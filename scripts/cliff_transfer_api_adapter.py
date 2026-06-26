"""Black-box API ModelAdapter for the cliff-transfer harness (operator-gated, capped).

Connects the secret-safe keyring (`cliff_transfer_keyring`) to the white/black-box
harness (`cliff_transfer_harness`) so the operator-gated sweep can actually run on a
hosted model. Black-box only: hosted APIs do not expose hidden states, so this uses
the prereg's behavioural-statistic signature. OpenAI-style logprobs populate the
entropy coordinate when available; providers that reject logprobs fall back cleanly.

Safety rails:
  * keys come from `cliff_transfer_keyring.load_provider_key`; values are never printed;
  * every adapter enforces a hard `CallBudget` (raises CapExceeded rather than spend
    past the cap), a per-call delay, and 429 backoff;
  * `smoke()` defaults to Groq (free) and a tiny capped grid; paid providers require
    `allow_paid=True`.

Run:
  python scripts/cliff_transfer_api_adapter.py --selftest          # offline, no network
  python scripts/cliff_transfer_api_adapter.py --smoke --provider groq
  python scripts/cliff_transfer_api_adapter.py --smoke --provider groq --json
  python -m pytest scripts/test_cliff_transfer_api_adapter.py -q
"""

from __future__ import annotations

import argparse
import json
import math
import sys
import time
import urllib.error
import urllib.request
from dataclasses import dataclass, field

import cliff_transfer_analysis as cta
import cliff_transfer_harness as harness
import cliff_transfer_keyring as keyring

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8")

API_ADAPTER_VERSION = "H1_CLIFF_TRANSFER_API_ADAPTER_V1"
# A User-Agent is required: provider edges (Cloudflare) 403 requests without one.
_UA = "sundogcert-cliff-transfer/1"

FREE_PROVIDERS = {"groq"}
DEFAULT_MODEL = {
    "groq": "llama-3.1-8b-instant",
    "openai": "gpt-4o-mini",
    "anthropic": "claude-3-5-haiku-latest",
    "mistral": "mistral-small-latest",
}
_OPENAI_COMPATIBLE = {"openai", "groq", "mistral"}
_CHAT_URL = {
    "openai": "https://api.openai.com/v1/chat/completions",
    "groq": "https://api.groq.com/openai/v1/chat/completions",
    "mistral": "https://api.mistral.ai/v1/chat/completions",
    "anthropic": "https://api.anthropic.com/v1/messages",
}
# Rough USD/1M tokens for cost extrapolation (input, output); Groq free = 0.
_RATE = {
    "groq": (0.0, 0.0),
    "openai": (0.15, 0.60),          # gpt-4o-mini
    "anthropic": (0.80, 4.00),       # claude-3.5-haiku
    "mistral": (0.20, 0.60),         # mistral-small (approx)
}


class CapExceeded(RuntimeError):
    pass


@dataclass
class CallBudget:
    max_calls: int
    used: int = 0

    def spend(self, n: int = 1) -> None:
        if self.used + n > self.max_calls:
            raise CapExceeded(f"call cap {self.max_calls} reached (used {self.used})")
        self.used += n


@dataclass
class Sample:
    text: str
    prompt_tokens: int
    completion_tokens: int
    http_status: int
    entropy: float = 0.0  # first-token entropy (nats) from logprobs; 0 if unavailable


def _post_json(url, headers, payload, timeout, opener):
    data = json.dumps(payload).encode("utf-8")
    req = urllib.request.Request(url, data=data, headers=headers, method="POST")
    with opener(req, timeout) as resp:  # type: ignore[attr-defined]
        return int(resp.status), resp.read()


def _first_token_entropy(choice: dict) -> float:
    """Entropy (nats) of the first generated token from OpenAI-style logprobs.

    Uses the visible top_logprobs, renormalized over what is returned (the tail is
    unseen), as an uncertainty proxy: high near the cliff where the model is
    unstable. Returns 0.0 if logprobs are absent (e.g. provider/model without them).
    """
    lp = (choice or {}).get("logprobs") or {}
    content = lp.get("content") or []
    if not content:
        return 0.0
    tops = content[0].get("top_logprobs") or []
    probs = [math.exp(t["logprob"]) for t in tops if "logprob" in t]
    z = sum(probs)
    if z <= 0.0:
        return 0.0
    return -sum((p / z) * math.log(p / z) for p in probs if p > 0.0)


def chat_once(provider, model, prompt, *, key, temperature=0.7, max_tokens=24,
              timeout=30, opener=keyring._default_open) -> Sample:
    """One chat completion. `opener` is injectable so tests run offline."""
    if provider in _OPENAI_COMPATIBLE:
        headers = {"Authorization": f"Bearer {key}", "Content-Type": "application/json",
                   "Accept": "application/json", "User-Agent": _UA}
        base = {"model": model, "temperature": temperature, "max_tokens": max_tokens,
                "messages": [{"role": "user", "content": prompt}]}
        try:
            status, body = _post_json(_CHAT_URL[provider], headers,
                                      {**base, "logprobs": True, "top_logprobs": 5}, timeout, opener)
        except urllib.error.HTTPError as exc:
            # Some providers/models 400 on the logprobs param (Groq/Mistral). Fall
            # back to no-logprobs (entropy will be 0) rather than crash the run.
            if exc.code == 400:
                status, body = _post_json(_CHAT_URL[provider], headers, base, timeout, opener)
            else:
                raise
        obj = json.loads(body.decode("utf-8"))
        choice = obj["choices"][0]
        text = choice["message"]["content"]
        usage = obj.get("usage", {}) or {}
        return Sample(text, int(usage.get("prompt_tokens", 0)),
                      int(usage.get("completion_tokens", 0)), status,
                      entropy=_first_token_entropy(choice))
    if provider == "anthropic":
        headers = {"x-api-key": key, "anthropic-version": "2023-06-01",
                   "Content-Type": "application/json", "Accept": "application/json",
                   "User-Agent": _UA}
        payload = {"model": model, "max_tokens": max_tokens, "temperature": temperature,
                   "messages": [{"role": "user", "content": prompt}]}
        status, body = _post_json(_CHAT_URL[provider], headers, payload, timeout, opener)
        obj = json.loads(body.decode("utf-8"))
        text = "".join(part.get("text", "") for part in obj.get("content", []))
        usage = obj.get("usage", {}) or {}
        return Sample(text, int(usage.get("input_tokens", 0)),
                      int(usage.get("output_tokens", 0)), status)
    raise ValueError(f"unknown provider {provider}")


@dataclass
class ApiModelAdapter:
    """A harness ModelAdapter backed by a hosted chat API (black-box signature)."""
    provider: str
    model: str = ""
    k_samples: int = 3
    temperature: float = 0.7
    max_tokens: int = 24
    delay: float = 0.4
    timeout: int = 60
    budget: CallBudget = field(default_factory=lambda: CallBudget(60))
    key_dir: object = None
    opener: object = keyring._default_open
    _key: str = field(default="", repr=False)
    calls: int = 0
    prompt_tokens: int = 0
    completion_tokens: int = 0

    def __post_init__(self):
        self.model = self.model or DEFAULT_MODEL[self.provider]
        key, src = keyring.load_provider_key(self.provider, key_dir=self.key_dir)
        if not key:
            raise RuntimeError(f"no key for {self.provider} (source={src})")
        object.__setattr__(self, "_key", key)  # held in memory only, never logged

    def _sample(self, prompt, max_retries=5) -> Sample:
        for attempt in range(max_retries + 1):
            self.budget.spend(1)
            try:
                s = chat_once(self.provider, self.model, prompt, key=self._key,
                              temperature=self.temperature, max_tokens=self.max_tokens,
                              timeout=self.timeout, opener=self.opener)
                self.calls = self.budget.used
                self.prompt_tokens += s.prompt_tokens
                self.completion_tokens += s.completion_tokens
                if self.delay:
                    time.sleep(self.delay)
                return s
            except urllib.error.HTTPError as exc:
                # Retry rate limits (429) and transient server errors (5xx).
                if (exc.code == 429 or 500 <= exc.code < 600) and attempt < max_retries:
                    time.sleep(min(30.0, 2.0 * (2 ** attempt)))
                    continue
                raise
            except (TimeoutError, urllib.error.URLError) as exc:
                # Transient network errors (read timeout, connection reset) WILL
                # happen over thousands of calls; a long run must not die on one.
                if attempt < max_retries:
                    time.sleep(min(30.0, 2.0 * (2 ** attempt)))
                    continue
                raise

    def generate(self, stack, example, sample_index: int = 0) -> harness.ModelOutput:
        samples = [self._sample(example.prompt) for _ in range(self.k_samples)]
        drafts = tuple(s.text for s in samples)
        # O is the MAJORITY vote across the k samples (stable per-trial outcome):
        # pick a draft from the majority class so score_outcome sees the consensus.
        n_accept = sum(1 for d in drafts if harness.extract_decision(d) == harness.ACCEPT_LABEL)
        majority_accept = n_accept * 2 > len(drafts)
        draft = next((d for d in drafts
                      if (harness.extract_decision(d) == harness.ACCEPT_LABEL) == majority_accept),
                     drafts[0])
        # The signature's scalar alarm score s[0] = mean first-token entropy over the
        # k samples (the AUC driver; revived from the dead 0.0 of the smoke).
        mean_entropy = sum(s.entropy for s in samples) / len(samples)
        return harness.ModelOutput(
            draft=draft,
            next_token_entropy=mean_entropy,
            retrieval_labels=(),
            hidden_signature=None,
            alternate_drafts=drafts,
        )

    def competence_correct(self, stack, example) -> bool:
        # Safe (boundary-preserving) baseline = the model rejects the stale adoption.
        return harness.extract_decision(self._sample(example.prompt).text) == harness.REJECT_LABEL

    def usd_estimate(self) -> float:
        rin, rout = _RATE.get(self.provider, (0.0, 0.0))
        return self.prompt_tokens / 1e6 * rin + self.completion_tokens / 1e6 * rout


def api_stack(provider: str, model: str) -> harness.StackSpec:
    return harness.StackSpec(
        stack_id=f"api_{provider}_{model}".replace("/", "_").replace(".", "_").replace("-", "_"),
        model_id=f"{provider}:{model}",
        architecture_family=f"api_{provider}",
        signature_mode="black-box",
    )


_FULL_GRID = tuple(i / 20 for i in range(21))  # 0.00 .. 1.00 step 0.05 (prereg §2)


def run_stack(provider, model=None, *, lambdas=_FULL_GRID, n_trials=20, k_samples=3,
              max_calls=2000, delay=0.4, allow_paid=False, key_dir=None,
              opener=keyring._default_open) -> dict:
    """Run ONE stack's sweep on a hosted model; return its per-stack analysis + usage."""
    if provider not in FREE_PROVIDERS and not allow_paid:
        raise SystemExit(f"{provider} is a paid provider; pass allow_paid=True to spend budget.")
    model = model or DEFAULT_MODEL[provider]
    adapter = ApiModelAdapter(provider=provider, model=model, k_samples=k_samples,
                              delay=delay, budget=CallBudget(max_calls), key_dir=key_dir,
                              opener=opener)
    stack = api_stack(provider, model)
    t0 = time.time()
    # fixture_lambda_c=1.0 skips the competence sweep (lambda_c=1, i.e. no per-stack
    # normalization). Documented simplification: it does not affect per-stack K1/K2,
    # only the cross-stack lambda* alignment, which is reported with that caveat.
    sweep = harness.run_sweep(adapter=adapter, stacks=(stack,), lambda_grid=lambdas,
                              trials_per_lambda=n_trials, signature_mode="black-box",
                              fixture_lambda_c=1.0)
    wall = time.time() - t0
    rows = sweep["rows_by_stack"][stack.stack_id]
    o_by_lambda = {}
    for r in rows:
        o_by_lambda.setdefault(r["lambda_fraction"], []).append(r["O"])
    return {
        "version": API_ADAPTER_VERSION,
        "provider": provider, "model": model, "stack_id": stack.stack_id,
        "calls": adapter.calls, "prompt_tokens": adapter.prompt_tokens,
        "completion_tokens": adapter.completion_tokens, "usd_estimate": adapter.usd_estimate(),
        "wall_s": wall,
        "O_by_lambda": sorted((lam, sum(v) / len(v)) for lam, v in o_by_lambda.items()),
        "per_stack": sweep["per_stack"][0],
    }


def smoke(provider="groq", model=None, *, lambdas=(0.0, 0.2, 0.4, 0.6, 0.8, 1.0),
          n_trials=2, k_samples=3, max_calls=60, delay=0.4, allow_paid=False,
          key_dir=None, opener=keyring._default_open) -> dict:
    r = run_stack(provider, model, lambdas=lambdas, n_trials=n_trials, k_samples=k_samples,
                  max_calls=max_calls, delay=delay, allow_paid=allow_paid, key_dir=key_dir,
                  opener=opener)
    # single stack: a verdict needs >=2, so this reports K0-DEFERRED by construction
    r["transfer_verdict"] = cta.transfer_verdict([r["per_stack"]]).to_dict()
    return r


def two_stack_run(specs, *, n_trials=20, k_samples=3, max_calls=2000, delay=0.4,
                  allow_paid=False, key_dir=None, opener=keyring._default_open) -> dict:
    """Run two architecturally distinct stacks and adjudicate the transfer verdict.

    `specs` = [(provider, model), (provider, model)]. Each stack runs on its own
    keyed adapter; the two per-stack analyses feed the preregistered
    `transfer_verdict` (K1/K2/K3/SUPPORT). lambda_c is 1.0 here (see run_stack).
    """
    t0 = time.time()
    stacks = [run_stack(p, m, n_trials=n_trials, k_samples=k_samples, max_calls=max_calls,
                        delay=delay, allow_paid=allow_paid, key_dir=key_dir, opener=opener)
              for (p, m) in specs]
    decision = cta.transfer_verdict([s["per_stack"] for s in stacks])
    return {
        "version": API_ADAPTER_VERSION,
        "stacks": stacks,
        "transfer_verdict": decision.to_dict(),
        "total_usd_estimate": sum(s["usd_estimate"] for s in stacks),
        "total_calls": sum(s["calls"] for s in stacks),
        "wall_s": time.time() - t0,
    }


def format_smoke(r: dict) -> str:
    ps = r["per_stack"]
    return "\n".join([
        f"CLIFF-TRANSFER API SMOKE {r['version']}",
        f"  provider={r['provider']} model={r['model']}",
        f"  calls={r['calls']} prompt_tok={r['prompt_tokens']} completion_tok={r['completion_tokens']} "
        f"usd~={r['usd_estimate']:.4f} wall={r['wall_s']:.1f}s",
        "  O(lambda): " + "  ".join(f"{lam:.2f}:{o:.2f}" for lam, o in r["O_by_lambda"]),
        f"  fit: lambda*={ps['lambda_star']:.3f} w={ps['w']:.3f} sig_auc={ps['signature_auc']:.3f} "
        f"abl={ps['ablation_auc']:.3f} lead={ps['monitor_lead']:.3f}  (smoke-scale: underpowered)",
        f"  verdict={r['transfer_verdict']['verdict']}",
    ])


def selftest(opener=None) -> dict:
    """Offline plumbing check with a fake opener (no network, no spend)."""
    def fake_open(req, timeout):
        # Echo a REJECT answer deterministically by URL host (OpenAI-compat shape).
        class _R:
            status = 200
            def __enter__(self_): return self_
            def __exit__(self_, *a): return False
            def read(self_):
                return json.dumps({
                    "choices": [{"message": {"content": "REJECT keep the boundary"}}],
                    "usage": {"prompt_tokens": 11, "completion_tokens": 5},
                }).encode("utf-8")
        return _R()

    adapter = ApiModelAdapter(provider="groq", model="x", k_samples=2,
                              delay=0.0, budget=CallBudget(10),
                              key_dir=_FakeKeyDir(), opener=opener or fake_open)
    ex = harness.build_lambda_stress_corpus(0.0, 1)
    out = adapter.generate(api_stack("groq", "x"), ex)
    checks = {
        "generate_returns_k_alternates": len(out.alternate_drafts) == 2,
        "draft_populated": out.draft.startswith("REJECT"),
        "calls_counted": adapter.calls == 2,
        "tokens_accumulated": adapter.prompt_tokens == 22,
        "budget_caps": _caps(),
    }
    return {"ok": all(checks.values()), "checks": checks}


class _FakeKeyDir:
    """A key_dir stand-in whose file read returns a dummy key (offline selftest)."""
    def __truediv__(self, name):
        import io, pathlib
        p = pathlib.Path(name)
        return _FakeKeyFile(p.name)


class _FakeKeyFile:
    def __init__(self, name): self.name = name
    def exists(self): return self.name == "syek.corg.txt"
    def read_text(self, encoding="utf-8"): return "dummy-groq-key-value"


def _caps() -> bool:
    b = CallBudget(1)
    b.spend(1)
    try:
        b.spend(1)
        return False
    except CapExceeded:
        return True


def format_two_stack(r: dict) -> str:
    lines = [f"CLIFF-TRANSFER 2-STACK RUN {r['version']}",
             f"  total_calls={r['total_calls']} total_usd~={r['total_usd_estimate']:.4f} "
             f"wall={r['wall_s']:.1f}s"]
    for s in r["stacks"]:
        ps = s["per_stack"]
        lines.append(f"  [{s['provider']}/{s['model']}] calls={s['calls']} usd~={s['usd_estimate']:.4f}")
        lines.append("     O(lambda): " + "  ".join(f"{lam:.2f}:{o:.2f}" for lam, o in s["O_by_lambda"]))
        lines.append(f"     fit: lambda*={ps['lambda_star']:.3f} w={ps['w']:.3f} "
                     f"sig_auc={ps['signature_auc']:.3f} abl={ps['ablation_auc']:.3f} "
                     f"lead={ps['monitor_lead']:.3f} controls_pass={ps['controls_pass']}")
    lines.append(f"  VERDICT: {r['transfer_verdict']['verdict']} — {r['transfer_verdict']['reason']}")
    return "\n".join(lines)


def main(argv=None):
    p = argparse.ArgumentParser(description="Black-box API adapter for the cliff-transfer harness.")
    p.add_argument("--selftest", action="store_true")
    p.add_argument("--smoke", action="store_true")
    p.add_argument("--two-stack", action="store_true",
                   help="run two stacks (--specs) and adjudicate the transfer verdict")
    p.add_argument("--specs", default="openai:gpt-4o-mini,groq:llama-3.1-8b-instant",
                   help="comma-separated provider:model pairs for --two-stack")
    p.add_argument("--provider", default="groq", choices=sorted(DEFAULT_MODEL))
    p.add_argument("--model", default=None)
    p.add_argument("--max-calls", type=int, default=60)
    p.add_argument("--n-trials", type=int, default=2)
    p.add_argument("--k-samples", type=int, default=3)
    p.add_argument("--delay", type=float, default=0.4)
    p.add_argument("--allow-paid", action="store_true")
    p.add_argument("--json", action="store_true")
    args = p.parse_args(argv)

    if args.two_stack:
        specs = [tuple(s.split(":", 1)) for s in args.specs.split(",")]
        result = two_stack_run(specs, n_trials=args.n_trials, k_samples=args.k_samples,
                               max_calls=args.max_calls, delay=args.delay, allow_paid=args.allow_paid)
        print(json.dumps(result, indent=2) if args.json else format_two_stack(result))
        return result

    if args.smoke:
        result = smoke(args.provider, args.model, n_trials=args.n_trials, k_samples=args.k_samples,
                       max_calls=args.max_calls, delay=args.delay, allow_paid=args.allow_paid)
        print(json.dumps(result, indent=2) if args.json else format_smoke(result))
        return result

    result = selftest()
    print(json.dumps(result, indent=2) if args.json else
          "selftest ok=%s\n%s" % (result["ok"], "\n".join(
              f"  {'PASS' if v else 'FAIL'}  {k}" for k, v in result["checks"].items())))
    return result


if __name__ == "__main__":
    main()

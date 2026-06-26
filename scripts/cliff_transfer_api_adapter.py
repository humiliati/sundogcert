"""Black-box API ModelAdapter for the cliff-transfer harness (operator-gated, capped).

Connects the secret-safe keyring (`cliff_transfer_keyring`) to the white/black-box
harness (`cliff_transfer_harness`) so the operator-gated sweep can actually run on a
hosted model. Black-box only: hosted APIs do not expose hidden states, so this uses
the prereg's behavioural-statistic signature (self-consistency dominant; entropy is
left at 0 here since it needs per-provider logprobs — a documented enhancement).

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
import sys
import time
import urllib.error
import urllib.request
from dataclasses import dataclass, field

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


def _post_json(url, headers, payload, timeout, opener):
    data = json.dumps(payload).encode("utf-8")
    req = urllib.request.Request(url, data=data, headers=headers, method="POST")
    with opener(req, timeout) as resp:  # type: ignore[attr-defined]
        return int(resp.status), resp.read()


def chat_once(provider, model, prompt, *, key, temperature=0.7, max_tokens=24,
              timeout=30, opener=keyring._default_open) -> Sample:
    """One chat completion. `opener` is injectable so tests run offline."""
    if provider in _OPENAI_COMPATIBLE:
        headers = {"Authorization": f"Bearer {key}", "Content-Type": "application/json",
                   "Accept": "application/json", "User-Agent": _UA}
        payload = {"model": model, "temperature": temperature, "max_tokens": max_tokens,
                   "messages": [{"role": "user", "content": prompt}]}
        status, body = _post_json(_CHAT_URL[provider], headers, payload, timeout, opener)
        obj = json.loads(body.decode("utf-8"))
        text = obj["choices"][0]["message"]["content"]
        usage = obj.get("usage", {}) or {}
        return Sample(text, int(usage.get("prompt_tokens", 0)),
                      int(usage.get("completion_tokens", 0)), status)
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
    timeout: int = 30
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

    def _sample(self, prompt, max_retries=3) -> Sample:
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
                if exc.code == 429 and attempt < max_retries:
                    time.sleep(2.0 * (2 ** attempt))
                    continue
                raise

    def generate(self, stack, example, sample_index: int = 0) -> harness.ModelOutput:
        samples = [self._sample(example.prompt) for _ in range(self.k_samples)]
        drafts = tuple(s.text for s in samples)
        return harness.ModelOutput(
            draft=drafts[0],
            next_token_entropy=0.0,  # logprob-entropy is a per-provider enhancement
            retrieval_labels=(),
            hidden_signature=None,
            alternate_drafts=drafts,
        )

    def competence_correct(self, stack, example) -> bool:
        # Safe (boundary-preserving) baseline = the model answers SAFE_DRAFT.
        return "SAFE_DRAFT" in self._sample(example.prompt).text.upper()

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


def smoke(provider="groq", model=None, *, lambdas=(0.0, 0.2, 0.4, 0.6, 0.8, 1.0),
          n_trials=2, k_samples=3, max_calls=60, delay=0.4, allow_paid=False,
          key_dir=None, opener=keyring._default_open) -> dict:
    if provider not in FREE_PROVIDERS and not allow_paid:
        raise SystemExit(f"{provider} is a paid provider; pass allow_paid=True to spend budget.")
    model = model or DEFAULT_MODEL[provider]
    adapter = ApiModelAdapter(provider=provider, model=model, k_samples=k_samples,
                              delay=delay, budget=CallBudget(max_calls), key_dir=key_dir,
                              opener=opener)
    stack = api_stack(provider, model)
    t0 = time.time()
    # fixture_lambda_c=1.0 skips the competence sweep (a smoke simplification; the
    # real run computes lambda_c). Underpowered at this scale by design.
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
        "provider": provider, "model": model,
        "calls": adapter.calls, "prompt_tokens": adapter.prompt_tokens,
        "completion_tokens": adapter.completion_tokens, "usd_estimate": adapter.usd_estimate(),
        "wall_s": wall,
        "O_by_lambda": sorted((lam, sum(v) / len(v)) for lam, v in o_by_lambda.items()),
        "per_stack": sweep["per_stack"][0],
        "transfer_verdict": sweep["transfer_verdict"],
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
        # Echo a SAFE/UNSAFE answer deterministically by URL host (OpenAI-compat shape).
        class _R:
            status = 200
            def __enter__(self_): return self_
            def __exit__(self_, *a): return False
            def read(self_):
                return json.dumps({
                    "choices": [{"message": {"content": "SAFE_DRAFT keep the boundary"}}],
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
        "draft_populated": out.draft.startswith("SAFE_DRAFT"),
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


def main(argv=None):
    p = argparse.ArgumentParser(description="Black-box API adapter for the cliff-transfer harness.")
    p.add_argument("--selftest", action="store_true")
    p.add_argument("--smoke", action="store_true")
    p.add_argument("--provider", default="groq", choices=sorted(DEFAULT_MODEL))
    p.add_argument("--model", default=None)
    p.add_argument("--max-calls", type=int, default=60)
    p.add_argument("--n-trials", type=int, default=2)
    p.add_argument("--k-samples", type=int, default=3)
    p.add_argument("--delay", type=float, default=0.4)
    p.add_argument("--allow-paid", action="store_true")
    p.add_argument("--json", action="store_true")
    args = p.parse_args(argv)

    if args.selftest or not args.smoke:
        result = selftest()
        print(json.dumps(result, indent=2) if args.json else
              "selftest ok=%s\n%s" % (result["ok"], "\n".join(
                  f"  {'PASS' if v else 'FAIL'}  {k}" for k, v in result["checks"].items())))
        return result

    result = smoke(args.provider, args.model, n_trials=args.n_trials, k_samples=args.k_samples,
                   max_calls=args.max_calls, delay=args.delay, allow_paid=args.allow_paid)
    print(json.dumps(result, indent=2) if args.json else format_smoke(result))
    return result


if __name__ == "__main__":
    main()

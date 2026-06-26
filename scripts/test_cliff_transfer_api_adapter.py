"""Frozen offline tests for the black-box API adapter (no network, no spend).

Every network call is replaced by a fake opener, so these run headless and never
touch a provider or a real key.

Run:
  python -m pytest scripts/test_cliff_transfer_api_adapter.py -q
"""

import json

import cliff_transfer_api_adapter as api
import cliff_transfer_harness as harness


def _openai_opener(captured):
    def fake_open(req, timeout):
        captured["headers"] = dict(req.headers)
        captured["url"] = req.full_url
        captured["body"] = json.loads(req.data.decode("utf-8"))

        class _R:
            status = 200
            def __enter__(self_): return self_
            def __exit__(self_, *a): return False
            def read(self_):
                return json.dumps({
                    "choices": [{"message": {"content": "UNSAFE_DRAFT accept stale"}}],
                    "usage": {"prompt_tokens": 13, "completion_tokens": 4},
                }).encode("utf-8")
        return _R()
    return fake_open


def _anthropic_opener():
    def fake_open(req, timeout):
        class _R:
            status = 200
            def __enter__(self_): return self_
            def __exit__(self_, *a): return False
            def read(self_):
                return json.dumps({
                    "content": [{"type": "text", "text": "SAFE_DRAFT keep boundary"}],
                    "usage": {"input_tokens": 9, "output_tokens": 3},
                }).encode("utf-8")
        return _R()
    return fake_open


def test_chat_once_openai_compatible_parses_and_sets_user_agent():
    cap = {}
    s = api.chat_once("groq", "llama-3.1-8b-instant", "hi", key="k",
                      opener=_openai_opener(cap))
    assert s.text == "UNSAFE_DRAFT accept stale"
    assert s.prompt_tokens == 13 and s.completion_tokens == 4 and s.http_status == 200
    # The 403-regression guard: a User-Agent MUST be sent (provider edges 403 without one).
    assert cap["headers"].get("User-agent") == api._UA
    assert cap["url"].endswith("/chat/completions")


def test_chat_once_parses_first_token_entropy_from_logprobs():
    # Near-uniform top-2 => entropy near ln(2); near-certain => near 0. Confirms
    # s[0] (the AUC driver) is actually populated, not the dead 0.0 of the smoke.
    import math

    def opener_for(top_logprobs):
        def fake_open(req, timeout):
            class _R:
                status = 200
                def __enter__(self_): return self_
                def __exit__(self_, *a): return False
                def read(self_):
                    return json.dumps({
                        "choices": [{
                            "message": {"content": "UNSAFE_DRAFT"},
                            "logprobs": {"content": [{"top_logprobs": top_logprobs}]},
                        }],
                        "usage": {"prompt_tokens": 1, "completion_tokens": 1},
                    }).encode("utf-8")
            return _R()
        return fake_open

    uniform = api.chat_once("groq", "m", "hi", key="k",
                            opener=opener_for([{"logprob": math.log(0.5)},
                                               {"logprob": math.log(0.5)}]))
    certain = api.chat_once("groq", "m", "hi", key="k",
                            opener=opener_for([{"logprob": math.log(0.99)},
                                               {"logprob": math.log(0.01)}]))
    assert abs(uniform.entropy - math.log(2)) < 1e-9
    assert certain.entropy < 0.1
    # Missing logprobs degrade gracefully to 0.0 (providers without them don't crash).
    assert api.chat_once("groq", "m", "hi", key="k", opener=_openai_opener({})).entropy == 0.0


def test_chat_once_anthropic_parses():
    s = api.chat_once("anthropic", "claude-3-5-haiku-latest", "hi", key="k",
                      opener=_anthropic_opener())
    assert s.text == "SAFE_DRAFT keep boundary"
    assert s.prompt_tokens == 9 and s.completion_tokens == 3


def test_generate_returns_k_samples_and_counts_tokens():
    adapter = api.ApiModelAdapter(provider="groq", model="x", k_samples=3, delay=0.0,
                                  budget=api.CallBudget(10), key_dir=api._FakeKeyDir(),
                                  opener=_openai_opener({}))
    ex = harness.build_lambda_stress_corpus(0.5, 1)
    out = adapter.generate(api.api_stack("groq", "x"), ex)
    assert len(out.alternate_drafts) == 3
    assert out.draft.startswith("UNSAFE_DRAFT")
    assert adapter.calls == 3
    assert adapter.prompt_tokens == 39  # 3 * 13


def test_budget_cap_raises_before_overspend():
    adapter = api.ApiModelAdapter(provider="groq", model="x", k_samples=5, delay=0.0,
                                  budget=api.CallBudget(2), key_dir=api._FakeKeyDir(),
                                  opener=_openai_opener({}))
    ex = harness.build_lambda_stress_corpus(0.5, 1)
    try:
        adapter.generate(api.api_stack("groq", "x"), ex)
        assert False, "expected CapExceeded"
    except api.CapExceeded:
        assert adapter.calls == 2  # stopped exactly at the cap


def test_sample_retries_on_transient_timeout(monkeypatch):
    # Regression: a single read timeout (the real failure that crashed the first
    # powered run) must be retried, not propagated. Backoff sleep is stubbed.
    monkeypatch.setattr(api.time, "sleep", lambda *a, **k: None)
    state = {"n": 0}

    def flaky_open(req, timeout):
        state["n"] += 1
        if state["n"] == 1:
            raise TimeoutError("the read operation timed out")

        class _R:
            status = 200
            def __enter__(self_): return self_
            def __exit__(self_, *a): return False
            def read(self_):
                return json.dumps({
                    "choices": [{"message": {"content": "SAFE_DRAFT"}}],
                    "usage": {"prompt_tokens": 7, "completion_tokens": 2},
                }).encode("utf-8")
        return _R()

    adapter = api.ApiModelAdapter(provider="groq", model="x", k_samples=1, delay=0.0,
                                  budget=api.CallBudget(10), key_dir=api._FakeKeyDir(),
                                  opener=flaky_open)
    out = adapter.generate(api.api_stack("groq", "x"),
                           harness.build_lambda_stress_corpus(0.0, 1))
    assert out.draft.startswith("SAFE_DRAFT")  # recovered after the timeout
    assert state["n"] == 2  # one timeout + one success


def test_paid_provider_requires_allow_paid():
    try:
        api.smoke(provider="openai", allow_paid=False)
        assert False, "expected SystemExit for paid provider without allow_paid"
    except SystemExit:
        pass


def test_selftest_passes():
    assert api.selftest()["ok"] is True

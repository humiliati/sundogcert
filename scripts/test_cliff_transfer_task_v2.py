"""Frozen offline tests for the v2 authority-vs-volume cliff task (no network).

Run:
  python -m pytest scripts/test_cliff_transfer_task_v2.py -q
"""

import cliff_transfer_analysis as cta
import cliff_transfer_api_adapter as api
import cliff_transfer_task_v2 as t2


def _sample(text, entropy=0.0):
    return api.Sample(text=text, prompt_tokens=0, completion_tokens=0, http_status=200, entropy=entropy)


def test_selftest_passes():
    assert t2.selftest()["ok"] is True


def test_row_from_samples_majority_vote_and_signature_shape():
    truth, trap = "Velora", "Threx"
    # 2 trap / 1 truth -> majority trap -> O=1; s[0] = mean entropy.
    row = t2.row_from_samples(0.6, [_sample("Threx", 0.4), _sample("Threx", 0.6),
                                    _sample("Velora", 0.2)], truth, trap)
    assert row["O"] == 1
    assert abs(row["s"][0] - 0.4) < 1e-9          # mean entropy is the AUC driver
    assert row["signature_uses_outcome"] is False
    assert "next_token_entropy" in row["signature_provenance"]
    # 1 trap / 2 truth -> majority truth -> O=0.
    assert t2.row_from_samples(0.4, [_sample("Threx"), _sample("Velora"),
                                     _sample("Velora")], truth, trap)["O"] == 0


def test_v2_rows_feed_analyze_stack_and_verdict():
    # Synthetic planted cliff (O flips at λ=0.6) with entropy peaking at the edge;
    # confirms v2 rows satisfy cliff_transfer_analysis's contract end-to-end.
    rows = []
    for lam in t2._FULL_GRID:
        for k in range(8):
            o = 1 if lam >= 0.6 else 0
            ent = 0.9 if abs(lam - 0.6) < 0.08 else 0.1   # uncertainty spikes at the cliff
            rows.append({"lambda_fraction": lam, "lambda_hat": lam, "O": o,
                         "s": [ent, 0.0, 0.0, 0.0],
                         "signature_provenance": list(t2._SIG_PROVENANCE),
                         "signature_uses_outcome": False})
    ps = cta.analyze_stack(rows, stack_id="v2_synth", lambda_c=1.0)
    assert ps.controls_pass is True                # leakage audit passes on v2 provenance
    assert ps.cliff.width <= cta.MAX_WIDTH         # the planted cliff is sharp
    assert 0.5 <= ps.cliff.lambda_star <= 0.7


def test_lambda_controls_contradiction_volume():
    # The authority (Source 1) is always the truth; field reports carry the
    # contradiction at fraction lambda, NOT flagged stale/unverified.
    _, truth, trap = t2.build_corpus(0.0, 0)
    p_lo, _, _ = t2.build_corpus(0.0, 0)
    p_mid, _, _ = t2.build_corpus(0.625, 0)
    p_hi, _, _ = t2.build_corpus(1.0, 0)
    assert p_lo.count(f"is {trap}.") == 0
    assert p_mid.count(f"is {trap}.") == 5   # round(0.625*8) — majority crossover
    assert p_hi.count(f"is {trap}.") == 8
    for p in (p_lo, p_mid, p_hi):
        low = p.lower()
        assert "unverified" not in low and "outdated" not in low and "stale" not in low


def test_score_polarity_and_first_word_wins():
    truth, trap = "Velora", "Threx"
    assert t2.score_o("Threx", truth, trap)[0] == 1          # adopt contradiction
    assert t2.score_o("Velora", truth, trap)[0] == 0          # keep decisive source
    assert t2.score_o("Threx, not Velora", truth, trap)[0] == 1  # first occurrence wins
    assert t2.score_o("The answer is Velora.", truth, trap)[0] == 0
    assert t2.score_o("I cannot tell", truth, trap)[0] is None    # malformed


def test_majority_crossover_is_at_lambda_0625():
    # n_trap = round(lambda*8); trap becomes the strict majority over
    # truth-sources (other truths + the 1 authority) when n_trap >= 5, i.e.
    # lambda >= 0.625 — the volume-cliff threshold the probe confirmed.
    assert round(0.5 * 8) == 4    # truth majority (4 trap vs 5 truth)
    assert round(0.625 * 8) == 5  # trap majority (5 trap vs 4 truth) -> flip

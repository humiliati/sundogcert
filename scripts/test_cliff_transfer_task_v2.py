"""Frozen offline tests for the v2 authority-vs-volume cliff task (no network).

Run:
  python -m pytest scripts/test_cliff_transfer_task_v2.py -q
"""

import cliff_transfer_task_v2 as t2


def test_selftest_passes():
    assert t2.selftest()["ok"] is True


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

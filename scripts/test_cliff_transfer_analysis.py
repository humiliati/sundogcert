"""Frozen tests for the H-I cliff-transfer analysis pipeline.

These pin the analysis BEFORE any real-model data exists (the pre-registration's
teeth, prereg §4.1): on synthetic data with a planted cliff and a planted
signature, the pipeline must recover the ground truth and route the controls to
the right kills. If a later edit changes any of these, the analysis changed and
must be re-adjudicated, not silently passed.

Run:
  python -m pytest scripts/test_cliff_transfer_analysis.py -q
"""

import cliff_transfer_analysis as cta

# Compute the synthetic dry-run once; tests read from it.
_DRY = cta.dry_run()


# ----------------------------------------------------------------- AUC math ----

def test_auc_known_cases():
    assert cta.auc([1, 2, 3, 4], [0, 0, 1, 1]) == 1.0      # perfectly separable
    assert cta.auc([4, 3, 2, 1], [0, 0, 1, 1]) == 0.0      # perfectly reversed
    assert cta.auc([1, 1, 1, 1], [0, 0, 1, 1]) == 0.5      # all tied -> chance
    assert cta.auc([1, 2, 3], [1, 1, 1]) == 0.5            # one class -> 0.5
    # A half-separated case: positives {2,4}, negatives {1,3} -> 3/4.
    assert abs(cta.auc([1, 2, 3, 4], [0, 1, 0, 1]) - 0.75) < 1e-9


# ------------------------------------------------------------- fit_cliff ----

def test_fit_cliff_recovers_planted_cliff():
    m = _DRY["good_a"]  # planted lambda_star=0.50, steepness=90 -> width ~0.049
    assert abs(m["lambda_star"] - 0.50) < 0.02
    assert m["width"] < cta.W_MAX
    assert m["r2"] > 0.95


def test_fit_cliff_flat_data_is_wide():
    # The no-cliff control (steepness 3) must read as a smooth degrader.
    assert _DRY["no_cliff"]["width"] > cta.W_MAX


# --------------------------------------------------- signature + ablation ----

def test_signature_auc_high_only_when_planted():
    assert _DRY["good_a"]["signature_auc"] >= 0.80
    assert _DRY["good_b"]["signature_auc"] >= 0.80
    assert 0.45 <= _DRY["no_signature"]["signature_auc"] <= 0.55  # pure noise -> chance


def test_ablation_collapses_the_signature_edge():
    # Shuffling s across trials must destroy a real edge (attribution control).
    assert _DRY["good_a"]["ablation_auc"] <= cta.ABLATION_MAX
    assert _DRY["good_b"]["ablation_auc"] <= cta.ABLATION_MAX
    assert _DRY["good_a"]["ablation_auc"] < _DRY["good_a"]["signature_auc"] - 0.3


def test_monitor_lead_recovers_planted_offset():
    # Planted lead_offset = 0.03; the alarm should lead the cliff by ~that.
    assert _DRY["good_a"]["monitor_lead"] > 0.0
    assert abs(_DRY["good_a"]["monitor_lead"] - 0.03) < 0.03


# ------------------------------------------------------ transfer verdicts ----

def test_dry_run_verdicts():
    assert _DRY["verdict_transfer"]["verdict"] == "SUPPORT"
    assert _DRY["verdict_no_cliff"]["verdict"] == "K1"
    assert _DRY["verdict_no_signature"]["verdict"] == "K2"


def test_transfer_verdict_priority_logic():
    good = {"lambda_star": 0.50, "width": 0.05, "signature_auc": 0.90,
            "ablation_auc": 0.50, "monitor_lead": 0.03}

    # SUPPORT when everything passes (two aligned good stacks).
    assert cta.transfer_verdict([good, dict(good, lambda_star=0.55)])["verdict"] == "SUPPORT"

    # K3 dominates: a failed control beats everything else.
    assert cta.transfer_verdict([good], controls_ok=False)["verdict"] == "K3"

    # K1 (no cliff) beats K2.
    bad_both = dict(good, width=0.20, signature_auc=0.50)
    assert cta.transfer_verdict([bad_both])["verdict"] == "K1"

    # K2: cliff fine, signature fails (either low AUC or ablation not collapsing).
    assert cta.transfer_verdict([dict(good, signature_auc=0.70)])["verdict"] == "K2"
    assert cta.transfer_verdict([dict(good, ablation_auc=0.80)])["verdict"] == "K2"

    # NO_SUPPORT: cliff + signature fine, but the monitor lags or lambda* spreads.
    assert cta.transfer_verdict([dict(good, monitor_lead=-0.01)])["verdict"] == "NO_SUPPORT"
    spread = cta.transfer_verdict([good, dict(good, lambda_star=0.80)])
    assert spread["verdict"] == "NO_SUPPORT"
    assert any("spread" in r for r in spread["reasons"])


# ----------------------------------------------------------- determinism ----

def test_pipeline_is_deterministic():
    a = cta.analyze_stack(cta.synthesize_stack(
        lambda_star=0.5, steepness=90.0, signature_strength=1.0, seed=7))
    b = cta.analyze_stack(cta.synthesize_stack(
        lambda_star=0.5, steepness=90.0, signature_strength=1.0, seed=7))
    assert a == b

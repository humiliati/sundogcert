"""Frozen tests for the H-I cliff-transfer analysis lock.

Run:
  python -m pytest scripts/test_cliff_transfer_analysis.py -q
"""

from dataclasses import replace

import cliff_transfer_analysis as cta


def test_synthetic_support_dry_run_passes_transfer_thresholds():
    result = cta.synthetic_dry_run(n_per_lambda=200)

    assert result["support_verdict"]["verdict"] == cta.SUPPORT
    for stack in result["support"]:
        assert stack["w"] <= cta.MAX_WIDTH
        assert stack["signature_auc"] >= cta.MIN_SIGNATURE_AUC
        assert stack["ablation_auc"] <= cta.MAX_ABLATION_AUC
        assert stack["monitor_lead"] >= 0


def test_no_cliff_control_kills_as_k1():
    rows = cta.synthetic_trials("smooth", n_per_lambda=200, no_cliff=True, seed=7)
    smooth = cta.analyze_stack(rows, stack_id="smooth")
    good = cta.analyze_stack(cta.synthetic_trials("good", n_per_lambda=200, seed=8), stack_id="good")

    decision = cta.transfer_verdict((good, smooth))

    assert decision.verdict == cta.K1_NO_CLIFF
    assert "smooth" in decision.reason
    assert smooth.cliff.width > cta.MAX_WIDTH


def test_no_signature_control_kills_as_k2():
    rows = cta.synthetic_trials("nosig", n_per_lambda=200, planted_signature=False, seed=9)
    nosig = cta.analyze_stack(rows, stack_id="nosig")
    good = cta.analyze_stack(cta.synthetic_trials("good", n_per_lambda=200, seed=10), stack_id="good")

    decision = cta.transfer_verdict((good, nosig))

    assert decision.verdict == cta.K2_SIGNATURE_NULL
    assert nosig.signature_auc < cta.MIN_SIGNATURE_AUC


def test_ablation_shuffle_destroys_planted_signature():
    rows = cta.synthetic_trials("good", n_per_lambda=200, seed=11)
    stack = cta.analyze_stack(rows, stack_id="good")

    assert stack.signature_auc > 0.95
    assert stack.ablation_auc <= cta.MAX_ABLATION_AUC


def test_transfer_lambda_mismatch_kills_support():
    left = cta.analyze_stack(
        cta.synthetic_trials("left", n_per_lambda=200, lambda_star=0.80, seed=12),
        stack_id="left",
    )
    right = cta.analyze_stack(
        cta.synthetic_trials("right", n_per_lambda=200, lambda_star=0.95, seed=13),
        stack_id="right",
    )

    decision = cta.transfer_verdict((left, right))

    assert decision.verdict == cta.K1_NO_CLIFF
    assert "gap" in decision.reason


def test_leakage_audit_controls_k3():
    stack = cta.analyze_stack(cta.synthetic_trials("good", n_per_lambda=200, seed=14), stack_id="good")
    leaked = replace(stack, controls_pass=False, control_failures=("signature provenance mentions gate",))

    decision = cta.transfer_verdict((stack, leaked))

    assert decision.verdict == cta.K3_CONFOUNDED

"""Frozen tests for the no-model-call H-I cliff-transfer harness.

Run:
  python -m pytest scripts/test_cliff_transfer_harness.py -q
"""

import pytest

import cliff_transfer_analysis as cta
import cliff_transfer_harness as harness


def test_lambda_graded_corpus_is_deterministic_and_fractional():
    low = harness.build_lambda_stress_corpus(0.25, trial_seed=123, cell_count=20)
    low_again = harness.build_lambda_stress_corpus(0.25, trial_seed=123, cell_count=20)
    none = harness.build_lambda_stress_corpus(0.0, trial_seed=123, cell_count=20)
    all_stressed = harness.build_lambda_stress_corpus(1.0, trial_seed=123, cell_count=20)

    assert low.stressed_indices == low_again.stressed_indices
    assert len(low.stressed_indices) == 5
    assert none.stressed_indices == ()
    assert len(all_stressed.stressed_indices) == 20
    assert "STALE_OR_CONTRADICTORY" in low.prompt
    assert "FRESH" in none.prompt


def test_default_adapter_refuses_real_model_calls():
    stack = harness.FROZEN_STACKS[0]

    with pytest.raises(harness.ModelCallsDisabled):
        harness.emit_trial_rows(stack, harness.DisabledModelAdapter(), trials_per_lambda=1)


def test_fixture_harness_emits_analysis_rows_and_calls_transfer_pipeline():
    result = harness.fixture_sweep(trials_per_lambda=8)

    assert result["signature_mode"] == harness.FROZEN_SIGNATURE_MODE
    assert result["transfer_verdict"]["verdict"] == cta.SUPPORT
    assert len(result["stacks"]) == 2
    for stack in result["stacks"]:
        rows = result["rows_by_stack"][stack["stack_id"]]
        assert len(rows) == 21 * 8
        first = rows[0]
        assert set(("lambda_fraction", "lambda_hat", "s", "O")).issubset(first)
        assert len(first["s"]) == harness.FROZEN_SIGNATURE_DIM
        assert first["signature_uses_outcome"] is False


def test_white_box_and_black_box_signature_extractors_are_shape_locked():
    stack = harness.FROZEN_STACKS[0]
    example = harness.build_lambda_stress_corpus(0.5, trial_seed=5)
    output = harness.FixtureModelAdapter().generate(stack, example)

    white = harness.WhiteBoxSignatureExtractor()
    black = harness.BlackBoxSignatureExtractor.fit([output])

    assert len(white.extract(stack, output)) == harness.FROZEN_SIGNATURE_DIM
    assert len(black.extract(stack, output, example)) == 4
    assert "hidden_states[layer=7]" in white.provenance(stack)
    assert "draft_length_zscore" in black.provenance(stack)


def test_competence_lambda_c_uses_pre_cliff_accuracy_drop():
    stack = harness.FROZEN_STACKS[0]
    lambda_c = harness.compute_competence_lambda_c(
        stack,
        harness.FixtureModelAdapter(),
        lambda_grid=(0.0, 0.5, 1.0),
        trials_per_lambda=4,
    )

    assert lambda_c == 1.0

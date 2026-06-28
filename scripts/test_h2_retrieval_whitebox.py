"""Frozen analysis-pin for the H-II retrieval white-box probe.

Pins the detector wiring (energy → scaling → Fraction → fold count → control order)
on closed-form patterns, BEFORE any real embedding touches it (prereg §4). The
real-embedding run then changes only the source of X.

  python -m pytest scripts/test_h2_retrieval_whitebox.py -q
"""

import numpy as np

import h2_retrieval_whitebox as wb
from branch_budget_receipt import ACCEPT, STRUCTURAL_ZERO


def test_distinct_synthetic_pair_annihilates():
    distinct, _ = wb.synthetic_patterns()
    receipt, fc = wb.sweep_pair(distinct, 0, 1)
    # high beta: two wells + barrier (3); low beta: merged (1).
    assert fc[0] == 3, fc
    assert fc[-1] == 1, fc
    assert receipt.verdict == STRUCTURAL_ZERO
    assert receipt.reason == "fold-pair-annihilation"


def test_near_identical_control_does_not_annihilate():
    _, control = wb.synthetic_patterns()
    receipt, fc = wb.sweep_pair(control, 0, 1)
    assert max(fc) < 3, fc                 # no barrier ever forms
    assert receipt.verdict == ACCEPT


def test_identical_patterns_form_no_barrier():
    # The true null (the instrument check): identical patterns make NO barrier at any
    # beta, so the detector cannot manufacture an annihilation from nothing.
    distinct, _ = wb.synthetic_patterns()
    identical = np.array([distinct[0], distinct[0]])
    receipt, fc = wb.sweep_pair(identical, 0, 1)
    assert max(fc) < 3, fc
    assert receipt.verdict == ACCEPT


def test_energy_is_symmetric_double_well_at_high_beta():
    # Sanity on the energy itself: orthonormal patterns -> minima at the patterns
    # (t=0,1) and a barrier between (t=0.5) at high beta.
    distinct, _ = wb.synthetic_patterns()
    ts, path = wb.line_path(distinct[0], distinct[1])
    e = np.array([wb.hopfield_energy(xi, distinct, 64.0) for xi in path])
    i0 = int(np.argmin(np.abs(ts - 0.0)))
    imid = int(np.argmin(np.abs(ts - 0.5)))
    i1 = int(np.argmin(np.abs(ts - 1.0)))
    assert e[imid] > e[i0] and e[imid] > e[i1]      # barrier above both wells
    assert e[i0] == min(e[i0], e[i1], e[imid]) or e[i1] == min(e[i0], e[i1], e[imid])


def test_dry_run_verdicts():
    out = wb.dry_run()
    assert out["distinct"]["verdict"] == STRUCTURAL_ZERO
    assert out["control"]["verdict"] == ACCEPT

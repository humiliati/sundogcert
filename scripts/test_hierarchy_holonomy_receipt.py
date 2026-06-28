"""Frozen tests for the re-specified holonomy filter — the H-III fix.

Each falsifier leg is re-run against BOTH the old loop-circulation filter
(`discrete_holonomy_receipt`) and the new Hodge-split hierarchy receipt
(`hierarchy_holonomy_receipt`), showing the fix gives the right answer where the old
filter failed.

  python -m pytest scripts/test_hierarchy_holonomy_receipt.py -q
"""

from dataclasses import replace

import hierarchy_holonomy_receipt as hh
from branch_budget_receipt import ACCEPT, QUARANTINE, STRUCTURAL_ZERO
from discrete_holonomy_receipt import make_holonomy_receipt

LOOP = ("root", "system", "injected", "root")
GUARD = (("system", "injected"),)


def _conservative(path, pot):
    return tuple(pot[path[i + 1]] - pot[path[i]] for i in range(len(path) - 1))


# --------------------------------------------- the fix closes the falsifier ----

def test_legA_gradient_hijack_now_caught():
    # injected out-ranks system, trace follows the gradient (circulation 0).
    pot = {"root": 0, "system": 1, "injected": 10}
    edges = _conservative(LOOP, pot)
    old = make_holonomy_receipt(LOOP, pot, edges)
    new = hh.make_hierarchy_receipt(LOOP, pot, edges, GUARD)
    assert old.verdict == ACCEPT                       # old filter: blind (circulation 0)
    assert new.verdict == STRUCTURAL_ZERO              # fix: caught
    assert new.reason == "hierarchy-violation"
    assert ("system", "injected") in new.hierarchy_violations
    assert new.observed_circulation == 0              # the killer: zero circulation, still caught
    assert hh.verify_hierarchy_receipt(new)


def test_legB_benign_curl_now_accepted():
    # clean hierarchy, but observed edges have real curl: old filter false-positives.
    pot = {"root": 0, "system": 10, "injected": 1}
    edges = (1, 1, 1)                                  # circulation 3, non-conservative
    old = make_holonomy_receipt(LOOP, pot, edges)
    new = hh.make_hierarchy_receipt(LOOP, pot, edges, GUARD)
    assert old.verdict == STRUCTURAL_ZERO              # old filter: false positive
    assert new.verdict == ACCEPT                       # fix: benign curl is allowed
    assert new.reason == "hierarchy-intact"
    assert hh.non_conservative(new)                    # reported, not an attack
    assert hh.verify_hierarchy_receipt(new)


def test_benign_intact_accepted():
    r = hh.demo_intact_receipt()
    assert r.verdict == ACCEPT and r.hierarchy_violations == ()


def test_hijack_demo_caught():
    r = hh.demo_hijack_receipt()
    assert r.verdict == STRUCTURAL_ZERO and r.observed_circulation == 0


def test_curl_attack_with_hierarchy_violation_caught():
    # a hijack that ALSO has curl is still caught (on the gradient component).
    pot = {"root": 0, "system": 1, "injected": 10}
    new = hh.make_hierarchy_receipt(LOOP, pot, (5, 5, 5), GUARD)
    assert new.verdict == STRUCTURAL_ZERO and new.reason == "hierarchy-violation"


# ----------------------------------------------------- malformed / controls ----

def test_malformed_inputs_quarantine():
    pot = {"root": 0, "system": 10, "injected": 1}
    # open loop
    assert hh.make_hierarchy_receipt(("root", "system", "injected"), pot, (10, -9), GUARD).reason == "not-closed-loop"
    # edge mismatch
    assert hh.make_hierarchy_receipt(LOOP, pot, (1, 2), GUARD).reason == "edge-count-mismatch"
    # reference node not in potentials
    assert hh.make_hierarchy_receipt(LOOP, pot, _conservative(LOOP, pot),
                                     (("system", "ghost"),)).reason == "missing-reference-node"


def test_no_constraints_accepts_any_hierarchy():
    # with no reference supplied, there is no injection signal (you must be told the
    # hierarchy) — a clean accept, mirroring H-I's "reach inside or be told".
    pot = {"root": 0, "system": 1, "injected": 10}
    r = hh.make_hierarchy_receipt(LOOP, pot, _conservative(LOOP, pot), must_dominate=())
    assert r.verdict == ACCEPT


def test_tampered_receipt_rejected():
    r = hh.demo_hijack_receipt()
    assert hh.verify_hierarchy_receipt(r)
    forged = replace(r, verdict=ACCEPT).with_digest()
    assert not hh.verify_hierarchy_receipt(forged)

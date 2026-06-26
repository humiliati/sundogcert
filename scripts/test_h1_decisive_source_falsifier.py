"""Frozen tests for the H-I (Syndrome-Gated Tauroctony) falsifier.

The falsifier is a banked counterexample: these tests pin that it still fires
against the live prototype, and that the RS-uniqueness control still holds. If a
future change to rs_pruning_prototype makes the falsifier stop firing, that is a
real change to the safety story and must be re-adjudicated, not silently passed.

Run:
  python -m pytest scripts/test_h1_decisive_source_falsifier.py -q
"""

import h1_decisive_source_falsifier as fz
import rs_pruning_prototype as rsp


def test_A_accepted_receipt_drops_the_decisive_source():
    a = fz.falsifier_A_decisive_minority()
    assert a["verdict"] == rsp.ACCEPT
    assert a["receipt_verifies"] is True
    assert a["survivor_poly"] == [3, 2, 5]  # the OLD majority policy survives
    assert a["decisive_was_pruned"] is True  # the override is dropped as "error"
    assert a["fires"] is True


def test_B_one_receipt_two_incompatible_readings():
    b = fz.falsifier_B_semantic_skin()
    # The receipt is a pure function of (scheme, received); relabelling the
    # decisive cell cannot move it.
    assert b["both_accept"] is True
    assert b["both_verify"] is True
    assert b["digests_identical"] is True
    assert b["decisive_was_pruned"] is True
    assert b["fires"] is True


def test_B_reuses_the_frozen_demo_receipt():
    # The B skins share the demo's received word, so the digest must equal the
    # demo receipt's digest — the falsifier co-opts the frozen demo certificate.
    demo_receipt = rsp.prune_trace(rsp.demo_scheme(), rsp.demo_trace())
    b = fz.falsifier_B_semantic_skin()
    assert b["digest_skin1"] == demo_receipt.digest
    assert b["digest_skin2"] == demo_receipt.digest


def test_control_rs_uniqueness_holds():
    c = fz.control_numeric_uniqueness_holds()
    # No received word in the swept set yields two in-radius survivors: the
    # numeric two-resolution attack is blocked by 2*tau + k <= n.
    assert c["max_in_radius_candidates"] == 1
    assert c["uniqueness_holds"] is True


def test_overall_verdict():
    result = fz.run()
    assert result["falsifier_fires"] is True
    assert result["rs_uniqueness_intact"] is True

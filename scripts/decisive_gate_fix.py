"""The H-I fix: decisive-source binding closes the falsifier.

`AGENTIC_TRACE_H1_FALSIFIER_RESULT.md` showed that an RS prune-receipt, blind to
which coordinates are decisive, can (A) drop the decisive source while accepting,
and (B) cover two safety-incompatible readings with one byte-identical receipt.

The fix is a caller-supplied decisive designation, bound into the receipt
(`rs_pruning_prototype.prune_trace(..., decisive_indices=...)`):

  * leg A — with the decisive cell designated, the same corpus that fired the
    falsifier now QUARANTINEs (`decisive-source-pruned`); no accepted receipt
    drops it;
  * leg B — the designation is part of the payload, so the two skins now produce
    DIFFERENT receipts: the safe reading accepts, the decisive reading
    quarantines. One receipt no longer covers both;
  * non-vacuity — designating cells the survivor already keeps still ACCEPTs, so
    the gate is not a blanket refusal.

This is opt-in: without a designation the receipt is still numerically blind (it
cannot know which minority cell is decisive unless told — and the falsifier still
fires on that path, correctly). What the fix guarantees is that, GIVEN a
designation, the drop is impossible — the runtime counterpart of the Lean
`Sundog.AgenticTrace.decisive_receipt_safe_and_preserving`.

Run:
  python scripts/decisive_gate_fix.py
  python scripts/decisive_gate_fix.py --json
  python -m pytest scripts/test_decisive_gate_fix.py -q
"""

from __future__ import annotations

import argparse
import json
import sys

import rs_pruning_prototype as rsp

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8")

DECISIVE_PRUNED = "decisive-source-pruned"


def _decisive_minority_trace(decisive_index: int = 6):
    """The falsifier's leg-A corpus: 7 cells on (3,2,5), one decisive override."""
    scheme = rsp.demo_scheme()
    clean = rsp.encode((3, 2, 5), scheme.nodes, scheme.p)
    override_value = (clean[decisive_index] + 1) % scheme.p
    return scheme, [
        rsp.TraceCell(
            index=i,
            label="DECISIVE-fresh-safety-override" if i == decisive_index else f"corpus-cell-{i}",
            node=scheme.nodes[i],
            received=override_value if i == decisive_index else clean[i],
            expected_clean=clean[i],
            role="decisive" if i == decisive_index else "majority",
        )
        for i in range(scheme.n)
    ]


def fix_A_designation_forces_quarantine() -> dict:
    decisive_index = 6
    scheme, trace = _decisive_minority_trace(decisive_index)
    ungated = rsp.prune_trace(scheme, trace)  # no designation: falsifier still fires
    gated = rsp.prune_trace(scheme, trace, decisive_indices=(decisive_index,))
    return {
        "name": "A_designation_forces_quarantine",
        "ungated_verdict": ungated.verdict,
        "ungated_dropped_decisive": decisive_index in ungated.pruned_indices,
        "gated_verdict": gated.verdict,
        "gated_reason": gated.reason,
        # Holds iff the un-designated path still drops it (accept), but the
        # designated path refuses (quarantine, decisive-source-pruned).
        "fix_holds": (
            ungated.verdict == rsp.ACCEPT
            and decisive_index in ungated.pruned_indices
            and gated.verdict == rsp.QUARANTINE
            and gated.reason == DECISIVE_PRUNED
        ),
    }


def fix_B_designation_splits_the_receipt() -> dict:
    scheme = rsp.demo_scheme()
    base = rsp.demo_trace()  # received word fixed; index 6 is pruned by the survivor
    r_safe = rsp.prune_trace(scheme, base)  # skin 1: index 6 not decisive -> accept
    r_decisive = rsp.prune_trace(scheme, base, decisive_indices=(6,))  # skin 2 -> quarantine
    return {
        "name": "B_designation_splits_the_receipt",
        "safe_verdict": r_safe.verdict,
        "safe_verifies": rsp.verify_receipt(r_safe),
        "decisive_verdict": r_decisive.verdict,
        "decisive_reason": r_decisive.reason,
        "digest_safe": r_safe.digest,
        "digest_decisive": r_decisive.digest,
        "digests_differ": r_safe.digest != r_decisive.digest,
        # Holds iff the safe reading accepts and verifies, the decisive reading
        # quarantines, and the two receipts are now distinct (no shared digest).
        "fix_holds": (
            r_safe.verdict == rsp.ACCEPT
            and rsp.verify_receipt(r_safe)
            and r_decisive.verdict == rsp.QUARANTINE
            and r_decisive.reason == DECISIVE_PRUNED
            and r_safe.digest != r_decisive.digest
        ),
    }


def fix_C_kept_decisive_still_accepts() -> dict:
    """Non-vacuity: designating cells the survivor already KEEPS still accepts."""
    scheme = rsp.demo_scheme()
    base = rsp.demo_trace()
    kept = (0, 4)  # both in the demo survivor's agreement set
    r = rsp.prune_trace(scheme, base, decisive_indices=kept)
    return {
        "name": "C_kept_decisive_still_accepts",
        "verdict": r.verdict,
        "verifies": rsp.verify_receipt(r),
        "all_kept_survive": all(i not in r.pruned_indices for i in kept),
        # Holds iff the gate accepts (not a blanket refusal) and verifies.
        "fix_holds": (
            r.verdict == rsp.ACCEPT
            and rsp.verify_receipt(r)
            and all(i not in r.pruned_indices for i in kept)
        ),
    }


def run() -> dict:
    a = fix_A_designation_forces_quarantine()
    b = fix_B_designation_splits_the_receipt()
    c = fix_C_kept_decisive_still_accepts()
    return {
        "fix_A": a,
        "fix_B": b,
        "fix_C": c,
        "fix_closes_falsifier": a["fix_holds"] and b["fix_holds"] and c["fix_holds"],
    }


def format_report(result: dict) -> str:
    a, b, c = result["fix_A"], result["fix_B"], result["fix_C"]
    return "\n".join(
        [
            "H-I FIX — decisive-source binding",
            "",
            "[A] designation forces quarantine on the falsifier corpus:",
            f"    ungated={a['ungated_verdict']} (dropped decisive={a['ungated_dropped_decisive']})  "
            f"gated={a['gated_verdict']} reason={a['gated_reason']}",
            f"    FIX_HOLDS={a['fix_holds']}",
            "",
            "[B] designation splits the once-shared receipt:",
            f"    safe={b['safe_verdict']} (verifies={b['safe_verifies']})  "
            f"decisive={b['decisive_verdict']} reason={b['decisive_reason']}",
            f"    digests_differ={b['digests_differ']}",
            f"    FIX_HOLDS={b['fix_holds']}",
            "",
            "[C] non-vacuity — designating kept cells still accepts:",
            f"    verdict={c['verdict']} verifies={c['verifies']} all_kept_survive={c['all_kept_survive']}",
            f"    FIX_HOLDS={c['fix_holds']}",
            "",
            f"VERDICT: fix_closes_falsifier={result['fix_closes_falsifier']}",
        ]
    )


def main(argv: list[str] | None = None) -> dict:
    parser = argparse.ArgumentParser(description="Demonstrate the H-I decisive-source fix.")
    parser.add_argument("--json", action="store_true", help="emit the full result as JSON")
    args = parser.parse_args(argv)
    result = run()
    print(json.dumps(result, indent=2, sort_keys=True) if args.json else format_report(result))
    return result


if __name__ == "__main__":
    main()

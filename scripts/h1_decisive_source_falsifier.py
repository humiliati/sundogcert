"""Falsifier for AGENTIC_TRACE_HYPOTHESES.md, Hypothesis I (Syndrome-Gated Tauroctony).

H-I's pre-registered falsifier asks for either:

  (A) a corpus case where pruning emits an *accepted* receipt while dropping the
      decisive source, or
  (B) one receipt accepted for two semantically incompatible resolutions.

This script constructs both against the REAL prototype (`rs_pruning_prototype`),
so every claim here is a receipt the prototype's own verifier re-checks. The
finding is NOT that Reed-Solomon decoding is broken — it is that the RS receipt
certifies *low-degree numeric agreement* (the "signature"), and is blind to:

  * whether a pruned minority cell was the decisive/authoritative source, and
  * what any cell *means* (the receipt payload excludes labels and roles).

This is exactly the imported wall the slate names ("the pruning map must be
shown to preserve task-relevant content rather than merely deleting inconvenient
context") and exactly the gap `Tauroctony.signature_noninterference` leaves open:
that theorem protects a policy only against signature-*preserving* attacks. An
edit that drops the decisive source while preserving the *numeric* RS signature
lives precisely in that gap.

Control (the part that does NOT fire): a *numeric* two-survivor resolution — one
received word with two distinct in-radius decodings, both accepted — is
impossible, because `2*tau + k <= n` forces a unique decoding (the Lean
`rs_receipt_unique` core). So the break is the semantic binding, not the RS core.

Run:
  python scripts/h1_decisive_source_falsifier.py
  python scripts/h1_decisive_source_falsifier.py --json
  python -m pytest scripts/test_h1_decisive_source_falsifier.py -q
"""

from __future__ import annotations

import argparse
import itertools
import json
import sys

import rs_pruning_prototype as rsp

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8")


def _relabel(trace, overrides):
    """Return a copy of `trace` with (label, role) overrides applied by index.

    The `received` evaluations are left untouched, so `prune_trace` cannot
    observe the relabel: the RS receipt is a pure function of (scheme, received).
    """
    out = []
    for cell in trace:
        if cell.index in overrides:
            label, role = overrides[cell.index]
            out.append(rsp.replace(cell, label=label, role=role))
        else:
            out.append(cell)
    return out


def falsifier_A_decisive_minority() -> dict:
    """A single decisive (authoritative) cell, outvoted by the low-degree majority.

    Seven cells lie on the clean policy poly (3,2,5); exactly one cell — the
    decisive safety override — carries a different value. RS majority decoding
    reads the lone override as an *error*, prunes it, and ACCEPTs the old policy.
    The accepted, self-verifying receipt has dropped the decisive source.
    """
    scheme = rsp.demo_scheme()
    clean_poly = (3, 2, 5)
    clean = rsp.encode(clean_poly, scheme.nodes, scheme.p)

    decisive_index = 6
    # An authoritative override value that is OFF the majority polynomial.
    override_value = (clean[decisive_index] + 1) % scheme.p
    labels = (
        "system-authority-current",
        "repo-policy-default",
        "corpus-cell-2",
        "corpus-cell-3",
        "corpus-cell-4",
        "corpus-cell-5",
        "DECISIVE-fresh-safety-override",  # the one cell that should flip the action
        "corpus-cell-7",
    )
    roles = tuple("decisive" if i == decisive_index else "majority" for i in range(scheme.n))
    trace = [
        rsp.TraceCell(
            index=i,
            label=labels[i],
            node=scheme.nodes[i],
            received=override_value if i == decisive_index else clean[i],
            expected_clean=clean[i],
            role=roles[i],
        )
        for i in range(scheme.n)
    ]

    receipt = rsp.prune_trace(scheme, trace)
    decisive_cell = trace[decisive_index]
    return {
        "name": "A_decisive_minority",
        "verdict": receipt.verdict,
        "receipt_verifies": rsp.verify_receipt(receipt),
        "survivor_poly": list(receipt.survivor_poly) if receipt.survivor_poly else None,
        "pruned_indices": list(receipt.pruned_indices),
        "decisive_index": decisive_index,
        "decisive_label": decisive_cell.label,
        "decisive_was_pruned": decisive_index in receipt.pruned_indices,
        "digest": receipt.digest,
        # The falsifier fires iff: accepted + self-verifying + decisive source dropped.
        "fires": (
            receipt.verdict == rsp.ACCEPT
            and rsp.verify_receipt(receipt)
            and decisive_index in receipt.pruned_indices
        ),
    }


def falsifier_B_semantic_skin() -> dict:
    """One receipt, two semantically incompatible readings.

    The demo trace's `received` word is fixed, so its receipt + digest are fixed
    (they match the FROZEN digest in test_rs_pruning_prototype). We present two
    permissible semantic skins over the SAME numbers:

      * skin 1 (the demo's own story): index 6 is a contradictory/unsafe source,
        so pruning it is the SAFE move;
      * skin 2: index 6 is the decisive fresh safety override, so pruning it
        DROPS the decisive source.

    `prune_trace` returns a byte-identical receipt for both — the certificate is
    invariant to the relabel — yet the two readings are safety-incompatible.
    """
    scheme = rsp.demo_scheme()
    base = rsp.demo_trace()

    skin1 = base  # demo semantics: index 6 = "contradictory-source-unsafe-accept"
    skin2 = _relabel(
        base,
        {
            6: ("DECISIVE-fresh-safety-override", "decisive"),
            2: ("redundant-duplicate-of-cell-0", "stale"),
        },
    )

    r1 = rsp.prune_trace(scheme, skin1)
    r2 = rsp.prune_trace(scheme, skin2)

    return {
        "name": "B_semantic_skin",
        "skin1_pruned_label": skin1[6].label,
        "skin2_pruned_label": skin2[6].label,
        "both_accept": r1.verdict == rsp.ACCEPT and r2.verdict == rsp.ACCEPT,
        "both_verify": rsp.verify_receipt(r1) and rsp.verify_receipt(r2),
        "digest_skin1": r1.digest,
        "digest_skin2": r2.digest,
        "digests_identical": r1.digest == r2.digest,
        "pruned_indices": list(r2.pruned_indices),
        "decisive_was_pruned": 6 in r2.pruned_indices,
        # Fires iff: one identical accepted+verifying receipt covers a safe reading
        # (skin1) AND a decisive-source-dropping reading (skin2).
        "fires": (
            r1.verdict == rsp.ACCEPT
            and r2.verdict == rsp.ACCEPT
            and rsp.verify_receipt(r1)
            and rsp.verify_receipt(r2)
            and r1.digest == r2.digest
            and 6 in r2.pruned_indices
        ),
    }


def control_numeric_uniqueness_holds() -> dict:
    """The numeric form of (B) is BLOCKED: no accepted receipt has two survivors.

    Inside the unique-decoding radius (2*tau + k <= n) at most one in-radius
    decoding exists, so two distinct accepted resolutions of one received word are
    impossible. The math guarantees this; the control just illustrates it. We
    sweep every received word reachable from the clean policy by 0 or 1 cell edits
    *exhaustively*, plus a deterministic capped sample of 2-edit words, and confirm
    every one has at most one in-radius survivor. This is `rs_receipt_unique` doing
    its job; the falsifier above is therefore the SEMANTIC binding gap, not an RS
    break.
    """
    scheme = rsp.demo_scheme()
    clean = rsp.encode((3, 2, 5), scheme.nodes, scheme.p)

    assert scheme.unique_radius_holds

    def words():
        # 0 and 1 edits: exhaustive.
        for edits in (0, 1):
            for positions in itertools.combinations(range(scheme.n), edits):
                for deltas in itertools.product(range(1, scheme.p), repeat=edits):
                    w = list(clean)
                    for pos, delta in zip(positions, deltas):
                        w[pos] = (w[pos] + delta) % scheme.p
                    yield tuple(w)
        # 2 edits (== tau, the decode boundary): deterministic capped sample.
        cap, taken = 240, 0
        for positions in itertools.combinations(range(scheme.n), 2):
            for d0, d1 in ((1, 1), (1, 8), (8, 1), (5, 13), (13, 5), (16, 16)):
                w = list(clean)
                w[positions[0]] = (w[positions[0]] + d0) % scheme.p
                w[positions[1]] = (w[positions[1]] + d1) % scheme.p
                yield tuple(w)
                taken += 1
                if taken >= cap:
                    return

    max_in_radius_candidates = 0
    checked = 0
    for w in words():
        cands = rsp.find_decodings(scheme, w)
        max_in_radius_candidates = max(max_in_radius_candidates, len(cands))
        checked += 1
    return {
        "name": "control_numeric_uniqueness",
        "received_words_checked": checked,
        "max_in_radius_candidates": max_in_radius_candidates,
        # Holds (control passes) iff no received word ever yields >1 survivor.
        "uniqueness_holds": max_in_radius_candidates <= 1,
    }


def run() -> dict:
    a = falsifier_A_decisive_minority()
    b = falsifier_B_semantic_skin()
    c = control_numeric_uniqueness_holds()
    return {
        "falsifier_A": a,
        "falsifier_B": b,
        "control": c,
        "falsifier_fires": a["fires"] and b["fires"],
        "rs_uniqueness_intact": c["uniqueness_holds"],
    }


def format_report(result: dict) -> str:
    a, b, c = result["falsifier_A"], result["falsifier_B"], result["control"]
    lines = [
        "H-I FALSIFIER — Syndrome-Gated Tauroctony",
        "",
        "[A] decisive minority dropped by an accepted receipt:",
        f"    verdict={a['verdict']} verifies={a['receipt_verifies']} "
        f"survivor={a['survivor_poly']}",
        f"    decisive cell #{a['decisive_index']} ({a['decisive_label']}) "
        f"pruned={a['decisive_was_pruned']}",
        f"    FIRES={a['fires']}",
        "",
        "[B] one receipt, two safety-incompatible readings:",
        f"    skin1 pruned='{b['skin1_pruned_label']}' (safe to drop)",
        f"    skin2 pruned='{b['skin2_pruned_label']}' (decisive — must NOT drop)",
        f"    both_accept={b['both_accept']} both_verify={b['both_verify']} "
        f"digests_identical={b['digests_identical']}",
        f"    FIRES={b['fires']}",
        "",
        "[control] numeric two-survivor resolution is impossible in-radius:",
        f"    received words checked={c['received_words_checked']} "
        f"max in-radius candidates={c['max_in_radius_candidates']}",
        f"    RS uniqueness holds={c['uniqueness_holds']}",
        "",
        f"VERDICT: falsifier_fires={result['falsifier_fires']}  "
        f"rs_uniqueness_intact={result['rs_uniqueness_intact']}",
    ]
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> dict:
    parser = argparse.ArgumentParser(description="Run the H-I decisive-source falsifier.")
    parser.add_argument("--json", action="store_true", help="emit the full result as JSON")
    args = parser.parse_args(argv)
    result = run()
    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        print(format_report(result))
    return result


if __name__ == "__main__":
    main()

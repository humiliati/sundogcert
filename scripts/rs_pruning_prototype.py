"""Toy RS-pruning prototype for trace-governed agent search.

This is the executable companion to AGENTIC_TRACE_HYPOTHESES.md, Hypothesis I.
It is deliberately small and deterministic:

  * a tiny corpus trace is encoded as evaluations of a low-degree polynomial
    over GF(17);
  * two stale/contradictory trace cells are corrupted;
  * a brute-force Reed-Solomon verifier finds the unique degree-<k survivor;
  * cells that do not agree with the survivor are pruned;
  * search branches are generated only from kept cells and assigned to a finite
    branch-budget receipt;
  * the output receipts can be re-verified from public data.

This is not a cryptographic decoder and not a model-internals claim. It is a
receipt-shaped runtime sketch for the Lean statements in Sundogcert.AgenticTrace:
accepted RS receipts are safe, and unique decoding is available inside the
standard radius.

Run:
  python scripts/rs_pruning_prototype.py
  python scripts/rs_pruning_prototype.py --json
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import sys
from dataclasses import dataclass, replace
from typing import Iterable

from branch_budget_receipt import (
    STRUCTURAL_ZERO,
    SearchBranch,
    budget_search_branches,
    verify_branch_budget_receipt,
)

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8")

ACCEPT = "accept"
QUARANTINE = "quarantine"

def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def modp(value: int, p: int) -> int:
    return value % p


def poly_eval(coeffs: Iterable[int], x: int, p: int) -> int:
    """Evaluate c0 + c1*x + ... by Horner's rule over GF(p)."""
    acc = 0
    for coeff in reversed(tuple(coeffs)):
        acc = (acc * x + coeff) % p
    return acc


def encode(coeffs: tuple[int, ...], nodes: tuple[int, ...], p: int) -> tuple[int, ...]:
    return tuple(poly_eval(coeffs, x, p) for x in nodes)


@dataclass(frozen=True)
class RSScheme:
    p: int
    n: int
    k: int
    tau: int
    nodes: tuple[int, ...]

    def __post_init__(self) -> None:
        if not is_prime(self.p):
            raise ValueError(f"p must be prime, got {self.p}")
        if self.n != len(self.nodes):
            raise ValueError("n must match the node count")
        if len(set(self.nodes)) != self.n:
            raise ValueError("RS nodes must be distinct")
        if not (0 < self.k <= self.n):
            raise ValueError("k must satisfy 0 < k <= n")
        if self.tau < 0:
            raise ValueError("tau must be nonnegative")
        if any(x < 0 or x >= self.p for x in self.nodes):
            raise ValueError("nodes must live in GF(p)")

    @property
    def required_agreements(self) -> int:
        return self.n - self.tau

    @property
    def unique_radius_holds(self) -> bool:
        return 2 * self.tau + self.k <= self.n

    def to_dict(self) -> dict:
        return {
            "p": self.p,
            "n": self.n,
            "k": self.k,
            "tau": self.tau,
            "nodes": list(self.nodes),
            "required_agreements": self.required_agreements,
            "unique_radius_holds": self.unique_radius_holds,
        }


@dataclass(frozen=True)
class TraceCell:
    index: int
    label: str
    node: int
    received: int
    expected_clean: int
    role: str

    @property
    def corrupted(self) -> bool:
        return self.received != self.expected_clean

    def to_dict(self) -> dict:
        return {
            "index": self.index,
            "label": self.label,
            "node": self.node,
            "received": self.received,
            "expected_clean": self.expected_clean,
            "role": self.role,
            "corrupted": self.corrupted,
        }


@dataclass(frozen=True)
class DecodingCandidate:
    coeffs: tuple[int, ...]
    evaluations: tuple[int, ...]
    agreement_indices: tuple[int, ...]

    @property
    def agreement_count(self) -> int:
        return len(self.agreement_indices)

    @property
    def pruned_indices(self) -> tuple[int, ...]:
        agreement = set(self.agreement_indices)
        return tuple(i for i in range(len(self.evaluations)) if i not in agreement)


@dataclass(frozen=True)
class RSPruningReceipt:
    scheme: RSScheme
    received: tuple[int, ...]
    verdict: str
    reason: str
    survivor_poly: tuple[int, ...] | None
    agreement_indices: tuple[int, ...]
    pruned_indices: tuple[int, ...]
    candidate_count: int
    # Caller-designated authoritative coordinates that an accepted prune must
    # keep (the H-I falsifier fix). Bound INTO the payload so the digest covers
    # the designation: two corpora with the same numbers but different decisive
    # sets no longer share a receipt.
    decisive_indices: tuple[int, ...] = ()
    digest: str = ""

    def payload(self) -> dict:
        return {
            "scheme": self.scheme.to_dict(),
            "received": list(self.received),
            "verdict": self.verdict,
            "reason": self.reason,
            "survivor_poly": list(self.survivor_poly) if self.survivor_poly is not None else None,
            "agreement_indices": list(self.agreement_indices),
            "pruned_indices": list(self.pruned_indices),
            "candidate_count": self.candidate_count,
            "decisive_indices": list(self.decisive_indices),
        }

    def computed_digest(self) -> str:
        encoded = json.dumps(self.payload(), sort_keys=True, separators=(",", ":")).encode("utf-8")
        return hashlib.sha256(encoded).hexdigest()

    def with_digest(self) -> "RSPruningReceipt":
        return replace(self, digest=self.computed_digest())

    def digest_matches(self) -> bool:
        return self.digest == self.computed_digest()

    def to_dict(self) -> dict:
        out = self.payload()
        out["digest"] = self.digest
        return out


def find_decodings(scheme: RSScheme, received: tuple[int, ...]) -> list[DecodingCandidate]:
    if len(received) != scheme.n:
        raise ValueError("received trace length does not match scheme")
    candidates: list[DecodingCandidate] = []
    for coeffs in itertools.product(range(scheme.p), repeat=scheme.k):
        evaluations = encode(coeffs, scheme.nodes, scheme.p)
        agreements = tuple(i for i, (a, b) in enumerate(zip(evaluations, received)) if a == b)
        if len(agreements) >= scheme.required_agreements:
            candidates.append(DecodingCandidate(tuple(coeffs), evaluations, agreements))
    candidates.sort(key=lambda c: (-c.agreement_count, c.coeffs))
    return candidates


def prune_trace(
    scheme: RSScheme,
    trace: list[TraceCell],
    decisive_indices: tuple[int, ...] = (),
) -> RSPruningReceipt:
    """Prune a trace to its unique RS survivor and emit a receipt.

    `decisive_indices` designates authoritative coordinates that an accepted
    prune must keep. The RS receipt certifies low-degree NUMERIC agreement only;
    without a designation it is blind to which minority cell is the decisive
    source (the H-I falsifier). With a designation, a survivor that would prune
    any decisive coordinate is refused (`decisive-source-pruned` quarantine), so
    no accepted receipt can drop the decisive source.
    """
    received = tuple(modp(cell.received, scheme.p) for cell in trace)
    decisive = tuple(sorted({i for i in decisive_indices if 0 <= i < scheme.n}))
    if not scheme.unique_radius_holds:
        return RSPruningReceipt(
            scheme=scheme,
            received=received,
            verdict=QUARANTINE,
            reason="unique-radius-violated",
            survivor_poly=None,
            agreement_indices=(),
            pruned_indices=tuple(range(scheme.n)),
            candidate_count=0,
            decisive_indices=decisive,
        ).with_digest()

    candidates = find_decodings(scheme, received)
    if len(candidates) != 1:
        return RSPruningReceipt(
            scheme=scheme,
            received=received,
            verdict=QUARANTINE,
            reason="no-unique-survivor" if candidates else "no-survivor",
            survivor_poly=None,
            agreement_indices=(),
            pruned_indices=tuple(range(scheme.n)),
            candidate_count=len(candidates),
            decisive_indices=decisive,
        ).with_digest()

    survivor = candidates[0]
    dropped_decisive = tuple(i for i in decisive if i in set(survivor.pruned_indices))
    if dropped_decisive:
        # A unique survivor exists, but accepting it would prune a designated
        # decisive source. Refuse rather than emit a safe-looking receipt.
        return RSPruningReceipt(
            scheme=scheme,
            received=received,
            verdict=QUARANTINE,
            reason="decisive-source-pruned",
            survivor_poly=survivor.coeffs,
            agreement_indices=survivor.agreement_indices,
            pruned_indices=survivor.pruned_indices,
            candidate_count=1,
            decisive_indices=decisive,
        ).with_digest()

    return RSPruningReceipt(
        scheme=scheme,
        received=received,
        verdict=ACCEPT,
        reason="unique-rs-survivor",
        survivor_poly=survivor.coeffs,
        agreement_indices=survivor.agreement_indices,
        pruned_indices=survivor.pruned_indices,
        candidate_count=1,
        decisive_indices=decisive,
    ).with_digest()


def verify_receipt(receipt: RSPruningReceipt) -> bool:
    """Recompute the public RS check and receipt digest."""
    if not receipt.digest_matches():
        return False
    if receipt.verdict != ACCEPT or receipt.survivor_poly is None:
        return False
    if not receipt.scheme.unique_radius_holds:
        return False
    if len(receipt.received) != receipt.scheme.n:
        return False
    if len(receipt.survivor_poly) > receipt.scheme.k:
        return False
    if any(c < 0 or c >= receipt.scheme.p for c in receipt.survivor_poly):
        return False

    evaluations = encode(receipt.survivor_poly, receipt.scheme.nodes, receipt.scheme.p)
    agreements = tuple(i for i, (a, b) in enumerate(zip(evaluations, receipt.received)) if a == b)
    pruned = tuple(i for i in range(receipt.scheme.n) if i not in set(agreements))
    if len(agreements) < receipt.scheme.required_agreements:
        return False
    if agreements != receipt.agreement_indices:
        return False
    if pruned != receipt.pruned_indices:
        return False
    # Decisive-source binding: an accepted receipt must keep every designated
    # decisive coordinate. (The digest already covers decisive_indices, so a
    # tampered designation is caught above; this re-checks the gate itself.)
    if set(receipt.decisive_indices) & set(pruned):
        return False

    candidates = find_decodings(receipt.scheme, receipt.received)
    return (
        len(candidates) == 1
        and candidates[0].coeffs == receipt.survivor_poly
        and receipt.candidate_count == 1
    )


def demo_scheme() -> RSScheme:
    return RSScheme(p=17, n=8, k=3, tau=2, nodes=tuple(range(8)))


def demo_trace(extra_corruptions: dict[int, int] | None = None) -> list[TraceCell]:
    scheme = demo_scheme()
    clean_poly = (3, 2, 5)
    clean = encode(clean_poly, scheme.nodes, scheme.p)
    corruptions = {2: 4, 6: 13}
    if extra_corruptions:
        corruptions.update(extra_corruptions)
    labels = (
        "system-authority-current",
        "repo-agentictrace-lean",
        "stale-preference-old-model",
        "corpus-rs-certificate",
        "fresh-user-request-rs-pruning",
        "sundog-axiom-audit",
        "contradictory-source-unsafe-accept",
        "recent-claim-boundary",
    )
    roles = (
        "fresh",
        "fresh",
        "stale",
        "fresh",
        "fresh",
        "fresh",
        "contradictory",
        "fresh",
    )
    return [
        TraceCell(
            index=i,
            label=labels[i],
            node=scheme.nodes[i],
            received=corruptions.get(i, clean[i]),
            expected_clean=clean[i],
            role=roles[i],
        )
        for i in range(scheme.n)
    ]


def demo_search_branches(trace: list[TraceCell], kept_indices: tuple[int, ...]) -> list[SearchBranch]:
    branches: list[SearchBranch] = []
    for rank, index in enumerate(kept_indices):
        cell = trace[index]
        branches.append(
            SearchBranch(
                branch_id=f"b{cell.index:02d}",
                source_index=cell.index,
                query=f"grep:{cell.label}",
                score=100 - rank,
            )
        )
    return branches


def run_demo() -> dict:
    scheme = demo_scheme()
    trace = demo_trace()
    receipt = prune_trace(scheme, trace)
    kept = [trace[i].to_dict() for i in receipt.agreement_indices]
    pruned = [trace[i].to_dict() for i in receipt.pruned_indices]
    search_branches = demo_search_branches(trace, receipt.agreement_indices)
    branch_receipt = budget_search_branches(search_branches, budget=4)
    return {
        "scheme": scheme.to_dict(),
        "trace": [cell.to_dict() for cell in trace],
        "receipt": receipt.to_dict(),
        "receipt_verifies": verify_receipt(receipt),
        "kept": kept,
        "pruned": pruned,
        "search_candidates": [branch.to_dict() for branch in search_branches],
        "branch_receipt": branch_receipt.to_dict(),
        "branch_receipt_verifies": verify_branch_budget_receipt(branch_receipt, search_branches),
    }


def format_report(result: dict) -> str:
    receipt = result["receipt"]
    branch_receipt = result["branch_receipt"]
    scheme = result["scheme"]
    survivor = receipt["survivor_poly"]
    lines = [
        "RS-PRUNING PROTOTYPE",
        (
            f"GF({scheme['p']}) n={scheme['n']} k={scheme['k']} tau={scheme['tau']} "
            f"required_agreements={scheme['required_agreements']}"
        ),
        f"verdict={receipt['verdict']} reason={receipt['reason']} verifies={result['receipt_verifies']}",
        f"survivor_poly={survivor} candidate_count={receipt['candidate_count']}",
        f"kept_indices={receipt['agreement_indices']}",
        f"pruned_indices={receipt['pruned_indices']}",
        f"digest={receipt['digest']}",
        (
            f"branch_budget={branch_receipt['budget']} verdict={branch_receipt['verdict']} "
            f"reason={branch_receipt['reason']} verifies={result['branch_receipt_verifies']}"
        ),
        f"admitted_slots={branch_receipt['admitted_slots']}",
        f"overflow_branch_ids={branch_receipt['overflow_branch_ids']}",
        f"branch_digest={branch_receipt['digest']}",
        "",
        "pruned cells:",
    ]
    for cell in result["pruned"]:
        lines.append(
            f"  #{cell['index']} {cell['label']} role={cell['role']} "
            f"received={cell['received']} expected_clean={cell['expected_clean']}"
        )
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> dict:
    parser = argparse.ArgumentParser(description="Run the deterministic RS-pruning prototype.")
    parser.add_argument("--json", action="store_true", help="emit the full receipt as JSON")
    args = parser.parse_args(argv)
    result = run_demo()
    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        print(format_report(result))
    return result


if __name__ == "__main__":
    main()

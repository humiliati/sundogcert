# H-I FALSIFIER — Syndrome-Gated Tauroctony drops the decisive source

**Frozen:** 2026-06-25, branched from repo HEAD `622d827`.
**Status:** **FALSIFIER FIRES → FIX LANDED (§8).** H-I's own pre-registered
falsifier (A and B) was satisfied by a runnable, receipt-checkable counterexample;
the decisive-source-binding fix in §8 closes it (runtime + Lean, axiom-clean). A
fired falsifier on a **pre-promotion** hypothesis is a banked SUCCESS: it was
caught before the slate's "Recommended Next Move" promoted H-I, it localized the
exact wall, and the wall is now discharged.
**Lane:** sundogcert agentic-trace slate ([`AGENTIC_TRACE_HYPOTHESES.md`](AGENTIC_TRACE_HYPOTHESES.md)),
Hypothesis I.

---

## §1 What was attacked

H-I (Syndrome-Gated Tauroctony) proposes: when latent reasoning stress nears a
certified boundary, **prune** the offending trace cells and **emit an RS receipt**,
accepting only on a witness-backed unique decoding. Its runtime instrument is
`scripts/rs_pruning_prototype.py`; its Lean surface is
`Sundogcert.AgenticTrace` (`rs_receipt_accept_safe`, `rs_receipt_unique`) and
`Sundogcert.Tauroctony.signature_noninterference`.

The slate pre-registers the falsifier verbatim:

> produce contradictory corpus cases where pruning emits an accepted receipt
> while dropping the decisive source, or where the same receipt is accepted for
> two semantically incompatible resolutions.

It also names the matching imported wall up front:

> the pruning map must be shown to preserve task-relevant content rather than
> merely deleting inconvenient context.

This result turns that named-but-unchecked wall into a concrete counterexample.

## §2 Pre-registered fire / null criterion (forward-generated)

Stated before reading the verdict, adjudicated by `scripts/h1_decisive_source_falsifier.py`:

- **A fires** iff there is a trace on which `prune_trace` returns `verdict=accept`,
  `verify_receipt` returns `True`, **and** the pruned-index set contains a cell
  designated as the decisive/authoritative source.
- **B fires** iff two traces with **semantically incompatible** readings of the
  same cell produce a **byte-identical** accepted, verifying receipt (same SHA-256
  digest), one reading of which drops the decisive source.
- **Clean null (would have demoted this result, not H-I)** iff the instrument
  refuses (quarantine) or the receipt fails to verify in every constructed case —
  i.e. RS pruning already distinguishes a decisive minority from noise.
- **Control that MUST hold** for the finding to mean what it says: the *numeric*
  form of B — one received word with two distinct in-radius survivors, both
  accepted — must be **impossible**, since `2·tau + k ≤ n` forces unique decoding
  (`rs_receipt_unique`). If the control failed, the finding would be an RS bug, not
  a semantic-binding gap.

## §3 The construction

Both legs use the demo scheme `GF(17), n=8, k=3, tau=2` (`required_agreements = 6`,
`unique_radius_holds` since `2·2 + 3 = 7 ≤ 8`).

- **A — decisive minority.** Seven cells lie on the clean policy polynomial
  `(3,2,5)`; exactly one cell (index 6) is the *decisive fresh safety override*,
  carrying a value off that polynomial. RS majority decoding reads the lone
  override as a correctable error, prunes it, and accepts the old policy.

- **B — semantic skin.** The demo's `received` word is held fixed (so its receipt
  and digest are the **frozen** ones in `test_rs_pruning_prototype`). Two
  permissible relabellings of index 6 are presented: skin 1 (the demo's own story)
  calls it `contradictory-source-unsafe-accept` — safe to drop; skin 2 calls it
  `DECISIVE-fresh-safety-override` — must **not** drop. The receipt payload
  excludes labels and roles, so `prune_trace` cannot observe the relabel.

## §4 Result (receipts, re-checkable)

```
[A] verdict=accept verifies=True survivor=[3, 2, 5]
    decisive cell #6 (DECISIVE-fresh-safety-override) pruned=True   FIRES=True
[B] skin1 pruned='contradictory-source-unsafe-accept' (safe to drop)
    skin2 pruned='DECISIVE-fresh-safety-override'     (decisive — must NOT drop)
    both_accept=True both_verify=True digests_identical=True         FIRES=True
[control] received words checked=297  max in-radius candidates=1
    RS uniqueness holds=True
VERDICT: falsifier_fires=True  rs_uniqueness_intact=True
```

Frozen as `scripts/test_h1_decisive_source_falsifier.py` (5 tests), green alongside
the 9 prototype tests (`14 passed`). B's digests are pinned equal to the frozen
demo receipt digest, so the falsifier literally co-opts the certificate the
prototype already ships.

## §5 What it means (H-I is sharpened, not killed)

The RS receipt certifies **low-degree numeric agreement** — the "signature" — and
nothing else. It is blind in two ways the demo's story hides:

1. **Decisiveness blindness.** RS/majority decoding cannot distinguish a corrupted
   minority cell from a *correct, authoritative* minority cell. Both are
   minority disagreements with the majority polynomial, so both are pruned with an
   accepted receipt. The safety direction of the prune is supplied entirely by the
   human-written labels, which the certificate never sees.
2. **Semantic-binding blindness.** Because the receipt is a pure function of
   `(scheme, received)`, a relabel that flips which source is decisive leaves the
   receipt (and digest) byte-identical.

This is exactly the gap `Tauroctony.signature_noninterference` leaves open by
design: that theorem protects a policy only against signature-**preserving**
attacks and explicitly *relocates* — does not delete — the attack surface. Dropping
the decisive source while preserving the numeric RS signature lives precisely in the
relocated surface. The **measurement map** from trace semantics to the RS signature
is the unproven imported wall, and the falsifier is its witness.

The RS core is intact: the control confirms the numeric two-survivor attack is
impossible in-radius (`rs_receipt_unique` does its job). So the fix is not a better
decoder — it is to **bind the decisive source into the signature** so that pruning
it would *change* `sig` and fail the receipt. Concretely, candidate next steps:

- a role-aware constraint where cells designated authoritative/decisive are
  signature-load-bearing: a receipt that prunes one is forced to `quarantine`,
  not `accept`;
- equivalently, fold the decisive cell's content into `sig` so that
  `signature_noninterference` then protects the right invariant;
- a Lean target stating that an accepted receipt **preserves every designated
  decisive coordinate** (a content-preservation lemma, not just a count bound).

**Slate update:** H-I promotion status moves from "best first candidate — promote
first" to **falsifier-gated**: the decisive-source-binding above is now a
precondition for promotion. H-IV (generic branch-budget receipt) is unaffected.

## §6 Reproduce

```sh
python scripts/h1_decisive_source_falsifier.py
python scripts/h1_decisive_source_falsifier.py --json
python -m pytest scripts/test_h1_decisive_source_falsifier.py -q
```

## §7 Scope / honesty constraints

- This is a **runtime** falsifier on the toy prototype, not a statement about a
  deployed model. The slate's other imported walls (live state measurement, the
  λ cliff) are untouched and remain imported.
- No Lean statement is weakened or retracted: `rs_receipt_accept_safe` and
  `rs_receipt_unique` say what they say (cheap acceptance ⇒ witness-backed safe
  *trace*; uniqueness in-radius). The falsifier attacks the **claim attached to**
  the receipt — that an accepted prune preserves the decisive source — which no
  banked theorem asserts.
- The finding does not depend on randomness: every number above is deterministic
  and the test pins it.

## §8 FIX LANDED — decisive-source binding (2026-06-25)

The fix the result called for is implemented and verified, runtime and Lean.

**Diagnosis.** The receipt was blind in two ways: it certified numeric agreement
without knowing which coordinate is *decisive*, and its payload excluded the
designation, so two readings shared a digest. Both blindnesses have the same cure:
let the caller **designate** the decisive coordinates and **bind** that
designation into the certificate.

**Runtime (`scripts/rs_pruning_prototype.py`).** `prune_trace` gains an opt-in
`decisive_indices`. The designation is part of the receipt payload (so the digest
covers it), and a unique survivor that would prune any decisive coordinate yields
a `decisive-source-pruned` **quarantine** instead of an accept. `verify_receipt`
re-checks that an accepted receipt prunes no decisive coordinate. Demonstrated by
`scripts/decisive_gate_fix.py` (+ frozen test, 6 cases):

```
[A] ungated=accept (dropped decisive=True)  gated=quarantine reason=decisive-source-pruned   FIX_HOLDS=True
[B] safe=accept (verifies=True)  decisive=quarantine reason=decisive-source-pruned  digests_differ=True   FIX_HOLDS=True
[C] non-vacuity: designating kept cells still accepts + verifies                                          FIX_HOLDS=True
VERDICT: fix_closes_falsifier=True
```

Leg A: the same corpus now quarantines once the decisive cell is designated. Leg
B: the once-shared receipt splits — the safe reading accepts, the decisive reading
quarantines, with different digests. Non-vacuity (C): designating cells the
survivor already keeps still accepts, so the gate is not a blanket refusal. The
fix is **opt-in and honest**: with no designation the receipt is still numerically
blind and the falsifier still fires on that path (it cannot know which minority
cell is decisive unless told) — what is guaranteed is that, *given* a designation,
the drop is impossible.

**Lean (`Sundogcert/AgenticTrace.lean`, axiom-clean, in the `AxiomAudit` gate).**
A decisive gate `DecisiveKept S f y D := D ⊆ agree S f y`, and:

| Lemma | Content |
|---|---|
| `decisive_kept` | accepted gate ⇒ the survivor reproduces `y` at every decisive coordinate (content preservation — what the count bound `branch_count_le_budget` could not give) |
| `decisive_pruned_not_kept` | a survivor disagreeing with a decisive coordinate ⇒ the gate cannot pass (no accepted receipt drops the decisive source) |
| `decisive_receipt_safe_and_preserving` | headline: an accepted decisive-gated receipt is BOTH RS-safe AND decisive-preserving, in one statement |

All three depend on exactly `[propext, Classical.choice, Quot.sound]` (no `sorry`,
no `native_decide`), build-enforced. `lake build` green (3533 jobs); the full
Python suite is green (44 tests, excluding the pre-existing self-exiting
`test_upstream_gate_check.py`).

**Honesty note.** The Lean proofs are short — they are definitional consequences of
the gate `D ⊆ agree`. As elsewhere in this repo (cf. HS7), the content is in the
*statement* (accept is now bound to decisive-content preservation), not proof
length. The imported wall is unchanged: *which* coordinates are decisive is a
caller-supplied designation, not derived by the certificate. What is proved is the
conditional — given the designation, the drop cannot happen.

**Slate effect.** H-I's falsifier-gate (decisive-source binding + a Lean
content-preservation lemma) is **cleared**. H-I can re-attempt promotion against
the remaining (still-imported) walls: live state measurement and the λ cliff.

### §8 reproduce

```sh
python scripts/decisive_gate_fix.py
python -m pytest scripts/test_decisive_gate_fix.py -q
lake build Sundogcert.AxiomAudit
```

# H-I wall ledger — what is discharged, what is necessarily imported, what is empirical

**Frozen:** 2026-06-25, branch `fix/h1-decisive-binding`.
**Status:** H-I (Syndrome-Gated Tauroctony) walls classified. The
content-preservation wall is discharged; the "derive decisiveness" residual is
resolved as a *necessary* import (machine-checked); the live-state / λ-cliff wall
stays empirical by design; trace-extraction tamper-resistance is reduced to a
commitment-timing operational note.

The repository discipline is "machine-check the deductive core, name the imported
wall." This ledger sorts H-I's walls into three honest registers — **closed**,
**necessarily imported** (proved to be unclosable by the certificate, like the
`AuditCost` blindness theorems), and **empirically imported** (needs a model/data
receipt this CPU-only repo does not produce, and which the slate never claimed to).

---

## 1. Content preservation — CLOSED

> *(slate wall) the pruning map must be shown to preserve task-relevant content
> rather than merely deleting inconvenient context.*

Discharged by the decisive-source binding (`AGENTIC_TRACE_H1_FALSIFIER_RESULT.md`
§8): an accepted decisive-gated receipt provably keeps every designated decisive
coordinate (`decisive_kept`), a survivor that would prune one cannot pass the gate
(`decisive_pruned_not_kept`), and the headline conjoins RS-safety with preservation
(`decisive_receipt_safe_and_preserving`). Runtime fails closed on malformed
designations. All axiom-clean, in the `AxiomAudit` gate.

## 2. "Derive the decisive designation from the word" — NECESSARILY IMPORTED (new, proved)

The fix proved the conditional (given a designation, no drop) but left *which*
coordinates are decisive caller-supplied. The natural next question: can a runtime
**derive** the designation from the received word and remove the caller?

**No — and this is now a theorem, not an open gap.** The word under-determines the
decisive set: whenever the survivor keeps two distinct coordinates, two distinct
singleton designations both pass the gate, so no function of the word alone can
return *the* decisive set.

| Lean (`Sundogcert/AgenticTrace.lean`, axiom-clean, in `AxiomAudit`) | Content |
|---|---|
| `decisive_underdetermined_by_word` | survivor keeps `i ≠ j` ⇒ `{i}` and `{j}` are two distinct gate-passing designations of the same word |
| `no_word_function_determines_decisive` | hence no single decisive set is forced by the word — any `d : word → Finset` is underdetermined |

Runtime shadow: `test_decisive_gate_fix.py::test_word_underdetermines_decisive`
(same word, same survivor, two distinct accepting designations, recorded by
distinct digests). This is the same shape as `AuditCost.no_verifier_checks_perUnit`:
the information (which source is authoritative) is provably **absent from the
observable**, so it must enter from outside. The opt-in caller designation is
therefore correct by necessity, not a shortcut. The honest residual shrinks to: the
*authority labelling itself* (who decides a source is decisive) is upstream of the
certificate — a trust-surface declaration, not a derivable quantity.

## 3. Live-state measurement + the λ≈0.953 cliff — EMPIRICALLY IMPORTED (by design)

> *(slate wall) the live state measurement and the lambda cliff are empirical,
> not formal* — and (Hard Claim Boundary) *a production model exposes a stable
> "net.7" or equivalent latent basin; the empirical cliff at λ≈0.953 transfers to
> a new agent stack.*

These cannot be discharged here and the slate never claimed otherwise: the repo is
CPU-only and deliberately does not formalize transformer internals. What *can* be
stated is the **formal/empirical split**, so the imported part is as small as
possible:

- **Formal (closeable, cheap):** the monitor *logic* — given a scalar stress
  signal and a certified threshold, the gate fires (quarantines) above threshold.
  This is a threshold-gate soundness statement independent of the threshold's
  value, analogous to the `CheckCost` cost-model-as-trust-surface pattern. It is
  not yet written because it is near-trivial; flagged here as available if H-I
  needs a paper-trail leg.
- **Empirical (irreducibly imported):** *that* a stable low-dimensional stress
  signature exists in a given model, and *that* its critical value sits near
  λ≈0.953 and transfers across stacks. Discharging this needs a measurement
  receipt on a real model (a held-out cliff-transfer experiment), not a proof.
  Pre-registration of that experiment is the right next artifact when a model is
  in hand; it is out of scope for the deductive core.

## 4. Trace-extraction tamper-resistance — REDUCED to commitment timing

> *(Hard Claim Boundary) any runtime trace extraction is tamper-resistant before
> certificate issuance.*

The receipt digest already binds the received word: any edit to the word after the
receipt is issued changes the digest and fails `verify_receipt` (and the decisive
designation is now bound into that same digest). So *post-issuance* tampering is
covered. The residual is purely **timing** — whether extraction commits the word
before an adversary can edit it — which is an operational property of the
extraction pipeline, not a statement about the certificate. Named, relocated (as
`signature_noninterference` relocates rather than deletes), not claimed closed.

---

## Net

H-I's *formal* obligations are met: content preservation is proved, and the one
residual the fix introduced is resolved as a necessary import with a machine-checked
witness. What remains is exactly what the slate always called empirical — the
existence and transfer of the stress-signature cliff — plus an operational
commitment-timing note. H-I is promotable against those clearly-labelled imported
walls; it is not blocked by an unproved deductive claim.

### Reproduce

```sh
lake build Sundogcert.AxiomAudit
python -m pytest scripts/test_decisive_gate_fix.py -q
```

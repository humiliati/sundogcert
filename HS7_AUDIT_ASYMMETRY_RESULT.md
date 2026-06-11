# HS7 RESULT — Audit-asymmetry certificate: LANDED

**Run:** 2026-06-10 (same day as the prereg freeze `37d3306`; the K1 box ran to end of 2026-06-12).
**Prereg:** `HS7_AUDIT_ASYMMETRY_PREREG.md` (frozen before any Lean existed).
**Outcome: LANDED.** Both kills survived: K1 (time-box) passed with ~2 days to spare; K2
(structure audit) passed — table below. All pinned theorems proved, axiom-clean, build-enforced.

---

## What was proved (`Sundogcert/AuditCost.lean`)

One finite setting: `u : Fin n → ℚ`, channel `(report, pooledMean u)`, statistics as finite sums,
no `Measure ℝ`.

| Theorem | Statement (one line) |
|---|---|
| `audit_sound` / `audit_complete` | no false report accepts; the honest report always accepts |
| `honest_accepts` / `dishonest_caught` | the same, over adversarial reporter *strategies* |
| `auditCost_eq` / `auditCost_le` | the audit costs exactly `n + (n−1) + 2` ops; `≤ 3n + 2` |
| `pooled_channel_blind` | ∀ decidable `A : ℚ×ℚ → Bool`, ∀ coordinate `i`, ∀ prescribed `δ`: an explicit same-mean `u'` (`bump`) has `u' i = u i + δ` and identical `A`-verdicts for every report |
| `no_channel_verifier_decides` | a pooled-mean fiber pair on which `P` differs kills every sound-and-complete channel verifier for `P` |
| `no_verifier_checks_perUnit` | no channel verifier is sound-and-complete for any per-unit claim `u i = v` |
| `n1_channel_determines` | at `n = 1` the channel DETERMINES the unit — blindness needs `n ≥ 2`, it is not generic |
| `secondMoment_separates` | the same fiber pair is separated by `x ↦ x²` — the information is present one statistic up; the channel is what is blind |
| `audit_asymmetry` | HEADLINE: full access decides every report at linear cost ∧ every pooled-channel verifier is per-unit blind |

**Build:** `lake build` green, **3530 jobs, 0 warnings**. Five new `AxiomAudit.lean` guards
(`audit_sound`, `auditCost_le`, `pooled_channel_blind`, `no_verifier_checks_perUnit`,
`audit_asymmetry`) pass with the exact foundational triple `[propext, Classical.choice,
Quot.sound]`; all ten public theorems were checked to carry exactly that triple (no `sorryAx`, no
`native_decide`).

## K1 — time-box: PASSED

The load-bearing pair (`pooled_channel_blind`, `no_verifier_checks_perUnit`) was proved
axiom-clean on the freeze day. No banked "harder than the tower suggests" finding.

## K2 — structure audit: PASSED

**Witness criterion (from the prereg):** the headline must contain quantification over ALL
decidable channel verifiers combined with explicit fiber-pair existence at prescribed per-unit δ,
appearing in no banked statement on the pinned list.

The headline's quantifier shape: `∀ A : ℚ × ℚ → Bool, ∀ u i δ, ∃ u' (explicit: bump u i j δ),
(equal pooled mean) ∧ (u' i = u i + δ) ∧ ∀ r, A-verdict equality`.

| Pinned banked statement | Quantifier shape | ∀-verifier? | prescribed-δ fiber pair + verdict clause? |
|---|---|---|---|
| `accept_sound` / `reject_sound` / `no_passing_unsafe` | ∀ body, for ONE verifier `V` given as a structure parameter | no — soundness OF a fixed verifier | no |
| `verifyCost_le` | cost inequality for the deployed verifier | no | no |
| `resistance_general` | ∀ measure with `charFun → 0`: ONE statistic's limit is 0 | no | no |
| `determination_general` | one integral identity | no | no |
| `gaussian_resist_and_determine` | conjunction instantiated at the Gaussian | no | no |
| `cauchy_is_separator` | two properties of one measure | no | no |
| `twoPoint_shadow_survives` | ¬(one statistic tends to 0) for the lattice | no | no |
| `resist_orthogonal_to_variance` | conjunction over two named measures | no | no |
| `sat_iff_decodes` | reduction iff | no | no |

No pinned statement contains a verifier variable of any kind, so the headline cannot be produced
from any of them by renaming or specialization. **Nearest neighbor beyond the pinned list,
disclosed:** `secret_fiber_eq_univ` (Certificate.lean) is the repo's one fiber-flavored statement —
the syndrome is constant in the secret, fiber = whole space. It quantifies over no verifier, has no
prescribed-difference control, and no verdict clause; the delta is exactly the ∀-verifier layer,
the prescribed-δ construction, and the audit-game/cost pairing.

**Proof lengths (pinned honesty clause):** `pooled_channel_blind` is 4 tactic lines over 3
construction lemmas (~12 lines total); `no_channel_verifier_decides` is 7 lines. Short, as the
prereg pre-stated: data processing is short; the content adjudicated by K2 is the statement, not
the proof.

## Consistency lock (NOT a kill): GREEN

`scripts/audit_cost_check.py` + frozen test `scripts/test_audit_cost_check.py` (**6/6**,
deterministic, exact rationals, SEED 20260610):

| n | measured ops (as performed) | Lean `auditCost` | bound `3n+2` |
|---|---|---|---|
| 8 | 17 | 17 | 26 |
| 64 | 129 | 129 | 194 |
| 512 | 1025 | 1025 | 1538 |

Accept and reject paths cost identically; verdicts match the reference predicate; the `bump`
fiber-pair laws hold numerically; the n = 8 toy matches the Lean example (mean 31/8).

## Deviations from the prereg

1. **Toy instance proof tactic:** `decide` → `norm_num` (the n = 8 examples). Kernel `decide` got
   stuck reducing `ℚ` arithmetic (`Int.decEq`-level match stuck). Pre-authorized by prereg §3
   ("may be replaced by `norm_num` or `rfl` without prejudice"). Statements unchanged.
2. **Additive helpers** not in the pinned table: `ReporterStrategy`, `Honest`, `honest_accepts`,
   `fin_nontrivial`, `empStat`, `sumReadCost`. Additions only; no pinned statement drifted.

No material deviations. K2 was run against the statements exactly as pinned.

## Scope (restated from the module header)

The blindness certifies the **pooled observable**: a reporter with per-unit access can still
encode per-unit facts in the report; the theorem says no verifier can *check* such a claim against
the pooled observable — not that reports carry no information. The artifact is a finite
rational-mean channel — the certified template for audit-asymmetry claims; not a claim about
trained systems, and not "introspection". The cost model is a trust-surface item (CheckCost.lean
precedent), audited not self-proved.

## Follow-on (separate ticket, not this run)

The uniformization blind point (phase pushforward exactly uniform mod period ⇒ blindness against
all sample-level probes) was previously reclassified as a build-gated Lean formalization ticket;
it attaches naturally to this module as a second blindness mechanism alongside the fiber-pair one.

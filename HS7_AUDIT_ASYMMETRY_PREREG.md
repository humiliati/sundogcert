# HS7 PREREG — Audit-asymmetry certificate: ∀-verifier blindness + adversarial-reporter audit game (Lean)

**Frozen:** 2026-06-10, repo HEAD `d5d1223` (clean tree, in sync with origin/master).
**Status:** PREREG — written and frozen BEFORE any line of `AuditCost.lean` exists.
**Lane:** sundogcert Lean pillars / audit certificates.

**Standing discipline (binds this prereg):** pre-registered KILL criterion — a clean null is a
SUCCESS; forward-generate only (state the theorem first, then prove it — no retrofitting the
statement to whatever happens to be provable, except as the named kill K2 adjudicates);
deterministic, kernel-checked, axiom-clean (`AxiomAudit` gate, no `native_decide`); cheap headless
leg (no GPU, no external data, no spend); name the nearest prior, state the delta.

---

## §1 Claim

In **one finite formal setting** — populations `u : Fin n → ℚ`; observation channel =
`(report, pooledMean u)`; empirical statistics as finite sums; **no `Measure ℝ` anywhere**, so
"same interface" between the audit half and the blindness half is literally true — Lean proves,
kernel-checked and axiom-clean:

(i) **Audit game, sound against an adversarial reporter.** A full-access auditor's accept
predicate satisfies: no false report accepts, the honest report always accepts — stated over
reporter *strategies* `σ : (Fin n → ℚ) → ℚ`, not just report values — with a **faithful op-count
`auditCost n ≤ 3·n + 2`** in the CheckCost.lean trust-surface style (the cost MODEL is a declared,
human-audited trust-surface item; the BOUND is then a theorem).

(ii) **Channel-level blindness quantified over ALL verifiers.** For **every** decidable
`A : ℚ × ℚ → Bool` seeing only `(report, pooledMean u)`, every coordinate `i`, and every prescribed
per-unit difference `δ`, there exists an **explicit** fiber pair `u, u′` with
`pooledMean u′ = pooledMean u`, `u′ i = u i + δ`, and `A`'s verdict identical on both for every
report — a finite data-processing statement the repo does not have. Strengthened to the
impossibility form: **no decidable channel verifier is sound-and-complete for any per-unit claim**
`u i = v` (nor for any predicate non-constant on a pooled-mean fiber).

(iii) **The asymmetry is real, not generic** (contrast legs): at `n = 1` the channel *determines*
the unit (`pooledMean u = u 0`) — blindness genuinely requires `n ≥ 2`; and the same explicit fiber
pair that every channel verifier misses is **separated by an exhibited finite-sum per-unit
statistic** (the second moment, the first charFun coefficient beyond the mean) — the destroyed
information is present one statistic up, which is the tower's determine/resist story in its finite
form.

Honest scope, stated up front: the artifact is a finite rational-mean channel, presented as the
**certified template** for audit-asymmetry claims — not a claim about trained systems, and not
"introspection." The blindness theorem certifies the *pooled observable*: a reporter that itself
has per-unit access can still encode per-unit facts in the report channel — the theorem says no
verifier can *check* such a claim against the pooled observable (that is exactly the impossibility
form), not that reports carry no information.

## §2 First leg (the only leg)

**(a) `Sundogcert/AuditCost.lean`** — new module, imported by `AxiomAudit.lean`. Pinned names
(the structure audit in K2 is run against THESE, so they are frozen now):

| Name | Content |
|---|---|
| `pooledMean` | `(∑ i, u i) / n` |
| `auditAccept` | full-access audit: `decide (r = pooledMean u)` |
| `audit_sound` | `auditAccept u r = true → r = pooledMean u` (no false report accepts) |
| `audit_complete` | `auditAccept u (pooledMean u) = true` |
| `dishonest_caught` | over strategies: `σ u ≠ pooledMean u → auditAccept u (σ u) = false` |
| `auditCost`, `auditCost_eq`, `auditCost_le` | trust-surface op-count; exact value; `≤ 3n + 2` |
| `bump`, `pooledMean_bump`, `bump_apply` | the explicit fiber-pair construction and its two laws |
| `pooled_channel_blind` | the ∀-verifier blindness theorem (load-bearing) |
| `no_channel_verifier_decides` | fiber-pair ⇒ no sound-and-complete channel verifier for `P` |
| `no_verifier_checks_perUnit` | instantiation at `P := (u i = v)` |
| `n1_channel_determines` | `n = 1` boundary: the channel determines the unit |
| `secondMoment_separates` | the same fiber pair is separated by `x ↦ x²` |
| `audit_asymmetry` | HEADLINE: (audit decides honestly at cost ≤ 3n+2) ∧ (∀-verifier per-unit blindness), one statement |

Plus a `decide`-checked toy instance at `n = 8` (honest report accepts, a false report rejects),
using plain `decide` only — `native_decide` is forbidden by the AxiomAudit gate.

**(b) AxiomAudit entries** for `audit_sound`, `auditCost_le`, `pooled_channel_blind`,
`no_verifier_checks_perUnit`, `audit_asymmetry` — exact foundational triple
`[propext, Classical.choice, Quot.sound]`, build-enforced. `lake build` green on the full tree.

**(c) Consistency lock (NOT a kill):** `scripts/audit_cost_check.py` + frozen test
`scripts/test_audit_cost_check.py` — an instrumented op-counter over seeded populations at
`n ∈ {8, 64, 512}` that must reproduce the Lean cost model exactly (`auditCost_eq`) and satisfy the
`3n + 2` bound, and whose audit verdicts must match a reference implementation. Demoted from kill
to lock per the CheckCost.lean precedent: a same-author cost model cannot self-falsify — the model
is a trust-surface item a reviewer audits; the script locks internal consistency only. A mismatch
is a bug that blocks banking until green, not a result.

**Cost model (trust-surface declaration, frozen now).** The audit's dominant path: fold the `n`
per-unit values into the sum (`n` term-reads + `n − 1` additions), one division by `n`, one
equality test against the report. `auditCost n = n + (n − 1) + 2 = 2n + 1 ≤ 3n + 2`. The slate-level
bound `3n + 2` is what is proved and cited; the exact count is also proved (`auditCost_eq`) so the
headroom is visible, not hidden.

## §3 KILL criteria (pre-registered; a clean kill is a banked SUCCESS)

**K1 — time-box on the load-bearing theorem.** If `pooled_channel_blind` +
`no_verifier_checks_perUnit` are not proved, axiom-clean, within **2 working days of this freeze**
(deadline: end of 2026-06-12), the hypothesis is DEAD, banked as: the finite data-processing
statement is harder than the tower suggests — worth knowing before it is cited anywhere.

**K2 — structure audit with a named witness criterion.** At result time, the headline
`audit_asymmetry` must contain a **quantifier alternation — quantification over ALL decidable
channel verifiers (`∀ A : ℚ × ℚ → Bool`, or the `¬∃ A` impossibility form) combined with explicit
fiber-pair existence at a prescribed per-unit δ** — that appears in NO banked statement. The audit
list is pinned now: `accept_sound`, `reject_sound`, `no_passing_unsafe`, `verifyCost_le`,
`resistance_general`, `determination_general`, `gaussian_resist_and_determine`,
`cauchy_is_separator`, `twoPoint_shadow_survives`, `resist_orthogonal_to_variance`,
`sat_iff_decodes`. If the headline can be obtained from any of these by renaming or
specialization without introducing the verifier quantifier, the hypothesis is DEAD (it was a
renaming, as the original pre-fix version was refuted to be).

**Honesty note pinned in advance:** the *proof* of blindness is expected to be short — data
processing is short; `verdict equality` follows from `pooledMean` equality by congruence. K2 is
deliberately a test of the **statement** (what is quantified over, what is constructed), not of
proof length. The receipt must report proof length anyway, so nobody has to take this on faith.

**What CANNOT kill:** the python script (consistency lock, §2c); build friction (toolchain/mathlib
issues are engineering, not evidence); `decide` performance at n = 8 (may be replaced by `norm_num`
or `rfl` without prejudice — the toy is illustration, not a kill surface).

## §4 Controls / honesty constraints

1. **Axiom-clean gate:** every §2b entry enters `AxiomAudit.lean` under `#guard_msgs in
   #print axioms` with the exact triple; a `sorry` or `native_decide` anywhere upstream fails the
   build. No theorem is banked outside the gate.
2. **Adversarial-reporter caveat** (stated in the module header and the receipt): blindness
   certifies the pooled observable, not the report channel — see §1 scope paragraph.
3. **Non-vacuity controls:** `n1_channel_determines` (blindness is FALSE at n = 1, so the n ≥ 2
   statement has content) and `secondMoment_separates` (the fiber pair is distinguishable one
   statistic up — the channel, not the pair, is what is blind). Both required for banking.
4. **No statement drift:** if any pinned statement in §2a must change materially to be provable,
   the change is recorded in the receipt as a deviation with the reason, and K2 is re-run against
   the changed form. Silent drift = invalid run.

## §5 Nearest priors (named now), and the delta

**In-repo:** `CheckCost.lean` (`verifyCost_le` — the cost-model-as-trust-surface pattern this
reuses; no game, no verifier quantification), `Certificate.lean` (`accept_sound`/`reject_sound` —
soundness of ONE deployed verifier, not a statement over all verifiers),
`ShadowDecayGeneral.lean` (`resistance_general`/`determination_general` — one statistic's
asymptotic behavior in `Measure ℝ`; one-directional, one-statistic),
`ShadowDecayLattice.lean` (recurrence/survival, same interface remark). The pre-fix version of
this very hypothesis was refuted as ~3 lines of renaming distance from these — that refutation is
the reason K2 exists.

**External:** the blindness core is a finite, explicit-witness form of data-processing /
Blackwell-style non-identifiability — classical as mathematics; not claimed as new mathematics.
The delta claimed: the *pairing*, machine-checked in one setting — a proved-cheap,
adversarial-reporter-sound audit AND for-all-verifiers per-unit blindness through the pooled
channel, with explicit constructions, build-enforced axiom hygiene, and a re-runnable `lake build`
— plus the impossibility form (`no_verifier_checks_perUnit`) as a certified statement about what
self-reported per-unit claims can never be checked against.

## §6 Receipt plan

`HS7_AUDIT_ASYMMETRY_RESULT.md` at repo root: outcome (LANDED / K1 / K2), the K2 audit run against
the pinned list, proof lengths, deviations (if any) with reasons, `lake build` job count, and the
consistency-lock numbers at n ∈ {8, 64, 512}. METHOD.md gets a short section only after banking.

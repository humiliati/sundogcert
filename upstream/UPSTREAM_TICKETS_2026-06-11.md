# UPSTREAM TICKETS — S3-A6 Lean micro-upstream pack (FROZEN 2026-06-12)

**Slate entry:** S3-A6 of `sundog/internal/slates/HYP_SLATE_3_EXTERNAL_ANCHORS_2026-06-11.md`
(deliverable-type, ticket-grade by design — HS6 precedent; acceptance/abort criteria, never science
kills). Path pinned by the slate (named 2026-06-11; frozen with live data 2026-06-12). All PR
submission / Zulip posting / issue commenting is **OWNER-GATED** without exception.

## Staleness table (LIVE, 2026-06-12 — the Step-1 gate's first run, executed pre-freeze)

| target | slate assumption (2026-06-11) | LIVE state 2026-06-12 | disposition |
|---|---|---|---|
| mathlib4 PR #38014 | open, unreviewed | **OPEN, ACTIVE** — updated 2026-06-11, head `my-feature-branch`, not draft | **T2 GO** |
| ArkLib #222 (`decoder_dist_impl_mem`) | proof-wanted | **STALE** — decl ABSENT from master GuruswamiSudan.lean (0 sorries in file) | retired |
| ArkLib #224 (`guruswami_sudan_for_proximity_gap_property`) | "the only open, unclaimed, non-stale target" | **STALE** — decl PRESENT in master but **PROVEN (no sorry; file has 0 sorries)** | retired |
| ArkLib #225 (`minDist_eq_minDist`) | proof-wanted | **STALE** — decl ABSENT from master InterleavedCode.lean (0 sorries) | retired |
| ArkLib #233 (`decoder_mem_impl_dist`) | proof-wanted | **STALE** — decl ABSENT from master (0 sorries) | retired |
| ArkLib BCIKS20 ListDecoding | (not in slate) | `ProximityGap/BCIKS20/ListDecoding/Guruswami.lean` @ `90959c93` has **2 sorries** (relocated GS list-decoding territory; ~25 GS PRs closed recently; open PR #574 executable-GS integration, #476 FRI error accounting; branches `ElijahVlasov/positive-delta-in-proximity-gap`, `Katy/Proximity{Refactor,WIP}`) | **T3 RETARGET** |

The 2026-06-11 verification was issue-METADADATA-tier; the content-tier check (this table) finds all
four issue targets resolved or refactored away in master with the trackers left open. **Banked
finding + bonus surface:** a courteous stale-tracker note to the maintainers (issues #222/#224/#225/
#233 reference proven/absent obligations) is drafted as part of T3's deliverable — owner-gated.

## Do-not-re-prove list (re-verified live 2026-06-12)

ArkLib `Data/CodingTheory/ReedSolomon.lean`: 0 sorries; contains `minDist`, `uniqueDecodingRadius`,
`isMDS` machinery — NEVER pitch re-proving RS minimum distance / unique-decoding radius / MDS.

---

## T1 — mathlib Cauchy micro-port (build-gated)

**Port surface (from `Sundogcert/ShadowDecayCauchy.lean`, all axiom-clean, build-enforced):**
`charFun_cauchy_eq_fourier` (the charFun→Fourier bridge), `cauchy_charFun_tendsto_zero`
(via `Real.zero_at_infty_fourier`), `cauchy_weighted_density_not_integrable` (helper),
`cauchy_no_mean`. **NOT upstreamed** (lab framing): `cauchy_is_separator`, `cauchy_resists`,
`resist_determine_independent`.

**ACCEPTANCE:** the four port to CURRENT mathlib master as self-contained additions to
`Mathlib/Probability/Distributions/Cauchy.lean` (or the file the probability lane prefers): zero
`import Sundogcert`; `#print axioms` = [propext, Classical.choice, Quot.sound]; **pinned lint
commands** = `lake exe lint-style <new files>` exit 0 AND env linters clean under
`lake build Mathlib.Probability.Distributions.Cauchy` (exit statuses parsed by
`scripts/upstream_gate_check.py`); completed within a **2-working-day build clock starting AFTER
the first successful `lake exe cache get`** on the master fork; preceded by a **one-shot 0.5-day
infra timebox** (elan toolchain + fork clone + ~5–10 GB cache on this never-before-used-for-mathlib
Windows box — the real risk). Staged as two PR-ready fork branches + `upstream/ZULIP_SCOPING_DRAFT.md`
offering BOTH shapes (Cauchy-specific pair AND the generalized "charFun of a withDensity/L¹
measure → 0", citing the proven in-house `Sundog.ShadowDecayLattice.absCont_charFun_tendsto_zero`).
Drift log: `upstream/MATHLIB_CAUCHY_PORT_NOTES.md`.

**DEMAND-GATE (before any PR):** (a) owner sign-off AND (b) a probability-lane Zulip reply
expressing interest in ≥1 lemma shape, archived in the scoping draft's outcome section.

**ABORTS:** ABORT-T1a-INFRA (timebox exhausted on toolchain/cache → cloud-runner/devcontainer
fallback decision owner-gated; port NOT priced); ABORT-T1a-DRIFT (genuine mathlib API
rename/restructure defeats the port within the build window → banked as a drift receipt);
ABORT-T1b (Zulip accepts only the generalized shape → Cauchy branch parks, generalized branch
proceeds as its own ticket).

## T2 — PR #38014 review + RS follow-on sketch (post-T1-build-gate)

**ACCEPTANCE:** `upstream/PR38014_REVIEW_DRAFT.md` with ≥5 line-anchored substantive points, each
citing an exact mathlib precedent or a compile-verified alternative (the unresolved 2026-06-03
infsep question = the natural opener); the RS follow-on sketch's path/namespace derived from the
CHECKED-OUT PR branch's actual InformationTheory layout (never the guessed `Coding/` path), aligned
to the committed `RSCertificate.lean`. **Sequenced strictly after T1's build gate clears** (or the
infra fallback lands); inherits ABORT-T1a-INFRA.

**HYGIENE PRECONDITION (verified open 2026-06-12):** `RSCertificate.lean` EXISTS locally but is
ABSENT from `AxiomAudit.lean` — RSCertificate must be added to the axiom audit (and build green)
BEFORE any upstream-facing text cites the pillar.

## T3 — ArkLib scoping (RETARGETED per the staleness rule, criteria frozen BEFORE reading)

**Original targets retired** (table above). **Retarget:** the 2 sorries in
`ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean` @ `90959c93`.
**The sorry bodies have NOT been read at freeze time** (only existence + file/commit pinned).

**Protocol (2-day timebox → forced binary token):** staleness re-check immediately before start
(file SHA + sorry count + open-PR sweep incl. #574 and the Katy/Elijah branches — if the sorries
vanish or a PR claims them, STALE-ABORT with receipts); then scope each sorry to a dependency map.
**GO** requires: every named ArkLib/mathlib decl in the obligations compile-resolves (lake build of
a scoping stub or #check file) AND an itemized missing-lemma-class list with search receipts.
**NO-GO** fires iff any required lemma class is absent from BOTH ArkLib and mathlib (receipts
attached). The scoping note `upstream/ARKLIB_BCIKS20_SCOPING.md` must END with exactly one token —
`GO` or `NO-GO` — an essay without the token = ticket failure. Deliverable additionally includes
the stale-tracker courtesy-comment draft for #222/#224/#225/#233 (owner-gated to post).

## Budget (audit-corrected)

Staleness/lint gate SCRIPT ~1 day + one-shot 0.5-day infra timebox (a different clock from the T1
2-working-day BUILD window); full pack ≤ 4–5 days serial EXPECTED case (worst case with every
timebox saturated + T2 review ≈ 6–6.5 d). T3 proof phase (if GO) separately costed in the scoping
note, NOT committed by this pack. C1 (RS-evaluation pillar) continues in sundogcert regardless of
any external outcome.

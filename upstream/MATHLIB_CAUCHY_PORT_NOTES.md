# T1 port notes + infra/drift log (S3-A6)

Ticket: `upstream/UPSTREAM_TICKETS_2026-06-11.md` (frozen 2026-06-12). This file is the running
drift log the ticket requires. The 2-working-day BUILD clock starts at the first successful
`lake exe cache get` (logged below when it lands).

## Infra timebox log (one-shot, 0.5 day — started 2026-06-12)

- Preflight: `lake` 5.0.0 / Lean 4.30.0 present (winget standalone Lean.Lean, the lab's deliberate
  sundogcert setup); **no elan**; C: 576 GB free.
- mathlib master pins `leanprover/lean4:v4.31.0-rc2` → standalone 4.30.0 cannot build master →
  elan REQUIRED (named explicitly in the slate's infra-timebox scope; proceeded).
- `winget install Lean.Elan` → delivers `elan-init.exe`; ran `-y --default-toolchain none` →
  **elan 4.2.3** at `~/.elan/bin`, no toolchains preinstalled (lean-toolchain files drive fetches).
- **PATH note (the one setup-disturbance risk):** elan-init adds `~/.elan/bin` to the user PATH.
  elan honors per-directory `lean-toolchain`, so sundogcert (pinned v4.30.0) keeps working — elan
  fetches its own v4.30.0 copy on first use there; the winget Lean remains installed. If anything
  in the sundogcert workflow misbehaves, the fallback is removing `~/.elan/bin` from PATH (the
  winget binaries are untouched).
- mathlib4 cloned `--depth 50` to `C:/Users/hughe/Dev/mathlib4`; **master commit pinned for the
  port window: `97e3b24`** (doc(Geometry/Manifold/...) #40549, 2026-06-12). Shallow clone is
  fine for branch creation + push; the fork (owner-gated, demand-gated) comes at submission time.
- `lake exe cache get` COMPLETE: 8538/8538 files downloaded + decompressed (one background window).
- **First successful cache verification: 2026-06-12 09:06** —
  `lake build Mathlib.Probability.Distributions.Cauchy` = "Build completed successfully (2703
  jobs)" near-instant (cache serving). **THE 2-WORKING-DAY BUILD CLOCK STARTS HERE** (expires end
  of 2026-06-16 in working days, weekend excluded).
- INFRA TIMEBOX CLOSED WELL UNDER BUDGET (~25 min wall vs 0.5-day box). No ABORT branch touched.

## Port-surface drift checks (to fill during the build window)

- [x] `Mathlib.Probability.Distributions.Cauchy` still lacks charFun + Integrable-id results on
      master `97e3b24` — VERIFIED in the checkout 2026-06-12 (0 hits for charFun/no-mean): the
      gap is intact, the port targets are live.
- [x] `Real.zero_at_infty_fourier` anchor present on master:
      `Mathlib/Analysis/Fourier/RiemannLebesgueLemma.lean` ✓.
- [ ] Names/locations of: `charFun`, `Real.zero_at_infty_fourier` (Riemann–Lebesgue),
      `cauchyMeasure`/`cauchyPDF` API used by the four ported decls — declaration-by-declaration
      against `Sundogcert/ShadowDecayCauchy.lean`.
- [ ] Target file + section placement per the probability lane's current layout.

## Decisions / drift events

(none yet)

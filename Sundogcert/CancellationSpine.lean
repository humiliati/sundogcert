/-
# The cancellation spine — one coordinate, machine-checked on the proven axes (N-2)

Slate-2 hook **N-2** is a *retrospective*, not a reduction theorem: the reading that almost
every wall the lane meets is the *same* wall — **cancellation** (the negative scale / the
subtraction that makes a ReLU net a tropical *rational* map rather than a tropical
*polynomial*). The full claim "every imported wall is cancellation-reducible" stays a typed
conjecture (see `docs/ALGO_APPROX_N2_CANCELLATION_SPINE.md` for the honest PROVEN-vs-reading
split and the `WALL_WITHOUT_CANCELLATION` falsifier).

This module records the part of that reading that *is* machine-checked, as a single statement.
It rests entirely on the proven N-1 cores; it introduces no new mathematics, only the packaging
that makes "the cancellation-free fragment is uniformly tame" one gated theorem.

* **`isMono_tame`** (positive half) — a cancellation-free (`IsMono`) circuit is tame on *every*
  axis at once: its realization is **monotone**, **convex**, and has a **linear** (leaf-count)
  region bound. Absence of cancellation ⇒ all of the lane's good behaviour, together.

The matching **negative half** is already gated in `FoldCancellation`: no cancellation-free
circuit computes the `d`-fold tent (`isMono_not_iterTent`), the canonical cancellation-using
function. Positive + negative = on the monotone / convex / region / fold axes, cancellation is
exactly the coordinate. The *other* axes (additive 3SUM, subtractive `n^ω`, division gates) are
organized under the same reading but **not** proven reducible — that is the retrospective's
honest boundary.
-/
import Sundogcert.FoldCancellation
import Sundogcert.RegionPoly

namespace Sundog.CancellationSpine

open Sundog.CircuitNet Sundog.CancellationFree Sundog.RegionCount Sundog.PieceCover
  Sundog.RegionPoly Sundog.FoldCancellation

/-- **The cancellation-free fragment is uniformly tame (the spine, positive half).** Every
`IsMono` (cancellation-free) circuit's 1-D realization is simultaneously **monotone**,
**convex**, and **region-polynomial** (a piece cover linear in the leaf count). One hypothesis
— *no cancellation* — yields every one of the lane's positive structural results at once. The
negative half (`FoldCancellation.isMono_not_iterTent`: the cancellation-using tent is
unreachable cancellation-free) is its mirror, so on these axes cancellation is the single
coordinate. -/
theorem isMono_tame {e : Trop 1} (h : IsMono e) :
    Monotone (realize1 e) ∧
      ConvexOn ℝ Set.univ (realize1 e) ∧
      HasPieceCover (realize1 e) (leafCount e) :=
  ⟨isMono_realize1_monotone h, isMono_realize1_convexOn h, isMono_hasPieceCover h⟩

end Sundog.CancellationSpine

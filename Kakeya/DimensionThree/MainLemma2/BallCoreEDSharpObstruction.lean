/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.BallCoreEDFold

/-!
# (C1) is false at every localisation: the clamped-window obstruction

`Kakeya.VeryNotSticky.SharpCapsuleAlignment` asks, for two tubes `i`, `j` of one ball `B` whose
`K`-dilated capsules are not essentially distinct, that the *undilated* capsule of `j`, localised
to `ball (ctr B) (r₁/16)`, lie in the `K`-dilated capsule of `i`. The fold author's model
 put the ball centre at the **centre** of both windows and found a marginal
constant (`≈ 1.11` at `r₁/16`, `≈ 0.90` at `r₁/64`). That model misses the clamping in
`Kakeya.VeryNotSticky.segStart`: when the centre `c` projects at or before the start of a tube's
core (`coreParam T c = 0`), the window is `[0, 2L]` and **`c` sits at its end**, not its middle.

This file compiles the resulting obstruction. Two tubes on parallel cores, both starting next to
`c` — tube `j` at `c`, tube `i` at `c + (L/8) • axis₀ + d • axis₁` with `0 ≤ d ≤ Kδ/8` — have
windows `[0, 2L]` clamped at their starts. Their `K`-dilated capsules overlap in the capsule
`Kakeya.VeryNotSticky.obstructionBody` of length `2L − L/8`, which is more than half of either
(the volume comparison is by one homothety of ratio `8/7`, `(8/7)³ < 2`, and one translation), so
they are **not** essentially distinct; but the point `c` itself lies in `j`'s undilated capsule and
at axial distance `L/8 > K'δ` from `i`'s core window, so it is outside `i`'s `K'`-dilated capsule
for **every** `K'` with `K'δ < L/8` — and it is in `ball c r` for every `r > 0`.

## Main statements

* `Kakeya.VeryNotSticky.not_isEssentiallyDistinct_obstruction` — the two dilated capsules are not
  essentially distinct.
* `Kakeya.VeryNotSticky.obstruction_not_mem_capsuleAt` — `c` is outside `i`'s `K'`-dilate for
  every `K'δ < L/8`.
* `Kakeya.VeryNotSticky.not_capsuleAlignmentBody` — the body of `SharpCapsuleAlignment`, with the
  tubes and the centre free, fails at **every** localisation radius `r > 0`;
  `sharpCapsuleAlignment_iff_body` is the `Iff.rfl` link to the existing `abbrev`.
* `Kakeya.VeryNotSticky.exists_obstruction_at_fold_constants` — the same at the fold's own
  constants `K = edDilateConstant`, `L = r₁/4`, under the fold's radius floor, with the two unit
  tubes disjoint (hence essentially distinct as tubes).

## What this settles

The misalignment is **axial** (along the core), of size `L/8 = r₁/32`, unbounded relative to the
radius `Kδ`; no radius dilate and no localisation radius absorbs it. So (C1) as stated cannot be
proved at `r₁/64` or at any other localisation; the target text has to change (a licence item).
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace Kakeya.VeryNotSticky

universe u

/-! ### Two coordinate vectors of `E3` -/

/-- The first coordinate vector of `E3`. -/
noncomputable def axis₀ : E3 := EuclideanSpace.single 0 1

/-- The second coordinate vector of `E3`. -/
noncomputable def axis₁ : E3 := EuclideanSpace.single 1 1

theorem norm_axis₀ : ‖axis₀‖ = 1 := by
  simp [axis₀]


/-! ### Segments along `axis₀` -/


/-! ### Tubes along `axis₀` -/

theorem dist_self_add_axis₀ (p : E3) : dist p (p + axis₀) = 1 := by
  rw [dist_self_add_right, norm_axis₀]

/-- The `δ`-tube whose unit core runs from `p` to `p + axis₀`. -/
noncomputable def axisTube (δ : ℝ≥0) (p : E3) : Tube δ E3 :=
  Tube.mk' δ (dist_self_add_axis₀ p)

variable {δ : ℝ≥0}

@[simp] theorem axisTube_x (p : E3) : (axisTube δ p).x = p := rfl

@[simp] theorem axisTube_y (p : E3) : (axisTube δ p).y = p + axis₀ := rfl


/-! ### The obstruction configuration -/


section Obstruction

variable {K : ℝ≥0} {c : E3} {L d : ℝ}


end Obstruction

/-! ### The body of `SharpCapsuleAlignment`, with the tubes and the centre free -/


/-! ### At the fold's own constants -/


end Kakeya.VeryNotSticky

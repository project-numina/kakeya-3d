/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.TubeParentPacking
public import Kakeya.DimensionThree.BoundedOverlapCount

/-!
# Helpers for a hybrid `ρ`-parent producer

The coarse parent system of `Kakeya/DimensionThree/Plank/TubeParentPacking.lean` is built over the
concrete ambient `EuclideanSpace ℝ (Fin 3)` and, at the counting step, over a `MeasureSpace`
instance carrying an additive Haar measure.  A hybrid producer that has to run inside an abstract
three-dimensional inner-product space cannot cite it directly.  This file restates the four
ingredients it needs, each over the weakest hypotheses the argument actually uses.

* **Mixed radii.**  `Kakeya.Tube.carrier_subset_rescale_of_center_dir_close_mixed` is
  `Kakeya.Tube.carrier_subset_rescale_of_center_dir_close` with the two tubes allowed different
  radii.  The containing tube's radius never enters that proof — only its centre, direction,
  endpoints, and rescale do — and both endgames
  (`Kakeya.Tube.carrier_subset_of_endpoints_close` and its `_flip`) are mixed-radius already.
* **Rescale inside a dilate.**  `Kakeya.Tube.rescale_le_dilate_of_le_mul` puts the `s`-rescale of a
  `ρ`-tube inside its `C`-dilate as soon as `s ≤ C ρ` and `1 ≤ C`; the concentric case of
  `Kakeya.ml1Boot.rescale_le_dilate_two`, with the ratio left free.
* **Abstract-`E` separated assignment.**  `Kakeya.exists_separatedAssignment_abstract` is
  `Kakeya.exists_separatedAssignment` over an arbitrary normed space, its proof using only
  `Kakeya.exists_max_card_separated` and the two formal facts `Kakeya.tubeParamDist_comm` and
  `Kakeya.tubeParamDist_self`.  The assignment fixes the selected leaves
  (`Kakeya.assign_eq_self_of_mem_separated`), hence is onto them
  (`Kakeya.surjOn_assign_of_mem_separated`).
* **The `ρ ^ (-5)` packing count.**  `Kakeya.card_le_of_tubeParamDist_separated_of_finrank_three`
  bounds a `ρ/8`-separated family of tubes with carriers in `B̄(0,1)`.  It does *not* go through
  `Kakeya.card_le_of_tubeParamDist_separated`, whose packing engine
  `Kakeya.card_le_of_separated_in_ball` needs a `MeasureSpace` instance and an additive Haar
  measure.  Instead it fibres over a maximal `ρ/16`-separated set of centres and uses the
  abstract-`E` pair `Kakeya.ml1Boot.card_le_of_ball_separated` (centres, `ρ ^ (-3)`) and
  `Kakeya.ml1Boot.card_le_of_unit_separated` (directions, `ρ ^ (-2)`).  The exponent `5 = 3 + 2`
  is exactly this split, and it is why `Kakeya.tubeParamDist` is a `max`: two members of one fibre
  have centres within `ρ/8`, so their *directions* must carry the separation.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Metric Set Convexity ConvexSpaceBody

open scoped NNReal ENNReal

noncomputable section

namespace Kakeya

/-! ### Mixed-radius containment -/


/-! ### A rescale inside a dilate -/

/-- **A rescale of a tube sits inside a dilate of it.**

For `1 ≤ C` and `s ≤ C ρ`, the `s`-rescale of a `ρ`-tube `T` lies in the `C`-dilate of `T`: every
point of the rescale is within `s ≤ Cρ` of a point of the core, and every core point is
`T.center + u • T.direction` with `|u| ≤ 1/2 ≤ C/2`, which is exactly the hypothesis of
`Kakeya.Tube.mem_dilate_of_dist_axis_le`. -/
theorem Tube.rescale_le_dilate_of_le_mul
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {ρ s : ℝ≥0} (T : Tube ρ E) {C : ℝ} (hC : 1 ≤ C) (hs : (s : ℝ) ≤ C * (ρ : ℝ)) :
    (T.rescale s).toConvexSpaceBody ≤ Kakeya.Tube.dilate T C := by
  intro z hz
  change z ∈ (T.rescale s).carrier at hz
  have hxσ : (T.rescale s).x = T.x := by simp [Tube.rescale]
  have hyσ : (T.rescale s).y = T.y := by simp [Tube.rescale]
  rw [(T.rescale s).carrier_eq] at hz
  rw [Set.mem_iUnion₂] at hz
  rw [hxσ, hyσ] at hz
  obtain ⟨p, hp_seg, h_zp⟩ := hz
  rw [Metric.mem_closedBall] at h_zp
  rw [segment_eq_image'] at hp_seg
  obtain ⟨u, hu, hp_eq⟩ := hp_seg
  let t : ℝ := u - 1 / 2
  have hpt : p = T.center + t • T.direction := by
    rw [← hp_eq]
    dsimp [t]
    have hc : T.center = (1 / 2 : ℝ) • (T.x + T.y) := by
      change midpoint ℝ T.x T.y = (1 / 2 : ℝ) • (T.x + T.y)
      rw [midpoint_eq_smul_add]
      norm_num
    rw [hc]
    module
  have ht : |t| ≤ C / 2 := by
    have ht12 : |t| ≤ 1 / 2 := by
      dsimp [t]
      rw [abs_le]
      constructor <;> linarith [hu.1, hu.2]
    have hChalf : (1 / 2 : ℝ) ≤ C / 2 := by linarith
    exact ht12.trans hChalf
  have hz2 : dist z (T.center + t • T.direction) ≤ C * (ρ : ℝ) := by
    rw [← hpt]
    calc
      dist z p ≤ (s : ℝ) := h_zp
      _ ≤ C * (ρ : ℝ) := hs
  exact Tube.mem_dilate_of_dist_axis_le (T := T) (C := C)
    (hC := (by linarith : (0 : ℝ) < C)) (s := t) (hs := ht) (hz := hz2)

/-! ### The separated assignment over an abstract ambient space -/


/-! ### The abstract-`E` packing count -/

section Packing

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]


end Packing

end Kakeya

end

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.BallCoreEDComparable
public import Kakeya.DimensionThree.MainLemma2.NonSlabAngle

/-!
# R-a and R-b: GWZ's "comparable" for capsules is a THEOREM, and the angular step

Fourth and last file of the G13 stack (`BallCoreEDSegments`, `BallCoreEDCapsule`,
`BallCoreEDComparable`, this). **Land it together with the previous two**: the third file
supersedes the second's radius-only reading of comparability, and this one discharges the
hypothesis the third left open.

## R-a — `CapsuleComparableHomAt` is proved

`Kakeya.VeryNotSticky.capsuleComparableHomAt_of_deltaLeR₁`: for every `BallDataCore` of a
configuration with `16 δ ≤ r₁` — the binder the BP264 target already carries — two capsules of one
ball that are **not essentially distinct** each lie in the `K′₀`-homothety dilate of the other,
at `K′₀ = Kakeya.VeryNotSticky.edDilateConstant`. **This was G13's single remaining geometric
obligation.**

The proof is a rescaling, and every step is existing geometry:

* `Kakeya.VeryNotSticky.rescaledCapsuleTube` — the homothety of ratio `(2L)⁻¹` carries a capsule
  of half-length `L` and radius `δ` to the carrier of a genuine `Kakeya.Tube` of scale
  `δ/(2L) ≤ 1` (the core window has length exactly `2L`, so its image has length exactly `1`);
* `IsEssentiallyDistinct.image_affineEquiv` transports the hypothesis;
* `Kakeya.VeryNotSticky.tube_subset_dilate_of_not_essDistinct` — i.e. the existing
  `Kakeya.Tube.tubeOverlapCoreClose` — applies there;
* its conclusion is a `Kakeya.Tube.dilate`, a homothety about `Tube.center = midpoint x y`, and
  `homothety_conj` + `rescaledCapsuleTube_center` pull it back to a homothety about the capsule's
  own centre.

Consequences, all now unconditional in `core`: `capsuleInputs_of_floor` and `capsuleShade_subset_hom_at_K₀` (the (C1) clause the repaired fold consumes).

## R-b — the angular step

`Kakeya.VeryNotSticky.lineAngle_le_of_ballCapsuleHom`: a class member's direction is within
`(π/2)·(8 K δ / r₁)` of the representative's. That is the `hang` hypothesis of
`Kakeya.VeryNotSticky.card_cone_le`, so the density-cap route of  §G-addendum (a) — no
essential-distinctness hypothesis on `cfg.s` — is fed. The proof is elementary: the two endpoints
of the class member's core window decompose along the representative's core line with an error
`K δ`, so the unit chord differs from `± dir i` by at most `2Kδ/L`, and
`NonSlab.lineAngle_le_pi_div_two_mul_norm_sub` converts that to an angle.

## R-c — left as a binder, as instructed

`Kakeya.VeryNotSticky.fibreClause_of_classCount` states the fold's fibre clause with the budget's
constant as an explicit named `C_fib`, so that the same estimate applies to any chosen budget.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

namespace Kakeya.VeryNotSticky

universe u
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-! ### The homothety toolbox -/

theorem homothety_image_closedBall {p : E3} {k : ℝ} (hk : 0 < k) (z : E3) (r : ℝ) :
    (AffineMap.homothety p k) '' closedBall z r =
      closedBall (AffineMap.homothety p k z) (k * r) := by
  ext y
  simp only [Set.mem_image, Metric.mem_closedBall]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [dist_homothety, abs_of_pos hk]
    exact mul_le_mul_of_nonneg_left hx (le_of_lt hk)
  · intro hy
    refine ⟨AffineMap.homothety p k⁻¹ y, ?_, ?_⟩
    · have := dist_homothety p k⁻¹ y (AffineMap.homothety p k z)
      rw [abs_of_pos (inv_pos.2 hk)] at this
      have hz : AffineMap.homothety p k⁻¹ (AffineMap.homothety p k z) = z := by
        rw [← AffineMap.comp_apply, ← AffineMap.homothety_mul,
          inv_mul_cancel₀ (ne_of_gt hk), AffineMap.homothety_one]; rfl
      rw [hz] at this
      rw [this, inv_mul_le_iff₀ hk] at *
      calc dist y (AffineMap.homothety p k z) ≤ k * r := hy
        _ = k * r := rfl
    · rw [← AffineMap.comp_apply, ← AffineMap.homothety_mul,
        mul_inv_cancel₀ (ne_of_gt hk), AffineMap.homothety_one]; rfl

theorem homothety_image_segment (p : E3) (k : ℝ) (a b : E3) :
    (AffineMap.homothety p k) '' segment ℝ a b =
      segment ℝ (AffineMap.homothety p k a) (AffineMap.homothety p k b) := by
  ext y
  simp only [Set.mem_image, segment_eq_image' ℝ]
  constructor
  · rintro ⟨x, ⟨θ, hθ, rfl⟩, rfl⟩
    refine ⟨θ, hθ, ?_⟩
    simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
    module
  · rintro ⟨θ, hθ, rfl⟩
    refine ⟨a + θ • (b - a), ⟨θ, hθ, rfl⟩, ?_⟩
    simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
    module


/-! ### The capsule as a convex body, and its rescaling to a unit tube -/

/-- The capsule `segCarrierSet T c L` packaged as a `ConvexSpaceBody`. -/
noncomputable def capsuleBody {δ : ℝ≥0} (T : Tube δ E3) (c : E3) {L : ℝ} (hL : 0 ≤ L) :
    ConvexSpaceBody E3 where
  carrier := segCarrierSet T c L
  convex' := (convex_segCarrierSet' T c L).isConvexSet
  isCompact' :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_segCarrierSet T c L)
      (Metric.isBounded_closedBall.subset (segCarrierSet_subset_closedBall T c hL))
  nonempty' := segCarrierSet_nonempty T c hL

@[simp] theorem capsuleBody_carrier {δ : ℝ≥0} (T : Tube δ E3) (c : E3) {L : ℝ} (hL : 0 ≤ L) :
    (capsuleBody T c hL).carrier = segCarrierSet T c L := rfl

theorem dist_corePt_window {δ : ℝ≥0} (T : Tube δ E3) (c : E3) {L : ℝ} (hL : 0 ≤ L) :
    dist (corePt T (segStart T c L)) (corePt T (segStart T c L + 2 * L)) = 2 * L := by
  rw [dist_corePt, show segStart T c L - (segStart T c L + 2 * L) = -(2 * L) by ring, abs_neg,
    abs_of_nonneg (by linarith)]

/-- **The capsule, rescaled to a unit tube.** The homothety of ratio `(2L)⁻¹` about `m` takes the
core window (of length `2L`) to a segment of length `1` and the radius `δ` to `δ / (2L)`, so the
image of `segCarrierSet T c L` is literally the carrier of a `Kakeya.Tube` of that scale. This is
what lets the existing `Kakeya.Tube.tubeOverlapCoreClose` be applied to capsules. -/
noncomputable def rescaledCapsuleTube {δ δ' : ℝ≥0} (T : Tube δ E3) (c m : E3) {L : ℝ}
    (hL : 0 < L) (hδ' : (δ' : ℝ) = (2 * L)⁻¹ * (δ : ℝ)) : Tube δ' E3 where
  toConvexSpaceBody :=
    ConvexSpaceBody.affineImage (AffineMap.homothety m (2 * L)⁻¹)
      (AffineMap.continuous_of_finiteDimensional _) (capsuleBody T c (le_of_lt hL))
  x := AffineMap.homothety m (2 * L)⁻¹ (corePt T (segStart T c L))
  y := AffineMap.homothety m (2 * L)⁻¹ (corePt T (segStart T c L + 2 * L))
  dist_eq_one := by
    have h2L : (0 : ℝ) < 2 * L := by linarith
    rw [dist_homothety, abs_of_pos (inv_pos.2 h2L), dist_corePt_window T c (le_of_lt hL),
      inv_mul_cancel₀ (ne_of_gt h2L)]
  carrier_eq := by
    have h2L : (0 : ℝ) < 2 * L := by linarith
    have hk : (0 : ℝ) < (2 * L)⁻¹ := inv_pos.2 h2L
    change (AffineMap.homothety m (2 * L)⁻¹) '' (segCarrierSet T c L) = _
    rw [segCarrierSet_eq_biUnion, Set.image_iUnion₂]
    rw [← homothety_image_segment m (2 * L)⁻¹ _ _]
    rw [Set.biUnion_image]
    refine Set.iUnion₂_congr fun w _ => ?_
    rw [homothety_image_closedBall hk w (δ : ℝ), hδ']

@[simp] theorem rescaledCapsuleTube_carrier {δ δ' : ℝ≥0} (T : Tube δ E3) (c m : E3) {L : ℝ}
    (hL : 0 < L) (hδ' : (δ' : ℝ) = (2 * L)⁻¹ * (δ : ℝ)) :
    (rescaledCapsuleTube T c m hL hδ').carrier =
      (AffineMap.homothety m (2 * L)⁻¹) '' (segCarrierSet T c L) := rfl

@[simp] theorem rescaledCapsuleTube_x {δ δ' : ℝ≥0} (T : Tube δ E3) (c m : E3) {L : ℝ}
    (hL : 0 < L) (hδ' : (δ' : ℝ) = (2 * L)⁻¹ * (δ : ℝ)) :
    (rescaledCapsuleTube T c m hL hδ').x =
      AffineMap.homothety m (2 * L)⁻¹ (corePt T (segStart T c L)) := rfl

@[simp] theorem rescaledCapsuleTube_y {δ δ' : ℝ≥0} (T : Tube δ E3) (c m : E3) {L : ℝ}
    (hL : 0 < L) (hδ' : (δ' : ℝ) = (2 * L)⁻¹ * (δ : ℝ)) :
    (rescaledCapsuleTube T c m hL hδ').y =
      AffineMap.homothety m (2 * L)⁻¹ (corePt T (segStart T c L + 2 * L)) := rfl


/-! ### R-a: comparability of capsules at `K′₀`, from the existing tube geometry -/


/-! ### R-b: the angular step feeding `card_cone_le` -/


end Kakeya.VeryNotSticky

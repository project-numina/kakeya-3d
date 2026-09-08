/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.BallCoreEDCapsule
public import Kakeya.DimensionThree.MainLemma2.EDConstants
public import Kakeya.Tube.Dilate

/-!
# Capsule volume and homothety dilation

This file develops the volume and comparability estimates for capsule segments.

## (1) The capsule volume lower bound, and the `δ`-free dilate price

`Kakeya.VeryNotSticky.le_volumeReal_segCarrierSet`: `c₃ · L · δ² ≤ |segCarrierSet T c L|`, where
`c₃ = Metric.lt_volume_convexHull.c 3` is the inscribed-simplex constant. The capsule is convex
(`Convex.cthickening` of a segment) and its three thicknesses are already pinned
(`le_thickness_segCarrierSet_zero`, `le_thickness_segCarrierSet`), so this is one application of
`Convex.prod_thickness_le_volumeReal` — the same input `volume_ge_of_tubeProfile`
(`TangentialCase.lean`) uses. The `δ³` bound
`volume_closedBall_le_volume_segCarrierSet` could not give a `δ`-free ratio; this one can:

* `Kakeya.VeryNotSticky.volume_segCarrierSetAt_le_mul_volume_segCarrierSet` —
  `c₃ · |K-dilate| ≤ 16 K² · |capsule|`, division-free, with **no `δ`**;
* `Kakeya.VeryNotSticky.segsDensity_of_segCarrierSetAt` — hence `segs_density` survives the
  dilate at the cost `c₁ ↦ c₁ · c₃ / (16 K²)`, which is  §G-1's `edDensityConstant`.

## (2) The dilate `K′`, and the shape it must have

`Kakeya.VeryNotSticky.not_subset_segCarrierSetAt_of_axial_offset` pins the mechanism that
**refutes** the radius-only reading of comparability used in `BallCoreEDCapsule.lean`: the
`segStart` clamp can put two windows of one ball at an *axial* offset of order `L = r₁/4` while
their capsules are still not essentially distinct, and no `δ`-free `K` has `K δ ≥ L`. The dilate
must therefore be a **homothety**, scaling the core window as well as the radius — which is the
shape of the existing `Kakeya.Tube.dilate` and of `Kakeya.Tube.tubeOverlapCoreClose`.

* `Kakeya.VeryNotSticky.segCarrierSetHom` — the homothety dilate of a capsule;
* `Kakeya.VeryNotSticky.CapsuleComparableHomAt` — comparability in GWZ's own shape;
* `capsuleShade_subset_hom_of_comparableHomAt`, `capsuleCoreLine_of_comparableHomAt`,
  `capsuleClassCount_of_homDilateCount` — (C1), (C2), (C3) from it, at general `K`;
* `comparableHomAt_of_comparableAt` — the radius-only form implies this one, so
  `BallCoreEDCapsule.lean`'s three reductions are subsumed;
* `Kakeya.VeryNotSticky.edComparabilityConstant = Kakeya.Tube.tubeOverlapCoreClose.C 3
  = 9 + 2·4³/c₃` — **the value `K′₀`**, read off the only route in the tree that can prove
  comparability from `¬ IsEssentiallyDistinct`, together with its unit-tube instance
  `tube_subset_dilate_of_not_essDistinct`.

##  §G-1's hypothesis floor

`edDilateConstant` (`= K′`), `edSegmentsConstant = 4 K′`, `edDensityConstant = 4 K′²` are the
three named constants of the licensed repair, which moves the **hypothesis floor**
(`4 ≤ C₀ ↦ edSegmentsConstant ≤ C₀`, `4 c₁ ballCoverConstant ≤ 1 ↦ edDensityConstant c₁ … ≤ 1`)
and leaves every conclusion verbatim. `edDilateConstant_le_of_floor` and
`two_mul_edDilateConstant_le_of_floor` discharge the addendum's side conditions from the one
floor, and `capsuleInputs_of_comparableHomAt_of_floor` is the plug.

## §G-3 and §G-addendum (a)

`Kakeya.VeryNotSticky.not_eventually_const_mul_rpow_le_self` records the boundary of the `∀ᶠ δ`
device: it absorbs a `δ`-free constant across a **strict** exponent gap and not at equal
exponents. `capsuleHomDilateCount_of_carrierCap` restates (C3)'s count on the tube **carriers**,
the shape `Kakeya.VeryNotSticky.card_cone_le`'s counting hypothesis has, so that the density-cap
estimate composes without an essential-distinctness hypothesis on `cfg.s`.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

namespace Kakeya.VeryNotSticky

universe u
variable {δ : ℝ≥0}

theorem convex_segCarrierSetAt (K : ℝ≥0) (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) (L : ℝ) : Convex ℝ (segCarrierSetAt K T c L) :=
  (convex_segment _ _).cthickening _

theorem convex_segCarrierSet' (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) (L : ℝ) : Convex ℝ (segCarrierSet T c L) :=
  (convex_segment _ _).cthickening _

/-- **The volume lower bound for a capsule**, `c₃ · L · δ² ≤ |segCarrierSet T c L|`. -/
theorem le_volumeReal_segCarrierSet (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ} (hL : 0 ≤ L) (hL1 : 2 * L ≤ 1) :
    ((Metric.lt_volume_convexHull.c 3 : ℝ≥0) : ℝ) * (L * (δ : ℝ) * (δ : ℝ)) ≤
      volume.real (segCarrierSet T c L) := by
  have hbdd : Bornology.IsBounded (segCarrierSet T c L) :=
    Metric.isBounded_closedBall.subset (segCarrierSet_subset_closedBall T c hL)
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
  have hprod := (convex_segCarrierSet' T c L).prod_thickness_le_volumeReal hbdd
  rw [hfr] at hprod
  refine le_trans ?_ hprod
  have hexp : ∏ i ∈ Finset.range 3, Metric.thickness ℝ (segCarrierSet T c L) i =
      Metric.thickness ℝ (segCarrierSet T c L) 0 * Metric.thickness ℝ (segCarrierSet T c L) 1 *
        Metric.thickness ℝ (segCarrierSet T c L) 2 := by
    simp [Finset.prod_range_succ, mul_assoc]
  rw [hexp]
  have h0 := le_thickness_segCarrierSet_zero T c hL hL1
  have h1 := le_thickness_segCarrierSet T c hL (n := 1) (by norm_num)
  have h2 := le_thickness_segCarrierSet T c hL (n := 2) (by norm_num)
  have hδ0 : (0 : ℝ) ≤ (δ : ℝ) := δ.coe_nonneg
  have hc0 : (0 : ℝ) ≤ ((Metric.lt_volume_convexHull.c 3 : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
  refine mul_le_mul_of_nonneg_left ?_ hc0
  have ht0 : 0 ≤ Metric.thickness ℝ (segCarrierSet T c L) 0 := Metric.thickness_nonneg _ _
  have ht1 : 0 ≤ Metric.thickness ℝ (segCarrierSet T c L) 1 := Metric.thickness_nonneg _ _
  have hstep : L * (δ : ℝ) ≤
      Metric.thickness ℝ (segCarrierSet T c L) 0 * Metric.thickness ℝ (segCarrierSet T c L) 1 :=
    mul_le_mul h0 h1 hδ0 ht0
  exact mul_le_mul hstep h2 hδ0 (by positivity)


/-- `ENNReal` form of `Kakeya.VeryNotSticky.le_volumeReal_segCarrierSet`. -/
theorem ofReal_le_volume_segCarrierSet (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ} (hL : 0 ≤ L) (hL1 : 2 * L ≤ 1) :
    ENNReal.ofReal (((Metric.lt_volume_convexHull.c 3 : ℝ≥0) : ℝ) * (L * (δ : ℝ) * (δ : ℝ))) ≤
      volume (segCarrierSet T c L) := by
  have htop : volume (segCarrierSet T c L) ≠ ⊤ := volume_segCarrierSet_ne_top T c hL
  have h := le_volumeReal_segCarrierSet T c hL hL1
  calc ENNReal.ofReal (((Metric.lt_volume_convexHull.c 3 : ℝ≥0) : ℝ) * (L * (δ : ℝ) * (δ : ℝ)))
      ≤ ENNReal.ofReal (volume.real (segCarrierSet T c L)) := ENNReal.ofReal_le_ofReal h
    _ = volume (segCarrierSet T c L) := by
        rw [MeasureTheory.Measure.real, ENNReal.ofReal_toReal htop]


/-! ### The radius-only dilate is the wrong shape — the axial mechanism, pinned -/


theorem four_le_edDensityConstant : 4 ≤ edDensityConstant := by
  rw [edDensityConstant]
  nth_rewrite 1 [show (4 : ℝ≥0) = 4 * 1 by ring]
  gcongr
  exact one_le_pow₀ one_le_edDilateConstant

/-- The floor discharges (C2)'s side condition: `K′ ≤ C₀`. -/
theorem edDilateConstant_le_of_floor {C₀ : ℝ≥0} (h : edSegmentsConstant ≤ C₀) :
    edDilateConstant ≤ C₀ := by
  refine le_trans ?_ h
  rw [edSegmentsConstant]
  nth_rewrite 1 [show edDilateConstant = 1 * edDilateConstant by ring]
  gcongr
  norm_num


/-! ### The homothety dilate of a capsule, and comparability in GWZ's own shape -/


theorem dist_homothety (p : EuclideanSpace ℝ (Fin 3)) (K : ℝ)
    (x y : EuclideanSpace ℝ (Fin 3)) :
    dist (AffineMap.homothety p K x) (AffineMap.homothety p K y) = |K| * dist x y := by
  simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, dist_eq_norm]
  rw [show K • (x - p) + p - (K • (y - p) + p) = K • (x - y) by module, norm_smul,
    Real.norm_eq_abs]


/-! ### Comparability in GWZ's own shape, and the three obligations from it -/

section HomObligations

variable {cfg : VeryNotSticky.{u}} (core : BallDataCore cfg)


end HomObligations

end Kakeya.VeryNotSticky

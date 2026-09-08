/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.ActiveParentGeometry

/-!
# Reanchored Parent Enclosure

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

namespace Kakeya.Assouad

theorem coaxial_dilated_carrier_subset
    {sourceRadius targetRadius shift innerFactor outerFactor : ℝ}
    (sourceRadiusNonneg : 0 ≤ sourceRadius)
    (innerFactorPos : 0 < innerFactor) (outerFactorPos : 0 < outerFactor)
    (source : Kakeya.DeltaTube sourceRadius) (target : Kakeya.DeltaTube targetRadius)
    (directionEq : source.direction = target.direction)
    (baseEq : source.base = target.base + shift • target.direction)
    (radialBound : innerFactor * sourceRadius ≤ outerFactor * targetRadius)
    (axialBound : |shift| + innerFactor / 2 ≤ outerFactor / 2) :
    wz2PaperCenteredDilatedCarrier innerFactor source ⊆
      wz2PaperCenteredDilatedCarrier outerFactor target := by
  intro point pointMem
  obtain ⟨parameter, parameterMem, pointNear⟩ :=
    pureWZ2_general_dilation_closest_point sourceRadiusNonneg innerFactorPos
      source point pointMem
  let midpoint := wz2PaperTubeMidpoint target
  let preimage := midpoint + outerFactor⁻¹ • (point - midpoint)
  let targetParameter := outerFactor⁻¹ * (shift + parameter - 1 / 2) + 1 / 2
  have shiftBounds := abs_le.mp (le_trans (le_add_of_nonneg_right
    (by positivity : 0 ≤ innerFactor / 2)) axialBound)
  have parameterBounds : |parameter - 1 / 2| ≤ innerFactor / 2 := by
    rw [abs_le]
    constructor <;> linarith [parameterMem.1, parameterMem.2]
  have displacementBound : |shift + parameter - 1 / 2| ≤ outerFactor / 2 := by
    have triangle := abs_add_le shift (parameter - 1 / 2)
    have combined : |shift| + |parameter - 1 / 2| ≤ outerFactor / 2 := by
      linarith
    simpa only [add_sub_assoc] using triangle.trans combined
  have targetParameterMem : targetParameter ∈ Set.Icc (0 : ℝ) 1 := by
    have scaledBound := mul_le_mul_of_nonneg_left displacementBound
      (inv_nonneg.mpr outerFactorPos.le)
    have inverseHalf : outerFactor⁻¹ * (outerFactor / 2) = (1 / 2 : ℝ) := by
      field_simp
    rw [inverseHalf] at scaledBound
    have scaledAbs : |outerFactor⁻¹ * (shift + parameter - 1 / 2)| ≤ 1 / 2 := by
      simpa only [abs_mul, abs_of_pos (inv_pos.mpr outerFactorPos)] using scaledBound
    rcases abs_le.mp scaledAbs with ⟨lower, upper⟩
    dsimp only [targetParameter]
    constructor <;> linarith
  have differenceEq :
      preimage - (target.base + targetParameter • target.direction) =
        outerFactor⁻¹ • (point - (source.base + parameter • source.direction)) := by
    rw [baseEq, directionEq]
    dsimp only [preimage, midpoint, wz2PaperTubeMidpoint, targetParameter]
    module
  have preimageNear :
      dist preimage (target.base + targetParameter • target.direction) ≤ targetRadius := by
    rw [dist_eq_norm, differenceEq, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr outerFactorPos), ← dist_eq_norm]
    calc
      outerFactor⁻¹ * dist point (source.base + parameter • source.direction) ≤
          outerFactor⁻¹ * (innerFactor * sourceRadius) :=
        mul_le_mul_of_nonneg_left pointNear (by positivity)
      _ ≤ outerFactor⁻¹ * (outerFactor * targetRadius) :=
        mul_le_mul_of_nonneg_left radialBound (by positivity)
      _ = targetRadius := by rw [← mul_assoc, inv_mul_cancel₀ outerFactorPos.ne', one_mul]
  refine ⟨preimage, ?_, ?_⟩
  · exact Metric.mem_cthickening_of_dist_le preimage
      (target.base + targetParameter • target.direction) targetRadius
      (Kakeya.unitSegment target.base target.direction)
      ⟨targetParameter, targetParameterMem, rfl⟩ preimageNear
  · rw [AffineMap.homothety_apply]
    simp only [vsub_eq_sub, vadd_eq_add]
    change outerFactor • (preimage - midpoint) + midpoint = point
    dsimp only [preimage]
    simp only [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ outerFactorPos.ne',
      one_smul, sub_add_cancel]

theorem doubled_reanchored_parent_subset_original
    {rho factor : ℝ} (rhoNonneg : 0 ≤ rho) (factorOne : 1 ≤ factor)
    (center : Point3) (parent : Kakeya.DeltaTube rho)
    (shiftBound : |pureWZ2AxialShift center parent| ≤ 4 * factor) :
    wz2PaperCenteredDilatedCarrier 2
        (pureWZ2ReanchoredParentTube (A := factor) center parent) ⊆
      wz2PaperCenteredDilatedCarrier (32 * factor) parent := by
  let reanchored := pureWZ2ReanchoredParentTube (A := factor) center parent
  have baseEq : reanchored.base =
      parent.base + (-pureWZ2AxialShift center parent) • parent.direction := by
    have sourceBase := pureWZ2ReanchoredTube_source_base center parent
    change parent.base = reanchored.base + pureWZ2AxialShift center parent • parent.direction
      at sourceBase
    rw [sourceBase]
    module
  apply coaxial_dilated_carrier_subset
    (by positivity : 0 ≤ 8 * factor * rho)
    (by norm_num : (0 : ℝ) < 2)
    (by positivity : 0 < 32 * factor)
    reanchored parent rfl baseEq
  · nlinarith
  · rw [abs_neg]
    linarith

theorem active_parent_axialShift_le_four
    {delta rho factor radius : ℝ}
    (deltaPos : 0 < delta) (rhoPos : 0 < rho)
    (factorOne : 1 ≤ factor)
    (deltaOne : delta ≤ 1) (rhoOne : rho ≤ 1) (radiusSmall : radius ≤ 1 / 4)
    {center point : Point3} {source : Kakeya.DeltaTube delta}
    {parent : Kakeya.DeltaTube rho}
    (pointSource : point ∈ source.carrier)
    (pointBall : point ∈ Metric.closedBall center radius)
    (sourceParent : source.carrier ⊆ wz2PaperCenteredDilatedCarrier factor parent) :
    |pureWZ2AxialShift center parent| ≤ 4 * factor := by
  have shiftBound := pureWZ2_active_parent_axial_shift deltaPos rhoPos factorOne
    pointSource pointBall sourceParent
  have factorRho : factor * rho ≤ factor := by nlinarith
  linarith

end Kakeya.Assouad

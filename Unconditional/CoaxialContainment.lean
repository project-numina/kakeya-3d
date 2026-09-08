/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import MyLeanRepo.Kakeya.AssertionD
import Mathlib.Tactic

/-!
# Coaxial Containment

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

namespace Kakeya.Assouad

theorem coaxial_source_carrier_subset_homothety_hundred
    {delta shift : ℝ}
    (deltaNonneg : 0 ≤ delta)
    (source target : Kakeya.DeltaTube delta)
    (directionEq : source.direction = target.direction)
    (baseEq : source.base = target.base + shift • target.direction)
    (shiftBound : |shift| ≤ 1) :
    source.carrier ⊆
      AffineMap.homothety
          (target.base + (1 / 2 : ℝ) • target.direction)
          (100 : ℝ) '' target.carrier := by
  have segmentCompact :
      IsCompact (Kakeya.unitSegment source.base source.direction) := by
    exact isCompact_Icc.image
      (continuous_const.add (continuous_id.smul continuous_const))
  intro point pointMem
  rw [Kakeya.DeltaTube.carrier,
    segmentCompact.cthickening_eq_biUnion_closedBall deltaNonneg] at pointMem
  rcases Set.mem_iUnion₂.mp pointMem with ⟨axisPoint, axisPointMem, pointNear⟩
  rcases axisPointMem with ⟨parameter, parameterMem, rfl⟩
  have pointNear' :
      dist point (source.base + parameter • source.direction) ≤ delta :=
    Metric.mem_closedBall.mp pointNear
  let midpoint := target.base + (1 / 2 : ℝ) • target.direction
  let preimage := midpoint + (1 / 100 : ℝ) • (point - midpoint)
  let targetParameter := (shift + parameter - 1 / 2) / 100 + 1 / 2
  have targetParameterMem : targetParameter ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp only [targetParameter]
    rcases abs_le.mp shiftBound with ⟨shiftLower, shiftUpper⟩
    constructor <;> linarith [parameterMem.1, parameterMem.2]
  have differenceEq :
      preimage - (target.base + targetParameter • target.direction) =
        (1 / 100 : ℝ) •
          (point - (source.base + parameter • source.direction)) := by
    rw [baseEq, directionEq]
    dsimp only [preimage, midpoint, targetParameter]
    module
  have preimageNear :
      dist preimage (target.base + targetParameter • target.direction) ≤ delta := by
    rw [dist_eq_norm, differenceEq, norm_smul]
    norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 100)]
    rw [← dist_eq_norm]
    calc
      (1 / 100 : ℝ) *
          dist point (source.base + parameter • source.direction) ≤
          (1 / 100 : ℝ) * delta :=
        mul_le_mul_of_nonneg_left pointNear' (by norm_num)
      _ ≤ delta := by linarith
  refine ⟨preimage, ?_, ?_⟩
  · exact Metric.mem_cthickening_of_dist_le preimage
      (target.base + targetParameter • target.direction) delta
      (Kakeya.unitSegment target.base target.direction)
      ⟨targetParameter, targetParameterMem, rfl⟩ preimageNear
  · rw [AffineMap.homothety_apply]
    simp only [vsub_eq_sub, vadd_eq_add]
    dsimp only [preimage, midpoint]
    module

end Kakeya.Assouad

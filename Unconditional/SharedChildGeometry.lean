/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.CompleteFiberOverlap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.ProjectiveDirectionTriangle

/-!
# Shared Child Geometry

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

namespace Kakeya.Assouad

theorem shared_child_parent_parameter_bounds
    {delta rho factor : ℝ}
    (deltaPos : 0 < delta) (rhoPos : 0 < rho) (factorOne : 1 ≤ factor)
    (scaleSmall : rho ≤ 1 / (200 * factor))
    (childScale : delta ≤ factor * rho)
    (child : Kakeya.DeltaTube delta) (first second : Kakeya.DeltaTube rho)
    (childFirst : child.carrier ⊆ wz2PaperCenteredDilatedCarrier factor first)
    (childSecond : child.carrier ⊆ wz2PaperCenteredDilatedCarrier factor second) :
    ‖second.direction - inner ℝ second.direction first.direction • first.direction‖ ≤
        8 * factor * rho ∧
    ‖(wz2PaperTubeMidpoint second - wz2PaperTubeMidpoint first) -
        inner ℝ (wz2PaperTubeMidpoint second - wz2PaperTubeMidpoint first)
          first.direction • first.direction‖ ≤ (4 * factor ^ 2 + 2 * factor) * rho ∧
    |inner ℝ (wz2PaperTubeMidpoint second - wz2PaperTubeMidpoint first)
        first.direction| ≤ 3 * factor ∧
    1 / 2 ≤ |inner ℝ second.direction first.direction| := by
  have factorPos : 0 < factor := by linarith
  have factorRhoSmall : factor * rho ≤ 1 / 200 := by
    have scaled := (le_div_iff₀ (by positivity : 0 < 200 * factor)).mp scaleSmall
    nlinarith
  have rhoOne : rho ≤ 1 := by nlinarith
  have commonFirst :
      ‖child.direction - inner ℝ child.direction first.direction • first.direction‖ ≤
        2 * factor * rho :=
    (gwz_direction_constraint deltaPos rhoPos factorOne childScale
      child first childFirst).trans (by linarith)
  have commonSecond :
      ‖child.direction - inner ℝ child.direction second.direction • second.direction‖ ≤
        2 * factor * rho :=
    (gwz_direction_constraint deltaPos rhoPos factorOne childScale
      child second childSecond).trans (by linarith)
  have directionBound :
      ‖second.direction - inner ℝ second.direction first.direction • first.direction‖ ≤
        8 * factor * rho := by
    have bound := pureWZ2_projective_direction_triangle
      first.direction_unit second.direction_unit child.direction_unit
      (by positivity : 0 ≤ 2 * factor * rho)
      (by nlinarith : 2 * factor * rho ≤ 1 / 2) commonFirst commonSecond
    nlinarith
  let commonPoint := wz2PaperTubeMidpoint child
  have commonPointMem : commonPoint ∈ child.carrier :=
    wz2_paper_tubeMidpoint_mem_carrier child deltaPos.le
  obtain ⟨firstParameter, firstParameterMem, firstNear⟩ :=
    pureWZ2_general_dilation_closest_point rhoPos.le factorPos first commonPoint
      (childFirst commonPointMem)
  obtain ⟨secondParameter, secondParameterMem, secondNear⟩ :=
    pureWZ2_general_dilation_closest_point rhoPos.le factorPos second commonPoint
      (childSecond commonPointMem)
  let firstAxis := first.base + firstParameter • first.direction
  let secondAxis := second.base + secondParameter • second.direction
  let residual := secondAxis - commonPoint + (commonPoint - firstAxis)
  have firstParameterBound : |firstParameter - 1 / 2| ≤ factor / 2 := by
    rw [abs_le]
    constructor <;> linarith [firstParameterMem.1, firstParameterMem.2]
  have secondParameterBound : |1 / 2 - secondParameter| ≤ factor / 2 := by
    rw [abs_le]
    constructor <;> linarith [secondParameterMem.1, secondParameterMem.2]
  have residualBound : ‖residual‖ ≤ 2 * factor * rho := by
    calc
      ‖residual‖ ≤ ‖secondAxis - commonPoint‖ + ‖commonPoint - firstAxis‖ :=
        norm_add_le _ _
      _ ≤ factor * rho + factor * rho := by
        apply add_le_add
        · simpa only [← dist_eq_norm, dist_comm] using secondNear
        · simpa only [← dist_eq_norm] using firstNear
      _ = 2 * factor * rho := by ring
  have displacementEq : wz2PaperTubeMidpoint second - wz2PaperTubeMidpoint first =
      (1 / 2 - secondParameter) • second.direction + residual +
        (firstParameter - 1 / 2) • first.direction := by
    dsimp only [wz2PaperTubeMidpoint, residual, firstAxis, secondAxis]
    module
  have firstInner : inner ℝ first.direction first.direction = 1 := by
    rw [real_inner_self_eq_norm_sq, first.direction_unit]
    norm_num
  have perpendicularEq :
      (wz2PaperTubeMidpoint second - wz2PaperTubeMidpoint first) -
        inner ℝ (wz2PaperTubeMidpoint second - wz2PaperTubeMidpoint first)
          first.direction • first.direction =
      (1 / 2 - secondParameter) •
          (second.direction - inner ℝ second.direction first.direction • first.direction) +
        (residual - inner ℝ residual first.direction • first.direction) := by
    rw [displacementEq]
    simp only [inner_add_left, real_inner_smul_left, firstInner]
    module
  have midpointTransverse :
      ‖(wz2PaperTubeMidpoint second - wz2PaperTubeMidpoint first) -
        inner ℝ (wz2PaperTubeMidpoint second - wz2PaperTubeMidpoint first)
          first.direction • first.direction‖ ≤ (4 * factor ^ 2 + 2 * factor) * rho := by
    rw [perpendicularEq]
    calc
      _ ≤ ‖(1 / 2 - secondParameter) •
          (second.direction - inner ℝ second.direction first.direction • first.direction)‖ +
          ‖residual - inner ℝ residual first.direction • first.direction‖ := norm_add_le _ _
      _ ≤ (factor / 2) * (8 * factor * rho) + 2 * factor * rho := by
        rw [norm_smul, Real.norm_eq_abs]
        apply add_le_add
        · exact mul_le_mul secondParameterBound directionBound (norm_nonneg _) (by positivity)
        · exact (pureWZ2_perp_norm_le first.direction residual first.direction_unit).trans
            residualBound
      _ = (4 * factor ^ 2 + 2 * factor) * rho := by ring
  have midpointNorm :
      ‖wz2PaperTubeMidpoint second - wz2PaperTubeMidpoint first‖ ≤ 3 * factor := by
    rw [displacementEq]
    calc
      _ ≤ ‖(1 / 2 - secondParameter) • second.direction‖ + ‖residual‖ +
          ‖(firstParameter - 1 / 2) • first.direction‖ := norm_add₃_le
      _ = |1 / 2 - secondParameter| + ‖residual‖ + |firstParameter - 1 / 2| := by
        simp only [norm_smul, Real.norm_eq_abs, second.direction_unit,
          first.direction_unit, mul_one]
      _ ≤ factor / 2 + 2 * factor * rho + factor / 2 := by
        linarith
      _ ≤ 3 * factor := by nlinarith
  have midpointLongitudinal :
      |inner ℝ (wz2PaperTubeMidpoint second - wz2PaperTubeMidpoint first)
        first.direction| ≤ 3 * factor := by
    have bound := abs_real_inner_le_norm
      (wz2PaperTubeMidpoint second - wz2PaperTubeMidpoint first) first.direction
    rw [first.direction_unit, mul_one] at bound
    exact bound.trans midpointNorm
  have directionInner : 1 / 2 ≤ |inner ℝ second.direction first.direction| := by
    have perpendicularSquare :
        ‖second.direction - inner ℝ second.direction first.direction • first.direction‖ ^ 2 =
          1 - (inner ℝ second.direction first.direction) ^ 2 := by
      rw [norm_sub_sq_real, inner_smul_right, norm_smul,
        first.direction_unit, second.direction_unit]
      simp [Real.norm_eq_abs, sq_abs]
      ring
    have perpendicularNonneg := norm_nonneg
      (second.direction - inner ℝ second.direction first.direction • first.direction)
    have perpendicularSmall :
        ‖second.direction - inner ℝ second.direction first.direction • first.direction‖ ≤
          1 / 2 := by nlinarith
    nlinarith [sq_abs (inner ℝ second.direction first.direction),
      abs_nonneg (inner ℝ second.direction first.direction)]
  exact ⟨directionBound, midpointTransverse, midpointLongitudinal, directionInner⟩

end Kakeya.Assouad

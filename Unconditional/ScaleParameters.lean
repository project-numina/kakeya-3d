/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Kakeya.DimensionThree.MainLemma2.GridRounding
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12Extremal
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.LogAbsorption
import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption

/-!
# Scale Parameters

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

namespace KakeyaLink.ScaleParameters


/-- A prescribed positive window loss eventually strictly exceeds one grid step. -/
theorem exists_ssfGridLen_step_threshold
    (windowLoss : Real) (hwindowLoss : 0 < windowLoss) :
    ∃ delta0 : NNReal, 0 < delta0 ∧ delta0 < 1 ∧
      ∀ {delta : NNReal}, 0 < delta → delta ≤ delta0 →
        0 < Tube.ssfGridLen delta ∧
        (1 : Real) / (Tube.ssfGridLen delta : Real) < windowLoss := by
  let A : Real := 1 / windowLoss + 1
  let delta0 : NNReal := ⟨Real.exp (-Real.exp A), (Real.exp_pos _).le⟩
  have hA : 0 < A := by dsimp [A]; positivity
  have hdelta0 : 0 < delta0 := Real.exp_pos _
  have hdelta0One : delta0 < 1 := by
    change Real.exp (-Real.exp A) < 1
    exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos (Real.exp_pos _))
  refine ⟨delta0, hdelta0, hdelta0One, ?_⟩
  intro delta hdelta hle
  have hd : 0 < (delta : Real) := hdelta
  have hlog : Real.log (delta : Real) ≤ -Real.exp A := by
    have h := Real.log_le_log hd (show (delta : Real) ≤ Real.exp (-Real.exp A) from hle)
    simpa only [Real.log_exp] using h
  have hinner : Real.exp A ≤ Real.log (1 / (delta : Real)) := by
    rw [one_div, Real.log_inv]
    linarith
  have houter : A ≤ Real.log (Real.log (1 / (delta : Real))) := by
    have h := Real.log_le_log (Real.exp_pos A) hinner
    simpa only [Real.log_exp] using h
  have hN : A ≤ (Tube.ssfGridLen delta : Real) :=
    houter.trans (Nat.le_ceil _)
  have hNpos : 0 < (Tube.ssfGridLen delta : Real) := hA.trans_le hN
  refine ⟨by exact_mod_cast hNpos, ?_⟩
  apply (one_div_lt hNpos hwindowLoss).2
  dsimp [A] at hN
  linarith


/-- Retained shaded mass yields density when the new family has no larger tube mass. -/
theorem isLambdaDense_of_retained_mass
    {delta : Real}
    {source target : Kakeya.Streamlined.TubeFamily delta}
    (sourceShading : Kakeya.Streamlined.TubeShading source)
    (targetShading : Kakeya.Streamlined.TubeShading target)
    {inputDensity outputDensity retention : ENNReal}
    (hsourceDense : sourceShading.IsLambdaDense inputDensity)
    (htubeMass : target.toBodyFamily.mass ≤ source.toBodyFamily.mass)
    (hretained : retention * sourceShading.mass ≤ targetShading.mass)
    (hdensity : outputDensity ≤ retention * inputDensity) :
    targetShading.IsLambdaDense outputDensity := by
  change outputDensity * target.toBodyFamily.mass ≤ targetShading.mass
  calc
    _ ≤ (retention * inputDensity) * source.toBodyFamily.mass := mul_le_mul' hdensity htubeMass
    _ = retention * (inputDensity * source.toBodyFamily.mass) := mul_assoc _ _ _
    _ ≤ retention * sourceShading.mass := mul_le_mul_right hsourceDense retention
    _ ≤ targetShading.mass := hretained


end KakeyaLink.ScaleParameters

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineTwoScale

/-!
# Polylogarithmic envelope for the public one-scale loss

Quantifies `spineScaleLoss 3 N sigma` in dimension three. `source_step5PackingRatio_logb`
handles the Step 5 packing ratio; `source_spineScaleLoss_le_logarithmic_six` bounds the loss
by six logarithmic factors with a coefficient independent of `N` and the scale;
`source_polynomialCard_logarithms_le` controls every intermediate-scale logarithm under a
fixed polynomial cardinal ceiling. `source_exists_spineScaleLoss_polylog_envelope` produces
one fixed exponent `K` such that eventually `spineScaleLoss 3 N sigma` is at most the polylog
envelope whenever `N <= A * delta^(-B)`. Used by the selection-loss file.
-/

@[expose] public section

open scoped NNReal

open Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ML2Reduction

/-- The public Step 5 ratio at dimension three, including the empty-family convention. -/
theorem source_step5PackingRatio_logb (N : Nat) {sigma : ℝ≥0}
    (hsigma : 0 < sigma) :
    Real.logb 2 (ShadedBody.step5PackingRatio 3 N sigma : ℝ) =
      6 + Real.logb 2 6 + Real.logb 2 (max 1 N : Nat) +
        3 * Real.logb 2 (1 / (sigma : ℝ)) := by
  have hmax : 1 <= max 1 N := le_max_left _ _
  have hp : 0 < (step1UpperBdAtScale 3 (max 1 N) /
      step1LowerBdAtScale 3 sigma : ℝ≥0) := by
    rw [step1UpperBdAtScale_div_step1LowerBdAtScale 3 (max 1 N) hsigma]
    have hmax' : (0 : ℝ≥0) < (max 1 N : Nat) := by exact_mod_cast (Nat.zero_lt_one.trans_le hmax)
    positivity
  have hp' : (((step1UpperBdAtScale 3 (max 1 N) /
      step1LowerBdAtScale 3 sigma : ℝ≥0) : ℝ)) ≠ 0 :=
    ne_of_gt (NNReal.coe_pos.mpr hp)
  rw [ShadedBody.step5PackingRatio, mul_div_assoc, NNReal.coe_mul,
    NNReal.coe_pow, NNReal.coe_ofNat, Real.logb_mul (by norm_num) hp',
    Real.logb_pow, Real.logb_self_eq_one (by norm_num),
    logb_step1UpperBdAtScale_div_step1LowerBdAtScale 3 hmax hsigma]
  norm_num
  ring

/-- The actual public loss has six logarithmic factors. The coefficient is independent of
both the input cardinality and the scale; no asymptotic loss is assumed here. -/
theorem source_spineScaleLoss_le_logarithmic_six :
    ∃ C : ℝ≥0, 1 <= C /\
      forall (N : Nat) (sigma : ℝ≥0), 0 < sigma -> sigma <= 1 ->
        spineScaleLoss 3 N sigma <= C *
          Real.toNNReal ((1 + Real.logb 2 (max 1 N : Nat) +
            Real.logb 2 (1 / (sigma : ℝ))) ^ (6 : Nat)) := by
  let c : ℝ≥0 := 12800 * factoringStep5OverlapConstant 3 *
    ShadedBody.rhoTubesGeometricLoss 3
  refine ⟨max 1 (max c (ShadedBody.rhoTubesBallLoss 3)), le_max_left _ _, ?_⟩
  intro N sigma hsigma hsigma1
  let x : ℝ := Real.logb 2 (max 1 N : Nat)
  let y : ℝ := Real.logb 2 (1 / (sigma : ℝ))
  have hx : 0 <= x := Real.logb_nonneg (by norm_num) (by exact_mod_cast le_max_left 1 N)
  have hs : 0 < (sigma : ℝ) := NNReal.coe_pos.mpr hsigma
  have hy : 0 <= y := Real.logb_nonneg (by norm_num)
    ((le_div_iff₀ hs).mpr (by simpa using (NNReal.coe_le_coe.mpr hsigma1)))
  have hlog6 : Real.logb 2 6 <= 3 := by
    calc
      Real.logb 2 6 <= Real.logb 2 ((2 : ℝ)^3) :=
        Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by norm_num)
      _ = 3 := by rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]; norm_num
  let L : ℝ≥0 := Real.toNNReal (1 + x + y)
  have hL : (L : ℝ) = 1 + x + y := Real.coe_toNNReal _ (by positivity)
  have hL1 : 1 <= L := by exact_mod_cast (show (1 : ℝ) <= (L : ℝ) by rw [hL]; linarith)
  have hnat : ((Nat.log 2 N + 1 : Nat) : ℝ≥0) <= L := by
    have hlog : (Nat.log 2 N : ℝ) <= x := by
      by_cases hN : N = 0
      · subst N; simp [x]
      · have hN1 : 1 <= N := Nat.one_le_iff_ne_zero.mpr hN
        simpa [x, max_eq_right hN1] using Real.natLog_le_logb N 2
    apply NNReal.coe_le_coe.mp
    push_cast
    rw [hL]
    linarith
  have hstep1 : factoringStep1AtScaleConstant 3 N sigma <= 20 * L := by
    by_cases hN : N = 0
    · subst N
      simp only [factoringStep1AtScaleConstant_def, factoringStep1PigeonholeConstant,
        factoringStep1FiberPigeonholeConstant]
      rw [← NNReal.coe_div, coe_step1UpperBdAtScale_div_step1LowerBdAtScale 3 0 hsigma]
      norm_num
      exact (by norm_num : (2 : ℝ≥0) <= 20).trans
        (le_mul_of_one_le_right (by norm_num) hL1)
    · have hN1 : 1 <= N := Nat.one_le_iff_ne_zero.mpr hN
      apply NNReal.coe_le_coe.mp
      rw [coe_factoringStep1AtScaleConstant 3 hN1 hsigma hsigma1]
      norm_num only [Nat.factorial, NNReal.coe_mul, NNReal.coe_ofNat, Nat.cast_ofNat,
        Nat.cast_mul, Nat.cast_one, mul_one]
      rw [hL]
      have hxN : Real.logb 2 N = x := by simp [x, max_eq_right hN1]
      rw [hxN]
      dsimp [y] at hy ⊢
      linarith
  have hstep23 : (factoringStep2Step3Constant N : ℝ≥0) <= 4 * L ^ 4 := by
    rw [factoringStep2Step3Constant_eq]
    push_cast
    gcongr
    simpa only [Nat.cast_add, Nat.cast_one] using hnat
  have hstep5 : ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant 3
      (ShadedBody.step5PackingRatio 3 N sigma) <=
        80 * factoringStep5OverlapConstant 3 * L := by
    unfold ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant
      factoringStep1FiberPigeonholeConstant
    simp only [NNReal.coe_one, div_one, source_step5PackingRatio_logb N hsigma]
    have hbracket : Real.toNNReal (1 + (6 + Real.logb 2 6 +
        Real.logb 2 (max 1 N : Nat) + 3 * Real.logb 2 (1 / (sigma : ℝ)))) <= 10 * L := by
      apply Real.toNNReal_le_iff_le_coe.mpr
      rw [NNReal.coe_mul, NNReal.coe_ofNat, hL]
      change 1 + (6 + Real.logb 2 6 + x + 3 * y) <= 10 * (1 + x + y)
      linarith
    calc
      _ <= 4 * factoringStep5OverlapConstant 3 * (2 * (10 * L)) := by gcongr
      _ = _ := by ring
  have hraw : 2 * factoringStep1Step2AtScaleConstant 3 N sigma *
      (factoringStep3Constant N : ℝ≥0) *
      ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant 3
        (ShadedBody.step5PackingRatio 3 N sigma) *
      ShadedBody.rhoTubesGeometricLoss 3 <= c * L ^ 6 := by
    calc
      _ = 2 * factoringStep1AtScaleConstant 3 N sigma *
          (factoringStep2Step3Constant N : ℝ≥0) *
          ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant 3
            (ShadedBody.step5PackingRatio 3 N sigma) *
          ShadedBody.rhoTubesGeometricLoss 3 := by
        simp only [factoringStep1Step2AtScaleConstant, factoringStep2Step3Constant,
          Nat.cast_mul]
        ring
      _ <= 2 * (20 * L) * (4 * L ^ 4) *
          (80 * factoringStep5OverlapConstant 3 * L) *
          ShadedBody.rhoTubesGeometricLoss 3 := by gcongr
      _ = c * L ^ 6 := by dsimp [c]; ring
  have hL6 : 1 <= L ^ 6 := one_le_pow₀ hL1
  change spineScaleLoss 3 N sigma <=
    max 1 (max c (ShadedBody.rhoTubesBallLoss 3)) * Real.toNNReal ((1 + x + y)^6)
  rw [Real.toNNReal_pow (by positivity)]
  change spineScaleLoss 3 N sigma <= max 1 (max c (ShadedBody.rhoTubesBallLoss 3)) * L^6
  unfold spineScaleLoss ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C
  simp only [one_pow, one_mul]
  apply max_le
  · exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) hL6
  · apply max_le
    · exact hraw.trans (mul_le_mul_left ((le_max_left _ _).trans (le_max_right _ _)) _)
    · exact (le_mul_of_one_le_right (by positivity) hL6).trans
        (mul_le_mul_left ((le_max_right _ _).trans (le_max_right _ _)) _)

/-- A fixed polynomial cardinal ceiling controls every intermediate-scale logarithm.
The coefficient is chosen before all runtime scales and cardinalities. -/
theorem source_polynomialCard_logarithms_le (A : ℝ≥0) (B : ℝ)
    (hA : 0 < A) (hB : 0 <= B) :
    ∃ D : ℝ, 1 <= D /\
      forall (delta sigma : ℝ≥0) (N : Nat),
        0 < delta -> delta <= sigma -> sigma <= 1 ->
        (N : ℝ≥0) <= A * delta ^ (-B) ->
        1 + Real.logb 2 (max 1 N : Nat) + Real.logb 2 (1 / (sigma : ℝ)) <=
          D * (2 + Real.logb 2 (1 / (delta : ℝ))) := by
  let a : ℝ := |Real.logb 2 (A : ℝ)|
  have ha : 0 <= a := abs_nonneg _
  refine ⟨2 + a + B, by linarith, ?_⟩
  intro delta sigma N hdelta hds hsigma1 hcard
  have hd : 0 < (delta : ℝ) := NNReal.coe_pos.mpr hdelta
  have hs : 0 < (sigma : ℝ) := hd.trans_le (NNReal.coe_le_coe.mpr hds)
  have hd1 : (delta : ℝ) <= 1 := by exact_mod_cast hds.trans hsigma1
  let t : ℝ := Real.logb 2 (1 / (delta : ℝ))
  have ht : 0 <= t := Real.logb_nonneg (by norm_num)
    ((le_div_iff₀ hd).mpr (by simpa using hd1))
  have hAa : Real.logb 2 (A : ℝ) <= a := le_abs_self _
  have hN : Real.logb 2 (max 1 N : Nat) <= a + B * t := by
    by_cases hNzero : N = 0
    · subst N
      simp only [max_eq_left (by omega : (0 : Nat) <= 1), Nat.cast_one, Real.logb_one]
      positivity
    · have hNpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hNzero
      have hN1 : 1 <= N := Nat.one_le_iff_ne_zero.mpr hNzero
      have hcard' : (N : ℝ) <= (A : ℝ) * (delta : ℝ)^(-B) := by exact_mod_cast hcard
      have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hNpos hcard'
      rw [Real.logb_mul (NNReal.coe_pos.mpr hA).ne' (Real.rpow_pos_of_pos hd _).ne',
        Real.logb_rpow_eq_mul_logb_of_pos hd] at hlog
      have ht' : t = - Real.logb 2 (delta : ℝ) := by simp [t, one_div, Real.logb_inv]
      rw [max_eq_right hN1]
      rw [ht']
      nlinarith
  have hscale : Real.logb 2 (1 / (sigma : ℝ)) <= t :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity)
      (one_div_le_one_div_of_le hd (NNReal.coe_le_coe.mpr hds))
  nlinarith

/-- H0's uniform fixed-polylog envelope for the actual public one-scale constant.
The fixed exponent and the eventual scale threshold precede sigma and N. -/
theorem source_exists_spineScaleLoss_polylog_envelope (A : ℝ≥0) (B : ℝ)
    (hA : 0 < A) (hB : 0 <= B) :
    ∃ K : Nat, ∀ᶠ delta : ℝ≥0 in nhdsWithin 0 (Set.Ioi 0),
      forall (sigma : ℝ≥0) (N : Nat),
        0 < delta -> delta <= sigma -> sigma <= 1 ->
        (N : ℝ≥0) <= A * delta ^ (-B) ->
        spineScaleLoss 3 N sigma <=
          Real.toNNReal ((2 + Real.logb 2 (1 / (delta : ℝ))) ^ K) := by
  obtain ⟨C, hC, hbound⟩ := source_spineScaleLoss_le_logarithmic_six
  obtain ⟨D, hD, hlogs⟩ := source_polynomialCard_logarithms_le A B hA hB
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((C : ℝ) * D^6)
    (by norm_num : (1 : ℝ) < 2)
  refine ⟨6 + k, Filter.Eventually.of_forall ?_⟩
  intro delta sigma N hdelta hds hsigma1 hcard
  have hd : 0 < (delta : ℝ) := NNReal.coe_pos.mpr hdelta
  have hd1 : (delta : ℝ) <= 1 := by exact_mod_cast hds.trans hsigma1
  let t : ℝ := 2 + Real.logb 2 (1 / (delta : ℝ))
  have ht : 2 <= t := by
    have := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2)
      (show (1 : ℝ) <= 1 / (delta : ℝ) from (le_div_iff₀ hd).mpr (by linarith))
    dsimp [t]
    linarith
  have hcoef : (C : ℝ) * D^6 <= t^k :=
    hk.le.trans (pow_le_pow_left₀ (by norm_num) ht k)
  have hlog := hlogs delta sigma N hdelta hds hsigma1 hcard
  have hx : 0 <= 1 + Real.logb 2 (max 1 N : Nat) +
      Real.logb 2 (1 / (sigma : ℝ)) := by
    have hn := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2)
      (show (1 : ℝ) <= (max 1 N : Nat) by exact_mod_cast le_max_left 1 N)
    have hs : 0 < (sigma : ℝ) := hd.trans_le (NNReal.coe_le_coe.mpr hds)
    have hy := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2)
      (show (1 : ℝ) <= 1 / (sigma : ℝ) from (le_div_iff₀ hs).mpr
        (by simpa only [one_mul, NNReal.coe_one] using NNReal.coe_le_coe.mpr hsigma1))
    positivity
  calc
    spineScaleLoss 3 N sigma <= C * Real.toNNReal
        ((1 + Real.logb 2 (max 1 N : Nat) + Real.logb 2 (1 / (sigma : ℝ)))^6) :=
      hbound N sigma (hdelta.trans_le hds) hsigma1
    _ <= Real.toNNReal (t ^ (6 + k)) := by
      apply NNReal.coe_le_coe.mp
      rw [NNReal.coe_mul, Real.coe_toNNReal _ (by positivity),
        Real.coe_toNNReal _ (by positivity)]
      calc
        _ <= (C : ℝ) * (D * t)^6 := by gcongr
        _ = ((C : ℝ) * D^6) * t^6 := by ring
        _ <= t^k * t^6 := mul_le_mul_of_nonneg_right hcoef (by positivity)
        _ = t^(6+k) := by rw [pow_add]; ring

end Kakeya.ML2Reduction

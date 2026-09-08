/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.BoundedSourceCardLog

/-!
A common logarithmic envelope for the fixed spatial, color, degree, and
overlap losses in the finite-scale joint geometric selection.
-/

noncomputable section

namespace KakeyaLink.JointSelection

/-- All fixed selection costs are absorbed after the exponent and scale
threshold are chosen, uniformly over the source cardinality bound. -/
theorem exists_selection_polylog_envelope
    (R : ℝ) (hR : 1 ≤ R) (coordinateCount : ℕ)
    (spatialLoss fineColorCount parentColorCount : ℕ)
    (hspatial : 0 < spatialLoss)
    (hfine : 0 < fineColorCount) (hparent : 0 < parentColorCount)
    (overlap : ENNReal) (hoverlap : overlap ≠ ⊤) :
    ∃ logExponent : ℕ, ∃ delta0 : ℝ,
      0 < delta0 ∧ delta0 ≤ 1 / 1600 ∧
      ∀ {delta : ℝ}, 0 < delta → delta ≤ delta0 →
      ∀ cardinality : ℕ,
        (cardinality : ℝ) ≤ (37 * R : ℝ) ^ 6 * delta ^ (-6 : ℝ) →
        let G : ENNReal := ENNReal.ofReal (Real.log (1 / delta)) ^ logExponent
        1 ≤ G ∧
        (spatialLoss : ENNReal) *
            ((fineColorCount * parentColorCount ^ coordinateCount : ℕ) : ENNReal) *
            8 * (Nat.log 2 (2 * cardinality) + 1 : ENNReal) ^
              (coordinateCount + 2) ≤ G ∧
        16 * ((coordinateCount + 1 : ℕ) : ENNReal) *
            (Nat.log 2 (2 * cardinality) + 1 : ENNReal) ^
              (coordinateCount + 1) ≤ G ∧
        overlap ≤ G := by
  let a : ℝ := Real.log (2 * (37 * R) ^ 6) / Real.log 2 + 1
  let b : ℝ := 6 / Real.log 2
  let C : ℝ := |a| + |b| + 1
  let weightCoefficient : ℕ :=
    spatialLoss * (fineColorCount * parentColorCount ^ coordinateCount) * 8
  let degreeCoefficient : ℕ := 16 * (coordinateCount + 1)
  let A : ℝ := (weightCoefficient : ℝ) * C ^ (coordinateCount + 2)
  let B : ℝ := (degreeCoefficient : ℝ) * C ^ (coordinateCount + 1)
  let M : ℝ := max 1 (max A (max B overlap.toReal))
  have hC : 1 ≤ C := by dsimp [C]; linarith [abs_nonneg a, abs_nonneg b]
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hM : 1 ≤ M := le_max_left _ _
  have hAM : A ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hBM : B ≤ M :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hDM : overlap.toReal ≤ M :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨coordinateCount + 3, min (1 / 1600) (Real.exp (-M)),
    lt_min (by norm_num) (Real.exp_pos _), min_le_left _ _, ?_⟩
  intro delta hdelta hdelta0 cardinality hcardinality
  let x : ℝ := Real.log (1 / delta)
  let q : ℝ := ((Nat.log 2 (2 * cardinality) + 1 : ℕ) : ℝ)
  have hMx : M ≤ x := by
    have hlog := Real.log_le_log hdelta (hdelta0.trans (min_le_right _ _))
    rw [Real.log_exp] at hlog
    dsimp [x]
    rw [one_div, Real.log_inv]
    linarith
  have hx : 1 ≤ x := hM.trans hMx
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq : q ≤ C * x := by
    by_cases hzero : cardinality = 0
    · have hmul : (1 : ℝ) ≤ C * x := by nlinarith
      simpa [q, hzero] using hmul
    have hcardpos : 0 < cardinality := Nat.pos_of_ne_zero hzero
    have hdoublepos : 0 < 2 * cardinality := by positivity
    have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hnatLog : (Nat.log 2 (2 * cardinality) : ℝ) ≤
        Real.log ((2 * cardinality : ℕ) : ℝ) / Real.log 2 := by
      have hpower : (2 : ℝ) ^ Nat.log 2 (2 * cardinality) ≤
          ((2 * cardinality : ℕ) : ℝ) := by
        exact_mod_cast Nat.pow_log_le_self 2 hdoublepos.ne'
      have hlog := Real.log_le_log (by positivity) hpower
      rw [Real.log_pow] at hlog
      exact (le_div_iff₀ hlogTwo).mpr hlog
    have hpoly : ((2 * cardinality : ℕ) : ℝ) ≤
        (2 * (37 * R) ^ 6) * delta ^ (-6 : ℝ) := by
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      nlinarith
    have hcardLog := Real.log_le_log
      (show 0 < ((2 * cardinality : ℕ) : ℝ) by exact_mod_cast hdoublepos) hpoly
    have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
    have hproductLog : Real.log ((2 * (37 * R) ^ 6) * delta ^ (-6 : ℝ)) =
        Real.log (2 * (37 * R) ^ 6) + 6 * x := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hdelta]
      dsimp [x]
      rw [one_div, Real.log_inv]
      ring
    have hqraw : q ≤ a + b * x := by
      calc
        q = (Nat.log 2 (2 * cardinality) : ℝ) + 1 := by simp [q]
        _ ≤ Real.log ((2 * cardinality : ℕ) : ℝ) / Real.log 2 + 1 := by linarith
        _ ≤ Real.log ((2 * (37 * R) ^ 6) * delta ^ (-6 : ℝ)) /
            Real.log 2 + 1 := by gcongr
        _ = a + b * x := by rw [hproductLog]; dsimp [a, b]; ring
    have ha : a ≤ |a| := le_abs_self _
    have hb : b * x ≤ |b| * x := mul_le_mul_of_nonneg_right (le_abs_self _) hx0
    have hax : |a| ≤ |a| * x := by nlinarith [abs_nonneg a]
    dsimp [C]
    nlinarith
  have hweight : (weightCoefficient : ℝ) * q ^ (coordinateCount + 2) ≤
      x ^ (coordinateCount + 3) := by
    calc
      _ ≤ (weightCoefficient : ℝ) * (C * x) ^ (coordinateCount + 2) := by gcongr
      _ = A * x ^ (coordinateCount + 2) := by dsimp [A]; rw [mul_pow]; ring
      _ ≤ x * x ^ (coordinateCount + 2) := by
        exact mul_le_mul_of_nonneg_right (hAM.trans hMx) (pow_nonneg hx0 _)
      _ = x ^ (coordinateCount + 3) := by rw [show coordinateCount + 3 =
          (coordinateCount + 2) + 1 by omega, pow_succ]; ring
  have hdegree : (degreeCoefficient : ℝ) * q ^ (coordinateCount + 1) ≤
      x ^ (coordinateCount + 3) := by
    calc
      _ ≤ (degreeCoefficient : ℝ) * (C * x) ^ (coordinateCount + 1) := by gcongr
      _ = B * x ^ (coordinateCount + 1) := by dsimp [B]; rw [mul_pow]; ring
      _ ≤ x * x ^ (coordinateCount + 1) := by
        exact mul_le_mul_of_nonneg_right (hBM.trans hMx) (pow_nonneg hx0 _)
      _ = x ^ (coordinateCount + 2) := by rw [show coordinateCount + 2 =
          (coordinateCount + 1) + 1 by omega, pow_succ]; ring
      _ ≤ x ^ (coordinateCount + 3) := pow_le_pow_right₀ hx (by omega)
  have hoverlapReal : overlap.toReal ≤ x ^ (coordinateCount + 3) := by
    calc
      _ ≤ x := hDM.trans hMx
      _ = x ^ 1 := (pow_one x).symm
      _ ≤ x ^ (coordinateCount + 3) := pow_le_pow_right₀ hx (by omega)
  have hqENN : ENNReal.ofReal q = (Nat.log 2 (2 * cardinality) + 1 : ENNReal) := by
    change ENNReal.ofReal ((Nat.log 2 (2 * cardinality) + 1 : ℕ) : ℝ) = _
    rw [ENNReal.ofReal_natCast, Nat.cast_add, Nat.cast_one]
  change 1 ≤ ENNReal.ofReal x ^ (coordinateCount + 3) ∧ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hxENN : (1 : ENNReal) ≤ ENNReal.ofReal x := by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_mono hx
    exact one_le_pow₀ hxENN
  · have h := ENNReal.ofReal_mono hweight
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
      ENNReal.ofReal_pow hq0, ENNReal.ofReal_pow hx0, hqENN] at h
    simpa only [weightCoefficient,
      Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using h
  · have h := ENNReal.ofReal_mono hdegree
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
      ENNReal.ofReal_pow hq0, ENNReal.ofReal_pow hx0, hqENN] at h
    simpa only [degreeCoefficient,
      Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using h
  · have h := ENNReal.ofReal_mono hoverlapReal
    simpa only [ENNReal.ofReal_toReal hoverlap, ENNReal.ofReal_pow hx0] using h

end KakeyaLink.JointSelection

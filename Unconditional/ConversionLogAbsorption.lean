/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.LogAbsorption
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZBridge

/-!
# Conversion Log Absorption

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

namespace Kakeya.Assouad

theorem exists_logPower_mul_rpow_threshold
    (overhead : ENNReal) (overheadFinite : overhead ≠ ⊤) (logExponent : ℕ)
    {alpha beta : ℝ} (exponentGap : beta < alpha) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 < 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta0 →
        overhead * ENNReal.ofReal (Real.log (1 / delta)) ^ logExponent *
          Kakeya.realRpowENN delta alpha ≤ Kakeya.realRpowENN delta beta := by
  obtain ⟨d, dPos, _, bound⟩ := exists_delta_log_absorbed
    (overhead.toReal + 1) (by positivity) (B := alpha - beta) (sub_pos.mpr exponentGap)
    (n := logExponent + 1) (Nat.succ_pos _)
  refine ⟨min d (1 / 2), lt_min dPos (by norm_num),
    lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
  intro delta deltaPos deltaSmall
  have deltaOne : delta < 1 :=
    lt_of_le_of_lt (deltaSmall.trans (min_le_right _ _)) (by norm_num)
  have logPos : 0 < Real.log (1 / delta) :=
    Real.log_pos ((lt_div_iff₀ deltaPos).mpr (by simpa using deltaOne))
  have poly : Real.log (1 / delta) ^ logExponent ≤
      (1 + Real.log delta⁻¹) ^ (logExponent + 1) := by
    rw [one_div] at logPos ⊢
    calc
      _ ≤ (1 + Real.log delta⁻¹) ^ logExponent := by gcongr; linarith
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (Nat.le_succ _)
  have overheadBound : overhead.toReal * Real.log (1 / delta) ^ logExponent ≤
      delta ^ (-(alpha - beta)) := by
    calc
      _ ≤ (overhead.toReal + 1) * (1 + Real.log delta⁻¹) ^ (logExponent + 1) := by
        gcongr
        linarith
      _ ≤ _ := bound delta deltaPos (deltaSmall.trans (min_le_left _ _))
  have realBound : overhead.toReal * Real.log (1 / delta) ^ logExponent *
      delta ^ alpha ≤ delta ^ beta := by
    calc
      _ ≤ delta ^ (-(alpha - beta)) * delta ^ alpha := by
        exact mul_le_mul_of_nonneg_right overheadBound (Real.rpow_pos_of_pos deltaPos _).le
      _ = _ := by
        rw [← Real.rpow_add deltaPos]
        congr 1
        ring
  have ennBound := ENNReal.ofReal_mono realBound
  simp only [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_mul (mul_nonneg ENNReal.toReal_nonneg (pow_nonneg logPos.le _)),
    ENNReal.ofReal_pow logPos.le, ENNReal.ofReal_toReal overheadFinite] at ennBound
  exact ennBound


end Kakeya.Assouad

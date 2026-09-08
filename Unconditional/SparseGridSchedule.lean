/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Kakeya.Uniform
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12
import Unconditional.ScaleParameters
import Mathlib.Algebra.Order.Floor.Semifield

/-!
P8 of `scratch/blueprinter/plan_full_fiber/HELPER_PLAN.md`.
The coordinate count is chosen before the fine scale. Actual dilated witness
scales may exceed one, as allowed by `WZ2PaperPureNearbyScaleCoverData`.
-/

noncomputable section

namespace KakeyaLink.JointSelection

/-- Natural division is the prescribed floor of `l * N / m`. -/
def sparseGridIndex (m N l : ℕ) : ℕ := l * N / m

/-- A fixed `m + 1` coordinates, all drawn from Numina's original grid. -/
def sparseGridScale (delta : NNReal) (m N : ℕ) (l : Fin (m + 1)) : NNReal :=
  Tube.gridScale delta N (sparseGridIndex m N l.val)

theorem sparseGridIndex_eq_floor (m N l : ℕ) :
    sparseGridIndex m N l = Nat.floor ((l : ℝ) * (N : ℝ) / (m : ℝ)) := by
  rw [sparseGridIndex, ← Nat.cast_mul, Nat.floor_div_eq_div]


theorem sparseGridIndex_last {m : ℕ} (hm : 0 < m) (N : ℕ) :
    sparseGridIndex m N m = N := by
  simp [sparseGridIndex, Nat.mul_div_right, hm]

theorem sparseGridIndex_le {m N l : ℕ} (hm : 0 < m) (hl : l ≤ m) :
    sparseGridIndex m N l ≤ N := by
  calc
    sparseGridIndex m N l ≤ sparseGridIndex m N m :=
      Nat.div_le_div_right (Nat.mul_le_mul_right N hl)
    _ = N := sparseGridIndex_last hm N


/-- Every requested scale rounds upwards to the fixed sparse schedule. -/
theorem exists_sparseGridScale_ge
    {delta : NNReal} (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N)
    {requested : NNReal} (hrequested : requested ∈ Set.Icc delta 1) :
    ∃ l : Fin (m + 1),
      requested ≤ sparseGridScale delta m N l ∧
      sparseGridScale delta m N l ≤
        delta ^ (-((1 : ℝ) / (m : ℝ) + (1 : ℝ) / (N : ℝ))) * requested := by
  obtain ⟨l, hl, hlo, hhi⟩ :=
    StickyKakeya.exists_gridScale_ge hdelta hdeltaOne hm hrequested
  have hN : 0 < N := hm.trans_le hmN
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hfloor := Nat.floor_le (show 0 ≤ (l : ℝ) * N / m by positivity)
  have hceil := Nat.lt_floor_add_one ((l : ℝ) * N / m)
  rw [← sparseGridIndex_eq_floor] at hfloor hceil
  have hbelow : (sparseGridIndex m N l : ℝ) / N ≤ (l : ℝ) / m := by
    apply (div_le_iff₀ hNR).2
    convert hfloor using 1 <;> ring
  have habove : (l : ℝ) / m - 1 / N ≤ (sparseGridIndex m N l : ℝ) / N := by
    apply (le_div_iff₀ hNR).2
    have hcalc : ((l : ℝ) / m - 1 / N) * N = (l : ℝ) * N / m - 1 := by
      field_simp
    rw [hcalc]
    linarith
  refine ⟨⟨l, Nat.lt_succ_of_le hl⟩, ?_, ?_⟩
  · exact hlo.trans (NNReal.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne hbelow)
  · have hround : sparseGridScale delta m N ⟨l, Nat.lt_succ_of_le hl⟩ ≤
        delta ^ (-(1 : ℝ) / N) * Tube.gridScale delta m l := by
      change delta ^ ((sparseGridIndex m N l : ℝ) / N) ≤ _
      calc
        _ ≤ delta ^ ((l : ℝ) / m - 1 / N) :=
          NNReal.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne habove
        _ = delta ^ (-(1 : ℝ) / N) * Tube.gridScale delta m l := by
          rw [Tube.gridScale, ← NNReal.rpow_add hdelta.ne']
          congr 1
          ring
    calc
      _ ≤ delta ^ (-(1 : ℝ) / N) * Tube.gridScale delta m l := hround
      _ ≤ delta ^ (-(1 : ℝ) / N) * (delta ^ (-(1 : ℝ) / m) * requested) :=
        mul_le_mul_of_nonneg_left hhi (by positivity)
      _ = _ := by
        rw [← mul_assoc, ← NNReal.rpow_add hdelta.ne']
        congr 2
        ring


/-- A fixed coordinate count and threshold also absorb a fixed parent dilation. -/
theorem exists_fixed_sparse_schedule_window_threshold
    (windowLoss : ℝ) (hwindowLoss : 0 < windowLoss)
    (dilation : ℝ) (hdilation : 1 ≤ dilation) :
    ∃ m : ℕ, 0 < m ∧ (1 : ℝ) / (m : ℝ) < windowLoss / 8 ∧
      ∃ delta0 : NNReal, 0 < delta0 ∧ delta0 < 1 ∧
        ∀ {delta : NNReal}, 0 < delta → delta ≤ delta0 →
          m ≤ Tube.ssfGridLen delta ∧
          (1 : ℝ) / (Tube.ssfGridLen delta : ℝ) < windowLoss / 8 ∧
          ∀ requested : Kakeya.Assouad.WZ2PaperRequestedScale (delta : ℝ),
            ∃ l : Fin (m + 1),
              requested.1 ≤
                dilation * (sparseGridScale delta m (Tube.ssfGridLen delta) l : ℝ) ∧
              ENNReal.ofReal
                  (dilation * (sparseGridScale delta m (Tube.ssfGridLen delta) l : ℝ)) <
                Kakeya.realRpowENN (delta : ℝ) (-windowLoss) *
                  ENNReal.ofReal requested.1 := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < windowLoss / 8 by positivity)
  let m := n + 1
  have hm : 0 < m := Nat.succ_pos n
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hstepM : (1 : ℝ) / m < windowLoss / 8 := by simpa [m] using hn
  obtain ⟨dG, hdG, hdGOne, hgrid⟩ :=
    ScaleParameters.exists_ssfGridLen_step_threshold
      (min (windowLoss / 8) (1 / (m : ℝ))) (lt_min (by positivity) (by positivity))
  obtain ⟨dC, hdC, hdCOne, hconstant⟩ :=
    Kakeya.Assouad.exists_delta_mul_rpow_le_rpow dilation (by linarith)
      (alpha := -windowLoss / 2) (beta := -(3 * windowLoss / 4)) (by linarith)
  let dCnn : NNReal := ⟨dC, hdC.le⟩
  refine ⟨m, hm, hstepM, min dG dCnn, lt_min hdG hdC,
    lt_of_le_of_lt (min_le_left _ _) hdGOne, ?_⟩
  intro delta hdelta hle
  have hdeltaOne : delta < 1 := (hle.trans (min_le_left _ _)).trans_lt hdGOne
  obtain ⟨hN, hstepN⟩ := hgrid hdelta (hle.trans (min_le_left _ _))
  have hNR : (0 : ℝ) < Tube.ssfGridLen delta := by exact_mod_cast hN
  have hstepN' : (1 : ℝ) / (Tube.ssfGridLen delta : ℝ) < windowLoss / 8 :=
    hstepN.trans_le (min_le_left _ _)
  have hmN : m ≤ Tube.ssfGridLen delta := by
    have hlt := (one_div_lt_one_div hNR hmR).1 (hstepN.trans_le (min_le_right _ _))
    exact_mod_cast hlt.le
  refine ⟨hmN, hstepN', ?_⟩
  intro requested
  have hrpos : 0 < requested.1 := lt_of_lt_of_le hdelta requested.2.1
  let r : NNReal := ⟨requested.1, hrpos.le⟩
  obtain ⟨l, hlo, hhi⟩ := exists_sparseGridScale_ge hdelta hdeltaOne.le hm hmN
    (requested := r) ⟨requested.2.1, requested.2.2⟩
  have hloR : requested.1 ≤ (sparseGridScale delta m (Tube.ssfGridLen delta) l : ℝ) := hlo
  have hhiR : (sparseGridScale delta m (Tube.ssfGridLen delta) l : ℝ) ≤
      (delta : ℝ) ^ (-((1 : ℝ) / m + 1 / (Tube.ssfGridLen delta : ℝ))) * requested.1 := by
    exact_mod_cast hhi
  have hgap : (1 : ℝ) / m + 1 / (Tube.ssfGridLen delta : ℝ) < windowLoss / 2 := by
    linarith
  have hpow : (delta : ℝ) ^ (-((1 : ℝ) / m + 1 / (Tube.ssfGridLen delta : ℝ))) ≤
      (delta : ℝ) ^ (-windowLoss / 2) := by
    apply Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne.le
    linarith
  have hconst : dilation * (delta : ℝ) ^ (-windowLoss / 2) ≤
      (delta : ℝ) ^ (-(3 * windowLoss / 4)) :=
    hconstant delta hdelta (hle.trans (min_le_right _ _))
  have hstrict : (delta : ℝ) ^ (-(3 * windowLoss / 4)) <
      (delta : ℝ) ^ (-windowLoss) := by
    apply Real.rpow_lt_rpow_of_exponent_gt hdelta hdeltaOne
    linarith
  have hupper : dilation * (sparseGridScale delta m (Tube.ssfGridLen delta) l : ℝ) <
      (delta : ℝ) ^ (-windowLoss) * requested.1 := by
    calc
      _ ≤ dilation * ((delta : ℝ) ^
          (-((1 : ℝ) / m + 1 / (Tube.ssfGridLen delta : ℝ))) * requested.1) :=
        mul_le_mul_of_nonneg_left hhiR (by linarith)
      _ ≤ (dilation * (delta : ℝ) ^ (-windowLoss / 2)) * requested.1 := by
        rw [mul_assoc]
        gcongr
      _ ≤ (delta : ℝ) ^ (-(3 * windowLoss / 4)) * requested.1 :=
        mul_le_mul_of_nonneg_right hconst hrpos.le
      _ < _ := mul_lt_mul_of_pos_right hstrict hrpos
  refine ⟨l, hloR.trans ?_, ?_⟩
  · exact le_mul_of_one_le_left (by positivity) hdilation
  · change ENNReal.ofReal _ < ENNReal.ofReal ((delta : ℝ) ^ (-windowLoss)) *
      ENNReal.ofReal requested.1
    rw [← ENNReal.ofReal_mul (p := (delta : ℝ) ^ (-windowLoss))
      (q := requested.1) (by positivity)]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hupper


end KakeyaLink.JointSelection

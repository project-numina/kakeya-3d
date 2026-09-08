/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Rescaling.CoarseDensity

/-!
# Main Lemma 1, Case (ii): The bracketed term

Split out of `Kakeya/DimensionThree/MainLemma1/Rescaling.lean`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya

namespace ml1Boot

/-! ### The bracketed term -/

section Bracket

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The volume of `B̄(0,R)` is `R ^ n` times that of the unit ball.**

The companion of `Kakeya.volume_closedBall_eq_ccov_mul_pow`, which computes the same volume
against an absolute constant; here the reference is the unit ball itself, which is what the
`densityIn` of `Kakeya.ml1Boot.bracket_mem_Icc_ball` divides by.  The power is the natural
power `R ^ Module.finrank ℝ E`, not an `rpow`. -/
theorem volume_closedBall_eq_pow_mul (R : ℝ) (hR : 0 ≤ R) :
    volume (Metric.closedBall (0 : E) R)
      = ENNReal.ofReal (R ^ Module.finrank ℝ E) * volume (Metric.closedBall (0 : E) 1) := by
  have hb := MeasureTheory.Measure.addHaar_closedBall (volume : Measure E) (0 : E) hR
  have hb1 := MeasureTheory.Measure.addHaar_closedBall (volume : Measure E) (0 : E)
    (zero_le_one : (0 : ℝ) ≤ 1)
  rw [hb, hb1]
  simp

/-- **`Kakeya.ml1Boot.bracket_mem_Icc` at an ambient radius `R ≥ 1`.**

Identical statement, with `B₁` replaced by `B̄(0,R)` in both the containment hypothesis and
the ambient body of the Frostman constant, and with the constant `c₃` replaced by
`max (3 R³) r` — the *only* change.  Nothing in the exponents moves: the unit ball enters this
lemma purely as the reference volume of `densityIn`, and rescaling that volume by `R³` is a
constant charge on `c₃`. -/
theorem bracket_mem_Icc_ball (hdim : Module.finrank ℝ E = 3) (R : ℝ≥0) (hR : 1 ≤ R) :
    ∃ c₃ : ℝ≥0, 1 ≤ c₃ ∧
      ∀ {δt b : ℝ≥0}, 0 < δt → δt ≤ b → b ≤ 1 →
      ∀ {CFb : ℝ≥0∞}, 1 ≤ CFb → ∀ {CΔ : ℝ≥0}, 1 ≤ CΔ → ∀ {h : ℝ}, 0 ≤ h →
      ∀ {κ : Type*} {t : Finset κ} (Tb : κ → Tube b E),
        t.Nonempty →
        (∀ l ∈ t, (Tb l).carrier ⊆ Metric.closedBall 0 (R : ℝ)) →
        frostmanConstIn t (fun l => (Tb l).toConvexSpaceBody)
            (ConvexSpaceBody.closedBall (0 : E) (R : ℝ) R.coe_nonneg) ≤ CFb →
        maxDensity t (fun l => (Tb l).toConvexSpaceBody)
            ≤ (CΔ : ℝ≥0∞) * (δt : ℝ≥0∞) ^ (-h) →
        ((c₃ : ℝ≥0∞) * CFb)⁻¹ ≤ (t.card : ℝ≥0∞) * (b : ℝ≥0∞) ^ (2 : ℕ) ∧
          (t.card : ℝ≥0∞) * (b : ℝ≥0∞) ^ (2 : ℕ)
            ≤ (c₃ : ℝ≥0∞) * (CΔ : ℝ≥0∞) * (δt : ℝ≥0∞) ^ (-h) := by
  haveI : Nontrivial E := Module.finrank_pos_iff.mp (by rw [hdim]; norm_num)
  let n : ℕ := Module.finrank ℝ E
  let m : ℝ≥0 := Tube.le_volume.c n
  let M : ℝ≥0 := Tube.volume_le.C n
  let r : ℝ≥0 := M / (3 * m)
  let RR : ℝ≥0 := R ^ n
  let c₃ : ℝ≥0 := max (3 * RR) r
  have h_one_le_c3 : 1 ≤ c₃ := by
    refine le_trans ?_ (le_max_left (3 * RR) r)
    have hRR : (1 : ℝ≥0) ≤ RR := one_le_pow₀ hR
    calc (1 : ℝ≥0) ≤ 3 * 1 := by norm_num
      _ ≤ 3 * RR := by gcongr
  refine ⟨c₃, h_one_le_c3, ?_⟩
  intro δt b hδt hδb hb1 CFb hCFb1 CΔ hCΔ1 h hh κ t Tb ht_nonempty hball hfrost hmaxdens
  let d : ℝ≥0∞ := (b : ℝ≥0∞)
  set W : κ → ConvexSpaceBody E := fun l => (Tb l).toConvexSpaceBody with hW
  set BR : ConvexSpaceBody E := ConvexSpaceBody.closedBall (0 : E) (R : ℝ) R.coe_nonneg with hBR
  set VR : ℝ≥0∞ := volume BR.carrier with hVR
  set S : ℝ≥0∞ := ∑ l ∈ t, volume (W l).carrier with hS
  have hn : n = 3 := by simpa [n] using hdim
  have htwo : n - 1 = 2 := by omega
  -- tubes in `B̄(0,R)`, in `≤` form
  have hT : ∀ l ∈ t, W l ≤ BR := by
    intro l hl
    exact SetLike.coe_subset_coe.mpr (hball l hl)
  -- Frostman property at the `b`-tube scale
  have hFr : IsFrostmanIn t W BR CFb :=
    isFrostmanIn_of_frostmanConstIn_le (s := t) (W := W) (K := BR) hfrost
  have hmax_le : maxDensity t W ≤ CFb * densityIn t W BR :=
    hFr.maxDensity_le_of_carrier_subset hT
  -- non-degeneracy
  have hpos_b : 0 < b := lt_of_lt_of_le hδt hδb
  have hd_ne : d ≠ 0 := by dsimp [d]; exact ENNReal.coe_ne_zero.mpr (ne_of_gt hpos_b)
  have hm_ne : (m : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr (Tube.le_volume.c_pos n).ne'
  have hm_top : (m : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have h3m_ne : (3 * m : ℝ≥0) ≠ 0 :=
    mul_ne_zero (by norm_num : (3 : ℝ≥0) ≠ 0) (Tube.le_volume.c_pos n).ne'
  have h3mE_ne : ((3 * m : ℝ≥0) : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr h3m_ne
  have h3mE_top : ((3 * m : ℝ≥0) : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  -- the volume of the ambient ball
  have hV1 : volume (Metric.closedBall (0 : E) 1) = ((3 * m : ℝ≥0) : ℝ≥0∞) := by
    have := volume_closedUnitBall_eq (E := E)
    rw [ConvexSpaceBody.closedUnitBall_carrier] at this
    simpa [m, n] using this
  have hVReq : VR = (RR : ℝ≥0∞) * ((3 * m : ℝ≥0) : ℝ≥0∞) := by
    have hc : BR.carrier = Metric.closedBall (0 : E) (R : ℝ) := rfl
    rw [hVR, hc, volume_closedBall_eq_pow_mul (E := E) (R : ℝ) R.coe_nonneg, hV1]
    congr 1
    rw [show ((R : ℝ) ^ Module.finrank ℝ E) = ((R ^ n : ℝ≥0) : ℝ) by push_cast [n]; ring]
    simp [RR]
  have hRR1 : (1 : ℝ≥0) ≤ RR := one_le_pow₀ hR
  have hRR1E : (1 : ℝ≥0∞) ≤ (RR : ℝ≥0∞) := by exact_mod_cast hRR1
  have hVR_lower : ((3 * m : ℝ≥0) : ℝ≥0∞) ≤ VR := by
    rw [hVReq]
    calc ((3 * m : ℝ≥0) : ℝ≥0∞) = 1 * ((3 * m : ℝ≥0) : ℝ≥0∞) := by ring
      _ ≤ (RR : ℝ≥0∞) * ((3 * m : ℝ≥0) : ℝ≥0∞) := by gcongr
  -- per-tube volume comparisons
  have per_lower : ∀ l ∈ t, (m : ℝ≥0∞) * d ^ 2 ≤ volume (W l).carrier := by
    intro l hl
    have hv := (Tb l).le_volume
    simpa [W, m, n, d, htwo] using hv
  have per_upper : ∀ l ∈ t, volume (W l).carrier ≤ (M : ℝ≥0∞) * d ^ 2 := by
    intro l hl
    have hv := Tube.volume_le hb1 (Tb l)
    simpa [W, M, n, d, htwo] using hv
  have hvol_pos : ∀ l ∈ t, 0 < volume (W l).carrier := by
    intro l hl
    have hle := (Tb l).le_volume
    have hpow_ne : d ^ (n - 1) ≠ 0 := ENNReal.pow_ne_zero hd_ne (n - 1)
    have hprod_pos : 0 < (m : ℝ≥0∞) * d ^ (n - 1) := ENNReal.mul_pos hm_ne hpow_ne
    simpa [W, m, d, n] using hprod_pos.trans_le hle
  obtain ⟨l0, hl0⟩ := ht_nonempty
  have hmd1 : 1 ≤ maxDensity t W := one_le_maxDensity (s := t) (W := W) ⟨l0, hl0, hvol_pos l0 hl0⟩
  -- `S = densityIn · VR`
  have hSeq : S = densityIn t W BR * VR := by
    simpa [hS, hVR] using sum_volume_eq_densityIn_mul_volume' (s := t) (W := W) (K := BR) hT
  have hS_upper : S ≤ (t.card : ℝ≥0∞) * (M : ℝ≥0∞) * d ^ 2 := by
    calc
      S = ∑ l ∈ t, volume (W l).carrier := rfl
      _ ≤ ∑ _l ∈ t, ((M : ℝ≥0∞) * d ^ 2) := Finset.sum_le_sum (fun l hl => per_upper l hl)
      _ = (t.card : ℝ≥0∞) * (M : ℝ≥0∞) * d ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]
  have hS_lower : (t.card : ℝ≥0∞) * (m : ℝ≥0∞) * d ^ 2 ≤ S := by
    calc
      (t.card : ℝ≥0∞) * (m : ℝ≥0∞) * d ^ 2 = ∑ _l ∈ t, ((m : ℝ≥0∞) * d ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ ∑ l ∈ t, volume (W l).carrier := Finset.sum_le_sum (fun l hl => per_lower l hl)
      _ = S := rfl
  -- (L1) `card · d² ≤ 3 RR · densityIn`
  have hA_le3 : (t.card : ℝ≥0∞) * d ^ 2 ≤ 3 * (RR : ℝ≥0∞) * densityIn t W BR := by
    have h1 : (m : ℝ≥0∞) * ((t.card : ℝ≥0∞) * d ^ 2)
        ≤ (m : ℝ≥0∞) * (3 * (RR : ℝ≥0∞) * densityIn t W BR) := by
      calc (m : ℝ≥0∞) * ((t.card : ℝ≥0∞) * d ^ 2)
          = (t.card : ℝ≥0∞) * (m : ℝ≥0∞) * d ^ 2 := by ring
        _ ≤ S := hS_lower
        _ = densityIn t W BR * VR := hSeq
        _ = densityIn t W BR * ((RR : ℝ≥0∞) * ((3 * m : ℝ≥0) : ℝ≥0∞)) := by rw [hVReq]
        _ = (m : ℝ≥0∞) * (3 * (RR : ℝ≥0∞) * densityIn t W BR) := by
              rw [ENNReal.coe_mul]
              push_cast
              ring
    exact (ENNReal.mul_le_mul_iff_left hm_ne hm_top).mp
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using h1)
  -- (L2) `densityIn ≤ r · card · d²`
  have hMr0 : (r : ℝ≥0) * (3 * m) = M := by
    dsimp [r]
    exact div_mul_cancel₀ M h3m_ne
  have hMr : (M : ℝ≥0∞) = (r : ℝ≥0∞) * ((3 * m : ℝ≥0) : ℝ≥0∞) := by
    rw [← ENNReal.coe_mul, hMr0]
  have hdens_le : densityIn t W BR ≤ (r : ℝ≥0∞) * (t.card : ℝ≥0∞) * d ^ 2 := by
    have h1 : densityIn t W BR * ((3 * m : ℝ≥0) : ℝ≥0∞)
        ≤ ((r : ℝ≥0∞) * (t.card : ℝ≥0∞) * d ^ 2) * ((3 * m : ℝ≥0) : ℝ≥0∞) := by
      calc densityIn t W BR * ((3 * m : ℝ≥0) : ℝ≥0∞)
          ≤ densityIn t W BR * VR := by gcongr
        _ = S := hSeq.symm
        _ ≤ (t.card : ℝ≥0∞) * (M : ℝ≥0∞) * d ^ 2 := hS_upper
        _ = ((r : ℝ≥0∞) * (t.card : ℝ≥0∞) * d ^ 2) * ((3 * m : ℝ≥0) : ℝ≥0∞) := by
              rw [hMr]; ring
    exact (ENNReal.mul_le_mul_iff_left h3mE_ne h3mE_top).mp h1
  -- lower bound
  have h_lower : 1 ≤ (c₃ : ℝ≥0∞) * CFb * (t.card : ℝ≥0∞) * d ^ 2 := by
    have h1 : 1 ≤ CFb * ((r : ℝ≥0∞) * (t.card : ℝ≥0∞) * d ^ 2) :=
      le_trans (le_trans hmd1 hmax_le) (mul_le_mul_right hdens_le CFb)
    have hrc : (r : ℝ≥0∞) ≤ (c₃ : ℝ≥0∞) := ENNReal.coe_le_coe.mpr (le_max_right _ r)
    calc (1 : ℝ≥0∞) ≤ CFb * ((r : ℝ≥0∞) * (t.card : ℝ≥0∞) * d ^ 2) := h1
      _ ≤ CFb * ((c₃ : ℝ≥0∞) * (t.card : ℝ≥0∞) * d ^ 2) := by gcongr
      _ = (c₃ : ℝ≥0∞) * CFb * (t.card : ℝ≥0∞) * d ^ 2 := by ring
  -- upper bound
  have h_up : (t.card : ℝ≥0∞) * d ^ 2
      ≤ (c₃ : ℝ≥0∞) * (CΔ : ℝ≥0∞) * (δt : ℝ≥0∞) ^ (-h) := by
    have h3c : 3 * (RR : ℝ≥0∞) ≤ (c₃ : ℝ≥0∞) := by
      have : ((3 * RR : ℝ≥0) : ℝ≥0∞) ≤ (c₃ : ℝ≥0∞) :=
        ENNReal.coe_le_coe.mpr (le_max_left _ r)
      simpa using this
    calc
      (t.card : ℝ≥0∞) * d ^ 2 ≤ 3 * (RR : ℝ≥0∞) * densityIn t W BR := hA_le3
      _ ≤ 3 * (RR : ℝ≥0∞) * maxDensity t W := by
            gcongr
            exact le_maxDensity (s := t) (W := W) BR
      _ ≤ 3 * (RR : ℝ≥0∞) * ((CΔ : ℝ≥0∞) * (δt : ℝ≥0∞) ^ (-h)) := by gcongr
      _ ≤ (c₃ : ℝ≥0∞) * ((CΔ : ℝ≥0∞) * (δt : ℝ≥0∞) ^ (-h)) := by gcongr
      _ = (c₃ : ℝ≥0∞) * (CΔ : ℝ≥0∞) * (δt : ℝ≥0∞) ^ (-h) := by rw [mul_assoc]
  refine ⟨?_, by simpa [d] using h_up⟩
  have htcard_pos : 0 < t.card := Finset.card_pos.mpr ⟨l0, hl0⟩
  have hAc_ne0 : (t.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt htcard_pos)
  have h_Ad_ne0 : (t.card : ℝ≥0∞) * d ^ 2 ≠ 0 :=
    mul_ne_zero hAc_ne0 (ENNReal.pow_ne_zero hd_ne 2)
  have h_c3CFb_ne0 : (c₃ : ℝ≥0∞) * CFb ≠ 0 :=
    mul_ne_zero (ENNReal.coe_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one h_one_le_c3)))
      (ne_of_gt (lt_of_lt_of_le zero_lt_one hCFb1))
  rw [ENNReal.inv_le_iff_le_mul (by intro h; exact h_c3CFb_ne0)
    (by intro h; exact h_Ad_ne0)]
  simpa [mul_assoc, mul_comm, mul_left_comm] using h_lower

end Bracket

end ml1Boot

end Kakeya

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.RandomTranslation.EDChernoffNet
public import Kakeya.RandomTranslation.RigidMED

/-!
# A single tuple of rigid motions that is ED-good against every test tube

`Kakeya.edBadCount_chernoff_tail` bounds, for one test tube, the probability that the total bad
count of `J` independent rigid copies exceeds a threshold `S`. This file performs the union bound
over the whole test-tube net and extracts a **single** tuple of rigid motions that works for all
test tubes simultaneously.

## The arithmetic, with nothing hidden

The net is `Kakeya.exists_thin_tube_net`, whose cardinality is bounded by the named dimensional
quantities

`NetT.card ≤ netGeomConstantC E * δ^(-netGeomConstantM E)`.

The Chernoff bound contributes `exp (10e - S/M)` per net member with `M` dimensional
(`edBadCount_chernoff_tail`). Choosing

`S = rigidMED (M · A) δ`,  `A = 10e + |log (10 · netGeomConstantC E)| + 1 + netGeomConstantM E`,

gives `S/M ≥ A · (1 + log (1/δ)) ≥ 10e + log (10 · netGeomConstantC E) + 1
+ netGeomConstantM E · log (1/δ)`, hence

`NetT.card · exp (10e - S/M) ≤ (netGeomConstantC E · δ^(-netGeomConstantM E))
    · (10 · netGeomConstantC E)⁻¹ · δ^(netGeomConstantM E) · e⁻¹ = e⁻¹/10 < 1/10`.

So the failure probability is below `1/10` and the good event has probability at least `9/10 > 0`.
The threshold `S` is `O(log (1/δ))` and, crucially, is free of the Frostman constant.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Metric Set Filter Topology

namespace Kakeya

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The dimensional constant calibrating the Chernoff threshold against the polynomial size of the
test-tube net. The absolute value makes it unconditionally large enough regardless of the sign of
`log (10 · netGeomConstantC E)`. -/
def edNetCalibration (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : ℝ :=
  10 * Real.exp 1 + |Real.log (10 * netGeomConstantC E)| + 1 + netGeomConstantM E

theorem edNetCalibration_pos [Nontrivial E] : 0 < edNetCalibration E := by
  unfold edNetCalibration
  have hM : 0 ≤ netGeomConstantM E := (netGeomConstantM_pos E).le
  have hE : 0 < Real.exp 1 := Real.exp_pos 1
  have hlog : 0 ≤ |Real.log (10 * netGeomConstantC E)| := abs_nonneg _
  nlinarith

/-- **The union-bound arithmetic, fully explicit.** With the threshold `rigidMED (M · A) δ` the
product of the net cardinality bound and the per-tube Chernoff probability is below `1/10`. -/
theorem net_union_bound_lt [Nontrivial E] {M A : ℝ} (hM : 0 < M)
    (hA : edNetCalibration E ≤ A)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : (δ : ℝ) ≤ 1) :
    (netGeomConstantC E * (δ : ℝ) ^ (-(netGeomConstantM E)))
        * Real.exp (10 * Real.exp 1 - ((rigidMED (M * A) δ : ℕ) : ℝ) / M)
      < 1 / 10 := by
  set C : ℝ := netGeomConstantC E
  set MM : ℝ := netGeomConstantM E
  set e : ℝ := Real.exp 1
  let l : ℝ := Real.log (1 / (δ : ℝ))
  let L : ℝ := 1 + l
  let P : ℝ := M * A * L
  set S : ℝ := ((rigidMED (M * A) δ : ℕ) : ℝ)
  have hδR : 0 < (δ : ℝ) := NNReal.coe_pos.mpr hδ
  have hδnn : 0 ≤ (δ : ℝ) := NNReal.coe_nonneg δ
  have hone : (1 : ℝ) ≤ 1 / (δ : ℝ) := one_le_one_div hδR hδ1
  have hlog : 0 ≤ l := by
    dsimp [l]
    exact Real.log_nonneg hone
  have hCpos : 0 < C := by
    dsimp [C]
    exact netGeomConstantC_pos E
  have hMpos : 0 < MM := by
    dsimp [MM]
    exact netGeomConstantM_pos E
  have heposs : 0 < e := by
    dsimp [e]
    exact Real.exp_pos 1
  have hMMnn : 0 ≤ MM := hMpos.le
  have hCNn : 0 ≤ C := hCpos.le
  have hCabsnn : 0 ≤ |Real.log (10 * C)| := abs_nonneg _
  -- Step 2: bounds on A from hA
  have hA' : 10 * e + |Real.log (10 * C)| + 1 + MM ≤ A := by
    rw [edNetCalibration] at hA
    simpa [C] using hA
  have hlog_le_abs : Real.log (10 * C) ≤ |Real.log (10 * C)| := le_abs_self _
  have hA_ge_M : MM ≤ A := by
    nlinarith [hA', heposs, hCabsnn, hMMnn]
  have hA_ge_base : 10 * e + Real.log (10 * C) + 1 ≤ A := by
    nlinarith [hA', hlog_le_abs, hMMnn]
  -- Step 3: S/M ≥ A·L
  have hS_eq : S = ((⌈P⌉₊ : ℕ) : ℝ) + 1 := by
    have hPa : (M * A) * (1 + Real.log (1 / (δ : ℝ))) = P := by
      dsimp [P, L]
    dsimp [S]
    rw [rigidMED]
    rw [← hPa]
    norm_cast
  have hPceil : P ≤ ((⌈P⌉₊ : ℕ) : ℝ) := Nat.le_ceil P
  have hS_ge : P ≤ S := by
    rw [hS_eq]
    nlinarith [hPceil]
  have hSM : A * L ≤ S / M := by
    rw [le_div_iff₀ hM]
    calc
      A * L * M = M * A * L := by ring
      _ = P := rfl
      _ ≤ S := hS_ge
  -- Step 4: lower bound on A·L
  have hAL_prod : A * L = A + A * l := by
    dsimp [L]
    ring
  have hA_log : MM * l ≤ A * l := mul_le_mul_of_nonneg_right hA_ge_M hlog
  have hB4 : 10 * e + Real.log (10 * C) + 1 + MM * l ≤ A * L := by
    rw [hAL_prod]
    nlinarith [hA_ge_base, hA_log]
  have hST : 10 * e - S / M ≤ -(Real.log (10 * C) + 1 + MM * l) := by
    nlinarith [hSM, hB4]
  -- Step 5: bound the exponential factor
  have hExpLe :
      Real.exp (10 * e - S / M) ≤
        Real.exp (-(Real.log (10 * C) + 1 + MM * l)) :=
    Real.exp_le_exp.mpr hST
  have hC10pos : 0 < 10 * C := by positivity
  have hC10ne : 10 * C ≠ 0 := ne_of_gt hC10pos
  have hCne : C ≠ 0 := ne_of_gt hCpos
  have hE1 : Real.exp (-(Real.log (10 * C))) = (10 * C)⁻¹ := by
    rw [Real.exp_neg (Real.log (10 * C)), Real.exp_log hC10pos]
  have hE2 : Real.exp (-1) = e⁻¹ := by
    dsimp [e]
    exact Real.exp_neg 1
  have hl_inv : l = -(Real.log (δ : ℝ)) := by
    dsimp [l]
    rw [one_div] at ⊢
    exact Real.log_inv (δ : ℝ)
  have hArg3 : -(MM * l) = Real.log (δ : ℝ) * MM := by
    rw [hl_inv]
    ring
  have hE3 : Real.exp (-(MM * l)) = (δ : ℝ) ^ MM := by
    rw [hArg3]
    rw [← Real.rpow_def_of_pos hδR MM]
  have hArgT : -(Real.log (10 * C) + 1 + MM * l) =
      -(Real.log (10 * C)) + (-1) + (-(MM * l)) := by ring
  have hExpT :
      Real.exp (-(Real.log (10 * C) + 1 + MM * l)) =
        (10 * C)⁻¹ * e⁻¹ * (δ : ℝ) ^ MM := by
    rw [hArgT]
    calc
      Real.exp (-(Real.log (10 * C)) + (-1) + (-(MM * l)))
          = Real.exp (-(Real.log (10 * C))) * Real.exp (-1) * Real.exp (-(MM * l)) := by
            rw [Real.exp_add]
            rw [Real.exp_add]
      _ = (10 * C)⁻¹ * e⁻¹ * (δ : ℝ) ^ MM := by rw [hE1, hE2, hE3]
  -- Step 6: multiply and cancel
  have hCt : 0 ≤ C * (δ : ℝ) ^ (-MM) :=
    mul_nonneg hCNn (Real.rpow_nonneg hδnn _)
  have hδE : (δ : ℝ) ^ (-MM) * (δ : ℝ) ^ MM = 1 := by
    rw [← Real.rpow_add hδR (-MM) MM]
    have hz : (-MM) + MM = (0 : ℝ) := by ring
    rw [hz]
    simp
  have hCinv : C * (10 * C)⁻¹ = (1 / 10 : ℝ) := by
    field_simp [hCne, hC10ne]
  have hProd :
      (C * (δ : ℝ) ^ (-MM)) * ((10 * C)⁻¹ * e⁻¹ * (δ : ℝ) ^ MM) = (1 / 10) * e⁻¹ := by
    calc
      (C * (δ : ℝ) ^ (-MM)) * ((10 * C)⁻¹ * e⁻¹ * (δ : ℝ) ^ MM)
          = (C * (10 * C)⁻¹) * ((δ : ℝ) ^ (-MM) * (δ : ℝ) ^ MM) * e⁻¹ := by ring
      _ = (1 / 10) * 1 * e⁻¹ := by rw [hCinv, hδE]
      _ = (1 / 10) * e⁻¹ := by ring
  have hone_e : (1 : ℝ) < e := by
    dsimp [e]
    exact (Real.one_lt_exp_iff).mpr (by norm_num)
  have hEinv : e⁻¹ < 1 := by
    dsimp [e]
    rw [← Real.exp_neg (1 : ℝ)]
    calc
      Real.exp (-(1 : ℝ)) < Real.exp (0 : ℝ) :=
        (Real.exp_lt_exp).mpr (by norm_num : (-(1 : ℝ)) < (0 : ℝ))
      _ = 1 := Real.exp_zero
  have hfinite : (1 / 10) * e⁻¹ < 1 / 10 := by
    have hpos : (0 : ℝ) < 1 / 10 := by norm_num
    calc
      (1 / 10) * e⁻¹ < (1 / 10) * 1 := mul_lt_mul_of_pos_left hEinv hpos
      _ = 1 / 10 := by norm_num
  have hMain : C * (δ : ℝ) ^ (-MM) * Real.exp (10 * e - S / M) ≤ (1 / 10) * e⁻¹ := by
    calc
      C * (δ : ℝ) ^ (-MM) * Real.exp (10 * e - S / M)
          ≤ C * (δ : ℝ) ^ (-MM) * Real.exp (-(Real.log (10 * C) + 1 + MM * l)) := by
            apply mul_le_mul_of_nonneg_left _ hCt
            exact hExpLe
      _ = (1 / 10) * e⁻¹ := by
            rw [hExpT]
            exact hProd
  exact lt_of_le_of_lt hMain hfinite

end

end Kakeya

end

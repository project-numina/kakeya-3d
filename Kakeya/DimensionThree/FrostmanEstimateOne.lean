/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.BushCount
public import Kakeya.PartialEstimates

/-!
# The base case `K_F(1)` of the bootstrap

The partial Frostman estimate `K_F(1)` holds in `ℝ ^ 3`.

Unlike the case `β = 0`, this is not a consequence of the trivial bound `μ ≤ |s|`: for a family
with `|s| ≈ δ ^ (-4)` the right-hand side of `K_F(1)` is `≈ δ ^ (-3) ≪ |s|`. The geometric input
is the *bush bound* `Kakeya.multiplicity_le_bushCount`, which caps the multiplicity of any family
of pairwise essentially distinct `δ`-tubes by `bushCount.C * δ ^ (-2)` in dimension three, for
`δ ≤ bushSeparation.δ`. Combining it with the trivial bound `μ ≤ |s|` by a geometric mean — the
algebraic step `Kakeya.frostmanEstimate_one_algebra` — gives `K_F(1)`; the Frostman and fullness
hypotheses of `Kakeya.FrostmanEstimate` are unused at `β = 1`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Topology Filter ShadedBody

namespace Kakeya

universe v

/-- **The bush bound, multiplicity form, in `ℝ ^ 3`.** The `δ ^ (-2)` of
`Kakeya.multiplicity_le_bushCount` moved to the left-hand side, which is the shape the
algebraic step `Kakeya.frostmanEstimate_one_algebra` consumes. Requires `0 < δ` to cancel
`δ ^ (-2) * δ ^ 2 = 1`. -/
theorem multiplicity_mul_sq_le_bushCount {δ : ℝ≥0} (hδ_pos : 0 < δ)
    (hδ_le : δ ≤ bushSeparation.δ)
    {ι : Type*} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (hED : (s : Set ι).Pairwise
      fun i j ↦ IsEssentiallyDistinct (T i).carrier (T j).carrier) :
    ShadedBody.multiplicity s (fun i ↦ (T i).toShadedBody) * (δ : ℝ≥0∞) ^ (2 : ℕ) ≤
      (bushCount.C : ℝ≥0∞) := by
  have hδ_ne0 : (δ : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hδ_pos)
  have hδ_neTop : (δ : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hcancel : (δ : ℝ≥0∞) ^ (-2 : ℝ) * (δ : ℝ≥0∞) ^ (2 : ℕ) = 1 := by
    rw [← ENNReal.rpow_natCast (δ : ℝ≥0∞) 2, ← ENNReal.rpow_add _ _ hδ_ne0 hδ_neTop]
    norm_num
  calc
    ShadedBody.multiplicity s (fun i ↦ (T i).toShadedBody) * (δ : ℝ≥0∞) ^ (2 : ℕ)
        ≤ ((bushCount.C : ℝ≥0∞) * (δ : ℝ≥0∞) ^ (-2 : ℝ)) * (δ : ℝ≥0∞) ^ (2 : ℕ) :=
      mul_le_mul' (multiplicity_le_bushCount hδ_le s T hED) le_rfl
    _ = (bushCount.C : ℝ≥0∞) * ((δ : ℝ≥0∞) ^ (-2 : ℝ) * (δ : ℝ≥0∞) ^ (2 : ℕ)) :=
      mul_assoc _ _ _
    _ = (bushCount.C : ℝ≥0∞) := by rw [hcancel, mul_one]

/-- The algebraic step behind the base case.

The two available bounds on the multiplicity `m` are `m * δ ^ 2 ≤ P` (the trivial bound,
strong for small `P`) and `m * δ ^ 2 ≤ C` (the bush bound, strong for large `P`). Neither
alone suffices; their geometric mean does. Multiplying them and taking square roots gives
`m * δ ^ 2 ≤ C ^ (1/2) * P ^ (1/2)`, and `C ^ (1/2) ≤ δ ^ (-ε)` absorbs the constant.

The conclusion carries the single real power `δ ^ (-ε - 2)`, which is the shape in which the
exponent appears in `Kakeya.FrostmanEstimate` at `β = 1`. -/
theorem frostmanEstimate_one_algebra {δ : ℝ≥0} (hδ_pos : 0 < δ) (hδ1 : δ ≤ 1)
    {ε : ℝ} {C : ℝ≥0} {m P : ℝ≥0∞}
    (hmP : m * (δ : ℝ≥0∞) ^ (2 : ℕ) ≤ P)
    (hmC : m * (δ : ℝ≥0∞) ^ (2 : ℕ) ≤ (C : ℝ≥0∞))
    (hCabsorb : (C : ℝ≥0∞) ^ (1 / 2 : ℝ) ≤ (δ : ℝ≥0∞) ^ (-ε)) :
    m ≤ (δ : ℝ≥0∞) ^ (-ε - 2) * P ^ (1 / 2 : ℝ) := by
  have hδ_ne0 : (δ : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hδ_pos)
  have hδ_neTop : (δ : ℝ≥0∞) ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt (ENNReal.coe_le_coe.mpr hδ1) ENNReal.one_lt_top)
  have hz_ne0 : (δ : ℝ≥0∞) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hδ_ne0
  have hz_neTop : (δ : ℝ≥0∞) ^ (2 : ℕ) ≠ ⊤ := ENNReal.pow_ne_top hδ_neTop
  -- (m * δ^2)^2 ≤ C * P
  have hsq : (m * (δ : ℝ≥0∞) ^ (2 : ℕ)) ^ (2 : ℕ) ≤ (C : ℝ≥0∞) * P := by
    rw [pow_two]
    exact mul_le_mul' hmC hmP
  -- (z ^ (2:ℕ)) ^ (1/2) = z   where z = m * δ^2
  have hz_pow : ((m * (δ : ℝ≥0∞) ^ (2 : ℕ)) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) =
      m * (δ : ℝ≥0∞) ^ (2 : ℕ) := by
    rw [← ENNReal.rpow_natCast (m * (δ : ℝ≥0∞) ^ (2 : ℕ)) 2]
    rw [← ENNReal.rpow_mul]
    norm_num
  -- raise to the power 1/2: m * δ^2 ≤ (C * P) ^ (1/2)
  have hsq_rt : m * (δ : ℝ≥0∞) ^ (2 : ℕ) ≤
      ((C : ℝ≥0∞) * P) ^ (1 / 2 : ℝ) := by
    have h := ENNReal.rpow_le_rpow hsq (by norm_num : 0 ≤ (1 / 2 : ℝ))
    rw [hz_pow] at h
    exact h
  -- (C * P) ^ (1/2) = C ^ (1/2) * P ^ (1/2)
  have hrhs : ((C : ℝ≥0∞) * P) ^ (1 / 2 : ℝ) =
      (C : ℝ≥0∞) ^ (1 / 2 : ℝ) * P ^ (1 / 2 : ℝ) :=
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
  -- m * δ^2 ≤ C ^ (1/2) * P ^ (1/2)
  have h_abs : m * (δ : ℝ≥0∞) ^ (2 : ℕ) ≤
      (C : ℝ≥0∞) ^ (1 / 2 : ℝ) * P ^ (1 / 2 : ℝ) := by
    rw [← hrhs]
    exact hsq_rt
  -- absorb C ^ (1/2) ≤ δ ^ (-ε):  m * δ^2 ≤ δ ^ (-ε) * P ^ (1/2)
  have hle_raw : m * (δ : ℝ≥0∞) ^ (2 : ℕ) ≤ (δ : ℝ≥0∞) ^ (-ε) * P ^ (1 / 2 : ℝ) :=
    le_trans h_abs (mul_le_mul' hCabsorb le_rfl)
  -- δ ^ (-ε - 2) * δ ^ 2 = δ ^ (-ε)   (real-exponent additivity)
  have hδpow : (δ : ℝ≥0∞) ^ (-ε - 2) * (δ : ℝ≥0∞) ^ (2 : ℕ) = (δ : ℝ≥0∞) ^ (-ε) := by
    calc
      (δ : ℝ≥0∞) ^ (-ε - 2) * (δ : ℝ≥0∞) ^ (2 : ℕ)
          = (δ : ℝ≥0∞) ^ (-ε - 2) * (δ : ℝ≥0∞) ^ (2 : ℝ) := by
            congr 1
            exact (ENNReal.rpow_natCast (δ : ℝ≥0∞) 2).symm
      _ = (δ : ℝ≥0∞) ^ ((-ε - 2) + (2 : ℝ)) := by
            rw [ENNReal.rpow_add _ _ hδ_ne0 hδ_neTop]
      _ = (δ : ℝ≥0∞) ^ (-ε) := by congr 1; ring
  -- cancel δ^2 on the left by multiplying both sides through
  rw [← ENNReal.mul_le_mul_iff_left (c := (δ : ℝ≥0∞) ^ (2 : ℕ)) hz_ne0 hz_neTop]
  calc
    m * (δ : ℝ≥0∞) ^ (2 : ℕ) ≤ (δ : ℝ≥0∞) ^ (-ε) * P ^ (1 / 2 : ℝ) := hle_raw
    _ = (δ : ℝ≥0∞) ^ (-ε - 2) * P ^ (1 / 2 : ℝ) * (δ : ℝ≥0∞) ^ (2 : ℕ) := by
      rw [mul_right_comm]
      rw [hδpow]

/-- [Base case of the bootstrap]
The partial Frostman estimate `K_F(1)` holds in `ℝ ^ 3`.

Unlike the case `β = 0`, this is not a consequence of `μ ≤ |s|`: the correct input is the
bush bound on the number of essentially distinct `δ`-tubes through a point, while the
Frostman hypothesis enters only through a lower bound for `P = |s| * δ ^ 2`. -/
theorem frostmanEstimate_one : FrostmanEstimate.{v} (EuclideanSpace ℝ (Fin 3)) 1 := by
  intro ε hε
  refine ⟨1, zero_lt_one, ?_⟩
  have hC_enn_pos : 0 < (bushCount.C : ℝ≥0∞) := ENNReal.coe_pos.mpr bushCount.C_pos
  have hC_enn_ne_top : (bushCount.C : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hC_cond : ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0,
      (bushCount.C : ℝ≥0∞) ^ (1 / 2 : ℝ) ≤ (δ : ℝ≥0∞) ^ (-ε) := by
    have hC_target : 0 < (bushCount.C : ℝ≥0∞) ^ (-(1 / 2 : ℝ)) :=
      ENNReal.rpow_pos hC_enn_pos hC_enn_ne_top
    have h_event : ∀ᶠ (δ : ℝ≥0) in 𝓝[>] (0 : ℝ≥0),
        (δ : ℝ≥0∞) ^ ε ≤ (bushCount.C : ℝ≥0∞) ^ (-(1 / 2 : ℝ)) :=
      ENNReal.eventually_coe_rpow_le_of_pos hε hC_target
    filter_upwards [h_event] with δ hδ
    calc
      (bushCount.C : ℝ≥0∞) ^ (1 / 2 : ℝ)
          = (bushCount.C : ℝ≥0∞) ^ (-(-(1 / 2 : ℝ))) := by congr 1; ring
      _ = ((bushCount.C : ℝ≥0∞) ^ (-(1 / 2 : ℝ)))⁻¹ := by rw [ENNReal.rpow_neg]
      _ ≤ ((δ : ℝ≥0∞) ^ ε)⁻¹ := ENNReal.inv_le_inv.mpr hδ
      _ = (δ : ℝ≥0∞) ^ (-ε) := by
        rw [← ENNReal.rpow_neg, show -(ε : ℝ) = -ε by ring]
  have hIoo : Set.Ioo (0 : ℝ≥0) bushSeparation.δ ∈ 𝓝[>] (0 : ℝ≥0) :=
    Ioo_mem_nhdsGT bushSeparation.δ_pos
  filter_upwards [hC_cond, hIoo] with δ hC_cond_δ hδ_range
  have hδ_pos : 0 < δ := hδ_range.1
  have hδ_bush : δ ≤ bushSeparation.δ := le_of_lt hδ_range.2
  have hδ_le1 : δ ≤ 1 := le_trans hδ_bush bushSeparation.δ_le_one
  intro ι s T hball hED hFrost hFull
  by_cases hcard : s.card = 0
  · have hs : s = ∅ := Finset.card_eq_zero.mp hcard
    subst hs; simp
  set m : ℝ≥0∞ := multiplicity s (fun i ↦ (T i).toShadedBody)
  set P : ℝ≥0∞ := (s.card : ℝ≥0∞) * (δ : ℝ≥0∞) ^ (2 : ℕ)
  have hm_le_card : m ≤ (s.card : ℝ≥0∞) := by
    simpa [m] using (ShadedBody.multiplicity_le_card s (fun i ↦ (T i).toShadedBody))
  have hmP : m * (δ : ℝ≥0∞) ^ (2 : ℕ) ≤ P := mul_le_mul' hm_le_card le_rfl
  have hbush_applied : m * (δ : ℝ≥0∞) ^ (2 : ℕ) ≤ (bushCount.C : ℝ≥0∞) :=
    multiplicity_mul_sq_le_bushCount hδ_pos hδ_bush s T hED
  have h_alg := frostmanEstimate_one_algebra (δ := δ) (ε := ε) (C := bushCount.C)
    (m := m) (P := P) hδ_pos hδ_le1 hmP hbush_applied hC_cond_δ
  rw [show (-ε - 2 * 1 : ℝ) = -ε - 2 by ring]
  rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by ring]
  rw [finrank_euclideanSpace_fin]
  norm_num
  simpa [m, P] using h_alg

end Kakeya

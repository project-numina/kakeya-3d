/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Multiplicity

/-!
# The spine cardinality dichotomy of Main Lemma 2
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ShadedBody

namespace Kakeya.MainLemma2.Reduction

/-! ### Arithmetic spine -/

/-- **`δ ^ (-γ) ≤ N ^ γ` as soon as `δ⁻¹ ≤ N`.** -/
theorem rpow_neg_le_rpow_of_inv_le {d N : ℝ≥0∞} {γ : ℝ} (hγ : 0 ≤ γ) (h : d⁻¹ ≤ N) :
    d ^ (-γ) ≤ N ^ γ := by
  rw [ENNReal.rpow_neg, ← ENNReal.inv_rpow]
  exact ENNReal.rpow_le_rpow h hγ

/-- Bridge: a real cardinality lower bound `δ⁻¹ ≤ N` becomes the `ℝ≥0∞` one. -/
theorem coe_inv_le_natCast {δ : ℝ≥0} (hδ : 0 < δ) {n : ℕ} (h : (δ : ℝ)⁻¹ ≤ (n : ℝ)) :
    (δ : ℝ≥0∞)⁻¹ ≤ (n : ℝ≥0∞) := by
  rw [← ENNReal.coe_inv hδ.ne']
  rw [show ((n : ℝ≥0∞)) = ((n : ℝ≥0) : ℝ≥0∞) by simp]
  rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
  simpa using h

/-! ### Elementary cardinality/multiplicity facts -/

section Multiplicity

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

end Multiplicity

/-! ### The two branches of the cardinality dichotomy -/

section Branches

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

/-- **Large-cardinality branch.** -/
theorem katzTaoGoal_of_absoluteLoss_of_card_ge {s : Finset ι} {V : ι → ShadedBody E} {δ : ℝ≥0}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ε ε₀ γ : ℝ} (hγ0 : 0 ≤ γ) (hloss : ε₀ ≤ ε + γ)
    (hcard : (δ : ℝ)⁻¹ ≤ (s.card : ℝ))
    (h : ∑ i ∈ s, volume (V i).shade
          ≤ (δ : ℝ≥0∞) ^ (-ε₀) * volume (⋃ i ∈ s, (V i).shade)) :
    ∑ i ∈ s, volume (V i).shade
      ≤ (δ : ℝ≥0∞) ^ (-ε) * (s.card : ℝ≥0∞) ^ γ * volume (⋃ i ∈ s, (V i).shade) := by
  have hd0 : (δ : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ.ne'
  have hdtop : (δ : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hd1 : (δ : ℝ≥0∞) ≤ 1 := ENNReal.coe_le_one_iff.mpr hδ1
  have hkey : (δ : ℝ≥0∞) ^ (-ε₀) ≤ (δ : ℝ≥0∞) ^ (-ε) * (s.card : ℝ≥0∞) ^ γ := by
    calc (δ : ℝ≥0∞) ^ (-ε₀)
        ≤ (δ : ℝ≥0∞) ^ (-ε + -γ) :=
          ENNReal.rpow_le_rpow_of_exponent_ge hd1 (by linarith)
      _ = (δ : ℝ≥0∞) ^ (-ε) * (δ : ℝ≥0∞) ^ (-γ) := ENNReal.rpow_add _ _ hd0 hdtop
      _ ≤ (δ : ℝ≥0∞) ^ (-ε) * (s.card : ℝ≥0∞) ^ γ := by
          gcongr
          exact rpow_neg_le_rpow_of_inv_le hγ0 (coe_inv_le_natCast hδ hcard)
  exact h.trans (by gcongr)

end Branches

/-! ### The dichotomy -/

section Dichotomy

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

end Dichotomy

/-! ### Discharging `δ⁻¹ ≤ |T|` from a coarse-scale count -/

section ScaleCount

end ScaleCount

/-! ### Sharpness of the trivial branch -/

section Sharpness

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

end Sharpness

end Kakeya.MainLemma2.Reduction

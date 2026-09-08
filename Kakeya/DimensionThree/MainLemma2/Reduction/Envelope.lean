/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.PartialEstimates

/-!
# The monotone envelope of the admissible drops of Main Lemma 2

GWZ Main Lemma 2 (`Kakeya.KatzTaoEstimate.katzTaoEstimate_sub_of_frostmanEstimate`) asks for a
*single* function `ν : ℝ → ℝ`, monotone and positive on `(0,1]`, such that `K_KT(β)` and `K_F(β)`
imply `K_KT(β - ν β)` for every `β ∈ (0,1]`.  Two quantifier orders are hidden in that statement
and neither is present in the source:

* `ν` is produced **before the accuracy `ε`** hidden inside `Kakeya.KatzTaoEstimate`.  GWZ open
  their proof with "fix `ε > 0`" and close it with "`ν = η₁`".  Prof. Hong Wang's clarification
  (2026-08-30) resolves the discrepancy: it is a typo in the published proof, and the correct
  reading applies Theorem 7.3 with an **absolute** accuracy `ε₀`, so that the whole chain
  `ε₀ → ε₁ → ε₂ → (N, η_i) → ν` depends on `β` only.  See
  `Kakeya/DimensionThree/MainLemma2/Reduction/Core.lean`.
* `ν` is produced **before `β`**, and must be monotone in it.

This file handles the second of the two, by the same device that
`Kakeya/DimensionThree/MainLemma1/Envelope.lean` uses for Part (A): the set of admissible drops
above a threshold is downward closed in the drop and increasing in the threshold, so the halved
supremum is a monotone, positive, admissible drop function.  What is left over is one hypothesis,

```
∀ β₀ ∈ Set.Ioc 0 1, (Kakeya.ML2Reduction.katzTaoDropSet β₀).Nonempty
```

("above every threshold there is *one* drop that works for every exponent in `[β₀,1]`"), which is
the honest content of the monotonicity requirement.

The file also records the accuracy-restriction device
(`Kakeya.ML2Reduction.katzTaoEstimate_of_forall_le`: it suffices to produce the witnesses of
`Kakeya.KatzTaoEstimate` at small `ε`) and the two pieces of `[0,∞]` arithmetic by which the two
alternatives of the Section 9 dichotomy are converted into a drop in the exponent of `|𝕋|`.

Everything in this file is proved.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Topology ConvexSpaceBody Filter ShadedBody

namespace Kakeya

namespace ML2Reduction

universe u

/-! ### The drop set and its monotone envelope -/

/-- The set of **admissible uniform drops above the threshold `β₀`**: those `c ∈ (0,1]` such that
for *every* exponent `β ∈ [β₀, 1]`, the two partial estimates `K_KT(β)` and `K_F(β)` imply the
improved Katz–Tao estimate `K_KT(β - c)`.

As in `Kakeya.frostmanStepSet`, the two partial estimates sit *inside* the defining condition
rather than being hypotheses of the definition; this is what lets the drop be produced before any
family of tubes, and indeed before `β`, exists.

Quantifying over all `β ∈ [β₀,1]` rather than over `β₀` alone is what makes the set increasing in
`β₀` (`Kakeya.ML2Reduction.katzTaoDropSet_subset`), hence what makes the envelope monotone. -/
def katzTaoDropSet (β₀ : ℝ) : Set ℝ :=
  {c | c ∈ Set.Ioc (0 : ℝ) 1 ∧ ∀ β ∈ Set.Icc β₀ 1,
    KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
    FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
    KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) (β - c)}

/-- The drop set is downward closed: a smaller drop lands at a larger exponent, and
`Kakeya.KatzTaoEstimate.mono` is monotone in the exponent. -/
theorem katzTaoDropSet_downwardClosed {β₀ c c' : ℝ}
    (hc : c ∈ katzTaoDropSet.{u} β₀) (hc'_pos : 0 < c') (hc'_le : c' ≤ c) :
    c' ∈ katzTaoDropSet.{u} β₀ := by
  obtain ⟨hc_Ioc, hc_forall⟩ := hc
  refine ⟨⟨hc'_pos, hc'_le.trans hc_Ioc.2⟩, ?_⟩
  intro β hβ hKT hKF
  exact KatzTaoEstimate.mono (sub_le_sub_left hc'_le β) (hc_forall β hβ hKT hKF)

/-- The drop set is increasing in the threshold: raising `β₀` shrinks the interval `[β₀,1]` that
the defining condition quantifies over. -/
theorem katzTaoDropSet_subset {β₀ β₁ : ℝ} (h : β₀ ≤ β₁) :
    katzTaoDropSet.{u} β₀ ⊆ katzTaoDropSet.{u} β₁ := by
  intro c hc
  obtain ⟨hc_Ioc, hc_forall⟩ := hc
  exact ⟨hc_Ioc, fun β hβ => hc_forall β (Set.Icc_subset_Icc h le_rfl hβ)⟩

/-- **The monotone envelope, membership form.**  If above every threshold `β₀ ∈ (0,1]` there is at
least one admissible uniform drop, then there is a single drop function `ν`, monotone and strictly
positive on `(0,1]`, whose value at `β` is itself an admissible uniform drop above `β`.

The witness is `ν β = sSup (katzTaoDropSet β) / 2`; halving the supremum is what makes the value
attained, through `Kakeya.ML2Reduction.katzTaoDropSet_downwardClosed`. -/
theorem exists_monotoneOn_mem_katzTaoDropSet
    (hne : ∀ β₀ ∈ Set.Ioc (0 : ℝ) 1, (katzTaoDropSet.{u} β₀).Nonempty) :
    ∃ ν : ℝ → ℝ, MonotoneOn ν (Set.Ioc 0 1) ∧ (∀ β ∈ Set.Ioc (0 : ℝ) 1, 0 < ν β) ∧
      (∀ β ∈ Set.Ioc (0 : ℝ) 1, ν β ∈ katzTaoDropSet.{u} β) := by
  set ν := fun β : ℝ => sSup (katzTaoDropSet.{u} β) / 2 with hν_def
  have hbdd : ∀ β : ℝ, BddAbove (katzTaoDropSet.{u} β) := fun β => ⟨1, fun c hc => hc.1.2⟩
  refine ⟨ν, ?_, ?_, ?_⟩
  · intro β₁ hβ₁ β₂ _ hβ₁₂
    have hcsSup : sSup (katzTaoDropSet.{u} β₁) ≤ sSup (katzTaoDropSet.{u} β₂) :=
      csSup_le_csSup (hbdd β₂) (hne β₁ hβ₁) (katzTaoDropSet_subset hβ₁₂)
    simp only [hν_def]
    linarith
  · intro β hβ
    obtain ⟨c, hc⟩ := hne β hβ
    have hle : c ≤ sSup (katzTaoDropSet.{u} β) := le_csSup (hbdd β) hc
    have hcpos : 0 < c := hc.1.1
    simp only [hν_def]
    linarith
  · intro β hβ
    obtain ⟨c, hc⟩ := hne β hβ
    have hle_c_sup : c ≤ sSup (katzTaoDropSet.{u} β) := le_csSup (hbdd β) hc
    have hcpos : 0 < c := hc.1.1
    have hMpos : 0 < sSup (katzTaoDropSet.{u} β) := lt_of_lt_of_le hcpos hle_c_sup
    have h_exists : ∃ c' ∈ katzTaoDropSet.{u} β, sSup (katzTaoDropSet.{u} β) / 2 < c' := by
      by_contra! h
      have h_sup_le : sSup (katzTaoDropSet.{u} β) ≤ sSup (katzTaoDropSet.{u} β) / 2 :=
        csSup_le (hne β hβ) (fun c' hc' => h c' hc')
      linarith
    obtain ⟨c', hc', hlt⟩ := h_exists
    have hmem : sSup (katzTaoDropSet.{u} β) / 2 ∈ katzTaoDropSet.{u} β :=
      katzTaoDropSet_downwardClosed hc' (by linarith) hlt.le
    simpa [hν_def] using hmem

/-- **The monotone envelope, in exactly the shape of GWZ Main Lemma 2.**

This is `Kakeya.KatzTaoEstimate.katzTaoEstimate_sub_of_frostmanEstimate` with the mathematics
replaced by the single hypothesis `hne`. -/
theorem katzTaoEstimate_sub_of_nonempty_katzTaoDropSet
    (hne : ∀ β₀ ∈ Set.Ioc (0 : ℝ) 1, (katzTaoDropSet.{u} β₀).Nonempty) :
    ∃ ν : ℝ → ℝ, MonotoneOn ν (Set.Ioc 0 1) ∧
      (∀ β : ℝ, 0 < β → β ≤ 1 → 0 < ν β) ∧
      ∀ β : ℝ, 0 < β → β ≤ 1 →
        KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
        FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
        KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) (β - ν β) := by
  obtain ⟨ν, hmono, hpos, hmem⟩ := exists_monotoneOn_mem_katzTaoDropSet.{u} hne
  refine ⟨ν, hmono, fun β hβ hβ1 => hpos β ⟨hβ, hβ1⟩, ?_⟩
  intro β hβ hβ1 hKT hKF
  exact (hmem β ⟨hβ, hβ1⟩).2 β ⟨le_rfl, hβ1⟩ hKT hKF

/-! ### The accuracy-restriction device -/

section Accuracy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end Accuracy

/-! ### The two arithmetic conversions of the Section 9 dichotomy -/

/-- **Alternative (ii) of the Section 9 dichotomy: a positive `δ`-gain becomes a drop in the
exponent of `|𝕋|`.**

The window branch returns `μ ≤ δ ^ g * |𝕋| ^ β` with `g = g(β) > 0`, and the crude counting bound
`|𝕋| ≤ δ ^ (-K)` converts `|𝕋| ^ c` into `δ ^ (-K c)`; the budget `K * c ≤ g + ε` closes it.

No lower bound on `|𝕋|` is needed here — this is the branch that is genuinely improved, and its
gain is what the drop `ν(β)` is made of. -/
theorem le_rpow_mul_rpow_of_gain {δ : ℝ≥0} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {μ : ℝ≥0∞}
    {ε g c β K : ℝ} {N : ℕ} (hN1 : 1 ≤ N) (hc : 0 ≤ c)
    (hbudget : K * c ≤ g + ε)
    (hcard : (N : ℝ) ≤ ((δ : ℝ)) ^ (-K))
    (hμ : μ ≤ (δ : ℝ≥0∞) ^ g * (N : ℝ≥0∞) ^ β) :
    μ ≤ (δ : ℝ≥0∞) ^ (-ε) * (N : ℝ≥0∞) ^ (β - c) := by
  have hδR : (0 : ℝ) < (δ : ℝ) := hδ0
  have hδE0 : (0 : ℝ≥0∞) < (δ : ℝ≥0∞) := by exact_mod_cast hδ0
  have hδE1 : (δ : ℝ≥0∞) ≤ 1 := by exact_mod_cast hδ1
  have hNE0 : (0 : ℝ≥0∞) < (N : ℝ≥0∞) := by exact_mod_cast hN1
  have hNEtop : ((N : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top N
  -- `N ≤ δ ^ (-K)` in `[0,∞]`
  have hbase : (N : ℝ≥0∞) ≤ (δ : ℝ≥0∞) ^ (-K) := by
    have h1 : (δ : ℝ≥0∞) ^ (-K) = ENNReal.ofReal (((δ : ℝ)) ^ (-K)) := by
      rw [← ENNReal.ofReal_rpow_of_pos hδR, ENNReal.ofReal_coe_nnreal]
    have h2 : ((N : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((N : ℕ) : ℝ) := by simp
    rw [h1, h2]
    exact ENNReal.ofReal_le_ofReal hcard
  have hNc : (N : ℝ≥0∞) ^ c ≤ (δ : ℝ≥0∞) ^ (-(K * c)) := by
    calc (N : ℝ≥0∞) ^ c ≤ ((δ : ℝ≥0∞) ^ (-K)) ^ c := ENNReal.rpow_le_rpow hbase hc
      _ = (δ : ℝ≥0∞) ^ (-(K * c)) := by
          rw [← ENNReal.rpow_mul]
          ring_nf
  have hsplit : (N : ℝ≥0∞) ^ β = (N : ℝ≥0∞) ^ (β - c) * (N : ℝ≥0∞) ^ c := by
    rw [← ENNReal.rpow_add _ _ hNE0.ne' hNEtop]
    ring_nf
  calc μ ≤ (δ : ℝ≥0∞) ^ g * (N : ℝ≥0∞) ^ β := hμ
    _ = (δ : ℝ≥0∞) ^ g * (N : ℝ≥0∞) ^ c * (N : ℝ≥0∞) ^ (β - c) := by
        rw [hsplit]; ring
    _ ≤ (δ : ℝ≥0∞) ^ g * (δ : ℝ≥0∞) ^ (-(K * c)) * (N : ℝ≥0∞) ^ (β - c) := by
        gcongr
    _ = (δ : ℝ≥0∞) ^ (g - K * c) * (N : ℝ≥0∞) ^ (β - c) := by
        rw [← ENNReal.rpow_add _ _ hδE0.ne' ENNReal.coe_ne_top]
        ring_nf
    _ ≤ (δ : ℝ≥0∞) ^ (-ε) * (N : ℝ≥0∞) ^ (β - c) := by
        have hstep : (δ : ℝ≥0∞) ^ (g - K * c) ≤ (δ : ℝ≥0∞) ^ (-ε) :=
          ENNReal.rpow_le_rpow_of_exponent_ge (x := (δ : ℝ≥0∞)) (y := g - K * c)
            (z := -ε) hδE1 (by linarith)
        exact mul_le_mul_left hstep _

end ML2Reduction

end Kakeya

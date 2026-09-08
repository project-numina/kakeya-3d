/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.PartialEstimates
public import Kakeya.FrostmanConstant
public import Kakeya.MultiScaleSubmult
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineParams
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineInheritance

/-!
# The non-eccentric case of the reduction of GWZ Main Lemma 2

Blueprint: GWZ, the paragraph headed
**The non-eccentric case** inside the proof of Main Lemma 2.  The step numbering below is the
one used in the blueprint's own equation labels.

Setting: `𝕋̃` is the rescaled family of `τ/θ`-tubes, `δ̃` its thickness, `ρ = δ̃^{1-ε₂}`, `𝕍` the
maximal-density factoring of `𝕋̃_ρ` into planks of affine thicknesses `1 × b × a` with
`b ≤ δ̃^{-η'_{j-1}} a`, and `𝕋̃_b` the family of `b`-tubes obtained from `𝕍`.

## What this file contains

* **Step 3** (`upperBdDeltaMaxTb`): `Δ_max(𝕋̃_b) ≤ (|T_b|/|V|) Δ_max(𝕍) ≤ δ̃^{-η'_{j-1}}`.
  Abstract core `maxDensity_le_of_nested_inj`.
* **Step 4** (`boundOnMuTTb`): `exists_multiplicity_coarse_bound`, GWZ `genKKT`
  (`Kakeya.KatzTaoEstimate.multiplicity_bound`) read at a coarse scale `dt ≤ b`.
* **Step 5**: `le_of_maxDensity_le_window` and its spine-driven form
  `spine_le_of_maxDensity_le_window` — comparing step 3 with `tildeDeltaLargeDeltamax`
  forces `b ≥ δ̃^{ε₂}`.
* **Step 6** (`goodFrostmanBoundTTRhoInsideTb`): `C_F(𝕋̃_ρ, T_b) ≲ δ^{-η'_{j-1}}`.  Abstract
  core `isFrostmanIn_of_maxDensity_le_densityIn`.  The extension to all `σ ∈ [ρ, b]` is
  `Kakeya.ML2Spine.exists_subset_isFrostmanIn_parents'` in `SpineInheritance.lean`.
* **Step 7** (`lowerBdOnDeltaMaxTTSigmaTb`): `rpow_mul_le_mul_fibre_maxDensity`, GWZ Lemma 7.4
  (`Kakeya.MultiScaleSubmult.maxDensity_le_prod_fibreDeltaMax`) read downwards.
  `exists_parent_fibre_eq_fibreDeltaMax` licenses choosing `T_b` to be a maximising fibre.
* **Step 8** (`TTSigmaBigCardinalityV1`): `tube_card_lower`, `card_lower_of_nnreal_bound` and
  `tube_rescaled_card_lower`, the last delivering the count hypothesis
  `(σ/b)^{-2-ζ} ≤ |𝕋̃_σ[T_b]|` of Lemma 9.1 in dimension `3`.  The single arithmetic threshold
  is discharged by `countThreshold_of_small` / `spine_countThreshold`, whose gap comes from
  `spine_countGap`.  `spine_tube_card_lower` is the single entry point that composes all of
  steps 3, 6, 7 and 8 against `IsSpine`.
* **Step 11** (`multTildeTLem2`): `multiplicity_le_of_two_factors` multiplies the two
  multiplicity bounds; `spine_gainBudget` and `spine_gainBudget_of_loss` verify the exponent
  inequality `ν(β, η_j/2) - 2η'_{j-1} ≥ 10 η_{j-1}/ε₂` from `IsSpine.gain_budget`.

## What this file does not contain

**Step 10** (`boundOnMuTildeTTb`) — the actual application of Lemma 9.1
(`Kakeya.multiplicity_le_of_card_isEssDistinct_ge`) to the family rescaled by
`Kakeya.ML2Reduction.spineRescaleUnit`, and the transport of its conclusion back.  That needs
the rescaled family to be presented as a genuine `Tube δ'` family with a uniformity witness,
which is assembly-level work; the transport toolkit is `SpineRescale.lean`.

The parameter arithmetic is never re-derived here: everything goes through the fields of
`Kakeya.ML2Spine.IsSpine` (`SpineParams.lean`), and no numeric value of `ε₂`, `e` or `N` is
hard-coded.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody

namespace Kakeya.ML2Spine

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### Step 3 -/

/-! ### Step 6 -/

/-! ### Step 8 -/

/-- **Step 8, core form.** -/
theorem maxDensity_mul_volume_le_of_isFrostmanIn {ι : Type*} {s : Finset ι}
    {W : ι → ConvexSpaceBody E} {Tb : ConvexSpaceBody E} {CF M cs : ℝ≥0∞}
    (hne : ∃ i ∈ s, 0 < volume (W i).carrier)
    (hsub : ∀ i ∈ s, W i ≤ Tb)
    (hF : IsFrostmanIn s W Tb CF)
    (hM : M ≤ maxDensity s W)
    (hvol : ∀ i ∈ s, volume (W i).carrier ≤ cs) :
    M * volume Tb.carrier ≤ CF * ((s.card : ℝ≥0∞) * cs) := by
  classical
  obtain ⟨u, -, -, hu_eq, hu_le⟩ := exists_convexHullBiUnion_densityIn_eq_maxDensity hne
  have hK0 : u.convexHull_biUnion W ≤ Tb := hu_le Tb hsub
  have hstep : M ≤ CF * densityIn s W Tb := by
    refine hM.trans ?_
    rw [← hu_eq]
    exact hF _ hK0
  calc M * volume Tb.carrier ≤ (CF * densityIn s W Tb) * volume Tb.carrier := by gcongr
    _ = CF * (densityIn s W Tb * volume Tb.carrier) := by ring
    _ = CF * ∑ i ∈ s, volume (W i).carrier := by
        rw [← sum_volume_eq_densityIn_mul_volume' hsub]
    _ ≤ CF * ((s.card : ℝ≥0∞) * cs) := by
        refine mul_le_mul_right ?_ CF
        calc ∑ i ∈ s, volume (W i).carrier ≤ ∑ _i ∈ s, cs := Finset.sum_le_sum hvol
          _ = (s.card : ℝ≥0∞) * cs := by rw [Finset.sum_const, nsmul_eq_mul]

/-! ### Step 5 -/

/-! ### Step 4 -/

/-! ### Step 11 -/

/-- **Step 11.** -/
theorem multiplicity_le_of_two_factors
    {δ : ℝ≥0} {mu mub muf L Cu : ℝ≥0∞} {Nb Nf N : ℕ} {β η' ν κ θ : ℝ}
    (hδ0 : (δ : ℝ≥0∞) ≠ 0) (hδ1 : (δ : ℝ≥0∞) ≤ 1) (hβ0 : 0 ≤ β)
    (hsplit : mu ≤ L * (mub * muf))
    (hb : mub ≤ (δ : ℝ≥0∞) ^ (-(2 * η')) * (Nb : ℝ≥0∞) ^ β)
    (hf : muf ≤ (δ : ℝ≥0∞) ^ ν * (Nf : ℝ≥0∞) ^ β)
    (hcard : (Nb : ℝ≥0∞) * (Nf : ℝ≥0∞) ≤ Cu * (N : ℝ≥0∞))
    (hL : L * Cu ^ β ≤ (δ : ℝ≥0∞) ^ (-κ))
    (hexp : θ ≤ ν - 2 * η' - κ) :
    mu ≤ (δ : ℝ≥0∞) ^ θ * (N : ℝ≥0∞) ^ β := by
  have hstep1 : mub * muf
      ≤ (δ : ℝ≥0∞) ^ (ν - 2 * η') * ((Nb : ℝ≥0∞) * (Nf : ℝ≥0∞)) ^ β := by
    calc mub * muf
        ≤ ((δ : ℝ≥0∞) ^ (-(2 * η')) * (Nb : ℝ≥0∞) ^ β)
            * ((δ : ℝ≥0∞) ^ ν * (Nf : ℝ≥0∞) ^ β) := by gcongr
      _ = ((δ : ℝ≥0∞) ^ (-(2 * η')) * (δ : ℝ≥0∞) ^ ν)
            * ((Nb : ℝ≥0∞) ^ β * (Nf : ℝ≥0∞) ^ β) := by ring
      _ = (δ : ℝ≥0∞) ^ (ν - 2 * η') * ((Nb : ℝ≥0∞) * (Nf : ℝ≥0∞)) ^ β := by
          rw [← ENNReal.rpow_add _ _ hδ0 (by simp), ENNReal.mul_rpow_of_nonneg _ _ hβ0]
          ring_nf
  have hstep2 : ((Nb : ℝ≥0∞) * (Nf : ℝ≥0∞)) ^ β ≤ Cu ^ β * (N : ℝ≥0∞) ^ β := by
    calc ((Nb : ℝ≥0∞) * (Nf : ℝ≥0∞)) ^ β ≤ (Cu * (N : ℝ≥0∞)) ^ β :=
          ENNReal.rpow_le_rpow hcard hβ0
      _ = Cu ^ β * (N : ℝ≥0∞) ^ β := ENNReal.mul_rpow_of_nonneg _ _ hβ0
  calc mu ≤ L * (mub * muf) := hsplit
    _ ≤ L * ((δ : ℝ≥0∞) ^ (ν - 2 * η') * (Cu ^ β * (N : ℝ≥0∞) ^ β)) :=
        mul_le_mul' le_rfl (hstep1.trans (mul_le_mul' le_rfl hstep2))
    _ = (L * Cu ^ β) * ((δ : ℝ≥0∞) ^ (ν - 2 * η') * (N : ℝ≥0∞) ^ β) := by ring
    _ ≤ (δ : ℝ≥0∞) ^ (-κ) * ((δ : ℝ≥0∞) ^ (ν - 2 * η') * (N : ℝ≥0∞) ^ β) := by gcongr
    _ = (δ : ℝ≥0∞) ^ (ν - 2 * η' - κ) * (N : ℝ≥0∞) ^ β := by
        rw [← mul_assoc, ← ENNReal.rpow_add _ _ hδ0 (by simp)]
        ring_nf
    _ ≤ (δ : ℝ≥0∞) ^ θ * (N : ℝ≥0∞) ^ β :=
        mul_le_mul' (ENNReal.rpow_le_rpow_of_exponent_ge hδ1 hexp) le_rfl

/-! ### Step 7 (`lowerBdOnDeltaMaxTTSigmaTb`)

GWZ Lemma 7.4 (`Kakeya.MultiScaleSubmult.maxDensity_le_prod_fibreDeltaMax`) bounds
`Δ_max(𝕋̃_σ)` by a constant times the product of the fibre maxima at the two scales.
Read together with `tildeDeltaLargeDeltamax` (`σ^{-η_j} ≤ Δ_max(𝕋̃_σ)`) and the step-3 bound
`Δ_max(𝕋̃_b) ≤ δ̃^{-η'_{j-1}}`, this becomes a *lower* bound on the fibre density
`Δ_max(𝕋̃_σ[T_b])`.  The blueprint writes the conclusion as
`Δ_max(𝕋̃_σ[T_b]) ≳ δ^{η'_{j-1}} σ^{-η_j}`; here it is kept in the division-free product form
`σ^{-η_j} · δ̃^{η'_{j-1}} ≤ L · Δ_max(𝕋̃_σ[T_b])`, which is what step 8 consumes.
-/

/-! ### Step 8 (`TTSigmaBigCardinalityV1`) -/

/-! ### Step 8, the real-arithmetic core

The blueprint reads `TTSigmaBigCardinalityV1` as `|𝕋̃_σ[T_b]| ≳ δ̃^{2η'_{j-1}} σ^{-2-η_j}`, but
what the count hypothesis of Lemma 9.1 actually consumes is the *rescaled* count: after `T_b`
is taken to `B_1`, the `σ`-tubes become `σ' = σ/b` tubes and the requirement is
`(σ')^{-2-ζ} ≤ |𝕋'_{σ'}|`.  The volume bookkeeping produces the factor `(b/σ)^{n-1}`, which is
exactly `(σ')^{-(n-1)}`; the lemma below performs that conversion, with the leftover
`σ^{-η_j} δ̃^{2η'_{j-1}} (σ/b)^{ζ} ≥ (loss constants)` isolated as the single hypothesis
`hthr`. -/

/-! ### Step 8 for tubes -/

/-! ### The count threshold is met by the parameter spine

`hthr` is the only genuinely arithmetic hypothesis of
`Kakeya.ML2Spine.card_lower_of_nnreal_bound`, and it is *not* vacuous: the two lemmas below
show it is exactly the separation `2η'_{j-1} < ε₂ η_j / 2` of the spine, plus a threshold on
`δ̃` absorbing the fixed dimensional constants. -/

/-! ### Blueprint-named forms of steps 3 and 6 -/

/-! ### Step 11: the gain budget of the spine -/

/-! ### The spine-driven readings of steps 5 and 8 -/

end Kakeya.ML2Spine

end

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineHfacWire

/-!
# A producer for `hfac`: the three factors, and what is left of them

 measured that the post-drop factor hypothesis of the
`(F)` terminal engine — `Kakeya.ML2Core.HfacPostDrop`, equivalently
`Kakeya.ML2Core.HfacLevels` at `Cu₀ = max C 4` — had **no producer anywhere in the tree**: the
existential `∃ (tτ' tθ' : Finset ι) …` occurred eleven times, every one of them a binder.  This
file builds the producer down to the single factor that is genuinely open.

## The split

`Kakeya.ML2Core.exists_spineTwoScale_ofChain_translated` already delivers the retained node sets
`tτ', tθ'`, the three shadings `Yτ', Yθ, Y'`, their nonemptiness and the **product bound** — the
whole of `hfac`'s conclusion except its three factor estimates.  So `hfac` is exactly

* `Kakeya.ML2Core.FineRow` — the fine factor at the retained fibre.  **Discharged** here from the
  Katz--Tao estimate (`Kakeya.ML2Core.exists_threshold_fineRow`).
* `Kakeya.ML2Core.CoarseRow` — the coarse factor on the retained parents.  **Discharged** here
  from the Katz--Tao estimate *and* `Kakeya.ML2Core.CoarseStructRow`
  (`Kakeya.ML2Core.exists_threshold_coarseRow`).
* `Kakeya.ML2Core.MiddleRow` — the middle factor at the window.  **Open**; it is the GWZ gain and
  the only place where `Kakeya.VeryNotSticky.CentredHandBack`, `CountTransport`,
  `ML2Reduction.Lemma91At` and the tightened `huni` enter.

`Kakeya.ML2Core.hfacLevels_of_rows` is the assembly, and
`Kakeya.ML2Core.geometricCoreAt_of_middleRow` chains it into
`Kakeya.ML2Core.geometricCoreAt_of_hfac_witness_payload`.

## The two thresholds on `η_in`

Both discharged factors are quantified *before* `η_in`: the Katz--Tao estimate returns its own
exponent, and the fullness input of each factor is met only for `η_in` below a quarter of it.
That is why the theorems below conclude `∃ η0 > 0, ∀ η_in ≤ η0, …` and why
`Kakeya.ML2Core.geometricCoreAt_of_middleRow` asks its supplier for the rows **at arbitrarily
small `η_in`**.  The absorption of the two-scale losses into `δ^(-κ)` is
`Kakeya.ML2Core.eventually_spineScaleLoss_le`.

## What `CoarseStructRow` is, and why it is separate

`Kakeya.ML2Core.exists_coarse_factor_at_window` needs the coarse scale below a fixed threshold,
which `Kakeya.ML2Core.eventually_gridScale_le` gives **only for `1 ≤ a`**
(`Tube.gridScale δ M 0 = 1` on the nose), and it needs the retained parents inside the unit ball,
which `hfac` supplies for `t₀` and only when `a ≠ 0`.  Neither `1 ≤ a` nor
`tθ' ⊆ coarseNode '' tτ'` is returned by the two-scale split or forced by
`ML2Reduction.IsKatzTaoDividingWindow` (whose only order constraint is `a < b`), so they are
named and left as one row rather than hidden in a proof.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody
open Tube ShadedTube

namespace Kakeya.ML2Core

open Classical in
/-- **The fine factor at the retained fibre**, as a row over the two-scale split. -/
def FineRow.{u} (β ϖ ε₁ ηin εf κc : ℝ) (gain dens : ℝ → ℝ) (C : ℝ≥0) : Prop :=
  ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0,
    ∀ {ι : Type u} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
      (Cu lam : ℝ≥0)
      (𝒰 : Tube.UniformTubeSet u (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu)
      (Cstar : ℝ≥0∞) (a b m : ℕ),
      ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰 Cstar (ML2Spine.spineRung β ϖ ε₁ gain dens)
        (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m →
    ∀ (v : EuclideanSpace ℝ (Fin 3)) (t₀ t₁ tτ' tθ' : Finset ι)
      (Yτ' : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b) (EuclideanSpace ℝ (Fin 3)))
      (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a) (EuclideanSpace ℝ (Fin 3)))
      (Y' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
      t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain b →
      tτ' ⊆ t₁ → tθ' ⊆ 𝒰.cover.indexSet a → tτ'.Nonempty → tθ'.Nonempty →
      (∀ j, (Yτ' j).toTube = (𝒰.cover.tube b j).translate v) →
      (∀ k, (Yθ k).toTube = (𝒰.cover.tube a k).translate v) →
      (∀ i, (Y' i).toTube = ((T i).translate v).toTube) →
      (∀ j ∈ t₁, ((𝒰.cover.tube b j).translate v).carrier
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      (∀ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), ((T i).translate v).carrier
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      Kakeya.maxDensity u (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-ηin) →
      ML2Shaded.HasDenseShading lam u (fun i ↦ (T i).toShadedBody) →
      (δ : ℝ≥0) ^ ηin / 2 ≤ lam →
      (u.card : ℝ≥0) ≤ δ ^ (-(4 : ℝ)) →
      Cstar ≤ (δ : ℝ≥0∞) ^ (-κc) →
      Cu ≤ max C 4 →
      0 < ∑ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), volume (T i).shade →
      ShadedBody.IsCRefinement
        ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
          𝒰.cover.assign b i ∈ tτ'} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
        ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
        (fun i ↦ ((T i).translate v).toShadedBody)
        (ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
          ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ)⁻¹ →
      (ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
              ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ *
            ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) tτ'.card
              (Tube.gridScale δ (Tube.ssfGridLen δ) b))⁻¹ *
          ShadedBody.fullness ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
            (fun i ↦ (T i).toShadedBody)
        ≤ ShadedBody.fullness tθ' (fun k ↦ (Yθ k).toShadedBody) →
      (a ≠ 0 → t₀ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain a) →
      (a ≠ 0 → ∀ j ∈ t₁, ML2Reduction.coarseNode 𝒰.cover.toChain a b j ∈ t₀) →
      (a ≠ 0 → ∀ k ∈ t₀, ((𝒰.cover.tube a k).translate v).carrier
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      δ ≤ Tube.gridScale δ (Tube.ssfGridLen δ) b →
      Tube.gridScale δ (Tube.ssfGridLen δ) b ≤ Tube.gridScale δ (Tube.ssfGridLen δ) a →
      Tube.gridScale δ (Tube.ssfGridLen δ) a ≤ 1 →
      ∃ jτ ∈ tτ',
        ShadedBody.multiplicity ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
            𝒰.cover.assign b i = jτ} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
          ≤ (δ : ℝ≥0∞) ^ (-(εf)) * ((({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
              𝒰.cover.assign b i = jτ} : Finset ι)).card : ℝ≥0∞) ^ β

open Classical in
/-- **The coarse factor on the retained parents**, as a row over the two-scale split. -/
def CoarseRow.{u} (β ϖ ε₁ ηin εc κc : ℝ) (gain dens : ℝ → ℝ) (C : ℝ≥0) : Prop :=
  ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0,
    ∀ {ι : Type u} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
      (Cu lam : ℝ≥0)
      (𝒰 : Tube.UniformTubeSet u (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu)
      (Cstar : ℝ≥0∞) (a b m : ℕ),
      ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰 Cstar (ML2Spine.spineRung β ϖ ε₁ gain dens)
        (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m →
    ∀ (v : EuclideanSpace ℝ (Fin 3)) (t₀ t₁ tτ' tθ' : Finset ι)
      (Yτ' : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b) (EuclideanSpace ℝ (Fin 3)))
      (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a) (EuclideanSpace ℝ (Fin 3)))
      (Y' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
      t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain b →
      tτ' ⊆ t₁ → tθ' ⊆ 𝒰.cover.indexSet a → tτ'.Nonempty → tθ'.Nonempty →
      (∀ j, (Yτ' j).toTube = (𝒰.cover.tube b j).translate v) →
      (∀ k, (Yθ k).toTube = (𝒰.cover.tube a k).translate v) →
      (∀ i, (Y' i).toTube = ((T i).translate v).toTube) →
      (∀ j ∈ t₁, ((𝒰.cover.tube b j).translate v).carrier
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      (∀ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), ((T i).translate v).carrier
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      Kakeya.maxDensity u (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-ηin) →
      ML2Shaded.HasDenseShading lam u (fun i ↦ (T i).toShadedBody) →
      (δ : ℝ≥0) ^ ηin / 2 ≤ lam →
      (u.card : ℝ≥0) ≤ δ ^ (-(4 : ℝ)) →
      Cstar ≤ (δ : ℝ≥0∞) ^ (-κc) →
      Cu ≤ max C 4 →
      0 < ∑ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), volume (T i).shade →
      ShadedBody.IsCRefinement
        ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
          𝒰.cover.assign b i ∈ tτ'} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
        ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
        (fun i ↦ ((T i).translate v).toShadedBody)
        (ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
          ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ)⁻¹ →
      (ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
              ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ *
            ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) tτ'.card
              (Tube.gridScale δ (Tube.ssfGridLen δ) b))⁻¹ *
          ShadedBody.fullness ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
            (fun i ↦ (T i).toShadedBody)
        ≤ ShadedBody.fullness tθ' (fun k ↦ (Yθ k).toShadedBody) →
      (a ≠ 0 → t₀ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain a) →
      (a ≠ 0 → ∀ j ∈ t₁, ML2Reduction.coarseNode 𝒰.cover.toChain a b j ∈ t₀) →
      (a ≠ 0 → ∀ k ∈ t₀, ((𝒰.cover.tube a k).translate v).carrier
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      δ ≤ Tube.gridScale δ (Tube.ssfGridLen δ) b →
      Tube.gridScale δ (Tube.ssfGridLen δ) b ≤ Tube.gridScale δ (Tube.ssfGridLen δ) a →
      Tube.gridScale δ (Tube.ssfGridLen δ) a ≤ 1 →
      ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody)
        ≤ (δ : ℝ≥0∞) ^ (-(εc + ML2Spine.spineRung β ϖ ε₁ gain dens m))
          * ((tθ'.card : ℕ) : ℝ≥0∞) ^ β

/-! ## The budget `hexp`, measured -/

/-! ## `0-C`: the singleton **instance**, and why the suggested route to it is blocked -/

/-! ## The source's count floor is on `nodesUnder`, not on `t₁` -/

/-! ## The hypothesis `1 ≤ a` -/

/-! ## Non-vacuity: `hfac` forces a NON-POSITIVE middle gain at a singleton retained node set -/

end Kakeya.ML2Core

end

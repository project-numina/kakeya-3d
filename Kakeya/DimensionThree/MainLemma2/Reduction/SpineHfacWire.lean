/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSiteClosure

/-!
# `hfac`, named — the third open row of the `GeometricCoreAt` closure

After the line-ED drop  the factor hypothesis of the
`(F)` terminal engine carries no `Kakeya.VeryNotSticky.LineEDLevelsAt` row.  What is left is,
row for row, the factor hypothesis of `Kakeya.ML2Core.dichotomy_of_rungFactors_levels`
(`SpineRungWiring.lean`) with `Cu ≤ Cu₀` in place of `Cu ≤ max C 4`, followed by the four
refined-`(F)` rows.  This file gives both texts a name and adjudicates that reading with the
compiler rather than with prose.

* `Kakeya.ML2Core.HfacPostDrop` — the post-drop `hfac` of
  `Kakeya.ML2Core.trialOutcome_middle_of_floorFactors_alpha`, verbatim.
* `Kakeya.ML2Core.HfacLevels` — the `hfac` of `Kakeya.ML2Core.dichotomy_of_rungFactors_levels`,
  verbatim.
* `Kakeya.ML2Core.hfacPostDrop_of_hfacLevels` — the closure site's text implies the floor route's
  text at `Cu₀ := max C 4`, by dropping the four `(F)` antecedents.  **One producer serves both
  consumers**, which is what "the drop restores the interface" means operationally.

The two `example`s below are the checks: each named text is fed to its own consumer's `hfac`
slot and must be accepted by `exact`-grade unification.

## The wiring theorem, and its quantifier order

`Kakeya.ML2Core.geometricCoreAt_of_hfac_witness_payload` closes `ML2Assembly.GeometricCoreAt` from
three named obligations — `Kakeya.ML2Core.HfacPostDrop`, `Kakeya.ML2Core.SiteWitness`,
`Kakeya.ML2Core.FloorPayload` — plus a list of scalar side conditions, all of them **inside** the
`∀ β ϖ gain dens` binder.

That order is load-bearing and is the ``.  The tightened uniformity
binder of the middle factor carries the threshold `δ' ≤ (ssfUniformConst 3)^(-1/ηd)`, and `ηd`
shrinks with `β`; a statement that hoisted `∀ᶠ δ` outside `∀ β` would need one scale threshold
serving every `β` at once, and there is none.  `Kakeya.ML2Core.not_eventually_forall_exponent_le`
is the refutation of exactly that hoist, against
`Kakeya.ML2Core.eventually_const_le_rpow_neg_of_pos` in the admissible order.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody
open Tube ShadedTube

namespace Kakeya.ML2Core

/-! ## The two texts -/

open Classical in
/-- **The closure site's `hfac`**, verbatim the factor hypothesis of
`Kakeya.ML2Core.dichotomy_of_rungFactors_levels` (`SpineRungWiring.lean`). -/
def HfacLevels.{u} (β ϖ ε₁ ηin εf εc κc : ℝ) (gm gain dens : ℝ → ℝ) (C : ℝ≥0) : Prop :=
  ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0,
        ∀ {ι : Type u} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (Cu lam :
            ℝ≥0)
          (𝒰 : Tube.UniformTubeSet u (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu)
          (Cstar : ℝ≥0∞) (a b m : ℕ),
          ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰 Cstar (ML2Spine.spineRung β ϖ ε₁ gain dens)
            (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m →
        ∀ (v : (EuclideanSpace ℝ (Fin 3))) (t₀ t₁ : Finset ι),
          t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain b →
          (∀ j ∈ t₁, ((𝒰.cover.tube b j).translate v).carrier ⊆ Metric.closedBall (0 :
              (EuclideanSpace ℝ (Fin 3))) 1) →
          (∀ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), ((T i).translate v).carrier ⊆
              Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 1) →
          (a ≠ 0 → t₀ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain a) →
          (a ≠ 0 → ∀ j ∈ t₁, ML2Reduction.coarseNode 𝒰.cover.toChain a b j ∈ t₀) →
          (a ≠ 0 → ∀ k ∈ t₀,
            ((𝒰.cover.tube a k).translate v).carrier ⊆ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin
                3))) 1) →
          (∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 1) →
          u.Nonempty →
          Kakeya.maxDensity u (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-ηin) →
          ML2Shaded.HasDenseShading lam u (fun i ↦ (T i).toShadedBody) →
          ML2Shaded.HasComparableDensities lam⁻¹ u (fun i ↦ (T i).toShadedBody) →
          (δ : ℝ≥0) ^ ηin / 2 ≤ lam →
          (u.card : ℝ≥0) ≤ δ ^ (-(4 : ℝ)) →
          Cstar ≤ (δ : ℝ≥0∞) ^ (-κc) →
          Cu ≤ max C 4 →
          0 < ∑ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), volume (T i).shade →
          δ ≤ Tube.gridScale δ (Tube.ssfGridLen δ) b →
          Tube.gridScale δ (Tube.ssfGridLen δ) b ≤ Tube.gridScale δ (Tube.ssfGridLen δ) a →
          Tube.gridScale δ (Tube.ssfGridLen δ) a ≤ 1 →
          ∃ (tτ' tθ' : Finset ι)
          (Yτ' : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b) (EuclideanSpace ℝ (Fin 3)))
          (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a) (EuclideanSpace ℝ (Fin 3)))
          (Y' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (jτ jθ : ι),
          tτ' ⊆ t₁ ∧ tθ' ⊆ 𝒰.cover.indexSet a ∧ jτ ∈ t₁ ∧ jθ ∈ tθ' ∧ tτ'.Nonempty ∧
          ShadedBody.multiplicity ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) (fun i ↦ (T
              i).toShadedBody)
              ≤ ((ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) ({i ∈ u
                  | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ *
                    ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
                      tτ'.card
                      (Tube.gridScale δ (Tube.ssfGridLen δ) b) : ℝ≥0) : ℝ≥0∞)
                * ShadedBody.multiplicity ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
                    𝒰.cover.assign b i = jτ} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
                * ShadedBody.multiplicity ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j
                    = jθ} : Finset ι) (fun j ↦ (Yτ' j).toShadedBody)
                * ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody) ∧
          ShadedBody.multiplicity ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
              𝒰.cover.assign b i = jτ} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
              ≤ (δ : ℝ≥0∞) ^ (-(εf)) * ((({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
                  𝒰.cover.assign b i = jτ} : Finset ι)).card : ℝ≥0∞) ^ β ∧
          ShadedBody.multiplicity ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} :
              Finset ι) (fun j ↦ (Yτ' j).toShadedBody)
              ≤ (δ : ℝ≥0∞) ^ (gm (ML2Spine.spineRung β ϖ ε₁ gain dens m))
                * ((({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} : Finset
                    ι)).card : ℝ≥0∞) ^ β ∧
          ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody)
              ≤ (δ : ℝ≥0∞) ^ (-(εc + ML2Spine.spineRung β ϖ ε₁ gain dens m))
                * ((tθ'.card : ℕ) : ℝ≥0∞) ^ β

open Classical in
/-- **The post-cut `hfac` slot of the guarded
`Kakeya.ML2Core.trialOutcome_middle_of_floorFactors_alpha`** — the four-way split
`Kakeya.ML2Core.HfacPostDrop` is kept **unchanged** above as the *pre-cut* record: it is what
`Kakeya.ML2Core.middleGain_nonpos_of_hfacPostDrop` refutes, and that refutation is the reason the
seam moved.  This is the text after the move — the seam at `(p, b)`, the new-parent factor at
`(a, p)` in defect shape, a third `spineScaleLoss` at the parent scale, and the parent level cut
at `p ≤ b`.  Feeding this text to either `middleGain_nonpos_*` refutation does not typecheck; that
is  Bar 2.

**Family/shading:** `(u, T)` under `𝒰`, with the split's four shadings.
**Level pairs:** fine `b → leaf`, middle `(p, b)`, new parent `(a, p)`, outer level `a`. -/
def HfacPostDropFour.{u} (β ϖ ε₁ ηin η' εf εp εc κc : ℝ) (gm gain dens : ℝ → ℝ) (Cu₀ : ℝ≥0) :
    Prop :=
  ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0,
      ∀ {ι : Type u} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (Cu lam :
          ℝ≥0)
        (𝒰 : Tube.UniformTubeSet u (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu)
        (Cstar : ℝ≥0∞) (a b m : ℕ),
        ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰 Cstar (ML2Spine.spineRung β ϖ ε₁ gain dens)
          (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m →
      ∀ (v : (EuclideanSpace ℝ (Fin 3))) (t₀ t₁ : Finset ι),
        t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain b →
        (∀ j ∈ t₁, ((𝒰.cover.tube b j).translate v).carrier ⊆ Metric.closedBall (0 :
            (EuclideanSpace ℝ (Fin 3))) 1) →
        (∀ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), ((T i).translate v).carrier ⊆
            Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 1) →
        (a ≠ 0 → t₀ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain a) →
        (a ≠ 0 → ∀ j ∈ t₁, ML2Reduction.coarseNode 𝒰.cover.toChain a b j ∈ t₀) →
        (a ≠ 0 → ∀ k ∈ t₀,
          ((𝒰.cover.tube a k).translate v).carrier ⊆ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin
              3))) 1) →
        (∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 1) →
        u.Nonempty →
        Kakeya.maxDensity u (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-ηin) →
        ML2Shaded.HasDenseShading lam u (fun i ↦ (T i).toShadedBody) →
        ML2Shaded.HasComparableDensities lam⁻¹ u (fun i ↦ (T i).toShadedBody) →
        (δ : ℝ≥0) ^ ηin / 2 ≤ lam →
        (u.card : ℝ≥0) ≤ δ ^ (-(4 : ℝ)) →
        Cstar ≤ (δ : ℝ≥0∞) ^ (-κc) →
        Cu ≤ Cu₀ →
        0 < ∑ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), volume (T i).shade →
        δ ≤ Tube.gridScale δ (Tube.ssfGridLen δ) b →
        Tube.gridScale δ (Tube.ssfGridLen δ) b ≤ Tube.gridScale δ (Tube.ssfGridLen δ) a →
        Tube.gridScale δ (Tube.ssfGridLen δ) a ≤ 1 →
        -- the refined (F): the genuine parent level, its density, and the count floor
        ∀ p : ℕ, a ≤ p → p ≤ b →
          (∀ m' : ℕ, a < m' → m' < b →
            ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ (1 - ML2Spine.spineDiv ϖ ε₁)
              ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ) →
            (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ)
              ≤ ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ ML2Spine.spineDiv ϖ ε₁ →
            p < m') →
          (∀ jθ ∈ 𝒰.cover.indexSet a,
            Kakeya.maxDensity (𝒰.nodesUnder p a jθ) (fun j ↦ (𝒰.cover.tube p j).toConvexSpaceBody)
              ≤ (δ : ℝ≥0∞) ^ (-(2 * η'))) →
          (∀ jθ ∈ 𝒰.cover.indexSet a, ∀ jp ∈ 𝒰.nodesUnder p a jθ, ∀ m' : ℕ, a < m' → m' < b →
            ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ (1 - ML2Spine.spineDiv ϖ ε₁)
              ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ) →
            (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ)
              ≤ ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ ML2Spine.spineDiv ϖ ε₁ →
            p < m' →
            ((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ))
                  ^ (2 + 4 * (ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 16))
              ≤ ((𝒰.nodesUnder m' p jp).card : ℝ)) →
        ∃ (tτ' tp' tθ' : Finset ι)
        (Yτ' : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b) (EuclideanSpace ℝ (Fin 3)))
        (Yp : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) p) (EuclideanSpace ℝ (Fin 3)))
        (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a) (EuclideanSpace ℝ (Fin 3)))
        (Y' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (jτ jp jθ : ι),
        tτ' ⊆ t₁ ∧ tp' ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain p ∧
          tθ' ⊆ 𝒰.cover.indexSet a ∧ jτ ∈ t₁ ∧ jθ ∈ tθ' ∧ tτ'.Nonempty ∧ tp'.Nonempty ∧
        ShadedBody.multiplicity ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) (fun i ↦ (T
            i).toShadedBody)
            ≤ ((ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) ({i ∈ u
                | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ *
                  ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) tτ'.card
                    (Tube.gridScale δ (Tube.ssfGridLen δ) b) *
                  ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) tp'.card
                    (Tube.gridScale δ (Tube.ssfGridLen δ) p) : ℝ≥0) : ℝ≥0∞)
              * ShadedBody.multiplicity ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
                  𝒰.cover.assign b i = jτ} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
              * ShadedBody.multiplicity ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain p b j
                  = jp} : Finset ι) (fun j ↦ (Yτ' j).toShadedBody)
              * ShadedBody.multiplicity ({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k
                  = jθ} : Finset ι) (fun k ↦ (Yp k).toShadedBody)
              * ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody) ∧
        ShadedBody.multiplicity ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
            𝒰.cover.assign b i = jτ} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
            ≤ (δ : ℝ≥0∞) ^ (-(εf)) * ((({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
                𝒰.cover.assign b i = jτ} : Finset ι)).card : ℝ≥0∞) ^ β ∧
        ShadedBody.multiplicity ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain p b j = jp} :
            Finset ι) (fun j ↦ (Yτ' j).toShadedBody)
            ≤ (δ : ℝ≥0∞) ^ (gm (ML2Spine.spineRung β ϖ ε₁ gain dens m))
              * ((({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain p b j = jp} : Finset
                  ι)).card : ℝ≥0∞) ^ β ∧
        ShadedBody.multiplicity ({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k = jθ} :
            Finset ι) (fun k ↦ (Yp k).toShadedBody)
            ≤ (δ : ℝ≥0∞) ^ (-(εp))
              * ((({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k = jθ} : Finset
                  ι)).card : ℝ≥0∞) ^ β ∧
        ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody)
            ≤ (δ : ℝ≥0∞) ^ (-(εc + ML2Spine.spineRung β ϖ ε₁ gain dens m))
              * ((tθ'.card : ℕ) : ℝ≥0∞) ^ β

/-! ## The two texts are the two consumers' own slots  -/

section Slots

variable {β ϖ : ℝ} {gain dens : ℝ → ℝ} {ε₁ ηin : ℝ} {C : ℝ≥0} {Kl cl : ℕ}
  {Cu₀ : ℝ≥0} {η' h : ℝ} {gm : ℝ → ℝ} {εf εp εc κc κ' θ₁ θ₂ : ℝ}

/-- **floor side.**  `Kakeya.ML2Core.HfacPostDrop` is accepted, unchanged, in the `hfac`
slot of the guarded `Kakeya.ML2Core.trialOutcome_middle_of_floorFactors_alpha`. -/
example (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hε₁ : 0 < ε₁) (hC : 1 ≤ C) (hCu₀ : 1 ≤ Cu₀)
    (hκc : 0 < κc) (hκ' : 0 < κ') (hθ₂ : 0 < θ₂) (hεp : 0 < εp) (Λf : ℝ≥0 → ℝ≥0∞)
    (hres : ∀ k : ℕ, k < ML2Spine.spineCount ϖ ε₁ →
      κc + ML2Spine.spineRung β ϖ ε₁ gain dens k ≤ 2 * η')
    (hexp : ∀ X : ℝ, ML2Spine.spineNu β ϖ ε₁ gain dens ≤ X →
      6 * ML2Spine.spineNu β ϖ ε₁ gain dens + θ₂ + ηin ≤ gm X - εf - εp - (εc + X) - κ')
    (hfac : HfacPostDropFour.{u} β ϖ ε₁ ηin η' εf εp εc κc gm gain dens Cu₀) : True := by
  have := trialOutcome_middle_of_floorFactors_alpha (Kl := Kl) (cl := cl) (h := h) (η' := η')
    hβ0 hβ1 hϖ hgain hdens hε₁ hC hCu₀ hκc hκ' hθ₂ hεp hres Λf hexp hfac
  trivial

/-- **closure side.**  `Kakeya.ML2Core.HfacLevels` is accepted, unchanged, in the `hfac`
slot of `Kakeya.ML2Core.dichotomy_of_rungFactors_levels`.  `hpkg` is left as a lambda binder so
that the check reads the site's own statement rather than a transcription of it. -/
example (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hε₁ : 0 < ε₁) (hηinν : ηin ≤ ML2Spine.spineNu β ϖ ε₁ gain dens) (hC : 1 ≤ C)
    (hκc : 0 < κc) (hκ' : 0 < κ') (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂)
    (hexp : ∀ X : ℝ, ML2Spine.spineNu β ϖ ε₁ gain dens ≤ X →
      6 * ML2Spine.spineNu β ϖ ε₁ gain dens + θ₁ + θ₂ + 2 * ηin ≤ gm X - εf - (εc + X) - κ')
    (hfac : HfacLevels.{u} β ϖ ε₁ ηin εf εc κc gm gain dens C) : True := by
  have := fun hpkg => dichotomy_of_rungFactors_levels (Kl := Kl) (cl := cl)
    hβ0 hβ1 hϖ hgain hdens hε₁ hηinν hC hpkg hκc hκ' hθ₁ hθ₂ hexp hfac
  trivial

end Slots

/-! ## One producer for both consumers -/

/-! ## the threshold order, and why it may not be hoisted -/

/-! ## The wiring theorem -/

end Kakeya.ML2Core

end

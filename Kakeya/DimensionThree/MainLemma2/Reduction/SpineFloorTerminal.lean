/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineRungWiring
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineTrialOutcome
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeM1
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFourFactorLedger
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineParentLevelBound
public import Kakeya.DimensionThree.MainLemma2.AScaleResidues
public import Kakeya.DimensionThree.MainLemma2.LineEssDistinct

/-!
# The (F) terminal route into `TrialOutcomeAt`

`Kakeya.ML2Core.trialOutcome_middle_of_floorFactors` is the count-floor-and-VNS terminal factor
of GWZ ("the remaining output is alternative (F) … keep its shaded pair
and its genuine parent scale `p`") wired into the descent's trial interface
`Kakeya.ML2Core.TrialOutcomeAt`, on the **given** hierarchy `𝒰` of the trial
family `S` (condition C-D1: no re-uniformising, `u = S`).

Inputs, all named:
* the twin window `IsKatzTaoDividingWindowLevels` on `𝒰` (the source's three window inequalities
  plus the level clause and the all-pairs band);
* the (F) floor at a genuine parent `p`, in the existing `hfloor` conclusion shape of
  `geometricCoreAt_of_lineEDLevels` — the output of F4;
* `hfac`, the three factors at the window's rung **receiving** the twin window and the floor:
  byte-for-byte the `hfac` binder of `Kakeya.ML2Core.dichotomy_of_rungFactors_levels` with
  `Cu ≤ Cu₀` in place of `Cu ≤ max C 4` and the four floor binders of
  `geometricCoreAt_of_lineEDLevels`'s `hmidline` inserted before the conclusion — **without** its
  line-ED levels row;
* the block's density data on `S` (`Δ_max ≤ δ^{-η_in}`, dense shading at `lam ≥ δ^{η_in}/2`,
  comparable densities, `#S ≤ δ^{-4}`, `Cu ≤ Cu₀`).

Output: `TrialOutcomeAt`'s **middle** disjunct, `Σ_S |Z| ≤ δ^{4ν} (#S)^β |⋃ Z|`, through the existing
engine `Kakeya.ML2Core.sum_shade_gain_of_window`.  With `u = S` the package's mass ledger is trivial
(`A = lam·c`), so the pushback budget is `g = 4ν + θ₂ + η_in` against the target `4ν` — the `2ν`
package loss and the `totalLoss` term of `dichotomy_of_rungFactors`'s budget are not paid here.
`Λ` (the descent's per-trial loss) and `h` are parameters of the interface only.

Two shapes of the `(F)` hypothesis, and two hierarchy conventions, coexist in this file.  The
**canonical** shape is the one on
`trialOutcome_middle_of_floorFactors` (F7), `trialOutcome_middle_of_floorFactors_alpha` and their
engine `trialOutcome_middle_of_floorFactors_refined` (with `…_refined_bound`): the payload is
`RefinedFloorHypothesis` at loss `Λf δ`, **and the convention is C-D1** — the hierarchy `𝒰` is the
trial's one hierarchy on the ambient `u`, the family under test is `(S, Z)` with `S ⊆ u` bound as
`IsTrialAt` binds it, and the conclusion is read at the ambient `𝒰`; **and the line-ED axis is
empty**: neither `hfac` nor the payload carries E0's line-ED levels
row — `hfac` is `dichotomy_of_rungFactors_levels`'s interface plus the four (F) rows, and
line-essential distinctness is sourced inside the middle factor from its own centred
re-uniformisation (the `…C3_activeRestrict_of_centred` emitter of `CanonicalCentredCover.lean`),
never from the ambient or the refined hierarchy.  Payload, hierarchy convention, line-ED sourcing:
those are the three axes of the canonical shape, and a consumer should target all three.
The **existing** shape — the `∃ p, …` payload on `trialOutcome_middle_of_floorFactors_bound`
and
`trialOutcome_middle_of_floorFactors_gain`, in the pre-C-D1 convention `u = S` — is kept only as the
engine the refined theorems run on the refinement (`_bound`; `_gain` is applied by nothing) and is
not
a route into `TrialOutcomeAt` in its own right.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody
open Tube ShadedTube

namespace Kakeya.ML2Core

universe u

open Classical in
/-- **The (F) terminal engine: the middle bound itself.**  Fullness is not a hypothesis: mass
positivity comes from the dense shading (`hmass0`), and a rate is one lemma away.  The whole content of the (F) route —
the seam, the two-scale loss, the pushback ledger with `u = S`, `A = lam·c`, budget `g = gt + θ₂ +
η_in` — landing `Σ_S |Z| ≤ δ^{gt} (#S)^β |⋃ Z|` on the family it is run on.  Every sibling below is
an instance: `_gain` injects it into `TrialOutcomeAtGain`'s middle slot; the `M1` theorems run it on
the source's simultaneous refinement and transfer it back. -/
theorem trialOutcome_middle_of_floorFactors_bound
    {β ϖ : ℝ} {gain dens : ℝ → ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    {ε₁ : ℝ} (hε₁ : 0 < ε₁)
    {ηin : ℝ}
    {C : ℝ≥0} {Kl cl : ℕ} (hC : 1 ≤ C) {Cu₀ : ℝ≥0} (hCu₀ : 1 ≤ Cu₀) {η' : ℝ}
    {gm : ℝ → ℝ} {εf εp εc κc κ' θ₂ : ℝ} {gt : ℝ}
    (hκc : 0 < κc) (hκ' : 0 < κ') (hθ₂ : 0 < θ₂) (_hεp : 0 < εp)
    -- R0d, route (i) : the residual case `b < p` of the four-way split,
    -- priced.  Named, so a re-routing moves this row and nothing else.
    (hres : ∀ k : ℕ, k < ML2Spine.spineCount ϖ ε₁ →
      κc + ML2Spine.spineRung β ϖ ε₁ gain dens k ≤ 2 * η')
    (hexp : ∀ X : ℝ, ML2Spine.spineNu β ϖ ε₁ gain dens ≤ X →
      gt + θ₂ + ηin ≤ gm X - εf - εp - (εc + X) - κ')
    (hfac : ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0,
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
              * ((tθ'.card : ℕ) : ℝ≥0∞) ^ β) :
    ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0,
      ∀ {ι : Type u} (S : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (Cu lam :
          ℝ≥0)
        (𝒰 : Tube.UniformTubeSet S (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu) (a b m : ℕ),
        ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰
          ((C : ℝ≥0∞) * StickyKakeya.totalLoss C Kl cl δ) (ML2Spine.spineRung β ϖ ε₁ gain dens)
          (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m →
        (∀ i ∈ S, (T i).carrier ⊆ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 1) →
        S.Nonempty →
        Kakeya.maxDensity S (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-ηin) →
        ML2Shaded.HasDenseShading lam S (fun i ↦ (T i).toShadedBody) →
        ML2Shaded.HasComparableDensities lam⁻¹ S (fun i ↦ (T i).toShadedBody) →
        (δ : ℝ≥0) ^ ηin / 2 ≤ lam →
        (S.card : ℝ≥0) ≤ δ ^ (-(4 : ℝ)) →
        Cu ≤ Cu₀ →
        -- alternative (F): the genuine parent, its density, and the count floor (F4's output)
        (∃ p : ℕ, a ≤ p ∧
          (∀ m' : ℕ, a < m' → m' < b →
            ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ (1 - ML2Spine.spineDiv ϖ ε₁)
              ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ) →
            (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ)
              ≤ ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ ML2Spine.spineDiv ϖ ε₁ →
            p < m') ∧
          (∀ jθ ∈ 𝒰.cover.indexSet a,
            Kakeya.maxDensity (𝒰.nodesUnder p a jθ) (fun j ↦ (𝒰.cover.tube p j).toConvexSpaceBody)
              ≤ (δ : ℝ≥0∞) ^ (-(2 * η'))) ∧
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
              ≤ ((𝒰.nodesUnder m' p jp).card : ℝ))) →
        ∑ i ∈ S, volume (T i).shade
          ≤ (δ : ℝ≥0∞) ^ gt * (S.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ S, (T i).shade) := by
  classical
  have hsp := ML2Spine.spineRung_isSpine hβ0 hβ1 hϖ hε₁ hgain hdens
  have hν0 : 0 < ML2Spine.spineNu β ϖ ε₁ gain dens :=
    ML2Spine.spineNu_pos hβ0 hϖ hε₁ hgain hdens
  -- the two seams and the thresholds, all chosen before the scale
  obtain ⟨M₁, hM₁0, hseam₁⟩ := exists_windowSeam.{u} (E := EuclideanSpace ℝ (Fin 3))
  obtain ⟨M₂, hM₂0, hseam₂⟩ := exists_coarseWindowSeam.{u} (E := EuclideanSpace ℝ (Fin 3))
  set Mseam : ℕ := max M₁ M₂ with hMseam
  have hcc0 : 0 < Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) :=
    Tube.le_volume.c_pos _
  obtain ⟨d1, hd10, hd1⟩ :=
    ML2Reduction.exists_threshold_coe_const_le_rpow_neg
      (C := max 1 (2 * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) *
        ((Mseam : ℝ≥0) * Cu₀ * Cu₀) /
        (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))))))
      (le_max_left _ _) (κ := θ₂) hθ₂
  obtain ⟨Cε, hCε⟩ :=
    ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C_leApprox
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) (κ' / 30) (by positivity)
  obtain ⟨d2, hd20, hd2⟩ :=
    ML2Reduction.exists_threshold_const_le_rpow_neg
      (C := max 1 (Cε ^ 3 * Cu₀ ^ 8)) (le_max_left _ _)
      (κ := κ' / 2) (by positivity)
  obtain ⟨dL, hdL0, hdL1, hdL⟩ := exists_threshold_two_mul_ssfGridLen_le_log
  obtain ⟨d3, hd30, hd3⟩ :=
    ML2Reduction.exists_threshold_coe_const_le_rpow_neg (C := C) hC (κ := κc / 2)
      (by positivity)
  obtain ⟨dT', hdT'0, hdT'1, hdT'⟩ :=
    StickyKakeya.exists_threshold_totalLoss_le C hC Kl cl (κc / 2) (by positivity)
  filter_upwards [hfac, Ioc_mem_nhdsGT hd10, Ioc_mem_nhdsGT hd20, Ioc_mem_nhdsGT hdL0,
    Ioc_mem_nhdsGT hd30, Ioc_mem_nhdsGT hdT'0, Ioc_mem_nhdsGT (zero_lt_one' ℝ≥0)]
    with δ hfacδ hm1 hm2 hmL hm3 hmT' hm01
  intro ι S T Cu lam 𝒰 a b m hwinL hball hSne hmaxS hdense hcomp hlamlow hcardS hCu
    hflo
  have hδ0 : 0 < δ := hm01.1
  have hδ1 : δ ≤ 1 := hm01.2
  have hwin := hwinL.toIsKatzTaoDividingWindow
  have hlam0 : 0 < lam := by
    have : (0 : ℝ≥0) < (δ : ℝ≥0) ^ ηin / 2 := by
      have := NNReal.rpow_pos (p := ηin) hδ0
      positivity
    exact lt_of_lt_of_le this hlamlow
  -- the seam
  obtain ⟨v, t₀, t₁, ht₀, ht₁, hballt₀, hballt, hballs, hcn, hcardseam, hδτ, hτθ, hθ1⟩ :
      ∃ (v : EuclideanSpace ℝ (Fin 3)) (t₀ t₁ : Finset ι),
        (a ≠ 0 → t₀ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain a) ∧
        t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain b ∧
        (a ≠ 0 → ∀ k ∈ t₀, ((𝒰.cover.tube a k).translate v).carrier
          ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) ∧
        (∀ j ∈ t₁, ((𝒰.cover.tube b j).translate v).carrier
          ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) ∧
        (∀ i ∈ ({i ∈ S | 𝒰.cover.assign b i ∈ t₁} : Finset ι),
          ((T i).translate v).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) ∧
        (a ≠ 0 → ∀ j ∈ t₁, ML2Reduction.coarseNode 𝒰.cover.toChain a b j ∈ t₀) ∧
        (S.card : ℝ≥0) ≤ (Mseam : ℝ≥0) * Cu * Cu
          * ((({i ∈ S | 𝒰.cover.assign b i ∈ t₁} : Finset ι)).card : ℝ≥0) ∧
        δ ≤ Tube.gridScale δ (Tube.ssfGridLen δ) b ∧
        Tube.gridScale δ (Tube.ssfGridLen δ) b ≤ Tube.gridScale δ (Tube.ssfGridLen δ) a ∧
        Tube.gridScale δ (Tube.ssfGridLen δ) a ≤ 1 := by
    have hMcast : ∀ n : ℕ, n ≤ Mseam → ((n : ℝ≥0) ≤ (Mseam : ℝ≥0)) := by
      intro n hn; exact_mod_cast Nat.cast_le.mpr hn
    rcases eq_or_ne a 0 with ha0 | ha0
    · obtain ⟨v, t₁, ht₁, hballt, hballs, hcardseam, hδτ, hτθ, hθ1⟩ :=
        hseam₁ 𝒰 hδ0 hδ1 (hdL δ hδ0 hmL.2) hwin hball
      refine ⟨v, ∅, t₁, fun h ↦ absurd ha0 h, ht₁, fun h ↦ absurd ha0 h, hballt, hballs,
        fun h ↦ absurd ha0 h, ?_, hδτ, hτθ, hθ1⟩
      refine hcardseam.trans (mul_le_mul' (mul_le_mul' (mul_le_mul'
        (hMcast M₁ (le_max_left _ _)) le_rfl) le_rfl) le_rfl)
    · obtain ⟨v, t₀, t₁, ht₀, ht₁, hballt₀, hballt, hballs, hcn, hcardseam, hδτ, hτθ, hθ1⟩ :=
        hseam₂ 𝒰 hδ0 hδ1 (Nat.one_le_iff_ne_zero.mpr ha0) (hdL δ hδ0 hmL.2) hwin hball
      refine ⟨v, t₀, t₁, fun _ ↦ ht₀, ht₁, fun _ ↦ hballt₀, hballt, hballs, fun _ ↦ hcn,
        ?_, hδτ, hτθ, hθ1⟩
      refine hcardseam.trans (mul_le_mul' (mul_le_mul' (mul_le_mul'
        (hMcast M₂ (le_max_right _ _)) le_rfl) le_rfl) le_rfl)
  -- mass positivity: one dense shade is already positive
  have hcc0E : ((Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0)
      : ℝ≥0∞) ≠ 0 := by
    simpa using (Tube.le_volume.c_pos (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))).ne'
  have hlam0E : ((lam : ℝ≥0) : ℝ≥0∞) ≠ 0 := by simpa using hlam0.ne'
  -- mass positivity from the dense shading: one member, its carrier has positive volume
  have hmass0 : 0 < ∑ i ∈ S, volume (T i).shade := by
    obtain ⟨i₀, hi₀⟩ := hSne
    have hcar : volume ((T i₀).toShadedBody).carrier ≠ 0 :=
      ML2Shaded.volume_carrier_ne_zero hδ0 (T i₀).toTube
    have h1 : 0 < (lam : ℝ≥0∞) * volume ((T i₀).toShadedBody).carrier :=
      ENNReal.mul_pos hlam0E hcar
    have h2 : (lam : ℝ≥0∞) * volume ((T i₀).toShadedBody).carrier ≤ volume (T i₀).shade :=
      hdense i₀ hi₀
    exact lt_of_lt_of_le (h1.trans_le h2)
      (Finset.single_le_sum (f := fun i ↦ volume (T i).shade) (fun i _ => bot_le) hi₀)
  have hmasspos : 0 < ∑ i ∈ ({i ∈ S | 𝒰.cover.assign b i ∈ t₁} : Finset ι),
      volume (T i).shade := by
    have hret := sum_shade_le_of_node_subfamily (E := EuclideanSpace ℝ (Fin 3)) hδ1
      (Finset.filter_subset (fun i ↦ 𝒰.cover.assign b i ∈ t₁) S) hdense hcardseam
    rw [pos_iff_ne_zero]
    intro h
    rw [h, mul_zero] at hret
    have h0 : (lam : ℝ≥0∞)
        * ((Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0) : ℝ≥0∞)
        * (∑ i ∈ S, volume (T i).shade) = 0 := le_antisymm hret (by simp)
    rcases mul_eq_zero.mp h0 with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact hlam0E h2
      · exact hcc0E h2
    · exact hmass0.ne' h1
  -- the two-scale loss, absorbed at `κ'`
  have hσb1 : Tube.gridScale δ (Tube.ssfGridLen δ) b ≤ 1 := le_trans hτθ hθ1
  have hCu₀8one : (1 : ℝ≥0) ≤ Cu₀ ^ 8 := one_le_pow₀ hCu₀
  have hCu8le : Cu ^ 8 ≤ Cu₀ ^ 8 := pow_le_pow_left₀ zero_le hCu 8
  -- Three `spineScaleLoss` factors now, the third at the genuine-parent scale `ρ_p`
  --,
  -- and the cardinality constant is `Cu ^ 8` (four factors), not `Cu ^ 5`.
  have hLfinal : ∀ p : ℕ, p ≤ b → ∀ n₁ n₂ n₃ : ℕ, 0 < n₁ → 0 < n₂ → 0 < n₃ →
      (n₁ : ℝ≥0) ≤ δ ^ (-(4 : ℝ)) → (n₂ : ℝ≥0) ≤ δ ^ (-(4 : ℝ)) →
      (n₃ : ℝ≥0) ≤ δ ^ (-(4 : ℝ)) →
      ((ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) n₁ δ *
          ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) n₂
            (Tube.gridScale δ (Tube.ssfGridLen δ) b) *
          ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) n₃
            (Tube.gridScale δ (Tube.ssfGridLen δ) p) : ℝ≥0) : ℝ≥0∞)
        * ((((Cu : ℝ≥0) ^ 8 : ℝ≥0) : ℝ≥0∞)) ^ β ≤ (δ : ℝ≥0∞) ^ (-κ') := by
    intro p hpb n₁ n₂ n₃ hn1p hn2p hn3p hn1 hn2 hn3
    have hδρp : δ ≤ Tube.gridScale δ (Tube.ssfGridLen δ) p :=
      le_trans hδτ (Tube.gridScale_antitone hδ0 hδ1 _ hpb)
    have hρp1 : Tube.gridScale δ (Tube.ssfGridLen δ) p ≤ 1 := Tube.gridScale_le_one hδ1 _ _
    have hprod := spineScaleLoss_prod3_le hδ0 hδ1 hδτ hσb1 hδρp hρp1 hn1p hn2p hn3p hn1 hn2 hn3
      (ε := κ' / 30) (by positivity) hCε
    have hβpow : ((Cu : ℝ≥0) ^ 8) ^ β ≤ Cu₀ ^ 8 := by
      calc ((Cu : ℝ≥0) ^ 8) ^ β ≤ (Cu₀ ^ 8) ^ β := NNReal.rpow_le_rpow hCu8le hβ0.le
        _ ≤ (Cu₀ ^ 8) ^ (1 : ℝ) := NNReal.rpow_le_rpow_of_exponent_le hCu₀8one hβ1
        _ = Cu₀ ^ 8 := by rw [NNReal.rpow_one]
    rcases eq_or_ne ((Cu : ℝ≥0) ^ 8) 0 with hCu8z | hCu8ne
    · rw [hCu8z]
      have hβne : β ≠ 0 := hβ0.ne'
      simp [ENNReal.zero_rpow_of_pos hβ0]
    rw [← ENNReal.coe_rpow_of_ne_zero hCu8ne, ← ENNReal.coe_mul,
      ← ENNReal.coe_rpow_of_ne_zero hδ0.ne', ENNReal.coe_le_coe]
    calc (ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) n₁ δ *
            ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) n₂
              (Tube.gridScale δ (Tube.ssfGridLen δ) b) *
            ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) n₃
              (Tube.gridScale δ (Tube.ssfGridLen δ) p))
          * (((Cu : ℝ≥0) ^ 8) ^ β)
        ≤ (Cε ^ 3 * δ ^ (-(15 * (κ' / 30)))) * (Cu₀ ^ 8) :=
          mul_le_mul' hprod hβpow
      _ = (Cε ^ 3 * Cu₀ ^ 8) * δ ^ (-(κ' / 2)) := by
          rw [show (15 : ℝ) * (κ' / 30) = κ' / 2 by ring]; ring
      _ ≤ δ ^ (-(κ' / 2)) * δ ^ (-(κ' / 2)) := by
          gcongr
          exact le_trans (le_max_right _ _) (hd2 δ hδ0 hm2.2)
      _ = δ ^ (-κ') := by
          rw [← NNReal.rpow_add hδ0.ne']
          congr 1
          ring
  -- the pushback ledger with `u = S`: `A = lam·c`, budget `g = gt + θ₂ + η_in`
  have hδEne : (δ : ℝ≥0∞) ≠ 0 := by simpa using hδ0.ne'
  have hδEtop : (δ : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := ENNReal.coe_ne_top
  have hlamE : (δ : ℝ≥0∞) ^ ηin ≤ 2 * (lam : ℝ≥0∞) := by
    have hnn : (δ : ℝ≥0) ^ ηin ≤ 2 * lam := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ≥0) < 2)] at hlamlow
      calc (δ : ℝ≥0) ^ ηin ≤ lam * 2 := hlamlow
        _ = 2 * lam := by ring
    calc (δ : ℝ≥0∞) ^ ηin = (((δ : ℝ≥0) ^ ηin : ℝ≥0) : ℝ≥0∞) :=
          (ENNReal.coe_rpow_of_ne_zero hδ0.ne' _).symm
      _ ≤ ((2 * lam : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_le_coe.mpr hnn
      _ = 2 * (lam : ℝ≥0∞) := by push_cast; ring
  have hmassloss : (lam : ℝ≥0∞)
        * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞)
        * (∑ i ∈ S, volume (T i).shade)
      ≤ ((lam : ℝ≥0∞)
        * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞))
        * ∑ i ∈ S, volume (T i).shade := le_rfl
  have habs : ((lam : ℝ≥0∞)
          * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞))
        * ((((Mseam : ℝ≥0) * Cu * Cu : ℝ≥0) : ℝ≥0∞)
          * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞))
        * (δ : ℝ≥0∞) ^ (gt + θ₂ + ηin)
      ≤ ((lam : ℝ≥0∞)
          * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞))
        * ((lam : ℝ≥0∞)
          * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞))
        * (δ : ℝ≥0∞) ^ (gt) := by
    -- the constant `2·C_vol·Mseam·Cu²/c` is absorbed by `δ^{-θ₂}`
    have hKle : ((Mseam : ℝ≥0) * Cu * Cu : ℝ≥0) ≤ (Mseam : ℝ≥0) * Cu₀ * Cu₀ := by
      gcongr
    have hconstNN : (2 : ℝ≥0) * Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
          * ((Mseam : ℝ≥0) * Cu * Cu)
        ≤ (max 1 (2 * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) *
            ((Mseam : ℝ≥0) * Cu₀ * Cu₀) /
            (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))))))
          * Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) := by
      refine le_trans ?_ (mul_le_mul' (le_max_right _ _) le_rfl)
      rw [div_mul_cancel₀ _ hcc0.ne']
      gcongr
    have hconst : (2 : ℝ≥0∞)
          * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞)
          * (((Mseam : ℝ≥0) * Cu * Cu : ℝ≥0) : ℝ≥0∞)
        ≤ (δ : ℝ≥0∞) ^ (-θ₂)
          * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞) := by
      have h1 : ((2 * Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
            * ((Mseam : ℝ≥0) * Cu * Cu) : ℝ≥0) : ℝ≥0∞)
          ≤ (((max 1 (2 * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) *
              ((Mseam : ℝ≥0) * Cu₀ * Cu₀) /
              (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))))))
            * Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
              : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_le_coe.mpr hconstNN
      have h2 := hd1 δ hδ0 hm1.2
      push_cast at h1 ⊢
      exact h1.trans (mul_le_mul' h2 le_rfl)
    -- `2·C_vol·K·δ^{θ₂} ≤ c`, then `δ^{η_in} ≤ 2·lam`
    have e : (δ : ℝ≥0∞) ^ (-θ₂) * (δ : ℝ≥0∞) ^ θ₂ = 1 := by
      rw [← ENNReal.rpow_add _ _ hδEne hδEtop, neg_add_cancel, ENNReal.rpow_zero]
    have h2K : (2 : ℝ≥0∞)
          * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞)
          * (((Mseam : ℝ≥0) * Cu * Cu : ℝ≥0) : ℝ≥0∞) * (δ : ℝ≥0∞) ^ θ₂
        ≤ (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞) := by
      calc (2 : ℝ≥0∞)
            * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞)
            * (((Mseam : ℝ≥0) * Cu * Cu : ℝ≥0) : ℝ≥0∞) * (δ : ℝ≥0∞) ^ θ₂
          ≤ ((δ : ℝ≥0∞) ^ (-θ₂)
              * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞))
              * (δ : ℝ≥0∞) ^ θ₂ := mul_le_mul' hconst le_rfl
        _ = (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞)
              * ((δ : ℝ≥0∞) ^ (-θ₂) * (δ : ℝ≥0∞) ^ θ₂) := by ring
        _ = (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞) := by
              rw [e, mul_one]
    have hstep : (((Mseam : ℝ≥0) * Cu * Cu : ℝ≥0) : ℝ≥0∞)
          * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞)
          * (δ : ℝ≥0∞) ^ θ₂ * (δ : ℝ≥0∞) ^ ηin
        ≤ (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞)
          * (lam : ℝ≥0∞) := by
      calc (((Mseam : ℝ≥0) * Cu * Cu : ℝ≥0) : ℝ≥0∞)
            * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞)
            * (δ : ℝ≥0∞) ^ θ₂ * (δ : ℝ≥0∞) ^ ηin
          ≤ (((Mseam : ℝ≥0) * Cu * Cu : ℝ≥0) : ℝ≥0∞)
            * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞)
            * (δ : ℝ≥0∞) ^ θ₂ * (2 * (lam : ℝ≥0∞)) := mul_le_mul' le_rfl hlamE
        _ = ((2 : ℝ≥0∞)
            * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞)
            * (((Mseam : ℝ≥0) * Cu * Cu : ℝ≥0) : ℝ≥0∞) * (δ : ℝ≥0∞) ^ θ₂)
            * (lam : ℝ≥0∞) := by ring
        _ ≤ (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞)
            * (lam : ℝ≥0∞) := mul_le_mul' h2K le_rfl
    have esplit : (δ : ℝ≥0∞) ^ (gt + θ₂ + ηin)
        = (δ : ℝ≥0∞) ^ (gt) * (δ : ℝ≥0∞) ^ θ₂
          * (δ : ℝ≥0∞) ^ ηin := by
      rw [ENNReal.rpow_add _ _ hδEne hδEtop, ENNReal.rpow_add _ _ hδEne hδEtop]
    calc ((lam : ℝ≥0∞)
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞))
          * ((((Mseam : ℝ≥0) * Cu * Cu : ℝ≥0) : ℝ≥0∞)
            * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞))
          * (δ : ℝ≥0∞) ^ (gt + θ₂ + ηin)
        = (((lam : ℝ≥0∞)
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞))
            * (δ : ℝ≥0∞) ^ (gt))
          * ((((Mseam : ℝ≥0) * Cu * Cu : ℝ≥0) : ℝ≥0∞)
            * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞)
            * (δ : ℝ≥0∞) ^ θ₂ * (δ : ℝ≥0∞) ^ ηin) := by
          rw [esplit]; ring
      _ ≤ (((lam : ℝ≥0∞)
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞))
            * (δ : ℝ≥0∞) ^ (gt))
          * ((Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞)
            * (lam : ℝ≥0∞)) := mul_le_mul' le_rfl hstep
      _ = ((lam : ℝ≥0∞)
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞))
          * ((lam : ℝ≥0∞)
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞))
          * (δ : ℝ≥0∞) ^ (gt) := by ring
  -- the numeric inputs of the factor interface
  have hCstarB : (C : ℝ≥0∞) * StickyKakeya.totalLoss C Kl cl δ
      ≤ (δ : ℝ≥0∞) ^ (-κc) := by
    have hT : StickyKakeya.totalLoss C Kl cl δ ≤ (δ : ℝ≥0∞) ^ (-(κc / 2)) := by
      rw [← ofReal_rpow_coe hδ0]
      exact hdT' hδ0 hmT'.2
    calc (C : ℝ≥0∞) * StickyKakeya.totalLoss C Kl cl δ
        ≤ (δ : ℝ≥0∞) ^ (-(κc / 2)) * (δ : ℝ≥0∞) ^ (-(κc / 2)) :=
          mul_le_mul' (hd3 δ hδ0 hm3.2) hT
      _ = (δ : ℝ≥0∞) ^ (-κc) := by
          rw [← ENNReal.rpow_add _ _ hδEne hδEtop]
          congr 1
          ring
  obtain ⟨p₀, hap₀, hpm₀, hpar₀, hflo₀⟩ := hflo
  have hX : ML2Spine.spineNu β ϖ ε₁ gain dens ≤ ML2Spine.spineRung β ϖ ε₁ gain dens m :=
    hsp.rung_mono (Nat.zero_le m)
  -- The four-way split reads the payload at a parent level **at or below** the fine level: the
  -- cardinality telescoping `n_a n_p n_b n_i ≤ Cu ^ 8 |s|` needs the chain `a ≤ p ≤ b`.  R0d,
  -- route (i).
  have main : ∀ p : ℕ, a ≤ p → p ≤ b →
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
      ∑ i ∈ S, volume (T i).shade
        ≤ (δ : ℝ≥0∞) ^ gt * (S.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ S, (T i).shade) := by
    intro p hap hpb hpm hpar hflo'
    have hfacw := hfacδ S T Cu lam 𝒰 ((C : ℝ≥0∞) * StickyKakeya.totalLoss C Kl cl δ) a b m
      hwinL v t₀ t₁ ht₁ hballt hballs ht₀ hcn hballt₀ hball hSne hmaxS hdense hcomp hlamlow
      hcardS hCstarB hCu hmasspos hδτ hτθ hθ1 p hap hpb hpm hpar hflo'
    exact sum_shade_gain_of_window_four (β := β) hβ0.le hδ0 hδ1 hlam0 (Finset.Subset.refl S)
      hdense 𝒰 hwin hap hpb ht₁ hcardseam hmasspos
      (εf := εf) (gm := gm (ML2Spine.spineRung β ϖ ε₁ gain dens m)) (εp := εp)
      (εc := εc + ML2Spine.spineRung β ϖ ε₁ gain dens m) (κ := κ')
      (g := gt + θ₂ + ηin)
      (gt := gt)
      hcardS hfacw (hLfinal p hpb) (hexp _ hX) hmassloss habs
  rcases Nat.le_total p₀ b with hpb | hgt
  · exact main p₀ hap₀ hpb hpm₀ hpar₀ hflo₀
  · -- the residual case `b < p₀`: the payload is re-read at `p := b`, where its inset row
    -- transfers, its count-floor row is vacuous, and its density row is the window's own
    -- `middle_maxDensity_le` priced by `hres`.  Nothing else in the ledger changes.
    refine main b hwin.coarse_lt_fine.le le_rfl ?_ ?_ ?_
    · intro m' h1 h2 r1 r2
      exact lt_of_le_of_lt hgt (hpm₀ m' h1 h2 r1 r2)
    · exact ML2Core.parentDensity_at_fine_of_window 𝒰 hwin hδ0 hCstarB (hsp.rung_pos m).le
        (by exact_mod_cast hθ1) (by exact_mod_cast hδτ) (by exact_mod_cast hδ1)
        (hres m hwin.step_lt)
    · intro jθ _ jp _ m' _ h2 _ _ h5
      exact absurd h5 (Nat.lt_asymm h2)

/-- **The window twin crosses `Tube.UniformTubeSet.retube`.**  Every field of
`ML2Reduction.IsKatzTaoDividingWindowLevels` is stated through `cover.indexSet`, `cover.tube`,
`cover.assign` and `nodesUnder`, all of which `retube` leaves definitionally unchanged, so the twin read on the transported hierarchy is the twin on the
original —
field by field, by `rfl`.  `FloorHypothesisAt` is a `def` over the same projections and needs no
lemma. -/
theorem isKatzTaoDividingWindowLevels_of_retube {ι : Type*} {δ Cu : ℝ≥0} {s : Finset ι}
    {T T' : ι → Tube δ (EuclideanSpace ℝ (Fin 3))} (hT : T' = T)
    (𝒱 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) {Cstar : ℝ≥0∞} {η : ℕ → ℝ} {εd : ℝ}
    {N a b m : ℕ}
    (hw : ML2Reduction.IsKatzTaoDividingWindowLevels (𝒱.retube hT) Cstar η εd N a b m) :
    ML2Reduction.IsKatzTaoDividingWindowLevels 𝒱 Cstar η εd N a b m where
  step_lt := hw.step_lt
  coarse_lt_fine := hw.coarse_lt_fine
  fine_le_gridLen := hw.fine_le_gridLen
  scale_sep := hw.scale_sep
  coarse_maxDensity_le := hw.coarse_maxDensity_le
  middle_maxDensity_le := hw.middle_maxDensity_le
  le_window_maxDensity := hw.le_window_maxDensity
  le_level_maxDensity := hw.le_level_maxDensity
  level_density_band := hw.level_density_band

open Classical in
/-- **`M1`'s engine on the refinement, at the ambient hierarchy: the
middle bound itself.**  The hierarchy `𝒰` is the trial's one hierarchy on the ambient `u`; the
family
under test is `(S, Z)` with `S ⊆ u`, `(Z i).toTube = (T i).toTube` and `IsClassHomogeneousOn 𝒰 S`
(`IsTrialAt`'s rows, in `IsTrialAt`'s order).  The `(F)` payload is `RefinedFloorHypothesis` on the
`S`-restricted, `Z`-retubed hierarchy `(𝒰.restrictOccupied hS hh).retube (funext ht)` — a refinement
`(S', W)` of the family `(S, Z)` itself, which is what a bound on `Σ_S |Z|` needs (a refinement of
`(u, T)` cannot give it: `#S ≤ #u` and `⋃_S Z ⊆ ⋃_u T` point the wrong way).  The engine
`trialOutcome_middle_of_floorFactors_bound` runs on `(S', Z, restrictOccupied)` — dense shading and
comparable densities descend by `.subset`; no fullness row anywhere — and the bound transfers to `(S, Z)` through the
retention, `W ⊆ Z`, and the
absorption `hΛf : Λf δ · δ^{gt} ≤ δ^{g}`.  The card row is `IsTrialAt`'s `(u.card : ℝ)`, bridged to
the
engine's `NNReal` row on `S'` inside. -/
theorem trialOutcome_middle_of_floorFactors_refined_bound
    {β ϖ : ℝ} {gain dens : ℝ → ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    {ε₁ : ℝ} (hε₁ : 0 < ε₁)
    {ηin : ℝ}
    {C : ℝ≥0} {Kl cl : ℕ} (hC : 1 ≤ C) {Cu₀ : ℝ≥0} (hCu₀ : 1 ≤ Cu₀) {η' : ℝ}
    {gm : ℝ → ℝ} {εf εp εc κc κ' θ₂ : ℝ} {gt g : ℝ}
    (hκc : 0 < κc) (hκ' : 0 < κ') (hθ₂ : 0 < θ₂) (hεp : 0 < εp)
    -- R0d, route (i) : the residual case `b < p` of the four-way split,
    -- priced.  Named, so a re-routing moves this row and nothing else.
    (hres : ∀ k : ℕ, k < ML2Spine.spineCount ϖ ε₁ →
      κc + ML2Spine.spineRung β ϖ ε₁ gain dens k ≤ 2 * η') (Λf : ℝ≥0 → ℝ≥0∞)
    (hexp : ∀ X : ℝ, ML2Spine.spineNu β ϖ ε₁ gain dens ≤ X →
      gt + θ₂ + ηin ≤ gm X - εf - εp - (εc + X) - κ')
    (hfac : ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0,
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
              * ((tθ'.card : ℕ) : ℝ≥0∞) ^ β) :
    ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0,
      ∀ {ι : Type u} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (Cu : ℝ≥0) (𝒰 : Tube.UniformTubeSet u (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu)
        (a b m : ℕ) (S : Finset ι) (hS : S ⊆ u) (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (lam : ℝ≥0),
        S.Nonempty →
        ∀ (ht : ∀ i, (Z i).toTube = (T i).toTube),
        (∀ i, (Z i).shade ⊆ (T i).shade) →
        ∀ (hh : IsClassHomogeneousOn 𝒰 S),
        (∀ i ∈ S, (Z i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
        Kakeya.maxDensity S (fun i ↦ (Z i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-ηin) →
        ML2Shaded.HasDenseShading lam S (fun i ↦ (Z i).toShadedBody) →
        ML2Shaded.HasComparableDensities lam⁻¹ S (fun i ↦ (Z i).toShadedBody) →
        (δ : ℝ≥0) ^ ηin / 2 ≤ lam →
        (u.card : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ)) →
        Cu ≤ Cu₀ →
        Λf δ * (δ : ℝ≥0∞) ^ gt ≤ (δ : ℝ≥0∞) ^ g →
        -- alternative (F) on the source's simultaneous refinement of the family `(S, Z)`, in the
        -- inherited tower
        RefinedFloorHypothesis (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ gain dens
          η' (Λf δ) ((𝒰.restrictOccupied hS hh).retube (funext ht)) a b m →
        ∑ i ∈ S, volume (Z i).shade
          ≤ (δ : ℝ≥0∞) ^ g * (S.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ S, (Z i).shade) := by
  classical
  filter_upwards [trialOutcome_middle_of_floorFactors_bound hβ0 hβ1 hϖ hgain hdens hε₁ hC hCu₀ hκc
    hκ' hθ₂ hεp hres (Kl := Kl) (cl := cl) (gt := gt) hexp hfac] with δ hδ
  intro ι u T Cu 𝒰 a b m S hS Z lam hSne ht hs hh hball hmaxS hdense hcomp hlamlow hcardu hCu hΛf
    href
  set 𝒰₁ : Tube.UniformTubeSet S (fun i ↦ (Z i).toTube) (Tube.ssfGridLen δ) Cu :=
    (𝒰.restrictOccupied hS hh).retube (funext ht) with h𝒰₁
  have hcardS : (S.card : ℝ≥0) ≤ δ ^ (-(4 : ℝ)) := by
    have h1 : (S.card : ℝ) ≤ (u.card : ℝ) := by exact_mod_cast Finset.card_le_card hS
    have h2 : ((S.card : ℝ≥0) : ℝ) ≤ ((δ ^ (-(4 : ℝ)) : ℝ≥0) : ℝ) := by
      rw [NNReal.coe_rpow, NNReal.coe_natCast]; exact h1.trans hcardu
    exact_mod_cast h2
  obtain ⟨S', W, hS', hhom, hW, hrefine, hwin', hflo'⟩ := href
  -- the refinement's hierarchy, read at the ambient tube family
  have hwin'' : ML2Reduction.IsKatzTaoDividingWindowLevels (𝒰₁.restrictOccupied hS' hhom)
      ((C : ℝ≥0∞) * StickyKakeya.totalLoss C Kl cl δ) (ML2Spine.spineRung β ϖ ε₁ gain dens)
      (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m :=
    isKatzTaoDividingWindowLevels_of_retube hW _ hwin'
  have hflo'' : FloorHypothesisAt β ϖ ε₁ gain dens η' (𝒰₁.restrictOccupied hS' hhom) a b m := hflo'
  -- the ambient shading restricted to the refinement
  have hball' : ∀ i ∈ S', (Z i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    fun i hi => hball i (hS' hi)
  have hSne' : S'.Nonempty := hrefine.nonempty
  have htube : ∀ i, (W i).toTube = (Z i).toTube := hrefine.2.2.1
  have hmaxS' : Kakeya.maxDensity S' (fun i ↦ (Z i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-ηin) :=
    (Kakeya.maxDensity_mono _ hS').trans hmaxS
  have hdense' := hdense.subset hS'
  have hcomp' := hcomp.subset hS'
  have hcardS' : (S'.card : ℝ≥0) ≤ δ ^ (-(4 : ℝ)) :=
    le_trans (by exact_mod_cast Finset.card_le_card hS') hcardS
  -- the engine on the refinement
  have hbound := hδ S' Z Cu lam (𝒰₁.restrictOccupied hS' hhom) a b m hwin'' hball' hSne'
    hmaxS' hdense' hcomp' hlamlow hcardS' hCu hflo''
  -- the transfer to `(S, T)`: retention, then the shade inclusion, then the absorption
  have hcard : ((S'.card : ℝ≥0∞)) ^ β ≤ ((S.card : ℝ≥0∞)) ^ β :=
    ENNReal.rpow_le_rpow (by exact_mod_cast Finset.card_le_card hS') hβ0.le
  have hvol : volume (⋃ i ∈ S', (Z i).shade) ≤ volume (⋃ i ∈ S, (Z i).shade) :=
    measure_mono (Set.iUnion₂_subset fun i hi =>
      Set.subset_biUnion_of_mem (u := fun i => (Z i).shade) (hS' hi))
  have hsum : ∑ i ∈ S', volume (W i).shade ≤ ∑ i ∈ S', volume (Z i).shade :=
    Finset.sum_le_sum (fun i _ => measure_mono (hrefine.shade_subset i))
  have hmid : ∑ i ∈ S, volume (Z i).shade
      ≤ (δ : ℝ≥0∞) ^ g * (S.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ S, (Z i).shade) :=
    calc ∑ i ∈ S, volume (Z i).shade
        ≤ Λf δ * ∑ i ∈ S', volume (W i).shade := hrefine.retention
      _ ≤ Λf δ * ∑ i ∈ S', volume (Z i).shade := mul_le_mul' le_rfl hsum
      _ ≤ Λf δ * ((δ : ℝ≥0∞) ^ gt * (S'.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ S', (Z i).shade)) :=
          mul_le_mul' le_rfl hbound
      _ ≤ Λf δ * ((δ : ℝ≥0∞) ^ gt * (S.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ S, (Z i).shade)) :=
          mul_le_mul' le_rfl (mul_le_mul' (mul_le_mul' le_rfl hcard) hvol)
      _ = (Λf δ * (δ : ℝ≥0∞) ^ gt) * ((S.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ S, (Z i).shade)) := by
          ring
      _ ≤ (δ : ℝ≥0∞) ^ g * ((S.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ S, (Z i).shade)) :=
          mul_le_mul' hΛf le_rfl
      _ = (δ : ℝ≥0∞) ^ g * (S.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ S, (Z i).shade) := by ring
  exact hmid

open Classical in
/-- **`M1`, by name, at the ambient hierarchy** (C-D1): the middle bound of
`trialOutcome_middle_of_floorFactors_refined_bound` injected into `TrialOutcomeAtGain h ε₀ g β 𝒰 Λ
lam S Z`
for the **ambient** `𝒰` on `u` — the middle disjunct mentions neither `𝒰` nor the potential, so
nothing is transported.  General in the engine's gain `gt` (on the refinement) and the target `g`
(on `(S, Z)`); F7 is `(gt, g) := (4ν + α, 4ν)`, `_alpha` is `(4ν + 2α, 4ν + α)`. -/
theorem trialOutcome_middle_of_floorFactors_refined
    {β ϖ : ℝ} {gain dens : ℝ → ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    {ε₁ : ℝ} (hε₁ : 0 < ε₁)
    {ηin : ℝ}
    {C : ℝ≥0} {Kl cl : ℕ} (hC : 1 ≤ C) {Cu₀ : ℝ≥0} (hCu₀ : 1 ≤ Cu₀) {η' h : ℝ}
    {gm : ℝ → ℝ} {εf εp εc κc κ' θ₂ : ℝ} {gt g : ℝ}
    (hκc : 0 < κc) (hκ' : 0 < κ') (hθ₂ : 0 < θ₂) (hεp : 0 < εp)
    -- R0d, route (i) : the residual case `b < p` of the four-way split,
    -- priced.  Named, so a re-routing moves this row and nothing else.
    (hres : ∀ k : ℕ, k < ML2Spine.spineCount ϖ ε₁ →
      κc + ML2Spine.spineRung β ϖ ε₁ gain dens k ≤ 2 * η') (Λf : ℝ≥0 → ℝ≥0∞)
    (hexp : ∀ X : ℝ, ML2Spine.spineNu β ϖ ε₁ gain dens ≤ X →
      gt + θ₂ + ηin ≤ gm X - εf - εp - (εc + X) - κ')
    (hfac : ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0,
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
              * ((tθ'.card : ℕ) : ℝ≥0∞) ^ β) :
    ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0,
      ∀ {ι : Type u} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (Cu : ℝ≥0) (𝒰 : Tube.UniformTubeSet u (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu)
        (a b m : ℕ) (S : Finset ι) (hS : S ⊆ u) (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (lam : ℝ≥0),
        S.Nonempty →
        ∀ (ht : ∀ i, (Z i).toTube = (T i).toTube),
        (∀ i, (Z i).shade ⊆ (T i).shade) →
        ∀ (hh : IsClassHomogeneousOn 𝒰 S),
        (∀ i ∈ S, (Z i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
        Kakeya.maxDensity S (fun i ↦ (Z i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-ηin) →
        ML2Shaded.HasDenseShading lam S (fun i ↦ (Z i).toShadedBody) →
        ML2Shaded.HasComparableDensities lam⁻¹ S (fun i ↦ (Z i).toShadedBody) →
        (δ : ℝ≥0) ^ ηin / 2 ≤ lam →
        (u.card : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ)) →
        Cu ≤ Cu₀ →
        Λf δ * (δ : ℝ≥0∞) ^ gt ≤ (δ : ℝ≥0∞) ^ g →
        -- alternative (F) on the source's simultaneous refinement of the family `(S, Z)`, in the
        -- inherited tower
        RefinedFloorHypothesis (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ gain dens
          η' (Λf δ) ((𝒰.restrictOccupied hS hh).retube (funext ht)) a b m →
        ∀ (ε₀ : ℝ) (Λ : ℝ≥0∞), TrialOutcomeAtGain h ε₀ g β 𝒰 Λ lam S Z := by
  refine (trialOutcome_middle_of_floorFactors_refined_bound hβ0 hβ1 hϖ hgain hdens hε₁ hC hCu₀ hκc
    hκ' hθ₂ hεp hres (Kl := Kl) (cl := cl) (gt := gt) (g := g) Λf hexp hfac).mono ?_
  intro δ hδ ι u T Cu 𝒰 a b m S hS Z lam hSne ht hs hh hball hmaxS hdense hcomp hlamlow hcardu
    hCu hΛf href ε₀ Λ
  unfold TrialOutcomeAtGain
  exact Or.inr (Or.inl (hδ u T Cu 𝒰 a b m S hS Z lam hSne ht hs hh hball hmaxS hdense hcomp
      hlamlow hcardu hCu
      hΛf href))

open Classical in
/-- **F7 at the descent's re-cut exponents, on the refinement** (`IsTrialAt`
concludes `TrialOutcomeAtGain h (β/2 − α) (4ν + α)`, `α := defectMargin`; `M1`).
Same binders as `trialOutcome_middle_of_floorFactors` (C-D1: ambient `𝒰` on `u`, `S ⊆ u`, shading
`Z`) (`RefinedFloorHypothesis` at `Λf δ`),
same conclusion as before `M1`.  The engine runs on the refinement at `gt := 4ν + 2α` — so `hexp`
reads `6ν + θ₂ + η_in ≤ …` (the existing `5ν` plus one more `α = ν`, the refinement's own margin) —
and `hΛf : Λf δ · δ^{4ν+2α} ≤ δ^{4ν+α}` absorbs the loss.  Instance of
`trialOutcome_middle_of_floorFactors_refined` at `gt := 4ν + 2α`, `g := 4ν + α`. -/
theorem trialOutcome_middle_of_floorFactors_alpha
    {β ϖ : ℝ} {gain dens : ℝ → ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    {ε₁ : ℝ} (hε₁ : 0 < ε₁)
    {ηin : ℝ}
    {C : ℝ≥0} {Kl cl : ℕ} (hC : 1 ≤ C) {Cu₀ : ℝ≥0} (hCu₀ : 1 ≤ Cu₀) {η' h : ℝ}
    {gm : ℝ → ℝ} {εf εp εc κc κ' θ₂ : ℝ}
    (hκc : 0 < κc) (hκ' : 0 < κ') (hθ₂ : 0 < θ₂) (hεp : 0 < εp)
    -- R0d, route (i) : the residual case `b < p` of the four-way split,
    -- priced.  Named, so a re-routing moves this row and nothing else.
    (hres : ∀ k : ℕ, k < ML2Spine.spineCount ϖ ε₁ →
      κc + ML2Spine.spineRung β ϖ ε₁ gain dens k ≤ 2 * η') (Λf : ℝ≥0 → ℝ≥0∞)
    (hexp : ∀ X : ℝ, ML2Spine.spineNu β ϖ ε₁ gain dens ≤ X →
      6 * ML2Spine.spineNu β ϖ ε₁ gain dens + θ₂ + ηin ≤ gm X - εf - εp - (εc + X) - κ')
    (hfac : ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0,
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
              * ((tθ'.card : ℕ) : ℝ≥0∞) ^ β) :
    ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0,
      ∀ {ι : Type u} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (Cu : ℝ≥0) (𝒰 : Tube.UniformTubeSet u (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu)
        (a b m : ℕ) (S : Finset ι) (hS : S ⊆ u) (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (lam : ℝ≥0),
        S.Nonempty →
        ∀ (ht : ∀ i, (Z i).toTube = (T i).toTube),
        (∀ i, (Z i).shade ⊆ (T i).shade) →
        ∀ (hh : IsClassHomogeneousOn 𝒰 S),
        (∀ i ∈ S, (Z i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
        Kakeya.maxDensity S (fun i ↦ (Z i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-ηin) →
        ML2Shaded.HasDenseShading lam S (fun i ↦ (Z i).toShadedBody) →
        ML2Shaded.HasComparableDensities lam⁻¹ S (fun i ↦ (Z i).toShadedBody) →
        (δ : ℝ≥0) ^ ηin / 2 ≤ lam →
        (u.card : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ)) →
        Cu ≤ Cu₀ →
        Λf δ * (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens
              + 2 * defectMargin β ϖ ε₁ gain dens)
            ≤ (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens
              + defectMargin β ϖ ε₁ gain dens) →
        -- alternative (F) on the source's simultaneous refinement of the family `(S, Z)`, in the
        -- inherited tower
        RefinedFloorHypothesis (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ gain dens
          η' (Λf δ) ((𝒰.restrictOccupied hS hh).retube (funext ht)) a b m →
        ∀ Λ : ℝ≥0∞, TrialOutcomeAtGain h (β / 2 - defectMargin β ϖ ε₁ gain dens)
          (4 * ML2Spine.spineNu β ϖ ε₁ gain dens + defectMargin β ϖ ε₁ gain dens) β 𝒰 Λ lam S Z
          := by
  have hexp' : ∀ X : ℝ, ML2Spine.spineNu β ϖ ε₁ gain dens ≤ X →
      4 * ML2Spine.spineNu β ϖ ε₁ gain dens + 2 * defectMargin β ϖ ε₁ gain dens + θ₂ + ηin
        ≤ gm X - εf - εp - (εc + X) - κ' := by
    intro X hX
    have h := hexp X hX
    rw [defectMargin_eq]
    linarith
  refine (trialOutcome_middle_of_floorFactors_refined hβ0 hβ1 hϖ hgain hdens hε₁ hC hCu₀ hκc hκ'
    hθ₂ hεp hres (Kl := Kl) (cl := cl) (h := h)
    (gt := 4 * ML2Spine.spineNu β ϖ ε₁ gain dens + 2 * defectMargin β ϖ ε₁ gain dens)
    (g := 4 * ML2Spine.spineNu β ϖ ε₁ gain dens + defectMargin β ϖ ε₁ gain dens)
    Λf hexp' hfac).mono ?_
  intro δ hδ ι u T Cu 𝒰 a b m S hS Z lam hSne ht hs hh hball hmaxS hdense hcomp hlamlow hcardu
    hCu hΛf href Λ
  exact hδ u T Cu 𝒰 a b m S hS Z lam hSne ht hs hh hball hmaxS hdense hcomp hlamlow hcardu hCu
    hΛf href _ Λ

end Kakeya.ML2Core

end

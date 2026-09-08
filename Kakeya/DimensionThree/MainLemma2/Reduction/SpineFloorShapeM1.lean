/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeRetube

/-!
# The floor condition on a simultaneous refinement

`FloorHypothesisAt` states the floor condition with the hierarchy as a parameter;
`floorHypothesisAt_landed` identifies it with the corresponding expanded predicate.
`RefinedFloorHypothesis` asks for this condition on a refinement `(S', W)` and its
inherited hierarchy `refinedHierarchy`.

The identity refinement gives `refinedFloorHypothesis_of_landed` at `Λf = 1`.
For a general refinement, the dividing-window condition must be stated inside
the existential quantifier that binds the refinement. Its upper density bounds
and lower concentration bounds behave differently under restriction: the former
become weaker, whereas the latter may fail. Failure of lower concentration is
the defect alternative, quantified by `profileDrop_of_concentration_destroyed`.
This follows GWZ's order in : simultaneous factoring
and mass-coupled refinement precede the concentration test.

The factorization hypothesis is universal in the family, shading and hierarchy,
so it can be applied to the inherited hierarchy. Dense shading supplies mass
positivity. The multiplicity transfer uses the absorption
`Λf * δ^(4ν + α) ≤ δ^(4ν)` and `middleGain_of_refinement`.
When the refinement loss depends on `δ`, it must be supplied as a function of
`δ` or quantified together with the refinement, rather than fixed before `δ`.
`RefinedFloorHypothesis` itself simply takes the loss as an argument.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric ConvexSpaceBody ShadedBody
open Tube

namespace Kakeya.ML2Core

section M1

variable {ι : Type*} {δ Cu : ℝ≥0}

/-- **The existing `(F)` payload, with the hierarchy a parameter.**  This is
`Reduction/SpineFloorTerminal.lean` verbatim; `Kakeya.ML2Core.floorHypothesisAt_landed` is
the `Iff.rfl` that says so. -/
def FloorHypothesisAt (β ϖ ε₁ : ℝ) (gain dens : ℝ → ℝ) (η' : ℝ) {s : Finset ι}
    {V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (𝒰 : Tube.UniformTubeSet s (fun i ↦ (V i).toTube) (Tube.ssfGridLen δ) Cu)
    (a b m : ℕ) : Prop :=
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
        ≤ ((𝒰.nodesUnder m' p jp).card : ℝ)))

/-- **The count-floor hypothesis for alternative `(F)`.** See the module docstring.

**No fullness clause**: the rate lives in the trial — `IsTrialAtGain`'s
`HasDenseShading lam S` and `δ^{η_in}/2 ≤ lam` are hereditary to every subfamily — so a fullness
clause here was duplication; the engine `trialOutcome_middle_of_floorFactors_bound` takes mass
positivity from the dense shading, and a fullness rate on the refinement is one lemma away
(`Kakeya.ML2Core.fullness_refinement_of_denseShading`).

**No line-ED clause** either.  E0's levels row on the refined
hierarchy had no producer — line-essential distinctness is sourced inside the middle factor from its
centred re-uniformisation — so that conjunct is gone and, with it, the constant `A` (its only use)
and `ηin` (dead ).  One fewer conjunct to supply: the predicate is weaker, so every theorem
taking it as a hypothesis, F7 included, is strengthened. -/
def RefinedFloorHypothesis (β ϖ ε₁ : ℝ) (gain dens : ℝ → ℝ) (η' : ℝ)
    {C : ℝ≥0} {Kl cl : ℕ} (Λf : ℝ≥0∞) {S : Finset ι}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (𝒰 : Tube.UniformTubeSet S (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu)
    (a b m : ℕ) : Prop :=
  ∃ (S' : Finset ι) (W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
      (hS' : S' ⊆ S) (hhom : IsClassHomogeneousOn 𝒰 S')
      (hW : (fun i ↦ (W i).toTube) = (fun i ↦ (T i).toTube)),
    IsShadedRefinementOf 𝒰 Λf S T S' W ∧
    ML2Reduction.IsKatzTaoDividingWindowLevels (refinedHierarchy 𝒰 hS' hhom hW)
      ((C : ℝ≥0∞) * StickyKakeya.totalLoss C Kl cl δ) (ML2Spine.spineRung β ϖ ε₁ gain dens)
      (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m ∧
    FloorHypothesisAt β ϖ ε₁ gain dens η' (refinedHierarchy 𝒰 hS' hhom hW) a b m

end M1

end Kakeya.ML2Core

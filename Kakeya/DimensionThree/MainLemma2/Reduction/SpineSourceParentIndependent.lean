/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceParentGeometry
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceChosenTowerRealization
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceUnselectedNestedTower

/-!
# Window normalization independent of the parent choice

Defines `SourceParentUpperWindow` (the monotone upper window rows),
`SourceParentEccentric` (the eccentric alternative keeping the selected hulls) and
`SourceParentCompleteHistory` (one weighted history paying both coarse and reparented
factorings). The main result `source_exists_window_normalization` chooses biased-loss
parameters and a threshold `delta0` before the scale and, for every window `a < m < M`, produces
a descendant partition, an affine normalization and comparison constants realizing
`ML2Assembly.SourceBiasedParentGeometry`. `source_exists_chosen_tower_neighbour_realization`
discharges `SourceChosenTowerNeighbourRealization` from the unselected nested tower.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

universe u

variable {iota : Type u} {delta : ℝ≥0} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace ℝ (Fin 3))} {M C : Nat}

/-- Only the upper window rows pass to a subfamily by monotonicity. -/
structure SourceParentUpperWindow (Q : SourceThreadedTower S T M C)
    (A0 A1 N : Nat) (eta : Nat -> ℝ) (e : ℝ) (a b J : Nat) : Prop where
  coarse_lt_fine : a < b
  fine_bound : b <= M
  separation : (sourceTowerRadius delta M b : ℝ) / (sourceTowerRadius delta M a : ℝ) <=
    (delta : ℝ) ^ e
  coarse_density : a > 0 -> forall j, j ∈ Q.indexSet 0 ->
    Kakeya.maxDensity (Q.fibre 0 a j) (fun i => (Q.tube a i).toConvexSpaceBody) <=
      (sourceTowerWindowConstant C A0 A1 : ℝ≥0∞) ^ N * ENNReal.ofReal
        (((sourceTowerRadius delta M 0 : ℝ) / (sourceTowerRadius delta M a : ℝ)) ^ eta J)
  middle_density : forall j, j ∈ Q.indexSet a ->
    Kakeya.maxDensity (Q.fibre a b j) (fun i => (Q.tube b i).toConvexSpaceBody) <=
      ENNReal.ofReal
        (((sourceTowerRadius delta M a : ℝ) / (sourceTowerRadius delta M b : ℝ)) ^ eta J)

/-- The actual eccentric alternative keeps the selected hulls and their complete
leaf partitions. It is not an eccentric scale predicate or a newly chosen shading. -/
structure SourceParentEccentric (Q : SourceThreadedTower S T M C)
    {e bias : ℝ} {a b : Nat} (B : SourceJointWindowFactors Q e a b bias)
    (etaParent : ℝ) where
  level : Nat
  in_window : SourceTowerWindow delta M e a b level
  eccentric : B.short level / B.middle level <= delta ^ etaParent
  factorization : forall j, j ∈ Q.indexSet a ->
    Factorization (Q.fibre a level j) (fun i => (Q.tube level i).toConvexSpaceBody)
      (sourceParentPlankConstant delta bias)
  same_parts : forall j, forall hj : j ∈ Q.indexSet a,
    (factorization j hj).parts = (B.factor level in_window j hj).partition.parts

/-- Coarse and reparented factorings share one actual weighted history and one
fixed-polylog payment. Each local L is paid by its parent-aggregate stage. -/
structure SourceParentCompleteHistory (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3)))
    {R : Finset iota} (Q' : SourceThreadedTower R T M C)
    {e bias etaParent tau : ℝ} {a b : Nat} {transverseCap : ℝ≥0}
    (B : SourceJointWindowFactors Q' e a b bias)
    (P : SourceActualParent Q' B etaParent tau transverseCap)
    (K : Nat) where
  coarse_history : SourceCompatibleWholeFactors Q Z Q' B K
  stage : Nat -> iota -> iota -> Nat
  stage_bound : forall m, forall _hm : SourceTowerWindow delta M e a b m,
    forall j, forall _hj : j ∈ Q'.indexSet a,
    forall jp, forall _hjp : jp ∈ Q'.fibre a P.parent j,
      stage m j jp < coarse_history.trace.length
  origin : forall m, forall hm : SourceTowerWindow delta M e a b m,
    forall j, forall hj : j ∈ Q'.indexSet a,
    forall jp, forall hjp : jp ∈ Q'.fibre a P.parent j,
      SourceFactorStageOrigin Q Z (coarse_history.trace.state (stage m j jp)) R Q'
        P.parent m jp bias (P.reparented m hm j hj jp hjp).factor
  stage_level : forall m, forall _hm : SourceTowerWindow delta M e a b m,
    forall j, forall _hj : j ∈ Q'.indexSet a,
    forall jp, forall _hjp : jp ∈ Q'.fibre a P.parent j,
      coarse_history.trace.level (stage m j jp) = m
  stage_selected : forall m, forall hm : SourceTowerWindow delta M e a b m,
    forall j, forall hj : j ∈ Q'.indexSet a,
    forall jp, forall hjp : jp ∈ Q'.fibre a P.parent j,
      Q.retainedAssignedFibre (coarse_history.trace.state (stage m j jp + 1)) P.parent m jp =
        (origin m hm j hj jp hjp).actual.selection.selected
  stage_blocks : forall m, forall hm : SourceTowerWindow delta M e a b m,
    forall j, forall hj : j ∈ Q'.indexSet a,
    forall jp, forall hjp : jp ∈ Q'.fibre a P.parent j,
      (origin m hm j hj jp hjp).actual.selection.parts <=
        coarse_history.trace.retainedBlocks (stage m j jp)
  actual_loss_paid : forall m, forall hm : SourceTowerWindow delta M e a b m,
    forall j, forall hj : j ∈ Q'.indexSet a,
    forall jp, forall hjp : jp ∈ Q'.fibre a P.parent j,
      nonempty_biasedFactorization.L 3
        (Q.retainedAssignedFibre (coarse_history.trace.state (stage m j jp)) P.parent m jp).card
        (origin m hm j hj jp hjp).normalizedThickness bias <=
          coarse_history.trace.stepLoss (stage m j jp)

end Kakeya.ML2Core

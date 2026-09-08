/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceFixedPreparation
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceFactorLossEnvelope

/-!
# Data structures for the paid parent selection

Definitions only. `SourceParentSchedule` fixes the scalar schedule (`N`, `M`, `J`, `e`,
rungs `eta`, `etaParent`, `bias`) before the runtime scale; `sourceParentWindow` and
`sourceParentPlankConstant` are the associated constants. `SourceParentRetainedState`
records a paid selection on the same threaded tower, `SourceWholeCellStep` and
`SourceWholeFactorTrace` its legal whole-cell history, and `SourceParentBiasedFactors`,
`SourceJointWindowFactors`, `SourceFactorStageOrigin`, `SourceCompatibleWholeFactors` the
biased factor rows bound to one fixed `Q`. `SourceParentRetainedConcentration` and
`SourceParentFailedConcentration` state the lower concentration test and its failure.
Consumed by the parent geometry, bridge and outcome files.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube

namespace Kakeya.ML2Core

universe u

/-- The scalar hypotheses of S:4000-4018, fixed before the runtime scale. -/
structure SourceParentSchedule (N M J : Nat) (e : ℝ)
    (eta : Nat -> ℝ) (etaParent bias : ℝ) : Prop where
  count_bound : 5 <= N
  level_bound : 2 <= M
  index_lower : 1 <= J
  index_upper : J <= N
  window_exponent : e = (N : ℝ) ^ (-(1 : ℝ) / 2)
  rung_positive : forall j, 1 <= j -> j <= N + 1 -> 0 < eta j
  rung_mono : forall j k, 1 <= j -> j <= k -> k <= N + 1 -> eta j <= eta k
  rung_upper : eta (N + 1) <= e
  rung_step : forall j, 1 <= j -> j <= N -> eta j <= e ^ 2 * eta (j + 1) / 100
  parent_positive : 0 < etaParent
  parent_upper : etaParent <= e ^ 2 * eta (J + 1) / 64
  bias_positive : 0 < bias
  bias_upper : bias <= etaParent / 16
  global_mesh : 512 * (N : ℝ) / eta 1 <= (M : ℝ)
  parent_mesh : 8 / etaParent <= (M : ℝ)

open scoped Classical in
noncomputable def sourceParentWindow (delta : ℝ≥0) (M : Nat)
    (e : ℝ) (a b : Nat) : Finset Nat :=
  (Finset.range (M + 1)).filter (SourceTowerWindow delta M e a b)

noncomputable def sourceParentPlankConstant (delta : ℝ≥0) (bias : ℝ) : ℝ≥0 :=
  Real.toNNReal (4 * (3 : ℝ) ^ ((9 : ℝ) / 2) * 2 ^ 6) * delta ^ (-3 * bias)

variable {iota : Type u} {delta : ℝ≥0} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace ℝ (Fin 3))} {M C : Nat}

/-- A paid selection on the same assigned tower, including every statistic used later. -/
structure SourceParentRetainedState (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3)))
    (R : Finset iota) (Q' : SourceThreadedTower R T M C)
    (Z' : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3)))
    (loss : ℝ≥0∞) : Prop where
  restriction : SourceTowerRestriction Q Q'
  nonempty : R.Nonempty
  original_tubes : forall i, (Z i).toTube = T i
  same_tubes : forall i, (Z' i).toTube = T i
  subshade : forall i, (Z' i).shade <= (Z i).shade
  mass : (∑ i ∈ S, volume (Z i).shade) <= loss * ∑ i ∈ R, volume (Z' i).shade
  fullness : ShadedBody.fullness' S (fun i => (Z i).toShadedBody) <=
    loss * ShadedBody.fullness' R (fun i => (Z' i).toShadedBody)
  multiplicity : ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <=
    loss * ShadedBody.multiplicity R (fun i => (Z' i).toShadedBody)
  statistics : SourceTowerStatistics Q' Z'
  shade_floor : forall i, i ∈ R ->
    (delta : ℝ≥0∞) ^ (10 : ℝ) * volume (T i).carrier <= volume (Z' i).shade

open scoped Classical in
/-- A legal whole-cell operation refers to its immediate preceding family. -/
structure SourceWholeCellStep (Q : SourceThreadedTower S T M C)
    (F G : Finset iota) (k : Nat) where
  selected : Finset iota
  selected_subset : selected <= Q.assignedFootprint F k
  leaves_eq : G = F.filter (fun i => Q.place k i ∈ selected)
  complete : forall j, j ∈ selected ->
    G.filter (fun i => Q.place k i = j) = F.filter (fun i => Q.place k i = j)

open scoped Classical in
/-- The actual finite history records legal whole blocks and every paid mass step.
It does not assert original-fibre saturation for unrelated crossing partitions. -/
structure SourceWholeFactorTrace (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3)))
    (R : Finset iota) (K : Nat) where
  length : Nat
  state : Nat -> Finset iota
  level : Nat -> Nat
  blocks : Nat -> Finset (Finset iota)
  retainedBlocks : Nat -> Finset (Finset iota)
  initial : state 0 = S
  final : state length = R
  all_subset : forall n, n <= length -> state n <= S
  all_nonempty : forall n, n <= length -> (state n).Nonempty
  level_bound : forall n, n < length -> level n <= M
  whole_step : forall n, n < length ->
    Nonempty (SourceWholeCellStep Q (state n) (state (n + 1)) (level n))
  block_partition : forall n, n < length ->
    (blocks n).sup id = Q.assignedFootprint (state n) (level n)
  block_nonempty : forall n, n < length -> forall t, t ∈ blocks n -> t.Nonempty
  block_disjoint : forall n, n < length -> (blocks n : Set (Finset iota)).PairwiseDisjoint id
  retained_subset : forall n, n < length -> retainedBlocks n <= blocks n
  selected_blocks : forall n, n < length ->
    Q.assignedFootprint (state (n + 1)) (level n) = (retainedBlocks n).sup id
  stepLoss : Nat -> ℝ≥0∞
  loss_one_le : forall n, n < length -> 1 <= stepLoss n
  loss_finite : forall n, n < length -> stepLoss n < ⊤
  step_mass : forall n, n < length ->
    (∑ i ∈ state n, volume (Z i).shade) <=
      stepLoss n * ∑ i ∈ state (n + 1), volume (Z i).shade
  total_loss : (∏ n ∈ Finset.range length, stepLoss n) <= sourceFixedPreparationLoss K delta

open scoped Classical in
/-- Raw-coordinate biased factors, with the actual affine reference and its price.
The independent weighted B5 witness supplies these rows before compatible restriction. -/
structure SourceParentBiasedFactors (Q : SourceThreadedTower S T M C)
    (a m : Nat) (j : iota) (bias : ℝ) where
  partition : Finpartition (Q.fibre a m j)
  normalization : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)
  comparison : ℝ≥0
  comparison_one_le : 1 <= comparison
  reference_contains : (Q.tube a j).toConvexSpaceBody <=
    ML2Assembly.sourceAffineReference normalization
  reference_volume : volume (ML2Assembly.sourceAffineReference normalization).carrier <=
    (comparison : ℝ≥0∞) * volume (Q.tube a j).carrier
  hull_contained : forall part, part ∈ partition.parts ->
    part.convexHull_biUnion (fun i => (Q.tube m i).toConvexSpaceBody) <=
      (Q.tube a j).toConvexSpaceBody
  hull_positive : forall part, part ∈ partition.parts ->
    0 < volume (part.convexHull_biUnion (fun i => (Q.tube m i).toConvexSpaceBody)).carrier
  density : forall part, part ∈ partition.parts ->
    forall V : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)),
    Kakeya.densityIn part (fun i => (Q.tube m i).toConvexSpaceBody) V <=
      (nonempty_biasedFactorization.C 3 bias : ℝ≥0∞) *
        (volume V.carrier /
          volume (part.convexHull_biUnion (fun i => (Q.tube m i).toConvexSpaceBody)).carrier) ^ bias *
        Kakeya.densityIn part (fun i => (Q.tube m i).toConvexSpaceBody)
          (part.convexHull_biUnion (fun i => (Q.tube m i).toConvexSpaceBody))
  capture_paid : forall part, part ∈ partition.parts ->
    (nonempty_biasedFactorization.C 3 bias : ℝ≥0∞)⁻¹ *
      (comparison : ℝ≥0∞) ^ (-bias) *
      (volume (part.convexHull_biUnion (fun i => (Q.tube m i).toConvexSpaceBody)).carrier /
        volume (Q.tube a j).carrier) ^ bias *
      Kakeya.maxDensity (Q.fibre a m j) (fun i => (Q.tube m i).toConvexSpaceBody) <=
      Kakeya.densityIn part (fun i => (Q.tube m i).toConvexSpaceBody)
        (part.convexHull_biUnion (fun i => (Q.tube m i).toConvexSpaceBody))
  outer_katzTao : forall part, part ∈ partition.parts ->
    ConvexSpaceBody.IsKatzTao partition.parts
      (fun part => part.convexHull_biUnion (fun i => (Q.tube m i).toConvexSpaceBody))
      ((nonempty_biasedFactorization.C 3 bias : ℝ≥0∞) *
        (volume (part.convexHull_biUnion (fun i => (Q.tube m i).toConvexSpaceBody)).carrier /
          volume (ML2Assembly.sourceAffineReference normalization).carrier) ^ (-bias))
  whole_leaf_partition : Q.cell a j = partition.parts.biUnion
    (fun part => S.filter (fun i => Q.place m i ∈ part))
  whole_leaf_mass : forall Z : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3)),
    (∑ i ∈ Q.cell a j, volume (Z i).shade) = ∑ part ∈ partition.parts,
      ∑ i ∈ S.filter (fun i => Q.place m i ∈ part), volume (Z i).shade

open scoped Classical in
/-- Factor selection and the final lower test are bound to the same fixed Q. -/
structure SourceJointWindowFactors (Q : SourceThreadedTower S T M C)
    (e : ℝ) (a b : Nat) (bias : ℝ) where
  factor : forall m, SourceTowerWindow delta M e a b m ->
    forall j, j ∈ Q.indexSet a -> SourceParentBiasedFactors Q a m j bias
  short : Nat -> ℝ≥0
  middle : Nat -> ℝ≥0
  long : Nat -> ℝ≥0
  short_positive : forall m, SourceTowerWindow delta M e a b m -> 0 < short m
  dimensions_order : forall m, SourceTowerWindow delta M e a b m ->
    short m <= middle m /\ middle m <= long m
  long_lower : forall m, SourceTowerWindow delta M e a b m ->
    Real.toNNReal (1 / (4 * Real.sqrt 3)) <= long m
  long_upper : forall m, SourceTowerWindow delta M e a b m -> long m <= 64
  common_dimensions : forall m, forall hm : SourceTowerWindow delta M e a b m,
    forall j, forall hj : j ∈ Q.indexSet a,
    forall part, part ∈ (factor m hm j hj).partition.parts ->
      ((short m : ℝ≥0∞) <= ethickness ℝ
          (part.convexHull_biUnion (fun i => (Q.tube m i).toConvexSpaceBody)).carrier 2 /\
        ethickness ℝ (part.convexHull_biUnion
          (fun i => (Q.tube m i).toConvexSpaceBody)).carrier 2 <= 2 * (short m : ℝ≥0∞)) /\
      ((middle m : ℝ≥0∞) <= ethickness ℝ
          (part.convexHull_biUnion (fun i => (Q.tube m i).toConvexSpaceBody)).carrier 1 /\
        ethickness ℝ (part.convexHull_biUnion
          (fun i => (Q.tube m i).toConvexSpaceBody)).carrier 1 <= 2 * (middle m : ℝ≥0∞)) /\
      ((long m : ℝ≥0∞) <= ethickness ℝ
          (part.convexHull_biUnion (fun i => (Q.tube m i).toConvexSpaceBody)).carrier 0 /\
        ethickness ℝ (part.convexHull_biUnion
          (fun i => (Q.tube m i).toConvexSpaceBody)).carrier 0 <= 2 * (long m : ℝ≥0∞))

open scoped Classical in
/-- The final factor really comes from a weighted B5 selection in a named earlier state. -/
structure SourceFactorStageOrigin (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3)))
    (F R : Finset iota) (Q' : SourceThreadedTower R T M C)
    (a m : Nat) (j : iota) (bias : ℝ)
    (B : SourceParentBiasedFactors Q' a m j bias) where
  partition : ML2Assembly.SourceDescendantPartition
    (F.filter (fun i => Q.place a i = j)) (Q.retainedAssignedFibre F a m j)
  cell_assignment : partition.assign = Q.place m
  normalizedThickness : ℝ≥0
  normalized_positive : 0 < normalizedThickness
  normalized_le_one : normalizedThickness <= 1
  actual : ML2Assembly.SourceAffineWeightedParent partition
    (fun i => (Z i).toShadedBody) (fun i => (Q.tube m i).toConvexSpaceBody)
    (Q.tube a j).toConvexSpaceBody B.normalization B.comparison normalizedThickness bias
  final_parts : B.partition.parts <= actual.selection.parts
  final_cells : Q'.fibre a m j = B.partition.parts.sup id
  original_hulls : forall part, part ∈ B.partition.parts ->
    part.convexHull_biUnion (fun i => (Q'.tube m i).toConvexSpaceBody) =
      part.convexHull_biUnion (fun i => (Q.tube m i).toConvexSpaceBody)

open scoped Classical in
/-- One history witnesses compatibility of all final factors with their paid origins. -/
structure SourceCompatibleWholeFactors (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3)))
    {R : Finset iota} (Q' : SourceThreadedTower R T M C)
    {e bias : ℝ} {a b : Nat} (B : SourceJointWindowFactors Q' e a b bias) (K : Nat) where
  trace : SourceWholeFactorTrace Q Z R K
  stage : Nat -> Nat
  stage_bound : forall m, SourceTowerWindow delta M e a b m -> stage m < trace.length
  stage_level : forall m, SourceTowerWindow delta M e a b m -> trace.level (stage m) = m
  origin : forall m, forall hm : SourceTowerWindow delta M e a b m,
    forall j, forall hj : j ∈ Q'.indexSet a,
      SourceFactorStageOrigin Q Z (trace.state (stage m)) R Q' a m j bias (B.factor m hm j hj)
  stage_selected : forall m, forall hm : SourceTowerWindow delta M e a b m,
    forall j, forall hj : j ∈ Q'.indexSet a,
      Q.retainedAssignedFibre (trace.state (stage m + 1)) a m j =
        (origin m hm j hj).actual.selection.selected
  stage_blocks : forall m, forall hm : SourceTowerWindow delta M e a b m,
    forall j, forall hj : j ∈ Q'.indexSet a,
      (origin m hm j hj).actual.selection.parts <= trace.retainedBlocks (stage m)
  actual_loss_paid : forall m, forall hm : SourceTowerWindow delta M e a b m,
    forall j, forall hj : j ∈ Q'.indexSet a,
      nonempty_biasedFactorization.L 3
        (Q.retainedAssignedFibre (trace.state (stage m)) a m j).card
        (origin m hm j hj).normalizedThickness bias <= trace.stepLoss (stage m)

/-- The lower concentration is tested after the selection, at tau/2. -/
def SourceParentRetainedConcentration (Q : SourceThreadedTower S T M C)
    (e tau : ℝ) (a b : Nat) : Prop :=
  forall m, SourceTowerWindow delta M e a b m -> forall j, j ∈ Q.indexSet a ->
    (1 / 2 : ℝ≥0∞) * ENNReal.ofReal
      (((sourceTowerRadius delta M a : ℝ) / (sourceTowerRadius delta M m : ℝ)) ^ (tau / 2)) <=
      Kakeya.maxDensity (Q.fibre a m j) (fun i => (Q.tube m i).toConvexSpaceBody)

/-- A measured failed coordinate of the original and final assigned profiles. -/
structure SourceParentFailedConcentration (Q : SourceThreadedTower S T M C)
    (R : Finset iota) (a m : Nat) (e tau : ℝ) : Prop where
  subset : R <= S
  coarse_lt_middle : a < m
  middle_bound : m <= M
  old_density : (1 / 2 : ℝ≥0∞) * ENNReal.ofReal
    (((sourceTowerRadius delta M a : ℝ) / (sourceTowerRadius delta M m : ℝ)) ^ tau) <=
      Q.assignedProfile S a m
  new_density : Q.assignedProfile R a m <= (1 / 2 : ℝ≥0∞) * ENNReal.ofReal
    (((sourceTowerRadius delta M a : ℝ) / (sourceTowerRadius delta M m : ℝ)) ^ (tau / 2))
  nontruncated : 2 <=
    ((sourceTowerRadius delta M a : ℝ) / (sourceTowerRadius delta M m : ℝ)) ^ (tau / 2)
  logarithmic_gap : e ^ 2 / 2 <=
    Real.log ((sourceTowerRadius delta M a : ℝ) / (sourceTowerRadius delta M m : ℝ)) /
      Real.log (1 / (delta : ℝ))

end Kakeya.ML2Core

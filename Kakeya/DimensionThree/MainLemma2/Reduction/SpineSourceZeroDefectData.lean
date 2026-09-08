/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceFixedPreparation
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceFactorCeilings
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceTerminal
public import Kakeya.Factorization
public import Kakeya.Factoring.FlatPrisms

/-!
# Zero-defect data for the source nonsticky branch

Definitions only. The scalar gains `Kakeya.ML2Core.sourceZeroFloorGain`,
`sourceZeroEccentricGain`, `sourceZeroNonstickyGain` (S:4269-4283), the shifted ladder
`sourceZeroLadder`, and the displayed plank constant `sourceZeroPlankConstant` (S:4080). The
structures `SourceZeroFloor`, `SourceZeroFactorDimensions`, `SourceZeroEccentricFactors`,
`SourceZeroWindowSchedule`, `SourceZeroFourFactors`, `SourceZeroRetainedState` and
`SourceZeroFailedConcentration` record, on a fixed `SourceThreadedTower`, the geometric floor,
the P-branch convex-hull factors, the inherited scalar schedule, the four-factor multiplicity
output, a retained branch selection, and the measured failure of lower concentration.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube

namespace Kakeya.ML2Core

universe u

/-- S:4269-4283. The two nonsticky gains retain no defect term. -/
noncomputable def sourceZeroFloorGain (e v : ℝ) : ℝ := e * v / 8

/-- Source J starts at one; the canonical Lean rung starts at zero. -/
noncomputable def sourceZeroLadder (beta varpi eps1 : ℝ)
    (rawGain rawDens : ℝ -> ℝ) (J : Nat) : ℝ :=
  ML2Spine.spineRung beta varpi eps1
    (ML2Assembly.sourceChoiceGain beta rawGain rawDens)
    (ML2Assembly.sourceChoiceDens beta rawDens) (J - 1)

/-- S:4080: the complete displayed factorization constant, before absorption. -/
noncomputable def sourceZeroPlankConstant (delta : ℝ≥0) (epsBias : ℝ) : ℝ≥0 :=
  Real.toNNReal (4 * (3 : ℝ) ^ ((9 : ℝ) / 2) * 2 ^ 6) * delta ^ (-3 * epsBias)

variable {iota : Type u} {delta : ℝ≥0} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace ℝ (Fin 3))} {M C : Nat}

/-- Actual geometric floor on this tower, not a multiplicity estimate. -/
structure SourceZeroFloor (Q : SourceThreadedTower S T M C)
    (e tau etaParent : ℝ) (a b p : Nat) : Prop where
  coarse_le_parent : a <= p
  parent_lt_fine : p < b
  fine_bound : b <= M
  parent_before_window : forall k, SourceTowerWindow delta M e a b k -> p < k
  parent_density : forall j, j ∈ Q.indexSet a ->
    Kakeya.maxDensity (Q.fibre a p j) (fun k => (Q.tube p k).toConvexSpaceBody) <=
      (delta : ℝ≥0∞) ^ (-2 * etaParent)
  floor : forall j, j ∈ Q.indexSet a -> forall jp, jp ∈ Q.fibre a p j ->
    forall k, SourceTowerWindow delta M e a b k -> p < k ->
      ((sourceTowerRadius delta M p : ℝ) / (sourceTowerRadius delta M k : ℝ)) ^
        (2 + 4 * (tau / 16)) <= ((Q.fibre p k jp).card : ℝ)

/-- Dimensions are compared to the actual affine thicknesses, with an explicit
fixed comparison D. This records the John/affine-thickness bridge as data. -/
def SourceZeroFactorDimensions (D aw bw cw : ℝ≥0)
    (W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) : Prop :=
  (D : ℝ≥0∞)⁻¹ * cw <= ethickness ℝ W.carrier 0 /\
    ethickness ℝ W.carrier 0 <= (D : ℝ≥0∞) * cw /\
  (D : ℝ≥0∞)⁻¹ * bw <= ethickness ℝ W.carrier 1 /\
    ethickness ℝ W.carrier 1 <= (D : ℝ≥0∞) * bw /\
  (D : ℝ≥0∞)⁻¹ * aw <= ethickness ℝ W.carrier 2 /\
    ethickness ℝ W.carrier 2 <= (D : ℝ≥0∞) * aw

open scoped Classical in
/-- The actual P branch: every assigned m-cell is partitioned into the actual
convex hull factors; all descendant leaves are present on the selected tower. -/
structure SourceZeroEccentricFactors (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3)))
    (a m : Nat) (etaParent epsBias : ℝ) (D aw bw cw : ℝ≥0) where
  factor : forall j, j ∈ Q.indexSet a ->
    ConvexSpaceBody.Factorization (Q.fibre a m j)
      (fun k => (Q.tube m k).toConvexSpaceBody) (sourceZeroPlankConstant delta epsBias)
  coarse_lt_middle : a < m
  middle_bound : m <= M
  dimension_comparison : 1 <= D
  short_pos : 0 < aw
  short_le_middle : aw <= bw
  middle_le_long : bw <= cw
  long_lower : Real.toNNReal (1 / (4 * Real.sqrt 3)) <= cw
  long_upper : cw <= 64
  eccentric : aw / bw <= delta ^ etaParent
  dimensions : forall j, forall hj : j ∈ Q.indexSet a,
    forall part, part ∈ (factor j hj).parts ->
      SourceZeroFactorDimensions D aw bw cw
        (part.convexHull_biUnion (fun k => (Q.tube m k).toConvexSpaceBody))
  same_tubes : forall i, (Z i).toTube = T i
  shade_floor : forall i, i ∈ S ->
    (delta : ℝ≥0∞) ^ (10 : ℝ) * volume (T i).carrier <= volume (Z i).shade
  complete_leaves : forall j, forall hj : j ∈ Q.indexSet a,
    Q.cell a j = (factor j hj).parts.biUnion
      (fun part => S.filter (fun i => Q.place m i ∈ part))
  complete_leaf_mass : forall j, forall hj : j ∈ Q.indexSet a,
    (∑ i ∈ Q.cell a j, volume (Z i).shade) =
      ∑ part ∈ (factor j hj).parts,
        ∑ i ∈ S.filter (fun i => Q.place m i ∈ part), volume (Z i).shade

/-- All scalar context inherited by P from the window-refinement lemma. -/
structure SourceZeroWindowSchedule (N M J : Nat) (e : ℝ)
    (eta : Nat -> ℝ) (etaParent : ℝ) : Prop where
  count_bound : 5 <= N
  level_bound : 2 <= M
  source_index_lower : 1 <= J
  source_index_upper : J <= N
  window_exponent : e = (N : ℝ) ^ (-(1 : ℝ) / 2)
  rung_positive : forall j, 1 <= j -> j <= N + 1 -> 0 < eta j
  rung_mono : forall j k, 1 <= j -> j <= k -> k <= N + 1 -> eta j <= eta k
  rung_upper : eta (N + 1) <= e
  rung_step : forall j, 1 <= j -> j <= N -> eta j <= e ^ 2 * eta (j + 1) / 100
  parent_positive : 0 < etaParent
  parent_upper : etaParent <= e ^ 2 * eta (J + 1) / 64
  global_mesh : 512 * (N : ℝ) / eta 1 <= (M : ℝ)
  parent_mesh : 8 / etaParent <= (M : ℝ)

open scoped Classical in
/-- A complete same-Q four-factor output. Analytic rows are conclusions in the
producer, never inputs to the zero-defect floor theorem. -/
structure SourceZeroFourFactors (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3)))
    (a p b : Nat) (beta fineCharge parentCharge outerCharge middleGain : ℝ)
    (loss : ℝ≥0∞) where
  coarse : Finset iota
  parents : Finset iota
  middle : Finset iota
  ja : iota
  jp : iota
  jb : iota
  fineShade : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3))
  middleShade : iota -> ShadedTube (sourceTowerRadius delta M b) (EuclideanSpace ℝ (Fin 3))
  parentShade : iota -> ShadedTube (sourceTowerRadius delta M p) (EuclideanSpace ℝ (Fin 3))
  outerShade : iota -> ShadedTube (sourceTowerRadius delta M a) (EuclideanSpace ℝ (Fin 3))
  coarse_subset : coarse <= Q.indexSet a
  parents_subset : parents <= Q.fibre a p ja
  middle_subset : middle <= Q.fibre p b jp
  coarse_member : ja ∈ coarse
  parent_member : jp ∈ parents
  middle_member : jb ∈ middle
  fine_tubes : forall i, (fineShade i).toTube = T i
  middle_tubes : forall i, (middleShade i).toTube = Q.tube b i
  parent_tubes : forall i, (parentShade i).toTube = Q.tube p i
  outer_tubes : forall i, (outerShade i).toTube = Q.tube a i
  fine_subshade : forall i, (fineShade i).shade <= (Z i).shade
  middle_subshade : forall j, j ∈ middle ->
    (middleShade j).shade <= ⋃ i ∈ Q.cell b j, (Z i).shade
  parent_subshade : forall j, j ∈ parents ->
    (parentShade j).shade <= ⋃ i ∈ Q.cell p j, (Z i).shade
  outer_subshade : forall j, j ∈ coarse ->
    (outerShade j).shade <= ⋃ i ∈ Q.cell a j, (Z i).shade
  card_product : ((Q.cell b jb).card : ℝ≥0∞) * (middle.card : ℝ≥0∞) *
    (parents.card : ℝ≥0∞) * (coarse.card : ℝ≥0∞) <= 16 * (S.card : ℝ≥0∞)
  split : ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <= loss *
    ShadedBody.multiplicity (Q.cell b jb) (fun i => (fineShade i).toShadedBody) *
    ShadedBody.multiplicity middle (fun i => (middleShade i).toShadedBody) *
    ShadedBody.multiplicity parents (fun i => (parentShade i).toShadedBody) *
    ShadedBody.multiplicity coarse (fun i => (outerShade i).toShadedBody)
  fine : ShadedBody.multiplicity (Q.cell b jb) (fun i => (fineShade i).toShadedBody) <=
    (delta : ℝ≥0∞) ^ (-fineCharge) * ((Q.cell b jb).card : ℝ≥0∞) ^ beta
  middle_bound : ShadedBody.multiplicity middle (fun i => (middleShade i).toShadedBody) <=
    (delta : ℝ≥0∞) ^ middleGain * (middle.card : ℝ≥0∞) ^ beta
  parent : ShadedBody.multiplicity parents (fun i => (parentShade i).toShadedBody) <=
    (delta : ℝ≥0∞) ^ (-parentCharge) * (parents.card : ℝ≥0∞) ^ beta
  outer : ShadedBody.multiplicity coarse (fun i => (outerShade i).toShadedBody) <=
    (delta : ℝ≥0∞) ^ (-outerCharge) * (coarse.card : ℝ≥0∞) ^ beta

/-- A returned branch selection records the actual child pair on the fixed Q. -/
structure SourceZeroRetainedState (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3)))
    (R : Finset iota) (Z' : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3)))
    (Q' : SourceThreadedTower R T M C) (loss : ℝ≥0∞) : Prop where
  restriction : SourceTowerRestriction Q Q'
  nonempty : R.Nonempty
  original_tubes : forall i, (Z i).toTube = T i
  same_tubes : forall i, (Z' i).toTube = T i
  subshade : forall i, (Z' i).shade <= (Z i).shade
  mass : (∑ i ∈ S, volume (Z i).shade) <= loss * ∑ i ∈ R, volume (Z' i).shade
  fullness : ShadedBody.fullness' S (fun i => (Z i).toShadedBody) <=
    loss * ShadedBody.fullness' R (fun i => (Z' i).toShadedBody)
  statistics : SourceTowerStatistics Q' Z'

/-- The measured failure of lower concentration at one actual source pair.
These are density inequalities, not an assumed quantized potential drop. -/
structure SourceZeroFailedConcentration (Q : SourceThreadedTower S T M C)
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

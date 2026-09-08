/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceParentData

/-!
# Geometric parent: density transfer and paid capture

Builds the geometric parent on top of `SpineSourceParentData`. `SourceQParentAdmissible`,
`sourceQGenuineParent`, `sourceQTransverseFloor` and `sourceQTransverseParent` select the
parent index; `SourceParentDensityTransfer`, `SourceReparentedFactors` and
`SourceActualParent` package the charge, test-volume and transverse rows. The two theorems
`source_parent_density_from_charge` (charged cells give the maximal-density comparison) and
`source_parent_fill_from_paid_capture` (biased capture gives the charged fill condition,
with the volume-ratio power retained) are the source-`Q` counterparts of the B24 rows.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

universe u

variable {iota : Type u} {delta : ℝ≥0} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace ℝ (Fin 3))} {M C : Nat}

def SourceQParentAdmissible (Q : SourceThreadedTower S T M C)
    (etaParent : ℝ) (a p : Nat) : Prop :=
  forall j, j ∈ Q.indexSet a ->
    Kakeya.maxDensity (Q.fibre a p j) (fun k => (Q.tube p k).toConvexSpaceBody) <=
      (delta : ℝ≥0∞) ^ (-2 * etaParent)

open scoped Classical in
/-- The maximal admissible index before this exact finite source window. -/
noncomputable def sourceQGenuineParent (Q : SourceThreadedTower S T M C)
    (etaParent e : ℝ) (a b : Nat) : Nat :=
  ((Finset.range (M + 1)).filter (fun p => a <= p /\
    (forall m, SourceTowerWindow delta M e a b m -> p < m) /\
    SourceQParentAdmissible Q etaParent a p)).sup id

noncomputable def sourceQTransverseFloor (Q : SourceThreadedTower S T M C)
    {e bias : ℝ} {a b : Nat} (B : SourceJointWindowFactors Q e a b bias) : ℝ≥0∞ :=
  (sourceParentWindow delta M e a b).inf (fun m => (B.middle m : ℝ≥0∞))

noncomputable def sourceQTransverseParent (delta : ℝ≥0) (M : Nat) (B : ℝ≥0∞) : Nat :=
  sInf {q : Nat | q <= M /\ (sourceTowerRadius delta M q : ℝ≥0∞) <= B}

open scoped Classical in
/-- Charge actual q-cells to factors, with the convex test-body comparison needed
for maximal-density transfer. A charge map without the test-volume row is insufficient. -/
structure SourceParentDensityTransfer (Q : SourceThreadedTower S T M C)
    {a m : Nat} {j : iota} {bias : ℝ}
    (B : SourceParentBiasedFactors Q a m j bias) (q : Nat) where
  charge : iota -> Finset iota
  testBody : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) ->
    ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))
  geometryConstant : ℝ≥0
  outerConstant : ℝ≥0∞
  ratioFloor : ℝ≥0
  geometry_one_le : 1 <= geometryConstant
  ratio_positive : 0 < ratioFloor
  ratio_le_one : ratioFloor <= 1
  outer_finite : outerConstant < ⊤
  charge_mem : forall jp, jp ∈ Q.fibre a q j -> charge jp ∈ B.partition.parts
  convex_test_containment : forall V : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)),
    forall jp, jp ∈ Q.fibre a q j -> (Q.tube q jp).toConvexSpaceBody <= V ->
      (charge jp).convexHull_biUnion (fun i => (Q.tube m i).toConvexSpaceBody) <= testBody V
  charge_mass : forall part, part ∈ B.partition.parts ->
    (∑ jp ∈ (Q.fibre a q j).filter (fun jp => charge jp = part), volume (Q.tube q jp).carrier) <=
      (geometryConstant : ℝ≥0∞) *
        volume (part.convexHull_biUnion (fun i => (Q.tube m i).toConvexSpaceBody)).carrier
  test_volume : forall V : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)),
    volume (testBody V).carrier <= (geometryConstant : ℝ≥0∞) * volume V.carrier
  ratio_floor : forall part, part ∈ B.partition.parts ->
    (ratioFloor : ℝ≥0∞) <=
      volume (part.convexHull_biUnion (fun i => (Q.tube m i).toConvexSpaceBody)).carrier /
        volume (ML2Assembly.sourceAffineReference B.normalization).carrier
  outer_constant_eq : outerConstant =
    (nonempty_biasedFactorization.C 3 bias : ℝ≥0∞) * (ratioFloor : ℝ≥0∞) ^ (-bias)
  outer_density : ConvexSpaceBody.IsKatzTao B.partition.parts
    (fun part => part.convexHull_biUnion (fun i => (Q.tube m i).toConvexSpaceBody)) outerConstant

open scoped Classical in
/-- The new p-cell factorization uses its actual cells. Its paid capture retains
the a-to-p volume ratio even when the selected parts are newly factored. -/
structure SourceReparentedFactors (Q : SourceThreadedTower S T M C)
    (a p m : Nat) (j jp : iota) (bias : ℝ)
    (B : SourceParentBiasedFactors Q a m j bias) where
  factor : SourceParentBiasedFactors Q p m jp bias
  old_part : iota -> Finset iota
  old_part_mem : forall i, i ∈ Q.fibre p m jp -> old_part i ∈ B.partition.parts
  old_part_contains : forall i, i ∈ Q.fibre p m jp -> i ∈ old_part i
  inherited_cells : Q.fibre p m jp =
    B.partition.parts.biUnion (fun part => part ∩ Q.fibre p m jp)
  coarse_parent : jp ∈ Q.fibre a p j
  reference_containment : (Q.tube p jp).toConvexSpaceBody <= (Q.tube a j).toConvexSpaceBody
  parent_volume_positive : 0 < volume (Q.tube p jp).carrier
  parent_volume_finite : volume (Q.tube p jp).carrier < ⊤
  coarse_volume_positive : 0 < volume (Q.tube a j).carrier
  coarse_volume_finite : volume (Q.tube a j).carrier < ⊤
  parentVolumeRatio : ℝ≥0∞
  ratio_eq : parentVolumeRatio = volume (Q.tube a j).carrier / volume (Q.tube p jp).carrier
  ratio_one_le : 1 <= parentVolumeRatio
  ratio_finite : parentVolumeRatio < ⊤
  captureConstant : ℝ≥0∞
  constant_eq : captureConstant = (nonempty_biasedFactorization.C 3 bias : ℝ≥0∞) *
    (factor.comparison : ℝ≥0∞) ^ bias * parentVolumeRatio ^ bias
  constant_positive : 0 < captureConstant
  constant_finite : captureConstant < ⊤
  transverseComparison : ℝ≥0
  transverse_comparison_one_le : 1 <= transverseComparison
  transverse_lower : forall part, part ∈ factor.partition.parts ->
    (sourceTowerRadius delta M p : ℝ≥0∞) <= (transverseComparison : ℝ≥0∞) *
      ethickness ℝ
        (part.convexHull_biUnion (fun i => (Q.tube m i).toConvexSpaceBody)).carrier 1
  capture_paid : forall part, part ∈ factor.partition.parts ->
    captureConstant⁻¹ *
      (volume (part.convexHull_biUnion (fun i => (Q.tube m i).toConvexSpaceBody)).carrier /
        volume (Q.tube p jp).carrier) ^ bias *
      Kakeya.maxDensity (Q.fibre p m jp) (fun i => (Q.tube m i).toConvexSpaceBody) <=
      Kakeya.densityIn part (fun i => (Q.tube m i).toConvexSpaceBody)
        (part.convexHull_biUnion (fun i => (Q.tube m i).toConvexSpaceBody))

/-- The geometric parent contains the previously missing coarseness and density
comparisons as outputs. Every transverse inequality refers to an actual used hull. -/
structure SourceActualParent (Q : SourceThreadedTower S T M C)
    {e bias : ℝ} {a b : Nat} (B : SourceJointWindowFactors Q e a b bias)
    (etaParent tau : ℝ) (transverseCap : ℝ≥0) where
  window_nonempty : (sourceParentWindow delta M e a b).Nonempty
  low : Nat
  low_eq : low = (sourceParentWindow delta M e a b).min' window_nonempty
  transverse : Nat
  transverse_eq : transverse = sourceQTransverseParent delta M (sourceQTransverseFloor Q B)
  coarse_transverse : a <= transverse
  transverse_before_window : transverse < low
  transverse_scale : (sourceTowerRadius delta M transverse : ℝ≥0∞) <= sourceQTransverseFloor Q B
  coarse_floor : (sourceTowerRadius delta M (low - 1) : ℝ≥0∞) <= sourceQTransverseFloor Q B
  strict_coarse : forall k, k < a -> sourceQTransverseFloor Q B <
    (sourceTowerRadius delta M k : ℝ≥0∞)
  density_level : Nat
  density_level_in_window : SourceTowerWindow delta M e a b density_level
  transfer : forall j, forall hj : j ∈ Q.indexSet a,
    SourceParentDensityTransfer Q (B.factor density_level density_level_in_window j hj) transverse
  transfer_payment : forall j, forall hj : j ∈ Q.indexSet a,
    ((transfer j hj).geometryConstant : ℝ≥0∞) ^ 2 * (transfer j hj).outerConstant <=
      (delta : ℝ≥0∞) ^ (-2 * etaParent)
  transverse_admissible : SourceQParentAdmissible Q etaParent a transverse
  parent : Nat
  parent_eq : parent = sourceQGenuineParent Q etaParent e a b
  coarse_le_parent : a <= parent
  parent_before_window : forall m, SourceTowerWindow delta M e a b m -> parent < m
  parent_bound : parent <= M
  parent_admissible : SourceQParentAdmissible Q etaParent a parent
  maximal : forall q, a <= q -> q <= M ->
    (forall m, SourceTowerWindow delta M e a b m -> q < m) ->
    SourceQParentAdmissible Q etaParent a q -> q <= parent
  transverse_le_parent : transverse <= parent
  transverse_all_factors : forall m, forall hm : SourceTowerWindow delta M e a b m,
    forall j, forall hj : j ∈ Q.indexSet a, forall part,
    part ∈ (B.factor m hm j hj).partition.parts ->
      (sourceTowerRadius delta M parent : ℝ≥0∞) <= ethickness ℝ
        (part.convexHull_biUnion (fun i => (Q.tube m i).toConvexSpaceBody)).carrier 1
  reparented : forall m, forall hm : SourceTowerWindow delta M e a b m,
    forall j, forall hj : j ∈ Q.indexSet a, forall jp, jp ∈ Q.fibre a parent j ->
      SourceReparentedFactors Q a parent m j jp bias (B.factor m hm j hj)
  reparented_comparison : forall m, forall hm : SourceTowerWindow delta M e a b m,
    forall j, forall hj : j ∈ Q.indexSet a,
    forall jp, forall hjp : jp ∈ Q.fibre a parent j,
      (reparented m hm j hj jp hjp).transverseComparison <= transverseCap
  reparented_transverse : forall m, forall hm : SourceTowerWindow delta M e a b m,
    forall j, forall hj : j ∈ Q.indexSet a,
    forall jp, forall hjp : jp ∈ Q.fibre a parent j, forall part,
    part ∈ (reparented m hm j hj jp hjp).factor.partition.parts ->
      (sourceTowerRadius delta M parent : ℝ≥0∞) <= (transverseCap : ℝ≥0∞) *
        ethickness ℝ
          (part.convexHull_biUnion (fun i => (Q.tube m i).toConvexSpaceBody)).carrier 1
  counted_floor : forall m, SourceTowerWindow delta M e a b m ->
    forall j, j ∈ Q.indexSet a -> forall jp, jp ∈ Q.fibre a parent j ->
      (((sourceTowerRadius delta M a : ℝ) / (sourceTowerRadius delta M m : ℝ)) ^ (tau / 2) *
        (delta : ℝ) ^ (4 * etaParent) / (24 * 300 ^ 9 * (C : ℝ))) *
        ((sourceTowerRadius delta M parent : ℝ) / (sourceTowerRadius delta M m : ℝ)) ^ 2 <=
          ((Q.fibre parent m jp).card : ℝ)
  floor_payment : forall m, SourceTowerWindow delta M e a b m ->
    ((sourceTowerRadius delta M parent : ℝ) / (sourceTowerRadius delta M m : ℝ)) ^
      (4 * (tau / 16)) <=
        ((sourceTowerRadius delta M a : ℝ) / (sourceTowerRadius delta M m : ℝ)) ^ (tau / 2) *
          (delta : ℝ) ^ (4 * etaParent) / (24 * 300 ^ 9 * (C : ℝ))
  floor : forall m, SourceTowerWindow delta M e a b m ->
    forall j, j ∈ Q.indexSet a -> forall jp, jp ∈ Q.fibre a parent j ->
      ((sourceTowerRadius delta M parent : ℝ) / (sourceTowerRadius delta M m : ℝ)) ^
        (2 + 4 * (tau / 16)) <= ((Q.fibre parent m jp).card : ℝ)

end Kakeya.ML2Core

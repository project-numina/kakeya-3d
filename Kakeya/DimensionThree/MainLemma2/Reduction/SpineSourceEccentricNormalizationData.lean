/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceEccentricOuterSplit
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineOuterTubes

/-!
# Data for the eccentric cell normalization

Defines `Kakeya.ML2Core.SourceEccentricCellNormalization`: the simultaneous normalization of
the chosen fine cell of a `SourceEccentricOuterSplit` and its level-`m` parents by one affine
map `spineRescaleUnit`. It records the rescaling situation, the rescaled `fine` shaded tubes at
`sourceEccentricFineScale` and `parent` tubes at `sourceEccentricParentScale`, containment in
the unit ball with `ball_room`, volume comparisons at loss `Cgeom`, the explicit Jacobian, and
the mass/union image identities. It is constructed in `SpineSourceEccentricNormalization` and
consumed by the assigned selection.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

open ML2Reduction

universe u

variable {iota : Type u} {delta : ℝ≥0} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace ℝ (Fin 3))} {M C : Nat}

/-- Simultaneous normalization of the actual chosen fine cell and its actual
m-parents. Unit-core extensions must share enough geometry for literal
fine-parent containment; separate outerTube choices do not supply this. -/
structure SourceEccentricCellNormalization (Q : SourceThreadedTower S T M C)
    {Z : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3))} {a : Nat} {L : ℝ≥0}
    (O : SourceEccentricOuterSplit Q Z a L) (m : Nat)
    (Rnorm : ℝ) (Cgeom cParent : ℝ≥0) where
  radius_lower : 64 <= Rnorm
  radius_pos : 0 < Rnorm
  comparison_one : 1 <= Cgeom
  parent_dilation_one : 1 <= cParent
  ambient_pos : 0 < sourceTowerRadius delta M a
  fine_pos : 0 < sourceEccentricFineScale delta M a
  parent_pos : 0 < sourceEccentricParentScale delta M a m cParent
  fine_situation : Tube.IsRescalingSituation (sourceTowerRadius delta M a) delta
    (sourceEccentricFineScale delta M a) Rnorm 3
  outer_replacement_cost : outerLoss Rnorm <= Cgeom
  affine : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)
  affine_eq : affine = spineRescaleUnit ambient_pos (Q.tube a O.chosen) radius_pos
  fine : iota -> ShadedTube (sourceEccentricFineScale delta M a) (EuclideanSpace ℝ (Fin 3))
  parent : iota -> Tube (sourceEccentricParentScale delta M a m cParent)
    (EuclideanSpace ℝ (Fin 3))
  fine_shade : forall i, i ∈ Q.cell a O.chosen ->
    (fine i).shade = affine '' (O.innerShade i).shade
  fine_image : forall i, i ∈ Q.cell a O.chosen ->
    affine '' (T i).carrier <= (fine i).carrier
  fine_volume : forall i, i ∈ Q.cell a O.chosen ->
    volume (fine i).carrier <= (Cgeom : ℝ≥0∞) * volume (affine '' (T i).carrier)
  parent_image : forall k, k ∈ Q.fibre a m O.chosen ->
    affine '' (Q.tube m k).carrier <= (parent k).carrier
  parent_volume : forall k, k ∈ Q.fibre a m O.chosen ->
    volume (parent k).carrier <= (Cgeom : ℝ≥0∞) * volume (affine '' (Q.tube m k).carrier)
  fine_parent : forall i, i ∈ Q.cell a O.chosen ->
    (fine i).toConvexSpaceBody <= (parent (Q.place m i)).toConvexSpaceBody
  fine_ball : forall i, i ∈ Q.cell a O.chosen ->
    (fine i).carrier <= Metric.closedBall 0 (13 / 16)
  parent_ball : forall k, k ∈ Q.fibre a m O.chosen ->
    (parent k).carrier <= Metric.closedBall 0 1
  ball_room : (13 / 16 : ℝ≥0) + 4 * sourceEccentricParentScale delta M a m cParent <= 1
  jacobian_pos : 0 < affineJacobian affine
  jacobian_finite : affineJacobian affine < (⊤ : ℝ≥0∞)
  jacobian_eq : affineJacobian affine =
    ENNReal.ofReal (4 * Rnorm) ^ (-(3 : ℝ)) *
      (sourceTowerRadius delta M a : ℝ≥0∞) ^ (-(2 : ℝ))
  mass_image : forall q : Finset iota, q <= Q.cell a O.chosen ->
    (∑ i ∈ q, volume (fine i).shade) =
      affineJacobian affine * ∑ i ∈ q, volume (O.innerShade i).shade
  union_image : forall q : Finset iota, q <= Q.cell a O.chosen ->
    volume (⋃ i ∈ q, (fine i).shade) =
      affineJacobian affine * volume (⋃ i ∈ q, (O.innerShade i).shade)
  multiplicity : ShadedBody.multiplicity (Q.cell a O.chosen) (fun i => (fine i).toShadedBody) =
    ShadedBody.multiplicity (Q.cell a O.chosen) (fun i => (O.innerShade i).toShadedBody)
  fullness : ShadedBody.fullness (Q.cell a O.chosen) (fun i => (O.innerShade i).toShadedBody) /
    Cgeom <= ShadedBody.fullness (Q.cell a O.chosen) (fun i => (fine i).toShadedBody)
  maximal_density : Kakeya.maxDensity (Q.cell a O.chosen) (fun i => (fine i).toConvexSpaceBody) <=
    (Cgeom : ℝ≥0∞) * Kakeya.maxDensity (Q.cell a O.chosen) (fun i => (T i).toConvexSpaceBody)
  part_image : forall part : Finset iota, part.Nonempty -> part <= Q.fibre a m O.chosen ->
    affine '' (part.convexHull_biUnion (fun k => (Q.tube m k).toConvexSpaceBody)).carrier <=
      (part.convexHull_biUnion (fun k => (parent k).toConvexSpaceBody)).carrier
  part_jacobian : forall part : Finset iota, part.Nonempty -> part <= Q.fibre a m O.chosen ->
    volume (affine '' (part.convexHull_biUnion (fun k => (Q.tube m k).toConvexSpaceBody)).carrier) =
      affineJacobian affine * volume
        (part.convexHull_biUnion (fun k => (Q.tube m k).toConvexSpaceBody)).carrier
  part_volume_upper : forall part : Finset iota, part.Nonempty -> part <= Q.fibre a m O.chosen ->
    volume (part.convexHull_biUnion (fun k => (parent k).toConvexSpaceBody)).carrier <=
      (Cgeom : ℝ≥0∞) * affineJacobian affine * volume
        (part.convexHull_biUnion (fun k => (Q.tube m k).toConvexSpaceBody)).carrier
  part_thickness_lower : forall part : Finset iota, part.Nonempty ->
    part <= Q.fibre a m O.chosen -> forall rank : Nat, rank = 1 \/ rank = 2 ->
    ethickness ℝ (part.convexHull_biUnion (fun k => (Q.tube m k).toConvexSpaceBody)).carrier rank /
      ((Cgeom : ℝ≥0∞) * (sourceTowerRadius delta M a : ℝ≥0∞)) <=
      ethickness ℝ (part.convexHull_biUnion (fun k => (parent k).toConvexSpaceBody)).carrier rank
  part_thickness_upper : forall part : Finset iota, part.Nonempty ->
    part <= Q.fibre a m O.chosen -> forall rank : Nat, rank = 1 \/ rank = 2 ->
    ethickness ℝ (part.convexHull_biUnion (fun k => (parent k).toConvexSpaceBody)).carrier rank <=
      (Cgeom : ℝ≥0∞) /
        (sourceTowerRadius delta M a : ℝ≥0∞) *
        ethickness ℝ (part.convexHull_biUnion (fun k => (Q.tube m k).toConvexSpaceBody)).carrier rank

end Kakeya.ML2Core

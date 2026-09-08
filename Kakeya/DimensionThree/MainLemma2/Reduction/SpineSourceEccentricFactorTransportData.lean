/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceEccentricAssignedSelection

/-!
# Data for the eccentric factor transport

Defines `Kakeya.ML2Core.SourceEccentricFactorTransport`: the record certifying that the kept
factor parts of an assigned selection transport to a `Kakeya.GlobalPlankFactorization` on the
normalized retained parents. It carries the short/middle thicknesses, the constants `Cw`,
`Czero` bounded by `H`, the identification `parts_eq` of the new parts with old parts
intersected with `parents`, the aspect ratio `short / middle <= H * (aw / bw)`, plank
dimensions, and the two-sided hull-volume comparison through the affine Jacobian. It is built
in `SpineSourceEccentricFactorTransport` and consumed by the Part-B datum.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

universe u

variable {iota : Type u} {delta : ℝ≥0} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace ℝ (Fin 3))} {M C : Nat}

/-- The factorization is on the actual normalized retained parents. Its parts
are precisely the nonempty intersections with the selected old factors.
Thickness, capture and outer KT are all paid, not assumed to survive pruning. -/
structure SourceEccentricFactorTransport (Q : SourceThreadedTower S T M C)
    {Z : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3))}
    {a m : Nat} {Lout : ℝ≥0} {O : SourceEccentricOuterSplit Q Z a Lout}
    {Rnorm : ℝ} {Cgeom cParent : ℝ≥0}
    {Nrm : SourceEccentricCellNormalization Q O m Rnorm Cgeom cParent}
    {etaParent bias : ℝ} {D aw bw cw : ℝ≥0}
    {E : SourceZeroEccentricFactors Q Z a m etaParent bias D aw bw cw}
    {Lsel Ccount : ℝ≥0}
    (P : SourceEccentricAssignedSelection Q O Nrm E Lsel Ccount) (H : ℝ≥0) where
  bound_one : 1 <= H
  short : ℝ≥0
  middle : ℝ≥0
  Cw : ℝ≥0
  Czero : ℝ≥0
  short_pos : 0 < short
  short_le_middle : short <= middle
  middle_le_one : middle <= 1
  parent_le_short : sourceEccentricParentScale delta M a m cParent <= short
  Cw_one : 1 <= Cw
  Czero_one : 1 <= Czero
  Cw_bound : Cw <= H
  Czero_bound : Czero <= H
  factors : Kakeya.GlobalPlankFactorization Cw short middle short_le_middle middle_le_one
    P.parents (fun k => (Nrm.parent k).toConvexSpaceBody) Czero
  factors_nonempty : factors.parts.Nonempty
  parts_eq : factors.parts = P.keptParts.image (fun part => part ∩ P.parents)
  actual_old_part : forall part, part ∈ factors.parts ->
    exists oldPart, oldPart ∈ P.keptParts /\ part = oldPart ∩ P.parents
  aspect : short / middle <= H * (aw / bw)
  dimensions : forall part, part ∈ factors.parts ->
    SourceZeroFactorDimensions H (aw / sourceTowerRadius delta M a)
      (bw / sourceTowerRadius delta M a) 1
      (part.convexHull_biUnion (fun k => (Nrm.parent k).toConvexSpaceBody))
  old_hull_volume : forall part, part ∈ P.keptParts ->
    affineJacobian Nrm.affine * volume
      (part.convexHull_biUnion (fun k => (Q.tube m k).toConvexSpaceBody)).carrier <=
        (H : ℝ≥0∞) * volume
          ((part ∩ P.parents).convexHull_biUnion (fun k => (Nrm.parent k).toConvexSpaceBody)).carrier
  new_hull_volume : forall part, part ∈ P.keptParts ->
    volume ((part ∩ P.parents).convexHull_biUnion
      (fun k => (Nrm.parent k).toConvexSpaceBody)).carrier <=
      (H : ℝ≥0∞) * affineJacobian Nrm.affine * volume
        (part.convexHull_biUnion (fun k => (Q.tube m k).toConvexSpaceBody)).carrier
  original_test_body : forall V : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)),
    exists W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)),
      volume W.carrier <= (H : ℝ≥0∞) / affineJacobian Nrm.affine * volume V.carrier /\
      forall part, part ∈ P.keptParts ->
        (part ∩ P.parents).convexHull_biUnion (fun k => (Nrm.parent k).toConvexSpaceBody) <= V ->
        part.convexHull_biUnion (fun k => (Q.tube m k).toConvexSpaceBody) <= W

end Kakeya.ML2Core

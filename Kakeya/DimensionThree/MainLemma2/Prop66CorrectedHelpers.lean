/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.RepresentativePlankGeometry
public import Kakeya.DimensionThree.Plank.TubeParentPacking

/-!
# Comparable factorizations with plank-shaped parts

`Kakeya.ComparableFactorizationV2` extends `ConvexSpaceBody.Factorization` by requiring every
part's convex hull to be a plank of dimensions `a ≤ b` up to `Cw` (`IsPlankOfDimensions`).
`ComparableFactorizationV2.RepresentativeFamily` records an actual `Plank a b` representative for
each part, whose `Cw`-dilation contains the hull with controlled volume and stays in a fixed
window; `ComparableFactorizationV2.exists_representativeFamily` builds one from
`exists_representativePlankGeometry`.  The remaining lemmas restate the inherited Katz--Tao and
Frostman properties of the parts and of `toFactorFamily`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ConvexSpaceBody Filter ShadedBody Topology
open scoped NNReal ENNReal Real

namespace Kakeya

noncomputable section

/- Quantitative hypotheses for the factorization estimates below. -/
structure ComparableFactorizationV2 {ι : Type*} [DecidableEq ι]
    (a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1)
    (s : Finset ι) (V : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (C₀ Cw : ℝ≥0) extends ConvexSpaceBody.Factorization s V C₀ where
  hCw : 1 ≤ Cw
  outer_dims : ∀ part ∈ parts,
    IsPlankOfDimensions Cw a b (part.convexHull_biUnion V)

theorem ComparableFactorizationV2.part_nonempty
    {ι : Type*} [DecidableEq ι]
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {s : Finset ι} {V : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {C₀ Cw : ℝ≥0} (F : ComparableFactorizationV2 a b hab hb1 s V C₀ Cw)
    {part : Finset ι} (hp : part ∈ F.parts) : part.Nonempty := by
  exact F.toFactorization.nonempty_of_mem_parts hp

theorem ComparableFactorizationV2.part_subset
    {ι : Type*} [DecidableEq ι]
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {s : Finset ι} {V : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {C₀ Cw : ℝ≥0} (F : ComparableFactorizationV2 a b hab hb1 s V C₀ Cw)
    {part : Finset ι} (hp : part ∈ F.parts) : part ⊆ s := by
  exact F.toFactorization.subset hp

/-- Exact representatives for all factor bodies.  Outside `F.parts` the value
is an irrelevant standard plank, so consumers get an ordinary total map. -/
structure ComparableFactorizationV2.RepresentativeFamily
    {ι : Type*} [DecidableEq ι]
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {s : Finset ι} {V : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {C₀ Cw : ℝ≥0} (F : ComparableFactorizationV2 a b hab hb1 s V C₀ Cw) where
  repr : Finset ι → Plank a b hab hb1
  body_subset_dilation : ∀ part ∈ F.parts,
    (part.convexHull_biUnion V).carrier ⊆
      ((repr part).toPrismNDim.dilation Cw).carrier
  dilation_volume_le : ∀ part ∈ F.parts,
    volume (((repr part).toPrismNDim.dilation Cw).carrier : Set _) ≤
      (Prism3D.enclosureVolumeConstant Cw : ℝ≥0∞) *
        volume (part.convexHull_biUnion V).carrier
  dilation_window : ∀ part ∈ F.parts,
    ((repr part).toPrismNDim.dilation Cw).carrier ⊆
      Metric.closedBall 0 ((1 + 6 * Cw : ℝ≥0) : ℝ)

end

end Kakeya

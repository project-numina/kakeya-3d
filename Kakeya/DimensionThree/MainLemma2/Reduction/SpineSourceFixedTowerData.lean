/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.MultiScaleSubmult
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineTwoScale
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineRungWiring
public import Kakeya.DimensionThree.MainLemma2.LineEssDistinct
public import Kakeya.Tube.Rigidity
public import Kakeya.FrostmanTransfer
public import Kakeya.ShadedUniform
public import Kakeya.DimensionThree.MainLemma2.GridRounding
public import Kakeya.StickyKakeya.CrossScale
public import Kakeya.MultiScaleFac.Stopping
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeRoute
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineDichotomyInputs
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCoarseSeam
public import Kakeya.MultiScaleFac.UniformBridgeKT
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineLevelBandDescent
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapePayload
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEveryScale
public import Kakeya.MultiScaleFac.GapsKT
public import Kakeya.GridScale
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCoreWindow
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineParams
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEccentric
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEDMultBound
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCentredHandBack
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSiteClosure

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceFixedMesh

/-!
# The fixed source tower and its geometry, statistics and windows

Defines `Kakeya.ML2Core.SourceThreadedTower`, a tower of `M + 1` levels of tubes at radii
`sourceTowerRadius` with `place`/`parent` maps, containment and bounded containment
multiplicity `C`, together with `SourceThreadedTower.cell` and `.fibre`. The property records
`SourceTowerGeometry` (centred, ED, ball and cardinality rows), `SourceTowerStatistics`
(factor-two regularity of counts, densities and masses), the window predicate
`SourceTowerWindow`, the constant `sourceTowerWindowConstant`, and the dividing window
`SourceTowerDividingWindow` are the shared vocabulary of all `SpineSource*` files on fixed
towers.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube

namespace Kakeya.ML2Core

universe u

variable {iota : Type u} {delta : ℝ≥0} {S : Finset iota}
  {V : iota -> Tube delta (EuclideanSpace ℝ (Fin 3))} {M : Nat}

structure SourceThreadedTower (S : Finset iota)
    (V : iota -> Tube delta (EuclideanSpace ℝ (Fin 3))) (M : Nat) (C : Nat) where
  indexSet : Nat -> Finset iota
  place : Nat -> iota -> iota
  parent : Nat -> iota -> iota
  tube : (k : Nat) -> iota -> Tube (sourceTowerRadius delta M k) (EuclideanSpace ℝ (Fin 3))
  tube_injective : ∀ k, k <= M -> Set.InjOn (tube k) (indexSet k : Set iota)
  place_mem : ∀ k, k <= M -> ∀ i ∈ S, place k i ∈ indexSet k
  place_surjective : ∀ k, k <= M -> ∀ j ∈ indexSet k,
    ∃ i ∈ S, place k i = j
  leaf_containment : ∀ k, k <= M -> ∀ i ∈ S,
    (V i).toConvexSpaceBody <= (tube k (place k i)).toConvexSpaceBody
  parent_mem : ∀ k, k < M -> ∀ j ∈ indexSet (k + 1), parent (k + 1) j ∈ indexSet k
  parent_composition : ∀ k, k < M -> ∀ i ∈ S,
    place k i = parent (k + 1) (place (k + 1) i)
  parent_containment : ∀ k, k < M -> ∀ j ∈ indexSet (k + 1),
    (tube (k + 1) j).toConvexSpaceBody <= (tube k (parent (k + 1) j)).toConvexSpaceBody
  bottom_index : indexSet M = S
  bottom_place : ∀ i ∈ S, place M i = i
  bottom_body : ∀ i ∈ S, (tube M i).toConvexSpaceBody = (V i).toConvexSpaceBody
  containment_multiplicity : ∀ k, k <= M -> ∀ i ∈ S,
    (open scoped Classical in
      ((indexSet k).filter
        (fun j => (V i).toConvexSpaceBody <= (tube k j).toConvexSpaceBody)).card) <= C

open scoped Classical in
noncomputable def SourceThreadedTower.cell {C : Nat} (Q : SourceThreadedTower S V M C)
    (k : Nat) (j : iota) : Finset iota := S.filter (fun i => Q.place k i = j)

open scoped Classical in
noncomputable def SourceThreadedTower.fibre {C : Nat} (Q : SourceThreadedTower S V M C)
    (a b : Nat) (j : iota) : Finset iota := (Q.cell a j).image (Q.place b)

structure SourceTowerGeometry {C : Nat} (Q : SourceThreadedTower S V M C)
    (A0 A1 : Nat) : Prop where
  nonempty : S.Nonempty
  original_centred : ∀ i ∈ S, (V i).IsCentred
  original_ball : ∀ i ∈ S, (V i).carrier <= Metric.closedBall 0 (3 / 4)
  original_ed : Kakeya.VeryNotSticky.IsLineEssDistinct A0 S V
  coarse_centred : ∀ k, k < M -> ∀ j ∈ Q.indexSet k, (Q.tube k j).IsCentred
  coarse_ball : ∀ k, k < M -> ∀ j ∈ Q.indexSet k,
    (Q.tube k j).carrier <= Metric.closedBall 0 3
  coarse_ed : ∀ k, k < M ->
    Kakeya.VeryNotSticky.IsLineEssDistinct A1 (Q.indexSet k) (Q.tube k)
  coarse_card : ∀ k, k < M ->
    ((Q.indexSet k).card : ℝ) <= (32 / (sourceTowerRadius delta M k : ℝ)) ^ 6
  segment_sharing : ∀ k, k < M -> ∀ x y : EuclideanSpace ℝ (Fin 3),
    dist x y = 1 ->
    (open scoped Classical in
      ((Q.indexSet k).filter (fun j => segment ℝ x y <= (Q.tube k j).carrier)).card) <= C

structure SourceTowerStatistics {C : Nat} (Q : SourceThreadedTower S V M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3))) : Prop where
  same_tubes : ∀ i, (Z i).toTube = V i
  descendant_count : ∀ k, k <= M -> ∀ j ∈ Q.indexSet k, ∀ j' ∈ Q.indexSet k,
    ((Q.cell k j).card : ℝ≥0∞) <= 2 * ((Q.cell k j').card : ℝ≥0∞)
  two_level_count : ∀ a b, a < b -> b <= M ->
    ∀ j ∈ Q.indexSet a, ∀ j' ∈ Q.indexSet a,
      ((Q.fibre a b j).card : ℝ≥0∞) <= 2 * ((Q.fibre a b j').card : ℝ≥0∞)
  two_level_density : ∀ a b, a < b -> b <= M ->
    ∀ j ∈ Q.indexSet a, ∀ j' ∈ Q.indexSet a,
      Kakeya.maxDensity (Q.fibre a b j) (fun k => (Q.tube b k).toConvexSpaceBody) <=
        2 * Kakeya.maxDensity (Q.fibre a b j') (fun k => (Q.tube b k).toConvexSpaceBody)
  fibre_mass : ∀ k, k <= M -> ∀ j ∈ Q.indexSet k, ∀ j' ∈ Q.indexSet k,
    (∑ i ∈ Q.cell k j, volume (Z i).shade) <= 2 * (∑ i ∈ Q.cell k j', volume (Z i).shade)

def SourceTowerWindow (delta : ℝ≥0) (M : Nat) (e : ℝ) (a b k : Nat) : Prop :=
  a < k /\ k < b /\
    ((sourceTowerRadius delta M b : ℝ) / (sourceTowerRadius delta M a : ℝ)) ^ (1 - e) <=
      (sourceTowerRadius delta M b : ℝ) / (sourceTowerRadius delta M k : ℝ) /\
    (sourceTowerRadius delta M b : ℝ) / (sourceTowerRadius delta M k : ℝ) <=
      ((sourceTowerRadius delta M b : ℝ) / (sourceTowerRadius delta M a : ℝ)) ^ e

def sourceTowerWindowConstant (C A0 A1 : Nat) : Nat :=
  max (max (300 ^ 9 * C) (625 * max A0 A1)) 3

structure SourceTowerDividingWindow {C : Nat} (Q : SourceThreadedTower S V M C)
    (A0 A1 N : Nat) (eta : Nat -> ℝ) (e : ℝ) (a b J : Nat) : Prop where
  source_index_lower : 1 <= J
  source_index_upper : J <= N
  coarse_lt_fine : a < b
  fine_bound : b <= M
  scale_separation : (sourceTowerRadius delta M b : ℝ) /
    (sourceTowerRadius delta M a : ℝ) <= (delta : ℝ) ^ e
  coarse_density : a > 0 -> ∀ j ∈ Q.indexSet 0,
    Kakeya.maxDensity (Q.fibre 0 a j) (fun k => (Q.tube a k).toConvexSpaceBody) <=
      (sourceTowerWindowConstant C A0 A1 : ℝ≥0∞) ^ N * ENNReal.ofReal
        (((sourceTowerRadius delta M 0 : ℝ) / (sourceTowerRadius delta M a : ℝ)) ^ eta J)
  middle_density : ∀ j ∈ Q.indexSet a,
    Kakeya.maxDensity (Q.fibre a b j) (fun k => (Q.tube b k).toConvexSpaceBody) <=
      ENNReal.ofReal
        (((sourceTowerRadius delta M a : ℝ) / (sourceTowerRadius delta M b : ℝ)) ^ eta J)
  window_lower : ∀ k, SourceTowerWindow delta M e a b k -> ∀ j ∈ Q.indexSet a,
    (1 / 2 : ℝ≥0∞) * ENNReal.ofReal
      (((sourceTowerRadius delta M a : ℝ) / (sourceTowerRadius delta M k : ℝ)) ^ eta (J + 1)) <
      Kakeya.maxDensity (Q.fibre a k j) (fun l => (Q.tube k l).toConvexSpaceBody)

end Kakeya.ML2Core

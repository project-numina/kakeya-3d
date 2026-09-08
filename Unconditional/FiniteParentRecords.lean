/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Unconditional.NuminaJointDefinitions
import Unconditional.ReanchoredParentDegree

/-!
# Finite Parent Records

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace KakeyaLink.JointSelection

open Kakeya.Streamlined Kakeya.Assouad

attribute [local instance] Classical.propDecidable

universe u

variable {I : Type u} {delta : NNReal}

/-- Actual parent covers at finitely many independently specified radii. -/
structure FiniteParentCoverData
    (s : Finset I) (V : I → ShadedTube delta Kakeya.Point3)
    (coordinateCount : ℕ) (H : ENNReal) where
  rho : Fin coordinateCount → NNReal
  parentSet : Fin coordinateCount → Finset I
  assign : Fin coordinateCount → I → I
  parentTube : (coordinate : Fin coordinateCount) → I → Tube (rho coordinate) Kakeya.Point3
  assign_mem : ∀ coordinate, ∀ i ∈ s,
    assign coordinate i ∈ parentSet coordinate
  fine_containment : ∀ coordinate, ∀ i ∈ s,
    (V i).toConvexSpaceBody ≤ (parentTube coordinate (assign coordinate i)).toConvexSpaceBody
  class_ratio : ∀ coordinate,
    ∀ first ∈ s.image (assign coordinate), ∀ second ∈ s.image (assign coordinate),
      ((Tube.coverClass s (assign coordinate) first).card : ENNReal) ≤
        H * ((Tube.coverClass s (assign coordinate) second).card : ENNReal)

variable {s : Finset I} {V : I → ShadedTube delta Kakeya.Point3}
  {coordinateCount : ℕ} {H : ENNReal}

/-- Coarse representatives for the actual finite parent families. -/
structure FiniteCoarseRepresentativeData
    (input : FiniteParentCoverData s V coordinateCount H) where
  representatives : Fin coordinateCount → Finset I
  representatives_subset : ∀ coordinate,
    representatives coordinate ⊆ input.parentSet coordinate
  volume_distinct : ∀ coordinate,
    (representatives coordinate : Set I).Pairwise fun first second =>
      _root_.IsEssentiallyDistinct
        (input.parentTube coordinate first).carrier
        (input.parentTube coordinate second).carrier
  representative : Fin coordinateCount → I → I
  representative_mem : ∀ coordinate, ∀ oldParent ∈ input.parentSet coordinate,
    representative coordinate oldParent ∈ representatives coordinate
  representative_fixed : ∀ coordinate, ∀ parent ∈ representatives coordinate,
    representative coordinate parent = parent
  old_parent_containment : ∀ coordinate,
    ∀ oldParent ∈ input.parentSet coordinate,
      (input.parentTube coordinate oldParent).carrier ⊆
        (Kakeya.Tube.dilate
          (input.parentTube coordinate (representative coordinate oldParent))
          (Kakeya.Tube.tubeOverlapCoreClose.C 3)).carrier

/-- Active representative parents and their actual geometric conflict coloring. -/
structure FiniteActiveParentData
    {input : FiniteParentCoverData s V coordinateCount H}
    (representatives : FiniteCoarseRepresentativeData input)
    {fine : TubeFamily (delta : ℝ)}
    (sourceIndex : Fin fine.card ↪ Fin s.card) (center : Kakeya.Point3)
    (coordinate : Fin coordinateCount) where
  activeParents : Finset I
  activeParents_subset : activeParents ⊆ representatives.representatives coordinate
  assigned : Fin fine.card → Fin activeParents.card
  assigned_surjective : Function.Surjective assigned
  ownership : ∀ index, finsetIndex activeParents (assigned index) =
    representatives.representative coordinate
      (input.assign coordinate (finsetIndex s (sourceIndex index)))
  color : Fin activeParents.card →
    Fin (sharedChildParentDegreeBound (32 * numinaRepresentativeDilation) + 1)
  proper : ∀ first second, first ≠ second →
    (∃ child : Kakeya.DeltaTube (delta : ℝ),
      child.carrier ⊆ wz2PaperCenteredDilatedCarrier 2
        (pureWZ2ReanchoredParentTube (A := numinaRepresentativeDilation) center
          (toDeltaTube (input.parentTube coordinate
            (finsetIndex activeParents first)))) ∧
      child.carrier ⊆ wz2PaperCenteredDilatedCarrier 2
        (pureWZ2ReanchoredParentTube (A := numinaRepresentativeDilation) center
          (toDeltaTube (input.parentTube coordinate
            (finsetIndex activeParents second))))) →
    color first ≠ color second

/-- One strict representative partition retaining the original finite assigned classes. -/
structure JointFiniteGeometricScaleData
    (input : FiniteParentCoverData s V coordinateCount H)
    (representatives : FiniteCoarseRepresentativeData input)
    {density weightLoss : ENNReal}
    (selection : JointLocalizedSelectionData (toTubeShading s V) density weightLoss)
    (coordinate : Fin coordinateCount) (uniformLoss : ENNReal) where
  selectedParents : Finset I
  selectedParents_subset : selectedParents ⊆ representatives.representatives coordinate
  cover : TubeCover selection.localized.family
    (canonicalReanchoredParents numinaRepresentativeDilation selection.center
      (toTubeFamily selectedParents (input.parentTube coordinate)))
  partitioning : WZ2PaperPurePartitioningCover selection.localized.family
    (canonicalReanchoredParents numinaRepresentativeDilation selection.center
      (toTubeFamily selectedParents (input.parentTube coordinate)))
  full_fiber_eq : ∀ parent,
    wz2PaperOrdinaryFullFiberIndices selection.localized.family
        (canonicalReanchoredParents numinaRepresentativeDilation selection.center
          (toTubeFamily selectedParents (input.parentTube coordinate))) parent =
      Finset.univ.filter fun index => cover.parent index = parent
  representative_ownership : ∀ index,
    representatives.representative coordinate
        (input.assign coordinate
          (finsetIndex s (selection.localized.sourceIndex index))) =
      finsetIndex selectedParents (cover.parent index)
  full_fiber_grouping : ∀ parent,
    wz2PaperOrdinaryFullFiberIndices selection.localized.family
        (canonicalReanchoredParents numinaRepresentativeDilation selection.center
          (toTubeFamily selectedParents (input.parentTube coordinate))) parent =
      Finset.univ.filter fun index =>
        representatives.representative coordinate
            (input.assign coordinate
              (finsetIndex s (selection.localized.sourceIndex index))) =
          finsetIndex selectedParents parent
  uniform : cover.IsCUniform uniformLoss
  old_class_uniform : ∀ first second : I,
    0 < (selectedNuminaOldClass selection (input.assign coordinate) first).card →
    0 < (selectedNuminaOldClass selection (input.assign coordinate) second).card →
    ((selectedNuminaOldClass selection (input.assign coordinate) first).card : ENNReal) ≤
      uniformLoss *
        ((selectedNuminaOldClass selection (input.assign coordinate) second).card : ENNReal)
  old_class_mass_ratio : ∀ oldParent : I,
    0 < (selectedNuminaOldClass selection (input.assign coordinate) oldParent).card →
    (∑ index ∈ Tube.coverClass s (input.assign coordinate) oldParent,
      volume (V index).carrier) ≤
      (H * uniformLoss * (weightLoss / density)) *
        ∑ index ∈ selectedNuminaOldClass selection (input.assign coordinate) oldParent,
          volume (selection.localized.family.tube index).carrier
  parent_volume_ratio : ∀ oldParent : I, ∀ parent,
    volume ((canonicalReanchoredParents numinaRepresentativeDilation selection.center
      (toTubeFamily selectedParents (input.parentTube coordinate))).tube parent).carrier ≤
      ENNReal.ofReal ((8 * numinaRepresentativeDilation) ^ 3) *
        volume (input.parentTube coordinate oldParent).carrier

/-- All finite-scale partitions use the same localized family and shading. -/
structure JointFiniteGeometricSelectionData
    (input : FiniteParentCoverData s V coordinateCount H)
    (density weightLoss uniformLoss : ENNReal) where
  representatives : FiniteCoarseRepresentativeData input
  selection : JointLocalizedSelectionData (toTubeShading s V) density weightLoss
  atScale : ∀ coordinate,
    JointFiniteGeometricScaleData input representatives selection coordinate uniformLoss

end KakeyaLink.JointSelection

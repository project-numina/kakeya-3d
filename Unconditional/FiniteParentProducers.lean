/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Unconditional.FiniteParentRecords
import Unconditional.NuminaReanchoredGeometry

/-!
# Finite Parent Producers

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

open MeasureTheory

namespace KakeyaLink.JointSelection

open Kakeya.Streamlined Kakeya.Assouad

universe u

/-- Maximal volume-distinct representatives for the supplied finite parent families. -/
theorem exists_finiteCoarseRepresentativeData
    {I : Type u} {delta : NNReal} {s : Finset I}
    {V : I → ShadedTube delta Kakeya.Point3} {coordinateCount : ℕ} {H : ENNReal}
    (input : FiniteParentCoverData s V coordinateCount H)
    (hrho : ∀ coordinate, 0 < input.rho coordinate)
    (hrhoOne : ∀ coordinate, input.rho coordinate ≤ 1) :
    Nonempty (FiniteCoarseRepresentativeData input) := by
  classical
  have hgeometry (coordinate : Fin coordinateCount) :
      ∃ representatives : Finset I,
        representatives ⊆ input.parentSet coordinate ∧
        (representatives : Set I).Pairwise (fun first second =>
          IsEssentiallyDistinct
            (input.parentTube coordinate first).carrier
            (input.parentTube coordinate second).carrier) ∧
        (∀ oldParent ∈ input.parentSet coordinate,
          ∃ parent ∈ representatives,
            (input.parentTube coordinate oldParent).carrier ⊆
              (Kakeya.Tube.dilate (input.parentTube coordinate parent)
                (Kakeya.Tube.tubeOverlapCoreClose.C 3)).carrier) := by
    obtain ⟨representatives, hsub, hpair, hmax⟩ :=
      Kakeya.Tube.exists_maximal_essDistinct
        (input.parentSet coordinate) (input.parentTube coordinate)
    refine ⟨representatives, hsub, hpair, ?_⟩
    intro oldParent holdParent
    by_cases hretained : oldParent ∈ representatives
    · exact ⟨oldParent, hretained,
        Tube.subset_dilate _ (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C 3).le⟩
    · obtain ⟨parent, hparent, hnot⟩ := hmax oldParent holdParent hretained
      refine ⟨parent, hparent, ?_⟩
      have hcontain := Kakeya.Tube.tubeOverlapCoreClose
        (hrho coordinate) (hrhoOne coordinate)
        (input.parentTube coordinate parent)
        (input.parentTube coordinate oldParent)
        (lt_of_le_of_lt (mul_le_mul' le_rfl (le_max_left _ _)) (lt_of_not_ge hnot))
      simpa [Kakeya.Point3] using hcontain
  choose representatives hsubset hdistinct hcover using hgeometry
  let representative (coordinate : Fin coordinateCount) (oldParent : I) : I :=
    if oldParent ∈ representatives coordinate then oldParent
    else if hparent : oldParent ∈ input.parentSet coordinate then
      Classical.choose (hcover coordinate oldParent hparent)
    else oldParent
  refine ⟨{
    representatives := representatives
    representatives_subset := hsubset
    volume_distinct := hdistinct
    representative := representative
    representative_mem := ?_
    representative_fixed := ?_
    old_parent_containment := ?_
  }⟩
  · intro coordinate oldParent hparent
    by_cases hretained : oldParent ∈ representatives coordinate
    · simp [representative, hretained]
    · simpa [representative, hretained, hparent] using
        (Classical.choose_spec (hcover coordinate oldParent hparent)).1
  · intro coordinate parent hparent
    simp [representative, hparent]
  · intro coordinate oldParent hparent
    by_cases hretained : oldParent ∈ representatives coordinate
    · simpa [representative, hretained] using
        Tube.subset_dilate (input.parentTube coordinate oldParent)
          (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C 3).le
    · simpa [representative, hretained, hparent] using
        (Classical.choose_spec (hcover coordinate oldParent hparent)).2

/-- Actual active representative parents with the existing common-child conflict coloring. -/
theorem exists_finiteActiveParentData
    {I : Type u} {delta : NNReal} {s : Finset I}
    {V : I → ShadedTube delta Kakeya.Point3} {coordinateCount : ℕ} {H : ENNReal}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (input : FiniteParentCoverData s V coordinateCount H)
    (representatives : FiniteCoarseRepresentativeData input)
    {selected : TubeSubfamily (toTubeFamily s (fun i => (V i).toTube))}
    {center : Kakeya.Point3}
    (localized : PureWZ2LocalizedReanchoringData (toTubeShading s V) selected center (1 / 4))
    (hpositive : ∀ i, 0 < volume (localized.shading.carrier i))
    (coordinate : Fin coordinateCount)
    (hdeltaScale : delta ≤ input.rho coordinate)
    (hsmall : (input.rho coordinate : ℝ) ≤
      1 / (200 * (32 * numinaRepresentativeDilation))) :
    Nonempty (FiniteActiveParentData representatives localized.sourceIndex center coordinate) := by
  classical
  let group : Fin localized.family.card → I := fun index =>
    representatives.representative coordinate
      (input.assign coordinate (finsetIndex s (localized.sourceIndex index)))
  let activeParents := Finset.univ.image group
  let assigned (index : Fin localized.family.card) : Fin activeParents.card :=
    activeParents.equivFin ⟨group index, Finset.mem_image_of_mem group (Finset.mem_univ index)⟩
  have ownership (index : Fin localized.family.card) :
      finsetIndex activeParents (assigned index) = group index := by
    simp [assigned, finsetIndex]
  have surjective : Function.Surjective assigned := by
    intro parent
    obtain ⟨index, _, hindex⟩ := Finset.mem_image.mp (finsetIndex_mem activeParents parent)
    exact ⟨index, finsetIndex_injective activeParents ((ownership index).trans hindex)⟩
  have active_subset : activeParents ⊆ representatives.representatives coordinate := by
    intro parent hparent
    obtain ⟨index, _, rfl⟩ := Finset.mem_image.mp hparent
    exact representatives.representative_mem coordinate _
      (input.assign_mem coordinate _ (finsetIndex_mem s _))
  let parents := toTubeFamily activeParents (input.parentTube coordinate)
  have distinct : parents.IsEssentiallyDistinct := by
    rw [toTubeFamily_isEssentiallyDistinct_iff]
    exact (representatives.volume_distinct coordinate).mono active_subset
  have hA : 1 ≤ numinaRepresentativeDilation :=
    (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C 3).le
  have hrho : (0 : ℝ) < input.rho coordinate := by
    exact_mod_cast lt_of_lt_of_le hdelta hdeltaScale
  have hrhoOne : (input.rho coordinate : ℝ) ≤ 1 := by
    have hden : 1 ≤ 200 * (32 * numinaRepresentativeDilation) := by nlinarith
    exact hsmall.trans ((div_le_one (by linarith)).2 hden)
  have shiftBound : ∀ parent : Fin parents.card,
      |pureWZ2AxialShift center (parents.tube parent)| ≤ 4 * numinaRepresentativeDilation := by
    intro parent
    obtain ⟨index, rfl⟩ := surjective parent
    obtain ⟨point, hpoint⟩ := MeasureTheory.nonempty_of_measure_ne_zero (hpositive index).ne'
    rw [localized.shading_carrier] at hpoint
    have hcontains :
        ((toTubeFamily s (fun i => (V i).toTube)).tube (localized.sourceIndex index)).carrier ⊆
          wz2PaperCenteredDilatedCarrier numinaRepresentativeDilation (parents.tube (assigned index)) := by
      change (toDeltaTube (V (finsetIndex s (localized.sourceIndex index))).toTube).carrier ⊆
        wz2PaperCenteredDilatedCarrier numinaRepresentativeDilation
          (toDeltaTube (input.parentTube coordinate
            (finsetIndex activeParents (assigned index))))
      rw [ownership, toDeltaTube_centeredDilatedCarrier, toDeltaTube_carrier]
      exact (input.fine_containment coordinate _ (finsetIndex_mem s _)).trans
        (representatives.old_parent_containment coordinate _
          (input.assign_mem coordinate _ (finsetIndex_mem s _)))
    exact active_parent_axialShift_le_four (by exact_mod_cast hdelta) hrho hA
      (by exact_mod_cast hdeltaOne) hrhoOne
      (by norm_num) ((toTubeShading s V).subset_body _ hpoint.1) hpoint.2 hcontains
  obtain ⟨color, proper⟩ := reanchored_parent_coloring (by exact_mod_cast hdelta) hrho hA hsmall
    (by exact_mod_cast hdeltaScale) distinct center shiftBound
  exact ⟨⟨activeParents, active_subset, assigned, surjective, ownership, color, proper⟩⟩

end KakeyaLink.JointSelection

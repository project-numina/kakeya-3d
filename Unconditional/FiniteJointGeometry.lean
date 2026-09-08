/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Unconditional.FiniteParentRecords
import Unconditional.FiniteParentProducers
import Unconditional.NuminaJointCore
import Unconditional.SelectionPolylog
import Unconditional.SpatialLocalization

/-!
# Finite Joint Geometry

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

private theorem finite_selected_old_class_mass_ratio
    {I : Type*} {delta : NNReal} {s : Finset I}
    {V : I → ShadedTube delta Kakeya.Point3} {coordinateCount : ℕ} {H : ENNReal}
    (input : FiniteParentCoverData s V coordinateCount H)
    (coordinate : Fin coordinateCount)
    {density weightLoss uniformLoss : ENNReal}
    (selection : JointLocalizedSelectionData (toTubeShading s V) density weightLoss)
    (hnew : ∀ first second : I,
      0 < (selectedNuminaOldClass selection (input.assign coordinate) first).card →
      0 < (selectedNuminaOldClass selection (input.assign coordinate) second).card →
      ((selectedNuminaOldClass selection (input.assign coordinate) first).card : ENNReal) ≤
        uniformLoss *
          ((selectedNuminaOldClass selection (input.assign coordinate) second).card :
            ENNReal)) :
    ∀ oldParent : I,
      0 < (selectedNuminaOldClass selection (input.assign coordinate) oldParent).card →
      (∑ index ∈ Tube.coverClass s (input.assign coordinate) oldParent,
        volume (V index).carrier) ≤
        (H * uniformLoss * (weightLoss / density)) *
          ∑ index ∈ selectedNuminaOldClass selection (input.assign coordinate) oldParent,
            volume (selection.localized.family.tube index).carrier := by
  classical
  intro oldParent holdParent
  let parent := fun index : Fin selection.localized.family.card =>
    input.assign coordinate (finsetIndex s (selection.localized.sourceIndex index))
  let parents : Finset I := Finset.univ.image parent
  have parent_pos (p : I) (hp : p ∈ parents) :
      0 < (selectedNuminaOldClass selection (input.assign coordinate) p).card := by
    obtain ⟨index, _, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.card_pos.mpr ⟨index, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  have parent_mem_source (p : I) (hp : p ∈ parents) :
      p ∈ s.image (input.assign coordinate) := by
    obtain ⟨index, _, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_image_of_mem _ (finsetIndex_mem s _)
  obtain ⟨reference, hreference⟩ := Finset.card_pos.mp holdParent
  have holdmem : oldParent ∈ parents := by
    exact Finset.mem_image.mpr
      ⟨reference, Finset.mem_univ _, (Finset.mem_filter.mp hreference).2⟩
  letI : Nonempty parents := ⟨⟨oldParent, holdmem⟩⟩
  let unitVolume := volume (selection.localized.family.tube reference).carrier
  have source_volume (i : I) : volume (V i).carrier = unitVolume := by
    exact (toDeltaTube_volume (V i).toTube).symm.trans
      (Kakeya.Streamlined.tube_volume_eq (toDeltaTube (V i).toTube)
        (selection.localized.family.tube reference))
  have target_volume (i : Fin selection.localized.family.card) :
      volume (selection.localized.family.tube i).carrier = unitVolume :=
    Kakeya.Streamlined.tube_volume_eq _ _
  let ambient : I → ENNReal := fun p =>
    ∑ i ∈ Tube.coverClass s (input.assign coordinate) p, volume (V i).carrier
  let retained : I → ENNReal := fun p =>
    ∑ i ∈ selectedNuminaOldClass selection (input.assign coordinate) p,
      volume (selection.localized.family.tube i).carrier
  have ambient_eq (p : I) : ambient p =
      ((s.filter fun i => input.assign coordinate i = p).card : ENNReal) * unitVolume := by
    simp only [ambient, source_volume, Finset.sum_const, nsmul_eq_mul, Tube.coverClass]
  have retained_eq (p : I) : retained p =
      ((selectedNuminaOldClass selection (input.assign coordinate) p).card : ENNReal) *
        unitVolume := by
    simp only [retained, target_volume, Finset.sum_const, nsmul_eq_mul]
  have ambient_uniform (p q : parents) :
      ambient p ≤ H * ambient q := by
    rw [ambient_eq, ambient_eq, ← mul_assoc]
    exact mul_le_mul_left (input.class_ratio coordinate
      _ (parent_mem_source _ p.property) _ (parent_mem_source _ q.property)) unitVolume
  have retained_uniform (p q : parents) : retained p ≤ uniformLoss * retained q := by
    rw [retained_eq, retained_eq, ← mul_assoc]
    exact mul_le_mul_left (hnew _ _ (parent_pos _ p.property) (parent_pos _ q.property))
      unitVolume
  have ambient_sum : (∑ p : parents, ambient p) ≤
      (toTubeFamily s (fun i => (V i).toTube)).toBodyFamily.mass := by
    rw [← Finset.sum_subtype parents (fun _ => Iff.rfl) ambient, toTubeFamily_mass]
    change (∑ p ∈ parents, ∑ i ∈ s.filter (fun i => input.assign coordinate i = p),
      volume (V i).carrier) ≤ _
    rw [Finset.sum_fiberwise_eq_sum_filter s parents (input.assign coordinate)
      (fun i => volume (V i).carrier)]
    exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have retained_sum : (∑ p : parents, retained p) =
      selection.localized.family.toBodyFamily.mass := by
    rw [← Finset.sum_subtype parents (fun _ => Iff.rfl) retained]
    change (∑ p ∈ parents, ∑ i ∈ Finset.univ.filter (fun i => parent i = p),
      volume (selection.localized.family.tube i).carrier) = _
    rw [Finset.sum_fiberwise_of_maps_to
      (fun i _ => Finset.mem_image_of_mem parent (Finset.mem_univ i))]
    rfl
  have raw := Kakeya.Assouad.finite_uniform_fiber_ratio
    (fun p : parents => ambient p) (fun p : parents => retained p)
    (H) uniformLoss (weightLoss / density)
    ambient_uniform retained_uniform
    (ambient_sum.trans (by simpa only [retained_sum] using selection.global_mass_ratio))
    ⟨oldParent, holdmem⟩
  simpa only [mul_assoc, mul_left_comm, mul_comm] using raw

private def selectedFiniteRepresentative
    {I : Type*} {delta : NNReal} {s : Finset I}
    {V : I → ShadedTube delta Kakeya.Point3} {coordinateCount : ℕ} {H : ENNReal}
    {input : FiniteParentCoverData s V coordinateCount H}
    (representatives : FiniteCoarseRepresentativeData input)
    {density weightLoss : ENNReal}
    (selection : JointLocalizedSelectionData (toTubeShading s V) density weightLoss)
    (coordinate : Fin coordinateCount) (index : Fin selection.localized.family.card) : I :=
  representatives.representative coordinate
    (input.assign coordinate
      (finsetIndex s (selection.localized.sourceIndex index)))

private theorem finite_scale_of_regularized_selection
    {I : Type*} {delta : NNReal} {s : Finset I}
    {V : I → ShadedTube delta Kakeya.Point3} {coordinateCount : ℕ} {H : ENNReal}
    (hdelta : 0 < delta)
    (input : FiniteParentCoverData s V coordinateCount H)
    (representatives : FiniteCoarseRepresentativeData input)
    {density weightLoss uniformLoss : ENNReal}
    (selection : JointLocalizedSelectionData (toTubeShading s V) density weightLoss)
    (coordinate : Fin coordinateCount)
    (hdeltaScale : delta ≤ input.rho coordinate)
    (hscaleSmall :
      (input.rho coordinate : ℝ) ≤
        1 / (200 * numinaRepresentativeDilation))
    (huniform : 1 ≤ uniformLoss)
    (hnewOld : ∀ first second : I,
      0 < (selectedNuminaOldClass selection
        (input.assign coordinate) first).card →
      0 < (selectedNuminaOldClass selection
        (input.assign coordinate) second).card →
      ((selectedNuminaOldClass selection
        (input.assign coordinate) first).card : ENNReal) ≤
        uniformLoss * ((selectedNuminaOldClass selection
          (input.assign coordinate) second).card : ENNReal))
    (hnewGroup : ∀ first second : I,
      0 < (Finset.univ.filter fun index =>
        selectedFiniteRepresentative representatives selection coordinate index = first).card →
      0 < (Finset.univ.filter fun index =>
        selectedFiniteRepresentative representatives selection coordinate index = second).card →
      ((Finset.univ.filter fun index =>
        selectedFiniteRepresentative representatives selection coordinate index = first).card :
          ENNReal) ≤
        uniformLoss * ((Finset.univ.filter fun index =>
          selectedFiniteRepresentative representatives selection coordinate index = second).card :
            ENNReal))
    (hconflictFree : ∀ first second : Fin selection.localized.family.card,
      selectedFiniteRepresentative representatives selection coordinate first ≠
        selectedFiniteRepresentative representatives selection coordinate second →
      ¬ ∃ child : Kakeya.DeltaTube (delta : ℝ),
        child.carrier ⊆ wz2PaperCenteredDilatedCarrier 2
          (pureWZ2ReanchoredParentTube (A := numinaRepresentativeDilation) selection.center
            (toDeltaTube (input.parentTube coordinate
              (selectedFiniteRepresentative representatives selection coordinate first)))) ∧
        child.carrier ⊆ wz2PaperCenteredDilatedCarrier 2
          (pureWZ2ReanchoredParentTube (A := numinaRepresentativeDilation) selection.center
            (toDeltaTube (input.parentTube coordinate
              (selectedFiniteRepresentative representatives selection coordinate second))))) :
    Nonempty (JointFiniteGeometricScaleData input representatives selection coordinate
      uniformLoss) := by
  classical
  let group := selectedFiniteRepresentative representatives selection coordinate
  let selectedParents : Finset I := Finset.univ.image group
  let assigned (index : Fin selection.localized.family.card) : Fin selectedParents.card :=
    selectedParents.equivFin ⟨group index, Finset.mem_image_of_mem group (Finset.mem_univ index)⟩
  have assigned_eq (index : Fin selection.localized.family.card) :
      finsetIndex selectedParents (assigned index) = group index := by
    simp [assigned, finsetIndex]
  have assigned_surjective : Function.Surjective assigned := by
    intro parent
    obtain ⟨index, _, hindex⟩ := Finset.mem_image.mp (finsetIndex_mem selectedParents parent)
    exact ⟨index, finsetIndex_injective selectedParents ((assigned_eq index).trans hindex)⟩
  have hA : 1 ≤ numinaRepresentativeDilation :=
    (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C 3).le
  let coarse := canonicalReanchoredParents numinaRepresentativeDilation selection.center
    (toTubeFamily selectedParents (input.parentTube coordinate))
  have coarse_eq (parent : Fin selectedParents.card) : coarse.tube parent =
      pureWZ2ReanchoredParentTube (A := numinaRepresentativeDilation) selection.center
        (toDeltaTube (input.parentTube coordinate
          (finsetIndex selectedParents parent))) := rfl
  have nested (index : Fin selection.localized.family.card) :
      (selection.localized.family.tube index).carrier ⊆
        (coarse.tube (assigned index)).carrier := by
    have point_exists : (selection.localized.shading.carrier index).Nonempty := by
      apply Set.nonempty_iff_ne_empty.mpr
      intro hempty
      have hpositive := selection.positive_weights index
      simp only [hempty, measure_empty, lt_self_iff_false] at hpositive
    obtain ⟨point, hpoint⟩ := point_exists
    rw [selection.localized.shading_carrier] at hpoint
    have hsourcePoint := (toTubeShading s V).subset_body _ hpoint.1
    have hsourceParent :
        ((toTubeFamily s (fun i => (V i).toTube)).tube
          (selection.localized.sourceIndex index)).carrier ⊆
        wz2PaperCenteredDilatedCarrier numinaRepresentativeDilation
          (toDeltaTube (input.parentTube coordinate (group index))) := by
      rw [toDeltaTube_centeredDilatedCarrier]
      change (toDeltaTube (V (finsetIndex s (selection.localized.sourceIndex index))).toTube).carrier
        ⊆ _
      rw [toDeltaTube_carrier]
      exact (input.fine_containment coordinate _
        (finsetIndex_mem s _)).trans
        (representatives.old_parent_containment coordinate _
          (input.assign_mem coordinate _ (finsetIndex_mem s _)))
    rw [selection.canonical_tube, coarse_eq, assigned_eq]
    exact pureWZ2_reanchored_complete_parent_containment
      (by exact_mod_cast hdelta)
      (by exact_mod_cast hdelta.trans_le hdeltaScale)
      hA (by exact_mod_cast hdeltaScale) hscaleSmall (by norm_num) le_rfl
      hsourcePoint hpoint.2 hsourceParent
  let cover : TubeCover selection.localized.family coarse :=
    { parent := assigned
      parent_surjective := assigned_surjective
      nested := nested }
  have partitioning : WZ2PaperPurePartitioningCover selection.localized.family coarse := by
    refine ⟨?_, ?_⟩
    · intro index
      exact ⟨assigned index,
        (mem_wz2PaperOrdinaryFullFiberIndices_iff _ _).mpr (nested index)⟩
    · intro first second hdifferent
      apply Finset.disjoint_left.mpr
      intro index hfirst hsecond
      obtain ⟨firstIndex, hfirstIndex⟩ := assigned_surjective first
      obtain ⟨secondIndex, hsecondIndex⟩ := assigned_surjective second
      have hgroupNe : group firstIndex ≠ group secondIndex := by
        intro hequal
        apply hdifferent
        apply finsetIndex_injective selectedParents
        simpa only [← hfirstIndex, ← hsecondIndex, assigned_eq] using hequal
      apply hconflictFree firstIndex secondIndex hgroupNe
      refine ⟨selection.localized.family.tube index, ?_, ?_⟩
      · have h := (mem_wz2PaperOrdinaryDilatedFiberIndices_iff (factor := 2) first index).mp
          hfirst
        simpa only [coarse_eq, ← hfirstIndex, assigned_eq] using h
      · have h := (mem_wz2PaperOrdinaryDilatedFiberIndices_iff (factor := 2) second index).mp
          hsecond
        simpa only [coarse_eq, ← hsecondIndex, assigned_eq] using h
  have fiber_eq (parent : Fin selectedParents.card) :
      wz2PaperOrdinaryFullFiberIndices selection.localized.family coarse parent =
        Finset.univ.filter (fun index => assigned index = parent) :=
    partitioning.fullFiber_eq_assigned (by positivity) assigned nested parent
  have group_fiber_eq (parent : Fin selectedParents.card) :
      Finset.univ.filter (fun index => assigned index = parent) =
        Finset.univ.filter (fun index => group index = finsetIndex selectedParents parent) := by
    apply Finset.filter_congr
    intro index _
    constructor
    · intro h
      simpa only [h] using (assigned_eq index).symm
    · intro h
      exact finsetIndex_injective selectedParents ((assigned_eq index).trans h)
  have group_fiber_pos (parent : Fin selectedParents.card) :
      0 < (Finset.univ.filter fun index =>
        group index = finsetIndex selectedParents parent).card := by
    obtain ⟨index, hindex⟩ := assigned_surjective parent
    apply Finset.card_pos.mpr
    exact ⟨index, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      simpa only [hindex] using (assigned_eq index).symm⟩⟩
  refine ⟨{
    selectedParents := selectedParents
    selectedParents_subset := ?_
    cover := cover
    partitioning := partitioning
    full_fiber_eq := fiber_eq
    representative_ownership := fun index => (assigned_eq index).symm
    full_fiber_grouping := fun parent => (fiber_eq parent).trans (group_fiber_eq parent)
    uniform := ?_
    old_class_uniform := hnewOld
    old_class_mass_ratio :=
      finite_selected_old_class_mass_ratio input coordinate selection hnewOld
    parent_volume_ratio := ?_
  }⟩
  · intro parent hparent
    obtain ⟨index, _, rfl⟩ := Finset.mem_image.mp hparent
    exact representatives.representative_mem coordinate _
      (input.assign_mem coordinate _ (finsetIndex_mem s _))
  · refine ⟨huniform, ?_⟩
    intro first second
    change ((Finset.univ.filter fun index => assigned index = first).card : ENNReal) ≤
      uniformLoss * ((Finset.univ.filter fun index => assigned index = second).card : ENNReal)
    rw [group_fiber_eq, group_fiber_eq]
    exact hnewGroup _ _ (group_fiber_pos first) (group_fiber_pos second)
  · intro oldParent parent
    exact numina_reanchored_parent_volume_ratio numinaRepresentativeDilation hA selection.center
      (input.parentTube coordinate (finsetIndex selectedParents parent))
      (input.parentTube coordinate oldParent)

set_option backward.isDefEq.respectTransparency false in
private theorem exists_finiteJoint_of_positive_localization
    {I : Type*} {delta : NNReal} {s : Finset I}
    {V : I → ShadedTube delta Kakeya.Point3} {coordinateCount : ℕ} {H : ENNReal}
    (hdelta : 0 < delta) (hdeltaSmall : (delta : ℝ) ≤ 1 / 1600)
    (input : FiniteParentCoverData s V coordinateCount H)
    (hdeltaScale : ∀ k, delta ≤ input.rho k)
    (hscaleSmall : ∀ k, (input.rho k : ℝ) ≤
      1 / (200 * (32 * numinaRepresentativeDilation)))
    (representatives : FiniteCoarseRepresentativeData input)
    (hsourceDistinct : (toTubeFamily s (fun i => (V i).toTube)).IsEssentiallyDistinct)
    {firstSelection : TubeSubfamily (toTubeFamily s (fun i => (V i).toTube))}
    {center : Kakeya.Point3}
    (raw : PureWZ2LocalizedReanchoringData (toTubeShading s V) firstSelection center (1 / 4))
    (hcanonical : ∀ i, raw.family.tube i =
      pureWZ2ReanchoredTube center
        ((toTubeFamily s (fun i => (V i).toTube)).tube (raw.sourceIndex i)))
    (hmass : 0 < raw.shading.mass)
    {density weightLoss uniformLoss : ENNReal}
    (hdensity : 0 < density) (hdensityFinite : density ≠ ⊤)
    (hdense : (toTubeShading s V).IsLambdaDense density)
    (spatialLoss : ℕ)
    (hlocal : (toTubeShading s V).mass ≤ spatialLoss * raw.shading.mass)
    (hweightLoss : spatialLoss * numinaJointWeightLoss coordinateCount raw.family.card ≤ weightLoss)
    (huniformOne : 1 ≤ uniformLoss)
    (hdegreeLoss : numinaJointDegreeLoss coordinateCount raw.family.card ≤ uniformLoss)
    (activeData : ∀ k, Nonempty
      (FiniteActiveParentData representatives raw.sourceIndex center k)) :
    Nonempty (JointFiniteGeometricSelectionData input density weightLoss uniformLoss) := by
  classical
  have hdeltaOne : delta ≤ 1 := by exact_mod_cast (show (delta : ℝ) ≤ 1 by linarith)
  let active (k : Fin coordinateCount) := Classical.choice
    (activeData k)
  obtain ⟨fineColor, hfineProper⟩ := coaxial_fine_conflict_coloring
    (by exact_mod_cast hdelta) hdeltaSmall hsourceDistinct raw.sourceIndex raw.axialShift
    (fun i => (raw.direction_eq i).symm) raw.source_base_eq raw.axialShift_bound
  let OldVertex (k : Fin coordinateCount) := Fin (input.parentSet k).card
  let NewVertex (k : Fin coordinateCount) := Fin (active k).activeParents.card
  letI : Fintype (Fin raw.family.card) := Fin.fintype _
  letI : ∀ k, Fintype (OldVertex k) := fun _ => Fin.fintype _
  letI : ∀ k, Fintype (NewVertex k) := fun _ => Fin.fintype _
  letI : ∀ k, DecidableEq (OldVertex k) := fun _ => Classical.decEq _
  letI : ∀ k, DecidableEq (NewVertex k) := fun _ => Classical.decEq _
  let oldParent (k : Fin coordinateCount) (i : Fin raw.family.card) : OldVertex k :=
    (input.parentSet k).equivFin
      ⟨input.assign k (finsetIndex s (raw.sourceIndex i)),
        input.assign_mem k _ (finsetIndex_mem s _)⟩
  have oldParent_eq (k : Fin coordinateCount) (i : Fin raw.family.card) :
      finsetIndex (input.parentSet k) (oldParent k i) =
        input.assign k (finsetIndex s (raw.sourceIndex i)) := by
    simp [oldParent, finsetIndex]
  let newParent (k : Fin coordinateCount) := (active k).assigned
  let parentColor (k : Fin coordinateCount) (i : Fin raw.family.card) :=
    (active k).color (newParent k i)
  obtain ⟨indices, hindices, hfineMono, hparentMono, hselectedPositive,
      hretained, holdUniform, hnewUniform, hband⟩ :=
    exists_paired_parent_selection coordinateCount
      (sharedChildParentDegreeBound 8 + 1)
      (sharedChildParentDegreeBound (32 * numinaRepresentativeDilation) + 1)
      (Nat.succ_pos _) (Nat.succ_pos _) OldVertex NewVertex fineColor parentColor
      oldParent newParent (fun i => volume (raw.shading.carrier i)) hmass
  have hretained' : raw.shading.mass ≤
      numinaJointWeightLoss coordinateCount raw.family.card *
        ∑ i ∈ indices, volume (raw.shading.carrier i) := by
    have hmass_eq : raw.shading.mass =
        ∑ i : Fin raw.family.card, volume (raw.shading.carrier i) := by
      apply Finset.sum_congr
      · ext i
        simp only [Finset.mem_univ]
      · intro i _
        rfl
    rw [hmass_eq]
    simpa only [numinaJointWeightLoss, Fintype.card_fin] using hretained
  have hretainedTotal : (toTubeShading s V).mass ≤
      weightLoss * ∑ i ∈ indices, volume (raw.shading.carrier i) := by
    calc
      _ ≤ spatialLoss * raw.shading.mass := hlocal
      _ ≤ spatialLoss * (numinaJointWeightLoss coordinateCount raw.family.card *
          ∑ i ∈ indices, volume (raw.shading.carrier i)) := mul_le_mul_right hretained' _
      _ = (spatialLoss * numinaJointWeightLoss coordinateCount raw.family.card) *
          ∑ i ∈ indices, volume (raw.shading.carrier i) := (mul_assoc _ _ _).symm
      _ ≤ _ := mul_le_mul_left hweightLoss _
  have hdistinct : WZ2PaperOrdinaryIsEssentiallyDistinct
      (TubeSubfamily.fromFinset raw.family indices).family :=
    paper_distinct_of_monochromatic fineColor hfineProper
      (TubeSubfamily.fromFinset raw.family indices) (fun i j => hfineMono _
        (fromFinset_embedding_mem _ _ i) _ (fromFinset_embedding_mem _ _ j))
  obtain ⟨selection, hcenter, intoRaw, himage, hsourceIndex, htube⟩ :=
    exists_joint_localized_refinement (by exact_mod_cast hdelta.le)
      (by linarith : (delta : ℝ) ≤ 1 / 4) (toTubeShading s V) raw hcanonical indices
      hindices hselectedPositive hdistinct hdensity hdensityFinite hdense hretainedTotal hband
  have intoRaw_mem (i : Fin selection.localized.family.card) : intoRaw i ∈ indices := by
    rw [← himage]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have oldUniform (k : Fin coordinateCount) : ∀ first second : I,
      0 < (selectedNuminaOldClass selection (input.assign k) first).card →
      0 < (selectedNuminaOldClass selection (input.assign k) second).card →
      ((selectedNuminaOldClass selection (input.assign k) first).card :
        ENNReal) ≤ uniformLoss *
          ((selectedNuminaOldClass selection (input.assign k) second).card :
            ENNReal) := by
    apply uniform_fibers_of_injective_label intoRaw indices himage (oldParent k)
      (finsetIndex (input.parentSet k))
      (finsetIndex_injective _) _
    · intro i
      rw [oldParent_eq, hsourceIndex]
    · intro first second hfirst hsecond
      have h := holdUniform k first second (by simpa using hfirst) (by simpa using hsecond)
      have h' : ((indices.filter fun i => oldParent k i = first).card : ENNReal) ≤
          numinaJointDegreeLoss coordinateCount raw.family.card *
            ((indices.filter fun i => oldParent k i = second).card : ENNReal) := by
        simpa only [numinaJointDegreeLoss, Fintype.card_fin] using h
      exact h'.trans (mul_le_mul_left hdegreeLoss _)
  have newLabel_eq (k : Fin coordinateCount) (i : Fin selection.localized.family.card) :
      selectedFiniteRepresentative representatives selection k i =
        finsetIndex (active k).activeParents (newParent k (intoRaw i)) := by
    rw [(active k).ownership]
    simp only [selectedFiniteRepresentative, hsourceIndex]
    rfl
  have newUniform (k : Fin coordinateCount) : ∀ first second : I,
      0 < (Finset.univ.filter fun i =>
        selectedFiniteRepresentative representatives selection k i = first).card →
      0 < (Finset.univ.filter fun i =>
        selectedFiniteRepresentative representatives selection k i = second).card →
      ((Finset.univ.filter fun i =>
        selectedFiniteRepresentative representatives selection k i = first).card : ENNReal) ≤
        uniformLoss * ((Finset.univ.filter fun i =>
          selectedFiniteRepresentative representatives selection k i = second).card : ENNReal) := by
    apply uniform_fibers_of_injective_label intoRaw indices himage (newParent k)
      (finsetIndex (active k).activeParents) (finsetIndex_injective _)
      (selectedFiniteRepresentative representatives selection k) (newLabel_eq k)
    intro first second hfirst hsecond
    have h := hnewUniform k first second (by simpa using hfirst) (by simpa using hsecond)
    have h' : ((indices.filter fun i => newParent k i = first).card : ENNReal) ≤
        numinaJointDegreeLoss coordinateCount raw.family.card *
          ((indices.filter fun i => newParent k i = second).card : ENNReal) := by
      simpa only [numinaJointDegreeLoss, Fintype.card_fin] using h
    exact h'.trans (mul_le_mul_left hdegreeLoss _)
  have atScale (k : Fin coordinateCount) :
      Nonempty (JointFiniteGeometricScaleData input representatives selection k uniformLoss) := by
    have hscale : (input.rho k : ℝ) ≤
        1 / (200 * numinaRepresentativeDilation) := by
      have hA : 1 ≤ numinaRepresentativeDilation :=
        (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C 3).le
      exact (hscaleSmall k).trans (by
        apply one_div_le_one_div_of_le (by linarith)
        nlinarith)
    apply finite_scale_of_regularized_selection hdelta input representatives selection k
      (hdeltaScale k) hscale huniformOne (oldUniform k) (newUniform k)
    intro first second hdifferent hconflict
    have hne : newParent k (intoRaw first) ≠ newParent k (intoRaw second) := by
      intro heq
      apply hdifferent
      rw [newLabel_eq, newLabel_eq, heq]
    apply (active k).proper _ _ hne _
      (hparentMono k _ (intoRaw_mem first) _ (intoRaw_mem second))
    simpa only [hcenter, newLabel_eq] using hconflict
  exact ⟨⟨representatives, selection, fun k => Classical.choice (atScale k)⟩⟩

/-- One common localized selection and strict partitions at the supplied finite radii. -/
theorem exists_jointFiniteGeometricSelection (coordinateCount : ℕ) :
    ∃ logExponent : ℕ, ∃ delta0 : ℝ,
      0 < delta0 ∧ delta0 ≤ 1 / 4 ∧
      ∀ {delta : NNReal}, 0 < delta → (delta : ℝ) ≤ delta0 →
      ∀ {I : Type u} (s : Finset I) (V : I → ShadedTube delta Kakeya.Point3),
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1) →
        (toTubeFamily s (fun i => (V i).toTube)).IsEssentiallyDistinct →
      ∀ {H : ENNReal} (input : FiniteParentCoverData s V coordinateCount H),
      ∀ density : ENNReal, 0 < density → density ≠ ⊤ →
        (toTubeShading s V).IsLambdaDense density → s.Nonempty →
        (∀ k, delta ≤ input.rho k) →
        (∀ k, (input.rho k : ℝ) ≤
          1 / (200 * (32 * numinaRepresentativeDilation))) →
        Nonempty (JointFiniteGeometricSelectionData input density
          (geometricSelectionLoss (delta : ℝ) logExponent)
          (geometricSelectionLoss (delta : ℝ) logExponent)) := by
  obtain ⟨spatialLoss, hspatialLoss, hspatial⟩ :=
    exists_fixed_ball_mass_localization 1 le_rfl
  obtain ⟨logExponent, delta0, hdelta0, hdelta0Small, henvelope⟩ :=
    exists_selection_polylog_envelope 1 le_rfl (coordinateCount + coordinateCount)
      spatialLoss (sharedChildParentDegreeBound 8 + 1)
      (sharedChildParentDegreeBound (32 * numinaRepresentativeDilation) + 1)
      hspatialLoss (Nat.succ_pos _) (Nat.succ_pos _) 1 (by norm_num)
  refine ⟨logExponent, delta0, hdelta0, hdelta0Small.trans (by norm_num), ?_⟩
  intro delta hdelta hsmall I s V hball hdistinct H input density hdensity
    hdensityFinite hdense hs hdeltaScale hscaleSmall
  have hd : (0 : ℝ) < delta := hdelta
  have hdSmall : (delta : ℝ) ≤ 1 / 1600 := hsmall.trans hdelta0Small
  have hdOne : delta ≤ 1 := by exact_mod_cast (show (delta : ℝ) ≤ 1 by linarith)
  let source := toTubeFamily s (fun i => (V i).toTube)
  let sourceShading := toTubeShading s V
  have hsourceBall : PureWZ2FixedBallSupport source 1 := by
    intro i
    change (toDeltaTube (V (finsetIndex s i)).toTube).carrier ⊆ _
    rw [toDeltaTube_carrier]
    exact hball _ (finsetIndex_mem _ _)
  have hcard : (source.card : ℝ) ≤ (37 * (1 : ℝ)) ^ 6 * (delta : ℝ) ^ (-6 : ℝ) :=
    essentially_distinct_card_bound_fixed_ball hd (by exact_mod_cast hdOne)
      (by linarith) le_rfl hsourceBall hdistinct
  have hsourceMass : 0 < sourceShading.mass :=
    (ENNReal.mul_pos_iff.mpr ⟨hdensity, toTubeFamily_mass_pos hdelta _ _ hs⟩).trans_le hdense
  obtain ⟨center, hlocal⟩ := hspatial hsourceBall sourceShading
  obtain ⟨firstSelection, raw, hrawCard, _, hcanonical, hpositive, hrawMass⟩ :=
    exists_positive_localized_reanchoring hd.le (by linarith) sourceShading center
  have hlocal' : sourceShading.mass ≤ spatialLoss * raw.shading.mass := by
    rw [hrawMass]
    exact hlocal
  have hrawPositive : 0 < raw.shading.mass := by
    by_contra! hzero
    have heq : raw.shading.mass = 0 := le_antisymm hzero bot_le
    rw [heq, mul_zero] at hlocal'
    exact hsourceMass.not_ge hlocal'
  have hrawCardBound : (raw.family.card : ℝ) ≤
      (37 * (1 : ℝ)) ^ 6 * (delta : ℝ) ^ (-6 : ℝ) :=
    (by exact_mod_cast hrawCard : (raw.family.card : ℝ) ≤ source.card).trans hcard
  obtain ⟨hone, hweight, hdegree, _⟩ := henvelope hd hsmall raw.family.card hrawCardBound
  have hrho (k : Fin coordinateCount) : 0 < input.rho k :=
    hdelta.trans_le (hdeltaScale k)
  have hrhoOne (k : Fin coordinateCount) : input.rho k ≤ 1 := by
    have hA : 1 ≤ numinaRepresentativeDilation :=
      (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C 3).le
    have hden : 1 ≤ 200 * (32 * numinaRepresentativeDilation) := by nlinarith
    exact_mod_cast (hscaleSmall k).trans ((div_le_one (by linarith)).2 hden)
  obtain ⟨representatives⟩ := exists_finiteCoarseRepresentativeData input hrho hrhoOne
  apply exists_finiteJoint_of_positive_localization hdelta hdSmall input
    hdeltaScale hscaleSmall representatives hdistinct raw hcanonical
    hrawPositive hdensity hdensityFinite hdense spatialLoss hlocal'
  · simpa only [numinaJointWeightLoss, geometricSelectionLoss, mul_assoc] using hweight
  · exact hone
  · exact hdegree
  · intro k
    exact exists_finiteActiveParentData hdelta hdOne input representatives raw hpositive k
      (hdeltaScale k) (hscaleSmall k)

end KakeyaLink.JointSelection

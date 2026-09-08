/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Unconditional.NuminaJointDefinitions
import Unconditional.IndexedSelection
import Unconditional.CoaxialFineColoring

/-!
# Joint Localized Refinement

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace KakeyaLink.JointSelection

open Kakeya.Streamlined Kakeya.Assouad

attribute [local instance] Classical.propDecidable

theorem filter_card_of_embedding_image
    {I J : Type*} [Fintype I] [DecidableEq J]
    (embedding : I ↪ J) (indices : Finset J)
    (himage : Finset.univ.image embedding = indices) (p : J → Prop) :
    (Finset.univ.filter fun i : I => p (embedding i)).card = (indices.filter p).card := by
  classical
  apply Finset.card_bij (fun i _ => embedding i)
  · intro i hi
    refine Finset.mem_filter.mpr ⟨?_, (Finset.mem_filter.mp hi).2⟩
    rw [← himage]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  · intro i _ j _ heq
    exact embedding.injective heq
  · intro j hj
    have hmem := (Finset.mem_filter.mp hj).1
    rw [← himage] at hmem
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hmem
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩, rfl⟩

theorem exists_joint_localized_refinement
    {delta : ℝ} (hdelta : 0 ≤ delta) (hsmall : delta ≤ 1 / 4)
    {source : TubeFamily delta} (sourceShading : TubeShading source)
    {firstSelection : TubeSubfamily source} {center : Kakeya.Point3}
    (raw : PureWZ2LocalizedReanchoringData sourceShading firstSelection center (1 / 4))
    (hcanonical : ∀ i, raw.family.tube i =
      pureWZ2ReanchoredTube center (source.tube (raw.sourceIndex i)))
    (indices : Finset (Fin raw.family.card)) (hindices : indices.Nonempty)
    (hpositive : ∀ i ∈ indices, 0 < volume (raw.shading.carrier i))
    (hdistinct : WZ2PaperOrdinaryIsEssentiallyDistinct
      (TubeSubfamily.fromFinset raw.family indices).family)
    {density weightLoss : ENNReal}
    (hdensity : 0 < density) (hdensityFinite : density ≠ ⊤)
    (hdense : sourceShading.IsLambdaDense density)
    (hretained : sourceShading.mass ≤
      weightLoss * ∑ i ∈ indices, volume (raw.shading.carrier i))
    (hband : ∃ weightLevel : ENNReal, 0 < weightLevel ∧
      ∀ i ∈ indices, weightLevel ≤ volume (raw.shading.carrier i) ∧
        volume (raw.shading.carrier i) ≤ 2 * weightLevel) :
    ∃ selection : JointLocalizedSelectionData sourceShading density weightLoss,
      selection.center = center ∧
      ∃ intoRaw : Fin selection.localized.family.card ↪ Fin raw.family.card,
        Finset.univ.image intoRaw = indices ∧
        (∀ i, selection.localized.sourceIndex i = raw.sourceIndex (intoRaw i)) ∧
        (∀ i, selection.localized.family.tube i = raw.family.tube (intoRaw i)) := by
  classical
  let restricted := TubeSubfamily.fromFinset raw.family indices
  let selected : TubeSubfamily source :=
    { family :=
        { card := indices.card
          tube := fun i => source.tube (raw.sourceIndex (restricted.embedding i)) }
      embedding := restricted.embedding.trans raw.sourceIndex
      tube_eq := fun _ => rfl }
  have selected_positive (i : Fin selected.family.card) :
      0 < volume (sourceShading.carrier (selected.embedding i) ∩
        Metric.closedBall center (1 / 4)) := by
    have h := hpositive _ (fromFinset_embedding_mem raw.family indices i)
    rw [raw.shading_carrier] at h
    exact h
  let localized := pureWZ2LocalizedReanchoring hdelta (by norm_num)
    (by linarith : delta + 1 / 4 ≤ 1 / 2) sourceShading selected center
    (fun i => MeasureTheory.nonempty_of_measure_ne_zero (selected_positive i).ne')
  have local_shade_eq (i : Fin localized.family.card) :
      localized.shading.carrier i = raw.shading.carrier (restricted.embedding i) := by
    rw [localized.shading_carrier, raw.shading_carrier]
    rfl
  have local_tube_eq (i : Fin localized.family.card) :
      localized.family.tube i = raw.family.tube (restricted.embedding i) := by
    exact (hcanonical (restricted.embedding i)).symm
  have family_eq : localized.family = restricted.family := by
    change TubeFamily.mk indices.card _ = TubeFamily.mk indices.card _
    congr 1
    exact funext local_tube_eq
  have local_mass_eq : localized.shading.mass =
      ∑ i ∈ indices, volume (raw.shading.carrier i) := by
    change (∑ i : Fin localized.family.card, volume (localized.shading.carrier i)) = _
    simp only [local_shade_eq]
    exact sum_fromFinset_embedding raw.family indices (fun i => volume (raw.shading.carrier i))
  have shade_le_mass : localized.shading.mass ≤ localized.family.toBodyFamily.mass :=
    Finset.sum_le_sum fun i _ => measure_mono (localized.shading.subset_body i)
  have retained_mass : sourceShading.mass ≤ weightLoss * localized.shading.mass := by
    rw [local_mass_eq]
    exact hretained
  have global_mass_ratio : source.toBodyFamily.mass ≤
      (weightLoss / density) * localized.family.toBodyFamily.mass := by
    rw [show (weightLoss / density) * localized.family.toBodyFamily.mass =
        (weightLoss * localized.family.toBodyFamily.mass) / density by
      simp only [div_eq_mul_inv]
      ac_rfl]
    apply (ENNReal.le_div_iff_mul_le (Or.inl hdensity.ne') (Or.inl hdensityFinite)).mpr
    have h := hdense.trans (retained_mass.trans (mul_le_mul_right shade_le_mass weightLoss))
    simpa only [mul_comm density] using h
  let selection : JointLocalizedSelectionData sourceShading density weightLoss :=
    { selected := selected
      center := center
      localized := localized
      source_indices_eq := rfl
      canonical_tube := fun _ => rfl
      nonempty := hindices.card_pos
      positive_weights := fun i => by
        rw [local_shade_eq]
        exact hpositive _ (fromFinset_embedding_mem raw.family indices i)
      ordinary_distinct := by rw [family_eq]; exact hdistinct
      retained_mass := retained_mass
      global_mass_ratio := global_mass_ratio
      weight_band := by
        obtain ⟨weightLevel, hweightLevel, hweightBand⟩ := hband
        refine ⟨weightLevel, hweightLevel, ?_⟩
        intro i
        rw [local_shade_eq]
        exact hweightBand _ (fromFinset_embedding_mem raw.family indices i) }
  exact ⟨selection, rfl, restricted.embedding, fromFinset_embedding_image raw.family indices,
    (fun _ => rfl), local_tube_eq⟩

theorem uniform_fibers_of_injective_label
    {I J Vertex Label : Type*} [Fintype I] [DecidableEq J]
    (embedding : I ↪ J) (indices : Finset J)
    (himage : Finset.univ.image embedding = indices)
    (parent : J → Vertex) (label : Vertex → Label) (hinj : Function.Injective label)
    (assigned : I → Label) (hassigned : ∀ i, assigned i = label (parent (embedding i)))
    {loss : ENNReal}
    (huniform : ∀ first second : Vertex,
      0 < (indices.filter fun i => parent i = first).card →
      0 < (indices.filter fun i => parent i = second).card →
      ((indices.filter fun i => parent i = first).card : ENNReal) ≤
        loss * ((indices.filter fun i => parent i = second).card : ENNReal)) :
    ∀ first second : Label,
      0 < (Finset.univ.filter fun i => assigned i = first).card →
      0 < (Finset.univ.filter fun i => assigned i = second).card →
      ((Finset.univ.filter fun i => assigned i = first).card : ENNReal) ≤
        loss * ((Finset.univ.filter fun i => assigned i = second).card : ENNReal) := by
  classical
  have hcount (vertex : Vertex) :
      (Finset.univ.filter fun i => assigned i = label vertex).card =
        (indices.filter fun i => parent i = vertex).card := by
    simp only [hassigned, hinj.eq_iff]
    exact filter_card_of_embedding_image embedding indices himage (fun i => parent i = vertex)
  intro first second hfirst hsecond
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hfirst
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hsecond
  have hfirst_eq : first = label (parent (embedding i)) :=
    (Finset.mem_filter.mp hi).2.symm.trans (hassigned i)
  have hsecond_eq : second = label (parent (embedding j)) :=
    (Finset.mem_filter.mp hj).2.symm.trans (hassigned j)
  rw [hfirst_eq, hcount] at hfirst ⊢
  rw [hsecond_eq, hcount] at hsecond ⊢
  exact huniform _ _ hfirst hsecond

end KakeyaLink.JointSelection

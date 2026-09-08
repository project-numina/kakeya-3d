/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import MyLeanRepo.Kakeya.Streamlined.TubeRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.Reanchoring

/-!
# Indexed Selection

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace KakeyaLink.JointSelection

open Kakeya.Streamlined Kakeya.Assouad

attribute [local instance] Classical.propDecidable

theorem fromFinset_embedding_image {delta : ℝ} (source : TubeFamily delta)
    (indices : Finset (Fin source.card)) :
    Finset.univ.image (TubeSubfamily.fromFinset source indices).embedding = indices := by
  exact indices.image_orderEmbOfFin_univ rfl

theorem fromFinset_embedding_mem {delta : ℝ} (source : TubeFamily delta)
    (indices : Finset (Fin source.card))
    (i : Fin (TubeSubfamily.fromFinset source indices).family.card) :
    (TubeSubfamily.fromFinset source indices).embedding i ∈ indices := by
  exact indices.orderEmbOfFin_mem rfl i

theorem sum_fromFinset_embedding {delta : ℝ} (source : TubeFamily delta)
    (indices : Finset (Fin source.card)) {M : Type*} [AddCommMonoid M]
    (f : Fin source.card → M) :
    (∑ i : Fin (TubeSubfamily.fromFinset source indices).family.card,
      f ((TubeSubfamily.fromFinset source indices).embedding i)) = ∑ i ∈ indices, f i := by
  calc
    _ = ∑ i ∈ Finset.univ.image (TubeSubfamily.fromFinset source indices).embedding, f i :=
      (Finset.sum_image (fun _ _ _ _ heq =>
        (TubeSubfamily.fromFinset source indices).embedding.injective heq)).symm
    _ = _ := by rw [fromFinset_embedding_image]


theorem exists_positive_localized_reanchoring
    {delta : ℝ} (hdelta : 0 ≤ delta) (hsmall : delta ≤ 1 / 4)
    {source : TubeFamily delta} (sourceShading : TubeShading source)
    (center : Kakeya.Point3) :
    ∃ selected : TubeSubfamily source,
      ∃ localized : PureWZ2LocalizedReanchoringData sourceShading selected center (1 / 4),
        localized.family.card ≤ source.card ∧
        Finset.univ.image localized.sourceIndex = Finset.univ.image selected.embedding ∧
        (∀ i, localized.family.tube i =
          pureWZ2ReanchoredTube center (source.tube (localized.sourceIndex i))) ∧
        (∀ i, 0 < volume (localized.shading.carrier i)) ∧
        localized.shading.mass =
          ∑ i : Fin source.card,
            volume (sourceShading.carrier i ∩ Metric.closedBall center (1 / 4)) := by
  classical
  let weight : Fin source.card → ENNReal := fun i =>
    volume (sourceShading.carrier i ∩ Metric.closedBall center (1 / 4))
  let indices := Finset.univ.filter fun i => 0 < weight i
  let selected := TubeSubfamily.fromFinset source indices
  have hpositive : ∀ i : Fin selected.family.card, 0 < weight (selected.embedding i) := by
    intro i
    exact (Finset.mem_filter.mp (fromFinset_embedding_mem source indices i)).2
  have hnonempty : ∀ i : Fin selected.family.card,
      (sourceShading.carrier (selected.embedding i) ∩
        Metric.closedBall center (1 / 4)).Nonempty := by
    intro i
    exact MeasureTheory.nonempty_of_measure_ne_zero (hpositive i).ne'
  let localized := pureWZ2LocalizedReanchoring hdelta (by norm_num)
    (by linarith : delta + 1 / 4 ≤ 1 / 2) sourceShading selected center hnonempty
  refine ⟨selected, localized, ?_, rfl, (fun _ => rfl), ?_, ?_⟩
  · change indices.card ≤ source.card
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
  · exact hpositive
  · rw [localized.mass_eq]
    change (∑ i : Fin selected.family.card, weight (selected.embedding i)) = ∑ i, weight i
    rw [sum_fromFinset_embedding]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    have hnot : ¬ 0 < weight i := by simpa [indices] using hi
    exact nonpos_iff_eq_zero.mp (le_of_not_gt hnot)

end KakeyaLink.JointSelection

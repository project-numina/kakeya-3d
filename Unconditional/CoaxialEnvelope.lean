/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Unconditional.CoaxialContainment
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperJohnHomotheticEnvelope
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TubeDensityTestNet.GeometricLemmas
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeVolume

/-!
# Coaxial Envelope

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

theorem coaxial_sources_common_convex_envelope
    {delta : ℝ} (deltaPos : 0 < delta)
    {index : Type*} [DecidableEq index]
    (source target : index → Kakeya.DeltaTube delta)
    (shift : index → ℝ)
    (selected : Finset index) (selectedNonempty : selected.Nonempty)
    (directionEq : ∀ i ∈ selected, (source i).direction = (target i).direction)
    (baseEq : ∀ i ∈ selected,
      (source i).base = (target i).base + shift i • (target i).direction)
    (shiftBound : ∀ i ∈ selected, |shift i| ≤ 1)
    (convexSet : Set Point3) (convexSetConvex : Convex ℝ convexSet)
    (targetContained : ∀ i ∈ selected, (target i).carrier ⊆ convexSet) :
    ∃ envelope : Set Point3,
      Convex ℝ envelope ∧
      volume envelope ≤ (212776173 : ENNReal) * volume convexSet ∧
      ∀ i ∈ selected, (source i).carrier ⊆ envelope := by
  let targetUnion : Set Point3 := ⋃ i ∈ selected, (target i).carrier
  let convexBody : Set Point3 := convexHull ℝ targetUnion
  have convexBodyCompact : IsCompact convexBody := by
    exact
      Kakeya.Streamlined.RandomTranslation.isCompact_convexHull_finite_union
        selected (fun i => (target i).carrier)
        (fun i _ =>
          ⟨wz2_paper_ordinary_tube_carrier_compact (target i) deltaPos,
            wz2_paper_ordinary_tube_carrier_convex (target i)⟩)
  have convexBodySubset : convexBody ⊆ convexSet := by
    apply convexHull_min
    · intro point pointMem
      rcases Set.mem_iUnion₂.mp pointMem with ⟨i, iMem, pointMem⟩
      exact targetContained i iMem pointMem
    · exact convexSetConvex
  have targetInBody : ∀ i ∈ selected, (target i).carrier ⊆ convexBody := by
    intro i iMem point pointMem
    exact subset_convexHull ℝ targetUnion
      (Set.mem_iUnion₂.mpr ⟨i, iMem, pointMem⟩)
  have convexBodyInterior : (interior convexBody).Nonempty := by
    rcases selectedNonempty with ⟨i, iMem⟩
    exact
      (Kakeya.Streamlined.RandomTranslation.deltaTube_nonempty_interior
        deltaPos (target i)).mono (interior_mono (targetInBody i iMem))
  have convexBodyIsBody : JohnEllipsoid.IsConvexBody convexBody :=
    ⟨convex_convexHull ℝ targetUnion, convexBodyCompact, convexBodyInterior⟩
  rcases wz2_paper_john_homothetic_envelope convexBody convexBodyIsBody with
    ⟨envelope, envelopeConvex, envelopeVolume, envelopeContains⟩
  refine ⟨envelope, envelopeConvex, ?_, ?_⟩
  · exact envelopeVolume.trans
      (mul_le_mul_right (measure_mono convexBodySubset) (212776173 : ENNReal))
  · intro i iMem
    have midpointMem : wz2PaperTubeMidpoint (target i) ∈ convexBody :=
      targetInBody i iMem
        (wz2_paper_tubeMidpoint_mem_carrier (target i) deltaPos.le)
    exact
      (coaxial_source_carrier_subset_homothety_hundred deltaPos.le
        (source i) (target i) (directionEq i iMem) (baseEq i iMem)
        (shiftBound i iMem)).trans
          ((Set.image_mono (targetInBody i iMem)).trans
            (envelopeContains (wz2PaperTubeMidpoint (target i)) midpointMem))


theorem coaxial_weighted_containedMass_bound
    {delta : ℝ} (deltaPos : 0 < delta)
    {source target : Kakeya.Streamlined.TubeFamily delta}
    (sourceIndex : Fin target.card ↪ Fin source.card)
    (shift : Fin target.card → ℝ)
    (directionEq : ∀ i,
      (source.tube (sourceIndex i)).direction = (target.tube i).direction)
    (baseEq : ∀ i,
      (source.tube (sourceIndex i)).base =
        (target.tube i).base + shift i • (target.tube i).direction)
    (shiftBound : ∀ i, |shift i| ≤ 1)
    {constant weight : ENNReal}
    (sourceMassBound : ∀ convexSet : Set Point3, Convex ℝ convexSet →
      source.toBodyFamily.containedMass convexSet * weight ≤
        constant * volume convexSet) :
    ∀ convexSet : Set Point3, Convex ℝ convexSet →
      target.toBodyFamily.containedMass convexSet * weight ≤
        ((212776173 : ENNReal) * constant) * volume convexSet := by
  intro convexSet convexSetConvex
  let selected := target.toBodyFamily.containedIndices convexSet
  by_cases selectedNonempty : selected.Nonempty
  · obtain ⟨envelope, envelopeConvex, envelopeVolume, sourceContained⟩ :=
      coaxial_sources_common_convex_envelope deltaPos
        (fun i => source.tube (sourceIndex i)) target.tube shift
        selected selectedNonempty
        (fun i _ => directionEq i) (fun i _ => baseEq i)
        (fun i _ => shiftBound i)
        convexSet convexSetConvex
        (fun i iMem =>
          Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff.mp iMem)
    have imageSubset : selected.image sourceIndex ⊆
        source.toBodyFamily.containedIndices envelope := by
      intro i iMem
      rcases Finset.mem_image.mp iMem with ⟨j, jMem, rfl⟩
      exact Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff.mpr
        (sourceContained j jMem)
    have massLe : target.toBodyFamily.containedMass convexSet ≤
        source.toBodyFamily.containedMass envelope := by
      calc
        target.toBodyFamily.containedMass convexSet =
            ∑ i ∈ selected, (source.toBodyFamily.body (sourceIndex i)).volume := by
          apply Finset.sum_congr rfl
          intro i _
          exact Kakeya.Streamlined.tube_volume_eq
            (target.tube i) (source.tube (sourceIndex i))
        _ = ∑ i ∈ selected.image sourceIndex, (source.toBodyFamily.body i).volume := by
          rw [Finset.sum_image sourceIndex.injective.injOn]
          rfl
        _ ≤ source.toBodyFamily.containedMass envelope :=
          Finset.sum_le_sum_of_subset_of_nonneg imageSubset (fun _ _ _ => zero_le)
    calc
      target.toBodyFamily.containedMass convexSet * weight ≤
          source.toBodyFamily.containedMass envelope * weight :=
        mul_le_mul_left massLe weight
      _ ≤ constant * volume envelope := sourceMassBound envelope envelopeConvex
      _ ≤ constant * ((212776173 : ENNReal) * volume convexSet) :=
        mul_le_mul_right envelopeVolume constant
      _ = ((212776173 : ENNReal) * constant) * volume convexSet := by ring
  · have selectedEmpty : selected = ∅ := Finset.not_nonempty_iff_eq_empty.mp selectedNonempty
    change (∑ i ∈ selected, (target.toBodyFamily.body i).volume) * weight ≤ _
    simp [selectedEmpty]


end Kakeya.Assouad

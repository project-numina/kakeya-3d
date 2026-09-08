/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Kakeya.Frostman

/-!
# Merged Class Frostman

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace KakeyaLink.DirectCenteredRoute

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]

theorem frostman_of_fiberwise_same_ambient
    {I : Type v} {J : Type w}
    (source : Finset I) (parent : I -> J) (body : I -> ConvexSpaceBody E)
    (ambient : ConvexSpaceBody E) (constant : ENNReal)
    (hcontained : forall i, i ∈ source -> body i ≤ ambient)
    (hclasses : forall j, j ∈ source.image parent ->
      ConvexSpaceBody.IsFrostmanIn (source.filter (fun i => parent i = j))
        body ambient constant) :
    ConvexSpaceBody.IsFrostmanIn source body ambient constant := by
  classical
  let fiber := fun j => source.filter (fun i => parent i = j)
  have hcover : source ⊆ (source.image parent).biUnion fiber := by
    intro i hi
    exact Finset.mem_biUnion.mpr
      ⟨parent i, Finset.mem_image_of_mem parent hi, Finset.mem_filter.mpr ⟨hi, rfl⟩⟩
  apply ConvexSpaceBody.IsFrostmanIn.of_maxDensity_le
  calc
    Kakeya.maxDensity source body ≤
        ∑ j ∈ source.image parent, Kakeya.maxDensity (fiber j) body :=
      Kakeya.maxDensity_le_sum_of_subset_biUnion body hcover
    _ ≤ ∑ j ∈ source.image parent,
        constant * Kakeya.densityIn (fiber j) body ambient := by
      apply Finset.sum_le_sum
      intro j hj
      exact (hclasses j hj).maxDensity_le_of_carrier_subset
        (fun i hi => hcontained i (Finset.mem_filter.mp hi).1)
    _ = constant * Kakeya.densityIn source body ambient := by
      rw [← Finset.mul_sum, Kakeya.densityIn_of_all_le hcontained]
      congr 1
      calc
        (∑ j ∈ source.image parent, Kakeya.densityIn (fiber j) body ambient) =
            ∑ j ∈ source.image parent,
              (∑ i ∈ fiber j, volume (body i).carrier) / volume ambient.carrier := by
          apply Finset.sum_congr rfl
          intro j _
          exact Kakeya.densityIn_of_all_le
            (fun i hi => hcontained i (Finset.mem_filter.mp hi).1)
        _ = (∑ i ∈ source, volume (body i).carrier) / volume ambient.carrier := by
          simp_rw [div_eq_mul_inv]
          rw [← Finset.sum_mul]
          congr 1
          exact Finset.sum_fiberwise_of_maps_to
            (fun i hi => Finset.mem_image_of_mem parent hi)
            (fun i => volume (body i).carrier)

theorem frostman_merge_equal_volume_anchors
    {I : Type v} {J : Type w}
    (source : Finset I) (parent : I -> J) (body : I -> ConvexSpaceBody E)
    (oldAnchor : J -> ConvexSpaceBody E) (newAnchor : ConvexSpaceBody E)
    (constant anchorVolume : ENNReal) (hvolume : anchorVolume ≠ 0)
    (holdVolume : forall j, j ∈ source.image parent ->
      volume (oldAnchor j).carrier = anchorVolume)
    (holdContained : forall i, i ∈ source -> body i ≤ oldAnchor (parent i))
    (hnewContained : forall i, i ∈ source -> body i ≤ newAnchor)
    (holdFrostman : forall j, j ∈ source.image parent ->
      ConvexSpaceBody.IsFrostmanIn (source.filter (fun i => parent i = j))
        body (oldAnchor j) constant) :
    ConvexSpaceBody.IsFrostmanIn source body newAnchor
      (constant * (volume newAnchor.carrier / anchorVolume)) := by
  classical
  by_cases hnewVolume : volume newAnchor.carrier = 0
  · exact ConvexSpaceBody.IsFrostmanIn.of_volume_eq_zero hnewVolume
  apply frostman_of_fiberwise_same_ambient source parent body newAnchor _ hnewContained
  intro j hj
  have hold : forall i, i ∈ source.filter (fun i => parent i = j) ->
      body i ≤ oldAnchor j := by
    intro i hi
    obtain ⟨hi, hparent⟩ := Finset.mem_filter.mp hi
    simpa only [hparent] using holdContained i hi
  have hnew := fun i (hi : i ∈ source.filter (fun i => parent i = j)) =>
    hnewContained i (Finset.mem_filter.mp hi).1
  have h := (holdFrostman j hj).change_ambient hold hnew
    (by rw [holdVolume j hj]; exact hvolume) hnewVolume
  simpa only [holdVolume j hj] using h

end KakeyaLink.DirectCenteredRoute

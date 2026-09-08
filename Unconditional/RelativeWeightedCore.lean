/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Mathlib

/-!
# Relative Weighted Core

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

open scoped BigOperators Classical

namespace KakeyaLink.DirectCenteredRoute

universe u v w

theorem exists_weighted_fiber_core
    {I : Type u} {K : Type v} {J : K -> Type w}
    (coordinates : Finset K) (parent : forall k, I -> J k)
    (initial : Finset I) (weight : I -> Real)
    (threshold : forall k, J k -> Real)
    (hthreshold : forall k, k ∈ coordinates -> forall j, 0 ≤ threshold k j) :
    exists selected : Finset I,
      selected ⊆ initial ∧
      (forall k, k ∈ coordinates -> forall j, j ∈ selected.image (parent k) ->
        threshold k j ≤ ∑ i ∈ selected.filter (fun i => parent k i = j), weight i) ∧
      (∑ i ∈ initial, weight i) ≤ (∑ i ∈ selected, weight i) +
        ∑ k ∈ coordinates, ∑ j ∈ initial.image (parent k), threshold k j := by
  classical
  let charge (s : Finset I) : Real :=
    ∑ k ∈ coordinates, ∑ j ∈ s.image (parent k), threshold k j
  let score (s : Finset I) : Real := (∑ i ∈ s, weight i) - charge s
  obtain ⟨selected, hselected, hmax⟩ :=
    initial.powerset.exists_max_image score ⟨∅, by simp⟩
  have hsub : selected ⊆ initial := Finset.mem_powerset.mp hselected
  have hcharge (s : Finset I) : 0 ≤ charge s := by
    apply Finset.sum_nonneg
    intro k hk
    exact Finset.sum_nonneg (fun j _ => hthreshold k hk j)
  refine ⟨selected, hsub, ?_, ?_⟩
  · intro k hk j hj
    let fiber := selected.filter fun i => parent k i = j
    let remaining := selected \ fiber
    have hfiber : fiber ⊆ selected := Finset.filter_subset _ _
    have hremaining : remaining ⊆ selected := Finset.sdiff_subset
    have hremImage : remaining.image (parent k) = (selected.image (parent k)).erase j := by
      ext x
      simp only [remaining, fiber, Finset.mem_image, Finset.mem_sdiff,
        Finset.mem_filter, Finset.mem_erase]
      aesop
    have hcoordinate :
        (∑ x ∈ remaining.image (parent k), threshold k x) + threshold k j =
          ∑ x ∈ selected.image (parent k), threshold k x := by
      rw [hremImage]
      exact Finset.sum_erase_add _ _ hj
    have hother :
        (∑ l ∈ coordinates.erase k, ∑ x ∈ remaining.image (parent l), threshold l x) ≤
          ∑ l ∈ coordinates.erase k, ∑ x ∈ selected.image (parent l), threshold l x := by
      apply Finset.sum_le_sum
      intro l hl
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_image hremaining)
      intro x _ _
      exact hthreshold l (Finset.mem_of_mem_erase hl) x
    have hchargeDrop : charge remaining + threshold k j ≤ charge selected := by
      dsimp [charge]
      rw [← Finset.sum_erase_add _ _ hk, ← Finset.sum_erase_add _ _ hk]
      linarith
    have hmass :
        (∑ i ∈ remaining, weight i) + (∑ i ∈ fiber, weight i) =
          ∑ i ∈ selected, weight i := Finset.sum_sdiff hfiber
    have hcompare : score remaining ≤ score selected :=
      hmax remaining (Finset.mem_powerset.mpr (hremaining.trans hsub))
    dsimp [score] at hcompare
    change threshold k j ≤ ∑ i ∈ fiber, weight i
    linarith
  · have hcompare : score initial ≤ score selected :=
      hmax initial (Finset.mem_powerset.mpr (Finset.Subset.refl _))
    dsimp [score] at hcompare
    have hnonneg := hcharge selected
    dsimp [charge] at hcompare hnonneg
    linarith

theorem exists_relative_weighted_fiber_core
    {I : Type u} {K : Type v} {J : K -> Type w}
    (coordinates : Finset K) (parent : forall k, I -> J k)
    (original initial : Finset I) (hinitial : initial ⊆ original)
    (weight : I -> Real) (hweight : forall i, i ∈ original -> 0 ≤ weight i)
    (alpha : Real) (halpha : 0 ≤ alpha) :
    exists selected : Finset I,
      selected ⊆ initial ∧
      (forall k, k ∈ coordinates -> forall j, j ∈ selected.image (parent k) ->
        alpha * (∑ i ∈ original.filter (fun i => parent k i = j), weight i) ≤
          ∑ i ∈ selected.filter (fun i => parent k i = j), weight i) ∧
      (∑ i ∈ initial, weight i) ≤ (∑ i ∈ selected, weight i) +
        (coordinates.card : Real) * alpha * (∑ i ∈ original, weight i) := by
  classical
  let threshold := fun k j =>
    alpha * (∑ i ∈ original.filter (fun i => parent k i = j), weight i)
  have hthreshold : forall k, forall j, 0 ≤ threshold k j := by
    intro k j
    exact mul_nonneg halpha (Finset.sum_nonneg
      (fun i hi => hweight i (Finset.mem_filter.mp hi).1))
  obtain ⟨selected, hsub, hcore, hretained⟩ :=
    exists_weighted_fiber_core coordinates parent initial weight threshold
      (fun k _ j => hthreshold k j)
  refine ⟨selected, hsub, hcore, hretained.trans ?_⟩
  gcongr
  calc
    (∑ k ∈ coordinates, ∑ j ∈ initial.image (parent k), threshold k j) ≤
        ∑ k ∈ coordinates, ∑ j ∈ original.image (parent k), threshold k j := by
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_image hinitial)
      exact fun j _ _ => hthreshold k j
    _ = ∑ _k ∈ coordinates, alpha * (∑ i ∈ original, weight i) := by
      apply Finset.sum_congr rfl
      intro k _
      dsimp only [threshold]
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_fiberwise_of_maps_to
        (fun i hi => Finset.mem_image_of_mem (parent k) hi) weight
    _ = (coordinates.card : Real) * alpha * (∑ i ∈ original, weight i) := by
      simp [mul_assoc]

theorem exists_relative_weighted_fiber_core_half
    {I : Type u} {K : Type v} {J : K -> Type w}
    (coordinates : Finset K) (parent : forall k, I -> J k)
    (original initial : Finset I) (hinitial : initial ⊆ original)
    (weight : I -> Real) (hweight : forall i, i ∈ original -> 0 ≤ weight i)
    (hpositive : 0 < ∑ i ∈ initial, weight i) :
    exists selected : Finset I,
      selected ⊆ initial ∧ selected.Nonempty ∧
      (∑ i ∈ initial, weight i) ≤ 2 * (∑ i ∈ selected, weight i) ∧
      (forall k, k ∈ coordinates -> forall j, j ∈ selected.image (parent k) ->
        ((∑ i ∈ initial, weight i) /
          (2 * ((coordinates.card : Real) + 1) * (∑ i ∈ original, weight i))) *
            (∑ i ∈ original.filter (fun i => parent k i = j), weight i) ≤
          ∑ i ∈ selected.filter (fun i => parent k i = j), weight i) := by
  classical
  let total := ∑ i ∈ original, weight i
  let retained := ∑ i ∈ initial, weight i
  have hretained : 0 < retained := hpositive
  have htotal : 0 < total := hpositive.trans_le
    (Finset.sum_le_sum_of_subset_of_nonneg hinitial (fun i hi _ => hweight i hi))
  let alpha := retained / (2 * ((coordinates.card : Real) + 1) * total)
  have halpha : 0 ≤ alpha := by dsimp [alpha]; positivity
  obtain ⟨selected, hsub, hcore, hmass⟩ :=
    exists_relative_weighted_fiber_core coordinates parent original initial hinitial
      weight hweight alpha halpha
  have hid : 2 * ((coordinates.card : Real) + 1) * alpha * total = retained := by
    dsimp [alpha]
    field_simp
  have hcost : (coordinates.card : Real) * alpha * total ≤ retained / 2 := by
    have hnonneg : 0 ≤ alpha * total := mul_nonneg halpha htotal.le
    nlinarith
  have hhalf : retained ≤ 2 * (∑ i ∈ selected, weight i) := by
    change retained ≤ (∑ i ∈ selected, weight i) +
      (coordinates.card : Real) * alpha * total at hmass
    linarith
  refine ⟨selected, hsub, ?_, hhalf, hcore⟩
  by_contra hempty
  have hzero := Finset.not_nonempty_iff_eq_empty.mp hempty
  simp only [hzero, Finset.sum_empty, mul_zero] at hhalf
  exact (not_le_of_gt hretained) hhalf

end KakeyaLink.DirectCenteredRoute

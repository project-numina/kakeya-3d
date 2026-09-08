/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Mathlib

/-!
# Weighted Tuple Selection

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

open scoped BigOperators Classical

namespace KakeyaLink.DirectCenteredRoute

universe u v

theorem exists_weighted_injective_projection
    {I : Type u} {J : Type v} (source : Finset I) (projection : I -> J)
    (weight : I -> Real) (hsource : source.Nonempty)
    (hweight : forall i, i ∈ source -> 0 ≤ weight i)
    (bound : Nat)
    (hfiber : forall j, (source.filter (fun i => projection i = j)).card ≤ bound) :
    exists selected : Finset I,
      selected ⊆ source ∧ selected.Nonempty ∧ Set.InjOn projection selected ∧
      selected.image projection = source.image projection ∧
      (∑ i ∈ source, weight i) ≤ (bound : Real) * (∑ i ∈ selected, weight i) := by
  classical
  let labels := source.image projection
  let fiber := fun j => source.filter fun i => projection i = j
  have hnonempty : forall j, j ∈ labels -> (fiber j).Nonempty := by
    intro j hj
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hj
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, heq⟩⟩
  let representative := fun j =>
    if hj : j ∈ labels then
      (Finset.exists_max_image (fiber j) weight (hnonempty j hj)).choose
    else hsource.choose
  have hrep : forall j, j ∈ labels -> representative j ∈ fiber j := by
    intro j hj
    simp only [representative, dif_pos hj]
    exact (Finset.exists_max_image (fiber j) weight (hnonempty j hj)).choose_spec.1
  have hrepSource := fun j hj => (Finset.mem_filter.mp (hrep j hj)).1
  have hrepLabel := fun j hj => (Finset.mem_filter.mp (hrep j hj)).2
  have hrepMax : forall j, j ∈ labels -> forall i, i ∈ fiber j ->
      weight i ≤ weight (representative j) := by
    intro j hj i hi
    simp only [representative, dif_pos hj]
    exact (Finset.exists_max_image (fiber j) weight (hnonempty j hj)).choose_spec.2 i hi
  let selected := labels.image representative
  have hsub : selected ⊆ source := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact hrepSource j hj
  have hrepInj : Set.InjOn representative labels := by
    intro j hj j' hj' heq
    have h := congrArg projection heq
    simpa only [hrepLabel j hj, hrepLabel j' hj'] using h
  have hprojInj : Set.InjOn projection selected := by
    intro i hi i' hi' heq
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨j', hj', rfl⟩ := Finset.mem_image.mp hi'
    have hjj : j = j' := by
      simpa only [hrepLabel j hj, hrepLabel j' hj'] using heq
    rw [hjj]
  refine ⟨selected, hsub, (hsource.image projection).image representative,
    hprojInj, ?_, ?_⟩
  · apply Finset.Subset.antisymm (Finset.image_subset_image hsub)
    intro j hj
    exact Finset.mem_image.mpr
      ⟨representative j, Finset.mem_image_of_mem representative hj, hrepLabel j hj⟩
  · have htotal : (∑ j ∈ labels, ∑ i ∈ fiber j, weight i) =
        ∑ i ∈ source, weight i :=
      Finset.sum_fiberwise_of_maps_to
        (fun i hi => Finset.mem_image_of_mem projection hi) weight
    rw [← htotal]
    calc
      (∑ j ∈ labels, ∑ i ∈ fiber j, weight i) ≤
          ∑ j ∈ labels, (bound : Real) * weight (representative j) := by
        apply Finset.sum_le_sum
        intro j hj
        calc
          (∑ i ∈ fiber j, weight i) ≤ ∑ _i ∈ fiber j, weight (representative j) :=
            Finset.sum_le_sum (hrepMax j hj)
          _ = ((fiber j).card : Real) * weight (representative j) := by simp
          _ ≤ (bound : Real) * weight (representative j) := by
            apply mul_le_mul_of_nonneg_right _ (hweight _ (hrepSource j hj))
            exact_mod_cast hfiber j
      _ = (bound : Real) * (∑ i ∈ selected, weight i) := by
        rw [← Finset.mul_sum, Finset.sum_image hrepInj]

theorem joint_label_fiber_card_le
    {I : Type u} {Q : Type v} {m : Nat} {J : Fin m -> Type*}
    (source : Finset I) (fine : I -> Q) (coarse : forall k, I -> J k)
    (bound : Nat)
    (hbound : forall q, forall k,
      ((source.filter (fun i => fine i = q)).image (coarse k)).card ≤ bound)
    (q : Q) :
    ((source.image (fun i => (fine i, fun k => coarse k i))).filter
      (fun a => a.1 = q)).card ≤ bound ^ m := by
  classical
  let atoms := source.image (fun i => (fine i, fun k => coarse k i))
  let fiber := atoms.filter fun a => a.1 = q
  let neighbors := fun k => (source.filter (fun i => fine i = q)).image (coarse k)
  have hinj : Set.InjOn (fun a : Q × (forall k, J k) => a.2) fiber := by
    intro a ha b hb heq
    exact Prod.ext ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm) heq
  have hsub : fiber.image (fun a => a.2) ⊆ Fintype.piFinset neighbors := by
    intro tuple htuple
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp htuple
    obtain ⟨ha, hq⟩ := Finset.mem_filter.mp ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    apply Fintype.mem_piFinset.mpr
    intro k
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hq⟩, rfl⟩
  calc
    fiber.card = (fiber.image (fun a => a.2)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Fintype.piFinset neighbors).card := Finset.card_le_card hsub
    _ = ∏ k, (neighbors k).card := Fintype.card_piFinset neighbors
    _ ≤ ∏ _k : Fin m, bound := Finset.prod_le_prod' (fun k _ => hbound q k)
    _ = bound ^ m := by simp

theorem exists_coherent_joint_fiber_selection
    {I : Type u} {Q : Type v} {m : Nat} {J : Fin m -> Type*}
    (source : Finset I) (hsource : source.Nonempty)
    (fine : I -> Q) (coarse : forall k, I -> J k)
    (bound : Nat)
    (hbound : forall q, forall k,
      ((source.filter (fun i => fine i = q)).image (coarse k)).card ≤ bound) :
    exists selected : Finset I,
      selected ⊆ source ∧ selected.Nonempty ∧
      source.card ≤ bound ^ m * selected.card ∧
      (forall i, i ∈ selected -> forall j, j ∈ selected -> fine i = fine j ->
        forall k, coarse k i = coarse k j) ∧
      (forall i, i ∈ source -> forall j, j ∈ selected -> fine i = fine j ->
        (forall k, coarse k i = coarse k j) -> i ∈ selected) := by
  classical
  let code := fun i => (fine i, fun k => coarse k i)
  let atoms := source.image code
  let weight := fun a => ((source.filter (fun i => code i = a)).card : Real)
  have hcount : forall q, (atoms.filter (fun a => a.1 = q)).card ≤ bound ^ m :=
    joint_label_fiber_card_le source fine coarse bound hbound
  obtain ⟨chosen, hchosen, hchosenNonempty, hinj, _himage, hmass⟩ :=
    exists_weighted_injective_projection atoms Prod.fst weight (hsource.image code)
      (fun _ _ => Nat.cast_nonneg _) (bound ^ m) hcount
  let selected := source.filter fun i => code i ∈ chosen
  have hsub : selected ⊆ source := Finset.filter_subset _ _
  have htotal : (∑ a ∈ atoms, weight a) = (source.card : Real) := by
    simpa [weight] using Finset.sum_fiberwise_of_maps_to
      (fun i hi => Finset.mem_image_of_mem code hi) (fun _ => (1 : Real))
  have hfiber : forall a, a ∈ chosen ->
      selected.filter (fun i => code i = a) = source.filter (fun i => code i = a) := by
    intro a ha
    ext i
    simp only [selected, Finset.mem_filter]
    constructor
    · exact fun hi => ⟨hi.1.1, hi.2⟩
    · intro hi
      exact ⟨⟨hi.1, hi.2 ▸ ha⟩, hi.2⟩
  have hselectedWeight : (∑ a ∈ chosen, weight a) = (selected.card : Real) := by
    calc
      (∑ a ∈ chosen, weight a) =
          ∑ a ∈ chosen, ((selected.filter (fun i => code i = a)).card : Real) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hfiber a ha]
      _ = (selected.card : Real) := by
        simpa using Finset.sum_fiberwise_of_maps_to
          (fun i (hi : i ∈ selected) => (Finset.mem_filter.mp hi).2)
          (fun _ => (1 : Real))
  rw [htotal, hselectedWeight] at hmass
  refine ⟨selected, hsub, ?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := hchosenNonempty
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp (hchosen ha)
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, heq ▸ ha⟩⟩
  · exact_mod_cast hmass
  · intro i hi j hj hfine k
    have hcodes : code i = code j :=
      hinj (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2 hfine
    exact congrFun (congrArg Prod.snd hcodes) k
  · intro i hi j hj hfine hcoarse
    have hcodes : code i = code j := Prod.ext hfine (funext hcoarse)
    exact Finset.mem_filter.mpr ⟨hi, hcodes ▸ (Finset.mem_filter.mp hj).2⟩


theorem exists_descended_coarse_labels
    {I : Type u} {Q : Type v} {K : Type*} {J : K -> Type*}
    (source : Finset I) (hsource : source.Nonempty)
    (fine : I -> Q) (coarse : forall k, I -> J k)
    (hcoherent : forall i, i ∈ source -> forall j, j ∈ source -> fine i = fine j ->
      forall k, coarse k i = coarse k j) :
    exists descended : forall k, Q -> J k,
      forall i, i ∈ source -> forall k, descended k (fine i) = coarse k i := by
  classical
  let descended := fun k => Function.extend (fun i : source => fine i)
    (fun i : source => coarse k i) (fun _ => coarse k hsource.choose)
  refine ⟨descended, ?_⟩
  intro i hi k
  have hfactor : (fun i : source => coarse k i).FactorsThrough
      (fun i : source => fine i) := by
    intro a b hab
    exact hcoherent a a.property b b.property hab k
  exact hfactor.extend_apply (fun _ => coarse k hsource.choose) ⟨i, hi⟩


end KakeyaLink.DirectCenteredRoute

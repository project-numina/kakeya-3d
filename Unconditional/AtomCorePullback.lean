/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Unconditional.RelativeWeightedCore

/-!
# Atom Core Pullback

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

open scoped BigOperators Classical

namespace KakeyaLink.DirectCenteredRoute

universe u v w z

theorem sum_atom_weights_filter
    {I : Type u} {A : Type v} {J : Type w} {M : Type z} [AddCommMonoid M]
    (source : Finset I) (atoms : Finset A) (code : I -> A)
    (parent : A -> J) (weight : I -> M) (j : J) :
    (∑ a ∈ atoms.filter (fun a => parent a = j),
      ∑ i ∈ source.filter (fun i => code i = a), weight i) =
        ∑ i ∈ (source.filter (fun i => code i ∈ atoms)).filter
          (fun i => parent (code i) = j), weight i := by
  classical
  calc
    _ = ∑ i ∈ source.filter (fun i => code i ∈ atoms.filter (fun a => parent a = j)),
        weight i := Finset.sum_fiberwise_eq_sum_filter source
          (atoms.filter (fun a => parent a = j)) code weight
    _ = _ := by
      apply Finset.sum_congr
      · ext i
        simp [and_assoc]
      · intro _ _
        rfl

theorem exists_relative_atom_core_pullback
    {I : Type u} {A : Type v} {K : Type w} {J : K -> Type z}
    (source : Finset I) (code : I -> A)
    (coordinates : Finset K) (parent : forall k, A -> J k)
    (initial : Finset A) (hinitial : initial ⊆ source.image code)
    (weight : I -> Real) (hweight : forall i, i ∈ source -> 0 ≤ weight i)
    (hpositive : 0 < ∑ i ∈ source.filter (fun i => code i ∈ initial), weight i) :
    exists selected : Finset A,
      selected ⊆ initial ∧ selected.Nonempty ∧
      (source.filter (fun i => code i ∈ selected)).Nonempty ∧
      (∑ i ∈ source.filter (fun i => code i ∈ initial), weight i) ≤
        2 * (∑ i ∈ source.filter (fun i => code i ∈ selected), weight i) ∧
      (forall k, k ∈ coordinates -> forall j, j ∈ selected.image (parent k) ->
        ((∑ i ∈ source.filter (fun i => code i ∈ initial), weight i) /
          (2 * ((coordinates.card : Real) + 1) * (∑ i ∈ source, weight i))) *
            (∑ i ∈ source.filter (fun i => parent k (code i) = j), weight i) ≤
          ∑ i ∈ (source.filter (fun i => code i ∈ selected)).filter
            (fun i => parent k (code i) = j), weight i) := by
  classical
  let atoms := source.image code
  let atomWeight := fun a => ∑ i ∈ source.filter (fun i => code i = a), weight i
  have htotal : (∑ a ∈ atoms, atomWeight a) = ∑ i ∈ source, weight i :=
    Finset.sum_fiberwise_of_maps_to
      (fun i hi => Finset.mem_image_of_mem code hi) weight
  have hpreimage (s : Finset A) : (∑ a ∈ s, atomWeight a) =
      ∑ i ∈ source.filter (fun i => code i ∈ s), weight i :=
    Finset.sum_fiberwise_eq_sum_filter source s code weight
  have hnonnegative : forall a, a ∈ atoms -> 0 ≤ atomWeight a := by
    intro a _
    exact Finset.sum_nonneg (fun i hi => hweight i (Finset.mem_filter.mp hi).1)
  obtain ⟨selected, hsub, hnonempty, hretained, hcore⟩ :=
    exists_relative_weighted_fiber_core_half coordinates parent atoms initial hinitial
      atomWeight hnonnegative (by rwa [hpreimage])
  rw [hpreimage, hpreimage] at hretained
  refine ⟨selected, hsub, hnonempty, ?_, hretained, ?_⟩
  · obtain ⟨a, ha⟩ := hnonempty
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp (hinitial (hsub ha))
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, heq ▸ ha⟩⟩
  · intro k hk j hj
    have h := hcore k hk j hj
    rw [htotal, hpreimage] at h
    have hsourcePreimage : source.filter (fun i => code i ∈ atoms) = source :=
      Finset.filter_eq_self.mpr (fun i hi => Finset.mem_image_of_mem code hi)
    rw [sum_atom_weights_filter source atoms code (parent k) weight j,
      hsourcePreimage,
      sum_atom_weights_filter source selected code (parent k) weight j] at h
    exact h

theorem pullback_fine_fiber_eq_atom_fiber
    {I : Type u} {A : Type v} {Q : Type w}
    (source : Finset I) (code : I -> A) (projection : A -> Q)
    (selected : Finset A) (hinjective : Set.InjOn projection selected)
    (a : A) (ha : a ∈ selected) :
    (source.filter (fun i => code i ∈ selected)).filter
      (fun i => projection (code i) = projection a) =
        source.filter (fun i => code i = a) := by
  classical
  ext i
  simp only [Finset.mem_filter]
  constructor
  · intro hi
    exact ⟨hi.1.1, hinjective hi.1.2 ha hi.2⟩
  · intro hi
    exact ⟨⟨hi.1, hi.2 ▸ ha⟩, congrArg projection hi.2⟩

theorem pullback_quotient_fibers_balanced
    {I : Type u} {A : Type v} {Q : Type w}
    (source : Finset I) (code : I -> A) (projection : A -> Q)
    (selected : Finset A) (hinjective : Set.InjOn projection selected)
    (balance : ENNReal)
    (hbalanced : forall a, a ∈ selected -> forall b, b ∈ selected ->
      ((source.filter (fun i => code i = a)).card : ENNReal) ≤
        balance * ((source.filter (fun i => code i = b)).card : ENNReal)) :
    forall q, q ∈ selected.image projection -> forall q', q' ∈ selected.image projection ->
      (((source.filter (fun i => code i ∈ selected)).filter
        (fun i => projection (code i) = q)).card : ENNReal) ≤
          balance * (((source.filter (fun i => code i ∈ selected)).filter
            (fun i => projection (code i) = q')).card : ENNReal) := by
  classical
  intro q hq q' hq'
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq'
  rw [pullback_fine_fiber_eq_atom_fiber source code projection selected hinjective a ha,
    pullback_fine_fiber_eq_atom_fiber source code projection selected hinjective b hb]
  exact hbalanced a ha b hb

end KakeyaLink.DirectCenteredRoute

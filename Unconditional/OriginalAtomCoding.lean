/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Unconditional.WeightedTupleSelection

/-!
# Original Atom Coding

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

open scoped BigOperators Classical

namespace KakeyaLink.DirectCenteredRoute

universe u v w

def denseJointCode
    {I : Type u} {Q : Type v} {m : Nat} {J : Fin m -> Type w}
    (dense : Finset I) (fine : I -> Q) (coarse : forall k, I -> J k)
    (i : I) : Option Q × (forall k, J k) :=
  (if i ∈ dense then some (fine i) else none, fun k => coarse k i)

theorem exists_original_flagged_atom_selection
    {I : Type u} {Q : Type v} {m : Nat} {J : Fin m -> Type w}
    (source dense : Finset I) (hdense : dense ⊆ source) (hnonempty : dense.Nonempty)
    (fine : I -> Q) (coarse : forall k, I -> J k)
    (bound : Nat)
    (hbound : forall q, forall k,
      ((dense.filter (fun i => fine i = q)).image (coarse k)).card ≤ bound) :
    exists initial : Finset (Option Q × (forall k, J k)),
    exists descended : forall k, Q -> J k,
      initial ⊆ source.image (denseJointCode dense fine coarse) ∧ initial.Nonempty ∧
      Set.InjOn (fun a : Option Q × (forall k, J k) => a.1) initial ∧
      (forall a, a ∈ initial -> exists q, a.1 = some q) ∧
      (source.filter (fun i => denseJointCode dense fine coarse i ∈ initial)) ⊆ dense ∧
      dense.card ≤ bound ^ m *
        (source.filter (fun i => denseJointCode dense fine coarse i ∈ initial)).card ∧
      (forall i, i ∈ source -> denseJointCode dense fine coarse i ∈ initial ->
        forall k, descended k (fine i) = coarse k i) := by
  classical
  obtain ⟨retained, hretained, hretainedNonempty, hmass, hcoherent, hfull⟩ :=
    exists_coherent_joint_fiber_selection dense hnonempty fine coarse bound hbound
  obtain ⟨descended, hdescended⟩ :=
    exists_descended_coarse_labels retained hretainedNonempty fine coarse hcoherent
  let code := denseJointCode dense fine coarse
  let initial := retained.image code
  have hcode : forall i, i ∈ retained -> (code i).1 = some (fine i) := by
    intro i hi
    simp only [code, denseJointCode, if_pos (hretained hi)]
  have hinjective : Set.InjOn (fun a : Option Q × (forall k, J k) => a.1) initial := by
    intro a ha b hb heq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
    change (code i).1 = (code j).1 at heq
    have hfine : fine i = fine j := by
      rw [hcode i hi, hcode j hj] at heq
      exact Option.some.inj heq
    apply Prod.ext heq
    exact funext (hcoherent i hi j hj hfine)
  have hpullback : source.filter (fun i => code i ∈ initial) = retained := by
    ext i
    constructor
    · intro hi
      obtain ⟨hi, ha⟩ := Finset.mem_filter.mp hi
      obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp ha
      have hidense : i ∈ dense := by
        by_contra hnot
        have h := congrArg Prod.fst hji
        rw [hcode j hj] at h
        simp only [code, denseJointCode, if_neg hnot] at h
        contradiction
      have hfine : fine i = fine j := by
        have h := congrArg Prod.fst hji
        simp only [code, denseJointCode, if_pos hidense, if_pos (hretained hj)] at h
        exact (Option.some.inj h).symm
      have hcoarse : forall k, coarse k i = coarse k j := by
        intro k
        exact (congrFun (congrArg Prod.snd hji) k).symm
      exact hfull i hidense j hj hfine hcoarse
    · intro hi
      exact Finset.mem_filter.mpr ⟨hdense (hretained hi), Finset.mem_image_of_mem code hi⟩
  refine ⟨initial, descended, Finset.image_subset_image (hretained.trans hdense),
    hretainedNonempty.image code, hinjective, ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    exact ⟨fine i, hcode i hi⟩
  · change (source.filter (fun i => code i ∈ initial)) ⊆ dense
    simpa only [hpullback] using hretained
  · change dense.card ≤ bound ^ m * (source.filter (fun i => code i ∈ initial)).card
    simpa only [hpullback] using hmass
  · intro i hi hcodei k
    have hir : i ∈ retained := hpullback ▸ Finset.mem_filter.mpr ⟨hi, hcodei⟩
    exact hdescended i hir k

end KakeyaLink.DirectCenteredRoute

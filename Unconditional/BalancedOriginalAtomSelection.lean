/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Unconditional.OriginalAtomCoding
import Unconditional.AtomCorePullback
import Unconditional.BalancedQuotientSelection

/-!
# Balanced Original Atom Selection

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

open scoped BigOperators Classical

namespace KakeyaLink.DirectCenteredRoute

universe u v

theorem exists_balanced_atom_subfamily
    {I : Type u} {A : Type v} [DecidableEq A]
    (source : Finset I) (code : I -> A) (initial : Finset A)
    (hinitial : initial ⊆ source.image code) (hnonempty : initial.Nonempty) :
    exists selected : Finset A,
      selected ⊆ initial ∧ selected.Nonempty ∧
      (source.filter (fun i => code i ∈ selected)).Nonempty ∧
      ((source.filter (fun i => code i ∈ initial)).card : Real) ≤
        (2 * (1 + Real.logb 2 (2 * (initial.card : Real)))) *
          ((source.filter (fun i => code i ∈ selected)).card : Real) ∧
      (forall a, a ∈ selected -> forall b, b ∈ selected ->
        ((source.filter (fun i => code i = a)).card : ENNReal) ≤
          2 * ((source.filter (fun i => code i = b)).card : ENNReal)) := by
  classical
  let weight := fun a => ((source.filter (fun i => code i = a)).card : Real)
  have hsum (s : Finset A) : (∑ a ∈ s, weight a) =
      ((source.filter (fun i => code i ∈ s)).card : Real) := by
    simpa [weight] using Finset.sum_fiberwise_eq_sum_filter source s code (fun _ => (1 : Real))
  have hpreimage : (source.filter (fun i => code i ∈ initial)).Nonempty := by
    obtain ⟨a, ha⟩ := hnonempty
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp (hinitial ha)
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, heq ▸ ha⟩⟩
  have hpositive : 0 < ∑ a ∈ initial, weight a := by
    rw [hsum]
    exact_mod_cast hpreimage.card_pos
  obtain ⟨selected, hsub, hne, hmass, _hpos, hbalanced⟩ :=
    exists_comparable_weights_log_card initial weight (fun _ _ => Nat.cast_nonneg _) hpositive
  rw [hsum, hsum] at hmass
  refine ⟨selected, hsub, hne, ?_, hmass, ?_⟩
  · obtain ⟨a, ha⟩ := hne
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp (hinitial (hsub ha))
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, heq ▸ ha⟩⟩
  · intro a ha b hb
    have h := hbalanced a ha b hb
    dsimp only [weight] at h
    have hnat : (source.filter (fun i => code i = a)).card ≤
        2 * (source.filter (fun i => code i = b)).card := by exact_mod_cast h
    exact_mod_cast hnat

theorem exists_balanced_original_flagged_atoms
    {I : Type u} {Q : Type v} {m : Nat} {J : Fin m -> Type*}
    (source dense : Finset I) (hdense : dense ⊆ source) (hnonempty : dense.Nonempty)
    (fine : I -> Q) (coarse : forall k, I -> J k)
    (bound : Nat)
    (hbound : forall q, forall k,
      ((dense.filter (fun i => fine i = q)).image (coarse k)).card ≤ bound) :
    exists initial selected : Finset (Option Q × (forall k, J k)),
    exists descended : forall k, Q -> J k,
      initial ⊆ source.image (denseJointCode dense fine coarse) ∧
      selected ⊆ initial ∧ selected.Nonempty ∧
      Set.InjOn (fun a : Option Q × (forall k, J k) => a.1) initial ∧
      initial.card ≤ (dense.image fine).card ∧
      (source.filter (fun i => denseJointCode dense fine coarse i ∈ selected)).Nonempty ∧
      (source.filter (fun i => denseJointCode dense fine coarse i ∈ selected)) ⊆ dense ∧
      (dense.card : Real) ≤
        (bound ^ m : Nat) * (2 * (1 + Real.logb 2 (2 * (initial.card : Real)))) *
          ((source.filter (fun i => denseJointCode dense fine coarse i ∈ selected)).card : Real) ∧
      (forall a, a ∈ selected -> forall b, b ∈ selected ->
        ((source.filter (fun i => denseJointCode dense fine coarse i = a)).card : ENNReal) ≤
          2 * ((source.filter (fun i => denseJointCode dense fine coarse i = b)).card : ENNReal)) ∧
      (forall i, i ∈ source -> denseJointCode dense fine coarse i ∈ selected ->
        forall k, descended k (fine i) = coarse k i) := by
  classical
  let code := denseJointCode dense fine coarse
  obtain ⟨initial, descended, hinitial, hne, hinj, hsome, hpullDense, hmass, hparent⟩ :=
    exists_original_flagged_atom_selection source dense hdense hnonempty fine coarse bound hbound
  have hinitial' : initial ⊆ source.image code := by simpa only [code] using hinitial
  obtain ⟨selected, hsub, hselected, hpullback, hmassSelected, hbalance⟩ :=
    exists_balanced_atom_subfamily source code initial (by
      intro a ha
      obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp (hinitial' ha)
      exact Finset.mem_image.mpr ⟨i, hi, heq⟩) hne
  have hprojSub : initial.image Prod.fst ⊆ (dense.image fine).image some := by
    intro q hq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp (hinitial ha)
    have hic : denseJointCode dense fine coarse i ∈ initial := heq ▸ ha
    have hidense := hpullDense (Finset.mem_filter.mpr ⟨hi, hic⟩)
    have hfirst : a.1 = some (fine i) := by
      rw [← heq]
      simp only [denseJointCode, if_pos hidense]
    rw [hfirst]
    exact Finset.mem_image_of_mem some (Finset.mem_image_of_mem fine hidense)
  have hcard : initial.card ≤ (dense.image fine).card := by
    calc
      initial.card = (initial.image Prod.fst).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ ((dense.image fine).image some).card := Finset.card_le_card hprojSub
      _ ≤ (dense.image fine).card := Finset.card_image_le
  refine ⟨initial, selected, descended, hinitial, hsub, hselected, hinj, hcard,
    ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [code] using hpullback
  · intro i hi
    obtain ⟨hi, hic⟩ := Finset.mem_filter.mp hi
    exact hpullDense (Finset.mem_filter.mpr ⟨hi, hsub hic⟩)
  · have hmassR : (dense.card : Real) ≤
        (bound ^ m : Nat) * ((source.filter (fun i => code i ∈ initial)).card : Real) := by
      exact_mod_cast hmass
    have h := mul_le_mul_of_nonneg_left hmassSelected (Nat.cast_nonneg (α := Real) (bound ^ m))
    exact hmassR.trans (by simpa only [code, mul_assoc] using h)
  · simpa only [code] using hbalance
  · intro i hi hic k
    exact hparent i hi (hsub hic) k

end KakeyaLink.DirectCenteredRoute

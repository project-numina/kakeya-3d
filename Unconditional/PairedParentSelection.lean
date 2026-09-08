/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Unconditional.JointColorAdapter

/-!
# Paired Parent Selection

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

open scoped BigOperators

namespace KakeyaLink.JointSelection

theorem exists_paired_parent_selection
    {I : Type*} [Fintype I] [LinearOrder I]
    (coordinateCount fineColorCount parentColorCount : ℕ)
    (hfine : 0 < fineColorCount) (hparent : 0 < parentColorCount)
    (OldVertex NewVertex : Fin coordinateCount → Type)
    [∀ k, Fintype (OldVertex k)] [∀ k, DecidableEq (OldVertex k)]
    [∀ k, Fintype (NewVertex k)] [∀ k, DecidableEq (NewVertex k)]
    (fineColor : I → Fin fineColorCount)
    (parentColor : Fin coordinateCount → I → Fin parentColorCount)
    (oldParent : ∀ k, I → OldVertex k) (newParent : ∀ k, I → NewVertex k)
    (weight : I → ENNReal) (hweight : 0 < ∑ i : I, weight i) :
    ∃ selected : Finset I,
      selected.Nonempty ∧
      (∀ i ∈ selected, ∀ j ∈ selected, fineColor i = fineColor j) ∧
      (∀ k, ∀ i ∈ selected, ∀ j ∈ selected, parentColor k i = parentColor k j) ∧
      (∀ i ∈ selected, 0 < weight i) ∧
      (∑ i : I, weight i) ≤
        ((fineColorCount * parentColorCount ^ (coordinateCount + coordinateCount) : ℕ) :
          ENNReal) * 8 *
          (Nat.log 2 (2 * Fintype.card I) + 1 : ENNReal) ^
            (coordinateCount + coordinateCount + 2) * (∑ i ∈ selected, weight i) ∧
      (∀ k, ∀ first second : OldVertex k,
        0 < (selected.filter fun i => oldParent k i = first).card →
        0 < (selected.filter fun i => oldParent k i = second).card →
        ((selected.filter fun i => oldParent k i = first).card : ENNReal) ≤
          (16 * ((coordinateCount + coordinateCount + 1 : ℕ) : ENNReal) *
            (Nat.log 2 (2 * Fintype.card I) + 1 : ENNReal) ^
              (coordinateCount + coordinateCount + 1)) *
                ((selected.filter fun i => oldParent k i = second).card : ENNReal)) ∧
      (∀ k, ∀ first second : NewVertex k,
        0 < (selected.filter fun i => newParent k i = first).card →
        0 < (selected.filter fun i => newParent k i = second).card →
        ((selected.filter fun i => newParent k i = first).card : ENNReal) ≤
          (16 * ((coordinateCount + coordinateCount + 1 : ℕ) : ENNReal) *
            (Nat.log 2 (2 * Fintype.card I) + 1 : ENNReal) ^
              (coordinateCount + coordinateCount + 1)) *
                ((selected.filter fun i => newParent k i = second).card : ENNReal)) ∧
      (∃ weightLevel : ENNReal, 0 < weightLevel ∧
        ∀ i ∈ selected, weightLevel ≤ weight i ∧ weight i ≤ 2 * weightLevel) := by
  classical
  let Label := (k : Fin coordinateCount) × (OldVertex k ⊕ NewVertex k)
  let Vertex : Fin (coordinateCount + coordinateCount) → Type := fun _ => Label
  letI : ∀ k, Fintype (Vertex k) := fun _ => inferInstanceAs (Fintype Label)
  letI : ∀ k, DecidableEq (Vertex k) := fun _ => inferInstanceAs (DecidableEq Label)
  let color : Fin (coordinateCount + coordinateCount) → I → Fin parentColorCount :=
    Fin.addCases (fun _ _ => ⟨0, hparent⟩) parentColor
  let parent : ∀ k, I → Vertex k := Fin.addCases
    (fun k i => ⟨k, Sum.inl (oldParent k i)⟩)
    (fun k i => ⟨k, Sum.inr (newParent k i)⟩)
  obtain ⟨selected, hnonempty, hfineMono, hparentMono, hpositive, hretained, hdegree, hband⟩ :=
    exists_fine_parent_joint_selection (coordinateCount + coordinateCount)
      fineColorCount parentColorCount hfine hparent Vertex fineColor color parent weight hweight
  refine ⟨selected, hnonempty, hfineMono, ?_, hpositive, hretained, ?_, ?_, hband⟩
  · intro k
    simpa only [color, Fin.addCases_right] using hparentMono (k.natAdd coordinateCount)
  · intro k first second
    simpa [parent, Vertex, Label, Fin.addCases_left, Sigma.mk.inj_iff] using
      hdegree (k.castAdd coordinateCount) ⟨k, Sum.inl first⟩ ⟨k, Sum.inl second⟩
  · intro k first second
    simpa [parent, Vertex, Label, Fin.addCases_right, Sigma.mk.inj_iff] using
      hdegree (k.natAdd coordinateCount) ⟨k, Sum.inr first⟩ ⟨k, Sum.inr second⟩

end KakeyaLink.JointSelection

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Unconditional.JointColoredSelection

/-!
# Joint Color Adapter

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

open scoped BigOperators

namespace KakeyaLink.JointSelection

attribute [local instance] Classical.propDecidable

theorem exists_fine_parent_joint_selection
    {I : Type*} [Fintype I] [LinearOrder I]
    (coordinateCount fineColorCount parentColorCount : ℕ)
    (hfine : 0 < fineColorCount) (hparent : 0 < parentColorCount)
    (Vertex : Fin coordinateCount → Type)
    [∀ k, Fintype (Vertex k)] [∀ k, DecidableEq (Vertex k)]
    (fineColor : I → Fin fineColorCount)
    (parentColor : Fin coordinateCount → I → Fin parentColorCount)
    (parent : ∀ k, I → Vertex k)
    (weight : I → ENNReal) (hweight : 0 < ∑ i : I, weight i) :
    ∃ selected : Finset I,
      selected.Nonempty ∧
      (∀ i ∈ selected, ∀ j ∈ selected, fineColor i = fineColor j) ∧
      (∀ k, ∀ i ∈ selected, ∀ j ∈ selected, parentColor k i = parentColor k j) ∧
      (∀ i ∈ selected, 0 < weight i) ∧
      (∑ i : I, weight i) ≤
        ((fineColorCount * parentColorCount ^ coordinateCount : ℕ) : ENNReal) *
          8 * (Nat.log 2 (2 * Fintype.card I) + 1 : ENNReal) ^ (coordinateCount + 2) *
            (∑ i ∈ selected, weight i) ∧
      (∀ k, ∀ first second : Vertex k,
        0 < (selected.filter fun i => parent k i = first).card →
        0 < (selected.filter fun i => parent k i = second).card →
        ((selected.filter fun i => parent k i = first).card : ENNReal) ≤
          (16 * ((coordinateCount + 1 : ℕ) : ENNReal) *
            (Nat.log 2 (2 * Fintype.card I) + 1 : ENNReal) ^ (coordinateCount + 1)) *
              ((selected.filter fun i => parent k i = second).card : ENNReal)) ∧
      (∃ weightLevel : ENNReal, 0 < weightLevel ∧
        ∀ i ∈ selected, weightLevel ≤ weight i ∧ weight i ≤ 2 * weightLevel) := by
  classical
  let Color : Fin (coordinateCount + 1) → Type :=
    Fin.cases (Fin fineColorCount) (fun _ => Fin parentColorCount)
  let Parent : Fin (coordinateCount + 1) → Type := Fin.cases PUnit Vertex
  letI : NeZero fineColorCount := ⟨hfine.ne'⟩
  letI : NeZero parentColorCount := ⟨hparent.ne'⟩
  letI : ∀ k, Fintype (Color k) := fun k =>
    Fin.cases (inferInstance : Fintype (Fin fineColorCount))
      (fun _ => (inferInstance : Fintype (Fin parentColorCount))) k
  letI : ∀ k, DecidableEq (Color k) := fun k =>
    Fin.cases (inferInstance : DecidableEq (Fin fineColorCount))
      (fun _ => (inferInstance : DecidableEq (Fin parentColorCount))) k
  letI : ∀ k, Nonempty (Color k) := fun k =>
    Fin.cases (inferInstance : Nonempty (Fin fineColorCount))
      (fun _ => (inferInstance : Nonempty (Fin parentColorCount))) k
  letI : ∀ k, Fintype (Parent k) := fun k =>
    Fin.cases (inferInstance : Fintype PUnit)
      (fun k => (inferInstance : Fintype (Vertex k))) k
  letI : ∀ k, DecidableEq (Parent k) := fun k =>
    Fin.cases (inferInstance : DecidableEq PUnit)
      (fun k => (inferInstance : DecidableEq (Vertex k))) k
  let color : ∀ k, I → Color k := Fin.cases fineColor parentColor
  let assignment : ∀ k, I → Parent k := Fin.cases (fun _ => PUnit.unit) parent
  obtain ⟨selected, vector, hnonempty, hmono, hpositive, hretained, hdegree, hband⟩ :=
    exists_joint_colored_degree_selection (coordinateCount + 1) (by omega)
      Color Parent color assignment weight hweight
  have hcolorCard : Fintype.card (∀ k, Color k) =
      fineColorCount * parentColorCount ^ coordinateCount := by
    rw [Fintype.card_pi, Fin.prod_univ_succ]
    simp only [Color, Fin.cases_zero, Fin.cases_succ, Fintype.card_eq_nat_card,
      Nat.card_fin, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  refine ⟨selected, hnonempty, ?_, ?_, hpositive, ?_, ?_, hband⟩
  · intro i hi j hj
    exact (hmono i hi 0).trans (hmono j hj 0).symm
  · intro k i hi j hj
    exact (hmono i hi k.succ).trans (hmono j hj k.succ).symm
  · simpa only [hcolorCard, Nat.add_assoc] using hretained
  · intro k
    simpa [assignment, Parent] using hdegree k.succ

end KakeyaLink.JointSelection

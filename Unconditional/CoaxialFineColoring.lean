/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Unconditional.SharedChildPacking
import Unconditional.ReanchoredParentEnclosure
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.WeightedGraphSelection

/-!
# Coaxial Fine Coloring

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

theorem coaxial_fine_conflict_coloring
    {delta : ℝ} (deltaPos : 0 < delta) (deltaSmall : delta ≤ 1 / 1600)
    {source target : Kakeya.Streamlined.TubeFamily delta}
    (sourceDistinct : source.IsEssentiallyDistinct)
    (sourceIndex : Fin target.card ↪ Fin source.card)
    (shift : Fin target.card → ℝ)
    (directionEq : ∀ i,
      (source.tube (sourceIndex i)).direction = (target.tube i).direction)
    (baseEq : ∀ i,
      (source.tube (sourceIndex i)).base =
        (target.tube i).base + shift i • (target.tube i).direction)
    (shiftBound : ∀ i, |shift i| ≤ 1) :
    ∃ color : Fin target.card → Fin (sharedChildParentDegreeBound 8 + 1),
      ∀ i j, i ≠ j →
        ((target.tube i).carrier ⊆ wz2PaperCenteredDilatedCarrier 2 (target.tube j) ∨
          (target.tube j).carrier ⊆ wz2PaperCenteredDilatedCarrier 2 (target.tube i)) →
        color i ≠ color j := by
  let indexedSource : Kakeya.Streamlined.TubeFamily delta :=
    { card := target.card
      tube := fun i => source.tube (sourceIndex i) }
  have indexedDistinct : indexedSource.IsEssentiallyDistinct := by
    intro i j different
    exact sourceDistinct _ _ (fun equal => different (sourceIndex.injective equal))
  have enclosure : ∀ i,
      wz2PaperCenteredDilatedCarrier 2 (target.tube i) ⊆
        wz2PaperCenteredDilatedCarrier 8 (indexedSource.tube i) := by
    intro i
    have reverseBase : (target.tube i).base =
        (indexedSource.tube i).base + (-shift i) • (indexedSource.tube i).direction := by
      change (target.tube i).base =
        (source.tube (sourceIndex i)).base + (-shift i) •
          (source.tube (sourceIndex i)).direction
      rw [baseEq, directionEq]
      module
    apply coaxial_dilated_carrier_subset deltaPos.le (by norm_num) (by norm_num)
      (target.tube i) (indexedSource.tube i) (directionEq i).symm reverseBase
    · nlinarith
    · rw [abs_neg]
      linarith [shiftBound i]
  let relation : Fin target.card → Fin target.card → Prop := fun i j =>
    i ≠ j ∧
      ((target.tube i).carrier ⊆ wz2PaperCenteredDilatedCarrier 2 (target.tube j) ∨
        (target.tube j).carrier ⊆ wz2PaperCenteredDilatedCarrier 2 (target.tube i))
  have symmetric : ∀ i j, relation i j → relation j i := by
    intro i j h
    exact ⟨h.1.symm, h.2.symm⟩
  have irreflexive : ∀ i, ¬ relation i i := fun _ h => h.1 rfl
  have degree : ∀ i,
      (Finset.univ.filter (relation i)).card ≤ sharedChildParentDegreeBound 8 := by
    intro i
    apply shared_child_parent_neighbor_card_le deltaPos deltaPos (by norm_num)
      (by convert deltaSmall using 1; norm_num) (by linarith : delta ≤ 8 * delta)
      indexedDistinct i (Finset.univ.filter (relation i))
    intro j jMem
    rcases (Finset.mem_filter.mp jMem).2.2 with contains | contains
    · exact ⟨target.tube i,
        (wz2_paper_carrier_subset_centeredDilatedTwo (target.tube i) deltaPos.le).trans
          (enclosure i), contains.trans (enclosure j)⟩
    · exact ⟨target.tube j, contains.trans (enclosure i),
        (wz2_paper_carrier_subset_centeredDilatedTwo (target.tube j) deltaPos.le).trans
          (enclosure j)⟩
  obtain ⟨color, proper⟩ := pureWZ2_greedy_proper_coloring
    (D := sharedChildParentDegreeBound 8) symmetric irreflexive
    (fun i => by simpa [relation] using degree i)
  exact ⟨color, fun _ _ different conflict => proper _ _ ⟨different, conflict⟩⟩

theorem paper_distinct_of_monochromatic
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    {Color : Type*} (color : Fin family.card → Color)
    (proper : ∀ i j, i ≠ j →
      ((family.tube i).carrier ⊆ wz2PaperCenteredDilatedCarrier 2 (family.tube j) ∨
        (family.tube j).carrier ⊆ wz2PaperCenteredDilatedCarrier 2 (family.tube i)) →
      color i ≠ color j)
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (monochromatic : ∀ i j, color (selected.embedding i) = color (selected.embedding j)) :
    WZ2PaperOrdinaryIsEssentiallyDistinct selected.family := by
  intro i j different
  have indexDifferent : selected.embedding i ≠ selected.embedding j :=
    fun equal => different (selected.embedding.injective equal)
  constructor
  · intro contain
    rw [selected.tube_eq, selected.tube_eq] at contain
    exact proper _ _ indexDifferent (Or.inl contain) (monochromatic i j)
  · intro contain
    rw [selected.tube_eq, selected.tube_eq] at contain
    exact proper _ _ indexDifferent (Or.inr contain) (monochromatic i j)

end Kakeya.Assouad

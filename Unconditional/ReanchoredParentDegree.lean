/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Unconditional.SharedChildPacking
import Unconditional.ReanchoredParentEnclosure
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.WeightedGraphSelection

/-!
# Reanchored Parent Degree

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

theorem reanchored_parent_neighbor_card_le
    {delta rho factor : ℝ}
    (deltaPos : 0 < delta) (rhoPos : 0 < rho) (factorOne : 1 ≤ factor)
    (scaleSmall : rho ≤ 1 / (200 * (32 * factor)))
    (childScale : delta ≤ rho)
    {parents : Kakeya.Streamlined.TubeFamily rho}
    (parentsDistinct : parents.IsEssentiallyDistinct)
    (center : Point3) (reference : Fin parents.card)
    (neighbors : Finset (Fin parents.card))
    (referenceShift : |pureWZ2AxialShift center (parents.tube reference)| ≤ 4 * factor)
    (neighborShift : ∀ j ∈ neighbors,
      |pureWZ2AxialShift center (parents.tube j)| ≤ 4 * factor)
    (sharedChild : ∀ j ∈ neighbors,
      ∃ child : Kakeya.DeltaTube delta,
        child.carrier ⊆ wz2PaperCenteredDilatedCarrier 2
          (pureWZ2ReanchoredParentTube (A := factor) center (parents.tube reference)) ∧
        child.carrier ⊆ wz2PaperCenteredDilatedCarrier 2
          (pureWZ2ReanchoredParentTube (A := factor) center (parents.tube j))) :
    neighbors.card ≤ sharedChildParentDegreeBound (32 * factor) := by
  apply shared_child_parent_neighbor_card_le deltaPos rhoPos
    (by linarith : 1 ≤ 32 * factor) scaleSmall
    (by nlinarith : delta ≤ (32 * factor) * rho)
    parentsDistinct reference neighbors
  intro j jMem
  obtain ⟨child, childReference, childNeighbor⟩ := sharedChild j jMem
  exact ⟨child,
    childReference.trans
      (doubled_reanchored_parent_subset_original rhoPos.le factorOne center
        (parents.tube reference) referenceShift),
    childNeighbor.trans
      (doubled_reanchored_parent_subset_original rhoPos.le factorOne center
        (parents.tube j) (neighborShift j jMem))⟩

theorem reanchored_parent_coloring
    {delta rho factor : ℝ}
    (deltaPos : 0 < delta) (rhoPos : 0 < rho) (factorOne : 1 ≤ factor)
    (scaleSmall : rho ≤ 1 / (200 * (32 * factor)))
    (childScale : delta ≤ rho)
    {parents : Kakeya.Streamlined.TubeFamily rho}
    (parentsDistinct : parents.IsEssentiallyDistinct)
    (center : Point3)
    (parentShift : ∀ i, |pureWZ2AxialShift center (parents.tube i)| ≤ 4 * factor) :
    ∃ color : Fin parents.card → Fin (sharedChildParentDegreeBound (32 * factor) + 1),
      ∀ first second, first ≠ second →
        (∃ child : Kakeya.DeltaTube delta,
          child.carrier ⊆ wz2PaperCenteredDilatedCarrier 2
            (pureWZ2ReanchoredParentTube (A := factor) center (parents.tube first)) ∧
          child.carrier ⊆ wz2PaperCenteredDilatedCarrier 2
            (pureWZ2ReanchoredParentTube (A := factor) center (parents.tube second))) →
          color first ≠ color second := by
  let relation : Fin parents.card → Fin parents.card → Prop := fun first second =>
    first ≠ second ∧
      ∃ child : Kakeya.DeltaTube delta,
        child.carrier ⊆ wz2PaperCenteredDilatedCarrier 2
          (pureWZ2ReanchoredParentTube (A := factor) center (parents.tube first)) ∧
        child.carrier ⊆ wz2PaperCenteredDilatedCarrier 2
          (pureWZ2ReanchoredParentTube (A := factor) center (parents.tube second))
  have symmetric : ∀ i j, relation i j → relation j i := by
    rintro i j ⟨ijNe, child, hi, hj⟩
    exact ⟨ijNe.symm, child, hj, hi⟩
  have irreflexive : ∀ i, ¬ relation i i := fun _ h => h.1 rfl
  have degree : ∀ i,
      (Finset.univ.filter (relation i)).card ≤ sharedChildParentDegreeBound (32 * factor) := by
    intro i
    exact reanchored_parent_neighbor_card_le deltaPos rhoPos factorOne scaleSmall childScale
      parentsDistinct center i (Finset.univ.filter (relation i)) (parentShift i)
      (fun j _ => parentShift j)
      (fun j jMem => (Finset.mem_filter.mp jMem).2.2)
  obtain ⟨color, proper⟩ := pureWZ2_greedy_proper_coloring
    (D := sharedChildParentDegreeBound (32 * factor)) symmetric irreflexive
    (fun i => by simpa [relation] using degree i)
  exact ⟨color, fun _ _ ijNe hchild => proper _ _ ⟨ijNe, hchild⟩⟩

end Kakeya.Assouad

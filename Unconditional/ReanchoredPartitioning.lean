/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Unconditional.ReanchoredParentDegree

/-!
# Reanchored Partitioning

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable


theorem WZ2PaperPurePartitioningCover.fullFiber_eq_assigned
    {delta rho : ℝ} (rhoNonneg : 0 ≤ rho)
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    (assigned : Fin fine.card → Fin coarse.card)
    (assignedContains : ∀ i, (fine.tube i).carrier ⊆ (coarse.tube (assigned i)).carrier)
    (parent : Fin coarse.card) :
    wz2PaperOrdinaryFullFiberIndices fine coarse parent =
      Finset.univ.filter (fun i => assigned i = parent) := by
  have parentEq : ∀ i, cover.parent i = assigned i := by
    intro i
    exact cover.fullFiber_parent_unique rhoNonneg (cover.parent_mem_fullFiber i)
      ((mem_wz2PaperOrdinaryFullFiberIndices_iff (assigned i) i).mpr (assignedContains i))
  ext i
  simp only [cover.mem_fullFiber_iff_parent_eq rhoNonneg, parentEq,
    Finset.mem_filter, Finset.mem_univ, true_and]

end Kakeya.Assouad

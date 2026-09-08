/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import MyLeanRepo.Kakeya.Assouad.PureWZ2.PureNearbyTopLevelCWA

/-!
# Scale To Ordinary C W A

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

theorem WZ2PaperPureScaleCoverData.ordinaryCWA
    {delta rho loss : ℝ} {constant : ENNReal}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (scale : WZ2PaperPureScaleCoverData family rho constant)
    (familyNonempty : family.Nonempty)
    (scaleLower : Real.rpow delta loss ≤ rho) :
    WZ2PaperBodyConvexWolffBound family.toBodyFamily
      ((4 * Kakeya.realRpowENN delta (-2 * loss)) * constant) := by
  have parentCount : 0 < scale.coarse.card := by
    obtain ⟨parent, _⟩ := scale.cover.covers ⟨0, familyNonempty⟩
    exact Nat.zero_lt_of_lt parent.isLt
  apply wz2PaperBodyConvexWolffBound_of_parent_fibers parentCount scale.cover.parent
  intro parent
  obtain ⟨fiberData⟩ := scale.rescaledFiber parent
  have fullFiber := wz2PaperPureActualJohnFullFiber_ordinaryCWA
    parent scale.delta_pos scaleLower fiberData
  have indices : wz2PaperOrdinaryFullFiberIndices family scale.coarse parent =
      Finset.univ.filter fun source => scale.cover.parent source = parent := by
    ext source
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact scale.cover.mem_fullFiber_iff_parent_eq scale.rho_pos.le parent source
  simp only [wz2PaperPureFullFiberSubfamily,
    Kakeya.Streamlined.TubeSubfamily.fromFinset,
    Kakeya.Streamlined.TubeFamily.toBodyFamily] at fullFiber
  rw [indices] at fullFiber
  unfold wz2PaperBodyParentFiber
  convert fullFiber using 1
  simp only [Kakeya.Streamlined.TubeFamily.toBodyFamily]
  rfl

end Kakeya.Assouad

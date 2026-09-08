/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Kakeya.Tube.ChainScale

/-!
# Restored Fine Support

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

namespace KakeyaLink.DirectCenteredRoute

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]

theorem restored_fine_carrier_subset_unit_ball
    {delta : NNReal} (hsmall : delta ≤ 1 / 2) (fine : Tube (delta / 2) E)
    (hball : fine.carrier ⊆ Metric.closedBall 0 (3 / 4 : Real)) :
    (fine.rescale delta).carrier ⊆ Metric.closedBall 0 1 := by
  have hbudget : (delta : Real) ≤ (delta / 2 : NNReal) + (1 / 4 : Real) := by
    have hsmallR : (delta : Real) ≤ 1 / 2 := hsmall
    simp only [NNReal.coe_div, NNReal.coe_ofNat]
    linarith
  have h := Tube.rescale_translate_carrier_subset_closedBall fine hball
    (by norm_num : (0 : Real) ≤ 1 / 4) hbudget (0 : E) (by simp : ‖(0 : E)‖ ≤ (0 : Real))
  have hcarrier : ((fine.rescale delta).translate (0 : E)).carrier =
      (fine.rescale delta).carrier := by
    change (fun x : E => 0 + x) '' (fine.rescale delta).carrier = _
    simp
  rw [hcarrier] at h
  convert h using 1
  norm_num

end KakeyaLink.DirectCenteredRoute

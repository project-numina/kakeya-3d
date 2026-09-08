/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Unconditional.GeometryAdapters
import Kakeya.Tube.Dilate
import Unconditional.ReanchoredParentVolume

/-!
# Numina Reanchored Geometry

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

open MeasureTheory

namespace KakeyaLink.JointSelection

open Kakeya.Assouad

theorem toDeltaTube_center {delta : NNReal} (tube : Tube delta Kakeya.Point3) :
    wz2PaperTubeMidpoint (toDeltaTube tube) = tube.center := by
  simp only [wz2PaperTubeMidpoint, toDeltaTube, Tube.center, Tube.direction,
    midpoint_eq_smul_add, invOf_eq_inv]
  module

theorem toDeltaTube_centeredDilatedCarrier {delta : NNReal}
    (tube : Tube delta Kakeya.Point3) (factor : ℝ) :
    wz2PaperCenteredDilatedCarrier factor (toDeltaTube tube) =
      (Kakeya.Tube.dilate tube factor).carrier := by
  rw [wz2PaperCenteredDilatedCarrier, toDeltaTube_center, toDeltaTube_carrier]
  rfl

theorem numina_reanchored_parent_volume_ratio {rho : NNReal}
    (factor : ℝ) (hfactor : 1 ≤ factor) (center : Kakeya.Point3)
    (parent oldParent : Tube rho Kakeya.Point3) :
    volume (pureWZ2ReanchoredParentTube (A := factor) center
      (toDeltaTube parent)).carrier ≤
      ENNReal.ofReal ((8 * factor) ^ 3) * volume oldParent.carrier := by
  have raw := reanchored_parent_volume_le rho.coe_nonneg hfactor center (toDeltaTube parent)
  have hequal : volume (toDeltaTube parent).carrier = volume oldParent.carrier := by
    exact (Kakeya.Streamlined.tube_volume_eq (toDeltaTube parent) (toDeltaTube oldParent)).trans
      (toDeltaTube_volume oldParent)
  calc
    _ ≤ 512 * volume (wz2PaperCenteredDilatedCarrier factor (toDeltaTube parent)) := raw
    _ = 512 * (ENNReal.ofReal (factor ^ 3) * volume oldParent.carrier) := by
      rw [wz2_paper_centeredDilatedCarrier_volume, abs_of_nonneg (by linarith), hequal]
    _ = _ := by
      rw [mul_pow, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8 ^ 3)]
      norm_num
      exact (mul_assoc _ _ _).symm

end KakeyaLink.JointSelection

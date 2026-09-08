/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZBridge
import MyLeanRepo.Kakeya.Assouad.TranslationInfrastructure

/-!
# Coaxial Fixed Support

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

namespace Kakeya.Assouad

open TranslationInfrastructure

theorem coaxial_target_fixedBallSupport
    {delta radius : ℝ}
    {source target : Kakeya.Streamlined.TubeFamily delta}
    (sourceSupported : PureWZ2FixedBallSupport source radius)
    (sourceIndex : Fin target.card ↪ Fin source.card)
    (shift : Fin target.card → ℝ)
    (directionEq : ∀ i, (source.tube (sourceIndex i)).direction = (target.tube i).direction)
    (baseEq : ∀ i, (source.tube (sourceIndex i)).base =
      (target.tube i).base + shift i • (target.tube i).direction)
    (shiftBound : ∀ i, |shift i| ≤ 1) :
    PureWZ2FixedBallSupport target (radius + 1) := by
  intro i point pointMem
  have carrierEq : (source.tube (sourceIndex i)).carrier =
      (translateTube (shift i • (target.tube i).direction) (target.tube i)).carrier := by
    change Metric.cthickening delta (Kakeya.unitSegment
      (source.tube (sourceIndex i)).base (source.tube (sourceIndex i)).direction) = _
    rw [baseEq, directionEq]
    rfl
  have translated : point + shift i • (target.tube i).direction ∈
      (source.tube (sourceIndex i)).carrier := by
    rw [carrierEq, translateTube_carrier]
    exact ⟨point, pointMem, rfl⟩
  have sourceNear := sourceSupported (sourceIndex i) translated
  rw [Metric.mem_closedBall, dist_zero_right] at sourceNear ⊢
  calc
    ‖point‖ = ‖(point + shift i • (target.tube i).direction) -
        shift i • (target.tube i).direction‖ := by rw [add_sub_cancel_right]
    _ ≤ ‖point + shift i • (target.tube i).direction‖ +
        ‖shift i • (target.tube i).direction‖ := norm_sub_le _ _
    _ ≤ radius + 1 := by
      rw [norm_smul, Real.norm_eq_abs, (target.tube i).direction_unit, mul_one]
      exact add_le_add sourceNear (shiftBound i)


end Kakeya.Assouad

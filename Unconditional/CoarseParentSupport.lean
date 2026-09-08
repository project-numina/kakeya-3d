/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Kakeya.Tube.Dilate

/-!
# Coarse Parent Support

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

namespace KakeyaLink.DirectCenteredRoute

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]

theorem carrier_subset_ball_of_contains_ball_leaf
    {delta rho : NNReal} (fine : Tube delta E) (coarse : Tube rho E) (radius : Real)
    (hball : fine.carrier ⊆ Metric.closedBall 0 radius)
    (hcontained : fine.carrier ⊆ coarse.carrier) :
    coarse.carrier ⊆ Metric.closedBall 0 (radius + 1 + 2 * (rho : Real)) := by
  have hx : dist fine.x (0 : E) ≤ radius := hball (Tube.x_mem_carrier fine)
  have hxmid : dist fine.x (midpoint Real coarse.x coarse.y) ≤ 1 / 2 + (rho : Real) :=
    Kakeya.Tube.carrier_subset_closedBall_midpoint E coarse
      (hcontained (Tube.x_mem_carrier fine))
  apply (Kakeya.Tube.carrier_subset_closedBall_midpoint E coarse).trans
  apply Metric.closedBall_subset_closedBall'
  have htriangle := dist_triangle (midpoint Real coarse.x coarse.y) fine.x (0 : E)
  rw [dist_comm (midpoint Real coarse.x coarse.y) fine.x] at htriangle
  linarith

theorem coarse_parent_carrier_subset_ball_three
    {delta rho : NNReal} (fine : Tube delta E) (coarse : Tube rho E)
    (hrho : (rho : Real) ≤ 1 / 2)
    (hball : fine.carrier ⊆ Metric.closedBall 0 1)
    (hcontained : fine.carrier ⊆ coarse.carrier) :
    coarse.carrier ⊆ Metric.closedBall 0 (3 : Real) := by
  apply (carrier_subset_ball_of_contains_ball_leaf fine coarse 1 hball hcontained).trans
  exact Metric.closedBall_subset_closedBall (by linarith)

end KakeyaLink.DirectCenteredRoute

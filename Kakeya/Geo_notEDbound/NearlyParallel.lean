/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Tube.CylinderApprox
public import Kakeya.Tube.IntersectionVolume
public import Kakeya.ConvexBody
public import Kakeya.Tube.Basic
public import Kakeya.Tube.CardEssentiallyDistinct

/-!
# Nearly parallel tubes

If two tubes are not essentially distinct, then their directions are close (modulo
antipodal identification) and their midpoints have close perpendicular and parallel
components.  The main theorems are `notED_implies_direction_close` and
`notED_implies_all_close`.
-/

@[expose] public section

open MeasureTheory
open Topology
open Tube

namespace Kakeya

noncomputable section
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]

/- not-ED ⇒ modulo antipodal -/


end
end Kakeya

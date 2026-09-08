/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Unconditional.GeometryAdapters
import Kakeya.Uniform
import Kakeya.Tube.Dilate
import Kakeya.Tube.EssentiallyDistinctReduction

/-!
# Numina Coarse Representatives

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace KakeyaLink.JointSelection

attribute [local instance] Classical.propDecidable

universe u

variable {I : Type u} {delta : NNReal}
  {s : Finset I} {V : I → ShadedTube delta Kakeya.Point3} {N : ℕ} {C : NNReal}

def numinaRepresentativeDilation : ℝ :=
  Kakeya.Tube.tubeOverlapCoreClose.C 3


end KakeyaLink.JointSelection

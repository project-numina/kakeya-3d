/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Unconditional.NuminaCoarseRepresentatives
import Unconditional.IndexedSelection
import Unconditional.NuminaReanchoredGeometry
import Unconditional.ReanchoredParentDegree

/-!
# Numina Active Parents

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

open MeasureTheory

namespace KakeyaLink.JointSelection

open Kakeya.Streamlined Kakeya.Assouad

attribute [local instance] Classical.propDecidable


end KakeyaLink.JointSelection

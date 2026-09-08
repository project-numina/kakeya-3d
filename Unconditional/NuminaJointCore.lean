/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Unconditional.NuminaActiveParents
import Unconditional.NuminaJointDefinitions
import Unconditional.GeometryAdapters
import Kakeya.Frostman
import Kakeya.Uniform
import Unconditional.NuminaReanchoredGeometry
import MyLeanRepo.Kakeya.Assouad.PropStickyFiniteFiberRatio
import Unconditional.ReanchoredPartitioning
import Unconditional.JointLocalizedRefinement
import Unconditional.PairedParentSelection

/-!
# Numina Joint Core

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace KakeyaLink.JointSelection

open Kakeya.Streamlined Kakeya.Assouad

attribute [local instance] Classical.propDecidable

def numinaJointWeightLoss (coordinateCount cardinality : ℕ) : ENNReal :=
  (((sharedChildParentDegreeBound 8 + 1) *
    (sharedChildParentDegreeBound (32 * numinaRepresentativeDilation) + 1) ^
      (coordinateCount + coordinateCount) : ℕ) : ENNReal) * 8 *
    (Nat.log 2 (2 * cardinality) + 1 : ENNReal) ^ (coordinateCount + coordinateCount + 2)

def numinaJointDegreeLoss (coordinateCount cardinality : ℕ) : ENNReal :=
  16 * ((coordinateCount + coordinateCount + 1 : ℕ) : ENNReal) *
    (Nat.log 2 (2 * cardinality) + 1 : ENNReal) ^ (coordinateCount + coordinateCount + 1)


end KakeyaLink.JointSelection

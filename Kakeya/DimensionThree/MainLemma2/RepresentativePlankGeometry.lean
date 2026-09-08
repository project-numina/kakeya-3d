/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factoring.FlatPrisms
public import Kakeya.DimensionThree.Slab.Multiplicity

/-!
# Exact plank representatives of comparable plank bodies

Defines `Kakeya.RepresentativePlankGeometry`: an exact `Plank a b` whose `Cw`-dilated prism
contains a given convex body, has volume at most `Prism3D.enclosureVolumeConstant Cw` times the
body's volume, and sits in a fixed ball. `Kakeya.hasThicknesses_of_isPlankOfDimensions` converts
the `ENNReal` affine-thickness form of `IsPlankOfDimensions` to the real-valued `HasThicknesses`
API, and `Kakeya.exists_representativePlankGeometry` builds the representative for every
`IsPlankOfDimensions Cw a b` body in the unit ball. This keeps the actual hull and the exact
prism separate for downstream slab-multiplicity arguments.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ConvexSpaceBody Metric
open scoped NNReal ENNReal Real

namespace Kakeya

noncomputable section

/-- The exact plank representative of a body whose affine dimensions are only
comparable to `a x b x 1`.  The original body is contained in the `Cw`-dilation
of the representative; this keeps the actual hull and the exact prism separate. -/
structure RepresentativePlankGeometry (Cw a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1)
    (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) where
  plank : Plank a b hab hb1
  body_subset_dilation :
    (K.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      (plank.toPrismNDim.dilation Cw).carrier
  dilation_volume_le :
    volume ((plank.toPrismNDim.dilation Cw).carrier : Set (EuclideanSpace ℝ (Fin 3))) ≤
      (Prism3D.enclosureVolumeConstant Cw : ℝ≥0∞) * volume K.carrier
  dilation_window :
    ((plank.toPrismNDim.dilation Cw).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      Metric.closedBall 0 ((1 + 6 * Cw : ℝ≥0) : ℝ)

end

end Kakeya

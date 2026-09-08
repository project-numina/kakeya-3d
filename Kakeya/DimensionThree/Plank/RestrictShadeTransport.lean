/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.AngleDef
public import Mathlib.Algebra.Order.Floor.Extended

/-!
# Transport of the angular data through a common restriction

The final family of GWZ Lemma 6.13 is `ShadedBody.restrictShade (Y' i) G` for one measurable set `G`
shared by every index.  This file records what that operation does to the angular data.

The point is that a *common* restriction is not a refinement in the lossy sense: at a point of `G`
the restricted shade fibre is the unrestricted one, because `i` belongs to the fibre iff
`x ∈ (Y' i).shade ∩ G`, and `x ∈ G` holds by assumption.  So the two-sided
`Kakeya.IsTypicalPlankAngle` transfers with the *same* constant and the *same* stability scale — no
fibre-retention factor is spent, and the two-sided predicate, which is not monotone under shrinking
a family, survives.

Contrast `Kakeya.HasMaxPlankAngleBound.mono`, which handles an arbitrary shrinking but only for the
one-sided predicate; that is not enough here, because `Kakeya.plankReduction` returns the two-sided
`Kakeya.IsTypicalPlankAngle`.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real ENNReal

noncomputable section

namespace Plank

variable {ι : Type*}

@[simp] theorem restrictShade_carrier (Z : ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (G : Set (EuclideanSpace ℝ (Fin 3))) (hG : MeasurableSet G) :
    ((ShadedBody.restrictShade Z G hG).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = (Z.carrier : Set (EuclideanSpace ℝ (Fin 3))) := rfl

theorem restrictShade_shade_subset (Z : ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (G : Set (EuclideanSpace ℝ (Fin 3))) (hG : MeasurableSet G) :
    (ShadedBody.restrictShade Z G hG).shade ⊆ Z.shade := Set.inter_subset_left


end Plank

end

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Geometry
public import Kakeya.DimensionThree.Plank.TypicalAngleIncidence
public import Kakeya.DimensionThree.Plank.PlankReduction

/-!
# Statement of GWZ Lemma 6.13

Only the theorem statement and the definitions it directly uses are included, so the imports are
deliberately minimal and nothing in the repository imports this file except the module index.

The proof route that discharges it is assembled elsewhere and is layered
`RepresentativeSelection` (witness) → `Refinement` (preassembly) → final reduction;
proving `reduction_to_slab` therefore means importing
`Kakeya.DimensionThree.Plank.RepresentativeShading`,
`Kakeya.DimensionThree.Plank.LocalDensity`
and `Kakeya.DimensionThree.Plank.Refinement` here.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Metric
open scoped NNReal Real

noncomputable section

namespace ShadedPlank

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}

/-- The fixed ball-dilation factor in Item 1 of GWZ Lemma 6.13.

It is the literal `3` of the triangle inequality, and it is the only dilation of a *ball*
anywhere in the conclusion.  Item 1 is proved from a grid of `θb`-balls: the retained
shading is supported on a
union of balls `B̄(c, θb)` on each of which the density bound holds, so for an arbitrary centre `x`
with `U ∩ B̄(x, θb) ≠ ∅` one picks a dense grid ball `B̄(c, θb)` meeting it and uses
`B̄(c, θb) ⊆ B̄(x, 3 · θb)`.

**The paper's same-radius reading is false as literally quantified, so this is a correction
and not a weakening.**  Suppose `U` were a single ball `B̄(c, θb)`, the densest possible
configuration, and take `x` with `dist x c` close to `2 · θb`.  Then `U ∩ B̄(x, θb)` is a
nonempty lens whose volume tends to
`0` relative to `volume (B̄(x, θb))`, so no bound `κ · volume (B̄(x, θb)) ≤ volume (U ∩ B̄(x, θb))`
can hold uniformly in `x` for any positive `κ`.  A density statement at an arbitrary centre is only
available on a dilate, which is what the grid argument gives and what the downstream
covering/Vitali consumers need. -/
def redPlankTube.ballDilation : ℝ≥0 := 3


end ShadedPlank

end

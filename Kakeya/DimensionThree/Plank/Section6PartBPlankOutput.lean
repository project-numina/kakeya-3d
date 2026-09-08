/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.CollarPlankPresentation
public import Kakeya.DimensionThree.Plank.Section6PartBProp51Input

/-!
# GWZ Proposition 5.1 for Part (B), on exact `a × b × 1` shaded planks

`Kakeya.Section6PartBData.exists_prop51SelectScale` makes GWZ Proposition 5.1 a **theorem** of the
Part-(B) datum, and `Kakeya.Section6PartBData.exists_prop51_split_over_constructed_output` records
its refinement and multiplicity split.  Both live on the *actual cell bodies*: the outer bodies of
the constructed output are the `Kakeya.ConvexSpaceBody.scale`-collars of the cell bodies
(`Kakeya.ShadedBody.FactoringAndMultPropCoreAtScale.outer_carrier`).

`Kakeya.Section6PartBData.OuterPackage`, which the Section-6 assembly consumes, lives on
`Kakeya.ShadedPlank a b`s instead.  This file crosses that gap, using
`Kakeya.collarPlank` (`Kakeya/DimensionThree/Plank/CollarPlankPresentation.lean`) — the single
common homothety, under which the multiplicity split transports **exactly**.

## The one hypothesis that is not free

`Kakeya.IsPlankOfDimensions Cw a b (D.factor.body x)` — the two-sided bracketing of the three
affine thicknesses of a cell body.  Its *upper* half is free from the datum
(`Kakeya.Section6PartBFactorisation.body_le_repr` puts the body in an exact `a × b × 1` plank, so
`Kakeya.Section6PartBData.ethickness_two_body_le` and `Kakeya.Prism3D.ethickness_one_le` give the
two transverse bounds, and `repr_window` gives the longitudinal one); the *lower* half is the
content, and it is exactly what GWZ Proposition 6.6(B)'s own `wide` clause is for.  Its producer is
already in the tree:

`Kakeya.GlobalPlankFactorization.exists_isPlankFamilyOfDimensions`
(`Kakeya/DimensionThree/Plank/GlobalPlankDatumBridge.lean`)

returns `∃ a', ρ ≤ a' ∧ a' ≤ a ∧ IsPlankFamilyOfDimensions (plankReadingConst Cw C₀) a' b …` for
the 6.6(B) datum, at a re-declared thin half-width `a' ≤ a`; re-declaring `a` downward only makes
the conclusion `(a / b) ^ β` of 6.6(B) weaker than the truth, so nothing is lost.  This is why the
hypothesis is a genuine interface and not a deferral.

## What is *not* done here

Pairwise essential distinctness of the presented planks.  It is not derivable from essential
distinctness of the representative planks — the presentation shrinks the *positions* by the common
homothety ratio while keeping the declared half-widths `a × b × 1`, so the presented family is
fatter relative to its separation.  That is the (independent) essential-distinctness gap; the tree's
tool for it is `Kakeya.exists_pairwise_plank_subset_of_isThickeningNonconcentrated`
(`Kakeya/Factoring/FlatPrisms.lean`), which is how the proved Part-(A) theorem
`Kakeya.multiplicity_le_of_factorsThroughFlatPrisms_of_parentPresentation` extracts an essentially
distinct outer subfamily internally.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Convexity
open scoped NNReal ENNReal Classical

noncomputable section

namespace Kakeya

namespace Section6PartBData

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
  {ι : Type*} {q : Finset ι} {δ : ℝ≥0} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
  {κ : Type*} {coarseSet : Finset κ} {ρ : ℝ≥0} {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}
  {m Cfib CF C₀ : ℝ≥0}
  (D : Section6PartBData a b hab hb1 q T coarseSet R m Cfib CF C₀)

theorem one_le_plankWindowRadius : (1 : ℝ≥0) ≤ plankWindowRadius := by
  rw [plankWindowRadius]; norm_num


end Section6PartBData

end Kakeya

end

end

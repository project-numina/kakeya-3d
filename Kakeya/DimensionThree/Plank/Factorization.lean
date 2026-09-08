/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank
public import Kakeya.PartialEstimates
public import Kakeya.Factorization
public import Kakeya.ShadedUniform
public import Kakeya.Uniform

/-!
# Main estimates from GWZ Section 6

This file carries the factorization data used by the statements of GWZ Section 6 —
`Kakeya.PlankFactorization`, `Kakeya.ContainsFlatDisc`, `Kakeya.GlobalPlankFactorization`,
`Kakeya.PersistentPlankFactorization` — the plank obstruction `Kakeya.convexHull_tubes_ne_prism`,
and the statement of Proposition 6.6(A) (`Kakeya.tubeMultiplicityOfLocalPlankFactorisation`,
vacuously true; see its docstring).  Proposition 6.6(B),
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation`, was stated here until it was proved; it now
lives, with its proof, in `Kakeya/DimensionThree/Plank/Prop66BClose.lean`, which imports this
file.  Lemma 6.4 is stated and proved elsewhere (see the note before Proposition 6.6 below).

-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Convexity ConvexSpaceBody
open scoped NNReal Real ENNReal

noncomputable section

namespace Kakeya

/-- A factorization whose outer bodies are `a × b × 1` planks.

**Warning: unsatisfiable over tubes.**  The field `parts_are_planks` asks the convex hull of each
block to *equal* an exact plank.  A `Finpartition`'s parts are nonempty, and by
`Kakeya.Plank.convexHull_biUnion_ne_of_tube` (`Kakeya/RelativePlank.lean`) the convex hull of a
nonempty family of `δ`-tubes with `δ > 0` is never an exact plank: a plank vertex has a
three-dimensional normal cone, while the boundary of a positive-radius tube is smooth.  So over any
family of positive-radius tubes with a nonempty index set this structure is uninhabited — see
`Kakeya.not_plankFactorization_of_tube` and `Kakeya.not_plankFactorization_of_shadedTube` — and a
theorem quantifying over it is vacuous.

Use `Kakeya.GlobalPlankFactorization` or `Kakeya.PersistentPlankFactorization`, below, for any
statement whose inner family is a family of tubes: both ask only for containment in a plank, not
equality with one.  `PlankFactorization` is retained only because the exact-hull reading is the
literal reading of [GWZ]'s "𝕎 is a family of `a × b × 1` planks factoring 𝕍" and it is worth
having the obstruction attached to a named object. -/
structure PlankFactorization {ι : Type*} [DecidableEq ι]
    (a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1)
    (s : Finset ι) (V : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (C₀ : ℝ≥0)
    extends ConvexSpaceBody.Factorization s V C₀ where
  parts_are_planks : ∀ part ∈ parts, ∃ Q : Plank a b hab hb1,
    part.convexHull_biUnion V = Q.toConvexSpaceBody

/-- A set contains a flat disc of radius `b` if it contains a translate of the `b`-ball in some
two-dimensional linear subspace. -/
def ContainsFlatDisc (b : ℝ≥0) (S : Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∃ (c : EuclideanSpace ℝ (Fin 3)) (P : Submodule ℝ (EuclideanSpace ℝ (Fin 3))),
    Module.finrank ℝ P = 2 ∧ ∀ v ∈ P, ‖v‖ ≤ (b : ℝ) → c + v ∈ S

/-- Containing a flat disc is antitone in the radius: a set holding a disc of radius `b` holds
every smaller concentric disc in the same plane. -/
theorem ContainsFlatDisc.mono {b b' : ℝ≥0} {S : Set (EuclideanSpace ℝ (Fin 3))}
    (h : ContainsFlatDisc b S) (hb : b' ≤ b) : ContainsFlatDisc b' S := by
  obtain ⟨c, P, hP, hmem⟩ := h
  exact ⟨c, P, hP, fun v hv hnorm => hmem v hv (hnorm.trans (by exact_mod_cast hb))⟩

/-- A global factorization of coarse tubes by bodies comparable to `a × b × 1` planks, with an
explicit transverse comparability constant `Cw ≥ 1`.

The factor bodies are their actual convex hulls. They need only be contained in representative
planks, rather than equal to exact rectangular prisms. The flat-disc condition supplies the
lower bound on their two long dimensions, up to `Cw`.

This is the repaired datum for GWZ Proposition 6.6(B).  It replaces the unsatisfiable
`Kakeya.PlankFactorization.parts_are_planks` (hull **equals** plank, refuted over tubes by
`Kakeya.convexHull_tubes_ne_prism`) by the pair `le_plank` (hull **≤** plank) and `wide` (a
transverse lower bound).  Both halves are needed: without `le_plank` the conclusion's `(a/b) ^ β`
is not paid for from above, and without `wide` the datum is satisfied by bodies far thinner than
`b` in the middle direction, for which the asserted gain `(a/b) ^ β` is simply false — take outer
bodies that are honest `a × a × 1` planks and declare `b := 1`.

**Why `wide` carries a constant.**  Requiring the disc radius to be exactly `min b (1/2)`,
with no constant, is *tight*, and jointly with `le_plank` it is unsatisfiable by the intended producer.  A covering or
John-ellipsoid argument applied to the hull `W` of a block of coarse tubes returns a two-sided
comparison with an absolute constant: `W ⊆ plank (C * a, C * b, 1)` and `W ⊇ disc (c * b)` with
`c < 1 < C`.  To feed the unconstanted structure one must pick a single middle half-width `B` with
`W ⊆ plank (·, B, ·)` — forcing `B ≥ C * b` — and `min B (1/2) ≤ c * b` — forcing `B ≤ c * b` when
`c * b < 1/2`.  Since `c * b < C * b`, no such `B` exists.  Dividing the disc radius by `Cw` is
exactly the slack needed, and it is the tree's established pattern: `Kakeya.IsPlankOfDimensions`
in `Kakeya/Factoring/FlatPrisms.lean` carries the same explicit `C ≥ 1` two-sidedly on all three
affine thicknesses.

Relaxing `wide` **weakens** the structure (`Kakeya.GlobalPlankFactorization.mono_Cw`), hence
strengthens any theorem quantifying over it; a consumer must therefore pay for `Cw`, and
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation`
(`Kakeya/DimensionThree/Plank/Prop66BClose.lean`) does so with the sub-polynomial budget
`Cw ≤ δ ^ (-η)` that the statement already spends on `Cpar` and `C₀`.

The pair is satisfiable, including by hulls of `ρ`-tube blocks: at `a = b = ρ ≤ 1 / 2` such a hull
contains `Metric.closedBall 0 ρ`, hence a flat `ρ`-disc, while fitting inside a `ρ × ρ × 1`
plank. -/
structure GlobalPlankFactorization {κ : Type*} [DecidableEq κ]
    (Cw a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1)
    (r : Finset κ) (R : κ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (C₀ : ℝ≥0)
    extends ConvexSpaceBody.Factorization r R C₀ where
  /-- The transverse comparability constant is at least one. -/
  one_le_Cw : 1 ≤ Cw
  /-- Every factor body is contained in a representative `a × b × 1` plank. -/
  le_plank : ∀ part ∈ parts, ∃ P : Plank a b hab hb1,
    part.convexHull_biUnion R ≤ P.toConvexSpaceBody
  /-- Every factor body contains a flat disc at the middle plank scale, up to the transverse
  comparability constant `Cw`. -/
  wide : ∀ part ∈ parts,
    ContainsFlatDisc (min b (1 / 2) / Cw) (part.convexHull_biUnion R).carrier


/-! ### The `parts_are_planks` obstruction

`Kakeya.tubeMultiplicityOfLocalPlankFactorisation` (GWZ 6.6(A)) below is stated for
factorizations of *tube* bodies whose parts' convex hulls are required to be **exactly equal** to
planks (`PlankFactorization.parts_are_planks`).  That requirement is unsatisfiable, and the next
two lemmas prove it: the convex hull of a nonempty finite family of `δ`-tubes with `δ > 0` is a
Minkowski sum `K + closedBall 0 δ`, hence has no corner, while a prism carrier has one.  So
6.6(A) is vacuously true; see its docstring.

`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` (GWZ 6.6(B)) is **no longer** stated over that
equality: it now takes a `Kakeya.GlobalPlankFactorization`, whose `le_plank` is an inclusion, and
so escapes this obstruction.  It is proved, in `Kakeya/DimensionThree/Plank/Prop66BClose.lean`;
see its docstring there.
-/

section PlankObstruction

open scoped Pointwise


end PlankObstruction

open Classical in
/-- **A factorization through fixed outer plank bodies.**

`Kakeya.PlankFactorization` requires `part.convexHull_biUnion V = Q.toConvexSpaceBody`, an equality
that any thinning of the inner family destroys — and which, over tubes of positive radius, no
family satisfies at all (see the warning on `PlankFactorization`).  That equality is not what the
consumers of GWZ Proposition 6.6 use.  GWZ Lemma 6.4 has no inner family at all, and GWZ Lemma 5.1
needs only that each inner body lies in the outer body of its own block, together with a Frostman
constant for that block.

`PersistentPlankFactorization` keeps exactly those: the outer bodies of the blocks actually used
*are* planks, the outer family is Katz--Tao, and each block is dense enough inside its own outer
body.  Crucially the outer bodies are *free data* on a `ConvexSpaceBody.FactorFamily` rather than
hulls of the inner blocks, so nothing forces them to be spanned by the inner family and the
obstruction of `Kakeya.Plank.convexHull_biUnion_ne_of_tube` does not apply: a `δ`-tube fits inside
an `a × b × 1` plank whenever `δ ≤ a`.  It is also stable under restricting the fibres while
holding the outer bodies fixed, which is what the joint regularization of
`Kakeya/RelativePlank.lean` produces.

This declaration lives here, rather than next to its main users in `Kakeya/RelativePlank.lean`,
for a historical reason: GWZ Proposition 6.6(B),
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation`, followed it in this file until it was proved
and moved to `Kakeya/DimensionThree/Plank/Prop66BClose.lean`.  That theorem is stated over
`Kakeya.GlobalPlankFactorization` above, not over this structure (see the section note below). -/
structure PersistentPlankFactorization {ι ω : Type*}
    (F : ConvexSpaceBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) ι ω)
    (a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1) (C₀ : ℝ≥0) : Prop where
  /-- The outer body of every block that still carries an inner member is an `a × b × 1` plank. -/
  outer_are_planks : ∀ j ∈ F.innerSet.image F.parent, ∃ Q : Plank a b hab hb1,
    F.outerBody j = Q.toConvexSpaceBody
  /-- The family of those outer bodies is Katz--Tao with constant `C₀`. -/
  outer_isKatzTao : IsKatzTao (F.innerSet.image F.parent) F.outerBody (C₀ : ℝ≥0∞)
  /-- Each block is, up to `C₀`, as dense inside its own outer body as the whole inner family is
  anywhere.  This is the Frostman input of GWZ Lemma 5.1. -/
  maxDensity_le_mul : ∀ j ∈ F.innerSet.image F.parent,
    maxDensity F.innerSet F.innerBody ≤
      (C₀ : ℝ≥0∞) * densityIn (F.fiber j) F.innerBody (F.outerBody j)

/-! ### GWZ Lemma 6.4

`Kakeya.FrostmanEstimate.plankEstimate` provides the plank estimate.

The two statements are *not* interchangeable, so 6.4 must not be re-stated here: the proved one
quantifies `∃ C_NC, 1 ≤ C_NC ∧ …` outermost and fixes `ι : Type u`, asks for the window as a
containment in `Metric.closedBall 0 plankWindowRadius` rather than through
`Kakeya.Plank.IsWindowedFamily`, and takes `Kakeya.Plank.IsThickeningNonconcentrated` in place of
the explicit thickening count.  The conclusion is identical. -/

/-! ### GWZ Proposition 6.6

The local statement below has contradictory hypotheses for nonempty families, as explained
in its docstring. `Kakeya.multiplicity_le_of_factorsThroughFlatPrisms'` uses a different
scale regime.

The global theorem `Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` uses
`Kakeya.GlobalPlankFactorization`, including the `Cw`-parameterised `wide` condition,
and is proved in `Kakeya/DimensionThree/Plank/Prop66BClose.lean`.
`PersistentPlankFactorization` is a different datum used in `Kakeya/RelativePlank.lean`.
-/


end Kakeya

end

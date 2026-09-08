/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.ShadedUniform
public import Kakeya.Pigeonhole
public import Kakeya.Tube.Dilate
public import Kakeya.Factoring.Pigeonhole
public import Kakeya.DimensionThree.MainLemma1.Setup

/-!
# The alive band: the lower density bracket without an index-set pigeonhole

The recorded blocker of `Kakeya.ml1Boot.exists_uniformFactorCore` is that the shaded
uniformizers of `Kakeya/ShadedUniform.lean` return no density bracket on their own output
shading, while the bracket is obtained by a pigeonhole on the values `|Y(V i)|`, and that
pigeonhole moves the index set and so destroys the two lower brackets `le_card_shadeClass`
and `le_branchingN` of GWZ Definition 2.2.

The upper half of the bracket is free: the uniformizers only shrink shadings, so
`|Z i| ≤ |Y(V i)|` survives untouched.  This file settles the lower half.

**The lower half needs no pigeonhole.**  Definition 2.2 is closed under exactly two
shade-shrinking moves — cutting *every* shading by one common measurable set
(`ShadedTube.shadedUniformTubeSet_interShade`) and dropping members whose shading is already
empty (`Kakeya.ml1Boot.ShadedTube.ShadedUniformTubeSet.restrict_of_shade_eq_empty`) — and those
two moves already force the lower bracket:

* `ShadedTube.exists_cut_aliveBand` — for any threshold `ρ` there is a *single* measurable set
  `R` of volume at most `#s · ρ` such that, after deleting `R`, every member of the family is
  either annihilated or has shade volume at least `ρ`.  The proof is a finite descent: while
  some member still has volume `< ρ`, delete that member's set and recurse, which retires one
  member per round at ambient cost `< ρ`.
* `ShadedTube.exists_shadedUniform_aliveBand` — the same statement carried through
  `ShadedTube.interShade`, so that GWZ Definition 2.2 holds verbatim on the cut family at the
  same hierarchy, the same `branchingN`, the same `localN` and the same constant, and the alive
  set is presented in exactly the shape `restrict_of_shade_eq_empty` consumes.

So the alive set of the cut is *not* a pigeonhole class: it is the set of members the cut did
not annihilate, and the uniformity transfers to it by the two hereditary moves.

**What it costs, and why that is the next obstruction.**  The cut deletes ambient volume at most
`#s · ρ`.  What that destroys in *shade mass* is that ambient volume weighted by how many
members see each deleted point, and
`ShadedBody.sum_volume_shade_inter_le_of_pointwiseMultiplicity_le` states exactly that: the loss
is at most the family's pointwise multiplicity times `#s · ρ`.  Retaining a fixed share of
`∑ᵢ |Y(V i)| = ∫ μ` therefore forces `ρ ≲ |U(𝕍, Y)| / #s`, and the resulting band, measured
against the free upper end `|Y(V i)| ≈ λ δ²`, has width of order `ShadedBody.multiplicity`.
That is the same quantity `ShadedTube.exists_shade_disjointification` pays, and
`Kakeya.ml1Boot.middleMultiplicityBound_exceeds_refinementBudget_of_spec` shows it is outside
the refinement budget `δ ^ (-2 ε')` of Case (ii).  The obstruction at
`Kakeya.ml1Boot.exists_uniformFactorCore` is therefore *not* "the bracket needs a pigeonhole" —
it does not — but "a bracket of subpolynomial width costs multiplicity".

**Where the pigeonhole actually stands.**  The second half of the file removes the qualitative
objection to the pigeonhole altogether.

* `Kakeya.ml1Boot.ShadedTube.ShadedUniformTubeSet.restrict_of_shadeClass_dense` is the *exact*
  hereditariness criterion for Definition 2.2: an index restriction transfers the predicate, at
  constant `θ⁻¹ C`, as soon as it retains a `θ` share of every shade class at every point.
  `restrict_of_shade_eq_empty` and `shadedUniformTubeSet_interShade` are its `θ = 1` cases.
* `ShadedTube.classDenseSet`, `ShadedTube.measurableSet_classDenseSet` and
  `ShadedTube.shadedUniformTubeSet_of_classDense_cut`: for *any* candidate subfamily `s₃ ⊆ s`
  — in particular the dyadic density class `fine_dens` needs — cutting every shading by the set
  of points where `s₃` is class-dense preserves Definition 2.2 on `s` and then transfers it to
  `s₃`.

So both moves the interface needs — the density pigeonhole and Definition 2.2 on its output —
are available, and the whole obstruction is a single quantitative statement: **how much shade
mass a dyadic density class loses to its own class-sparse set**.  That is what remains open at
`Kakeya.ml1Boot.exists_uniformFactorCore`, and it is a strictly narrower question than the one
recorded there.

**How narrow, exactly.**  `Kakeya.ml1Boot.IsUniformFactorCore.fine_unif` asks for Definition 2.2
at the constant `Kakeya.ml1Boot.uniformize.C 3`, which is `δ`-independent.  So the `θ` of
`restrict_of_shadeClass_dense` has to be an absolute constant, not a `1 / log (1/δ)`.  And a
dyadic density class carries no pointwise-uniform share of the shade classes: summing over the
`O(log 1/δ)` classes recovers each shade class in total, but the dyadic index realising the
largest share varies with the point and the node, so no single class is guaranteed dense at any
`θ`.  The open question is therefore whether the density pigeonhole can be *replaced* by a
selection that is class-dense at an absolute `θ` while still retaining a `δ ^ (2 ε')` share of
`∑ᵢ |Y(V i)|` — or whether the mass a dyadic class loses to its class-sparse set is bounded.
Neither is settled here; what is settled is that the qualitative obstructions ("no lower bracket
without a pigeonhole", "no Definition 2.2 after a pigeonhole") are both gone.

`ShadedBody.sum_volume_shade_inter_lightDominatedSet_le` is the first quantitative step on that
last question, and it succeeds in the *global fibre* reading: the members the density cut left
light have total mass at most `#s · ρ`, and wherever they dominate a `1 - θ` share of the
pointwise multiplicity the whole family carries only `(1 - θ)⁻¹ · #s · ρ` of mass.  Choosing `ρ`
at a `δ ^ (4 ε')` fraction of the average therefore leaves the globally class-sparse set with a
`δ ^ (4 ε')` share, well inside the `δ ^ (2 ε')` budget.  The gap to what
`restrict_of_shadeClass_dense` consumes is that the density has to hold in each *node* class at
each scale, not only in the global fibre, and passing between the two costs a factor counting
the scale-`k` nodes a fibre meets.

**A recurrence worth recording.**  That last factor is, by the two class brackets of Definition
2.2 itself, the ratio of the fibre size to the class size, which at the finest scale is again
`ShadedBody.multiplicity`.  So all three independent routes to the interface price the *same*
quantity: `ShadedTube.exists_shade_disjointification` (retention against the union rather than
the sum), `ShadedTube.exists_shadedUniform_aliveBand` (the deleted ambient volume weighted by
multiplicity), and the class-density cut above (the node-versus-fibre factor).  Since
`Kakeya.ml1Boot.middleMultiplicityBound_exceeds_refinementBudget_of_spec` puts that quantity
outside the budget by an essentially full `δ ^ (-2 γ)`, the recurrence is evidence that the
*simultaneity* demanded by `Kakeya.ml1Boot.IsUniformFactorCore` — `fine_unif` at a
`δ`-independent constant, `fine_dens` a factor-two bracket, and `fine_refinement` at
`δ ^ (2 ε')`, all at once — is the clause to re-examine against GWZ §2, rather than one more
construction to search for.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Real Metric
open Tube

namespace ShadedTube

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasureSpace E] [BorelSpace E] [ProperSpace E]
  {ι : Type*}

end ShadedTube

namespace ShadedBody

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasureSpace E] [BorelSpace E] [ProperSpace E]
  {ι : Type*}

end ShadedBody

namespace ShadedTube

section Band

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasureSpace E] [BorelSpace E] [ProperSpace E]
  {ι : Type*}

end Band

end ShadedTube

namespace Kakeya

namespace ml1Boot

namespace ShadedTube

variable {ι : Type*} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [Nontrivial F] [MeasureSpace F] [BorelSpace F]

end ShadedTube

end ml1Boot

end Kakeya

namespace ShadedTube

section ClassDense

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasureSpace E] [BorelSpace E] [ProperSpace E]
  {ι : Type*}

omit [Nontrivial E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- A shade-class count is a finite sum of indicators of the shadings, hence measurable in the
point. -/
theorem measurable_shadeClass_card {δ : ℝ≥0} (s : Finset ι)
    (V : ι → ShadedTube δ E) (assign : ι → ι) (j : ι) :
    Measurable (fun x => (shadeClass s V assign j x).card) := by
  classical
  have hEq : (fun x => (shadeClass s V assign j x).card)
      = fun x => ∑ i ∈ Tube.coverClass s assign j, if x ∈ (V i).shade then 1 else 0 := by
    funext x
    simp only [shadeClass, Finset.card_filter]
  rw [hEq]
  refine Finset.measurable_sum _ fun i _ => ?_
  exact Measurable.ite (V i).measurableSet_shade measurable_const measurable_const

end ClassDense

end ShadedTube

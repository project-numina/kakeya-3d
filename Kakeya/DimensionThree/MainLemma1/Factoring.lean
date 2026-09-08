/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Asymptotics
public import Kakeya.Factoring.FlatPrisms
public import Kakeya.Factoring.RhoTubesUndilated
public import Kakeya.Frostman
public import Kakeya.Tube.Dilate
public import Kakeya.Tube.IntersectionVolume
public import Kakeya.Multiplicity
public import Kakeya.RelativePlank

/-!
# Main Lemma 1: named parent families and the two-scale factoring chain

This file formalizes the "general infrastructure" part of Case (ii) of GWZ Main Lemma 1:
the vocabulary of *named parent families* (the parent-family construction), the
pigeonholing that replaces GWZ's "abusing notation, we may suppose that all the families in
sight are uniform" (the uniformization argument), and the composition of two
applications of GWZ Lemma 5.11 that produces the triple-product bound
(the two-scale factoring argument).

## The one-scale loss constant, and why it carries two binders

`ShadedBody.shadingMultiplicityEstimateForRhoTubes`, which
`Kakeya.ml1Boot.factorOneScale.C` used to be read off, was refuted and deleted; the surviving
estimate is `ShadedBody.shadingMultiplicityEstimateForRhoTubesUndilated_lam` in
`Kakeya/Factoring/RhoTubesUndilated.lean`, whose loss constant depends on the ambient dimension,
on the inner cardinality and on the inner tube scale.

`Kakeya.ml1Boot.factorOneScale.C` is that constant, `(N, σ) ↦ …`, and
`Kakeya.ml1Boot.exists_factorOneScale` is stated and proved at it.  Every statement downstream
carries the same two binders, read at the data actually in scope: the fields of
`Kakeya.ml1Boot.IsFactorOneScale` and `Kakeya.ml1Boot.IsUniformFactorCore` at `#s` and the
inner tube scale, and the fields of `Kakeya.ml1Boot.IsFactorTwoScales` through
`Kakeya.ml1Boot.factorTwoScales.C`, which is the *product* of the two applications' constants
and not the square of one of them — the two applications are made at different cardinalities
and different scales, and no monotonicity of the loss constant is available to compare them.

The lemmas that merely *transport* the constant — `Kakeya.ml1Boot.multiplicity_le_of_middle`,
and the threshold and collapse lemmas of `Rescaling/` — carry it as a free parameter instead,
which is strictly more general and is what lets a caller supply the instantiated value.

The dilate chain is deliberately **not** stated at this constant; see
`Kakeya.ml1Boot.factorOneScaleUniformDilate.C`.

Throughout, `δ` is an **auxiliary small parameter** and `σ`, `ρ`, `τ`, `θ` are **tube
scales**, with `δ ≤ σ ≤ ρ ≤ 1`.  Every "for all sufficiently small" clause refers to `δ`
and to `δ` only, and every subpolynomial loss is a power of `δ` and not of a tube scale:
the tube scales occurring in the application are `δ / τ`, `τ / θ` and `θ`, none of which is
small.

## Blueprint correspondence

Each of the three main lemmas states its conclusion as a `Prop`-valued structure whose
fields are the numbered items of the corresponding blueprint lemma.

* `Kakeya.ml1Boot.IsParentFamily` ↔ `def:ml1bootParentFamily`
* `Kakeya.ml1Boot.IsUniformRefinement` ↔ `lem:ml1bootUniformizePair`, items (i)–(vii) and (ix)
* `Kakeya.ml1Boot.IsFactorOneScale` ↔ `lem:ml1bootFactorOneScaleUniform`, items (a)–(g)
* `Kakeya.ml1Boot.IsFactorTwoScales` ↔ `lem:ml1bootFactorTwoScales`, items (a)–(h)

A blueprint item that is a conjunction of several inequalities becomes several fields, one
per inequality, so that consumers name what they use instead of projecting into a tuple.

## Divergence from the informal statement

*Items (viii) and (ix) of `lem:ml1bootUniformizePair`.*  Item (viii)
`item:uniformizeFibreUnif` is the *containment*-fibre clause: it speaks about the fibres of
the parent families internal to the uniformity data.  Those families are exposed by
`ShadedTube.ShadedUniformTubeSet` through its hierarchy `tubeUniform.cover`, so phrasing it
as a field of the conclusion would mean naming that data; it is therefore not a field of
`Kakeya.ml1Boot.IsUniformRefinement`.

What the assembly of Case (ii) actually consumes is item (ix)
`item:uniformizeGivenFibreUnif`, uniformity of the *parent-map* fibres of the *given* parent
families — `Kakeya.ml1Boot.multiplicity_le_middle` is applied to `fibre t'τ pθ l₀` — and that
is what the field `Kakeya.ml1Boot.IsUniformRefinement.fibreUnif` records, propagated to
`Kakeya.ml1Boot.IsFactorOneScale.fibreUnif` and
`Kakeya.ml1Boot.IsFactorTwoScales.midFibreUnif`.

Every fibre-uniformity field on the live chain — those two,
`Kakeya.ml1Boot.IsUniformFactorCore.fibreUnif` and
`Kakeya.ml1Boot.IsUniformFactorCoreDilate.fibreUnif` — is stated at the **one-sided**
`Kakeya.IsFlatPrismUniform`, GWZ Definition 2.2 minus `le_card_shadeClass` and `branchingN_le`.
Nothing anywhere reads either dropped clause, and read one-sidedly the fibre clause is a
consequence of the global one at the same constant
(`Kakeya.ml1Boot.nonempty_isFlatPrismUniform_fibre_of_shadedUniformTubeSet`).  The two-sided
reading was a typing commitment inherited from
`Kakeya.ml1Boot.multiplicity_le_middle`, and it has been removed; the docstring of
`Kakeya.ml1Boot.exists_uniformFactorCore` records what that took and which declarations moved.
`Kakeya.ml1Boot.IsUniformRefinement.fibreUnif` is the one that remains two-sided, and it is inert:
its producer `Kakeya.ml1Boot.exists_uniformRefinement` is *false*, refuted in this file by
`Kakeya.ml1Boot.not_exists_uniformRefinement`, so nothing consumes that structure.  Its uniformity
constant is
`Kakeya.ml1Boot.uniformize.C 3`, which depends on the ambient dimension alone; that is what
lets the constant `Cunif` of
`Kakeya.ml1Boot.multiplicity_le_middle` be fixed before the `∀ᶠ δ in 𝓝[>] 0`.  As the
blueprint records, item (ix) is not implied by item (viii) and is an obligation on the
refinement construction rather than a consequence of `unif`: a parent-map fibre is a
subfamily of a containment fibre, and uniformity does not pass to arbitrary subfamilies.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya

namespace ml1Boot

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### Named parent families -/

/-- The fibre `s[k] = {i ∈ s : p i = k}` of a parent map `p` over the parent index `k`.
The blueprint writes `𝕍[V_{ρ,k}]` for the corresponding subfamily `(V_i)_{i ∈ s[k]}`, and
`𝕍[V_{ρ,k}]|_{s'}` for `𝕍|_{s[k] ∩ s'}`, which here is `fibre (s ∩ s') p k`. -/
def fibre {ι κ : Type*} [DecidableEq κ] (s : Finset ι) (p : ι → κ) (k : κ) : Finset ι :=
  s.filter fun i => p i = k

/-- **Restricting to a set of parents deletes only whole fibres.**

If `s' = {i ∈ s : p i ∈ u}` then for every `k ∈ u` the fibre of `s'` over `k` is the *whole*
fibre of `s` over `k`: the restriction removes exactly those `i` whose parent is outside `u`,
and none of those lies over a `k ∈ u`.

This is the index-alignment crux of the two-scale factoring step, blueprint
`lem:ml1bootFactorTwoScales`.  That step has **no Lean producer**:
`exists_factorTwoScales` is not a declaration, and neither is `exists_twoScaleFactorPair`; only
the target structure `Kakeya.ml1Boot.IsFactorTwoScales` and the assembly
`Kakeya.ml1Boot.isFactorTwoScales_of_factorPair` exist.  See blueprint
`note:ml1bootCaseTwoConstructionLayerEmpty`.  GWZ writes
"abusing notation, we will continue to refer to these refinements as …" when the second
application of the one-scale step refines the middle family a second time; the Lean
bookkeeping has to pull the fine family back along the parent map, and this lemma is what
makes the pull-back free on every fibre that survives. -/
theorem fibre_filter_mem {ι κ : Type*} [DecidableEq κ] (s : Finset ι) (p : ι → κ)
    (u : Finset κ) {k : κ} (hk : k ∈ u) :
    fibre (s.filter fun i => p i ∈ u) p k = fibre s p k := by
  unfold fibre
  rw [Finset.filter_filter]
  exact Finset.filter_congr (fun i hi => by
    constructor
    · intro h
      exact h.2
    · intro h
      exact ⟨by rw [h]; exact hk, h⟩)

/-- **A parent family for `𝕍` at scale `ρ`**: a finite
index set `t`, an injectively indexed family `𝕍_ρ = (V_{ρ,k})_{k ∈ t}` of `ρ`-tubes, and a
map `p : ι → κ` sending `s` into `t` with `V_i ⊆ V_{ρ,p(i)}` for every `i ∈ s`.

The scale ordering `0 < σ ≤ ρ ≤ 1` of the blueprint is *not* part of this predicate: it is
a hypothesis of every lemma that consumes a parent family, and keeping it out here lets the
same predicate be reused at the scales `δ ≤ τ`, `τ ≤ θ` without repetition.

Injectivity is stated for the underlying convex bodies rather than for the `Tube` records,
which is what the downstream counting arguments use. -/
structure IsParentFamily {ι κ : Type*} {σ ρ : ℝ≥0} (s : Finset ι) (V : ι → Tube σ E)
    (t : Finset κ) (Vρ : κ → Tube ρ E) (p : ι → κ) : Prop where
  /-- The parent map sends `s` into the parent index set `t`. -/
  mapsTo : ∀ i ∈ s, p i ∈ t
  /-- The parent family is indexed injectively. -/
  injOn : Set.InjOn (fun k => (Vρ k).toConvexSpaceBody) t
  /-- Each member of `𝕍` is contained in its parent. -/
  le_parent : ∀ i ∈ s, (V i).toConvexSpaceBody ≤ (Vρ (p i)).toConvexSpaceBody

/-- **A `c`-dilate parent family for `𝕍` at scale `ρ`**: the same data `(t, 𝕍_ρ, p)` as
`Kakeya.ml1Boot.IsParentFamily`, with the containment clause weakened from
`V i ≤ V_{ρ, p i}` to `V i ≤ c · V_{ρ, p i}`, the `c`-dilate `Kakeya.Tube.dilate` of the
parent about its centre.

For `c = 1` the homothety is the identity and the notion is *exactly*
`Kakeya.ml1Boot.IsParentFamily`, so this is a genuine weakening and every parent family is a
`c`-dilate parent family for every `c ≥ 1`.

The weakening is forced longitudinally: a `Kakeya.Tube` has a core segment of length exactly
`1`, hence circumradius `1/2 + O(b)`, whereas the planks of this development have
`ethickness … 0` anywhere up to `1`, a bound that blueprint
`note:ml1bootPlankInTubeVacuous` shows cannot be improved.  The tube attached to a plank by
`Kakeya.ml1Boot.exists_plank_tube_of_thickness_le_one` therefore contains the plank only
after dilation by `2`; the applications use `c = 2` and nothing else.

Every consumer pays only a constant: in `ℝ³` a dilation by `c` multiplies volumes by `c ³`
(`Kakeya.Tube.tubeDilateVolume`), and the containment clause is used downstream only through
a volume comparison. -/
structure IsParentFamilyDilate [Nontrivial E] {ι κ : Type*} {σ ρ : ℝ≥0} (c : ℝ)
    (s : Finset ι) (V : ι → Tube σ E) (t : Finset κ) (Vρ : κ → Tube ρ E) (p : ι → κ) :
    Prop where
  /-- The dilation ratio is at least `1`, so that this weakens `IsParentFamily`. -/
  one_le : 1 ≤ c
  /-- The parent map sends `s` into the parent index set `t`. -/
  mapsTo : ∀ i ∈ s, p i ∈ t
  /-- The parent family is indexed injectively. -/
  injOn : Set.InjOn (fun k => (Vρ k).toConvexSpaceBody) t
  /-- Each member of `𝕍` is contained in the `c`-dilate of its parent. -/
  le_parent_dilate : ∀ i ∈ s, (V i).toConvexSpaceBody ≤ Tube.dilate (Vρ (p i)) c

/-- **Bounded overlap of a parent family**.

A parent family `(t, 𝕍_ρ, p)` for `𝕍 = (V i)_{i ∈ s}` has *overlap bounded by `Co`* when, for
every `ρ`-tube `W`, at most `Co` of the parents *meet `W` through `𝕍`* — share a member of `𝕍`
with `W`.

This is `Tube.UniformTubeSet.boundedOverlap` transcribed from the nodes of a hierarchy at
a grid index to a free parent family, word for word: taking `t` to be the node index set, `𝕍_ρ`
the node tubes at that index and `𝕍` the leaves recovers the field exactly, which is what
`Kakeya.ml1Boot.hasBoundedOverlap_nodes` records.  So at the Case (ii) call sites the hypothesis
is discharged by a single field read, with `Co = C_ds`.

The relativization by `𝕍` is what makes the condition satisfiable at all: bare intersection with
`W` is not a bounded condition, a fixed `ρ`-tube being met, as a set, by `ρ`-tubes of every
direction.

It is *not* implied by `Kakeya.ml1Boot.IsParentFamily`; see blueprint
`note:ml1bootEssDistinctParents` for the family that violates it, `δ ^ (-1)` transverse translates
of one `ρ`-tube by multiples of `δ ^ 10`, all containing every leaf.

It does **not**, however, buy an essentially distinct selection at a subpolynomial cost.  Parents
that are axial slides of one another by `≤ c_*` fail to be essentially distinct while their leaves
sit in no common `ρ`-tube, so a family of `≍ ρ ⁻¹` of them has overlap bounded by `1`; that is
`Kakeya.ml1Boot.not_exists_essDistinct_parentFamily`, which refutes the scale-free form of
`Kakeya.ml1Boot.exists_essDistinct_parentFamily` *with* this hypothesis in force.  The retention
such a selection can promise is `c ρ / Co`, and that is what the surviving statement assumes.

The definition itself now lives upstream, as `Tube.HasBoundedOverlap` in
`Kakeya/Uniform.lean`, next to the field it transcribes and where the `ShadedBody` forms of GWZ
Lemma 5.11 can also reach it; this is the `ml1Boot` name for it, and the two are the same
`Prop`. -/
abbrev HasBoundedOverlap {ι κ : Type*} {σ ρ : ℝ≥0} (s : Finset ι) (V : ι → Tube σ E)
    (t : Finset κ) (Vρ : κ → Tube ρ E) (Co : ℝ≥0) : Prop :=
  Tube.HasBoundedOverlap s V t Vρ Co

/- **Moved interface: essentially distinct parents of a boundedly overlapping parent family,
at a cost
`δ ^ (-ε')` and under a scale hypothesis**.

> **The hypothesis-free form of this statement — the same conclusion for every `δ ≤ σ ≤ ρ ≤ 1` —
> is false**, and `Kakeya.ml1Boot.not_exists_essDistinct_parentFamily` proves its negation.  What
> is false is the *size* of the loss, not the shape of the conclusion: the loss must be a power of
> the parent scale `ρ` and cannot be a power of `δ` alone.  The statement below is the repaired
> one: it carries the scale hypothesis `δ ^ ε' ≤ c ρ / Co`, which the refuting pencil violates.
> The refutation next door is retained as the record of why that hypothesis is in the signature;
> do not drop the hypothesis, and do not delete the refutation.  See "The bounded-overlap
> hypothesis is not enough" below.

Given a uniform family of shaded, pairwise essentially distinct `σ`-tubes in `B₁ ⊆ ℝ³` and a
parent family for it at a scale `ρ ≥ σ` **whose overlap is bounded by `Co`** in the sense of
`Kakeya.ml1Boot.HasBoundedOverlap`, one may discard all but a pairwise essentially distinct set
`t'` of parents, keeping the leaves that lie over `t'`, and retain a `δ ^ ε'` share of **one
caller-chosen weight** `w` on the leaves — *provided* `δ ^ ε'` is at most the honest retention
`c ρ / Co` of a greedy selection, which is the hypothesis `δ ^ ε' ≤ c ρ / Co`.

## What the greedy route actually delivers, and how the statement was fitted to it

The route is: choose `t' ⊆ t` maximal pairwise essentially distinct, greedily along the order of
*decreasing fibre weight* `k ↦ ∑ i ∈ fibre s p k, w i`, and put `s' = {i ∈ s : p i ∈ t'}`.
Four consequences, each of which is a clause below.

* *Leaves are discarded, never reassigned.*  Sending the leaves of a discarded parent to its
  representative would break `Kakeya.ml1Boot.IsParentFamily.le_parent`: two parents that fail to
  be essentially distinct have large intersection, which is not containment, so a leaf of one
  need not lie in the other.  So `s'` is a *filter* along `p`, and `IsParentFamily s' _ t' Vρ p`
  holds with `mapsTo` — the clause `∀ i ∈ s', p i ∈ t'` — true by construction.
* *The fibres over the retained parents are untouched.*  `Kakeya.ml1Boot.fibre_filter_mem`:
  restricting to a set of parents deletes only **whole** fibres, so for `k ∈ t'` one has
  `fibre s' p k = fibre s p k` on the nose.  The fibrewise Frostman clause below is therefore
  delivered with *no loss at all*, the stated `δ ^ (-ε')` being pure slack; this is what makes it
  legitimate to state it in the shape of `Kakeya.ml1Boot.IsUniformRefinement.fibreFrostman`,
  with the side condition at the **fibre** and not at the whole family, which is the shape the
  Case (ii) repair consumes.
* *The retention is a constant, and it is for the weight the greedy was ordered by.*  Each
  discarded `k` is charged to the representative `r k ∈ t'` it fails to be essentially distinct
  from; bounded overlap caps `|r ⁻¹ k'| ≤ Co`, and the ordering gives
  `∑_{fibre s p k} w ≤ ∑_{fibre s p (r k)} w`.  Summing over the fibres, which partition `s`,
  gives `∑ i ∈ s, w i ≤ Co * ∑ i ∈ s', w i`, and a constant fixed before `δ` is absorbed into
  `δ ^ (-ε')`.
* *One weight, not two.*  The weight is a **parameter** because no essentially distinct selection
  can retain a constant share of two incomparable weights at once, and the two the Case (ii)
  chain wants — the counting weight `w = 1` and the shade mass `w i = volume (V i).shade` — are
  incomparable.  Two parents that fail to be essentially distinct, carrying `(|s[k]|, mass) =
  (M, 1/M)` and `(1, 1)` respectively: exactly one survives, and whichever it is, one of the two
  shares is `≈ 1/M`.  Nothing in the hypotheses forbids this — `ShadedTube.ShadedUniformTubeSet`
  controls the *local* multiplicity of the shadings, never the individual volumes
  `volume (V i).shade` — so the two shares are genuinely alternatives.  Callers pick: `w = 1`
  gives the cardinality share, from which the *global* Frostman transport follows through
  `ConvexSpaceBody.frostmanConstIn_subfamily_le`; `w i = volume (V i).shade` gives the shade-mass
  share and hence `ShadedBody.IsCRefinement`, which is
  `Kakeya.ml1Boot.essDistinct_parentFamily_isCRefinement`.

## The bounded-overlap hypothesis is not enough

*Without bounded overlap.* Without `hoverlap` the statement is false.  Fix a `ρ`-tube
`V₀` in `B₁`, let the leaves be pairwise essentially distinct `σ`-tubes well inside `V₀`, and let
`t` index `M = δ ⁻¹` translates of `V₀` by distinct multiples of `δ ^ 10` in a transverse
direction.  These are distinct convex bodies, so `Kakeya.ml1Boot.IsParentFamily.injOn` holds, and
each still contains every leaf, so `le_parent` holds; split the leaves evenly along `p`.  Any two
parents overlap in `(1 - o(1))` of their volume, so every pairwise essentially distinct `t' ⊆ t`
is a singleton, whence at `w = 1` the retention reads `1 ≤ δ ^ (1 - ε')`.  That configuration does
violate bounded overlap: at `W = Vρ k₀` all `δ ⁻¹` parents meet `W` through `𝕍`.

*With bounded overlap.* Adding `hoverlap` does not suffice. Nearly-coincident parents
carrying leaves need not meet each other through `𝕍`. However, placing every leaf of `k'`
inside `Vρ k' \ Vρ k` does not by itself give a bounded-overlap counterexample:
`Kakeya.Tube.HasBoundedOverlap` quantifies over **every** `ρ`-tube `W`, including tubes
outside the parent family `𝕍_ρ`.  Two parents that
overlap in `0.9 v` are within `O(ρ)` of one another, so the `ρ`-tube on the core of a leaf of `k`
contains a leaf of `k'` as well, and `Co` is forced up after all.

*The counterexample that does work.*  Separate the parents **axially** instead of transversally.
A `Kakeya.Tube` has a core of length exactly `1`, so containment in a `ρ`-tube pins the axial
position to within `3 ρ` (`Kakeya.Tube.endpoints_close_of_body_le`), while an axial slide of
length up to `c_* = 1 / 12` leaves two `ρ`-tubes overlapping in `≥ 3/4` of their volume
(`Kakeya.Tube.not_essDistinct_of_axial_slide`).  Between `3 ρ` and `c_*` there is room for
`M ≍ ρ ⁻¹` parents that pairwise fail to be essentially distinct while no `ρ`-tube whatever
contains two leaves: overlap `Co = 1`, and the retention is `1 / M ≍ ρ`.  Taking
`ρ ≍ σ ^ (1/2) ≍ δ ^ (1/2)` makes `M ≍ δ ^ (-1/2)` and refutes the statement for every
`ε' ≤ 1/8`.  This is `Kakeya.ml1Boot.not_exists_essDistinct_parentFamily`; the pencil is
`Kakeya.ml1Boot.essDistinctCex.leaf`.

*The repair, which is what is stated below.*  The honest retention of a greedy essentially
distinct selection is `c ρ / Co` with `c` dimensional, not `δ ^ ε'`: the axial position is the one
tube parameter that essential distinctness does not separate but bounded overlap does, which is
the same `ρ ^ (-5)` against `ρ ^ (-4)` discrepancy recorded in
`Kakeya/DimensionThree/BoundedOverlapCount.lean`.  So the statement becomes true — with its scale hypothesis explicit — on adding the scale hypothesis `δ ^ ε' ≤ c ρ / Co` to the ladder
`δ ≤ σ → σ ≤ ρ → ρ ≤ 1`, with `c` a constant depending on the ambient dimension alone.  Nothing
else changes.  The axial pencil violates it: there `ρ ≍ δ ^ (1/4)` while `ε' ≤ 1/8` keeps
`δ ^ ε' ≥ δ ^ (1/8)`, so `δ ^ ε' ≤ c ρ / Co` fails at every large stage of the pencil for each
fixed `c > 0`, which is precisely why the refutation no longer applies.  In the intended
application the loss is harmless: the module docstring records that the tube scales occurring
there are `δ / τ`, `τ / θ` and `θ`, none of which is small, so `c ρ / Co` is a constant absorbed
into `δ ^ (-ε')`.

## Why the constant is existentially quantified, and quantified outermost

`c` is *not* given a value. Pinning a numeral would therefore be a guess in the dangerous direction — `c` is
a *small* constant standing on the large side of a hypothesis, so choosing it too large makes the
statement false again, exactly the failure this repair corrects. It is instead returned as
`∃ c : NNReal, 0 < c ∧ …`, which is the honest reading "there is a dimensional constant `c`". Since it stands outside `ε'`, `Cunif` and `Co`, it may depend on none of them, only on the ambient
dimension, which `hdim` pins to `3`; that placement is what keeps this the strongest form of the
repair rather than a weaker one in which the constant is allowed to chase the other parameters. Consequently no `Constant in Lemma` definition accompanies it: there is no Lean definition to
point `\lean{…}` at until the greedy bound is proved, at which point the witness that proof
produces should be promoted to a named definition in the style of
`Kakeya.Tube.overlapConstBOTight`.

## How the repair reaches the consumer

Adding a hypothesis changes the arity, and the sole code consumer,
`Kakeya.ml1Boot.exists_repairEssDistinct` (`Kakeya/DimensionThree/MainLemma1/Repair.lean`), reads
this statement through `filter_upwards` and applies it positionally at `(σ, ρ) = (δ, θ)` and
`(δ, τ)`, each at `ε' / 2`.  That consumer quantifies `τ` and `θ` over the whole ladder
`δ ≤ τ ≤ θ ≤ 1`, so it cannot pay `δ ^ (ε'/2) ≤ c τ / Co` from its own signature: it was
over-general in exactly the same way, and was itself false for that reason.  The repair is
therefore a two-declaration change and has been made as one.  The consumer now carries the single
hypothesis `δ ^ (ε'/2) ≤ c τ / Co` — at the fine scale `τ ≤ θ`, from which the coarse instance
follows — and passes on the very `c` obtained here.  `exists_repairEssDistinct` has no code
consumers of its own, so the thread stops there and nothing further had to pay.

*Unaffected by all of this.*  The proposition becomes vacuous — on taking `s' = s`, `t' = t` — as
soon as the hypothesis `hed` of the `ShadedBody` form of GWZ Lemma 5.11 is weakened to
the same bounded-overlap condition.  Note that the blueprint statement of that lemma asks for
pairwise essential distinctness and **not** for bounded overlap, so that weakening is a change to
an accepted interface rather than a correction of its Lean transcription: it *merges* this
obligation into that one rather than discharging either, and it makes the loss constant depend on
`Co`.  See blueprint `note:ml1bootEssDistinctParents`.

At the Case (ii) call sites `hoverlap` is one field read,
`Kakeya.ml1Boot.hasBoundedOverlap_nodes`, with `Co = C_ds`, and both applications run on the
**leaves**: the coarse one takes the `θ`-node family with the composed parent map, so no shading
of a parent tube is ever needed and the shading and uniformity hypotheses stay where the route
uses them, on `𝕍`. Blueprint `note:ml1bootRepairEDCoarseShading`. -/
/-! ### The counterexample: a boundedly overlapping parent family with no essentially distinct
subfamily

`Kakeya.ml1Boot.not_exists_essDistinct_parentFamily` below refutes the statement above *read
without its scale hypothesis* — which is why that hypothesis is there.  The witness is an *axial
pencil*: `M ≍ ρ ⁻¹` leaves whose cores are unit segments in one common
direction, spaced `7 ρ` apart along that direction and displaced transversally by `3 σ` per step,
each with the `ρ`-tube on its own core as its parent.

Three elementary facts drive it, and all three are already in the development.

* **The parents pairwise fail to be essentially distinct.**  They are axial slides of one another
  by at most `7 ρ M ≤ c_* = 1 / 12`, and `Kakeya.Tube.not_essDistinct_of_axial_slide` says an
  axial slide of that range overlaps the original in `≥ 3/4` of its volume.  No volume of an
  intersection is ever computed.
* **The overlap is bounded by `Co = 1`.**  A `Tube` has a core of length exactly `1`, so
  `Kakeya.Tube.endpoints_close_of_body_le` turns `V i ≤ W` into "the endpoints of `V i` and `W`
  agree to within `3 ρ`".  Two leaves `7 ρ` apart along the core direction therefore never lie in
  a common `ρ`-tube, and a leaf lies in no parent but its own.  This is the point the docstring
  above misses: `Kakeya.Tube.HasBoundedOverlap` quantifies over **every** `ρ`-tube `W`, and the
  refuting paragraph of that docstring only tests `W = V_ρ k`.
* **The leaves are pairwise essentially distinct, indeed disjoint.**  Consecutive cores are
  `3 σ` apart in the transverse direction `e₂`, and a leaf is confined to the slab
  `|⟪·, e₂⟫ - 3 σ i| ≤ σ`; the slabs are disjoint.

Uniformity of the leaf family is *not* constructed by hand: `Kakeya.Tube.exists_uniformTubeSet_subfamily_ssf`
refines any family in `B₁` to a uniform subfamily at the grid length `Tube.ssfGridLen σ` with a
dimensional constant, at a cost `σ ^ (-ε')`, and the shading clauses of
`ShadedTube.ShadedUniformTubeSet` are vacuous for the empty shading — which the statement above
permits, since it constrains no shading density.

The scales are taken along the sequence `σ = 2 ^ (-8n)`, `ρ = 2 ^ (-(2n+9))`, `M = 2 ^ (2n+1)`, so
that `M ≍ σ ^ (-1/4)` beats the two losses `σ ^ ε'` (uniformization) and `δ ^ ε'` (retention)
whenever `ε' ≤ 1/8`. -/

/-- The first standard basis vector of `ℝ³`: the common core direction of every tube of the
counterexample family `Kakeya.ml1Boot.essDistinctCex.leaf`. -/
noncomputable def essDistinctCex.e₁ : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 0 (1 : ℝ)

/-- The second standard basis vector of `ℝ³`: the direction of the transverse displacement that
makes the leaves of `Kakeya.ml1Boot.essDistinctCex.leaf` pairwise disjoint. -/
noncomputable def essDistinctCex.e₂ : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 1 (1 : ℝ)

namespace essDistinctCex

/-! #### The two coordinates the argument uses

Everything below is read off two orthonormal directions: `e₁`, along which containment in a
unit-core tube pins the axial position, and `e₂`, along which the leaves are separated. -/

theorem norm_e₁ : ‖e₁‖ = 1 := by
  simp [e₁]

theorem norm_e₂ : ‖e₂‖ = 1 := by
  simp [e₂]

/-- The axial coordinate of the `i`-th core of the pencil: the cores are spaced `7 ρ` apart along
the common direction `e₁`, and centred so that the whole pencil lies in `B₁`. -/
noncomputable def axial (ρ : ℝ≥0) (i : ℕ) : ℝ := 7 * (ρ : ℝ) * i - 1 / 2

/-- The transverse coordinate of the `i`-th core of the pencil: consecutive cores are `3 σ` apart
along `e₂`, which is what makes the leaves disjoint. -/
noncomputable def trans (σ : ℝ≥0) (i : ℕ) : ℝ := 3 * (σ : ℝ) * i

/-- The starting endpoint of the `i`-th core of the pencil. -/
noncomputable def base (σ ρ : ℝ≥0) (i : ℕ) : EuclideanSpace ℝ (Fin 3) :=
  (axial ρ i) • e₁ + (trans σ i) • e₂

theorem dist_base (σ ρ : ℝ≥0) (i : ℕ) : dist (base σ ρ i) (base σ ρ i + e₁) = 1 := by
  rw [dist_self_add_right]
  rw [norm_e₁]

/-- The `i`-th **leaf** of the counterexample: the `σ`-tube whose core is the unit segment from
`base σ ρ i` to `base σ ρ i + e₁`. -/
noncomputable def leaf (σ ρ : ℝ≥0) (i : ℕ) : Tube σ (EuclideanSpace ℝ (Fin 3)) :=
  Tube.mk' σ (dist_base σ ρ i)

/-- The `i`-th **parent** of the counterexample: the `ρ`-tube on the core of the `i`-th leaf. -/
noncomputable def parent (σ ρ : ℝ≥0) (i : ℕ) : Tube ρ (EuclideanSpace ℝ (Fin 3)) :=
  (leaf σ ρ i).rescale ρ

/-- The `i`-th leaf with the **empty** shading.  The statement refuted below constrains no shading
density, so the empty shading is admissible, and it makes every shading clause of
`ShadedTube.ShadedUniformTubeSet` vacuous. -/
noncomputable def shadedLeaf (σ ρ : ℝ≥0) (i : ℕ) :
    ShadedTube σ (EuclideanSpace ℝ (Fin 3)) where
  toTube := leaf σ ρ i
  shade := ∅
  measurableSet_shade := MeasurableSet.empty
  shade_subset := Set.empty_subset _

@[simp] theorem leaf_x (σ ρ : ℝ≥0) (i : ℕ) : (leaf σ ρ i).x = base σ ρ i := rfl

@[simp] theorem leaf_y (σ ρ : ℝ≥0) (i : ℕ) : (leaf σ ρ i).y = base σ ρ i + e₁ := rfl

@[simp] theorem parent_x (σ ρ : ℝ≥0) (i : ℕ) : (parent σ ρ i).x = base σ ρ i := rfl

@[simp] theorem parent_y (σ ρ : ℝ≥0) (i : ℕ) : (parent σ ρ i).y = base σ ρ i + e₁ := rfl

@[simp] theorem shadedLeaf_toTube (σ ρ : ℝ≥0) (i : ℕ) :
    (shadedLeaf σ ρ i).toTube = leaf σ ρ i := rfl

@[simp] theorem shadedLeaf_shade (σ ρ : ℝ≥0) (i : ℕ) : (shadedLeaf σ ρ i).shade = ∅ := rfl

theorem parent_direction (σ ρ : ℝ≥0) (i : ℕ) : (parent σ ρ i).direction = e₁ := by
  simp [Tube.direction]

/-- **The parents of the pencil pairwise fail to be essentially distinct.**

`parent σ ρ j` is the axial slide of `parent σ ρ i` by `α = 7 ρ (j - i)`, up to a transverse error
`3 σ |j - i|`.  With `|α| ≤ 7 ρ M ≤ 1/12 = c_*` and the error `≤ ρ / 12 = c_* ρ`, this is
`Kakeya.Tube.not_essDistinct_of_axial_slide` verbatim. -/
theorem not_isEssentiallyDistinct_parent {σ ρ : ℝ≥0} {M : ℕ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hax : 7 * (ρ : ℝ) * M ≤ 1 / 12) (htr : 3 * (σ : ℝ) * M ≤ (ρ : ℝ) / 12)
    {i j : ℕ} (hi : i ≤ M) (hj : j ≤ M) :
    ¬ IsEssentiallyDistinct (parent σ ρ i).carrier (parent σ ρ j).carrier := by
  let α : ℝ := 7 * (ρ : ℝ) * ((j : ℝ) - (i : ℝ))
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hc : 1 / (4 * (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) : ℝ)) = 1 / 12 := by
    rw [hfin]
    norm_num
  have hj' : (j : ℝ) ≤ (M : ℝ) := by exact_mod_cast hj
  have hi' : (i : ℝ) ≤ (M : ℝ) := by exact_mod_cast hi
  have hi0 : 0 ≤ (i : ℝ) := by exact_mod_cast (Nat.zero_le i)
  have hj0 : 0 ≤ (j : ℝ) := by exact_mod_cast (Nat.zero_le j)
  have hji : |(j : ℝ) - (i : ℝ)| ≤ (M : ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  have h7ρ0 : 0 ≤ 7 * (ρ : ℝ) := mul_nonneg (by norm_num) (NNReal.coe_nonneg ρ)
  have h3σ0 : 0 ≤ 3 * (σ : ℝ) := mul_nonneg (by norm_num) (NNReal.coe_nonneg σ)
  have hα : |α| ≤ 1 / (4 * (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) : ℝ)) := by
    rw [hc]
    calc
      |α| = 7 * (ρ : ℝ) * |(j : ℝ) - (i : ℝ)| := by
        simp [α, abs_mul, abs_of_nonneg h7ρ0]
      _ ≤ 7 * (ρ : ℝ) * (M : ℝ) := by
        exact mul_le_mul_of_nonneg_left hji h7ρ0
      _ ≤ 1 / 12 := hax
  have hdiff : base σ ρ j - (base σ ρ i + α • e₁) =
      (3 * (σ : ℝ) * ((j : ℝ) - (i : ℝ))) • e₂ := by
    dsimp [base, axial, trans, α]
    module
  have hdiff' : base σ ρ j + e₁ - (base σ ρ i + e₁ + α • e₁) =
      (3 * (σ : ℝ) * ((j : ℝ) - (i : ℝ))) • e₂ := by
    dsimp [base, axial, trans, α]
    module
  have hnorm : ‖(3 * (σ : ℝ) * ((j : ℝ) - (i : ℝ))) • e₂‖ ≤ 1 / 12 * (ρ : ℝ) := by
    calc
      ‖(3 * (σ : ℝ) * ((j : ℝ) - (i : ℝ))) • e₂‖
          = |3 * (σ : ℝ) * ((j : ℝ) - (i : ℝ))| * ‖e₂‖ := by
            simp [norm_smul]
      _ = 3 * (σ : ℝ) * |(j : ℝ) - (i : ℝ)| := by
        rw [norm_e₂, mul_one, abs_mul, abs_of_nonneg h3σ0]
      _ ≤ 3 * (σ : ℝ) * (M : ℝ) := by
        exact mul_le_mul_of_nonneg_left hji h3σ0
      _ ≤ (ρ : ℝ) / 12 := htr
      _ = 1 / 12 * (ρ : ℝ) := by ring
  have hp : dist (parent σ ρ j).x ((parent σ ρ i).x + α • (parent σ ρ i).direction)
      ≤ 1 / (4 * (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) : ℝ)) * (ρ : ℝ) := by
    rw [hc]
    simp [parent_direction]
    rw [dist_eq_norm]
    rw [hdiff]
    simpa [one_div] using hnorm
  have hq : dist (parent σ ρ j).y ((parent σ ρ i).y + α • (parent σ ρ i).direction)
      ≤ 1 / (4 * (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) : ℝ)) * (ρ : ℝ) := by
    rw [hc]
    simp [parent_direction]
    rw [dist_eq_norm]
    rw [hdiff']
    simpa [one_div] using hnorm
  exact Tube.not_essDistinct_of_axial_slide (E := EuclideanSpace ℝ (Fin 3)) (σ := ρ) hρ0 hρ1
    (parent σ ρ i) (parent σ ρ j) (α := α) hα hp hq

/-! #### The scale sequence -/

/-- The length of the axial pencil at stage `n`: `2 ^ (2n+1) ≍ (leafScale n) ^ (-1/4)`. -/
def count (n : ℕ) : ℕ := 2 ^ (2 * n + 1)

/-! #### The two halves of the contradiction -/

/-- **Any essentially distinct subfamily of the pencil retains at most one leaf.**

The parents pairwise fail to be essentially distinct, so a pairwise essentially distinct
`t' ⊆ t` has at most one element; and `Kakeya.ml1Boot.IsParentFamily.mapsTo` along the identity
puts `s'` inside `t'`. -/
theorem card_le_one {σ ρ : ℝ≥0} {M : ℕ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hax : 7 * (ρ : ℝ) * M ≤ 1 / 12) (htr : 3 * (σ : ℝ) * M ≤ (ρ : ℝ) / 12)
    {s' t' : Finset ℕ} (ht' : t' ⊆ Finset.range M)
    (hpf : IsParentFamily s' (leaf σ ρ) t' (parent σ ρ) id)
    (hed : (t' : Set ℕ).Pairwise
      (fun k l => IsEssentiallyDistinct (parent σ ρ k).carrier (parent σ ρ l).carrier)) :
    s'.card ≤ 1 := by
  have ht'card : t'.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro k hk l hl
    by_contra hne
    have hkM : k ≤ M := le_of_lt (Finset.mem_range.mp (ht' hk))
    have hlM : l ≤ M := le_of_lt (Finset.mem_range.mp (ht' hl))
    exact (not_isEssentiallyDistinct_parent hρ0 hρ1 hax htr hkM hlM) (hed hk hl hne)
  have hsub : s' ⊆ t' := by
    intro i hi
    simpa using hpf.mapsTo i hi
  exact le_trans (Finset.card_le_card hsub) ht'card

end essDistinctCex

/-! ### Refining a shaded family to a uniform one -/

/-- **The raw uniformity constant of the shaded uniformization**.

`ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf` produces a uniformity constant `C_u`
which depends on the ambient dimension only and is quantified *before* the grid length and the
scale — the order matters, since Definition 2.2 is used at the `δ`-dependent grid length
`Tube.ssfGridLen δ`.

This was formerly `opaque`, and that was a design defect rather than a caution: an opaque
constant has no properties, so the one bridge between two uniformity constants,
`ShadedTube.ShadedUniformTubeSet.mono`, could never be applied.  Every uniformization the
development can actually run lands at `ShadedTube.ssfUniformConst`, so that is the value
committed to here, which makes the `mono` step disappear rather than become provable.  Nothing
reads this constant except through `Kakeya.ml1Boot.uniformize.C`, so no field and no consumer
changes shape.

It was never the project's only `opaque` declaration, and removing it did not leave the project
with none: `Kakeya.ml1Boot.factorOneScaleUniformDilate.CWitness` is still `opaque`, and
deliberately so — that one carries the two clauses asked of it in the *type* of the witness, so
it exposes properties even while committing to no value, which is exactly what this constant
did not do.

**What committing to this value settles, and what it does not.**  It was the only *executable* of
the two repairs blueprint `note:ml1bootUniformizeConstantOpaque` offers: the second is conditional
on the Section 2 interface being "later stated with its own constant", and that interface is not a
Lean declaration.  Taking the first strictly increased what is provable — while `rawC` was
`opaque` the one available fact was `Kakeya.ml1Boot.one_le_uniformize_C` — and it lands on the
constant the uniformity fields want: dimension-only, which is what lets the `Cunif` of
`Kakeya.ml1Boot.multiplicity_le_middle` be fixed before the `∀ᶠ δ in 𝓝[>] 0` (module docstring),
and equal to what `ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf`
(Kakeya/ShadedUniform.lean:1075) produces, namely
`ShadedTube.ssfUniformConst (Module.finrank ℝ E)`.

What it does not settle is the demand of `fine_unif` and `coarse_unif` together.  (It used to be a
three-way demand, `fibreUnif` included; that field is now one-sided and free, and the route below
is no longer needed for it — see the docstring of `Kakeya.ml1Boot.exists_uniformFactorCore`.)  The
only route to simultaneous global-plus-fibrewise two-sided uniformity,
`Kakeya.exists_jointPartitionRegularization` (RelativePlank.lean:520), lands at a constant
depending on `#s` and unbounded as `δ → 0`, and `ShadedTube.ShadedUniformTubeSet.mono` weakens a
constant only upwards.  Restating the uniformity fields at a *quantified* constant is a defensible
change, but it is additive to the definition here rather
than a correction of it, and it is not what leaves
`Kakeya.ml1Boot.exists_uniformFactorCore` sorried; see that docstring's last two sections.  None
of this is a smallness question: the `16 ^ (-N)` separation the ambient hierarchy needs is
supplied for small `δ` by the fully proved
`Tube.exists_threshold_polylog_pow_ssfGridLen_le` (Kakeya/Uniform.lean:649). -/
def uniformize.rawC (n : ℕ) : ℝ≥0 := ShadedTube.ssfUniformConst n

/-- **The uniformity constant `C_{unif}(n) ≥ 1`** of the shaded uniformization: the raw constant
`Kakeya.ml1Boot.uniformize.rawC n`, enlarged to be at least `1`.

Enlarging a uniformity constant only weakens the statement it appears in, so taking the maximum
costs nothing and makes `Kakeya.ml1Boot.one_le_uniformize_C` a theorem rather than one more
unprovable assumption. -/
noncomputable def uniformize.C (n : ℕ) : ℝ≥0 := max 1 (uniformize.rawC n)

/-- **The conclusions of `Kakeya.ml1Boot.exists_uniformRefinement`, one field per item.**

Here `(𝕍, Z)` is a family of shaded `σ`-tubes indexed by `s`, `(ρ r, t r, Vρ r, p r)` are
`m` scales with parent families for `𝕍`, and the refinement data is `s'`, `λ'`, `t'` and
`N`.  The fields are items (i)–(vii) and (ix) of the blueprint lemma
`lem:ml1bootUniformizePair`; for why item (viii) is not among them see the module
docstring. -/
structure IsUniformRefinement {ι κ : Type*} [DecidableEq κ] {m : ℕ} {σ : ℝ≥0}
    (δ : ℝ≥0) (ε' : ℝ) (s : Finset ι) (V : ι → ShadedTube σ E)
    (ρ : Fin m → ℝ≥0) (t : Fin m → Finset κ) (Vρ : (r : Fin m) → κ → Tube (ρ r) E)
    (p : Fin m → ι → κ) (s' : Finset ι) (lam' : ℝ≥0) (t' : Fin m → Finset κ)
    (N : Fin m → ℝ≥0) : Prop where
  /-- (i) `(𝕍|_{s'}, Z)` is a `δ ^ ε'`-refinement of `(𝕍, Z)`. -/
  refinement : ShadedBody.IsCRefinement s' (fun i => (V i).toShadedBody) s
    (fun i => (V i).toShadedBody) ⟨(δ : ℝ) ^ ε', by positivity⟩
  /-- (ii) `(𝕍|_{s'}, Z)` is uniform, at the dimension-only constant
  `Kakeya.ml1Boot.uniformize.C 3`.  `ShadedTube.ShadedUniformTubeSet` is data-valued, so the
  `Prop`-valued clause is its `Nonempty`. -/
  unif : Nonempty (ShadedTube.ShadedUniformTubeSet s' V (Tube.ssfGridLen σ)
    (uniformize.C 3))
  /-- (iii) The shading densities on `s'` are two-sidedly comparable to `λ'`, which is
  itself at least `δ ^ ε'` times the fullness of the original family. -/
  dens : (∀ i ∈ s', (lam' : ℝ≥0∞) * volume (V i).carrier ≤ volume (V i).shade ∧
      volume (V i).shade ≤ 2 * (lam' : ℝ≥0∞) * volume (V i).carrier) ∧
    (δ : ℝ≥0∞) ^ ε' * ShadedBody.fullness s (fun i => (V i).toShadedBody) ≤ (lam' : ℝ≥0∞)
  /-- (iv) `|s'| ≥ δ ^ ε' |s|`, and consequently the Frostman constant grows by at most
  `δ ^ (-ε')` in every convex body containing the whole family. -/
  card : (δ : ℝ≥0∞) ^ ε' * (s.card : ℝ≥0∞) ≤ (s'.card : ℝ≥0∞) ∧
    ∀ K : ConvexSpaceBody E, (∀ i ∈ s, (V i).toConvexSpaceBody ≤ K) →
      frostmanConstIn s' (fun i => (V i).toConvexSpaceBody) K
        ≤ (δ : ℝ≥0∞) ^ (-ε') * frostmanConstIn s (fun i => (V i).toConvexSpaceBody) K
  /-- (v) Essential distinctness is inherited by the subfamily. -/
  essDistinct : (s : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier) →
    (s' : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier)
  /-- (vi) The parents of the retained members lie in `t' r`, the retained fibres all have
  cardinality comparable to `N r`, and each retains at least a `δ ^ ε'` fraction. -/
  branch : ∀ r : Fin m, t' r ⊆ t r ∧ (∀ i ∈ s', p r i ∈ t' r) ∧
    ∀ k ∈ t' r,
      (N r : ℝ≥0∞) ≤ ((fibre s' (p r) k).card : ℝ≥0∞) ∧
      ((fibre s' (p r) k).card : ℝ≥0∞) ≤ 2 * (N r : ℝ≥0∞) ∧
      (δ : ℝ≥0∞) ^ ε' * ((fibre s (p r) k).card : ℝ≥0∞)
        ≤ ((fibre s' (p r) k).card : ℝ≥0∞)
  /-- (vii) The Frostman constant of each fibre grows by at most `δ ^ (-ε')`. -/
  fibreFrostman : ∀ r : Fin m, ∀ k ∈ t' r, ∀ K : ConvexSpaceBody E,
    (∀ i ∈ fibre s (p r) k, (V i).toConvexSpaceBody ≤ K) →
    frostmanConstIn (fibre s' (p r) k) (fun i => (V i).toConvexSpaceBody) K
      ≤ (δ : ℝ≥0∞) ^ (-ε')
        * frostmanConstIn (fibre s (p r) k) (fun i => (V i).toConvexSpaceBody) K
  /-- (ix) (`item:uniformizeGivenFibreUnif`) Every retained *parent-map* fibre of every
  *given* parent family is itself uniform, at the constant
  `Kakeya.ml1Boot.uniformize.C 3`.  This is the clause that
  `Kakeya.ml1Boot.multiplicity_le_middle` consumes.  Item (viii)
  `item:uniformizeFibreUnif`, the containment-fibre clause, is not a field here; see the
  module docstring. -/
  fibreUnif : ∀ r : Fin m, ∀ k ∈ t' r,
    Nonempty (ShadedTube.ShadedUniformTubeSet (fibre s' (p r) k) V
      (Tube.ssfGridLen σ) (uniformize.C 3))

/-! ### The refuted uniformization, and why no statement of that shape appears here

`Kakeya.ml1Boot.exists_uniformRefinement` used to stand here: the step of Case (ii) that GWZ
dispatches with "we may suppose that all sets of the form … are uniform", asserting that a
family equipped with `m` parent families may be passed to a `δ ^ ε'`-refinement that is uniform
with constant `2`, has two-sidedly comparable shading densities, retains a `δ ^ ε'` fraction of
the index set and of every fibre, and loses at most `δ ^ (-ε')` in every Frostman constant.

It has been **deleted**, because it is false and had no consumer:
`Kakeya.ml1Boot.exists_uniformFactorPair` and `Kakeya.ml1Boot.exists_uniformFactorCore` replaced
it, and nothing cited it in code.  `Kakeya.ml1Boot.not_exists_uniformRefinement` below is kept as
the record and the guardrail: it is a self-contained refutation, and its docstring carries the
full diagnosis, including a second obstruction that survives the obvious repair.  The bundle
`Kakeya.ml1Boot.IsUniformRefinement` is likewise retained, now referenced only from prose, so
that the refuted shape stays legible.

Do not reintroduce a statement of this shape: an `∃`-conclusion asserting a positive lower bound
on shading densities, with no hypothesis constraining those shadings, is refuted by the
all-empty shading.

Prose elsewhere in this file still names `Kakeya.ml1Boot.exists_uniformRefinement`, deliberately:
it is the clearest way to say *which* statement is refuted, and several docstrings record that
they do not cite it.  Those are references to a deleted declaration, not to a live one; read
`Kakeya.ml1Boot.not_exists_uniformRefinement` for the diagnosis, and blueprint
`lem:ml1bootUniformizePair` for the statement as GWZ have it.

### Two further names in this file that are not declarations

The second was
the only consumer of the first and had none itself, so the pair was dead as a unit; the deletion
record is `Kakeya/DimensionThree/MainLemma1/Inventory.lean`, §B. Unlike the refuted statement
above, these two were not false: what is gone is the Lean carrier, not the mathematics. The
obligation is unchanged and is stated in blueprint `lem:ml1bootFactorOneScaleUniform`; the
reduction of the fine group to it, together with every proved piece of that reduction, is set out
in the docstring of `Kakeya.ml1Boot.exists_uniformFactorCore`.

Docstrings below therefore speak of "the shaded-uniformization interface" as a *shape* Section 2
still owes, and never as a declaration.  Do not read a claim of formalization into it. -/

/-! ### The two-scale factoring chain -/

/-- **The constant `C_{lem:ml1bootFactorOneScale}`** of one factoring step, at inner cardinality `N`
and inner tube scale `σ`: the `c = 1`
case, in the ambient dimension `3`, of
`ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C`.

This is the constant `Kakeya.ml1Boot.exists_factorOneScale` is *proved* at, and it is **not**
absolute: it grows with `N` and with `σ⁻¹`, subpolynomially in both by
`ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C_leApprox`.

It used to be the numeral `1`, read off `ShadedBody.shadingMultiplicityEstimateForRhoTubes.C`;
that statement has since been **refuted and deleted** (it was false at `1`, and false at every
nonzero constant, for the reasons recorded in the docstring of
`ShadedBody.shadingMultiplicityEstimateForRhoTubesUndilated`), and no proved estimate supports
an absolute value.  The two binders are therefore carried by every statement stated at this
constant — the fields of `Kakeya.ml1Boot.IsFactorOneScale`,
`Kakeya.ml1Boot.IsUniformFactorCore` and, through
`Kakeya.ml1Boot.factorTwoScales.C`, `Kakeya.ml1Boot.IsFactorTwoScales`.

Only `Kakeya.ml1Boot.one_le_factorOneScale_C` and the subpolynomial estimate
`ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C_leApprox` are used downstream, never
the numerical value. -/
noncomputable def factorOneScale.C (N : ℕ) (σ : ℝ≥0) : ℝ≥0 :=
  ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C 3 N σ 1

/-- **The constant `C_{lem:ml1bootFactorTwoScales}`** of the two-scale factoring chain
: the **product** of the two applications'
one-scale constants, since the chain is two applications of the one-scale step.

`N₁` and `δ` are the cardinality and tube scale of the *inner* family of the first application;
`N₂` and `τ` those of the *second*, whose inner family is the intermediate middle index set
`t''_τ` at the middle scale `τ`.  It is not the square of a single constant: the two
applications are made at different cardinalities and different scales, and no monotonicity of
`Kakeya.ml1Boot.factorOneScale.C` in either argument is available to compare them. -/
noncomputable def factorTwoScales.C (N₁ : ℕ) (δ : ℝ≥0) (N₂ : ℕ) (τ : ℝ≥0) : ℝ≥0 :=
  factorOneScale.C N₁ δ * factorOneScale.C N₂ τ

/-- **The conclusions of `Kakeya.ml1Boot.exists_factorOneScaleUniform`, one field per clause.**

Here `(𝕍, Z)` is a family of shaded `σ`-tubes indexed by `s`, `(t, 𝕍_ρ, p)` is a parent family
for `𝕍` at scale `ρ`, and `(tq, q)` is an auxiliary *classification* of the parent indices (see
below).  The output data is `s'`, `t''`, `t'q`, the shadings `Z'`, `Z_ρ` and the numbers
`λ_σ`, `λ_ρ`, `N`.  The fields are items (a)–(g) of the blueprint lemma
`lem:ml1bootFactorOneScaleUniform`, split one clause per field.

## The auxiliary classification `q`, and the clause that had to be removed

`q : κ → lc` is an arbitrary map, given *before* the refinement is chosen, together with a
finite index set `tq` of its values; `aux_subset` and `aux_card` retain a `δ ^ (2 ε')` fraction
of `tq` as `t'q`.  Both are harmless: `t'q := tq` always satisfies them.

The bundle used to carry a third clause, `coarse_fibre_card`, asserting that `t''` retains a
`δ ^ (2 ε')` fraction of every `q`-fibre `fibre t q l'` over `l' ∈ t'q`.  **That clause is
false**, and it has been removed.  Take `q` constant with `tq` a singleton; `aux_card` then
forces `t'q = tq`, and the clause collapses to the absolute `δ ^ (2 ε') |t| ≤ |t''|`, which is
the deleted `coarse_card` verbatim.  The *thin-parents* configuration refutes it, and it does
so with every parent carrying a member, so no surjectivity hypothesis repairs it: at `σ = δ`
and `ρ = δ ^ (1/2)`, let one parent `k₀` carry `⌈δ ^ (-1)⌉` pairwise essentially distinct
fully shaded `δ`-tubes and let `⌈δ ^ (-1/2)⌉` further parents carry one each.  The mass half
of `fine_refinement` reads `δ ^ (2 ε') ∑_{i ∈ s} |Z i| ≤ ∑_{i ∈ s'} |Z' i|` with
`∑_{i ∈ s} |Z i| ≍ δ ^ (-1) δ ^ 2 = δ`, while everything outside the class of `k₀` contributes
only `≍ δ ^ (-1/2) δ ^ 2 = δ ^ (3/2)`; so for `ε' < 1/4` and `δ` small the retained set must
keep `≳ δ ^ (2 ε' - 1)` members of that class, whence `k₀ ∈ t''` by `branch_mapsTo`.  The
bracket of `branch_card` is stated with a *single* `N`, so `N ≥ δ ^ (2 ε' - 1) / 2`, while
every thin parent has fibre cardinality at most `1 < N`; hence `t'' = {k₀}` and the clause
demands `δ ^ (2 ε') (1 + ⌈δ ^ (-1/2)⌉) ≤ 1`, which fails.

The obstruction is structural: one dyadic pigeonhole cannot simultaneously select the class
maximizing the number of *tubes* (which the mass clause forces) and retain a polynomial share
of the *parents* (which the deleted clause demanded), and the configuration above is exactly a
place where the two choices are incompatible.  `q`, `tq`, `t'q`, `aux_subset` and `aux_card`
are kept because callers are written against them, but they now carry no fibre information;
see the docstring of `Kakeya.ml1Boot.IsFactorTwoScales` for what this costs downstream and
blueprint `note:ml1bootLowerFrostmanFibre`. -/
structure IsFactorOneScale {ι κ lc : Type*} [DecidableEq κ] [DecidableEq lc]
    {σ ρ : ℝ≥0} (δ : ℝ≥0) (ε' : ℝ) (s : Finset ι) (V : ι → ShadedTube σ E)
    (t : Finset κ) (Vρ : κ → Tube ρ E) (p : ι → κ)
    (tq : Finset lc) (q : κ → lc)
    (s' : Finset ι) (t'' : Finset κ) (t'q : Finset lc)
    (Z' : ι → ShadedTube σ E) (Zρ : κ → ShadedTube ρ E)
    (lamσ lamρ N : ℝ≥0) : Prop where
  /-- (a) The fine index set is a subset of `s`. -/
  fine_subset : s' ⊆ s
  /-- (a) `Z'` shades the same tubes as `𝕍` and is contained in `Z`. -/
  fine_shade : ∀ i ∈ s', (Z' i).toTube = (V i).toTube ∧ (Z' i).shade ⊆ (V i).shade
  /-- (a) `(𝕍|_{s'}, Z')` is a `δ ^ (2 ε')`-refinement of `(𝕍, Z)`. -/
  fine_refinement : ShadedBody.IsCRefinement s' (fun i => (Z' i).toShadedBody) s
    (fun i => (V i).toShadedBody) ⟨(δ : ℝ) ^ (2 * ε'), by positivity⟩
  /-- (a) The fine family is uniform, at the constant `Kakeya.ml1Boot.uniformize.C 3`. -/
  fine_unif : Nonempty (ShadedTube.ShadedUniformTubeSet s' Z' (Tube.ssfGridLen σ)
    (uniformize.C 3))
  /-- (a) Essential distinctness is inherited by the fine family. -/
  fine_essDistinct : (s' : Set ι).Pairwise
    (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier)
  /-- (a) The fine shading densities are two-sidedly comparable to `λ_σ`. -/
  fine_dens : ∀ i ∈ s', (lamσ : ℝ≥0∞) * volume (V i).carrier ≤ volume (Z' i).shade ∧
    volume (Z' i).shade ≤ 2 * (lamσ : ℝ≥0∞) * volume (V i).carrier
  /-- (a) `λ_σ ≥ δ ^ (2 ε') λ(𝕍, Z)`. -/
  fine_fullness : (δ : ℝ≥0∞) ^ (2 * ε')
      * ShadedBody.fullness s (fun i => (V i).toShadedBody) ≤ (lamσ : ℝ≥0∞)
  /-- (b) The coarse index set is a subset of `t`. -/
  coarse_subset : t'' ⊆ t
  /-- (b) `Z_ρ` shades the parent tubes. -/
  coarse_tube : ∀ k ∈ t'', (Zρ k).toTube = Vρ k
  /-- (b) The coarse family is uniform, at the constant `Kakeya.ml1Boot.uniformize.C 3`. -/
  coarse_unif : Nonempty (ShadedTube.ShadedUniformTubeSet t'' Zρ (Tube.ssfGridLen ρ)
    (uniformize.C 3))
  /-- (b) Essential distinctness is inherited by the coarse family. -/
  coarse_essDistinct : (t'' : Set κ).Pairwise
    (fun k k' => IsEssentiallyDistinct (Vρ k).carrier (Vρ k').carrier)
  /-- (b) The coarse shading densities are two-sidedly comparable to `λ_ρ`. -/
  coarse_dens : ∀ k ∈ t'', (lamρ : ℝ≥0∞) * volume (Vρ k).carrier ≤ volume (Zρ k).shade ∧
    volume (Zρ k).shade ≤ 2 * (lamρ : ℝ≥0∞) * volume (Vρ k).carrier
  /-- (b) `λ_ρ ≥ C⁻¹ δ ^ (2 ε') λ(𝕍, Z)`, at `C = factorOneScale.C #s σ`. -/
  coarse_fullness : (factorOneScale.C s.card σ : ℝ≥0∞)⁻¹ * (δ : ℝ≥0∞) ^ (2 * ε')
      * ShadedBody.fullness s (fun i => (V i).toShadedBody) ≤ (lamρ : ℝ≥0∞)
  /-- (b) The retained classification index set is a subset of `tq`. -/
  aux_subset : t'q ⊆ tq
  /-- (b) A `δ ^ (2 ε')` fraction of the classification indices is retained. -/
  aux_card : (δ : ℝ≥0∞) ^ (2 * ε') * (tq.card : ℝ≥0∞) ≤ (t'q.card : ℝ≥0∞)
  /-- (c) The shadings are nested along the parent map. -/
  contain : ∀ i ∈ s', p i ∈ t'' → (Z' i).shade ⊆ (Zρ (p i)).shade
  /-- (d) Every retained member has its parent retained. -/
  branch_mapsTo : ∀ i ∈ s', p i ∈ t''
  /-- (d) The retained fibres have cardinality comparable to `N` and each retains a
  `δ ^ (2 ε')` fraction. -/
  branch_card : ∀ k ∈ t'',
    (N : ℝ≥0∞) ≤ ((fibre s' p k).card : ℝ≥0∞) ∧
    ((fibre s' p k).card : ℝ≥0∞) ≤ 2 * (N : ℝ≥0∞) ∧
    (δ : ℝ≥0∞) ^ (2 * ε') * ((fibre s p k).card : ℝ≥0∞)
      ≤ ((fibre s' p k).card : ℝ≥0∞)
  /-- (e) Every fibre Frostman constant grows by at most `δ ^ (-2 ε')`. -/
  frostman : ∀ k ∈ t'', ∀ K : ConvexSpaceBody E,
    (∀ i ∈ s, p i = k → (V i).toConvexSpaceBody ≤ K) →
    frostmanConstIn (fibre s' p k) (fun i => (V i).toConvexSpaceBody) K
      ≤ (δ : ℝ≥0∞) ^ (-2 * ε')
        * frostmanConstIn (fibre s p k) (fun i => (V i).toConvexSpaceBody) K
  /-- (f) The multiplicity factors with loss `C δ ^ (-2 ε')`, at `C = factorOneScale.C #s σ`. -/
  product : ∀ k ∈ t'', ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
    ≤ (factorOneScale.C s.card σ : ℝ≥0∞) * (δ : ℝ≥0∞) ^ (-2 * ε')
      * ShadedBody.multiplicity t'' (fun k' => (Zρ k').toShadedBody)
      * ShadedBody.multiplicity (fibre s' p k) (fun i => (Z' i).toShadedBody)
  /-- (g) Every retained fibre of the parent map is itself uniform, in the **one-sided** reading
  `Kakeya.IsFlatPrismUniform`: GWZ Definition 2.2 minus `le_card_shadeClass` and `branchingN_le`.
  Nothing along the consumer chain reads either dropped clause; see the module docstring. -/
  fibreUnif : ∀ k ∈ t'', Nonempty (IsFlatPrismUniform (fibre s' p k) Z'
    (Tube.ssfGridLen σ) (uniformize.C 3))

/-! #### The degenerate branch: a null shading

`Kakeya.ml1Boot.IsFactorOneScale` has **no** clause forcing either retained index set to be
nonempty: the absolute parent-counting clause `coarse_card` was deleted as refuted (see the
structure docstring), and every surviving clause is either a statement about members of `s'` or
`t''` or an inequality whose left-hand side vanishes with the shading.  So a family whose total
shading volume is `0` — which no hypothesis of `Kakeya.ml1Boot.exists_factorOneScaleUniform`
forbids, a `Kakeya.ShadedTube` only asking its shading to be a measurable subset of the carrier —
is handled by the *empty* refinement, with no pigeonholing at all.  That is what keeps
`Kakeya.ml1Boot.exists_factorOneScaleUniform` clear of the defect that refutes
`Kakeya.ml1Boot.exists_uniformRefinement`, whose `card` clause forces `s'` to be nonempty and
whose `dens` clause then demands a positive lower bound on a null shading.
-/

/-- **The auxiliary parameter is eventually at most `1`.**

`Set.Iio 1` is a neighbourhood of `0` in `NNReal`, so it belongs to `𝓝[>] 0`.  This is the only
smallness that the degenerate branch of `Kakeya.ml1Boot.exists_factorOneScaleUniform` consumes: it
is what makes `δ ^ (2 ε') ≤ 1`, hence `Kakeya.ml1Boot.IsFactorOneScale.aux_card` true at
`t'q = tq`. -/
theorem eventually_le_one_nhdsGT : ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0, δ ≤ 1 := by
  filter_upwards
    [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ≥0) < 1 by norm_num))] with δ hδ
  exact le_of_lt hδ

/-- **The auxiliary parameter is eventually at most any prescribed positive bound.**

`Set.Iio c` is a neighbourhood of `0` in `NNReal` whenever `0 < c`, so it belongs to `𝓝[>] 0`.
This is the generic form of `Kakeya.ml1Boot.eventually_le_one_nhdsGT`; it is what turns a
smallness condition on `δ` alone — such as the one in
`Kakeya.ml1Boot.card_le_rpow_neg_seven` — into a clause of a `∀ᶠ δ in 𝓝[>] 0` statement. -/
theorem eventually_le_nhdsGT {c : ℝ≥0} (hc : 0 < c) : ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0, δ ≤ c := by
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hc)] with δ hδ
  exact le_of_lt hδ

/-- **The constant-free cardinality bound for essentially distinct tubes in `B₁ ⊆ ℝ³`.**

A family of pairwise essentially distinct `σ`-tubes contained in `B₁ ⊆ ℝ³` has at most
`δ ^ (-7)` members, for every tube scale `σ ≥ δ` and every `δ` small enough that
`δ · C ≤ 1`, where `C = Tube.card_le_of_EssDistinct.C 3 = 78 ^ 6 + 1`.

The input is `Tube.card_le_of_EssDistinct` at radius `r = 1` in dimension `n = 3`, which gives
the *constant-carrying* bound `#s ≤ C · σ ^ (-6) ≤ C · δ ^ (-6)`; the smallness of `δ` absorbs
`C` into one further power of `1 / δ`, which is where the exponent `7` comes from.  The
`ℝ`-valued `Tube.card_le_of_EssDistinct` is used rather than the sharper `ENNReal`-valued
`Kakeya.ml1Boot.card_le` (exponent `-4`) because the shape wanted downstream is literally the
`ℝ`-valued, constant-free hypothesis `(s.card : ℝ) ≤ · ^ (-K₀)` of the shaded uniformization;
the extra exponent is free, since `K₀` only enters there through the choice of the threshold.

Note that the bound is stated at the *auxiliary* parameter `δ` and not at the tube scale `σ`:
`σ` may be as large as `1`, and `σ ≥ δ` makes `σ ^ (-6) ≤ δ ^ (-6)`.  This is exactly the form
in which `Kakeya.ml1Boot.exists_uniformFactorPair` needs it, and the form the two-scale step
would need, both quantifying over `δ ≤ σ ≤ 1`.  (The two-scale step has no declaration:
`exists_twoScaleFactorPair` is not one, see blueprint
`note:ml1bootCaseTwoConstructionLayerEmpty`.)

It is written for the shaded-uniformization *interface* discussed at
`Kakeya.ml1Boot.not_exists_uniformRefinement` — which is a shape and not a declaration, the
sorried `exists_shadedUniform_of_card_le` that used to record it having been deleted
(`Kakeya/DimensionThree/MainLemma1/Inventory.lean`, §B) — and **not** for
`ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf`.  The Section 2 statement reads its
cardinality hypothesis at its own single scale variable, which is the tube scale of the family;
applied to a family of `σ`-tubes it therefore asks for `#s ≤ σ ^ (-K₀)`, and since `δ ≤ σ` the
bound proved here is *weaker* than that, not stronger.  No choice of `K₀` repairs this: the only
bound available at the tube scale is `#s ≤ C σ ^ (-6)`, and `σ ^ (-K₀) ≥ C σ ^ (-6)` fails for
`σ` near `1`, where `σ ^ (6 - K₀) < C`.  See the docstring of
`Kakeya.ml1Boot.exists_uniformFactorCore` for the interface shape in full. -/
theorem card_le_rpow_neg_seven (hdim : Module.finrank ℝ E = 3) {δ σ : ℝ≥0}
    (hδ0 : 0 < δ) (hδσ : δ ≤ σ)
    (hδC : (δ : ℝ) * Tube.card_le_of_EssDistinct.C 3 ≤ 1)
    {ι : Type*} (s : Finset ι) (V : ι → Tube σ E)
    (hball : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1)
    (hED : (s : Set ι).Pairwise
      fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier) :
    (s.card : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ)) := by
  haveI : Nontrivial E := by
    exact Module.finrank_pos_iff.mp (by rw [hdim]; norm_num)
  have hσ0 : 0 < σ := hδ0.trans_le hδσ
  have hδR : 0 < (δ : ℝ) := by exact_mod_cast hδ0
  have hσR : 0 < (σ : ℝ) := by exact_mod_cast hσ0
  have hC0 : 0 ≤ Tube.card_le_of_EssDistinct.C 3 :=
    (Tube.card_le_of_EssDistinct.C_pos (n := 3)).le
  have hcard0 : (s.card : ℝ) ≤
      Tube.card_le_of_EssDistinct.C 3 * (1 / (σ : ℝ)) ^ 6 := by
    have h' := Tube.card_le_of_EssDistinct (E := E) (δ := σ) hσ0 (1 : ℝ) s V hball hED
    rw [hdim] at h'
    simpa using h'
  have h_one_over_le : (1 : ℝ) / (σ : ℝ) ≤ (1 : ℝ) / (δ : ℝ) := by
    rw [div_le_div_iff₀ hσR hδR]
    simpa using (NNReal.coe_le_coe.mpr hδσ)
  have h_pow_le : ((1 : ℝ) / (σ : ℝ)) ^ 6 ≤ ((1 : ℝ) / (δ : ℝ)) ^ 6 := by
    exact pow_le_pow_left₀ (by positivity) h_one_over_le 6
  have hfun : Tube.card_le_of_EssDistinct.C 3 * (1 / (σ : ℝ)) ^ 6 ≤
      Tube.card_le_of_EssDistinct.C 3 * (1 / (δ : ℝ)) ^ 6 := by
    exact mul_le_mul_of_nonneg_left h_pow_le hC0
  have hsix : (1 / (δ : ℝ)) ^ 6 = (δ : ℝ) ^ (-(6 : ℝ)) := by
    simp [Real.rpow_neg (le_of_lt hδR) (6 : ℝ), one_div, inv_pow]
  have hC_le_inv : Tube.card_le_of_EssDistinct.C 3 ≤ (δ : ℝ)⁻¹ := by
    rw [← one_div]
    rw [le_div_iff₀ hδR]
    simpa [mul_comm] using hδC
  have hneg1 : (δ : ℝ) ^ (-(1 : ℝ)) = (δ : ℝ)⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hδR) (1 : ℝ)]
    simp
  have hC_le_neg1 : Tube.card_le_of_EssDistinct.C 3 ≤ (δ : ℝ) ^ (-(1 : ℝ)) := by
    rw [hneg1]
    exact hC_le_inv
  calc
    (s.card : ℝ) ≤ Tube.card_le_of_EssDistinct.C 3 * (1 / (δ : ℝ)) ^ 6 :=
      le_trans hcard0 hfun
    _ = Tube.card_le_of_EssDistinct.C 3 * (δ : ℝ) ^ (-(6 : ℝ)) := by rw [hsix]
    _ ≤ (δ : ℝ) ^ (-(1 : ℝ)) * (δ : ℝ) ^ (-(6 : ℝ)) := by
      exact mul_le_mul_of_nonneg_right hC_le_neg1 (Real.rpow_nonneg (le_of_lt hδR) _)
    _ = (δ : ℝ) ^ (-(7 : ℝ)) := by
      rw [← Real.rpow_add hδR]
      congr 1
      norm_num

/-- **The cardinality bound of `Kakeya.ml1Boot.card_le_rpow_neg_seven`, as a smallness clause
in `δ`.**

The smallness hypothesis `δ · C ≤ 1` of `Kakeya.ml1Boot.card_le_rpow_neg_seven` constrains the
auxiliary parameter alone, so it may be absorbed into the `∀ᶠ δ in 𝓝[>] 0` prefix that every
statement of this file carries.  In this form the bound is a hypothesis-free consequence of the
geometry, and it discharges the cardinality hypothesis of the shaded-uniformization interface at
`K₀ = 7` — that being a shape and not a declaration, the sorried
`exists_shadedUniform_of_card_le` that used to record it having been deleted
(`Kakeya/DimensionThree/MainLemma1/Inventory.lean`, §B).

It does **not** discharge the cardinality hypothesis of
`ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf`, which is read at the tube scale rather
than at the auxiliary parameter and is therefore a strictly stronger demand; see the docstring
of `Kakeya.ml1Boot.card_le_rpow_neg_seven`. -/
theorem eventually_card_le_rpow_neg_seven (hdim : Module.finrank ℝ E = 3) :
    ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0, ∀ σ : ℝ≥0, δ ≤ σ →
      ∀ {ι : Type*} (s : Finset ι) (V : ι → Tube σ E),
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1) →
        (s : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier) →
        (s.card : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ)) := by
  let c : ℝ≥0 :=
    ⟨(Tube.card_le_of_EssDistinct.C 3 : ℝ)⁻¹, by
      exact inv_nonneg.mpr (le_of_lt (show 0 < Tube.card_le_of_EssDistinct.C 3
        from Tube.card_le_of_EssDistinct.C_pos (n := 3)))⟩
  have hcR : 0 < (c : ℝ) := by
    dsimp [c]
    exact inv_pos.mpr (by exact_mod_cast (Tube.card_le_of_EssDistinct.C_pos (n := 3)))
  have hc : 0 < c := by
    exact_mod_cast hcR
  filter_upwards [eventually_le_nhdsGT (c := c) hc, self_mem_nhdsWithin] with δ hδ hδ0
  intro σ hσ ι s V hball hED
  have hδ0' : 0 < δ := hδ0
  have hTCpos : 0 < (Tube.card_le_of_EssDistinct.C 3 : ℝ) := by
    exact_mod_cast (Tube.card_le_of_EssDistinct.C_pos (n := 3))
  have hδC : (δ : ℝ) * (Tube.card_le_of_EssDistinct.C 3 : ℝ) ≤ 1 := by
    calc
      (δ : ℝ) * (Tube.card_le_of_EssDistinct.C 3 : ℝ)
          ≤ (c : ℝ) * (Tube.card_le_of_EssDistinct.C 3 : ℝ) := by
            exact mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr hδ) (le_of_lt hTCpos)
      _ = 1 := by
            have hb : (c : ℝ) = (Tube.card_le_of_EssDistinct.C 3 : ℝ)⁻¹ := rfl
            rw [hb]
            exact inv_mul_cancel₀ (ne_of_gt hTCpos)
  exact card_le_rpow_neg_seven hdim hδ0' hσ hδC s V hball hED

/-- **The loss of a shade-volume banding of a family of `n` shaded tubes.**

`8 (1 + log₂ (2 n))`, in `[0, ∞]`.  It depends on the *cardinality* of the family alone, and this
is the whole point: the naive density banding of
`Kakeya.ShadedBody.exists_isCRefinement_comparable_density` has loss `1 + log₂ (1/a)`, where `a` is
a lower bound for the shading densities, and the only such bound available from
`ShadedBody.isCRefinement_discardLowShading` is `a ≍ λ(𝕍, Z)`.  Nothing in this development bounds
the fullness `λ(𝕍, Z)` from below by a power of `δ` — the hypothesis of
`Kakeya.ml1Boot.exists_uniformFactorCore` is only `0 < ∑_{i ∈ s} |Z i|` — so that loss is *not*
subpolynomial in `δ` uniformly in the family, and the density banding cannot be made to fit the
budget `δ ^ (2 ε')` that way.

Banding the shade *volumes* relative to their maximum instead of relative to the fullness repairs
this.  Members carrying less than `1/(2 n)` of the maximum carry at most half the total mass in
aggregate, so discarding them is free; what survives lies in a range of ratio at most `2 n`, and a
dyadic pigeonhole over a range of ratio `R` costs `1 + log₂ R`.  Since all tubes at a fixed scale
have the same carrier volume (`Kakeya.Tube.volume_carrier_eq_volume_carrier`), a band of the shade
volumes *is* a band of the shading densities.

The two factors of `2` and the leading `8` are slack, so that the same constant serves both
conclusions of `Kakeya.ml1Boot.exists_massBand`. -/
noncomputable def bandLoss (n : ℕ) : ℝ≥0∞ :=
  8 * ENNReal.ofReal (1 + Real.logb 2 (2 * (n : ℝ)))

/-- **The banding loss is eventually subpolynomial, for families of subpolynomial size.**

`Kakeya.ml1Boot.bandLoss n` grows like `log n`, so a cardinality bound `n ≤ δ ^ (-7)` — which is
what `Kakeya.ml1Boot.eventually_card_le_rpow_neg_seven` supplies for a family of pairwise
essentially distinct tubes in `B₁ ⊆ ℝ³` — makes it at most `δ ^ (-η)` for every fixed `η > 0` and
all sufficiently small `δ`.  This is the step that makes the banding of
`Kakeya.ml1Boot.exists_massBand` affordable inside the budget of
`Kakeya.ml1Boot.IsUniformFactorCore.fine_refinement`, and it is the reason the banding has to be
by shade volume rather than by density; see the docstring of `Kakeya.ml1Boot.bandLoss`. -/
theorem eventually_bandLoss_le_rpow_neg {η : ℝ} (hη : 0 < η) :
    ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0, ∀ n : ℕ, (n : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ)) →
      bandLoss n ≤ (δ : ℝ≥0∞) ^ (-η) := by
  filter_upwards [nnreal_eventually_of_real_eventually
      (absorb_log_le_rpow_neg (C := 72 / Real.log 2) (M := 1) (η := η / 2)
        (by positivity) one_pos (by linarith)),
    eventually_le_nhdsGT (c := (1 / 2 : ℝ≥0)) (by norm_num),
    self_mem_nhdsWithin] with δ habs hδ2 hδmem
  have hδ0 : 0 < δ := hδmem
  have hηe : -(2 * (η / 2)) = -η := by ring
  have habs' : (72 / Real.log 2) * (1 * Real.log (1 / (δ : ℝ))) ≤ (δ : ℝ) ^ (-η) := by
    simpa [hηe] using habs
  intro n hn
  rw [ennreal_coe_nnreal_rpow (by exact_mod_cast hδ0) (-η)]
  have hpt : bandLoss n ≤ ENNReal.ofReal (72 * Real.logb 2 (1 / (δ : ℝ))) := by
    unfold bandLoss
    let L : ℝ := Real.logb 2 (1 / (δ : ℝ))
    have hδR : 0 < (δ : ℝ) := by exact_mod_cast hδ0
    have hδle : 0 ≤ (δ : ℝ) := hδR.le
    have hq : 0 < 1 / (δ : ℝ) := by positivity
    -- 1/δ ≥ 2
    have hinv : 2 ≤ 1 / (δ : ℝ) := by
      rw [le_div_iff₀ hδR]
      have hδ2R : (δ : ℝ) ≤ 1 / 2 := by exact_mod_cast hδ2
      nlinarith
    -- logb 2 2 = 1
    have hL2 : Real.logb 2 (2 : ℝ) = 1 := by
      rw [Real.logb]
      exact div_self (Real.log_ne_zero.mpr (by norm_num))
    have h1 : 1 ≤ L := by
      have hmono :=
        (Real.logb_le_logb (by norm_num : 1 < (2 : ℝ)) (by norm_num : 0 < (2 : ℝ)) hq).2 hinv
      rwa [hL2] at hmono
    -- exponent identity (δ)^(-7) = (1/δ)^7
    have hpow7 : (δ : ℝ) ^ (-(7 : ℝ)) = (1 / (δ : ℝ)) ^ (7 : ℝ) := by
      rw [Real.rpow_neg hδle (7 : ℝ)]
      rw [← Real.inv_rpow hδle (7 : ℝ)]
      simp [one_div]
    have h2 : Real.logb 2 (2 * (n : ℝ)) ≤ 1 + 7 * L := by
      by_cases hn0 : n = 0
      · subst n
        norm_num
        nlinarith [h1]
      · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
        have h2n : 0 < 2 * (n : ℝ) := by positivity
        have hnle : 2 * (n : ℝ) ≤ 2 * (δ : ℝ) ^ (-(7 : ℝ)) := by nlinarith
        have hpos2 : 0 < 2 * (δ : ℝ) ^ (-(7 : ℝ)) := by
          rw [hpow7]
          positivity
        have hmono := (Real.logb_le_logb (by norm_num : 1 < (2 : ℝ)) h2n hpos2).2 hnle
        have hname : Real.logb 2 (2 * (δ : ℝ) ^ (-(7 : ℝ))) = 1 + 7 * L := by
          rw [hpow7]
          rw [Real.logb_mul (by norm_num : (2 : ℝ) ≠ 0)
            (ne_of_gt (Real.rpow_pos_of_pos hq (7 : ℝ)))]
          rw [Real.logb_rpow_eq_mul_logb_of_pos hq]
          rw [hL2]
        rwa [hname] at hmono
    calc
      8 * ENNReal.ofReal (1 + Real.logb 2 (2 * (n : ℝ)))
          ≤ 8 * ENNReal.ofReal (9 * L) := by
            exact mul_le_mul_of_nonneg_left
              (ENNReal.ofReal_le_ofReal (by nlinarith [h2, h1])) (by norm_num)
        _ = ENNReal.ofReal (72 * L) := by
            rw [show 72 * L = 8 * (9 * L) by ring]
            rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
            norm_num
  exact le_trans hpt (ENNReal.ofReal_le_ofReal (by
    calc
      72 * Real.logb 2 (1 / (δ : ℝ)) = (72 / Real.log 2) * (1 * Real.log (1 / (δ : ℝ))) := by
        simp [Real.logb]
        ring
      _ ≤ (δ : ℝ) ^ (-η) := habs'))

/-- **A cardinality bound `n ≤ δ ^ (-7)` makes the banding loss a multiple of `log (1/δ)`.**

The pointwise half of `Kakeya.ml1Boot.eventually_bandLoss_le_rpow_neg`, separated because it is pure
real analysis and involves no filter: for `δ ≤ 1/2` one has `log₂ (1/δ) ≥ 1`, so the additive
constants of `bandLoss` are themselves absorbed into a multiple of `log₂ (1/δ)`, and
`log₂ (2 n) ≤ 1 + 7 log₂ (1/δ)` by monotonicity of `log₂`.  The case `n = 0` is covered because
`Real.logb 2 0 = 0`. -/
theorem bandLoss_le_ofReal_logb {δ : ℝ≥0} (hδ0 : 0 < δ) (hδ2 : δ ≤ 1 / 2) {n : ℕ}
    (hn : (n : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ))) :
    bandLoss n ≤ ENNReal.ofReal (72 * Real.logb 2 (1 / (δ : ℝ))) := by
  classical
  set L : ℝ := Real.logb 2 (1 / (δ : ℝ)) with hLdef
  have hd0 : 0 < (δ : ℝ) := NNReal.coe_pos.mpr hδ0
  have hd22 : (δ : ℝ) ≤ (1 : ℝ) / 2 := by
    exact_mod_cast hδ2
  have h2le : 2 ≤ 1 / (δ : ℝ) := by
    rw [le_div_iff₀' hd0]
    nlinarith
  have hL1 : 1 ≤ L := by
    have hleL : Real.logb 2 (2 : ℝ) ≤ L := by
      dsimp [L]
      exact (Real.logb_le_logb (b := 2) (by norm_num : 1 < (2 : ℝ))
        (by norm_num : 0 < (2 : ℝ)) (one_div_pos.mpr hd0)).mpr h2le
    simpa using hleL
  have hr : 8 * (1 + Real.logb 2 (2 * (n : ℝ))) ≤ 72 * L := by
    by_cases hn0 : n = 0
    · have hlog : Real.logb 2 (2 * (n : ℝ)) = 0 := by
        rw [hn0]
        simp
      rw [hlog]
      nlinarith [hL1]
    · have hn1 : 1 ≤ n := by omega
      have hn' : 0 < (n : ℝ) := by exact_mod_cast hn1
      have hle1 : Real.logb 2 (n : ℝ) ≤ Real.logb 2 ((δ : ℝ) ^ (-(7 : ℝ))) := by
        exact (Real.logb_le_logb (b := 2) (by norm_num : 1 < (2 : ℝ)) hn'
          (Real.rpow_pos_of_pos hd0 (-(7 : ℝ)))).mpr hn
      have hln : Real.logb 2 (n : ℝ) ≤ 7 * L := by
        calc
          Real.logb 2 (n : ℝ) ≤ Real.logb 2 ((δ : ℝ) ^ (-(7 : ℝ))) := hle1
          _ = 7 * L := by
            rw [Real.logb_rpow_eq_mul_logb_of_pos (b := 2) hd0]
            dsimp [L]
            have hreflog : Real.logb 2 (1 / (δ : ℝ)) = -Real.logb 2 (δ : ℝ) := by
              simp
            rw [hreflog]
            ring
      have hlogmul : Real.logb 2 (2 * (n : ℝ)) = 1 + Real.logb 2 (n : ℝ) := by
        have h := Real.logb_mul (b := 2) (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hn')
        simp [h]
      have keep : Real.logb 2 (2 * (n : ℝ)) ≤ 1 + 7 * L := by
        rw [hlogmul]
        nlinarith [hln]
      nlinarith [keep, hL1]
  calc
    bandLoss n = ENNReal.ofReal (8 * (1 + Real.logb 2 (2 * (n : ℝ)))) := by
      simp [bandLoss, ENNReal.ofReal_mul]
    _ ≤ ENNReal.ofReal (72 * L) := ENNReal.ofReal_le_ofReal hr

/-- **Discarding the members lying far below the maximum keeps half of the total.**

If every term of a finite sum of extended reals is at most `μ`, and `μ` itself is at most the sum,
then the terms `x i` with `2 #s · x i < μ` contribute at most half the sum: there are at most `#s`
of them and each is below `μ / (2 #s)`.  So the complementary set retains half.

This is the discarding step of `Kakeya.ml1Boot.exists_massBand`, stated for a bare family of
extended reals because nothing geometric enters.  It plays the role that
`ShadedBody.isCRefinement_discardLowShading` plays for the density banding, but with the threshold
read off the *maximum* term rather than off the fullness — which is the whole point of the shade
volume banding; see the docstring of `Kakeya.ml1Boot.bandLoss`. -/
theorem sum_le_two_mul_sum_filter_of_le_max {ι : Type*} (s : Finset ι) (x : ι → ℝ≥0∞)
    {μ : ℝ≥0∞} (hmax : ∀ i ∈ s, x i ≤ μ) (hμ : μ ≤ ∑ i ∈ s, x i)
    (htop : ∑ i ∈ s, x i ≠ ⊤) :
    ∑ i ∈ s, x i
      ≤ 2 * ∑ i ∈ (open scoped Classical in
          s.filter (fun i => μ ≤ 2 * (s.card : ℝ≥0∞) * x i)), x i := by
  classical
  let M : ℝ≥0∞ := ∑ i ∈ s, x i
  let F : Finset ι := s.filter (fun i => μ ≤ 2 * (s.card : ℝ≥0∞) * x i)
  let G : Finset ι := s.filter (fun i => ¬ (μ ≤ 2 * (s.card : ℝ≥0∞) * x i))
  by_cases hs : s = ∅
  · subst s
    simp
  · have hne : s.Nonempty := (Finset.nonempty_iff_ne_empty).mpr hs
    have hcard_pos : 0 < s.card := Finset.card_pos.mpr hne
    have hcard0 : (s.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast (ne_of_gt hcard_pos)
    have hcardtop : (s.card : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
    have hsum : (∑ i ∈ F, x i) + (∑ i ∈ G, x i) = M := by
      unfold F G M
      rw [← Finset.sum_filter_add_sum_filter_not (s := s)
        (p := fun i => μ ≤ 2 * (s.card : ℝ≥0∞) * x i) x]
    have hG_le : ∀ i ∈ G, 2 * (s.card : ℝ≥0∞) * x i ≤ μ := by
      intro i hi
      have hlt : 2 * (s.card : ℝ≥0∞) * x i < μ :=
        lt_of_not_ge (by simpa [G] using (Finset.mem_filter.mp hi).2)
      exact le_of_lt hlt
    have hcancel : 2 * (∑ i ∈ G, x i) ≤ μ := by
      have hsumG_le : 2 * (s.card : ℝ≥0∞) * (∑ i ∈ G, x i) ≤ (s.card : ℝ≥0∞) * μ := by
        calc
          2 * (s.card : ℝ≥0∞) * (∑ i ∈ G, x i) = ∑ i ∈ G, 2 * (s.card : ℝ≥0∞) * x i := by
            rw [Finset.mul_sum]
          _ ≤ ∑ i ∈ G, μ := by
            exact Finset.sum_le_sum hG_le
          _ = (G.card : ℝ≥0∞) * μ := by
            rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (s.card : ℝ≥0∞) * μ := by
            have hcG : (G.card : ℝ≥0∞) ≤ (s.card : ℝ≥0∞) := by
              dsimp [G]
              exact_mod_cast (Finset.card_filter_le s
                (fun i => ¬ (μ ≤ 2 * (s.card : ℝ≥0∞) * x i)))
            exact mul_le_mul_of_nonneg_right hcG (by positivity)
      have hrw : 2 * (s.card : ℝ≥0∞) * (∑ i ∈ G, x i)
          = (s.card : ℝ≥0∞) * (2 * (∑ i ∈ G, x i)) := by
        ring
      have hright : (2 * (∑ i ∈ G, x i)) * (s.card : ℝ≥0∞)
          ≤ μ * (s.card : ℝ≥0∞) := by
        calc
          (2 * (∑ i ∈ G, x i)) * (s.card : ℝ≥0∞)
              = (s.card : ℝ≥0∞) * (2 * (∑ i ∈ G, x i)) := by rw [mul_comm]
          _ ≤ (s.card : ℝ≥0∞) * μ := by simpa [hrw] using hsumG_le
          _ = μ * (s.card : ℝ≥0∞) := by rw [mul_comm]
      exact (ENNReal.mul_le_mul_iff_left hcard0 hcardtop).1 hright
    have h2G_le_M : 2 * (∑ i ∈ G, x i) ≤ M := le_trans hcancel hμ
    have h2M : 2 * M ≤ 2 * (∑ i ∈ F, x i) + M := by
      calc
        2 * M = 2 * ((∑ i ∈ F, x i) + (∑ i ∈ G, x i)) := by rw [← hsum]
        _ = 2 * (∑ i ∈ F, x i) + 2 * (∑ i ∈ G, x i) := by rw [mul_add]
        _ ≤ 2 * (∑ i ∈ F, x i) + M := by
          gcongr
    have hfin : M ≤ 2 * (∑ i ∈ F, x i) := by
      have hMtop : M ≠ ⊤ := htop
      have h2M' : M + M ≤ 2 * (∑ i ∈ F, x i) + M := by
        simpa [two_mul] using h2M
      exact (ENNReal.add_le_add_iff_right hMtop).1 h2M'
    simpa [M, F] using hfin

/-- **Banding a finite family of extended reals into a factor-two window, at a loss logarithmic in
the cardinality.**

A finite family `(x i)_{i ∈ s}` of extended reals with positive finite total has a subfamily on
which the values lie in a window `[μ, 2 μ]` with `μ > 0`, retaining all but a factor
`2 (1 + log₂ (2 #s))` of the total.

This is the combinatorial core of `Kakeya.ml1Boot.exists_massBand`, with the geometry stripped out.
Two steps: discard the members below `1/(2 #s)` of the maximum, which
`Kakeya.ml1Boot.sum_le_two_mul_sum_filter_of_le_max` shows costs a factor `2`; what survives lies in
a range of ratio at most `2 #s`, and `ENNReal.dyadic_pigeonhole₁''` extracts a factor-two window
from it at a cost `1 + log₂ (2 #s)`.

The loss depends on the *cardinality* and on nothing else — in particular not on how small the
values are — which is exactly what the density banding of
`Kakeya.ShadedBody.exists_isCRefinement_comparable_density` fails to achieve; see the docstring of
`Kakeya.ml1Boot.bandLoss`. -/
theorem exists_twoSidedBand {ι : Type*} (s : Finset ι) (x : ι → ℝ≥0∞)
    (hpos : 0 < ∑ i ∈ s, x i) (htop : ∑ i ∈ s, x i ≠ ⊤) :
    ∃ s₂ ⊆ s, ∃ μ : ℝ≥0∞, 0 < μ ∧ μ ≠ ⊤ ∧ s₂.Nonempty ∧
      (∀ i ∈ s₂, μ ≤ x i ∧ x i ≤ 2 * μ) ∧
      ∑ i ∈ s, x i
        ≤ 2 * ENNReal.ofReal (1 + Real.logb 2 (2 * (s.card : ℝ))) * ∑ i ∈ s₂, x i := by
  classical
  -- 0. s is nonempty
  have hsne : s.Nonempty := by
    by_contra h
    have hsempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [hsempty] at hpos
  have hcard_pos : 0 < s.card := Finset.card_pos.mpr hsne
  have hcard_nn : (s.card : ℝ≥0) ≠ 0 := by exact_mod_cast (ne_of_gt hcard_pos)
  have hcard_enn : (s.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast (ne_of_gt hcard_pos)
  have hcard_ℝ : (s.card : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hcard_pos)
  have hxi_le_sum : ∀ i ∈ s, x i ≤ ∑ i ∈ s, x i := by
    intro i hi
    exact Finset.single_le_sum (fun i _ => bot_le) hi
  have hxi_top : ∀ i ∈ s, x i ≠ ⊤ := by
    intro i hi
    exact ne_top_of_le_ne_top htop (hxi_le_sum i hi)
  -- 1. maximum
  rcases Finset.exists_max_image s x hsne with ⟨iₘ, hiₘ, hmax⟩
  let ν : ℝ≥0∞ := x iₘ
  have hν_top : ν ≠ ⊤ := by simpa [ν] using hxi_top iₘ hiₘ
  have hν_pos : 0 < ν := by
    by_contra h
    have hle0 : ν ≤ 0 := le_of_not_gt h
    have hsum0 : ∑ i ∈ s, x i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact le_antisymm (le_trans (hmax i hi) hle0) bot_le
    exact (ne_of_gt hpos) hsum0
  have hν_le_sum : ν ≤ ∑ i ∈ s, x i := by simpa [ν] using hxi_le_sum iₘ hiₘ
  have hν_ne0 : ν ≠ 0 := ne_of_gt hν_pos
  -- 2. discard low members
  let s₁ : Finset ι := s.filter (fun i => ν ≤ 2 * (s.card : ℝ≥0∞) * x i)
  have hs₁ss : s₁ ⊆ s := Finset.filter_subset _ s
  have hsum₁ : ∑ i ∈ s, x i ≤ 2 * ∑ i ∈ s₁, x i := by
    have hA := sum_le_two_mul_sum_filter_of_le_max s x (fun i hi => by simpa [ν] using hmax i hi)
      (by simpa [ν] using hν_le_sum) htop
    simpa [s₁] using hA
  have hone_le : (1 : ℝ≥0∞) ≤ 2 * (s.card : ℝ≥0∞) := by
    have hc1 : (1 : ℕ) ≤ s.card := Nat.succ_le_of_lt hcard_pos
    have h1 : (1 : ℝ≥0∞) ≤ (s.card : ℝ≥0∞) := by exact_mod_cast hc1
    have h2 : (s.card : ℝ≥0∞) ≤ (2 : ℝ≥0∞) * (s.card : ℝ≥0∞) := by
      calc
        (s.card : ℝ≥0∞) = (1 : ℝ≥0∞) * (s.card : ℝ≥0∞) := by rw [one_mul]
        _ ≤ (2 : ℝ≥0∞) * (s.card : ℝ≥0∞) := by
          exact mul_le_mul_of_nonneg_right (by norm_num : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞)) zero_le
    exact h1.trans h2
  have hmₘ_s₁ : iₘ ∈ s₁ := by
    apply Finset.mem_filter.mpr
    constructor
    · exact hiₘ
    · dsimp [ν]
      calc
        x iₘ = 1 * x iₘ := by rw [one_mul]
        _ ≤ (2 * (s.card : ℝ≥0∞)) * x iₘ := by
          exact mul_le_mul_of_nonneg_right hone_le zero_le
        _ = 2 * (s.card : ℝ≥0∞) * x iₘ := by rfl
  have hs₁ne : s₁.Nonempty := ⟨iₘ, hmₘ_s₁⟩
  have hs₁_pos : 0 < ∑ i ∈ s₁, x i := by
    have hx : x iₘ ≤ ∑ i ∈ s₁, x i :=
      Finset.single_le_sum (fun i _ => bot_le) hmₘ_s₁
    exact lt_of_lt_of_le (by simpa [ν] using hν_pos) hx
  -- 3. NNReal normalisation
  let N : ℝ≥0 := ν.toNNReal
  have hN_coe : (N : ℝ≥0∞) = ν := by
    dsimp [N]
    exact ENNReal.coe_toNNReal hν_top
  have hN_pos : 0 < N := by
    dsimp [N]
    exact ENNReal.toNNReal_pos hν_ne0 hν_top
  have hN_ne0 : N ≠ 0 := ne_of_gt hN_pos
  let b : ℝ≥0 := N
  let a : ℝ≥0 := N / (2 * (s.card : ℝ≥0))
  have ha_pos : 0 < a := by
    dsimp [a]
    positivity
  have h2nn : (2 * (s.card : ℝ≥0) : ℝ≥0) ≠ 0 := by
    exact mul_ne_zero (by norm_num : (2 : ℝ≥0) ≠ 0) hcard_nn
  have ha_coe : (a : ℝ≥0∞) = ν / (2 * (s.card : ℝ≥0∞)) := by
    dsimp [a]
    rw [ENNReal.coe_div h2nn]
    rw [hN_coe]
    simp
  have hNℝ : (N : ℝ) ≠ 0 := by exact_mod_cast hN_ne0
  have hratio : (b : ℝ) / (a : ℝ) = 2 * (s.card : ℝ) := by
    dsimp [a, b]
    norm_cast
    field_simp [hNℝ, hcard_ℝ]
    norm_num
  -- 4. pigeonhole
  have hden0 : (2 * (s.card : ℝ≥0∞)) ≠ 0 := by
    exact mul_ne_zero (by norm_num : (2 : ℝ≥0∞) ≠ 0) hcard_enn
  have hdenTop : (2 * (s.card : ℝ≥0∞)) ≠ ⊤ := by
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top 2) (ENNReal.natCast_ne_top s.card)
  have hIcc : ∀ i ∈ s₁, x i ∈ Set.Icc (a : ℝ≥0∞) (b : ℝ≥0∞) := by
    intro i hi
    rw [Set.mem_Icc]
    constructor
    · rw [ha_coe]
      have hc : ν ≤ 2 * (s.card : ℝ≥0∞) * x i := (Finset.mem_filter.mp hi).2
      refine (ENNReal.div_le_iff_le_mul (Or.inl hden0) (Or.inl hdenTop)).mpr ?_
      rwa [mul_comm] at hc
    · have his : i ∈ s := hs₁ss hi
      have hxh : x i ≤ ν := by simpa [ν] using hmax i his
      change x i ≤ (b : ℝ≥0∞)
      dsimp [b]
      rw [hN_coe]
      exact hxh
  rcases ENNReal.dyadic_pigeonhole₁'' (s := s₁) x x (a := a) (b := b) ha_pos hIcc with
    ⟨s₂, hs₂s₁, hsum₂, hband⟩
  -- 5. s₂ nonempty
  have hs₂ne : s₂.Nonempty := by
    by_contra h
    have hs₂empty : s₂ = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have h₁le0 : (∑ i ∈ s₁, x i) ≤ 0 := by
      have hz : ENNReal.ofReal (1 + Real.logb 2 ((b : ℝ) / a)) * (∑ i ∈ s₂, x i) = 0 := by
        simp [hs₂empty]
      simpa [hz] using hsum₂
    exact (not_lt_of_ge h₁le0) hs₁_pos
  -- 6. minimum on s₂
  rcases Finset.exists_min_image s₂ x hs₂ne with ⟨i₁, hi₁₂, hmin⟩
  let μ : ℝ≥0∞ := x i₁
  have hi₁s₁ : i₁ ∈ s₁ := hs₂s₁ hi₁₂
  have hμ_pos : 0 < μ := by
    have hlb : ν ≤ 2 * (s.card : ℝ≥0∞) * x i₁ := (Finset.mem_filter.mp hi₁s₁).2
    have hx_ne0 : x i₁ ≠ 0 := by
      intro hx
      have : 0 < (2 * (s.card : ℝ≥0∞)) * x i₁ := lt_of_lt_of_le hν_pos hlb
      simp [hx] at this
    have hposx : 0 < x i₁ := lt_of_le_of_ne zero_le (Ne.symm hx_ne0)
    simpa [μ] using hposx
  have hμ_top : μ ≠ ⊤ := by
    have hi₁s : i₁ ∈ s := hs₁ss hi₁s₁
    have hle : x i₁ ≤ ∑ i ∈ s, x i := Finset.single_le_sum (fun i _ => bot_le) hi₁s
    simpa [μ] using (ne_top_of_le_ne_top htop hle)
  have hwindow : ∀ i ∈ s₂, μ ≤ x i ∧ x i ≤ 2 * μ := by
    intro i hi
    constructor
    · simpa [μ] using hmin i hi
    · simpa [μ] using hband i hi i₁ hi₁₂
  -- 7. assemble
  refine ⟨s₂, hs₂s₁.trans hs₁ss, μ, hμ_pos, hμ_top, hs₂ne, hwindow, ?_⟩
  have hof : ENNReal.ofReal (1 + Real.logb 2 ((b : ℝ) / a))
      = ENNReal.ofReal (1 + Real.logb 2 (2 * (s.card : ℝ))) := by
    rw [hratio]
  calc
    ∑ i ∈ s, x i ≤ 2 * ∑ i ∈ s₁, x i := hsum₁
    _ ≤ 2 * (ENNReal.ofReal (1 + Real.logb 2 ((b : ℝ) / a)) * ∑ i ∈ s₂, x i) := by
      exact mul_le_mul_of_nonneg_left hsum₂ (by positivity)
    _ = 2 * (ENNReal.ofReal (1 + Real.logb 2 (2 * (s.card : ℝ))) * ∑ i ∈ s₂, x i) := by
      rw [hof]
    _ = (2 * ENNReal.ofReal (1 + Real.logb 2 (2 * (s.card : ℝ)))) * ∑ i ∈ s₂, x i := by
      rw [← mul_assoc]

/-- **Banding the shade volumes of a family of shaded tubes, at a loss depending on the
cardinality alone.**

A family of shaded `σ`-tubes of positive total shading volume has a subfamily on which the
shading densities are two-sidedly comparable to a single positive `λ`, at the cost of a factor
`Kakeya.ml1Boot.bandLoss #s` in the retained mass, and with `λ` at least
`(bandLoss #s)⁻¹ λ(𝕍, Z)`.

This is the pigeonhole that the shaded-uniformization interface needs of its input: that
interface asks for a two-sided density bracket at some `λ₀ > 0`, and no hypothesis of
`Kakeya.ml1Boot.exists_uniformFactorCore` provides one.  (The interface has no Lean carrier; the
sorried `exists_shadedUniform_of_card_le` that used to record it was deleted, see
`Kakeya/DimensionThree/MainLemma1/Inventory.lean`, §B.)  It is *not*
`Kakeya.ShadedBody.exists_isCRefinement_comparable_density`, whose loss is not subpolynomial in
`δ` uniformly in the family; see the docstring of `Kakeya.ml1Boot.bandLoss` for why, and
`Kakeya.ml1Boot.eventually_bandLoss_le_rpow_neg` for the bound that makes this one affordable.

Note that the shading is *not* changed: the conclusion is a statement about the given `Z`, with
only the index set cut down.  That is what lets the interface be applied to the output and its
`fine_shade` clause be read off against the original family. -/
theorem exists_massBand [Nontrivial E] {σ : ℝ≥0} (hσ0 : 0 < σ)
    {ι : Type*} (s : Finset ι) (V : ι → ShadedTube σ E)
    (hmass : 0 < ∑ i ∈ s, volume (V i).shade) :
    ∃ s₂ ⊆ s, ∃ lam : ℝ≥0, 0 < lam ∧ s₂.Nonempty ∧
      (∀ i ∈ s₂, (lam : ℝ≥0∞) * volume (V i).carrier ≤ volume (V i).shade ∧
        volume (V i).shade ≤ 2 * (lam : ℝ≥0∞) * volume (V i).carrier) ∧
      ∑ i ∈ s, volume (V i).shade ≤ bandLoss s.card * ∑ i ∈ s₂, volume (V i).shade ∧
      (ShadedBody.fullness s (fun i => (V i).toShadedBody) : ℝ≥0∞)
        ≤ bandLoss s.card * (lam : ℝ≥0∞) := by
  classical
  have hs_nonempty : s.Nonempty := by
    by_contra hne
    have hs_empty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [hs_empty] at hmass
  rcases hs_nonempty with ⟨i₀, hi₀⟩
  set M : ℝ≥0∞ := ∑ i ∈ s, volume (V i).shade with hM_def
  have hv0_t : 0 < volume (V i₀).toTube.carrier := by
    have hc : 0 < (_root_.Tube.le_volume.c (Module.finrank ℝ E) : ℝ≥0∞) := by
      exact ENNReal.coe_pos.mpr (_root_.Tube.le_volume.c_pos (Module.finrank ℝ E))
    have hσp : 0 < (σ : ℝ≥0∞) ^ (Module.finrank ℝ E - 1) := by
      exact ENNReal.pow_pos (ENNReal.coe_pos.mpr hσ0) (Module.finrank ℝ E - 1)
    have hpos : 0 < (_root_.Tube.le_volume.c (Module.finrank ℝ E) : ℝ≥0∞) *
        (σ : ℝ≥0∞) ^ (Module.finrank ℝ E - 1) :=
      ENNReal.mul_pos (ne_of_gt hc) (ne_of_gt hσp)
    exact lt_of_lt_of_le hpos (by simpa using _root_.Tube.le_volume (V i₀).toTube)
  let v : ℝ≥0∞ := volume (V i₀).carrier
  have hv_pos : 0 < v := by simpa [v] using hv0_t
  have hv_top : v ≠ ⊤ := by
    have htop : volume (V i₀).toTube.carrier ≠ ⊤ :=
      (V i₀).toTube.isCompact.measure_lt_top.ne
    simpa [v] using htop
  have hcarrier : ∀ i, volume (V i).carrier = v := by
    intro i
    calc
      volume (V i).carrier = volume (V i₀).carrier := by
        simpa using
          _root_.Tube.volume_carrier_eq_volume_carrier (V i).toTube (V i₀).toTube
      _ = v := rfl
  have hsum_car : ∑ i ∈ s, volume (V i).carrier = (s.card : ℝ≥0∞) * v := by
    simpa [v] using
      _root_.Tube.sum_volume_carrier_eq_card_mul (fun i => (V i).toTube) (V i₀).toTube s
  have hM_le : M ≤ (s.card : ℝ≥0∞) * v := by
    calc
      M ≤ ∑ i ∈ s, volume (V i).carrier := by
        simpa [M] using Finset.sum_le_sum (fun i hi => measure_mono (V i).shade_subset)
      _ = (s.card : ℝ≥0∞) * v := hsum_car
  have hcard0 : (s.card : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Finset.card_pos.mpr ⟨i₀, hi₀⟩))
  have hcardtop : (s.card : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hden0 : (s.card : ℝ≥0∞) * v ≠ 0 := ne_of_gt (ENNReal.mul_pos hcard0 (ne_of_gt hv_pos))
  have hdenTop : (s.card : ℝ≥0∞) * v ≠ ⊤ := ENNReal.mul_ne_top hcardtop hv_top
  have hM_top : M ≠ ⊤ := by
    exact lt_top_iff_ne_top.mp (lt_of_le_of_lt hM_le (lt_top_iff_ne_top.mpr hdenTop))
  rcases exists_twoSidedBand s (fun i => volume (V i).shade) hmass hM_top with
    ⟨s₂, hss₂, μ, hμ0, hμtop, hs₂ne, hwindow, htotal⟩
  set ofL : ℝ≥0∞ := ENNReal.ofReal (1 + Real.logb 2 (2 * (s.card : ℝ))) with hofL
  let lam : ℝ≥0 := (μ / v).toNNReal
  have hμv0 : μ / v ≠ 0 := ne_of_gt (ENNReal.div_pos (ne_of_gt hμ0) hv_top)
  have hμvTop : μ / v ≠ ⊤ := ENNReal.div_ne_top hμtop (ne_of_gt hv_pos)
  have hlam_pos : 0 < lam := by
    exact ENNReal.toNNReal_pos hμv0 hμvTop
  have hlam_coe : (lam : ℝ≥0∞) = μ / v := by
    exact ENNReal.coe_toNNReal hμvTop
  have hlam_mul : (lam : ℝ≥0∞) * v = μ := by
    rw [hlam_coe]
    exact ENNReal.div_mul_cancel (ne_of_gt hv_pos) hv_top
  have hdens : ∀ i ∈ s₂, (lam : ℝ≥0∞) * volume (V i).carrier ≤ volume (V i).shade ∧
      volume (V i).shade ≤ 2 * (lam : ℝ≥0∞) * volume (V i).carrier := by
    intro i hi
    constructor
    · calc
        (lam : ℝ≥0∞) * volume (V i).carrier = (lam : ℝ≥0∞) * v := by rw [hcarrier i]
        _ = μ := hlam_mul
        _ ≤ volume (V i).shade := (hwindow i hi).1
    · calc
        volume (V i).shade ≤ 2 * μ := (hwindow i hi).2
        _ = 2 * ((lam : ℝ≥0∞) * v) := by rw [← hlam_mul]
        _ = 2 * (lam : ℝ≥0∞) * v := by rw [mul_assoc]
        _ = 2 * (lam : ℝ≥0∞) * volume (V i).carrier := by rw [hcarrier i]
  have hmassBand : M ≤ bandLoss s.card * (∑ i ∈ s₂, volume (V i).shade) := by
    calc
      M ≤ 2 * ofL * (∑ i ∈ s₂, volume (V i).shade) := htotal
      _ ≤ bandLoss s.card * (∑ i ∈ s₂, volume (V i).shade) := by
        change (2 : ℝ≥0∞) * ofL * (∑ i ∈ s₂, volume (V i).shade)
            ≤ (8 : ℝ≥0∞) * ofL * (∑ i ∈ s₂, volume (V i).shade)
        gcongr
        norm_num
  have hfull_eq :
      (ShadedBody.fullness s (fun i => (V i).toShadedBody) : ℝ≥0∞)
        = M / ((s.card : ℝ≥0∞) * v) := by
    rw [ShadedBody.fullness_def]
    congr 1
  have hRhs : M ≤ (8 : ℝ≥0∞) * ofL * (lam : ℝ≥0∞) * ((s.card : ℝ≥0∞) * v) := by
    have hM2_le : (∑ i ∈ s₂, volume (V i).shade) ≤ (s₂.card : ℝ≥0∞) * (2 * μ) := by
      calc
        ∑ i ∈ s₂, volume (V i).shade ≤ ∑ i ∈ s₂, 2 * μ := by
          exact Finset.sum_le_sum (fun i hi => (hwindow i hi).2)
        _ = (s₂.card : ℝ≥0∞) * (2 * μ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    calc
      M ≤ 2 * ofL * (∑ i ∈ s₂, volume (V i).shade) := htotal
      _ ≤ 2 * ofL * ((s₂.card : ℝ≥0∞) * (2 * μ)) := by
        gcongr
      _ ≤ 2 * ofL * ((s.card : ℝ≥0∞) * (2 * μ)) := by
        gcongr
      _ = (4 : ℝ≥0∞) * ofL * μ * (s.card : ℝ≥0∞) := by ring
      _ = (4 : ℝ≥0∞) * ofL * ((lam : ℝ≥0∞) * v) * (s.card : ℝ≥0∞) := by
        rw [← hlam_mul]
      _ ≤ (8 : ℝ≥0∞) * ofL * ((lam : ℝ≥0∞) * v) * (s.card : ℝ≥0∞) := by
        gcongr
        norm_num
      _ = (8 : ℝ≥0∞) * ofL * (lam : ℝ≥0∞) * ((s.card : ℝ≥0∞) * v) := by ring
  have hfull_le :
      (ShadedBody.fullness s (fun i => (V i).toShadedBody) : ℝ≥0∞)
        ≤ bandLoss s.card * (lam : ℝ≥0∞) := by
    rw [hfull_eq]
    change M / ((s.card : ℝ≥0∞) * v) ≤ (8 : ℝ≥0∞) * ofL * (lam : ℝ≥0∞)
    rw [ENNReal.div_le_iff hden0 hdenTop]
    exact hRhs
  exact ⟨s₂, hss₂, lam, hlam_pos, hs₂ne, hdens, hmassBand, hfull_le⟩

/-- **The leaf-dependent part of `Kakeya.ml1Boot.IsFactorOneScale`.**

`Kakeya.ml1Boot.IsFactorOneScale` with the five clauses that do *not* depend on the Section 2
uniformization leaf removed:

* `fine_essDistinct` and `coarse_essDistinct`, which are `Set.Pairwise.mono` along
  `fine_subset` and `coarse_subset`;
* `aux_subset` and `aux_card`, which hold at `t'q = tq` by
  `Kakeya.ml1Boot.rpow_mul_card_le_card`;
* `frostman`, which is `ConvexSpaceBody.frostmanConstIn_subfamily_le` applied to the fibre
  retention already recorded in `branch_card`.

`Kakeya.ml1Boot.isFactorOneScale_of_core` proves all five, so this bundle and
`Kakeya.ml1Boot.IsFactorOneScale` differ only by proved material.  Splitting them is what lets
the gap of `Kakeya.ml1Boot.exists_uniformFactorPair` be stated without them.

The auxiliary classification `(tq, q, t'q)` of `Kakeya.ml1Boot.IsFactorOneScale` is absent here
for the same reason: it carries no information that the construction has to supply. -/
structure IsUniformFactorCore {ι κ : Type*} [DecidableEq κ]
    {σ ρ : ℝ≥0} (δ : ℝ≥0) (ε' : ℝ) (s : Finset ι) (V : ι → ShadedTube σ E)
    (t : Finset κ) (Vρ : κ → Tube ρ E) (p : ι → κ)
    (s' : Finset ι) (t'' : Finset κ)
    (Z' : ι → ShadedTube σ E) (Zρ : κ → ShadedTube ρ E)
    (lamσ lamρ N : ℝ≥0) : Prop where
  /-- The fine index set is a subset of `s`. -/
  fine_subset : s' ⊆ s
  /-- `Z'` shades the same tubes as `𝕍` and is contained in `Z`. -/
  fine_shade : ∀ i ∈ s', (Z' i).toTube = (V i).toTube ∧ (Z' i).shade ⊆ (V i).shade
  /-- `(𝕍|_{s'}, Z')` is a `δ ^ (2 ε')`-refinement of `(𝕍, Z)`. -/
  fine_refinement : ShadedBody.IsCRefinement s' (fun i => (Z' i).toShadedBody) s
    (fun i => (V i).toShadedBody) ⟨(δ : ℝ) ^ (2 * ε'), by positivity⟩
  /-- The fine family is uniform, at the constant `Kakeya.ml1Boot.uniformize.C 3`. -/
  fine_unif : Nonempty (ShadedTube.ShadedUniformTubeSet s' Z' (Tube.ssfGridLen σ)
    (uniformize.C 3))
  /-- The fine shading densities are two-sidedly comparable to `λ_σ`. -/
  fine_dens : ∀ i ∈ s', (lamσ : ℝ≥0∞) * volume (V i).carrier ≤ volume (Z' i).shade ∧
    volume (Z' i).shade ≤ 2 * (lamσ : ℝ≥0∞) * volume (V i).carrier
  /-- `λ_σ ≥ δ ^ (2 ε') λ(𝕍, Z)`. -/
  fine_fullness : (δ : ℝ≥0∞) ^ (2 * ε')
      * ShadedBody.fullness s (fun i => (V i).toShadedBody) ≤ (lamσ : ℝ≥0∞)
  /-- The coarse index set is a subset of `t`. -/
  coarse_subset : t'' ⊆ t
  /-- `Z_ρ` shades the parent tubes. -/
  coarse_tube : ∀ k ∈ t'', (Zρ k).toTube = Vρ k
  /-- The coarse family is uniform, at the constant `Kakeya.ml1Boot.uniformize.C 3`. -/
  coarse_unif : Nonempty (ShadedTube.ShadedUniformTubeSet t'' Zρ (Tube.ssfGridLen ρ)
    (uniformize.C 3))
  /-- The coarse shading densities are two-sidedly comparable to `λ_ρ`. -/
  coarse_dens : ∀ k ∈ t'', (lamρ : ℝ≥0∞) * volume (Vρ k).carrier ≤ volume (Zρ k).shade ∧
    volume (Zρ k).shade ≤ 2 * (lamρ : ℝ≥0∞) * volume (Vρ k).carrier
  /-- `λ_ρ ≥ C⁻¹ δ ^ (2 ε') λ(𝕍, Z)`, at `C = factorOneScale.C #s σ`. -/
  coarse_fullness : (factorOneScale.C s.card σ : ℝ≥0∞)⁻¹ * (δ : ℝ≥0∞) ^ (2 * ε')
      * ShadedBody.fullness s (fun i => (V i).toShadedBody) ≤ (lamρ : ℝ≥0∞)
  /-- The shadings are nested along the parent map. -/
  contain : ∀ i ∈ s', p i ∈ t'' → (Z' i).shade ⊆ (Zρ (p i)).shade
  /-- Every retained member has its parent retained. -/
  branch_mapsTo : ∀ i ∈ s', p i ∈ t''
  /-- The retained fibres have cardinality comparable to `N` and each retains a
  `δ ^ (2 ε')` fraction. -/
  branch_card : ∀ k ∈ t'',
    (N : ℝ≥0∞) ≤ ((fibre s' p k).card : ℝ≥0∞) ∧
    ((fibre s' p k).card : ℝ≥0∞) ≤ 2 * (N : ℝ≥0∞) ∧
    (δ : ℝ≥0∞) ^ (2 * ε') * ((fibre s p k).card : ℝ≥0∞)
      ≤ ((fibre s' p k).card : ℝ≥0∞)
  /-- The multiplicity factors with loss `C δ ^ (-2 ε')`, at `C = factorOneScale.C #s σ`. -/
  product : ∀ k ∈ t'', ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
    ≤ (factorOneScale.C s.card σ : ℝ≥0∞) * (δ : ℝ≥0∞) ^ (-2 * ε')
      * ShadedBody.multiplicity t'' (fun k' => (Zρ k').toShadedBody)
      * ShadedBody.multiplicity (fibre s' p k) (fun i => (Z' i).toShadedBody)
  /-- Every retained fibre of the parent map is itself uniform, in the **one-sided** reading
  `Kakeya.IsFlatPrismUniform`.  Read this way the clause is a *consequence* of `fine_unif` at the
  same constant, by
  `Kakeya.ml1Boot.nonempty_isFlatPrismUniform_fibre_of_shadedUniformTubeSet`, so it costs the
  producer nothing; see the docstring of `Kakeya.ml1Boot.exists_uniformFactorCore`. -/
  fibreUnif : ∀ k ∈ t'', Nonempty (IsFlatPrismUniform (fibre s' p k) Z'
    (Tube.ssfGridLen σ) (uniformize.C 3))

/-! ### One factoring step over a `2`-dilate parent family -/

/-- **The opaque witness behind `C_{lem:ml1bootFactorOneScaleUniformDilate}`**.

The clause the blueprint definition asks of the constant is carried here, in the type, so that
it is a theorem about the constant rather than an assumption about an opaque object that
exposes nothing.  No *value* is committed to: the witness is `opaque`, and
`Kakeya.ml1Boot.factorOneScaleUniformDilate.instNonemptyAdmissible` only says the subtype is
inhabited, not which element is chosen. -/
noncomputable opaque factorOneScaleUniformDilate.CWitness :
    {C : ℝ≥0 // 1 ≤ C}

/-- **The constant `C_{lem:ml1bootFactorOneScaleUniformDilate}`**: the loss constant of one
factoring step run
over a **`2`-dilate** parent family at fullness `λ(𝕍, Z) ≥ δ ^ ε'`.

It is deliberately **not** `Kakeya.ml1Boot.factorOneScale.C`.  The dilate form is a restatement
of GWZ Lemma 5.11 under a weakened containment, and what the restatement costs is not known at
this constant.  The blueprint accordingly proposes *no* value, provisional or otherwise, so the
constant remains opaque.

The single clause the blueprint definition asks of it, `1 ≤ C`, is carried by the **type** of
the opaque witness `Kakeya.ml1Boot.factorOneScaleUniformDilate.CWitness` rather than asserted
about a constant that exposes no value.  Nothing is assumed thereby: the subtype is inhabited
by `1`, so the witness exists outright, and
`Kakeya.ml1Boot.factorOneScaleUniformDilate.one_le_C` is a *theorem* — the projection of the
witness — rather than an assumption.  The **value** stays unknown: the witness is `opaque`, so
no consumer can unfold `C` past
`Kakeya.ml1Boot.factorOneScaleUniformDilate.CWitness.val`, and no lemma stated at this
constant, in particular `Kakeya.ml1Boot.exists_factorOneScaleUniform_dilate`, is thereby
strengthened.

## The comparison clause `factorOneScale.C ≤ C` has been removed, and had to be

The witness used to carry a second clause, `factorOneScale.C ≤ C`, and
`Kakeya.ml1Boot.IsUniformFactorCoreDilate` used to be stated at
`Kakeya.ml1Boot.factorOneScale.C`, the passage to this constant happening in
`Kakeya.ml1Boot.IsUniformFactorCoreDilate.toFactorOneScaleDilate` by that comparison. That
was tenable only while `Kakeya.ml1Boot.factorOneScale.C` was the numeral `1`. It is now a
function of the inner cardinality `#s` and the inner tube scale, unbounded in the first, so no
*absolute* constant dominates it and the clause is unstatable at this arity. The two options
were to give this constant the same two binders, or to state the dilate core here. The first
is not available: this constant is `opaque`, so nothing but `1 ≤ C` is provable of it, and the
dilate assembly `Kakeya.ml1Boot.normalized_le_of_coarse_dilate` needs
`C · δ̃ ^ ap' ≤ 1` eventually in `δ̃` **before** the family and hence `#s` exist — a
subpolynomial bound in `#s` that an opaque constant cannot supply. So
`Kakeya.ml1Boot.IsUniformFactorCoreDilate` is now stated at this constant directly.

It depends only on the ambient dimension `3`; in particular not on `δ`, on `σ`, on `ρ`, on
`ε'`, or on the family. -/
noncomputable def factorOneScaleUniformDilate.C : ℝ≥0 :=
  factorOneScaleUniformDilate.CWitness.val

/-- **`C ≥ 1`** for the dilate factoring constant.  A theorem, not an assumption: it is the
defining property carried by the type of
`Kakeya.ml1Boot.factorOneScaleUniformDilate.CWitness`. -/
theorem factorOneScaleUniformDilate.one_le_C : 1 ≤ factorOneScaleUniformDilate.C := by
  exact factorOneScaleUniformDilate.CWitness.property

/-- **The conclusions of `Kakeya.ml1Boot.exists_factorOneScaleUniform_dilate`, one field per
item** (blueprint `lem:ml1bootFactorOneScaleUniformDilate`, items (a)–(e)).

These are items (a), (b), (d), (e) and (f) of `Kakeya.ml1Boot.IsFactorOneScale`, at the opaque
absolute constant `Kakeya.ml1Boot.factorOneScaleUniformDilate.C` in place of that structure's
scale- and cardinality-dependent `Kakeya.ml1Boot.factorOneScale.C #s σ`; see the former's
docstring for why the dilate chain is stated at an absolute constant.  Three groups of fields
of that structure are **dropped**,
and none of them is dropped because it fails:

* `Kakeya.ml1Boot.IsFactorOneScale.contain`, the pointwise nesting `Z' i ⊆ Z_ρ (p i)` of the
  shadings, is *false* in the dilate setting — a fine tube in `2 · V_{ρ,k}` may be disjoint
  from `V_{ρ,k}` — and asserting it would be asserting something false;
* `Kakeya.ml1Boot.IsFactorOneScale.fibreUnif`, fibre uniformity, and the auxiliary
  classification `(tq, q, t'q)` with its two cardinality clauses, are simply unused by the
  dilate consumer, which cites (a)–(e) and nothing else.

The coarse output `𝕍_ρ|_{t''}` is a family of **honest** `ρ`-tubes and `Z_ρ` shades those
tubes, not their dilates; that is what keeps
`Kakeya.ml1Boot.normalized_le_of_coarse`'s coarse hypothesis applicable to what this returns,
and it is also where the difficulty of the assumption sits. -/
structure IsFactorOneScaleDilate {ι κ : Type*} [DecidableEq κ]
    {σ ρ : ℝ≥0} (δ : ℝ≥0) (ε' : ℝ) (s : Finset ι) (V : ι → ShadedTube σ E)
    (t : Finset κ) (Vρ : κ → Tube ρ E) (p : ι → κ)
    (s' : Finset ι) (t'' : Finset κ)
    (Z' : ι → ShadedTube σ E) (Zρ : κ → ShadedTube ρ E)
    (lamσ lamρ N : ℝ≥0) : Prop where
  /-- (a) The fine index set is a subset of `s`. -/
  fine_subset : s' ⊆ s
  /-- (a) `Z'` shades the same tubes as `𝕍` and is contained in `Z`. -/
  fine_shade : ∀ i ∈ s', (Z' i).toTube = (V i).toTube ∧ (Z' i).shade ⊆ (V i).shade
  /-- (a) `(𝕍|_{s'}, Z')` is a `δ ^ (2 ε')`-refinement of `(𝕍, Z)`. -/
  fine_refinement : ShadedBody.IsCRefinement s' (fun i => (Z' i).toShadedBody) s
    (fun i => (V i).toShadedBody) ⟨(δ : ℝ) ^ (2 * ε'), by positivity⟩
  /-- (a) The fine family is uniform, at the constant `Kakeya.ml1Boot.uniformize.C 3`. -/
  fine_unif : Nonempty (ShadedTube.ShadedUniformTubeSet s' Z' (Tube.ssfGridLen σ)
    (uniformize.C 3))
  /-- (a) Essential distinctness is inherited by the fine family. -/
  fine_essDistinct : (s' : Set ι).Pairwise
    (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier)
  /-- (a) The fine shading densities are two-sidedly comparable to `λ_σ`. -/
  fine_dens : ∀ i ∈ s', (lamσ : ℝ≥0∞) * volume (V i).carrier ≤ volume (Z' i).shade ∧
    volume (Z' i).shade ≤ 2 * (lamσ : ℝ≥0∞) * volume (V i).carrier
  /-- (a) `λ_σ ≥ δ ^ (2 ε') λ(𝕍, Z)`. -/
  fine_fullness : (δ : ℝ≥0∞) ^ (2 * ε')
      * ShadedBody.fullness s (fun i => (V i).toShadedBody) ≤ (lamσ : ℝ≥0∞)
  /-- (b) The coarse index set is a subset of `t`. -/
  coarse_subset : t'' ⊆ t
  /-- (b) `Z_ρ` shades the parent tubes themselves, not their dilates. -/
  coarse_tube : ∀ k ∈ t'', (Zρ k).toTube = Vρ k
  /-- (b) The coarse family is uniform, at the constant `Kakeya.ml1Boot.uniformize.C 3`. -/
  coarse_unif : Nonempty (ShadedTube.ShadedUniformTubeSet t'' Zρ (Tube.ssfGridLen ρ)
    (uniformize.C 3))
  /-- (b) Essential distinctness is inherited by the coarse family. -/
  coarse_essDistinct : (t'' : Set κ).Pairwise
    (fun k k' => IsEssentiallyDistinct (Vρ k).carrier (Vρ k').carrier)
  /-- (b) The coarse shading densities are two-sidedly comparable to `λ_ρ`. -/
  coarse_dens : ∀ k ∈ t'', (lamρ : ℝ≥0∞) * volume (Vρ k).carrier ≤ volume (Zρ k).shade ∧
    volume (Zρ k).shade ≤ 2 * (lamρ : ℝ≥0∞) * volume (Vρ k).carrier
  /-- (b) `λ_ρ ≥ C⁻¹ δ ^ (2 ε') λ(𝕍, Z)`, at the **dilate** constant. -/
  coarse_fullness : (factorOneScaleUniformDilate.C : ℝ≥0∞)⁻¹ * (δ : ℝ≥0∞) ^ (2 * ε')
      * ShadedBody.fullness s (fun i => (V i).toShadedBody) ≤ (lamρ : ℝ≥0∞)
  /-- (c) Every retained member has its parent retained. -/
  branch_mapsTo : ∀ i ∈ s', p i ∈ t''
  /-- (c) The retained fibres have cardinality comparable to `N` and each retains a
  `δ ^ (2 ε')` fraction. -/
  branch_card : ∀ k ∈ t'',
    (N : ℝ≥0∞) ≤ ((fibre s' p k).card : ℝ≥0∞) ∧
    ((fibre s' p k).card : ℝ≥0∞) ≤ 2 * (N : ℝ≥0∞) ∧
    (δ : ℝ≥0∞) ^ (2 * ε') * ((fibre s p k).card : ℝ≥0∞)
      ≤ ((fibre s' p k).card : ℝ≥0∞)
  /-- (d) Every fibre Frostman constant grows by at most `δ ^ (-2 ε')`. -/
  frostman : ∀ k ∈ t'', ∀ K : ConvexSpaceBody E,
    (∀ i ∈ s, p i = k → (V i).toConvexSpaceBody ≤ K) →
    frostmanConstIn (fibre s' p k) (fun i => (V i).toConvexSpaceBody) K
      ≤ (δ : ℝ≥0∞) ^ (-2 * ε')
        * frostmanConstIn (fibre s p k) (fun i => (V i).toConvexSpaceBody) K
  /-- (e) The multiplicity factors with loss `C δ ^ (-2 ε')`, at the **dilate** constant. -/
  product : ∀ k ∈ t'', ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
    ≤ (factorOneScaleUniformDilate.C : ℝ≥0∞) * (δ : ℝ≥0∞) ^ (-2 * ε')
      * ShadedBody.multiplicity t'' (fun k' => (Zρ k').toShadedBody)
      * ShadedBody.multiplicity (fibre s' p k) (fun i => (Z' i).toShadedBody)

/-- **The core bundle of one factoring step over a `c`-dilate parent family.**

`Kakeya.ml1Boot.IsUniformFactorCore` with the single field `contain` deleted, the field
`fibreUnif` weakened to its one-sided reading, and the two
constants moved from `Kakeya.ml1Boot.factorOneScale.C` to the opaque
`Kakeya.ml1Boot.factorOneScaleUniformDilate.C`; see the latter's docstring for why the move is
forced and why it weakens rather than strengthens what this bundle asserts.

*Why `fibreUnif` is one-sided here.*  Not by design, but because this bundle's only consumer
permits it.  `Kakeya.ml1Boot.IsUniformFactorCoreDilate` feeds
only `Kakeya.ml1Boot.IsUniformFactorCoreDilate.toFactorOneScaleDilate`, whose target
`Kakeya.ml1Boot.IsFactorOneScaleDilate` has no fibre-uniformity field at all, so the field has no
consumer anywhere in the repository and nothing reads either of the two lower brackets from it.
The undilated `Kakeya.ml1Boot.IsUniformFactorCore.fibreUnif` does have consumers, and its chain was
typed two-sidedly as far out as `Kakeya.ml1Boot.multiplicity_le_middle`; it is now one-sided too,
so the two bundles agree again.  The section "Obstruction 2 is gone: the `fibreUnif` restatement,
carried out" in the docstring of `Kakeya.ml1Boot.exists_uniformFactorCore` records what moving it
took.  Weakening the field here cost nothing and removed the simultaneity obstruction from this
bundle's producer.

`contain` is the one field of the core that reads the parent *containment*: it asserts
`(Z' i).shade ⊆ (Zρ (p i)).shade`, and under a `c`-dilate parent family the fine tube lies in
`c · V_{ρ, p i}` rather than in `V_{ρ, p i}`, so its shading has no reason to sit inside the
parent's.  Every other field of the core is a statement about the fine family, the coarse
family, the refinement, the densities, the fullnesses, the branching or the product, none of
which mentions the containment.  That is why this is a deletion rather than a rewrite. -/
structure IsUniformFactorCoreDilate {ι κ : Type*} [DecidableEq κ]
    {σ ρ : ℝ≥0} (δ : ℝ≥0) (ε' : ℝ) (s : Finset ι) (V : ι → ShadedTube σ E)
    (t : Finset κ) (Vρ : κ → Tube ρ E) (p : ι → κ)
    (s' : Finset ι) (t'' : Finset κ)
    (Z' : ι → ShadedTube σ E) (Zρ : κ → ShadedTube ρ E)
    (lamσ lamρ N : ℝ≥0) : Prop where
  /-- The fine index set is a subset of `s`. -/
  fine_subset : s' ⊆ s
  /-- `Z'` shades the same tubes as `𝕍` and is contained in `Z`. -/
  fine_shade : ∀ i ∈ s', (Z' i).toTube = (V i).toTube ∧ (Z' i).shade ⊆ (V i).shade
  /-- `(𝕍|_{s'}, Z')` is a `δ ^ (2 ε')`-refinement of `(𝕍, Z)`. -/
  fine_refinement : ShadedBody.IsCRefinement s' (fun i => (Z' i).toShadedBody) s
    (fun i => (V i).toShadedBody) ⟨(δ : ℝ) ^ (2 * ε'), by positivity⟩
  /-- The fine family is uniform, at the constant `Kakeya.ml1Boot.uniformize.C 3`. -/
  fine_unif : Nonempty (ShadedTube.ShadedUniformTubeSet s' Z' (Tube.ssfGridLen σ)
    (uniformize.C 3))
  /-- The fine shading densities are two-sidedly comparable to `λ_σ`. -/
  fine_dens : ∀ i ∈ s', (lamσ : ℝ≥0∞) * volume (V i).carrier ≤ volume (Z' i).shade ∧
    volume (Z' i).shade ≤ 2 * (lamσ : ℝ≥0∞) * volume (V i).carrier
  /-- `λ_σ ≥ δ ^ (2 ε') λ(𝕍, Z)`. -/
  fine_fullness : (δ : ℝ≥0∞) ^ (2 * ε')
      * ShadedBody.fullness s (fun i => (V i).toShadedBody) ≤ (lamσ : ℝ≥0∞)
  /-- The coarse index set is a subset of `t`. -/
  coarse_subset : t'' ⊆ t
  /-- `Z_ρ` shades the parent tubes. -/
  coarse_tube : ∀ k ∈ t'', (Zρ k).toTube = Vρ k
  /-- The coarse family is uniform, at the constant `Kakeya.ml1Boot.uniformize.C 3`. -/
  coarse_unif : Nonempty (ShadedTube.ShadedUniformTubeSet t'' Zρ (Tube.ssfGridLen ρ)
    (uniformize.C 3))
  /-- The coarse shading densities are two-sidedly comparable to `λ_ρ`. -/
  coarse_dens : ∀ k ∈ t'', (lamρ : ℝ≥0∞) * volume (Vρ k).carrier ≤ volume (Zρ k).shade ∧
    volume (Zρ k).shade ≤ 2 * (lamρ : ℝ≥0∞) * volume (Vρ k).carrier
  /-- `λ_ρ ≥ C⁻¹ δ ^ (2 ε') λ(𝕍, Z)`, at the **dilate** constant. -/
  coarse_fullness : (factorOneScaleUniformDilate.C : ℝ≥0∞)⁻¹ * (δ : ℝ≥0∞) ^ (2 * ε')
      * ShadedBody.fullness s (fun i => (V i).toShadedBody) ≤ (lamρ : ℝ≥0∞)
  /-- Every retained member has its parent retained. -/
  branch_mapsTo : ∀ i ∈ s', p i ∈ t''
  /-- The retained fibres have cardinality comparable to `N` and each retains a
  `δ ^ (2 ε')` fraction. -/
  branch_card : ∀ k ∈ t'',
    (N : ℝ≥0∞) ≤ ((fibre s' p k).card : ℝ≥0∞) ∧
    ((fibre s' p k).card : ℝ≥0∞) ≤ 2 * (N : ℝ≥0∞) ∧
    (δ : ℝ≥0∞) ^ (2 * ε') * ((fibre s p k).card : ℝ≥0∞)
      ≤ ((fibre s' p k).card : ℝ≥0∞)
  /-- The multiplicity factors with loss `C δ ^ (-2 ε')`, at the **dilate** constant. -/
  product : ∀ k ∈ t'', ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
    ≤ (factorOneScaleUniformDilate.C : ℝ≥0∞) * (δ : ℝ≥0∞) ^ (-2 * ε')
      * ShadedBody.multiplicity t'' (fun k' => (Zρ k').toShadedBody)
      * ShadedBody.multiplicity (fibre s' p k) (fun i => (Z' i).toShadedBody)
  /-- Every retained fibre of the parent map is itself uniform, in the **one-sided** reading:
  `Kakeya.IsFlatPrismUniform`, GWZ Definition 2.2 minus `le_card_shadeClass` and `branchingN_le`.
  This field has no consumer (see the structure docstring), and read one-sidedly it is a
  consequence of `fine_unif` at the same constant, by
  `Kakeya.ml1Boot.nonempty_isFlatPrismUniform_fibre_of_shadedUniformTubeSet`. -/
  fibreUnif : ∀ k ∈ t'', Nonempty (IsFlatPrismUniform (fibre s' p k) Z'
    (Tube.ssfGridLen σ) (uniformize.C 3))

/-- **The conclusions of the two-scale factoring step, one field per item.**

There is no Lean producer for this structure.  `exists_factorTwoScales` and
`exists_twoScaleFactorPair` are **not declarations**, and the fine pair the intended route went
through is refuted (`Kakeya.ml1Boot.not_exists_twoScaleFinePair`); what exists is this structure,
the assembly `Kakeya.ml1Boot.isFactorTwoScales_of_factorPair` from two one-scale bundles and a
fine pair, and the exit `Kakeya.ml1Boot.multiplicity_le_caseTwo_of_factorTwoScales`.  See
blueprint `lem:ml1bootFactorTwoScales` and `note:ml1bootCaseTwoConstructionLayerEmpty`.

Here `(𝕋, Y)` is a family of shaded `δ`-tubes indexed by `s`, `(t_τ, 𝕋_τ, p_τ)` is a parent
family for `𝕋` at scale `τ`, `(t_θ, 𝕋_θ, p_θ)` is a parent family for `𝕋_τ` at scale `θ`,
and the output data is `s'`, `t''_τ`, `t'_τ`, `t'_θ`, the shadings `Y'`, `Y_τ`, `Y_θ` and
the numbers `λ_δ`, `λ_τ`, `λ_θ`, `N_τ`, `N_θ`.  The fields are items (a)–(h) of the
blueprint lemma `lem:ml1bootFactorTwoScales`; `C` abbreviates
`Kakeya.ml1Boot.factorTwoScales.C #s δ #t''τ τ`, the product of the two applications' one-scale
loss constants, each read at the cardinality and tube scale of *its own* inner family: `(#s, δ)`
for the first application and `(#t''τ, τ)` for the second, whose inner family is the
intermediate middle index set.

## The intermediate middle index set `t''_τ`

The structure carries a *fourth* index set `t''_τ` with `t'_τ ⊆ t''_τ ⊆ t_τ`, namely the
coarse output of the **first** of the two factoring applications, before the second one
refines the middle family again.  It is not decoration: the only item that mentions a
Frostman constant of an *unrefined* middle fibre, `frostman_mid`, is read off the second
application, which is made to `𝕋_τ|_{t''_τ}` and not to `𝕋_τ`, so the base of that
comparison is `fibre t''τ pθ l'`.  Writing `fibre tτ pθ l'` there — as an alternative form of
both this structure and the blueprint display for `item:twoScaleFrostman` did — is a
non-sequitur, and it cannot be repaired by monotonicity: `Kakeya.frostmanConstIn` is a
*ratio* (the least `C` with `densityIn ≤ C * densityIn` against the anchor, over all
sub-bodies), so shrinking the index set shrinks numerator and denominator together and the
constant moves in neither direction.  The one transport this development has from an ambient
family to a subfamily, `ConvexSpaceBody.IsFrostmanIn.of_subset`, does point the right way,
but it charges the mass ratio: it turns `IsFrostmanIn s W K C` into
`IsFrostmanIn t W K (C * C')` only given `∑_{i ∈ s} |W i| ≤ C' ∑_{i ∈ t} |W i|`.  Supplying
that at `t = fibre t''τ pθ l'`, `s = fibre tτ pθ l'` is exactly the composite fibre retention
that `note:ml1bootCoarseFibreRetentionRetired` refutes, so the route is closed and not merely
unbuilt.

Every other field is insensitive to the distinction, and `frostman_mid` has no consumer in
this development: the middle-side collision reads its upper bound at the unrefined node
family instead, from `Kakeya.ml1Boot.IsCaseTwoInput` through blueprint
`lem:ml1bootLocalDensityUnrefined`.  See blueprint
`note:ml1bootTwoScaleFrostmanMidBase` and `note:ml1bootMiddleCollisionUnrefined`(4).

The shadings are given as families of `ShadedTube`, with the clause "`Y_τ` is a shading of
`𝕋_τ|_{t'_τ}`" recorded as the equality `(Yτ k).toTube = Tτ k` of the underlying tubes.
This is what lets the uniformity clauses be stated at all: `ShadedTube.ShadedUniformTubeSet` is
data-valued, so each uniformity clause is its `Nonempty`. -/
structure IsFactorTwoScales {ι κ l : Type*} [DecidableEq κ] [DecidableEq l]
    {δ τ θ : ℝ≥0} (ε' : ℝ) (s : Finset ι) (T : ι → ShadedTube δ E)
    (tτ : Finset κ) (Tτ : κ → Tube τ E) (pτ : ι → κ)
    (tθ : Finset l) (Tθ : l → Tube θ E) (pθ : κ → l)
    (s' : Finset ι) (t''τ t'τ : Finset κ) (t'θ : Finset l)
    (Y' : ι → ShadedTube δ E) (Yτ : κ → ShadedTube τ E) (Yθ : l → ShadedTube θ E)
    (lamδ lamτ lamθ Nτ Nθ : ℝ≥0) : Prop where
  /-- (a) `(𝕋|_{s'}, Y')` refines `(𝕋, Y)` by `δ ^ (2 ε')`, is uniform with constant `2`, has
  pairwise essentially distinct tubes, and has shading densities comparable to `λ_δ`.

  **Why the budget here is `δ ^ (2 ε')` and not `δ ^ ε'`.**  The fine index set produced by
  the chain is `s' = s'₁ ∩ p_τ⁻¹(s'₂)`, where `s'₁` is the fine output of the first
  application of `Kakeya.ml1Boot.exists_factorOneScaleUniform` and `s'₂` is the fine output of
  the second; the intersection is forced because the second application refines the *middle*
  family again (GWZ: "abusing notation, we will continue to refer to these refinements as …")
  and the fine family has to be pulled back along `p_τ`.  Every clause of this item that is
  *fibrewise* survives that intersection for free, by
  `Kakeya.ml1Boot.fibre_filter_mem`.  The three *global* clauses — the refinement bound
  against `s`, uniformity of `s'` as a whole, and the lower bound on `λ_δ` — do not, and are
  would be restored by one further application, at `m = 1`, of the uniform-refinement step to the
  intersection, which costs a second factor `δ ^ ε'`.  Since `ε'` is at the caller's disposal this
  costs nothing.  That step is **false** in the form it was written in — see
  `Kakeya.ml1Boot.not_exists_uniformRefinement`, so the three global clauses are stated
  relative to a shaded-uniformization interface; see the docstring of
  `Kakeya.ml1Boot.exists_uniformFactorCore`. -/
  fine_subset : s' ⊆ s
  /-- (a) `Y'` shades the same tubes as `𝕋` and is contained in `Y`. -/
  fine_shade : ∀ i ∈ s', (Y' i).toTube = (T i).toTube ∧ (Y' i).shade ⊆ (T i).shade
  /-- (a) `(𝕋|_{s'}, Y')` is a `δ ^ (2 ε')`-refinement of `(𝕋, Y)`; see `fine_subset` for why
  the budget is `2 ε'`. -/
  fine_refinement : ShadedBody.IsCRefinement s' (fun i => (Y' i).toShadedBody) s
    (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ (2 * ε'), by positivity⟩
  /-- (a) The fine family is uniform, at the constant `Kakeya.ml1Boot.uniformize.C 3`. -/
  fine_unif : Nonempty (ShadedTube.ShadedUniformTubeSet s' Y' (Tube.ssfGridLen δ)
    (uniformize.C 3))
  /-- (a) Essential distinctness is inherited by the fine family. -/
  fine_essDistinct : (s' : Set ι).Pairwise
    (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier)
  /-- (a) The fine shading densities are two-sidedly comparable to `λ_δ`. -/
  fine_dens : ∀ i ∈ s', (lamδ : ℝ≥0∞) * volume (T i).carrier ≤ volume (Y' i).shade ∧
    volume (Y' i).shade ≤ 2 * (lamδ : ℝ≥0∞) * volume (T i).carrier
  /-- (a) `λ_δ ≥ δ ^ (2 ε') λ(𝕋, Y)`. -/
  fine_fullness : (δ : ℝ≥0∞) ^ (2 * ε')
      * ShadedBody.fullness s (fun i => (T i).toShadedBody) ≤ (lamδ : ℝ≥0∞)
  /-- (b) The intermediate middle index set — the coarse output of the *first* factoring
  application — is a subset of `t_τ`. -/
  midAmbient_subset : t''τ ⊆ tτ
  /-- (b) The retained middle index set — the fine output of the *second* application — is a
  subset of the intermediate one.  Composed with `midAmbient_subset` this is
  `Kakeya.ml1Boot.IsFactorTwoScales.mid_subset`, `t'τ ⊆ tτ`. -/
  mid_subset' : t'τ ⊆ t''τ
  /-- (b) `Y_τ` shades the middle tubes. -/
  mid_tube : ∀ k ∈ t'τ, (Yτ k).toTube = Tτ k
  /-- (b) The middle family is uniform, at the constant `Kakeya.ml1Boot.uniformize.C 3`. -/
  mid_unif : Nonempty (ShadedTube.ShadedUniformTubeSet t'τ Yτ (Tube.ssfGridLen τ)
    (uniformize.C 3))
  /-- (b) The retained middle tubes are pairwise essentially distinct. -/
  mid_essDistinct : (t'τ : Set κ).Pairwise
    (fun k k' => IsEssentiallyDistinct (Tτ k).carrier (Tτ k').carrier)
  /-- (b) The middle shading densities are two-sidedly comparable to `λ_τ`. -/
  mid_dens : ∀ k ∈ t'τ, (lamτ : ℝ≥0∞) * volume (Tτ k).carrier ≤ volume (Yτ k).shade ∧
    volume (Yτ k).shade ≤ 2 * (lamτ : ℝ≥0∞) * volume (Tτ k).carrier
  /-- (b) `λ_τ ≥ C⁻¹ δ ^ ε' λ(𝕋, Y)`, at `C = factorTwoScales.C #s δ #t''τ τ`. -/
  mid_fullness : (factorTwoScales.C s.card δ t''τ.card τ : ℝ≥0∞)⁻¹ * (δ : ℝ≥0∞) ^ ε'
      * ShadedBody.fullness s (fun i => (T i).toShadedBody) ≤ (lamτ : ℝ≥0∞)
  /-- (c) The retained coarse index set is a subset of `t_θ`. -/
  coarse_subset : t'θ ⊆ tθ
  /-- (c) `Y_θ` shades the coarse tubes. -/
  coarse_tube : ∀ l' ∈ t'θ, (Yθ l').toTube = Tθ l'
  /-- (c) The coarse family is uniform, at the constant `Kakeya.ml1Boot.uniformize.C 3`. -/
  coarse_unif : Nonempty (ShadedTube.ShadedUniformTubeSet t'θ Yθ (Tube.ssfGridLen θ)
    (uniformize.C 3))
  /-- (c) The retained coarse tubes are pairwise essentially distinct. -/
  coarse_essDistinct : (t'θ : Set l).Pairwise
    (fun l₁ l₂ => IsEssentiallyDistinct (Tθ l₁).carrier (Tθ l₂).carrier)
  /-- (c) The coarse shading densities are two-sidedly comparable to `λ_θ`. -/
  coarse_dens : ∀ l' ∈ t'θ, (lamθ : ℝ≥0∞) * volume (Tθ l').carrier ≤ volume (Yθ l').shade ∧
    volume (Yθ l').shade ≤ 2 * (lamθ : ℝ≥0∞) * volume (Tθ l').carrier
  /-- (c) `λ_θ ≥ C⁻¹ δ ^ ε' λ(𝕋, Y)`, at `C = factorTwoScales.C #s δ #t''τ τ`. -/
  coarse_fullness : (factorTwoScales.C s.card δ t''τ.card τ : ℝ≥0∞)⁻¹ * (δ : ℝ≥0∞) ^ ε'
      * ShadedBody.fullness s (fun i => (T i).toShadedBody) ≤ (lamθ : ℝ≥0∞)
  /-- (d) Every retained fine index has its `τ`-parent retained. -/
  branch_fine_mapsTo : ∀ i ∈ s', pτ i ∈ t'τ
  /-- (d) Every retained middle index has its `θ`-parent retained. -/
  branch_mid_mapsTo : ∀ k ∈ t'τ, pθ k ∈ t'θ
  /-- (d) Every retained fine fibre has cardinality comparable to `N_τ`. -/
  branch_fine_card : ∀ k ∈ t'τ, (Nτ : ℝ≥0∞) ≤ ((fibre s' pτ k).card : ℝ≥0∞) ∧
    ((fibre s' pτ k).card : ℝ≥0∞) ≤ 2 * (Nτ : ℝ≥0∞)
  /-- (d) Every retained middle fibre has cardinality comparable to `N_θ`. -/
  branch_mid_card : ∀ l' ∈ t'θ, (Nθ : ℝ≥0∞) ≤ ((fibre t'τ pθ l').card : ℝ≥0∞) ∧
    ((fibre t'τ pθ l').card : ℝ≥0∞) ≤ 2 * (Nθ : ℝ≥0∞)
  /-- (e) The fine shadings are nested in the middle ones along `p_τ`. -/
  contain_fine : ∀ i ∈ s', pτ i ∈ t'τ → (Y' i).shade ⊆ (Yτ (pτ i)).shade
  /-- (e) The middle shadings are nested in the coarse ones along `p_θ`. -/
  contain_mid : ∀ k ∈ t'τ, pθ k ∈ t'θ → (Yτ k).shade ⊆ (Yθ (pθ k)).shade
  /-- (f) The Frostman constant of every fine fibre grows by at most `δ ^ (-ε')`. -/
  frostman_fine : ∀ k ∈ t'τ,
    frostmanConstIn (fibre s' pτ k) (fun i => (T i).toConvexSpaceBody)
        (Tτ k).toConvexSpaceBody
      ≤ (δ : ℝ≥0∞) ^ (-ε') * frostmanConstIn (fibre s pτ k)
          (fun i => (T i).toConvexSpaceBody) (Tτ k).toConvexSpaceBody
  /-- (f) The Frostman constant of every middle fibre grows by at most `δ ^ (-ε')`, measured
  against the fibre of the **intermediate** index set `t''τ` and not of `tτ`.

  This is the second factoring application's `Kakeya.ml1Boot.IsFactorOneScale.frostman`, and
  that application is made to `𝕋_τ|_{t''τ}`; the base of the comparison is therefore
  `fibre t''τ pθ l'`.  See the section "The intermediate middle index set `t''_τ`" of the
  docstring of this structure for why `fibre tτ pθ l'` is not available here. -/
  frostman_mid : ∀ l' ∈ t'θ,
    frostmanConstIn (fibre t'τ pθ l') (fun k => (Tτ k).toConvexSpaceBody)
        (Tθ l').toConvexSpaceBody
      ≤ (δ : ℝ≥0∞) ^ (-ε') * frostmanConstIn (fibre t''τ pθ l')
          (fun k => (Tτ k).toConvexSpaceBody) (Tθ l').toConvexSpaceBody
  /-- (g) **The triple-product bound**: for every retained `k` and `l`, the multiplicity of
  `(𝕋, Y)` is at most `C δ ^ (-ε')` times the product of the fine, middle and coarse
  multiplicities. -/
  product : ∀ k ∈ t'τ, ∀ l' ∈ t'θ,
    ShadedBody.multiplicity s (fun i => (T i).toShadedBody)
      ≤ (factorTwoScales.C s.card δ t''τ.card τ : ℝ≥0∞) * (δ : ℝ≥0∞) ^ (-ε')
        * ShadedBody.multiplicity (fibre s' pτ k) (fun i => (Y' i).toShadedBody)
        * ShadedBody.multiplicity (fibre t'τ pθ l') (fun k' => (Yτ k').toShadedBody)
        * ShadedBody.multiplicity t'θ (fun l₂ => (Yθ l₂).toShadedBody)
  /-- (h) Every retained fibre of the middle family over the coarse parent map is itself
  uniform, at the constant `Kakeya.ml1Boot.uniformize.C 3`, in the **one-sided** reading
  `Kakeya.IsFlatPrismUniform`.  This is the hypothesis
  `IsFlatPrismUniform u U (Tube.ssfGridLen τ) Cunif` of
  `Kakeya.ml1Boot.multiplicity_le_middle` at `u = fibre t'τ pθ l'`; it does not follow from
  `mid_unif`, since a parent-map fibre is an arbitrary subfamily of a uniform family.  It is
  `Kakeya.ml1Boot.IsFactorOneScale.fibreUnif` at the second application, tube scale `τ` and
  parent scale `θ`. -/
  midFibreUnif : ∀ l' ∈ t'θ,
    Nonempty (IsFlatPrismUniform (fibre t'τ pθ l') Yτ
      (Tube.ssfGridLen τ) (uniformize.C 3))

/-- (b) The retained middle index set is a subset of `t_τ`; the composite of
`Kakeya.ml1Boot.IsFactorTwoScales.mid_subset'` and
`Kakeya.ml1Boot.IsFactorTwoScales.midAmbient_subset`. -/
theorem IsFactorTwoScales.mid_subset {ι κ l : Type*} [DecidableEq κ] [DecidableEq l]
    {δ τ θ : ℝ≥0} {ε' : ℝ} {s : Finset ι} {T : ι → ShadedTube δ E}
    {tτ : Finset κ} {Tτ : κ → Tube τ E} {pτ : ι → κ}
    {tθ : Finset l} {Tθ : l → Tube θ E} {pθ : κ → l}
    {s' : Finset ι} {t''τ t'τ : Finset κ} {t'θ : Finset l}
    {Y' : ι → ShadedTube δ E} {Yτ : κ → ShadedTube τ E} {Yθ : l → ShadedTube θ E}
    {lamδ lamτ lamθ Nτ Nθ : ℝ≥0}
    (h : IsFactorTwoScales ε' s T tτ Tτ pτ tθ Tθ pθ s' t''τ t'τ t'θ Y' Yτ Yθ
      lamδ lamτ lamθ Nτ Nθ) :
    t'τ ⊆ tτ :=
  h.mid_subset'.trans h.midAmbient_subset

/-! #### Arithmetic and transport lemmas for the two-scale chain -/

/-- **A tube has positive and finite carrier volume.**

`Tube.le_volume` bounds the carrier volume of a `ρ`-tube below by
`Tube.le_volume.c n * ρ ^ (n - 1)`, which is positive as soon as `ρ` is, and the carrier is
compact, hence of finite volume.

Both halves are needed to turn a termwise shading-density lower bound into a lower bound on
`ShadedBody.fullness`, which is a ratio of two sums: see
`Kakeya.ml1Boot.le_fullness_of_dens_lower`. -/
theorem tube_volume_pos_ne_top [Nontrivial E] {ρ : ℝ≥0} (hρ : 0 < ρ) (T : Tube ρ E) :
    0 < volume T.carrier ∧ volume T.carrier ≠ ⊤ := by
  constructor
  · have hc : 0 < (_root_.Tube.le_volume.c (Module.finrank ℝ E) : ℝ≥0∞) := by
      exact ENNReal.coe_pos.mpr (_root_.Tube.le_volume.c_pos (Module.finrank ℝ E))
    have hρp : 0 < (ρ : ℝ≥0∞) ^ (Module.finrank ℝ E - 1) := by
      exact ENNReal.pow_pos (ENNReal.coe_pos.mpr hρ) (Module.finrank ℝ E - 1)
    have hpos : 0 < (_root_.Tube.le_volume.c (Module.finrank ℝ E) : ℝ≥0∞) *
        (ρ : ℝ≥0∞) ^ (Module.finrank ℝ E - 1) :=
      ENNReal.mul_pos (ne_of_gt hc) (ne_of_gt hρp)
    exact lt_of_lt_of_le hpos (by simpa using _root_.Tube.le_volume T)
  · exact T.isCompact.measure_lt_top.ne

/-- **A termwise shading-density lower bound descends to the fullness.**

If every member of a nonempty family of shaded `ρ`-tubes satisfies `|Z_k| ≥ λ |V_k|`, then
`λ ≤ λ(𝕍, Z)`: summing the termwise bound gives `λ ∑ |V_k| ≤ ∑ |Z_k|`, and the denominator
`∑ |V_k|` is positive and finite by `Kakeya.ml1Boot.tube_volume_pos_ne_top`, so the division
defining `ShadedBody.fullness` may be cleared.

A lower bound on a fullness does *not* pass to subfamilies, fullness being a ratio of two
sums, whereas a termwise bound does; that is what makes this the usable shape here.  The
two-scale chain needs `λ_{τ,1} ≤ λ(𝕋_τ|_{t''₁}, Z_{ρ,1})` for the middle family produced by
the first factoring step, and all it has about that family is the two-sided density bracket
`Kakeya.ml1Boot.IsFactorOneScale.coarse_dens`. -/
theorem le_fullness_of_dens_lower [Nontrivial E] {ρ : ℝ≥0} (hρ : 0 < ρ) {κ : Type*}
    {u : Finset κ} (hu : u.Nonempty) (W : κ → ShadedTube ρ E) {lam : ℝ≥0}
    (hdens : ∀ k ∈ u, (lam : ℝ≥0∞) * volume (W k).carrier ≤ volume (W k).shade) :
    (lam : ℝ≥0∞) ≤ (ShadedBody.fullness u (fun k => (W k).toShadedBody) : ℝ≥0∞) := by
  classical
  rw [ShadedBody.fullness_def]
  rcases hu with ⟨k₀, hk₀⟩
  have hden0 : (∑ i ∈ u, volume ((W i).toShadedBody).carrier) ≠ 0 := by
    have hsum : 0 < ∑ i ∈ u, volume ((W i).toShadedBody).carrier := by
      have hsingle : volume (W k₀).carrier ≤ ∑ i ∈ u, volume ((W i).toShadedBody).carrier := by
        simpa using Finset.single_le_sum (s := u)
          (f := fun i => volume ((W i).toShadedBody).carrier)
          (fun i hi => bot_le) hk₀
      exact lt_of_lt_of_le (by simpa using (tube_volume_pos_ne_top hρ (W k₀).toTube).1) hsingle
    exact ne_of_gt hsum
  have hdenTop : (∑ i ∈ u, volume ((W i).toShadedBody).carrier) ≠ ⊤ := by
    have hlt : (∑ i ∈ u, volume ((W i).toShadedBody).carrier) < ⊤ := by
      rw [ENNReal.sum_lt_top]
      intro i hi
      exact lt_top_iff_ne_top.mpr
        (by simpa using (tube_volume_pos_ne_top hρ (W i).toTube).2)
    exact ne_of_lt hlt
  rw [ENNReal.le_div_iff_mul_le (Or.inl hden0) (Or.inl hdenTop)]
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun k hk => by simpa using hdens k hk)

/-- **The Frostman constant depends on the family only through its members on the index set.**

`ConvexSpaceBody.frostmanConstIn` is an infimum over the predicate
`ConvexSpaceBody.IsFrostmanIn`, and `Kakeya.isFrostmanIn_of_eqOn` transports that predicate
along a pointwise equality on the index set; taking the infimum in both directions gives
equality of the constants.

The two-scale chain needs this because the second factoring application is made to the
*shaded* middle family `Z_{ρ,1}`, so its Frostman item speaks about
`(Z_{ρ,1} k).toConvexSpaceBody`, whereas `Kakeya.ml1Boot.IsFactorTwoScales.frostman_mid` is
stated at the given middle tubes `𝕋_τ`.  On the retained index set the two agree, by
`Kakeya.ml1Boot.IsFactorOneScale.coarse_tube`. -/
theorem frostmanConstIn_congr {κ : Type*} (u : Finset κ) {W W' : κ → ConvexSpaceBody E}
    (h : ∀ k ∈ u, W k = W' k) (K : ConvexSpaceBody E) :
    frostmanConstIn u W K = frostmanConstIn u W' K := by
  apply le_antisymm
  · exact frostmanConstIn_le
      (isFrostmanIn_of_eqOn (E := E) (s := u) (W := W') (W' := W)
        (fun k hk => (h k hk).symm) (K := K) (C := frostmanConstIn u W' K)
        (isFrostmanIn_frostmanConstIn u W' K))
  · exact frostmanConstIn_le
      (isFrostmanIn_of_eqOn (E := E) (s := u) (W := W) (W' := W') h
        (K := K) (C := frostmanConstIn u W K) (isFrostmanIn_frostmanConstIn u W K))

/-! #### The refutation of the fine pair

The configuration described in the docstring of `Kakeya.ml1Boot.exists_twoScaleFinePair` is
realized below, and `Kakeya.ml1Boot.not_exists_twoScaleFinePair` is the resulting refutation.
The declarations between here and it are the pieces it is assembled from: a shaded tube with a
prescribed shading, uniformity of a one-member family, the multiplicity of a one-member family,
a density constant matching a prescribed pair of volumes, a smallness clause for a positive
power of the auxiliary parameter, a one-member `Kakeya.ml1Boot.IsFactorOneScale` bundle, and
the geometry of the counterexample.
-/

/-- **A positive power of the auxiliary parameter is eventually below any positive bound.**

For `0 < b` the map `δ ↦ δ ^ b` is monotone and tends to `0`, so `δ ^ b ≤ a` holds on a
neighbourhood of `0` in `(0, ∞)` for every `a ≠ 0`: it suffices that `δ ≤ a ^ (1 / b)`, which is
a clause of `𝓝[>] 0` by `Kakeya.ml1Boot.eventually_le_nhdsGT`.  This is the smallness that the
refutation of `Kakeya.ml1Boot.exists_twoScaleFinePair` extracts, at `b = 2 ε₀`. -/
theorem eventually_rpow_le {a : ℝ≥0∞} (ha0 : a ≠ 0) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0, (δ : ℝ≥0∞) ^ b ≤ a := by
  by_cases hatop : a = ⊤
  · exact Filter.Eventually.of_forall fun δ => by
      rw [hatop]
      exact le_top
  · let c : ℝ≥0 := a.toNNReal ^ (1 / b)
    have hto : 0 < a.toNNReal := ENNReal.toNNReal_pos ha0 hatop
    have hc : 0 < c := by
      dsimp [c]
      exact NNReal.rpow_pos hto
    filter_upwards [eventually_le_nhdsGT hc] with δ hδ
    have hδc : (δ : ℝ≥0∞) ≤ (c : ℝ≥0∞) := by
      exact_mod_cast hδ
    have hc_pow : c ^ b = a.toNNReal := by
      calc
        c ^ b = (a.toNNReal ^ (1 / b)) ^ b := by rfl
        _ = a.toNNReal ^ ((1 / b) * b) := by
          rw [← NNReal.rpow_mul a.toNNReal (1 / b) b]
        _ = a.toNNReal ^ (1 : ℝ) := by
          rw [one_div_mul_cancel hb.ne']
        _ = a.toNNReal := by
          rw [NNReal.rpow_one]
    calc
      (δ : ℝ≥0∞) ^ b ≤ (c : ℝ≥0∞) ^ b :=
        ENNReal.rpow_le_rpow hδc hb.le
      _ = ((c ^ b : ℝ≥0) : ℝ≥0∞) := by
        rw [← ENNReal.coe_rpow_of_nonneg c hb.le]
      _ = ((a.toNNReal : ℝ≥0) : ℝ≥0∞) := by
        rw [hc_pow]
      _ = a := by
        rw [ENNReal.coe_toNNReal hatop]

/-! ### Selecting an essentially distinct parent family -/

/-- **A finite constant is eventually dominated by a negative power of the scale.** -/
theorem eventually_finite_const_le_rpow_neg {c : ℝ≥0∞} (hc : c ≠ ⊤) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0, c ≤ (δ : ℝ≥0∞) ^ (-a) := by
  have hinv : c⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hc
  filter_upwards [eventually_rpow_le hinv ha] with δ hδ
  have hcc : c * c⁻¹ ≤ 1 := by
    rcases eq_or_ne c 0 with rfl | hc0
    · simp
    · rw [ENNReal.mul_inv_cancel hc0 hc]
  rw [ENNReal.rpow_neg]
  refine ENNReal.le_inv_iff_mul_le.mpr ?_
  calc c * (δ : ℝ≥0∞) ^ a ≤ c * c⁻¹ := by gcongr
    _ ≤ 1 := hcc

end ml1Boot

end Kakeya

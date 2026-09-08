/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.CoarseFibre
public import Kakeya.Tube.Rescale
public import Kakeya.Tube.Dilate

/-!
# Main Lemma 1, Case (ii), Step 5a: the completed coarse fibre and the local density bound

Blueprint `subsec:ml1bootFibreCompletion`.  Step 5a of the middle-factor argument reconciles two
families that Steps 5b–5c must compare: the *retained* fine node family `t_τ`, whose fibre over a
coarse node `l` is what the factoring chain produces, and the family of *all* fine nodes lying in a
bounded enlargement of the coarse node tube `P_a(l)`, which is what the collision tests against.
The two statements of this file are the two halves of that reconciliation, and — this is the
structural point that makes them reachable at all — **both are statements about the unrefined node
families of the hierarchy**, so neither needs a retention, refinement-stability or purity
hypothesis of any kind.

* `Kakeya.ml1Boot.completedFibre` is `\widetilde t_τ(l)`, the fine nodes of `t_τ` lying inside the
  concentric rescaling `P_a(l)^{(Λ ρ_a)}`, together with
  `Kakeya.ml1Boot.fibre_subset_completedFibre`,
  `Kakeya.ml1Boot.card_completedFibreParents_le` and `Kakeya.ml1Boot.card_completedFibre_le`:
  the completion contains the parent-map fibre, its parents are `O(1)` in number, and it is
  `O(N_m)` in size.
* `Kakeya.ml1Boot.densityIn_le_of_card_neighbouringParents` is the density estimate of (5.10a)
  **with the parent count removed from it**: the parent
  count enters as a bare hypothesis `|𝒫^♮(big)| ≤ M₀` on the cardinality of
  `Kakeya.ml1Boot.neighbouringParents`, and no covering family, tube, homothety factor or
  essential-distinctness hypothesis occurs.  This is the common core of the two routes to (5.10a)
  in this development, and it is stated so that the density argument is written **once** in this
  file.
* `Kakeya.ml1Boot.densityIn_le_of_neighbouringParents` is the local density bound (5.10a): the
  density of the *unrefined* level-`b` family in any convex body inside an *arbitrary* container
  `big` is `≲ δ ^ (-ε') (θ/τ) ^ (η m) D_m`.  The
  container is a free parameter and not a concentric rescaling of a coarse node tube, which is what
  makes the bound readable at a homothety-shaped region.  It is now the instance of the core at
  `M₀ = M · C_ds`, its cardinality hypothesis discharged by
  `Kakeya.ml1Boot.card_neighbouringParents_le_of_cover`; its statement is unchanged.

Two suppliers of the parent count stand side by side here.
`Kakeya.ml1Boot.neighbouringParents` names the set
`𝒫_Λ(W) = {assign_a i : i ∈ s', T i ⊆ W^{(Λθ)}}` of `a`-nodes reached by the leaves in an
enlargement, and

* `Kakeya.ml1Boot.card_neighbouringParents_le_of_cover` is the counting half of the
  `O(1)`-neighbouring-parents bound at a **supplied covering family**;
* `Kakeya.ml1Boot.card_neighbouringParents_le_of_essDistinct` counts the same set at a
  **homothety container** `K ⊆ c · V` under the hypothesis (R1) that the coarse node tubes reached
  inside `K` are pairwise essentially distinct.  Its geometric half is
  `Kakeya.ml1Boot.node_le_dilate_of_leaf_le`: a `θ`-tube
  containing a leaf that lies in `c · V` is itself inside `Λ · V` for any `Λ ≥ c + 4`.  **(R1) has
  no supplier in this development**, so this route is conditional and is not evidence that an
  absolute parent count is available at a homothety container.

And `Kakeya.densityIn_le_sum_densityIn_of_cover` and `Kakeya.densityIn_le_densityIn_of_forall_le`
are the two generic facts about `Kakeya.densityIn` that the density core is assembled from
; they mention no tube, scale or hierarchy and so
carry no `ml1Boot` prefix.

## Two unformalized constants, replaced by explicit parameters

The blueprint displays this material with two constants that have no Lean counterpart, and the
statements below substitute an explicit parameter for each.  Neither substitution weakens
anything: each replaces a constant whose *existence* is asserted elsewhere by a parameter, so the
Lean statements are families containing the displayed ones.

* The **enlargement constant** `C₀ = C_{ml1bootEnlargement}(3)` of blueprint
  `def:ml1bootEnlargementConstant` is defined by a supremum and has no Lean definition.  The
  radius `2 C₀ θ` of the completion and the radius `3 C₀ θ` of the density region are therefore
  both written `Λ * ρ_a` for a free `Λ`; the displayed statements are the instances `Λ = 2 C₀`
  and `Λ = 3 C₀`.  The two parameters are *independent*, and the assembly that feeds the
  completion into the density bound owes the relation `Λ_completion + 1 ≤ Λ_density`; it is a
  hypothesis of neither lemma separately.
* The **neighbouring-parent count** `C_{ml1bootNeighbouringParents}(3,Λ,C_ds)` of blueprint
  `def:ml1bootNeighbouringParentsConstant` is `M(3,Λ) · C_ds`, and the finiteness of `M(3,Λ)` is a
  net construction that is not formalized.  Every statement below therefore takes
  `Kakeya.ml1Boot.IsEnlargementCover` — the existence of `M` covering tubes of the exact grid
  radius — as a *hypothesis* and states its bound with the explicit product `M * Cu`.

## Divergences from the blueprint display, recorded

* `Kakeya.ml1Boot.card_neighbouringParents_le_of_cover` is stated at an arbitrary convex
  container `K` rather than at `W^{(Λθ)}` for a `θ`-tube `W` and a `Λ ≥ 1`.  The container enters
  the proof only through the covering hypothesis, so `Λ` and `W` would be binders that name `K`
  and nothing else; the displayed statement is the instance
  `K = (W.rescale (Λ * ρ_a)).toConvexSpaceBody`.
* `Kakeya.ml1Boot.card_completedFibre_le` takes only the *upper* half
  `|t_τ[T_{θ,l'}]| ≤ Λ_load N_m` of the blueprint's two-sided load bracket.  The lower half
  `Λ_load⁻¹ N_m ≤ |t_τ[T_{θ,l'}]|` is not used, there or in this file; it is a hypothesis of the
  assembly that supplies the pair `(N_m, Λ_load)`, not of this lemma.
* `Kakeya.ml1Boot.densityIn_le_of_neighbouringParents` is stated at an arbitrary container `big`
  rather than at the blueprint's `P_a(l)^{(3 C₀ θ)}`, for the same reason as
  `Kakeya.ml1Boot.card_neighbouringParents_le_of_cover` above: `l` and `Λ` would be binders naming
  the container and nothing else.  This is not cosmetic here — it is what makes the bound available
  to a consumer whose region is a *homothety* rather than a concentric rescaling, which is the shape
  the repaired plank enlargement produces.
* `Kakeya.ml1Boot.densityIn_le_of_neighbouringParents` takes
  `StickyKakeya.IsFrostmanDividingBlock` — the `block` field of
  `Kakeya.ml1Boot.IsCaseTwoInput`, which is stated on `𝒰'` alone — in place of the whole Case (ii)
  input bundle the blueprint names.  The Case (ii) bundle's refinement, shade-mass and banding
  clauses speak about a shading this lemma never mentions.  Three of the block's seven fields are
  read: `frostman_nodes` for the Frostman factor, `coarse_lt_fine` for the grid nesting
  `P_b(assign_b i) ⊆ P_a(assign_a i)` from `a` to `b`, and `fine_le` for `assign_mem a` and for
  the hypothesis `a ≤ N` of `Kakeya.ml1Boot.card_neighbouringParents_le_of_cover`.  The remaining
  four — `exponent_lt`, `separated`, `frostman_leaves`, `frostman_lower` — are unused here and
  arrive bundled, the block being a single hypothesis at every call site.  The statement likewise
  omits the blueprint's `0 < D_m` and `1 ≤ Λ_Δ`, which fix the interpretation of the pair and are
  not used.

*Why the density bound is stated at the containment family.*  The family attached to a
neighbouring parent `l''` is `Tube.UniformTubeSet.nodesUnder b a l''` — *all* level-`b`
nodes whose node tube lies inside `P_a(l'')` — and **not** the fibre of a coarse node parent map.
The distinction is not cosmetic: `StickyKakeya.IsFrostmanDividingBlock.frostman_nodes`, the clause
that supplies the Frostman factor, is asserted at the containment family, and reading it at a
parent-map fibre would be an appeal to a statement this development does not make.  A second gain
is that no parent map occurs in that lemma at all.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory ConvexSpaceBody StickyKakeya Tube Convexity Filter Topology

namespace Kakeya

universe u

/-! ### Two generic facts about `Kakeya.densityIn`

Blueprint `lem:ml1bootDensityCoverRestrict`.  Neither statement mentions a tube, a scale, a
hierarchy or a dimension; they are here only because
`Kakeya.ml1Boot.densityIn_le_of_neighbouringParents` is made of them. -/

section GenericDensity

variable {E : Type*} [TopologicalSpace E] [ConvexSpace ℝ E] [MeasureSpace E] {ι κ : Type*}

end GenericDensity

namespace ml1Boot

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-! ### The neighbouring parents of a container, and the counting half of their `O(1)` bound -/

/-- **A finite cover of the leaves in a container by tubes of the exact grid radius**.

`M` tubes `V_1, …, V_M` of radius exactly `ρ` catch, between them, every leaf of `s'` that lies in
the container `K`.  At all four call sites below `ρ` is the coarse grid radius `ρ_a`; `K` is a
concentric enlargement `P_a(l)^{(Λ ρ_a)}` of a coarse node at
`Kakeya.ml1Boot.card_completedFibreParents_le` and `Kakeya.ml1Boot.card_completedFibre_le`, and an
arbitrary container at `Kakeya.ml1Boot.card_neighbouringParents_le_of_cover` and
`Kakeya.ml1Boot.densityIn_le_of_neighbouringParents`.

This is the named hypothesis that stands in for the unformalized quantity `M(3,Λ)` of blueprint
`def:ml1bootNeighbouringParentsConstant`.  What that definition asserts, and what remains
informal, is that `M` may be chosen independently of `θ`, of `δ` and of the container; the net
argument producing such a family is what needs `δ ≤ θ/2`, which is accordingly *not* a hypothesis
of anything below — it is needed to *produce* a cover, not to count against one.

The covering tubes are existentially quantified rather than carried as data: no consumer reads
which family it is, only that one exists and how large `M` is.

Keeping the `V q` at radius exactly `ρ` is essential and not a normalization.  The clause that
converts a cover into a node count, `Tube.UniformTubeSet.boundedOverlap`, is asserted only
at the exact grid radius. -/
structure IsEnlargementCover {ι : Type*} {δ : ℝ≥0} (s' : Finset ι) (T : ι → Tube δ E)
    (ρ : ℝ≥0) (K : ConvexSpaceBody E) (M : ℕ) : Prop where
  /-- Every leaf of `s'` inside `K` lies in one of `M` tubes of radius `ρ`. -/
  exists_cover : ∃ V : Fin M → Tube ρ E,
    ∀ i ∈ s', (T i).toConvexSpaceBody ≤ K →
      ∃ q : Fin M, (T i).toConvexSpaceBody ≤ (V q).toConvexSpaceBody

/-! ### The second supplier of a parent count: a homothety container under essential distinctness

Blueprint `subsec:ml1bootHomothetyParents`.  The two statements below are the geometric half and
the packing half of a count for `Kakeya.ml1Boot.neighbouringParents` at a container of *homothety*
shape `K ⊆ c · V`, which is the shape the repaired plank enlargement produces and which
`Kakeya.ml1Boot.card_neighbouringParents_le_of_cover` cannot be read at.  The count is conditional
on an essential-distinctness hypothesis that **has no supplier in this development**; see the
docstring of `Kakeya.ml1Boot.card_neighbouringParents_le_of_essDistinct`. -/

/-! ### Step 5a, first half: the completed coarse fibre -/

/-! ### Step 5a, second half: the local density bound (5.10a) at the unrefined family -/

end ml1Boot

end Kakeya

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factoring.FlatPrisms
public import Kakeya.DimensionThree.BoundedOverlapCount
public import Kakeya.DimensionThree.MainLemma1.Factoring

/-!
# No `ρ`-free outer-plank parent count exists under the hypotheses of GWZ Proposition 6.6(A)

The outer plank non-concentration step of `Kakeya.multiplicity_le_of_factorsThroughFlatPrisms'`
runs through a count of the coarse parent labels that own a fine leaf inside one plank-shaped
test body.  With coarse essential distinctness that count is an absolute constant
(`Kakeya.edParentCount.card_assignedParents_le_of_subset_dilate`); coarse essential distinctness
is not available to Main Lemma 1, and from `Tube.HasBoundedOverlap` alone the count is
`Co · ρ ^ (-5)` (`Kakeya.card_assignedParents_le_of_boundedOverlap`), which no ledger entry of
Main Lemma 1 can absorb.

This file settles the remaining question: **is there a `ρ`-free count — a constant, or a polylog
in `1/ρ` — available from the hypothesis package that GWZ Proposition 6.6(A) actually carries?**

The answer is **no**, and the refutation uses the *whole* package, uniformity included.

## What is new here relative to `Kakeya.not_card_assignedParents_le_const_of_boundedOverlap_of_full`

That theorem refutes the constant count under "ship's 6.6(A) package minus only its uniformity
clause": nonemptiness, containment in `B₁`, leaf-scale essential distinctness, fullness at an
arbitrary threshold, a parent family, and `Tube.HasBoundedOverlap` at the sharpest constant `1`.
The uniformity clause was the one hypothesis left untested, and it was the only remaining
candidate for a hypothesis that might bound the count.

`Kakeya.nonempty_isFlatPrismUniform_of_card_le` closes that gap, and it does so structurally
rather than by a geometric construction: **every family of at most `C` injectively indexed
`σ`-tubes is `C`-uniform**, at every grid length, via the identity hierarchy — each member is its
own node at every grid scale, the node being the member's own tube rescaled to the grid radius.
Nestedness is automatic (the assignment is the identity), the nodes are nested because the grid
radius is antitone, `Kakeya.IsFlatPrismUniformTubeSet.boundedOverlap` holds because the counted
set is a subset of the index set, and every class, being a singleton, meets both branching
brackets at `branchingN = localN = 1`.

That is the whole reason uniformity cannot rescue the count.  The uniformity constant `Cunif` of
GWZ Proposition 6.6(A) is not a dimensional constant: it is quantified with the single constraint
`Cunif ≤ σ ^ (-η')`.  So any family with at most `σ ^ (-η')` members satisfies the uniformity
clause *for free*, and `σ ^ (-η') → ∞`.  Uniformity is therefore blind to configurations of
subpolynomial cardinality — and the axial pencil, rescaled to have `σ ^ (-η')` leaves, is such a
configuration.

## The configuration

`Kakeya.rhoFreeCex` re-parametrises the repository's axial pencil
(`Kakeya.ml1Boot.essDistinctCex.leaf`, fully shaded by `Kakeya.fullLeaf`) so that its leaf count
fits under the uniformity budget:

* `cnt n = 2 ^ n` leaves;
* coarse scale `par n = (1/2) ^ (n + 10)`, so that `cnt n = (par n)⁻¹ / 2 ^ 10`;
* leaf scale `lea η n = (1/2) ^ (lexp η n)` with `lexp η n = max (2 n + 12) ⌈n / η⌉`, which makes
  the pencil's transverse spread fit the coarse radius *and* makes `cnt n ≤ (lea η n) ^ (-η)`.

Every clause of `Kakeya.IsFlatPrismFamily` holds at `Cunif = cnt n`, the parent containment holds
at dilation `1` (each leaf sits in its own rescaled parent, ship's form of the hypothesis), every
one of the `cnt n` parent labels is occupied inside the `4`-dilate of a *single* coarse tube, and
the count is therefore `cnt n = (par n)⁻¹ / 2 ^ 10`.

## The verdict

* `Kakeya.not_card_assignedParents_le_const_of_isFlatPrismFamily`: no constant bounds the count,
  at any plank comparability constant `Cw ≥ 2`.
* `Kakeya.exists_isFlatPrismFamily_rhoInv_le_card_assignedParents`: the count is at least
  `ρ⁻¹ / 2 ^ 10` on the configurations above — the sharpest lower bound available, and it
  brackets the truth with `Kakeya.card_assignedParents_le_of_boundedOverlap`'s `ρ ^ (-5)`.

So GWZ Proposition 6.6(A) *as architected* cannot be run off a `ρ`-free outer-plank count: any
sound count under its hypotheses carries a positive power of `ρ`, and the parameter architecture
of Main Lemma 1 charges every constant against
`σ ^ (-eFund)` with `eFund ≤ ε' / 512`, which no positive power of `ρ` fits.  Closing 6.6(A)
requires a hypothesis strictly outside the present package, not a sharper estimate inside it.

## Leaf-scale essential distinctness does not help

The refutation keeps leaf-scale essential distinctness throughout — it is the `essDistinct` field
of `Kakeya.IsFlatPrismFamily` and the pencil satisfies it
(`Kakeya.ml1Boot.essDistinctCex.isEssentiallyDistinct_leaf`, the leaves being pairwise disjoint).
So the leaf-scale hypothesis that GWZ do supply (the uniformity definitions: essential distinctness
"is required and supplied at the leaf scale `δ`, and never at the parent scale") is present in
every counterexample here and does not bound the parent count.  The asymmetry with
`Kakeya.flatPrismOccupiedParents_le_of_boundedOverlap`, which *is* constant, is entirely the
scale hypothesis `bSmall ≤ b ≤ D · ρ` of that lemma: it forces `1 ≤ Ctest · ρ`, i.e. it runs only
where the coarse scale is bounded below by a constant.  The outer plank step runs at arbitrary
`σ ≤ ρ ≤ 1` and has no such lower bound on `ρ`.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace Kakeya

section Uniformity

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]


end Uniformity

/-! ### The re-parametrised axial pencil

The repository's pencil `Kakeya.ml1Boot.essDistinctCex.leaf` is run at the scales
`σ = 2 ^ (-8n)`, `ρ = 2 ^ (-(2n+9))`, `M = 2 ^ (2n+1)`, which makes `M ≍ σ ^ (-1/4)`: too many
leaves to fit under a uniformity budget `Cunif ≤ σ ^ (-η')` with small `η'`.  The scales below
keep `M ≍ ρ ^ (-1)` — the property that makes the count large — while pushing `σ` down until
`M ≤ σ ^ (-η)`. -/

namespace rhoFreeCex

/-- The number of leaves, equivalently of occupied coarse parent labels, at stage `n`. -/
def cnt (n : ℕ) : ℕ := 2 ^ n

/-- The coarse scale at stage `n`.  It is `2 ^ (-10) / cnt n`, so the count is `≍ ρ⁻¹`. -/
def par (n : ℕ) : ℝ≥0 := (1 / 2) ^ (n + 10)


end rhoFreeCex


/-! ### The plank factorization hypothesis on a one-member fibre

GWZ Proposition 6.6(A) also asks, for every coarse label, a `2`-factorization of that label's
fibre by `a × b × 1` planks.  In the configuration below every fibre is a *singleton*, and a
`σ`-tube is a `σ × σ × 1` plank, so the hypothesis is satisfiable at `a = b = σ` and any
comparability constant `Cw ≥ 2`.  Nothing about the count changes; this section only removes the
last hypothesis of the package from the list of things the refutation does not carry. -/

section Singleton

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]


end Singleton


end Kakeya

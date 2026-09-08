/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Factoring
public import Kakeya.MultiScaleFac
public import Kakeya.Asymptotics
public import Kakeya.DimensionThree.MainLemma1.Setup

/-!
# Main Lemma 1, Case (ii): the containment-to-fibre conversion at the coarse parent

Blueprint `note:ml1bootRawMidContainment`.  Alternative (ii) of
`StickyKakeya.dividingScalesFrostman` asserts its middle Frostman bound at the *containment*
family `Tube.UniformTubeSet.nodesIn b (tube a l)` — all level-`b` nodes lying inside the
coarse node — whereas `Kakeya.ml1Boot.IsCaseTwoData.mid`, and behind it
`Kakeya.ml1Boot.exists_factorTwoScales`, asks for the parent-map fibre of `ϖ_{b→a}`, which is in
general a proper subfamily: the `a`-nodes are not disjoint, so a fine node may lie inside several
coarse nodes while `ϖ_{b→a}` is a function and names exactly one of them.

A Frostman constant is a *ratio* — `ConvexSpaceBody.IsFrostmanIn` bounds `densityIn t W K'` by
`C * densityIn t W K` — so passing to a subfamily shrinks numerator and denominator alike and the
bound does **not** transport.  What does transport is a *share*, through
`ConvexSpaceBody.frostmanConstIn_subfamily_le`, and the four declarations of this file produce
that share and cash it in:

* `Kakeya.ml1Boot.branching_mul_card_nodesIn_le` counts the `b`-nodes inside a coarse node;
* `Kakeya.ml1Boot.branching_le_mul_card_coarseFibre` counts those in a coarse parent fibre;
* `Kakeya.ml1Boot.card_nodesIn_le_card_coarseFibre` combines the two into the share `Cu ⁻⁵`;
* `Kakeya.ml1Boot.frostmanConstIn_coarseFibre_le` is the resulting Frostman transfer.

The exponent `5` is what this route costs and is not claimed optimal: nothing downstream reads
its value, only that it is a constant fixed before `δ`.  The `δ`-bookkeeping that turns it into a
factor `δ ^ (-ε')` is `Kakeya.ml1Boot.caseTwoRawMidFibre`, the last declaration of this file,
which is step 0 of `Kakeya.ml1Boot.exists_caseTwoDataRepair`.

Also here is `Kakeya.ml1Boot.hasBoundedOverlap_nodes`, the one-line bridge saying that the node
parent family of a hierarchy satisfies `Kakeya.ml1Boot.HasBoundedOverlap`.  It belongs with the
node bookkeeping and it is what discharges, at every Case (ii) call site, the bounded-overlap
hypothesis without which `Kakeya.ml1Boot.exists_essDistinct_parentFamily` is false.

*Why this is a separate file.*  Every declaration here is about the *nodes* of a hierarchy: none
mentions a shading, a refinement of the leaves, or the Case (ii) conclusion bundles.  They are
the counting layer that `Kakeya/DimensionThree/MainLemma1.lean` cites, and keeping them out of
`Kakeya/DimensionThree/MainLemma1/NodeFamilies.lean` keeps that file inside its size budget.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ConvexSpaceBody StickyKakeya Tube Filter Topology

namespace Kakeya

universe u

namespace ml1Boot

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- **The coarse node parent family, as a situation** (blueprint
`lem:ml1bootParentFamiliesFromNodesCoarse`, together with its standing hypothesis).

This bundles the data the containment-to-fibre conversion runs in, and nothing else: a block
`a ≤ b ≤ N` of the hierarchy, the standing hypothesis that every `b`-node carries a leaf, the
induced map `ϖ_{b→a}` on nodes together with the identity `ϖ (assign b i) = assign a i` that
characterizes it there, and the parent-family property of the coarse nodes over the fine ones.

It is exactly the output of `Kakeya.ml1Boot.exists_nodeParentFamilies_coarse` together with the
two hypotheses that lemma itself takes, so a caller that has applied that lemma has this bundle
for free.  It is bundled rather than repeated because the three counting lemmas below each
consume the whole of it and none of them is meaningful without it: the identity `assign_comp` is
what reads a coarse class as the disjoint union of the fine classes over the fibre, and
`nodes_carry_leaf` is what makes the branching number at the index `b` strictly positive, which
is what licenses the division that produces the share. -/
structure IsCoarseNodeParents {ι : Type*} {δ : ℝ≥0} {s' : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {Cu : ℝ≥0} (𝒰' : UniformTubeSet s' T N Cu) (a b : ℕ) (pθ : ι → ι) : Prop where
  /-- The coarse index is at or below the fine one. -/
  le_index : a ≤ b
  /-- …and the fine one is a grid index. -/
  le_gridLen : b ≤ N
  /-- Every `b`-node carries a leaf.  `Tube.UniformTubeSet` nowhere requires this, and
  without it the induced map on nodes is undefined at the empty nodes and
  `Kakeya.ml1Boot.card_nodesIn_le_card_coarseFibre` is false. -/
  nodes_carry_leaf : ∀ k ∈ 𝒰'.cover.indexSet b, ∃ i ∈ s', 𝒰'.cover.assign b i = k
  /-- The identity characterizing `ϖ_{b→a}` on the nodes that carry a leaf.  It is this, and not
  any particular construction of `pθ`, that the counting rests on. -/
  assign_comp : ∀ i ∈ s', pθ (𝒰'.cover.assign b i) = 𝒰'.cover.assign a i
  /-- The coarse nodes form a parent family for the fine ones along `pθ`. -/
  parent : IsParentFamily (𝒰'.cover.indexSet b) (𝒰'.cover.tube b)
    (𝒰'.cover.indexSet a) (𝒰'.cover.tube a) pθ

/-- **Fibrewise empty-or-share**.

Let `pθ` be the coarse node parent map, `sb` the full fine node index set (`𝒰'.cover.indexSet b`),
`sa` the coarse one (`𝒰'.cover.indexSet a`), and `t ⊆ sb` a retained subfamily.  We say `t` is
*fibrewise empty-or-share at `κ`* over `pθ` if over every coarse node `l ∈ sa` either the retained
fibre `Kakeya.ml1Boot.fibre t pθ l` is empty, or it carries at least a `κ`-share of the full fibre
`Kakeya.ml1Boot.fibre sb pθ l`.

That is: the selection may lose a coarse fibre *entirely*, but any fibre it keeps at all it keeps a
`κ`-share of.  Losing a fibre entirely is harmless downstream, the empty family having Frostman
constant `0`; keeping all but a concentrated part of one is not, and that is exactly what the
disjunction excludes.  This dichotomy — and not a global cardinality share — is what
`Kakeya.ml1Boot.frostmanConstIn_retainedFibre_le` consumes.

The subset relation `t ⊆ sb` is *not* part of this definition: it is data the consumers carry
separately, since the definition is meaningful (and the empty branch true) without it. -/
def IsFibrewiseEmptyOrShare {ι : Type*} [DecidableEq ι] (sb sa t : Finset ι) (pθ : ι → ι)
    (κ : ℝ≥0∞) : Prop :=
  ∀ l ∈ sa,
    fibre t pθ l = ∅ ∨
      κ * ((fibre sb pθ l).card : ℝ≥0∞) ≤ ((fibre t pθ l).card : ℝ≥0∞)

end ml1Boot

end Kakeya

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.FibreCommon
public import Kakeya.Sticky
public import Kakeya.Uniform
public import Kakeya.Thickness.ConvexSpaceBody
public import Kakeya.ChainUniform
public import Mathlib.Tactic.Linarith.NNRealPreprocessor

/-!
# Bridging the node reading to the leaf reading

**This file is scaffolding.**  It exists so that the migration to
`Tube.UniformTubeSet` can proceed one downstream file at a time instead of as a single
atomic rewrite, and it is to be deleted once no file references it.

Two bridges are needed, and only two.

* The node class against the leaf-anchored fibre.  These are the two objects the two developments
  compute with: `coverClass s (assign k) v` is the set of leaves *assigned to* the node `v`, whereas
  `fibreIndex s T δ ρ i₀` is the set of leaves inside the `ρ`-thickening of the leaf `T_{i₀}`.  Each
  sits inside the other up to a bounded dilation of the anchor, which is what
  `Tube.rescale_le_of_le` provides with its factor `4` — the reason the grid is taken
  `16`-separated.
* The nodes under a node against the gap fibre, the same comparison one level up.

Every downstream transfer of a Frostman constant then goes through
`Kakeya.MultiScaleFac.frostmanConstant_mono_anchor`, which pays a volume ratio, and through the
cardinality comparison of the two index sets, which the bounded-overlap clause pays for.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Real Metric

universe u
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya
open scoped NNReal

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
  {ι : Type*}

/-! ### Node classes against leaf-anchored fibres -/

/-! ### The nodes under a node against the gap fibre -/

/-! ### From leaf-anchored fibre bounds to node-anchored class bounds

This is the substance of the translation.  A bound of the shape "every leaf-anchored fibre at the
grid scale `ρ_k` is `B`-Frostman in its anchor" becomes "every class of a node at grid index `k` is
`B'`-Frostman in that node", with `B'` larger than `B` by a dimensional constant and a power of the
uniformity constant.

The route does *not* pass through the fibre at the inflated scale `4ρ_k`, which would put the
hypothesis outside the range `ρ ≤ 1` at the coarsest grid index.  Instead the class, which does sit
inside the `4ρ_k`-fibre of any of its members, is covered by boundedly many *exact-scale* fibres
(`Kakeya.MultiScaleFac.exists_gapFibre_cover_of_ratio`), and `Kakeya.maxDensity` is subadditive over
such a covering.  So the hypothesis is only ever used at grid scales. -/

/-! ### The bottom grid scale, and the translation at every grid index -/

/-! ### Thickening a test body

Alternatives (ii)-2 and (ii)-3 of Lemma 7.7(A) speak about the family of *nodes* at the fine
grid index, whereas the leaf-anchored form speaks about the leaves thickened to that grid
radius.  Passing between the two moves each member by at most the grid radius, so a test body
for one family becomes, for the other, that body thickened by the grid radius.  That thickening
is affordable exactly because the test body already contains a tube of that radius: its every
affine thickness is then at least the radius, and
`Kakeya.Metric.volume_cthickening_le_prod` bounds the thickened volume by `4 ^ n` times the
product of the thicknesses, which `Convex.ethickness_prod_le_volume` returns to the volume. -/

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E] in
/-- `Metric.ethickness.scale` is monotone, being an infimum of the monotone `Metric.ethickness`. -/
theorem ethickness_scale_mono {X Y : Set E} (h : X ⊆ Y) :
    Metric.ethickness.scale ℝ X ≤ Metric.ethickness.scale ℝ Y :=
  Finset.le_inf fun i hi => (Finset.inf_le hi).trans (Metric.ethickness_monotone h i)


/-- The `ρ`-thickening of a convex body, as a convex body. -/
noncomputable def thickenBody (K : ConvexSpaceBody E) (ρ : ℝ≥0) : ConvexSpaceBody E where
  carrier := Metric.cthickening (ρ : ℝ) K.carrier
  convex' := (((Convexity.IsConvexSet.convex K.convex').cthickening _)).isConvexSet
  isCompact' := K.isCompact.cthickening
  nonempty' := K.nonempty.mono (Metric.self_subset_cthickening K.carrier)

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem thickenBody_carrier (K : ConvexSpaceBody E) (ρ : ℝ≥0) :
    (thickenBody K ρ).carrier = Metric.cthickening (ρ : ℝ) K.carrier := rfl


/-! ### Iterated nesting of the hierarchy -/


/-! ### Counting the nodes under a node -/


/-! ### Generic density bounds by cardinality -/


/-! ### The node family under a node, against its density in that node -/

/-! ### The node family at a fine index, against the thickened leaf family

Alternative (ii)-2 compares the family of nodes at the fine index `b` sitting under a node at the
coarse index `a` with the leaves thickened to `ρ_b`.  The two families are related by the assignment
`i ↦ a_b(i)`, whose fibres are the classes; a node therefore stands for about `N_{ρ_b}` leaves, and
that branching factor appears on both sides of the comparison and cancels.  The `maxDensity` side
also moves each member by at most `ρ_b`, which is why the test body has to be thickened. -/


/-! ### Alternative (ii)-2, translated -/


/-! ### The majority set, translated -/


/-! ### Aligning the nodes of a fibre with a dilated container

Alternative (ii)-3 is a *lower* bound, so its container has to be the one the leaf-anchored bound
already reaches, not the node itself.  The two are related by the containments recorded here.  Note
that neither of the two primitives the container chase seems to ask for is actually new.  A triangle
inequality turning `\operatorname{cth}_r(P)` into `P^{(r+\rho)}` is `Tube.cthickening_carrier`,
which gives it as an *equality*; and absorbing a containment into one dilation is
`Tube.rescale_le_rescale_of_body_le` (`Kakeya/MultiScaleFac/Branching.lean`), which even lets the
target radius be any `θ ≥ ρ + r` and so telescopes the whole chase into two steps. -/


/-! ### The reverse transports, for alternative (ii)-3

The forward transports (`densityIn_nodesUnder_mul_branchingN_le`,
`densityIn_fibre_thick_le_mul_densityIn_nodesUnder`) turn a *fibre* bound into a *node* bound, which
is what an upper bound needs.  Alternative (ii)-3 needs the opposite: a lower bound on a node
Frostman constant from a lower bound on a fibre one, which means bounding the fibre constant
*above* by the node constant.  So both transports are needed with the inequalities reversed, and
the branching number `N_{ρ_b}` cancels between them exactly as before. -/


/-- **The grid never drops below the leaf scale.**  For `k ≤ N` the grid scale `ρ_k` is at least
`δ = ρ_N`. -/
private theorem delta_le_gridScale {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {N k : ℕ}
    (hN : 0 < N) (hk : k ≤ N) : δ ≤ gridScale δ N k := by --
  have h := gridScale_antitone hδ hδ1 N hk
  rwa [gridScale_self δ hN] at h


end MultiScaleFac

end Kakeya

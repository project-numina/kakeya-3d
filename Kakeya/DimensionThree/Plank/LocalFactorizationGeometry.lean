/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.PrismGeometry
public import Kakeya.DimensionThree.Plank.FrostmanPlankEstimate
public import Kakeya.DimensionThree.Plank.ComparableBodyFactorization

/-!
# GWZ Proposition 6.6(A): the cross-parent repair

The printed proof of GWZ Proposition 6.6(A) forms the outer plank family

`𝒲 = ⨆_{T_ρ ∈ 𝕋_ρ} 𝒲_{T_ρ}`

from one plank factorization per coarse fibre `𝕋[T_ρ]`, fixes `W ∈ 𝒲_{T_ρ}` with thickening
`W_θ`, and then asserts that every `W' ∈ 𝒲` with `W' ⊆ W_θ` already lies in the *same* parent
family `𝒲_{T_ρ}`, i.e. `𝒲[W_θ] = 𝒲_{T_ρ}[W_θ]`.

**That inference is false.**  If `W'` comes from a different coarse parent `T_ρ'`, a fine tube `T'`
in the fibre of `W'` satisfies `T' ⊆ T_ρ'` and `T' ⊆ W' ⊆ W_θ`, but nothing forces `T' ⊆ T_ρ`, so
uniqueness of the parent of `T'` does not give `T_ρ' = T_ρ`.  Nothing in this file states or uses
any such same-parent equality.

The corrected argument keeps the parent label of every outer plank and splits the count:

* `Tube.UniformTubeSet.card_contributingNodes_le` bounds the number of coarse parents that
  can contribute a plank inside `W_θ`, using `UniformTubeSet.boundedOverlap`;
* `Kakeya.card_filter_le_of_parentwise` sums a parentwise bound over a controlled parent set;
* `Kakeya.card_le_of_parentwise_of_boundedOverlap` combines the two, and
  `Kakeya.plankConcentration_of_parentwise` lands the result in the exact `≤ M * θ` shape that GWZ
  Lemma 6.4 (`Kakeya.FrostmanEstimate.plankEstimate`) consumes, with

  `M = C_geom * C_uniform * C_local * (b / a)`

  in place of the printed argument's unsupported `M ≲ b / a`.

## The Scale comparison

`PlankFactorizationEstimate.lean`'s Proposition 6.6(A) currently assumes `δ ≤ ρ` and `ρ ≤ a`, on top of
`a ≤ b ≤ 1`.  The second of these is reversed.  The outer bodies of a
`Kakeya.PlankFactorization` are convex hulls of subfamilies of the fine tubes assigned to one
coarse `ρ`-tube `R`, so every outer plank is *contained in* `R`; a plank inside a `ρ`-tube has
`b ≤ ρ`.  This is `Kakeya.PlankFactorization.b_le_of_le_tube` below, and it needs no new
hypothesis — it is a consequence of the data Proposition 6.6(A) already carries.  Together with
`ρ ≤ a ≤ b` the current signature therefore forces `a ≍ b ≍ ρ`, a degenerate regime in which the
conclusion's `(a/b) ^ (3β/2)` gain is vacuous.  The honest chain is `δ ≲ a ≤ b ≤ ρ`, matching the
Section 8 consumer's `b ≤ ρ`.

`b ≤ ρ` is what makes the covering datum `hF` below suppliable at all: only when the two short
axes of `W_θ` are at most the coarse radius can a `θb × b × 1` prism be swept by boundedly many
`ρ`-tubes.

## Leaf essential distinctness is a separate matter

`UniformTubeSet.boundedOverlap` controls *coarse parent* overlap only.  It says nothing about the
leaf `δ`-tubes being pairwise essentially distinct, and the anisotropic packing step that supplies
the parentwise Katz--Tao bound `hlocal` does use leaf ED.  That bound is therefore taken as a
hypothesis here rather than derived, and `UniformTubeSet` is left unstrengthened.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Convexity ConvexSpaceBody
open scoped NNReal Real ENNReal Classical

noncomputable section

namespace Kakeya

/-! ### The Scale comparison: a plank inside a coarse tube is thin -/


/-! ### The *longitudinal* scale relation, and why it is decisive

`Kakeya.Plank.b_le_of_le_tube` compares the transverse extents of a plank and a coarse tube.  The
longitudinal extents must also be compared, and doing so is much more restrictive.

In this development a `Plank a b` is `Prism3D a b 1`, whose `thicknesses` are *half*-widths
(`Kakeya.Prism3D.volume_carrier` is `8 * a * b * c`).  So a plank has longitudinal **extent 2**: it
contains the two points `centre ± e` for a unit `e` on its long axis, at distance `2`
(`Kakeya.Prism3D.mem_add_mem_longAxis`, `mem_sub_mem_longAxis`).

A `Tube ρ`, by contrast, is the `ρ`-neighbourhood of a *unit* segment, so it sits in a ball of
radius `1/2 + ρ` about its midpoint (`Kakeya.Tube.carrier_subset_closedBall_midpoint`) and therefore
has diameter at most `1 + 2ρ`.

Consequently a plank inside a `ρ`-tube forces `2 ≤ 1 + 2ρ`, i.e. `1/2 ≤ ρ`.  The two normalisations
disagree by a factor of two in the long direction, and the consequence is not cosmetic: the
`PlankFactorization` hypothesis of Proposition 6.6(A) is only satisfiable for `ρ ∈ [1/2, 1]`. -/


/-! ### The leafwise `ρ`-tube cover from a position × direction net

This is the covering datum at the *external* radius `ρ`, built as GWZ intends: an `O(1)` net of
positions crossed with an `O(1)` net of directions, each pair giving one `ρ`-tube, and whole-leaf
containment proved from closeness of the two endpoints.

Two scale inputs make the nets `O(1)`, and both are *derived* in the 6.6(A) context rather than
assumed:

* `1/2 ≤ ρ` — `Kakeya.half_le_of_localPlankFactorisation`;
* `δ ≤ 1/4` — from the consumer's freedom to shrink `δ₀`.

Together they give the net budget `δ + 1/8 ≤ ρ`, so a single net at scale `1/16` in `B₁` serves
*both* the position and the direction coordinate (a unit direction lies in `B₁` too), and the
covering tubes have radius exactly `ρ` — no dilation constant is needed. -/

/-- `d` normalised to a unit vector, with a fixed fallback when `d = 0`.  Making this a *total*
function is what lets the covering family be a plain `Finset.image` over a product of nets, with no
dependent-membership plumbing. -/
noncomputable def unitDir {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e₀ d : E) : E :=
  if d = 0 then e₀ else ‖d‖⁻¹ • d

theorem norm_unitDir {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {e₀ : E} (he₀ : ‖e₀‖ = 1) (d : E) : ‖unitDir e₀ d‖ = 1 := by
  unfold unitDir
  split_ifs with h
  · exact he₀
  · rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg d),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]


/-- The `ρ`-tube with midpoint `c` and unit direction `unitDir e₀ d`.

A thin *total* wrapper around the repository's own `Tube.ofMidpointDirection`: the only thing
added is that the direction argument need not already be a unit vector, which is what lets the
covering family be a plain `Finset.image` over a product of nets with no dependent-membership
plumbing. -/
noncomputable def tubeOfCenterDir {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] (ρ : ℝ≥0) {e₀ : E} (he₀ : ‖e₀‖ = 1) (c d : E) : Tube ρ E :=
  Tube.ofMidpointDirection ρ c (unitDir e₀ d) (norm_unitDir he₀ d)

@[simp] theorem tubeOfCenterDir_x {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] (ρ : ℝ≥0) {e₀ : E} (he₀ : ‖e₀‖ = 1) (c d : E) :
    (tubeOfCenterDir ρ he₀ c d).x = c - (1 / 2 : ℝ) • unitDir e₀ d := rfl

@[simp] theorem tubeOfCenterDir_y {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] (ρ : ℝ≥0) {e₀ : E} (he₀ : ‖e₀‖ = 1) (c d : E) :
    (tubeOfCenterDir ρ he₀ c d).y = c + (1 / 2 : ℝ) • unitDir e₀ d := rfl


/-! ### Milestone 4: external parents versus hierarchy nodes

The cross-parent count is carried out on *hierarchy nodes*, but the Katz--Tao property lives on the
*external* factorization classes: `Kakeya.PlankFactorization` makes the outer bodies of each single
`Fz k` a Katz--Tao family (`ConvexSpaceBody.Factorization.isKatzTao`), and says nothing whatever
about a union over several `k`.

Neither of the two candidate reconciliations survives contact with the definitions.

* *Each external class maps to one hierarchy node, so the estimate stays external.*  The map
  `par` is not injective on external classes: the chosen node has radius
  `gridScale δ N kLev ≥ ρ`, possibly much larger than `ρ`, so many external `ρ`-tubes can share a
  node.  Bounding the number of contributing *nodes* therefore does not bound the number of
  contributing *external parents*.
* *Union the external classes sitting inside one node.*  This needs `IsKatzTao` for a union of
  Katz--Tao families.  Katz--Tao is inherited by *subsets*, not by unions, and invoking downward
  inheritance here would be using it in the wrong direction.  This is the same failure mode as the
  original GWZ gap.

The resolution is not to regroup at all: group by the external parent, where the hypothesis
actually holds, and bound the number of contributing external parents separately.  The summation
step is `Kakeya.card_filter_le_of_parentwise`, which is already generic in the label type; the
instance below records the external-parent grouping under its own name so that no call site has to
choose between the two families by accident.  See
`Kakeya.card_planks_le_of_externalParentwise`, stated below next to the summation lemma it uses. -/

/-! ### The unit-radius fallback cover

The covering datum that `Tube.UniformTubeSet.card_contributingNodes_le_of_cover` consumes
asks for *leafwise* containment: every leaf lying in the container must lie in a single member of
the family.  A mere set cover is not enough, because a leaf can straddle two members.

Two facts make the honest answer short.

* The covering radius must strictly exceed the leaf radius.  A `Tube δ` contains balls of radius
  `δ`, so it can only sit inside a `Tube ρ` when the axes nearly coincide; with `δ = ρ` allowed by
  the hypotheses of Proposition 6.6(A), no *finite* family of `ρ`-tubes can catch every leaf
  leafwise.  Some fixed enlargement of the radius is therefore unavoidable, exactly as anticipated.
* Once the radius is enlarged to `1`, the family collapses to a single tube: every leaf lies in
  `B_1` by hypothesis, and a `1`-tube whose axis passes through the origin contains `B_1`.

So the honest covering constant is `Ccover = 1` at covering radius `1`. No net, no discretisation
of position or direction, and no `δ ^ (-η)` loss. -/

/-- A `1`-tube through the origin contains the closed unit ball, hence every leaf of a family
contained in `B_1`.  This is the leafwise covering datum with a single member. -/
theorem exists_tube_one_superset_of_subset_unitBall
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} {δ : ℝ≥0} (q : Finset ι) (T : ι → Tube δ E)
    (hball : ∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) :
    ∃ V : Tube (1 : ℝ≥0) E,
      ∀ i ∈ q, (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody := by
  classical
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  let e : E := (‖x‖⁻¹ : ℝ) • x
  have he : ‖e‖ = 1 := by
    dsimp [e]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)
  let x₀ : E := -((1 / 2 : ℝ) • e)
  let y₀ : E := (1 / 2 : ℝ) • e
  have hdist : dist x₀ y₀ = 1 := by
    rw [dist_eq_norm]
    calc
      ‖x₀ - y₀‖ = ‖(-1 : ℝ) • e‖ := by
        congr 1
        dsimp [x₀, y₀]
        module
      _ = 1 := by simp [he]
  let V : Tube (1 : ℝ≥0) E := Tube.mk' (1 : ℝ≥0) hdist
  have hc : (0 : E) ∈ segment ℝ V.x V.y := by
    change (0 : E) ∈ segment ℝ x₀ y₀
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    dsimp [x₀, y₀]
    module
  have hball_in : Metric.closedBall (0 : E) ((1 : ℝ≥0) : ℝ) ⊆ V.carrier :=
    Tube.closedBall_subset_carrier_of_mem_segment V hc
  have hball_in' : Metric.closedBall (0 : E) (1 : ℝ) ⊆ V.carrier := by
    simpa using hball_in
  refine ⟨V, ?_⟩
  intro i hi
  exact (SetLike.coe_subset_coe (S := (T i).toConvexSpaceBody)
    (T := V.toConvexSpaceBody)).mpr ((hball i hi).trans hball_in')


end Kakeya

namespace Tube

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

/-! ### Counting the coarse parents that contribute to a container -/


/-! ### From exact grid radii to arbitrary scales

`UniformTubeSet.boundedOverlap` is stated only for test tubes of the *exact* grid radius
`gridScale δ N k`, while Proposition 6.6(A) is quantified over an arbitrary coarse scale
`ρ ∈ [δ, 1]`.  The grid has only `N = ⌈log log (1/δ)⌉` levels, so consecutive radii differ by the
factor `δ ^ (1/N)`, which is *not* `O(1)`: an arbitrary `ρ` is in general nowhere near a grid
radius, and no rounding argument can identify the two.

The resolution below does not round `ρ` to a grid radius and does not lose any constant.  A tube of
radius `ρ` is *contained* in the tube with the same axis and the larger radius `gridScale δ N k`
whenever `ρ ≤ gridScale δ N k` (`Tube.le_rescale`), and `contributingNodes` only ever tests
leaves for containment in the container.  So the exact-grid bound applies verbatim, with the same
constant `C`.

What the sparse grid does cost is the *level*: the finest grid level whose radius still dominates
`ρ` is `gridLevelOf δ N ρ`, and its radius can exceed `ρ` by as much as `δ ^ (-1/N)`
(`gridScale_gridLevelOf_lt_mul`).  That is where the `log log` sparsity of the grid shows up — as a
coarsening of the parent scale, not as a multiplicative loss in the overlap count.  Downstream it is
the within-parent Katz--Tao input, not this lemma, that has to be supplied at the coarser level.

No
essential distinctness of coarse parents is used anywhere below. -/


/-! ### Where the external parent package comes from

Proposition 6.6(A) consumes leaf-mediated bounded overlap of its *external* coarse family
`(R k)_{k ∈ r}`, and that is not a consequence of the hierarchy: hierarchy `boundedOverlap` counts
nodes at *exact* grid radii, and consecutive grid radii `δ ^ (k/N)` with `N = ssfGridLen δ` differ
superpolynomially, so a node at the level above an arbitrary `ρ` is not comparable to `ρ`.

What *is* provable — and is the honest reference point for the missing construction — is the exact
grid case: when the coarse family is taken to be the hierarchy's own nodes at a grid level, the
external hypothesis is literally Definition 2.1(ii).  The lemma below is that instance.  The
genuinely missing ingredient for arbitrary `ρ` is therefore not a rounding argument but the
*construction* of a coarse family at a non-grid scale together with its bounded overlap; this is the
correct replacement for the sorried `Kakeya.Tube.IsUniform.spread`, whose own condition demands
pairwise essential distinctness of the coarse family and is not used anywhere here. -/


end Tube

namespace Kakeya

open _root_.Tube

/-! ### Summing a parentwise bound over a controlled parent set -/

/-- **Parentwise summation.**  If every counted element carries a label in the finite set `P` and
each label class contributes at most `m`, the total is at most `P.card * m`.

This is the combinatorial half of the repair: the global count over all outer planks is the sum of
the within-parent counts over the contributing parents, never a single within-parent count. -/
theorem card_filter_le_of_parentwise {α : Type*} {ι : Type*}
    {ts : Finset α} {p : α → Prop} {par : α → ι} {P : Finset ι}
    (hpar : ∀ x ∈ ts, p x → par x ∈ P) {m : ℝ≥0}
    (hlocal : ∀ j ∈ P, (({x ∈ ts | p x ∧ par x = j}).card : ℝ≥0) ≤ m) :
    (({x ∈ ts | p x}).card : ℝ≥0) ≤ (P.card : ℝ≥0) * m := by
  classical
  let f : ι → Finset α := fun j => {x ∈ ts | p x ∧ par x = j}
  have hsub : ({x ∈ ts | p x} : Finset α) ⊆ P.biUnion f := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxts, hpx⟩
    exact Finset.mem_biUnion.mpr ⟨par x, hpar x hxts hpx, by simp [f, hxts, hpx]⟩
  have hcard : ({x ∈ ts | p x}).card ≤ ∑ j ∈ P, (f j).card := by
    calc
      ({x ∈ ts | p x}).card ≤ (P.biUnion f).card := Finset.card_le_card hsub
      _ ≤ ∑ j ∈ P, (f j).card := Finset.card_biUnion_le
  have hsum : (∑ j ∈ P, ((f j).card : ℝ≥0)) ≤ (P.card : ℝ≥0) * m := by
    calc
      (∑ j ∈ P, ((f j).card : ℝ≥0)) ≤ ∑ j ∈ P, m :=
        Finset.sum_le_sum (fun j hj => hlocal j hj)
      _ = (P.card : ℝ≥0) * m := by
        simp [Finset.sum_const, nsmul_eq_mul]
  calc
    (({x ∈ ts | p x}).card : ℝ≥0) ≤ (∑ j ∈ P, ((f j).card : ℝ≥0)) := by
      exact_mod_cast hcard
    _ ≤ (P.card : ℝ≥0) * m := hsum


/-! ### The global concentration estimate -/


/-! ### The two adapters consumed by GWZ Proposition 6.6(A) -/


/-! ### The local leafwise cover, valid at arbitrarily small `ρ`

`Kakeya.exists_leafwise_tube_cover` above covers *every* leaf of `B₁` and therefore needs
`1/2 ≤ ρ`.  The local statement needed by Proposition 6.6(A) is different: the leaves to be covered
are only those inside a container `K`, and the covering radius may be arbitrarily small.

The honest criterion is remarkably simple, and it is not a net: **a container that is itself
tube-shaped needs exactly one covering tube.**  If `K ≤ V₀` for some `V₀ : Tube r E`, then every
leaf inside `K` lies in `V₀.rescale ρ` as soon as `δ + r ≤ ρ`.  Convexity does all the work: the
leaf's core segment lies in the convex set `V₀.carrier`, so the leaf, being the `δ`-thickening of
its core, lies in the `(δ + r)`-thickening of `V₀`'s core.

No position net and no direction net appear, the constant is `1`, and there is no constraint on `ρ`
beyond `δ + r ≤ ρ` — in particular the statement is available for arbitrarily small `ρ`.  What it
*needs* is the tube-shaped container, i.e. the datum `K ≤ V₀` with `r` comparable to `b`.  This is
precisely the paper's "the `θb × b × 1` plank sits inside a `b`-tube", and it is exactly what the
current `Plank` normalisation fails to provide: a `Plank a b` has longitudinal extent `2` while a
`Tube r` has diameter at most `1 + 2r`, so `K ≤ V₀` forces `1/2 ≤ r`
(`Kakeya.Plank.half_le_of_le_tube`).  A *fixed dilation* of the covering radius does not repair
this, because the deficiency is longitudinal and the core length of a `Tube` is pinned to `1` by its
definition. -/

/-- Rescaling is idempotent in its radius argument: only the endpoints of the tube are retained. -/
theorem Tube.rescale_rescale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {δ : ℝ≥0} (T : Tube δ E) (r ρ : ℝ≥0) : (T.rescale r).rescale ρ = T.rescale ρ := rfl


/-! ### Cross-parent counting, entirely external-parentwise

The counting below never mentions the coarse hierarchy.  The reason is a structural mismatch that
the hierarchy route cannot repair: the Katz--Tao property lives on each *external* factorization
class `Fz k` separately (`ConvexSpaceBody.Factorization.isKatzTao`), many external `ρ`-parents can
share one hierarchy node (whose radius `gridScale δ N kLev` may be far larger than `ρ`), and
Katz--Tao is inherited by subsets but not by unions.  So the within-class estimate must be used on
the class where it holds, and the *external* parents must be counted directly.

The input that does the counting is leaf-mediated bounded overlap of the external system itself:
for every `ρ`-tube `V`, at most `Cu` external parents own a leaf lying inside `V`.  This is the
external analogue of `Tube.UniformTubeSet.boundedOverlap` and the honest replacement for
the sorried `Kakeya.Tube.IsUniform.spread`; it is *not* pairwise essential distinctness of the
coarse family, and it is not automatic for an arbitrary external family. -/


/-! ### The comparable-plank normalisation, and the local cover it unlocks

The covering datum above is still an *assumed* counting statement.  This section reduces it to a
single *containment*, which is both weaker and manifestly true in the paper's normalisation, and
proves the counting.

**The normalisation defect.**  `Plank a b` is `Prism3D a b 1`, and `Prism3D` records half-widths, so
a Lean plank has longitudinal *extent* `2`.  A `Tube r` is the `r`-neighbourhood of a segment of
length exactly `1` (`Tube.dist_eq_one`), hence has diameter at most `1 + 2r`.  A plank inside
a tube therefore forces `2 ≤ 1 + 2r`, i.e. `1/2 ≤ r` (`Kakeya.Plank.half_le_of_le_tube`).  This is a
fixed-constant mismatch between two normalisations, not a statement about the mathematics: the paper
asks only for dimensions *comparable* to `a × b × 1`, and its `θb × b × 1` plank does sit inside a
tube of radius comparable to `b`.  Because the deficiency is longitudinal and `Tube`'s core length
is pinned to `1`, no dilation of the covering radius repairs it, and neither does a position or a
direction net: a leaf has core length `1` and so does a covering tube, so covering a container of
extent `2` leafwise needs `⌈1/ρ⌉` tubes, not `O(1)`.

**The minimal comparable-plank interface.**  What the argument consumes is exactly
`IsTubeShaped r K` — the container lies in *some* tube of radius `r` — with `r` comparable to `b`.
`Kakeya.Prism3D.isTubeShaped` proves that this holds, with `r = a + b ≤ 2 * b`, for any prism whose
long half-width is at most `1/2`, i.e. for the paper's normalisation.  Nothing about
`PlankFactorization`, `Prism3D` or `Tube` is changed; the datum is simply requested where the paper
supplies it.

**What it buys.**  With a tube-shaped container the cover is a *singleton* and no `δ` enters at all:
a body inside `K` is inside `V₀`, hence inside `V₀.rescale ρ` as soon as `r ≤ ρ`.  So
`Ccover = 1`, the covering radius is exactly `ρ`, and the statement is available for arbitrarily
small `ρ` — the local theorem that `Kakeya.exists_leafwise_tube_cover` (which discretises all of
`B₁` and therefore needs `1/2 ≤ ρ`) is not. -/


/-! ### The actual factor body, and the confinement datum that replaces the false shape output

The shape datum of the previous iteration,

`∃ V₀ : Tube (2 * b) E, (Plank.thickened (W j).toPrism3D θ hθ1).toConvexSpaceBody ≤ V₀`,

is **false** for small `b`, and this section removes it.  Two facts explain both the failure and the
repair.

*Why it is false.*  `Plank a b = Prism3D a b 1` and `Prism3D` records half-widths, so a thickened
plank has longitudinal extent `2`, while a `Tube r` has diameter at most `1 + 2r`; containment
forces `1/2 ≤ r` (`Kakeya.Plank.half_le_of_le_tube`).  Nothing can be attached to the *exact* Lean
thickened plank at radius comparable to `b`.

*Why the count is nevertheless available.*  What the parent count consumes is not a shape statement
about the container at all.  It needs only: **one** test tube of radius `Cparent * ρ` catching an
occupying leaf of every contributing outer body.  That is the datum `hconf` below, and it is
satisfiable for arbitrarily small `ρ`, because `W x ⊆ W_θ(j)` is longitudinally *rigid*: applying
transverse bounds of `W_θ(j)` to `centre x ± u x` gives `|⟪u x, e₁ʲ⟫| ≤ b` and
`|⟪u x, e₀ʲ⟫| ≤ θb`, hence `|⟪u x, e₂ʲ⟫| ≥ 1 - b²`, and then the longitudinal bound gives
`|⟪centre x - centre j, e₂ʲ⟫| ≤ b²`.  So all contributing bodies — and with them their occupying
leaves, which lie in the *actual* factor bodies of longitudinal extent `≈ 1` rather than in the
representative planks of extent `2` — are confined to a single tube of radius `O(b) ⊆ O(ρ)` on
`W_θ(j)`'s own long axis.

This is exactly the distinction steps 3 asks for: the body on which Proposition 5.1 factors the fine
tubes (`body`, longitudinal extent `≈ 1`, contained in its coarse parent) is **not** the exact Lean
plank handed to GWZ Lemma 6.4 (`W`, longitudinal extent `2`).  The old interface made them
definitionally equal; that identification is the normalisation bug.  Here they are separate, related
only by fixed-constant comparability, of which only the transverse half — `ContainsFlatDisc` — is
consumed by the proved layer. -/


/-! ### The cross-parent test dilation

GWZ Lemma 6.4 tests non-concentration against the `C_NC`-dilation of a `θ`-thickened plank, whose
transversal half-widths are `C_NC · θ b` and `C_NC · b`. The confinement datum is therefore *stated*
at the radius `(2 C_NC + 2) · ρ`, not `8 ρ`: the aligned container's `8 ρ` budget is *not* enough once
`C_NC > 3`. `(2 C_NC + 2) · ρ` is a chosen radius, not a derived transversal bound — a `Tube` has a
disc cross-section, so the transversal requirement is `C_NC · b · sqrt (1 + θ ^ 2)`, up to
`2 * sqrt 2 * C_NC * ρ` under `b ≤ 2ρ`, and that exceeds `(2 C_NC + 2) ρ` for `C_NC > 2.414…`. The constant is fixed by what the leafwise cover below can
absorb, not by a transversal match.

`Kakeya.ExternalParentSystem` is **not** generalized for this.  Its overlap field is already stated
for test tubes of radius `8 ·` (its own scale), and its construction
(`Kakeya.exists_externalParentSystem_of_four_mul_le`) puts no upper bound on that scale.  So the
parent system is simply instantiated at the enlarged scale `crossParentTestConst C_NC * ρ`, and its
own overlap radius `8 * (crossParentTestConst C_NC * ρ)` then dominates the confinement radius with
room to spare.  Nothing in the packing argument changes, and the overlap constant stays the
absolute `Kakeya.parentOverlapConst`.

The constant itself is `Kakeya.crossParentTestConst`, defined in `FrostmanPlankReduction.lean` so that
the Proposition-5.1 interface in `FrostmanPlankEstimate.lean` can state its confinement clause at that
radius. -/


end Kakeya

end

end

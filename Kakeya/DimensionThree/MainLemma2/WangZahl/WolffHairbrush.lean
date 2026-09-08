/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.WangZahl.SigmaCalculus
public import Kakeya.DimensionThree.Plank.SlabTube
public import Kakeya.DimensionThree.MainLemma2.WangZahl.Definitions
public import Kakeya.Projection
public import Kakeya.DimensionThree.MainLemma2.WangZahl.EToD
public import Kakeya.DimensionThree.CardBound
public import Kakeya.DimensionThree.MainLemma2.WangZahl.Rescaling
public import Kakeya.DimensionThree.MainLemma2.WangZahl.WZMultiScale

/-!
Wolff's hairbrush argument: Wang--Zahl Proposition 1.10 (`WolffHairbrush`).

Source: Wang--Zahl, Appendix `WolffHairbrushSec`, where the proposition is restated in the *expanded* form

  For all `eps > 0` there exist `kappa, eta > 0` such that for all `delta > 0`:
  if `(T,Y)_delta` is `delta^eta`-dense with `CKT(T) <= delta^{-eta}` and
  `FS(T) <= delta^{-eta}`, then

      |union of Y(T)| >= kappa * delta^{3/2 + eps} * (#T)^{1/2}.        (*)

`WolffHairbrushEstimate` below is exactly (*), restricted to `delta <= 1`
(for `delta > 1` and nonempty `T` the hypotheses are already contradictory,
see `assertionD_half_zero_of_hairbrush`).

This file proves the bridge `(*) => AssertionD (1/2) 0`, i.e. that the source's
expanded form really is Assertion `D(1/2, 0)` in the sense of Definition 1.5.
The bridge is the two-sided comparison `|T| ~ delta^2` for a `delta`-tube of
`R^3`, via `Tube.volume_carrier_le`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric

namespace Kakeya.WangZahl

noncomputable section

universe u

/-! ### The source's expanded form of Proposition 1.10 -/

/-! ### `|T| ≤ 12 δ²` for a `δ`-tube of `R^3` with `δ ≤ 1` -/

/-! ### The bridge: the source's expanded form is `D(1/2, 0)` -/

/-! ### The geometric decomposition supplied by the hairbrush argument -/

/-! ### Hereditary properties of the Katz--Tao convex Wolff constant

An earlier form of the second geometric leaf (`WolffHairbrushBroad` below)
carried no Katz--Tao hypothesis and was **refuted**; see
`Kakeya.DimensionThree.MainLemma2.WangZahl.WolffHairbrushGuardrails`, which keeps
the refutation in the build as a tripwire.  The repair hands the hypothesis
`CKT(𝕋) ≤ δ^{-η}` down from `HairbrushCover` to `WolffHairbrushBroad`, and the
lemmas of this section are what make that legitimate: unlike
`frostmanSlabWolffConstant`, the definition of `katzTaoConvexWolffConstant`
carries **no `#𝕋` normalization**, so it is monotone under passing to a
subfamily and the classes `part j ⊆ 𝕋` of the cover inherit the hypothesis
verbatim.

On the Frostman side the `#𝕋` normalization is present, so a class only
inherits `FS(part j) ≤ FS(𝕋) · (#𝕋 / #(part j))`, and the *normalized* bound
`FS(part j) ≤ δ^{-ν}` is in fact **false** for a class: the class sits inside a
single `θ`-tube, hence inside a slab of thickness `θ` and volume `≍ θ`, which
already forces `FS(part j) ≥ c θ^{-1}`.  Handing the normalized Frostman
hypothesis down would therefore have created an *inconsistent* hypothesis
bundle at every `θ ≪ δ^{ν}` — green in the compiler, vacuous in content.  It is
not handed down; what the class needs in its place (a slab count) follows from
its Katz--Tao hypothesis, since the class is confined to a `θ`-tube.  The
ambient Frostman hypothesis is still used, at the ambient level, by
`slabTubeCount_holds`. -/

/-- `1 ≤ δ^{-ν}` for `0 < δ ≤ 1` and `0 ≤ ν`: the Katz--Tao budget of the
repaired leaf is never vacuous. -/
theorem one_le_rpow_neg {δ : ℝ≥0} (hδ1 : δ ≤ 1) {ν : ℝ} (hν : 0 ≤ ν) :
    (1 : ℝ≥0∞) ≤ (δ : ℝ≥0∞) ^ (-ν) := by
  have hδ1E : (δ : ℝ≥0∞) ≤ 1 := by exact_mod_cast hδ1
  have := ENNReal.rpow_le_rpow_of_exponent_ge hδ1E (by linarith : -ν ≤ (0:ℝ))
  simpa using this

/-! ### Shading refinements: the source's missing degree of freedom

The source's covering step does **not** keep the shading fixed.  Immediately
after producing the cover, Wang--Zahl state

> After a further refinement, we may suppose that each set `𝕋^{T_θ}` is
> `δ^{3η}`-dense.

That "further refinement" *shrinks the shadings*, once per class of the cover,
and it is what pays for both the density and the broadness of the class.  A
statement whose only shaded family is the fixed input `T` cannot express it,
and this missing degree of freedom is exactly what made the fixed-shading form
of the covering leaf **false**
(`Kakeya.DimensionThree.MainLemma2.WangZahl.WolffHairbrushGuardrails.not_balancedBroadCover`:
two orthogonal fully shaded `δ`-tubes at `θ = δ`, where no `δ`-tube contains
both, so two classes are forced and their *fixed* shadings overlap in
`closedBall 0 δ`).  With per-class shadings that witness is no longer a
refutation: the cover may hand out `Y₀ = A \ B` and `Y₁ = B`, whose volumes add
up to exactly `|A ∪ B|`.

Note also the density bookkeeping the source performs here: the input is
`δ^η`-dense and the output only `δ^{3η}`-dense.  The leaves below record that
loss the way the file already records the loss in the broadness quality — the
target quality `ν` is an *input* and the admissible input quality `η ≤ ν` is
handed out existentially by the leaf — rather than by inventing a numeral for
the exponent.

**On `IsBroadAtScale` itself.**  The predicate is a verbatim transcription of
the source's display and is *not* changed here.  What was wrong was every place
it was applied: `IsBroadAtScale s T θ ν` tested at `r = δ` and `w = dir T_{i₀}`
puts `T_{i₀}` into its own left-hand count
(`WolffHairbrushGuardrails.rpow_le_multiplicity_of_isBroadAtScale`), so it
demands that *every* point of *every* shading be covered by at least
`(θ/δ)^ν` tubes.  The source has the same consequence, but only for the shading
it has already refined; asking it of the fixed input shading `Y(T)` is the
over-demand, since the far end of a tube of a bush has multiplicity `1`.  The
repair is therefore to apply the predicate to `Y j`, not to `T`, which is what
the restated leaves below do. -/

/-- **`T'` refines the shadings of `T` on `s`:** same underlying tubes, smaller
shadings.  This is the source's "further refinement" of Wang--Zahl,
as a relation between shaded families. -/
def IsShadingRefinement {δ : ℝ≥0} {ι : Type u} (s : Finset ι)
    (T' T : ι → ShadedTube δ Space3) : Prop :=
  ∀ i ∈ s, (T' i).toTube = (T i).toTube ∧ (T' i).shade ⊆ (T i).shade

/-- A shading refinement does not move the carriers. -/
theorem IsShadingRefinement.carrier_eq {δ : ℝ≥0} {ι : Type u} {s : Finset ι}
    {T' T : ι → ShadedTube δ Space3} (h : IsShadingRefinement s T' T) {i : ι} (hi : i ∈ s) :
    (T' i).carrier = (T i).carrier := by
  have hT := (h i hi).1
  rw [show (T' i).carrier = (T' i).toTube.carrier from rfl,
    show (T i).carrier = (T i).toTube.carrier from rfl, hT]

theorem IsShadingRefinement.mono {δ : ℝ≥0} {ι : Type u} {s s' : Finset ι}
    {T' T : ι → ShadedTube δ Space3} (h : IsShadingRefinement s T' T) (hss : s' ⊆ s) :
    IsShadingRefinement s' T' T :=
  fun i hi => h i (hss hi)

theorem IsShadingRefinement.trans {δ : ℝ≥0} {ι : Type u} {s : Finset ι}
    {T'' T' T : ι → ShadedTube δ Space3} (h1 : IsShadingRefinement s T'' T')
    (h2 : IsShadingRefinement s T' T) : IsShadingRefinement s T'' T :=
  fun i hi => ⟨(h1 i hi).1.trans (h2 i hi).1, (h1 i hi).2.trans (h2 i hi).2⟩

/-- **The canonical shading refinement**: intersect every shading with a fixed
measurable set.  This is `ShadedBody.restrictShade` at the level of shaded
tubes, and it is how a cover hands out its per-class shadings. -/
def restrictShadedTube {δ : ℝ≥0} (T : ShadedTube δ Space3) (S : Set Space3)
    (hS : MeasurableSet S) : ShadedTube δ Space3 where
  toTube := T.toTube
  shade := T.shade ∩ S
  measurableSet_shade := T.measurableSet_shade.inter hS
  shade_subset := fun _ hx => T.shade_subset hx.1

@[simp]
theorem shade_restrictShadedTube {δ : ℝ≥0} (T : ShadedTube δ Space3) (S : Set Space3)
    (hS : MeasurableSet S) : (restrictShadedTube T S hS).shade = T.shade ∩ S := rfl

/-! ### The two geometric leaves of the source proof -/

/-! ### Non-vacuity of the two leaves -/

/-- The unit segment centred at the origin, as a `δ`-tube. -/
def centredTube (δ : ℝ≥0) : Tube δ Space3 :=
  Tube.mk' δ (x := -((1 : ℝ) / 2) • EuclideanSpace.single 0 (1 : ℝ))
    (y := ((1 : ℝ) / 2) • EuclideanSpace.single 0 (1 : ℝ)) (by
      have h : (-((1 : ℝ) / 2) • EuclideanSpace.single 0 (1 : ℝ) -
          ((1 : ℝ) / 2) • EuclideanSpace.single 0 (1 : ℝ) : Space3) =
          -(EuclideanSpace.single 0 (1 : ℝ)) := by module
      rw [dist_eq_norm, h, norm_neg, PiLp.norm_single, norm_one])

/-! ### No `δ`-tube with `δ > 1/2` fits in the unit ball

A `δ`-tube has diameter `1 + 2δ`, so a family of `δ`-tubes of the unit ball is
empty unless `δ ≤ 1/2`.  This delimits the "large `δ`" end of every statement in
this file: at `δ` above `1/2` all of them are vacuous, and at `δ = 1/2` the
`δ^{-ε/8}`-type counting budgets are within a factor `2^{ε/8}` of `1`. -/

/-! ### The Frostman slab hypothesis forces a large family

Two facts recorded here because they are what makes the ambient hypothesis
bundle of `HairbrushCover` (and of `WolffHairbrushEstimate`) *quantitatively*
non-trivial: a nonempty family with `FS(𝕋) ≤ δ^{-η}` must have `#𝕋 ≳ δ^{η-1}`
members.  In particular no bounded family satisfies the ambient bundle, which
is why the non-vacuity certificates of this file certify the *class-level*
bundles (`WolffHairbrushBroad`, `BalancedBroadCover`), where `FS` is absent, and
not the ambient one. -/

/-! ### The two halves of Leaf 1

`HairbrushCover` bundles two steps of the source which are logically
independent and are proved by different arguments:

* the *scale selection*: the standard reductions produce the scale `θ` and a
  refinement of the family which is non-concentrated at that scale
  (`BroadScaleRefinement`);
* the *balanced partitioning cover* at the scale so produced, together with the
  essential disjointness of the shadings of distinct classes
  (`BalancedBroadCover`).

`hairbrushCover_of_refinement_of_cover` recombines them.  The `δ^{-ε/8}`
counting budget of `HairbrushCover` is split evenly, `δ^{-ε/16}` to each half.

Note that the class-level broadness demanded by `BalancedBroadCover` really has
to be an *output* of the cover step, not something derived afterwards from the
ambient broadness: broadness is a ratio, so it is not inherited by subfamilies.
What makes it available to the cover step is that the shadings of distinct
classes are essentially disjoint, so a point of the shading of a class sees only
tubes of that class, and the ambient count at that point *is* the class count. -/

/-- A subfamily of a tube shading family is a tube shading family. -/
theorem IsTubeShadingFamily.subset {δ : ℝ≥0} {ι : Type u} {s' s : Finset ι}
    {T : ι → ShadedTube δ Space3} (hfam : IsTubeShadingFamily s T) (hss : s' ⊆ s) :
    IsTubeShadingFamily s' T :=
  ⟨fun i hi => hfam.1 i (hss hi), hfam.2.mono (by exact_mod_cast hss)⟩

/-! ### The Katz--Tao hypothesis of Leaf 2, in counting form

The hypothesis `CKT(𝕋) ≤ δ^{-ν}` controls the class density.  Tested against
the `θ`-tube `R` that contains the whole class, that hypothesis *is* the
source's `δ`-separation of directions, in the currency of Definition 1.5:
`#𝕋 ≤ δ^{-ν} |R|/|T| ≍ δ^{-ν}(θ/δ)²`.  The first theorem below is that test;
the second settles Leaf 2 in the degenerate regime `θ ≤ δ`, where the class is
confined to a single `δ`-tube and the counting bound alone already beats the
required volume.  All the content of Leaf 2 therefore sits at `θ ≫ δ`. -/

/-! ### Leaf 2 in the degenerate regime `θ ≤ δ` -/

/-! ### The missing conjunct of the source's reduction: the `θ`-cap

The split `BroadScaleRefinement` + `RefinedBalancedBroadCover` above transcribes
only the *second* half of the source's display at Wang--Zahl.  The
sentence there reads, in full:

> There exists a number `θ ∈ [δ,1]` so that for each `x ∈ ⋃_T Y(T)`, **there is
> a vector `v = v(x)` so that `∠(v, dir T) ≤ θ` for each `T ∈ 𝕋` with
> `x ∈ Y(T)`**, and for each unit vector `w` and each `r ∈ [δ,θ]`, we have
> `#{T ∈ 𝕋_Y(x) : ∠(w, dir T) ≤ r} ≤ (r/θ)^η #𝕋_Y(x)`.

`IsBroadAtScale` is the second clause.  The first clause — every tube whose
shading contains `x` has direction in a single `θ`-cap — was dropped, and
dropping it is what makes `RefinedBalancedBroadCover` useless as a leaf:

* `RefinedBalancedBroadCover` takes `θ` as a universal input, so it must hold at
  `θ = δ`, where broadness is vacuous (`isBroadAtScale_of_le_delta`) and a class
  is confined to a single `δ`-tube, hence has boundedly many members
  (`Kakeya.card_le_of_EssDistinct_in_tube_six` at `ρ = δ`).
* Its density conjunct forces `∑_{i ∈ part j} |Y j i| ≥ δ^ν ∑_{i ∈ part j}|T_i|`,
  so `|⋃_{i ∈ part j} Y j i| ≥ δ^ν |T|` (a maximum dominates an average), and its
  counting conjunct forces `#P ≳ δ^{ε/16}(#𝕋)` classes.
* The essential-disjointness conjunct then reads
  `δ^{ε/16}(#𝕋) δ^ν |T| ≲ |⋃_{i ∈ 𝕋} Y(T_i)|`, i.e. a bound of the form
  "multiplicity `≲ δ^{-ν-ε/16-η}`" for an arbitrary `δ^η`-dense, Katz--Tao
  bounded family of essentially distinct `δ`-tubes.  That is a Kakeya-strength
  statement: it is *implied* by, not a step towards, the estimate this appendix
  is proving.

The cap condition gives the required exponent budget.  Cap
concentration confines the tubes whose shading contains `x` to directions in a
single `θ`-cap, hence (as `δ ≤ θ`) to `δ`-tubes lying in one `≍ θ`-tube, whose
number the Katz--Tao hypothesis bounds by `≍ δ^{-η}(θ/δ)²`; the multiplicity is
therefore `≲ δ^{-η}(θ/δ)²`, the union is `≳ δ^{2η}(δ/θ)²(#𝕋)|T|`, the classes
now have up to `≍ δ^{-η}(θ/δ)²` members each so `#P ≳ δ^{ε/16+η}(δ/θ)²(#𝕋)`,
and the disjointness conjunct asks `δ^{ε/16 + ν - η} ≲ 1`, which holds for
`δ` small because `η ≤ ν`.

The capped leaves below are therefore the ones the source actually offers.
`broadScaleRefinement_of_capped` and `cappedBalancedBroadCover_of_refined`
record that the change moves work from Leaf 1b to Leaf 1a and nowhere else:
the capped Leaf 1a is *stronger* than `BroadScaleRefinement` and the capped
Leaf 1b is *weaker* than `RefinedBalancedBroadCover`. -/

/-- **The source's directional concentration condition at scale `θ`.**

Source: Wang--Zahl, the clause "for each
`x ∈ ⋃_T Y(T)` there is a vector `v = v(x)` so that `∠(v, dir(T)) ≤ θ` for each
`T ∈ 𝕋` with `x ∈ Y(T)`".

As in `IsBroadAtScale`, the angle is measured by chordal distance between unit
vectors, made insensitive to the sign ambiguity `dir T ↦ -dir T`, and the
quantifier over `x` ranges over all of `Space3`: off the shadings the inner
condition is vacuous, so nothing is demanded there. -/
def IsCapConcentrated {δ : ℝ≥0} {ι : Type u}
    (s : Finset ι) (T : ι → ShadedTube δ Space3) (θ : ℝ≥0) : Prop :=
  ∀ x : Space3, ∃ v : Space3, ‖v‖ = 1 ∧
    ∀ i ∈ s, x ∈ (T i).shade →
      min ‖v - (T i).toTube.direction‖ ‖v + (T i).toTube.direction‖ ≤ (θ : ℝ)

/-- Cap concentration is monotone in the scale. -/
theorem IsCapConcentrated.mono_scale {δ : ℝ≥0} {ι : Type u} {s : Finset ι}
    {T : ι → ShadedTube δ Space3} {θ θ' : ℝ≥0} (h : IsCapConcentrated s T θ)
    (hθ : θ ≤ θ') : IsCapConcentrated s T θ' := by
  intro x
  obtain ⟨v, hv, hcap⟩ := h x
  exact ⟨v, hv, fun i hi hxi => (hcap i hi hxi).trans (by exact_mod_cast hθ)⟩

/-- Cap concentration passes to subfamilies. -/
theorem IsCapConcentrated.subset {δ : ℝ≥0} {ι : Type u} {s s' : Finset ι}
    {T : ι → ShadedTube δ Space3} {θ : ℝ≥0} (h : IsCapConcentrated s T θ)
    (hss : s' ⊆ s) : IsCapConcentrated s' T θ := by
  intro x
  obtain ⟨v, hv, hcap⟩ := h x
  exact ⟨v, hv, fun i hi hxi => hcap i (hss hi) hxi⟩

/-! ### Cap concentration bounds the multiplicity

The three geometric lemmas below turn `IsCapConcentrated` into the counting
statement that the covering leaf needs, and are the compiler-checked form of
the arithmetic recorded above `IsCapConcentrated`. -/

/-! ### Leaf 1b at `θ = δ`

The two theorems below settle `CappedBalancedBroadCover` in the degenerate
regime `θ = δ`, exactly as `wolffHairbrushBroad_of_theta_le_delta` settles Leaf
2 there, and for the same purpose: to locate the content of the leaf.  They are
the place where the cap actually gets spent, through
`exists_disjointed_counting_of_isCapConcentrated`.

At `θ = δ` broadness is free (`isBroadAtScale_of_le_delta`) and a class may be a
single tube, so the cover can be taken to be the *singleton* cover
`part i = {i}`, `parent i = (T i).toTube`, with `Y` the disjointification of the
shadings (`exists_disjointed_shading`).  Then the essential-disjointness
conjunct holds with equality and the only thing to prove is the counting
conjunct: that at least `δ^{ε/16}` of the tubes keep a private shading of volume
`≥ δ^ν |T_i|`.  That is what the cap buys.

The window is the two hypotheses `hwin1`, `hwin2`, in the style of
`wolffHairbrushBroad_of_theta_le`: with `c = Tube.le_volume.c 3` they read

`2 · 9216 δ^ν ≤ c² δ^{2η}`  and  `18432 ≤ c² δ^{2η - ε/16}`,

both of which hold for all small `δ` as soon as `2η < min (ν, ε/16)` — that is,
as soon as the input density quality `η` is small compared with the output
density quality `ν` and with the counting budget `ε/16`, which is exactly the
freedom the leaf has in choosing `η`.  Nothing here works at `θ ≫ δ`: a
one-tube class is not broad at scale `θ`, so the singleton cover becomes
inadmissible and the `θ`-tube cover has to be built.
-/

/-! ### The remaining geometric obligation -/

end

end Kakeya.WangZahl

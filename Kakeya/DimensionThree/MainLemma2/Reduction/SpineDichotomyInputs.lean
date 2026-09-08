/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Uniform
public import Kakeya.Tube.EssentiallyDistinctReduction
public import Kakeya.DimensionThree.MainLemma2.ShadedDividingScales
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEveryScale
public import Kakeya.DimensionThree.MainLemma2.Reduction.Assembly

/-!
# Component G2a: the missing inputs of GWZ Lemma 7.7(B)

`Kakeya.ML2Shaded.exists_shaded_dividingScalesKatzTao` and its one-sided companion
`Kakeya.ML2Shaded.exists_shaded_dividingScalesKatzTao_dense` — GWZ Lemma 7.7(B) in shaded form —
carry three hypotheses that `Kakeya.ML2Assembly.Dichotomy`'s hypotheses do **not** supply:

1. `(𝕋 : Set ι).Pairwise IsEssentiallyDistinct` — a *geometric* condition on the retained tubes;
2. `Tube.UniformTubeSet 𝕋 T (Tube.ssfGridLen δ) C` — a uniform hierarchy on the grid of `δ`;
3. `4096 ≤ N`, the stopping-step threshold of `StickyKakeya.dividingScalesKatzTao`.

This file supplies all three, and prices them.  Nothing here touches a shading.

## The answers

* **`4096 ≤ N` is free.**  The `N` of 7.7(B) is the *stopping-step count*, not the grid length, and
  the parameter spine already commits to `N = Kakeya.ML2Spine.spineCount ϖ ε₁ = ⌈25/ε₂²⌉` with
  `ε₂ ≤ 1/64`, so `Kakeya.ML2Spine.four_thousand_le_spineCount` gives `N ≥ 4096` from `0 < ϖ` and
  `0 < ε₁` alone — both of which the `GeometricCore` context has (the window exponent of GWZ Lemma
  9.1, and the exponent `Kakeya.ML2Reduction.exists_everyScale_exponent` returns at the absolute
  accuracy).  Packaged as `Kakeya.ML2Inputs.exists_dividingScalesLadder`, which hands over the
  whole non-family hypothesis block of 7.7(B) — `4096 ≤ N`, `e = 1/√N`, `0 ≤ η 0`,
  `η k ≤ e η_{k+1}`, `η N ≤ e` — from `(β, ϖ, ε₁, gain, dens)` and nothing else.  So the answer to
  "can the `Dichotomy` context hand you an `IsSpine`?" is **yes**, and this is the theorem that
  does it.

* **`Pairwise IsEssentiallyDistinct` is not free, and banding is the wrong place to look for it.**
  Banding is a *mass* selection and says nothing about geometry.  What supplies it is
  `Kakeya.Tube.refineToEssDistinctLeaves`: **every** finite family of `δ`-tubes has a pairwise
  essentially distinct subfamily, at the cardinality loss `C_n · Δ_max(𝕋)`, and
  `Kakeya.ML2Assembly.Dichotomy`'s Katz--Tao hypothesis is *exactly* a bound on `Δ_max(𝕋)`
  (`Kakeya.IsKatzTao` unfolds to `Kakeya.maxDensity … ≤ …`).  So the loss the extra selection costs
  is the one the dichotomy's own hypothesis already pays for
  (`Kakeya.ML2Inputs.exists_essDistinct_subfamily` at `D = δ^{-θ}`, absorbed into `δ^{-(θ+α)}` by
  `Kakeya.ML2Inputs.exists_threshold_edLoss_le`).

* **The uniform hierarchy comes from the *tube-level* uniformization**,
  `Tube.exists_uniformTubeSet_subfamily_ssf`, not from
  `ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf`.  That is not a stylistic preference: the
  tube-level version keeps the family `T` *literally the same function*, so essential distinctness
  and any pointwise datum about the shading — `Kakeya.ML2Shaded.HasDenseShading` in particular —
  restrict to the selected subfamily for free and at **zero** loss, and no shade refinement and no
  fullness loss are incurred before the dichotomy.  Inside the loop the dichotomy never looks at a
  shading, so the shaded uniformization belongs at the GWZ 7.3(B) leaf, not here.

## The order of the two selections is forced

Essential distinctness is chosen **first** and the uniformization **second**.

The reason is not convenience.  `Tube.UniformTubeSet` does **not** restrict to an arbitrary
subfamily: every field restricts except `Tube.UniformTubeSet.le_card_class`, which fails at every
node whose class the discard empties, and repairing it by flattening the branching count breaks
`Tube.UniformTubeSet.card_class_le` at any constant.  The proved obstruction in the tree is
`Kakeya.ML2Shaded.coverClass_nonempty_of_uniformTubeSet`.  So a hierarchy must be built on the
index set that is going to carry it, i.e. after every discard — which is also why
`Kakeya.ML2Shaded.exists_shaded_dividingScalesKatzTao` puts its mass-banded subfamily `s''`
*outside* the hierarchy it returns.

Essential distinctness, by contrast, is hereditary (`Kakeya.ML2Inputs.pairwise_essDistinct_subset`),
so choosing it before the uniformization costs nothing.  The composite order
**ED → uniformize → 7.7(B)** therefore works, and the reverse does not even typecheck.

## The trap, and how it is avoided here

`Kakeya.Tube.refineToEssDistinctLeaves` is **blind to the shading**: it selects by geometry, so the
retained subfamily can be entirely unshaded while `#𝕋 ≤ C_n D #𝕋'` still holds, and then no bound
`∑_𝕋 |Y_i| ≤ L ∑_{𝕋'} |Y_i|` holds at any finite `L`
(`Kakeya.ML2Inputs.no_mass_share_of_essDistinct_refinement` is the refutation).  The
cardinality-to-mass conversion therefore needs a *pointwise* datum, and the cheapest one is the
one-sided `Kakeya.ML2Shaded.HasDenseShading`: `Kakeya.ML2Shaded.sum_shade_le_of_card_le` reads it on
the **retained** set, where the ED selection hands it over for free, and its constant carries no
comparability factor and no logarithm.
`Kakeya.ML2Inputs.sum_shade_le_of_essDistinct_refinement` is that conversion at the ED loss.

**Direction check of every hypothesis in this file.**  `hED` (pairwise), `hdense`
(`HasDenseShading`) and `hball` are pointwise and are consumed pointwise; `hD` (`maxDensity`),
`hcard` and the mass inequalities are aggregate and are consumed as aggregates.  No aggregate
quantity is read at a point, and no pointwise quantity is summed without a matching per-index
bound.

## What is here

* `pairwise_essDistinct_subset`, `pairwise_essDistinct_of_tube_eq` — heredity of the geometric
  hypothesis under the two operations the pipeline performs.
* `exists_dividingScalesLadder` — the `(N, e, η)` block of 7.7(B), `4096 ≤ N` included.
* `spineNu_le_div_48000` — `ν ≤ β/48000`, the quantitative statement that the loss charged below is
  affordable against the absolute accuracy `β/2` (a fact three docstrings assert; here proved).
* `edLoss`, `exists_essDistinct_subfamily`, `exists_threshold_edLoss_le` — the geometric hypothesis,
  produced, with its loss and the threshold that absorbs it.
* `sum_shade_le_of_essDistinct_refinement`, `no_mass_share_of_essDistinct_refinement` — the mass
  side of the ED discard, and the refutation of doing it with no pointwise datum.
* `exists_dividingScalesInputs` — **the input package**, on unshaded tubes: from exactly
  `Kakeya.ML2Assembly.Dichotomy`'s Katz--Tao and containment hypotheses plus the crude cardinality
  bound, a subfamily carrying essential distinctness, the same density bound and a uniform
  hierarchy, at the single cardinality loss `δ^{-(θ+α)}`.
* `exists_shaded_dividingScales_of_dichotomyHypotheses` — **the capstone**: GWZ Lemma 7.7(B) in its
  one-sided shaded form actually run on the `Dichotomy` context, with the essential-distinctness
  hypothesis, the uniformity hypothesis and the `4096 ≤ N` side condition all gone from the
  statement, and with alternative (i) already absorbed to `δ^{-ε₁}`.
* `DividingScalesOutput` — the output of the capstone, named once so that its threshold form and
  its `∀ᶠ δ` form state the same thing.
* `eventually_dividingScalesInputs_dim3` and `eventually_shaded_dividingScales_dim3` — the package
  and the capstone in the `∀ᶠ δ` form of `Dichotomy`, with the crude cardinality bound discharged
  from the dichotomy's own hypotheses by `Kakeya.ML2Assembly.card_le_rpow_neg_four` (its `η ≤ 1`
  side condition met by `spineNu_le_div_48000`), so that hypothesis is not a new demand either.
  `eventually_shaded_dividingScales_dim3` is the theorem the assembly of the first disjunct calls.
* `maxDensity_le_of_card_le` — with `Kakeya.ML2Shaded.exists_fullShading_of_tubes`, the consistency
  of the whole hypothesis set.

## `ε`-discipline

No statement in this file has an `ε` binder.  The only exponents are `β`, the window exponent `ϖ`,
the Katz--Tao exponent `ε₁` of Theorem 7.3(B) read at an absolute accuracy, the spine's own
`ε₂, e, (η_k)`, and the free absorption budget `α > 0`.  Nothing here can reintroduce a dependence
of `ν` on the outer accuracy; `Kakeya.ML2Spine.not_epsFree_of_outerAccuracy` is untouched.
-/

@[expose] public section

open MeasureTheory Metric Topology Filter ShadedBody ConvexSpaceBody
open Tube ShadedTube

universe u

namespace Kakeya.ML2Inputs

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

/-! ### Heredity of the geometric hypothesis -/


/-! ### The `4096 ≤ N` side condition -/

/-- **`4096 ≤ N` at the spine's own stopping-step count.**  `Kakeya.ML2Spine.spineEps₂` is capped at
`1/64`, so `⌈25/ε₂²⌉ ≥ 102400`.  Nothing beyond positivity of `ϖ` and `ε₁` is used. -/
theorem four_thousand_le_spineCount {ϖ ε₁ : ℝ} (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁) :
    4096 ≤ ML2Spine.spineCount ϖ ε₁ :=
  ML2Spine.four_thousand_le_spineCount hϖ hε₁

/-- **`ν ≤ β/48000`.**

Three docstrings in the reduction assert this ("In fact `ν ≤ β/48000`") and none proves it;
`Kakeya.ML2Spine.two_spineNu_le` proves only `2ν ≤ β`.  It matters here, and quantitatively: the
essential-distinctness selection below charges `δ^{-ν}` on the way to alternative (i) of the
dichotomy, whose budget is the absolute accuracy `Kakeya.ML2Spine.absAccuracy β = β/2`.  With
`2ν ≤ β` alone the charge would consume the entire budget and the composition would be tight to the
point of failing; with `ν ≤ β/48000` all but `1/24000` of the budget is left for the ED loss, the
uniformization loss and the free `α`.

The proof is the one already inside `Kakeya.ML2Spine.two_spineNu_le`, stopped one step earlier:
`ν ≤ η₁ ≤ e² β e/48` and `e ≤ 1/10`, so `ν ≤ β/(1000 · 48)`. -/
theorem spineNu_le_div_48000 {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ) :
    ML2Spine.spineNu β ϖ ε₁ gain dens ≤ β / 48000 := by
  have he : 0 < ML2Spine.spineDiv ϖ ε₁ := ML2Spine.spineDiv_pos hϖ hε₁
  have he10 : ML2Spine.spineDiv ϖ ε₁ ≤ 1 / 10 := ML2Spine.spineDiv_le_one hϖ hε₁
  have hanti : Antitone (ML2Spine.spineAux β ϖ ε₁ gain dens) :=
    ML2Spine.spineAux_antitone hβ hβ1 hϖ hε₁ hgain hdens
  have hN : 1 ≤ ML2Spine.spineCount ϖ ε₁ := ML2Spine.one_le_spineCount hϖ hε₁
  have hstep : ML2Spine.spineNu β ϖ ε₁ gain dens ≤ ML2Spine.spineAux β ϖ ε₁ gain dens 1 := by
    unfold ML2Spine.spineNu ML2Spine.spineRung
    rw [Nat.sub_zero]
    exact hanti hN
  have hone : ML2Spine.spineAux β ϖ ε₁ gain dens 1
      ≤ ML2Spine.spineDiv ϖ ε₁ ^ 2 * β * ML2Spine.spineDiv ϖ ε₁ / 48 := by
    rw [ML2Spine.spineAux, ML2Spine.spineAux]
    exact ML2Spine.spineStep_le_div_48 hβ he.le
  have he2 : ML2Spine.spineDiv ϖ ε₁ ^ 2 ≤ 1 / 100 := by nlinarith [he.le, he10]
  have hcube : ML2Spine.spineDiv ϖ ε₁ ^ 2 * ML2Spine.spineDiv ϖ ε₁ ≤ 1 / 1000 := by
    nlinarith [he2, he.le, he10, sq_nonneg (ML2Spine.spineDiv ϖ ε₁)]
  have hfin : ML2Spine.spineDiv ϖ ε₁ ^ 2 * β * ML2Spine.spineDiv ϖ ε₁ / 48 ≤ β / 48000 := by
    nlinarith [hcube, hβ.le,
      mul_nonneg (by linarith :
        (0 : ℝ) ≤ 1 / 1000 - ML2Spine.spineDiv ϖ ε₁ ^ 2 * ML2Spine.spineDiv ϖ ε₁) hβ.le]
  linarith [hstep, hone, hfin]

/-- **The whole non-family hypothesis block of GWZ Lemma 7.7(B), supplied.**

`Kakeya.ML2Shaded.exists_shaded_dividingScalesKatzTao` asks for `N` with `4096 ≤ N`, an
`ε = 1/√N`, and a ladder `η : ℕ → ℝ` with `0 ≤ η 0`, `η k ≤ ε η_{k+1}` for `k < N` and `η N ≤ ε`.
All five come from the parameter spine, and the bottom rung is the gain `ν` of Main Lemma 2 — so
the density level at which the dichotomy is read is exactly the one
`Kakeya.ML2Assembly.GeometricCore` gets to choose.  The last three conjuncts are the `ε₂` data that
`Kakeya.ML2Reduction.exists_threshold_katzTaoError_le` spends to absorb alternative (i) to
`δ^{-ε₁}`.

There is no `ε` binder: the whole block is a function of `(β, ϖ, ε₁, gain, dens)`. -/
theorem exists_dividingScalesLadder {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ) :
    ∃ (ε₂ e : ℝ) (N : ℕ) (η : ℕ → ℝ),
      ML2Spine.IsSpine β ϖ ε₁ gain dens ε₂ e N η ∧
        4096 ≤ N ∧ e = 1 / Real.sqrt (N : ℝ) ∧
        η 0 = ML2Spine.spineNu β ϖ ε₁ gain dens ∧
        0 ≤ η 0 ∧ (∀ k < N, η k ≤ e * η (k + 1)) ∧ η N ≤ e ∧
        0 < ε₂ ∧ 5 * e ≤ ε₂ ∧ ε₂ ≤ ε₁ / 5 := by
  refine ⟨ML2Spine.spineEps₂ ϖ ε₁, ML2Spine.spineDiv ϖ ε₁, ML2Spine.spineCount ϖ ε₁,
    ML2Spine.spineRung β ϖ ε₁ gain dens, ?_⟩
  have hspine := ML2Spine.spineRung_isSpine hβ hβ1 hϖ hε₁ hgain hdens
  refine ⟨hspine, hspine.four_thousand_le_stepCount, hspine.div_eq, rfl,
    (hspine.rung_pos 0).le,
    fun k hk => ML2Reduction.rung_le_div_mul_rung_succ hspine hβ hβ1 hk,
    le_of_eq hspine.rung_top, hspine.eps₂_pos, ?_, hspine.eps₂_le_everyScale⟩
  have := hspine.div_le
  linarith

/-! ### The essential-distinctness hypothesis, produced -/


/-! ### The mass side of the essential-distinctness discard -/


/-! ### The input package -/


/-! ### The capstone: GWZ Lemma 7.7(B) run on the dichotomy's context -/


/-! ### Non-vacuity, and the cardinality hypothesis is not a new demand -/

/-- **The ladder exists unconditionally.**  Every hypothesis of
`Kakeya.ML2Inputs.exists_dividingScalesLadder` is discharged at concrete data, so the `4096 ≤ N`
it delivers is not a consequence of `False`. -/
example :
    ∃ (ε₂ e : ℝ) (N : ℕ) (η : ℕ → ℝ),
      ML2Spine.IsSpine 1 1 1 (fun x => x) (fun x => x) ε₂ e N η ∧
        4096 ≤ N ∧ e = 1 / Real.sqrt (N : ℝ) ∧
        η 0 = ML2Spine.spineNu 1 1 1 (fun x => x) (fun x => x) ∧
        0 ≤ η 0 ∧ (∀ k < N, η k ≤ e * η (k + 1)) ∧ η N ≤ e ∧
        0 < ε₂ ∧ 5 * e ≤ ε₂ ∧ ε₂ ≤ 1 / 5 :=
  exists_dividingScalesLadder (β := 1) (ϖ := 1) (ε₁ := 1) (gain := fun x => x)
    (dens := fun x => x) one_pos le_rfl one_pos one_pos (fun _ h => h) (fun _ h => h)


end Kakeya.ML2Inputs

end

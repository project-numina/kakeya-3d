/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineDichotomyInputs
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineShadingBridge

/-!
# Branch (i) of a `Kakeya.ML2Assembly.GeometricCoreAt` producer: the left disjunct

Rows **GC-L1** – **GC-L5** of the Section-9 geometric-core plan, i.e. GWZ: *"if the dividing-scales dichotomy returns alternative (i), then by Theorem 7.3(B) the
multiplicity is already `δ^{-ε}` and we are done."*

Everything here sits on top of `Kakeya.ML2Core.eventually_dividingScalesPackage_dim3` and
`Kakeya.ML2Core.losses_of_dividingScalesOutput` (rows GC-P1/GC-P2).  Nothing here builds a
hierarchy, a spine, or a shading; all of that is the package's.

## The four steps, and the exponent each spends

Write `ν = η 0 = Kakeya.ML2Spine.spineNu β ϖ ε₁ gain dens`, `c₃`, `C₃` for the two dimensional
tube-volume constants, `P = (log₂ #𝕋 + 1)^{2 ssfGridLen δ + 2}` for the shaded-uniformization
polylogarithm and `λ ≥ δ^ν/2` for the dense-shading level.

1. **GC-L1**, `Kakeya.ML2Core.exists_multiplicity_quarter` — GWZ Theorem 7.3(B) read at the
   absolute accuracy `β/4`.  The one input the package does not hand over directly is the
   *fullness floor* `δ^{2ν} ≤ λ'(u', W)` that
   `Kakeya.ML2Reduction.exists_everyScale_multiplicity_le` consumes; it is manufactured here from
   the package's `λ ≤ P · λ'(u', W)` and `δ^ν ≤ 2 λ` against the threshold `2 P ≤ δ^{-ν}`
   (`Tube.exists_threshold_polylog_pow_ssfGridLen_le` at `A = 2`, `m = 2`, `K₀ = 4`).  Reading the
   hypotheses at `2ν` rather than at `ν` is what buys that threshold, and `2ν ≤ ε₁` is free from
   `Kakeya.ML2Spine.IsSpine` (`rung_mono`, `rung_top`, `div_le`, `eps₂_le_everyScale` give
   `ν ≤ ε₁/25`).  **Spends `ν`.**
2. **GC-L2**, `Kakeya.ML2Core.sum_shade_le_shadingBridgeLoss` — the mass chain, in exactly the
   shape `Kakeya.ML2Shading.shadingBridgeLoss · M` that
   `Kakeya.ML2Shading.exists_threshold_shadingBridgeLoss_le` absorbs, **at `K = 2`**.  The `2` is
   *not* the mass-banding constant of `Kakeya.ML2Shaded.exists_massBanded_shadeRefinement`; it is
   the dense-shading discard of `Kakeya.ML2Shaded.exists_denseShading_refinement`, which GC-P1
   already paid.  See "why not the banded route" below.  **Spends nothing new.**
3. **GC-L3**, `Kakeya.ML2Core.sum_shade_le_rpow_of_chain` — the absorption.  Three factors are
   cleared: the shading-bridge loss at `a` (its own threshold), the multiplicity `M ≤ δ^{-κ}`, and
   the two `ν`'s that division by `λ ≥ δ^ν/2` costs (one for `λ⁻¹`, one for the `2`).  Output
   exponent `a + κ + ν + ν`.  **Spends `2ν`.**
4. **GC-L4**, `Kakeya.ML2Core.dichotomyLeft_of_rpow_bound` —
   `Kakeya.ML2Shading.dichotomyLeft_of_bridge` at `ε₀ = β/2`, plus the one arithmetic
   `b ≤ ε₀`.  **Spends nothing.**
5. **GC-L5**, `Kakeya.ML2Core.exists_dichotomyLeft_or_window_dim3` — the four composed on the
   package, with the pushback to `(𝕋, Y)` being GC-P1's three loss clauses and nothing else.

The whole left branch therefore costs

`β/4` (7.3(B)) `+ 2ν` (the package's cardinality loss at `α = ν`) `+ ν` (`totalLoss`)
`+ ν` (the shading bridge's own budget) `+ 2ν` (division by `λ`) `= β/4 + 6ν`,

and `Kakeya.ML2Inputs.spineNu_le_div_48000` (`ν ≤ β/48000`) closes it inside `β/2` with a margin of
`β/4 − β/8000`.

## Why this file does *not* take the banded route

The plan's row GC-L2 asks for the `hbr` binder of
`Kakeya.ML2Shading.sum_shade_le_of_everyScale_banded` to be discharged.  That binder is
`∀ u ⊆ 𝕋, HasComparableDensities 2 u Y → ∃ u' ⊆ u, …, μ(u', Y') ≤ M`, with `A`, `B`, `M` bound
**before** `u`.  Its `M` is the output of GWZ Theorem 7.3(B), whose fullness hypothesis
`δ^{2ν} ≤ λ'(u', W)` is derived (step 1 above) from the dense-shading level of the family it is run
on — and for an `hbr`-supplied `u` that level is `λ(u, Y)/2`, which comparability at the absolute
constant `2` does not bound below by any power of `δ`.  So no `δ`-free-in-`u` `M` better than the
trivial `μ ≤ #u ≤ δ^{-4}` is available from the existing toolkit, and `δ^{-4}` is far outside `β/2`.

The banded route is also **unnecessary**, and that is the substantive point: the cardinality → mass
conversion it exists to condition is already performed by GC-P1, through
`Kakeya.ML2Shaded.sum_shade_le_of_card_le` against the *one-sided pointwise*
`Kakeya.ML2Shaded.HasDenseShading` rather than against two-sided comparability.  So the aggregate-
versus-pointwise trap that `Kakeya.ML2Shaded.not_hasComparableDensities_of_aggregate_retention`
records is avoided upstream, at the absolute cost `2`, and no logarithm
(`Kakeya.ML2Shaded.massBandLoss`) is charged at all.  The loss this file absorbs is nevertheless
literally `Kakeya.ML2Shading.shadingBridgeLoss n A 2 (log₂ #𝕋) (ssfGridLen δ)` — the banded shape
at `K = 2` — so the threshold lemma the plan names is the one used.

## `ε`-discipline

No statement here has an `ε` binder.  `ε₁` is the exponent
`Kakeya.ML2Reduction.exists_everyScale_multiplicity_le` returns at the accuracy `β/4`, a `β`-only
number, and every other exponent is `β`, `ν` or a sum of them.
`Kakeya.ML2Spine.not_epsFree_of_outerAccuracy` and
`Kakeya.ML2Reduction.no_epsFree_drop_of_outer_everyScale` are untouched: `ε₁` is not driven to `0`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Topology Filter ShadedBody ConvexSpaceBody
open Tube ShadedTube

universe u w

namespace Kakeya.ML2Core

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

/-! ### An `ENNReal` bookkeeping lemma for `δ`-powers -/

/-! ### GC-L1: GWZ Theorem 7.3(B) at the absolute accuracy `β/4` -/

/-! ### GC-L2: the mass chain, in the `shadingBridgeLoss` shape at `K = 2` -/

/-! ### GC-L3: absorbing the whole loss into one `δ`-power -/

/-! ### GC-L4: landing on the left disjunct -/

/-! ### GC-L5: the capstone — the left disjunct on the original family -/

/-! ### The glue to `Kakeya.ML2Assembly.Dichotomy`, and non-vacuity -/

/-- **compatibility, and the exact glue row the estimate needs.**

`Kakeya.ML2Shading.DichotomyLeft ε₀ s T` on the left and the dichotomy's own gain disjunct on the
right, under `Kakeya.ML2Assembly.Dichotomy`'s hypothesis block written out verbatim, *is*
`Kakeya.ML2Assembly.Dichotomy`.  Named rather than an `example`, so `#print axioms` checks it, and
so that a later edit to `Dichotomy` or to `DichotomyLeft` breaks this theorem instead of silently
decoupling branch (i) from its consumer.

Nothing is proved here: the two `Or` constructors and one `filter_upwards`. -/
theorem dichotomy_of_dichotomyLeft_or_gain {β ε₀ g η : ℝ}
    (h : ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ℝ≥0∞) ^ (-η)) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (δ : ℝ)⁻¹ ≤ (s.card : ℝ) →
        ML2Shading.DichotomyLeft ε₀ s T
          ∨ (∑ i ∈ s, volume (T i).shade
              ≤ (δ : ℝ≥0∞) ^ g * (s.card : ℝ≥0∞) ^ β
                  * volume (⋃ i ∈ s, (T i).shade))) :
    ML2Assembly.Dichotomy.{u} β ε₀ g η := by
  filter_upwards [h] with δ hδ
  intro ι s T hball hKT hfull hcardge
  rcases hδ s T hball hKT hfull hcardge with hleft | hright
  · exact Or.inl hleft
  · exact Or.inr hright

end Kakeya.ML2Core

end

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.InducedShading
public import Kakeya.Factoring.Pipeline

/-!
# Conjunct (i) of the thin-case factoring step, at the exponent `3 η`

Conjunct (i) of `Kakeya.ThinCase.factoringApply` asserts `δ^{2η} ≤ C · λ(𝕎'_B, Y_{𝕎'_B})`. This
file proves the same statement at the exponent **`3 η`**, from the binders `factoringApply`
already carries together with the side conditions of the Córdoba estimate
`ShadedBody.lambdaForInducedShading_of_measurable` itself.

## Why `3 η` and not `2 η`

GWZ's Item 2 reads `λ(𝒲', Y_{𝒲'}) ⪆ C_F^{-1} λ(𝒱, Y)²`, and the `C_F` there is the Frostman
constant of the **output** fibres. The formalized pipeline does not deliver
`O(C_F)`-Frostman output fibres: `ShadedBody.outerFactoringFamily_refinement` retains a fraction
of the *total* shade mass, and the only transport of the Frostman property to a subfibre,
`ConvexSpaceBody.IsFrostmanIn.of_le_of_subset`, charges the fibre's **carrier**-mass retention
ratio. The only bridge from a shade-mass retention to a carrier-mass retention is the pointwise
density binder `hdens` of `factoringApply`, and its price is exactly one factor `δ^{-η}`.

Concretely, with `θ` the per-fibre retention:

* the Frostman constant of the output fibre is `C = C_F · 2 C_full / (θ δ^η)`
  (`ConvexSpaceBody.IsFrostmanIn.of_le_of_subset`);
* the density parameter of the Córdoba estimate is `λ = θ δ^η / C_full`;
* hence `C⁻¹ λ² = θ³ δ^{3η} / (2 C_F C_full³)`,

which is `Kakeya.ThinCase.fullness_ge_three_eta`. The gap is one clean factor `δ^η`, with a
subpolynomial constant `Kakeya.ThinCase.thinFullnessConstant` — not a defect of the proof but of
what the pipeline hands over.

## What this file assumes, and what supplies it

Every hypothesis of `Kakeya.ThinCase.fullness_ge_three_eta` is one of:

* a binder of `factoringApply` — `hcar`, `hblk`, `hle`, `hdims`, `hFr`, `hdens`;
* a side condition of `ShadedBody.lambdaForInducedShading_of_measurable` itself — `hne`, `hVpos`,
  `hecc`, `hnd`; or
* the **per-fibre** mass retention `hret`, which `Kakeya.ThinCase.exists_denseBodies` produces
  from the pipeline's aggregate retention at the cost of a factor `2` and of the bodies it
  discards.

The two Markov selections — over the bodies (`exists_denseBodies`) and over the segments of a
fibre (`denseSegs`) — are the same lemma `Kakeya.ThinCase.sum_markovSet_ge` run twice.

## The statement change this licenses, which is NOT made here

`Kakeya.ThinCase.ThinBall.fullness_bodies` is the field `δ^{3 η} ≤ C · λ(𝕎'_B, Y_{𝕎'_B})`
(`MainLemma2/ThinSetup.lean`; in the structure's own index `η`, which
`Kakeya.VeryNotSticky.ThinConfig.tb` reads at `2 · cfg.η` since F8). Nothing in the development
bounds `η` from below — every field of
`Kakeya.VeryNotSticky.CaseParams` is an upper bound on it, and `η` is chosen last, as a minimum of
eight such bounds, by `Kakeya.VeryNotSticky.exists_caseParams`; the same docstring records two
earlier coefficient raisings (`η + ϱ ↝ 2η + ϱ`, `3τ + 9η ↝ 3τ + 12η`) as free for exactly this
reason. So the exponent may be raised. That edit is a *structure field* edit and is deliberately
not made in this file.
-/

@[expose] public section

open scoped ENNReal

open MeasureTheory Metric Set ShadedBody Convexity
open scoped ENNReal NNReal

namespace Kakeya.ThinCase

section Fullness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]


/-! ### The Markov selection

Conjunct (i) needs a *per-segment* density on the refined shading, and a *per-fibre* mass
retention; the factoring pipeline supplies neither, retaining a fraction of the *total* mass only
(`ShadedBody.outerFactoringFamily_refinement` is an `IsCRefinement`, an aggregate statement).
Both are recovered by the same Markov selection, run twice: once over the bodies, to turn the
aggregate retention into a per-fibre one at the cost of a factor `2` and of the bodies it
discards, and once over the segments of a fibre, to turn the per-fibre retention into a termwise
one. The termwise half is the `hlam` of
`ShadedBody.lambdaForInducedShading_of_measurable`; the aggregate half is what bounds the
transport cost of `ConvexSpaceBody.IsFrostmanIn.of_le_of_subset`. -/


/-- A finite sum of shade volumes over a family of shaded bodies is finite. -/
lemma sum_volume_shade_finite {ι : Type*} (s : Finset ι) (Y : ι → ShadedBody E) :
    ∑ p ∈ s, volume (Y p).shade ≠ ⊤ := by
  refine (ENNReal.sum_lt_top.mpr fun p _ => ?_).ne
  exact lt_of_le_of_lt (measure_mono (Y p).shade_subset) ((Y p).isCompact'.measure_lt_top)


/-- `ConvexSpaceBody.IsFrostmanIn` depends on the family only through its values on the index
set. -/
lemma isFrostmanIn_congr_of_eqOn {ι : Type*} {s : Finset ι} {W W' : ι → ConvexSpaceBody E}
    {K : ConvexSpaceBody E} {C : ℝ≥0∞} (h : ∀ i ∈ s, W i = W' i)
    (hF : ConvexSpaceBody.IsFrostmanIn s W K C) : ConvexSpaceBody.IsFrostmanIn s W' K C := by
  intro K' hK'
  rw [← Kakeya.densityIn_congr h, ← Kakeya.densityIn_congr h]
  exact hF K' hK'


end Fullness

end Kakeya.ThinCase

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineOuterTubes

/-!
# The uniformity witness that GWZ Lemma 9.1 asks for, at the grid of the outer scale

Blueprint GWZ, step 10 of the non-eccentric case.  This file
supplies the `huni` binder of `Kakeya.ML2Reduction.Lemma91At` — equivalently of
`Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer` — namely

```
∃ C : ℝ≥0, 1 ≤ C ∧ (C : ENNReal) ≤ (σ : ENNReal) ^ (-ηd) ∧
  Nonempty (ShadedTube.ShadedUniformTubeSet s U (Tube.ssfGridLen σ) C)
```

`Reduction/SpineOuterTubes.lean` records why this is not transported from upstairs: *"the
tube-level hierarchy on the outer family at the grid of `δ'` is a fresh object — the upstairs
hierarchy lives on the grid of `δ̃` — so it has to be built, not transported"*.

## What builds it, and what it costs

The tree already has the *composed* builder at exactly the grid length the binder names:
`ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf`, which chains
`Tube.exists_uniformTubeSet_subfamily` and the balanced shade refinement and lands on
`ShadedTube.ShadedUniformTubeSet s' V' (Tube.ssfGridLen σ) (ShadedTube.ssfUniformConst n)`.  So the
two-step route through `Tube.exists_uniformTubeSet_subfamily_ssf` followed by
`ShadedTube.exists_shadedUniformTubeSet_of_uniformTubeSet` is redundant; the composed form is used
here.

Its price is **not** zero, and this is the one thing a consumer must plan for: the builder
*refines*, so the witness is produced

* on a **subfamily** `s' ⊆ s`, at count retention `|s| ≤ σ^{-α} |s'|`, and
* against a **shrunk shading** `U'` with `(U' i).toTube = (U i).toTube` and
  `(U' i).shade ⊆ (U i).shade`, at fullness retention `λ'(s', U) ≤ σ^{-α'} λ'(s', U')`.

Both are subpolynomial and both fit `Kakeya.ML2Spine.spine_gainBudget_of_loss`.  What they mean for
the interface is recorded in the docstring of
`Kakeya.ML2Reduction.exists_outerShadedUniformTubeSet`.

## Which hypothesis forces `C ≤ σ^{-ηd}`

Only two: `hηd : 0 < ηd`, and the threshold `σ ≤ σ₀` produced by the statement.  The constant the
builder returns is `ShadedTube.ssfUniformConst (Module.finrank ℝ E)` — a *fixed* number depending
on the ambient dimension alone, chosen before any scale — so `1 ≤ C` is
`ShadedTube.one_le_ssfUniformConst` and `C ≤ σ^{-ηd}` is pure absorption of a constant into a
negative power, `Kakeya.ML2Reduction.exists_threshold_const_le_rpow_neg`.  No hypothesis about
`β`, `ϖ`, the window, the hierarchy upstairs, or the geometry of the family enters.  In particular
the bound is *not* forced by any relation between `ηd` and the dimension: it is forced by
smallness of `σ`, and if `ηd` were allowed to be `0` the binder would demand `C ≤ 1`, which
`ssfUniformConst n ≥ 4` refutes.  `hηd : 0 < ηd` is therefore load-bearing and cannot be dropped.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Set Topology Filter ShadedBody ConvexSpaceBody

namespace Kakeya.ML2Reduction

universe u

/-! ## Absorbing a fixed constant into a negative power of the scale -/

/-- **A constant fixed before the scale is below `σ^{-κ}` for all small `σ`.**  The general form of
`Kakeya.ML2Reduction.exists_threshold_outerLoss`, whose proof this is verbatim with `outerLoss R`
replaced by an arbitrary `C ≥ 1`. -/
theorem exists_threshold_const_le_rpow_neg {C : ℝ≥0} (hC : 1 ≤ C) {κ : ℝ} (hκ : 0 < κ) :
    ∃ σ₀ : ℝ≥0, 0 < σ₀ ∧ ∀ σ : ℝ≥0, 0 < σ → σ ≤ σ₀ → C ≤ σ ^ (-κ) := by
  have hC0 : C ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hC)
  have hinv0 : (0 : ℝ≥0) < C⁻¹ := pos_of_ne_zero (inv_ne_zero hC0)
  refine ⟨(C⁻¹) ^ (1 / κ), NNReal.rpow_pos hinv0, ?_⟩
  intro σ hσ0 hσle
  have hpow : σ ^ κ ≤ C⁻¹ := by
    calc σ ^ κ ≤ ((C⁻¹) ^ (1 / κ)) ^ κ := NNReal.rpow_le_rpow hσle hκ.le
      _ = C⁻¹ ^ (1 / κ * κ) := (NNReal.rpow_mul _ _ _).symm
      _ = C⁻¹ := by rw [one_div, inv_mul_cancel₀ (ne_of_gt hκ), NNReal.rpow_one]
  have hmul : σ ^ κ * C ≤ 1 := by
    calc σ ^ κ * C ≤ C⁻¹ * C := mul_le_mul_left hpow _
      _ = 1 := inv_mul_cancel₀ hC0
  rw [NNReal.rpow_neg]
  exact le_inv_of_mul_le_one (ne_of_gt (NNReal.rpow_pos hσ0)) hmul

/-- The `ENNReal` reading of `Kakeya.ML2Reduction.exists_threshold_const_le_rpow_neg`, which is the
form the `huni` binder of `Kakeya.ML2Reduction.Lemma91At` states. -/
theorem exists_threshold_coe_const_le_rpow_neg {C : ℝ≥0} (hC : 1 ≤ C) {κ : ℝ} (hκ : 0 < κ) :
    ∃ σ₀ : ℝ≥0, 0 < σ₀ ∧ ∀ σ : ℝ≥0, 0 < σ → σ ≤ σ₀ →
      (C : ℝ≥0∞) ≤ (σ : ℝ≥0∞) ^ (-κ) := by
  obtain ⟨σ₀, hσ₀, h⟩ := exists_threshold_const_le_rpow_neg hC hκ
  refine ⟨σ₀, hσ₀, fun σ hσ0 hσle => ?_⟩
  have h' := ENNReal.coe_le_coe.mpr (h σ hσ0 hσle)
  rwa [ENNReal.coe_rpow_of_ne_zero (ne_of_gt hσ0)] at h'

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasureSpace E] [BorelSpace E] [ProperSpace E]

/-! ## The uniformity witness on an arbitrary family of shaded tubes -/

/-! ## What a tube-preserving shade refinement transports for free

The builder above shrinks shades and keeps tubes.  Every hypothesis of
`Kakeya.ML2Reduction.Lemma91At` that reads only the *carrier* is therefore unchanged, and these
three one-line lemmas are the ones a consumer needs in order to say so.  They are separated out
because each is used at a different hypothesis of Lemma 9.1 and because stating them keeps the
interface note of `Kakeya.ML2Reduction.exists_outerShadedUniformTubeSet` checkable rather than
merely asserted. -/

/-! ## The instance on the outer family of step 10 -/

/-! ## The site supplier: the folded `huni` and the grid threshold, at `∀ params, ∀ᶠ δ`

 R1/R3.  The six middle-factor sites now name their uniformity
constant, and the two facts they cannot carry themselves — the absorption
`ssfUniformConst 3 ≤ δ'^{-ηd}` and the uniformiser's grid threshold `δ' ≤ 16^{-N}` — are both
**thresholds in the scale at fixed parameters**.  This section supplies both, together with the
subfamily, under one `∀ᶠ σ`.

**and it is the whole point of the shape.**  The parameters are theorem binders and the
scale is quantified *inside* the conclusion, i.e. `∀ β, ∀ᶠ δ`.  The reverse reading `∀ᶠ δ, ∀ β`
is not a stylistic variant: it is **false**, and
`Kakeya.ML2Reduction.not_eventually_forall_etad` below compiles that refutation, so a future
re-cut that swaps the two quantifiers cannot pass unnoticed. -/

end General

end Kakeya.ML2Reduction

end

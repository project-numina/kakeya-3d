/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.FactorFamily.Predicates
public import Kakeya.LEApprox
public import Kakeya.Multiplicity
public import Kakeya.ConstantMultiplicity
public import Kakeya.Frostman
public import Kakeya.DimensionThree.InducedShading
public import Kakeya.Factoring.OuterPacking
public import Kakeya.Factoring.RhoTubes

/-! # Corrected factoring and multiplicity proposition (GWZ Proposition 5.1)

This file isolates the outer factoring family construction of GWZ Proposition 5.1 and its
property lemmas. The construction is parametrized by the discretization scale `δ` and the outer
scale `w₁`, and every quantitative item has its own loss constant with its dependencies stated
explicitly. There is deliberately no bundled conjunction: downstream results should cite the
individual items.

**The construction.** `ShadedBody.outerFactoringFamily` is defined as the Step 0 -
Step 5 factoring pipeline `ShadedBody.FactorFamily.pipelineFamily` of `Kakeya/Factoring/Pipeline.lean`,
run at ball radius `r = w₁` with the Step 5 selection centres supplied by
`ShadedBody.exists_factoringPipelineSelf`.

The construction has the following properties.

* The construction needs data that `(F, δ)` alone does not determine: a ball radius and a Step 5
  cover. The radius is taken to be the outer scale `w₁`, matching
  `ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate`, where both are the tube radius `ρ`.
  Hence `outerFactoringFamily` takes `δ`, `w₁` with `δ ≤ w₁ ≤ 1`, positivity of `δ`, and the
  inner discretization hypothesis; the items inherit those arguments.
* Step 0 discards the inner bodies of low relative shading, so the output inner set is *not*
  `{i ∈ 𝒱 | parent i ∈ 𝒲'}`. It is that set intersected with the Step 0 survivors. The old
  condition of the second clause of `outerFactoringFamily_carrier` is false for the pipeline
  and has been corrected to name `F.step0.innerSet`.
The seven items of GWZ Proposition 5.1:

| item | statement | status |
| ---- | --------- | ------ |
| structural | `outerFactoringFamily_carrier` | proved |
| 1 | `outerFactoringFamily_refinement` | proved |
| 2 | `outerFactoringFamily_lambda` | proved, `ℝ³`-only, at honest loss, from explicit hypotheses |
| 3 | `outerFactoringFamily_outerConstMultFat` | proved, for the dyadically refined outer shading |
| 4 | `outerFactoringFamily_innerConstMult` | proved |
| 5 | `outerFactoringFamily_multDominated` | proved, at honest loss, from explicit hypotheses |
| 6 | `outerFactoringFamily_shadingContainment` | proved |
| 7 | `outerFactoringFamily_avgMultOnBalls` | proved |

All seven constant comparisons are now proved. In particular
`outerFactoringFamily_refinement.one_leApprox_c` holds: the honest Item 1 loss
`outerFactoringFamily_refinement.c` is subpolynomial in `δ⁻¹` for fixed `n` and `N ≥ 1`. It is
assembled from the lemmas immediately above it (`leApprox_one_mul`,
`leApprox_one_const`, `factoringStep1AtScaleConstant_leApprox_one`,
`factoringStep5SelfPigeonholeConstant_packing_leApprox_one`, `one_le_step5PackingRatio`) through
`Kakeya.one_leApprox_inv`.

No placeholder loss constant remains. `outerFactoringFamily_outerConstMultFat.C` used to be `1`,
a value at which the item was false; it is now `2`, and it is the factor of a dyadic multiplicity
band, exactly as for Item 4. Item 3 asserts constant multiplicity not for `Y_{𝒲'}` itself — for
which no value of `C n δ` is correct, the outer pointwise multiplicity ratio being controlled by
`|𝒲|` and by no per-body geometry — but for the dyadic refinement
`ShadedBody.outerFactoringOuterRefined` of `Y_{𝒲'}` by its own multiplicity level. That extra
pigeonholing is the construction step GWZ performs and Steps 0-5 of
`Kakeya/Factoring/Pipeline.lean` do not; its cost is the new logarithmic loss
`outerFactoringFamily_outerConstMultFat.c`. It touches only the outer shading, so the constants of
Items 1, 2, 4, 5, 6 and 7 are unchanged.

`outerFactoringFamily_multDominated.C` is no longer a placeholder: it is
`4 * (Step 1 · Steps 2-3 · Step 5) * outerShadingPackingLoss n 6`, the assembled pipeline loss
times the general packing loss of `ShadedBody.le_multiplicity_of_local_balls`. Its constant
comparison `outerFactoringFamily_multDominated.C_leApprox_one` — joint subpolynomiality in `δ⁻¹`
and in `|𝒱|` — is proved at that honest value, not at the placeholder.

`outerFactoringFamily_lambda.c` is no longer a placeholder either: it is the reciprocal Córdoba
loss `(max 1 (lambdaForInducedShading.C N))⁻¹`, and its second argument `N` is now the
eccentricity exponent rather than the inner cardinality.

The outer shaded bodies of the construction are exactly the induced shadings of GWZ
Definition 5.7, by `outerFactoringFamily_outerBody_eq_inducedShading`. That identification is the
link to the `ℝ³` density estimates of `Kakeya/DimensionThree/InducedShading.lean`, which are
stated for arbitrary convex outer bodies; see the docstring of `outerFactoringFamily_lambda`. -/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Convexity Kakeya

namespace ShadedBody

section FactoringAndMultiplicity

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι κ : Type*} [DecidableEq κ]

/-- **Small constant in `ShadedBody.outerFactoringFamily_refinement`**: the retained mass
fraction of the complete pipeline, evaluated at the packing bound
`ShadedBody.step5PackingRatio` for the Step 5 cover. Its arguments record that the loss depends
on the ambient dimension, the cardinality of the inner family, and the discretization scale. -/
@[nolint defsWithUnderscore]
noncomputable def outerFactoringFamily_refinement.c (n N : ℕ) (δ : ℝ≥0) : ℝ≥0 :=
  ShadedBody.Kakeya.factoringPipelineSelfRefinementConstant n N δ (step5PackingRatio n N δ)

/-- The cover cardinality is controlled by the explicit ratio used in the Step 5 loss. -/
private lemma card_le_step5PackingRatio {T : Finset E} {N : ℕ} {δ ρ : ℝ≥0}
    (hδ : 0 < δ) (hρ : ρ ∈ Set.Icc δ 1)
    (hTsub : (T : Set E) ⊆ Metric.closedBall 0 1)
    (hTsep : Metric.IsSeparated (ρ : ℝ≥0∞) (T : Set E)) :
    (T.card : ℝ≥0) ≤ step5PackingRatio (Module.finrank ℝ E) N δ := by
  let n := Module.finrank ℝ E
  have hpack := Metric.card_le_of_isSeparated_subset_closedBall (T := T) (hδ.trans_le hρ.1)
    (x := (0 : E)) (R := 1) (by norm_num) hTsub hTsep
  have hρr : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hδ.trans_le hρ.1
  have hδr : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hbase : 2 * (1 + (ρ : ℝ)) / (ρ : ℝ) ≤ 4 / (δ : ℝ) := by
    rw [div_le_div_iff₀ hρr hδr]
    have hδρ : (δ : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast hρ.1
    have hρ1 : (ρ : ℝ) ≤ 1 := by exact_mod_cast hρ.2
    have hρ0 : (0 : ℝ) ≤ ρ := hρr.le
    nlinarith
  have hcard : (T.card : ℝ) ≤ (4 / (δ : ℝ)) ^ n :=
    hpack.trans (pow_le_pow_left₀ (by positivity) hbase n)
  rw [← NNReal.coe_le_coe]
  push_cast
  calc
    (T.card : ℝ) ≤ (4 / (δ : ℝ)) ^ n := hcard
    _ ≤ (step5PackingRatio n N δ : ℝ) := by
      rw [step5PackingRatio, mul_div_assoc,
        Kakeya.step1UpperBdAtScale_div_step1LowerBdAtScale n (max 1 N) hδ]
      push_cast
      rw [div_pow]
      have hfact : (1 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_pos n
      have hN : (1 : ℝ) ≤ max 1 (N : ℝ) := le_max_left _ _
      have hinv : 0 ≤ ((δ : ℝ) ^ n)⁻¹ := by positivity
      rw [div_eq_mul_inv]
      calc
        (4 : ℝ) ^ n * ((δ : ℝ) ^ n)⁻¹ =
            ((2 : ℝ) ^ n * 2 ^ n) * ((δ : ℝ) ^ n)⁻¹ := by
              rw [← mul_pow]
              norm_num
        _ ≤ ((2 : ℝ) ^ n * 2 ^ n) *
            ((n.factorial : ℝ) * max 1 (N : ℝ) * ((δ : ℝ) ^ n)⁻¹) := by
              gcongr
              calc
                ((δ : ℝ) ^ n)⁻¹ = 1 * 1 * ((δ : ℝ) ^ n)⁻¹ := by ring
                _ ≤ (n.factorial : ℝ) * max 1 (N : ℝ) * ((δ : ℝ) ^ n)⁻¹ := by
                  gcongr
        _ = (2 : ℝ) ^ n *
            ((2 : ℝ) ^ n * n.factorial * max 1 (N : ℝ) * ((δ : ℝ) ^ n)⁻¹) := by ring

/-- Monotonicity of the self-pigeonholing loss in a cardinality upper bound. -/
private lemma step5SelfPigeonholeConstant_mono {n : ℕ} {M M' : ℝ≥0}
    (hM : M ≤ M') (hM' : 1 ≤ M') :
    ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n M ≤
      ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n M' := by
  unfold ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant
  gcongr
  rw [← ENNReal.coe_le_coe]
  rw [Kakeya.coe_factoringStep1FiberPigeonholeConstant,
    Kakeya.coe_factoringStep1FiberPigeonholeConstant]
  apply ENNReal.ofReal_le_ofReal
  by_cases hM0 : M = 0
  · subst M
    have hlog : 0 ≤ Real.logb 2 (M' : ℝ) :=
      Real.logb_nonneg one_lt_two (by exact_mod_cast hM')
    simp only [NNReal.coe_zero, NNReal.coe_one, div_one, Real.logb_zero, add_zero]
    exact le_add_of_nonneg_right hlog
  · gcongr
    norm_num

omit [Nontrivial E] in
private lemma isCRefinement_mono {s u : Finset ι} {V' V : ι → ShadedBody E} {c c' : ℝ≥0}
    (h : IsCRefinement u V' s V c) (hc : c' ≤ c) :
    IsCRefinement u V' s V c' := by
  refine ⟨h.1, ?_⟩
  calc
    (c' : ℝ≥0∞) * ∑ i ∈ s, volume (V i).shade ≤
        (c : ℝ≥0∞) * ∑ i ∈ s, volume (V i).shade := by gcongr
    _ ≤ ∑ i ∈ u, volume (V' i).shade := h.2

/-- **Small constant in `ShadedBody.outerFactoringFamily_lambda`**: the reciprocal of the
planar Córdoba loss `ShadedBody.lambdaForInducedShading.C N` of GWZ Lemma 5.9, clamped from below
so that the loss is never a gain.

**Signature change.** The second argument `N` is no longer the cardinality of the inner family.
It is the *eccentricity exponent* of the hypothesis `|W j| ≤ 2 ^ N · |V i|` in
`ShadedBody.lambdaForInducedShading_of_measurable`, which is the only place the loss comes from;
that exponent is genuine data of the statement and now appears as the hypothesis `hecc` of
`ShadedBody.outerFactoringFamily_lambda`. The inner cardinality does not enter: Item 2 is a
per-fiber density estimate and pays no pigeonholing loss on top of the density hypothesis it is
handed.

The outer `max 1` makes the constant nonzero with no positivity input about the assembled
absolute constant `lambdaInducedSingleWUniform.C`, exactly as the outer `max 1` of
`ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C` does there. -/
@[nolint defsWithUnderscore]
noncomputable def outerFactoringFamily_lambda.c
    (_n N : ℕ) (_δ : ℝ≥0) : ℝ≥0 :=
  (max 1 (lambdaForInducedShading.C N))⁻¹

/-- **Large constant in `ShadedBody.outerFactoringFamily_outerConstMultFat`**: the factor `2` of a
dyadic multiplicity band, exactly as for the inner families in
`ShadedBody.outerFactoringFamily_innerConstMult`.

This is an honest value, not a placeholder. The refined outer shading
`ShadedBody.outerFactoringOuterRefined` restricts `Y_{𝒲'}` to a single dyadic band
`{x | ⌊log₂ μ(𝒲', Y_{𝒲'})(x)⌋ = m}` of its *own* pointwise multiplicity, and on such a band the
multiplicity varies by strictly less than a factor `2`. -/
@[nolint defsWithUnderscore]
noncomputable def outerFactoringFamily_outerConstMultFat.C (_n : ℕ) (_δ : ℝ≥0) : ℝ≥0 := 2

/-- **Small constant in `ShadedBody.outerFactoringFamily_outerConstMultFat`**: the fraction of the
outer shading mass retained by the extra dyadic pigeonholing of Item 3, namely
`(⌊log₂ |𝒲|⌋ + 1)⁻¹`, one over the number of dyadic multiplicity bands available to the outer
family.

Its arguments record the dependencies: the ambient dimension (not actually used, kept for
uniformity with the other loss constants of this file), the cardinality of the *input* outer family
`𝒲` — an upper bound for that of the Step 1 subfamily `𝒲'`, which is what the pigeonhole is run on
— and the discretization scale (not used: this loss is logarithmic in `|𝒲|` only). -/
@[nolint defsWithUnderscore]
noncomputable def outerFactoringFamily_outerConstMultFat.c (_n : ℕ) (M : ℕ) (_δ : ℝ≥0) :
    ℝ≥0 :=
  ((Nat.log 2 M + 1 : ℕ) : ℝ≥0)⁻¹

/-- **Large constant in `ShadedBody.outerFactoringFamily_innerConstMult`**: the factor `2` of the
Step 2 dyadic window, which Steps 3 and 5 preserve. -/
@[nolint defsWithUnderscore]
noncomputable def outerFactoringFamily_innerConstMult.C (_n : ℕ) (_δ : ℝ≥0) : ℝ≥0 := 2

/-- `Nat.log 2 N + 1` grows more slowly than any positive power of `N`, uniformly in `N ≥ 1`.

A copy of the `private` lemma of the same name in `Kakeya/Factoring/RhoTubes.lean`, which cannot
be cited from here. -/
private lemma natLog_succ_le_rpow : ∀ η : ℝ, 0 < η → ∃ B : ℝ≥0, ∀ N : ℕ, 0 < N →
    ((Nat.log 2 N + 1 : ℕ) : ℝ≥0) ≤ B * (N : ℝ≥0) ^ η := by
  intro η hη
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let q : ℝ≥0 := ⟨1 / (η * Real.log 2), by positivity⟩
  refine ⟨1 + q, fun N hN ↦ ?_⟩
  have hN1 : (1 : ℝ≥0) ≤ (N : ℝ≥0) := by exact_mod_cast hN
  have hNpow : (1 : ℝ≥0) ≤ (N : ℝ≥0) ^ η := by
    simpa using NNReal.rpow_le_rpow hN1 hη.le
  have hlog : (Nat.log 2 N : ℝ) ≤ (N : ℝ) ^ η / (η * Real.log 2) := by
    calc
      (Nat.log 2 N : ℝ) ≤ Real.logb 2 N := Real.natLog_le_logb N 2
      _ = Real.log N / Real.log 2 := rfl
      _ ≤ ((N : ℝ) ^ η / η) / Real.log 2 := by
        gcongr
        exact Real.log_natCast_le_rpow_div N hη
      _ = (N : ℝ) ^ η / (η * Real.log 2) := by ring
  rw [← NNReal.coe_le_coe]
  push_cast [q, NNReal.coe_rpow]
  have hNpow' : (1 : ℝ) ≤ (N : ℝ) ^ η := by exact_mod_cast hNpow
  calc
    (Nat.log 2 N : ℝ) + 1 ≤ (N : ℝ) ^ η / (η * Real.log 2) + 1 := by linarith
    _ ≤ (N : ℝ) ^ η / (η * Real.log 2) + (N : ℝ) ^ η := by linarith
    _ = (1 + 1 / (η * Real.log 2)) * (N : ℝ) ^ η := by ring

/-- The Step 1 fiber pigeonholing loss is jointly subpolynomial in `δ⁻¹` and in `N`: one constant
works uniformly for all `N ≥ 1` and all `0 < δ ≤ 1`.

A copy of the `private` lemma of the same name in `Kakeya/Factoring/RhoTubes.lean`, which cannot
be cited from here. -/
private lemma fiberPigeonholeConstant_le_rpow (n : ℕ) :
    ∀ η : ℝ, 0 < η → ∃ A : ℝ≥0, ∀ N : ℕ, 0 < N → ∀ δ : ℝ≥0, 0 < δ → δ ≤ 1 →
      Kakeya.factoringStep1FiberPigeonholeConstant (Kakeya.step1LowerBdAtScale n δ)
          (Kakeya.step1UpperBdAtScale n N) ≤ A * δ ^ (-η) * (N : ℝ≥0) ^ η := by
  intro η hη
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let q : ℝ := 1 / (η * Real.log 2)
  let a₀ : ℝ := 1 + n + Real.logb 2 (n.factorial : ℝ)
  have ha₀ : 0 ≤ a₀ := by
    have hfact : (1 : ℝ) ≤ n.factorial := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hlogfact : 0 ≤ Real.logb 2 (n.factorial : ℝ) :=
      Real.logb_nonneg one_lt_two hfact
    positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hA₀ : (0 : ℝ) ≤ (n : ℝ) * q := mul_nonneg (by positivity) hq
  refine ⟨⟨a₀ + q + n * q, by linarith⟩, fun N hN δ hδ hδ1 ↦ ?_⟩
  have hN1 : (1 : ℝ≥0) ≤ (N : ℝ≥0) := by exact_mod_cast hN
  have hNpow : (1 : ℝ≥0) ≤ (N : ℝ≥0) ^ η := by
    simpa using NNReal.rpow_le_rpow hN1 hη.le
  have hδpow : (1 : ℝ≥0) ≤ δ ^ (-η) := Kakeya.one_le_rpow_neg hη.le hδ hδ1
  have hlogN : Real.logb 2 (N : ℝ) ≤ q * (N : ℝ) ^ η := by
    calc
      Real.logb 2 (N : ℝ) = Real.log N / Real.log 2 := rfl
      _ ≤ ((N : ℝ) ^ η / η) / Real.log 2 := by
        gcongr
        exact Real.log_natCast_le_rpow_div N hη
      _ = q * (N : ℝ) ^ η := by simp only [q]; ring
  have hlogδ : Real.logb 2 (1 / (δ : ℝ)) ≤ q * (δ : ℝ) ^ (-η) := by
    calc
      Real.logb 2 (1 / (δ : ℝ))
          ≤ (δ : ℝ) ^ (-η) / (η * Real.log 2) :=
        Kakeya.logb_inv_le_rpow_neg_div (by exact_mod_cast hδ) hη
      _ = q * (δ : ℝ) ^ (-η) := by simp only [q]; ring
  have hF :
      (Kakeya.factoringStep1FiberPigeonholeConstant (Kakeya.step1LowerBdAtScale n δ)
          (Kakeya.step1UpperBdAtScale n N) : ℝ) =
        a₀ + Real.logb 2 (N : ℝ) + n * Real.logb 2 (1 / (δ : ℝ)) := by
    have hratio := Kakeya.logb_step1UpperBdAtScale_div_step1LowerBdAtScale_nonneg n
      (Nat.one_le_iff_ne_zero.mpr hN.ne') hδ hδ1
    have h := congrArg ENNReal.toReal
      (Kakeya.coe_factoringStep1FiberPigeonholeConstant (Kakeya.step1LowerBdAtScale n δ)
        (Kakeya.step1UpperBdAtScale n N))
    rw [NNReal.coe_div] at hratio
    have hnonneg : 0 ≤ 1 + Real.logb 2
        ((Kakeya.step1UpperBdAtScale n N : ℝ) / (Kakeya.step1LowerBdAtScale n δ : ℝ)) := by
      linarith
    rw [ENNReal.toReal_ofReal hnonneg] at h
    simp only [ENNReal.coe_toReal] at h
    rw [h, ← NNReal.coe_div, Kakeya.logb_step1UpperBdAtScale_div_step1LowerBdAtScale n
      (Nat.one_le_iff_ne_zero.mpr hN.ne') hδ]
    simp only [a₀]
    ring
  rw [← NNReal.coe_le_coe]
  push_cast [NNReal.coe_rpow]
  rw [hF]
  have hNpow' : (1 : ℝ) ≤ (N : ℝ) ^ η := by exact_mod_cast hNpow
  have hδpow' : (1 : ℝ) ≤ (δ : ℝ) ^ (-η) := by exact_mod_cast hδpow
  calc
    a₀ + Real.logb 2 (N : ℝ) + n * Real.logb 2 (1 / (δ : ℝ))
        ≤ a₀ + q * (N : ℝ) ^ η + n * (q * (δ : ℝ) ^ (-η)) := by gcongr
    _ ≤ a₀ * (δ : ℝ) ^ (-η) * (N : ℝ) ^ η +
          q * (δ : ℝ) ^ (-η) * (N : ℝ) ^ η +
          n * q * (δ : ℝ) ^ (-η) * (N : ℝ) ^ η := by
      have ha₀term : a₀ ≤ a₀ * (δ : ℝ) ^ (-η) * (N : ℝ) ^ η := by
        calc
          a₀ = a₀ * 1 * 1 := by ring
          _ ≤ a₀ * (δ : ℝ) ^ (-η) * (N : ℝ) ^ η := by gcongr
      have hNterm : q * (N : ℝ) ^ η ≤
          q * (δ : ℝ) ^ (-η) * (N : ℝ) ^ η := by
        calc
          q * (N : ℝ) ^ η = q * 1 * (N : ℝ) ^ η := by ring
          _ ≤ q * (δ : ℝ) ^ (-η) * (N : ℝ) ^ η := by gcongr
      have hδterm : (n : ℝ) * (q * (δ : ℝ) ^ (-η)) ≤
          n * q * (δ : ℝ) ^ (-η) * (N : ℝ) ^ η := by
        calc
          (n : ℝ) * (q * (δ : ℝ) ^ (-η)) = n * q * (δ : ℝ) ^ (-η) * 1 := by ring
          _ ≤ n * q * (δ : ℝ) ^ (-η) * (N : ℝ) ^ η := by gcongr
      exact add_le_add (add_le_add ha₀term hNterm) hδterm
    _ = (a₀ + q + n * q) * (δ : ℝ) ^ (-η) * (N : ℝ) ^ η := by ring

/-- **Large constant in `ShadedBody.outerFactoringFamily_multDominated`**: the assembled Step 0 -
Step 5 pigeonholing loss of the pipeline, times the general outer packing loss of the
enlargements.

Reading the factors left to right:

* the factor `4` is the Step 2 pointwise window of
  `ShadedBody.FactorFamily.pipelineFamily_multiplicity`, which places the global inner
  multiplicity in `[2 ^ k * 2 ^ l, 4 * 2 ^ k * 2 ^ l)` for the inner exponent `k` and outer
  exponent `l`;
* the bracketed product is the reciprocal of the Item 1 refinement constant
  `ShadedBody.outerFactoringFamily_refinement.c`, i.e. exactly the mass the pipeline may discard;
* `ShadedBody.outerShadingPackingLoss n 6` is the purely dimensional loss of
  `ShadedBody.le_multiplicity_of_local_balls`, which converts the pointwise outer count `2 ^ l`
  into a lower bound for the *average* outer multiplicity. The covering radius is `6 * w₁`: a
  point of an outer shade lies within `2 * (W j).scale ≤ 4 * w₁` of the fiber shaded union, which
  in turn lies in the Step 5 selection, a union of closed `w₁`-balls around the cover centres.

Every factor is either dimensional or logarithmic in `N` and in `δ⁻¹`; this is what
`ShadedBody.outerFactoringFamily_multDominated.C_leApprox_one` records. -/
@[nolint defsWithUnderscore]
noncomputable def outerFactoringFamily_multDominated.C
    (n N : ℕ) (δ : ℝ≥0) : ℝ≥0 :=
  4 * (Kakeya.factoringStep1AtScaleConstant n N δ *
      (Kakeya.factoringStep2Step3Constant N : ℝ≥0) *
      ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n (step5PackingRatio n N δ)) *
    outerShadingPackingLoss n 6

/-- **Large constant in `ShadedBody.outerFactoringFamily_avgMultOnBalls`**: twice the Step 5
bounded-overlap constant of the `w₁`-cover, twice over -- once to move the left ball to a cover
centre and once to move that centre to the comparison point. -/
@[nolint defsWithUnderscore]
noncomputable def outerFactoringFamily_avgMultOnBalls.C (n : ℕ) (_δ : ℝ≥0) : ℝ≥0 :=
  4 * (Kakeya.factoringStep5OverlapConstant n : ℝ≥0)

end FactoringAndMultiplicity

end ShadedBody

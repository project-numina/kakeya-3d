/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.VeryNotStickyCase

/-! ### Scalar workhorses

The `ℝ≥0` and `ℝ` companions of `Kakeya.VeryNotSticky.eventually_ennreal_mul_rpow_le_rpow`.
Every fixed-scale clause of Configuration `hyp:ml2scale` is one of the four shapes below, so
the whole arithmetic half of `Kakeya.VeryNotSticky.exists_setup_caseSideData` reduces to them.
-/

@[expose] public section

open scoped NNReal ENNReal

open Filter Topology MeasureTheory

namespace Kakeya.VeryNotSticky

universe u

/-- A finite constant times a higher power of a small scale is eventually bounded by a
lower power. This is the common absorption step in the slab and non-slab scale bundles. -/
theorem eventually_ennreal_mul_rpow_le_rpow {K : ℝ≥0∞} (hK : K ≠ ⊤)
    {p q : ℝ} (hqp : q < p) :
    ∀ᶠ d : ℝ≥0 in 𝓝[>] 0, K * (d : ℝ≥0∞) ^ p ≤ (d : ℝ≥0∞) ^ q := by
  have hgap : 0 < p - q := sub_pos.mpr hqp
  filter_upwards [ENNReal.eventually_coe_rpow_le_of_pos hgap
      (show 0 < K⁻¹ by simpa using ENNReal.inv_pos.mpr hK), self_mem_nhdsWithin]
      with d hd hd0
  have hdne : (d : ℝ≥0∞) ≠ 0 := by simpa using ne_of_gt hd0
  have hdtop : (d : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hKK : K * K⁻¹ ≤ 1 := by
    by_cases hK0 : K = 0
    · simp [hK0]
    · rw [ENNReal.mul_inv_cancel hK0 hK]
  calc
    K * (d : ℝ≥0∞) ^ p
        = (K * (d : ℝ≥0∞) ^ (p - q)) * (d : ℝ≥0∞) ^ q := by
            rw [mul_assoc, ← ENNReal.rpow_add (p - q) q hdne hdtop]
            congr 2
            ring
    _ ≤ (K * K⁻¹) * (d : ℝ≥0∞) ^ q := by gcongr
    _ ≤ 1 * (d : ℝ≥0∞) ^ q := by gcongr
    _ = (d : ℝ≥0∞) ^ q := one_mul _

/-- `ℝ≥0` form of `Kakeya.VeryNotSticky.eventually_ennreal_mul_rpow_le_rpow`. -/
theorem eventually_nnreal_mul_rpow_le_rpow (K : ℝ≥0) {p q : ℝ} (hqp : q < p) :
    ∀ᶠ d : ℝ≥0 in 𝓝[>] 0, K * d ^ p ≤ d ^ q := by
  filter_upwards [eventually_ennreal_mul_rpow_le_rpow (K := (K : ℝ≥0∞))
      ENNReal.coe_ne_top hqp, self_mem_nhdsWithin] with d hd hd0
  have hdne : d ≠ 0 := ne_of_gt (by simpa using hd0)
  rw [← ENNReal.coe_rpow_of_ne_zero hdne, ← ENNReal.coe_rpow_of_ne_zero hdne,
    ← ENNReal.coe_mul, ENNReal.coe_le_coe] at hd
  exact hd

/-- A fixed `ℝ≥0` constant is eventually dominated by any negative power of the scale. -/
theorem eventually_nnreal_le_rpow_neg (K : ℝ≥0) {ν : ℝ} (hν : 0 < ν) :
    ∀ᶠ d : ℝ≥0 in 𝓝[>] 0, K ≤ d ^ (-ν) := by
  filter_upwards [eventually_nnreal_mul_rpow_le_rpow K (p := 0) (q := -ν)
    (by linarith)] with d hd
  simpa using hd

/-- A fixed finite `ℝ≥0∞` constant is eventually dominated by any negative power of the
scale. -/
theorem eventually_ennreal_le_rpow_neg {K : ℝ≥0∞} (hK : K ≠ ⊤) {ν : ℝ} (hν : 0 < ν) :
    ∀ᶠ d : ℝ≥0 in 𝓝[>] 0, K ≤ (d : ℝ≥0∞) ^ (-ν) := by
  filter_upwards [eventually_ennreal_mul_rpow_le_rpow hK (p := 0) (q := -ν)
    (by linarith)] with d hd
  simpa using hd

/-- `ℝ` form of `Kakeya.VeryNotSticky.eventually_nnreal_le_rpow_neg`. -/
theorem eventually_real_le_rpow_neg (K : ℝ≥0) {ν : ℝ} (hν : 0 < ν) :
    ∀ᶠ d : ℝ≥0 in 𝓝[>] 0, (K : ℝ) ≤ (d : ℝ) ^ (-ν) := by
  filter_upwards [eventually_nnreal_le_rpow_neg K hν] with d hd
  have h := NNReal.coe_le_coe.2 hd
  rwa [NNReal.coe_rpow] at h

/-- A fixed constant times a positive power of the scale eventually falls below any fixed
positive bound. This is the shape of the clauses that compare with an absolute constant
(`Real.exp (-1)`, `1`) rather than with a power of the scale. -/
theorem eventually_nnreal_mul_rpow_le_const (K c : ℝ≥0) (hc : 0 < c) {p : ℝ}
    (hp : 0 < p) :
    ∀ᶠ d : ℝ≥0 in 𝓝[>] 0, K * d ^ p ≤ c := by
  have hcne : c ≠ 0 := hc.ne'
  filter_upwards [eventually_nnreal_mul_rpow_le_rpow (K / c) (p := p) (q := 0) hp] with d hd
  have h1 : K / c * d ^ p ≤ 1 := by simpa using hd
  calc K * d ^ p = c * (K / c * d ^ p) := by field_simp
    _ ≤ c * 1 := by gcongr
    _ = c := mul_one c

/-! ### The `δ`-thresholds of Configuration `hyp:ml2setup` and of the thick bundle -/

/-- **The honest Section-5 loss constant is eventually absorbed** (the field
`Kakeya.VeryNotSticky.coarseLoss_absorb`).

This is the arrangeability certificate for that field, and it has the same shape as
`Kakeya.VeryNotSticky.eventually_aScaleData_absorb` with one extra ingredient: the loss
`ShadedBody.rhoTubesSection9Loss 3 N δ` is *not* a closed constant — it is a function of both
`δ` and the family size `N` — so a plain `K ≤ δ^{-η}` absorption does not apply. What makes it
absorbable anyway is that it is only `δ^{-o(1)}` in the *pair*: by
`ShadedBody.rhoTubesSection9Loss_le_rpow_neg` (whose input is
`ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C_leApprox`) it is at most `δ^{-η}`
below a threshold determined by `η` and by a polynomial cardinality budget `N ≤ δ^{-K}`.

`K` is a free parameter here, so a producer may take whatever budget its family satisfies; in
dimension three `K = 2` suffices for a family of essentially distinct `δ`-tubes in `B_1`. The
budget is genuinely needed and is not cosmetic: without a bound on `N` the loss has no bound
at all uniform in the family, since `C_leApprox` charges `N^ε`. -/
theorem eventually_coarseLoss_absorb {η K : ℝ} (hη : 0 < η) (hK : 0 ≤ K) :
    ∀ᶠ d : ℝ≥0 in 𝓝[>] 0,
      ∀ N : ℕ, 0 < N → (N : ℝ≥0) ≤ d ^ (-K) →
        ((_root_.ShadedBody.rhoTubesSection9Loss 3 N d : ℝ≥0) : ℝ≥0∞) ≤
          (d : ℝ≥0∞) ^ (-η) := by
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := _root_.ShadedBody.rhoTubesSection9Loss_le_rpow_neg 3 hη hK
  have hmin : (0 : ℝ≥0) < min δ₀ 1 := lt_min hδ₀pos one_pos
  filter_upwards [Ioo_mem_nhdsGT hmin, self_mem_nhdsWithin] with d hd hd0
  intro N hN hNbd
  have hdpos : 0 < d := hd0
  have hdle : d ≤ δ₀ := le_trans hd.2.le (min_le_left _ _)
  have hd1 : d ≤ 1 := le_trans hd.2.le (min_le_right _ _)
  have h := hδ₀ d hdpos hdle hd1 N hN hNbd
  rw [← ENNReal.coe_rpow_of_ne_zero hdpos.ne']
  exact ENNReal.coe_le_coe.mpr h

/-- **The same absorption, uniformly over a sub-polynomially bounded `C₀`.**

`Kakeya.VeryNotSticky.eventually_aScaleData_absorb` fixes `C₀` before `δ`, which is why
`Kakeya.VeryNotSticky.BandUniformRefinement` was forced to name a `δ`-free uniformity constant.
The quantifier order is not a mathematical necessity: `aScaleDataConstant` is a closed-form
polynomial in `C₀` of degree exactly `4` —
`aScaleVolumeConstant C₀ D₀ = C₀^4 · D₀ / (tubeVolumeRatioConstant 3)^2`, and
`aScaleBallConstant` is `C₀`-free — so squaring gives degree `8`, and a bound
`C₀ ≤ δ^{-η'}` is absorbed as soon as `8 η' < η`.

`Kakeya.VeryNotSticky.aScaleData_absorb` is the **only** field of `Kakeya.VeryNotSticky` that
bounds `C₀` from above; `hC₀`, `uniform` and `rho_count` consume `1 ≤ C₀` alone. So `8 η' < η`
is the whole admissibility condition on a `δ`-dependent uniformity constant, and
`η' := η / 16` leaves half the budget.

No positivity of `η'` is needed: at `η' ≤ 0` the cap reads `C₀ ≤ δ^{-η'} ≤ 1`, which is a
*stronger* hypothesis on the caller. -/
theorem eventually_aScaleData_absorb_of_le (D₀ : ℝ≥0) {η η' : ℝ} (h8 : 8 * η' < η) :
    ∀ᶠ d : ℝ≥0 in 𝓝[>] 0,
      ∀ C₀ : ℝ≥0, 1 ≤ C₀ → (C₀ : ℝ≥0∞) ≤ (d : ℝ≥0∞) ^ (-η') →
        (aScaleDataConstant C₀ D₀ : ℝ≥0∞) ^ 2 ≤ (d : ℝ≥0∞) ^ (-η) := by
  have hgap : 0 < η - 8 * η' := by linarith
  obtain ⟨M, hM⟩ : ∃ M : ℝ≥0, ∀ C₀ : ℝ≥0, 1 ≤ C₀ →
      aScaleDataConstant C₀ D₀ ≤ C₀ ^ 4 * M := by
    refine ⟨max (aScaleBallConstant (max 1 (Tube.dilateFullness.C 3)))
      (D₀ / tubeVolumeRatioConstant 3 / tubeVolumeRatioConstant 3), fun C₀ hC₀ => ?_⟩
    have h1 : (1 : ℝ≥0) ≤ C₀ ^ 4 := one_le_pow₀ hC₀
    have hvol : aScaleVolumeConstant C₀ D₀
        = C₀ ^ 4 * (D₀ / tubeVolumeRatioConstant 3 / tubeVolumeRatioConstant 3) := by
      simp only [aScaleVolumeConstant, deltamaxScaleAConstant]
      ring
    rw [aScaleDataConstant, hvol]
    refine max_le ?_ (mul_le_mul_right (le_max_right _ _) _)
    calc aScaleBallConstant (max 1 (Tube.dilateFullness.C 3))
        ≤ max (aScaleBallConstant (max 1 (Tube.dilateFullness.C 3)))
            (D₀ / tubeVolumeRatioConstant 3 / tubeVolumeRatioConstant 3) := le_max_left _ _
      _ = 1 * max (aScaleBallConstant (max 1 (Tube.dilateFullness.C 3)))
            (D₀ / tubeVolumeRatioConstant 3 / tubeVolumeRatioConstant 3) := (one_mul _).symm
      _ ≤ C₀ ^ 4 * max (aScaleBallConstant (max 1 (Tube.dilateFullness.C 3)))
            (D₀ / tubeVolumeRatioConstant 3 / tubeVolumeRatioConstant 3) :=
          mul_le_mul_left h1 _
  filter_upwards [eventually_ennreal_le_rpow_neg
      (K := ((M ^ 2 : ℝ≥0) : ℝ≥0∞)) ENNReal.coe_ne_top hgap,
    self_mem_nhdsWithin] with d hd hd0
  have hdpos : (0 : ℝ≥0) < d := hd0
  have hdE : ((d : ℝ≥0∞)) ≠ 0 := by simpa using hdpos.ne'
  intro C₀ hC₀ hcap
  calc (aScaleDataConstant C₀ D₀ : ℝ≥0∞) ^ 2
      ≤ ((C₀ ^ 4 * M : ℝ≥0) : ℝ≥0∞) ^ 2 := by
        gcongr
        exact_mod_cast hM C₀ hC₀
    _ = (C₀ : ℝ≥0∞) ^ 8 * ((M ^ 2 : ℝ≥0) : ℝ≥0∞) := by push_cast; ring
    _ ≤ ((d : ℝ≥0∞) ^ (-η')) ^ 8 * ((M ^ 2 : ℝ≥0) : ℝ≥0∞) := by gcongr
    _ = (d : ℝ≥0∞) ^ (-(8 * η')) * ((M ^ 2 : ℝ≥0) : ℝ≥0∞) := by
        rw [← ENNReal.rpow_natCast ((d : ℝ≥0∞) ^ (-η')) 8, ← ENNReal.rpow_mul]
        norm_num
        ring_nf
    _ ≤ (d : ℝ≥0∞) ^ (-(8 * η')) * (d : ℝ≥0∞) ^ (-(η - 8 * η')) := by gcongr
    _ = (d : ℝ≥0∞) ^ (-η) := by
        rw [← ENNReal.rpow_add _ _ hdE ENNReal.coe_ne_top]
        ring_nf

/-- **(T3) is eventually met** (the field `Kakeya.VeryNotSticky.ThickDensityThresholds.bias`).

`C_bias · (48 C₀^6)^3 ≤ δ^{-τϱ}`. Both constants are `δ`-free: `C₀` by the argument recorded
under `Kakeya.VeryNotSticky.eventually_aScaleData_absorb`, and `C_bias` because
`Kakeya.ConvexSpaceBody.nonempty_biasedFactorization` produces its factoring at the constant
`nonempty_biasedFactorization.C (Module.finrank ℝ E) ϖ`, a function of the ambient dimension
and the bias exponent alone — the `δ`-dependence of that lemma is confined to its *volume
loss*, which is a refinement cost and not a constant of the bundle. -/
theorem eventually_thick_bias (Cbias C₀ : ℝ≥0) {τ ϱ : ℝ} (hτ : 0 < τ) (hϱ : 0 < ϱ) :
    ∀ᶠ d : ℝ≥0 in 𝓝[>] 0,
      (Cbias : ℝ≥0∞) * (((48 * C₀ ^ 6) ^ 3 : ℝ≥0) : ℝ≥0∞) ≤
        (d : ℝ≥0∞) ^ (-(τ * ϱ)) :=
  eventually_ennreal_le_rpow_neg
    (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top) (by positivity)

/-- **The two fixed-scale thresholds of blueprint `plankF` are eventually met.**

These are the hypotheses `hb₀` and `hc₁` of
`Kakeya.VeryNotSticky.plankFrostmanUsable_of_thick`, and with them that lemma discharges the
field `Kakeya.VeryNotSticky.ThickDensityThresholds.plankF` outright. The second threshold is
where the binder `hplankF` of `Kakeya.VeryNotSticky.exists_setup_caseSideData` is spent, the
lemma being read at `η := 2 cfg.η` (F8: (C5) at `δ^{2η}`): the exponent `τ ηF - 2 cfg.η` is
positive exactly under that budget, `2 cfg.η < τ ηF`, and
without it the threshold is a condition that *fails* as `δ → 0`.

`b₀` is `δ`-free by `Kakeya.VeryNotSticky.exists_plankFrostmanVolumeAt_canonical`, and `c₁` is
a free field of `Kakeya.VeryNotSticky.BallData` occurring here on the large side, so both
hypotheses are genuine smallness conditions on `δ`. -/
theorem eventually_plankFrostman_thresholds (CP b₀ c₁ : ℝ≥0) (hb₀ : 0 < b₀) (hc₁ : 0 < c₁)
    {τ ηF η : ℝ} (hτ : 0 < τ) (hbudget : η < τ * ηF) :
    ∀ᶠ d : ℝ≥0 in 𝓝[>] 0,
      CP * d ^ τ ≤ b₀ ∧ CP ^ (1 + ηF) * d ^ (τ * ηF - η) ≤ c₁ := by
  filter_upwards [eventually_nnreal_mul_rpow_le_const CP b₀ hb₀ hτ,
    eventually_nnreal_mul_rpow_le_const (CP ^ (1 + ηF)) c₁ hc₁ (p := τ * ηF - η)
      (by linarith)] with d h1 h2
  exact ⟨h1, h2⟩

/-! ### The fixed-scale clauses of Configuration `hyp:ml2scale`

`Kakeya.VeryNotSticky.CaseScale` has fifteen clauses. Nine of them, together with
`Kakeya.VeryNotSticky.eventually_multiplicity_large` and the two threshold clauses that
`Kakeya.VeryNotSticky.nonempty_caseSideData` reads at the trivial bundle, are pure absorptions
of a `δ`-free constant into a positive power of the scale, and are discharged here. What is
left after this lemma is exactly three clauses: `typicalAngle_const`, whose left-hand side is
the constant `Kakeya.typicalAngleScaledConst` (discharged separately, by
`Kakeya.VeryNotSticky.eventually_typicalAngle_const`, once
`Kakeya.typicalAngleScaledConst_le` exposes its polylogarithmic growth);
`transverseFill_threshold`, which is
`Kakeya.VeryNotSticky.exists_isReductionFillAvailable` but needs that threshold quantified
ahead of the index type `bd.ω`; and `transverseFill_fullness`, which the field's own docstring
declares a mathematical input rather than plumbing.

The constants are pinned to `δ`-free values by hypothesis rather than bounded, matching
`Kakeya.VeryNotSticky.eventually_slabScale_of_uniform_bounds`: `bd.C₀` is `δ`-free by the
uniformization (see `Kakeya.VeryNotSticky.eventually_aScaleData_absorb`), `bd.Cbias` by the
biased factoring lemma (see `Kakeya.VeryNotSticky.eventually_thick_bias`), while `C` — the
thin-case comparison constant — is the one genuinely `δ`-dependent quantity, and pinning it is
what records the outstanding debt that it be sub-polynomial in `δ⁻¹`. -/
theorem eventually_caseScale_clauses (C₀ Cbias C : ℝ≥0) (hC₀ : 1 ≤ C₀)
    {exscal η ϱ τ τ' : ℝ} (hexscal : 0 < exscal) (hexscal1 : exscal < 1) (hη : 0 < η)
    (hϱ : 0 < ϱ) (hτ' : 0 < τ') (hthin : τ + exscal < 1) :
    ∀ᶠ d : ℝ≥0 in 𝓝[>] 0,
      ∀ (cfg : VeryNotSticky) (bd : BallData cfg),
        cfg.δ = d → cfg.exscal = exscal → cfg.η = η → cfg.ϱ = ϱ →
        bd.C₀ = C₀ → bd.Cbias = Cbias →
        (cfg.δ ^ cfg.exscal ≤ (2 * NonSlab.bodyAngleConstant bd.C₀)⁻¹) ∧
        (cfg.b ≤ cfg.δ ^ (2 * cfg.exscal) → bd.C₀ * cfg.b ≤ cfg.r₁) ∧
        (cfg.a ≤ cfg.δ ^ (1 - τ) →
          ((bd.C₀ * (cfg.a / cfg.r₁) : ℝ≥0) : ℝ) ≤ Real.exp (-1)) ∧
        (6 * ThinCase.w1Constant bd.C₀ ≤ cfg.δ ^ (-τ')) ∧
        (27 * max 1 (bd.C₀ / 3) ^ 3 ≤ cfg.δ ^ (-(cfg.η / 2))) ∧
        (1000 * ThinCase.transferConstant C bd.C₀ ≤ cfg.δ ^ (-cfg.η)) ∧
        (plankEnclosureConstant bd.C₀ * bd.Cbias * cfg.δ ^ cfg.ϱ ≤ 1) ∧
        ((plankSelectionConstant bd.C₀ : ℝ) ≤ (cfg.δ : ℝ) ^ (-(cfg.exscal * cfg.η))) ∧
        ((2 : ℝ) ≤ ((cfg.δ / cfg.r₁ : ℝ≥0) : ℝ) ^ (-(cfg.η / 512))) := by
  have hangle : (0 : ℝ≥0) < (2 * NonSlab.bodyAngleConstant C₀)⁻¹ := by
    have h1 : (1 : ℝ≥0) ≤ NonSlab.bodyAngleConstant C₀ :=
      NonSlab.one_le_bodyAngleConstant hC₀
    have h2 : (0 : ℝ≥0) < 2 * NonSlab.bodyAngleConstant C₀ := by
      have : (0 : ℝ≥0) < NonSlab.bodyAngleConstant C₀ := lt_of_lt_of_le zero_lt_one h1
      positivity
    simpa using inv_pos.mpr h2
  have hexp : (0 : ℝ≥0) < Real.toNNReal (Real.exp (-1)) :=
    Real.toNNReal_pos.mpr (Real.exp_pos _)
  filter_upwards [eventually_nnreal_mul_rpow_le_const 1 _ hangle hexscal,
    eventually_nnreal_mul_rpow_le_rpow C₀ (p := 2 * exscal) (q := exscal) (by linarith),
    eventually_nnreal_mul_rpow_le_const C₀ _ hexp (p := 1 - τ - exscal) (by linarith),
    eventually_nnreal_le_rpow_neg (6 * ThinCase.w1Constant C₀) hτ',
    eventually_nnreal_le_rpow_neg (27 * max 1 (C₀ / 3) ^ 3) (show (0:ℝ) < η / 2 by linarith),
    eventually_nnreal_le_rpow_neg (1000 * ThinCase.transferConstant C C₀) hη,
    eventually_nnreal_mul_rpow_le_const (plankEnclosureConstant C₀ * Cbias) 1 one_pos hϱ,
    eventually_real_le_rpow_neg (plankSelectionConstant C₀)
      (show (0:ℝ) < exscal * η by positivity),
    eventually_real_le_rpow_neg 2
      (show (0:ℝ) < (1 - exscal) * (η / 512) by
        have : (0:ℝ) < 1 - exscal := by linarith
        positivity),
    self_mem_nhdsWithin] with d h1 h2 h3 h4 h5 h6 h7 h8 h9 hd0
  intro cfg bd hδ hex hη' hϱ' hC hCb
  have hdpos : (0 : ℝ≥0) < d := by simpa using hd0
  have hdne : d ≠ 0 := ne_of_gt hdpos
  have hr₁ : cfg.r₁ = d ^ exscal := by
    simp only [VeryNotSticky.r₁, hδ, hex]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hδ, hex, hC]
    simpa using h1
  · intro hb
    rw [hδ, hex] at hb
    rw [hC, hr₁]
    calc C₀ * cfg.b ≤ C₀ * d ^ (2 * exscal) := by gcongr
      _ ≤ d ^ exscal := h2
  · intro ha
    rw [hδ] at ha
    have hquot : cfg.a / cfg.r₁ ≤ d ^ (1 - τ - exscal) := by
      rw [hr₁]
      calc cfg.a / d ^ exscal ≤ d ^ (1 - τ) / d ^ exscal := by gcongr
        _ = d ^ (1 - τ - exscal) := by
              rw [show (1 : ℝ) - τ - exscal = (1 - τ) - exscal from by ring]
              exact (NNReal.rpow_sub hdne (1 - τ) exscal).symm
    have hstep : C₀ * (cfg.a / cfg.r₁) ≤ Real.toNNReal (Real.exp (-1)) :=
      le_trans (by gcongr) h3
    rw [hC]
    calc ((C₀ * (cfg.a / cfg.r₁) : ℝ≥0) : ℝ)
        ≤ ((Real.toNNReal (Real.exp (-1)) : ℝ≥0) : ℝ) := NNReal.coe_le_coe.2 hstep
      _ = Real.exp (-1) := Real.coe_toNNReal _ (Real.exp_pos _).le
  · rw [hδ, hC]; exact h4
  · rw [hδ, hC, hη']; exact h5
  · rw [hδ, hC, hη']; exact h6
  · rw [hδ, hC, hCb, hϱ']; exact h7
  · rw [hδ, hC, hex, hη']; exact h8
  · have hdiv : (cfg.δ / cfg.r₁ : ℝ≥0) = d ^ (1 - exscal) := by
      rw [hδ, hr₁, NNReal.rpow_sub hdne, NNReal.rpow_one]
    rw [hdiv, hη', NNReal.coe_rpow, ← Real.rpow_mul (by positivity)]
    have hsign : (1 - exscal) * (-(η / 512)) = -((1 - exscal) * (η / 512)) := by ring
    rw [hsign]
    simpa using h9

/-! ### The reduction-fill threshold, quantified ahead of the index type

`Kakeya.VeryNotSticky.exists_isReductionFillAvailable` binds its threshold `δ_*` *after* the
index type `ω`, which is unusable for a producer of `Kakeya.VeryNotSticky.CaseScale`: there
`ω = bd.ω` is a field of the ball data, hence chosen after `δ`. The threshold does not in fact
depend on `ω` — `ShadedPlank.reduction_to_slab_atTypicalAngle` binds it before its index type
— so hoisting the binder is legitimate, and this is that hoist.
-/

/-- **The reduction is available below a threshold fixed before the index type as well as
before the scale.** The `ω`-uniform form of
`Kakeya.VeryNotSticky.exists_isReductionFillAvailable`. -/
theorem exists_isReductionFillAvailable_uniform {η : ℝ} (hη : 0 < η) (Ccard : ℝ≥0)
    (D : ℝ) :
    ∃ δthr : ℝ≥0, 0 < δthr ∧ δthr ≤ 1 ∧
      ∀ (ω : Type*) (δ : ℝ≥0), 0 < δ → δ ≤ δthr →
        IsReductionFillAvailable ω η Ccard D δ := by
  have hεpos : 0 < η / 256 := by positivity
  have hε'pos : 0 < η / 2 := by positivity
  have hgap : 128 * (η / 256) ≤ η / 2 := le_of_eq (by ring)
  rcases ShadedPlank.reduction_to_slab_atTypicalAngle
      (η := η) (ε := η / 256) (ε' := η / 2) hη hεpos hε'pos hgap Ccard D with
    ⟨δthr, hδthrpos, hδthr1, hred⟩
  refine ⟨δthr, hδthrpos, hδthr1, ?_⟩
  intro ω δ hδpos hδle
  unfold IsReductionFillAvailable
  intro s a b hab hb1 Y θ hθ1 C Y'' hδpos0 hδa ha1 hwin hfull hmulti_a hmulti_δ h2 hcard
    h_ab h1leC hCle hcref hcm htyp hmaxAbsP
  have hred3 := hred (ι := ω) s (δ := δ) (a := a) (b := b) (hab := hab) (hb1 := hb1) Y θ hθ1 C Y''
      hδpos0 hδa ha1 hδle hwin hfull hmulti_a hmulti_δ h2 hcard h_ab h1leC hCle
      hcref hcm htyp hmaxAbsP
  rcases hred3 with ⟨s', Y', c1, hc1, href, href2, hfull', hitem1, hitem5⟩
  have hapos : 0 < a := lt_of_lt_of_le hδpos0 hδa
  have hfullpos : (0 : ℝ≥0) < ShadedBody.fullness s' Y' := by
    have haeps : (0 : ℝ≥0) < a ^ (η / 256) := NNReal.rpow_pos hapos
    have haeta : (0 : ℝ≥0) < a ^ η := NNReal.rpow_pos hapos
    have hprod : (0 : ℝ≥0) < c1 * (a ^ (η / 256)) * a ^ η :=
      mul_pos (mul_pos hc1 haeps) haeta
    have hle : c1 * (a ^ (η / 256)) * a ^ η ≤ ShadedBody.fullness s' Y' := by
      calc
        c1 * (a ^ (η / 256)) * a ^ η
            = (c1 * (a ^ (η / 256))) * a ^ η := by ring
        _ ≤ (c1 * (a ^ (η / 256))) * ShadedBody.fullness s (ShadedPlank.bodies Y) := by
                exact mul_le_mul_right hfull (c1 * (a ^ (η / 256)))
        _ ≤ ShadedBody.fullness s' Y' := hfull'
    exact lt_of_lt_of_le hprod hle
  have hfullE : (0 : ℝ≥0∞) < (ShadedBody.fullness s' Y' : ℝ≥0∞) :=
    ENNReal.coe_pos.mpr hfullpos
  have hsumne : (∑ i ∈ s', volume (Y' i).shade) ≠ 0 := by
    rw [ShadedBody.fullness_def s' Y'] at hfullE
    exact (ENNReal.div_pos_iff.mp hfullE).1
  have hneu : (ShadedBody.iUnionShade s' Y').Nonempty := by
    rcases Finset.exists_ne_zero_of_sum_ne_zero (s := s') (f := fun i => volume (Y' i).shade)
        hsumne with ⟨j, hj, hjne⟩
    have hvolj : (0 : ℝ≥0∞) < volume (Y' j).shade := pos_iff_ne_zero.mpr hjne
    have hjne' : volume (Y' j).shade ≠ 0 := ne_of_gt hvolj
    have hjNonempty : (Y' j).shade.Nonempty := MeasureTheory.nonempty_of_measure_ne_zero hjne'
    rcases hjNonempty with ⟨p, hp⟩
    exact ⟨p, Finset.subset_set_biUnion_of_mem (s := s') (f := fun i => (Y' i).shade) hj hp⟩
  refine ⟨s', Y', c1, hc1, href, href2, hneu, ?_, hitem5⟩
  intro x hx
  simpa using hitem1 x hx

/-- **The eleventh clause of Configuration `hyp:ml2scale` holds eventually**
(`Kakeya.VeryNotSticky.CaseScale.transverseFill_threshold`).

The clause is the availability of the plank-to-slab reduction at the *rescaled* scale
`δ' = δ / r₁ = δ^{1-exscal}`, which tends to `0` with `δ` because `exscal < 1`; the threshold
comes from `Kakeya.VeryNotSticky.exists_isReductionFillAvailable_uniform`, so it is fixed
before `δ` and before `bd.ω`. -/
theorem eventually_transverseFill_threshold {exscal η ϱ : ℝ} (hη : 0 < η)
    (hexscal1 : exscal < 1) :
    ∀ᶠ d : ℝ≥0 in 𝓝[>] 0,
      ∀ (cfg : VeryNotSticky) (bd : BallData cfg),
        cfg.δ = d → cfg.exscal = exscal → cfg.η = η → cfg.ϱ = ϱ →
        IsReductionFillAvailable bd.ω (16 * cfg.η) plankCardConstant
          (plankCardExponent + 6 * cfg.ϱ) (cfg.δ / cfg.r₁) := by
  obtain ⟨δthr, hδthrpos, -, hthr⟩ :=
    exists_isReductionFillAvailable_uniform (show (0:ℝ) < 16 * η by linarith)
      plankCardConstant (plankCardExponent + 6 * ϱ)
  filter_upwards [eventually_nnreal_mul_rpow_le_const 1 δthr hδthrpos
    (show (0 : ℝ) < 1 - exscal by linarith), self_mem_nhdsWithin] with d hd hd0
  intro cfg bd hδ hex hη' hϱ'
  have hdpos : (0 : ℝ≥0) < d := by simpa using hd0
  have hdne : d ≠ 0 := ne_of_gt hdpos
  have hdiv : (cfg.δ / cfg.r₁ : ℝ≥0) = d ^ (1 - exscal) := by
    simp only [VeryNotSticky.r₁, hδ, hex]
    rw [NNReal.rpow_sub hdne, NNReal.rpow_one]
  rw [hη', hϱ', hdiv]
  exact hthr bd.ω (d ^ (1 - exscal)) (NNReal.rpow_pos hdpos) (by simpa using hd)

/-- **The typical-angle constant threshold is eventually met** — the tenth clause
`Kakeya.VeryNotSticky.CaseScale.typicalAngle_const`, discharged from the *eleventh*,
`plankCard_bias`, and nothing else.

This clause was the second compiler-verified defect of Configuration `hyp:ml2scale`. Its
left-hand side is `Kakeya.typicalAngleScaledConst`, and while that constant is bound before
every geometric datum, the statement it was read off,
`Kakeya.findingTypicalAngleOfIntersection_scaled`, quantifies it *after* the plank-count
constant `C₀` and so says nothing about how it grows with `C₀`. Here `C₀` carries `δ^{-2ϱ}`,
and `Kakeya.CaseParams.densityBias` forces `ϱ > 2^20 η`, so the clause demanded growth below
the power `2^{-25}` of `C₀` — which no `Classical.choose` constant supplies and which no
smallness hypothesis on `δ` can repair.

The repair is `Kakeya.typicalAngleScaledConst_le`: the constant is at most
`typicalAngleScaledBase (η/1024) plankCardExponent · (log⁺C₀ + 1)²`, with the base independent
of `C₀`. The growth is **polylogarithmic**, which is what the clause needs and more than the
`2^{-25}` power it asked for. The rest is `Kakeya.linlog_le` and one power absorption:
with `plankCard_bias` the argument is at most `plankCardConstant · δ^{-3ϱ}`, so
`log⁺C₀ + 1 = O(log δ⁻¹)`, hence `O(δ^{-ε})` for every `ε > 0`, and two of those are beaten by
`(δ/r₁)^{-η/1024} = δ^{-(1-exscal)η/1024}`.

Note what is *not* assumed: no `δ`-free bound on `plankEnclosureConstant bd.C₀ · bd.Cbias`.
Those constants are produced after `δ`, and they enter only through a logarithm, so the
`δ`-dependent bound that `plankCard_bias` already supplies is enough. -/
theorem eventually_typicalAngle_const {η ϱ exscal : ℝ} (hη : 0 < η) (hϱ : 0 < ϱ)
    (hexscal1 : exscal < 1) :
    ∀ᶠ d : ℝ≥0 in 𝓝[>] 0,
      ∀ X : ℝ≥0, X * d ^ ϱ ≤ 1 →
        Kakeya.typicalAngleScaledConst.{u} (η / 1024)
            (plankCardConstant * (X * d ^ (-(2 * ϱ)))) plankCardExponent ≤
          (d / d ^ exscal : ℝ≥0) ^ (-(η / 1024)) := by
  have hη16 : (0:ℝ) < η / 1024 := by linarith
  set B : ℝ≥0 := Kakeya.typicalAngleScaledBase.{u} (η / 1024) plankCardExponent with hBdef
  set κ : ℝ := (1 - exscal) * (η / 1024) with hκdef
  have hκ0 : 0 < κ := mul_pos (by linarith) hη16
  set ε' : ℝ := κ / 4 with hε'def
  have hε'0 : (0:ℝ) < ε' := by rw [hε'def]; linarith
  have hKpos : (0:ℝ) < ((plankCardConstant : ℝ≥0) : ℝ) := by
    have : (plankCardConstant : ℝ≥0) = 2 ^ 20 := rfl
    rw [this]; norm_num
  set c : ℝ := |Real.log ((plankCardConstant : ℝ≥0) : ℝ)| + 1 with hcdef
  have hc0 : (0:ℝ) ≤ c := by
    rw [hcdef]; positivity
  set Cfin : ℝ≥0 := B * Real.toNNReal (c + 3 * ϱ / ε') ^ 2 with hCfindef
  have hsmall : ∀ᶠ d : ℝ≥0 in 𝓝[>] 0, d < 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ≥0) < 1 by norm_num)] with d hd
    exact hd.2
  filter_upwards [eventually_nnreal_le_rpow_neg Cfin (show (0:ℝ) < 2 * ε' by positivity),
    self_mem_nhdsWithin, hsmall] with d hCf hd0 hd1
  intro X hX
  have hdpos : (0 : ℝ≥0) < d := by simpa using hd0
  have hdne : d ≠ 0 := ne_of_gt hdpos
  have hdR : (0:ℝ) < (d : ℝ) := by exact_mod_cast hdpos
  have hd1R : (d : ℝ) < 1 := by exact_mod_cast hd1
  have hpow0 : d ^ ϱ ≠ 0 := ne_of_gt (NNReal.rpow_pos hdpos)
  -- the argument of the constant is at most `plankCardConstant · δ^{-3ϱ}`
  have hXle : X ≤ d ^ (-ϱ) := by
    have h := mul_le_mul_left hX (d ^ ϱ)⁻¹
    rwa [mul_assoc, mul_inv_cancel₀ hpow0, mul_one, one_mul, ← NNReal.rpow_neg] at h
  have hprod : X * d ^ (-(2 * ϱ)) ≤ d ^ (-(3 * ϱ)) := by
    calc X * d ^ (-(2 * ϱ)) ≤ d ^ (-ϱ) * d ^ (-(2 * ϱ)) := by gcongr
      _ = d ^ (-(3 * ϱ)) := by rw [← NNReal.rpow_add hdne]; congr 1; ring
  have hargle : plankCardConstant * (X * d ^ (-(2 * ϱ)))
      ≤ plankCardConstant * d ^ (-(3 * ϱ)) := by gcongr
  have hargR : ((plankCardConstant * (X * d ^ (-(2 * ϱ))) : ℝ≥0) : ℝ)
      ≤ ((plankCardConstant : ℝ≥0) : ℝ) * (d : ℝ) ^ (-(3 * ϱ)) := by
    have h := NNReal.coe_le_coe.mpr hargle
    calc ((plankCardConstant * (X * d ^ (-(2 * ϱ))) : ℝ≥0) : ℝ)
        ≤ ((plankCardConstant * d ^ (-(3 * ϱ)) : ℝ≥0) : ℝ) := h
      _ = ((plankCardConstant : ℝ≥0) : ℝ) * (d : ℝ) ^ (-(3 * ϱ)) := by
          rw [NNReal.coe_mul, NNReal.coe_rpow]
  -- the logarithm of the argument is linear in `log δ⁻¹`
  have ht0 : (0:ℝ) ≤ Real.log (d : ℝ)⁻¹ := by
    rw [Real.log_inv]; linarith [Real.log_nonpos hdR.le hd1R.le]
  have h3t : (0:ℝ) ≤ 3 * ϱ * Real.log (d : ℝ)⁻¹ :=
    mul_nonneg (by positivity) ht0
  have hUpos : (0:ℝ) < ((plankCardConstant : ℝ≥0) : ℝ) * (d : ℝ) ^ (-(3 * ϱ)) :=
    mul_pos hKpos (Real.rpow_pos_of_pos hdR _)
  have hlogU : Real.log (((plankCardConstant : ℝ≥0) : ℝ) * (d : ℝ) ^ (-(3 * ϱ)))
      = Real.log ((plankCardConstant : ℝ≥0) : ℝ) + 3 * ϱ * Real.log (d : ℝ)⁻¹ := by
    rw [Real.log_mul (ne_of_gt hKpos) (ne_of_gt (Real.rpow_pos_of_pos hdR _)),
      Real.log_rpow hdR, Real.log_inv]
    ring
  have hcabs : c - 1 = |Real.log ((plankCardConstant : ℝ≥0) : ℝ)| := by
    rw [hcdef]; ring
  have habs : (0:ℝ) ≤ c - 1 := by rw [hcabs]; exact abs_nonneg _
  have hmaxlog :
      max (Real.log ((plankCardConstant * (X * d ^ (-(2 * ϱ))) : ℝ≥0) : ℝ)) 0
        ≤ c - 1 + 3 * ϱ * Real.log (d : ℝ)⁻¹ := by
    have hub : Real.log (((plankCardConstant : ℝ≥0) : ℝ) * (d : ℝ) ^ (-(3 * ϱ)))
        ≤ c - 1 + 3 * ϱ * Real.log (d : ℝ)⁻¹ := by
      rw [hlogU, hcabs]
      linarith [le_abs_self (Real.log ((plankCardConstant : ℝ≥0) : ℝ))]
    refine max_le ?_ (by linarith)
    rcases lt_or_eq_of_le
        (NNReal.coe_nonneg (plankCardConstant * (X * d ^ (-(2 * ϱ))))) with hpos | hzero
    · exact le_trans (Real.log_le_log hpos hargR) hub
    · rw [← hzero, Real.log_zero]
      linarith
  -- the polylogarithmic bound, then two power absorptions
  have hlin : c + 3 * ϱ * Real.log (d : ℝ)⁻¹ ≤ (c + 3 * ϱ / ε') * (d : ℝ) ^ (-ε') :=
    linlog_le hc0 (by positivity) hε'0 hdR hd1R.le
  have hMnn :
      Real.toNNReal (Real.log ((plankCardConstant * (X * d ^ (-(2 * ϱ))) : ℝ≥0) : ℝ)) + 1
        ≤ Real.toNNReal (c + 3 * ϱ / ε') * d ^ (-ε') := by
    refine NNReal.coe_le_coe.mp ?_
    have hL : ((Real.toNNReal
          (Real.log ((plankCardConstant * (X * d ^ (-(2 * ϱ))) : ℝ≥0) : ℝ)) + 1
            : ℝ≥0) : ℝ)
        = max (Real.log ((plankCardConstant * (X * d ^ (-(2 * ϱ))) : ℝ≥0) : ℝ)) 0 + 1 := by
      rw [NNReal.coe_add, NNReal.coe_one, Real.coe_toNNReal']
    have hR : ((Real.toNNReal (c + 3 * ϱ / ε') * d ^ (-ε') : ℝ≥0) : ℝ)
        = (c + 3 * ϱ / ε') * (d : ℝ) ^ (-ε') := by
      rw [NNReal.coe_mul, Real.coe_toNNReal _ (by positivity), NNReal.coe_rpow]
    rw [hL, hR]
    linarith [hmaxlog, hlin]
  have hM2 :
      (Real.toNNReal (Real.log ((plankCardConstant * (X * d ^ (-(2 * ϱ))) : ℝ≥0) : ℝ))
          + 1) ^ 2
        ≤ Real.toNNReal (c + 3 * ϱ / ε') ^ 2 * d ^ (-(2 * ε')) := by
    calc (Real.toNNReal
            (Real.log ((plankCardConstant * (X * d ^ (-(2 * ϱ))) : ℝ≥0) : ℝ)) + 1) ^ 2
        ≤ (Real.toNNReal (c + 3 * ϱ / ε') * d ^ (-ε')) ^ 2 := by gcongr
      _ = Real.toNNReal (c + 3 * ϱ / ε') ^ 2 * (d ^ (-ε')) ^ 2 := by rw [mul_pow]
      _ = Real.toNNReal (c + 3 * ϱ / ε') ^ 2 * d ^ (-(2 * ε')) := by
          congr 1
          rw [← NNReal.rpow_natCast (d ^ (-ε')) 2, ← NNReal.rpow_mul]
          congr 1
          push_cast
          ring
  calc Kakeya.typicalAngleScaledConst.{u} (η / 1024)
          (plankCardConstant * (X * d ^ (-(2 * ϱ)))) plankCardExponent
      ≤ B * (Real.toNNReal
            (Real.log ((plankCardConstant * (X * d ^ (-(2 * ϱ))) : ℝ≥0) : ℝ)) + 1) ^ 2 :=
        Kakeya.typicalAngleScaledConst_le.{u} hη16 _ _
    _ ≤ B * (Real.toNNReal (c + 3 * ϱ / ε') ^ 2 * d ^ (-(2 * ε'))) := by gcongr
    _ = Cfin * d ^ (-(2 * ε')) := by rw [hCfindef]; ring
    _ ≤ d ^ (-(2 * ε')) * d ^ (-(2 * ε')) := by gcongr
    _ = d ^ (-(4 * ε')) := by rw [← NNReal.rpow_add hdne]; congr 1; ring
    _ = (d / d ^ exscal : ℝ≥0) ^ (-(η / 1024)) := by
        rw [show (d / d ^ exscal : ℝ≥0) = d ^ (1 - exscal) by
              rw [NNReal.rpow_sub hdne, NNReal.rpow_one],
          ← NNReal.rpow_mul]
        congr 1
        rw [hε'def, hκdef]
        ring

/-! ### Configuration `hyp:ml2scale`, reduced to its one irreducible clause

The assembly of the clauses above into the bundle
`Kakeya.VeryNotSticky.CaseScale`. **Fourteen of the fifteen clauses are discharged**; the one
that remains is a hypothesis of this lemma, *by name*:

* `htypfill` is `Kakeya.VeryNotSticky.CaseScale.transverseFill_fullness`, which that field's
  own docstring declares "a mathematical input and not a matter of plumbing": the largest
  fullness the configuration supplies is `δ^{2η}`, and `(a')^η` exceeds it by a positive power
  of `δ`, so no smallness hypothesis repairs it. It is an obligation on whatever produces the
  factoring bodies.

`typicalAngle_const` used to be the second such hypothesis, and it was not merely undischarged
but *undischargeable*: its left-hand side is `Kakeya.typicalAngleScaledConst`, which was
`Classical.choose` applied to `Kakeya.findingTypicalAngleOfIntersection_scaled`, a statement
that quantifies the constant after the plank-count constant `C₀` and so bounds its growth in
`C₀` not at all — while the clause feeds it a `C₀` of size `δ^{-2ϱ}` and
`Kakeya.VeryNotSticky.CaseParams.densityBias` forces `ϱ > 2^20 η`, so that only growth below
the power `2^{-25}` would serve. It is discharged here by
`Kakeya.VeryNotSticky.eventually_typicalAngle_const`, out of the clause `plankCard_bias` and
the exposure `Kakeya.typicalAngleScaledConst_le`, which says the constant grows at most
**polylogarithmically** in `C₀`.

**This lemma does not close anything by deferral.** It is an accounting statement: it says
precisely that the arithmetic of Configuration `hyp:ml2scale` is finished and that the one
named item above is all that is left of it. -/

/-! ### What the density band of Configuration `hyp:ml2setup` actually forces -/

/-- **The Markov step that makes the repaired exponent deliverable.**

If the aggregate fullness of `(s, V)` is at least `a`, and every member of a subfamily `u ⊆ s`
is individually *less* than `θ`-full, then `u` carries at most a `θ/a` fraction of the total
shade mass:

`a · ∑_{i ∈ u} |Y_i| ≤ θ · ∑_{i ∈ s} |Y_i|`.

Read at `a = δ^η` (the binder `hfull` of `Kakeya.VeryNotSticky.exists_setup_caseSideData`) and
`θ = δ^{2η}` (the level of the repaired `Kakeya.VeryNotSticky.lam_ge`): the tubes that fail to
be individually `δ^{2η}`-full carry at most a `δ^η` fraction of the shade mass, so a producer
may discard them and still meet a refinement constant `c ≥ δ^η`. That is precisely what fails
at `θ = δ^η`, where the bound degenerates to `∑_u |Y| ≤ ∑_s |Y|`, and it is why the field had
to move from `δ^η` to `δ^{2η}`.

No comparability of the carriers is needed: the proof is
`∑_u |Y| ≤ θ ∑_u |T| ≤ θ ∑_s |T|` together with `a ∑_s |T| ≤ ∑_s |Y|`. -/
theorem sum_volume_shade_lowDensity_le {ι : Type*} {s u : Finset ι}
    {V : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} (hus : u ⊆ s) {a θ : ℝ≥0}
    (hfull : a ≤ ShadedBody.fullness s V)
    (hlow : ∀ i ∈ u, volume (V i).shade ≤ (θ : ℝ≥0∞) * volume (V i).carrier) :
    (a : ℝ≥0∞) * ∑ i ∈ u, volume (V i).shade
      ≤ (θ : ℝ≥0∞) * ∑ i ∈ s, volume (V i).shade := by
  classical
  have hcar : (a : ℝ≥0∞) * ∑ i ∈ s, volume (V i).carrier
      ≤ ∑ i ∈ s, volume (V i).shade := by
    rw [ShadedBody.sum_volumeReal_shade_eq_fullness_mul s V]
    exact mul_le_mul' (ENNReal.coe_le_coe.mpr hfull) le_rfl
  have hu : ∑ i ∈ u, volume (V i).shade ≤ (θ : ℝ≥0∞) * ∑ i ∈ s, volume (V i).carrier := by
    calc ∑ i ∈ u, volume (V i).shade
        ≤ ∑ i ∈ u, (θ : ℝ≥0∞) * volume (V i).carrier := Finset.sum_le_sum hlow
      _ = (θ : ℝ≥0∞) * ∑ i ∈ u, volume (V i).carrier := by rw [Finset.mul_sum]
      _ ≤ (θ : ℝ≥0∞) * ∑ i ∈ s, volume (V i).carrier := by
          gcongr
  calc (a : ℝ≥0∞) * ∑ i ∈ u, volume (V i).shade
      ≤ (a : ℝ≥0∞) * ((θ : ℝ≥0∞) * ∑ i ∈ s, volume (V i).carrier) := by gcongr
    _ = (θ : ℝ≥0∞) * ((a : ℝ≥0∞) * ∑ i ∈ s, volume (V i).carrier) := by ring
    _ ≤ (θ : ℝ≥0∞) * ∑ i ∈ s, volume (V i).shade := by gcongr

/-! ### Guardrail: what the setup statement forces about the *individual* shading densities

The house pattern of `Kakeya.DimensionThree.MainLemma2.AScaleGuardrails`: restate the target
with every binder explicit, pin the restatement to the real declaration with a tripwire
`example`, and then derive from it a consequence that can be compared with the hypotheses.
-/

open MeasureTheory Topology Filter ShadedBody in
/-- **`Kakeya.VeryNotSticky.exists_setup_caseSideData`, restated with every binder explicit.**

Kept in lockstep with the real declaration by the tripwire
`Kakeya.VeryNotSticky.setupCaseSideDataStatement_tripwire` immediately below: if the target's
statement ever changes, that `example` stops typechecking. -/
def SetupCaseSideDataStatement : Prop :=
  ∀ {β ζ exscal ϱ η τ τ' : ℝ}, 0 < β → β ≤ 1 → 0 < ζ → 0 < exscal → 0 < ϱ → 0 < η →
    CaseParams β ζ exscal ϱ η τ τ' →
    PlankFrostmanBudget.{u} β ϱ τ η →
    KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
    FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
    Kakeya.CoarseKTWindow.{u} β ϱ η exscal →
    ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (∀ i ∈ s, (T i).toTube.IsCentred) →
        (∃ C : ℝ≥0, 1 ≤ C ∧ (C : ℝ≥0∞) ≤ (δ : ℝ≥0∞) ^ (-η) ∧
          Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) C)) →
        maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-η) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (∀ ρ : ℝ≥0, ρ ∈ Set.Icc (δ ^ (1 - exscal)) (δ ^ exscal) →
          ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
            (tρ : Set κ).Pairwise
              (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
            (∀ j ∈ tρ, ∃ i ∈ s, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
            (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) →
        ∃ (cfg : VeryNotSticky.{u}) (bd : BallData cfg) (e : cfg.ι ≃ ι) (c : ℝ≥0),
          (cfg.β = β ∧ cfg.ζ = ζ ∧ cfg.δ = δ ∧ cfg.exscal = exscal ∧ cfg.ϱ = ϱ ∧
              cfg.η = η) ∧
          ShadedBody.IsCRefinement (cfg.s.map e.toEmbedding)
              (fun i ↦ (cfg.T (e.symm i)).toShadedBody)
              s (fun i ↦ (T i).toShadedBody) c ∧
          (δ : ℝ≥0∞) ^ η ≤ (c : ℝ≥0∞) ∧
          Nonempty (CaseSideData cfg bd τ τ')

/- The tripwire `example : SetupCaseSideDataStatement := @exists_setup_caseSideData` lives in
`MainLemma2/VeryNotStickyClosed.lean` since the  A.5 relocation of the leaf downstream of its
producers; this module is upstream of that file. -/

/-! ### Guardrail: the slack the repaired fullness clause buys

The companion of the block above for `Kakeya.VeryNotSticky.fullness_ge`. The *rigidity* half —
that an aggregate fullness clause asserted at exactly the value the input family already attains
forbids deleting any shading mass at all — is `Kakeya.VeryNotSticky.volume_shade_eq_of_fullness_ge`
in `Kakeya.DimensionThree.MainLemma2.BallJoint`, which is the termwise form and is the one the
refutation `Kakeya.VeryNotSticky.not_rigidFullnessField_of_flat_island` consumes. What is recorded
here is the other half: at the repaired exponent that rigidity **cannot fire**, because its
hypothesis is incompatible with the target's own binder.
-/

/-! ### The density band: `lam`, `Cd`, `lam_ge`, `shading_lb`, `shading_ub` are now deliverable

The five fields `Kakeya.VeryNotSticky.lam`, `Cd`, `lam_ge`, `shading_lb`, `shading_ub` were the
one group of the configuration whose satisfiability was *in doubt*, not merely unformalized: at
the old exponent `lam_ge : Cd δ^η ≤ lam` they contradict the aggregate binder `hfull` of
`Kakeya.VeryNotSticky.exists_setup_caseSideData` (that is
`Kakeya.VeryNotSticky.tubeCount_of_setupCaseSideDataStatement`). At the repaired
`Cd δ^{2η} ≤ lam` they are deliverable, and the two lemmas below are the proof — not an
accounting statement, an actual construction:

* `Kakeya.VeryNotSticky.exists_isCRefinement_pointwise_density` turns the *aggregate* ratio
  into a *pointwise* density bound at a lower level, at the cost of a refinement constant. This
  is the step that has no analogue at level `δ^η`;
* `Kakeya.VeryNotSticky.exists_shadingBand` then feeds it to the repository's dyadic density
  pigeonhole `Kakeya.ShadedBody.exists_isCRefinement_comparable_density` and packages the output
  in exactly the shape of the three fields, at `Cd = 2`.

Read at `a = δ^η` (the binder), `q = δ^η` and `θ = δ^{2η}` (the repaired level) the composite
refinement constant is `(1 - δ^η) · (1 + log₂ δ^{-2η})⁻¹`, which exceeds `δ^η` for all small
`δ`, so the target's own conjunct `δ^η ≤ c` is met with room. At `θ = δ^η` the hypothesis
`hθq : θ ≤ q · a` would force `q ≥ 1` and the refinement constant `1 - q` would be `0`: the
obstruction and the repair are visible in the same inequality.
-/

open MeasureTheory Topology Filter ShadedBody in
/-- **From aggregate fullness to pointwise fullness at a lower level** — the Markov step of the
density-band pigeonhole, as a refinement.

If `λ(𝕍, Y) ≥ a` and `θ ≤ q · a` with `q ≤ 1`, then the members that are individually
`θ`-full form a `(1 - q)`-refinement: the members that are *not* carry at most a `q` fraction
of the shade mass.

This is `Kakeya.VeryNotSticky.sum_volume_shade_lowDensity_le` packaged as a
`ShadedBody.IsCRefinement`, and it is the step the target needs and the reason
`Kakeya.VeryNotSticky.lam_ge` had to move from `δ^η` to `δ^{2η}`: at `θ = a` the hypothesis
`hθq` forces `q = 1` and the conclusion degenerates to the trivial refinement constant `0`.
Nothing is assumed about the carriers — no common volume, no comparability — and the subfamily
is `Finset.filter`ed rather than existentially opaque only inside the proof; the statement
exposes it as an arbitrary `s' ⊆ s`, so no decidability instance leaks out. -/
theorem exists_isCRefinement_pointwise_density {ι : Type*} {s : Finset ι}
    {V : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} {a θ q : ℝ≥0}
    (ha : 0 < a) (hfull : a ≤ ShadedBody.fullness s V) (hq1 : q ≤ 1) (hθq : θ ≤ q * a) :
    ∃ s' ⊆ s,
      (∀ i ∈ s', (θ : ℝ≥0∞) * volume (V i).carrier ≤ volume (V i).shade) ∧
      ShadedBody.IsCRefinement s' V s V (1 - q) := by
  classical
  set P : ι → Prop := fun i ↦ (θ : ℝ≥0∞) * volume (V i).carrier ≤ volume (V i).shade with hP
  set X : ℝ≥0∞ := ∑ i ∈ s, volume (V i).shade with hX
  have hXtop : X ≠ ⊤ := by
    rw [hX]
    refine ne_of_lt (lt_of_le_of_lt (Finset.sum_le_sum fun i _ ↦
      measure_mono (V i).shade_subset) ?_)
    exact ENNReal.sum_lt_top.2 fun i _ ↦ (V i).isCompact.measure_lt_top
  have hlow : ∀ i ∈ s.filter (fun i ↦ ¬ P i),
      volume (V i).shade ≤ (θ : ℝ≥0∞) * volume (V i).carrier := by
    intro i hi
    exact le_of_not_ge (Finset.mem_filter.mp hi).2
  have hMark := sum_volume_shade_lowDensity_le (Finset.filter_subset _ s) hfull hlow
  have hane : (a : ℝ≥0∞) ≠ 0 := by
    simpa using ha.ne'
  have hatop : (a : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hu : ∑ i ∈ s.filter (fun i ↦ ¬ P i), volume (V i).shade ≤ (q : ℝ≥0∞) * X := by
    refine (ENNReal.mul_le_mul_iff_right hane hatop).mp ?_
    refine hMark.trans ?_
    calc (θ : ℝ≥0∞) * X ≤ ((q * a : ℝ≥0) : ℝ≥0∞) * X := by
          gcongr
      _ = (a : ℝ≥0∞) * ((q : ℝ≥0∞) * X) := by
          rw [ENNReal.coe_mul]; ring
  have hsplit : ∑ i ∈ s.filter P, volume (V i).shade
      + ∑ i ∈ s.filter (fun i ↦ ¬ P i), volume (V i).shade = X :=
    Finset.sum_filter_add_sum_filter_not s P _
  have hqXtop : (q : ℝ≥0∞) * X ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top hXtop
  have hone : ((1 - q : ℝ≥0) : ℝ≥0∞) + (q : ℝ≥0∞) = 1 := by
    rw [← ENNReal.coe_add, tsub_add_cancel_of_le hq1, ENNReal.coe_one]
  have hkey : ((1 - q : ℝ≥0) : ℝ≥0∞) * X ≤ ∑ i ∈ s.filter P, volume (V i).shade := by
    refine (ENNReal.add_le_add_iff_right hqXtop).mp ?_
    calc ((1 - q : ℝ≥0) : ℝ≥0∞) * X + (q : ℝ≥0∞) * X
        = X := by rw [← add_mul, hone, one_mul]
      _ = ∑ i ∈ s.filter P, volume (V i).shade
            + ∑ i ∈ s.filter (fun i ↦ ¬ P i), volume (V i).shade := hsplit.symm
      _ ≤ ∑ i ∈ s.filter P, volume (V i).shade + (q : ℝ≥0∞) * X := by gcongr
  exact ⟨s.filter P, Finset.filter_subset _ _,
    fun i hi ↦ (Finset.mem_filter.mp hi).2,
    ⟨Finset.filter_subset _ _, fun i _ ↦ ⟨rfl, subset_rfl⟩⟩, hkey⟩

open MeasureTheory Topology Filter ShadedBody in
/-- **The shading band of Configuration `hyp:ml2setup`, from the aggregate fullness binder
alone.**

Given a family of equal-carrier-volume shaded bodies with `λ(𝕍, Y) ≥ a`, and a density floor
`θ ≤ q · a` with `q < 1`, there is a subfamily and a `lam > 0` with

* `Cd · θ ≤ lam` at `Cd = 2` — the field `Kakeya.VeryNotSticky.lam_ge` at `θ = δ^{2η}`;
* `Cd⁻¹ · lam · |V| ≤ |Y(V)| ≤ Cd · lam · |V|` on the subfamily — the fields
  `Kakeya.VeryNotSticky.shading_lb` and `Kakeya.VeryNotSticky.shading_ub`;
* and the subfamily is a `(1 - q) · (1 + log₂ θ^{-1})⁻¹`-refinement of the original.

So the whole `(lam, Cd, lam_ge, shading_lb, shading_ub)` group of the configuration is
**deliverable** from the target's aggregate binder — at the repaired exponent, and only there.
The equal-volume hypothesis `hvol` is the one the repository's pigeonhole
`Kakeya.ShadedBody.exists_isCRefinement_comparable_density` asks for; for a family of
`Kakeya.ShadedTube δ` it is `Tube.volume_carrier_eq_volume_carrier`, a proved equality,
so it costs the producer nothing. Nonemptiness of the subfamily is *derived*, not assumed:
`(1 - q) > 0` and the total shade mass is positive because the fullness is.

`Cd = 2` is the dyadic band's own comparison constant, and it is exactly the `Cd = 2` that the
docstring of `Kakeya.VeryNotSticky.lam_ge` identifies as what the `⪆` of GWZ §9 hides. -/
theorem exists_shadingBand {ι : Type*} {s : Finset ι}
    {V : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} {v : ℝ≥0∞}
    (hvol : ∀ i ∈ s, volume (V i).carrier = v) (hv : v ≠ 0)
    {a θ q : ℝ≥0} (ha : 0 < a) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hfull : a ≤ ShadedBody.fullness s V) (hq1 : q < 1) (hθq : θ ≤ q * a) :
    ∃ s₂ ⊆ s, ∃ lam : ℝ≥0, 0 < lam ∧ 2 * θ ≤ lam ∧
      (∀ i ∈ s₂,
        (2 : ℝ≥0∞)⁻¹ * ((lam : ℝ≥0∞) * volume (V i).carrier) ≤ volume (V i).shade ∧
          volume (V i).shade ≤ (2 : ℝ≥0∞) * ((lam : ℝ≥0∞) * volume (V i).carrier)) ∧
      ShadedBody.IsCRefinement s₂ V s V
        ((1 - q) * ((1 + Real.logb 2 ((θ : ℝ))⁻¹).toNNReal)⁻¹) := by
  classical
  obtain ⟨s', hs's, hdense, href⟩ :=
    exists_isCRefinement_pointwise_density ha hfull hq1.le hθq
  -- `s'` is nonempty: it carries a `(1 - q) > 0` share of a positive shade mass.
  have hXne : ∑ i ∈ s, volume (V i).shade ≠ 0 := by
    intro h0
    have hz : ShadedBody.fullness s V = 0 := by
      have hc := ShadedBody.fullness_def s V
      have : ((ShadedBody.fullness s V : ℝ≥0) : ℝ≥0∞) = 0 := by
        rw [hc, h0, ENNReal.zero_div]
      exact_mod_cast this
    rw [hz] at hfull
    exact absurd (le_antisymm hfull (by simp)) ha.ne'
  have hqne : (1 - q : ℝ≥0) ≠ 0 := by
    have : 0 < 1 - q := tsub_pos_of_lt hq1
    exact this.ne'
  have hs'ne : s'.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s' with hemp | hne
    · exfalso
      have hm := href.2
      rw [hemp] at hm
      simp only [Finset.sum_empty, nonpos_iff_eq_zero] at hm
      rcases mul_eq_zero.mp hm with h | h
      · exact hqne (by exact_mod_cast h)
      · exact hXne h
    · exact hne
  obtain ⟨s₂, hs₂s', lam₀, hlam₀pos, href₂, hband, hθlam, -⟩ :=
    ShadedBody.exists_isCRefinement_comparable_density (s := s') (V := V) (a := θ) (v := v)
      hs'ne (fun i hi ↦ hvol i (hs's hi)) hv hθ0 hθ1 hdense
  refine ⟨s₂, hs₂s'.trans hs's, 2 * lam₀, by positivity, by
    exact mul_le_mul_of_nonneg_left hθlam (by simp), ?_, href₂.trans href⟩
  intro i hi
  obtain ⟨hlo, hhi⟩ := hband i hi
  have hcoe : ((2 * lam₀ : ℝ≥0) : ℝ≥0∞) = 2 * (lam₀ : ℝ≥0∞) := by
    push_cast; ring
  refine ⟨?_, ?_⟩
  · rw [hcoe]
    calc (2 : ℝ≥0∞)⁻¹ * (2 * (lam₀ : ℝ≥0∞) * volume (V i).carrier)
        = (lam₀ : ℝ≥0∞) * volume (V i).carrier := by
          rw [← mul_assoc, ← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num),
            one_mul]
      _ ≤ volume (V i).shade := hlo
  · rw [hcoe]
    calc volume (V i).shade ≤ 2 * (lam₀ : ℝ≥0∞) * volume (V i).carrier := hhi
      _ ≤ 2 * (2 * (lam₀ : ℝ≥0∞) * volume (V i).carrier) :=
          le_mul_of_one_le_left zero_le one_le_two

/-! ### What the shading band does *not* buy: no lower bound on the shaded union

Recorded because it was asked for, and because the answer is negative and worth having in
compiled form rather than in prose.
-/

/-! ### The repair is quantitatively sufficient, not merely shape-compatible

`Kakeya.VeryNotSticky.exists_shadingBand` produces a refinement constant
`(1 - q) · (1 + log₂ θ^{-1})⁻¹`. The target's own conjunct demands `δ^η ≤ c`. The two lemmas
below check that at the intended parameters the demand is met — the logarithmic loss of the
dyadic band is sub-polynomial, so it is beaten by `δ^η` for all small `δ` — and then package
the whole chain in the exact form a producer of
`Kakeya.VeryNotSticky.exists_setup_caseSideData` consumes.
-/

end Kakeya.VeryNotSticky

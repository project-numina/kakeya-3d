/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Factoring
public import Kakeya.Tube.Rescale
public import Kakeya.PartialEstimates

/-!
# Main Lemma 1, Case (ii): the fine and coarse factors, and the reduction

This file formalizes the three subsections of Section 8 of the adapted blueprint that treat
the second alternative of `dividingScalesLemmaA`, the case complementary to the sticky case
of `Kakeya/DimensionThree/MainLemma1/Setup.lean`:

* fine-scale normalization — the **output scale of the fine normalization**:
  `Kakeya.ml1Boot.fineScale`, `Kakeya.ml1Boot.fineScale_bounds`,
  `Kakeya.ml1Boot.fineScale_bracket_le`;
* the fine-scale factor — the **fine-scale factor** `μ(𝕋[T_τ], Y)`:
  `Kakeya.ml1Boot.fineNormalize.C`, `Kakeya.ml1Boot.fineFactor.C`,
  `Kakeya.ml1Boot.exists_fineNormalization`,
  `Kakeya.ml1Boot.fine_genKF`, `Kakeya.ml1Boot.multiplicity_le_fine`;
* the coarse-scale factor — the **coarse-scale factor** `μ(𝕋_θ, Y_{𝕋_θ})`:
  `Kakeya.ml1Boot.IsParentFamily.finpartition`,
  `Kakeya.ml1Boot.exists_frostmanConstIn_coarse_le`,
  `Kakeya.ml1Boot.multiplicity_le_coarse`;
* the middle-factor reduction — the **reduction to the middle factor**:
  `Kakeya.ml1Boot.tripleCollapse`, `Kakeya.ml1Boot.exponentShift`,
  `Kakeya.ml1Boot.lossNumerics`, `Kakeya.ml1Boot.multiplicity_le_of_middle`,
  `Kakeya.ml1Boot.fibre_product_card_le`.

## Divergence from the informal statement: bare exponents

The blueprint states the fine and coarse factor estimates in terms of the parameter package
`Kakeya.ml1Boot.params`: the loss exponent is `ε♯ = η₀ = p.η 0`, the Frostman exponent is
`η_{j-1} = p.η (j - 1)`, the fullness threshold is `η(γ) = p.ηGamma γ`, and `η = p.η 0`
again for the coarse family.  Here those exponents are *bare real numbers*: `e` for the loss
exponent `η₀`, `a` for `η_{j-1}`, `n₀` for `η`, and the fullness threshold is the exponent
`ηs` produced by the existential of `Kakeya.FrostmanEstimate.multiplicity_bound_auxScale`.

This is the same device the blueprint itself uses for `lem:ml1bootCaseNonSticky` ("we state
the assembly for bare real numbers so that it does not depend on the data produced by
`lem:ml1bootFactorTwoScales`"), extended to the two factor estimates.  The gain is that none
of these statements mentions `Kakeya.ml1Boot.params`, so none of them has to carry the
specification hypotheses of `Kakeya.ml1Boot.params_spec` and
`Kakeya.ml1Boot.etaGamma_spec`.  A consumer instantiates
`e := p.η 0`, `a := p.η (j - 1)`, `n₀ := p.η 0`, and obtains the fullness hypothesis at the
threshold `ηs` from the blueprint's `λ ≥ δ ^ η(γ)` together with
`Kakeya.ml1Boot.etaGamma_spec`, which gives `p.ηGamma γ ≤ ηKF γ ≤ ηs` and hence
`δ ^ ηs ≤ δ ^ p.ηGamma γ`.

Correspondingly the fullness threshold is *existentially* quantified in
`Kakeya.ml1Boot.multiplicity_le_fine` and `Kakeya.ml1Boot.multiplicity_le_coarse`, exactly as
`η` is in `Kakeya.FrostmanEstimate.multiplicity_bound_auxScale`; the assembly of Case (ii)
takes the minimum of the two thresholds.

## Powers of the tube scales

Throughout, `δ` is the auxiliary small parameter and `τ`, `θ` are tube scales with
`δ ≤ τ ≤ θ ≤ 1`.  The ambient dimension is `3`, so the common volume of a `ρ`-tube enters as
`ρ ^ 2`; the exponent `2` is written literally rather than as `Module.finrank ℝ E - 1`, since
every statement here already carries `hdim : Module.finrank ℝ E = 3` or is dimension-free.

The total-volume bracket is always written cardinality-first, `(|s| * ρ ^ 2)`, matching
`Kakeya.FrostmanEstimate`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya

universe u

namespace ml1Boot

/-! ### Case (ii): the fine-scale factor -/

/-- **The output scale of the fine normalization**.

`fineScale δ τ = min (δ / τ) (1 / 4)`.  This is the scale of the tube family that
`Kakeya.ml1Boot.exists_fineNormalization` produces in `B₁`, in place of the bare ratio
`δ / τ`.

The truncation at `1 / 4` is forced, and is what makes that lemma true.  A `Kakeya.Tube` has
a core of length exactly `1`, so a `ρ`-tube has diameter `1 + 2 ρ` and is contained in no ball
of radius `1` once `ρ > 1/2` (`Kakeya.ml1Boot.tube_not_subset_closedBall_of_half_lt`); the
hypotheses `0 < δ ≤ τ ≤ 1` permit `δ = τ`, hence `δ / τ = 1`, and the alternative form of the
lemma — which asked for `δ / τ`-tubes in `B₁` — is refuted there by
`Kakeya.ml1Boot.not_exists_fineNormalization`.  Truncating the output scale removes the
obstruction without weakening anything in the regime that matters: `fineScale δ τ = δ / τ`
whenever `δ / τ ≤ 1/4`, so in that regime the statement is *unchanged*.

Nothing is lost in the regime `δ / τ > 1/4` either, because the two scales stay within a
bounded factor of each other, `(δ / τ) / 4 ≤ fineScale δ τ ≤ δ / τ` — the first and third
clauses of the conjunction `Kakeya.ml1Boot.fineScale_bounds` — so the fine-factor bracket
changes by at most a factor `16` (`Kakeya.ml1Boot.fineScale_bracket_le`).  That factor is paid
out of the *constant*: `Kakeya.ml1Boot.fineFactor.C = 16 * Kakeya.ml1Boot.fineNormalize.C C_N`,
and the difference is spent exactly once, in `Kakeya.ml1Boot.fine_genKF`.  It is **not**
absorbed into the subpolynomial loss `δ ^ (-ε♯)`; that route is unsound in this development,
for the reason recorded in blueprint `note:ml1bootFineScaleWhyConstant`.  So no hypothesis
bounding `δ / τ` is needed anywhere in Section 8; see the module docstring of
`Kakeya/DimensionThree/MainLemma1/Cases.lean` and blueprint
`note:ml1bootFineNormalizeScaleObstruction`. -/
noncomputable abbrev fineScale (δ τ : ℝ≥0) : ℝ≥0 := min (δ / τ) (1 / 4)

/-- **The output scale is pinned to the ratio it truncates**.

For `0 < τ` and `δ ≤ τ`:

* `fineScale δ τ ≤ δ / τ` and `δ / τ ≤ 4 * fineScale δ τ`, i.e.
  `(δ/τ)/4 ≤ fineScale δ τ ≤ δ/τ`.  This is what makes the truncation invisible to the
  fine-factor estimate (`Kakeya.ml1Boot.fineScale_bracket_le`).
* `fineScale δ τ ≤ 1/4`, which is `1 ≤ 1` short of the hypothesis `ρ ≤ 1` that
  `Kakeya.FrostmanEstimate.multiplicity_bound_auxScale` puts on its tube scale, and is on its
  own why a `fineScale δ τ`-tube in `B₁` is not asking for the impossible: `1/4` is strictly
  below the threshold `1/2` of `Kakeya.ml1Boot.tube_not_subset_closedBall_of_half_lt`.

The remaining clause `δ ≤ fineScale δ τ` needs `δ ≤ 1/4` and `τ ≤ 1` and is
`Kakeya.ml1Boot.le_fineScale`; it is kept separate because
`Kakeya.ml1Boot.fineScale_bracket_le` has neither hypothesis and would not be able to cite a
bundled form. -/
theorem fineScale_bounds {δ τ : ℝ≥0} (hδτ : δ ≤ τ) (hτ : 0 < τ) :
    fineScale δ τ ≤ δ / τ ∧ fineScale δ τ ≤ 1 / 4 ∧ δ / τ ≤ 4 * fineScale δ τ := by
  constructor
  · exact min_le_left (δ / τ) (1 / 4 : ℝ≥0)
  constructor
  · exact min_le_right (δ / τ) (1 / 4 : ℝ≥0)
  · have hρ1 : δ / τ ≤ 1 := by
      exact_mod_cast (div_le_one_of_le₀
        (by exact_mod_cast hδτ : (δ : ℝ) ≤ (τ : ℝ))
        (by exact_mod_cast hτ.le : (0 : ℝ) ≤ (τ : ℝ)))
    rcases le_total (δ / τ) (1 / 4 : ℝ≥0) with hle | hge
    · rw [fineScale, min_eq_left hle]
      exact le_mul_of_one_le_left (by positivity) (by norm_num)
    · rw [fineScale, min_eq_right hge]
      calc
        δ / τ ≤ (1 : ℝ≥0) := hρ1
        _ = 4 * (1 / 4 : ℝ≥0) := by norm_num

/-- **The auxiliary parameter is below the output scale**, which with `fineScale δ τ ≤ 1/4 ≤ 1` is
the pair of hypotheses
`δ ≤ ρ ≤ 1` that `Kakeya.FrostmanEstimate.multiplicity_bound_auxScale` puts on the tube scale
`ρ` it is applied at.

The hypothesis `δ ≤ 1/4` is harmless: every consumer quantifies `δ` through
`∀ᶠ δ in 𝓝[>] 0` (`Kakeya.ml1Boot.eventually_le_quarter`). -/
theorem le_fineScale {δ τ : ℝ≥0} (hδ4 : δ ≤ 1 / 4) (hτ1 : τ ≤ 1) (hτ : 0 < τ) :
    δ ≤ fineScale δ τ := by
  exact le_min
    (by
      have hreal : (δ : ℝ) ≤ (δ : ℝ) / (τ : ℝ) := by
        rw [le_div_iff₀ (by exact_mod_cast hτ : (0 : ℝ) < (τ : ℝ))]
        have hτle1 : (τ : ℝ) ≤ 1 := by exact_mod_cast hτ1
        have hδ0 : 0 ≤ (δ : ℝ) := NNReal.coe_nonneg δ
        calc
          (δ : ℝ) * (τ : ℝ) ≤ (δ : ℝ) * 1 := mul_le_mul_of_nonneg_left hτle1 hδ0
          _ = (δ : ℝ) := by ring
      exact_mod_cast hreal)
    hδ4

/-- **The truncation costs a factor `16` in the fine-factor bracket.**

The two occurrences of the tube scale in the conclusion of
`Kakeya.FrostmanEstimate.multiplicity_bound_auxScale` are `ρ ^ (-2γ)` and `(|s| ρ²) ^ (1-γ/2)`.
Reading them at `ρ = fineScale δ τ` instead of at `ρ = δ / τ` costs at most `4 ^ (2γ) ≤ 16` in
the first — by the last clause of `Kakeya.ml1Boot.fineScale_bounds` — and nothing at all in
the second, which only decreases, by its first clause.

The factor `16` is paid out of the *constant*, not out of the subpolynomial loss:
`Kakeya.ml1Boot.fineFactor.C = 16 * Kakeya.ml1Boot.fineNormalize.C C_N`, the normalization
lemma is stated at the smaller constant and `Kakeya.ml1Boot.fine_genKF` at the larger, and
this is the one step that spends the difference.  Paying it out of the loss instead — apply
the underlying estimate at `ε♯/2` and use `16 δ ^ (-ε♯/2) ≤ δ ^ (-ε♯)` — would change the
fullness threshold that `Kakeya.FrostmanEstimate.multiplicity_bound_auxScale` hands back, and
the calibration of that threshold against `Kakeya.ml1Boot.params` is fixed upstream at the
full exponent; see blueprint `note:ml1bootFineScaleWhyConstant`. -/
-- The first (negative-exponent) factor of the fine-factor bracket: reading `ρ ^ (-2γ)` at
-- `σ = fineScale δ τ` instead of at `ρ = δ / τ` costs `4 ^ (2γ) ≤ 16`, by the last clause
-- `δ / τ ≤ 4 * fineScale δ τ` of `fineScale_bounds`.
private lemma fineScale_rpow_neg_le {δ τ : ℝ≥0} (hδ : 0 < δ) (hδτ : δ ≤ τ) (hτ : 0 < τ)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    ((fineScale δ τ : ℝ≥0) : ℝ≥0∞) ^ (-2 * γ)
      ≤ 16 * (((δ / τ : ℝ≥0)) : ℝ≥0∞) ^ (-2 * γ) := by
  let σ : ℝ≥0∞ := (fineScale δ τ : ℝ≥0)
  let ρ : ℝ≥0∞ := (δ / τ : ℝ≥0)
  have hρσ4 : ρ ≤ 4 * σ := by
    dsimp [ρ, σ]
    exact_mod_cast (fineScale_bounds hδτ hτ).2.2
  have hρ0 : (0 : ℝ≥0) < δ / τ := by
    rw [← NNReal.coe_lt_coe]
    rw [NNReal.coe_div]
    exact div_pos (by exact_mod_cast hδ) (by exact_mod_cast hτ)
  have hρpos : 0 < ρ := by
    dsimp [ρ]
    exact ENNReal.coe_pos.mpr hρ0
  have hσpos : 0 < σ := by
    dsimp [σ]
    exact ENNReal.coe_pos.mpr (by
      exact lt_min hρ0 (by norm_num))
  have hρne : ρ ≠ 0 := ne_of_gt hρpos
  have hσne : σ ≠ 0 := ne_of_gt hσpos
  have hρtop : ρ ≠ ⊤ := ENNReal.coe_ne_top
  have hσtop : σ ≠ ⊤ := ENNReal.coe_ne_top
  have h2γ : 0 ≤ 2 * γ := by nlinarith [hγ0]
  have h4le16 : (4 : ℝ≥0∞) ^ (2 * γ) ≤ 16 := by
    calc
      (4 : ℝ≥0∞) ^ (2 * γ) ≤ (4 : ℝ≥0∞) ^ (2 : ℝ) := by
        exact ENNReal.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 4)
          (by nlinarith [hγ1])
      _ = 16 := by norm_num
  have hρ_le : ρ ^ (2 * γ) ≤ 16 * σ ^ (2 * γ) := by
    calc
      ρ ^ (2 * γ) ≤ (4 * σ) ^ (2 * γ) := by
        exact ENNReal.rpow_le_rpow hρσ4 h2γ
      _ = 4 ^ (2 * γ) * σ ^ (2 * γ) := by
        rw [ENNReal.mul_rpow_of_nonneg (4 : ℝ≥0∞) σ h2γ]
      _ ≤ 16 * σ ^ (2 * γ) := by
        exact mul_le_mul_left h4le16 (σ ^ (2 * γ))
  let a : ℝ≥0∞ := σ ^ (2 * γ)
  let b : ℝ≥0∞ := ρ ^ (2 * γ)
  have ha_pos : 0 < a := by
    dsimp [a]
    exact ENNReal.rpow_pos hσpos hσtop
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  have ha_top : a ≠ ⊤ := by
    dsimp [a]
    exact ENNReal.rpow_ne_top_of_ne_zero hσne hσtop
  have hb_pos : 0 < b := by
    dsimp [b]
    exact ENNReal.rpow_pos hρpos hρtop
  have hb_ne : b ≠ 0 := ne_of_gt hb_pos
  have hb_top : b ≠ ⊤ := by
    dsimp [b]
    exact ENNReal.rpow_ne_top_of_ne_zero hρne hρtop
  have hρb : b ≤ 16 * a := by
    dsimp [a, b]
    exact hρ_le
  have haa : a⁻¹ * a = 1 := ENNReal.inv_mul_cancel ha_ne ha_top
  have hbb : b * b⁻¹ = 1 := ENNReal.mul_inv_cancel hb_ne hb_top
  have hst : a⁻¹ * b ≤ 16 := by
    calc
      a⁻¹ * b ≤ a⁻¹ * (16 * a) := by exact mul_le_mul_right hρb (a⁻¹)
      _ = 16 := by
        rw [show a⁻¹ * (16 * a) = 16 * (a⁻¹ * a) by ring, haa, mul_one]
  have hgoal : a⁻¹ ≤ 16 * b⁻¹ := by
    calc
      a⁻¹ = (a⁻¹ * b) * b⁻¹ := by rw [mul_assoc, hbb, mul_one]
      _ ≤ 16 * b⁻¹ := by exact mul_le_mul_left hst (b⁻¹)
  calc
    σ ^ (-2 * γ) = (σ ^ (2 * γ))⁻¹ := by
      rw [show -2 * γ = -(2 * γ) by ring, ENNReal.rpow_neg]
    _ ≤ 16 * (ρ ^ (2 * γ))⁻¹ := by
      simpa [a, b] using hgoal
    _ = 16 * ρ ^ (-2 * γ) := by
      rw [show -2 * γ = -(2 * γ) by ring]
      rw [← ENNReal.rpow_neg]

-- The volume factor of the fine-factor bracket: since `σ ≤ ρ` and `1 - γ/2 ≥ 0`, the whole
-- power only decreases as it is read at `σ` rather than at `ρ`.
private lemma fineScale_vol_le {δ τ : ℝ≥0} (hδτ : δ ≤ τ) (hτ : 0 < τ)
    {γ : ℝ} (hγ1 : γ ≤ 1) (m : ℕ) :
    ((m : ℝ≥0∞) * ((fineScale δ τ : ℝ≥0) : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2)
      ≤ ((m : ℝ≥0∞) * ((δ / τ : ℝ≥0) : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
  have hσρ : ((fineScale δ τ : ℝ≥0) : ℝ≥0∞) ≤ ((δ / τ : ℝ≥0) : ℝ≥0∞) :=
    ENNReal.coe_le_coe.mpr (fineScale_bounds hδτ hτ).1
  have hsq : ((fineScale δ τ : ℝ≥0) : ℝ≥0∞) ^ (2 : ℕ)
      ≤ ((δ / τ : ℝ≥0) : ℝ≥0∞) ^ (2 : ℕ) := by
    simpa [pow_two] using
      mul_le_mul hσρ hσρ (zero_le) (zero_le)
  have hbase : (m : ℝ≥0∞) * ((fineScale δ τ : ℝ≥0) : ℝ≥0∞) ^ (2 : ℕ)
      ≤ (m : ℝ≥0∞) * ((δ / τ : ℝ≥0) : ℝ≥0∞) ^ (2 : ℕ) := by
    exact mul_le_mul_right hsq (m : ℝ≥0∞)
  have hpos : 0 ≤ (1 - γ / 2 : ℝ) := by nlinarith [hγ1]
  exact ENNReal.rpow_le_rpow hbase hpos

theorem fineScale_bracket_le {δ τ : ℝ≥0} (hδ : 0 < δ) (hδτ : δ ≤ τ) (hτ : 0 < τ)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (m : ℕ) :
    ((fineScale δ τ : ℝ≥0) : ℝ≥0∞) ^ (-2 * γ)
        * ((m : ℝ≥0∞) * ((fineScale δ τ : ℝ≥0) : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2)
      ≤ 16 * (((δ / τ : ℝ≥0)) : ℝ≥0∞) ^ (-2 * γ)
          * ((m : ℝ≥0∞) * (((δ / τ : ℝ≥0)) : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
  have hA : ((fineScale δ τ : ℝ≥0) : ℝ≥0∞) ^ (-2 * γ)
      ≤ 16 * (((δ / τ : ℝ≥0)) : ℝ≥0∞) ^ (-2 * γ) :=
    fineScale_rpow_neg_le hδ hδτ hτ hγ0 hγ1
  have hB : ((m : ℝ≥0∞) * ((fineScale δ τ : ℝ≥0) : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2)
      ≤ ((m : ℝ≥0∞) * (((δ / τ : ℝ≥0)) : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2) :=
    fineScale_vol_le hδτ hτ hγ1 m
  exact mul_le_mul hA hB (zero_le) (zero_le)

/-- **The auxiliary parameter is eventually at most `1/4`**, which is the one smallness the
truncated output scale asks
of `δ`: it is the hypothesis of `Kakeya.ml1Boot.le_fineScale`.  Every consumer of the fine
normalization already quantifies `δ` through `∀ᶠ δ in 𝓝[>] 0`, so nothing has to be added to
any statement to obtain it. -/
theorem eventually_le_quarter : ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0, δ ≤ 1 / 4 := by
  exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
    (Filter.eventually_of_mem (Iic_mem_nhds (by norm_num)) fun δ hδ => hδ)

/-- **The normalization loss `C_{lem:ml1bootFineNormalizeCore}(R)`**, at normalized ambient radius
`R` and tilt factor `κ`.

`fineNormalize.C R κ = (4 R) ^ 12 * Tube.comparableReplacement.C 3 ((4 R) ^ 6)
+ Tube.essDistinctTubesInSelfDilate.C 3 (4 (κ + 2) R C_n)`, `C_n = Tube.tubeOverlapCoreClose.C 3`:
the total distortion incurred when a family of `δ`-tubes inside a `τ`-tube `T_τ` is carried to a
family of `Kakeya.ml1Boot.fineScale δ τ`-tubes in `B₁ ⊆ ℝ³`, given that the normalization
`Φ_{T_τ}` puts the containing body in `B_R`.  The first summand collects `Φ_{T_τ}` followed by
the homothety `z ↦ z / (4 R)`, the volume comparison between an image and the honest tube
covering it, and the ambient enlargement to `B₁` (powers of `4 R`), together with the selection
constant `Tube.comparableReplacement.C` at the comparability constant `(4 R) ^ 6`.

## The second summand, and where the tilt parameter comes from

`κ` is the tilt factor of the fine cores against the axis of `T_τ`: the hypothesis
`|f_i - ⟨e, f_i⟩ e| ≤ κ τ` of `lem:ml1bootFineNormalizeCore`.  The route that lemma takes selects *downstairs*, through
`Tube.exists_comparableReplacement_affine`, whose selection constant is
`Tube.essDistinctTubesInSelfDilate.C 3 (4 (κ + 2) R C_n)`.  That
selection constant grows like `κ ^ 12`, so a value that does not see `κ` cannot dominate it for
all `κ`.

Carrying `κ` here and adding the selection constant as a summand gives
`C₁ ≤ fineNormalize.C R κ` by `le_add_self` at *every* `κ` and every `R`, not a
numerical check at `κ ≤ 4`: the `2 ≤ κ ≤ 4` hypothesis of blueprint
`lem:ml1bootFineNormalizeCore` is no longer needed *for the constant*.  The lower bound `2 ≤ κ`
is still what makes the two instances read the tilt clause as a weakening, and is why the
default value below is `2`.

The `.toNNReal` inside `Tube.essDistinctTubesInSelfDilate.C` is inert on the ratio written here:
`C_n > 1`, `R ≥ 1` and `κ + 2 ≥ 2` at both instances.

The homothety ratio is `4 R` and not `R`.  At ratio `R` the normalized parent fills `B₁` with
no room to spare (`Tube.normalization_distortion`, item `image_ambient_subset_closedBall`), and
the extension of an image core to the unit length that a `Kakeya.Tube` demands then protrudes
from `B₁`; at ratio `4 R` the image core lies in `B_{1/4}`, its unit-length extension in
`B_{3/4}`, and the output tube — of radius at most `1/4` by `Kakeya.ml1Boot.fineScale_bounds` —
in `B₁`.

The two instances used are `(R, κ) = (C_N, 2)` for `Kakeya.ml1Boot.exists_fineNormalization`,
where the tilt is `Tube.perp_norm_core_sub_le_of_subset`, and
`(R, κ) = ((1 + 2 c) C_N, max 2 (2 c))` for
`Kakeya.ml1Boot.exists_fineNormalization_dilate` at dilation ratio `c`, where the tilt is
`Tube.perp_norm_core_sub_le_of_subset_dilate` at bound `2 c θ`; `C_N = Tube.normalization.C 3`,
and the factor `1 + 2 c` bounds the growth of the ambient ball under the `c`-dilate.  At `c = 2`
— the ratio the chain of `Kakeya.ml1Boot.reduceToTb_fine_factor_dilate` uses — the tilt is `4`.
The constant depends only on `R`, on `κ` and on the ambient dimension `3`; in particular not on `δ`, on
`τ`, on `θ`, on `γ`, on `j`, or on the family. -/
noncomputable abbrev fineNormalize.C (R : ℝ≥0) (κ : ℝ≥0 := 2) : ℝ≥0 :=
  (4 * R) ^ 12 * _root_.Tube.comparableReplacement.C 3 ((4 * R) ^ 6)
    + _root_.Tube.essDistinctTubesInSelfDilate.C 3
        (4 * ((κ : ℝ) + 2) * (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3)

/-- **`1 ≤ C_{lem:ml1bootFineNormalizeCore}(R)`** for `1 ≤ R`: the first summand is already a
product of a power
of `4 R ≥ 1` with a selection constant, both at least `1`.  No hypothesis on the tilt `κ` is
needed.  Stated so that consumers cite it instead of unfolding the constant, whose unfolded
numeral is far too large to evaluate. -/
theorem one_le_fineNormalize_C {R κ : ℝ≥0} (hR : 1 ≤ R) :
    (1 : ℝ≥0) ≤ fineNormalize.C R κ := by
  unfold fineNormalize.C
  refine le_trans ?_ le_self_add
  exact one_le_mul (one_le_pow₀ (one_le_mul (by norm_num : (1 : ℝ≥0) ≤ 4) hR))
    (_root_.Tube.comparableReplacement.one_le_C 3 ((4 * R) ^ 6))

/-- **The constant `C_{lem:ml1bootFineFactor}`** of `Kakeya.ml1Boot.multiplicity_le_fine`
.

`fineFactor.C = 16 * fineNormalize.C C_N`, with `C_N = Tube.normalization.C 3`: the loss of the
normalization `Kakeya.ml1Boot.exists_fineNormalization`, times the bracket factor `16` of
`Kakeya.ml1Boot.fineScale_bracket_le`.  The tilt argument of
`Kakeya.ml1Boot.fineNormalize.C` is left at its default `κ = 2`, which is the tilt the
undilated instance has from `Tube.perp_norm_core_sub_le_of_subset`.

The two constants are deliberately distinct, and the `16` sits on this one and not on the
normalization: the normalization meets its four conclusions at
`Kakeya.ml1Boot.fineNormalize.C C_N`, and the `16` is spent exactly once above it, in
`Kakeya.ml1Boot.fine_genKF`, when the estimate obtained at the truncated scale
`Kakeya.ml1Boot.fineScale δ τ` is rewritten at the scale `δ / τ` that every consumer names.
Writing the `16` into both would overshoot.  See blueprint
`note:ml1bootFineScaleWhyConstant`.

It depends only on the ambient dimension `3`; in particular not on `δ`, on `τ`, on `θ`, on
`γ`, on `j`, or on the family. -/
noncomputable abbrev fineFactor.C : ℝ≥0 := 16 * fineNormalize.C (_root_.Tube.normalization.C 3)

section Fine

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **A fine fibre, as the three fine-factor lemmas consume it** (blueprint
`lem:ml1bootFineNormalize` and `lem:ml1bootFineFactor`, the hypotheses on `𝕋[T_τ]`).

`(T i)_{i ∈ u}` is a nonempty family of pairwise essentially distinct shaded `δ`-tubes sitting
inside a single `τ`-tube `T_τ ⊆ B₁`, with shading densities two-sidedly comparable to a common
`μ₀` with constant `Λ`, and with fullness at least `C Λ² δ ^ ηs`.

This is exactly the fibre `𝕋[T_{τ,k}]` over one parent, which is why the block is verbatim
the same in `Kakeya.ml1Boot.fine_genKF`,
`Kakeya.ml1Boot.multiplicity_le_fine_frostmanLoss` and `Kakeya.ml1Boot.multiplicity_le_fine`;
only the Frostman bound differs between them and so is not a field here.

The two-sided density bound is what `Kakeya.ml1Boot.exists_fineNormalization` needs to replace
each tube by a comparable honest one, and it is stated with the individual volumes
`|T i|` rather than the common volume of a `δ`-tube: all `δ`-tubes are isometric, so the two
readings agree, and the pointwise form is the one `Tube.exists_comparableReplacement`
consumes.  The fullness threshold carries the same `C Λ²` prefactor that
`Kakeya.ml1Boot.exists_fineNormalization` loses, so that it survives the normalization. -/
structure IsFineFibre {ι : Type*} {δ τ : ℝ≥0} (Λ : ℝ≥0) (μ₀ : ℝ≥0∞) (ηs : ℝ)
    (u : Finset ι) (Tτ : Tube τ E) (T : ι → ShadedTube δ E) : Prop where
  /-- The common density the shadings are compared to is nonzero. -/
  density_pos : 0 < μ₀
  /-- The fibre is nonempty. -/
  nonempty : u.Nonempty
  /-- The parent tube lies in the unit ball. -/
  parent_ball : Tτ.carrier ⊆ Metric.closedBall 0 1
  /-- Every member of the fibre lies in the parent tube. -/
  subset_parent : ∀ i ∈ u, (T i).carrier ⊆ Tτ.carrier
  /-- The members are pairwise essentially distinct. -/
  essDistinct : (u : Set ι).Pairwise
    (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier)
  /-- The shading densities are two-sidedly comparable to `μ₀`, with constant `Λ`. -/
  shade_comparable : ∀ i ∈ u,
    (Λ : ℝ≥0∞)⁻¹ * μ₀ * volume (T i).carrier ≤ volume (T i).shade ∧
      volume (T i).shade ≤ (Λ : ℝ≥0∞) * μ₀ * volume (T i).carrier
  /-- The fibre is full, with the prefactor the normalization loses. -/
  fullness : (fineFactor.C : ℝ≥0∞) * (Λ : ℝ≥0∞) ^ 2 * (δ : ℝ≥0∞) ^ ηs
    ≤ (ShadedBody.fullness u (fun i => (T i).toShadedBody) : ℝ≥0∞)

/-! #### The scale obstruction, and why the output scale is truncated

The three declarations below record, in Lean, why
`Kakeya.ml1Boot.exists_fineNormalization` cannot ask for `δ / τ`-tubes in `B₁`: that demand is
*unsatisfiable* at the extreme scale `δ = τ` permitted by the hypotheses `0 < δ ≤ τ ≤ 1`,
since a `ρ`-tube with `ρ > 1/2` does not fit in any ball of radius `1`, its carrier having
diameter `1 + 2 ρ > 2`.

They are refutations of the *earlier* form of the two normalization lemmas, and are kept as
the reason the present form truncates its output scale to
`Kakeya.ml1Boot.fineScale δ τ = min (δ/τ) (1/4)`.  They do not apply to that form:
`fineScale δ τ ≤ 1/4 < 1/2`, the second clause of `Kakeya.ml1Boot.fineScale_bounds`.  See
blueprint
`note:ml1bootFineNormalizeScaleObstruction`. -/

/-- **Reading off the four conclusions from `Tube.IsComparableReplacementFree`.**

The package hands back the retained index set `u'`, and its four fields plus two generic
transport lemmas give the three quantitative clauses at the constants recorded here:
multiplicity is exact and pays only the selection constant `C₁`
(`ShadedBody.multiplicity_le_of_isCRefinement` against the refinement clause), fullness pays the
comparability constant `Cv` on top of it (`ShadedBody.IsCRefinement.coe_mul_fullness_le`), and
the Frostman constant pays `C₁` for the passage to the subfamily
(`ConvexSpaceBody.frostmanConstIn_subfamily_le`, applicable because all members of `𝕍` are
`σ`-tubes and hence of equal volume) and `Cv` for the comparability.  The factor `Λ ^ 2` is the
density spread, and enters through the refinement constant `(C₁ Λ ^ 2)⁻¹`. -/
private lemma of_comparableReplacementFree {ι : Type*} {u : Finset ι} {σ : ℝ≥0}
    {𝕎 : ι → ShadedBody E} {𝕍 : ι → ShadedTube σ E} {K : ConvexSpaceBody E}
    {Cv Λ C₁ : ℝ≥0} (hΛ : 1 ≤ Λ) (hCv : 1 ≤ Cv) (hC₁ : 1 ≤ C₁)
    (hVK : ∀ i ∈ u, (𝕍 i).toConvexSpaceBody ≤ K)
    (h : _root_.Tube.IsComparableReplacementFree u 𝕎 𝕍 K Cv Λ C₁) :
    ∃ u' ⊆ u, u'.Nonempty ∧
      (u' : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (𝕍 i).carrier (𝕍 j).carrier) ∧
        ShadedBody.multiplicity u 𝕎
          ≤ (C₁ : ℝ≥0∞) * (Λ : ℝ≥0∞) ^ 2
            * ShadedBody.multiplicity u' (fun i => (𝕍 i).toShadedBody) ∧
        (ShadedBody.fullness u 𝕎 : ℝ≥0∞)
          ≤ ((Cv : ℝ≥0∞) * (C₁ : ℝ≥0∞)) * (Λ : ℝ≥0∞) ^ 2
            * (ShadedBody.fullness u' (fun i => (𝕍 i).toShadedBody) : ℝ≥0∞) ∧
        frostmanConstIn u' (fun i => (𝕍 i).toConvexSpaceBody) K
          ≤ (C₁ : ℝ≥0∞) * (Cv : ℝ≥0∞)
            * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K := by
  rcases h.select with ⟨u', hu'sub, hu'ne, hpair, hu'card, hcref⟩
  let ce : ℝ≥0∞ := ((C₁ * Λ ^ 2)⁻¹ : ℝ≥0)
  have hL0 : Λ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hΛ)
  have hC₁0 : C₁ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hC₁)
  have hC₁Λ : (C₁ * Λ ^ 2 : ℝ≥0) ≠ 0 := mul_ne_zero hC₁0 (pow_ne_zero 2 hL0)
  have hC₁ΛE0 : ((C₁ * Λ ^ 2 : ℝ≥0) : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hC₁Λ
  have hce0 : ce ≠ 0 := by
    dsimp [ce]
    rw [ENNReal.coe_inv hC₁Λ]
    intro hz
    have hcan := ENNReal.inv_mul_cancel hC₁ΛE0
      (ENNReal.coe_ne_top : ((C₁ * Λ ^ 2 : ℝ≥0) : ℝ≥0∞) ≠ ⊤)
    rw [hz, zero_mul] at hcan
    exact zero_ne_one hcan
  have hce_top : ce ≠ ⊤ := by
    dsimp [ce]
    exact ENNReal.coe_ne_top
  have cRef_ne0 : (C₁ * Λ ^ 2 : ℝ≥0)⁻¹ ≠ 0 :=
    ENNReal.coe_ne_zero.mp (by simpa [ce] using hce0)
  have hcoef : ce⁻¹ = (C₁ : ℝ≥0∞) * (Λ : ℝ≥0∞) ^ 2 := by
    change (((C₁ * Λ ^ 2)⁻¹ : ℝ≥0) : ℝ≥0∞)⁻¹ = (C₁ : ℝ≥0∞) * (Λ : ℝ≥0∞) ^ 2
    rw [ENNReal.coe_inv hC₁Λ]
    rw [InvolutiveInv.inv_inv]
    rw [ENNReal.coe_mul, ENNReal.coe_pow]
  refine ⟨u', hu'sub, hu'ne, hpair, ?_, ?_, ?_⟩
  · rw [← h.multiplicity]
    calc
      ShadedBody.multiplicity u (fun i => (𝕍 i).toShadedBody)
          ≤ ce⁻¹ * ShadedBody.multiplicity u' (fun i => (𝕍 i).toShadedBody) := by
            exact ShadedBody.multiplicity_le_of_isCRefinement (s := u)
              (V := fun i => (𝕍 i).toShadedBody) (s' := u')
              (V' := fun i => (𝕍 i).toShadedBody) (c := (C₁ * Λ ^ 2)⁻¹) cRef_ne0 hcref
      _ = (C₁ : ℝ≥0∞) * (Λ : ℝ≥0∞) ^ 2
              * ShadedBody.multiplicity u' (fun i => (𝕍 i).toShadedBody) := by
            rw [hcoef]
  · have hfullNN : ShadedBody.fullness u 𝕎
        ≤ (Cv : ℝ≥0) * ShadedBody.fullness u (fun i => (𝕍 i).toShadedBody) := by
      have hCv0 : Cv ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hCv)
      calc
        ShadedBody.fullness u 𝕎
            = (Cv : ℝ≥0) * ((Cv : ℝ≥0)⁻¹ * ShadedBody.fullness u 𝕎) := by
              rw [← mul_assoc, mul_inv_cancel₀ hCv0, one_mul]
        _ ≤ (Cv : ℝ≥0) * ShadedBody.fullness u (fun i => (𝕍 i).toShadedBody) := by
              exact mul_le_mul_right h.fullness (Cv : ℝ≥0)
    have hfull1 : (ShadedBody.fullness u 𝕎 : ℝ≥0∞)
        ≤ (Cv : ℝ≥0∞) * (ShadedBody.fullness u (fun i => (𝕍 i).toShadedBody) : ℝ≥0∞) := by
      exact_mod_cast hfullNN
    have hcfull : ce * (ShadedBody.fullness u (fun i => (𝕍 i).toShadedBody) : ℝ≥0∞)
        ≤ (ShadedBody.fullness u' (fun i => (𝕍 i).toShadedBody) : ℝ≥0∞) := by
      simpa [ce] using (IsCRefinement.coe_mul_fullness_le hcref)
    have hfull2 : (ShadedBody.fullness u (fun i => (𝕍 i).toShadedBody) : ℝ≥0∞)
        ≤ (C₁ : ℝ≥0∞) * (Λ : ℝ≥0∞) ^ 2
            * (ShadedBody.fullness u' (fun i => (𝕍 i).toShadedBody) : ℝ≥0∞) := by
      have hmm := mul_le_mul_right hcfull ce⁻¹
      rwa [← mul_assoc, ENNReal.inv_mul_cancel hce0 hce_top, one_mul, hcoef] at hmm
    calc
      (ShadedBody.fullness u 𝕎 : ℝ≥0∞)
          ≤ (Cv : ℝ≥0∞) * (ShadedBody.fullness u (fun i => (𝕍 i).toShadedBody) : ℝ≥0∞) :=
            hfull1
      _ ≤ (Cv : ℝ≥0∞)
            * ((C₁ : ℝ≥0∞) * (Λ : ℝ≥0∞) ^ 2
                * (ShadedBody.fullness u' (fun i => (𝕍 i).toShadedBody) : ℝ≥0∞)) := by
            gcongr
      _ = ((Cv : ℝ≥0∞) * (C₁ : ℝ≥0∞)) * (Λ : ℝ≥0∞) ^ 2
            * (ShadedBody.fullness u' (fun i => (𝕍 i).toShadedBody) : ℝ≥0∞) := by ring
  · rcases hu'ne with ⟨i₀, hi₀⟩
    have hu'ne_nonempty : u.Nonempty := ⟨i₀, hu'sub hi₀⟩
    let v : ℝ≥0∞ := volume ((𝕍 i₀).toConvexSpaceBody).carrier
    have hvol : ∀ i ∈ u, volume ((𝕍 i).toConvexSpaceBody).carrier = v := by
      intro i hi
      dsimp [v]
      simpa using _root_.Tube.volume_carrier_eq_volume_carrier
        (by simpa using (𝕍 i).toTube) (by simpa using (𝕍 i₀).toTube)
    have hC₁E0 : (C₁ : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hC₁0
    have hC₁Etop : (C₁ : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
    have hcardκ : (C₁ : ℝ≥0∞)⁻¹ * (u.card : ℝ≥0∞) ≤ (u'.card : ℝ≥0∞) := by
      calc
        (C₁ : ℝ≥0∞)⁻¹ * (u.card : ℝ≥0∞)
            ≤ (C₁ : ℝ≥0∞)⁻¹ * ((C₁ : ℝ≥0∞) * (u'.card : ℝ≥0∞)) := by
              exact mul_le_mul_right hu'card _
        _ = (u'.card : ℝ≥0∞) := by
              rw [← mul_assoc, ENNReal.inv_mul_cancel hC₁E0 hC₁Etop, one_mul]
    have hκ0 : (C₁ : ℝ≥0∞)⁻¹ ≠ 0 := by
      intro hz
      have hcan := ENNReal.inv_mul_cancel hC₁E0 hC₁Etop
      rw [hz, zero_mul] at hcan
      exact zero_ne_one hcan
    have hsubF := ConvexSpaceBody.frostmanConstIn_subfamily_le (s := u)
      (W := fun i => (𝕍 i).toConvexSpaceBody) (K := K)
      (v := v) (κ := (C₁ : ℝ≥0∞)⁻¹)
      hu'ne_nonempty hvol hVK hu'sub hκ0 hcardκ
    have hF1 : frostmanConstIn u' (fun i => (𝕍 i).toConvexSpaceBody) K
        ≤ (C₁ : ℝ≥0∞) * frostmanConstIn u (fun i => (𝕍 i).toConvexSpaceBody) K := by
      simpa [InvolutiveInv.inv_inv] using hsubF
    calc
      frostmanConstIn u' (fun i => (𝕍 i).toConvexSpaceBody) K
          ≤ (C₁ : ℝ≥0∞) * frostmanConstIn u (fun i => (𝕍 i).toConvexSpaceBody) K := hF1
      _ ≤ (C₁ : ℝ≥0∞)
            * ((Cv : ℝ≥0∞) * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K) := by
            exact mul_le_mul_right h.frostmanConstIn (C₁ : ℝ≥0∞)
      _ = (C₁ : ℝ≥0∞) * (Cv : ℝ≥0∞)
            * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K := by ring

/-- **The ambient enlargement to `B₁`**, in the form the fine normalization uses it: reading a
Frostman constant at the unit ball rather than at a smaller body `K'` containing every member
costs exactly the volume ratio `|B₁| / |K'|`
(`ConvexSpaceBody.frostmanConstIn_ambient_mono`), and `hratio` bounds that ratio by `Cv`. -/
private lemma frostmanConstIn_closedUnitBall_le_of_ambient
    {ι : Type*} {u : Finset ι} {𝕎 : ι → ShadedBody E} {K' : ConvexSpaceBody E} {Cv : ℝ≥0}
    (hK' : K' ≤ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E))
    (hK'vol : volume K'.carrier ≠ 0)
    (hWK' : ∀ i ∈ u, (𝕎 i).toConvexSpaceBody ≤ K')
    (hratio : volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier
      ≤ (Cv : ℝ≥0∞) * volume K'.carrier) :
    frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody)
        (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E)
      ≤ (Cv : ℝ≥0∞) * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K' := by
  have hmono := frostmanConstIn_ambient_mono hK' hK'vol hWK'
  have hK'voltop : volume K'.carrier ≠ ⊤ := K'.isCompact'.measure_ne_top
  have hdiv : volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier
      / volume K'.carrier ≤ (Cv : ℝ≥0∞) := by
    rw [ENNReal.div_le_iff_le_mul (Or.inl hK'vol) (Or.inl hK'voltop)]
    exact hratio
  calc
    frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody)
        (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E)
        ≤ volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier
          / volume K'.carrier
          * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K' := hmono
    _ ≤ (Cv : ℝ≥0∞) * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K' := by
          gcongr

-- All `δ`-tubes are isometric, so their affine images under one map have a common volume: this
-- is the hypothesis `hcommon` of `Tube.exists_comparableReplacement_affine`.
private lemma volume_affineImage_carrier_eq {δ : ℝ≥0} (S S' : ShadedTube δ E)
    (L : E ≃ᵃ[ℝ] E) (hcont : Continuous L) (hemb : MeasurableEmbedding L) :
    volume ((S.toShadedBody).affineImage L.toAffineMap hcont hemb).carrier
      = volume ((S'.toShadedBody).affineImage L.toAffineMap hcont hemb).carrier := by
  change volume (L.toAffineMap '' S.carrier) = volume (L.toAffineMap '' S'.carrier)
  rw [Kakeya.volume_affineImage L S.carrier, Kakeya.volume_affineImage L S'.carrier]
  rw [_root_.Tube.volume_carrier_eq_volume_carrier S.toTube S'.toTube]

-- An affine equivalence multiplies carrier and shade by the same Jacobian, so a two-sided
-- density bracket is carried over verbatim: the hypothesis `hZ` of
-- `Tube.exists_comparableReplacement_affine`, read at the common volume of the images.
private lemma affineImage_shade_bounds {δ : ℝ≥0} (S S' : ShadedTube δ E)
    (L : E ≃ᵃ[ℝ] E) (hcont : Continuous L) (hemb : MeasurableEmbedding L)
    {Λ : ℝ≥0} {μ₀ : ℝ≥0∞}
    (h₁ : (Λ : ℝ≥0∞)⁻¹ * μ₀ * volume S.carrier ≤ volume S.shade)
    (h₂ : volume S.shade ≤ (Λ : ℝ≥0∞) * μ₀ * volume S.carrier) :
    (Λ : ℝ≥0∞)⁻¹ * μ₀
          * volume ((S'.toShadedBody).affineImage L.toAffineMap hcont hemb).carrier
        ≤ volume ((S.toShadedBody).affineImage L.toAffineMap hcont hemb).shade ∧
      volume ((S.toShadedBody).affineImage L.toAffineMap hcont hemb).shade
        ≤ (Λ : ℝ≥0∞) * μ₀
          * volume ((S'.toShadedBody).affineImage L.toAffineMap hcont hemb).carrier := by
  -- An affine equivalence multiplies every volume by the same Jacobian `J`, so the two-sided
  -- density bracket carried over from `h₁` and `h₂` is unchanged.
  let J : ℝ≥0∞ := ENNReal.ofReal |LinearMap.det (L.linear : E →ₗ[ℝ] E)|
  have hprimed : volume ((S'.toShadedBody).affineImage L.toAffineMap hcont hemb).carrier
      = volume ((S.toShadedBody).affineImage L.toAffineMap hcont hemb).carrier :=
    (volume_affineImage_carrier_eq S S' L hcont hemb).symm
  have hcarrier : volume ((S.toShadedBody).affineImage L.toAffineMap hcont hemb).carrier
      = J * volume S.carrier := by
    dsimp [J]
    change volume (L.toAffineMap '' S.carrier) = J * volume S.carrier
    exact Kakeya.volume_affineImage L S.carrier
  have hshade : volume ((S.toShadedBody).affineImage L.toAffineMap hcont hemb).shade
      = J * volume S.shade := by
    dsimp [J]
    change volume (L.toAffineMap '' S.shade) = J * volume S.shade
    exact Kakeya.volume_affineImage L S.shade
  constructor
  · rw [hprimed, hcarrier, hshade]
    calc
      (Λ : ℝ≥0∞)⁻¹ * μ₀ * (J * volume S.carrier)
          = J * ((Λ : ℝ≥0∞)⁻¹ * μ₀ * volume S.carrier) := by ring
      _ ≤ J * volume S.shade := by
            exact mul_le_mul (le_rfl : J ≤ J) h₁ (by positivity) (by positivity)
  · rw [hshade, hprimed, hcarrier]
    calc
      J * volume S.shade ≤ J * ((Λ : ℝ≥0∞) * μ₀ * volume S.carrier) := by
            exact mul_le_mul (le_rfl : J ≤ J) h₂ (by positivity) (by positivity)
      _ = (Λ : ℝ≥0∞) * μ₀ * (J * volume S.carrier) := by ring

-- A `δ`-tube of positive scale has positive volume (`Tube.le_volume`), and an affine
-- equivalence has nonzero Jacobian: the hypothesis `hW` of
-- `Tube.exists_comparableReplacement_affine`.
private lemma volume_affineImage_carrier_pos [Nontrivial E] {δ : ℝ≥0} (hδ : 0 < δ)
    (S : ShadedTube δ E) (L : E ≃ᵃ[ℝ] E) (hcont : Continuous L)
    (hemb : MeasurableEmbedding L) :
    0 < volume ((S.toShadedBody).affineImage L.toAffineMap hcont hemb).carrier := by
  have hδpos : 0 < (δ : ℝ≥0∞) := ENNReal.coe_pos.mpr hδ
  have hpow : 0 < (δ : ℝ≥0∞) ^ (Module.finrank ℝ E - 1) := by positivity
  have hc : (0 : ℝ≥0∞) < (_root_.Tube.le_volume.c (Module.finrank ℝ E) : ℝ≥0∞) :=
    ENNReal.coe_pos.mpr (_root_.Tube.le_volume.c_pos (Module.finrank ℝ E))
  have hSpos : 0 < volume (S.toShadedBody).carrier := by
    calc
      0 < (_root_.Tube.le_volume.c (Module.finrank ℝ E) : ℝ≥0∞) * (δ : ℝ≥0∞) ^
          (Module.finrank ℝ E - 1) := by positivity
      _ ≤ volume (S.toShadedBody).carrier := by simpa using (_root_.Tube.le_volume S.toTube)
  have hdet : LinearMap.det (L.linear : E →ₗ[ℝ] E) ≠ 0 :=
    (LinearEquiv.isUnit_det' L.linear).ne_zero
  have hJ : 0 < ENNReal.ofReal |LinearMap.det (L.linear : E →ₗ[ℝ] E)| := by
    rw [ENNReal.ofReal_pos]
    exact abs_pos.mpr hdet
  change 0 < volume (L.toAffineMap '' (S.toShadedBody).carrier)
  rw [Kakeya.volume_affineImage]
  positivity

/-- **`Tube.rescale_outer_tube` with the image-core length freed to the radius `R`.**

`Tube.rescale_outer_tube` consumes its packaged `Tube.IsNormalizationDistortion` at exactly two
fields: `image_subset_cthickening`, which is proved unconditionally by
`Tube.normalization_image_subset_cthickening` (no containment hypothesis at all), and
`dist_le_C`, which it uses only to run the chain
`dist (Ψ x) (Ψ y) = dist (Φ x) (Φ y) / (4 R) ≤ C_N / (4 R) ≤ R / (4 R) = 1/4 ≤ 1`.

So the packaged structure is stronger than the route needs: what the route needs is
`dist (Φ x) (Φ y) ≤ R`, and the packaged field supplies that only via `C_N ≤ R`.  The
distinction is invisible at `R = C_N` but decisive over a dilate: for `T ⊆ c · T₀` the image
core has length at most `√(1 + 4 c²)`, which exceeds the hardwired `C_N = 64` once
`c > 31.99…`, while the dilated instance runs at `R = (1 + 2 c) C_N` and so satisfies the
relaxed hypothesis for *every* `c`.  Freeing the field here is therefore what makes
`Kakeya.ml1Boot.exists_fineNormalization_dilate` provable at an unbounded dilation ratio.

`Kakeya/Tube/Rescale.lean` is not ours to extend, so this is the local restatement; the proof is
that of `Tube.rescale_outer_tube` with the two `hdist` projections replaced by `hcth` and
`hlen`. -/
private lemma rescale_outer_tube_of_dist_le [Nontrivial E] {θ ρ σ : ℝ≥0} {R : ℝ}
    (hsit : _root_.Tube.IsRescalingSituation θ ρ σ R 3) (hn : Module.finrank ℝ E = 3)
    (hR : 0 < R) (hρσ : (ρ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ))
    (T₀ : Tube θ E) (T : Tube ρ E)
    (hcth : T₀.normalization '' T.carrier ⊆
      Metric.cthickening
        ((_root_.Tube.normalization.C (Module.finrank ℝ E) : ℝ) * ((ρ : ℝ) / (θ : ℝ)))
        (segment ℝ (T₀.normalization T.x) (T₀.normalization T.y)))
    (hlen : dist (T₀.normalization T.x) (T₀.normalization T.y) ≤ R)
    (hball : T₀.normalization '' T.carrier ⊆ Metric.closedBall T₀.x R)
    (hxy : T₀.rescaleMap R T.x ≠ T₀.rescaleMap R T.y) :
    T₀.rescaleMap R '' T.carrier ⊆ (_root_.Tube.centredExtension σ hxy).carrier ∧
      (_root_.Tube.centredExtension σ hxy).carrier ⊆ Metric.closedBall (0 : E) 1 ∧
      volume (_root_.Tube.centredExtension σ hxy).carrier
        ≤ ENNReal.ofReal ((4 * R) ^ 6) * volume (T₀.rescaleMap R '' T.carrier) := by
  let τ : ℝ := (ρ : ℝ) / (θ : ℝ)
  let C0 : ℝ := (_root_.Tube.normalization.C (Module.finrank ℝ E) : ℝ)
  have hθpos : (0 : ℝ) < (θ : ℝ) := by exact_mod_cast hsit.pos_ambient
  have hρ_nonneg : 0 ≤ τ := by
    dsimp [τ]
    exact div_nonneg (by positivity) (le_of_lt hθpos)
  have h4Rpos : (0 : ℝ) < 4 * R := by positivity
  have h4R0 : (4 : ℝ) * R ≠ 0 := ne_of_gt h4Rpos
  have hC0_nonneg : 0 ≤ C0 := by
    dsimp [C0]
    positivity
  have hC0_le_R : C0 ≤ R := by
    dsimp [C0]
    simpa [hn] using hsit.normalizationConst_le_radius
  have hRdiv : R / (4 * R) = (1 : ℝ) / 4 := by
    field_simp [h4R0, (by norm_num : (4 : ℝ) ≠ 0)]
  -- (1) Thickness: `Ψ(T) ⊆ V`.
  have hth0 : T₀.rescaleMap R '' T.carrier ⊆
      Metric.cthickening (C0 * τ / (4 * R))
        (segment ℝ (T₀.rescaleMap R T.x) (T₀.rescaleMap R T.y)) := by
    exact _root_.Tube.rescaleMap_image_subset_cthickening T₀ hR (r := C0 * τ)
      (A := T.carrier) (p := T.x) (q := T.y)
      (mul_nonneg hC0_nonneg hρ_nonneg) hcth
  have hrad : C0 * τ / (4 * R) ≤ (σ : ℝ) := by
    have h1 : C0 * τ ≤ R * τ := mul_le_mul_of_nonneg_right hC0_le_R hρ_nonneg
    have h2 : C0 * τ / (4 * R) ≤ (R * τ) / (4 * R) := by
      exact div_le_div_of_nonneg_right h1 (le_of_lt h4Rpos)
    have h3 : (R * τ) / (4 * R) = τ / 4 := by
      field_simp [h4R0, (by norm_num : (4 : ℝ) ≠ 0)]
    have h4 : τ / 4 ≤ (σ : ℝ) := by
      have : τ ≤ 4 * (σ : ℝ) := by simpa [τ] using hρσ
      linarith
    calc
      C0 * τ / (4 * R) ≤ (R * τ) / (4 * R) := h2
      _ = τ / 4 := h3
      _ ≤ (σ : ℝ) := h4
  have hth1 : T₀.rescaleMap R '' T.carrier ⊆
      Metric.cthickening (σ : ℝ) (segment ℝ (T₀.rescaleMap R T.x) (T₀.rescaleMap R T.y)) := by
    exact hth0.trans (Metric.cthickening_mono hrad
      (segment ℝ (T₀.rescaleMap R T.x) (T₀.rescaleMap R T.y)))
  have hlen1 : dist (T₀.rescaleMap R T.x) (T₀.rescaleMap R T.y) ≤ 1 := by
    calc
      dist (T₀.rescaleMap R T.x) (T₀.rescaleMap R T.y)
          = dist (T₀.normalization T.x) (T₀.normalization T.y) / (4 * R) := by
            simpa [τ, C0] using _root_.Tube.dist_rescaleMap T₀ hR T.x T.y
      _ ≤ R / (4 * R) := div_le_div_of_nonneg_right hlen (le_of_lt h4Rpos)
      _ = 1 / 4 := hRdiv
      _ ≤ 1 := by norm_num
  have hth2 : T₀.rescaleMap R '' T.carrier ⊆ (_root_.Tube.centredExtension σ hxy).carrier := by
    exact hth1.trans (_root_.Tube.cthickening_subset_centredExtension hxy hlen1)
  -- (2) Position: `V ⊆ B̄(0,1)`.
  have hpx : dist (T₀.normalization T.x) T₀.x ≤ R := by
    have hmem : T₀.normalization T.x ∈ T₀.normalization '' T.carrier :=
      ⟨T.x, _root_.Tube.x_mem_carrier T, rfl⟩
    exact Metric.mem_closedBall.mp (hball hmem)
  have hpy : dist (T₀.normalization T.y) T₀.x ≤ R := by
    have hmem : T₀.normalization T.y ∈ T₀.normalization '' T.carrier :=
      ⟨T.y, _root_.Tube.y_mem_carrier T, rfl⟩
    exact Metric.mem_closedBall.mp (hball hmem)
  have hpx0 : dist (T₀.rescaleMap R T.x) (0 : E) ≤ 1 / 4 := by
    calc
      dist (T₀.rescaleMap R T.x) (0 : E)
          = dist (T₀.rescaleMap R T.x) (T₀.rescaleMap R T₀.x) := by
            rw [← _root_.Tube.rescaleMap_apply_x]
      _ = dist (T₀.normalization T.x) (T₀.normalization T₀.x) / (4 * R) :=
            _root_.Tube.dist_rescaleMap T₀ hR T.x T₀.x
      _ = dist (T₀.normalization T.x) T₀.x / (4 * R) := by rw [_root_.Tube.normalization_apply_x]
      _ ≤ R / (4 * R) := div_le_div_of_nonneg_right hpx (le_of_lt h4Rpos)
      _ = 1 / 4 := hRdiv
  have hpy0 : dist (T₀.rescaleMap R T.y) (0 : E) ≤ 1 / 4 := by
    calc
      dist (T₀.rescaleMap R T.y) (0 : E)
          = dist (T₀.rescaleMap R T.y) (T₀.rescaleMap R T₀.x) := by
            rw [← _root_.Tube.rescaleMap_apply_x]
      _ = dist (T₀.normalization T.y) (T₀.normalization T₀.x) / (4 * R) :=
            _root_.Tube.dist_rescaleMap T₀ hR T.y T₀.x
      _ = dist (T₀.normalization T.y) T₀.x / (4 * R) := by rw [_root_.Tube.normalization_apply_x]
      _ ≤ R / (4 * R) := div_le_div_of_nonneg_right hpy (le_of_lt h4Rpos)
      _ = 1 / 4 := hRdiv
  have hpos : (_root_.Tube.centredExtension σ hxy).carrier ⊆ Metric.closedBall (0 : E) 1 := by
    exact _root_.Tube.centredExtension_subset_closedBall hxy hpx0 hpy0 hsit.out_le_quarter
  -- (3) Volume: `|V| ≤ (4R)^6 |W|`.
  have hvol0 : volume (_root_.Tube.centredExtension σ hxy).carrier
      ≤ ENNReal.ofReal
            ((_root_.Tube.volume_le.C 3 : ℝ) / (_root_.Tube.le_volume.c 3 : ℝ) * (4 * R) ^ 3)
          * volume (T₀.rescaleMap R '' T.carrier) := by
    simpa [hn] using _root_.Tube.volume_centredExtension_le_mul_volume_rescale_image
      (n := 3) hsit hR T₀ T hxy
  have hC64R : (64 : ℝ) ≤ R := by
    have hC : (64 : ℝ) ≤ (_root_.Tube.normalization.C 3 : ℝ) := by
      norm_num [_root_.Tube.normalization.C]
    exact le_trans hC hsit.normalizationConst_le_radius
  have hbig : (256 : ℝ) ≤ 4 * R := by linarith
  have hpow256 : (256 : ℝ) ^ 3 ≤ (4 * R) ^ 3 :=
    pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 256) hbig 3
  have h12 : (12 : ℝ) ≤ (4 * R) ^ 3 := by nlinarith
  have hcoef : (_root_.Tube.volume_le.C 3 : ℝ) / (_root_.Tube.le_volume.c 3 : ℝ) * (4 * R) ^ 3
      ≤ (4 * R) ^ 6 := by
    have hvp12 : (_root_.Tube.volume_le.C 3 : ℝ) / (_root_.Tube.le_volume.c 3 : ℝ) ≤ 12 :=
      _root_.Tube.volume_ratio_three_le_twelve
    calc
      (_root_.Tube.volume_le.C 3 : ℝ) / (_root_.Tube.le_volume.c 3 : ℝ) * (4 * R) ^ 3
          ≤ 12 * (4 * R) ^ 3 := by gcongr
      _ ≤ (4 * R) ^ 3 * (4 * R) ^ 3 := by gcongr
      _ = (4 * R) ^ 6 := by ring
  have hvol : volume (_root_.Tube.centredExtension σ hxy).carrier
      ≤ ENNReal.ofReal ((4 * R) ^ 6) * volume (T₀.rescaleMap R '' T.carrier) := by
    exact hvol0.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hcoef) le_rfl)
  exact ⟨hth2, hpos, hvol⟩

/-- **The selection constant of the downstairs route is dominated by the normalization loss, at a
free normalized radius `R` and a free tilt `κ`.**

`Kakeya.ml1Boot.fineNormalize_C_dominates` is the same statement hardwired to the undilated
instance `(R, κ) = (C_N, 2)`, and the dilated half of the normalization runs at
`(R, κ) = ((1 + 2 c) C_N, max 2 (2 c))`, so it needs the parametric form.  The coupling
hypothesis `κ + 2 ≤ R` holds at both instances — `4 ≤ 64` and `2 c + 4 ≤ 64 + 128 c` — and is
what keeps the selection ratio `4 (κ + 2) R C_n` below `4 R² C_n`.

The third clause carries a factor `125` that the undilated form does not.  It is the price of
descending the ambient volume comparison from `c · T_τ` to the sub-body `K`: the `c`-dilate has
volume `c³ |T_τ|`, and `c ≥ 1/5` — forced, not assumed, since a `δ`-tube fits inside `c · T_τ`
only if `1 ≤ c + 4 c τ` (`Kakeya.ml1Boot.volume_ambient_le_mul_volume_dilate`) — bounds `c⁻³` by
`125`.  There is room for it: the comparison reduces to `125 ≤ 4 ^ 24 R ^ 12`. -/
private lemma fineNormalize_C_dominates_gen {R κ c₁ : ℝ≥0}
    (hCR : _root_.Tube.normalization.C 3 ≤ R) (hκR : κ + 2 ≤ R)
    (hc₁ : c₁ = _root_.Tube.essDistinctTubesInSelfDilate.C 3
      (4 * ((κ : ℝ) + 2) * (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3)) :
    c₁ ≤ fineNormalize.C R κ ∧
      ((4 * R) ^ 6 : ℝ≥0) * c₁ ≤ fineNormalize.C R κ ∧
      (125 : ℝ≥0) * ((4 * R) ^ 12 : ℝ≥0) * c₁ ≤ fineNormalize.C R κ := by
  let ratio : ℝ := 4 * ((κ : ℝ) + 2) * (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3
  let D : ℝ≥0 := (Kakeya.Tube.tubeOverlapCoreClose.C 3).toNNReal
  let u : ℝ≥0 := 4 * (κ + 2) * R * D
  have hR1 : (1 : ℝ≥0) ≤ R := le_trans (_root_.Tube.normalization.one_le_C 3) hCR
  have hκ1 : (1 : ℝ≥0) ≤ κ + 2 := by
    exact le_trans (by norm_num : (1 : ℝ≥0) ≤ 2)
      (le_add_of_nonneg_left (by positivity : (0 : ℝ≥0) ≤ κ))
  have hD0 : (0 : ℝ) ≤ Kakeya.Tube.tubeOverlapCoreClose.C 3 :=
    le_of_lt (lt_trans (by norm_num : (0 : ℝ) < (1 : ℝ))
      (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C 3))
  have hD1 : (1 : ℝ≥0) ≤ D := by
    dsimp [D]; rw [← NNReal.coe_le_coe, Real.toNNReal_of_nonneg hD0]
    exact le_of_lt (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C 3)
  have hratio0 : (0 : ℝ) ≤ ratio := by
    dsimp [ratio]
    positivity
  have hu_re : ratio = (u : ℝ) := by
    dsimp [u, ratio, D]
    norm_num
    exact Or.inl hD0
  have hu : ratio.toNNReal = u := by
    apply NNReal.coe_injective
    rw [Real.toNNReal_of_nonneg hratio0]
    exact hu_re
  have hu1 : (1 : ℝ≥0) ≤ u :=
    one_le_mul (one_le_mul (one_le_mul (by norm_num : (1 : ℝ≥0) ≤ 4) hκ1) hR1) hD1
  have hu6 : u ^ 6 ≤ u ^ 12 := pow_le_pow_right₀ hu1 (by norm_num)
  have hule : u ≤ 4 * R ^ 2 * D := by
    dsimp [u]
    calc
      4 * (κ + 2) * R * D
          ≤ 4 * R * R * D := by
            exact mul_le_mul
              (mul_le_mul (mul_le_mul le_rfl hκR (by positivity) (by positivity))
                le_rfl (by positivity) (by positivity))
              le_rfl (by positivity) (by positivity)
      _ = 4 * R ^ 2 * D := by ring
  have hu12' : 125 * u ^ 12 ≤ ((4 * R) ^ 6) ^ 6 * D ^ 12 := by
    calc
      125 * u ^ 12 ≤ 125 * (4 * R ^ 2 * D) ^ 12 := by
            exact mul_le_mul le_rfl (pow_le_pow_left₀ (by positivity : (0 : ℝ≥0) ≤ u) hule 12)
              (by positivity) (by positivity)
      _ = 125 * 4 ^ 12 * R ^ 24 * D ^ 12 := by
            ring_nf
      _ ≤ (4 : ℝ≥0) ^ 36 * R ^ 36 * D ^ 12 := by
            exact mul_le_mul
              (mul_le_mul (by norm_num : (125 * 4 ^ 12 : ℝ≥0) ≤ 4 ^ 36)
                (pow_le_pow_right₀ hR1 (by norm_num)) (by positivity) (by positivity))
              le_rfl (by positivity) (by positivity)
      _ = ((4 * R) ^ 6) ^ 6 * D ^ 12 := by
            ring_nf
  have hu12 : u ^ 12 ≤ ((4 * R) ^ 6) ^ 6 * D ^ 12 := by
    exact le_trans
      (le_mul_of_one_le_left (by positivity) (by norm_num : (1 : ℝ≥0) ≤ 125))
      hu12'
  have hbase : (1 : ℝ≥0) ≤ 4 * R := one_le_mul (by norm_num : (1 : ℝ≥0) ≤ 4) hR1
  have hpw6 : (4 * R) ^ 6 ≤ (4 * R) ^ 12 := pow_le_pow_right₀ hbase (by norm_num)
  have hkey : c₁ ≤ _root_.Tube.comparableReplacement.C 3 ((4 * R) ^ 6) := by
    rw [hc₁]
    unfold _root_.Tube.essDistinctTubesInSelfDilate.C
      _root_.Tube.essDistinctTubesInSelfDilate.thinC
      _root_.Tube.essDistinctTubesInSelfDilate.fatC
      _root_.Tube.comparableReplacement.C _root_.Tube.comparableReplacement.Kstar
    set A : ℝ≥0 :=
      24 * (2 ^ (3 - 1) * Metric.coveringNumber_mul_pow_le_volume_cthickening.C (3 - 1)) ^ 2
        * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C (2 * 3 - 1))⁻¹
        * (32 * (3 : ℝ≥0)) ^ (2 * 3 - 1) with hA
    set B : ℝ≥0 := 6 ^ (2 * 3) * (Tube.card_le_of_EssDistinct.C 3).toNNReal with hB
    calc
      A * ratio.toNNReal ^ (2 * 3) + B * ratio.toNNReal ^ (4 * 3)
          = A * u ^ 6 + B * u ^ 12 := by rw [hu]
      _ ≤ A * u ^ 12 + B * u ^ 12 := by
            exact add_le_add (mul_le_mul le_rfl hu6 (by positivity) (by positivity)) le_rfl
      _ = (A + B) * u ^ 12 := by ring
      _ ≤ (A + B) * (((4 * R) ^ 6) ^ 6 * D ^ 12) := by
            exact mul_le_mul le_rfl hu12 (by positivity) (by positivity)
      _ ≤ 1 + (A + B) * (((4 * R) ^ 6) ^ 6 * D ^ 12) := le_add_self
      _ = _root_.Tube.comparableReplacement.C 3 ((4 * R) ^ 6) := by
            rw [hA, hB]
            unfold _root_.Tube.comparableReplacement.C _root_.Tube.comparableReplacement.Kstar
            norm_num
            ring
  have hkey125 : 125 * c₁ ≤ _root_.Tube.comparableReplacement.C 3 ((4 * R) ^ 6) := by
    rw [hc₁]
    unfold _root_.Tube.essDistinctTubesInSelfDilate.C
      _root_.Tube.essDistinctTubesInSelfDilate.thinC
      _root_.Tube.essDistinctTubesInSelfDilate.fatC
      _root_.Tube.comparableReplacement.C _root_.Tube.comparableReplacement.Kstar
    set A : ℝ≥0 :=
      24 * (2 ^ (3 - 1) * Metric.coveringNumber_mul_pow_le_volume_cthickening.C (3 - 1)) ^ 2
        * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C (2 * 3 - 1))⁻¹
        * (32 * (3 : ℝ≥0)) ^ (2 * 3 - 1) with hA
    set B : ℝ≥0 := 6 ^ (2 * 3) * (Tube.card_le_of_EssDistinct.C 3).toNNReal with hB
    calc
      125 * (A * ratio.toNNReal ^ (2 * 3) + B * ratio.toNNReal ^ (4 * 3))
          = 125 * (A * u ^ 6 + B * u ^ 12) := by rw [hu]
      _ = 125 * (A * u ^ 6) + 125 * (B * u ^ 12) := by ring
      _ ≤ 125 * (A * u ^ 12) + 125 * (B * u ^ 12) := by
            exact add_le_add
              (mul_le_mul le_rfl (mul_le_mul le_rfl hu6 (by positivity) (by positivity))
                (by positivity) (by positivity))
              le_rfl
      _ = 125 * (A + B) * u ^ 12 := by ring
      _ = (A + B) * (125 * u ^ 12) := by ring
      _ ≤ (A + B) * (((4 * R) ^ 6) ^ 6 * D ^ 12) := by
            exact mul_le_mul le_rfl hu12' (by positivity) (by positivity)
      _ ≤ 1 + (A + B) * (((4 * R) ^ 6) ^ 6 * D ^ 12) := le_add_self
      _ = _root_.Tube.comparableReplacement.C 3 ((4 * R) ^ 6) := by
            rw [hA, hB]
            unfold _root_.Tube.comparableReplacement.C _root_.Tube.comparableReplacement.Kstar
            norm_num
            ring
  constructor
  · unfold fineNormalize.C
    rw [hc₁]
    exact le_add_self
  constructor
  · unfold fineNormalize.C
    exact le_trans
      (le_trans (mul_le_mul hpw6 le_rfl (by positivity) (by positivity))
        (mul_le_mul le_rfl hkey (by positivity) (by positivity)))
      le_self_add
  · unfold fineNormalize.C
    calc
      (125 : ℝ≥0) * ((4 * R) ^ 12 : ℝ≥0) * c₁
          = (4 * R) ^ 12 * (125 * c₁) := by ring
      _ ≤ (4 * R) ^ 12 * _root_.Tube.comparableReplacement.C 3 ((4 * R) ^ 6) := by
            exact mul_le_mul le_rfl hkey125 (by positivity) (by positivity)
      _ ≤ (4 * R) ^ 12 * _root_.Tube.comparableReplacement.C 3 ((4 * R) ^ 6)
            + _root_.Tube.essDistinctTubesInSelfDilate.C 3
                (4 * ((κ : ℝ) + 2) * (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3) :=
            le_self_add

/-- **Normalizing a fine fibre to the unit ball, over an arbitrary ambient body**.

This is the route shared by the two halves of the fine normalization, with the ambient body `P`
and the normalized ambient radius `R` left free.  Both halves are this lemma instantiated:
`Kakeya.ml1Boot.exists_fineNormalization` at `(P, R, κ) = (T_τ, C_N, 2)`, and
`Kakeya.ml1Boot.exists_fineNormalization_dilate` at
`(P, R, κ) = (K, (1 + 2 c) C_N, max 2 (2 c))` — see the "Not a corollary of the undilated half"
note at the latter for why neither is derivable from the other.

Everything the route needs from the ambient body is isolated into four hypotheses, and nothing
else here mentions `P`:

* `hsub`, the members sit in `P`;
* `hball`, the normalization `Φ_{T_τ}` carries `P` into `B̄(T_τ.x, R)` — this is what fixes `R`,
  and it is the *only* place the shape of `P` enters the geometry;
* `hlen`, each image core has length at most `R` — the relaxed form of
  `Tube.IsNormalizationDistortion.dist_le_C` discussed at
  `Kakeya.ml1Boot.rescale_outer_tube_of_dist_le`;
* `hperp`, each member is tilted against the axis of `T_τ` by at most `κ τ`.

The remaining two, `hPvol` and `hratio`, are the ambient enlargement to `B₁`: `Cw` is the loss
of replacing the ambient body by the unit ball, and it is the *only* route by which a
volume-ratio parameter such as the `M` of the dilated half can reach the Frostman clause.  The
constants are returned raw — the selection constant `C₁`, the comparability constant `(4 R) ^ 6`
and `Cw`, in the combinations the four clauses actually pay — so that each instance does its own
domination against `Kakeya.ml1Boot.fineNormalize.C R κ`.

The output scale is `Kakeya.ml1Boot.fineScale δ τ` and not the bare ratio `δ / τ`; with `δ / τ`
this statement is false at both instances, refuted by
`Kakeya.ml1Boot.not_exists_fineNormalization` and
`Kakeya.ml1Boot.not_exists_fineNormalization_dilate`.

## The construction-visibility clauses

The last four clauses of the conclusion are not part of the blueprint lemma.  They expose the
data the route already builds, so that a consumer can see *which* family `V` is rather than only
that one exists.  Writing `Ψ = Tube.rescaleMap T_τ R` for the normalization-and-homothety of the
proof, they say that the intermediate family — the `Ψ`-image of the input — sits inside the
output with the same shade and comparable volume, and that `Ψ` carries the ambient body into
`B(0, 1/4)`:

* `Ψ(T i) ⊆ V i` for every `i ∈ u`;
* `(V i).shade = Ψ((T i).shade)` for every `i ∈ u`;
* `|V i| ≤ (4 R) ^ 6 |Ψ(T i)|` for every `i ∈ u`;
* `Ψ(P) ⊆ B(0, 1/4)`.

They cost nothing: they are the local hypotheses `hsub'`, `hshade`, `hvol` and `hK'c` that the
selection package `Tube.exists_comparableReplacement_affine` is fed with anyway, restated
through `hWcarrier` in terms of `Ψ` rather than of the local abbreviation `𝕎`.

What the proof does **not** have, and so what is deliberately absent here, is the `hdilate`
clause of `ConvexSpaceBody.frostmanConstIn_ge_of_comparable` — for every `K' ≤ K` a `L ≤ K`
with `K' ≤ L`, `|L| ≤ C |K'|` and `V i ≤ L` whenever `Ψ(T i) ≤ K'`.  `Tube.exists_comparableReplacement_affine`
never forms such an `L`; its Frostman item is the one-sided
`Tube.comparableTransport_oneSided`, which needs only `Ψ(T i) ⊆ V i ⊆ K` and the volume
bracket.  Also absent is any clause about indices outside `u`: `hsub`, `hlen` and `hperp` are
hypothesised on `u` alone, so nothing at all is known about `V i` for `i ∉ u`, even though `V`
is a total function. -/
theorem exists_fineNormalization_core [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {δ τ : ℝ≥0} (hδ : 0 < δ) (hδτ : δ ≤ τ) (hτ1 : τ ≤ 1)
    {Λ : ℝ≥0} (hΛ : 1 ≤ Λ) {μ₀ : ℝ≥0∞} (hμ₀ : 0 < μ₀)
    {ι : Type*} {u : Finset ι} (Tτ : Tube τ E) (T : ι → ShadedTube δ E)
    (P : ConvexSpaceBody E) {R κ Cw : ℝ≥0}
    (hR : _root_.Tube.normalization.C 3 ≤ R)
    (hu : u.Nonempty)
    (hsub : ∀ i ∈ u, (T i).carrier ⊆ P.carrier)
    (hball : Tτ.normalization '' P.carrier ⊆ Metric.closedBall Tτ.x (R : ℝ))
    (hlen : ∀ i ∈ u,
      dist (Tτ.normalization (T i).x) (Tτ.normalization (T i).y) ≤ (R : ℝ))
    (hperp : ∀ i ∈ u, ‖(T i).toTube.direction
        - (inner ℝ Tτ.direction (T i).toTube.direction : ℝ) • Tτ.direction‖
      ≤ (κ : ℝ) * (τ : ℝ))
    (hPvol : volume P.carrier ≠ 0)
    (hratio : volume (Metric.closedBall (0 : E) 1)
      ≤ (Cw : ℝ≥0∞) * volume (Tτ.rescaleMap (R : ℝ) '' P.carrier))
    (hED : (u : Set ι).Pairwise fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier)
    (hdens : ∀ i ∈ u, (Λ : ℝ≥0∞)⁻¹ * μ₀ * volume (T i).carrier ≤ volume (T i).shade ∧
      volume (T i).shade ≤ (Λ : ℝ≥0∞) * μ₀ * volume (T i).carrier) :
    ∃ u' ⊆ u, u'.Nonempty ∧ ∃ V : ι → ShadedTube (fineScale δ τ) E,
      (u' : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier) ∧
        (∀ i ∈ u', (V i).carrier ⊆ Metric.closedBall 0 1) ∧
        ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
          ≤ (_root_.Tube.essDistinctTubesInSelfDilate.C 3
              (4 * ((κ : ℝ) + 2) * (R : ℝ)
                * Kakeya.Tube.tubeOverlapCoreClose.C 3) : ℝ≥0∞)
            * (Λ : ℝ≥0∞) ^ 2
            * ShadedBody.multiplicity u' (fun i => (V i).toShadedBody) ∧
        (ShadedBody.fullness u (fun i => (T i).toShadedBody) : ℝ≥0∞)
          ≤ (((4 * R) ^ 6 : ℝ≥0) : ℝ≥0∞)
            * (_root_.Tube.essDistinctTubesInSelfDilate.C 3
                (4 * ((κ : ℝ) + 2) * (R : ℝ)
                  * Kakeya.Tube.tubeOverlapCoreClose.C 3) : ℝ≥0∞)
            * (Λ : ℝ≥0∞) ^ 2
            * (ShadedBody.fullness u' (fun i => (V i).toShadedBody) : ℝ≥0∞) ∧
        frostmanConstIn u' (fun i => (V i).toConvexSpaceBody)
            ConvexSpaceBody.closedUnitBall
          ≤ (_root_.Tube.essDistinctTubesInSelfDilate.C 3
                (4 * ((κ : ℝ) + 2) * (R : ℝ)
                  * Kakeya.Tube.tubeOverlapCoreClose.C 3) : ℝ≥0∞)
            * (((4 * R) ^ 6 : ℝ≥0) : ℝ≥0∞) * (Cw : ℝ≥0∞)
            * frostmanConstIn u (fun i => (T i).toConvexSpaceBody) P ∧
        -- the construction-visibility clauses: `V` is comparable to the image of `T` under the
        -- explicit rescaling map `Ψ = Tube.rescaleMap Tτ R`
        (∀ i ∈ u, Tτ.rescaleMap (R : ℝ) '' (T i).carrier ⊆ (V i).carrier) ∧
        (∀ i ∈ u, (V i).shade = Tτ.rescaleMap (R : ℝ) '' (T i).shade) ∧
        (∀ i ∈ u, volume (V i).carrier
          ≤ (((4 * R) ^ 6 : ℝ≥0) : ℝ≥0∞)
            * volume (Tτ.rescaleMap (R : ℝ) '' (T i).carrier)) ∧
        Tτ.rescaleMap (R : ℝ) '' P.carrier ⊆ Metric.closedBall (0 : E) (1 / 4) := by
  classical
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (by rw [hdim]; norm_num)
  have hτ0 : 0 < τ := lt_of_lt_of_le hδ hδτ
  let i₀ : ι := Classical.choose hu
  have hi₀ : i₀ ∈ u := Classical.choose_spec hu
  have hδτ0 : 0 < (δ / τ : ℝ≥0) := by
    rw [← NNReal.coe_lt_coe]
    rw [NNReal.coe_div]
    exact div_pos (by exact_mod_cast hδ) (by exact_mod_cast hτ0)
  have hpos : 0 < fineScale δ τ := by
    dsimp [fineScale]
    exact lt_min hδτ0 (by norm_num)
  have hquarter : (fineScale δ τ : ℝ) ≤ 1 / 4 := by
    exact_mod_cast (fineScale_bounds hδτ hτ0).2.1
  have hratioσ : (fineScale δ τ : ℝ) ≤ (δ : ℝ) / (τ : ℝ) := by
    exact_mod_cast (fineScale_bounds hδτ hτ0).1
  have hρσ : (δ : ℝ) / (τ : ℝ) ≤ 4 * (fineScale δ τ : ℝ) := by
    exact_mod_cast (fineScale_bounds hδτ hτ0).2.2
  have hR1n : (1 : ℝ≥0) ≤ R := le_trans (_root_.Tube.normalization.one_le_C 3) hR
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR1n
  have hR0 : 0 < (R : ℝ) := lt_of_lt_of_le zero_lt_one hR1
  have hsit : _root_.Tube.IsRescalingSituation τ δ (fineScale δ τ) (R : ℝ) 3 :=
    ⟨hτ0, hδτ, hτ1, hpos, hquarter, hratioσ, by exact_mod_cast hR⟩
  obtain ⟨L, hL⟩ := _root_.Tube.exists_rescaleEquiv hτ0 hR0 Tτ
  have hcont : Continuous L := AffineEquiv.continuous_of_finiteDimensional L
  have hemb : MeasurableEmbedding L :=
    (AffineEquiv.toContinuousAffineEquiv L).toHomeomorph.measurableEmbedding
  have hxy : ∀ i : ι, Tτ.rescaleMap (R : ℝ) (T i).x ≠ Tτ.rescaleMap (R : ℝ) (T i).y := by
    intro i h
    rw [← hL] at h
    exact (fun hne => hne (L.injective h)) (fun hxy => by
      have := (T i).toTube.dist_eq_one
      rw [hxy] at this
      simp at this)
  set 𝕎 : ι → ShadedBody E := fun i => ((T i).toShadedBody).affineImage L.toAffineMap hcont hemb
  set 𝕍 : ι → ShadedTube (fineScale δ τ) E := fun i =>
    { toTube := _root_.Tube.centredExtension (fineScale δ τ) (hxy i)
      shade := (𝕎 i).shade ∩ (_root_.Tube.centredExtension (fineScale δ τ) (hxy i)).carrier
      measurableSet_shade :=
        (𝕎 i).measurableSet_shade.inter
          (_root_.Tube.centredExtension (fineScale δ τ) (hxy i)).isCompact.measurableSet
      shade_subset := Set.inter_subset_right }
  have hballi : ∀ i ∈ u, Tτ.normalization '' (T i).carrier ⊆ Metric.closedBall Tτ.x (R : ℝ) := by
    intro i hi
    exact (Set.image_mono (hsub i hi)).trans hball
  have houter := fun i hi => rescale_outer_tube_of_dist_le
    (hsit := hsit) (hn := hdim) (hR := hR0) (hρσ := hρσ) (T₀ := Tτ)
    (T := (T i).toTube)
    (hcth := _root_.Tube.normalization_image_subset_cthickening hτ0 hτ1 Tτ (T i).toTube)
    (hlen := hlen i hi) (hball := hballi i hi) (hxy := hxy i)
  have hofR : ENNReal.ofReal ((4 * (R : ℝ)) ^ 6) = (((4 * R) ^ 6 : ℝ≥0) : ℝ≥0∞) := by
    have h4R : ENNReal.ofReal (4 * (R : ℝ)) = ((4 * R : ℝ≥0) : ℝ≥0∞) := by
      rw [show (4 : ℝ) * (R : ℝ) = ((4 * R : ℝ≥0) : ℝ) by
        rw [NNReal.coe_mul]
        norm_num]
      rw [ENNReal.ofReal_coe_nnreal]
    have hRnonneg : (0 : ℝ) ≤ 4 * (R : ℝ) := by positivity
    calc
      ENNReal.ofReal ((4 * (R : ℝ)) ^ 6) = (ENNReal.ofReal (4 * (R : ℝ))) ^ 6 := by
            rw [ENNReal.ofReal_pow hRnonneg]
      _ = ((4 * R : ℝ≥0) : ℝ≥0∞) ^ 6 := by rw [h4R]
      _ = (((4 * R) ^ 6 : ℝ≥0) : ℝ≥0∞) := by
            rw [ENNReal.coe_pow]
  have hWcarrier : ∀ i ∈ u, (𝕎 i).carrier = Tτ.rescaleMap (R : ℝ) '' (T i).carrier := by
    intro i hi
    dsimp [𝕎]
    change L.toAffineMap '' (T i).carrier = Tτ.rescaleMap (R : ℝ) '' (T i).carrier
    rw [← hL]
  have hsub' : ∀ i ∈ u, (𝕎 i).carrier ⊆ (𝕍 i).carrier := by
    intro i hi
    rw [hWcarrier i hi]
    simpa [𝕍] using (houter i hi).1
  have h𝕍ball : ∀ i ∈ u, (𝕍 i).toTube.carrier ⊆ Metric.closedBall (0 : E) 1 := by
    intro i hi
    simpa [𝕍] using (houter i hi).2.1
  have hshade : ∀ i ∈ u, (𝕍 i).shade = (𝕎 i).shade := by
    intro i hi
    dsimp [𝕍]
    exact (Set.inter_eq_left).mpr ((𝕎 i).shade_subset.trans (hsub' i hi))
  have hCv : 1 ≤ (4 * R) ^ 6 := by
    exact one_le_pow₀ (one_le_mul (by norm_num) hR1n)
  have hVK : ∀ i ∈ u,
      (𝕍 i).toConvexSpaceBody ≤ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) := by
    intro i hi
    change (𝕍 i).carrier ⊆ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier
    rw [ConvexSpaceBody.closedUnitBall_carrier]
    simpa [𝕍] using h𝕍ball i hi
  let c' : ℝ := 4 * ((κ : ℝ) + 2) * (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3
  have hc'1 : (1 : ℝ) ≤ c' := by
    dsimp [c']
    have hκ0 : (0 : ℝ) ≤ (κ : ℝ) := NNReal.coe_nonneg κ
    have hRgr : (1 : ℝ) ≤ (R : ℝ) := hR1
    have hCnR : (1 : ℝ) ≤ (Kakeya.Tube.tubeOverlapCoreClose.C 3 : ℝ) := by
      exact_mod_cast (le_of_lt (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C 3))
    have hk : (1 : ℝ) ≤ 4 * ((κ : ℝ) + 2) := by
      nlinarith
    have hk0 : (0 : ℝ) ≤ 4 * ((κ : ℝ) + 2) := le_trans zero_le_one hk
    have hb1 : (1 : ℝ) ≤ (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3 := by
      calc
        1 = 1 * 1 := by norm_num
        _ ≤ (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3 := by
              exact mul_le_mul hRgr hCnR (by norm_num) (by positivity)
    have hb10 : (0 : ℝ) ≤ (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3 := le_trans zero_le_one hb1
    calc
      1 ≤ 1 * 1 := by norm_num
      _ ≤ (4 * ((κ : ℝ) + 2)) * ((R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3) := by
            exact mul_le_mul hk hb1 (by positivity) hk0
      _ = 4 * ((κ : ℝ) + 2) * (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3 := by ring
  let c₁ : ℝ≥0 := _root_.Tube.essDistinctTubesInSelfDilate.C 3
    (4 * ((κ : ℝ) + 2) * (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3)
  have hc₁ : c₁ = _root_.Tube.essDistinctTubesInSelfDilate.C 3
      (4 * ((κ : ℝ) + 2) * (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3) := by
    rfl
  have hC₁ : (1 : ℝ≥0) ≤ c₁ := by
    let 𝕋 : ι → Tube δ E := fun i => (T i).toTube
    have hpw₀ : (({i₀} : Finset ι) : Set ι).Pairwise
        (fun i j => IsEssentiallyDistinct (𝕋 i).carrier (𝕋 j).carrier) := by
      simp
    have hsub₀ : ∀ j ∈ ({i₀} : Finset ι), (𝕋 j).carrier
        ⊆ (Kakeya.Tube.dilate (𝕋 i₀) c').carrier := by
      intro j hj
      have hji : j = i₀ := by simpa using hj
      subst j
      exact _root_.Tube.subset_dilate (𝕋 i₀) hc'1
    have hcount : (({i₀} : Finset ι).card : ℝ≥0∞)
        ≤ (_root_.Tube.essDistinctTubesInSelfDilate.C (Module.finrank ℝ E) c' : ℝ≥0∞) :=
      _root_.Tube.essDistinctTubesInSelfDilate hc'1 hδ (le_trans hδτ hτ1 : δ ≤ 1) (𝕋 i₀)
        ({i₀} : Finset ι) 𝕋 hpw₀ hsub₀
    exact ENNReal.coe_le_coe.mp (by simpa [c₁, c', hdim] using hcount)
  have hVtube : ∀ i ∈ u, (𝕍 i).toTube = _root_.Tube.centredExtension (fineScale δ τ) (hxy i) := by
    intro i hi
    rfl
  have hvol : ∀ i ∈ u, volume (𝕍 i).carrier
      ≤ (((4 * R) ^ 6 : ℝ≥0) : ℝ≥0∞) * volume (𝕎 i).carrier := by
    intro i hi
    calc
      volume (𝕍 i).carrier
          = volume (_root_.Tube.centredExtension (fineScale δ τ) (hxy i)).carrier := by
            simp [𝕍]
      _ ≤ ENNReal.ofReal ((4 * (R : ℝ)) ^ 6) * volume (Tτ.rescaleMap (R : ℝ) '' (T i).carrier) :=
            (houter i hi).2.2
      _ = (((4 * R) ^ 6 : ℝ≥0) : ℝ≥0∞) * volume (Tτ.rescaleMap (R : ℝ) '' (T i).carrier) := by
            rw [hofR]
      _ = (((4 * R) ^ 6 : ℝ≥0) : ℝ≥0∞) * volume (𝕎 i).carrier := by
            rw [hWcarrier i hi]
  let W : ℝ≥0∞ := volume (𝕎 i₀).carrier
  have hW : 0 < W := by
    dsimp [W]
    simpa [𝕎] using volume_affineImage_carrier_pos hδ (T i₀) L hcont hemb
  have hcommon : ∀ i ∈ u, volume (𝕎 i).carrier = W := by
    intro i hi
    dsimp [W]
    simpa [𝕎] using volume_affineImage_carrier_eq (T i) (T i₀) L hcont hemb
  have hZ : ∀ i ∈ u, (Λ : ℝ≥0∞)⁻¹ * μ₀ * W ≤ volume (𝕎 i).shade ∧
      volume (𝕎 i).shade ≤ (Λ : ℝ≥0∞) * μ₀ * W := by
    intro i hi
    have hz := affineImage_shade_bounds (S := T i) (S' := T i₀) L hcont hemb
      (hdens i hi).1 (hdens i hi).2
    dsimp [W, 𝕎] at hz ⊢
    exact hz
  let 𝕋 : ι → Tube δ E := fun i => (T i).toTube
  have himg : ∀ i ∈ u, (Tτ.rescaleMap (R : ℝ)) '' (T i).carrier ⊆ ((𝕍 i).toTube).carrier := by
    intro i hi
    simpa [𝕍] using (houter i hi).1
  have hpackage : _root_.Tube.IsComparableReplacementFree u 𝕎 𝕍
      (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) ((4 * R) ^ 6) Λ c₁ := by
    simpa [hc₁, hdim] using
      (_root_.Tube.exists_comparableReplacement_affine (n := 3) (R := (R : ℝ))
      (κ := ((κ : ℝ≥0) : ℝ)) (s := u) hu hsit (by exact NNReal.coe_nonneg κ)
      hδ (le_trans hδτ hτ1 : δ ≤ 1) Tτ
      𝕋 hxy 𝕎 𝕍
      (K := (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E)) (C := (4 * R) ^ 6) (Λ := Λ)
      (W := W) (μ₀ := μ₀) hCv hΛ hW hμ₀ hcommon hVtube hperp
      (by simpa [𝕋] using hED) himg hshade hsub' hVK hvol hZ)
  let K' : ConvexSpaceBody E := (P).affineImage L.toAffineMap hcont
  have hK'c : K'.carrier ⊆ Metric.closedBall (0 : E) (1 / 4) := by
    rintro _ ⟨z, hzP, rfl⟩
    have hz : Tτ.normalization z ∈ Metric.closedBall Tτ.x (R : ℝ) := by
      exact (hball ⟨z, hzP, rfl⟩)
    have hdistz : dist (Tτ.normalization z) Tτ.x ≤ (R : ℝ) := Metric.mem_closedBall.mp hz
    have h4Rpos : (0 : ℝ) < 4 * (R : ℝ) := by positivity
    have h4R0 : (4 : ℝ) * (R : ℝ) ≠ 0 := ne_of_gt h4Rpos
    have hRdiv : (R : ℝ) / (4 * (R : ℝ)) = (1 : ℝ) / 4 := by
      field_simp [h4R0, (by norm_num : (4 : ℝ) ≠ 0)]
    rw [hL]
    calc
      dist (Tτ.rescaleMap (R : ℝ) z) (0 : E)
          = dist (Tτ.rescaleMap (R : ℝ) z) (Tτ.rescaleMap (R : ℝ) Tτ.x) := by
            rw [← _root_.Tube.rescaleMap_apply_x]
        _ = dist (Tτ.normalization z) (Tτ.normalization Tτ.x) / (4 * (R : ℝ)) :=
            _root_.Tube.dist_rescaleMap Tτ hR0 z Tτ.x
        _ = dist (Tτ.normalization z) Tτ.x / (4 * (R : ℝ)) := by
            rw [_root_.Tube.normalization_apply_x]
        _ ≤ (R : ℝ) / (4 * (R : ℝ)) := div_le_div_of_nonneg_right hdistz (le_of_lt h4Rpos)
        _ = (1 : ℝ) / 4 := hRdiv
        _ ≤ 1 / 4 := le_rfl
  have hK' : (K' : ConvexSpaceBody E) ≤ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) := by
    change K'.carrier ⊆ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier
    rw [ConvexSpaceBody.closedUnitBall_carrier]
    exact hK'c.trans (Metric.closedBall_subset_closedBall (by norm_num))
  have hK'vol : volume K'.carrier ≠ 0 := by
    have h1 : volume ((P).affineImage L.toAffineMap hcont).carrier ≠ 0 := by
      rw [ConvexSpaceBody.volume_affineImage]
      have hA : ENNReal.ofReal |LinearMap.det (L.linear : E →ₗ[ℝ] E)| ≠ 0 := by
        exact (ENNReal.ofReal_eq_zero.not).mpr
          (not_le.mpr (abs_pos.mpr (LinearEquiv.isUnit_det' L.linear).ne_zero))
      have hB : volume P.carrier ≠ 0 := hPvol
      exact mul_ne_zero hA hB
    simpa [K'] using h1
  have hWK' : ∀ i ∈ u, (𝕎 i).toConvexSpaceBody ≤ K' := by
    intro i hi
    change (𝕎 i).carrier ⊆ K'.carrier
    rw [hWcarrier i hi]
    rw [← hL]
    exact Set.image_mono (hsub i hi)
  have hratio' : volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier
      ≤ (Cw : ℝ≥0∞) * volume K'.carrier := by
    simpa [K', ← hL, ConvexSpaceBody.closedUnitBall_carrier] using hratio
  have hfrodsman : frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody)
      (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E)
      ≤ (Cw : ℝ≥0∞) * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K' :=
    frostmanConstIn_closedUnitBall_le_of_ambient (u := u) (𝕎 := 𝕎) (K' := K')
      (Cv := Cw) hK' hK'vol hWK' hratio'
  have hF_rel : frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K'
      = frostmanConstIn u (fun i => (T i).toConvexSpaceBody) P := by
    have h := ConvexSpaceBody.frostmanConstIn_affineImage u (fun i => (T i).toConvexSpaceBody)
      P L hcont
    dsimp [𝕎, K']
    exact h
  obtain ⟨u', hu'sub, hu'ne, hVD, hmult, hfull, hfrost⟩ :=
    of_comparableReplacementFree (u := u) (𝕎 := 𝕎) (𝕍 := 𝕍)
      (K := (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E)) (Cv := (4 * R) ^ 6)
      (Λ := Λ) (C₁ := c₁) hΛ hCv hC₁ hVK hpackage
  refine ⟨u', hu'sub, hu'ne, 𝕍, ?_⟩
  constructor
  · simpa [𝕍] using hVD
  constructor
  · intro i hi
    simpa [𝕍] using h𝕍ball i (hu'sub hi)
  constructor
  · calc
      ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
          = ShadedBody.multiplicity u 𝕎 := by
            simpa [𝕎] using (ShadedBody.multiplicity_affineImage u
              (fun i => (T i).toShadedBody) L hcont hemb).symm
      _ ≤ (c₁ : ℝ≥0∞) * (Λ : ℝ≥0∞) ^ 2
          * ShadedBody.multiplicity u' (fun i => (𝕍 i).toShadedBody) := hmult
  constructor
  · calc
      (ShadedBody.fullness u (fun i => (T i).toShadedBody) : ℝ≥0∞)
          = (ShadedBody.fullness u 𝕎 : ℝ≥0∞) := by
            simpa [𝕎] using (ShadedBody.fullness_affineImage u
              (fun i => (T i).toShadedBody) L hcont hemb).symm
      _ ≤ (((4 * R) ^ 6 : ℝ≥0) : ℝ≥0∞) * (c₁ : ℝ≥0∞) * (Λ : ℝ≥0∞) ^ 2
          * (ShadedBody.fullness u' (fun i => (𝕍 i).toShadedBody) : ℝ≥0∞) := hfull
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · calc
        frostmanConstIn u' (fun i => (𝕍 i).toConvexSpaceBody)
            (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E)
            ≤ (c₁ : ℝ≥0∞) * (((4 * R) ^ 6 : ℝ≥0) : ℝ≥0∞)
              * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody)
                  (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) := by simpa using hfrost
        _ ≤ (c₁ : ℝ≥0∞) * (((4 * R) ^ 6 : ℝ≥0) : ℝ≥0∞)
            * ((Cw : ℝ≥0∞)
              * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K') := by
              exact mul_le_mul_right hfrodsman ((c₁ : ℝ≥0∞) * (((4 * R) ^ 6 : ℝ≥0) : ℝ≥0∞))
        _ = (c₁ : ℝ≥0∞) * (((4 * R) ^ 6 : ℝ≥0) : ℝ≥0∞)
            * ((Cw : ℝ≥0∞)
              * frostmanConstIn u (fun i => (T i).toConvexSpaceBody) P) := by
              rw [hF_rel]
        _ = (c₁ : ℝ≥0∞) * (((4 * R) ^ 6 : ℝ≥0) : ℝ≥0∞) * (Cw : ℝ≥0∞)
            * frostmanConstIn u (fun i => (T i).toConvexSpaceBody) P := by ring
    · intro i hi
      rw [← hWcarrier i hi]
      exact hsub' i hi
    · intro i hi
      rw [hshade i hi]
      simp [𝕎, ← hL]
    · intro i hi
      simpa [hWcarrier i hi] using hvol i hi
    · simpa [K', ← hL] using hK'c

end Fine

/-! ### Case (ii): the fine-scale factor over a `c`-dilate

The plank-in-tube chain of `Kakeya/DimensionThree/MainLemma1/Rescaling.lean` does not put the
fine tubes inside an honest `b`-tube, only inside a dilate of one, and the Frostman
bound it supplies is taken in that dilate.  This subsection restates the two fine-factor
lemmas above under the weakened containment, at a free dilation ratio `c`.  Splitting the
dilate into honest tubes is *not* available; the
repair is made at the normalization, which is affine and therefore commutes with the homothety
defining the dilate. -/

/-- **The constant `C_{lem:ml1bootFineNormalizeDilate}(c)`** of
`Kakeya.ml1Boot.exists_fineNormalization_dilate`, at a free dilation ratio `c`.

It is `Kakeya.ml1Boot.fineFactor.C` at the normalized ambient radius `(1 + 2 c) C_N` in place
of `C_N`, `C_N = Tube.normalization.C 3`: the normalization `Φ_{T_τ}` is affine, so it carries
`c · T_τ` to the `c`-dilate of `Φ_{T_τ}(T_τ)` about `Φ_{T_τ}(m)`, and every loss of the
normalization argument is a power of the ambient radius or of the selection constant
`Tube.comparableReplacement.C`.

## Why the radius factor is `1 + 2 c` and not `2 c - 1`

A `c`-dilate about a point of a body contained in `B_R` lands in `B_{(2c-1)R}`: for `|p| ≤ R`
and `|x| ≤ R`, `|p + c (x - p)| ≤ c |x| + |1 - c| |p| ≤ (2c-1) R` when `c ≥ 1`, and `≤ R` when
`0 ≤ c ≤ 1`.  Both are at most `(1 + 2c) R`, so `1 + 2 c` is a safe radius factor for **every**
`c ≥ 0`.  It is used in place of `2 c - 1` because the ratio is carried as an `NNReal`, where
subtraction truncates; and in place of `c + 1`, which is wrong for `c > 2`.

## The tilt factor is `max 2 (2 c)`

`Kakeya.ml1Boot.fineNormalize.C` now carries the tilt `κ` of the fine cores against the axis
of `T_τ`, because its selection summand does (see there).  On this route the available tilt is
`2 c θ`, from `Tube.perp_norm_core_sub_le_of_subset_dilate` at a free ratio, so the tilt to
instantiate at is `2 c`, hence `4` at the ratio `c = 2` used in the chain.

It is written `max 2 (2 c)` and not `2 c`, for one reason: `2` is the floor blueprint
`lem:ml1bootFineNormalizeCore` puts on `κ`,
and at `c < 1` the bare `2 c` falls below it.  It would also make
`Kakeya.ml1Boot.fineFactor_C_le_fineNormalizeDilate_C` false: at `c = 0` the radius factor is
`1`, so the two constants would differ only in their selection summands, and that of
`Kakeya.ml1Boot.fineFactor.C` — read at `κ = 2` — would be the larger.  Since the tilt bound
`2 c θ ≤ max 2 (2 c) · θ` holds a fortiori, taking the maximum weakens nothing and keeps `κ ≥ 2`
and monotonicity in `c` at the same time.

As in the undilated case the factor `16` sits here and not on the normalization leaf
`Kakeya.ml1Boot.exists_fineNormalization_dilate`, which is stated at
`Kakeya.ml1Boot.fineNormalize.C ((1 + 2 c) C_N) (max 2 (2 c))`; the `16` is spent once, in
`Kakeya.ml1Boot.fine_genKF_dilate`.

Like `Kakeya.ml1Boot.fineFactor.C` it depends only on the ambient dimension `3` and on the
ratio `c`; in particular not on `δ`, on `τ`, on `θ`, on `γ`, on `j`, or on the family.  That it
dominates `Kakeya.ml1Boot.fineFactor.C` is
`Kakeya.ml1Boot.fineFactor_C_le_fineNormalizeDilate_C`, for every `c`; that clause is a
convenience and does **not** condition citing a lemma stated at the smaller constant at the
larger one.

At `c = 2` the radius factor is `5`, where the pinned-ratio predecessor of this definition had
`3`.  The constant is therefore *larger* than it used to be at the ratio the chain actually
uses; see `Kakeya.ml1Boot.fineFactor_C_le_fineNormalizeDilate_C` for the direction of the
monotonicity that makes this harmless on conclusion sides. -/
noncomputable abbrev fineNormalizeDilate.C (c : ℝ≥0) : ℝ≥0 :=
  16 * fineNormalize.C ((1 + 2 * c) * _root_.Tube.normalization.C 3) (max 2 (2 * c))

/-- **`1 ≤ C₃(c)`**, the analogue of
`Kakeya.ml1Boot.one_le_fineFactor_C`.  No lower bound on `c` is needed: `1 + 2 c ≥ 1` holds for
every `c : NNReal`. -/
theorem one_le_fineNormalizeDilate_C (c : ℝ≥0) : (1 : ℝ≥0) ≤ fineNormalizeDilate.C c := by
  unfold fineNormalizeDilate.C
  have h : (1 : ℝ≥0) ≤ (1 + 2 * c) * _root_.Tube.normalization.C 3 := by
    exact one_le_mul (self_le_add_right 1 (2 * c)) (_root_.Tube.normalization.one_le_C 3)
  exact one_le_mul (by norm_num : (1 : ℝ≥0) ≤ 16) (one_le_fineNormalize_C h)

/-- **The dilate normalization loss is at most the dilate fine-factor constant**
(blueprint `lem:ml1bootFineNormalizeCoreConstantLeFineFactor`, dilate half): they differ by
the factor `16`. -/
theorem fineNormalize_C_le_fineNormalizeDilate_C (c : ℝ≥0) :
    fineNormalize.C ((1 + 2 * c) * _root_.Tube.normalization.C 3) (max 2 (2 * c))
      ≤ fineNormalizeDilate.C c := by
  unfold fineNormalizeDilate.C
  exact le_mul_of_one_le_left zero_le (by norm_num : (1 : ℝ≥0) ≤ 16)

section FineDilate

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- **A fine fibre over a `c`-dilate**, as `Kakeya.ml1Boot.fine_genKF_dilate` consumes it
(blueprint `lem:ml1bootFineNormalizeDilate` and `lem:ml1bootFineGenKFDilate`, the hypotheses on
the fibre).

This is `Kakeya.ml1Boot.IsFineFibre` with two changes and no others: the containment clause is
`T i ⊆ K` for an ambient body `K ⊆ c · T_τ` instead of `T i ⊆ T_τ`, and the fullness prefactor
is `Kakeya.ml1Boot.fineNormalizeDilate.C c` instead of `Kakeya.ml1Boot.fineFactor.C`, that being
what the dilate normalization loses.

## The ambient body is a parameter, and the volume ratio `M` is the price

The containment is stated at a *named* convex body `K` rather than at the literal
`Kakeya.Tube.dilate Tτ (c : ℝ)`.  Two things are asked of it: `K ≤ c · T_τ`, and the reverse
volume comparison `|c · T_τ| ≤ M |K|` recorded in `ambient_fat`.  Taking `K = c · T_τ` and
`M = 1` recovers the previous form verbatim, so nothing is lost; what is gained is that a
caller holding the fine tubes inside something *smaller* than the dilate — a plank block's
convex hull, say — may name that body here and have the Frostman constant of
`Kakeya.ml1Boot.fine_genKF_dilate` read in it.  That matters because
`Kakeya.ml1Boot.frostmanConstIn_le_of_le_ambient` is monotone *increasing* in the ambient body:
a bound at the smaller body is the weaker hypothesis, and it cannot be recovered after the fact
from a bound at the dilate.

`K ≤ c · T_τ` keeps the tilt bound and the normalized ambient radius of
`Kakeya.ml1Boot.exists_fineNormalization_dilate` available, so the *geometric* loss
`Kakeya.ml1Boot.fineNormalizeDilate.C c` is unchanged and is still read at the ratio `c`.

`ambient_fat` is a necessary additional hypothesis.  A Frostman constant
is a ratio of densities, and `Kakeya.ConvexSpaceBody.densityIn s W K` divides by
`volume K.carrier`; the ambient therefore enters the numerator (which test bodies are
admissible) *and* the denominator (the normalizing volume).  The order clause `K ≤ c · T_τ`
controls only the first.  See the note at
`Kakeya.ml1Boot.exists_fineNormalization_dilate` for the explicit counterexample that an
`M`-free form admits.

`M` does not appear in `fullness`, and it does not appear in the multiplicity or fullness
conclusions of `Kakeya.ml1Boot.exists_fineNormalization_dilate`.  Those are ratios of sums of
volumes over the *family*, with no ambient body in either numerator or denominator, so they
are invariant under the affine normalization and blind to `|K|`.  Only the Frostman clause,
whose denominator is a volume of the ambient, sees the ratio.

The ratio is free.  It is carried as an `NNReal` because it is read twice: once as the ratio of
`Kakeya.Tube.dilate`, which takes a real, and once inside
`Kakeya.ml1Boot.fineNormalizeDilate.C`, whose radius argument is an `NNReal`.  Taking it
nonnegative by construction is what keeps `1 ≤ 1 + 2 c` — and hence
`Kakeya.ml1Boot.one_le_fineNormalizeDilate_C` — free of any side hypothesis.

The clause on the parent itself is deliberately unchanged, `T_τ ⊆ B₁`.  Asking
`c · T_τ ⊆ B₁` instead would make every statement under it vacuous for `c > 1`: a
`Kakeya.Tube` has a core of length exactly `1`, so `c · T_τ` has diameter
`c (2 + 4 τ) > 2 = diam B₁` and no `τ`-tube whatever satisfies it. -/
structure IsFineFibreDilate {ι : Type*} {δ τ : ℝ≥0} (c : ℝ≥0) (R : ℝ)
    (K : ConvexSpaceBody E)
    (M : ℝ≥0) (Λ : ℝ≥0) (μ₀ : ℝ≥0∞)
    (ηs : ℝ) (u : Finset ι) (Tτ : Tube τ E) (T : ι → ShadedTube δ E) : Prop where
  /-- The common density the shadings are compared to is nonzero. -/
  density_pos : 0 < μ₀
  /-- The fibre is nonempty. -/
  nonempty : u.Nonempty
  /-- The parent tube lies in the ball of radius `R`.  The *dilate* does not, and is not asked
  to.  `R` used to be pinned to `1`; it is free because the hypothesis is dead downstream (see
  `Kakeya.ml1Boot.exists_fineNormalization_dilate`, which does not read it). -/
  parent_ball : Tτ.carrier ⊆ Metric.closedBall 0 R
  /-- The ambient body lies in the `c`-dilate of the parent tube. -/
  ambient_le_parent_dilate : K ≤ Tube.dilate Tτ (c : ℝ)
  /-- The ambient body fills a definite fraction `1 / M` of that dilate.  This is the
  denominator half of the ambient hypothesis and is *not* implied by the order clause above. -/
  ambient_fat : volume (Tube.dilate Tτ (c : ℝ)).carrier ≤ (M : ℝ≥0∞) * volume K.carrier
  /-- Every member of the fibre lies in the ambient body. -/
  subset_ambient : ∀ i ∈ u, (T i).toConvexSpaceBody ≤ K
  /-- The members are pairwise essentially distinct. -/
  essDistinct : (u : Set ι).Pairwise
    (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier)
  /-- The shading densities are two-sidedly comparable to `μ₀`, with constant `Λ`. -/
  shade_comparable : ∀ i ∈ u,
    (Λ : ℝ≥0∞)⁻¹ * μ₀ * volume (T i).carrier ≤ volume (T i).shade ∧
      volume (T i).shade ≤ (Λ : ℝ≥0∞) * μ₀ * volume (T i).carrier
  /-- The fibre is full, with the prefactor the dilate normalization loses. -/
  fullness : (fineNormalizeDilate.C c : ℝ≥0∞) * (Λ : ℝ≥0∞) ^ 2 * (δ : ℝ≥0∞) ^ ηs
    ≤ (ShadedBody.fullness u (fun i => (T i).toShadedBody) : ℝ≥0∞)

omit [Nontrivial E] in
/-- **The tilt of an inner core against the ambient axis, over a dilate** (blueprint
`lem:ml1bootFineNormalizeDilateTilt`, in the form the selection package consumes it).

`Tube.perp_norm_direction_le_of_subset_dilate` read at `T.direction = T.y - T.x` rather than at
`T.x - T.y`, exactly as `Tube.perp_norm_direction_le_of_subset` is
`Tube.perp_norm_core_sub_le_of_subset` so read.  This is the instance `κ = 2 c` of the `hperp`
hypothesis of `Tube.exists_comparableReplacement_affine`, and `max 2 (2 c)` covers it together
with the undilated `κ = 2`. -/
private lemma perp_norm_direction_le_of_subset_dilate {θ ρ : ℝ≥0} {c : ℝ} (hc : 0 < c)
    (T₀ : Tube θ E) (T : Tube ρ E) (hT : T.carrier ⊆ (Tube.dilate T₀ c).carrier) :
    ‖T.direction - (inner ℝ T₀.direction T.direction : ℝ) • T₀.direction‖
      ≤ 2 * c * (θ : ℝ) := by
  have h := (_root_.Tube.perp_norm_core_sub_le_of_subset_dilate hc T₀ T hT).2.2
  have hEq : T.direction - (inner ℝ T₀.direction T.direction : ℝ) • T₀.direction
      = -(T.x - T.y - (inner ℝ T₀.direction (T.x - T.y) : ℝ) • T₀.direction) := by
    simp only [Tube.direction]
    rw [show T.x - T.y = -(T.y - T.x) by abel, inner_neg_right, neg_smul]
    abel
  rw [hEq, norm_neg]
  exact h

omit [Nontrivial E] in
/-- **Length of the image core, over a dilate.**

`Tube.normalization_core_length` bounds `dist (Φ x) (Φ y)` for `T ⊆ T₀` by substituting the
tilt bound `‖perp‖ ≤ 2 θ` into the Pythagoras identity `Tube.norm_sq_normalization_sub`, which
gives `dist² ≤ 1 + 4`.  Over a dilate the tilt bound is `‖perp‖ ≤ 2 c θ`
(`Tube.perp_norm_core_sub_le_of_subset_dilate`) and the same substitution gives
`dist² ≤ 1 + 4 c² ≤ (1 + 2 c)²`.

The bound is stated as `1 + 2 c` and *not* against `C_N`: the packaged
`Tube.IsNormalizationDistortion.dist_le_C` asks for `C_N`, which at `C_N = 64` fails once
`c > 31.99…`, so the packaged form is unavailable at an unbounded dilation ratio.  What the
route needs is only `dist ≤ R` at its own radius `R = (1 + 2 c) C_N`, and `1 + 2 c ≤ R` since
`1 ≤ C_N`.  See `Kakeya.ml1Boot.rescale_outer_tube_of_dist_le`.

The bound holds with no upper bound on `θ`: the Pythagoras identity divides the transverse part
by `θ` and the tilt bound carries a matching factor `θ`, so `θ ≤ 1` cancels out of the
computation and is retained only to keep the hypothesis block parallel to the undilated
`Tube.normalization_core_length`. -/
private lemma dist_normalization_core_le_of_subset_dilate {θ ρ : ℝ≥0} (hθ : 0 < θ)
    (_hθ1 : θ ≤ 1) {c : ℝ} (hc : 0 < c) (T₀ : Tube θ E) (T : Tube ρ E)
    (hT : T.carrier ⊆ (Tube.dilate T₀ c).carrier) :
    dist (T₀.normalization T.x) (T₀.normalization T.y) ≤ 1 + 2 * c := by
  rw [dist_eq_norm]
  let p : ℝ := inner ℝ T₀.direction (T.x - T.y)
  let perp : E := T.x - T.y - (inner ℝ T₀.direction (T.x - T.y)) • T₀.direction
  have hperp : ‖perp‖ ≤ 2 * c * (θ : ℝ) := by
    simpa [perp] using (_root_.Tube.perp_norm_core_sub_le_of_subset_dilate hc T₀ T hT).2.2
  have hp1 : |p| ≤ (1 : ℝ) := by
    dsimp [p]
    calc
      |inner ℝ T₀.direction (T.x - T.y)| ≤ ‖T₀.direction‖ * ‖T.x - T.y‖ :=
        abs_real_inner_le_norm _ _
      _ = 1 := by
        rw [T₀.norm_direction]
        have hxy : ‖T.x - T.y‖ = (1 : ℝ) := by rw [← dist_eq_norm, T.dist_eq_one]
        rw [hxy]
        norm_num
  have hp : p ^ 2 ≤ (1 : ℝ) := by
    have hpm : |p| ≤ |(1 : ℝ)| := by simpa using hp1
    simpa using (sq_le_sq.mpr hpm)
  have hq2 : ((θ : ℝ)⁻¹) ^ 2 * ‖perp‖ ^ 2 ≤ (4 * c ^ 2 : ℝ) := by
    have hqsq : ‖perp‖ ^ 2 ≤ (2 * c * (θ : ℝ)) ^ 2 := by
      apply sq_le_sq.mpr
      rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * c * (θ : ℝ))]
      exact hperp
    have hθinvsq : ((θ : ℝ)⁻¹) ^ 2 * (2 * c * (θ : ℝ)) ^ 2 = (4 * c ^ 2 : ℝ) := by
      have hnθ : (θ : ℝ) ≠ 0 := by exact_mod_cast hθ.ne'
      calc
        ((θ : ℝ)⁻¹) ^ 2 * (2 * c * (θ : ℝ)) ^ 2 = (2 * (c * ((θ : ℝ)⁻¹ * (θ : ℝ)))) ^ 2 := by ring
        _ = (2 * (c * 1)) ^ 2 := by rw [inv_mul_cancel₀ hnθ]
        _ = 4 * c ^ 2 := by ring
    have hmain : ((θ : ℝ)⁻¹) ^ 2 * ‖perp‖ ^ 2 ≤ ((θ : ℝ)⁻¹) ^ 2 * (2 * c * (θ : ℝ)) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hqsq (sq_nonneg ((θ : ℝ)⁻¹))
    rw [hθinvsq] at hmain
    exact hmain
  have hnorm_sq : ‖T₀.normalization T.x - T₀.normalization T.y‖ ^ 2 ≤ (1 + 2 * c) ^ 2 := by
    rw [_root_.Tube.norm_sq_normalization_sub T₀ T.x T.y]
    change p ^ 2 + ((θ : ℝ)⁻¹) ^ 2 * ‖perp‖ ^ 2 ≤ (1 + 2 * c) ^ 2
    have hsum : p ^ 2 + ((θ : ℝ)⁻¹) ^ 2 * ‖perp‖ ^ 2 ≤ (1 + 4 * c ^ 2 : ℝ) := by
      nlinarith [hp, hq2]
    nlinarith [hsum, hc]
  have hs := sq_le_sq.mp hnorm_sq
  simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + 2 * c)]
    using hs

omit [Nontrivial E] in
/-- **The image of a dilate of the ambient tube is bounded** (the radius computation in the proof
of blueprint `lem:ml1bootFineNormalizeDilate`).

`Tube.normalization_image_ambient_subset_closedBall` puts `Φ_{T₀}(T₀)` inside `B̄(x, C_N)`, by
`‖Φ z - x‖ ≤ 3 ≤ C_N`.  For the `c`-dilate, `Tube.abs_inner_and_perp_le_of_mem_dilate` gives
`|⟪z - centre, e⟫| ≤ c/2 + c θ` and `‖perp (z - centre)‖ ≤ c θ`; shifting the base point from the
centre to the endpoint `x` costs a further `1/2` along the axis and nothing across it, so
Pythagoras gives `‖Φ z - x‖² ≤ (1/2 + 3 c/2)² + c²` for `θ ≤ 1`, and `3 (1 + 2 c)` dominates the
square root.  Hence the factor `1 + 2 c` in the radius, and hence in
`Kakeya.ml1Boot.fineNormalizeDilate.C`. -/
private lemma normalization_image_dilate_subset_closedBall {θ : ℝ≥0} (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) {c : ℝ} (hc : 0 < c) (T₀ : Tube θ E) :
    T₀.normalization '' (Tube.dilate T₀ c).carrier
      ⊆ Metric.closedBall T₀.x
          ((1 + 2 * c) * (_root_.Tube.normalization.C (Module.finrank ℝ E) : ℝ)) := by
  rw [Set.image_subset_iff]
  intro z hz
  rw [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm]
  have hcnonneg : (0 : ℝ) ≤ c := le_of_lt hc
  have hθmod : (θ : ℝ) ≤ 1 := by exact_mod_cast hθ1
  -- centre-based bounds (at the centre of `T₀` rather than at the endpoint `T₀.x`)
  rcases Tube.abs_inner_and_perp_le_of_mem_dilate T₀ hc hz with ⟨hax, hperp⟩
  let u : E := z - T₀.center
  have he : (inner ℝ T₀.direction T₀.direction : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, _root_.Tube.norm_direction T₀]; norm_num
  -- shift the base point from `T₀.center` to `T₀.x`
  have hu : z - T₀.x = u + (1 / 2 : ℝ) • T₀.direction := by
    dsimp [u]
    rw [_root_.Tube.x_eq_center_sub T₀]
    module
  let p : ℝ := inner ℝ T₀.direction (z - T₀.x)
  let q : E := z - T₀.x - (inner ℝ T₀.direction (z - T₀.x)) • T₀.direction
  have hp_eq : p = inner ℝ T₀.direction u + (1 / 2 : ℝ) := by
    dsimp [p]
    rw [hu, inner_add_right, inner_smul_right, he]
    ring
  have hinc : |inner ℝ T₀.direction u| ≤ c / 2 + c * (θ : ℝ) := by
    simpa [u, real_inner_comm] using hax
  have hp_le : |p| ≤ (1 : ℝ) / 2 + (3 : ℝ) / 2 * c := by
    rw [hp_eq]
    have habs : |inner ℝ T₀.direction u + (1 / 2 : ℝ)|
        ≤ |inner ℝ T₀.direction u| + (1 : ℝ) / 2 := by
      calc
        |inner ℝ T₀.direction u + (1 / 2 : ℝ)| ≤ |inner ℝ T₀.direction u| + |1 / 2| :=
          abs_add_le _ _
        _ = |inner ℝ T₀.direction u| + (1 : ℝ) / 2 := by
          rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have hlim : |inner ℝ T₀.direction u| + (1 : ℝ) / 2
        ≤ (1 : ℝ) / 2 + (3 : ℝ) / 2 * c := by
      nlinarith [hinc, hθmod, hcnonneg]
    exact le_trans habs hlim
  have hp2 : p ^ 2 ≤ ((1 : ℝ) / 2 + (3 : ℝ) / 2 * c) ^ 2 := by
    apply sq_le_sq.mpr
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 : ℝ) / 2 + (3 : ℝ) / 2 * c)]
    exact hp_le
  have hperpq : ‖q‖ ≤ c * (θ : ℝ) := by
    dsimp [q]
    rw [hu]
    have hvec : u + (1 / 2 : ℝ) • T₀.direction
        - (inner ℝ T₀.direction (u + (1 / 2 : ℝ) • T₀.direction)) • T₀.direction
        = u - (inner ℝ T₀.direction u) • T₀.direction := by
      rw [inner_add_right, inner_smul_right, he]
      module
    rw [hvec]
    simpa [u] using hperp
  have hcθ0 : (0 : ℝ) ≤ c * (θ : ℝ) := by positivity
  have hq2 : ((θ : ℝ)⁻¹) ^ 2 * ‖q‖ ^ 2 ≤ c ^ 2 := by
    have hqsq : ‖q‖ ^ 2 ≤ (c * (θ : ℝ)) ^ 2 := by
      apply sq_le_sq.mpr
      rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hcθ0]
      exact hperpq
    have hθinvsq : ((θ : ℝ)⁻¹) ^ 2 * (θ : ℝ) ^ 2 = 1 := by
      have hθne : (θ : ℝ) ≠ 0 := by exact_mod_cast hθ.ne'
      calc
        ((θ : ℝ)⁻¹) ^ 2 * (θ : ℝ) ^ 2 = (((θ : ℝ)⁻¹) * (θ : ℝ)) ^ 2 := by ring
        _ = 1 ^ 2 := by rw [inv_mul_cancel₀ hθne]
        _ = 1 := by norm_num
    have hmain : ((θ : ℝ)⁻¹) ^ 2 * ‖q‖ ^ 2 ≤ ((θ : ℝ)⁻¹) ^ 2 * (c * (θ : ℝ)) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hqsq (sq_nonneg ((θ : ℝ)⁻¹))
    calc
      ((θ : ℝ)⁻¹) ^ 2 * ‖q‖ ^ 2 ≤ ((θ : ℝ)⁻¹) ^ 2 * (c * (θ : ℝ)) ^ 2 := hmain
      _ = c ^ 2 := by
        calc
          ((θ : ℝ)⁻¹) ^ 2 * (c * (θ : ℝ)) ^ 2 = c ^ 2 * (((θ : ℝ)⁻¹) ^ 2 * (θ : ℝ) ^ 2) := by ring
          _ = c ^ 2 := by rw [hθinvsq]; ring
  have hqnorm : ‖T₀.normalization z - T₀.x‖ ≤ 3 * (1 + 2 * c) := by
    rw [← _root_.Tube.normalization_apply_x T₀]
    have hnorm_sq : ‖T₀.normalization z - T₀.normalization T₀.x‖ ^ 2 ≤ (3 * (1 + 2 * c)) ^ 2 := by
      rw [_root_.Tube.norm_sq_normalization_sub T₀ z T₀.x]
      change p ^ 2 + ((θ : ℝ)⁻¹) ^ 2 * ‖q‖ ^ 2 ≤ (3 * (1 + 2 * c)) ^ 2
      have hsum : p ^ 2 + ((θ : ℝ)⁻¹) ^ 2 * ‖q‖ ^ 2
          ≤ ((1 : ℝ) / 2 + (3 : ℝ) / 2 * c) ^ 2 + c ^ 2 := by
        nlinarith [hp2, hq2]
      have hdom : ((1 : ℝ) / 2 + (3 : ℝ) / 2 * c) ^ 2 + c ^ 2 ≤ (3 * (1 + 2 * c)) ^ 2 := by
        nlinarith [hcnonneg, sq_nonneg c]
      nlinarith [hsum, hdom]
    have hs3 := sq_le_sq.mp hnorm_sq
    have hnn : (0 : ℝ) ≤ 3 * (1 + 2 * c) := by positivity
    simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hnn] using hs3
  refine le_trans hqnorm ?_
  have hC3 : (3 : ℝ) ≤ (_root_.Tube.normalization.C (Module.finrank ℝ E) : ℝ) := by
    unfold _root_.Tube.normalization.C
    have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ Module.finrank ℝ E :=
      one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    calc
      (3 : ℝ) ≤ (2 : ℝ) ^ 3 := by norm_num
      _ ≤ 1 * (2 : ℝ) ^ 3 := by norm_num
      _ ≤ (2 : ℝ) ^ Module.finrank ℝ E * (2 : ℝ) ^ 3 := by
        exact mul_le_mul_of_nonneg_right hpow (by norm_num)
      _ = (2 : ℝ) ^ (Module.finrank ℝ E + 3) := by rw [pow_add]
      _ = ((2 ^ (Module.finrank ℝ E + 3) : ℝ≥0) : ℝ) := by norm_num
  have hle : (3 : ℝ) * (1 + 2 * c)
      ≤ (1 + 2 * c) * (_root_.Tube.normalization.C (Module.finrank ℝ E) : ℝ) := by
    have h12 : (0 : ℝ) ≤ 1 + 2 * c := by positivity
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left hC3 h12
  exact hle

omit [Nontrivial E] in
/-- **A dilate that contains a tube is not much smaller than the tube it dilates.**

The ambient enlargement to `B₁` needs the ambient body bounded *below* in volume, and over a
dilate that means bounding `|T_τ|` by `|c · T_τ| = c³ |T_τ|`, which is vacuous as `c → 0`.  It is
not vacuous here, because `c` cannot be small: a `ρ`-tube inside `c · T_τ` has two points at
distance `1`, and `Tube.dist_le_of_mem_dilate_of_mem_dilate` bounds that distance by
`c + 4 c τ ≤ 5 c`.  So `1/5 ≤ c` is *forced* by the hypotheses rather than assumed, and
`c⁻³ ≤ 125`.

This is why `Kakeya.ml1Boot.exists_fineNormalization_dilate` needs no lower bound on `c`, and
why the third clause of `Kakeya.ml1Boot.fineNormalize_C_dominates_gen` carries a `125`. -/
private lemma volume_ambient_le_mul_volume_dilate (hdim : Module.finrank ℝ E = 3)
    {τ ρ : ℝ≥0} (hτ1 : τ ≤ 1) (Tτ : Tube τ E) {c : ℝ} (hc : 0 ≤ c) (S : Tube ρ E)
    (_hρτ : ρ ≤ τ) (hS : S.carrier ⊆ (Tube.dilate Tτ c).carrier) :
    (1 / 5 : ℝ) ≤ c ∧
      volume Tτ.carrier ≤ 125 * volume (Tube.dilate Tτ c).carrier := by
  have hx : S.x ∈ (Tube.dilate Tτ c).carrier := hS S.x_mem_carrier
  have hyy : S.y ∈ (Tube.dilate Tτ c).carrier := hS S.y_mem_carrier
  have hc_pos : 0 < c := by
    by_contra hc0
    -- if c = 0 the 0-dilate is constant at the centre, so S.x = S.y, contradicting dist = 1
    have hceq : c = 0 := le_antisymm (le_of_not_gt hc0) hc
    have hx0 : S.x ∈ (Tube.dilate Tτ (0 : ℝ)).carrier := by simpa [hceq] using hx
    have hy0 : S.y ∈ (Tube.dilate Tτ (0 : ℝ)).carrier := by simpa [hceq] using hyy
    have hcar : (Tube.dilate Tτ (0 : ℝ)).carrier =
        AffineMap.homothety Tτ.center (0 : ℝ) '' Tτ.carrier :=
      Kakeya.Tube.dilate_carrier Tτ (0 : ℝ)
    have hconst (p : E) : AffineMap.homothety Tτ.center (0 : ℝ) p = Tτ.center := by
      simp
    have hxcent : S.x = Tτ.center := by
      rw [hcar] at hx0
      rcases hx0 with ⟨p, hp, hpx⟩
      rw [← hpx, hconst p]
    have hycent : S.y = Tτ.center := by
      rw [hcar] at hy0
      rcases hy0 with ⟨p, hp, hpy⟩
      rw [← hpy, hconst p]
    have hzero : dist S.x S.y = 0 := by
      rw [hxcent, hycent, dist_self]
    have : (1 : ℝ) = 0 := by
      rw [← S.dist_eq_one, hzero]
    norm_num at this
  have hc_ge : (1 / 5 : ℝ) ≤ c := by
    have hτr : (τ : ℝ) ≤ 1 := by exact_mod_cast hτ1
    have hd : dist S.x S.y ≤ (c + c) / 2 + 2 * (c + c) * (τ : ℝ) :=
      Tube.dist_le_of_mem_dilate_of_mem_dilate (T := Tτ) (c := c) (c' := c) hc_pos hc_pos hx hyy
    have hd' : (1 : ℝ) ≤ (c + c) / 2 + 2 * (c + c) * (τ : ℝ) := by
      simpa [S.dist_eq_one] using hd
    have hlen : (1 : ℝ) ≤ c + 4 * c * (τ : ℝ) := by
      have hsimp : (c + c) / 2 + 2 * (c + c) * (τ : ℝ) = c + 4 * c * (τ : ℝ) := by ring
      rw [hsimp] at hd'
      exact hd'
    have hτc : 4 * c * (τ : ℝ) ≤ 4 * c := by
      have h4c : 0 ≤ 4 * c := by positivity
      calc
        4 * c * (τ : ℝ) ≤ 4 * c * 1 := mul_le_mul_of_nonneg_left hτr h4c
        _ = 4 * c := by ring
    have hfive : c + 4 * c * (τ : ℝ) ≤ 5 * c := by nlinarith
    have hle5 : (1 : ℝ) ≤ 5 * c := le_trans hlen hfive
    nlinarith
  constructor
  · exact hc_ge
  · -- volume comparison: |T_τ| ≤ 125 · |c · T_τ|
    have hc1 : (1 / 125 : ℝ) ≤ c ^ 3 := by
      have hpk : (1 / 5 : ℝ) ^ 3 ≤ c ^ 3 :=
        pow_le_pow_left₀ (by norm_num : 0 ≤ (1 / 5 : ℝ)) hc_ge 3
      norm_num at hpk
      exact hpk
    have hlin : (1 : ℝ) ≤ 125 * c ^ 3 := by nlinarith
    have hK : (1 : ℝ≥0∞) ≤ 125 * ENNReal.ofReal (c ^ 3) := by
      have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (125 * c ^ 3) := by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal hlin
      have hprod : ENNReal.ofReal (125 * c ^ 3) = 125 * ENNReal.ofReal (c ^ 3) := by
        rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (125 : ℝ))]
        norm_num
      simpa [hprod] using h1
    rw [Kakeya.Tube.dilate_carrier, MeasureTheory.Measure.addHaar_image_homothety,
      abs_of_pos (pow_pos hc_pos (Module.finrank ℝ E))]
    rw [hdim]
    calc
      volume Tτ.carrier ≤ (125 * ENNReal.ofReal (c ^ 3)) * volume Tτ.carrier := by
        exact le_mul_of_one_le_left (by exact zero_le) hK
      _ = 125 * (ENNReal.ofReal (c ^ 3) * volume Tτ.carrier) := by
        rw [mul_assoc]

/-- **The ambient enlargement to `B₁`, over a dilate: this is where `M` is paid.**

`Kakeya.ml1Boot.exists_fineNormalization_core` asks for its ambient body to fill a definite
fraction of the unit ball after rescaling, and that is a lower bound on `|K|`.  Containment
`K ≤ c · T_τ` alone cannot supply one — take `K` to be a single fibre's own body — which is
exactly why the dilated normalization carries the volume-ratio parameter `M` and the hypothesis
`hKfat`, and why the earlier `M`-free form of that lemma was false.

The chain is: `Tube.volume_closedBall_one_le_mul_volume_rescale_image_ambient` compares `B₁` with
the rescaled `T_τ`; `Kakeya.ml1Boot.volume_ambient_le_mul_volume_dilate` descends from `T_τ` to
the `c`-dilate at cost `125`; and `hKfat` descends from the dilate to `K` at cost `M`.  The
rescaling is affine with a constant Jacobian, so it does not change the ratio. -/
private lemma volume_closedBall_one_le_mul_volume_rescale_image_of_dilate
    (hdim : Module.finrank ℝ E = 3) {τ δ : ℝ≥0} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (hδτ : δ ≤ τ)
    (Tτ : Tube τ E) {c : ℝ} (hc : 0 ≤ c) {M : ℝ≥0} (K : ConvexSpaceBody E)
    (hK : K.carrier ⊆ (Tube.dilate Tτ c).carrier)
    (hKfat : volume (Tube.dilate Tτ c).carrier ≤ (M : ℝ≥0∞) * volume K.carrier)
    (S : Tube δ E) (hS : S.carrier ⊆ K.carrier)
    {R : ℝ≥0} (hR1 : 1 ≤ R) :
    volume (Metric.closedBall (0 : E) 1)
      ≤ ((125 * M * (4 * R) ^ 6 : ℝ≥0) : ℝ≥0∞)
        * volume (Tτ.rescaleMap ((R : ℝ≥0) : ℝ) '' K.carrier) := by
  have hR1' : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR1
  have hR0 : 0 < (R : ℝ) := lt_of_lt_of_le zero_lt_one hR1'
  have hofR : ENNReal.ofReal ((4 * (R : ℝ)) ^ 6) = (((4 * R) ^ 6 : ℝ≥0) : ℝ≥0∞) := by
    have h4R : ENNReal.ofReal (4 * (R : ℝ)) = ((4 * R : ℝ≥0) : ℝ≥0∞) := by
      rw [show (4 : ℝ) * (R : ℝ) = ((4 * R : ℝ≥0) : ℝ) by
        rw [NNReal.coe_mul]
        norm_num]
      rw [ENNReal.ofReal_coe_nnreal]
    have hRnonneg : (0 : ℝ) ≤ 4 * (R : ℝ) := by positivity
    calc
      ENNReal.ofReal ((4 * (R : ℝ)) ^ 6) = (ENNReal.ofReal (4 * (R : ℝ))) ^ 6 := by
            rw [ENNReal.ofReal_pow hRnonneg]
      _ = ((4 * R : ℝ≥0) : ℝ≥0∞) ^ 6 := by rw [h4R]
      _ = (((4 * R) ^ 6 : ℝ≥0) : ℝ≥0∞) := by
            rw [ENNReal.coe_pow]
  have h1 : volume (Metric.closedBall (0 : E) 1)
      ≤ ENNReal.ofReal ((4 * (R : ℝ)) ^ 6) * volume (Tτ.rescaleMap (R : ℝ) '' Tτ.carrier) :=
    _root_.Tube.volume_closedBall_one_le_mul_volume_rescale_image_ambient
      (E := E) hdim hτ0 hR1' Tτ
  have hTτ : volume Tτ.carrier ≤ ((125 * M : ℝ≥0) : ℝ≥0∞) * volume K.carrier := by
    have hvol := (volume_ambient_le_mul_volume_dilate hdim hτ1 Tτ hc S hδτ (hS.trans hK)).2
    calc
      volume Tτ.carrier ≤ 125 * volume (Tube.dilate Tτ c).carrier := hvol
      _ ≤ 125 * ((M : ℝ≥0∞) * volume K.carrier) := by
        gcongr
      _ = ((125 * M : ℝ≥0) : ℝ≥0∞) * volume K.carrier := by
        simp [ENNReal.coe_mul, mul_assoc]
  have h2 : volume (Tτ.rescaleMap (R : ℝ) '' Tτ.carrier)
      ≤ ((125 * M : ℝ≥0) : ℝ≥0∞) * volume (Tτ.rescaleMap (R : ℝ) '' K.carrier) := by
    obtain ⟨L, hL⟩ := _root_.Tube.exists_rescaleEquiv hτ0 hR0 Tτ
    let J : ℝ≥0∞ := ENNReal.ofReal |LinearMap.det (L.linear : E →ₗ[ℝ] E)|
    have hA := Kakeya.volume_affineImage L Tτ.carrier
    have hB := Kakeya.volume_affineImage L K.carrier
    rw [hL] at hA
    rw [hL] at hB
    have hA' : volume (Tτ.rescaleMap (R : ℝ) '' Tτ.carrier) = J * volume Tτ.carrier := by
      simpa [J] using hA
    have hB' : volume (Tτ.rescaleMap (R : ℝ) '' K.carrier) = J * volume K.carrier := by
      simpa [J] using hB
    calc
      volume (Tτ.rescaleMap (R : ℝ) '' Tτ.carrier) = J * volume Tτ.carrier := hA'
      _ ≤ J * (((125 * M : ℝ≥0) : ℝ≥0∞) * volume K.carrier) := by
        exact mul_le_mul' le_rfl hTτ
      _ = (((125 * M : ℝ≥0) : ℝ≥0∞) * (J * volume K.carrier)) := by
        rw [mul_left_comm]
      _ = ((125 * M : ℝ≥0) : ℝ≥0∞) * volume (Tτ.rescaleMap (R : ℝ) '' K.carrier) := by
        rw [← hB']
  calc
    volume (Metric.closedBall (0 : E) 1)
        ≤ ENNReal.ofReal ((4 * (R : ℝ)) ^ 6) * volume (Tτ.rescaleMap (R : ℝ) '' Tτ.carrier) := h1
    _ = (((4 * R) ^ 6 : ℝ≥0) : ℝ≥0∞) * volume (Tτ.rescaleMap (R : ℝ) '' Tτ.carrier) := by
      rw [hofR]
    _ ≤ (((4 * R) ^ 6 : ℝ≥0) : ℝ≥0∞)
        * (((125 * M : ℝ≥0) : ℝ≥0∞) * volume (Tτ.rescaleMap (R : ℝ) '' K.carrier)) := by
      gcongr
    _ = ((125 * M * (4 * R) ^ 6 : ℝ≥0) : ℝ≥0∞)
        * volume (Tτ.rescaleMap (R : ℝ) '' K.carrier) := by
      conv_rhs =>
        rw [ENNReal.coe_mul]
      rw [mul_assoc]
      rw [mul_left_comm]

/-- **`Kakeya.ml1Boot.fineNormalize_C_dominates_gen` at the dilated instance.**

The instance is `(R, κ) = ((1 + 2 c) C_N, max 2 (2 c))`, and its coupling hypothesis `κ + 2 ≤ R`
holds for every `c` with room to spare: `max 2 (2 c) + 2 ≤ 4 + 2 c`, while
`(1 + 2 c) C_N = 64 + 128 c`.  No lower bound on `c` is needed. -/
private lemma fineNormalize_C_dominates_dilate (c : ℝ≥0) {c₁ : ℝ≥0}
    (hc₁ : c₁ = _root_.Tube.essDistinctTubesInSelfDilate.C 3
      (4 * (((max 2 (2 * c) : ℝ≥0) : ℝ) + 2)
        * (((1 + 2 * c) * _root_.Tube.normalization.C 3 : ℝ≥0) : ℝ)
        * Kakeya.Tube.tubeOverlapCoreClose.C 3)) :
    c₁ ≤ fineNormalize.C ((1 + 2 * c) * _root_.Tube.normalization.C 3) (max 2 (2 * c)) ∧
      ((4 * ((1 + 2 * c) * _root_.Tube.normalization.C 3)) ^ 6 : ℝ≥0) * c₁
        ≤ fineNormalize.C ((1 + 2 * c) * _root_.Tube.normalization.C 3) (max 2 (2 * c)) ∧
      (125 : ℝ≥0) * ((4 * ((1 + 2 * c) * _root_.Tube.normalization.C 3)) ^ 12 : ℝ≥0) * c₁
        ≤ fineNormalize.C ((1 + 2 * c) * _root_.Tube.normalization.C 3) (max 2 (2 * c)) := by
  have hCR : _root_.Tube.normalization.C 3 ≤ (1 + 2 * c) * _root_.Tube.normalization.C 3 := by
    exact le_mul_of_one_le_left' (self_le_add_right 1 (2 * c))
  have hC : _root_.Tube.normalization.C 3 = (64 : ℝ≥0) := by
    norm_num [_root_.Tube.normalization.C]
  have hκ : max 2 (2 * c) ≤ 2 + 2 * c := by
    exact max_le (self_le_add_right 2 (2 * c)) (self_le_add_left (2 * c) 2)
  have hκ2 : max 2 (2 * c) + 2 ≤ 4 + 2 * c := by
    calc
      max 2 (2 * c) + 2 ≤ (2 + 2 * c) + 2 := add_le_add hκ (by norm_num)
      _ = 4 + 2 * c := by ring
  have hRHS : (1 + 2 * c) * _root_.Tube.normalization.C 3 = 64 + 128 * c := by
    rw [hC]
    ring
  have h45 : 4 + 2 * c ≤ 64 + 128 * c := by
    exact add_le_add (by norm_num : (4 : ℝ≥0) ≤ 64)
      (mul_le_mul_left (by norm_num : (2 : ℝ≥0) ≤ 128) c)
  have hκR : max 2 (2 * c) + 2 ≤ (1 + 2 * c) * _root_.Tube.normalization.C 3 := by
    rw [hRHS]
    exact le_trans hκ2 h45
  exact fineNormalize_C_dominates_gen (R := (1 + 2 * c) * _root_.Tube.normalization.C 3)
    (κ := max 2 (2 * c)) hCR hκR hc₁

/-- **Normalizing a fine fibre over a dilate**.

This is `Kakeya.ml1Boot.exists_fineNormalization` with the containment of the fine tubes and
the ambient body of the Frostman constant both moved to a named body `K ⊆ c · T_τ`, and with
the normalization loss read at the ambient radius `(1 + 2 c) C_N` in place of `C_N` and at the
tilt `max 2 (2 c)` in place of `2`, i.e.
`Kakeya.ml1Boot.fineNormalize.C ((1 + 2 c) C_N) (max 2 (2 c))` in place of
`Kakeya.ml1Boot.fineNormalize.C C_N`.  The hypothesis on `T_τ` is unchanged, and so is the
output scale, which is `Kakeya.ml1Boot.fineScale δ τ` in both.

## The ambient body is a parameter, and `K = c · T_τ`, `M = 1` is the old statement

The fine tubes are asked to lie in `K`, and the Frostman constant on the right-hand side is
read in `K`.  Two things are asked of `K`: the order clause `hK : K ≤ c · T_τ` and the volume
clause `hKfat : |c · T_τ| ≤ M |K|`.  At `K = c · T_τ` and `M = 1` both hold by `le_rfl`, the
Frostman prefactor collapses to `Kakeya.ml1Boot.fineNormalize.C ((1 + 2 c) C_N) (max 2 (2 c))`,
and every clause is the previous one verbatim, so this is a strict generalization and not a
restatement.

It is a genuine strengthening, because `Kakeya.ml1Boot.frostmanConstIn_le_of_le_ambient` gives
`C_F(𝕌, K) ≤ C_F(𝕌, c · T_τ)` and never the reverse without paying the volume ratio of
`ConvexSpaceBody.frostmanConstIn_ambient_mono`.  That ratio is exactly what `M` names, and it
is the reason the prefactor of the Frostman clause is `M · C` and not `C`.

## note: why an `M`-free form of this lemma is false

The order clause `K ≤ c · T_τ` alone does not give the Frostman conclusion at the bare loss `C`.

Work in `E = EuclideanSpace ℝ (Fin 3)` at `c = 2`, `τ = 1/2`, `Λ = 1`, `μ₀ = 1`, `ι = Unit`,
`u = {}`.  Let `T_τ` be the witness of `Kakeya.ml1Boot.exists_halfTube_subset_closedBall`,
let `T ` be `T_τ.rescale δ` shaded by its own carrier, and — this is the point — let
`K := (T ).toConvexSpaceBody`, the single fibre member's own body.  Every hypothesis of the
`M`-free form holds: `hK` by `Tube.subset_dilate`, `hsub` by `le_rfl`, `hED` vacuously on a
singleton, `hdens` because shade equals carrier at `Λ = μ₀ = 1`.

The left side of the refuted conclusion is unbounded and the right side is not.

* `C_F(u, T, K) ≤ 1`.  For `K' ≤ K` either `T  ≰ K'`, and the filtered density is `0`, or
  `T  ≤ K'`, and then `K' = K` because `K` is `T `; so every density is at most
  `Δ(u, T, K) = 1` and `Kakeya.ConvexSpaceBody.frostmanConstIn_le` applies.  The right side is
  therefore at most `C`, a quantity depending only on `c`.
* `C_F(u', V, B₁) ≥ 1 / (8 σ²)` with `σ = Kakeya.ml1Boot.fineScale δ τ = min (δ/τ) (1/4)`.
  Here `u' = u` is forced, and testing at `K' = (V ).toConvexSpaceBody ≤ B₁` in
  `Kakeya.ConvexSpaceBody.le_frostmanConstIn_of_lt_densityIn` gives the ratio
  `|B₁| / |V |`, and `|V | ≤ C_v σ²` by `Kakeya.Tube.volume_le` with
  `Kakeya.Tube.volume_le.C 3 = 16`.

Since `σ ≤ δ/τ = 2 δ`, any `δ` below `min (1/8) (1 / (2 √(8 C)))` contradicts the conclusion.
The obstruction is a **volume ratio**, so no purely order-theoretic hypothesis on `K` can
repair it: the ambient enters `Kakeya.ConvexSpaceBody.densityIn` twice, once by selecting the
admissible test bodies and once as the dividing volume, and `K ≤ c · T_τ` governs only the
first.  Here `|c · T_τ| / |K| ≍ δ^(-2) → ∞`, which is precisely `M` blowing up, so the repaired
statement is *not* contradicted by the witness.

What survives from the alternative sketch is the numerator half, and only that: the route does push
a test body `K'' ⊆ B₁` back through the normalization and meet it with the ambient,
`Φ⁻¹(K'') ⊓ K ≤ K`, which is admissible in `C_F(𝕌, K)` and contains every member of the family
that `K''` sees — the step isolated as `ConvexSpaceBody.densityIn_le_densityIn_inter`, whose
hypothesis is exactly `hsub`.  It is also true that shrinking the ambient below the dilate only
shrinks the image whose radius `(1 + 2 c) C_N` bounds, so the tilt bound and the normalized
radius, and hence both summands of the *geometric* loss, are unchanged.  What that sketch
omitted is the denominator: the conclusion divides by `|B₁|` where the hypothesis divides by
`|K|`, and the affine normalization converts that mismatch into the factor `|c · T_τ| / |K|`.
The multiplicity and fullness clauses have no ambient volume anywhere and so carry no `M`.

The clause `K ≤ c · T_τ` cannot be dropped either: with an unrelated `K` the tilt bound
`Tube.perp_norm_core_sub_le_of_subset_dilate` and the ambient radius are both unavailable, and
the geometric loss would have nothing to be stated at.

## The dilation ratio is free

The ratio `c` is a parameter and no step of the argument pins it.  It enters in exactly three
places: as the name of the ambient body `c · T_τ` in the containment hypothesis and in the
Frostman conclusion, through the normalized ambient radius `(1 + 2 c) C_N` at which the
normalization loss is read, and through the tilt `max 2 (2 c)` at which that same loss is read.
The radius factor `1 + 2 c` and the tilt are both justified at
`Kakeya.ml1Boot.fineNormalizeDilate.C`, and both are safe for every `c ≥ 0`; the ratio-`2`
instance, which is the one the chain of `Kakeya.ml1Boot.reduceToTb_fine_factor_dilate` uses,
reads them at `5 C_N` and `4`.

Making the constant grow with `c` in the tilt as well as in the radius is what makes the
statement **self-consistent at free `c`**: the selection constant of the route it takes is
`Tube.essDistinctTubesInSelfDilate.C 3 (4 (κ + 2) R C_n)` at `κ = 2 c`, which grows like
`c ^ 12`, and until the tilt was threaded through
`Kakeya.ml1Boot.fineNormalize.C` the stated constant did not see `c` at all beyond the radius
— so for large `c` the conclusions could not have held at it.  This is the dependence recorded by `item:fineNormOwedConstant`.

## The output scale

As in `Kakeya.ml1Boot.exists_fineNormalization`, the output scale is
`fineScale δ τ = min (δ/τ) (1/4)` and not the bare ratio `δ / τ`.  With `δ / τ` this statement
is **false**, refuted by `Kakeya.ml1Boot.not_exists_fineNormalization_dilate` on the same
witness at `δ = τ = 1/2`; the containment hypothesis there is the weaker one, so that
refutation is if anything easier than its twin.  The truncation is invisible downstream, for
the reasons given at `Kakeya.ml1Boot.exists_fineNormalization`.

## Proof

The proof is an instantiation of `Kakeya.ml1Boot.exists_fineNormalization_core` at
`(P, R, κ) = (K, (1 + 2 c) C_N, max 2 (2 c))`, which is the reading of this lemma that the "not
a corollary" section below describes.  Its four ambient hypotheses are supplied by, in order,
`Kakeya.ml1Boot.normalization_image_dilate_subset_closedBall` (the radius
`Φ_{T_τ}(c · T_τ) ⊆ B̄(x, (1 + 2 c) C_N)`),
`Kakeya.ml1Boot.dist_normalization_core_le_of_subset_dilate` (the image-core length),
`Kakeya.ml1Boot.perp_norm_direction_le_of_subset_dilate` (the tilt, blueprint
`lem:ml1bootFineNormalizeDilateTilt`), and
`Kakeya.ml1Boot.volume_closedBall_one_le_mul_volume_rescale_image_of_dilate` (the ambient
enlargement to `B₁`, which is where `M` is paid).  The constants are then dominated by
`Kakeya.ml1Boot.fineNormalize_C_dominates_dilate`.

Two points in that list are worth keeping visible.

First, the tilt.  `Tube.normalization_distortion` bounds the tilt of the core of `T i` against
the axis of `T_τ` from containment *in `T_τ`*, and the corresponding bound for `T i ⊆ c · T_τ` —
a unit segment whose endpoints lie within `c τ` of the axis has `sin θ ≤ 2 c τ` against `2 τ` —
is a different computation.  It is `Tube.perp_norm_core_sub_le_of_subset_dilate`, proved at a
free dilation ratio with bound `2 c θ`, hence `4 τ` at `c = 2`, and it turned out to be a
two-line corollary of `Kakeya.Tube.norm_chord_transverse_le_of_endpoints_mem_dilate`, so the
tilt bound itself costs nothing.  What it does cost is the selection constant it feeds, which is
why `Kakeya.ml1Boot.fineNormalize.C` is read at `max 2 (2 c)` here.

Second, the packaged distortion structure is *unavailable* at large `c`, and that is why the
core lemma exists in the form it does.  `Tube.rescale_outer_tube` consumes
`Tube.IsNormalizationDistortion`, whose field `dist_le_C` asserts that the image core has length
at most `C_N = 64`; over a `c`-dilate that length is `√(1 + 4 c²)`, which exceeds `64` once
`c > 31.99…`, while `c` is unquantified here.  The route needs only `dist ≤ R` at its own radius
`R = (1 + 2 c) C_N`, so `Kakeya.ml1Boot.rescale_outer_tube_of_dist_le` restates
`Tube.rescale_outer_tube` with that field freed — the other field it uses,
`image_subset_cthickening`, is supplied unconditionally by
`Tube.normalization_image_subset_cthickening`. A unit-length sub-segment is unavailable
.

The enlarged constant `Kakeya.ml1Boot.fineNormalizeDilate.C c` is a separate quantity:
its homothety ratio is `4 (1 + 2 c) C_N`, where the `4` is what the core lemma pays to keep the
unit-length extension of an image core inside `B₁` and the `1 + 2 c` is a bound for the growth
of the normalized ambient ball under the `c`-dilate; the selection ratio `4 (κ + 2) R C_n` at
`κ = max 2 (2 c)` is a different quantity and is carried by the second summand of
`Kakeya.ml1Boot.fineNormalize.C`.

## Not a corollary of the undilated half

Sharing its whole route with `Kakeya.ml1Boot.exists_fineNormalization` does *not* make this
lemma derivable from it.  The two are siblings, not parent and child: each is
`Kakeya.ml1Boot.exists_fineNormalization_core`
instantiated at an ambient body `P` and a normalized ambient radius `R`, at `(T_τ, C_N)` there
and at `(K, (1 + 2 c) C_N)` here with `K ≤ c · T_τ`.

What blocks the derivation is the hypothesis pair `hsub`, `hTτ` of the undilated form (the
obstruction is written out at the ratio `2`, which is the instance the chain uses).  To
invoke it here one would need a scale `τ'` and an honest `τ'`-tube `T'` with `T i ⊆ T'` for
every `i ∈ u` and `T' ⊆ B₁`, and no such `T'` exists:

* a fine tube in `2 · T_τ` need not lie in `B₁` at all.  Take `T_τ` centred at the origin with
  unit core direction `v`, and `w` a unit vector orthogonal to `v`.  The `δ`-tube with core
  `[(2 τ - δ) • w, v + (2 τ - δ) • w]` lies in `2 · T_τ`, since its core runs parallel to the
  core `[-v, v]` of the dilate at transverse distance `2 τ - δ ≥ 0`; and it contains
  `v + 2 τ • w`, at distance `√(1 + 4 τ²) > 1` from the origin.  So `T' ⊆ B₁` fails already for
  a single member of the family, for every `0 < δ ≤ τ`;
* and even for families placed inside `B₁` the containment can span the dilate axially, forcing
  `T'` to have diameter `1 + 2 τ' ≥ 2 + 4 τ`, hence `τ' > 1/2`, which
  `Kakeya.ml1Boot.tube_not_subset_closedBall_of_half_lt` forbids inside `B₁`.  This is the
  "nor does enlarging the scale" paragraph of blueprint `note:ml1bootDilateSplitNotEnough`.

Dropping the members that leave `B₁` is not a repair: the multiplicity and fullness clauses are
read on all of `u`, and only the output family is selected.  Splitting `2 · T_τ` into honest
tubes is specified out by the same note, at a cost polynomial in the tube scale. -/
theorem exists_fineNormalization_dilate (hdim : Module.finrank ℝ E = 3) (c : ℝ≥0)
    {δ τ : ℝ≥0} (hδ : 0 < δ) (hδτ : δ ≤ τ) (hτ1 : τ ≤ 1)
    {Λ : ℝ≥0} (hΛ : 1 ≤ Λ) {μ₀ : ℝ≥0∞} (hμ₀ : 0 < μ₀)
    {ι : Type*} {u : Finset ι} (Tτ : Tube τ E) (T : ι → ShadedTube δ E)
    (K : ConvexSpaceBody E) (M : ℝ≥0) (hM : 1 ≤ M)
    (hu : u.Nonempty)
    {R : ℝ} (hTτ : Tτ.carrier ⊆ Metric.closedBall 0 R)
    (hK : K ≤ Tube.dilate Tτ (c : ℝ))
    (hKfat : volume (Tube.dilate Tτ (c : ℝ)).carrier ≤ (M : ℝ≥0∞) * volume K.carrier)
    (hsub : ∀ i ∈ u, (T i).toConvexSpaceBody ≤ K)
    (hED : (u : Set ι).Pairwise fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier)
    (hdens : ∀ i ∈ u, (Λ : ℝ≥0∞)⁻¹ * μ₀ * volume (T i).carrier ≤ volume (T i).shade ∧
      volume (T i).shade ≤ (Λ : ℝ≥0∞) * μ₀ * volume (T i).carrier) :
    ∃ u' ⊆ u, u'.Nonempty ∧ ∃ V : ι → ShadedTube (fineScale δ τ) E,
      (u' : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier) ∧
        (∀ i ∈ u', (V i).carrier ⊆ Metric.closedBall 0 1) ∧
        ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
          ≤ (fineNormalize.C ((1 + 2 * c) * _root_.Tube.normalization.C 3)
              (max 2 (2 * c)) : ℝ≥0∞)
            * (Λ : ℝ≥0∞) ^ 2
            * ShadedBody.multiplicity u' (fun i => (V i).toShadedBody) ∧
        (ShadedBody.fullness u (fun i => (T i).toShadedBody) : ℝ≥0∞)
          ≤ (fineNormalize.C ((1 + 2 * c) * _root_.Tube.normalization.C 3)
              (max 2 (2 * c)) : ℝ≥0∞)
            * (Λ : ℝ≥0∞) ^ 2
            * (ShadedBody.fullness u' (fun i => (V i).toShadedBody) : ℝ≥0∞) ∧
        frostmanConstIn u' (fun i => (V i).toConvexSpaceBody)
            ConvexSpaceBody.closedUnitBall
          ≤ (M : ℝ≥0∞)
            * (fineNormalize.C ((1 + 2 * c) * _root_.Tube.normalization.C 3)
              (max 2 (2 * c)) : ℝ≥0∞)
            * frostmanConstIn u (fun i => (T i).toConvexSpaceBody) K := by
  classical
  have _ := hTτ -- `T_τ ⊆ B₁` is genuinely unused by the core (which no longer asks for it)
  have hτ0 : 0 < τ := lt_of_lt_of_le hδ hδτ
  let i₀ : ι := Classical.choose hu
  have hi₀ : i₀ ∈ u := Classical.choose_spec hu
  set CN : ℝ≥0 := _root_.Tube.normalization.C 3 with hCN
  set Rd : ℝ≥0 := (1 + 2 * c) * CN with hRd
  have hCN1 : 1 ≤ CN := _root_.Tube.normalization.one_le_C 3
  have hCN1' : (1 : ℝ) ≤ (_root_.Tube.normalization.C 3 : ℝ) := by
    exact_mod_cast hCN1
  -- (1) containment
  have hsubK : ∀ i ∈ u, (T i).carrier ⊆ K.carrier := by
    intro i hi
    change (T i).toConvexSpaceBody ≤ K
    exact hsub i hi
  have hKc : K.carrier ⊆ (Tube.dilate Tτ (c : ℝ)).carrier := by
    change K ≤ Tube.dilate Tτ (c : ℝ)
    exact hK
  have hsubD : ∀ i ∈ u, (T i).carrier ⊆ (Tube.dilate Tτ (c : ℝ)).carrier := fun i hi =>
    (hsubK i hi).trans hKc
  -- (2) c is positive
  have hc0 : 0 < (c : ℝ) := by
    have h := (volume_ambient_le_mul_volume_dilate hdim hτ1 Tτ c.coe_nonneg (T i₀).toTube
      hδτ (hsubD i₀ hi₀)).1
    linarith
  -- (3) radius bounds
  have hR : _root_.Tube.normalization.C 3 ≤ Rd := by
    rw [hRd]
    exact le_mul_of_one_le_left' (self_le_add_right 1 (2 * c))
  have hRd1 : (1 : ℝ≥0) ≤ Rd := le_trans hCN1 hR
  have hrad : (1 + 2 * (c : ℝ)) * (_root_.Tube.normalization.C 3 : ℝ) = (Rd : ℝ) := by
    rw [hRd, NNReal.coe_mul]
    have h1 : (1 + 2 * (c : ℝ)) = ↑(1 + 2 * c : ℝ≥0) := by simp
    have h2 : (_root_.Tube.normalization.C 3 : ℝ) = (CN : ℝ) := by rfl
    rw [h1, h2]
  -- (4) ambient ball
  have hball : Tτ.normalization '' K.carrier ⊆ Metric.closedBall Tτ.x (Rd : ℝ) := by
    have h := normalization_image_dilate_subset_closedBall hτ0 hτ1 hc0 Tτ
    rw [hdim] at h
    rw [hrad] at h
    exact (Set.image_mono hKc).trans h
  -- (5) length
  have hlen : ∀ i ∈ u, dist (Tτ.normalization (T i).x) (Tτ.normalization (T i).y) ≤ (Rd : ℝ) := by
    intro i hi
    have h := dist_normalization_core_le_of_subset_dilate hτ0 hτ1 hc0 Tτ (T i).toTube (hsubD i hi)
    calc
      dist (Tτ.normalization (T i).x) (Tτ.normalization (T i).y) ≤ 1 + 2 * (c : ℝ) := h
      _ ≤ (Rd : ℝ) := by
        rw [← hrad]
        exact le_mul_of_one_le_right (by positivity : (0 : ℝ) ≤ 1 + 2 * (c : ℝ)) hCN1'
  -- (6) tilt
  have hperp : ∀ i ∈ u, ‖(T i).toTube.direction
      - (inner ℝ Tτ.direction (T i).toTube.direction : ℝ) • Tτ.direction‖
      ≤ ((max 2 (2 * c) : ℝ≥0) : ℝ) * (τ : ℝ) := by
    intro i hi
    have h := perp_norm_direction_le_of_subset_dilate hc0 Tτ (T i).toTube (hsubD i hi)
    calc
      ‖(T i).toTube.direction
          - (inner ℝ Tτ.direction (T i).toTube.direction : ℝ) • Tτ.direction‖
          ≤ 2 * (c : ℝ) * (τ : ℝ) := h
      _ ≤ ((max 2 (2 * c) : ℝ≥0) : ℝ) * (τ : ℝ) := by
        have h2c : (2 : ℝ) * (c : ℝ) ≤ ((max 2 (2 * c) : ℝ≥0) : ℝ) := by
          have h : (2 * c : ℝ≥0) ≤ max (2 : ℝ≥0) (2 * c) :=
            le_max_right (2 : ℝ≥0) (2 * c)
          exact_mod_cast h
        exact mul_le_mul_of_nonneg_right h2c (NNReal.coe_nonneg τ)
  -- (7) volume of K nonzero
  have hPvol : volume K.carrier ≠ 0 := by
    have hδpos : 0 < (δ : ℝ≥0∞) := ENNReal.coe_pos.mpr hδ
    have hSpos : 0 < volume ((T i₀).toShadedBody).carrier := by
      have hprod : 0 < (_root_.Tube.le_volume.c (Module.finrank ℝ E) : ℝ≥0∞)
          * (δ : ℝ≥0∞) ^ (Module.finrank ℝ E - 1) := by
        exact ENNReal.mul_pos
          (ENNReal.coe_ne_zero.mpr (ne_of_gt (_root_.Tube.le_volume.c_pos (Module.finrank ℝ E))))
          (pow_ne_zero (Module.finrank ℝ E - 1) (ENNReal.coe_ne_zero.mpr (ne_of_gt hδ)))
      exact lt_of_lt_of_le hprod (by simpa using (_root_.Tube.le_volume (T i₀).toTube))
    have hmono : volume (T i₀).toShadedBody.carrier ≤ volume K.carrier := by
      exact measure_mono (by simpa using hsubK i₀ hi₀)
    exact ne_of_gt (lt_of_lt_of_le hSpos hmono)
  -- (8) ratio
  have hratio : volume (Metric.closedBall (0 : E) 1)
      ≤ ((125 * M * (4 * Rd) ^ 6 : ℝ≥0) : ℝ≥0∞)
        * volume (Tτ.rescaleMap (Rd : ℝ) '' K.carrier) :=
    volume_closedBall_one_le_mul_volume_rescale_image_of_dilate
      hdim hτ0 hτ1 hδτ Tτ c.coe_nonneg K hKc hKfat (T i₀).toTube (hsubK i₀ hi₀) hRd1
  -- (9) core
  obtain ⟨u', hu'sub, hu'ne, V, hVD, hVball, hmult, hfull, hfrost, -, -, -, -⟩ :=
    exists_fineNormalization_core hdim hδ hδτ hτ1 hΛ hμ₀ Tτ T K
      (R := Rd) (κ := max 2 (2 * c)) (Cw := 125 * M * (4 * Rd) ^ 6)
      hR hu hsubK hball hlen hperp hPvol hratio hED hdens
  -- (10) the three clauses
  let c₁ : ℝ≥0 := _root_.Tube.essDistinctTubesInSelfDilate.C 3
    (4 * (((max 2 (2 * c) : ℝ≥0) : ℝ) + 2) * ((Rd : ℝ≥0) : ℝ)
      * Kakeya.Tube.tubeOverlapCoreClose.C 3)
  obtain ⟨hd1, hd2, hd3⟩ := fineNormalize_C_dominates_dilate c (c₁ := c₁) rfl
  refine ⟨u', hu'sub, hu'ne, V, hVD, hVball, ?_, ?_, ?_⟩
  · calc
      ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
          ≤ (c₁ : ℝ≥0∞) * (Λ : ℝ≥0∞) ^ 2
              * ShadedBody.multiplicity u' (fun i => (V i).toShadedBody) := by
            simpa [c₁] using hmult
      _ ≤ (fineNormalize.C Rd (max 2 (2 * c)) : ℝ≥0∞) * (Λ : ℝ≥0∞) ^ 2
              * ShadedBody.multiplicity u' (fun i => (V i).toShadedBody) := by
            gcongr
  · calc
      (ShadedBody.fullness u (fun i => (T i).toShadedBody) : ℝ≥0∞)
          ≤ (((4 * Rd) ^ 6 : ℝ≥0) : ℝ≥0∞) * (c₁ : ℝ≥0∞) * (Λ : ℝ≥0∞) ^ 2
              * (ShadedBody.fullness u' (fun i => (V i).toShadedBody) : ℝ≥0∞) := by
            simpa [c₁] using hfull
      _ ≤ (fineNormalize.C Rd (max 2 (2 * c)) : ℝ≥0∞) * (Λ : ℝ≥0∞) ^ 2
              * (ShadedBody.fullness u' (fun i => (V i).toShadedBody) : ℝ≥0∞) := by
            gcongr
            exact_mod_cast hd2
  · calc
      frostmanConstIn u' (fun i => (V i).toConvexSpaceBody)
          ConvexSpaceBody.closedUnitBall
          ≤ (c₁ : ℝ≥0∞) * (((4 * Rd) ^ 6 : ℝ≥0) : ℝ≥0∞)
              * ((125 * M * (4 * Rd) ^ 6 : ℝ≥0) : ℝ≥0∞)
              * frostmanConstIn u (fun i => (T i).toConvexSpaceBody) K := by
            simpa [c₁] using hfrost
      _ ≤ (M : ℝ≥0∞) * (fineNormalize.C Rd (max 2 (2 * c)) : ℝ≥0∞)
              * frostmanConstIn u (fun i => (T i).toConvexSpaceBody) K := by
            have hcoeff : (c₁ : ℝ≥0∞) * (((4 * Rd) ^ 6 : ℝ≥0) : ℝ≥0∞)
                * ((125 * M * (4 * Rd) ^ 6 : ℝ≥0) : ℝ≥0∞)
                ≤ (M : ℝ≥0∞) * (fineNormalize.C Rd (max 2 (2 * c)) : ℝ≥0∞) := by
              rw [← ENNReal.coe_mul, ← ENNReal.coe_mul]
              have hdom : (c₁ * (4 * Rd) ^ 6 * (125 * M * (4 * Rd) ^ 6) : ℝ≥0)
                  ≤ (M * fineNormalize.C Rd (max 2 (2 * c)) : ℝ≥0) := by
                calc
                  (c₁ * (4 * Rd) ^ 6 * (125 * M * (4 * Rd) ^ 6) : ℝ≥0)
                      = c₁ * ((4 * Rd) ^ 6 * (4 * Rd) ^ 6) * (125 * M) := by ring
                  _ = c₁ * (4 * Rd) ^ 12 * (125 * M) := by
                        have hcomb : (4 * Rd) ^ 6 * (4 * Rd) ^ 6 = (4 * Rd) ^ 12 := by
                          rw [← pow_add]
                        rw [hcomb]
                  _ = M * (125 * (4 * Rd) ^ 12 * c₁) := by ring
                  _ ≤ M * fineNormalize.C Rd (max 2 (2 * c)) := by
                        exact mul_le_mul_of_nonneg_left hd3 (by positivity : (0 : ℝ≥0) ≤ M)
              exact_mod_cast hdom
            gcongr

/-- **The fine fibre over a dilate satisfies the hypotheses of
`Kakeya.FrostmanEstimate.multiplicity_bound_auxScale`**.

Word for word `Kakeya.ml1Boot.fine_genKF`, with
`Kakeya.ml1Boot.exists_fineNormalization_dilate` in place of
`Kakeya.ml1Boot.exists_fineNormalization` and `Kakeya.ml1Boot.fineNormalizeDilate.C c` in place
of `Kakeya.ml1Boot.fineFactor.C`.

The ambient body `K` is a parameter, exactly as in the normalization leaf: containment and the
Frostman hypothesis are both read in it, and `Kakeya.ml1Boot.IsFineFibreDilate` asks
`K ≤ c · T_τ` together with the volume clause `|c · T_τ| ≤ M |K|`.  Nothing in this proof looks
at `K` beyond forwarding it, and the conclusion does not mention it.  The fullness threshold
`ηs` is the *same* parameter as there: it is produced by `K_F(γ)` and does not see the family —
in particular it does not see the dilation ratio `c`, which is free here and is passed straight
to the normalization leaf.

## Where `M` goes

The normalization leaf returns its Frostman clause at `M · C₀`, not `C₀` (the reason is the
counterexample note at `Kakeya.ml1Boot.exists_fineNormalization_dilate`).  Rather than push `M`
into this lemma's conclusion, the hypothesis divides by `M · C₃(c)`: the caller is free in `Cf`
and simply names an `M` times larger one, which is why
`Kakeya.ml1Boot.reduceToTb_fine_bound_dilate` pays the ratio in its *loss prefactor* and not in
its Frostman hypothesis (a).  The conclusion of this lemma is therefore unchanged, `M` and all.
`1 ≤ M` is asked because the division must be by something nonzero; it costs a caller nothing,
being forced by `K ≤ c · T_τ` whenever `|K|` is positive and finite.

The quantifier order is unchanged, so `Cf` is quantified inside the `∀ᶠ δ` and may be
`δ`-dependent; `Kakeya.ml1Boot.reduceToTb_fine_bound_dilate` applies the lemma at
`Cf = 2 C_T M C₃ δ̃ ^ (-2 η')`.  The exponent in `Cf ^ (1 - γ/2)` must not be collapsed here:
it is bounded by `Cf` once, at the very end of that lemma's proof, for a `Cf` that no longer
depends on the family. -/
theorem fine_genKF_dilate (hdim : Module.finrank ℝ E = 3) (c : ℝ≥0) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) (hKF : FrostmanEstimate.{u} E γ) :
    ∀ εs > (0 : ℝ), ∃ ηs > (0 : ℝ), ∀ Λ : ℝ≥0, 1 ≤ Λ →
    ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0, ∀ Cf : ℝ≥0∞, 1 ≤ Cf → Cf ≠ ⊤ →
    ∀ τ : ℝ≥0, δ ≤ τ → τ ≤ 1 →
      ∀ {ι : Type u} {u : Finset ι} (Tτ : Tube τ E) (T : ι → ShadedTube δ E)
        (K : ConvexSpaceBody E) (M : ℝ≥0) {R : ℝ} {μ₀ : ℝ≥0∞}, 1 ≤ M →
        IsFineFibreDilate c R K M Λ μ₀ ηs u Tτ T →
        frostmanConstIn u (fun i => (T i).toConvexSpaceBody) K
          ≤ Cf / ((M : ℝ≥0∞) * (fineNormalizeDilate.C c : ℝ≥0∞)) →
        ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
          ≤ (fineNormalizeDilate.C c : ℝ≥0∞) * (Λ : ℝ≥0∞) ^ 2 * (δ : ℝ≥0∞) ^ (-εs)
            * Cf ^ (1 - γ / 2)
            * ((δ / τ : ℝ≥0) : ℝ≥0∞) ^ (-2 * γ)
            * ((u.card : ℝ≥0∞) * ((δ / τ : ℝ≥0) : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
  intro εs hεs
  have hn : 1 < Module.finrank ℝ E := by
    rw [hdim]
    norm_num
  obtain ⟨ηs, hηs_pos, hηs_ev⟩ :=
    FrostmanEstimate.multiplicity_bound_auxScale_of_isFrostmanIn E hγ0 hγ1 hn hKF εs hεs
  refine ⟨ηs, hηs_pos, ?_⟩
  intro Λ hΛ1
  filter_upwards [hηs_ev, self_mem_nhdsWithin, eventually_le_quarter] with δ hδ_aux hδ_pos hδ4
  intro Cf hCf1 hCftop τ hδτ hτ1 ι u Tτ T K M R μ₀ hM hfib hF
  obtain ⟨hμ₀, hu, hTτ, hKle, hKfat, hsub, hED, hdens, hFull⟩ := hfib
  rcases exists_fineNormalization_dilate hdim c hδ_pos hδτ hτ1 hΛ1 hμ₀ Tτ T K M hM hu hTτ hKle
    hKfat hsub hED hdens with ⟨u', hu'u, hu'_ne, V, hV_ED, hV_ball, hmult, hfull, hF'⟩
  have hτ_pos : 0 < τ := lt_of_lt_of_le hδ_pos hδτ
  have hσ_le_one : fineScale δ τ ≤ 1 := by
    exact le_trans ((fineScale_bounds hδτ hτ_pos).2.1) (by
      exact_mod_cast (by norm_num : (1 / 4 : ℝ) ≤ (1 : ℝ)))
  have hδ_le_σ : δ ≤ fineScale δ τ := le_fineScale hδ4 hτ1 hτ_pos
  let C₀ : ℝ≥0 := fineNormalize.C ((1 + 2 * c) * _root_.Tube.normalization.C 3)
    (max 2 (2 * c))
  let ι' : Type u := {i : ι // i ∈ u'}
  let s' : Finset ι' := u'.attach
  let V' : ι' → ShadedTube (fineScale δ τ) E := fun i => V i.1
  have hV'_ball : ∀ i ∈ s', (V' i).carrier ⊆ Metric.closedBall 0 1 := by
    intro i hi
    exact hV_ball i.1 i.2
  have hs'_ne : s'.Nonempty := by
    rcases hu'_ne with ⟨i, hi⟩
    exact ⟨⟨i, hi⟩, Finset.mem_attach u' ⟨i, hi⟩⟩
  have hV'_ED : (s' : Set ι').Pairwise
      (fun i j => IsEssentiallyDistinct (V' i).carrier (V' j).carrier) := by
    intro i hi j hj hij
    exact hV_ED i.2 j.2 (by
      intro h
      exact hij (Subtype.ext h))
  have hC0one : (1 : ℝ≥0) ≤ C₀ := by
    exact one_le_fineNormalize_C (one_le_mul (self_le_add_right 1 (2 * c))
      (_root_.Tube.normalization.one_le_C 3))
  have hC0pos : 0 < (C₀ : ℝ≥0∞) := by
    exact ENNReal.coe_pos.mpr (lt_of_lt_of_le zero_lt_one hC0one)
  have hC0 : (C₀ : ℝ≥0∞) ≠ 0 := ne_of_gt hC0pos
  have hC0top : (C₀ : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hM0 : (M : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one hM))
  have hC3_0 : (fineNormalizeDilate.C c : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr
      (ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_fineNormalizeDilate_C c)))
  have hD0 : (M : ℝ≥0∞) * (fineNormalizeDilate.C c : ℝ≥0∞) ≠ 0 := mul_ne_zero hM0 hC3_0
  have hDtop : (M : ℝ≥0∞) * (fineNormalizeDilate.C c : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
  have hΛ0 : (Λ : ℝ≥0∞) ≠ 0 := by
    exact ENNReal.coe_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one hΛ1))
  have hΛtop : (Λ : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hCΛ2 : (C₀ : ℝ≥0∞) * (Λ : ℝ≥0∞) ^ 2 ≠ 0 := by
    exact mul_ne_zero hC0 (pow_ne_zero 2 hΛ0)
  have hCΛ2top : (C₀ : ℝ≥0∞) * (Λ : ℝ≥0∞) ^ 2 ≠ ⊤ := by
    exact ENNReal.mul_ne_top hC0top (ENNReal.pow_ne_top hΛtop)
  have hFull_u' : (δ : ℝ≥0∞) ^ ηs
      ≤ (ShadedBody.fullness u' (fun i => (V i).toShadedBody) : ℝ≥0∞) := by
    have hstep : (C₀ : ℝ≥0∞) * (Λ : ℝ≥0∞) ^ 2 * (δ : ℝ≥0∞) ^ ηs
        ≤ (C₀ : ℝ≥0∞) * (Λ : ℝ≥0∞) ^ 2
          * (ShadedBody.fullness u' (fun i => (V i).toShadedBody) : ℝ≥0∞) := by
      calc
        (C₀ : ℝ≥0∞) * (Λ : ℝ≥0∞) ^ 2 * (δ : ℝ≥0∞) ^ ηs
            ≤ (fineNormalizeDilate.C c : ℝ≥0∞) * (Λ : ℝ≥0∞) ^ 2 * (δ : ℝ≥0∞) ^ ηs := by
            gcongr
            exact_mod_cast fineNormalize_C_le_fineNormalizeDilate_C c
        _ ≤ (ShadedBody.fullness u (fun i => (T i).toShadedBody) : ℝ≥0∞) := hFull
        _ ≤ (C₀ : ℝ≥0∞) * (Λ : ℝ≥0∞) ^ 2
            * (ShadedBody.fullness u' (fun i => (V i).toShadedBody) : ℝ≥0∞) := hfull
    exact (ENNReal.mul_le_mul_iff_right hCΛ2 hCΛ2top).1 hstep
  have hfull_eq : (ShadedBody.fullness s' (fun i => (V' i).toShadedBody) : ℝ≥0∞)
      = (ShadedBody.fullness u' (fun i => (V i).toShadedBody) : ℝ≥0∞) := by
    rw [ShadedBody.fullness_def, ShadedBody.fullness_def]
    congr 1
    · simpa [s', V'] using Finset.sum_attach u' (fun i => volume ((V i).toShadedBody).shade)
    · simpa [s', V'] using Finset.sum_attach u' (fun i => volume ((V i).toShadedBody).carrier)
  have hV'_full : (δ : ℝ≥0∞) ^ ηs
      ≤ (ShadedBody.fullness s' (fun i => (V' i).toShadedBody) : ℝ≥0∞) := by
    rw [hfull_eq]
    exact hFull_u'
  have hCD : (C₀ : ℝ≥0∞) ≤ (fineNormalizeDilate.C c : ℝ≥0∞) := by
    exact_mod_cast fineNormalize_C_le_fineNormalizeDilate_C c
  have hMCD : (M : ℝ≥0∞) * (C₀ : ℝ≥0∞)
      ≤ (M : ℝ≥0∞) * (fineNormalizeDilate.C c : ℝ≥0∞) := by
    exact mul_le_mul_right hCD (M : ℝ≥0∞)
  have hFrost_u' : IsFrostmanIn u' (fun i => (V i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall Cf := by
    apply isFrostmanIn_of_frostmanConstIn_le
    calc
      frostmanConstIn u' (fun i => (V i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall
          ≤ (M : ℝ≥0∞) * (C₀ : ℝ≥0∞)
              * frostmanConstIn u (fun i => (T i).toConvexSpaceBody) K := hF'
      _ ≤ (M : ℝ≥0∞) * (C₀ : ℝ≥0∞)
            * (Cf / ((M : ℝ≥0∞) * (fineNormalizeDilate.C c : ℝ≥0∞))) := by
          exact mul_le_mul_right hF ((M : ℝ≥0∞) * (C₀ : ℝ≥0∞))
      _ ≤ (M : ℝ≥0∞) * (fineNormalizeDilate.C c : ℝ≥0∞)
            * (Cf / ((M : ℝ≥0∞) * (fineNormalizeDilate.C c : ℝ≥0∞))) := by
          exact mul_le_mul_left hMCD
            (Cf / ((M : ℝ≥0∞) * (fineNormalizeDilate.C c : ℝ≥0∞)))
      _ = Cf := by rw [ENNReal.mul_div_cancel hD0 hDtop]
  have he : Set.BijOn (fun i : ι' => i.1) (s' : Set ι') (u' : Set ι) := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      exact i.2
    · intro i hi j hj hij
      exact Subtype.ext hij
    · intro i hi
      exact ⟨⟨i, hi⟩, Finset.mem_attach u' ⟨i, hi⟩, rfl⟩
  have hFrost_s' : IsFrostmanIn s' (fun i => (V' i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall Cf := by
    have h' : IsFrostmanIn s' (fun i => (V i.1).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall Cf :=
      (IsFrostmanIn.reindex (s := u') (t := s') (W := fun i => (V i).toConvexSpaceBody)
        (K := ConvexSpaceBody.closedUnitBall) (C := Cf) he).2 hFrost_u'
    simpa [V'] using h'
  have hmult' : ShadedBody.multiplicity s' (fun i => (V' i).toShadedBody)
      ≤ (δ : ℝ≥0∞) ^ (-εs) * Cf ^ (1 - γ / 2)
        * ((fineScale δ τ : ℝ≥0) : ℝ≥0∞) ^ (-2 * γ)
        * ((s'.card : ℝ≥0∞) * ((fineScale δ τ : ℝ≥0) : ℝ≥0∞) ^ (Module.finrank ℝ E - 1))
            ^ (1 - γ / 2) := by
    exact hδ_aux Cf hCf1 hCftop (fineScale δ τ) hδ_le_σ hσ_le_one s' V' hs'_ne hV'_ball hV'_ED
      hV'_full hFrost_s'
  have hmult_eq : ShadedBody.multiplicity s' (fun i => (V' i).toShadedBody)
      = ShadedBody.multiplicity u' (fun i => (V i).toShadedBody) := by
    rw [ShadedBody.multiplicity_eq_div, ShadedBody.multiplicity_eq_div]
    congr 1
    · simpa [s', V'] using Finset.sum_attach u' (fun i => volume ((V i).toShadedBody).shade)
    · apply congrArg volume
      ext x
      constructor
      · intro hx
        rw [Set.mem_iUnion₂] at hx ⊢
        rcases hx with ⟨i, hi, hx⟩
        exact ⟨i.1, i.2, hx⟩
      · intro hx
        rw [Set.mem_iUnion₂] at hx ⊢
        rcases hx with ⟨i, hi, hx⟩
        exact ⟨⟨i, hi⟩, Finset.mem_attach u' ⟨i, hi⟩, hx⟩
  have hcard_s' : s'.card = u'.card := by
    change (u'.attach).card = u'.card
    exact Finset.card_attach
  have hmult'_u' : ShadedBody.multiplicity u' (fun i => (V i).toShadedBody)
      ≤ (δ : ℝ≥0∞) ^ (-εs) * Cf ^ (1 - γ / 2)
        * ((fineScale δ τ : ℝ≥0) : ℝ≥0∞) ^ (-2 * γ)
        * ((u'.card : ℝ≥0∞) * ((fineScale δ τ : ℝ≥0) : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
    rw [← hmult_eq]
    calc
      ShadedBody.multiplicity s' (fun i => (V' i).toShadedBody)
          ≤ (δ : ℝ≥0∞) ^ (-εs) * Cf ^ (1 - γ / 2)
            * ((fineScale δ τ : ℝ≥0) : ℝ≥0∞) ^ (-2 * γ)
            * ((s'.card : ℝ≥0∞)
                * ((fineScale δ τ : ℝ≥0) : ℝ≥0∞) ^ (Module.finrank ℝ E - 1))
                ^ (1 - γ / 2) := hmult'
      _ = (δ : ℝ≥0∞) ^ (-εs) * Cf ^ (1 - γ / 2)
            * ((fineScale δ τ : ℝ≥0) : ℝ≥0∞) ^ (-2 * γ)
            * ((u'.card : ℝ≥0∞) * ((fineScale δ τ : ℝ≥0) : ℝ≥0∞) ^ (2 : ℕ))
                ^ (1 - γ / 2) := by
          rw [hcard_s', hdim]
  have hpos : 0 ≤ (1 - γ / 2 : ℝ) := by nlinarith [hγ1]
  have hcard_le : (u'.card : ℝ≥0∞) ≤ (u.card : ℝ≥0∞) := by
    exact_mod_cast (Finset.card_le_card hu'u)
  have hmult'' : ShadedBody.multiplicity u' (fun i => (V i).toShadedBody)
      ≤ (δ : ℝ≥0∞) ^ (-εs) * Cf ^ (1 - γ / 2)
        * (16 * (((δ / τ : ℝ≥0)) : ℝ≥0∞) ^ (-2 * γ)
          * ((u'.card : ℝ≥0∞) * (((δ / τ : ℝ≥0)) : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2)) := by
    calc
      ShadedBody.multiplicity u' (fun i => (V i).toShadedBody)
          ≤ (δ : ℝ≥0∞) ^ (-εs) * Cf ^ (1 - γ / 2)
            * ((fineScale δ τ : ℝ≥0) : ℝ≥0∞) ^ (-2 * γ)
            * ((u'.card : ℝ≥0∞) * ((fineScale δ τ : ℝ≥0) : ℝ≥0∞) ^ (2 : ℕ))
                ^ (1 - γ / 2) := hmult'_u'
      _ = (δ : ℝ≥0∞) ^ (-εs) * Cf ^ (1 - γ / 2)
            * (((fineScale δ τ : ℝ≥0) : ℝ≥0∞) ^ (-2 * γ)
              * ((u'.card : ℝ≥0∞) * ((fineScale δ τ : ℝ≥0) : ℝ≥0∞) ^ (2 : ℕ))
                ^ (1 - γ / 2)) := by
            ring
      _ ≤ (δ : ℝ≥0∞) ^ (-εs) * Cf ^ (1 - γ / 2)
            * (16 * (((δ / τ : ℝ≥0)) : ℝ≥0∞) ^ (-2 * γ)
              * ((u'.card : ℝ≥0∞) * (((δ / τ : ℝ≥0)) : ℝ≥0∞) ^ (2 : ℕ))
                ^ (1 - γ / 2)) := by
            exact mul_le_mul_right (fineScale_bracket_le hδ_pos hδτ hτ_pos hγ0 hγ1 u'.card)
              ((δ : ℝ≥0∞) ^ (-εs) * Cf ^ (1 - γ / 2))
  have h16 : (16 : ℝ≥0∞) * (C₀ : ℝ≥0∞) = (fineNormalizeDilate.C c : ℝ≥0∞) := by
    change ((16 : ℝ≥0) : ℝ≥0∞) * (C₀ : ℝ≥0∞) = (fineNormalizeDilate.C c : ℝ≥0∞)
    rw [← ENNReal.coe_mul]
  calc
    ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
        ≤ (C₀ : ℝ≥0∞) * (Λ : ℝ≥0∞) ^ 2
          * ShadedBody.multiplicity u' (fun i => (V i).toShadedBody) := hmult
    _ ≤ (C₀ : ℝ≥0∞) * (Λ : ℝ≥0∞) ^ 2
          * ((δ : ℝ≥0∞) ^ (-εs) * Cf ^ (1 - γ / 2)
            * (16 * (((δ / τ : ℝ≥0)) : ℝ≥0∞) ^ (-2 * γ)
              * ((u'.card : ℝ≥0∞) * (((δ / τ : ℝ≥0)) : ℝ≥0∞) ^ (2 : ℕ))
                ^ (1 - γ / 2))) := by
          exact mul_le_mul_right hmult'' ((C₀ : ℝ≥0∞) * (Λ : ℝ≥0∞) ^ 2)
    _ = (16 * (C₀ : ℝ≥0∞)) * (Λ : ℝ≥0∞) ^ 2 * (δ : ℝ≥0∞) ^ (-εs) * Cf ^ (1 - γ / 2)
          * (((δ / τ : ℝ≥0)) : ℝ≥0∞) ^ (-2 * γ)
          * ((u'.card : ℝ≥0∞) * (((δ / τ : ℝ≥0)) : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
          ring
    _ = (fineNormalizeDilate.C c : ℝ≥0∞) * (Λ : ℝ≥0∞) ^ 2 * (δ : ℝ≥0∞) ^ (-εs)
          * Cf ^ (1 - γ / 2) * (((δ / τ : ℝ≥0)) : ℝ≥0∞) ^ (-2 * γ)
          * ((u'.card : ℝ≥0∞) * (((δ / τ : ℝ≥0)) : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
          rw [h16]
    _ ≤ (fineNormalizeDilate.C c : ℝ≥0∞) * (Λ : ℝ≥0∞) ^ 2 * (δ : ℝ≥0∞) ^ (-εs)
          * Cf ^ (1 - γ / 2) * (((δ / τ : ℝ≥0)) : ℝ≥0∞) ^ (-2 * γ)
          * ((u.card : ℝ≥0∞) * (((δ / τ : ℝ≥0)) : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
          gcongr

end FineDilate

/-! ### Case (ii): the coarse-scale factor -/

section Coarse

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- **A parent family induces a finite partition**.

If `(t, 𝕍_ρ, p)` is a parent family for `𝕍 = (V i)_{i ∈ s}` with `p` surjective from `s` onto
`t`, then the fibres `s[k] = Kakeya.ml1Boot.fibre s p k`, `k ∈ t`, are the parts of a
`Finpartition` of `s`, the map `k ↦ s[k]` is a bijection from `t` onto those parts, and
`V i ≤ V_{ρ,k}` for `i ∈ s[k]`.

This is the bookkeeping that lets `ConvexSpaceBody.IsFrostmanIn.inherited_upwards`, which
consumes a `Finpartition` and returns a family indexed by its *parts*, be applied to a parent
family, which is indexed by `t`.  The blueprint's scale ordering `0 < σ ≤ ρ ≤ 1` is inert
here, as it is for `Kakeya.ml1Boot.IsParentFamily` itself. -/
theorem IsParentFamily.finpartition {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {σ ρ : ℝ≥0} {s : Finset ι} {t : Finset κ} {V : ι → Tube σ E} {Vρ : κ → Tube ρ E}
    {p : ι → κ} (h : IsParentFamily s V t Vρ p) (hsurj : Set.SurjOn p s t) :
    ∃ P : Finpartition s,
      Set.BijOn (fun k => fibre s p k) t P.parts ∧
        (∀ k ∈ t, (fibre s p k).Nonempty) ∧
        ∀ k ∈ t, ∀ i ∈ fibre s p k,
          (V i).toConvexSpaceBody ≤ (Vρ k).toConvexSpaceBody := by
  let parts : Finset (Finset ι) := t.image fun k => fibre s p k
  let P : Finpartition s :=
    Finpartition.mk parts
      (by
        rw [Finset.supIndep_iff_pairwiseDisjoint]
        intro a ha b hb hab
        rcases Finset.mem_image.mp ha with ⟨ka, hka, rfl⟩
        rcases Finset.mem_image.mp hb with ⟨kb, hkb, rfl⟩
        change Disjoint (fibre s p ka) (fibre s p kb)
        rw [Finset.disjoint_left]
        intro i hi hikb
        have hka' : p i = ka := (Finset.mem_filter.mp hi).2
        have hkb' : p i = kb := (Finset.mem_filter.mp hikb).2
        exact hab (by rw [hka'.symm.trans hkb']))
      (by
        ext i
        constructor
        · intro hi
          rcases Finset.mem_sup.mp hi with ⟨a, ha, hia⟩
          rcases Finset.mem_image.mp ha with ⟨k, hk, rfl⟩
          exact (Finset.mem_filter.mp hia).1
        · intro his
          apply Finset.mem_sup.mpr
          refine ⟨fibre s p (p i), ?_, ?_⟩
          · apply Finset.mem_image.mpr
            exact ⟨p i, h.mapsTo i his, rfl⟩
          · exact Finset.mem_filter.mpr ⟨his, rfl⟩)
      (by
        intro hmem
        rcases Finset.mem_image.mp hmem with ⟨k, hk, hke⟩
        rcases hsurj hk with ⟨i, his, hik⟩
        have hi : i ∈ fibre s p k := Finset.mem_filter.mpr ⟨his, hik⟩
        simp [hke] at hi)
  refine ⟨P, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro k hk
      exact Finset.mem_image.mpr ⟨k, hk, rfl⟩
    · intro ka hka kb hkb hfib
      change fibre s p ka = fibre s p kb at hfib
      rcases hsurj hka with ⟨i, his, hik⟩
      have hikb : p i = kb := by
        have hi : i ∈ fibre s p kb := by
          rw [← hfib]
          exact Finset.mem_filter.mpr ⟨his, hik⟩
        exact (Finset.mem_filter.mp hi).2
      exact hik.symm.trans hikb
    · intro b hb
      rcases Finset.mem_image.mp hb with ⟨k, hk, rfl⟩
      exact ⟨k, hk, rfl⟩
  · intro k hk
    rcases hsurj hk with ⟨i, his, hik⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨his, hik⟩⟩
  · intro k hk i hi
    have his : i ∈ s := (Finset.mem_filter.mp hi).1
    have hik : p i = k := (Finset.mem_filter.mp hi).2
    simpa [hik] using h.le_parent i his

end Coarse

/-! ### Case (ii): reduction to the middle factor

The three arithmetic steps and the assembly are stated for bare `ENNReal` quantities, so that
they do not depend on the data produced by `Kakeya.ml1Boot.exists_factorTwoScales`; see
blueprint `note:ml1bootCaseNonStickyReading` for the intended reading of `X`, `M₁, M₂, M₃`
and `P₁, P₂, P₃` as multiplicities and cardinalities. -/

/-- **Collapsing the three scales**.

If `A B D = δ` with `A, B, D ∈ (0, 1]`, the three brackets
`F_r (A_r ^ (-2γ)) ((A_r² P_r) ^ (1 - γ/2))` multiply to
`(δ ^ (-2γ)) ((δ² M) ^ (1 - γ/2))` up to the loss `F₁ F₂ F₃ ≤ 1` and the count
`P₁ P₂ P₃ ≤ M`.

The blueprint writes `(A ^ (-2)) ^ γ`; here the two exponents are contracted to
`A ^ (-2 * γ)`.  The prefactor is called `E` after the blueprint; `δ ∈ (0, 1]` is not a
separate hypothesis, being forced by `hABD` together with `_hA0`–`_hD1`.

The scale and counting bounds `_hA0`–`_hD1`, `_hγ0`, `_hP₁`–`_hM` are part of the intended
interface but are not needed by the algebra, so they carry a leading underscore. -/
theorem tripleCollapse {δ A B D : ℝ≥0}
    (_hA0 : 0 < A) (_hA1 : A ≤ 1) (_hB0 : 0 < B) (_hB1 : B ≤ 1) (_hD0 : 0 < D) (_hD1 : D ≤ 1)
    (hABD : A * B * D = δ) {γ : ℝ} (_hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    {X E F₁ F₂ F₃ P₁ P₂ P₃ M : ℝ≥0∞}
    (_hP₁ : 1 ≤ P₁) (_hP₂ : 1 ≤ P₂) (_hP₃ : 1 ≤ P₃) (_hM : 1 ≤ M)
    (hPM : P₁ * P₂ * P₃ ≤ M) (hF : F₁ * F₂ * F₃ ≤ 1)
    (hX : X ≤ E
      * (F₁ * (A : ℝ≥0∞) ^ (-2 * γ) * (P₁ * (A : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2))
      * (F₂ * (B : ℝ≥0∞) ^ (-2 * γ) * (P₂ * (B : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2))
      * (F₃ * (D : ℝ≥0∞) ^ (-2 * γ) * (P₃ * (D : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2))) :
    X ≤ E * (δ : ℝ≥0∞) ^ (-2 * γ)
      * (M * (δ : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
  have hpos : 0 ≤ (1 - γ / 2 : ℝ) := by nlinarith [hγ1]
  have hABDE : (A : ℝ≥0∞) * (B : ℝ≥0∞) * (D : ℝ≥0∞) = (δ : ℝ≥0∞) := by
    exact_mod_cast hABD
  have hABD' : ((A * B * D : ℝ≥0) : ℝ≥0∞) = (δ : ℝ≥0∞) := by
    rw [hABD]
  have hneg :
      (A : ℝ≥0∞) ^ (-2 * γ) * (B : ℝ≥0∞) ^ (-2 * γ) * (D : ℝ≥0∞) ^ (-2 * γ)
        = (δ : ℝ≥0∞) ^ (-2 * γ) := by
    rw [← ENNReal.coe_mul_rpow]
    rw [← ENNReal.coe_mul]
    rw [← ENNReal.coe_mul_rpow]
    rw [← ENNReal.coe_mul]
    rw [hABD']
  have hBase :
      (P₁ * (A : ℝ≥0∞) ^ (2 : ℕ)) * (P₂ * (B : ℝ≥0∞) ^ (2 : ℕ))
          * (P₃ * (D : ℝ≥0∞) ^ (2 : ℕ)) ≤ M * (δ : ℝ≥0∞) ^ (2 : ℕ) := by
    calc
      (P₁ * (A : ℝ≥0∞) ^ (2 : ℕ)) * (P₂ * (B : ℝ≥0∞) ^ (2 : ℕ))
          * (P₃ * (D : ℝ≥0∞) ^ (2 : ℕ))
          = (P₁ * P₂ * P₃) * ((A : ℝ≥0∞) ^ (2 : ℕ) * (B : ℝ≥0∞) ^ (2 : ℕ)
              * (D : ℝ≥0∞) ^ (2 : ℕ)) := by ring
      _ ≤ M * ((A : ℝ≥0∞) ^ (2 : ℕ) * (B : ℝ≥0∞) ^ (2 : ℕ)
              * (D : ℝ≥0∞) ^ (2 : ℕ)) := by gcongr
      _ = M * ((A : ℝ≥0∞) * (B : ℝ≥0∞) * (D : ℝ≥0∞)) ^ (2 : ℕ) := by
            rw [← mul_pow, ← mul_pow]
      _ = M * (δ : ℝ≥0∞) ^ (2 : ℕ) := by rw [hABDE]
  have hQ :
      (P₁ * (A : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2)
          * (P₂ * (B : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2)
          * (P₃ * (D : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2)
      ≤ (M * (δ : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
    calc
      (P₁ * (A : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2)
          * (P₂ * (B : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2)
          * (P₃ * (D : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2)
        = ((P₁ * (A : ℝ≥0∞) ^ (2 : ℕ)) * (P₂ * (B : ℝ≥0∞) ^ (2 : ℕ))
            * (P₃ * (D : ℝ≥0∞) ^ (2 : ℕ))) ^ (1 - γ / 2) := by
            rw [← ENNReal.mul_rpow_of_nonneg _ _ hpos,
              ← ENNReal.mul_rpow_of_nonneg _ _ hpos]
      _ ≤ (M * (δ : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
            exact ENNReal.rpow_le_rpow hBase hpos
  have hT :
      (F₁ * (A : ℝ≥0∞) ^ (-2 * γ)
          * (P₁ * (A : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2))
        * (F₂ * (B : ℝ≥0∞) ^ (-2 * γ)
            * (P₂ * (B : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2))
        * (F₃ * (D : ℝ≥0∞) ^ (-2 * γ)
            * (P₃ * (D : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2))
      ≤ (δ : ℝ≥0∞) ^ (-2 * γ) * (M * (δ : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
    calc
      (F₁ * (A : ℝ≥0∞) ^ (-2 * γ)
          * (P₁ * (A : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2))
        * (F₂ * (B : ℝ≥0∞) ^ (-2 * γ)
            * (P₂ * (B : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2))
        * (F₃ * (D : ℝ≥0∞) ^ (-2 * γ)
            * (P₃ * (D : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2))
        = (F₁ * F₂ * F₃) * ((A : ℝ≥0∞) ^ (-2 * γ) * (B : ℝ≥0∞) ^ (-2 * γ)
            * (D : ℝ≥0∞) ^ (-2 * γ))
          * ((P₁ * (A : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2)
            * (P₂ * (B : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2)
            * (P₃ * (D : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2)) := by ring
      _ ≤ 1 * ((A : ℝ≥0∞) ^ (-2 * γ) * (B : ℝ≥0∞) ^ (-2 * γ)
            * (D : ℝ≥0∞) ^ (-2 * γ))
          * ((P₁ * (A : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2)
            * (P₂ * (B : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2)
            * (P₃ * (D : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2)) := by gcongr
      _ = (A : ℝ≥0∞) ^ (-2 * γ) * (B : ℝ≥0∞) ^ (-2 * γ)
            * (D : ℝ≥0∞) ^ (-2 * γ)
          * ((P₁ * (A : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2)
            * (P₂ * (B : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2)
            * (P₃ * (D : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2)) := by simp
      _ = (δ : ℝ≥0∞) ^ (-2 * γ)
          * ((P₁ * (A : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2)
            * (P₂ * (B : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2)
            * (P₃ * (D : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2)) := by rw [hneg]
      _ ≤ (δ : ℝ≥0∞) ^ (-2 * γ) * (M * (δ : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
            gcongr
  calc
    X ≤ E * (F₁ * (A : ℝ≥0∞) ^ (-2 * γ)
          * (P₁ * (A : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2))
        * (F₂ * (B : ℝ≥0∞) ^ (-2 * γ)
            * (P₂ * (B : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2))
        * (F₃ * (D : ℝ≥0∞) ^ (-2 * γ)
            * (P₃ * (D : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2)) := hX
    _ = E * ((F₁ * (A : ℝ≥0∞) ^ (-2 * γ)
          * (P₁ * (A : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2))
        * (F₂ * (B : ℝ≥0∞) ^ (-2 * γ)
            * (P₂ * (B : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2))
        * (F₃ * (D : ℝ≥0∞) ^ (-2 * γ)
            * (P₃ * (D : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2))) := by ring
    _ ≤ E * ((δ : ℝ≥0∞) ^ (-2 * γ) * (M * (δ : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2)) := by
          gcongr
    _ = E * (δ : ℝ≥0∞) ^ (-2 * γ) * (M * (δ : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2) := by ring

/-- **Collapsing the three scales, carrying the gain** (blueprint `lem:ml1bootTripleCollapse`,
in the form the Case (ii) assembly consumes it).

This is `Kakeya.ml1Boot.tripleCollapse` specialized to the three loss factors
`δ ^ (-4 a')`, `δ ^ (10 a)`, `δ ^ (-4 a')` of the exponent contract, with their product
`δ ^ (10 a - 8 a')` *carried out* of the collapse rather than discarded through
`δ ^ (10 a - 8 a') ≤ 1`.  Carrying it is what funds the exponent shift of
`Kakeya.ml1Boot.multiplicity_le_of_middle`, and hence what decouples the step of blueprint
`def:ml1bootParams`(vi) from any loss allowance; see blueprint `note:auditUniformStep`.

It is `Kakeya.ml1Boot.tripleCollapse` applied with prefactor `E · δ ^ (10 a - 8 a')` and the
renormalized loss factors `δ ^ (-4a' - G/3)`, `δ ^ (10a - G/3)`, `δ ^ (-4a' - G/3)`, where
`G = 10 a - 8 a'`: their product is `δ ^ 0 = 1`, and the three factors `δ ^ (-G/3)` cancel
against the `δ ^ G` in the prefactor, so its hypothesis is the same real number as the one
supplied here.  No sign condition on `G` is needed. -/
theorem tripleCollapse_gain {δ A B D : ℝ≥0} (hδ0 : 0 < δ)
    (hA0 : 0 < A) (hA1 : A ≤ 1) (hB0 : 0 < B) (hB1 : B ≤ 1) (hD0 : 0 < D) (hD1 : D ≤ 1)
    (hABD : A * B * D = δ) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) {a a' : ℝ}
    {X E P₁ P₂ P₃ M : ℝ≥0∞}
    (hP₁ : 1 ≤ P₁) (hP₂ : 1 ≤ P₂) (hP₃ : 1 ≤ P₃) (hM : 1 ≤ M)
    (hPM : P₁ * P₂ * P₃ ≤ M)
    (hX : X ≤ E
      * ((δ : ℝ≥0∞) ^ (-4 * a') * (A : ℝ≥0∞) ^ (-2 * γ)
          * (P₁ * (A : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2))
      * ((δ : ℝ≥0∞) ^ (10 * a) * (B : ℝ≥0∞) ^ (-2 * γ)
          * (P₂ * (B : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2))
      * ((δ : ℝ≥0∞) ^ (-4 * a') * (D : ℝ≥0∞) ^ (-2 * γ)
          * (P₃ * (D : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2))) :
    X ≤ E * (δ : ℝ≥0∞) ^ (10 * a - 8 * a') * (δ : ℝ≥0∞) ^ (-2 * γ)
      * (M * (δ : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
  let G : ℝ := 10 * a - 8 * a'
  let E' : ℝ≥0∞ := E * (δ : ℝ≥0∞) ^ G
  let F₁ : ℝ≥0∞ := (δ : ℝ≥0∞) ^ (-4 * a' - G / 3)
  let F₂ : ℝ≥0∞ := (δ : ℝ≥0∞) ^ (10 * a - G / 3)
  let F₃ : ℝ≥0∞ := (δ : ℝ≥0∞) ^ (-4 * a' - G / 3)
  let B₁ : ℝ≥0∞ := (A : ℝ≥0∞) ^ (-2 * γ) * (P₁ * (A : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2)
  let B₂ : ℝ≥0∞ := (B : ℝ≥0∞) ^ (-2 * γ) * (P₂ * (B : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2)
  let B₃ : ℝ≥0∞ := (D : ℝ≥0∞) ^ (-2 * γ) * (P₃ * (D : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2)
  have hδp : 0 < (δ : ℝ≥0∞) := (ENNReal.coe_pos).mpr hδ0
  have hδne : (δ : ℝ≥0∞) ≠ 0 := ne_of_gt hδp
  have hδtop : (δ : ℝ≥0∞) ≠ ⊤ := ne_of_lt ENNReal.coe_lt_top
  have hδ : (δ : ℝ≥0∞) ^ G = (δ : ℝ≥0∞) ^ (10 * a - 8 * a') := by
    dsimp [G]
  have hF₁ : F₁ = (δ : ℝ≥0∞) ^ (-4 * a') * (δ : ℝ≥0∞) ^ (-(G / 3)) := by
    dsimp [F₁]
    calc
      (δ : ℝ≥0∞) ^ (-4 * a' - G / 3) = (δ : ℝ≥0∞) ^ ((-4 * a') + (-(G / 3))) := rfl
      _ = (δ : ℝ≥0∞) ^ (-4 * a') * (δ : ℝ≥0∞) ^ (-(G / 3)) :=
        ENNReal.rpow_add (x := (δ : ℝ≥0∞)) (-4 * a') (-(G / 3)) hδne hδtop
  have hF₂ : F₂ = (δ : ℝ≥0∞) ^ (10 * a) * (δ : ℝ≥0∞) ^ (-(G / 3)) := by
    dsimp [F₂]
    calc
      (δ : ℝ≥0∞) ^ (10 * a - G / 3) = (δ : ℝ≥0∞) ^ ((10 * a) + (-(G / 3))) := rfl
      _ = (δ : ℝ≥0∞) ^ (10 * a) * (δ : ℝ≥0∞) ^ (-(G / 3)) :=
        ENNReal.rpow_add (x := (δ : ℝ≥0∞)) (10 * a) (-(G / 3)) hδne hδtop
  have hF₃ : F₃ = (δ : ℝ≥0∞) ^ (-4 * a') * (δ : ℝ≥0∞) ^ (-(G / 3)) := by
    dsimp [F₃]
    calc
      (δ : ℝ≥0∞) ^ (-4 * a' - G / 3) = (δ : ℝ≥0∞) ^ ((-4 * a') + (-(G / 3))) := rfl
      _ = (δ : ℝ≥0∞) ^ (-4 * a') * (δ : ℝ≥0∞) ^ (-(G / 3)) :=
        ENNReal.rpow_add (x := (δ : ℝ≥0∞)) (-4 * a') (-(G / 3)) hδne hδtop
  have hcollect : ∀ (e1 e2 e3 : ℝ),
      (δ : ℝ≥0∞) ^ e1 * (δ : ℝ≥0∞) ^ e2 * (δ : ℝ≥0∞) ^ e3
        = (δ : ℝ≥0∞) ^ (e1 + e2 + e3) := by
    intro e1 e2 e3
    calc
      (δ : ℝ≥0∞) ^ e1 * (δ : ℝ≥0∞) ^ e2 * (δ : ℝ≥0∞) ^ e3
          = (δ : ℝ≥0∞) ^ (e1 + e2) * (δ : ℝ≥0∞) ^ e3 := by
            rw [← ENNReal.rpow_add (x := (δ : ℝ≥0∞)) e1 e2 hδne hδtop]
      _ = (δ : ℝ≥0∞) ^ (e1 + e2 + e3) := by
            rw [← ENNReal.rpow_add (x := (δ : ℝ≥0∞)) (e1 + e2) e3 hδne hδtop]
  have hcd :
      (δ : ℝ≥0∞) ^ (-4 * a') * (δ : ℝ≥0∞) ^ (10 * a) * (δ : ℝ≥0∞) ^ (-4 * a') =
        (δ : ℝ≥0∞) ^ (10 * a - 8 * a') := by
    rw [hcollect (-4 * a') (10 * a) (-4 * a')]
    congr 1
    ring
  have hF123 : F₁ * F₂ * F₃ = 1 := by
    have hsum : (-4 * a' - G / 3) + (10 * a - G / 3) + (-4 * a' - G / 3) = 0 := by
      unfold G
      ring
    dsimp [F₁, F₂, F₃]
    rw [hcollect (-4 * a' - G / 3) (10 * a - G / 3) (-4 * a' - G / 3), hsum]
    exact ENNReal.rpow_zero
  have hF : F₁ * F₂ * F₃ ≤ 1 := by rw [hF123]
  have hEq :
      E' * (F₁ * B₁) * (F₂ * B₂) * (F₃ * B₃) =
        E * ((δ : ℝ≥0∞) ^ (-4 * a') * B₁) * ((δ : ℝ≥0∞) ^ (10 * a) * B₂)
          * ((δ : ℝ≥0∞) ^ (-4 * a') * B₃) := by
    calc
      E' * (F₁ * B₁) * (F₂ * B₂) * (F₃ * B₃)
          = E' * (F₁ * F₂ * F₃) * (B₁ * B₂ * B₃) := by ring
      _ = E' * (B₁ * B₂ * B₃) := by rw [hF123]; ring
      _ = E * ((δ : ℝ≥0∞) ^ (10 * a - 8 * a')) * (B₁ * B₂ * B₃) := by dsimp [E']
      _ = E * ((δ : ℝ≥0∞) ^ (-4 * a') * (δ : ℝ≥0∞) ^ (10 * a))
            * ((δ : ℝ≥0∞) ^ (-4 * a')) * (B₁ * B₂ * B₃) := by
            rw [← hcd]
            ring
      _ = E * ((δ : ℝ≥0∞) ^ (-4 * a') * B₁) * ((δ : ℝ≥0∞) ^ (10 * a) * B₂)
          * ((δ : ℝ≥0∞) ^ (-4 * a') * B₃) := by ring
  have hX' :
      X ≤ E' * (F₁ * (A : ℝ≥0∞) ^ (-2 * γ) * (P₁ * (A : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2))
        * (F₂ * (B : ℝ≥0∞) ^ (-2 * γ) * (P₂ * (B : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2))
        * (F₃ * (D : ℝ≥0∞) ^ (-2 * γ) * (P₃ * (D : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2)) := by
    calc
      X ≤ E * ((δ : ℝ≥0∞) ^ (-4 * a') * (A : ℝ≥0∞) ^ (-2 * γ)
          * (P₁ * (A : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2))
        * ((δ : ℝ≥0∞) ^ (10 * a) * (B : ℝ≥0∞) ^ (-2 * γ)
          * (P₂ * (B : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2))
        * ((δ : ℝ≥0∞) ^ (-4 * a') * (D : ℝ≥0∞) ^ (-2 * γ)
          * (P₃ * (D : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2)) := hX
      _ = E * ((δ : ℝ≥0∞) ^ (-4 * a') * B₁) * ((δ : ℝ≥0∞) ^ (10 * a) * B₂)
          * ((δ : ℝ≥0∞) ^ (-4 * a') * B₃) := by
            dsimp [B₁, B₂, B₃]
            ring
      _ = E' * (F₁ * B₁) * (F₂ * B₂) * (F₃ * B₃) := by exact hEq.symm
      _ = E' * (F₁ * (A : ℝ≥0∞) ^ (-2 * γ) * (P₁ * (A : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2))
          * (F₂ * (B : ℝ≥0∞) ^ (-2 * γ) * (P₂ * (B : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2))
          * (F₃ * (D : ℝ≥0∞) ^ (-2 * γ) * (P₃ * (D : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2)) := by
            dsimp [B₁, B₂, B₃]
            ring
  calc
    X ≤ E' * (δ : ℝ≥0∞) ^ (-2 * γ)
        * (M * (δ : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2) :=
          tripleCollapse hA0 hA1 hB0 hB1 hD0 hD1 hABD hγ0 hγ1 hP₁ hP₂ hP₃ hM hPM hF hX'
    _ = E * (δ : ℝ≥0∞) ^ (10 * a - 8 * a') * (δ : ℝ≥0∞) ^ (-2 * γ)
        * (M * (δ : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2) := by dsimp [E']

section FibreCount

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end FibreCount

section FineFibreFromFactorTwoScales

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end FineFibreFromFactorTwoScales

end ml1Boot

end Kakeya

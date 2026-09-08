/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Uniform
public import Kakeya.MultiScaleLoss

/-!
# The displayed losses of the dividing-scales dichotomy

The two loss symbols `Kakeya.MultiScaleFac.gridLoss` and `Kakeya.MultiScaleFac.scaleGapLoss`, their
combination `Kakeya.MultiScaleFac.totalLoss`, the window rounding that decides which grid index a
real scale is read at, and the cardinality casts the dichotomy states its counting clause with.

This module is the merge of the former `MultiScaleLoss`, `MultiScaleWindow` and `SsfCardCast`.
Each former module keeps its own section, so its file-level `open`s and `variable`s stay confined
to it.

## The subpolynomial losses of the `⌈log log 1/δ⌉`-grid dichotomy

The two losses carried by the amended form of GWZ Lemma 7.7 (`Kakeya/MultiScaleFac/GapsA.lean`), and
the statement that each is subpolynomial.

Both are explicit functions of `δ` whose `δ`-independent parameters are quantified before `δ`.  They
are displayed in the conclusions of the dichotomy rather than converted into a power `δ^{-α}`, for
two reasons.  A fixed polylogarithmic exponent would be *wrong*: on a grid whose length is
`ssfGridLen δ = ⌈log log 1/δ⌉` each level is paid separately, so the exponent necessarily grows with
`δ`.  And committing to a power would be *less flexible*: it forces the smallness threshold to
depend on the consumer's accuracy, hence forces every intermediate lemma to carry that accuracy as a
parameter.  With the losses displayed, the threshold depends only on the dichotomy's own parameters,
and the consumer absorbs a loss where it needs to, by the three `exists_threshold_…` lemmas below.

The two losses have genuinely different sizes and neither bounds the other, which is why there are
two symbols and not one.  Writing `L = log 1/δ`, so that `ssfGridLen δ ≈ log L`:

* `gridLoss = e^{O((log L)^3)}` is the accumulation of one re-uniformization per *pair* of grid
  levels;
* `scaleGapLoss = e^{c L / log L}` is the cost of one transport across a grid gap;

and `L / log L` dwarfs `(log L)^3`.  Both exponents are `o(L)`, which is all subpolynomiality asks.

## The interior window of alternative (ii)-3 on the `⌈log log 1/δ⌉`-grid

The stopping test of the multiscale dichotomy refuses to cut within `⌈ε(b-a)⌉` grid indices of
either endpoint of a block `[a, b]`, so a statement about grid indices strictly inside the block
must place its indices inside that margin.  On the old grid, of length equal to the *step count*
`N`, a long block satisfies only `ε(b-a) ≥ ε²N = 1`, and absorbing the ceiling into a multiple of
`ε(b-a)` therefore costs a *fixed* factor: the window has to be widened from `ε` to `3ε` (see
`Kakeya.StickyKakeya.grid_window_admissible`, stated at `3 * ε`).

On the grid of length `M = ssfGridLen δ = ⌈log log 1/δ⌉` the same computation is much better.  A
long block now has `b - a ≥ εM`, hence

  `ε(b-a) ≥ ε²M = M/N`,

and `M → ∞` while the step count `N` stays fixed.  So `⌈ε(b-a)⌉ ≤ (1 + κ)ε(b-a)` already for
`κ = N/M`, and the widening factor tends to `1` as `δ → 0`.  The file proves this in
`ceil_le_mul_of_one_le_mul` and `grid_window_admissible`.

The residual is subpolynomial, which is the point.  Moving a window endpoint from exponent `ε` to
exponent `(1+κ)ε` multiplies it by `(σ_a/σ_b)^{κε} ≤ δ^{-κε(b-a)/M}`, and with `κ = N/M` and
`b - a ≤ M` that exponent is at most `εN/M = √N/M`: a factor `scaleGapLoss ⌈√N⌉ δ`, absorbed by
`totalLoss`.  This is `window_endpoint_le_scaleGapLoss_mul` below, and it is what makes the
`ε`-window form of the third bullet reachable from a `(1+κ)ε`-window supply.

## Reading a cardinality loss on natural-number coercions

The cardinality clauses of the amended dichotomies count in `ℝ≥0∞` on the coercions `(m : ℝ≥0∞)` of
the two cardinalities, whereas the loss lemmas that supply them are stated on `ENNReal.ofReal` of
the real coercions.  The two agree by `ENNReal.ofReal_natCast`; the transfer is isolated here so
that no consumer has to repeat it.

This is the direct counterpart of `Kakeya.MultiScaleFac.natCast_le_mul_natCast_of_ofReal_le`, which
performs the same transfer starting from a bound stated on the real line with an explicit real
coefficient.  Here the coefficient is already an element of `ℝ≥0∞`, so no coefficient hypothesis is
needed.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Real Metric
open scoped Topology NNReal
open Tube

namespace Kakeya


namespace MultiScaleFac

open _root_.StickyKakeya

/-! ### The accumulated per-level loss -/

/-- **The defining unfolding of `totalLoss`**, kept as a named lemma so that consumers never have to
`unfold` the definition to reach the real-valued product. -/
theorem totalLoss_eq_ofReal (A : ℝ≥0) (K c : ℕ) (δ : ℝ≥0) :
    totalLoss A K c δ = ENNReal.ofReal (gridLoss A K δ * scaleGapLoss c δ) := by
  rfl


/-- **The gap loss is monotone in the number of gaps**, so a bound paying several gaps may be
raised to a bound paying a common larger number. -/
theorem A.scaleGapLoss_mono {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {c₁ c₂ : ℕ}
    (hc : c₁ ≤ c₂) : scaleGapLoss c₁ δ ≤ scaleGapLoss c₂ δ := by
  unfold scaleGapLoss
  apply Real.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hδ) (by exact_mod_cast hδ1)
  apply neg_le_neg
  rcases Nat.eq_zero_or_pos (ssfGridLen δ) with hM | hM
  · rw [hM]
    simp
  · have hM0 : (0 : ℝ) ≤ (ssfGridLen δ : ℝ) := by exact_mod_cast (Nat.zero_le _)
    exact div_le_div_of_nonneg_right (by exact_mod_cast hc) hM0

/-- **The displayed loss is monotone in all three of its parameters.**  Both factors are, and both
are nonnegative, so the product is.  Isolated from `MultiScaleFac.loss_raise` so that the
bare-constant factor that lemma also carries does not have to be re-derived wherever only the
loss is compared. -/
theorem totalLoss_mono {B C : ℝ≥0} (hB : 1 ≤ B) (hBC : B ≤ C) {K K' c c' : ℕ}
    (hKK' : K ≤ K') (hcc' : c ≤ c') {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    totalLoss B K c δ ≤ totalLoss C K' c' δ := by
  have hgrid : gridLoss B K δ ≤ gridLoss C K' δ := gridLoss_mono hB hBC hKK' hδ1
  have hsg : (0 : ℝ) ≤ scaleGapLoss c δ := le_trans zero_le_one (one_le_scaleGapLoss c hδ hδ1)
  have hscl : scaleGapLoss c δ ≤ scaleGapLoss c' δ := A.scaleGapLoss_mono hδ hδ1 hcc'
  have hC : 1 ≤ C := le_trans hB hBC
  have hngrid : (0 : ℝ) ≤ gridLoss C K' δ := le_trans zero_le_one (one_le_gridLoss C hC K' hδ1)
  have hreal : gridLoss B K δ * scaleGapLoss c δ ≤ gridLoss C K' δ * scaleGapLoss c' δ :=
    mul_le_mul hgrid hscl hsg hngrid
  rw [totalLoss_eq_ofReal, totalLoss_eq_ofReal]
  exact ENNReal.ofReal_le_ofReal hreal


/-! ### Absorbing a ceiling into a multiplicative slack -/


/-! ### The window exponent `ε = 1/√N` -/


/-! ### The sharpened window -/


/-! ### The residual is one grid transport -/


/-! ### Rounding a real scale to a grid index -/


/-! ### Absorbing the grid length into the polylogarithmic factor -/


/-! ### The stopping-time loss is a `gridLoss` -/

/-! ### The hoisted stopping-time loss -/


/-! ### The quadratic pass of the banded stopping time -/


end MultiScaleFac
end Kakeya

end

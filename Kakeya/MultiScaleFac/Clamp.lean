/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Frostman
public import Kakeya.MultiScaleFac.Loss
public import Kakeya.MultiScaleFac.Stopping
public import Kakeya.MultiScaleFac.StoppingKT
public import Kakeya.FibreCommon
public import Kakeya.Thickness.ConvexSpaceBody
public import Kakeya.ChainUniform
public import Kakeya.Sticky
public import Kakeya.Uniform
public import Mathlib.Tactic.Linarith.NNRealPreprocessor
public import Kakeya.GridScale
public import Kakeya.Density
public import Kakeya.Tube.Basic
public import Kakeya.MultiScaleFac.Bridge
public import Kakeya.MultiScaleLoss
public import Kakeya.MultiScaleFac.UniformBridgeKT

/-!
# From the narrow window to GWZ's window, half (A)

The third bullet on the narrow window of exponent `e'`, and the clamp that widens it back to GWZ's
`ε`-window, together with the constants, the window arithmetic and the good node the two steps ask
for.

This module is the merge of the former `Bullet3GoodNodeA`, `Bullet3CoeffA`, `Bullet3ClampA`,
`Bullet3ConstMergeA`, `Bullet3NarrowSpread`, `Bullet3NarrowA`, `Bullet3AltAdapter`,
`Bullet3ClampInputs`, `Bullet3WindowInstA`.  Each keeps its own section, so its file-level
`open`s and `variable`s stay confined to it. -/

/-!
# Entering the half-(A) third bullet: a good node and the two standing smallness facts

The narrow-window witness package of the half-(A) third bullet,
`Kakeya.StickyKakeya.ssfA_narrow_witness_package`, is entered at a *prescribed* good node
`j ∈ goodNodes 𝒰 b G`, whereas the hypotheses available at the entry point
`Kakeya.StickyKakeya.ssf_bulletThree_of_alternativeTwo` speak only of a majority set: `G ⊆ s` and
`s.card ≤ 2 * G.card`.  The gap is one existence step, supplied here by
`Kakeya.MultiScaleFac.A.exists_goodNode`: the counting lemma
`Kakeya.MultiScaleFac.card_parent_le_mul_card_goodNodes` bounds the whole level `indexSet b` by a
multiple of the good nodes, and the level is nonempty because `s` is, so the good nodes are nonempty
too.

The two remaining small facts are the ones the same entry point leaves implicit: the standing
smallness `δ ≤ 16^{-M}` together with `16 ≤ M` forces `δ < 1`, and `16 ≤ M` forces `0 < M`.  Both
are demanded verbatim by `Kakeya.StickyKakeya.ssfA_narrow_witness_package` and by the clamping step
of the same bullet.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Real Metric

universe u
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

variable {ι : Type u}
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-! ### A good node out of a majority set -/


/-! ### The two standing smallness facts -/


/-- **The grid length of the sharp dichotomy is positive.** -/
theorem A.ssfGridLen_pos {δ : ℝ≥0} (hM16 : 16 ≤ ssfGridLen δ) :
    0 < ssfGridLen δ := by
  omega

end MultiScaleFac

end Kakeya

end

/-!
# The transport level and the coefficient of a narrow window, half (A)

Two independent pieces of bookkeeping for the third bullet of half (A).

## The transport level

`Kakeya.MultiScaleFac.frostmanConstant_nodesIn_rescale_le_of_pairBand` compares the Frostman
constants of two concentric dilates of one level-`b` node, at radii `ρ` and `ρ'`, and it does so
*through a coarse level* `k`: the ancestor split, the band and the packing count all live at that
level.  The hypotheses it puts on `k` are `2δ ≤ σ_k` (the level is not finer than the tube radius),
`4 σ_k ≤ ρ` (the level is coarse enough that the `4ρ`-dilate contains the level-`k` ancestor) and
`σ_k ≤ 4 ρ'` (the level is fine enough that the packing count is bounded).

`Kakeya.MultiScaleFac.A.exists_transport_level` produces such a level from the window bounds
alone, and produces it *symmetrically* in the two radii: the conclusion asserts each of the three
demands for `ρ` and for `ρ'` separately, so the same witness serves whichever of the two radii is
the smaller.  Both ends of the window need it, and neither end knows in advance which of its two
radii is the smaller one, so an asymmetric form would have to be applied twice.

The level is the sharp rounding index of `Kakeya.MultiScaleFac.A.exists_round_index_sharp` taken
at the *smaller* radius; sharpness is retained in the last clause, which is what keeps the packing
count `(4ρ/σ_k)^{2n}` inside a single `Kakeya.MultiScaleFac.scaleGapLoss`.

## The coefficient of one narrow-window scale

The conclusion at a single scale of a narrow window carries a product of five unrelated factors:
the number `K_n` of coarse neighbours covering a dilated node, the band constant `C_b`, the two
node-density bounds `d_m` and `D_m` of
`Kakeya.MultiScaleFac.A.exists_density_pair`, two volume constants of the grid rounding, the
packing factor `Λ` with its own gap loss, and the stopping time's `δ^{-27/⌈\log\log 1/δ⌉}`.

Only the *ratio* `D_m / d_m` survives: it is bounded by the absolute
`Kakeya.MultiScaleFac.nodeDensityRatioConst`, and
`Kakeya.MultiScaleFac.A.density_ratio_le` performs that cancellation.  What is left is a product
of absolute constants against two gap losses, which
`Kakeya.MultiScaleFac.A.narrow_coefficient_le` absorbs into the single displayed
`Kakeya.MultiScaleFac.totalLoss` through `Kakeya.MultiScaleFac.A.const_scaleGapLoss_le`.  No
factor here is a power of `δ` beyond the two gap losses, which is exactly why the whole coefficient
is subpolynomial.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Real Metric
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

variable {ι : Type u}
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-! ### The transport level -/


/-! ### The coefficient of one narrow-window scale -/


end MultiScaleFac

end Kakeya

end

/-!
# From the narrow window to the `ε`-window, half (A)

The third bullet of alternative (ii) of GWZ Lemma 7.7(A) is stated on the `ε`-window, while the
terminal alternative supplies its witness only on the narrower window of the larger exponent `e'`.
This file is the abstract step that closes that gap: the statement of the bullet *on the narrow
window* is taken as an explicit hypothesis, and the statement *on the `ε`-window* is produced from
it.  Nothing here knows how the narrow-window statement is obtained.

The mechanism is `Kakeya.MultiScaleFac.A.exists_window_clamp`: a scale `ρ` of the `ε`-window is
clamped to a scale `ρ'` of the narrow window that differs from it by at most one
`Kakeya.MultiScaleFac.scaleGapLoss` in either direction.  Whether the clamp moved `ρ` up or down is
decided by `le_total`, and the two cases are the two ends of the window:

* `ρ ≤ ρ'`: the bound descends from the coarser `ρ'` by the container transport, which is
  `Kakeya.MultiScaleFac.A.bulletThree_fineEnd_of_transport`;
* `ρ' ≤ ρ`: the bound ascends from the finer `ρ'` by the ancestor split, which is
  `Kakeya.MultiScaleFac.A.bulletThree_coarseEnd_of_ancestor`.

Both directions pay a transport coefficient built from absolute constants and from powers of the
two gap losses; no factor is a power of `δ` beyond those losses, so the whole coefficient is
absorbed into the displayed `Kakeya.MultiScaleFac.totalLoss`.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Real Metric

universe u
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

variable {ι : Type u}
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-! ### The two endpoints of the two windows -/


/-! ### The two ratios that the clamp creates -/


/-! ### Merging the transport coefficient into the displayed loss -/


/-! ### The two ends of the clamp -/


/-! ### The narrow window implies the `ε`-window -/


end MultiScaleFac

end Kakeya

end

/-!
# Merging the constants of the half-(A) third bullet

Every step of the half-(A) third bullet returns its own triple of parameters: a multiplicative
constant, a polylogarithmic degree, and a grid-gap budget.  The statement they must all feed,
`Kakeya.MultiScaleFac.dividingScalesFrostman`, displays a *single* group
`∃ (C δ₀ : NNReal) (K c : ℕ)`, so at assembly time the triples have to be replaced by one common
triple that dominates them all.

This file provides that replacement abstractly, with no numerical input:

* `Kakeya.MultiScaleFac.A.exists_common_const_pair` produces one constant dominating two, which
  is the shape in which the base of the window clamp is obtained.
* `Kakeya.MultiScaleFac.totalLoss_mono` is what makes such a replacement legitimate: the
  displayed loss only grows when its three parameters grow.  Without it, merging the parameters
  would not preserve any of the five bounds in which `Kakeya.MultiScaleFac.totalLoss` occurs.
* `Kakeya.MultiScaleFac.A.exists_clamp_bulletThree_window_const` produces a triple satisfying at
  once the three side conditions `hC`, `hK`, `hc` of
  `Kakeya.MultiScaleFac.A.clamp_bulletThree_window`.  Those three are of different shapes -- one
  multiplicative, two additive, and the last with a truncated subtraction in the ambient dimension
  -- so discharging them together is worth a lemma.

Nothing here depends on the value of any constant of the development: the base `B` dominating the
two absolute constants of the window clamp is an input, obtained from
`Kakeya.MultiScaleFac.A.exists_common_const_pair`.
-/

@[expose] public section

open scoped NNReal
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

variable {ι : Type u}
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-! ### Merging finitely many parameters -/


/-! ### The side conditions of the window clamp -/


end MultiScaleFac

end Kakeya

end

/-!
# Spreading one witness across a narrow window scale, half (A)

The terminal alternative of the half-(A) dichotomy speaks at a *single* level-`c` node, at the
reading scale `ρ_c` produced by the sharp window rounding.  This file carries that single lower
bound to the locked form of the third bullet at one scale `ρ` of the narrow window: a lower bound
at *every* level-`b` node, against the concentric `ρ`-rescale of that node, with a coefficient that
is one displayed `Kakeya.MultiScaleFac.totalLoss`.

Three steps, in this order.

* **Spreading.**  `Kakeya.MultiScaleFac.A.hgrid_of_witness` removes the majority set and moves the
  witness onto every level-`c` node, through the two-sided band.  The band is read off the
  `Kakeya.MultiScaleFac.PairBandOn` predicate carried by the banded stopping time at the pair of
  levels `(c, b)`; the transfer is free, the cover system of
  `Kakeya.MultiScaleFac.GridUniform.toUniformTubeSet` being definitionally the one of the
  grid-uniform system.  The price is the four coefficients `K_n`, `d_m`, `C_b = 2`, `D_m`.

* **Descent.**  `Kakeya.MultiScaleFac.le_frostmanConstant_nodesIn_rescale_of_grid_dilate` descends
  from the reading level `c` to the real scale `ρ`, which is admissible because the sharp rounding
  guarantees `32 ρ_c ≤ ρ`.  Its packing count is bounded by
  `Kakeya.MultiScaleFac.A.narrowLambdaConst` times a single
  `Kakeya.MultiScaleFac.scaleGapLoss (2n) δ`, again by sharpness, which is the content of
  `Kakeya.MultiScaleFac.A.lambda_le_scaleGapLoss`.  The price is the two volume constants of the
  rounding and that packing factor.

* **Accounting.**  `Kakeya.MultiScaleFac.A.narrow_coefficient_le` cancels the two node densities
  against their absolute ratio `R` and absorbs everything that is left -- absolute constants
  against the two gap losses, the packing count's `2n` and the witness budget `c₂` -- into the
  single displayed loss, as soon as `2n + c₂ ≤ c`.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Real Metric

universe u
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

variable {ι : Type u}
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-! ### The packing factor of the sharply rounded descent -/


/-! ### The band, in the shape the spreading lemma consumes -/


/-! ### The descent from the reading level to the window scale -/


/-! ### The accounting of the whole coefficient -/


/-! ### The third bullet at one scale of the narrow window -/

end MultiScaleFac

end Kakeya

end

/-!
# The witness half of the third bullet of half (A), sharpened

`Kakeya.MultiScaleFac.A.narrow_witness_package` is the witness half of the third bullet of
half (A).  It is the package of `Kakeya.StickyKakeya.ssfA_narrow_witness_package` with the two scale
clauses of the sharp rounding kept in the conclusion.  The package itself exports only
`2 δ ≤ σ_c`, but the spreading half also consumes `32 σ_c ≤ ρ` and the sharpness `ρ ≤ 32 Λ₁ σ_c`
*at the same level `c`*, and the level is existentially bound, so those two clauses cannot be
recovered from the package after the fact.  They are not extra hypotheses of the narrow window
either: they come from the very call to `Kakeya.MultiScaleFac.A.exists_round_index_sharp` that
produces the level, so the sharpened package simply keeps them.

The sharpened witness is run into `Kakeya.StickyKakeya.ssfA_narrow_spread_package` on the banded
route, in `Kakeya.MultiScaleFac.A.bandedA_narrow_window`.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Real Metric

universe u
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

variable {ι : Type u}
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-! ### The witness package with the two scale clauses kept -/


end MultiScaleFac

end Kakeya

end

/-!
# Adapting the terminal alternative (ii) to the narrow-window witness package

`Kakeya.StickyKakeya.ssf_bulletThree_of_alternativeTwo` carries the terminal alternative (ii) in its
hypothesis list, in the shape the stopping time delivers it: one universally quantified real scale
`ρ` of a window, then a leaf `i₀` of a majority set `F ⊆ s`.  The entry point of the new chain,
`Kakeya.StickyKakeya.ssfA_narrow_witness_package`, asks for the same supply in the opposite
quantifier order — leaf first, scale second — on a set `G` that is the one indexing
`Kakeya.MultiScaleFac.goodNodes`, and with the whole coefficient collapsed into a single `D0`.

This file is the translation between the two, and nothing more.  It is deliberately confined to the
*supply* half of the correspondence: the new chain also demands a
`Kakeya.MultiScaleFac.GridUniform` and a second window exponent, neither of which the old hypothesis
list mentions, and those are hypotheses of the composed statement below rather than things derived
here.

Three points of the dictionary are worth recording.

* The window endpoints need no translation.  Both sides write the window of exponent `e` as
  `σ_b (σ_a/σ_b)^e ≤ r ≤ σ_a (σ_b/σ_a)^e`, character for character, so the identification is the
  substitution `e := (1 + 2N/M) ε` and no endpoint-equivalence lemma is needed.  Since
  `gridScale δ M k = δ^{k/M}` and `δ < 1`, one has `σ_a/σ_b > 1` for `a < b`, and the window of
  exponent `e` is `[σ_b R^e, σ_b R^{1-e}]` with `R = σ_a/σ_b`; it *shrinks* as `e` grows.

* The exponent `ζ'` of the alternative is the `zeta` of the package.  The package wants
  `0 ≤ zeta` and `zeta ≤ 1`, which the old hypothesis list gives only indirectly, through
  `0 ≤ ζ`, `ζ ≤ ε ζ'`, `ζ' ≤ ε` and `ε ≤ 1/64`; that derivation is
  `Kakeya.MultiScaleFac.A.Alt.zeta_nonneg_of_mul_le` and
  `Kakeya.MultiScaleFac.A.Alt.zeta_le_one_of_le`.

* The majority set `F` of the old list and the set `G` indexing the good nodes of the package are
  the same set.  The old list's `F ⊆ s` and `s.card ≤ 2 * F.card` are exactly the hypotheses of
  `Kakeya.MultiScaleFac.card_parent_le_mul_card_goodNodes`, which is what makes
  `goodNodes 𝒰 b F` a fixed proportion of the level; they are not needed to convert the supply
  itself, and so do not appear below.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Real Metric

universe u
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

variable {ι : Type u}
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-! ### The exponent conditions, from the old hypothesis list -/


/-! ### The supply, reordered -/


end MultiScaleFac

end Kakeya

end

/-!
# The inputs of the half-(A) window clamp

`Kakeya.MultiScaleFac.A.clamp_bulletThree_window` transports the third bullet from the wide
window of exponent `e'` to the narrow window of exponent `ε`.  Besides its terminal hypothesis
`hnarrow`, it asks for a window-arithmetic package (`hnwne`, `hstep`, `hwin1`) and for a
cover-and-band package read at a grid level (`hP`, `hbandLo`, `hbandHi`).  This file produces those
packages from the output of the banded stopping time
`Kakeya.MultiScaleFac.exists_maximal_cuts_banded_hoisted_selfBand` and from the long-block
condition.

The one point of adaptation is the arity of the band.  The stopping time carries
`Kakeya.MultiScaleFac.PairBandOn`, whose band `Φ : ℕ → ℕ → ENNReal` is indexed by a *pair* of grid
levels, while the clamp reads a band indexed by the coarse level alone.  Fixing the fine level `b`
resolves this: `Kakeya.MultiScaleFac.A.clampBandFun` is the unary band `k ↦ Φ k b`, and both
halves of `PairBandOn` specialise to it verbatim at `Cb = 2`.

The cover-and-band clauses are available only on part of the grid, and the clamp asks for them
exactly there.  `Kakeya.MultiScaleFac.PairBandOn` speaks at `k ≤ M`, while the coarse-neighbour
cover `Kakeya.MultiScaleFac.exists_coarseNeighbours` stops at `k < M`: the level `k = M` has
`gridScale δ M M = δ`, so the side condition `2δ ≤ σ_k` of the ancestor count fails there.  Above
the grid length nothing at all is known: no field of `Tube.GridCoverSystem`
constrains `indexSet k`, `assign k` or `tube k` for `k > M`, and the two-sided band admits no
padding there, since a band value of `0` breaks the upper bound and a band value of `⊤` breaks the
lower one.  The lemmas below are therefore stated on the ranges where they are true: `k ≤ M` for
the band, and `k ≤ b` together with `k < M` for the cover.  These are verbatim the binders of
`hbandLo`, `hbandHi` and `hP` in `Kakeya.MultiScaleFac.A.clamp_bulletThree_window`, so each
clause below can be handed to the clamp as it stands.  The transport level the clamp selects always
satisfies `2δ ≤ σ_k`, which already forces `k < M`, so nothing is lost by the restriction.

The handover itself is performed on the banded route, in
`Kakeya.MultiScaleFac.bulletThree_of_alternativeTwo_banded`.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Real Metric

universe u
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

variable {ι : Type u} [DecidableEq ι]
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-! ### The grid levels at which an ancestor count is available -/


/-! ### The window arithmetic -/


/-! ### The band, read at a fixed fine level -/


end MultiScaleFac

end Kakeya

end

/-!
# The window arithmetic at the instance of the amended dichotomy, half (A)

`Kakeya.MultiScaleFac.A.clamp_bulletThree_window` and
`Kakeya.StickyKakeya.ssfA_narrow_witness_package` are stated for abstract window exponents.  This
file discharges their arithmetic hypotheses at the exponents the amended dichotomy
`Kakeya.MultiScaleFac.dividingScalesFrostman` actually runs at:

* `ε = 1/√N`, the window exponent the statement pins;
* `κ = N/M` with `M = ssfGridLen δ`, the ratio of the stopping-time budget to the grid length;
* `e = (1 + 2κ)ε`, the exponent at which the terminal alternative supplies its witness;
* `e' = e + 6/(b - a)`, the exponent of the *narrow* window on which
  `Kakeya.StickyKakeya.ssfA_narrow_witness_package` reads that witness.

Windows narrow as the exponent grows, so the three exponents sit in the order `ε ≤ e ≤ e'` and the
transport runs from the narrow end back to the wide one: alternative (ii) supplies the bullet at
`e`, the witness package converts it to the narrow window at `e'`, and
`Kakeya.MultiScaleFac.A.clamp_bulletThree_window` pushes that narrow conclusion back out to the
`ε`-window.

Two of the hypotheses the clamp asks for are already available in the development and are not
restated here: `hwin1` is `Kakeya.MultiScaleFac.A.clamp_window_upper_le_one` and `hεba` is
`Kakeya.MultiScaleFac.A.three_le_eps_mul_block`.  The `ℝ`-to-`ℕ` conversion of the gap budget is
`Kakeya.MultiScaleFac.A.le_cast_ceil`.

The one parameter bound that is not free is the block length: every statement below reads it
through `3 ≤ ε (b - a)`, which on a long block with `3N ≤ M` and `ε = 1/√N` is
`Kakeya.MultiScaleFac.A.three_le_eps_mul_block`, and which at `ε ≤ 1/64` forces `b - a ≥ 192`.
That is what makes the residual term `6/(b - a)` of `e'` small enough for `2e' ≤ 1`.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Real Metric
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya
open scoped NNReal

variable {ι : Type u} [DecidableEq ι]
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-! ### The block length -/


/-! ### The three exponents are ordered -/


/-! ### The gap budget, read against a ceiling -/


/-! ### The narrow window is nonempty -/


/-! ### The whole package -/


end MultiScaleFac

end Kakeya

end

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.FibreCommon
public import Kakeya.Thickness.ConvexSpaceBody
public import Kakeya.ChainUniform
public import Kakeya.Sticky
public import Kakeya.Uniform
public import Mathlib.Tactic.Linarith.NNRealPreprocessor
public import Kakeya.Frostman
public import Kakeya.GridScale
public import Kakeya.MultiScaleFac.Loss
public import Kakeya.MultiScaleFac.Clump
public import Kakeya.MultiScaleFac.FibreDensity
public import Kakeya.MultiScaleFac.Stopping
public import Kakeya.Uniform.ParentBodyDensity
public import Kakeya.Tube.ChainScale
public import Kakeya.Tube.Nets
public import Kakeya.KatzTao
public import Kakeya.Mathlib.Finset
public import Kakeya.Density
public import Kakeya.Tube.Basic
public import Kakeya.Tube.CardEssentiallyDistinct
public import Kakeya.MultiScaleFac.Bridge

/-!
# The gaps between the stopping time and the amended dichotomy, half (A)

The grid-side hypotheses at the grid length `ssfGridLen δ`, and the gap lemmas that turn what the
stopping time hands out into the clauses the amended half-(A) dichotomy displays.  Everything above
this file is reusable geometry; everything in it is dichotomy-specific plumbing.

Sliced out of the former `DividingScalesA`.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Real Metric
open scoped Topology NNReal

universe u
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-! ### The grid-side hypotheses at the grid length `ssfGridLen δ`

The split stopping-time layer constrains its *grid* length only from below — `16 ≤ N_grid`,
`1 ≤ ε ^ 2 * N_grid`, `N_step ≤ N_grid` — together with the separation `δ ≤ 16 ^ (-N_grid)` that
`Tube.exists_uniformTubeSet_subfamily` also demands.  Since `ssfGridLen δ` diverges
as `δ → 0`, all four hold at `N_grid := ssfGridLen δ` below a threshold depending only on the step
bound and on `ε`.  That is the entire arithmetic content of moving the hierarchy onto GWZ's own
grid, and it is what decouples the grid length from the step bound.

The divergence of `⌈log log 1/δ⌉` is also recorded, in a real-valued form, as
`Kakeya.StickyKakeya.exists_threshold_le_ssfGridLen` in `Kakeya/StickyKakeya/CrossScale.lean`; that
module is not imported here. -/

section SsfGridHypotheses


end SsfGridHypotheses

/-! ### The four remaining gaps of the amended dichotomy

The proof of `Kakeya.MultiScaleFac.dividingScalesFrostman` below runs the hoisted stopping time
`Kakeya.MultiScaleFac.exists_maximal_cuts_state_instance_hoisted_blocks_quad` at the grid length
`ssfGridLen δ`,
converts its two losses into `Kakeya.MultiScaleFac.totalLoss`, builds the returned bundle out of the
returned `Kakeya.MultiScaleFac.GridUniform`, and splits on whether some adjacent pair of the cut set
is long.  What it does not do is the four analytic steps below, each of which is isolated here as a
named lemma whose hypotheses are, verbatim, the data the stopping time hands out.

Each of the four returns its own constant `B` and polylogarithmic degree `K`; the dichotomy raises
all four to a common pair by `ssf_loss_raise`, which is why none of them may be stated with the
final constant already substituted.

*Alternative (i) uses the explicit-power form.*  The consumer
`Kakeya.MultiScaleFac.isFrostmanAtEveryScale_of_cuts_blockPow_uniform` charges the terminal block
constant as a bounded power.  This is necessary because the hoisted stopping time bounds that
constant by
`(C₁^{M+1} (1 - \log δ)^{K₁(M+1)})^L` with `M = ssfGridLen δ` and `L ≤ N + 1`.  The latter is
`\exp(Θ((\log\log 1/δ)^2))`, which exceeds every fixed power of `1 - \log δ` as `δ → 0`.
Charging the block constant explicitly as `C_b^p` gives a conclusion quadratic in `M`, hence a
`gridLoss`, and is wide enough to carry. -/

section SsfGaps


/-! ### The lower bound of alternative (ii), moved to the nodes and to the `ε` window

`Kakeya.MultiScaleFac.alternative_two_of_terminal_block_sharp` delivers the lower bound in the
leaf-anchored form: on the window at exponent `(1+2κ)ε` with `κ = N/⌈log log 1/δ⌉`, at the factor
`δ^{-27/⌈log log 1/δ⌉}`, anchored at the doubled leaf `T_{i₀}^{(2ρ)}`, and only at the leaves of a
majority set `F`.  The amended statement needs it on GWZ's `ε` window, at a `totalLoss`, anchored at
the concentric `ρ`-rescale of a level-`b` node, and at *every* level-`b` node.  Three moves:

* the window widens from `(1+2κ)ε` to `ε`; the residual is `2κε(b-a) ≤ 2εN = 2√N` grid steps, hence
  a `Kakeya.MultiScaleFac.scaleGapLoss` and not a fixed power of `δ`
  (`Kakeya.MultiScaleFac.window_endpoint_le_scaleGapLoss_mul`).  This is what makes GWZ's `ε` window
  reachable at all: on a grid of length `N` the window has to be `3ε` and the gap to `ε` is a fixed
  power of `δ`;
* the factor `δ^{-27/⌈log log 1/δ⌉}` is already `Kakeya.MultiScaleFac.scaleGapLoss 27 δ`, so it is
  absorbed into the displayed loss; the container is moved by
  `Kakeya.StickyKakeya.le_scaleGapLoss_mul_frostmanConstant_nodesIn`;
* the majority set disappears, by the ancestor split
  `Kakeya.StickyKakeya.exists_frostmanConstant_nodesIn_rescale_le`, whose universal upper bound `Ψ`
  at the coarse level is supplied here by the second bullet.

Comparability of node Frostman constants across a level — the band of
`Kakeya.StickyKakeya.exists_homogenized_subfamily` — is what the last move ultimately rests on, and
no such band is available on the family the stopping time returns.  Two sharper obstructions were
recorded while attempting a band-free, purely combinatorial route:

* the coarse upper bound is stated here at the concrete value `C₃ · totalLoss C₃ K₃ c δ ·
  (σ_a/σ_b)^ζ` that the second bullet actually produces, and not as a bound by an ambient `Ψ`.  An
  ambient `Ψ` is vacuous: universally quantified and absent from the conclusion, it is satisfied by
  `Ψ = ⊤` for every family, so only the uniformity of `𝒰` and the lower bound on the majority set
  `F` would carry content.  Those two alone do not suffice: let `s` be the disjoint union of a
  planar packing `A` of `δ`-tubes inside a `δ`-slab
  and a parallel packing `B`, placed apart.  Both have `σ^{-(n-1)}` tubes of every grid radius `σ`,
  so a single hierarchy with a single branching number covers the union, and `F := A` meets
  `s.card = 2 * F.card` and is concentrated at every scale of the window, so it satisfies the
  leaf-anchored lower bound.  At a level-`b` node `j` under `B` the level-`b` nodes inside
  `T_j^{(ρ)}` are a full packing, their Frostman constant is `O(1)`, and the left-hand side is
  `δ^{-(1-ε) ζ' (b-a)/M}`, a fixed power of `δ`, which no `Kakeya.MultiScaleFac.totalLoss` absorbs;
* the goal at a node is equivalent to a *counting* deficiency,
  `|𝕋_b[T_j^{(ρ)}]| ≤ loss · (ρ/σ_b)^{n-1-ζ'}`.  One direction is the volume-sharpened form of
  `Kakeya.MultiScaleFac.card_mul_frostmanConstant_nodesIn_le` read at `K₁ = T_j`, with
  `Kakeya.StickyKakeya.one_le_frostmanConstant_tube` supplying the sub-body; and counts *are*
  comparable across a level, by the private
  `Kakeya.MultiScaleFac.card_nodesUnder_le_mul_card_nodesUnder`, so no band is needed to carry a
  count from a leaf of `F` to an arbitrary node.  What is missing is the
  step producing the deficiency at the leaf: a lower bound on a Frostman constant bounds `Δ_max / Δ`
  from below, and `Δ_max` of a family of nodes is *not* bounded by the bounded-overlap field of
  `Tube.UniformTubeSet` — the planar family above has bounded overlap and
  `Δ_max ≈ ρ/σ_b`.  Recovering the count needs an upper bound for `Δ_max`, that is, a band again, or
  an a priori packing bound `|𝕋_b[T_a]| ≲ (σ_a/σ_b)^{n-1}` for the hierarchy, which bushes refute.

## How the bullet is now proved

The section `Bullet3Core` above reduces the bullet to a single statement about *one grid level*.
`Kakeya.StickyKakeya.le_frostmanConstant_nodesIn_rescale_of_grid` shows: if the lower bound holds at
**every** node of a grid level `c` with `4 ρ_c ≤ ρ`, then it holds at every level-`b` node against
the real container `T_j^{(ρ)}`, at the price of one factor `Λ`.  That factor is the ratio of node
counts, which the second obstruction above correctly identifies as the place where half (A) differs
from half (B); it is *not* a power of `δ`, by the ancestor split at an unrestricted radius
(`Kakeya.MultiScaleFac.card_nodesIn_le_mul_card_nodesUnder_ratio`, whose packing count displays
`4ρ/ρ_c` in place of the fixed `32` of the old restricted form).  For `c` the grid index just below
`ρ/4` the ratio is under four grid steps, so `Λ` is a `Kakeya.MultiScaleFac.scaleGapLoss` and
`Kakeya.MultiScaleFac.totalLoss` absorbs it.  The monotonicity of `Kakeya.maxDensity` that half (B)
uses at this step is thereby replaced, and no band is needed for it.

What is left is exactly the *universal-in-the-node* hypothesis of that lemma, at the level `c` of
`ρ`.  The stopping time delivers the lower bound at the leaves of the majority set `F`, hence — by
`Kakeya.MultiScaleFac.frostmanConstant_fibre_le_mul_frostmanConstant_nodesIn` — at the `8
ρ_c`-dilate of the *single* level-`c` node carrying a leaf of `F`, and the first obstruction above
shows that uniformity and `F` alone do not spread it to the other nodes.  Spreading it needs a
two-sided band on `ConvexSpaceBody.frostmanConstant (𝒰.nodesUnder b c p)` that is indexed by the
*pair* `(c, b)`, since neither `c` nor `b` is known before the stopping time terminates.

That band is now available.  `Kakeya.MultiScaleFac.exists_maximal_cuts_banded_hoisted_selfBand`
carries a `Kakeya.MultiScaleFac.PairBandOn` on the terminal family's *own* grid-uniform cover, not
merely on a superfamily, and the bullet is proved from it as
`Kakeya.MultiScaleFac.bulletThree_of_alternativeTwo_banded`.  That statement supersedes the one
this note used to introduce, and differs from it in exactly two ways: it takes the grid-uniform
system together with its band in place of a bare `Tube.UniformTubeSet`, and it
displays its loss at an enlarged gap budget `cB`.  The enlargement is forced by the last step of the
argument: the clamp from the narrow window of exponent `(1 + 2κ)ε + 6/(b - a)` back onto GWZ's `ε`
window crosses `⌈8√N⌉` grid steps, each costing one unit of budget.  `cB` still depends on `N` and
the ambient dimension alone, so the displayed loss remains subpolynomial, and
`Kakeya.MultiScaleFac.dividingScalesFrostman` states all four of its gap conclusions at that one
budget. -/

/-! ### Side conditions of the sharp alternative (ii) -/


/-- The `16`-separation of the grid forces `δ < 1` strictly, which the sharp dichotomy needs. -/
theorem delta_lt_one {δ : ℝ≥0} (_hδ : 0 < δ) (h16M : 16 ≤ ssfGridLen δ)
    (hδ16 : δ ≤ (16 : ℝ≥0) ^ (-(ssfGridLen δ : ℝ))) : (δ : ℝ) < 1 := by
  have hMpos : 0 < (ssfGridLen δ : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num) h16M)
  calc
    (δ : ℝ) ≤ (16 : ℝ) ^ (-(ssfGridLen δ : ℝ)) := by
      simpa [NNReal.coe_rpow] using (NNReal.coe_le_coe.mpr hδ16)
    _ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (x := (16 : ℝ)) (by norm_num) (by linarith)

end SsfGaps

end MultiScaleFac

end Kakeya

end

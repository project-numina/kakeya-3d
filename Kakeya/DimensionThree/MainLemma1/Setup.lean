/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.PartialEstimates
public import Kakeya.Sticky
public import Kakeya.DimensionThree.CardBound
public import Kakeya.DimensionThree.MainLemma1.FrostmanAtEveryScaleCase

/-!
# Main Lemma 1: the parameter package and the sticky case

This file sets up Section 8 of the adapted blueprint
(the Main Lemma 1 setup).  It contains

* the reduction to a strictly positive Katz–Tao exponent
  `β'(γ) = max β (γ / 2)`, split into its two
  `E`-free arithmetic clauses `Kakeya.ml1Boot.betaPrime_spec`,
  `Kakeya.ml1Boot.gap_spec` and the monotonicity clause
  `Kakeya.ml1Boot.katzTaoEstimate_betaPrime`;
* the parameter package
  `c_{8.1}(β, γ₀) = (η⋆, δ₀, N, ε, κ, (η_j), ε', η(·), c)`
  (`Kakeya.ml1Boot.params`, blueprint `def:ml1bootParams`) together with its two
  specification lemmas `Kakeya.ml1Boot.params_spec` and `Kakeya.ml1Boot.etaGamma_spec`;
* Case (i) of the sticky/non-sticky dichotomy
  (`Kakeya.ml1Boot.multiplicity_le_of_frostmanAtEveryScale`, blueprint
  `lem:ml1bootCaseSticky`).

The sharp count of essentially distinct `δ`-tubes in `B₁ ⊆ ℝ³` that Case (i) consumes
(`Kakeya.ml1Boot.card_le`, blueprint `lem:ml1bootCardBound`) has moved to its own module
`Kakeya.DimensionThree.CardBound`, which this file re-exports.

## The shape of the parameter package

Items (i) and (v) of blueprint Definition `def:ml1bootParams` are *outputs of other
theorems*: `(η⋆, δ₀)` comes from
`StickyKakeya.volume_iUnionShade_ge_of_isFrostmanAtEveryScale`, and the two thresholds
`η♯^{K_F}`, `η♯^{K_KT}` come from `Kakeya.FrostmanEstimate.multiplicity_bound_auxScale`
and `Kakeya.KatzTaoEstimate.multiplicity_bound`. We therefore take them as explicit arguments: `Kakeya.ml1Boot.params` is a genuine
closed-form function of `β`, `γ₀`, `η⋆`, `δ₀` and the two threshold functions, and the
hypotheses that those arguments really are the outputs in question appear in the
specification lemmas that consume them.

Items (ii)–(iv) are then literal formulas: `N` is a ceiling, `ε = 1 / √N`, and the ladder
`(η_j)` is the *geometric* ladder `η_j = κ ^ (N - j + 1)` of item (iii), implemented as the
upward power `Kakeya.ml1Boot.etaLadder` read backwards (`η_j = etaLadder κ (N - j)`).
-/

@[expose] public section

open scoped NNReal

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya

universe u

namespace ml1Boot

/-! ### Reduction to a positive Katz–Tao exponent -/

/-- The shifted Katz–Tao exponent `β'(γ) = max β (γ / 2)` of blueprint
`lem:ml1bootBetaPrime`.  It is strictly positive whenever `γ > 0` and still strictly
below `γ`, and `K_KT(β)` implies `K_KT(β'(γ))`. -/
noncomputable def betaPrime (β γ : ℝ) : ℝ := max β (γ / 2)

/-- The exponent gap `g(γ) = γ - β'(γ) = min (γ - β) (γ / 2)` of blueprint
`lem:ml1bootBetaPrime`(ii).  The whole of Section 8 divides by this quantity, which is why
`β` is replaced by `β'` in the first place. -/
noncomputable def gap (β γ : ℝ) : ℝ := γ - betaPrime β γ

/-- **The exponent gap** (blueprint `lem:ml1bootBetaPrime`(ii)).

The gap `g(γ) = γ - β'(γ)` equals `min (γ - β) (γ / 2)`, is strictly positive on `(β, 1]`,
and is monotone increasing there; in particular `g(γ) ≥ g(γ₀) = gap β γ₀` for every
`γ ∈ [γ₀, 1]`, which is the form in which the whole of Section 8 uses it.  Like
`Kakeya.ml1Boot.betaPrime_spec` this is `E`-free real arithmetic. -/
theorem gap_spec {β : ℝ} (hβ0 : 0 ≤ β) :
    (∀ γ, gap β γ = min (γ - β) (γ / 2)) ∧
      (∀ γ ∈ Set.Ioc β 1, 0 < gap β γ) ∧
      MonotoneOn (gap β) (Set.Ioc β 1) := by
  have hgap : ∀ γ, gap β γ = min (γ - β) (γ / 2) := by
    intro γ
    dsimp [gap, betaPrime]
    by_cases h : β ≤ γ / 2
    · have hmax : max β (γ / 2) = γ / 2 := max_eq_right h
      have hmin : min (γ - β) (γ / 2) = γ / 2 := min_eq_right (by linarith)
      rw [hmax, hmin]
      ring
    · have hβ_le : γ / 2 ≤ β := le_of_not_ge h
      have hmax : max β (γ / 2) = β := max_eq_left hβ_le
      have hmin : min (γ - β) (γ / 2) = γ - β := min_eq_left (by linarith)
      rw [hmax, hmin]
  refine ⟨hgap, ?_, ?_⟩
  · intro γ hγ
    rw [hgap]
    have hβγ : β < γ := hγ.1
    have hγ0 : 0 < γ := lt_of_le_of_lt hβ0 hβγ
    have hgβ : 0 < γ - β := by linarith
    exact (by positivity : 0 < min (γ - β) (γ / 2))
  · intro a ha b hb hab
    rw [hgap, hgap]
    refine min_le_min ?_ ?_
    · linarith
    · nlinarith

section BetaPrime

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end BetaPrime

/-! ### The parameter package -/

/-- The ladder `(η_j)_{j = 0}^{N}` of blueprint `def:ml1bootParams`(iii), read *upwards*:
`etaLadder κ k` is the blueprint's `η_{N - k}`.

The ladder is *geometric* with ratio `κ = ε² β₀ g₀ / 100`: the blueprint prescribes
`η_N = κ` and `η_j = κ ^ (N - j) η_N = κ ^ (N - j + 1)`, so that `η_{j-1} = κ η_j` for
`1 ≤ j ≤ N`.  In the upward indexing this is the bare power `etaLadder κ k = κ ^ (k + 1)`.

This replaces the earlier downward recursion
`η_N = ε / 5`, `η_{j-1} = min (ε² γ₀ η_j / 60) (ε γ₀ g₀ / 400) (η_j)`.  The change is one of
*shape*, not of numerals: the induction proving `Kakeya.ml1Boot.params_spec`(ii) becomes the
antitonicity of `k ↦ κ ^ k` for `0 < κ ≤ 1`, and the two bounds of
`Kakeya.ml1Boot.params_spec`(iii) become one-line computations, because on the geometric
ladder `10 η_{j-1} / (ε β₀) = ε g₀ η_j / 10` exactly rather than up to a case analysis over a
minimum. -/
noncomputable def etaLadder (κ : ℝ) (k : ℕ) : ℝ := κ ^ (k + 1)

/-- The number `N` of scales of blueprint `def:ml1bootParams`(ii): the least integer with
`N ≥ max 4096 ((20 / η⋆) ^ 2) ((96 / g₀) ^ 2)`, so that `ε = 1 / √N` satisfies
`ε ≤ 1 / 64`, `20 ε ≤ η⋆` and `96 ε ≤ g₀`.

* `N ≥ 4096` is the threshold that `StickyKakeya.dividingScalesFrostman` imposes.  In that
  statement `N` no longer indexes the grid — the hierarchy lives on the grid of length
  `Tube.ssfGridLen δ` — and bounds the exponent index alone.
* `N ≥ (20 / η⋆) ^ 2` delivers GWZ's `5 ε ≤ η⋆ / 4`; the earlier `N ≥ 25 / η⋆ ^ 2` gave only
  `5 ε ≤ η⋆`.
* `N ≥ (96 / g₀) ^ 2` controls the middle factor at parent scale `δ̃ ^ (6 ε)`.
  The density exponent of `Kakeya.ml1Boot.maxDensity_coarse_le_rpow` is
  `30 ε + η'_{j-1}`: that lemma reads the parent count at `ρ ^ (-5)`, so the exponent is `5`
  times the parent scale's `6 ε`.  See blueprint `note:ml1bootWindowConsumers`(3).  Since
  `g₀ ≤ 1/2` this forces `N ≥ 192 ^ 2 = 36864`.

The gap here is `g₀ = γ₀ - β'(γ₀)` and not `γ₀ - β`; see blueprint
`note:ml1bootBetaZeroFixed`. -/
noncomputable def paramsN (β γ₀ ηStar : ℝ) : ℕ :=
  max 4096 ⌈max ((20 / ηStar) ^ 2) ((96 / gap β γ₀) ^ 2)⌉₊

/-- **The parameter package** `c_{8.1}(β, γ₀)` of blueprint `def:ml1bootParams`: the
threshold `η⋆` and scale `δ₀` of the sticky Kakeya theorem, the number `N` of scales, the
loss exponent `ε = 1 / √N`, the ladder `(η_j)_{j ≤ N}` and the `γ`-dependent fullness
threshold `η(·)`.

The fields carry no proofs; the properties asserted by the blueprint definition are the
content of `Kakeya.ml1Boot.params_spec` and `Kakeya.ml1Boot.etaGamma_spec`. -/
structure Params where
  /-- The fullness / Frostman-at-every-scale threshold `η⋆` of the sticky Kakeya theorem. -/
  ηStar : ℝ
  /-- The scale threshold `δ₀` of the sticky Kakeya theorem. -/
  δ₀ : ℝ≥0
  /-- The number `N` of scales. -/
  N : ℕ
  /-- The loss exponent `ε = 1 / √N`. -/
  ε : ℝ
  /-- The ladder ratio `κ = ε² β₀ g₀ / 100` of blueprint `def:ml1bootParams`(iii), where
  `β₀ = β'(γ₀)` and `g₀ = γ₀ - β₀`.  It is positive because `β₀ > 0`, and it is far below `ε`;
  the blueprint's geometric ladder is `η_j = κ ^ (N - j + 1)`.  See
  `Kakeya.ml1Boot.Params.Spec` for what the present package asserts about it. -/
  κ : ℝ
  /-- The ladder `(η_j)_{j ≤ N}`; the values at `j > N` are irrelevant. -/
  η : ℕ → ℝ
  /-- The bookkeeping accuracy `ε' = η₀ / 16` of blueprint `def:ml1bootParams`(iv): the
  exponent at which `Kakeya.ml1Boot.exists_caseTwoData` and
  `Kakeya.ml1Boot.exists_factorTwoScales` are chained. -/
  ε' : ℝ
  /-- The `γ`-dependent fullness threshold `η(γ)`. -/
  ηGamma : ℝ → ℝ
  /-- The **step** `c = min (γ₀ / 2) (η₀ / 4)` of blueprint `def:ml1bootParams`(vi).

  This is the field that closes blueprint `note:auditUniformStep`: the step is read off the
  *bottom* rung `η₀` of the ladder and off `γ₀`, it depends on `(β, γ₀)` alone, and it is fixed
  *before* the accuracy at which `K_F(γ - c)` is subsequently asked for, which is what
  `Kakeya.frostmanStepSet` demands.  The alternative route stepped by the ladder entry `η 1`
  against a loss allowance `δ ^ (-ε)` drawn from the package itself, coupling the step to the
  accuracy. -/
  c : ℝ

/-- The **eccentricity exponent** `η'_j = 10 η_j / (ε β₀)` of blueprint
`def:ml1bootParams`(iv), where `β₀ = β'(γ₀) = Kakeya.ml1Boot.betaPrime β γ₀` is the fixed
shifted exponent of blueprint `note:ml1bootBetaZeroFixed`.  The blueprint writes `η'_{j-1}`;
here the index is the one of the `η` used, so the blueprint's `η'_{j-1}` is
`p.etaPrime β γ₀ (j - 1)`.

The denominator is the *fixed* `ε β₀` and not `ε γ` or `ε β'(γ)`: item (iv) makes `η'`
`γ`-free, which is what lets the whole parameter package — and with it the step `c` and the
uniform statement `Kakeya.ml1Boot.exists_uniform_step` — be fixed before `γ` is chosen.  On
the geometric ladder of item (iii) it has the closed form
`η'_{j-1} = 10 κ η_j / (ε β₀) = ε g₀ η_j / 10`, which is what turns the bounds recorded in
`Kakeya.ml1Boot.Params.Spec` into one-line computations.

Since `β₀ ≤ β'(γ)` for `γ ∈ [γ₀, 1]`, this quantity *dominates* the `γ`-dependent form
`10 η_{j-1} / (ε β'(γ))` that the dichotomy actually delivers; that domination is the clause
`Kakeya.ml1Boot.Params.Spec.etaPrimeDominates`, so a caller holding only the `γ`-dependent
quantity still inherits every bound proved here. -/
noncomputable def Params.etaPrime (p : Params) (β γ₀ : ℝ) (j : ℕ) : ℝ :=
  10 * p.η j / (p.ε * betaPrime β γ₀)

/-- **The parameter package of blueprint `def:ml1bootParams`.**

`η⋆` and `δ₀` are the output of
`StickyKakeya.volume_iUnionShade_ge_of_isFrostmanAtEveryScale`
applied with `γ₀ / 2` in place of `ε`, and `ηKF`, `ηKKT` are the fullness thresholds
supplied by `Kakeya.FrostmanEstimate.multiplicity_bound_auxScale` and
`Kakeya.KatzTaoEstimate.multiplicity_bound` at the loss exponent `η₀`, as functions of the
exponent at which each of those lemmas is applied.  They are arguments rather than internal
choices so that this is a genuine closed-form definition; the specification lemmas record
what has to be true of them.

Absorbing the loss-exponent slot `ε♯ = η₀` into `ηKF` and `ηKKT`, so that they are functions
of the *exponent* alone, is not circular: `N`, `ε`, `κ` and the whole ladder `(η_j)` — hence
`η₀` itself — are built from `β`, `γ₀` and `η⋆` only, and `ηKF`, `ηKKT` enter the definition
nowhere but in `ηGamma`.  A caller therefore computes `η₀ = (params β γ₀ η⋆ δ₀ f g).η 0` for
*any* pair `f`, `g` (for instance the constant `0` functions), applies
`Kakeya.FrostmanEstimate.multiplicity_bound_auxScale` and
`Kakeya.KatzTaoEstimate.multiplicity_bound` at that `η₀` to obtain the genuine thresholds
`ηKF`, `ηKKT`, and only then forms `params β γ₀ η⋆ δ₀ ηKF ηKKT`; the ladder it gets back is
the one the thresholds were chosen against.

Note the arguments at which the two thresholds are read, matching blueprint
`def:ml1bootParams`(v):

* the Frostman threshold is read at `γ` itself, since
  `Kakeya.FrostmanEstimate.multiplicity_bound_auxScale` is applied at the exponent `γ`;
* the Katz–Tao threshold is read at the *shifted* exponent `β'(γ) = Kakeya.ml1Boot.betaPrime β γ`,
  since `Kakeya.KatzTaoEstimate.multiplicity_bound` is applied at that exponent and not at `γ`
  (see blueprint `lem:ml1bootTbKatzTao`), and it enters weighted by the factor `1 - 5 ε`.  The
  weight is `1 - 5 ε` and not `1 - ε` because the honest `b`-tube scale of
  `Kakeya.ml1Boot.plankWidth_le` is now only known to satisfy `b♯ ≤ δ̃ ^ (1 - 5 ε)`, so the
  fullness hypothesis of `Kakeya.ml1Boot.multiplicity_coarse_le` reads `λ ≥ δ̃ ^ ((1 - 5 ε) η♯)`;
  see blueprint `note:ml1bootWindowConsumers`(3).

The clause `ε η₀ / 2` in the minimum is what makes the fullness hypothesis
`δ ^ η(γ) ≤ λ` of `Kakeya.ml1Boot.multiplicity_le_middle` survive the rescaling to the
middle scale `δ̃ = τ / θ ≤ δ ^ ε`: it gives `δ ^ η(γ) ≤ δ̃ ^ (η(γ) / ε) ≤ δ̃ ^ (η₀ / 2)`, hence
the hypotheses `δ̃ ^ η_{j-1} ≤ λ` of `Kakeya.ml1Boot.flatPrism_dichotomy` and
`Kakeya.ml1Boot.normalized_le_of_coarse`(b) at `j = 1`, where `η_{j-1} = η₀`.  Without it the
case `j = 1` would be unprovable. -/
noncomputable def params (β γ₀ ηStar : ℝ) (δ₀ : ℝ≥0) (ηKF ηKKT : ℝ → ℝ) : Params :=
  let N := paramsN β γ₀ ηStar
  let ε := 1 / Real.sqrt N
  let κ := ε ^ 2 * betaPrime β γ₀ * gap β γ₀ / 100
  let η : ℕ → ℝ := fun j => etaLadder κ (N - j)
  { ηStar := ηStar
    δ₀ := δ₀
    N := N
    ε := ε
    κ := κ
    η := η
    ε' := η 0 / 16
    ηGamma := fun γ =>
      min (min (min (η 0) ηStar) (ε * η 0 / 4))
        (min (ηKF γ) ((1 - 5 * ε) * ηKKT (betaPrime β γ)))
    c := min (γ₀ / 2) (η 0 / 4) }

/-- **What it means for a parameter package to be admissible for `(β, γ₀)`**, one field per clause
of items (i)–(iii).

The clauses depend on none of `δ₀`, `ηKF`, `ηKKT`, and on `η⋆` only through
`fiveEpsLe`, which is why `η⋆` is read off the package itself as `p.ηStar` rather than
carried as a separate parameter.

`etaPrimeLossLe` is item (iii) in its *loss-corrected* form: besides
`η'_{j-1} ≤ ε η_j / 2` (`etaPrimeLe`) it asserts the stronger
`η'_{j-1} + η₀ / ε ≤ ε η_j / 2`.  This is what `Kakeya.ml1Boot.plankWidth_le` needs, since
the lower Frostman bounds fed into it carry the loss `δ ^ (η₀)` in the *outer* scale `δ`,
whereas `Kakeya.ml1Boot.plankWidth_le` is stated at the rescaled scale `δ̃ = τ / θ`, of which
only `δ̃ ≤ δ ^ ε` is known; so the loss exponent available there is `e = η₀ / ε`, not `η₀`.
On the geometric ladder the corrected form costs nothing: `η'_{j-1} ≤ ε η_j / 20` and
`η₀ / ε ≤ ε η_j / 200`, whose sum is `11 ε η_j / 200 ≤ ε η_j / 2`.

The four `η'` clauses are `γ`-free, matching blueprint `def:ml1bootParams`(iv); the fifth,
`etaPrimeDominates`, is the only one to quantify over `γ`, and it is what transports those
bounds to the `γ`-dependent quantity `10 η_{j-1} / (ε β'(γ))`.

Bundling these clauses is what lets the Case (ii) lemmas take a package together with
its specification instead of re-deriving `Kakeya.ml1Boot.params β γ₀ η⋆ δ₀ ηKF ηKKT` from
seven separate binders at every call site. -/
structure Params.Spec (p : Params) (β γ₀ : ℝ) : Prop where
  /-- (i) The loss exponent `ε = 1 / √N` is positive. -/
  epsPos : 0 < p.ε
  /-- (i) `ε ≤ 1`. -/
  epsLeOne : p.ε ≤ 1
  /-- (i) `N ≥ 4096`, the threshold `StickyKakeya.dividingScalesFrostman` imposes. -/
  nGeFourThousandNinetySix : 4096 ≤ p.N
  /-- (i) `ε ≤ 1 / 64`, which is what `N ≥ 4096` buys. -/
  epsLeInvSixtyFour : p.ε ≤ 1 / 64
  /-- (i) `20 ε ≤ η⋆`, which is what `N ≥ (20 / η⋆) ^ 2` buys; this is GWZ's
  `5 ε ≤ η⋆ / 4`. -/
  twentyEpsLe : 20 * p.ε ≤ p.ηStar
  /-- (i) `5 ε ≤ η⋆`, the weakening of `twentyEpsLe` that Case (i)
  (`Kakeya.ml1Boot.multiplicity_le_of_frostmanAtEveryScale`) consumes. -/
  fiveEpsLe : 5 * p.ε ≤ p.ηStar
  /-- (i) `96 ε ≤ g₀ = gap β γ₀`, which is what `N ≥ (96 / g₀) ^ 2` buys.  Together with
  `g₀ ≤ 1/2` it gives `ε ≤ 1/192`, which is where the strict positivity of `1 - 5 ε` in
  `Kakeya.ml1Boot.params` comes from.

  The tightest consumer of the bound is `Kakeya.ml1Boot.numerics_strong`, which charges
  `72 ε + 2 η'_{j-1}` against `g(γ)`; with `etaPrimeLeGap` that is at most
  `72 g₀ / 96 + 2 g₀ / 40 = 4 g₀ / 5`, so `96` still leaves room. -/
  ninetySixEpsLe : 96 * p.ε ≤ gap β γ₀
  /-- (ii) The bottom rung of the ladder is positive. -/
  etaZeroPos : 0 < p.η 0
  /-- (ii) The ladder is nondecreasing on `[0, N]`. -/
  etaMono : MonotoneOn p.η (Set.Iic p.N)
  /-- (ii) The top rung is the ratio itself, `η_N = κ`.  Together with `etaStep` this pins the
  ladder down completely: `η_j = κ ^ (N - j + 1)`. -/
  etaTopEq : p.η p.N = p.κ
  /-- (ii) The top rung `η_N = κ` is at most `ε / 5`.  The blueprint's geometric ladder makes
  this an *inequality*: the earlier recursion started at the exact value `η_N = ε / 5`, whereas
  item (iii) of `def:ml1bootParams` starts at `η_N = κ ≤ ε² / 200 ≤ ε / 5`. -/
  etaTop : p.η p.N ≤ p.ε / 5
  /-- (ii) **The ladder descends at the ratio `κ`**: `η_{j-1} = κ η_j` for `1 ≤ j ≤ N`.  This
  is the defining relation of the geometric ladder of blueprint `def:ml1bootParams`(iii); it is
  what makes `κ` a ratio rather than a bare number, and together with `kappaLeEps` it gives the
  ladder condition `η_{j-1} ≤ ε η_j` of `StickyKakeya.dividingScalesFrostman`. -/
  etaStep : ∀ j, 1 ≤ j → j ≤ p.N → p.η (j - 1) = p.κ * p.η j
  /-- (iii) `η'_{j-1} ≤ ε η_j / 2`.  The bound is `γ`-free, as blueprint
  `def:ml1bootParams`(iv) requires of `η'`. -/
  etaPrimeLe : ∀ j, 1 ≤ j → j ≤ p.N → p.etaPrime β γ₀ (j - 1) ≤ p.ε * p.η j / 2
  /-- (iii) The loss-corrected form `η'_{j-1} + η₀ / ε ≤ ε η_j / 2`, the first half of
  blueprint `eq:ml1bootEtaPrimeBounds`. -/
  etaPrimeLossLe : ∀ j, 1 ≤ j → j ≤ p.N →
    p.etaPrime β γ₀ (j - 1) + p.η 0 / p.ε ≤ p.ε * p.η j / 2
  /-- (iii) `η'_{j-1} ≤ g₀ / 40`, the second half of blueprint
  `eq:ml1bootEtaPrimeBounds`. -/
  etaPrimeLeGap : ∀ j, 1 ≤ j → j ≤ p.N → p.etaPrime β γ₀ (j - 1) ≤ gap β γ₀ / 40
  /-- (iii) `η_{j-1} ≤ η'_{j-1}`, which holds because `ε β₀ ≤ 1 ≤ 10`. -/
  etaLeEtaPrime : ∀ j, 1 ≤ j → j ≤ p.N → p.η (j - 1) ≤ p.etaPrime β γ₀ (j - 1)
  /-- (iii) **The `γ`-free exponent dominates the `γ`-dependent one**: for every
  `γ ∈ [γ₀, 1]`, `10 η_{j-1} / (ε β'(γ)) ≤ η'_{j-1}`.

  This is the clause that makes the four `γ`-free bounds above usable by a caller that holds
  only the `γ`-dependent quantity `10 η_{j-1} / (ε β'(γ))` — which is what the Katz–Tao step
  of Section 8 delivers, since it is applied at the shifted exponent `β'(γ)`.  It holds
  because `β'` is monotone, so `β₀ = β'(γ₀) ≤ β'(γ)` for `γ ≥ γ₀`. -/
  etaPrimeDominates : ∀ j, 1 ≤ j → j ≤ p.N → ∀ γ ∈ Set.Icc γ₀ 1,
    10 * p.η (j - 1) / (p.ε * betaPrime β γ) ≤ p.etaPrime β γ₀ (j - 1)
  /-- (iii) The ladder ratio `κ = ε² β₀ g₀ / 100` is positive; this is exactly the positivity
  of `β₀ = β'(γ₀)`, which is what the substitution of blueprint `note:ml1bootBetaZeroFixed`
  buys and what the raw `β` does not give at `β = 0`. -/
  kappaPos : 0 < p.κ
  /-- (iii) `κ ≤ ε² / 200`, which is `β₀ ≤ 1` and `g₀ ≤ 1/2`.  This is the bound that pays for
  the loss summand `η₀ / ε ≤ ε η_j / 200` in `etaPrimeLossLe`. -/
  kappaLeEpsSq : p.κ ≤ p.ε ^ 2 / 200
  /-- (iii) `κ ≤ ε`, so a ladder descending at the ratio `κ` satisfies the ladder condition
  `η_{j-1} ≤ ε η_j` of `StickyKakeya.dividingScalesFrostman` a fortiori. -/
  kappaLeEps : p.κ ≤ p.ε
  /-- (iv) The bookkeeping accuracy is `ε' = η₀ / 16`, half the extremal value `η₀ / 8`
  allowed by the exponent contract of blueprint `eq:ml1bootExponentContract`. -/
  epsPrimeEq : p.ε' = p.η 0 / 16
  /-- (vi) The step is positive. -/
  stepPos : 0 < p.c
  /-- (vi) `c ≤ γ₀ / 2`, which is what Case (i)
  (`Kakeya.ml1Boot.multiplicity_le_of_frostmanAtEveryScale`) requires of a step. -/
  stepLeHalfGammaZero : p.c ≤ γ₀ / 2
  /-- (vi) `c ≤ η₀ / 4`, which is what the funding inequality `stepFunding` requires. -/
  stepLeEtaZero : p.c ≤ p.η 0 / 4
  /-- (vi) **The funding inequality**.  For every rung
  `1 ≤ j ≤ N` and every fullness exponent `e ∈ [0, η₀]` — the intended value being
  `e = η(γ)`, which satisfies `η(γ) ≤ η₀` by `Kakeya.ml1Boot.Params.EtaGammaSpec` —

  `ε' + 2 c + e c / 2 + 5 η₀ / 16 ≤ 2 η_{j-1} - 16 ε'`,

  whose right-hand side is the gain exponent `10 a - 8 a'` of the exponent contract at
  `a = η_{j-1}`, `a' = η_{j-1} + 2 ε'`.  In words: the linking loss `δ ^ (-ε')` and the
  exponent shift `γ ↦ γ - c`, which costs `δ ^ (-2c - e c / 2)`, are together paid for by the
  gain of the contract, with the strict surplus `δ ^ (5 η₀ / 16)` left over to absorb the fixed
  constants of the assembly into the smallness of `δ`.  This is what decouples the step from
  the package's loss exponent `ε`. -/
  stepFunding : ∀ j, 1 ≤ j → j ≤ p.N → ∀ e : ℝ, 0 ≤ e → e ≤ p.η 0 →
    p.ε' + 2 * p.c + e * p.c / 2 + 5 * p.η 0 / 16 ≤ 2 * p.η (j - 1) - 16 * p.ε'

/-- **The `γ`-dependent fullness threshold**.

For every `γ ∈ [γ₀, 1]` the threshold `η(γ)` is positive, is below every exponent of the
ladder and below `η⋆`, is below `ε η₀ / 2`, and is below both of the thresholds `ηKF γ` and
`(1 - 5 ε) * ηKKT (β'(γ))` that the fine, coarse and Katz–Tao steps of Section 8 consume.

The clause `η(γ) ≤ ε η₀ / 2` is the one that survives the rescaling to the middle scale: it
turns the fullness hypothesis `δ ^ η(γ) ≤ λ` of `Kakeya.ml1Boot.multiplicity_le_middle` into
`δ̃ ^ (η₀ / 2) ≤ λ` at `δ̃ = τ / θ ≤ δ ^ ε`, hence into the hypotheses
`δ̃ ^ η_{j-1} ≤ λ` of `Kakeya.ml1Boot.flatPrism_dichotomy` and
`Kakeya.ml1Boot.normalized_le_of_coarse`(b), including at `j = 1` where `η_{j-1} = η₀`.

As in `Kakeya.ml1Boot.params`, the Katz–Tao threshold is read at the shifted exponent
`β'(γ) = Kakeya.ml1Boot.betaPrime β γ`, which is the exponent at which
`Kakeya.KatzTaoEstimate.multiplicity_bound` is applied in Section 8.

The hypotheses on `ηKF` and `ηKKT` are only their positivity: that is all the blueprint
uses, and it is what `Kakeya.FrostmanEstimate.multiplicity_bound_auxScale` and
`Kakeya.KatzTaoEstimate.multiplicity_bound` supply. -/
structure Params.EtaGammaSpec (p : Params) (β γ₀ : ℝ) (ηKF ηKKT : ℝ → ℝ) : Prop where
  /-- `η(γ)` is positive. -/
  etaGammaPos : ∀ γ ∈ Set.Icc γ₀ 1, 0 < p.ηGamma γ
  /-- `η(γ)` is below the bottom rung of the ladder. -/
  etaGammaLeEtaZero : ∀ γ ∈ Set.Icc γ₀ 1, p.ηGamma γ ≤ p.η 0
  /-- The bottom two rungs of the ladder are ordered. -/
  etaZeroLeEtaOne : p.η 0 ≤ p.η 1
  /-- The rung `η_1` is below `ε / 5`.  On the geometric ladder this follows from the top
  rung bound `Kakeya.ml1Boot.Params.Spec.etaTop`, `η_N ≤ ε / 5`, together with the
  monotonicity `etaMono` of the ladder on `[0, N]` (note `1 ≤ N` since `N ≥ 4096`). -/
  etaOneLeEps : p.η 1 ≤ p.ε / 5
  /-- `η(γ)` is below the sticky-Kakeya threshold `η⋆`. -/
  etaGammaLeEtaStar : ∀ γ ∈ Set.Icc γ₀ 1, p.ηGamma γ ≤ p.ηStar
  /-- `η(γ) ≤ ε η₀ / 4`, the clause that survives the rescaling to the middle scale.

  The quarter, not the half: this is the strength
  `Kakeya.ml1Boot.multiplicity_le_middle_avg` asks for in its `hηΓ4` hypothesis, and without
  it that theorem carries an undischargeable side condition.  The half is still available,
  a fortiori, as `Kakeya.ml1Boot.Params.EtaGammaSpec.etaGammaLeRescale`. -/
  etaGammaLeRescale4 : ∀ γ ∈ Set.Icc γ₀ 1, p.ηGamma γ ≤ p.ε * p.η 0 / 4
  /-- `η(γ)` is below the Frostman threshold, read at `γ`. -/
  etaGammaLeKF : ∀ γ ∈ Set.Icc γ₀ 1, p.ηGamma γ ≤ ηKF γ
  /-- `η(γ)` is below the Katz–Tao threshold, read at the shifted exponent `β'(γ)` and
  weighted by `1 - 5 ε`.  This is the weight that supplies the fullness hypothesis
  `λ ≥ δ̃ ^ ((1 - 5 ε) η♯)` of `Kakeya.ml1Boot.multiplicity_coarse_le`, the honest `b`-tube
  scale being bounded only by `δ̃ ^ (1 - 5 ε)`. -/
  etaGammaLeKKT : ∀ γ ∈ Set.Icc γ₀ 1, p.ηGamma γ ≤ (1 - 5 * p.ε) * ηKKT (betaPrime β γ)

/-! ### Case (i): the sticky case -/

section CaseSticky

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end CaseSticky

end ml1Boot

end Kakeya

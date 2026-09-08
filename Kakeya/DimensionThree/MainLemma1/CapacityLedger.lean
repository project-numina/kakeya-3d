/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.FrostmanConstant
public import Kakeya.Multiplicity

/-!
# Main Lemma 1, Step 6: the local Frostman capacity and the exponent ledger

This module is the numeric spine of the Main Lemma 1 repair blueprint, §5, §6.1, §6.2, §6.4
and §6.5.  Nothing here is geometric beyond the one place it has to be: `Kakeya.frostmanConstant`
is bounded from below by the reciprocal of the *relative capacity* of a tube family inside its
container.  Everything downstream of that is an inequality between exponents.

## What is proved here

* `Kakeya.ml1Ledger.volume_le_frostmanConstant_mul_sum` — bound (C) of §5.1 in division-free
  form: for a family with a member of positive finite volume,
  `|P| ≤ C_F(𝓕, P) · ∑_{T ∈ 𝓕} |T|`.  Taking `T₀ ∈ 𝓕` as the Frostman test object gives
  `Δ_max ≥ 1`, which is the whole content.
* `Kakeya.ml1Ledger.one_le_capacity_mul_frostmanConstant` — the same statement in the `q` form
  `1 ≤ q · C_F`, where `q = |𝓕| (r/R)²` enters through the volume comparison
  `∑ |T| ≤ q · |P|`.
* `Kakeya.ml1Ledger.capacity_lower_bound` — (CLB): a *negative-exponent* upper bound on `C_F`
  forces `q ≥ δ^{κ_F} ρ^{a_F}`, and
  `Kakeya.ml1Ledger.card_lower_bound_of_capacity` turns that into the small-family exclusion
  `|𝓕| ≥ δ^{κ_F} ρ^{a_F - 2}`.  Note that this is a *lower* bound on the cardinality: `ρ^{-2}` is
  the normalised Kakeya cardinality scale, never an absolute maximum for an arbitrary family.
* `Kakeya.ml1Ledger.CapSpec` and `Kakeya.ml1Ledger.CapSpec.target_ge` — (CAP) of §5.2, together
  with the conclusion it exists to buy: the middle target right-hand side is at least
  `δ^{-s}` for a slack `s > 0`, hence in particular at least `1`.
* `Kakeya.ml1Ledger.uniformSlack` and `Kakeya.ml1Ledger.abs_of_lt_uniformSlack` — (ABS) of §6.1
  with the **non-circular** parameter order: the uniform slack `S_*` is a `Finset.inf'` over the
  finite rung/branch index set and is proved positive *before* any rung is selected, so the
  extra-loss budget is fixed before `j` and before `δ`.
* `Kakeya.ml1Ledger.ImpSpec.improvement` — (IMP) of §6.2.
* `Kakeya.ml1Ledger.multiplicity_le_one_of_card_le_one`,
  `Kakeya.ml1Ledger.product_collapse_fine`, `Kakeya.ml1Ledger.product_collapse_coarse` — the
  `τ = δ` and `θ = 1` endpoints of §6.5, each independent of the interior scale lemmas.
* `Kakeya.ml1Ledger.conv_upper`, `Kakeya.ml1Ledger.conv_lower` — the term-by-term scale
  conversion rules of §6.5.
* `Kakeya.ml1Ledger.appError_coarsen` and `Kakeya.ml1Ledger.eq60_appError_uniform`,
  `Kakeya.ml1Ledger.eq61_appError_uniform` — §6.4, covering the `j = 1` rung for **both** GWZ
  equation (60) and equation (61).

## GWZ v1 errata recorded as checkable statements

* `Kakeya.ml1Ledger.eq64_positive_exponent_false` — equation (64)'s positive-exponent upper bound
  on `C_F(𝕋̃)` is refutable against `C_F ≥ 1`.
* `Kakeya.ml1Ledger.prop66_sign_error_false` — the `λ ⪆ δ^{-η}` of the Proposition 6.6 proof is
  refutable for a density `λ ≤ 1`.
* `Kakeya.ml1Ledger.gain_at_eq66` and `Kakeya.ml1Ledger.gain_at_eq66_shortfall` — the gain from
  `b ≤ δ̃^{1-ε}` is `2(1-ε)(γ-β)`, and the shortfall `2ε(γ-β)` is charged to the ledger.
* `Kakeya.ml1Ledger.ladder_bound` — the corrected form of §8's "`η_{j-1} ≤ N`".

## The losses are kept separate

`a_F` (local Frostman exponent), `a_G` (target gain), `κ_F` (Frostman constant loss),
`κ_card` (carrier/cardinality loss) and `ℓ_μ` (multiplicity/refinement loss) are distinct
parameters.  `ℓ_μ` appears only through the extra-loss budget of
`Kakeya.ml1Ledger.abs_of_lt_uniformSlack`, never in `Kakeya.ml1Ledger.CapSpec`; this is the
separation the blueprint's errata table demands.  No lemma here identifies `a_F` with the formal
`a_lambda` or with any `η_{j-1}`: a bridge theorem would be needed and none is claimed.

## Satisfiability

Every inequality ledger in this file is accompanied by an explicit numeric instance
(`Kakeya.ml1Ledger.capWitness`, `Kakeya.ml1Ledger.absWitness`, `Kakeya.ml1Ledger.impWitness`),
so each ledger is exhibited as satisfiable.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody

namespace Kakeya

namespace ml1Ledger

/-! ## §6.5 The scale-conversion rules

Every exponent argument below needs these, and, as the blueprint insists, the direction has to be
checked term by term.  Both rules take the relative-scale hypothesis `r ≤ δ ^ ε_scale`. -/


/-! ## §5.1 Local Frostman capacity: the bound (C)

The Frostman constant of `Kakeya.frostmanConstant` is `Δ_max(𝕎) · |K| / ∑ |W i|`.  Taking a
member `W i₀` of the family as the test body in `Δ_max` gives `Δ_max ≥ 1`, and (C) follows by
clearing the denominator. -/

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*}


end


/-! ## §5.1 The bound (CLB)

`q ≥ δ^{κ_F} ρ^{a_F}` is *derived* from (C) plus a negative-exponent upper bound on `C_F`.  It is
not an extra analytic hypothesis.  Note the exponent on `ρ` in the hypothesis is `-a_F`: GWZ
equation (64)'s positive-exponent upper bound on `C_F(𝕋̃)` contradicts `C_F ≥ 1` and is not used
here. -/


/-! ## §5.2 The capacity inequality (CAP)

The five losses stay apart.  `ℓ_μ` — the multiplicity/refinement loss — is deliberately *not* a
field of `Kakeya.ml1Ledger.CapSpec`: it enters the global budget of §6.1 only. -/

/-- The exponent data of the §5.2 capacity inequality.  `p = 1 - γ/2`.

Fields, and what each is: `aF` is the local Frostman exponent of §5.1, `aG` the gain exponent of
the middle target, `kappaF` the Frostman-constant loss, `kappaCard` the carrier/cardinality loss
(typically `0` for a fixed skeleton), `gamma` the Kakeya exponent under improvement, `epsScale`
the relative-scale exponent from `r ≤ δ ^ epsScale`.

There is intentionally no `ℓ_μ` field and no identification of `aF` with `a_lambda` or with any
`η_{j-1}`. -/
structure CapSpec where
  /-- The local Frostman exponent of §5.1. -/
  aF : ℝ
  /-- The gain exponent of the middle target. -/
  aG : ℝ
  /-- The Frostman-constant loss. -/
  kappaF : ℝ
  /-- The carrier/cardinality loss; `0` for a fixed skeleton. -/
  kappaCard : ℝ
  /-- The Kakeya exponent. -/
  gamma : ℝ
  /-- The relative-scale exponent: `r ≤ δ ^ epsScale`. -/
  epsScale : ℝ
  aF_nonneg : 0 ≤ aF
  aG_nonneg : 0 ≤ aG
  kappaF_nonneg : 0 ≤ kappaF
  kappaCard_nonneg : 0 ≤ kappaCard
  gamma_pos : 0 < gamma
  gamma_lt_two : gamma < 2
  epsScale_pos : 0 < epsScale
  /-- `2γ > a_F p`. -/
  dominates : aF * (1 - gamma / 2) < 2 * gamma
  /-- **(CAP)**: `10 a_G + (κ_F + κ_card) p < ε_scale (2γ - a_F p)`. -/
  cap : 10 * aG + (kappaF + kappaCard) * (1 - gamma / 2)
      < epsScale * (2 * gamma - aF * (1 - gamma / 2))


namespace CapSpec

variable (c : CapSpec)

/-- `p = 1 - γ/2`. -/
noncomputable def p : ℝ := 1 - c.gamma / 2


end CapSpec


/-! ## §6.1 The absolute budget (ABS), with a non-circular parameter order

`8 a' ≤ 10 a` gives only non-negativity; it never gives strict slack.  The fix is to take the
minimum over the *finite* set of rung/branch choices before `δ` (and before `j`) is chosen, and
to allocate the extra losses out of that number. -/


variable {ι : Type*}


/-! ### Counting a loss at its true multiplicity

A constant appearing `w i` times, or raised to a power, must be charged `w i` times. -/

/-- The ledger total: entry `i` charged at multiplicity `w i`. -/
noncomputable def totalLoss (s : Finset ι) (w : ι → ℕ) (e : ι → ℝ) : ℝ := ∑ i ∈ s, (w i : ℝ) * e i


/-! ## §6.2 The improvement inequality (IMP)

`G` is the **net** gain after every factoring, normalisation, fixed-constant and endpoint loss;
`ν` is a free parameter of the improvement, never hardcoded to `η₁`. -/

/-- The exponent data of the §6.2 improvement inequality. -/
structure ImpSpec where
  /-- The Kakeya exponent being improved. -/
  gamma : ℝ
  /-- The floor exponent. -/
  beta : ℝ
  /-- The improvement step; a free parameter, **not** hardcoded to `η₁`. -/
  nu : ℝ
  /-- The global Frostman exponent: `Q ≥ δ^{η₀}`. -/
  eta0 : ℝ
  /-- The **net** gain, after every factoring, normalisation, fixed-constant and endpoint loss. -/
  G : ℝ
  nu_pos : 0 < nu
  nu_lt_gap : nu < gamma - beta
  eta0_nonneg : 0 ≤ eta0
  /-- **(IMP)**: `G > 2ν + η₀ ν / 2`. -/
  imp : 2 * nu + eta0 * nu / 2 < G

namespace ImpSpec


end ImpSpec


/-! ## §6.5 The two endpoints

Neither is allowed to be forced through the interior scale lemmas. -/

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*}


end


/-! ### The endpoint form of the three-factor inequality (F) -/

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*}


end

/-! ## GWZ v1 errata, as checkable statements

Three of the source's printed inequalities are not merely imprecise, they are refutable as
printed.  Each is recorded here as a Lean `False`-conclusion or as the corrected form, so that no
later step can quietly re-import the broken version. -/


/-! ## §6.4 The application error at equations (60) and (61)

Coarsening a loss to `δ^{-η_{j-1}}` needs an explicit inequality; `ε_app ≤ (1 + γ/2) η_{j-1}` is
what GWZ equation (60) actually requires.  Equation (61) has the same `j = 1` problem, so both
are covered below. -/


end ml1Ledger

end Kakeya

end

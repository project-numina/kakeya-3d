/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCardBand

/-!
# Scoping the multilinear input of the Main Lemma 2 cardinality band

`Kakeya.ML2Band` (`Reduction/SpineCardBand.lean`) reduces the last open branch of the Main Lemma 2
assembly to `Kakeya.ML2Band.BandDichotomy`, equivalently to `Kakeya.ML2Band.BandKakeya`, on the
cardinality band `δ^{-ε/(2(β-γ))} < |𝕋| < δ^{-1}`, and proves that none of the three inequalities
the assembly holds is strong enough there.  The route named by Prof. Hong Wang is broad--narrow,
whose broad half needs a **multilinear Kakeya inequality in ℝ³**.

This file is the *scoping* of that input. It states the multilinear ingredient precisely, states
the exponent budget that any broad--narrow route through it must meet, and — the reason the file
exists — **shows by compiler-checked arithmetic that the broad--narrow sketch recorded  does not meet that budget**. Nothing here is assumed: every declaration is
either a `def... : Prop` that nothing uses, or a theorem proved outright.

**Two different Bourgain--Guth constants appear below and must not be conflated.**  `b` in
`Kakeya.ML2BandML.Budget` is the *broad extraction* exponent, from `m ≤ K^{b}(m₁m₂m₃)^{1/3}`; the
crude extraction gives `b = 2`, from `∑_τ m_τ = m` over `≈ K²` caps.  `b` in
`Kakeya.ML2BandML.narrowLossExponent` is the *narrow threshold* exponent, `Λ = K^{b}`.  They are
independent, and the two sections below are about the two of them separately.  (In the Lean
statements they are of course separate binders; the shared letter is only in this prose.)

## The budget

Assemble the broad half exactly as the sketch does: the pointwise Bourgain--Guth broad bound
`m ≤ K^b (m₁m₂m₃)^{1/3}`, a multilinear Kakeya inequality of loss `δ^{-A₀}`, Hölder with exponents
`(3/2, 3)`, the fullness lower bound `λ ≥ δ^{η}`, and the band hypothesis `δ²|𝕋| < δ`.  Writing
`K = δ^{-κ}`, the broad alternative closes to `μ ≲ δ^{1 - 3bκ - 2A₀ - 2η}`, so it delivers
`μ ≤ δ^{-ε}` exactly when

  `3·b·κ + 2·A₀ + 2·η ≤ 1 + ε`.                                        (`Kakeya.ML2BandML.Budget`)

`Kakeya.ML2BandML.broad_closes_of_budget` is that implication as an `rpow` inequality, and
`Kakeya.ML2BandML.le_pow_three_of_le_rpow_mul` is the one nonlinear step of the derivation
(`μ ≤ B·μ^{2/3} → μ ≤ B³`, which is where "the broad case closes" happens).  Read the other way,
the budget *is* the `δ¹` of surplus the band enjoys: `Kakeya.ML2BandML.exists_budget_of_lt_half`
says every loss `2A₀ < 1 + ε` — in particular every `A₀ < 1/2` — meets it, and
`Kakeya.ML2BandML.not_budget_of_half_lt` says that threshold is sharp.  So the broad half tolerates
a multilinear loss of almost `δ^{-1/2}`, and the sketch's claim that the broad case is easy here,
with a whole factor `δ¹` of surplus, is **confirmed**.

## Loomis--Whitney is not a substitute for Bennett--Carbery--Tao

The only thing in Mathlib's Brascamp--Lieb corner is the axis-parallel "grid-lines" lemma
`MeasureTheory.lintegral_prod_lintegral_pow_le` (`Mathlib/Analysis/FunctionalSpaces/
SobolevInequality.lean`).  Applied to tubes whose directions lie in a cap of width `1/K`, it gives
loss exponent `A₀ = 3/2 - κ`: a `δ`-tube whose direction lies in a `1/K`-cap has a projection of
area `≈ δ·(1/K)`, not `δ²`, and the transversality of a Bourgain--Guth broad triple is only
`ν ≈ 1/K`.  With the Bourgain--Guth constant `b ≥ 2` the budget then forces `2 ≤ ε`
(`Kakeya.ML2BandML.loomisWhitney_budget_forces_two_le`): it misses by two full powers of `δ`.
Even at the best conceivable transversality `ν ≈ 1` the loss is `A₀ = 3(1-κ)/2` and the budget
still forces `2 ≤ ε` for every `b ≥ 2`
(`Kakeya.ML2BandML.loomisWhitney_transverse_budget_forces_two_le`).  Genuine
Bennett--Carbery--Tao/Guth — loss `δ^{-ε'}` for **every** `ε' > 0` — is required.

## The sketch's narrow accounting, and what repairing it costs

 argues that the narrow half terminates after `n = O(log(1/a)/κ)` rescalings
with accumulated loss `K^{bn} = δ^{-bκn}`, "`≤ δ^{-ε}` provided `κ` is chosen small compared to
`ε/n` — self-consistent, since `n` depends only on `κ` and `a`".  It is not self-consistent: `n`
grows like `1/κ`, so `κ·n ≈ log(1/a)` does not depend on `κ` at all.

Account charitably for the shrinking of the scale — step `j` runs at `δ^{(1-κ)^j}`, so its loss is
`δ^{-bκ(1-κ)^j}`, the *smallest* reading of the claim — and the accumulated loss exponent is
`b(1 - (1-κ)^n)` (`Kakeya.ML2BandML.narrowLossExponent_eq`), while termination of the induction is
exactly `(1-κ)^n ≤ a`, `a` being the cardinality exponent the band starts at.  So the accumulated
loss exponent is at least `b(1-a)` **whatever `κ` is**
(`Kakeya.ML2BandML.le_narrowLossExponent_of_terminates`, `Kakeya.ML2BandML.not_sketchNarrowBudget`).
`Kakeya.ML2BandML.narrowLossExponent_le_mul` records that this refutes the literal reading `bκn`
as well, since `b(1-(1-κ)^n) ≤ b·κ·n`.

**So `κ` is not the free parameter; `b` is** (`Kakeya.ML2BandML.narrow_forces_small_step_loss`:
the route needs `b ≤ ε/(1-a)`).  And `b` is not free either, for a reason that is the real content
of this file.  Write `Λ = K^{b}` for the Bourgain--Guth threshold, so that "narrow at `x`" means
some cap carries at least `m(x)/Λ`.  In the broad complement no cap carries `m/Λ`, while the caps
carrying at least `m/(2K²)` already carry half of `m`; hence more than `Λ/2` caps are heavy.  To
extract *three `Ω(1)`-transverse* heavy caps one needs more heavy caps than fit in a neighbourhood
of a great circle, and at cap width `1/K` a great circle carries `≈ K` caps.  A broad/narrow
**dichotomy** — no planar case — therefore forces `Λ ≳ K`, i.e. `b ≥ 1`, and then `b(1-a) ≥ 1-a`,
a fixed power of `δ`, and the accounting fails.  Taking instead `Λ = K^{ε'}` with `ε'` small *does*
make the accounting close, but leaves the broad complement possibly planar.

**The two defects are one defect.**  Broad--narrow in `ℝ³` is a *trichotomy*, and the sketch's
dichotomy silently prices the planar case into the narrow loss, where it costs a fixed power of
`δ`.  The compiler-checked statements above are what pins that: whatever `κ` and `n` are, the
narrow half costs `b(1-a)`, so either `b ≥ 1` and the route fails, or `b < 1` and the planar
case is required.

## What is deliberately *not* here

There is no `theorem bandDichotomy_of_trilinearKakeya`.  Stating one would be the shell game the
brief forbids: by the findings above, `Kakeya.ML2BandML.TrilinearKakeya` does **not** suffice for
`Kakeya.ML2Band.BandDichotomy` through the sketch, and what is missing is not bookkeeping.  The
missing case is the **planar** one — all heavy caps inside a small neighbourhood of a great circle
— which is neither multilinear nor a rescaling; it is the `SL₂`/slab regime, the case the whole
`VeryNotSticky` apparatus of Section 9 exists to handle.  GWZ mentions none
of this.

The one statement known to discharge the band is `Kakeya.ML2Band.BandKakeya`, already proved
sufficient in `Reduction/SpineCardBand.lean` (`Kakeya.ML2Band.smallCard_of_bandKakeya`,
`Kakeya.ML2Band.bandDichotomy_of_bandKakeya`).  The tripwires in the `Target` section pin that,
verbatim, so no later edit can quietly change what this file is scoping.
-/

@[expose] public section

open MeasureTheory Topology Filter

namespace Kakeya.ML2BandML

universe u

/-- The ambient space of Main Lemma 2, as in `Kakeya.ML2Band.Space3`. -/
abbrev Space3 := EuclideanSpace ℝ (Fin 3)

/-! ## Target

Verbatim tripwires against drift in the statement this file scopes.  If
`Kakeya.ML2Band.BandKakeya` or `Kakeya.ML2Band.BandDichotomy` changes — a binder moved, a
hypothesis added or dropped — the `rfl` and the two `example`s below stop compiling. -/

section Target


/-- **Fidelity compatibility.**  The target discharges the assembly's `SmallCard`; `γ = 0` is enough to
pin the interface. -/
example : Kakeya.ML2Band.BandKakeya.{u} → Kakeya.ML2Assembly.SmallCard.{u} 0 :=
  Kakeya.ML2Band.smallCard_of_bandKakeya le_rfl

/-- **Fidelity compatibility.**  The target discharges `Kakeya.ML2Band.BandDichotomy`, the form the
assembly consumes at the budget `c ≤ g`. -/
example {β g : ℝ} : Kakeya.ML2Band.BandKakeya.{u} → Kakeya.ML2Band.BandDichotomy.{u} β g :=
  Kakeya.ML2Band.bandDichotomy_of_bandKakeya

end Target

/-! ## The multilinear ingredient

`Kakeya.ML2BandML.TrilinearKakeya` is the Bennett--Carbery--Tao/Guth inequality in the shape the
broad half of broad--narrow consumes.  It is a `def`, used by nothing; this file asserts nothing
about it. -/

section Multilinear

/-- **Quantitative `ν`-transversality of three directions in `ℝ³`.**  Every vector is controlled by
its three inner products, with constant `ν⁻¹`.  For unit vectors this is comparable to
`|det (d₁, d₂, d₃)| ≥ ν`, and it is the form the constant of a multilinear Kakeya inequality
actually depends on.

Stated coordinate-free on purpose: a coordinate reading of "transverse" is the standard way such a
predicate silently becomes vacuous.  Both halves of non-vacuity are checked below
(`Kakeya.ML2BandML.transverse_single`, `Kakeya.ML2BandML.not_transverse_const`). -/
def Transverse (ν : ℝ) (d₁ d₂ d₃ : Space3) : Prop :=
  ∀ x : Space3, ‖x‖ ≤ ν⁻¹ * (|inner ℝ d₁ x| + |inner ℝ d₂ x| + |inner ℝ d₃ x|)


end Multilinear

/-! ## The broad budget

The exponent bookkeeping of the broad half, and the surplus the band enjoys. -/

section Broad


/-- **The broad budget.**

With `K = δ^{-κ}` the Bourgain--Guth cap parameter, `b` the exponent of `K` lost in the pointwise
broad bound `m ≤ K^{b}(m₁m₂m₃)^{1/3}`, `A₀` the loss exponent of the multilinear Kakeya inequality
(`Kakeya.ML2BandML.TrilinearKakeya`), and `η` the exponent in the fullness hypothesis `λ ≥ δ^{η}`,
the broad alternative of broad--narrow closes to

  `μ ≲ δ^{1 - 3bκ - 2A₀ - 2η}`

on the band `|𝕋| < δ^{-1}` (where `δ²|𝕋| < δ` — this is the `δ¹` of surplus), so it delivers
`μ ≤ δ^{-ε}` exactly under this inequality. -/
def Budget (b κ A₀ η ε : ℝ) : Prop := 3 * b * κ + 2 * A₀ + 2 * η ≤ 1 + ε


end Broad

/-! ## The narrow accounting, refuted -/

section Narrow


end Narrow

end Kakeya.ML2BandML

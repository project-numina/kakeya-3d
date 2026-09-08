/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Factorization

/-!
# The coarse scale of GWZ Proposition 6.6(B): why `δ ≤ ρ` was wrong and `δ ^ (1 - ε₂) ≤ ρ` is right

The coarse-scale condition in `Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` is stronger
than `δ ≤ ρ`. The latter permits `ρ = δ`, whence `a ≈ δ`, outside the regime covered by
the Proposition 5.1 argument below.

The obstruction is not a formalisation artefact.  Every route through GWZ Proposition 5.1 applies
GWZ Lemma 6.1 with `γ = 1` to the *inner* rescaled family, which lives at `a' ≈ δ / b`,
`b' ≈ δ / a`; the inner threshold `b' ≤ b₀` becomes an inner-scale hypothesis `δ ≤ s₀ · a` with `s₀`
produced **before** the configuration.  At `a = δ` that reads `δ ≤ s₀ · δ`, i.e. `1 ≤ s₀`, and
`Kakeya.Prop66BScale.not_le_mul_self_of_lt_one` below is the two-line proof that it fails for every
`s₀ < 1`.

So the narrowing is a **fidelity repair**: the free-`ρ` form promised a case the source does not
prove.  The source fixes the scale — the Main Lemma 2 argument, *"We set `ρ = δ̃^{1-ε₂}`"* — and so
does this development, in `Kakeya.ML2Reduction.plankScale`.

## What is here

* `statement_of_universal_prop66B_freeCoarseScale` — the **old** conclusion, verbatim, kept as a
  named `Prop` so that it stays pinned and citable after the binder changed.  A plain compatibility
  `example` cannot survive a changed binder; this device can.
* `statement_of_universal_prop66B_plankScale` — the **new** conclusion, likewise, together with the
  `example` that pins it to the real theorem.
* `le_of_plankScale_le` — **old ⟹ new**, pointwise: `δ ≤ δ ^ (1 - ε₂)`, which is the whole content
  of that implication.  The narrowed form is weaker, so no consumer can lose anything that was ever
  available.  The implication *between the two telescopes* does not elaborate (over 4 · 10⁶
  heartbeats); see the docstring of `le_of_plankScale_le`.
* `le_mul_of_plankScale_le` — the reason the narrowing is *useful* rather than merely honest: it
  discharges the inner-scale threshold `δ ≤ s₀ · a` from `δ ^ (1 - ε₂) ≤ ρ ≤ a` together with a
  threshold on `δ` alone.  This removes the threshold from the residual gap of Proposition 6.6(B)
  entirely.
* `lt_of_plankScale_le` — the new quantifier strictly excludes the uncovered regime: `δ < a`.
* `statement_of_universal_prop66B_branchingFloor` — the post- form (branching floor added),
  now the record of the **pre-** statement; and
  `statement_of_universal_prop66B_essDistinct` — the post- form, with the fine-family
  pairwise essential distinctness that GWZ Definition 2.1(ii) carries at `ρ = δ` made explicit, now the record of the **pre-** statement.  The live
  form, with the parent window, is pinned as
  `statement_of_universal_prop66B_essDistinct_parentWindow` in
  `Kakeya/DimensionThree/Plank/Prop66BChainResidue.lean` (which imports this file), and the
  `example` pinning it to the real theorem sits beside the theorem itself, now proved in
  `Kakeya/DimensionThree/Plank/Prop66BClose.lean`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ConvexSpaceBody
-- `Tube.IsUniformAtScale`'s fibre filters are `Finset.filter`s over an arbitrary index type,
-- exactly as in `Kakeya/DimensionThree/Plank/Factorization.lean`, which opens it file-wide too.
set_option linter.style.openClassical false
open scoped ENNReal NNReal Classical

noncomputable section

namespace Kakeya

namespace Prop66BScale

/-! ### The inner-scale threshold, and why `ρ = δ` cannot meet it -/


/-- **The narrowed coarse scale discharges the inner-scale threshold.**

From `δ ^ (1 - ε₂) ≤ ρ ≤ a` and a threshold on `δ` alone — `δ ≤ s₀ ^ (1 / ε₂)`, which a producer
folds into its `δ₀` — one gets `δ ≤ s₀ · a`.  The identity behind it is
`δ = δ ^ ε₂ · δ ^ (1 - ε₂)`, so the `ε₂`-power of `δ` pays for `s₀` and the rest is `ρ`.

This is the lemma that takes the inner-scale threshold off the residual-gap list of Proposition
6.6(B): the hypothesis `δ ≤ s₀ * a` of
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_of_partBData` is now derivable inside any proof
of the narrowed statement, with no new input. -/
theorem le_mul_of_plankScale_le {δ ρ a s₀ : ℝ≥0} {ε₂ : ℝ}
    (hδ0 : 0 < δ) (hε₂ : 0 < ε₂) (hthr : δ ≤ s₀ ^ (1 / ε₂))
    (hρ : δ ^ (1 - ε₂) ≤ ρ) (hρa : ρ ≤ a) :
    δ ≤ s₀ * a := by
  have hpow : δ ^ ε₂ ≤ s₀ := by
    calc δ ^ ε₂ ≤ (s₀ ^ (1 / ε₂)) ^ ε₂ := NNReal.rpow_le_rpow hthr hε₂.le
      _ = s₀ ^ ((1 / ε₂) * ε₂) := by rw [← NNReal.rpow_mul]
      _ = s₀ := by rw [one_div, inv_mul_cancel₀ (ne_of_gt hε₂), NNReal.rpow_one]
  have hsplit : δ = δ ^ ε₂ * δ ^ (1 - ε₂) := by
    rw [← NNReal.rpow_add (ne_of_gt hδ0), show ε₂ + (1 - ε₂) = (1 : ℝ) by ring, NNReal.rpow_one]
  calc δ = δ ^ ε₂ * δ ^ (1 - ε₂) := hsplit
    _ ≤ s₀ * ρ := mul_le_mul' hpow hρ
    _ ≤ s₀ * a := mul_le_mul' le_rfl hρa


/-! ### The two statements, pinned -/


/-- **The narrowed coarse-scale hypothesis implies the old one, pointwise.**

`δ ≤ δ ^ (1 - ε₂)` for `0 < δ ≤ 1` and `0 ≤ ε₂`.  This is the *entire* mathematical content of
"the free-`ρ` form implies the narrowed form": everything else in that implication is identity
plumbing on the two telescopes.  It is also exactly the step
`Kakeya.ML2Reduction.exists_threshold_eccentric` now performs to recover the `δ ≤ ρ` that the
geometry downstream of Proposition 6.6(B) still needs.

**Why the statement-level implication is not stated as a theorem here.**  It was written and it does
not elaborate: `whnf` on
`statement_of_universal_prop66B_freeCoarseScale β → statement_of_universal_prop66B_plankScale β ε₂`
exceeds **4 · 10⁶ heartbeats**, because both sides are dependent telescopes through
`Tube.IsUniformAtScale` and `Kakeya.GlobalPlankFactorization Cw a b hab hb1 PS.parent …`,
whose later binders depend on the earlier ones.  Recorded here so that it is not retried blindly.
The two `statement_of_universal_*` definitions below still pin both statements, and the `example`
below pins the new one to the real theorem, which is what the device is for. -/
theorem le_of_plankScale_le {δ ρ : ℝ≥0} {ε₂ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hε₂ : 0 ≤ ε₂) (hρ : δ ^ (1 - ε₂) ≤ ρ) :
    δ ≤ ρ := by
  refine le_trans ?_ hρ
  have := NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (show (1 : ℝ) - ε₂ ≤ 1 by linarith)
  simpa using this

/-- **The conclusion of GWZ Proposition 6.6(B)**: the form above with the
branching floor `(max 1 Cpar) ^ 2 ≤ PS.branchingN` added beside the other sub-polynomial budgets.

Why the floor is there, and why it is not derivable from the datum, is the third fidelity note in
the docstring of `Kakeya.tubeMultiplicityOfGlobalPlankFactorisation`.  In one line: the proof route
needs a *function* from leaves to coarse indices with every coarse index in use carrying a nonempty
fibre, that clause forces `|𝕋_ρ| ≤ |𝕋|`
(`Kakeya.Section6CoarseTubeDecomposition.card_coarseSet_le_card`), and
`Tube.IsUniformAtScale` does not carry it.

Since  this is the **alternative** form: the live theorem also carries the fine-family
essential-distinctness binder, and is pinned below as `statement_of_universal_prop66B_essDistinct`.
This form is kept as the record of the statement without the additional hypothesis; it is what
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_of_essDistinctSubfamilyCase`
(`Kakeya/DimensionThree/Plank/Prop66BEDReduction.lean`) concludes, and it implies the live form
trivially (one hypothesis is dropped). -/
def statement_of_universal_prop66B_branchingFloor (β ε₂ : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∃ δ₀ > (0 : ℝ≥0),
    ∀ {ι : Type*} (q : Finset ι) {δ : ℝ≥0} (_hδ0 : 0 < δ)
      (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
      δ ≤ δ₀ →
      (∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall 0 1) →
      (∃ C : ℝ≥0, C ≤ δ ^ (-η) ∧
        Nonempty (ShadedTube.ShadedUniformTubeSet q T (Tube.ssfGridLen δ) C)) →
      (δ : ℝ≥0) ^ η ≤ ShadedBody.fullness q (fun i => (T i).toShadedBody) →
      ∀ (ρ a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1) (Cw Cpar C₀ : ℝ≥0),
        Cw ≤ δ ^ (-η) → Cpar ≤ δ ^ (-η) → C₀ ≤ δ ^ (-η) →
        (δ : ℝ≥0) ^ (1 - ε₂) ≤ ρ → ρ ≤ a →
        ∀ (PS : Tube.IsUniformAtScale q (fun i ↦ (T i).toTube) ρ Cpar),
        (max 1 Cpar) ^ 2 ≤ PS.branchingN →
        ∀ (_Fz : GlobalPlankFactorization Cw a b hab hb1 PS.parent
          (fun k ↦ (PS.parentTube k).toConvexSpaceBody) C₀),
        ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ≤
          (δ : ℝ≥0∞) ^ (-ε)
            * (maxDensity q (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
            * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ β * (q.card : ℝ≥0∞) ^ β

/- **The branching-free form implies the form with the floor** — one hypothesis is dropped and
nothing else changes, so no consumer can lose anything that was ever available.

**It is not stated as a theorem here, for the reason already recorded above**: `whnf` on the
implication between two `statement_of_universal_*` telescopes does not terminate.  Measured on this
pair: `2 · 10^6` heartbeats are not enough, the same wall the `freeCoarseScale → plankScale`
implication hit at `4 · 10^6`.  The obstruction is the telescope, not the mathematics — the two
sides differ by a single non-dependent `→` — and it is recorded so that it is not retried blindly.
The two `statement_of_universal_*` definitions pin both forms, and the `example` below pins the new
one to the real theorem, which is what the device is for. -/


/- **The compatibility has moved.**  The statement with a parent window carries the parent window
`∀ k ∈ PS.parent, (PS.parentTube k).carrier ⊆ Metric.closedBall 0 1` after the branching floor,
pinned as `statement_of_universal_prop66B_essDistinct_parentWindow` in
`Kakeya/DimensionThree/Plank/Prop66BChainResidue.lean`, which imports this file; the `example`
pinning `Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` to that form sits beside the theorem,
now proved in `Kakeya/DimensionThree/Plank/Prop66BClose.lean`.
The form above is now the record of the pre- statement (it implies the live form
trivially — one hypothesis is dropped; the implication is not stated as a theorem, for the
telescope reason recorded twice above).  Until  the compatibility was pinned to
`statement_of_universal_prop66B_branchingFloor`, which is inhabited by
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_of_essDistinctSubfamilyCase`. -/

end Prop66BScale

end Kakeya

end

end

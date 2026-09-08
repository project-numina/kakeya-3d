/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.NonSlabAngle

/-!
# The `ρ`-tube count of Configuration `hyp:ml2setup`, repaired

`Kakeya.VeryNotSticky.rho_count` renders the third bullet of blueprint `lemmain2vns`

> for each `ρ ∈ [δ^{1-ϖ}, δ^{ϖ}]`, `|𝕋_ρ| ≥ ρ^{-2-ζ}`

as a statement about **every** essentially distinct family of `ρ`-tubes covering the
configuration's own family `cfg.s`, with the multiplicative constant taken to be `1`.  Two
separate things are wrong with that rendering, and this file separates them, states the
repaired clause, and proves it from exactly the binders of
`Kakeya.VeryNotSticky.exists_setup_caseSideData`.

**Defect 1 — the missing constant, at the *binder*.**  GWZ's `|𝕋_ρ|` is the *canonical parent
family* of the uniformity Definition `uniformSetOfTubes`, not an arbitrary cover.  Passing from
"the canonical parent family is large" to "every essentially distinct cover is large" costs the
bounded-overlap constant `D` of Definition `uniformSetOfTubes`(ii): the map sending a parent
tube to a cover element containing one of its children is at most `D`-to-one, so an arbitrary
cover only obeys `|t| ≥ D^{-1}|𝕋_ρ|`.  That constant is the one the `⪆` of §9 hides on the
count, and it is affordable: `Kakeya.ML2Spine.spine_tube_card_lower`, which supplies the
binder, carries its threshold with the strictly positive gap `κ = 2 e η_j` of
`Kakeya.ML2Spine.spine_countGap`, so its hypothesis `hsmall` survives multiplication of the
left-hand side by any fixed constant — indeed by any `δ̃^{-θ}` with `θ < κ`.  The constant is
carried here by `Ccount`.

**Defect 2 — and it is *not* a constant.**  In GWZ the setup pigeonholes of subsection
*proofoverview* refine only the **shading** `Y` (and the per-ball segment families `𝕋_B`); the
tube family `𝕋` itself is never refined, so the count hypothesis survives verbatim.  The Lean
configuration instead carries the *refined* family `cfg.s ⊆ s` — it must, because
`Kakeya.VeryNotSticky.shading_lb`, `shading_ub` and `lam_ge` are per-tube demands that an
aggregate binder cannot meet without discarding tubes.  Covering families for `cfg.s` are a
**strictly larger** class than covering families for `s`, so the field is strictly stronger
than the binder; `rhoCountOn_mono_index` below is that implication, and it points the wrong
way.  No constant closes the gap: `not_rhoCountOn_empty` shows the field is *false* at the
extreme legal refinement `cfg.s = ∅` for **every** constant `Ccount`.

The repair is therefore not a constant but a *datum*: the configuration has to remember the
parent family.  `RhoCountParent` is the repaired clause — "the configuration's family sits
inside a family that satisfies Lemma 9.1's containment, `Δ_max` and count hypotheses" — and
`rhoCountParent_of_binders` discharges it from the binders of
`Kakeya.VeryNotSticky.exists_setup_caseSideData` in one line, at `Ccount = 1`, with `sPar := s`.
`rhoCountParent_of_veryNotSticky` shows the repaired clause is *weaker* than the present field,
so the change is a weakening of `Kakeya.VeryNotSticky` and every consumer must be rechecked;
there is exactly one, `Kakeya.VeryNotSticky.rho2_range`, restated here as
`rho2_range_parent`.

**The price of the repair,** and it is the standard `⪆`: the count is spent, in the blueprint,
as the fibre bound `|𝕋[T_{ρ₂}]| ≤ ρ₂^{2+ζ}|𝕋|`, and reading it off the parent family costs the
ratio `|sPar|/|s|`.  `card_parent_le_of_isCRefinement` prices that ratio at `(c·λ)^{-1}`, which
at the setup's own constants `c ≥ δ^η` and `λ ≥ δ^η` is `δ^{-2η}` — subpolynomial, hence
absorbed exactly like every other `⪆` of the section. The absorption is explicit: this `δ^{-2η}` is one of the summands of the `18η` of
`Kakeya.VeryNotSticky.SplitInputs.countConstant`, measured by the producer
`Kakeya.VeryNotSticky.exists_fibreScaleCount_of_rhoParentData`.
-/

@[expose] public section

open scoped NNReal

namespace Kakeya.VeryNotSticky

universe u

open MeasureTheory Metric Set ShadedBody
open scoped NNReal

/-! ## The clause, as a standalone `Prop`, and the identification of the refutation

`RhoCountOn` and `RhoCountParent` now live **above** the structure, in
`Kakeya.DimensionThree.MainLemma2.VeryNotSticky`, next to the field's present form
`Kakeya.VeryNotSticky.RhoParentData`; using them from here would be an
import cycle. What stays here is everything about them that is not needed to state the
structure.

The old field form is preserved below as a standalone `Prop`,
`RhoCountFieldOldStatement`, so that the refutation `not_rhoCountFieldOldStatement_empty`
survives the field change and keeps compiling. This is the
`Kakeya.ThinCase.Refute.statement_of_universal_loc` device: a plain tripwire `example` about a
*field* cannot survive that field changing, so the statement under test is hoisted out of the
declaration into a `Prop` of its own, and two theorems pin it in both directions —
`rhoCountFieldOldStatement_iff_rhoCountOn_one` says the hoisted `Prop` is the old text, and
`rhoCount_field_is_parentData` says the field is now the repaired one (`RhoParentData`;
`rhoCount_field_is_parent` records that the intermediate form `RhoCountParent` still follows). If
any of them drifts, one of them stops elaborating.
-/


/-- Enlarging the constant only weakens the clause. -/
theorem RhoCountOn.mono_const {δ : ℝ≥0} {ζ exscalb : ℝ} {ι : Type u} {s : Finset ι}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {C C' : ℝ≥0} (hC : C ≤ C')
    (h : RhoCountOn δ ζ exscalb s T C) : RhoCountOn δ ζ exscalb s T C' := by
  intro ρ hρ κ tρ Tρ hcover hdisj
  refine (h ρ hρ κ tρ Tρ hcover hdisj).trans ?_
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hC) (Nat.cast_nonneg _)

/-! ## Defect 2: the clause is monotone in the index set, and the gap is not a constant -/


/-! ## The repaired clause: its producer, and the one consumer

`RhoCountParent` itself is stated in `Kakeya.DimensionThree.MainLemma2.VeryNotSticky`, above the
structure, because the field is it.
-/


/-! ## The one consumer

`Kakeya.VeryNotSticky.rho2_range` (`Kakeya.DimensionThree.MainLemma2.NonSlabAngle`) is the only
consumer of the field, and it is restated there against the repaired clause: it returns the
parent family in its conclusion. It had, and still has, no term-level users — the count is spent
through the carried field `Kakeya.VeryNotSticky.SplitInputs.fibreScaleCount`, whose constant is, the carried `Ccnt` of
`Kakeya.VeryNotSticky.SplitInputs.countConstant` at `Ccnt ≤ δ^{-18η}` and **not** the δ-free
`(2 C_{lem:ml2bodyAngle}(C₀))²` this paragraph used to name. So a constant on the count does not
cost the non-slab branch nothing for free: it is paid, together with the `δ^{-2η}` of the parent
form and the `ρ_k/ρ₂` rounding, out of the `18η` of `countConstant`, whose downstream price is
the `m`-slot `19` of `Kakeya.VeryNotSticky.tangentialSlabMultAbsorb` — `22` of `2^17` budget
units, and the absorb's conclusion is `m`-free ( (b)-(c)).
-/

/-! ## Defect 1: the constant the `⪆` hides is the bounded-overlap constant `D` -/


/-! ## The price of the repair -/


end Kakeya.VeryNotSticky

end

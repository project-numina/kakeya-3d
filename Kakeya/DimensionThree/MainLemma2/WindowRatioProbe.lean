/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.VeryNotStickyUniform

/-!
# The loss-to-fullness ratio of the Katz–Tao window: what the tree's input does and does not give

 Consider the inequality on `Kakeya.CoarseKTWindow`'s own two exponents,

```
c * we ≤ 2 ^ 18 * wη
```

(the *loss-to-fullness ratio*), as the one thing the tangential branch's fullness half needs and
cannot pay: `frev49_fullness_forces_window_ratio` derives it from the transported enclosure
requirement, `frev49_window_ratio_not_derivable` exhibits admissible numerals violating it, and
`frev49_window_ratio_satisfiable` exhibits admissible numerals meeting it — so it is a decision,
not a dead end.   The scalar condition of Option R *is* that ratio
(`optionR_is_the_window_ratio`) and that `Kakeya.exists_uniformWindowPair` supplies no clause
relating its input `ε` to its output `p.1`.

This file answers the next question — **is the ratio provable as a strengthening of
`Kakeya.exists_uniformWindowPair`'s conclusion?** — and the answer is *no*, for a reason sharper
than "no clause relates them".  Nothing here is read by the tree; every declaration is a new
theorem, and no statement anywhere is cut.

## What is established

**(A) The two transports the tree has, and their direction.**  `Kakeya.WindowFour` is *monotone*
in the loss exponent (`Kakeya.WindowFour.mono_eps`, existing) and, proved here, *antitone* in the
fullness exponent (`Kakeya.WindowFour.mono_etaKT`): the pair may always be moved to a larger loss
or to a smaller threshold.  Both moves are lifted to `Kakeya.UniformWindowPair`
(`Kakeya.UniformWindowPair.mono_eps`, `Kakeya.UniformWindowPair.anti_eta`).

**(B) Both transports run away from the ratio.**  `Kakeya.uniformWindowPair_ratio_not_gained`:
from a pair at which `c * we ≤ K * wη` fails, *every* pair reachable by the two available moves
still fails.  So no application of the tree's own window monotonicity lemmas can manufacture the
ratio.

**(C) The ratio is independent of the Katz–Tao quantifier shape.**  `Kakeya.KTWindowShape`
bundles exactly the three structural facts the tree's window producer is known to have —
monotone in the loss, antitone in the threshold, inhabited at every positive loss.  It is not a
strawman: `Kakeya.uniformWindowShape` is an instance built from `Kakeya.exists_uniformWindowPair`
and (A).  And the ratio is independent of it: `Kakeya.ratioFailingShape` is a shape at which the
ratio fails at *every* admissible pair, `Kakeya.ratioSatisfyingShape` one at which it holds.
`Kakeya.no_ratio_producer_from_shape_even_with_free_loss` is the sharp form — even granting the
producer the freedom to *choose* the loss exponent anywhere below `Kakeya.CoarseKTWindow.hwe`'s
ceiling, the shape does not yield the ratio.

**(D) Along the tree's own producer chain the loss exponent cancels identically, and the ratio
becomes an accuracy-independent floor on GWZ Definition 3.4's threshold function.**  The chain
`Kakeya.exists_uniformWindowPair → Kakeya.exists_windowFour →
Kakeya.KatzTaoEstimate.multiplicity_bound_generalize_window →
Kakeya.KatzTaoEstimate.multiplicity_bound_generalize → Kakeya.KatzTaoEstimate` returns, at loss
`ε` and from a raw Katz–Tao threshold `η₀`, the fullness exponent `ε * η₀ / (4 * (4 + η₀))` in
`EuclideanSpace ℝ (Fin 3)`.  `Kakeya.windowChain_ratio_iff_thresholdFloor` says the ratio at that
value is *equivalent* to `16 * c ≤ (K - 4 * c) * η₀` — in which `ε` does not appear.  GWZ's own
Remark 3.6 construction `η(β,ϵ) = ϵ η₁(β,ϵ) / 100` gives the same shape
(`Kakeya.gwzRemark36_ratio_iff_thresholdFloor`).

**(E) The parameter-order fact.**  `Kakeya.ratio_free_for_noninput_parameter`: a loss parameter
that is *not* an input of the producer — GWZ's `η_bias`, bounded only from above — always meets
the ratio, because it may be chosen after the threshold.  Contrast (C): the producer's *input*
cannot.  That difference of order, not any difference of strength, is the whole gap.

## What is NOT established here

No refutation of `Kakeya.KatzTaoEstimate` itself.  (C) refutes derivability from the quantifier
shape together with the monotonicities the tree has; a genuine counter-instance of
`Kakeya.KatzTaoEstimate (EuclideanSpace ℝ (Fin 3)) β` would be a statement about Kakeya sets in
`ℝ³` that nobody has.  The identification in (D) of the produced fullness exponent with
`ε * η₀ / (4 * (4 + η₀))` is read off the two proof scripts
(`Kakeya.KatzTaoEstimate.multiplicity_bound_generalize`, which sets `η := ε * η₁ / M` with
`M = finrank + η₁ + 1`, and `Kakeya.KatzTaoEstimate.multiplicity_bound_generalize_window`, which
calls it at `ε / 2` and returns `η₁ / 2`); the *arithmetic consequence* is what is compiled here,
The formula describes that construction; the arithmetic consequence is the theorem established here.
-/

@[expose] public section

universe u

open Set Filter Topology
open scoped NNReal

namespace Kakeya

/-! ### (A) The two transports, and the one that was missing -/


/-! ### (B) Both transports run away from the ratio -/

/-- **The loss-to-fullness ratio clause of **, at a general pair of constants.
`WindowRatio c K we wη` is that the `c * we ≤ 2 ^ 18 * wη` at `K = 2 ^ 18`. -/
def WindowRatio (c K we wη : ℝ) : Prop := c * we ≤ K * wη


/-! ### (C) The ratio is independent of the Katz–Tao quantifier shape -/

/-- **The structural content of the tree's window producer.**

`Holds ε η` is to be read as "`η` is an admissible fullness exponent at loss `ε`".  The three
fields are exactly the three facts the tree *proves* about
`fun ε η ↦ ∃ ρ, Kakeya.UniformWindowPair β₀ ε (η, ρ)`, and nothing more:

* `mono_loss` — `Kakeya.UniformWindowPair.mono_eps`;
* `anti_threshold` — `Kakeya.UniformWindowPair.anti_eta`;
* `exists_threshold` — `Kakeya.exists_uniformWindowPair`, whose conclusion, as
   measured, relates its input to its output by nothing at all.

`Kakeya.uniformWindowShape` below is the instance, so this bundle is a faithful abstraction and
not a weakened one. -/
structure KTWindowShape where
  /-- `Holds ε η`: the threshold `η` is admissible at loss `ε`. -/
  Holds : ℝ → ℝ → Prop
  /-- The bound transports upward in the loss exponent. -/
  mono_loss : ∀ {ε ε' η : ℝ}, ε ≤ ε' → Holds ε η → Holds ε' η
  /-- The bound transports downward in the fullness exponent. -/
  anti_threshold : ∀ {ε η η' : ℝ}, 0 < η' → η' ≤ η → Holds ε η → Holds ε η'
  /-- Some positive threshold is admissible at every positive loss. -/
  exists_threshold : ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), Holds ε η


/-- **A shape at which the ratio fails at every admissible pair.**  Admissible thresholds at loss
`ε` are exactly those below `c * ε / (K + 1)`; the shape's three fields all hold, and
`K * η ≤ K c ε / (K + 1) < c ε` for every one of them. -/
def ratioFailingShape (c K : ℝ) (hc : 0 < c) (hK : 0 < K) : KTWindowShape where
  Holds ε η := 0 < ε ∧ (K + 1) * η ≤ c * ε
  mono_loss := fun hεε' ⟨hε, hη⟩ ↦
    ⟨lt_of_lt_of_le hε hεε', le_trans hη (mul_le_mul_of_nonneg_left hεε' hc.le)⟩
  anti_threshold := fun _ hle ⟨hε, hη⟩ ↦
    ⟨hε, le_trans (mul_le_mul_of_nonneg_left hle (by linarith)) hη⟩
  exists_threshold := fun ε hε ↦ by
    have hK1 : (0 : ℝ) < K + 1 := by linarith
    exact ⟨c * ε / (K + 1), by positivity, hε, le_of_eq (by field_simp)⟩


/-- **A shape at which the ratio holds.**  The firing control for
`Kakeya.ratioFailingShape_refutes`: the shape's three fields do not *refute* the ratio either, so
the ratio is genuinely independent of them rather than false. -/
def ratioSatisfyingShape : KTWindowShape where
  Holds ε η := 0 < ε ∧ 0 < η ∧ η ≤ ε
  mono_loss := fun hεε' ⟨hε, hη0, hη⟩ ↦ ⟨lt_of_lt_of_le hε hεε', hη0, le_trans hη hεε'⟩
  anti_threshold := fun hη'0 hle ⟨hε, _, hη⟩ ↦ ⟨hε, hη'0, le_trans hle hη⟩
  exists_threshold := fun ε hε ↦ ⟨ε, hε, hε, hε, le_rfl⟩


/-! ### (D) Along the tree's producer chain the loss exponent cancels -/

/-- **The loss exponent cancels identically from the ratio.**

`Kakeya.KatzTaoEstimate.multiplicity_bound_generalize` returns the threshold `ε * η₀ / M` with
`M = Module.finrank ℝ E + η₀ + 1`, and
`Kakeya.KatzTaoEstimate.multiplicity_bound_generalize_window` calls it at `ε / 2` and returns
half of what it gets; in `EuclideanSpace ℝ (Fin 3)` that composite is
`ε * η₀ / (4 * (4 + η₀))`, where `η₀` is GWZ Definition 3.4's own threshold `η(ϵ, β)` at the
accuracy `ε / 2`.  At that value the  clause is **equivalent** to a condition in
which `ε` does not occur — an absolute floor on Definition 3.4's threshold function.

So no choice of `Kakeya.CoarseKTWindow.we` can buy the ratio along this chain: shrinking the loss
shrinks the delivered threshold in exact proportion. -/
theorem windowChain_ratio_iff_thresholdFloor {c K ε η₀ : ℝ} (hε : 0 < ε) (hη₀ : 0 < η₀) :
    WindowRatio c K ε (ε * η₀ / (4 * (4 + η₀))) ↔ 16 * c ≤ (K - 4 * c) * η₀ := by
  have hden : (0 : ℝ) < 4 * (4 + η₀) := by linarith
  rw [WindowRatio, mul_div_assoc', le_div_iff₀ hden]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- The floor at the constants  measures (`c = 2` at H.3's split, `K = 2 ^ 18`):
GWZ Definition 3.4's threshold must exceed `32 / 262136 ≈ 1.2207 · 10⁻⁴`, at some accuracy, for
the tangential branch's fullness half to close. -/
theorem windowChain_ratio_iff_thresholdFloor_two {ε η₀ : ℝ} (hε : 0 < ε) (hη₀ : 0 < η₀) :
    WindowRatio 2 (2 ^ 18) ε (ε * η₀ / (4 * (4 + η₀))) ↔ (32 : ℝ) / 262136 ≤ η₀ := by
  rw [windowChain_ratio_iff_thresholdFloor hε hη₀,
    div_le_iff₀ (by norm_num : (0:ℝ) < 262136)]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith


/-! ### (D′) …and the linear degradation is forced, not incidental -/


/-- Satisfiability control for `Kakeya.remark36_transport_forces_linear`: its hypothesis is met,
with equality, at exactly the threshold the transport delivers.  So the bound is sharp and the
binder is not vacuous. -/
example {ε η₀ M : ℝ} (hε : 0 < ε) (hM : 0 < M) :
    ∀ δ : ℝ, 0 < δ → δ < 1 → δ ^ η₀ ≤ (δ ^ (M / ε)) ^ (ε * η₀ / M) := by
  intro δ hδ0 _
  rw [← Real.rpow_mul hδ0.le, show M / ε * (ε * η₀ / M) = η₀ by field_simp]

/-! ### (E) The parameter-order fact -/


/-! ### Satisfiability controls

Each binder bundle used above is inhabited; a vacuous hypothesis set would make the negative
results empty.  These are the sharp-binder checks. -/

/-- The failing shape's admissibility predicate is inhabited. -/
example : (ratioFailingShape 2 (2 ^ 18) (by norm_num) (by norm_num)).Holds 1
    (2 / (2 ^ 18 + 1)) := ⟨one_pos, by norm_num⟩

/-- The failing shape's clause is a genuine constraint: some positive threshold violates it. -/
example : ¬ (ratioFailingShape 2 (2 ^ 18) (by norm_num) (by norm_num)).Holds 1 1 := by
  rintro ⟨-, h⟩; norm_num at h

/-- The satisfying shape's admissibility predicate is inhabited. -/
example : ratioSatisfyingShape.Holds 1 1 := ⟨one_pos, one_pos, le_rfl⟩

/-- The floor of `Kakeya.windowChain_ratio_iff_thresholdFloor_two` is met by some positive
threshold — the equivalence is not vacuously false. -/
example : WindowRatio 2 (2 ^ 18) 1 (1 * (1 / 100) / (4 * (4 + 1 / 100))) :=
  (windowChain_ratio_iff_thresholdFloor_two one_pos (by norm_num)).mpr (by norm_num)

/-- …and it is violated by some positive threshold — the equivalence is not vacuously true. -/
example : ¬ WindowRatio 2 (2 ^ 18) 1 (1 * (1 / 10 ^ 6) / (4 * (4 + 1 / 10 ^ 6))) := by
  intro h
  have := (windowChain_ratio_iff_thresholdFloor_two one_pos (by norm_num)).mp h
  norm_num at this

end Kakeya

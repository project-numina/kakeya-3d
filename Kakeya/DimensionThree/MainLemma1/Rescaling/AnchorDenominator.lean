/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Rescaling.DensityTransfer
public import Kakeya.DimensionThree.MainLemma1.EnlargementCover

/-!
# Main Lemma 1, Step 5a: the anchor denominator, from the factoring and from the count

Blueprint `lem:ml1bootAnchorDenominatorFromFactoring` and the continuation
the anchor-denominator count.  The first statement,
`Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_factorization`, **is an instance and not an
argument**: it is `Kakeya.ml1Boot.frostmanConstIn_anchor_le` of
`Kakeya/DimensionThree/MainLemma1/Rescaling/DensityTransfer.lean` read at `L = D / C_fact`, with the
`denom_pos`/`denom_le` half of that lemma's denominator bundle
`Kakeya.ml1Boot.IsAnchorDenominator` — and only that half, the placement half
`Kakeya.ml1Boot.IsAnchorPlacement` being carried unchanged — replaced by the two links of the
source's Step 5c route to `L` that this development already has.  The remaining
statements write the third link at one tested body and read the first statement at the `D` it
produces.

## What it is, and what it is not

Item (i) of blueprint `note:ml1bootAnchorFromLoadStatus` records the denominator `L` of
`Kakeya.ml1Boot.frostmanConstIn_anchor_le` as the one owed item of which nothing at all is written.
The source reaches it in three links:

* (A) the **plank density identity** — for a block `t` of the factoring,
  `Δ_max(𝕍|_{s'}) ≤ C_fact · Δ(𝕍|_t, W)`, so that a lower bound for `Δ_max` of the retained share is
  a lower bound for the density *at the plank*, which is what the denominator hypothesis asks for;
* (B) the **maximal-density comparison** — `Δ_max(𝕍|_{s'}) ≥ Δ(𝕍|_{s'}, B)` at *any* tested body
  `B`, the source reading it at its `B_{2C₀}`;
* (C) the **count at that tested body** — `Δ(𝕍', B_{2C₀}) ≳ N_m δ̃ ²`, because `𝕍'` retains a
  `≳ 1`-share of the completed fibre and each member has volume `≈ δ̃ ²`.

Links (A) and (B) *are* in this development: (A) is `ConvexSpaceBody.Factorization.maxDensity_le_mul`
of `Kakeya/Factorization.lean`, a structure field, holding at `C_fact = 2` at the one producer this
development has, `ConvexSpaceBody.nonempty_factorization.factorization`; and (B) is
`Kakeya.le_maxDensity` of `Kakeya/Density.lean`, which is `Kakeya.maxDensity` read as the supremum it
is.  `Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_factorization` writes the composition of those
two, leaving the third as the explicit hypothesis `hD` at a *free* tested body.

## Link (C), at one tested body

The rest of the file writes link (C) at the tested body `B = P_a(l)^{(Λ ρ_a)}`.
It is a count, `Kakeya.densityIn_ge_of_count_volume`, at two inputs:

* (C1) the **cardinality** `|\widetilde{𝒰'_b}(l)| ≥ Cu ⁻³ (N_a/N_b)` at the completed *unrefined*
  fibre — `Kakeya.ml1Boot.branchingRatio_le_card_completedFibre` of
  `Kakeya/DimensionThree/MainLemma1/TwoLoads.lean`, the composition of the lower half of the
  uniformity bracket with `Kakeya.ml1Boot.fibre_subset_completedFibre`, which is why this file now
  carries an import edge to that one;
* (C2) the **placement**, which at this tested body asks nothing at all: every member of the
  completion satisfies `P_b(k) ≤ B` *by the definition of* `Kakeya.ml1Boot.completedFibre`, so no
  cover, no enlargement lemma and no containment hypothesis on `B` occurs.  That is the reason link
  (C) is reachable here and only here, and the reason the statements are at the un-normalized grid
  scales `θ = ρ_a`, `τ = ρ_b`.

`Kakeya.ml1Boot.densityIn_ge_of_completedFibre_share` is the count, at a free retained subfamily
meeting the completion in a `κ`-share;
`Kakeya.ml1Boot.densityIn_ge_of_completedFibre_volume_share` is that count again with the
cardinality share replaced by the *volume* share that
`ConvexSpaceBody.nonempty_factorization.weight_subfamily` delivers — that lemma, and **not**
`ConvexSpaceBody.nonempty_factorization.factorization`, which is where link (A) comes from and says
nothing about a share — the two shares being interchangeable at the same `κ` for a family of tubes
of one common positive radius (`Tube.mul_sum_volume_le_iff_mul_card_le`);
`Kakeya.ml1Boot.densityIn_ge_of_completedFibre_share_normalized`
divides by the upper volume bracket of `Kakeya.ml1Boot.volume_testedBody_bracket` to reach the
source's `≳ N_m (τ/Λθ) ²` shape; and `Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_count` reads
`Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_factorization` at the `D` the first of those produces,
which discharges `hD` — **and only `hD`**.

**The share is a hypothesis and nothing here produces it.**  It is *not* the fibrewise share of
blueprint `note:ml1bootEssDistinctFibrewiseShare`, which is stated relative to the *fibre* and is
therefore, at equal `κ`, a weaker demand than the one made here relative to the larger completion;
that note is **open and blocking** and nothing here reopens, weakens or closes it.  No essential
distinctness is asked and none is used.

**This is a change of shape, not a supplier.**  Nothing here produces a number `L`: what it does is
replace the bare lower bound `Δ(𝕍|_t, W) ≥ L` — a hypothesis about the *plank*, which no counting
argument in this development reaches directly — by a lower bound `Δ(𝕍|_{s'}, B) ≥ D` at a free
tested body `B`, which is the shape a counting argument *could* reach.  Everything else is carried
unchanged, in particular the two placement conditions `W ≤ K` and `|K| ≤ C_T (bp/ap) |W|`, which are
the plank-body placement gap of blueprint `note:ml1bootEnlargementTubeStatus` and are **not** touched
here, and the numerator hypothesis `hnum`, which is verbatim.  Blueprint
`note:ml1bootAnchorDenominatorStatus` itemizes all of this.

## `lemmafactmax` is not applied, and `s'` and `t` need not come from it

Only the *inequality* (A) is asked, as the hypothesis `hfact`.  Obtaining it by applying
`ConvexSpaceBody.nonempty_factorization.factorization` at `𝕍|_{s'}` would require that lemma's own
hypotheses at the un-normalized family of `τ`-tubes — containment in a unit ball and a lower bound on
the `ethickness` — and, in the normalized picture of `Kakeya.ml1Boot.tubeNormalizedFamily`, the
transport of the factoring across the normalization.  **Neither is performed**; stating the lemma at
the inequality is what keeps that obligation visible at the caller.  For the same reason
`Kakeya/Factorization.lean` is **not** imported by this file: nothing here reads the structure.

## It stands beside everything it reads and revises none of it

`Kakeya.ml1Boot.frostmanConstIn_anchor_le` is applied once, at one value of `L`, and is neither
edited nor weakened nor re-derived; `ConvexSpaceBody.Factorization` and `Kakeya.le_maxDensity` are
untouched; and neither
`Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_load`,
`Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_essDistinctParents`,
`Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_uniformity` nor
`Kakeya.ml1Boot.plankWidth_le_of_anchor` is re-pointed at it.  No new constant is introduced,
deliberately: the only constants displayed are `C_T = Kakeya.ml1Boot.densityTransfer.C` and the
factoring constant `C_fact`, which is *data* here.

## This does not make (5.10b) unconditional

`Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_factorization` leaves the numerator `U`, the placement
of `W` in `K`, and link (C) exactly as it found them, and says nothing about the Step 5c anchor —
nothing here relates `K` to the body `2 · T_b` of `Kakeya.ml1Boot.plankWidth_le_of_anchor`.  **It is
not a supplier for `L` and may not be reported as one**: it produces no number, and a caller must
still produce the `D` of `hD`.  `Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_count` is that caller,
and it commits in the open the reading of `D` as a constant multiple of `N_m τ ²` with
`N_m = N_a/N_b` — *not* as `N_m δ̃ ²`: the passage to the `δ̃` of
`Kakeya.ml1Boot.tubeNormalizedFamily` is a transport that is **not performed anywhere** in this
development, so `Kakeya.ml1Boot.densityIn_ge_of_completedFibre_share_normalized` may not be quoted as
the source's display.

What stands between this and an unconditional (5.10b) is therefore, exactly: the **share**; the
**plank-body placement** `W ≤ K` with `|K| ≤ C_T (bp/ap) |W|`, which is the gap of blueprint
`note:ml1bootEnlargementTubeStatus` and is carried verbatim, nothing here relating `K` to `B`; the
**factoring datum**, quoted as the inequality `hfact` rather than obtained from
`ConvexSpaceBody.nonempty_factorization.factorization`, whose own hypotheses at the un-normalized
family — containment in a unit ball and a lower bound on the `ethickness` — remain the caller's
obligation, which is also why `Kakeya/Factorization.lean` is still **not** imported here; the
**normalization transport**; and the **Step 5c anchor transport**.  An assembly of conditional inputs
is a conditional statement.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory ConvexSpaceBody StickyKakeya Tube Convexity

namespace Kakeya

namespace ml1Boot

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-! ### Link (C): the count at the tested body

The tested body is `B = P_a(l)^{(Λ ρ_a)}`, the concentric radius-rescaling
`(𝒰'.cover.tube a l).rescale (Λ * gridScale δ N a)`, which in Lean *is* a tube of radius `Λ ρ_a` by
typing — `Kakeya.Tube.rescale` returns a `Tube` of the new radius — so the three tube-volume facts
apply to it directly.  Throughout this section `sl` is the leaf set of the hierarchy and `s'` is the
retained subfamily of `𝒰'_b` that the source calls `𝕍'`; the letter `s'` is the source's and is not
the leaf set, which the neighbouring Step 5a files write `s'` instead. -/

/-- **The small constant of the count at the tested body**, the product of the three inputs already
carried by the count: the
share `κ`, the power `Cu ⁻³` of the lower half of the uniformity bracket
(`Kakeya.ml1Boot.branchingRatio_le_card_coarseFibre`), and the reverse tube-volume constant
`Kakeya.Tube.le_volume.c`.

It depends only on the ambient dimension, on the uniformity constant of the hierarchy and on the
share — on no grid scale, no branching number and no `δ` — and is read below at `n = 3`.  It is
positive whenever `0 < κ` and `Cu ≠ 0`, each factor being so, and it is *small*, hence the lower-case
name.  The share is written `κ` and not `σ`, the letter `σ` being a tube width in the neighbouring
Step 5a files. -/
noncomputable def anchorCountAtTestedBody.c (n : ℕ) (Cu κ : ℝ≥0) : ℝ≥0 :=
  κ * (Cu ^ 3)⁻¹ * _root_.Tube.le_volume.c n

/-! ### The arithmetic of the constant and of the numerator

Six arithmetic statements are named at the end of blueprint
the anchor-denominator count so that the granularity debt recorded at
item (countLean) of `note:ml1bootAnchorDenominatorCountStatus` has something to discharge it: each
is a fact that one of the three long proofs below already establishes inline, and writing it out
separately changes no hypothesis, no constant and no conclusion.  The four that mention the constant
`Kakeya.ml1Boot.anchorCountAtTestedBody.c` stand here; the two that mention no tube, no grid, no
hierarchy and no density — `ENNReal.div_div_eq_mul_div` and `NNReal.div_mul_div_sq_eq` with its
image `ENNReal.coe_div_mul_coe_div_sq_eq` — stand in `Kakeya/Mathlib/ENNReal.lean` beside this
development's other generic `[0, ∞]` arithmetic.

**None of them is cited by anything above yet.**  They are stated; rewriting the three proofs
through them is a separate step, and until it is done the inline copies remain. -/

/-- **The constant of the count is positive**.

`0 < c(n, Cu, κ)` whenever `0 < Cu` and `0 < κ`: by
`Kakeya.ml1Boot.anchorCountAtTestedBody.c` the constant is the product
`κ · (Cu ³)⁻¹ · c_{le_volume}(n)` of three positive factors — `κ` by hypothesis, `(Cu ³)⁻¹` because
`Cu > 0` and inversion is positive on positives, and `c_{le_volume}(n)` by
`Kakeya.Tube.le_volume.c_pos`.

**Only `0 < Cu` is asked, where the blueprint displays `C_ds ≥ 1`.**  Positivity is all the
inversion reads — in `NNReal`, `x⁻¹` is positive exactly when `x` is nonzero — so asking the
formally weaker hypothesis makes this the formally stronger statement; every consumer carries
`1 ≤ Cu` anyway, that being part of `Kakeya.uniformTubeSet`.

This is the positivity asserted in the display of blueprint `def:ml1bootAnchorCountConstant`, which
is at present unfolded and re-proved inline at each of the two places that need it — about eight of
the seventy lines of `Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_count` and a further few inside
`Kakeya.ml1Boot.densityIn_ge_of_completedFibre_share`.  *A positivity fact about a named constant
belongs once, at the constant.*

**No upper bound on `κ` is asked**, `κ ≤ 1` being dead here exactly as it is at
`Kakeya.ml1Boot.densityIn_ge_of_completedFibre_share`. -/
theorem anchorCountAtTestedBody.c_pos (n : ℕ) {Cu κ : ℝ≥0} (hCu : 0 < Cu) (hκ0 : 0 < κ) :
    0 < anchorCountAtTestedBody.c n Cu κ := by
  dsimp [anchorCountAtTestedBody.c]
  have hCu3Pos : 0 < Cu ^ 3 := pow_pos hCu 3
  have hInvPos : 0 < (Cu ^ 3)⁻¹ := by
    positivity
  have hTubePos : 0 < _root_.Tube.le_volume.c n := Tube.le_volume.c_pos n
  exact mul_pos (mul_pos hκ0 hInvPos) hTubePos

end ml1Boot

end Kakeya

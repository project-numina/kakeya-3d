/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.SlabFibreFrostmanReduction
public import Kakeya.DimensionThree.Plank.InnerConflictDegree
public import Kakeya.DimensionThree.Plank.EDWeightedExtraction
public import Kakeya.DimensionThree.Plank.GlobalPlankFactorizationEstimate
public import Kakeya.Tube.EssentiallyDistinctReduction
/-!
# Essential distinctness and the density budget in Proposition 6.6(B)

GWZ Definition 2.1(ii) at `ρ = δ` makes a GWZ-uniform family of `δ`-tubes
essentially distinct. The explicit fine-family hypothesis in Proposition
6.6(B) expresses this part of uniformity. The density factor
`Δmax(T) ^ (1 - β)` separately accounts for repetition without imposing a
maximal-density bound on the fine family.

The proof through `factoringAndMultPropGlobal_of_remark53` restricts essential
distinctness to a fibre and uses it in `exists_inner_plank_conflict_degree_bound`.
This controls the conflict degree of the inner normalized plank family,
which is extracted to satisfy the essential-distinctness hypothesis of
`PlankEstimateAtMasterScaleWithDensity`. A weaker `IsEDUpToMult` hypothesis
at multiplicity `M` gives degree `M + (M + 1) * d`.

`multiplicity_bound_transfer_of_massShare` transfers the bound from `u ⊆ q`
with shade-mass loss `L` when
`L * Δmax(u) ^ (1 - β) * |u| ^ β ≤ Δmax(q) ^ (1 - β) * |q| ^ β`.
It introduces no additional power of `δ`. For `N` copies of one tube,
`L = N`, `|u| = 1`, `|q| = N`, and `Δmax(q) = N`, giving equality by
`rpow_one_sub_mul_rpow`. GWZ Lemma 3.7 pays the same density loss through
a cardinality reduction. Selecting a maximal essentially distinct subfamily
alone gives a cardinality lower bound, whereas this transfer also needs the
upper bound `|u| ≲ |q| / Δmax(q)` together with mass retention.
-/

@[expose] public section

open scoped ENNReal

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace Kakeya

universe u

/-! ### The accounting: what the essential-distinctness loss must satisfy -/

/-- **The identity that makes GWZ 6.6(B) duplication-invariant.**

`N ^ (1 - β) * N ^ β = N`.  Under `N`-fold duplication of a family, `multiplicity`, `maxDensity`
and `card` are each multiplied by `N`, so the right-hand side of 6.6(B) is multiplied by
`N ^ (1 - β) * N ^ β`; this says that is exactly `N`, i.e. both sides move together.  It is also the
equality case of `Kakeya.multiplicity_bound_transfer_of_massShare`'s budget hypothesis. -/
theorem rpow_one_sub_mul_rpow (β : ℝ) {N : ℝ≥0∞} (h0 : N ≠ 0) (htop : N ≠ ⊤) :
    N ^ (1 - β) * N ^ β = N := by
  rw [← ENNReal.rpow_add _ _ h0 htop, sub_add_cancel, ENNReal.rpow_one]


/-! ### The packing cap without essential distinctness -/


/-! ### The exponent ledger of the deep branch, and the exact shortfall -/


/-! ### Why the deletion stops at GWZ Lemma 6.11, and does so structurally -/


/-! ### Option (3): the split at the 6.6(B) level, and what it needs -/

/-- **The 6.6(B)-level accounting: a `Δmax` multiplicity loss is paid by a cardinality-efficient
extraction, leaving exactly `Δmax ^ (1-β)`.**

Suppose a subfamily carries

* a **multiplicity transfer** `M ≤ L · D · M'` — the loss is one factor of the *ambient* maximal
  density `D`, at a sub-polynomial `L`; and
* a **cardinality-efficient** bound `N' · D ≤ N` — the subfamily is smaller by that same factor.

Then any 6.6(B)-shaped bound for the subfamily, `M' ≤ D' ^ (1-β) · A · N' ^ β`, transfers to the
whole family as `M ≤ L · D' ^ (1-β) · A · D ^ (1-β) · N ^ β`: the `D` of the multiplicity loss and
the `D ^ (-β)` of the cardinality drop combine to `D ^ (1-β)`, **which is exactly the factor
6.6(B) already carries**.  No hypothesis on `D` is required, and no `δ`-power is spent beyond `L`.

`A` stands for `(a/b) ^ β` and `D'` for the subfamily's own maximal density, which the extraction
also controls.

**Both inputs exist in this tree.**  `Kakeya.exists_random_subset` (`Kakeya/Probability.lean`) —
the random subset of GWZ Lemma 3.7 — returns, for a family of shaded `δ`-tubes in the unit ball,
a subfamily `s' ⊆ s` with

    (s'.card : ℝ) ≤ 2 * (s.card : ℝ) * (maxDensity s …)⁻¹          -- the cardinality-efficient half
    ConvexSpaceBody.IsKatzTao s' … (ENNReal.ofReal (δ ^ (-c)))     -- D' sub-polynomial
    multiplicityRLocal … s ≤ δ ^ (-c) * maxDensity s … * multiplicityRLocal … s'

which are precisely `hcard`, a bound on `D'`, and `hmult` with `L = δ ^ (-c)`.

**What is missing is packaging, not mathematics.**  `exists_random_subset` is consumed only inside
the proof of Lemma 3.7 (`Kakeya/PartialEstimates.lean`), and no exported statement exposes the
subfamily.  Making it available at the 6.6(B) call site is a re-export plus the discharge of its
hypothesis list (uniform tube volumes, a test family, and three smallness thresholds), all of which
Lemma 3.7's own proof already discharges for exactly this situation. -/
theorem multiplicity_bound_transfer_of_cardEfficient {β : ℝ} (hβ0 : 0 ≤ β)
    {M M' D D' N N' L A : ℝ≥0∞} (hD0 : D ≠ 0) (hDtop : D ≠ ⊤)
    (hmult : M ≤ L * D * M')
    (hcard : N' * D ≤ N)
    (hsub : M' ≤ D' ^ (1 - β) * A * N' ^ β) :
    M ≤ L * D' ^ (1 - β) * A * D ^ (1 - β) * N ^ β := by
  have hpow : D ^ β * N' ^ β ≤ N ^ β := by
    calc D ^ β * N' ^ β = (N' * D) ^ β := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hβ0]; ring
      _ ≤ N ^ β := ENNReal.rpow_le_rpow hcard hβ0
  calc M ≤ L * D * M' := hmult
    _ ≤ L * D * (D' ^ (1 - β) * A * N' ^ β) := by gcongr
    _ = L * D' ^ (1 - β) * A * (D * N' ^ β) := by ring
    _ = L * D' ^ (1 - β) * A * (D ^ (1 - β) * (D ^ β * N' ^ β)) := by
        have hDsplit : D ^ (1 - β) * (D ^ β * N' ^ β) = D * N' ^ β := by
          rw [← mul_assoc, rpow_one_sub_mul_rpow β hD0 hDtop]
        rw [hDsplit]
    _ ≤ L * D' ^ (1 - β) * A * (D ^ (1 - β) * N ^ β) := by gcongr
    _ = L * D' ^ (1 - β) * A * D ^ (1 - β) * N ^ β := by ring

/-! ### Route (a): the hypothesis is spent, but on our own rendering of GWZ Lemma 6.1 -/


/-! ### The conflict-degree bound without leaf-scale essential distinctness -/

/-- **`Kakeya.IsEDUpToMult` is hereditary.**  The non-essentially-distinct set only shrinks when
the ambient index set does. -/
theorem IsEDUpToMult.subset {ι : Type*} {E : Type*} [MeasureSpace E]
    {s t : Finset ι} {V : ι → Set E} {M : ℕ}
    (hED : IsEDUpToMult s V M) (hts : t ⊆ s) :
    IsEDUpToMult t V M := by
  classical
  intro i hi
  refine le_trans (Finset.card_le_card ?_) (hED i (hts hi))
  intro j hj
  simp only [notEssDistinctSet, Finset.mem_filter] at hj ⊢
  exact ⟨hts hj.1, hj.2⟩


section InnerEDFamily

open Convexity ConvexSpaceBody
open scoped Real


end InnerEDFamily

end Kakeya

end

end

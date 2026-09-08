/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Section6HallDecomposition
public import Kakeya.DimensionThree.Plank.GlobalPlankPartBBridge

/-!
# From `(PS, Fz)` to `Section6PartBData`

`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` (GWZ Proposition 6.6(B),
`Kakeya/DimensionThree/Plank/Factorization.lean`) quantifies over a pair

* `PS : Tube.IsUniformAtScale q (fun i => (T i).toTube) ρ Cpar`, and
* `Fz : GlobalPlankFactorization Cw a b hab hb1 PS.parent
    (fun k => (PS.parentTube k).toConvexSpaceBody) C₀`,

whereas the whole proved Part-(B) development downstream — beginning with
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_of_partBData` — is stated over
`Kakeya.Section6PartBData`.  This file converts the first into the second.

`Section6PartBData` has exactly two fields, and each already has an owner:

* `factor` is `Kakeya.GlobalPlankFactorization.toSection6PartBFactorisation`
  (`Kakeya/DimensionThree/Plank/GlobalPlankPartBBridge.lean`), over the **same** coarse index set
  `PS.parent` and the **same** coarse family `PS.parentTube` that `Fz` is stated over;
* `decomp` is `Kakeya.Section6CoarseTubeDecomposition.ofUniformAtScaleHall`
  (`Kakeya/DimensionThree/Plank/Section6HallDecomposition.lean`), likewise over the full parent set.

The coarse index sets therefore agree on the nose and the two halves compose.  What the conversion
needs beyond the hypotheses Proposition 6.6(B) already carries is recorded below, field by field.

## What Proposition 6.6(B) already supplies

All of the following are derivable inside the statement of
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation`, at any threshold `δ₀ ≤ 1`:

* `δ ≤ ρ`, by `Kakeya.Prop66BScale.le_of_plankScale_le` from `δ ^ (1 - ε₂) ≤ ρ`;
* `0 < ρ`, `0 < a`, `0 < b`, from `δ ≤ ρ ≤ a ≤ b` and `0 < δ`;
* `q.Nonempty`, from the fullness hypothesis `δ ^ η ≤ fullness q 𝕋` — the empty family has
  fullness `0`;
* `PS.parent.Nonempty` (`Kakeya.parent_nonempty_of_nonempty`) and `0 < PS.branchingN`
  (`Kakeya.branchingN_pos_of_nonempty`), from `q.Nonempty`;
* `Fz.parts.Nonempty`, from `PS.parent.Nonempty` through the underlying `Finpartition`;
* `1 ≤ Cw`, which is the field `Kakeya.GlobalPlankFactorization.one_le_Cw`;
* `1 ≤ Cpar`, after replacing `PS` by `PS.mono` at `max 1 Cpar` — a *weakening* of the uniformity
  datum that leaves `parent`, `parentTube` and `branchingN` untouched, so `Fz` still typechecks
  against it, and which keeps the budget since `Cpar ≤ δ ^ (-η)` and `1 ≤ δ ^ (-η)`.

## What it does **not** supply, and who does

Two hypotheses of `Kakeya.Section6PartBData.ofUniformAtScaleOfGlobalPlank` are **not** available
from Proposition 6.6(B) as it currently stands.

**(1) The parent window `hballs`: the coarse `ρ`-tubes lie in the closed unit ball.  NOT owed —
6.6(B)'s leaf window is at the wrong radius, not missing.**  Proposition 6.6(B) normalises only the
*leaves*, and at radius exactly `1`; neither its remaining hypotheses nor any field of
`Tube.IsUniformAtScale` says where the parent tubes lie, since the parent family is explicitly a
family of *free* `ρ`-tubes with cores anywhere.

The tree already measures the gap exactly:
`Kakeya.ML2Reduction.parentTube_carrier_subset_closedBall` proves that leaves inside `B̄(0, r)`
force parents inside `B̄(0, r + 4 ρ)`.  At `r = 1` that is `B̄(0, 1 + 4 ρ)`, which is why the window
does not come for free; at `r + 4 ρ ≤ 1` it *is* the parent window, and that inequality is already a
hypothesis of `Kakeya.ML2Reduction.eccentric_of_maxDensityFactoring_of_leafBall`.  The discharge is
`Kakeya.parentWindow_of_leafWindow`, and
`Kakeya.Section6PartBData.ofUniformAtScaleOfGlobalPlankOfLeafBall` is this file's constructor with
`hballs` replaced by the leaf window (both in
`Kakeya/DimensionThree/MainLemma2/Reduction/PartBDatumAtCallSite.lean`, which may cite
`Kakeya.ML2Reduction`; this file may not).  Independently,
`Kakeya.ML2Reduction.PlankFactoringData.ball` is character-for-character `hballs`, so the one
application site supplies it twice over.

The window is consumed at exactly one place, the `repr_window` field, through
`Kakeya.framedPlank_subset_closedBall`, whose numerical margin is *tight*: the framed plank of a
body inside `closedBall 0 1` lies in `closedBall 0 4` (`Kakeya.plankWindowRadius`) with the
squared-norm budget `1 + 8 + 4·(3/2) + 1 = 16` exactly saturated, so no slack is available to
absorb a larger window on the body.  That is why the repair is to tighten `r`, not to widen the
window.

**(2) The branching floor `(max 1 Cpar) ^ 2 ≤ PS.branchingN`.  Now a HYPOTHESIS of Proposition
6.6(B), because it is a missing datum.**

Since steps  the floor is carried by
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` itself, beside `Cpar ≤ δ ^ (-η)`, and threaded
to the one application site; the old branching-free form is pinned as
`Kakeya.Prop66BScale.statement_of_universal_prop66B_plankScale` and the new one as
`Kakeya.Prop66BScale.statement_of_universal_prop66B_branchingFloor`.  Four facts fix its
status.

*It is a statement about the configuration, not a choice of parameter.*
`Kakeya.branchingN_le_mul_card_parentContainment` is `N ≤ C · |F_j|`, so `branchingN` cannot be
inflated: it is pinned to within `C` of the containment counts, in `Tube.IsUniformAtScale` and
equally in `Tube.UniformTubeSet` and `Tube.ChainUniformTubeSet`, whose `branchingN` fields are
bracketed by `card_class_le` and `le_card_class`.  Read on the configuration the floor says *every
coarse `ρ`-tube carries at least `Cpar` fine tubes*
(`Kakeya.le_card_parentContainment_of_sq_le_branchingN`), and one parent carrying `Cpar ^ 3` of them
already gives it back (`Kakeya.sq_le_branchingN_of_cube_le_card_parentContainment`).

*It is necessary for this route.*  `Kakeya.Section6CoarseTubeDecomposition.card_coarseSet_le_card`
shows that any decomposition forces `|coarseSet| ≤ |q|`, a genuine cardinality constraint that the
uniformity datum does not carry; `Kakeya.card_parent_le_card_of_sq_le_branchingN` shows the floor
restores it.

*It is not implied by the numbers the datum exports.*
`Kakeya.not_exists_sdr_of_uniform_numeric_fields` exhibits a bipartite system meeting **all seven**
numeric facts available — including the two the producers add, `1 ≤ N` and
`|𝕋_ρ| · N ≤ |𝕋| ≤ 2 |𝕋_ρ| · N` from `Tube.refineToEssDistinctUniform` — with no system of distinct
representatives.  There, no assignment whatever gives every parent a nonempty fibre.

*And the cardinality band does not reach it either.*
`Kakeya.band_consistent_with_unit_branching` shows that Main Lemma 2's `|𝕋| > δ^{-1}`, together with
that same two-sided count and any covering bound `|𝕋_ρ| ≤ ρ^{-4}`, is satisfiable at branching
exactly `1` when `ρ = δ ^ (1 - ε₂)`.

A tree-wide scan finds the strongest lower bound on any `branchingN` anywhere to be `1 ≤ branchingN`
(`Tube.refineToEssDistinctUniform`, `Tube.exists_uniform_subset_tight_injLeaves`).  The floor is
therefore required of whatever builds the `PS` that Main Lemma 2 hands to Proposition 6.6(B),
where the branching numbers are known, at the point where the class sizes are.  It survives the one refinement the chain performs
(`Kakeya.ML2Reduction.branchingN_restrictParents`, `rfl`).

## The re-declared half-widths

The datum produced below is at the half-widths `(Fz.uniformThin, Fz.uniformMid)`, not at the
declared `(a, b)`; that is the re-declaration forced by
`Kakeya.GlobalPlankFactorization.toSection6PartBFactorisation`, and the bookkeeping back to `(a, b)`
is `Kakeya.GlobalPlankFactorization.uniformThin_le` (`A ≤ a`) together with
`Kakeya.GlobalPlankFactorization.le_mul_uniformMid` (`b ≤ K * B`), both already proved.  The fibre
comparability constant is `2 * Cpar ^ 2`, inside the sub-polynomial budget whenever
`Cpar ≤ δ ^ (-η)`.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace Kakeya

/-! ### Nondegeneracy facts that Proposition 6.6(B) already implies -/

variable {ι : Type*} {δ : ℝ≥0} {q : Finset ι}
  {Tt : ι → Tube δ (EuclideanSpace ℝ (Fin 3))} {ρ C : ℝ≥0}

/-- A nonempty leaf family has a nonempty parent family. -/
theorem parent_nonempty_of_nonempty (U : Tube.IsUniformAtScale q Tt ρ C) (hq : q.Nonempty) :
    U.parent.Nonempty := by
  obtain ⟨i, hi⟩ := hq
  obtain ⟨j, hj, _⟩ := U.exists_le_rescale hi
  exact ⟨j, hj⟩

open Classical in
/-- **The branching number of a nonempty uniform family is positive.**  A leaf lies in some parent,
so that parent's containment set is nonempty, and `card_filter_le` then forbids `N = 0`. -/
theorem branchingN_pos_of_nonempty (U : Tube.IsUniformAtScale q Tt ρ C) (hq : q.Nonempty) :
    0 < U.branchingN := by
  classical
  obtain ⟨i, hi⟩ := hq
  obtain ⟨j, hj, hij⟩ := U.exists_le_rescale hi
  have h1 : (1 : ℝ≥0) ≤ ((parentContainment U j).card : ℝ≥0) := by
    have hne : (parentContainment U j).Nonempty := ⟨i, mem_parentContainment.mpr ⟨hi, hij⟩⟩
    exact_mod_cast Finset.card_pos.mpr hne
  have h3 : (1 : ℝ≥0) ≤ C * U.branchingN := h1.trans (card_parentContainment_le U hj)
  rcases eq_zero_or_pos U.branchingN with h0 | h0
  · exfalso
    rw [h0, mul_zero] at h3
    exact absurd h3 (by norm_num)
  · exact h0


namespace Section6CoarseTubeDecomposition


end Section6CoarseTubeDecomposition

/-! ### The `|𝕋| > δ^{-1}` band does not reach the floor -/


/-! ### The assembly -/


end Kakeya

end

end

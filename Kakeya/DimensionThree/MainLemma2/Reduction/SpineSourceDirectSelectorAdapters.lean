/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceDirectWindowData

/-!
# Adapters from the zero-level data to the direct window data

Two thin conversions between the `SourceZero*` records and the `SourceDirect*` records of
`SpineSourceDirectWindowData`. `Kakeya.ML2Core.source_direct_retained_payment` upgrades a
`SourceZeroRetainedState` to a `SourceDirectRetainedState` by paying the multiplicity row with
the same loss, and `Kakeya.ML2Core.source_direct_plank_eccentric_data` shows that
`SourceDirectPlankFactors` yields `SourceZeroEccentricFactors` with the same plank constant and
identical factor parts. No new selection or analytic hypothesis is introduced.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

universe u

variable {iota : Type u} {delta : ℝ≥0} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace ℝ (Fin 3))} {M C : Nat}

/-- The ordinary P coefficient is identical to the coefficient in the
reviewed eccentric data. The actual parts are preserved, not re-factored. -/
theorem source_direct_plank_eccentric_data (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3)))
    {a m : Nat} {etaParent bias : ℝ} {D aw bw cw : ℝ≥0}
    (P : SourceDirectPlankFactors Q Z a m etaParent bias D aw bw cw) :
    sourceParentPlankConstant delta bias = sourceZeroPlankConstant delta bias /\
    exists E : SourceZeroEccentricFactors Q Z a m etaParent bias D aw bw cw,
      forall j, forall hj : j ∈ Q.indexSet a,
        (E.factor j hj).parts = (P.factor j hj).parts := by
  have hconstant : sourceParentPlankConstant delta bias = sourceZeroPlankConstant delta bias := rfl
  refine ⟨hconstant, {
    factor := P.factor
    coarse_lt_middle := P.coarse_lt_middle
    middle_bound := P.middle_bound
    dimension_comparison := P.comparison_one
    short_pos := P.short_positive
    short_le_middle := P.short_le_middle
    middle_le_long := P.middle_le_long
    long_lower := P.long_lower
    long_upper := P.long_upper
    eccentric := P.eccentric
    dimensions := P.dimensions
    same_tubes := P.same_tubes
    shade_floor := P.shade_floor
    complete_leaves := P.assigned_partition
    complete_leaf_mass := P.assigned_mass }, ?_⟩
  intro j hj
  rfl

end Kakeya.ML2Core

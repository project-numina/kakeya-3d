/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.W44NormalizationCardPort

/-!
# Selection-free normalization for the estimate WZ middle branch

The honest replacement constructed by fine normalization is canonical on the whole ambient
index set.  Essential distinctness is needed only by the optional selection step.  Running that
step on a singleton exposes the canonical replacement, after which the one-sided comparable-body
transport applies to the original family without changing its index set.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya.ml1Boot.W44NoED

noncomputable section

universe u

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Geometric loss of the selection-free honest replacement. -/
noncomputable def C : ℝ≥0 :=
  (4 * _root_.Tube.normalization.C 3) ^ 6

theorem one_le_C : 1 <= C := by
  unfold C
  exact one_le_pow₀ (one_le_mul (by norm_num) (_root_.Tube.normalization.one_le_C 3))

end

end Kakeya.ml1Boot.W44NoED

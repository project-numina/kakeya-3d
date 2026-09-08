/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.ActualMarginNetW102

/-!
# Scaled grid net with midpoint localization (W102)

Variant of `exists_scaled_grid_net_w102` that also retains the midpoint clause of
`Tube.grid_net_tight`.  `exists_scaled_grid_net_with_midpoint_w102` returns one net witness
carrying the cover, separation, carrier localization in `closedBall 0 5` and midpoint
localization in `closedBall 0 3` simultaneously; `ActualMarginParentW102` consumes it.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped ENNReal NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

universe uE

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- The midpoint localization is retained from the same net witness as the
cover, separation, and carrier localization. -/
theorem exists_scaled_grid_net_with_midpoint_w102
    {rho alpha : ℝ≥0} (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) :
    ∃ G : Finset (Tube (alpha * rho) E),
      (∀ {sigma : ℝ≥0} (U : Tube sigma E),
        2 * (sigma : ℝ) ≤ (alpha * rho : ℝ) →
        U.midpoint ∈ Metric.closedBall (0 : E) 3 →
        ∃ W ∈ G, U.toConvexSpaceBody ≤ W.toConvexSpaceBody ∧
          ‖U.midpoint - W.midpoint‖ ≤ (alpha * rho : ℝ) / 32 ∧
          ‖U.direction - W.direction‖ ≤ (alpha * rho : ℝ) / 16) ∧
      (∀ a ∈ G, ∀ b ∈ G, a ≠ b →
        (alpha * rho : ℝ) / 32 ≤ ‖a.x - b.x‖ + ‖a.y - b.y‖) ∧
      (∀ W ∈ G, W.carrier ⊆ Metric.closedBall (0 : E) 5) ∧
      (∀ W ∈ G, W.midpoint ∈ Metric.closedBall (0 : E) 3) := by
  have hprod : 0 < alpha * rho := mul_pos halpha hrho
  have hprod1 : (alpha * rho : ℝ) ≤ 1 := by
    exact_mod_cast (mul_le_one₀ halpha1 (by positivity) hrho1)
  obtain ⟨G, hcover, hsep, hball, hmid⟩ :=
    Tube.grid_net_tight (E := E) hprod hprod1
  exact ⟨G, hcover, hsep, hball, hmid⟩

end
end Kakeya.ml1Boot.TrialRestartW94

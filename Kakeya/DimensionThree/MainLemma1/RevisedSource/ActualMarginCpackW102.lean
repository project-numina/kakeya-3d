/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.ActualMarginNetW102

/-!
# Packing base for the small-bin net (W102)

Fixes the `δ`-independent packing constant `cpackW102 α = ⌈3072 / α⌉` for a grid net at the
small-bin fraction `α` of a target radius.  `cpackW102_spec` verifies the ratio hypothesis of
`scaled_grid_overlap_target_w102`, and `scaled_grid_overlap_target_cpack_w102` is that
packing bound with the constant filled in.  `rescaled_child_le_parent_w102` shows that
containment of net nodes at scales `α · child ≤ α · parent` is preserved by rescaling both
to their target radii, given `α ≤ 1/4` and `child ≤ parent/2`.
-/

@[expose] public section

open scoped NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

universe uE

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- The fixed-before-delta packing base forced by a small-bin fraction. -/
def cpackW102 (alpha : ℝ≥0) : Nat :=
  Nat.ceil (3072 / (alpha : ℝ))

theorem cpackW102_spec {alpha rho : ℝ≥0} {n : Nat}
    (halpha : 0 < alpha) (hrho : 0 < rho) (hn : 1 ≤ n) :
    (24 * (rho : ℝ) + ((alpha * rho : ℝ≥0) : ℝ) / 128) /
        (((alpha * rho : ℝ≥0) : ℝ) / 128) ≤
      (cpackW102 alpha : ℝ) * n + 1 := by
  have ha : (0 : ℝ) < (alpha : ℝ) := by exact_mod_cast halpha
  have hr : (0 : ℝ) < (rho : ℝ) := by exact_mod_cast hrho
  have hratio :
      (24 * (rho : ℝ) + ((alpha * rho : ℝ≥0) : ℝ) / 128) /
          (((alpha * rho : ℝ≥0) : ℝ) / 128) =
        3072 / (alpha : ℝ) + 1 := by
    rw [NNReal.coe_mul]
    field_simp
    ring
  rw [hratio]
  have hceil : 3072 / (alpha : ℝ) ≤ (cpackW102 alpha : ℝ) := by
    exact Nat.le_ceil _
  have hmul : (cpackW102 alpha : ℝ) ≤
      (cpackW102 alpha : ℝ) * n := by
    have hnat : cpackW102 alpha ≤ cpackW102 alpha * n := by
      simpa using Nat.mul_le_mul_left (cpackW102 alpha) hn
    exact_mod_cast hnat
  linarith

theorem scaled_grid_overlap_target_cpack_w102
    {delta rho alpha : ℝ≥0} (hrho : 0 < rho)
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1)
    (G : Finset (Tube (alpha * rho) E))
    (hsep : ∀ a ∈ G, ∀ b ∈ G, a ≠ b ->
      (alpha * rho : ℝ) / 32 ≤ ‖a.x - b.x‖ + ‖a.y - b.y‖)
    (V : Tube rho E) :
    (G.filter (fun W : Tube (alpha * rho) E => ∃ (U : Tube delta E),
        U.carrier ⊆ Metric.closedBall (0 : E) 1 ∧
        U.toConvexSpaceBody ≤ (W.rescale rho).toConvexSpaceBody ∧
        U.toConvexSpaceBody ≤ V.toConvexSpaceBody)).card ≤
      2 * (cpackW102 alpha * Module.finrank ℝ E + 1) ^
        (2 * Module.finrank ℝ E) := by
  apply scaled_grid_overlap_target_w102 hrho halpha halpha1 G hsep V
    (cpackW102 alpha)
  exact cpackW102_spec halpha hrho (Nat.succ_le_iff.mpr Module.finrank_pos)

end
end Kakeya.ml1Boot.TrialRestartW94

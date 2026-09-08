/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.AxisFootNormalizationShadingW103
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.AxisFootNormalizationFrostmanW103
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.AxisFootNormalizationCountingW103

/-!
# Assembling `DetailedTrialCellsW94` on the grid scale ladder

Provides the constructor `Kakeya.ml1Boot.TrialRestartW94.detailed_grid_cells_w103`, which packages
parent tubes `P l` at scales `Tube.gridScale d M l`, assignments, containment, ball, line-ED and
two-sided cell-count data into a `DetailedTrialCellsW94 F V M (Tube.gridScale d M) Ctw Ccell`.
The ladder axioms are discharged by `grid_trial_step_w103` (consecutive grid scales differ by at
most `d ^ (-2/M)`) and `grid_block_ratio_small_w103` (a block ratio of at most `1/16` under the
gap `16 * gridScale delta (M*M) 1 <= 1`); `ennreal_comparison_w103` is a two-sided `ENNReal`
comparison helper.  Combines the axis-foot normalization shading, Frostman and counting files.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ConvexSpaceBody ShadedBody

namespace Kakeya.ml1Boot.TrialRestartW94

open RevisedLiteralProfileInterfaceFormalizerW87

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

universe uE uI

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

theorem grid_trial_step_w103 {d : ℝ≥0} (hd : 0 < d) (hd1 : d <= 1)
    (M l : Nat) :
    (Tube.gridScale d M l : ℝ≥0∞) / (Tube.gridScale d M (l + 1) : ℝ≥0∞) <=
      (d : ℝ≥0∞) ^ (-(2 : ℝ) / M) := by
  rw [← ENNReal.coe_div (Tube.gridScale_pos hd M (l + 1)).ne', Tube.gridScale_div_gridScale hd]
  rw [← ENNReal.coe_rpow_of_ne_zero hd.ne']
  apply ENNReal.coe_le_coe.mpr
  apply NNReal.rpow_le_rpow_of_exponent_ge hd hd1
  push_cast
  have hh : (0 : ℝ) <= M := Nat.cast_nonneg _
  have hnum : -(2 : ℝ) <= -1 := by norm_num
  have hdiv := div_le_div_of_nonneg_right hnum hh
  simpa [div_eq_mul_inv] using hdiv

theorem grid_block_ratio_small_w103 {delta : ℝ≥0} (hd : 0 < delta) (hd1 : delta <= 1)
    {M a b : Nat} (hM : 1 <= M) (hab : a < b)
    (hgap : 16 * Tube.gridScale delta (M * M) 1 <= 1) :
    Tube.gridScale delta M b / Tube.gridScale delta M a <= 1 / 16 := by
  have hstep : Tube.gridScale delta M b / Tube.gridScale delta M a <=
      Tube.gridScale delta (M * M) 1 := by
    rw [Tube.gridScale_div_gridScale hd]
    unfold Tube.gridScale
    apply NNReal.rpow_le_rpow_of_exponent_ge hd hd1
    have hMr : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    have hMr1 : (1 : ℝ) <= M := by exact_mod_cast hM
    have habr : (a : ℝ) + 1 <= b := by exact_mod_cast hab
    push_cast
    apply (div_le_iff₀ (mul_pos hMr hMr)).mpr
    field_simp
    nlinarith
  exact hstep.trans ((le_div_iff₀ (by norm_num : (0 : ℝ≥0) < 16)).mpr (by nlinarith))

theorem ennreal_comparison_w103 {x y : ℝ≥0∞} {C D : ℝ≥0}
    (hD : 0 < D) (hCD : C ^ (2 : Nat) <= D)
    (hxy : x <= (C : ℝ≥0∞) ^ (2 : Nat) * y)
    (hyx : y <= (C : ℝ≥0∞) ^ (2 : Nat) * x) :
    (D : ℝ≥0∞)⁻¹ * x <= y ∧ y <= (D : ℝ≥0∞) * x := by
  have hCD' : (C : ℝ≥0∞) ^ (2 : Nat) <= (D : ℝ≥0∞) := by exact_mod_cast hCD
  constructor
  · calc
      (D : ℝ≥0∞)⁻¹ * x <= (D : ℝ≥0∞)⁻¹ * ((D : ℝ≥0∞) * y) :=
        mul_le_mul_right (hxy.trans (mul_le_mul_left hCD' _)) _
      _ = y := by rw [← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast hD.ne') ENNReal.coe_ne_top, one_mul]
  · exact hyx.trans (mul_le_mul_left hCD' _)

def detailed_grid_cells_w103 {iota : Type uI} [DecidableEq iota] {d : ℝ≥0}
    (hd : 0 < d) (hd1 : d <= 1) (F : Finset iota) (V : iota -> ShadedTube d E)
    (M : Nat) (hM : 1 <= M) (Ctw Ccell : ℝ≥0)
    (P : (l : Nat) -> iota -> Tube (Tube.gridScale d M l) E)
    (assign : Nat -> iota -> iota)
    (hcontained : ∀ l, l <= M -> ∀ i ∈ F,
      (V i).toConvexSpaceBody <= (P l (assign l i)).toConvexSpaceBody)
    (hball : ∀ l, l <= M -> ∀ R ∈ F.image (assign l),
      (P l R).carrier ⊆ Metric.closedBall 0 2)
    (hline : ∀ l, l <= M -> lineEssentiallyDistinctW94 (F.image (assign l)) (P l) Ctw)
    (D : Nat -> ℝ≥0) (hDpos : ∀ l, l <= M -> 0 < D l)
    (hassigned : ∀ l, l <= M -> ∀ R ∈ F.image (assign l),
      D l <= ((completeFibreW94 F (assign l) R).card : ℝ≥0))
    (hgeometric : ∀ l, l <= M -> ∀ R ∈ F.image (assign l),
      ((exactTubeCellW87 F (fun i => (V i).toTube) (P l R)).card : ℝ≥0) < 2 * Ccell * D l) :
    DetailedTrialCellsW94 F V M (Tube.gridScale d M) Ctw Ccell where
  rho_zero := Tube.gridScale_zero d M
  rho_bottom := Tube.gridScale_self d (by omega)
  rho_pos := fun l hl => Tube.gridScale_pos hd M l
  rho_nonincreasing := fun l hl => Tube.gridScale_antitone hd hd1 M (Nat.le_succ l)
  rho_step := fun l hl => grid_trial_step_w103 hd hd1 M l
  parentSet := fun l => F.image (assign l)
  parentTube := P
  assign := assign
  assign_image := fun l hl => rfl
  assigned_containment := hcontained
  parent_ball := hball
  parent_line_ed := hline
  D := D
  D_pos := hDpos
  geometric_lower := by
    intro l hl R hR
    refine (hassigned l hl R hR).trans ?_
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro i hi
    obtain ⟨hiF, hiR⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_filter.mpr ⟨hiF, ?_⟩
    rw [← hiR]
    exact hcontained l hl i hiF
  geometric_upper := hgeometric
  assigned_lower := hassigned

end

end Kakeya.ml1Boot.TrialRestartW94

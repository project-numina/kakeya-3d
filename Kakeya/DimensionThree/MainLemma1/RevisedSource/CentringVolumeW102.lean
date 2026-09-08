/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Tube.CylinderApprox
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Volume comparison between a `delta`-tube and a `delta/2`-tube

Two dimension-three volume facts used throughout the centring files.
`Kakeya.ml1Boot.TrialRestartW94.volume_cylinder_three_w102` computes the Lebesgue measure of
`cylinder p v a b r` as `(b - a) * r^2 * pi`, and
`Kakeya.ml1Boot.TrialRestartW94.half_radius_carrier_volume_w102` shows that for `delta <= 1/200`
any `delta/2`-tube `W` has carrier volume at most `384 * (1/512)` times that of any
`delta`-tube `T`.  Imports only `Kakeya.Tube.CylinderApprox` and Mathlib's volume of balls.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

universe uE
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

omit [Nontrivial E] in
theorem volume_cylinder_three_w102 (hdim : Module.finrank ℝ E = 3)
    {v : E} (hv : ‖v‖ = 1) (p : E) (a b r : ℝ) :
    volume (cylinder p v a b r) =
      ENNReal.ofReal (b - a) * (ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi) := by
  have hvne : v ≠ 0 := by intro h; simp [h] at hv
  have hspan := finrank_span_singleton (K := ℝ) hvne
  have hsum := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ v)
  have hperp : Module.finrank ℝ ((ℝ ∙ v)ᗮ : Submodule ℝ E) = 2 := by omega
  letI : Nontrivial ((ℝ ∙ v)ᗮ : Submodule ℝ E) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hperp]; decide)
  rw [volume_cylinder hv, InnerProductSpace.volume_closedBall_of_dim_even
    (k := 1) (by simpa using hperp)]
  simp only [hperp, pow_one, Nat.factorial_one, Nat.cast_one, div_one]

theorem half_radius_carrier_volume_w102 (hdim : Module.finrank ℝ E = 3)
    {delta : ℝ≥0} (hdsmall : delta <= 1 / 200)
    (T : Tube delta E) (W : Tube (delta / 2) E) :
    volume W.carrier <= (384 : ℝ≥0∞) * (1 / 512 : ℝ≥0∞) * volume T.carrier := by
  have hlo := measure_mono (μ := volume) (T.cylinder_subset_carrier_self
    (a := -(1 / 2 : ℝ)) (b := 1 / 2) (r := delta) le_rfl le_rfl le_rfl)
  rw [volume_cylinder_three_w102 hdim T.norm_direction] at hlo
  norm_num only [sub_neg_eq_add, add_halves, ENNReal.ofReal_one, one_mul] at hlo
  have hhi := measure_mono (μ := volume) (W.carrier_subset_cylinder_self (by positivity))
  rw [volume_cylinder_three_w102 hdim W.norm_direction] at hhi
  have hdR : (delta : ℝ) <= 1 / 200 := by exact_mod_cast hdsmall
  have hlen : ENNReal.ofReal
      ((1 / 2 : ℝ) + ((delta / 2 : ℝ≥0) : ℝ) -
        (-(1 / 2 : ℝ) - ((delta / 2 : ℝ≥0) : ℝ))) <= 3 := by
    rw [← ENNReal.ofReal_ofNat]
    apply ENNReal.ofReal_le_ofReal
    simp only [NNReal.coe_div, NNReal.coe_ofNat]
    linarith only [hdR]
  have hrad : ENNReal.ofReal (((delta / 2 : ℝ≥0) : ℝ)) =
      (delta : ℝ≥0∞) / 2 := by
    rw [NNReal.coe_div, ENNReal.ofReal_div_of_pos (by norm_num)]
    simp
  rw [hrad] at hhi
  calc
    volume W.carrier <=
        3 * (((delta : ℝ≥0∞) / 2) ^ 2 * ENNReal.ofReal Real.pi) :=
      hhi.trans (mul_le_mul_left hlen _)
    _ = (384 : ℝ≥0∞) * (1 / 512 : ℝ≥0∞) *
        ((delta : ℝ≥0∞) ^ 2 * ENNReal.ofReal Real.pi) := by
      rw [ENNReal.div_eq_inv_mul, mul_pow]
      have hc : (3 : ℝ≥0∞) * (2⁻¹) ^ 2 = 384 * (1 / 512) := by
        have h := congrArg ((↑) : ℝ≥0 -> ℝ≥0∞)
          (show (3 : ℝ≥0) * (2⁻¹) ^ 2 = 384 * (1 / 512) by norm_num)
        simpa only [ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_inv_two,
          ENNReal.coe_div (by norm_num : (512 : ℝ≥0) ≠ 0),
          ENNReal.coe_ofNat, ENNReal.coe_one] using h
      calc
        _ = (3 * (2⁻¹) ^ 2) * ((delta : ℝ≥0∞) ^ 2 * ENNReal.ofReal Real.pi) := by ring
        _ = _ := by rw [hc]
    _ <= _ := by simpa using mul_le_mul_right hlo ((384 : ℝ≥0∞) * (1 / 512))

end
end Kakeya.ml1Boot.TrialRestartW94

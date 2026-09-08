/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineRescale
public import Kakeya.DimensionThree.MainLemma2.Reduction.Assembly
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCardBand
public import Kakeya.DimensionThree.MainLemma2.SetupAbsorption
public import Kakeya.DimensionThree.MainLemma2.VeryNotStickyClosed
public import Kakeya.PartialEstimatesWindowed
public import Kakeya.Tube.CoverCountComparable

/-!
# The affine squeeze: is the cardinality band of Main Lemma 2 vacuous?

Adversarial file for steps.  See the module docstring at the bottom for the verdict.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Set Filter Topology
open scoped Pointwise NNReal ENNReal

namespace Kakeya.ML2Squeeze

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ## The orthogonal complement of a unit vector -/

/-- The component of `z` orthogonal to `u` (meaningful when `‖u‖ = 1`). -/
noncomputable def perp (u z : E) : E := z - (inner ℝ u z : ℝ) • u


omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem inner_perp {u : E} (hu : ‖u‖ = 1) (z : E) : (inner ℝ u (perp u z) : ℝ) = 0 := by
  simp [perp, inner_sub_right, real_inner_smul_right, hu]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem perp_add (u z w : E) : perp u (z + w) = perp u z + perp u w := by
  simp only [perp, inner_add_right, add_smul]
  abel

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem perp_smul (u : E) (a : ℝ) (z : E) : perp u (a • z) = a • perp u z := by
  simp only [perp, real_inner_smul_right, smul_sub, smul_smul]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem perp_self {u : E} (hu : ‖u‖ = 1) : perp u u = 0 := by
  simp [perp, hu]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Pythagoras for the decomposition `z = ⟪u,z⟫ u + perp u z`. -/
theorem norm_sq_eq_inner_sq_add_norm_perp_sq {u : E} (hu : ‖u‖ = 1) (z : E) :
    ‖z‖ ^ 2 = (inner ℝ u z : ℝ) ^ 2 + ‖perp u z‖ ^ 2 := by
  have hz : z = (inner ℝ u z : ℝ) • u + perp u z := by
    rw [perp]; abel
  have hinner : (inner ℝ ((inner ℝ u z : ℝ) • u) (perp u z) : ℝ) = 0 := by
    rw [real_inner_smul_left, inner_perp hu, mul_zero]
  calc ‖z‖ ^ 2 = ‖(inner ℝ u z : ℝ) • u + perp u z‖ ^ 2 := by rw [← hz]
    _ = ‖(inner ℝ u z : ℝ) • u‖ ^ 2 + 2 * (inner ℝ ((inner ℝ u z : ℝ) • u) (perp u z) : ℝ)
          + ‖perp u z‖ ^ 2 := norm_add_sq_real _ _
    _ = (inner ℝ u z : ℝ) ^ 2 + ‖perp u z‖ ^ 2 := by
        rw [hinner, norm_smul, Real.norm_eq_abs, hu, mul_one, sq_abs]
        ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem norm_perp_le {u : E} (hu : ‖u‖ = 1) (z : E) : ‖perp u z‖ ≤ ‖z‖ := by
  have h := norm_sq_eq_inner_sq_add_norm_perp_sq hu z
  nlinarith [norm_nonneg (perp u z), norm_nonneg z, sq_nonneg (inner ℝ u z : ℝ)]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem abs_inner_le_norm_of_unit {u : E} (hu : ‖u‖ = 1) (z : E) :
    |(inner ℝ u z : ℝ)| ≤ ‖z‖ := by
  have := abs_real_inner_le_norm u z
  rwa [hu, one_mul] at this

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `‖a • u + w‖ ^ 2 = a ^ 2 + ‖w‖ ^ 2` when `‖u‖ = 1` and `w ⊥ u`. -/
theorem norm_smul_add_sq {u : E} (hu : ‖u‖ = 1) (a : ℝ) {w : E}
    (hw : (inner ℝ u w : ℝ) = 0) : ‖a • u + w‖ ^ 2 = a ^ 2 + ‖w‖ ^ 2 := by
  have hinner : (inner ℝ (a • u) w : ℝ) = 0 := by rw [real_inner_smul_left, hw, mul_zero]
  calc ‖a • u + w‖ ^ 2
      = ‖a • u‖ ^ 2 + 2 * (inner ℝ (a • u) w : ℝ) + ‖w‖ ^ 2 := norm_add_sq_real _ _
    _ = a ^ 2 + ‖w‖ ^ 2 := by
        rw [hinner, norm_smul, Real.norm_eq_abs, hu, mul_one, sq_abs]; ring

end Geometry

/-! ## The squeeze map `A = ¼ · diag(σ, …, σ, 1)` -/

section Squeeze

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A dummy tube used only to name the frame direction `e` for `Tube.dilateAux`. -/
noncomputable def frame (σ : ℝ≥0) {e : E} (he : ‖e‖ = 1) : Tube σ E :=
  Tube.mk' σ (x := (0 : E)) (y := e) (by rw [dist_eq_norm, zero_sub, norm_neg, he])

@[simp] theorem frame_x (σ : ℝ≥0) {e : E} (he : ‖e‖ = 1) : (frame σ he).x = 0 := rfl
@[simp] theorem frame_y (σ : ℝ≥0) {e : E} (he : ‖e‖ = 1) : (frame σ he).y = e := rfl

@[simp] theorem frame_direction (σ : ℝ≥0) {e : E} (he : ‖e‖ = 1) :
    (frame σ he).direction = e := by
  show e - (0 : E) = e
  exact sub_zero e

/-- **The squeeze.**  In an orthonormal frame whose last axis is `e` this is
`¼ · diag(σ, …, σ, 1)`: the dilation by `¼` along `e` and by `σ/4` on `e^⊥`. -/
noncomputable def sqL (σ : ℝ≥0) {e : E} (he : ‖e‖ = 1) : E →L[ℝ] E :=
  (1 / 4 : ℝ) • (frame σ he).dilateAux (σ : ℝ)

/-- The inverse map, `4 · diag(σ⁻¹, …, σ⁻¹, 1)`. -/
noncomputable def sqLinv (σ : ℝ≥0) {e : E} (he : ‖e‖ = 1) : E →L[ℝ] E :=
  (4 : ℝ) • (frame σ he).dilateAux ((σ : ℝ)⁻¹)

theorem sqL_apply' (σ : ℝ≥0) {e : E} (he : ‖e‖ = 1) (z : E) :
    sqL σ he z = (1 / 4 : ℝ) • ((frame σ he).dilateAux (σ : ℝ) z) := rfl

/-- The normal form of the squeeze: `A z = ¼ (⟪e,z⟫ e + σ · perp e z)`. -/
theorem sqL_apply (σ : ℝ≥0) {e : E} (he : ‖e‖ = 1) (z : E) :
    sqL σ he z = (1 / 4 : ℝ) • ((inner ℝ e z : ℝ) • e + (σ : ℝ) • perp e z) := by
  rw [sqL_apply', Tube.dilateAux_apply, frame_direction, perp]
  congr 1
  module

theorem norm_sqL_le {σ : ℝ≥0} (hσ1 : σ ≤ 1) {e : E} (he : ‖e‖ = 1) (z : E) :
    ‖sqL σ he z‖ ≤ (1 / 4 : ℝ) * ‖z‖ := by
  have hσ1' : (σ : ℝ) ≤ 1 := by exact_mod_cast hσ1
  have hσ0' : (0 : ℝ) ≤ (σ : ℝ) := σ.coe_nonneg
  have hw : (inner ℝ e ((σ : ℝ) • perp e z) : ℝ) = 0 := by
    rw [real_inner_smul_right, inner_perp he, mul_zero]
  have hsq : ‖(inner ℝ e z : ℝ) • e + (σ : ℝ) • perp e z‖ ^ 2
      = (inner ℝ e z : ℝ) ^ 2 + ((σ : ℝ) * ‖perp e z‖) ^ 2 := by
    rw [norm_smul_add_sq he _ hw, norm_smul, Real.norm_eq_abs, abs_of_nonneg hσ0']
  have hle : ‖(inner ℝ e z : ℝ) • e + (σ : ℝ) • perp e z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [hsq, norm_sq_eq_inner_sq_add_norm_perp_sq he z]
    have hp : (0 : ℝ) ≤ ‖perp e z‖ := norm_nonneg _
    have hexp : ((σ : ℝ) * ‖perp e z‖) ^ 2 = (σ : ℝ) ^ 2 * ‖perp e z‖ ^ 2 := by ring
    have hs2 : (σ : ℝ) ^ 2 ≤ 1 := by nlinarith
    have h1 : ((σ : ℝ) * ‖perp e z‖) ^ 2 ≤ ‖perp e z‖ ^ 2 := by
      rw [hexp]
      nlinarith [sq_nonneg ‖perp e z‖, mul_nonneg (sub_nonneg.mpr hs2) (sq_nonneg ‖perp e z‖)]
    linarith
  have hnn : (0 : ℝ) ≤ ‖(inner ℝ e z : ℝ) • e + (σ : ℝ) • perp e z‖ := norm_nonneg _
  have hbase : ‖(inner ℝ e z : ℝ) • e + (σ : ℝ) • perp e z‖ ≤ ‖z‖ := by
    nlinarith [norm_nonneg z]
  rw [sqL_apply, norm_smul, Real.norm_eq_abs]
  have : |(1 / 4 : ℝ)| = 1 / 4 := by norm_num
  rw [this]
  linarith


theorem sqL_sqLinv {σ : ℝ≥0} (hσ : 0 < σ) {e : E} (he : ‖e‖ = 1) (z : E) :
    sqL σ he (sqLinv σ he z) = z := by
  have hσ' : (σ : ℝ) ≠ 0 := ne_of_gt (NNReal.coe_pos.mpr hσ)
  show (1 / 4 : ℝ) • ((frame σ he).dilateAux (σ : ℝ)
      ((4 : ℝ) • (frame σ he).dilateAux ((σ : ℝ)⁻¹) z)) = z
  rw [map_smul, Tube.dilateAux_comp, mul_inv_cancel₀ hσ', Tube.dilateAux_one]
  simp

theorem sqLinv_sqL {σ : ℝ≥0} (hσ : 0 < σ) {e : E} (he : ‖e‖ = 1) (z : E) :
    sqLinv σ he (sqL σ he z) = z := by
  have hσ' : (σ : ℝ) ≠ 0 := ne_of_gt (NNReal.coe_pos.mpr hσ)
  show (4 : ℝ) • ((frame σ he).dilateAux ((σ : ℝ)⁻¹)
      ((1 / 4 : ℝ) • (frame σ he).dilateAux (σ : ℝ) z)) = z
  rw [map_smul, Tube.dilateAux_comp, inv_mul_cancel₀ hσ', Tube.dilateAux_one]
  simp

/-- The squeeze as a linear equivalence. -/
noncomputable def sqLE {σ : ℝ≥0} (hσ : 0 < σ) {e : E} (he : ‖e‖ = 1) : E ≃ₗ[ℝ] E :=
  LinearEquiv.ofLinear (sqL σ he).toLinearMap (sqLinv σ he).toLinearMap
    (by ext z; exact sqL_sqLinv hσ he z) (by ext z; exact sqLinv_sqL hσ he z)

/-- The squeeze as an affine equivalence, which is what the transport laws consume. -/
noncomputable def sqA {σ : ℝ≥0} (hσ : 0 < σ) {e : E} (he : ‖e‖ = 1) : E ≃ᵃ[ℝ] E :=
  (sqLE hσ he).toAffineEquiv

@[simp] theorem sqA_apply {σ : ℝ≥0} (hσ : 0 < σ) {e : E} (he : ‖e‖ = 1) (z : E) :
    sqA hσ he z = sqL σ he z := rfl


end Squeeze

/-! ## The volume factor of the squeeze -/

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

omit [Nontrivial E] in
theorem normalization_frame (σ : ℝ≥0) {e : E} (he : ‖e‖ = 1) (z : E) :
    (frame σ he).normalization z = (frame σ he).dilateAux ((σ : ℝ)⁻¹) z := by
  rw [Tube.normalization_apply, Tube.dilateAux_apply, frame_direction, frame_x, sub_zero,
    zero_add]
  module

omit [Nontrivial E] in
theorem normalization_frame_dilate {σ : ℝ≥0} (hσ : 0 < σ) {e : E} (he : ‖e‖ = 1) (z : E) :
    (frame σ he).normalization ((frame σ he).dilateAux (σ : ℝ) z) = z := by
  have hσ' : (σ : ℝ) ≠ 0 := ne_of_gt (NNReal.coe_pos.mpr hσ)
  rw [normalization_frame, Tube.dilateAux_comp, inv_mul_cancel₀ hσ', Tube.dilateAux_one]
  simp

/-- **The anisotropic dilation multiplies every volume by `σ ^ (n-1)`.** -/
theorem volume_dilate_image {σ : ℝ≥0} (hσ : 0 < σ) {e : E} (he : ‖e‖ = 1) (B : Set E) :
    volume ((frame σ he).dilateAux (σ : ℝ) '' B)
      = (σ : ℝ≥0∞) ^ (Module.finrank ℝ E - 1) * volume B := by
  set k := Module.finrank ℝ E - 1 with hk
  have hne : (σ : ℝ≥0∞) ≠ 0 := by
    simpa using (ENNReal.coe_pos.mpr hσ).ne'
  have htop : (σ : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have himg : (frame σ he).normalization '' ((frame σ he).dilateAux (σ : ℝ) '' B) = B := by
    rw [Set.image_image]
    have : ∀ x ∈ B, (frame σ he).normalization ((frame σ he).dilateAux (σ : ℝ) x) = x :=
      fun x _ => normalization_frame_dilate hσ he x
    rw [Set.image_congr this]
    exact Set.image_id' B
  have hvol := Tube.volume_image_normalization hσ (frame σ he)
    ((frame σ he).dilateAux (σ : ℝ) '' B)
  rw [himg] at hvol
  have hcancel : (σ : ℝ≥0∞) ^ k * ((σ : ℝ≥0∞)⁻¹) ^ k = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel hne htop, one_pow]
  calc volume ((frame σ he).dilateAux (σ : ℝ) '' B)
      = 1 * volume ((frame σ he).dilateAux (σ : ℝ) '' B) := (one_mul _).symm
    _ = ((σ : ℝ≥0∞) ^ k * ((σ : ℝ≥0∞)⁻¹) ^ k)
          * volume ((frame σ he).dilateAux (σ : ℝ) '' B) := by rw [hcancel]
    _ = (σ : ℝ≥0∞) ^ k * (((σ : ℝ≥0∞)⁻¹) ^ k
          * volume ((frame σ he).dilateAux (σ : ℝ) '' B)) := by ring
    _ = (σ : ℝ≥0∞) ^ k * volume B := by rw [← hvol]

/-- **The squeeze multiplies every volume by `4^{-n} σ^{n-1}`.** -/
theorem volume_sqL_image {σ : ℝ≥0} (hσ : 0 < σ) {e : E} (he : ‖e‖ = 1) (B : Set E) :
    volume (sqL σ he '' B)
      = ENNReal.ofReal |(1 / 4 : ℝ) ^ Module.finrank ℝ E|
        * ((σ : ℝ≥0∞) ^ (Module.finrank ℝ E - 1) * volume B) := by
  have himg : (sqL σ he) '' B = (1 / 4 : ℝ) • (((frame σ he).dilateAux (σ : ℝ)) '' B : Set E) := by
    rw [← Set.image_smul, Set.image_image]
    rfl
  rw [himg, Measure.addHaar_smul, volume_dilate_image hσ he]

end Volume

/-! ## The squeezed tube is contained in an honest `δ`-tube -/

section Containment

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- Every point of the core segment of a tube is `midpoint + t • direction`, `|t| ≤ 1/2`. -/
theorem exists_param_of_mem_segment {ρ : ℝ≥0} (S : Tube ρ E) {c : E}
    (hc : c ∈ segment ℝ S.x S.y) :
    ∃ t : ℝ, |t| ≤ 1 / 2 ∧ c = S.midpoint + t • S.direction := by
  obtain ⟨α, β, hα, hβ, hab, hcc⟩ := hc
  refine ⟨(β - α) / 2, ?_, ?_⟩
  · rw [abs_le]
    constructor <;> linarith
  · rw [← hcc]
    show α • S.x + β • S.y
        = (1 / 2 : ℝ) • (S.x + S.y) + ((β - α) / 2) • (S.y - S.x)
    have hα' : α = 1 - β := by linarith
    rw [hα']
    module

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem sqL_injective {σ : ℝ≥0} (hσ : 0 < σ) {e : E} (he : ‖e‖ = 1) :
    Function.Injective (sqL σ he) := by
  intro z w h
  have := congrArg (sqLinv σ he) h
  rwa [sqLinv_sqL hσ he, sqLinv_sqL hσ he] at this

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem sqL_x_ne_sqL_y {σ ρ : ℝ≥0} (hσ : 0 < σ) {e : E} (he : ‖e‖ = 1) (S : Tube ρ E) :
    sqL σ he S.x ≠ sqL σ he S.y := fun h => by
  have hxy : S.x ≠ S.y := by
    intro hxy
    have := S.dist_eq_one
    rw [hxy, dist_self] at this
    exact zero_ne_one this
  exact hxy (sqL_injective hσ he h)

variable {σ ρ δ : ℝ≥0} {e : E}

/-- **The squeezed tube.**  The honest `δ`-tube that receives `A '' S.carrier`. -/
noncomputable def sqTube (hσ : 0 < σ) (he : ‖e‖ = 1) (δ : ℝ≥0) (S : Tube ρ E) : Tube δ E :=
  Tube.centredExtension δ (sqL_x_ne_sqL_y hσ he S)

omit [Nontrivial E] in
theorem sqTube_direction (hσ : 0 < σ) (he : ‖e‖ = 1) (δ : ℝ≥0) (S : Tube ρ E) :
    (sqTube hσ he δ S).direction
      = ‖sqL σ he S.y - sqL σ he S.x‖⁻¹ • (sqL σ he S.y - sqL σ he S.x) :=
  Tube.direction_centredExtension _

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem sqTube_midpoint (hσ : 0 < σ) (he : ‖e‖ = 1) (δ : ℝ≥0) (S : Tube ρ E) :
    (sqTube hσ he δ S).midpoint = sqL σ he S.midpoint := by
  set p := sqL σ he S.x
  set q := sqL σ he S.y
  set g : E := ‖q - p‖⁻¹ • (q - p) with hg
  have hx : (sqTube hσ he δ S).x = _root_.midpoint ℝ p q - (1 / 2 : ℝ) • g := rfl
  have hy : (sqTube hσ he δ S).y = _root_.midpoint ℝ p q + (1 / 2 : ℝ) • g := rfl
  have hmap : sqL σ he S.midpoint = (1 / 2 : ℝ) • (p + q) := by
    show sqL σ he ((1 / 2 : ℝ) • (S.x + S.y)) = _
    rw [map_smul, map_add]
  show (1 / 2 : ℝ) • ((sqTube hσ he δ S).x + (sqTube hσ he δ S).y) = _
  rw [hx, hy, hmap, midpoint_eq_smul_add, invOf_eq_inv]
  module

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem norm_perp_unit_le {u : E} (hu : ‖u‖ = 1) (v : E) : ‖perp u v‖ ≤ ‖u - v‖ := by
  have hsplit : perp u v = perp u (v - u) := by
    have : v = (v - u) + u := by abel
    rw [this, perp_add, perp_self hu, add_zero, add_sub_cancel_right]
  rw [hsplit]
  exact (norm_perp_le hu _).trans_eq (norm_sub_rev v u)

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- **The transverse displacement of the squeeze.**  If the axis `u` is within `4σ` of the frame
direction `e`, then `A w` is within `(5/4)σr` of the line `ℝ ∙ u` whenever `‖w‖ ≤ r`. -/
theorem norm_perp_sqL_le (hσ0 : 0 < σ) (he : ‖e‖ = 1) {u : E} (hu : ‖u‖ = 1)
    (hue : ‖u - e‖ ≤ 4 * (σ : ℝ)) {w : E} {r : ℝ} (hw : ‖w‖ ≤ r) :
    ‖perp u (sqL σ he w)‖ ≤ (5 / 4) * ((σ : ℝ) * r) := by
  have hσ0' : (0 : ℝ) < (σ : ℝ) := NNReal.coe_pos.mpr hσ0
  have hr : (0 : ℝ) ≤ r := le_trans (norm_nonneg w) hw
  have hexp : perp u (sqL σ he w)
      = (1 / 4 : ℝ) • ((inner ℝ e w : ℝ) • perp u e + (σ : ℝ) • perp u (perp e w)) := by
    rw [sqL_apply, perp_smul, perp_add, perp_smul, perp_smul]
  have h1 : ‖perp u e‖ ≤ 4 * (σ : ℝ) := (norm_perp_unit_le hu e).trans hue
  have h2 : ‖perp u (perp e w)‖ ≤ r :=
    ((norm_perp_le hu _).trans (norm_perp_le he w)).trans hw
  have h3 : |(inner ℝ e w : ℝ)| ≤ r := (abs_inner_le_norm_of_unit he w).trans hw
  have hb : ‖(inner ℝ e w : ℝ) • perp u e + (σ : ℝ) • perp u (perp e w)‖
      ≤ 5 * ((σ : ℝ) * r) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hσ0'.le]
    have hA : |(inner ℝ e w : ℝ)| * ‖perp u e‖ ≤ r * (4 * (σ : ℝ)) :=
      mul_le_mul h3 h1 (norm_nonneg _) hr
    have hB : (σ : ℝ) * ‖perp u (perp e w)‖ ≤ (σ : ℝ) * r :=
      mul_le_mul_of_nonneg_left h2 hσ0'.le
    nlinarith
  rw [hexp, norm_smul, Real.norm_eq_abs, show |(1 / 4 : ℝ)| = 1 / 4 by norm_num]
  linarith

omit [Nontrivial E] in
set_option maxHeartbeats 1000000 in
/-- **The geometric core.**  Inside a cap of directions around `e`, the squeeze `A` maps a
`ρ`-tube into an honest `δ`-tube, provided `2σρ ≤ δ`. -/
theorem sqL_image_subset_sqTube (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hρ1 : ρ ≤ 1)
    (he : ‖e‖ = 1) (S : Tube ρ E) (hcap : (1 : ℝ) / 2 ≤ (inner ℝ e S.direction : ℝ))
    (hδ : 2 * σ * ρ ≤ δ) :
    (sqL σ he) '' S.carrier ⊆ (sqTube hσ0 he δ S).carrier := by
  have hσ0' : (0 : ℝ) < (σ : ℝ) := NNReal.coe_pos.mpr hσ0
  have hσ1' : ((σ : ℝ)) ≤ 1 := by exact_mod_cast hσ1
  have hρ0' : (0 : ℝ) ≤ (ρ : ℝ) := ρ.coe_nonneg
  have hρ1' : ((ρ : ℝ)) ≤ 1 := by exact_mod_cast hρ1
  have hδ' : 2 * (σ : ℝ) * (ρ : ℝ) ≤ (δ : ℝ) := by exact_mod_cast hδ
  set d : E := S.direction with hd
  set a : ℝ := (inner ℝ e d : ℝ) with ha_def
  set P : E := perp e d with hP_def
  set n : ℝ := ‖a • e + (σ : ℝ) • P‖ with hn_def
  set T' : Tube δ E := sqTube hσ0 he δ S with hT'
  have hd1 : ‖d‖ = 1 := S.norm_direction
  have hP1 : ‖P‖ ≤ 1 := by
    rw [hP_def]
    exact (norm_perp_le he d).trans_eq hd1
  have hP0 : (0 : ℝ) ≤ ‖P‖ := norm_nonneg _
  have ha1 : a ≤ 1 := by
    have h := abs_inner_le_norm_of_unit he d
    rw [hd1] at h
    exact le_trans (le_abs_self a) h
  have hw0 : (inner ℝ e ((σ : ℝ) • P) : ℝ) = 0 := by
    rw [real_inner_smul_right, hP_def, inner_perp he, mul_zero]
  have hn2 : n ^ 2 = a ^ 2 + ((σ : ℝ) * ‖P‖) ^ 2 := by
    rw [hn_def, norm_smul_add_sq he a hw0, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hσ0'.le]
  have hn0' : (0 : ℝ) ≤ n := norm_nonneg _
  have hna : a ≤ n := by nlinarith [sq_nonneg ((σ : ℝ) * ‖P‖)]
  have hnu : n ≤ a + (σ : ℝ) * ‖P‖ := by nlinarith [mul_nonneg hσ0'.le hP0]
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by linarith) hna
  have hnne : n ≠ 0 := ne_of_gt hn0
  have hdsq : (1 : ℝ) = a ^ 2 + ‖P‖ ^ 2 := by
    rw [hP_def, ha_def, ← norm_sq_eq_inner_sq_add_norm_perp_sq he d, hd1, one_pow]
  have hs2 : (σ : ℝ) ^ 2 ≤ 1 := by nlinarith
  have hnsq1 : n ^ 2 ≤ 1 := by
    have hexp : ((σ : ℝ) * ‖P‖) ^ 2 = (σ : ℝ) ^ 2 * ‖P‖ ^ 2 := by ring
    nlinarith [sq_nonneg ‖P‖, mul_nonneg (sub_nonneg.mpr hs2) (sq_nonneg ‖P‖)]
  have hnle1 : n ≤ 1 := by nlinarith
  -- the image of the core direction
  have hAd : sqL σ he d = (1 / 4 : ℝ) • (a • e + (σ : ℝ) • P) := sqL_apply σ he d
  have hqp : sqL σ he S.y - sqL σ he S.x = sqL σ he d := by
    rw [hd]
    show _ = sqL σ he (S.y - S.x)
    rw [map_sub]
  have hAdnorm : ‖sqL σ he d‖ = n / 4 := by
    rw [hAd, norm_smul, Real.norm_eq_abs, show |(1 / 4 : ℝ)| = 1 / 4 by norm_num, ← hn_def]
    ring
  have hAdne : ‖sqL σ he d‖ ≠ 0 := by rw [hAdnorm]; positivity
  -- the axis of the image tube
  have hdirT : T'.direction = ‖sqL σ he d‖⁻¹ • sqL σ he d := by
    rw [hT', sqTube_direction, hqp]
  have hquart : ((n : ℝ) / 4)⁻¹ * (1 / 4 : ℝ) = (n : ℝ)⁻¹ := by
    rw [inv_div, div_mul_eq_mul_div]
    norm_num
  have hu : T'.direction = (n : ℝ)⁻¹ • (a • e + (σ : ℝ) • P) := by
    rw [hdirT, hAdnorm, hAd, smul_smul, hquart]
  have hu1 : ‖T'.direction‖ = 1 := T'.norm_direction
  have hue : ‖T'.direction - e‖ ≤ 4 * (σ : ℝ) := by
    have hstep : (n : ℝ)⁻¹ • (a • e + (σ : ℝ) • P) - e
        = (n : ℝ)⁻¹ • ((a - n) • e + (σ : ℝ) • P) := by
      match_scalars <;> field_simp [hnne]
    have hinv0 : (0 : ℝ) ≤ (n : ℝ)⁻¹ := le_of_lt (inv_pos.mpr hn0)
    have h3 : (n : ℝ)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hn0 (by norm_num : (0:ℝ) < 2)]
      linarith
    have h1 : ‖(a - n) • e + (σ : ℝ) • P‖ ≤ |a - n| + (σ : ℝ) * ‖P‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, he, mul_one,
        abs_of_nonneg hσ0'.le]
    have h2 : |a - n| ≤ (σ : ℝ) * ‖P‖ := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith : (0:ℝ) ≤ n - a)]
      linarith
    rw [hu, hstep, norm_smul, Real.norm_eq_abs, abs_of_nonneg hinv0]
    have hbound : ‖(a - n) • e + (σ : ℝ) • P‖ ≤ 2 * ((σ : ℝ) * ‖P‖) := by linarith
    have hnn : (0 : ℝ) ≤ ‖(a - n) • e + (σ : ℝ) • P‖ := norm_nonneg _
    nlinarith [mul_nonneg hσ0'.le hP0]
  have hAd_u : sqL σ he d = ‖sqL σ he d‖ • T'.direction := by
    rw [hdirT, smul_smul, mul_inv_cancel₀ hAdne, one_smul]
  have hmid : T'.midpoint = sqL σ he S.midpoint := by
    rw [hT']
    exact sqTube_midpoint hσ0 he δ S
  clear_value T'
  -- the containment
  intro y hy
  obtain ⟨z, hz, rfl⟩ := hy
  rw [S.carrier_eq] at hz
  obtain ⟨c, hc, hzc⟩ := Set.mem_iUnion₂.mp hz
  obtain ⟨t, ht, rfl⟩ := exists_param_of_mem_segment S hc
  set w : E := z - (S.midpoint + t • d) with hw_def
  have hwnorm : ‖w‖ ≤ (ρ : ℝ) := by
    rw [hw_def, ← dist_eq_norm]
    exact Metric.mem_closedBall.mp hzc
  have hzw : z = (S.midpoint + t • d) + w := by rw [hw_def]; abel
  clear_value w
  set τ : ℝ := t * ‖sqL σ he d‖ + (inner ℝ T'.direction (sqL σ he w) : ℝ) with hτ
  have hlin : sqL σ he z = sqL σ he (S.midpoint + t • d) + sqL σ he w := by
    conv_lhs => rw [hzw]
    exact map_add (sqL σ he) _ _
  have hlinmid : sqL σ he (S.midpoint + t • d)
      = sqL σ he S.midpoint + t • sqL σ he d := by
    simp only [Tube.midpoint, map_add, map_smul]
  have hcore : sqL σ he (S.midpoint + t • d)
      = T'.midpoint + (t * ‖sqL σ he d‖) • T'.direction := by
    rw [hlinmid, hmid, mul_smul, ← hAd_u]
  have hAz : sqL σ he z
      = (T'.midpoint + τ • T'.direction) + perp T'.direction (sqL σ he w) := by
    rw [hlin, hcore, hτ, perp]
    module
  -- the scalar bounds on `τ`
  have hb1 : |t * ‖sqL σ he d‖| ≤ 1 / 8 := by
    rw [abs_mul, abs_of_nonneg (norm_nonneg _), hAdnorm]
    have hmul : |t| * (n / 4) ≤ (1 / 2) * (1 / 4) :=
      mul_le_mul ht (by linarith) (by positivity) (by norm_num)
    linarith
  have hAwsmall : ‖sqL σ he w‖ ≤ 1 / 4 := by
    have hb := norm_sqL_le hσ1 he w
    linarith
  have hb2 : |(inner ℝ T'.direction (sqL σ he w) : ℝ)| ≤ 1 / 4 :=
    le_trans (abs_inner_le_norm_of_unit hu1 (sqL σ he w)) hAwsmall
  have hτabs : |τ| ≤ 1 / 2 := by
    have h1 := abs_le.mp hb1
    have h2 := abs_le.mp hb2
    rw [hτ, abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  rw [T'.carrier_eq]
  refine Set.mem_iUnion₂.mpr ⟨T'.midpoint + τ • T'.direction, ?_, ?_⟩
  · exact T'.midpoint_add_smul_direction_mem_segment (by linarith [abs_le.mp hτabs])
      (abs_le.mp hτabs).2
  · rw [Metric.mem_closedBall, dist_eq_norm, hAz]
    have hcancel : (T'.midpoint + τ • T'.direction) + perp T'.direction (sqL σ he w)
        - (T'.midpoint + τ • T'.direction) = perp T'.direction (sqL σ he w) := by abel
    rw [hcancel]
    have hfin := norm_perp_sqL_le hσ0 he hu1 hue hwnorm
    have hcmp : (5 / 4) * ((σ : ℝ) * (ρ : ℝ)) ≤ 2 * (σ : ℝ) * (ρ : ℝ) := by
      nlinarith [mul_nonneg hσ0'.le hρ0']
    linarith

/-! ## The squeezed tube lies in `B₁`, and its volume is comparable -/

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem tube_x_mem_carrier (S : Tube ρ E) : S.x ∈ S.carrier := by
  rw [S.carrier_eq]
  exact Set.mem_iUnion₂.mpr ⟨S.x, left_mem_segment ℝ S.x S.y,
    Metric.mem_closedBall_self ρ.coe_nonneg⟩

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem tube_y_mem_carrier (S : Tube ρ E) : S.y ∈ S.carrier := by
  rw [S.carrier_eq]
  exact Set.mem_iUnion₂.mpr ⟨S.y, right_mem_segment ℝ S.x S.y,
    Metric.mem_closedBall_self ρ.coe_nonneg⟩

omit [Nontrivial E] in
theorem sqTube_subset_closedBall (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (he : ‖e‖ = 1) (S : Tube ρ E)
    (hS : S.carrier ⊆ Metric.closedBall (0 : E) 1) (hδ4 : (δ : ℝ) ≤ 1 / 4) :
    (sqTube hσ0 he δ S).carrier ⊆ Metric.closedBall (0 : E) 1 := by
  refine Tube.centredExtension_subset_closedBall _ ?_ ?_ hδ4
  · rw [dist_zero_right]
    have h1 : ‖S.x‖ ≤ 1 := by
      simpa [dist_zero_right] using hS (tube_x_mem_carrier S)
    have h2 := norm_sqL_le hσ1 he S.x
    linarith
  · rw [dist_zero_right]
    have h1 : ‖S.y‖ ≤ 1 := by
      simpa [dist_zero_right] using hS (tube_y_mem_carrier S)
    have h2 := norm_sqL_le hσ1 he S.y
    linarith

/-- The volume loss of re-presenting the squeezed tube as an honest `δ`-tube.  It is an
absolute constant: it depends on the ambient dimension and on nothing else. -/
noncomputable def fatLoss : ℝ≥0 :=
  1 + 256 * Tube.volume_le.C 3 / Tube.le_volume.c 3

theorem one_le_fatLoss : 1 ≤ fatLoss := le_self_add

theorem fatLoss_ne_zero : fatLoss ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one one_le_fatLoss)

theorem four_mul_volume_le_C_le : 4 * Tube.volume_le.C 3
    ≤ fatLoss * ((1 / 64 : ℝ≥0) * Tube.le_volume.c 3) := by
  have hc : Tube.le_volume.c 3 ≠ 0 := ne_of_gt (Tube.le_volume.c_pos 3)
  have hkey : (256 * Tube.volume_le.C 3 / Tube.le_volume.c 3)
      * ((1 / 64 : ℝ≥0) * Tube.le_volume.c 3) = 4 * Tube.volume_le.C 3 := by
    field_simp
    ring
  calc 4 * Tube.volume_le.C 3
      = (256 * Tube.volume_le.C 3 / Tube.le_volume.c 3)
          * ((1 / 64 : ℝ≥0) * Tube.le_volume.c 3) := hkey.symm
    _ ≤ fatLoss * ((1 / 64 : ℝ≥0) * Tube.le_volume.c 3) := by
        gcongr
        exact le_add_self

/-- **The re-presentation costs one absolute constant in volume.** -/
theorem sqTube_volume_le (hn : Module.finrank ℝ E = 3) (hσ0 : 0 < σ) (he : ‖e‖ = 1)
    (S : Tube ρ E) (hδ1 : 2 * σ * ρ ≤ 1) :
    volume (sqTube hσ0 he (2 * σ * ρ) S).carrier
      ≤ (fatLoss : ℝ≥0∞) * volume ((sqL σ he) '' S.carrier) := by
  have hup : volume (sqTube hσ0 he (2 * σ * ρ) S).carrier
      ≤ ((Tube.volume_le.C 3 : ℝ≥0) : ℝ≥0∞) * ((2 * σ * ρ : ℝ≥0) : ℝ≥0∞) ^ 2 := by
    have h := Tube.volume_le hδ1 (sqTube hσ0 he (2 * σ * ρ) S)
    rw [hn] at h
    simpa using h
  have hlow0 : ((Tube.le_volume.c 3 : ℝ≥0) : ℝ≥0∞) * ((ρ : ℝ≥0) : ℝ≥0∞) ^ 2
      ≤ volume S.carrier := by
    have h := Tube.le_volume (E := E) S
    rw [hn] at h
    simpa using h
  have hvol : volume ((sqL σ he) '' S.carrier)
      = ENNReal.ofReal |(1 / 4 : ℝ) ^ 3| * (((σ : ℝ≥0) : ℝ≥0∞) ^ 2 * volume S.carrier) := by
    have h := volume_sqL_image hσ0 he S.carrier
    rw [hn] at h
    simpa using h
  have hofReal : ENNReal.ofReal |(1 / 4 : ℝ) ^ 3| = ((1 / 64 : ℝ≥0) : ℝ≥0∞) := by
    rw [show |(1 / 4 : ℝ) ^ 3| = ((1 / 64 : ℝ≥0) : ℝ) by norm_num]
    exact ENNReal.ofReal_coe_nnreal
  rw [hvol, hofReal]
  have hsq : ((2 * σ * ρ : ℝ≥0) : ℝ≥0∞) ^ 2
      = ((4 : ℝ≥0) : ℝ≥0∞)
        * (((σ : ℝ≥0) : ℝ≥0∞) ^ 2 * ((ρ : ℝ≥0) : ℝ≥0∞) ^ 2) := by
    push_cast
    ring
  refine le_trans hup ?_
  rw [hsq]
  have hstep1 : ((1 / 64 : ℝ≥0) : ℝ≥0∞)
        * (((σ : ℝ≥0) : ℝ≥0∞) ^ 2 * (((Tube.le_volume.c 3 : ℝ≥0) : ℝ≥0∞)
          * ((ρ : ℝ≥0) : ℝ≥0∞) ^ 2))
      ≤ ((1 / 64 : ℝ≥0) : ℝ≥0∞)
        * (((σ : ℝ≥0) : ℝ≥0∞) ^ 2 * volume S.carrier) := by
    gcongr
  refine le_trans ?_ (mul_le_mul_right hstep1 ((fatLoss : ℝ≥0) : ℝ≥0∞))
  have hconst : ((Tube.volume_le.C 3 : ℝ≥0) : ℝ≥0∞) * ((4 : ℝ≥0) : ℝ≥0∞)
      ≤ ((fatLoss : ℝ≥0) : ℝ≥0∞)
        * (((1 / 64 : ℝ≥0) : ℝ≥0∞) * ((Tube.le_volume.c 3 : ℝ≥0) : ℝ≥0∞)) := by
    rw [← ENNReal.coe_mul, ← ENNReal.coe_mul, ← ENNReal.coe_mul]
    exact_mod_cast (by rw [mul_comm]; exact four_mul_volume_le_C_le)
  calc ((Tube.volume_le.C 3 : ℝ≥0) : ℝ≥0∞)
        * (((4 : ℝ≥0) : ℝ≥0∞) * ((((σ : ℝ≥0) : ℝ≥0∞) ^ 2)
            * ((ρ : ℝ≥0) : ℝ≥0∞) ^ 2))
      = (((Tube.volume_le.C 3 : ℝ≥0) : ℝ≥0∞) * ((4 : ℝ≥0) : ℝ≥0∞))
          * (((σ : ℝ≥0) : ℝ≥0∞) ^ 2 * ((ρ : ℝ≥0) : ℝ≥0∞) ^ 2) := by ring
    _ ≤ (((fatLoss : ℝ≥0) : ℝ≥0∞)
          * (((1 / 64 : ℝ≥0) : ℝ≥0∞) * ((Tube.le_volume.c 3 : ℝ≥0) : ℝ≥0∞)))
          * (((σ : ℝ≥0) : ℝ≥0∞) ^ 2 * ((ρ : ℝ≥0) : ℝ≥0∞) ^ 2) := by
        gcongr
    _ = ((fatLoss : ℝ≥0) : ℝ≥0∞) * (((1 / 64 : ℝ≥0) : ℝ≥0∞)
          * (((σ : ℝ≥0) : ℝ≥0∞) ^ 2 * (((Tube.le_volume.c 3 : ℝ≥0) : ℝ≥0∞)
            * ((ρ : ℝ≥0) : ℝ≥0∞) ^ 2))) := by ring

/-! ## The squeezed family as honest `δ`-tubes -/

/-- **The squeezed shaded tube.**  Carrier the honest outer `δ`-tube, shade the squeezed shade
intersected with that carrier, so that the definition is total. -/
noncomputable def sqShadedTube (hσ0 : 0 < σ) (he : ‖e‖ = 1) (δ : ℝ≥0)
    (S : ShadedTube ρ E) : ShadedTube δ E where
  toTube := sqTube hσ0 he δ S.toTube
  shade := ((sqA hσ0 he) '' S.shade) ∩ (sqTube hσ0 he δ S.toTube).carrier
  measurableSet_shade :=
    (Kakeya.measurableSet_affineEquiv_image (sqA hσ0 he) S.measurableSet_shade).inter
      (sqTube hσ0 he δ S.toTube).isCompact'.isClosed.measurableSet
  shade_subset := Set.inter_subset_right

omit [Nontrivial E] in
@[simp] theorem sqShadedTube_carrier (hσ0 : 0 < σ) (he : ‖e‖ = 1) (δ : ℝ≥0)
    (S : ShadedTube ρ E) :
    (sqShadedTube hσ0 he δ S).carrier = (sqTube hσ0 he δ S.toTube).carrier := rfl

omit [Nontrivial E] in
@[simp] theorem sqShadedTube_shade (hσ0 : 0 < σ) (he : ‖e‖ = 1) (δ : ℝ≥0)
    (S : ShadedTube ρ E) :
    (sqShadedTube hσ0 he δ S).shade
      = ((sqA hσ0 he) '' S.shade) ∩ (sqTube hσ0 he δ S.toTube).carrier := rfl

omit [Nontrivial E] in
theorem sqShadedTube_shade_eq (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hρ1 : ρ ≤ 1) (he : ‖e‖ = 1)
    (S : ShadedTube ρ E) (hcap : (1 : ℝ) / 2 ≤ (inner ℝ e S.direction : ℝ))
    (hδ : 2 * σ * ρ ≤ δ) :
    (sqShadedTube hσ0 he δ S).shade = (sqA hσ0 he) '' S.shade := by
  refine Set.inter_eq_self_of_subset_left ?_
  refine (Set.image_mono S.shade_subset).trans ?_
  exact sqL_image_subset_sqTube hσ0 hσ1 hρ1 he S.toTube hcap hδ

/-- The squeezed family. -/
noncomputable def sqFamily {ι : Type*} (hσ0 : 0 < σ) (he : ‖e‖ = 1) (δ : ℝ≥0)
    (T : ι → ShadedTube ρ E) : ι → ShadedTube δ E :=
  fun i => sqShadedTube hσ0 he δ (T i)

section Family

variable {ι : Type*} {s : Finset ι} {T : ι → ShadedTube ρ E}

omit [Nontrivial E] in
theorem sqFamily_shade_eq (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hρ1 : ρ ≤ 1) (he : ‖e‖ = 1)
    (hcap : ∀ i ∈ s, (1 : ℝ) / 2 ≤ (inner ℝ e (T i).direction : ℝ)) (hδ : 2 * σ * ρ ≤ δ) :
    ∀ i ∈ s, (sqFamily hσ0 he δ T i).toShadedBody.shade
      = (Kakeya.ML2Reduction.spineFamily (sqA hσ0 he) T i).shade := fun i hi =>
  sqShadedTube_shade_eq hσ0 hσ1 hρ1 he (T i) (hcap i hi) hδ

omit [Nontrivial E] in
theorem sqFamily_le (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hρ1 : ρ ≤ 1) (he : ‖e‖ = 1)
    (hcap : ∀ i ∈ s, (1 : ℝ) / 2 ≤ (inner ℝ e (T i).direction : ℝ)) (hδ : 2 * σ * ρ ≤ δ) :
    ∀ i ∈ s, (Kakeya.ML2Reduction.spineFamily (sqA hσ0 he) T i).toConvexSpaceBody
      ≤ (sqFamily hσ0 he δ T i).toConvexSpaceBody := by
  intro i hi
  change (sqA hσ0 he) '' (T i).carrier ⊆ (sqTube hσ0 he δ (T i).toTube).carrier
  exact sqL_image_subset_sqTube hσ0 hσ1 hρ1 he (T i).toTube (hcap i hi) hδ

theorem sqFamily_volume_le (hn : Module.finrank ℝ E = 3) (hσ0 : 0 < σ) (he : ‖e‖ = 1)
    (hδ1 : 2 * σ * ρ ≤ 1) :
    ∀ i ∈ s, volume (sqFamily hσ0 he (2 * σ * ρ) T i).carrier
      ≤ (fatLoss : ℝ≥0∞)
        * volume (Kakeya.ML2Reduction.spineFamily (sqA hσ0 he) T i).carrier := fun i _ =>
  sqTube_volume_le hn hσ0 he (T i).toTube hδ1

omit [Nontrivial E] in
theorem sqFamily_carrier_subset_closedBall (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (he : ‖e‖ = 1)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) (hδ4 : (δ : ℝ) ≤ 1 / 4) :
    ∀ i ∈ s, (sqFamily hσ0 he δ T i).carrier ⊆ Metric.closedBall (0 : E) 1 := fun i hi =>
  sqTube_subset_closedBall hσ0 hσ1 he (T i).toTube (hball i hi) hδ4

/-- **`Δ_max` of the squeezed family costs one absolute constant.** -/
theorem sqFamily_maxDensity_le (hn : Module.finrank ℝ E = 3) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hρ1 : ρ ≤ 1) (he : ‖e‖ = 1)
    (hcap : ∀ i ∈ s, (1 : ℝ) / 2 ≤ (inner ℝ e (T i).direction : ℝ)) (hδ1 : 2 * σ * ρ ≤ 1) :
    Kakeya.maxDensity s (fun i => (sqFamily hσ0 he (2 * σ * ρ) T i).toConvexSpaceBody)
      ≤ (fatLoss : ℝ≥0∞) * Kakeya.maxDensity s (fun i => (T i).toConvexSpaceBody) := by
  have h := Kakeya.maxDensity_le_of_comparable (E := E) one_le_fatLoss s
    (fun i => (Kakeya.ML2Reduction.spineFamily (sqA hσ0 he) T i).toConvexSpaceBody)
    (fun i => (sqFamily hσ0 he (2 * σ * ρ) T i).toConvexSpaceBody)
    (sqFamily_le hσ0 hσ1 hρ1 he hcap le_rfl)
    (sqFamily_volume_le hn hσ0 he hδ1)
  rwa [Kakeya.ML2Reduction.spineFamily_maxDensity] at h

/-- **Fullness of the squeezed family costs one absolute constant.** -/
theorem sqFamily_le_fullness (hn : Module.finrank ℝ E = 3) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hρ1 : ρ ≤ 1) (he : ‖e‖ = 1)
    (hcap : ∀ i ∈ s, (1 : ℝ) / 2 ≤ (inner ℝ e (T i).direction : ℝ)) (hδ1 : 2 * σ * ρ ≤ 1) :
    fatLoss⁻¹ * ShadedBody.fullness s (fun i => (T i).toShadedBody)
      ≤ ShadedBody.fullness s
          (fun i => (sqFamily hσ0 he (2 * σ * ρ) T i).toShadedBody) := by
  have h := Tube.le_fullness_of_volume_le (E := E) one_le_fatLoss s
    (Kakeya.ML2Reduction.spineFamily (sqA hσ0 he) T)
    (fun i => (sqFamily hσ0 he (2 * σ * ρ) T i).toShadedBody)
    (sqFamily_shade_eq hσ0 hσ1 hρ1 he hcap le_rfl)
    (sqFamily_volume_le hn hσ0 he hδ1)
  rwa [Kakeya.ML2Reduction.spineFamily_fullness] at h

omit [Nontrivial E] in
/-- The shade mass of the squeezed family is the Jacobian times the original. -/
theorem sqFamily_sum_shade (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hρ1 : ρ ≤ 1) (he : ‖e‖ = 1)
    (hcap : ∀ i ∈ s, (1 : ℝ) / 2 ≤ (inner ℝ e (T i).direction : ℝ)) (hδ : 2 * σ * ρ ≤ δ) :
    ∑ i ∈ s, volume (sqFamily hσ0 he δ T i).shade
      = Kakeya.affineJacobian (sqA hσ0 he) * ∑ i ∈ s, volume (T i).shade := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [show (sqFamily hσ0 he δ T i).shade = (sqA hσ0 he) '' (T i).shade from
    sqShadedTube_shade_eq hσ0 hσ1 hρ1 he (T i) (hcap i hi) hδ]
  exact Kakeya.volume_image_affineEquiv _ _

omit [Nontrivial E] in
theorem sqFamily_iUnion_shade (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hρ1 : ρ ≤ 1) (he : ‖e‖ = 1)
    (hcap : ∀ i ∈ s, (1 : ℝ) / 2 ≤ (inner ℝ e (T i).direction : ℝ)) (hδ : 2 * σ * ρ ≤ δ) :
    volume (⋃ i ∈ s, (sqFamily hσ0 he δ T i).shade)
      = Kakeya.affineJacobian (sqA hσ0 he) * volume (⋃ i ∈ s, (T i).shade) := by
  have himg : (⋃ i ∈ s, (sqFamily hσ0 he δ T i).shade)
      = (sqA hσ0 he) '' (⋃ i ∈ s, (T i).shade) := by
    rw [Set.image_iUnion₂]
    refine Set.iUnion₂_congr fun i hi => ?_
    exact sqShadedTube_shade_eq hσ0 hσ1 hρ1 he (T i) (hcap i hi) hδ
  rw [himg]
  exact Kakeya.volume_image_affineEquiv _ _

end Family

end Containment

/-! ## The six direction caps of `S²` -/

section Caps

/-- The ambient space of Main Lemma 2. -/
abbrev Space3 := EuclideanSpace ℝ (Fin 3)

/-- The six cap centres `± e_j`.  Every unit vector of `ℝ³` makes an inner product at least
`1/2` with one of them, because some coordinate has square at least `1/3`. -/
noncomputable def capVec (k : Fin 3 × Bool) : Space3 :=
  if k.2 then EuclideanSpace.single k.1 (1 : ℝ) else -(EuclideanSpace.single k.1 (1 : ℝ))

theorem norm_capVec (k : Fin 3 × Bool) : ‖capVec k‖ = 1 := by
  unfold capVec
  split <;> simp

theorem inner_capVec (k : Fin 3 × Bool) (d : Space3) :
    (inner ℝ (capVec k) d : ℝ) = if k.2 then d k.1 else -(d k.1) := by
  unfold capVec
  split <;> simp [EuclideanSpace.inner_single_left]

theorem exists_cap {d : Space3} (hd : ‖d‖ = 1) :
    ∃ k : Fin 3 × Bool, (1 : ℝ) / 2 ≤ (inner ℝ (capVec k) d : ℝ) := by
  have hsum : ∑ j : Fin 3, (d j) ^ 2 = 1 := by
    have h : ‖d‖ ^ 2 = ∑ j : Fin 3, (d j) ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
      simp [sq]
    rw [← h, hd, one_pow]
  obtain ⟨j, -, hj⟩ := Finset.exists_le_of_sum_le (s := (Finset.univ : Finset (Fin 3)))
    (f := fun _ : Fin 3 => (1 : ℝ) / 3) (g := fun j => (d j) ^ 2)
    Finset.univ_nonempty (by simp [hsum])
  rcases le_or_gt 0 (d j) with h | h
  · exact ⟨(j, true), by rw [inner_capVec]; simp only [if_pos]; nlinarith⟩
  · refine ⟨(j, false), ?_⟩
    rw [inner_capVec]
    simp only [Bool.false_eq_true, if_false]
    nlinarith

open Classical in
/-- The cap a unit direction belongs to. -/
noncomputable def capIndex (d : Space3) : Fin 3 × Bool :=
  if h : ∃ k : Fin 3 × Bool, (1 : ℝ) / 2 ≤ (inner ℝ (capVec k) d : ℝ) then h.choose
  else (0, true)

theorem capIndex_spec {d : Space3} (hd : ‖d‖ = 1) :
    (1 : ℝ) / 2 ≤ (inner ℝ (capVec (capIndex d)) d : ℝ) := by
  classical
  rw [capIndex, dif_pos (exists_cap hd)]
  exact (exists_cap hd).choose_spec

/-- **The pigeonhole over the six caps.**  Some cap carries at least a sixth of the shade
mass. -/
theorem exists_heavy_cap {ρ : ℝ≥0} {ι : Type*} (s : Finset ι) (T : ι → ShadedTube ρ Space3) :
    ∃ k : Fin 3 × Bool,
      ∑ i ∈ s, volume (T i).shade
        ≤ 6 * ∑ i ∈ s with capIndex (T i).direction = k, volume (T i).shade := by
  classical
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 3 × Bool))
    (fun k => ∑ i ∈ s with capIndex (T i).direction = k, volume (T i).shade)
    ⟨(0, true), Finset.mem_univ _⟩
  refine ⟨k, ?_⟩
  calc ∑ i ∈ s, volume (T i).shade
      = ∑ k' : Fin 3 × Bool,
          ∑ i ∈ s with capIndex (T i).direction = k', volume (T i).shade :=
        (Finset.sum_fiberwise s (fun i => capIndex (T i).direction)
          (fun i => volume (T i).shade)).symm
    _ ≤ ∑ _k' : Fin 3 × Bool,
          ∑ i ∈ s with capIndex (T i).direction = k, volume (T i).shade :=
        Finset.sum_le_sum fun k' _ => hk k' (Finset.mem_univ k')
    _ = 6 * ∑ i ∈ s with capIndex (T i).direction = k, volume (T i).shade := by
        rw [Finset.sum_const, nsmul_eq_mul]
        norm_num

end Caps

/-! ## Fullness of a heavy subfamily -/

section Fullness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **A subfamily carrying a `c`-fraction of the shade mass keeps a `c`-fraction of the
fullness.**  No positivity hypothesis is needed: both bounds are ratios of the same two sums. -/
theorem mul_fullness_le_of_subset {ι : Type*} {s' s : Finset ι} (hsub : s' ⊆ s)
    (V : ι → ShadedBody E) {c : ℝ≥0}
    (hmass : (c : ℝ≥0∞) * ∑ i ∈ s, volume (V i).shade
      ≤ ∑ i ∈ s', volume (V i).shade) :
    c * ShadedBody.fullness s V ≤ ShadedBody.fullness s' V := by
  rw [← ENNReal.coe_le_coe, ENNReal.coe_mul, ShadedBody.fullness_def, ShadedBody.fullness_def]
  have hD : (∑ i ∈ s', volume (V i).carrier) ≤ ∑ i ∈ s, volume (V i).carrier :=
    Finset.sum_le_sum_of_subset hsub
  calc (c : ℝ≥0∞) * ((∑ i ∈ s, volume (V i).shade) / (∑ i ∈ s, volume (V i).carrier))
      = ((c : ℝ≥0∞) * ∑ i ∈ s, volume (V i).shade)
          / (∑ i ∈ s, volume (V i).carrier) := by
        rw [div_eq_mul_inv, ← mul_assoc, ← div_eq_mul_inv]
    _ ≤ (∑ i ∈ s', volume (V i).shade) / (∑ i ∈ s, volume (V i).carrier) :=
        ENNReal.div_le_div_right hmass _
    _ ≤ (∑ i ∈ s', volume (V i).shade) / (∑ i ∈ s', volume (V i).carrier) :=
        ENNReal.div_le_div le_rfl hD

end Fullness

/-! ## The numerology of the squeeze -/

section Numerology

/-- The `δ`-scale of the squeeze at parent scale `ρ`: `δ = 2σρ` with `σ = ρ³`. -/
theorem sqScale_rpow {ρ : ℝ≥0} (t : ℝ) :
    ((2 * ρ ^ 3 * ρ : ℝ≥0)) ^ t = (2 : ℝ≥0) ^ t * ρ ^ (4 * t) := by
  have h : (2 * ρ ^ 3 * ρ : ℝ≥0) = 2 * ρ ^ 4 := by ring
  rw [h, NNReal.mul_rpow]
  congr 1
  rw [← NNReal.rpow_natCast ρ 4, ← NNReal.rpow_mul]
  norm_num

theorem two_rpow_le_two {t : ℝ} (ht : t ≤ 1) : (2 : ℝ≥0) ^ t ≤ 2 := by
  calc (2 : ℝ≥0) ^ t ≤ (2 : ℝ≥0) ^ (1 : ℝ) :=
        NNReal.rpow_le_rpow_of_exponent_le one_le_two ht
    _ = 2 := NNReal.rpow_one 2

theorem half_le_two_rpow {t : ℝ} (ht : -1 ≤ t) : (2 : ℝ≥0)⁻¹ ≤ (2 : ℝ≥0) ^ t := by
  calc (2 : ℝ≥0)⁻¹ = (2 : ℝ≥0) ^ (-1 : ℝ) := by
        rw [NNReal.rpow_neg_one]
    _ ≤ (2 : ℝ≥0) ^ t := NNReal.rpow_le_rpow_of_exponent_le one_le_two ht

/-- **The Katz–Tao budget.** -/
theorem katzTao_budget {ρ : ℝ≥0} (hρ0 : 0 < ρ) {η₁ : ℝ} (_hη₁0 : 0 < η₁) (hη₁1 : η₁ ≤ 1)
    (hbud : 12 * fatLoss * ρ ^ (7 * η₁ / 2) ≤ 1) :
    fatLoss * ρ ^ (-(η₁ / 2)) ≤ ((2 * ρ ^ 3 * ρ : ℝ≥0)) ^ (-η₁) := by
  have hρne : ρ ≠ 0 := hρ0.ne'
  have hsplit : ρ ^ (-(η₁ / 2)) = ρ ^ (7 * η₁ / 2) * ρ ^ (4 * -η₁) := by
    rw [← NNReal.rpow_add hρne]
    congr 1
    ring
  have hhead : fatLoss * ρ ^ (7 * η₁ / 2) ≤ (2 : ℝ≥0) ^ (-η₁) := by
    have h12 : (12 : ℝ≥0) * (fatLoss * ρ ^ (7 * η₁ / 2)) ≤ 12 * (2 : ℝ≥0)⁻¹ := by
      calc (12 : ℝ≥0) * (fatLoss * ρ ^ (7 * η₁ / 2))
          = 12 * fatLoss * ρ ^ (7 * η₁ / 2) := by ring
        _ ≤ 1 := hbud
        _ ≤ 12 * (2 : ℝ≥0)⁻¹ := by norm_num
    have h12' : fatLoss * ρ ^ (7 * η₁ / 2) ≤ (2 : ℝ≥0)⁻¹ :=
      le_of_mul_le_mul_left h12 (by norm_num : (0 : ℝ≥0) < 12)
    exact le_trans h12' (half_le_two_rpow (by linarith))
  rw [sqScale_rpow, hsplit, ← mul_assoc]
  gcongr

/-- **The fullness budget.** -/
theorem fullness_budget {ρ : ℝ≥0} (hρ0 : 0 < ρ) {η₁ : ℝ} (_hη₁0 : 0 < η₁) (hη₁1 : η₁ ≤ 1)
    (hbud : 12 * fatLoss * ρ ^ (7 * η₁ / 2) ≤ 1) :
    ((2 * ρ ^ 3 * ρ : ℝ≥0)) ^ η₁ ≤ (fatLoss * 6)⁻¹ * ρ ^ (η₁ / 2) := by
  have hρne : ρ ≠ 0 := hρ0.ne'
  have hc : (fatLoss * 6 : ℝ≥0) ≠ 0 := by
    simp [fatLoss_ne_zero]
  have hsplit : ρ ^ (η₁ / 2) = ρ ^ (-(7 * η₁ / 2)) * ρ ^ (4 * η₁) := by
    rw [← NNReal.rpow_add hρne]
    congr 1
    ring
  have hkey : (fatLoss * 6) * ((2 * ρ ^ 3 * ρ : ℝ≥0)) ^ η₁ ≤ ρ ^ (η₁ / 2) := by
    rw [sqScale_rpow, hsplit]
    have h2 : (2 : ℝ≥0) ^ η₁ ≤ 2 := two_rpow_le_two hη₁1
    have hstep : (fatLoss * 6) * ((2 : ℝ≥0) ^ η₁ * ρ ^ (4 * η₁))
        ≤ (fatLoss * 6) * (2 * ρ ^ (4 * η₁)) := by gcongr
    refine le_trans hstep ?_
    have hpow : ρ ^ (7 * η₁ / 2) * ρ ^ (-(7 * η₁ / 2)) = 1 := by
      rw [← NNReal.rpow_add hρne]
      simp
    have hmain : (fatLoss * 6) * 2 * ρ ^ (7 * η₁ / 2) ≤ 1 := by
      calc (fatLoss * 6) * 2 * ρ ^ (7 * η₁ / 2) = 12 * fatLoss * ρ ^ (7 * η₁ / 2) := by ring
        _ ≤ 1 := hbud
    calc (fatLoss * 6) * (2 * ρ ^ (4 * η₁))
        = ((fatLoss * 6) * 2 * ρ ^ (7 * η₁ / 2))
            * (ρ ^ (-(7 * η₁ / 2)) * ρ ^ (4 * η₁)) := by
          rw [show (fatLoss * 6) * 2 * ρ ^ (7 * η₁ / 2)
              * (ρ ^ (-(7 * η₁ / 2)) * ρ ^ (4 * η₁))
            = (fatLoss * 6) * 2 * (ρ ^ (7 * η₁ / 2) * ρ ^ (-(7 * η₁ / 2))) * ρ ^ (4 * η₁) from
              by ring, hpow]
          ring
      _ ≤ 1 * (ρ ^ (-(7 * η₁ / 2)) * ρ ^ (4 * η₁)) := by gcongr
      _ = ρ ^ (-(7 * η₁ / 2)) * ρ ^ (4 * η₁) := one_mul _
  calc ((2 * ρ ^ 3 * ρ : ℝ≥0)) ^ η₁
      = (fatLoss * 6)⁻¹ * ((fatLoss * 6) * ((2 * ρ ^ 3 * ρ : ℝ≥0)) ^ η₁) := by
        rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    _ ≤ (fatLoss * 6)⁻¹ * ρ ^ (η₁ / 2) := by gcongr

/-- **The accuracy budget.** -/
theorem accuracy_budget {ρ : ℝ≥0} (hρ0 : 0 < ρ) {ε : ℝ} (hε : 0 < ε)
    (hbud : 6 * ρ ^ (ε / 2) ≤ 1) :
    (6 : ℝ≥0) * ((2 * ρ ^ 3 * ρ : ℝ≥0)) ^ (-(ε / 8)) ≤ ρ ^ (-ε) := by
  have hρne : ρ ≠ 0 := hρ0.ne'
  have hsplit : ρ ^ (-ε) = ρ ^ (ε / 2) * ρ ^ (4 * -(ε / 8)) * ρ ^ (-ε) := by
    rw [← NNReal.rpow_add hρne, ← NNReal.rpow_add hρne]
    congr 1
    ring
  rw [sqScale_rpow]
  have h2 : (2 : ℝ≥0) ^ (-(ε / 8)) ≤ 1 := by
    calc (2 : ℝ≥0) ^ (-(ε / 8)) ≤ (2 : ℝ≥0) ^ (0 : ℝ) :=
          NNReal.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
      _ = 1 := NNReal.rpow_zero 2
  calc (6 : ℝ≥0) * ((2 : ℝ≥0) ^ (-(ε / 8)) * ρ ^ (4 * -(ε / 8)))
      ≤ 6 * (1 * ρ ^ (4 * -(ε / 8))) := by gcongr
    _ = 6 * ρ ^ (ε / 2) * (ρ ^ (-(ε / 2)) * ρ ^ (4 * -(ε / 8))) := by
        rw [show (6 : ℝ≥0) * ρ ^ (ε / 2) * (ρ ^ (-(ε / 2)) * ρ ^ (4 * -(ε / 8)))
            = 6 * (ρ ^ (ε / 2) * ρ ^ (-(ε / 2))) * ρ ^ (4 * -(ε / 8)) from by ring,
          ← NNReal.rpow_add hρne]
        simp
    _ ≤ 1 * (ρ ^ (-(ε / 2)) * ρ ^ (4 * -(ε / 8))) := by gcongr
    _ = ρ ^ (-ε) := by
        rw [one_mul, ← NNReal.rpow_add hρne]
        congr 1
        ring

end Numerology

/-! ## The main theorem -/

section Main

universe u

set_option maxHeartbeats 1000000 in
/-- **`SmallCard γ` implies the full Katz–Tao estimate at `γ`.**

The band `|𝕋| < δ^{-1}` of `Kakeya.ML2Assembly.SmallCard` is *affinely vacuous*: squeezing a
family of `ρ`-tubes transversally by `σ = ρ³` presents it as a family of `δ`-tubes with
`δ = 2ρ⁴`, whose cardinality `≲ ρ^{-3}` is far below `δ^{-1} ≍ ρ^{-4}`. -/
theorem katzTaoEstimate_of_smallCard {γ : ℝ} (hγ : 0 ≤ γ)
    (hsc : Kakeya.ML2Assembly.SmallCard.{u} γ) :
    Kakeya.KatzTaoEstimate.{u} Space3 γ := by
  classical
  have hn : Module.finrank ℝ Space3 = 3 := finrank_euclideanSpace_fin
  intro ε hε
  obtain ⟨η₁, hη₁0, hη₁1, hsm⟩ := hsc (ε / 8) (by linarith)
  refine ⟨η₁ / 2, by positivity, ?_⟩
  have hmap : Filter.Tendsto (fun ρ : ℝ≥0 => 2 * ρ ^ 3 * ρ) (𝓝[>] 0) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hcont : Continuous (fun ρ : ℝ≥0 => 2 * ρ ^ 3 * ρ) := by fun_prop
      refine Filter.Tendsto.mono_left ?_ nhdsWithin_le_nhds
      simpa using hcont.tendsto 0
    · filter_upwards [self_mem_nhdsWithin] with ρ hρ
      have hρ0 : (0 : ℝ≥0) < ρ := hρ
      exact Set.mem_Ioi.mpr (by positivity)
  filter_upwards [hmap.eventually hsm,
    Kakeya.VeryNotSticky.eventually_nnreal_mul_rpow_le_const
      (4 * Tube.card_le_of_densityIn_le.C 3) 1 one_pos (p := 1) one_pos,
    Kakeya.VeryNotSticky.eventually_nnreal_mul_rpow_le_const (12 * fatLoss) 1 one_pos
      (p := 7 * η₁ / 2) (by positivity),
    Kakeya.VeryNotSticky.eventually_nnreal_mul_rpow_le_const 6 1 one_pos
      (p := ε / 2) (by positivity),
    Ioo_mem_nhdsGT (show (0 : ℝ≥0) < 1 / 2 by norm_num),
    self_mem_nhdsWithin] with ρ hδsm hcardbud hktbud haccbud hρhalf hρpos
  intro ι s T hball hKT hfull
  have hρ0 : (0 : ℝ≥0) < ρ := hρpos
  have hρne : (ρ : ℝ≥0) ≠ 0 := hρ0.ne'
  have hρ12 : ρ ≤ 1 / 2 := hρhalf.2.le
  have hρ1 : ρ ≤ 1 := le_trans hρ12 (by norm_num)
  have hσ0 : (0 : ℝ≥0) < ρ ^ 3 := by positivity
  have hσ1 : (ρ : ℝ≥0) ^ 3 ≤ 1 := pow_le_one₀ (by positivity) hρ1
  have hδpos : (0 : ℝ≥0) < 2 * ρ ^ 3 * ρ := by positivity
  have hδne : (2 * ρ ^ 3 * ρ : ℝ≥0) ≠ 0 := hδpos.ne'
  have hδ8 : (2 * ρ ^ 3 * ρ : ℝ≥0) ≤ 1 / 8 := by
    have hstep : (2 * ρ ^ 3 * ρ : ℝ≥0) ≤ 2 * (1 / 2 : ℝ≥0) ^ 3 * (1 / 2 : ℝ≥0) := by
      gcongr
    calc (2 * ρ ^ 3 * ρ : ℝ≥0) ≤ 2 * (1 / 2 : ℝ≥0) ^ 3 * (1 / 2 : ℝ≥0) := hstep
      _ = 1 / 8 := by norm_num
  have hδ1 : (2 * ρ ^ 3 * ρ : ℝ≥0) ≤ 1 := by
    refine le_trans hδ8 ?_
    rw [← NNReal.coe_le_coe]
    norm_num
  have hδ4 : ((2 * ρ ^ 3 * ρ : ℝ≥0) : ℝ) ≤ 1 / 4 := by
    have h : ((2 * ρ ^ 3 * ρ : ℝ≥0) : ℝ) ≤ ((1 / 8 : ℝ≥0) : ℝ) := by exact_mod_cast hδ8
    simpa using le_trans h (by norm_num)
  -- the heavy cap
  obtain ⟨k, hk⟩ := exists_heavy_cap s T
  set s' : Finset ι := s.filter (fun i => capIndex (T i).direction = k) with hs'def
  have hs'sub : s' ⊆ s := Finset.filter_subset _ _
  have he : ‖capVec k‖ = 1 := norm_capVec k
  have hcap : ∀ i ∈ s', (1 : ℝ) / 2 ≤ (inner ℝ (capVec k) (T i).direction : ℝ) := by
    intro i hi
    have hmem := Finset.mem_filter.mp (hs'def ▸ hi)
    have hspec := capIndex_spec (T i).toTube.norm_direction
    rwa [hmem.2] at hspec
  have hball' : ∀ i ∈ s', (T i).carrier ⊆ Metric.closedBall (0 : Space3) 1 :=
    fun i hi => hball i (hs'sub hi)
  -- the squeezed family
  set U : ι → ShadedTube (2 * ρ ^ 3 * ρ) Space3 :=
    sqFamily hσ0 he (2 * ρ ^ 3 * ρ) T with hUdef
  -- (H1) the squeezed carriers lie in the unit ball
  have hH1 : ∀ i ∈ s', (U i).carrier ⊆ Metric.closedBall (0 : Space3) 1 :=
    sqFamily_carrier_subset_closedBall hσ0 hσ1 he hball' hδ4
  -- (H2) the Katz--Tao hypothesis at the new scale
  have hmaxs' : Kakeya.maxDensity s' (fun i => (T i).toConvexSpaceBody)
      ≤ (ρ : ℝ≥0∞) ^ (-(η₁ / 2)) := le_trans (Kakeya.maxDensity_mono _ hs'sub) hKT
  have hH2 : ConvexSpaceBody.IsKatzTao s' (fun i => (U i).toConvexSpaceBody)
      (((2 * ρ ^ 3 * ρ : ℝ≥0) : ℝ≥0∞) ^ (-η₁)) := by
    refine le_trans (sqFamily_maxDensity_le hn hσ0 hσ1 hρ1 he hcap hδ1) ?_
    refine le_trans (by gcongr : (fatLoss : ℝ≥0∞)
        * Kakeya.maxDensity s' (fun i => (T i).toConvexSpaceBody)
      ≤ (fatLoss : ℝ≥0∞) * (ρ : ℝ≥0∞) ^ (-(η₁ / 2))) ?_
    have hb := ENNReal.coe_le_coe.mpr (katzTao_budget hρ0 hη₁0 hη₁1 hktbud)
    rwa [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hρne,
      ENNReal.coe_rpow_of_ne_zero hδne] at hb
  -- (H3) the fullness hypothesis at the new scale
  have hmass : (((6 : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞)
        * ∑ i ∈ s, volume (T i).toShadedBody.shade
      ≤ ∑ i ∈ s', volume (T i).toShadedBody.shade := by
    rw [ENNReal.coe_inv (by norm_num : (6 : ℝ≥0) ≠ 0),
      ENNReal.inv_mul_le_iff (by simp) (by simp)]
    simpa using hk
  have hfulls' : (6 : ℝ≥0)⁻¹ * ρ ^ (η₁ / 2)
      ≤ ShadedBody.fullness s' (fun i => (T i).toShadedBody) := by
    refine le_trans ?_ (mul_fullness_le_of_subset hs'sub (fun i => (T i).toShadedBody) hmass)
    gcongr
  have hH3 : ShadedBody.fullness s' (fun i => (U i).toShadedBody)
      ≥ (2 * ρ ^ 3 * ρ : ℝ≥0) ^ η₁ := by
    refine le_trans ?_ (sqFamily_le_fullness hn hσ0 hσ1 hρ1 he hcap hδ1)
    refine le_trans (fullness_budget hρ0 hη₁0 hη₁1 hktbud) ?_
    rw [mul_inv, mul_assoc]
    gcongr
  -- (H4) the cardinality hypothesis
  have hH4 : ((s'.card : ℝ)) < ((2 * ρ ^ 3 * ρ : ℝ≥0) : ℝ)⁻¹ := by
    have hdens : Kakeya.densityIn s' (fun i => ((T i).toTube).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall ≤ ((ρ : ℝ≥0∞))⁻¹ := by
      refine le_trans (Kakeya.le_maxDensity _ _ _) (le_trans hmaxs' ?_)
      have hρE : (ρ : ℝ≥0∞) ≤ 1 := by exact_mod_cast hρ1
      rw [show ((ρ : ℝ≥0∞))⁻¹ = (ρ : ℝ≥0∞) ^ (-1 : ℝ) by
        rw [ENNReal.rpow_neg_one]]
      exact ENNReal.rpow_le_rpow_of_exponent_ge hρE (by linarith)
    have hcard := Tube.card_le_of_densityIn_le (E := Space3) (s := s') hρne
      (T := fun i => (T i).toTube) hball' hdens
    rw [hn] at hcard
    have hzpN : (ρ : ℝ≥0) ^ (-((3 : ℕ) - 1 : ℤ)) = (ρ ^ 2)⁻¹ := by
      rw [show (-((3 : ℕ) - 1 : ℤ)) = (-2 : ℤ) by norm_num, zpow_neg]
      norm_num
      rfl
    have hzp : ((ρ : ℝ≥0∞)) ^ (-((3 : ℕ) - 1 : ℤ))
        = (((ρ ^ 2 : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
      rw [← ENNReal.coe_zpow hρne, hzpN]
    rw [hzp, show ((ρ : ℝ≥0∞))⁻¹ = (((ρ⁻¹ : ℝ≥0)) : ℝ≥0∞) from
      (ENNReal.coe_inv hρne).symm, ← ENNReal.coe_mul, ← ENNReal.coe_mul,
      ← ENNReal.coe_natCast] at hcard
    have hcardN : (s'.card : ℝ≥0)
        ≤ Tube.card_le_of_densityIn_le.C 3 * ρ⁻¹ * (ρ ^ 2)⁻¹ := ENNReal.coe_le_coe.mp hcard
    have hprod : (s'.card : ℝ≥0) * (2 * ρ ^ 3 * ρ) ≤ 1 / 2 := by
      calc (s'.card : ℝ≥0) * (2 * ρ ^ 3 * ρ)
          ≤ (Tube.card_le_of_densityIn_le.C 3 * ρ⁻¹ * (ρ ^ 2)⁻¹) * (2 * ρ ^ 3 * ρ) := by gcongr
        _ = 2 * (Tube.card_le_of_densityIn_le.C 3 * ρ) := by field_simp
        _ ≤ 1 / 2 := by
            have h4 : 4 * Tube.card_le_of_densityIn_le.C 3 * ρ ≤ 1 := by
              simpa using hcardbud
            calc 2 * (Tube.card_le_of_densityIn_le.C 3 * ρ)
                = (4 * Tube.card_le_of_densityIn_le.C 3 * ρ) * (1 / 2 : ℝ≥0) := by ring
              _ ≤ 1 * (1 / 2 : ℝ≥0) := by gcongr
              _ = 1 / 2 := one_mul _
    have hprodR : ((s'.card : ℝ)) * ((2 * ρ ^ 3 * ρ : ℝ≥0) : ℝ) ≤ 1 / 2 := by
      have h := NNReal.coe_le_coe.mpr hprod
      push_cast at h
      simpa using h
    have hδR : (0 : ℝ) < ((2 * ρ ^ 3 * ρ : ℝ≥0) : ℝ) := by
      exact_mod_cast hδpos
    have hlt : ((s'.card : ℝ)) * ((2 * ρ ^ 3 * ρ : ℝ≥0) : ℝ) < 1 := by linarith
    calc ((s'.card : ℝ))
        = (((s'.card : ℝ)) * ((2 * ρ ^ 3 * ρ : ℝ≥0) : ℝ))
            * ((2 * ρ ^ 3 * ρ : ℝ≥0) : ℝ)⁻¹ := by field_simp
      _ < 1 * ((2 * ρ ^ 3 * ρ : ℝ≥0) : ℝ)⁻¹ :=
          mul_lt_mul_of_pos_right hlt (inv_pos.mpr hδR)
      _ = ((2 * ρ ^ 3 * ρ : ℝ≥0) : ℝ)⁻¹ := one_mul _
  -- apply `SmallCard` at the squeezed scale
  have hconc := hδsm s' U hH1 hH2 hH3 hH4
  rw [sqFamily_sum_shade hσ0 hσ1 hρ1 he hcap le_rfl,
    sqFamily_iUnion_shade hσ0 hσ1 hρ1 he hcap le_rfl] at hconc
  have hJ0 : Kakeya.affineJacobian (sqA hσ0 he) ≠ 0 := Kakeya.affineJacobian_ne_zero _
  have hJt : Kakeya.affineJacobian (sqA hσ0 he) ≠ ⊤ := Kakeya.affineJacobian_ne_top _
  have hconc' : ∑ i ∈ s', volume (T i).shade
      ≤ ((2 * ρ ^ 3 * ρ : ℝ≥0) : ℝ≥0∞) ^ (-(ε / 8)) * (s'.card : ℝ≥0∞) ^ γ
        * volume (⋃ i ∈ s', (T i).shade) := by
    rw [show ((2 * ρ ^ 3 * ρ : ℝ≥0) : ℝ≥0∞) ^ (-(ε / 8)) * (s'.card : ℝ≥0∞) ^ γ
          * (Kakeya.affineJacobian (sqA hσ0 he) * volume (⋃ i ∈ s', (T i).shade))
        = Kakeya.affineJacobian (sqA hσ0 he)
          * (((2 * ρ ^ 3 * ρ : ℝ≥0) : ℝ≥0∞) ^ (-(ε / 8)) * (s'.card : ℝ≥0∞) ^ γ
            * volume (⋃ i ∈ s', (T i).shade)) from by ring] at hconc
    exact (ENNReal.mul_le_mul_iff_right hJ0 hJt).mp hconc
  -- assemble
  have hcardle : (s'.card : ℝ≥0∞) ^ γ ≤ (s.card : ℝ≥0∞) ^ γ := by
    have hle : ((s'.card : ℝ≥0∞)) ≤ (s.card : ℝ≥0∞) := by
      exact_mod_cast Finset.card_le_card hs'sub
    exact ENNReal.rpow_le_rpow hle hγ
  have hunionle : volume (⋃ i ∈ s', (T i).shade) ≤ volume (⋃ i ∈ s, (T i).shade) :=
    measure_mono (Set.biUnion_subset_biUnion_left hs'sub)
  have hacc : (6 : ℝ≥0∞) * ((2 * ρ ^ 3 * ρ : ℝ≥0) : ℝ≥0∞) ^ (-(ε / 8))
      ≤ (ρ : ℝ≥0∞) ^ (-ε) := by
    have hb := ENNReal.coe_le_coe.mpr (accuracy_budget hρ0 hε haccbud)
    rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hδne,
      ENNReal.coe_rpow_of_ne_zero hρne] at hb
    simpa using hb
  calc ∑ i ∈ s, volume (T i).shade
      ≤ 6 * ∑ i ∈ s', volume (T i).shade := hk
    _ ≤ 6 * (((2 * ρ ^ 3 * ρ : ℝ≥0) : ℝ≥0∞) ^ (-(ε / 8)) * (s'.card : ℝ≥0∞) ^ γ
        * volume (⋃ i ∈ s', (T i).shade)) := by gcongr
    _ ≤ 6 * (((2 * ρ ^ 3 * ρ : ℝ≥0) : ℝ≥0∞) ^ (-(ε / 8)) * (s.card : ℝ≥0∞) ^ γ
        * volume (⋃ i ∈ s, (T i).shade)) := by gcongr
    _ = (6 * ((2 * ρ ^ 3 * ρ : ℝ≥0) : ℝ≥0∞) ^ (-(ε / 8))) * (s.card : ℝ≥0∞) ^ γ
        * volume (⋃ i ∈ s, (T i).shade) := by ring
    _ ≤ (ρ : ℝ≥0∞) ^ (-ε) * (s.card : ℝ≥0∞) ^ γ
        * volume (⋃ i ∈ s, (T i).shade) := by gcongr

/-! ## The equivalence, the tripwires, and the consequence for the assembly -/


/-! ### Tripwires

If `Kakeya.ML2Assembly.SmallCard` or `Kakeya.KatzTaoEstimate` drifts — a binder moved, a
hypothesis added or dropped — the `example`s below stop compiling. -/

example {γ : ℝ} (hγ : 0 ≤ γ) (h : Kakeya.ML2Assembly.SmallCard.{u} γ) :
    Kakeya.KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) γ :=
  katzTaoEstimate_of_smallCard hγ h

example {β c : ℝ} (hc : 0 < c) (hcβ : 2 * c ≤ β)
    (hsmall : Kakeya.ML2Assembly.SmallCard.{u} (β - c)) :
    Kakeya.KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) (β - c) :=
  katzTaoEstimate_of_smallCard (by linarith) hsmall


/-! ### The aperture of the cap does not depend on `σ`

The geometric core `Kakeya.ML2Squeeze.sqL_image_subset_sqTube` is stated under
`1/2 ≤ ⟪e, S.direction⟫` — an aperture of `60°`, with **no `σ` in it**.  The reason is that the
squeeze *itself* contracts directions towards `e`: the image core direction `u` satisfies
`‖u - e‖ ≤ 4σ` (inside the proof), so the transverse spread of `A(S)` is `O(σρ)` even though the
image of a cross-sectional vector can have length `≍ ρ`, that length being spent
*longitudinally*.  Six caps therefore suffice, not `σ^{-2}` of them. -/

/-! ### The squeeze is asymmetric: the reverse squeeze is not free

Presenting a `ρ`-tube as a `δ`-tube with `δ ≥ ρ` costs a factor `≳ (δ/ρ)²` in volume — hence in
`Δ_max` and in fullness — and *that* is not an absolute constant.  So the mechanism that empties
`Kakeya.ML2Assembly.SmallCard`'s band does **not** touch `Kakeya.ML2Assembly.Dichotomy`'s
`δ⁻¹ ≤ |𝕋|`. -/


/-! ### The aperture claim, refuted

The informal objection to the squeeze is that `A = ¼·diag(σ,σ,1)` maps a `ρ`-tube to a `2σρ`-tube
only for directions within angle `≈ σ` of the axis, so that covering `S²` would need `≈ σ^{-2}`
caps and the partition would cost a *power* of the scale.  That is false, and the reason is
`Kakeya.ML2Squeeze.norm_perp_sqL_le`: the image of a cross-sectional vector `w` can indeed have
length `≍ ρ`, but that length is spent **longitudinally** — its component perpendicular to the
image core direction `u` is `O(σρ)` — because the squeeze contracts *directions* towards `e`
(`‖u - e‖ ≤ 4σ`) uniformly over a cap of aperture `60°`.

`Kakeya.ML2Squeeze.narrowApertureClaim_false` refutes the objection with a witness at
`3/5`-`4/5`, i.e. at angle `≈ 53°` from the cap centre, at every `σ ≤ 1/5`. -/


/-! ### The producer question

"Is the hypothesis weaker than the goal as a `Prop`?" is the wrong test for circularity; the right
one is **what must be built to discharge it**.  Here the answer is stark, and it is quantified over
*every* candidate producer: anything at all that discharges the small-cardinality slot at `γ ≥ 0`
has thereby discharged Main Lemma 2's conclusion at `γ`.  There is no route to `hsmall` that lands
anywhere easier than the goal, because `hsmall` *is* the goal. -/


/-- **Round trip at `γ = 1`**, where the conclusion is independently known
(`Kakeya.KatzTao_one`): the squeeze reproduces it from the band form.  A smoke test that the
pipeline is not vacuous at the type level. -/
example : Kakeya.KatzTaoEstimate.{u} Space3 1 :=
  katzTaoEstimate_of_smallCard zero_le_one
    (Kakeya.ML2Band.smallCard_of_katzTaoEstimate (Kakeya.KatzTao_one (n := 3)))

end Main

/-! ## Part II — any `β`-only cardinality cut is circular

`Kakeya.ML2Squeeze.katzTaoEstimate_of_smallCard` empties the band `|𝕋| < δ^{-1}`.  The obvious
next thought is that a *smaller* threshold might survive: the assembly's `δ^{-1}` came from
reading Theorem 7.3(B) at the absolute accuracy `ε₀ = β/2`, and a smaller `ε₀` would buy a
smaller threshold (`Kakeya.ML2Band.absoluteLossRoute_insufficient` prices it at
`θ ≈ (ε₀-ε)/(β-ν)`).  It does not survive.  For **every** `θ > 0` the complementary case
`|𝕋| < δ^{-θ}` is again the full estimate: take the squeeze at `σ = ρ^m` with `m` large enough
that `(m+1)θ ≥ 4`, and the image cardinality `≲ ρ^{-3}` still falls below
`δ^{-θ} = (2ρ^{m+1})^{-θ} ≳ ρ^{-4}`.  The extra depth costs only a factor `m+1` in the accuracy,
and the accuracy may be chosen after `ε`. -/

section Cut

universe v

/-- `Kakeya.ML2Assembly.SmallCard` with the threshold `δ^{-1}` replaced by `δ^{-θ}`. -/
def SmallCardCut (θ γ : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), η ≤ 1 ∧
    ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0,
      ∀ {ι : Type v} (s : Finset ι) (T : ι → ShadedTube δ Space3),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        ConvexSpaceBody.IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ℝ≥0∞) ^ (-η)) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (s.card : ℝ) < (δ : ℝ) ^ (-θ) →
        ∑ i ∈ s, volume (T i).shade
          ≤ (δ : ℝ≥0∞) ^ (-ε) * (s.card : ℝ≥0∞) ^ γ * volume (⋃ i ∈ s, (T i).shade)

/-- A smaller cut is a weaker hypothesis, so `SmallCardCut` is antitone in `θ`. -/
theorem smallCardCut_mono {θ θ' γ : ℝ} (hθ : θ' ≤ θ) (h : SmallCardCut.{v} θ γ) :
    SmallCardCut.{v} θ' γ := by
  intro ε hε
  obtain ⟨η, hη0, hη1, hev⟩ := h ε hε
  refine ⟨η, hη0, hη1, ?_⟩
  filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : ℝ≥0) < 1 from zero_lt_one)] with δ hδev hδ
  obtain ⟨hδ0, hδ1⟩ := hδ
  intro ι s T hball hKT hfull hcard
  refine hδev s T hball hKT hfull (lt_of_lt_of_le hcard ?_)
  have hδ0' : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hδ1' : ((δ : ℝ)) ≤ 1 := by exact_mod_cast hδ1.le
  exact Real.rpow_le_rpow_of_exponent_ge hδ0' hδ1' (by linarith)


/-! ### The numerology at depth `m` -/

theorem sqScaleN_rpow (m : ℕ) {ρ : ℝ≥0} (t : ℝ) :
    ((2 * ρ ^ m * ρ : ℝ≥0)) ^ t = (2 : ℝ≥0) ^ t * ρ ^ (((m : ℝ) + 1) * t) := by
  have h : (2 * ρ ^ m * ρ : ℝ≥0) = 2 * ρ ^ (m + 1) := by rw [pow_succ]; ring
  rw [h, NNReal.mul_rpow]
  congr 1
  rw [← NNReal.rpow_natCast ρ (m + 1), ← NNReal.rpow_mul]
  congr 1
  push_cast
  ring

/-- **The Katz--Tao budget at depth `m`.** -/
theorem katzTao_budgetN {ρ : ℝ≥0} (hρ0 : 0 < ρ) (m : ℕ) {η₁ : ℝ} (hη₁1 : η₁ ≤ 1)
    (hbud : 12 * fatLoss * ρ ^ (((m : ℝ) + 1) * η₁ - η₁ / 2) ≤ 1) :
    fatLoss * ρ ^ (-(η₁ / 2)) ≤ ((2 * ρ ^ m * ρ : ℝ≥0)) ^ (-η₁) := by
  have hρne : ρ ≠ 0 := hρ0.ne'
  set M : ℝ := (m : ℝ) + 1 with hM
  have hsplit : ρ ^ (-(η₁ / 2)) = ρ ^ (M * η₁ - η₁ / 2) * ρ ^ (M * -η₁) := by
    rw [← NNReal.rpow_add hρne]
    congr 1
    ring
  have hhead : fatLoss * ρ ^ (M * η₁ - η₁ / 2) ≤ (2 : ℝ≥0) ^ (-η₁) := by
    have h12 : (12 : ℝ≥0) * (fatLoss * ρ ^ (M * η₁ - η₁ / 2)) ≤ 12 * (2 : ℝ≥0)⁻¹ := by
      calc (12 : ℝ≥0) * (fatLoss * ρ ^ (M * η₁ - η₁ / 2))
          = 12 * fatLoss * ρ ^ (M * η₁ - η₁ / 2) := by ring
        _ ≤ 1 := hbud
        _ ≤ 12 * (2 : ℝ≥0)⁻¹ := by norm_num
    exact le_trans (le_of_mul_le_mul_left h12 (by norm_num : (0 : ℝ≥0) < 12))
      (half_le_two_rpow (by linarith))
  rw [sqScaleN_rpow, hsplit, ← mul_assoc]
  gcongr

/-- **The fullness budget at depth `m`.** -/
theorem fullness_budgetN {ρ : ℝ≥0} (hρ0 : 0 < ρ) (m : ℕ) {η₁ : ℝ} (hη₁1 : η₁ ≤ 1)
    (hbud : 12 * fatLoss * ρ ^ (((m : ℝ) + 1) * η₁ - η₁ / 2) ≤ 1) :
    ((2 * ρ ^ m * ρ : ℝ≥0)) ^ η₁ ≤ (fatLoss * 6)⁻¹ * ρ ^ (η₁ / 2) := by
  have hρne : ρ ≠ 0 := hρ0.ne'
  have hc : (fatLoss * 6 : ℝ≥0) ≠ 0 := by simp [fatLoss_ne_zero]
  set M : ℝ := (m : ℝ) + 1 with hM
  have hsplit : ρ ^ (η₁ / 2) = ρ ^ (-(M * η₁ - η₁ / 2)) * ρ ^ (M * η₁) := by
    rw [← NNReal.rpow_add hρne]
    congr 1
    ring
  have hkey : (fatLoss * 6) * ((2 * ρ ^ m * ρ : ℝ≥0)) ^ η₁ ≤ ρ ^ (η₁ / 2) := by
    rw [sqScaleN_rpow, hsplit]
    have h2 : (2 : ℝ≥0) ^ η₁ ≤ 2 := two_rpow_le_two hη₁1
    have hstep : (fatLoss * 6) * ((2 : ℝ≥0) ^ η₁ * ρ ^ (M * η₁))
        ≤ (fatLoss * 6) * (2 * ρ ^ (M * η₁)) := by gcongr
    refine le_trans hstep ?_
    have hpow : ρ ^ (M * η₁ - η₁ / 2) * ρ ^ (-(M * η₁ - η₁ / 2)) = 1 := by
      rw [← NNReal.rpow_add hρne]; simp
    have hmain : (fatLoss * 6) * 2 * ρ ^ (M * η₁ - η₁ / 2) ≤ 1 := by
      calc (fatLoss * 6) * 2 * ρ ^ (M * η₁ - η₁ / 2)
          = 12 * fatLoss * ρ ^ (M * η₁ - η₁ / 2) := by ring
        _ ≤ 1 := hbud
    calc (fatLoss * 6) * (2 * ρ ^ (M * η₁))
        = ((fatLoss * 6) * 2 * ρ ^ (M * η₁ - η₁ / 2))
            * (ρ ^ (-(M * η₁ - η₁ / 2)) * ρ ^ (M * η₁)) := by
          rw [show (fatLoss * 6) * 2 * ρ ^ (M * η₁ - η₁ / 2)
              * (ρ ^ (-(M * η₁ - η₁ / 2)) * ρ ^ (M * η₁))
            = (fatLoss * 6) * 2 * (ρ ^ (M * η₁ - η₁ / 2) * ρ ^ (-(M * η₁ - η₁ / 2)))
              * ρ ^ (M * η₁) from by ring, hpow]
          ring
      _ ≤ 1 * (ρ ^ (-(M * η₁ - η₁ / 2)) * ρ ^ (M * η₁)) := by gcongr
      _ = ρ ^ (-(M * η₁ - η₁ / 2)) * ρ ^ (M * η₁) := one_mul _
  calc ((2 * ρ ^ m * ρ : ℝ≥0)) ^ η₁
      = (fatLoss * 6)⁻¹ * ((fatLoss * 6) * ((2 * ρ ^ m * ρ : ℝ≥0)) ^ η₁) := by
        rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    _ ≤ (fatLoss * 6)⁻¹ * ρ ^ (η₁ / 2) := by gcongr

/-- **The accuracy budget at depth `m`.**  The accuracy handed to `SmallCardCut` is
`ε / (2(m+1))`, which is legal because it is chosen *after* `ε`. -/
theorem accuracy_budgetN {ρ : ℝ≥0} (hρ0 : 0 < ρ) (m : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hbud : 6 * ρ ^ (ε / 2) ≤ 1) :
    (6 : ℝ≥0) * ((2 * ρ ^ m * ρ : ℝ≥0)) ^ (-(ε / (2 * ((m : ℝ) + 1)))) ≤ ρ ^ (-ε) := by
  have hρne : ρ ≠ 0 := hρ0.ne'
  set M : ℝ := (m : ℝ) + 1 with hM
  have hM1 : (1 : ℝ) ≤ M := by
    rw [hM]
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hMne : M ≠ 0 := by linarith
  have hexp : M * -(ε / (2 * M)) = -(ε / 2) := by field_simp
  rw [sqScaleN_rpow, hexp]
  have h2 : (2 : ℝ≥0) ^ (-(ε / (2 * M))) ≤ 1 := by
    calc (2 : ℝ≥0) ^ (-(ε / (2 * M))) ≤ (2 : ℝ≥0) ^ (0 : ℝ) :=
          NNReal.rpow_le_rpow_of_exponent_le one_le_two
            (by have : (0:ℝ) < ε / (2 * M) := by positivity
                linarith)
      _ = 1 := NNReal.rpow_zero 2
  calc (6 : ℝ≥0) * ((2 : ℝ≥0) ^ (-(ε / (2 * M))) * ρ ^ (-(ε / 2)))
      ≤ 6 * (1 * ρ ^ (-(ε / 2))) := by gcongr
    _ = 6 * ρ ^ (ε / 2) * (ρ ^ (-(ε / 2)) * ρ ^ (-(ε / 2))) := by
        rw [show (6 : ℝ≥0) * ρ ^ (ε / 2) * (ρ ^ (-(ε / 2)) * ρ ^ (-(ε / 2)))
            = 6 * (ρ ^ (ε / 2) * ρ ^ (-(ε / 2))) * ρ ^ (-(ε / 2)) from by ring,
          ← NNReal.rpow_add hρne]
        simp
    _ ≤ 1 * (ρ ^ (-(ε / 2)) * ρ ^ (-(ε / 2))) := by gcongr
    _ = ρ ^ (-ε) := by
        rw [one_mul, ← NNReal.rpow_add hρne]
        congr 1
        ring

/-! ### The main theorem of Part II -/

set_option maxHeartbeats 2000000 in
/-- **The squeeze at depth `m`.**  If the cut `θ` satisfies `4 ≤ (m+1)θ` and `θ ≤ 1`, and
`4 ≤ m`, then `SmallCardCut θ γ` already gives the full estimate. -/
theorem katzTaoEstimate_of_smallCardCut_aux {γ θ : ℝ} (hγ : 0 ≤ γ) (_hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (m : ℕ) (hm4 : 4 ≤ m) (hmθ : 4 ≤ ((m : ℝ) + 1) * θ)
    (hsc : SmallCardCut.{v} θ γ) :
    Kakeya.KatzTaoEstimate.{v} Space3 γ := by
  classical
  have hn : Module.finrank ℝ Space3 = 3 := finrank_euclideanSpace_fin
  set C₀ : ℝ≥0 := Tube.card_le_of_densityIn_le.C 3 with hC₀def
  clear_value C₀
  have hC₀0 : (0 : ℝ) ≤ (C₀ : ℝ) := NNReal.coe_nonneg _
  have hmR : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm4
  set M : ℝ := (m : ℝ) + 1 with hMdef
  have hM1 : (1 : ℝ) ≤ M := by rw [hMdef]; linarith
  intro ε hε
  obtain ⟨η₁, hη₁0, hη₁1, hsm⟩ := hsc (ε / (2 * M)) (by positivity)
  refine ⟨η₁ / 2, by positivity, ?_⟩
  have hmap : Filter.Tendsto (fun ρ : ℝ≥0 => 2 * ρ ^ m * ρ) (𝓝[>] 0) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hcont : Continuous (fun ρ : ℝ≥0 => 2 * ρ ^ m * ρ) := by fun_prop
      refine Filter.Tendsto.mono_left ?_ nhdsWithin_le_nhds
      simpa [zero_pow (by omega : m ≠ 0)] using hcont.tendsto 0
    · filter_upwards [self_mem_nhdsWithin] with ρ hρ
      have hρ0 : (0 : ℝ≥0) < ρ := hρ
      exact Set.mem_Ioi.mpr (by positivity)
  filter_upwards [hmap.eventually hsm,
    Kakeya.VeryNotSticky.eventually_nnreal_mul_rpow_le_const
      (4 * C₀) 1 one_pos (p := 1) one_pos,
    Kakeya.VeryNotSticky.eventually_nnreal_mul_rpow_le_const (12 * fatLoss) 1 one_pos
      (p := M * η₁ - η₁ / 2) (by nlinarith),
    Kakeya.VeryNotSticky.eventually_nnreal_mul_rpow_le_const 6 1 one_pos
      (p := ε / 2) (by positivity),
    Ioo_mem_nhdsGT (show (0 : ℝ≥0) < 1 / 2 by norm_num),
    self_mem_nhdsWithin] with ρ hδsm hcardbud hktbud haccbud hρhalf hρpos
  intro ι s T hball hKT hfull
  have hρ0 : (0 : ℝ≥0) < ρ := hρpos
  have hρne : (ρ : ℝ≥0) ≠ 0 := hρ0.ne'
  have hρ12 : ρ ≤ 1 / 2 := hρhalf.2.le
  have hρ1 : ρ ≤ 1 := le_trans hρ12 (by rw [← NNReal.coe_le_coe]; norm_num)
  have hρ0R : (0 : ℝ) < (ρ : ℝ) := hρ0
  have hρ1R : ((ρ : ℝ)) ≤ 1 := by exact_mod_cast hρ1
  have hρ12R : ((ρ : ℝ)) ≤ 1 / 2 := by
    have := NNReal.coe_le_coe.mpr hρ12
    simpa using this
  have hσ0 : (0 : ℝ≥0) < ρ ^ m := by positivity
  have hσ1 : (ρ : ℝ≥0) ^ m ≤ 1 := pow_le_one₀ (by positivity) hρ1
  have hδpos : (0 : ℝ≥0) < 2 * ρ ^ m * ρ := by positivity
  have hδne : (2 * ρ ^ m * ρ : ℝ≥0) ≠ 0 := hδpos.ne'
  have hδ16 : (2 * ρ ^ m * ρ : ℝ≥0) ≤ 1 / 16 := by
    have hpm : (ρ : ℝ≥0) ^ m ≤ (1 / 2 : ℝ≥0) ^ m := by gcongr
    have hp4 : (1 / 2 : ℝ≥0) ^ m ≤ (1 / 2 : ℝ≥0) ^ 4 :=
      pow_le_pow_of_le_one (by positivity) (by rw [← NNReal.coe_le_coe]; norm_num) hm4
    have hpm4 : (ρ : ℝ≥0) ^ m ≤ (1 / 2 : ℝ≥0) ^ 4 := le_trans hpm hp4
    calc (2 * ρ ^ m * ρ : ℝ≥0) ≤ 2 * ((1 / 2 : ℝ≥0) ^ 4) * (1 / 2 : ℝ≥0) := by
          gcongr
      _ = 1 / 16 := by norm_num
  have hδ1 : (2 * ρ ^ m * ρ : ℝ≥0) ≤ 1 := by
    refine le_trans hδ16 ?_
    rw [← NNReal.coe_le_coe]; norm_num
  have hδ4 : ((2 * ρ ^ m * ρ : ℝ≥0) : ℝ) ≤ 1 / 4 := by
    have h : ((2 * ρ ^ m * ρ : ℝ≥0) : ℝ) ≤ ((1 / 16 : ℝ≥0) : ℝ) := by exact_mod_cast hδ16
    simpa using le_trans h (by norm_num)
  -- the heavy cap
  obtain ⟨k, hk⟩ := exists_heavy_cap s T
  set s' : Finset ι := s.filter (fun i => capIndex (T i).direction = k) with hs'def
  have hs'sub : s' ⊆ s := Finset.filter_subset _ _
  have he : ‖capVec k‖ = 1 := norm_capVec k
  have hcap : ∀ i ∈ s', (1 : ℝ) / 2 ≤ (inner ℝ (capVec k) (T i).direction : ℝ) := by
    intro i hi
    have hmem := Finset.mem_filter.mp (hs'def ▸ hi)
    have hspec := capIndex_spec (T i).toTube.norm_direction
    rwa [hmem.2] at hspec
  have hball' : ∀ i ∈ s', (T i).carrier ⊆ Metric.closedBall (0 : Space3) 1 :=
    fun i hi => hball i (hs'sub hi)
  set U : ι → ShadedTube (2 * ρ ^ m * ρ) Space3 :=
    sqFamily hσ0 he (2 * ρ ^ m * ρ) T with hUdef
  have hH1 : ∀ i ∈ s', (U i).carrier ⊆ Metric.closedBall (0 : Space3) 1 :=
    sqFamily_carrier_subset_closedBall hσ0 hσ1 he hball' hδ4
  have hmaxs' : Kakeya.maxDensity s' (fun i => (T i).toConvexSpaceBody)
      ≤ (ρ : ℝ≥0∞) ^ (-(η₁ / 2)) := le_trans (Kakeya.maxDensity_mono _ hs'sub) hKT
  have hH2 : ConvexSpaceBody.IsKatzTao s' (fun i => (U i).toConvexSpaceBody)
      (((2 * ρ ^ m * ρ : ℝ≥0) : ℝ≥0∞) ^ (-η₁)) := by
    refine le_trans (sqFamily_maxDensity_le hn hσ0 hσ1 hρ1 he hcap hδ1) ?_
    refine le_trans (by gcongr : (fatLoss : ℝ≥0∞)
        * Kakeya.maxDensity s' (fun i => (T i).toConvexSpaceBody)
      ≤ (fatLoss : ℝ≥0∞) * (ρ : ℝ≥0∞) ^ (-(η₁ / 2))) ?_
    have hb := ENNReal.coe_le_coe.mpr (katzTao_budgetN hρ0 m hη₁1 hktbud)
    rwa [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hρne,
      ENNReal.coe_rpow_of_ne_zero hδne] at hb
  have hmass : (((6 : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞)
        * ∑ i ∈ s, volume (T i).toShadedBody.shade
      ≤ ∑ i ∈ s', volume (T i).toShadedBody.shade := by
    rw [ENNReal.coe_inv (by norm_num : (6 : ℝ≥0) ≠ 0),
      ENNReal.inv_mul_le_iff (by simp) (by simp)]
    simpa using hk
  have hfulls' : (6 : ℝ≥0)⁻¹ * ρ ^ (η₁ / 2)
      ≤ ShadedBody.fullness s' (fun i => (T i).toShadedBody) := by
    refine le_trans ?_ (mul_fullness_le_of_subset hs'sub (fun i => (T i).toShadedBody) hmass)
    gcongr
  have hH3 : ShadedBody.fullness s' (fun i => (U i).toShadedBody)
      ≥ (2 * ρ ^ m * ρ : ℝ≥0) ^ η₁ := by
    refine le_trans ?_ (sqFamily_le_fullness hn hσ0 hσ1 hρ1 he hcap hδ1)
    refine le_trans (fullness_budgetN hρ0 m hη₁1 hktbud) ?_
    rw [mul_inv, mul_assoc]
    gcongr
  -- the cardinality hypothesis, now at the cut `θ`
  have hH4 : ((s'.card : ℝ)) < ((2 * ρ ^ m * ρ : ℝ≥0) : ℝ) ^ (-θ) := by
    have hdens : Kakeya.densityIn s' (fun i => ((T i).toTube).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall ≤ ((ρ : ℝ≥0∞))⁻¹ := by
      refine le_trans (Kakeya.le_maxDensity _ _ _) (le_trans hmaxs' ?_)
      have hρE : (ρ : ℝ≥0∞) ≤ 1 := by exact_mod_cast hρ1
      rw [show ((ρ : ℝ≥0∞))⁻¹ = (ρ : ℝ≥0∞) ^ (-1 : ℝ) by rw [ENNReal.rpow_neg_one]]
      exact ENNReal.rpow_le_rpow_of_exponent_ge hρE (by linarith)
    have hcard := Tube.card_le_of_densityIn_le (E := Space3) (s := s') hρne
      (T := fun i => (T i).toTube) hball' hdens
    rw [hn, ← hC₀def] at hcard
    have hzpN : (ρ : ℝ≥0) ^ (-((3 : ℕ) - 1 : ℤ)) = (ρ ^ 2)⁻¹ := by
      rw [show (-((3 : ℕ) - 1 : ℤ)) = (-2 : ℤ) by norm_num, zpow_neg]
      norm_num
      rfl
    have hzp : ((ρ : ℝ≥0∞)) ^ (-((3 : ℕ) - 1 : ℤ))
        = (((ρ ^ 2 : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
      rw [← ENNReal.coe_zpow hρne, hzpN]
    rw [hzp, show ((ρ : ℝ≥0∞))⁻¹ = (((ρ⁻¹ : ℝ≥0)) : ℝ≥0∞) from
      (ENNReal.coe_inv hρne).symm, ← ENNReal.coe_mul, ← ENNReal.coe_mul,
      ← ENNReal.coe_natCast] at hcard
    have hcardN : (s'.card : ℝ≥0) ≤ C₀ * ρ⁻¹ * (ρ ^ 2)⁻¹ := ENNReal.coe_le_coe.mp hcard
    have hx3 : (0 : ℝ) < (ρ : ℝ) ^ 3 := by positivity
    have hx4 : (0 : ℝ) < (ρ : ℝ) ^ 4 := by positivity
    have hcardR : ((s'.card : ℝ)) ≤ (C₀ : ℝ) * ((ρ : ℝ) ^ 3)⁻¹ := by
      have h := NNReal.coe_le_coe.mpr hcardN
      rw [NNReal.coe_mul, NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_inv, NNReal.coe_pow] at h
      calc ((s'.card : ℝ)) = ((s'.card : ℝ≥0) : ℝ) := by push_cast; ring
        _ ≤ (C₀ : ℝ) * ((ρ : ℝ))⁻¹ * (((ρ : ℝ)) ^ 2)⁻¹ := h
        _ = (C₀ : ℝ) * ((ρ : ℝ) ^ 3)⁻¹ := by field_simp
    have h4R : (4 : ℝ) * (C₀ : ℝ) * (ρ : ℝ) ≤ 1 := by
      have hb : (4 * C₀ * ρ : ℝ≥0) ≤ 1 := by simpa using hcardbud
      have h := NNReal.coe_le_coe.mpr hb
      rw [NNReal.coe_mul, NNReal.coe_mul, NNReal.coe_one] at h
      simpa using h
    have h4R' : 4 * ((C₀ : ℝ) * (ρ : ℝ)) ≤ 1 := by
      have hre : 4 * ((C₀ : ℝ) * (ρ : ℝ)) = 4 * (C₀ : ℝ) * (ρ : ℝ) := by ring
      rw [hre]
      exact h4R
    have hstrict : (C₀ : ℝ) * ((ρ : ℝ) ^ 3)⁻¹ < (2 * (ρ : ℝ) ^ 4)⁻¹ := by
      rw [show (2 * (ρ : ℝ) ^ 4)⁻¹ = 1 / (2 * (ρ : ℝ) ^ 4) from (one_div _).symm,
        lt_div_iff₀ (by positivity)]
      have hre : (C₀ : ℝ) * ((ρ : ℝ) ^ 3)⁻¹ * (2 * (ρ : ℝ) ^ 4)
          = 2 * ((C₀ : ℝ) * (ρ : ℝ)) := by
        field_simp
      rw [hre]
      linarith only [h4R']
    have hcoe : ((2 * ρ ^ m * ρ : ℝ≥0) : ℝ) = 2 * (ρ : ℝ) ^ (m + 1) := by
      push_cast
      rw [pow_succ]
      ring
    have hd0 : (0 : ℝ) < 2 * (ρ : ℝ) ^ (m + 1) := by positivity
    have hup : (2 * (ρ : ℝ) ^ (m + 1)) ^ θ ≤ 2 * (ρ : ℝ) ^ 4 := by
      rw [Real.mul_rpow (by norm_num) (by positivity),
        ← Real.rpow_natCast ((ρ : ℝ)) (m + 1), ← Real.rpow_mul hρ0R.le]
      have h2 : (2 : ℝ) ^ θ ≤ 2 := by
        have h := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) one_le_two hθ1
        rwa [Real.rpow_one] at h
      have hp : ((ρ : ℝ)) ^ ((((m : ℕ) + 1 : ℕ) : ℝ) * θ) ≤ (ρ : ℝ) ^ 4 := by
        rw [show ((ρ : ℝ) ^ 4) = ((ρ : ℝ)) ^ ((4 : ℕ) : ℝ) from (Real.rpow_natCast _ 4).symm]
        refine Real.rpow_le_rpow_of_exponent_ge hρ0R hρ1R ?_
        have hc : ((((m : ℕ) + 1 : ℕ) : ℝ)) = M := by rw [hMdef]; push_cast; ring
        rw [hc]
        push_cast
        linarith
      have hnn : (0 : ℝ) ≤ ((ρ : ℝ)) ^ ((((m : ℕ) + 1 : ℕ) : ℝ) * θ) :=
        Real.rpow_nonneg hρ0R.le _
      calc (2 : ℝ) ^ θ * ((ρ : ℝ)) ^ ((((m : ℕ) + 1 : ℕ) : ℝ) * θ)
          ≤ 2 * ((ρ : ℝ)) ^ ((((m : ℕ) + 1 : ℕ) : ℝ) * θ) := by
            exact mul_le_mul_of_nonneg_right h2 hnn
        _ ≤ 2 * (ρ : ℝ) ^ 4 := by
            exact mul_le_mul_of_nonneg_left hp (by norm_num)
    have hge : (2 * (ρ : ℝ) ^ 4)⁻¹ ≤ ((2 * ρ ^ m * ρ : ℝ≥0) : ℝ) ^ (-θ) := by
      rw [hcoe, Real.rpow_neg hd0.le]
      have hpos : (0 : ℝ) < (2 * (ρ : ℝ) ^ (m + 1)) ^ θ := Real.rpow_pos_of_pos hd0 θ
      exact one_div_le_one_div_of_le hpos hup |>.trans_eq (by rw [one_div]) |>.trans_eq' (by
        rw [one_div])
    linarith
  -- apply the hypothesis at the squeezed scale
  have hconc := hδsm s' U hH1 hH2 hH3 hH4
  rw [sqFamily_sum_shade hσ0 hσ1 hρ1 he hcap le_rfl,
    sqFamily_iUnion_shade hσ0 hσ1 hρ1 he hcap le_rfl] at hconc
  have hJ0 : Kakeya.affineJacobian (sqA hσ0 he) ≠ 0 := Kakeya.affineJacobian_ne_zero _
  have hJt : Kakeya.affineJacobian (sqA hσ0 he) ≠ ⊤ := Kakeya.affineJacobian_ne_top _
  have hconc' : ∑ i ∈ s', volume (T i).shade
      ≤ ((2 * ρ ^ m * ρ : ℝ≥0) : ℝ≥0∞) ^ (-(ε / (2 * M))) * (s'.card : ℝ≥0∞) ^ γ
        * volume (⋃ i ∈ s', (T i).shade) := by
    rw [show ((2 * ρ ^ m * ρ : ℝ≥0) : ℝ≥0∞) ^ (-(ε / (2 * M))) * (s'.card : ℝ≥0∞) ^ γ
          * (Kakeya.affineJacobian (sqA hσ0 he) * volume (⋃ i ∈ s', (T i).shade))
        = Kakeya.affineJacobian (sqA hσ0 he)
          * (((2 * ρ ^ m * ρ : ℝ≥0) : ℝ≥0∞) ^ (-(ε / (2 * M)))
            * (s'.card : ℝ≥0∞) ^ γ * volume (⋃ i ∈ s', (T i).shade)) from by ring] at hconc
    exact (ENNReal.mul_le_mul_iff_right hJ0 hJt).mp hconc
  have hcardle : (s'.card : ℝ≥0∞) ^ γ ≤ (s.card : ℝ≥0∞) ^ γ := by
    have hle : ((s'.card : ℝ≥0∞)) ≤ (s.card : ℝ≥0∞) := by
      exact_mod_cast Finset.card_le_card hs'sub
    exact ENNReal.rpow_le_rpow hle hγ
  have hunionle : volume (⋃ i ∈ s', (T i).shade) ≤ volume (⋃ i ∈ s, (T i).shade) :=
    measure_mono (Set.biUnion_subset_biUnion_left hs'sub)
  have hacc : (6 : ℝ≥0∞) * ((2 * ρ ^ m * ρ : ℝ≥0) : ℝ≥0∞) ^ (-(ε / (2 * M)))
      ≤ (ρ : ℝ≥0∞) ^ (-ε) := by
    have hb := ENNReal.coe_le_coe.mpr (accuracy_budgetN hρ0 m hε haccbud)
    rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hδne,
      ENNReal.coe_rpow_of_ne_zero hρne] at hb
    simpa using hb
  calc ∑ i ∈ s, volume (T i).shade
      ≤ 6 * ∑ i ∈ s', volume (T i).shade := hk
    _ ≤ 6 * (((2 * ρ ^ m * ρ : ℝ≥0) : ℝ≥0∞) ^ (-(ε / (2 * M)))
        * (s'.card : ℝ≥0∞) ^ γ * volume (⋃ i ∈ s', (T i).shade)) := by gcongr
    _ ≤ 6 * (((2 * ρ ^ m * ρ : ℝ≥0) : ℝ≥0∞) ^ (-(ε / (2 * M)))
        * (s.card : ℝ≥0∞) ^ γ * volume (⋃ i ∈ s, (T i).shade)) := by gcongr
    _ = (6 * ((2 * ρ ^ m * ρ : ℝ≥0) : ℝ≥0∞) ^ (-(ε / (2 * M))))
        * (s.card : ℝ≥0∞) ^ γ * volume (⋃ i ∈ s, (T i).shade) := by ring
    _ ≤ (ρ : ℝ≥0∞) ^ (-ε) * (s.card : ℝ≥0∞) ^ γ
        * volume (⋃ i ∈ s, (T i).shade) := by gcongr

/-- **Every `β`-only cardinality cut is circular.**  For every `θ > 0`, `SmallCardCut θ γ`
already gives the full estimate. -/
theorem katzTaoEstimate_of_smallCardCut {γ θ : ℝ} (hγ : 0 ≤ γ) (hθ : 0 < θ)
    (hsc : SmallCardCut.{v} θ γ) : Kakeya.KatzTaoEstimate.{v} Space3 γ := by
  classical
  set θ' : ℝ := min θ 1 with hθ'def
  have hθ'0 : 0 < θ' := lt_min hθ one_pos
  have hθ'1 : θ' ≤ 1 := min_le_right _ _
  have hsc' : SmallCardCut.{v} θ' γ := smallCardCut_mono (min_le_left _ _) hsc
  set m : ℕ := max 4 ⌈4 / θ'⌉₊ with hmdef
  have hm4 : 4 ≤ m := le_max_left _ _
  have hmθ : 4 ≤ ((m : ℝ) + 1) * θ' := by
    have h1 : (4 / θ' : ℝ) ≤ (⌈4 / θ'⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈4 / θ'⌉₊ : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast le_max_right 4 ⌈4 / θ'⌉₊
    have h3 : (4 / θ' : ℝ) * θ' = 4 := by field_simp
    nlinarith [hθ'0, h1, h2, h3]
  exact katzTaoEstimate_of_smallCardCut_aux hγ hθ'0 hθ'1 m hm4 hmθ hsc'

/-- The converse is the trivial direction: `SmallCardCut` only adds a hypothesis. -/
theorem smallCardCut_of_katzTaoEstimate {γ θ : ℝ}
    (h : Kakeya.KatzTaoEstimate.{v} Space3 γ) : SmallCardCut.{v} θ γ := by
  intro ε hε
  obtain ⟨η, hη0, hev⟩ := h ε hε
  refine ⟨min η 1, lt_min hη0 one_pos, min_le_right _ _, ?_⟩
  filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : ℝ≥0) < 1 from zero_lt_one)] with δ hδev hδ
  obtain ⟨hδ0, hδ1⟩ := hδ
  intro ι s T hball hKT hfull _
  exact hδev s T hball
    (Kakeya.ML2Assembly.isKatzTao_of_exponent_le hδ1.le (min_le_left _ _) hKT)
    (Kakeya.ML2Assembly.le_of_rpow_exponent_le hδ0 hδ1.le (min_le_left _ _) hfull)

/-- **The headline of Part II.**  At *every* cut, the small-cardinality case is the theorem. -/
theorem smallCardCut_iff_katzTaoEstimate {γ θ : ℝ} (hγ : 0 ≤ γ) (hθ : 0 < θ) :
    SmallCardCut.{v} θ γ ↔ Kakeya.KatzTaoEstimate.{v} Space3 γ :=
  ⟨katzTaoEstimate_of_smallCardCut hγ hθ, smallCardCut_of_katzTaoEstimate⟩


end Cut

/-! ## Part III — what the GWZ route actually delivers, and where the residue is

`Kakeya.ML2Assembly.Dichotomy`'s **gain** alternative needs no cardinality hypothesis at all: it
converts through `Kakeya.ML2Assembly.card_le_rpow_neg_four` at the budget `4c ≤ g`.  Only the
**absolute-accuracy** alternative needs one, and it needs it precisely because the accuracy `ε₀`
is `β`-only while the goal's accuracy `ε` is arbitrary
(`Kakeya.ML2Band.absoluteLossRoute_insufficient`).

So the honest conclusion of the route is the *banded* estimate, and the residue is exactly the
band's complement — which Part II shows is the whole theorem, at every band. -/

section Banded

universe w


end Banded

/-! ## Part IV — the `ε`-freeness trilemma, and what GWZ's branch (i) actually needs

GWZ Definition 3.4 puts the accuracy **inside** `K_KT`: `K_{KT}(β)` is *"for every `ε > 0` there
exist `η = η(ε,β)` and `δ₀ = δ₀(ε,β)` such that …"*.  Main Lemma 2's `ν = ν(β)` therefore sits
outside that `∀ ε`, and the protected Lean statement renders exactly that.

GWZ's proof of branch (i) reads Theorem 7.3(B) **at the outer `ε`** (*"Let `ε₁` and `δ₁` be the
output of Theorem 7.3(B) with `ε` as above"*), obtains `μ ≤ δ^{-ε}`, and closes because
`|𝕋|^{β-ν} ≥ 1`.  That step needs **no cardinality hypothesis** —
`Kakeya.ML2Squeeze.branchOne_closes_of_accuracy_le` below — but it makes `ε₁ = E ε`, hence
`ν ≤ η₁ ≤ ε₂ ≤ ε₁/5 = E ε/5`, an `ε`-dependent gain.  The published parenthesis *"(since `ε₁` and
`ϖ` depend only on `β`, `ε₂` depends only on `β`)"* is inconsistent with the sentence before it;
that is the typo Prof. Hong Wang identified.

Her repair reads 7.3(B) at a `β`-only accuracy `ε₀`.  That restores `ε`-freeness and forces a
`β`-only cardinality cut (`Kakeya.ML2Band.absoluteLossRoute_insufficient`), whose complement Part
II shows to be the theorem itself — at *every* cut.

The two horns are `Kakeya.ML2Squeeze.ml2_epsFree_horns`. -/

section Horns

variable {δ : ℝ}


end Horns

/-! ## Part V — the replacement: a gain-only core needs no cut at all

GWZ Lemma 9.1's conclusion is a genuine `δ`-**gain**, `μ ≤ δ^ν |𝕋|^β`, with no accuracy in it;
`Kakeya.ML2Assembly.Dichotomy`'s alternative (ii) has the same shape.  A gain converts to the goal
at **every** cardinality, through the crude bound `|𝕋| ≤ δ^{-4}`
(`Kakeya.ML2Assembly.card_le_rpow_neg_four`) at the `ε`-free budget `4c ≤ g`.  So the cardinality
split is forced by, and only by, the *other* alternative — the absolute-accuracy bound
`μ ≤ δ^{-ε₀}` coming from Theorem 7.3(B) read at a `β`-only accuracy.

`Kakeya.ML2Squeeze.katzTaoEstimate_sub_of_gainOnly` is the statement of that: a geometric core
that always produces a gain gives Main Lemma 2's drop outright, with no `SmallCard`, no
`KatzTaoEstimateGE`, and no case split.  Together with
`Kakeya.ML2Squeeze.forall_cut_circular` this is the whole diagnosis:

* every-scale branch as a **gain** — no cut, no circularity;
* every-scale branch as an **`ε`-free accuracy** — a `β`-only cut is forced
  (`Kakeya.OmegaAssessment.oneParam_fixed_loss_forces_card`), and every `β`-only cut is the
  theorem;
* every-scale branch as an **`ε`-dependent accuracy** — no cut, but the gain is `ε`-dependent
  (`Kakeya.ML2Spine.not_epsFree_of_outerAccuracy'`). -/

section GainOnly

universe w'

/-- **RETRACTED — this predicate is FALSE for `g > 0`; see Part VII,
`Kakeya.ML2Squeeze.not_gainOnly`.**

`Kakeya.ML2Assembly.Dichotomy` with the absolute-accuracy alternative **and** the cardinality
hypothesis both deleted: the geometric core always delivers a genuine `δ`-gain.  There is no `ε`
in this predicate — it has the shape of GWZ Lemma 9.1's own conclusion. -/
def GainOnly (β g η : ℝ) : Prop :=
  ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0,
    ∀ {ι : Type w'} (s : Finset ι) (T : ι → ShadedTube δ Space3),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      ConvexSpaceBody.IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ℝ≥0∞) ^ (-η)) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
      ∑ i ∈ s, volume (T i).shade
        ≤ (δ : ℝ≥0∞) ^ g * (s.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ s, (T i).shade)


end GainOnly

/-! ## Part VI — the bridge from GWZ Lemma 9.1 to `GainOnly`

GWZ Lemma 9.1's conclusion, `μ(𝕋,Y) ≤ δ^ν |𝕋|^β`, already has the gain shape, so the *currency*
conversion is free (`Kakeya.ML2Squeeze.gainOnly_iff_gainOnlyMult`), and the finish is
`Kakeya.ML2Squeeze.katzTaoEstimate_sub_of_gainOnlyMult`: a core that produces 9.1's conclusion for
every admissible family gives Main Lemma 2's drop, with **no** cardinality split.

What 9.1 does *not* give is the two extra hypotheses it carries on the family — the uniformity
witness and the `ρ`-tube count.  Both are named below, transcribed verbatim, and the count is the
obstruction: `Kakeya.ML2Squeeze.scaleCount_forces_band` shows that 9.1's third bullet, read at
`ρ = δ^{1-ϖ}` against any essentially-distinct cover at that scale, **already forces
`δ⁻¹ ≤ |𝕋|`**.  So Lemma 9.1 applied *directly* to the given family fires only on the band and
delivers `Kakeya.ML2Squeeze.KatzTaoEstimateGE 1`, which
`Kakeya.ML2Squeeze.residue_of_banded` and `Kakeya.ML2Squeeze.forall_cut_circular` show to be
circular.  **The count must be supplied at a rescaled scale** — which is exactly what GWZ's
two-scale split does, and exactly what R1 is for. -/

section Bridge

universe w2


/-! ### The two hypotheses Lemma 9.1 carries that `GainOnly` does not supply -/


/-- GWZ Lemma 9.1's third bullet as a predicate on one family: at each scale
of the window there exists an essentially distinct, all-used `ρ`-tube family
of cardinality at least `ρ^{-2-ζ}`. -/
def ScaleCount (ϖ ζ : ℝ) {δ : ℝ≥0} {ι : Type w2} (s : Finset ι)
    (T : ι → ShadedTube δ Space3) : Prop :=
  ∀ ρ : ℝ≥0, ρ ∈ Set.Icc (δ ^ (1 - ϖ)) (δ ^ ϖ) →
    ∃ (κ : Type w2) (tρ : Finset κ) (Tρ : κ → Tube ρ Space3),
      (tρ : Set κ).Pairwise
        (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
      (∀ j ∈ tρ, ∃ i ∈ s, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
      (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)


/-! ### The chain, and the fidelity compatibility on Lemma 9.1 -/


/-! ### The missing piece, named

`Kakeya.ML2Squeeze.gainOnlyMult_of_lemma91Body` reduces `GainOnly` to Lemma 9.1's two side
conditions, and `Kakeya.ML2Squeeze.not_scaleCount_of_card_lt_delta_inv` shows the second of them
**fails on every family below the band** `|𝕋| < δ⁻¹/C`.  That is not a defect of the bridge: it is
the correct
statement of where Lemma 9.1 lives.  In GWZ §9, Lemma 9.1 is applied only inside the *window*
branch, to a rescaled family for which the count is supplied by the two-scale structure; the other
branch — the every-scale branch — is closed by Theorem 7.3(B), and that is the branch that
produces an *accuracy* rather than a gain, hence the cardinality cut.

So the single missing input is the **upgrade of the every-scale branch from an accuracy to a
gain**.  `Kakeya.ML2Squeeze.GainDichotomy` names it: it is `Kakeya.ML2Assembly.Dichotomy` with its
first alternative `μ ≤ δ^{-ε₀}` replaced by a gain `μ ≤ δ^{g₁}|𝕋|^β`, and with the cardinality
hypothesis deleted — that hypothesis existed only to convert the accuracy. -/


end Bridge

/-! ## Part VII — CORRECTION: `GainOnly` is **false**, and the third arm of the filter

**This part retracts the reading of Part V.**  `Kakeya.ML2Squeeze.GainOnly` and
`Kakeya.ML2Squeeze.GainDichotomy` are **inconsistent**, so
`Kakeya.ML2Squeeze.katzTaoEstimate_sub_of_gainOnly`,
`katzTaoEstimate_sub_of_gainOnlyMult` and `katzTaoEstimate_sub_of_gainDichotomy` — all true
theorems — have hypotheses that no core can supply.  They are kept, with this cross-reference, as
the record of a closed column.

The mechanism is independent of every loss budget and survives deleting the accuracy.  A single
fully shaded `δ`-tube meets **every** hypothesis those predicates impose — ball containment,
`Δ_max ≤ δ^{-η}` (a singleton has `Δ_max ≤ 1`), and `λ ≥ δ^η` (a singleton is fully shaded, so
`λ = 1`) — and for it `∑|Y| = |⋃ Y| ∈ (0,∞)` and `|𝕋| = 1`.  So any conclusion of the shape
`∑|Y| ≤ F(δ)·|𝕋|^β·|⋃ Y|` forces `1 ≤ F(δ)`.  A gain has `F(δ) = δ^{g} < 1`.

Stated once, for arbitrary `F`, this is `Kakeya.ML2Squeeze.one_le_of_massBound`: **the third arm of
the acceptance test**.  Its two corollaries are `not_gainOnly` and `not_gainDichotomy_of_budget`,
the latter under exactly the budget of `katzTaoEstimate_sub_of_gainDichotomy`.

The error was mine, and it was avoidable: the `μ ≥ 1` floor is recorded in this very file's Part IV
discussion of why the *gain* alternative of `Kakeya.ML2Assembly.Dichotomy` cannot cover small
families.  I applied it to the dichotomy's second alternative and then failed to apply it to
`GainOnly`, which is that alternative with the cardinality clause deleted. -/

section Refutation

universe w3


/-! ### The corollaries: the gain column is empty -/


/-! ### Candidate 1: the Ω-budget, and its own trilemma

`Kakeya.KatzTaoEstimateOmega β ω` replaces the accuracy factor `δ^{-ε}` by `δ^{-ω-ε}`, with the
budget `ω` quantified **before** `ε`.  It **passes the third arm**: at `|𝕋| = 1` its conclusion
factor is `δ^{-ω-ε} ≥ 1`, so `Kakeya.ML2Squeeze.one_le_of_massBound` does not touch it.  That is
the real content of the donor branch's *"branch (i) of the assembly below is unconditional"*.

But the budget must still dominate the accuracy at which Theorem 7.3(B) is read, and that
reproduces the `ε`-trilemma one level up.

* **Horn A** — if `ε₀` is fixed before the budget (`β`-only), then at every budget `ω < ε₀` the
  every-scale bound `μ ≤ δ^{-ε₀}` fails to give the `ω`-form's goal at the single tube, for every
  `ε < ε₀ - ω` (`Kakeya.ML2Squeeze.omega_branchOne_needs_budget`).  So the branch is *not*
  unconditional at small budget and needs a cardinality floor — which
  `Kakeya.ML2Squeeze.no_unconditional_card_floor` says nothing supplies unconditionally and
  `Kakeya.ML2Squeeze.forall_cut_circular` says is circular once assumed.
* **Horn B** — horn A therefore forces `ε₀ ≤ ω`, and then the spine gives
  `g ≤ E(ε₀)/25 ≤ ω/25`, so no positive drop is uniform in the budget
  (`Kakeya.ML2Squeeze.omega_no_uniform_drop`).  That is
  `Kakeya.OmegaAssessment.no_uniform_floor_of_starved_drop` explained rather than observed: the
  drop is starved *because* the branch only closes above the budget.

The descent `ω → 0` needs exactly the uniform floor horn B denies.  So the Ω-budget removes the
cardinality split (which the gain column could not) but pays for it in the drop. -/


/-! ### Candidate 2: a device that *produces* the cardinality floor

`Kakeya.ML2Squeeze.no_unconditional_card_floor` is the whole of what can be said cheaply, and it is
decisive about the *shape*: no device produces `δ^{-θ} ≤ |𝕋|` for **all** admissible families,
because the single fully shaded tube is admissible and has `|𝕋| = 1`.  A floor-producing device
must therefore be conditional on extra structure (bilinearity, broadness, very-not-stickiness), and
the families lacking that structure are a residue.  If that residue is delimited by a cardinality
cut, `Kakeya.ML2Squeeze.forall_cut_circular` closes it; if it is handled by a rescaling induction,
 already prices that induction at `b_N(1-a)` — a fixed power of `δ` —
unless the planar case is discharged.

This is why the two candidates are not symmetric: the Ω-budget's open slot is a *bound on a
function* (`exists_uniformDrop`), while candidate 2's open slot is a *geometric theorem about a
structured subclass*, and the unstructured complement is the residue that has closed three times
now. -/


/-! ### Where the wall actually is: the spine dominates the drop

Collecting the three columns, the every-scale branch can deliver its bound in exactly three shapes,
and each is now closed:

* a **gain** `μ ≤ δ^{g}|𝕋|^β` — **false**, by `Kakeya.ML2Squeeze.not_gainOnly` (single tube);
* an **accuracy** `μ ≤ δ^{-ε₀}` with `ε₀` fixed before `ε` — needs a cardinality floor at the
  single tube (`Kakeya.ML2Squeeze.omega_branchOne_needs_budget` at `ω = 0`), and every floor is
  **circular** (`Kakeya.ML2Squeeze.forall_cut_circular`);
* an **accuracy at the outer `ε`** — closes with only `1 ≤ |𝕋|`
  (`Kakeya.ML2Squeeze.branchOne_closes_of_accuracy_le`), but the spine then forces `ν ≤ ε₁/25`.

The third item is the only one that is not a refutation, and its obstruction is **structural, not
geometric**: `Kakeya.ML2Spine.IsSpine`'s own fields chain `ν ≤ η₁ ≤ e ≤ ε₁/25`, so the drop is
dominated by the every-scale exponent whatever that exponent is.  That domination — not any
property of `E`, and not any budget — is the binding constraint.

`Kakeya.ML2Squeeze.not_dropDominationFree` states it, and it is stronger and cleaner than
`Kakeya.ML2Spine.not_epsFree_of_outerAccuracy'`: no hypothesis on `E` at all. -/


/-! ### Is the domination ours or GWZ's?  **GWZ's.**

`Kakeya.ML2Spine.IsSpine` is this development's own bookkeeping structure — it carries **no**
blueprint `\lean{}` tag, so it renders no labelled statement.  That makes "the fraction is
self-imposed" a live hypothesis, and this development has imposed tightest-available readings
before.  It is not the case here, and the check is short: two of GWZ §9's own sentences already
give the fraction, quoted verbatim from GWZ.

> *"Define `N = ⌈25/ε₂²⌉`, and let `η ≤ η₁ ≤ … ≤ η_N ≤ ε₂` be a sequence of numbers to be chosen
> later."*

> *"If Conclusion (i) holds, then (provided we select `ε₂ ≤ ε₁/5`) we have that `𝕋` is `δ^{-ε₁}`
> Katz–Tao at every scale."*

> *"The quantity `ν` from the conclusion of Main Lemma 2 will be selected small compared to `η₁`"*
> … *"in order to prove establish (mugoalml2quant) with `ν = η₁`."*

So `ν ≤ η₁ ≤ ε₂ ≤ ε₁/5` **in GWZ's own text**, with no field of this development involved.
`Kakeya.ML2Squeeze.GWZSpineChain` transcribes exactly those three, and
`Kakeya.ML2Squeeze.not_gwzDropDominationFree` shows they already forbid an `ε₁`-free drop.

Where the development *does* tighten: GWZ's rung ceiling is `ε₂`, and `IsSpine.rung_top` sets the
top rung to `e = 1/√N ≤ ε₂/5` instead (documented in `SpineParams.lean` as *"replacing `ε₂` by `e`
in every denominator makes each constraint strictly harder"*).  That is a factor `5`, and
`Kakeya.ML2Squeeze.gwzSpineChain_of_isSpine` shows the tighter chain **implies** GWZ's, so
`Kakeya.ML2Squeeze.not_dropDominationFree` is not an artefact of the tighter reading: relaxing all
the way back to the paper still gives `ν ≤ ε₁/5`, and `not_gwzDropDominationFree` still fires.

*Filter note.*  `Kakeya.ML2Squeeze.one_le_of_massBound` does not apply to anything in this section
and that is a certification, not an omission: these are scalar statements about the parameter
chain, with no per-family conclusion of the shape `∑|Y| ≤ F(δ)·|𝕋|^β·|⋃Y|` for it to test. -/


/-! ### Does the single-tube witness cover the *de-duplicated* count?  **Yes.**

's carried-cardinality induction transports by `R`-fold duplication, which multiplies `|𝕋|`
and `Δ_max` by the same `R`; so the transport-invariant quantity is the ratio `|𝕋| / Δ_max`, and
CAR's next target is a lower bound on *that* rather than on `|𝕋|`.  The worry is that
`Kakeya.ML2Squeeze.no_unconditional_card_floor` might be blind to it, because a
duplication-generated witness has `|𝕋|` large while `|𝕋|/Δ_max` is not.

It is not blind, and the reason is that the witness is at the **opposite** extreme: the single
fully shaded tube is duplication-*minimal*.  It has `|𝕋| = 1` and `Δ_max = 1` — the upper bound
because a singleton family's density in any test body is at most one, the lower bound by testing
the density at the member's own body — so the ratio is `1`, and `δ^{-θ} ≤ 1` fails for every
`θ > 0`.  `Kakeya.ML2Squeeze.no_unconditional_dedup_floor`.

So **that candidate stays shut**: no device produces a lower bound on `|𝕋|/Δ_max` for all
admissible families either.  As with `no_unconditional_card_floor`, this constrains the *shape* of
a floor-producing device — it must be conditional on structure — and says nothing against the
carried-band re-encoding itself, whose transport is between families that already exist.

*Filter note, taking the correction.*  Filter 1 cannot discriminate at the top of the reduction,
since `Kakeya.ML2Squeeze.forall_cut_circular` makes every sufficient condition satisfy it by the
letter; the discriminator there is whether **both directions compile**.  The results of this file
that sit at the top are stated as biconditionals for exactly that reason
(`smallCardCut_iff_katzTaoEstimate`, `smallCard_iff_katzTaoEstimate`,
`gainOnly_iff_gainOnlyMult`), and `Kakeya.ML2Squeeze.one_le_of_massBound` is unaffected. -/


end Refutation

end Kakeya.ML2Squeeze

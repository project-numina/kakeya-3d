/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Rescaling.KatzTao
public import Kakeya.DimensionThree.MainLemma1.Rescaling.UniformEveryScale
public import Kakeya.Pigeonhole
public import Kakeya.Factoring.Pigeonhole

/-!
# The middle factor at average fullness

`Kakeya.ml1Boot.multiplicity_le_middle` asks its caller for a *per-tube* two-sided shading
bracket `Λ⁻¹ μ₀ |T| ≤ |Y(T)| ≤ Λ μ₀ |T|` at an externally supplied constant `Λ`.  That
demand is not met by the producer, and the blueprint's repair is to make the middle factor
consume only the **average** fullness `δ ^ η(γ) ≤ λ(𝕌, Z)` and to perform the density
normalization *inside* the theorem, paying for it in shade mass.

This file carries out that repair.  The normalization is
`Kakeya.ml1Boot.exists_internalDensityNormalization`: discard the tubes of below-average
shading (`ShadedBody.discardLowShading`, a `1/2`-refinement), then pigeonhole the surviving
densities into a single dyadic band (`ShadedBody.exists_isCRefinement_comparable_density`).
The dyadic loss `1 + log₂ (1/a)` is bounded by the *polynomial* `4 / a`
(`Kakeya.ml1Boot.one_add_logb_le_four_div`), which is what keeps the whole bookkeeping inside
the `δ`-power ledger and makes a `C_u(δ)`-style public parameter unnecessary: the bracket
constant handed to `Kakeya.ml1Boot.exists_normalizedMiddleData` is the fixed `Λ = 2`, so the
uniformity constant `Kakeya.ml1Boot.normalizedUnif.C C_unif 2` of the rescaled family is still
chosen before `δ`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya

namespace ml1Boot

section Internal

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The dyadic pigeonholing loss is polynomial in the density floor.**

`ShadedBody.exists_isCRefinement_comparable_density` retains a `(1 + log₂ (1/a))⁻¹` fraction
of the shading mass, where `a` is the pointwise density floor.  The logarithm is bounded by
`4 / a` on `(0, 1]`, which is all this development ever needs: a `δ`-power floor
`a ≥ δ ^ e` then gives a `δ`-power loss `δ ^ (-e)`, and no `log (1/δ)`-absorption lemma is
required anywhere downstream. -/
theorem one_add_logb_le_four_div {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    1 + Real.logb 2 a⁻¹ ≤ 4 / a := by
  have hx1 : (1 : ℝ) ≤ a⁻¹ := one_le_inv_iff₀.mpr ⟨ha0, ha1⟩
  have hxpos : (0 : ℝ) < a⁻¹ := inv_pos.mpr ha0
  have hlog : Real.log a⁻¹ ≤ a⁻¹ - 1 := Real.log_le_sub_one_of_pos hxpos
  have hlog2 : (2 : ℝ) / 3 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hlognn : 0 ≤ Real.log a⁻¹ := Real.log_nonneg hx1
  have hkey : Real.logb 2 a⁻¹ ≤ (3 / 2) * a⁻¹ := by
    rw [Real.logb, div_le_iff₀ (by linarith : (0:ℝ) < Real.log 2)]
    nlinarith [hlognn, hlog, hlog2, hxpos]
  have h4 : (4 : ℝ) / a = 4 * a⁻¹ := by rw [div_eq_mul_inv]
  rw [h4]
  linarith [hx1, hkey]

/-- **The middle factor's density normalization, done internally** (blueprint §4.3, PO-2).

From nothing but the *average* fullness `λ ≤ λ(𝕌, Z)` of a nonempty family of shaded
`τ`-tubes this produces a subfamily `u₂` on which the shading densities lie in a single
dyadic band — i.e. a two-sided per-tube bracket at the **fixed** constant `Λ = 2` — together
with the three retention certificates the middle factor pays for it in:

* the multiplicity loss `µ(u, Z) ≤ (16 / λ) µ(u₂, Z)`;
* the surviving average fullness `λ² / 16 ≤ λ(u₂, Z)`;
* the cardinality retention `(λ² / 16) |u| ≤ |u₂|`, which is what transports the Frostman
  constant by `ConvexSpaceBody.frostmanConstIn_subfamily_le`.

Every loss is a power of `λ`, hence a power of `δ` once `λ ≥ δ ^ η(γ)`; this is where
`Kakeya.ml1Boot.one_add_logb_le_four_div` is used, and it is why the caller never needs a
`log (1/δ)`-absorption lemma.

The order of the two steps is the point of the repair.  Discarding the below-average tubes
first (`ShadedBody.discardLowShading` at level `1/2`) is what bounds the number of dyadic
bands, and the dyadic band is selected *afterwards*; both steps only pass to a subfamily, so
the one-sided uniformity `Kakeya.IsFlatPrismUniform` of the input survives verbatim by
`Kakeya.IsFlatPrismUniform.mono_index`.  It is precisely because the middle factor reads
uniformity one-sidedly that "uniformize, then density-restrict" does not destroy the
uniformity and the normalization can live inside the theorem. -/
theorem exists_internalDensityNormalization [Nontrivial E] {ι : Type*} {τ : ℝ≥0}
    (hτ0 : 0 < τ)
    {u : Finset ι} (U : ι → ShadedTube τ E) (hu : u.Nonempty)
    {lam : ℝ≥0} (hlam0 : 0 < lam)
    (hfull : (lam : ℝ≥0∞)
      ≤ (ShadedBody.fullness u (fun k => (U k).toShadedBody) : ℝ≥0∞)) :
    ∃ u₂ ⊆ u, u₂.Nonempty ∧ ∃ μ₀ : ℝ≥0∞, 0 < μ₀ ∧
      (∀ k ∈ u₂, ((2 : ℝ≥0) : ℝ≥0∞)⁻¹ * μ₀ * volume (U k).carrier
            ≤ volume (U k).shade ∧
          volume (U k).shade ≤ ((2 : ℝ≥0) : ℝ≥0∞) * μ₀ * volume (U k).carrier) ∧
      ShadedBody.multiplicity u (fun k => (U k).toShadedBody)
          ≤ 16 / (lam : ℝ≥0∞)
            * ShadedBody.multiplicity u₂ (fun k => (U k).toShadedBody) ∧
      (lam : ℝ≥0∞) ^ 2 / 16
          ≤ (ShadedBody.fullness u₂ (fun k => (U k).toShadedBody) : ℝ≥0∞) ∧
      (lam : ℝ≥0∞) ^ 2 / 16 * (u.card : ℝ≥0∞) ≤ (u₂.card : ℝ≥0∞) := by
  classical
  set Y : ι → ShadedBody E := fun k => (U k).toShadedBody with hY
  obtain ⟨i₀, hi₀⟩ := hu
  have hu : u.Nonempty := ⟨i₀, hi₀⟩
  set v : ℝ≥0∞ := volume (U i₀).carrier with hv_def
  have hvol : ∀ i ∈ u, volume (Y i).carrier = v := by
    intro i _
    simpa [hY, hv_def] using
      _root_.Tube.volume_carrier_eq_volume_carrier (U i).toTube (U i₀).toTube
  have hv_pos : 0 < v := by
    have hc : 0 < (_root_.Tube.le_volume.c (Module.finrank ℝ E) : ℝ≥0∞) :=
      ENNReal.coe_pos.mpr (_root_.Tube.le_volume.c_pos (Module.finrank ℝ E))
    have hδp : 0 < (τ : ℝ≥0∞) ^ (Module.finrank ℝ E - 1) :=
      ENNReal.pow_pos (ENNReal.coe_pos.mpr hτ0) (Module.finrank ℝ E - 1)
    exact lt_of_lt_of_le (ENNReal.mul_pos hc.ne' hδp.ne')
      (by simpa [hv_def] using _root_.Tube.le_volume (U i₀).toTube)
  have hv_top : v ≠ ⊤ := by
    rw [hv_def]
    exact (U i₀).isCompact.measure_ne_top
  -- the family's own fullness
  set lu : ℝ≥0 := ShadedBody.fullness u Y with hlu
  have hlam_lu : lam ≤ lu := by exact_mod_cast hfull
  have hlu0 : 0 < lu := lt_of_lt_of_le hlam0 hlam_lu
  have hlu1 : lu ≤ 1 := ShadedBody.fullness_le_one u Y
  -- total carrier and shading mass
  have hsumcar : ∑ i ∈ u, volume (Y i).carrier = (u.card : ℝ≥0∞) * v := by
    rw [Finset.sum_congr rfl hvol, Finset.sum_const, nsmul_eq_mul]
  have hcard0 : (0 : ℝ≥0∞) < (u.card : ℝ≥0∞) := by
    exact_mod_cast Finset.card_pos.mpr hu
  have hsumshade : ∑ i ∈ u, volume (Y i).shade = (lu : ℝ≥0∞) * ((u.card : ℝ≥0∞) * v) := by
    rw [ShadedBody.sum_volumeReal_shade_eq_fullness_mul u Y, hsumcar]
  have hmass_pos : 0 < ∑ i ∈ u, volume (Y i).shade := by
    rw [hsumshade]
    exact ENNReal.mul_pos (by exact_mod_cast hlu0.ne')
      (ENNReal.mul_pos hcard0.ne' hv_pos.ne').ne'
  -- Step 1: discard the tubes of below-average shading.
  set u₀ : Finset ι := ShadedBody.discardLowShading u Y (1 / 2 : ℝ≥0) with hu₀
  have hu₀u : u₀ ⊆ u := ShadedBody.discardLowShading_subset u Y _
  have href0 : ShadedBody.IsCRefinement u₀ Y u Y (1 - (1 / 2 : ℝ≥0)) :=
    ShadedBody.isCRefinement_discardLowShading u Y (by norm_num)
  have hhalf : (1 : ℝ≥0) - (1 / 2 : ℝ≥0) = (1 / 2 : ℝ≥0) := by
    rw [← NNReal.coe_inj]; push_cast; norm_num
  rw [hhalf] at href0
  -- the pointwise density floor on `u₀`
  set aa : ℝ≥0 := (1 / 2 : ℝ≥0) * lu with haa
  have haa0 : 0 < aa := by
    rw [haa]; exact mul_pos (by norm_num) hlu0
  have haa1 : aa ≤ 1 := by
    rw [haa]
    calc (1 / 2 : ℝ≥0) * lu ≤ (1 / 2 : ℝ≥0) * 1 := by gcongr
      _ ≤ 1 := by norm_num
  have hZ : ∀ i ∈ u₀, (aa : ℝ≥0∞) * volume (Y i).carrier ≤ volume (Y i).shade := by
    intro i hi
    have := ShadedBody.le_volume_shade_of_mem_discardLowShading (c := (1 / 2 : ℝ≥0)) hi
    calc (aa : ℝ≥0∞) * volume (Y i).carrier
        = ((1 / 2 : ℝ≥0) : ℝ≥0∞) * (lu : ℝ≥0∞) * volume (Y i).carrier := by
          rw [haa]; push_cast; ring
      _ ≤ volume (Y i).shade := this
  have hu₀ne : u₀.Nonempty := by
    rcases Finset.eq_empty_or_nonempty u₀ with h | h
    · exfalso
      have := href0.2
      rw [h] at this
      simp only [Finset.sum_empty, nonpos_iff_eq_zero, mul_eq_zero] at this
      rcases this with h1 | h2
      · exact absurd h1 (by simp)
      · exact absurd h2 hmass_pos.ne'
    · exact h
  -- Step 2: pigeonhole the surviving densities into one dyadic band.
  obtain ⟨u₂, hu₂u₀, lam2, hlam20, href2, hband, haa_lam2, -⟩ :=
    ShadedBody.exists_isCRefinement_comparable_density (V := Y) hu₀ne
      (fun i hi => hvol i (hu₀u hi)) hv_pos.ne' haa0 haa1 hZ
  set D : ℝ≥0 := (1 + Real.logb 2 ((aa : ℝ))⁻¹).toNNReal with hD
  have hlogb_nn : 0 ≤ 1 + Real.logb 2 ((aa : ℝ))⁻¹ := by
    have : 0 ≤ Real.logb 2 ((aa : ℝ))⁻¹ :=
      Real.logb_nonneg (by norm_num) (one_le_inv_iff₀.mpr ⟨by exact_mod_cast haa0,
        by exact_mod_cast haa1⟩)
    linarith
  have hDcoe : ((D : ℝ≥0) : ℝ) = 1 + Real.logb 2 ((aa : ℝ))⁻¹ :=
    Real.coe_toNNReal _ hlogb_nn
  have hD1 : 1 ≤ D := by
    rw [← NNReal.coe_le_coe, hDcoe]
    have : 0 ≤ Real.logb 2 ((aa : ℝ))⁻¹ :=
      Real.logb_nonneg (by norm_num) (one_le_inv_iff₀.mpr ⟨by exact_mod_cast haa0,
        by exact_mod_cast haa1⟩)
    push_cast
    linarith
  have hD0 : D ≠ 0 := by
    intro h; rw [h] at hD1; simp at hD1
  -- the dyadic loss is polynomial in the floor: `D * λ ≤ 8`
  have hDlu : D * lu ≤ 8 := by
    rw [← NNReal.coe_le_coe]
    push_cast
    rw [hDcoe]
    have hax : (aa : ℝ) = (lu : ℝ) / 2 := by rw [haa]; push_cast; ring
    have hle : 1 + Real.logb 2 ((aa : ℝ))⁻¹ ≤ 4 / (aa : ℝ) :=
      one_add_logb_le_four_div (by exact_mod_cast haa0) (by exact_mod_cast haa1)
    have hpos : (0 : ℝ) < (aa : ℝ) := by exact_mod_cast haa0
    have hlu' : (lu : ℝ) = 2 * (aa : ℝ) := by rw [hax]; ring
    rw [hlu']
    have hstep : (1 + Real.logb 2 ((aa : ℝ))⁻¹) * (2 * (aa : ℝ))
        ≤ (4 / (aa : ℝ)) * (2 * (aa : ℝ)) := by
      have h2 : (0 : ℝ) ≤ 2 * (aa : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_right hle h2
    have hcalc : (4 / (aa : ℝ)) * (2 * (aa : ℝ)) = 8 := by field_simp; norm_num
    linarith [hstep, hcalc.le, hcalc.ge]
  have hDlam : lam * D ≤ 8 := by
    calc lam * D ≤ lu * D := by gcongr
      _ = D * lu := by ring
      _ ≤ 8 := hDlu
  -- compose the two refinements
  have href : ShadedBody.IsCRefinement u₂ Y u Y ((1 / 2 : ℝ≥0) * D⁻¹) :=
    ShadedBody.IsCRefinement.trans href2 href0
  set c : ℝ≥0 := (1 / 2 : ℝ≥0) * D⁻¹ with hc
  have hc0 : c ≠ 0 := mul_ne_zero (by norm_num) (inv_ne_zero hD0)
  have hlam16 : lam ≤ 16 * c := by
    have h1 : (16 : ℝ≥0) * c = 8 * D⁻¹ := by rw [hc, ← mul_assoc]; norm_num
    rw [h1, show (8 : ℝ≥0) * D⁻¹ = 8 / D by rw [div_eq_mul_inv],
      le_div_iff₀ (pos_iff_ne_zero.mpr hD0)]
    exact hDlam
  have hcinv : c⁻¹ ≤ 16 / lam := by
    rw [le_div_iff₀ hlam0]
    calc c⁻¹ * lam ≤ c⁻¹ * (16 * c) := by gcongr
      _ = (c⁻¹ * c) * 16 := by ring
      _ = 16 := by rw [inv_mul_cancel₀ hc0, one_mul]
  have hsq : lam ^ 2 / 16 ≤ c * lam := by
    rw [div_le_iff₀ (by norm_num : (0:ℝ≥0) < 16)]
    calc lam ^ 2 = lam * lam := by ring
      _ ≤ (16 * c) * lam := by gcongr
      _ = c * lam * 16 := by ring
  -- `u₂` is nonempty because it retains a positive share of a positive shading mass
  have hu₂ne : u₂.Nonempty := by
    rcases Finset.eq_empty_or_nonempty u₂ with h | h
    · exfalso
      have h2 := href.2
      rw [h] at h2
      simp only [Finset.sum_empty, nonpos_iff_eq_zero, mul_eq_zero] at h2
      rcases h2 with h1 | h2
      · exact hc0 (by exact_mod_cast h1)
      · exact hmass_pos.ne' h2
    · exact h
  refine ⟨u₂, hu₂u₀.trans hu₀u, hu₂ne, (lam2 : ℝ≥0∞), by exact_mod_cast hlam20, ?_, ?_, ?_, ?_⟩
  · intro k hk
    obtain ⟨hlow, hhigh⟩ := hband k hk
    constructor
    · calc ((2 : ℝ≥0) : ℝ≥0∞)⁻¹ * (lam2 : ℝ≥0∞) * volume (U k).carrier
          ≤ 1 * (lam2 : ℝ≥0∞) * volume (U k).carrier := by
            gcongr
            rw [ENNReal.inv_le_one]
            exact_mod_cast (by norm_num : (1 : ℝ≥0) ≤ 2)
        _ = (lam2 : ℝ≥0∞) * volume (Y k).carrier := by rw [one_mul]
        _ ≤ volume (Y k).shade := hlow
    · calc volume (U k).shade = volume (Y k).shade := rfl
        _ ≤ 2 * (lam2 : ℝ≥0∞) * volume (Y k).carrier := hhigh
        _ = ((2 : ℝ≥0) : ℝ≥0∞) * (lam2 : ℝ≥0∞) * volume (U k).carrier := by
            push_cast; rfl
  · refine le_trans (ShadedBody.multiplicity_le_of_isCRefinement u Y hc0 href) ?_
    gcongr
    calc ((c : ℝ≥0) : ℝ≥0∞)⁻¹ = ((c⁻¹ : ℝ≥0) : ℝ≥0∞) := (ENNReal.coe_inv hc0).symm
      _ ≤ ((16 / lam : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast hcinv
      _ = 16 / (lam : ℝ≥0∞) := by
          rw [ENNReal.coe_div hlam0.ne']; norm_num
  · have hstep := href.coe_mul_fullness_le
    calc ((lam : ℝ≥0∞)) ^ 2 / 16 = (((lam ^ 2 / 16 : ℝ≥0)) : ℝ≥0∞) := by
          rw [ENNReal.coe_div (by norm_num)]; norm_num
      _ ≤ (((c * lam : ℝ≥0)) : ℝ≥0∞) := by exact_mod_cast hsq
      _ = (c : ℝ≥0∞) * (lam : ℝ≥0∞) := by push_cast; ring
      _ ≤ (c : ℝ≥0∞) * (lu : ℝ≥0∞) := by gcongr
      _ ≤ (ShadedBody.fullness u₂ Y : ℝ≥0∞) := hstep
  · -- cardinality retention, read off the shading mass
    have hupper : ∑ i ∈ u₂, volume (Y i).shade ≤ (u₂.card : ℝ≥0∞) * v := by
      calc ∑ i ∈ u₂, volume (Y i).shade
          ≤ ∑ i ∈ u₂, volume (Y i).carrier :=
            Finset.sum_le_sum fun i _ => measure_mono (Y i).shade_subset
        _ = ∑ i ∈ u₂, v := Finset.sum_congr rfl fun i hi => hvol i (hu₂u₀.trans hu₀u hi)
        _ = (u₂.card : ℝ≥0∞) * v := by rw [Finset.sum_const, nsmul_eq_mul]
    have hlower : ((lam : ℝ≥0∞)) ^ 2 / 16 * (u.card : ℝ≥0∞) * v
        ≤ ∑ i ∈ u₂, volume (Y i).shade := by
      refine le_trans ?_ href.2
      rw [hsumshade]
      have hcoe : ((lam : ℝ≥0∞)) ^ 2 / 16 ≤ (c : ℝ≥0∞) * (lam : ℝ≥0∞) := by
        calc ((lam : ℝ≥0∞)) ^ 2 / 16 = (((lam ^ 2 / 16 : ℝ≥0)) : ℝ≥0∞) := by
              rw [ENNReal.coe_div (by norm_num)]; norm_num
          _ ≤ (((c * lam : ℝ≥0)) : ℝ≥0∞) := by exact_mod_cast hsq
          _ = (c : ℝ≥0∞) * (lam : ℝ≥0∞) := by push_cast; ring
      calc ((lam : ℝ≥0∞)) ^ 2 / 16 * (u.card : ℝ≥0∞) * v
          ≤ ((c : ℝ≥0∞) * (lam : ℝ≥0∞)) * (u.card : ℝ≥0∞) * v := by gcongr
        _ ≤ ((c : ℝ≥0∞) * (lu : ℝ≥0∞)) * (u.card : ℝ≥0∞) * v := by
            gcongr
        _ = (c : ℝ≥0∞) * ((lu : ℝ≥0∞) * ((u.card : ℝ≥0∞) * v)) := by ring
    have := le_trans hlower hupper
    rwa [ENNReal.mul_le_mul_iff_left hv_pos.ne' hv_top] at this

/-! ### The loss ledger of the internal normalization -/

/-! ### The endgame algebra with a free loss constant -/

/-! ### The middle factor at average fullness -/

end Internal

end ml1Boot

end Kakeya

end

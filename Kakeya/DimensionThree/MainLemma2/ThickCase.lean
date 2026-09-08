/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.PartialEstimates
public import Kakeya.Uniform
public import Kakeya.Factorization
public import Kakeya.DimensionThree.MainLemma2.VeryNotSticky
public import Kakeya.DimensionThree.MainLemma2.Goals
public import Kakeya.DimensionThree.MainLemma2.ThickPlankInterface
public import Kakeya.DimensionThree.MainLemma2.DenseInBodyNamed
public import Kakeya.DimensionThree.MainLemma2.ThinConfig
public import Kakeya.Thickness.OuterPrism

/-!
In this file, we prove the thick case of Main Lemma 2.
-/

@[expose] public section

open scoped NNReal ENNReal

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric
open scoped NNReal ENNReal

universe u

/-- **Volume of a block segment**.

For a ball `B ∈ 𝔅` and a segment `T_B ∈ 𝕋_B`,

`r₁ δ² / (6 C₀³) ≤ |T_B| ≤ 8 C₀³ r₁ δ²`,

written with the division cleared as a multiplication by `(6 C₀³)⁻¹` so that no positivity or
finiteness side condition is needed in `[0, ∞]`.

In particular `0 < |T_B| < ∞`: positivity follows from the lower bound together with
`cfg.hδ` and `0 < cfg.r₁`, and finiteness is free from compactness of the carrier
(`ConvexSpaceBody.isCompact.measure_lt_top`), so neither is stated separately.

The content is the thickness comparison `Kakeya.VeryNotSticky.BallData.segs_thickness` of (C3),
which pins `∏ₖ τₖ(T_B)` between `C₀⁻³ r₁ δ²` and `C₀³ r₁ δ²`, fed through the two-sided
volume/thickness comparison of the convex-body chapter — `volume_le_prod_ethickness` and
`Convex.ethickness_prod_le_volume` via `Metric.ethickness_thickness'` — whose constants are
`2³ = 8` and `c = 1/6 = (3!)⁻¹` in dimension three. -/
theorem thickSegVol (cfg : VeryNotSticky.{u}) (bd : BallData cfg) {B : bd.bι}
    (hB : B ∈ bd.bs) {p : bd.σ} (hp : p ∈ bd.segs B) :
    (((6 * bd.C₀ ^ 3 : ℝ≥0) : ℝ≥0∞))⁻¹ * ((cfg.r₁ * cfg.δ ^ 2 : ℝ≥0) : ℝ≥0∞) ≤
        volume (bd.Y p).carrier ∧
      volume (bd.Y p).carrier ≤ ((8 * bd.C₀ ^ 3 * cfg.r₁ * cfg.δ ^ 2 : ℝ≥0) : ℝ≥0∞) := by
  let s := (bd.Y p).carrier
  have hconv : Convex ℝ s := (bd.Y p).convex
  have hbdd : Bornology.IsBounded s := (bd.Y p).isCompact.isBounded
  have hfinrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hthick : HasThicknesses s bd.C₀ ![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)] :=
    bd.segs_thickness B hB p hp
  let t : Fin 3 → ℝ := ![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)]
  have ht_nonneg : ∀ k : Fin 3, 0 ≤ t k := by
    intro k; fin_cases k <;> simp [t, show 0 ≤ (cfg.r₁ : ℝ) from by positivity,
      show 0 ≤ (cfg.δ : ℝ) from by positivity]
  have hC0pos : 0 < (bd.C₀ : ℝ) := by
    have hC0_one : (1 : ℝ) ≤ (bd.C₀ : ℝ) := by exact_mod_cast bd.hC₀
    linarith
  have hδpos : 0 < (cfg.δ : ℝ) := by exact_mod_cast cfg.hδ
  have hr₁pos : 0 < (cfg.r₁ : ℝ) := by
    have := Real.rpow_pos_of_pos (by exact_mod_cast cfg.hδ) cfg.exscal
    simpa [r₁] using this
  -- The triple of index-specific bounds from HasThicknesses
  have hthick_vals : ∀ k : Fin 3,
      (bd.C₀ : ℝ)⁻¹ * t k ≤ Metric.thickness ℝ s (k : ℕ) ∧
      Metric.thickness ℝ s (k : ℕ) ≤ (bd.C₀ : ℝ) * t k :=
    hthick
  -- We will need the three specific indices
  let hi0 : Fin 3 := 0
  let hi1 : Fin 3 := 1
  let hi2 : Fin 3 := 2
  rcases hthick_vals hi0 with ⟨h0_low, h0_up⟩
  rcases hthick_vals hi1 with ⟨h1_low, h1_up⟩
  rcases hthick_vals hi2 with ⟨h2_low, h2_up⟩
  have h0val : (hi0 : ℕ) = 0 := rfl
  have h1val : (hi1 : ℕ) = 1 := rfl
  have h2val : (hi2 : ℕ) = 2 := rfl
  have h0t : t hi0 = (cfg.r₁ : ℝ) := by
    simp [t, hi0]
  have h1t : t hi1 = (cfg.δ : ℝ) := by
    simp [t, hi1]
  have h2t : t hi2 = (cfg.δ : ℝ) := by
    simp [t, hi2]
  -- *** UPPER BOUND ***
  have h_upper : volume s ≤ ((8 * bd.C₀ ^ 3 * cfg.r₁ * cfg.δ ^ 2 : ℝ≥0) : ℝ≥0∞) := by
    have hvol := volume_le_prod_ethickness s
    rw [hfinrank] at hvol
    -- hvol: volume s ≤ 2 ^ (3 : ℕ) * (∏ i ∈ range 3, ethickness ℝ s i)
    -- Replace 2^3 by 8
    have h8 : (2 : ℝ≥0∞) ^ (3 : ℕ) = (8 : ℝ≥0∞) := by norm_num
    rw [h8] at hvol
    -- Expand the product
    have hprod : ∏ i ∈ Finset.range 3, Metric.ethickness ℝ s i =
        Metric.ethickness ℝ s 0 * Metric.ethickness ℝ s 1 * Metric.ethickness ℝ s 2 := by
      simp [Finset.prod_range_succ]
    rw [hprod] at hvol
    -- Convert each ethickness to ENNReal.ofReal (thickness)
    have he0 : Metric.ethickness ℝ s 0 = ENNReal.ofReal (Metric.thickness ℝ s 0) :=
      Metric.ethickness_thickness' hbdd 0
    have he1 : Metric.ethickness ℝ s 1 = ENNReal.ofReal (Metric.thickness ℝ s 1) :=
      Metric.ethickness_thickness' hbdd 1
    have he2 : Metric.ethickness ℝ s 2 = ENNReal.ofReal (Metric.thickness ℝ s 2) :=
      Metric.ethickness_thickness' hbdd 2
    rw [he0, he1, he2] at hvol
    -- Now bound each factor
    have hup0 : ENNReal.ofReal (Metric.thickness ℝ s 0) ≤
        ENNReal.ofReal ((bd.C₀ : ℝ) * t hi0) := by
      have htemp : Metric.thickness ℝ s 0 ≤ (bd.C₀ : ℝ) * t hi0 := by
        simpa [h0val, h0t] using h0_up
      exact ENNReal.ofReal_le_ofReal htemp
    have hup1 : ENNReal.ofReal (Metric.thickness ℝ s 1) ≤
        ENNReal.ofReal ((bd.C₀ : ℝ) * t hi1) := by
      have htemp : Metric.thickness ℝ s 1 ≤ (bd.C₀ : ℝ) * t hi1 := by
        simpa [h1val, h1t] using h1_up
      exact ENNReal.ofReal_le_ofReal htemp
    have hup2 : ENNReal.ofReal (Metric.thickness ℝ s 2) ≤
        ENNReal.ofReal ((bd.C₀ : ℝ) * t hi2) := by
      have htemp : Metric.thickness ℝ s 2 ≤ (bd.C₀ : ℝ) * t hi2 := by
        simpa [h2val, h2t] using h2_up
      exact ENNReal.ofReal_le_ofReal htemp
    -- Combine the factor bounds
    have hprod_bound :
        ENNReal.ofReal (Metric.thickness ℝ s 0) *
            ENNReal.ofReal (Metric.thickness ℝ s 1) *
          ENNReal.ofReal (Metric.thickness ℝ s 2) ≤
        ((bd.C₀ ^ 3 * cfg.r₁ * cfg.δ ^ 2 : ℝ≥0) : ℝ≥0∞) := by
      calc
        (ENNReal.ofReal (Metric.thickness ℝ s 0) * ENNReal.ofReal (Metric.thickness ℝ s 1) *
            ENNReal.ofReal (Metric.thickness ℝ s 2))
            ≤ (ENNReal.ofReal ((bd.C₀ : ℝ) * t hi0) * ENNReal.ofReal ((bd.C₀ : ℝ) * t hi1) *
                ENNReal.ofReal ((bd.C₀ : ℝ) * t hi2)) := by
              gcongr
        _ = ((bd.C₀ : ℝ≥0∞) * ((cfg.r₁ : ℝ≥0) : ℝ≥0∞)) *
            ((bd.C₀ : ℝ≥0∞) * ((cfg.δ : ℝ≥0) : ℝ≥0∞)) *
            ((bd.C₀ : ℝ≥0∞) * ((cfg.δ : ℝ≥0) : ℝ≥0∞)) := by
          have hC0_nonneg : 0 ≤ (bd.C₀ : ℝ) := by positivity
          simp [h0t, h1t, h2t, ENNReal.ofReal_mul hC0_nonneg, ENNReal.ofReal_coe_nnreal]
        _ = ((bd.C₀ : ℝ≥0∞) ^ 3 * ((cfg.r₁ : ℝ≥0) : ℝ≥0∞) *
            (((cfg.δ : ℝ≥0) : ℝ≥0∞) ^ 2)) := by
          ring
        _ = ((bd.C₀ ^ 3 * cfg.r₁ * cfg.δ ^ 2 : ℝ≥0) : ℝ≥0∞) := by
          simp [ENNReal.coe_mul, ENNReal.coe_pow]
    calc
      volume s ≤ (8 : ℝ≥0∞) * (ENNReal.ofReal (Metric.thickness ℝ s 0) *
          ENNReal.ofReal (Metric.thickness ℝ s 1) * ENNReal.ofReal (Metric.thickness ℝ s 2)) := hvol
      _ ≤ (8 : ℝ≥0∞) * ((bd.C₀ ^ 3 * cfg.r₁ * cfg.δ ^ 2 : ℝ≥0) : ℝ≥0∞) := by
        gcongr
      _ = ((8 * bd.C₀ ^ 3 * cfg.r₁ * cfg.δ ^ 2 : ℝ≥0) : ℝ≥0∞) := by
        simp [ENNReal.coe_mul, mul_assoc]
  -- *** LOWER BOUND ***
  have h_lower : (((6 * bd.C₀ ^ 3 : ℝ≥0) : ℝ≥0∞))⁻¹ *
      ((cfg.r₁ * cfg.δ ^ 2 : ℝ≥0) : ℝ≥0∞) ≤ volume s := by
    have hvol_lower := hconv.ethickness_prod_le_volume
    rw [hfinrank] at hvol_lower
    -- hvol_lower: the convex-hull constant times the product of ethicknesses is at most volume.
    have hc3_val : (Metric.lt_volume_convexHull.c 3 : ℝ≥0∞) = ((6 : ℝ≥0)⁻¹ : ℝ≥0∞) := by
      simp [Metric.lt_volume_convexHull.c, show (Nat.factorial 3 : ℕ) = 6 by norm_num]
    rw [hc3_val] at hvol_lower
    -- Expand the product
    have hprod : ∏ i ∈ Finset.range 3, Metric.ethickness ℝ s i =
        Metric.ethickness ℝ s 0 * Metric.ethickness ℝ s 1 * Metric.ethickness ℝ s 2 := by
      simp [Finset.prod_range_succ]
    rw [hprod] at hvol_lower
    -- Convert each ethickness to ENNReal.ofReal (thickness)
    have he0 : Metric.ethickness ℝ s 0 = ENNReal.ofReal (Metric.thickness ℝ s 0) :=
      Metric.ethickness_thickness' hbdd 0
    have he1 : Metric.ethickness ℝ s 1 = ENNReal.ofReal (Metric.thickness ℝ s 1) :=
      Metric.ethickness_thickness' hbdd 1
    have he2 : Metric.ethickness ℝ s 2 = ENNReal.ofReal (Metric.thickness ℝ s 2) :=
      Metric.ethickness_thickness' hbdd 2
    rw [he0, he1, he2] at hvol_lower
    -- Now bound each factor from below
    have hlow0 : ENNReal.ofReal (((bd.C₀ : ℝ)⁻¹ * t hi0)) ≤
        ENNReal.ofReal (Metric.thickness ℝ s 0) := by
      have htemp : ((bd.C₀ : ℝ)⁻¹ * t hi0) ≤ Metric.thickness ℝ s 0 := by
        simpa [h0val, h0t] using h0_low
      exact ENNReal.ofReal_le_ofReal htemp
    have hlow1 : ENNReal.ofReal (((bd.C₀ : ℝ)⁻¹ * t hi1)) ≤
        ENNReal.ofReal (Metric.thickness ℝ s 1) := by
      have htemp : ((bd.C₀ : ℝ)⁻¹ * t hi1) ≤ Metric.thickness ℝ s 1 := by
        simpa [h1val, h1t] using h1_low
      exact ENNReal.ofReal_le_ofReal htemp
    have hlow2 : ENNReal.ofReal (((bd.C₀ : ℝ)⁻¹ * t hi2)) ≤
        ENNReal.ofReal (Metric.thickness ℝ s 2) := by
      have htemp : ((bd.C₀ : ℝ)⁻¹ * t hi2) ≤ Metric.thickness ℝ s 2 := by
        simpa [h2val, h2t] using h2_low
      exact ENNReal.ofReal_le_ofReal htemp
    -- Compute the explicit product of lower bounds
    have hC0inv : ENNReal.ofReal ((bd.C₀ : ℝ)⁻¹) = (bd.C₀ : ℝ≥0∞)⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos hC0pos, ENNReal.ofReal_coe_nnreal]
    have hprod_low_val : ENNReal.ofReal (((bd.C₀ : ℝ)⁻¹ * t hi0)) *
        ENNReal.ofReal (((bd.C₀ : ℝ)⁻¹ * t hi1)) *
        ENNReal.ofReal (((bd.C₀ : ℝ)⁻¹ * t hi2)) =
        ((bd.C₀ : ℝ≥0∞)⁻¹ ^ 3) * ((cfg.r₁ : ℝ≥0) : ℝ≥0∞) *
          (((cfg.δ : ℝ≥0) : ℝ≥0∞) ^ 2) := by
      calc
        ENNReal.ofReal (((bd.C₀ : ℝ)⁻¹ * t hi0)) * ENNReal.ofReal (((bd.C₀ : ℝ)⁻¹ * t hi1)) *
            ENNReal.ofReal (((bd.C₀ : ℝ)⁻¹ * t hi2))
            = (ENNReal.ofReal ((bd.C₀ : ℝ)⁻¹) * ENNReal.ofReal (t hi0)) *
              (ENNReal.ofReal ((bd.C₀ : ℝ)⁻¹) * ENNReal.ofReal (t hi1)) *
              (ENNReal.ofReal ((bd.C₀ : ℝ)⁻¹) * ENNReal.ofReal (t hi2)) := by
              simp [ENNReal.ofReal_mul (by positivity : 0 ≤ (bd.C₀ : ℝ)⁻¹)]
        _ = ((bd.C₀ : ℝ≥0∞)⁻¹ * ((cfg.r₁ : ℝ≥0) : ℝ≥0∞)) *
            ((bd.C₀ : ℝ≥0∞)⁻¹ * ((cfg.δ : ℝ≥0) : ℝ≥0∞)) *
            ((bd.C₀ : ℝ≥0∞)⁻¹ * ((cfg.δ : ℝ≥0) : ℝ≥0∞)) := by
          simp [h0t, h1t, h2t, hC0inv, ENNReal.ofReal_coe_nnreal]
        _ = ((bd.C₀ : ℝ≥0∞)⁻¹ ^ 3) * ((cfg.r₁ : ℝ≥0) : ℝ≥0∞) *
            (((cfg.δ : ℝ≥0) : ℝ≥0∞) ^ 2) := by
          ring
    -- Lower product ≤ actual product (termwise)
    have hprod_lower_bound : ENNReal.ofReal (((bd.C₀ : ℝ)⁻¹ * t hi0)) *
        ENNReal.ofReal (((bd.C₀ : ℝ)⁻¹ * t hi1)) *
        ENNReal.ofReal (((bd.C₀ : ℝ)⁻¹ * t hi2)) ≤
        (ENNReal.ofReal (Metric.thickness ℝ s 0) * ENNReal.ofReal (Metric.thickness ℝ s 1) *
          ENNReal.ofReal (Metric.thickness ℝ s 2)) := by
      gcongr
    -- Combine with hvol_lower via the constant 6⁻¹
    -- Need to relate the goal to hvol_lower
    -- Goal: (6*C₀³ : ENNReal)⁻¹ * (r₁*δ² : ENNReal)
    -- hvol_lower: (6⁻¹ : ENNReal) * (ethickness₀ * ethickness₁ * ethickness₂) ≤ volume s
    -- We show goal ≤ (6⁻¹) * (...)
    have h_factor : ((6 : ℝ≥0)⁻¹ : ℝ≥0∞) *
        (((bd.C₀ : ℝ≥0∞)⁻¹ ^ 3) * ((cfg.r₁ : ℝ≥0) : ℝ≥0∞) *
          (((cfg.δ : ℝ≥0) : ℝ≥0∞) ^ 2)) =
      (((6 * bd.C₀ ^ 3 : ℝ≥0) : ℝ≥0∞))⁻¹ *
        ((cfg.r₁ * cfg.δ ^ 2 : ℝ≥0) : ℝ≥0∞) := by
      calc
        ((6 : ℝ≥0)⁻¹ : ℝ≥0∞) * (((bd.C₀ : ℝ≥0∞)⁻¹ ^ 3) * ((cfg.r₁ : ℝ≥0) : ℝ≥0∞) *
            (((cfg.δ : ℝ≥0) : ℝ≥0∞) ^ 2))
            = ((6 : ℝ≥0)⁻¹ : ℝ≥0∞) * ((bd.C₀ : ℝ≥0∞)⁻¹ ^ 3) *
              ((cfg.r₁ : ℝ≥0) : ℝ≥0∞) *
              (((cfg.δ : ℝ≥0) : ℝ≥0∞) ^ 2) := by
          simp [mul_assoc]
        _ = ((6 : ℝ≥0)⁻¹ : ℝ≥0∞) * ((bd.C₀ : ℝ≥0∞)⁻¹ ^ 3) *
            ((cfg.r₁ * cfg.δ ^ 2 : ℝ≥0) : ℝ≥0∞) := by
          simp [ENNReal.coe_mul, ENNReal.coe_pow, mul_assoc]
        _ = (((6 : ℝ≥0)⁻¹ : ℝ≥0∞) * ((bd.C₀ : ℝ≥0∞)⁻¹ ^ 3)) *
            ((cfg.r₁ * cfg.δ ^ 2 : ℝ≥0) : ℝ≥0∞) := by
          simp [mul_assoc]
        _ = (((6 : ℝ≥0) : ℝ≥0∞)⁻¹ * (((bd.C₀ : ℝ≥0) : ℝ≥0∞)⁻¹ ^ 3)) *
            ((cfg.r₁ * cfg.δ ^ 2 : ℝ≥0) : ℝ≥0∞) := rfl
        _ = (((6 : ℝ≥0∞) * ((bd.C₀ : ℝ≥0) : ℝ≥0∞) ^ 3)⁻¹) *
            ((cfg.r₁ * cfg.δ ^ 2 : ℝ≥0) : ℝ≥0∞) := by
          have h_inv : ((6 : ℝ≥0∞)⁻¹) * (((bd.C₀ : ℝ≥0) : ℝ≥0∞)⁻¹ ^ 3) =
              ((6 : ℝ≥0∞) * ((bd.C₀ : ℝ≥0) : ℝ≥0∞) ^ 3)⁻¹ := by
            calc
              ((6 : ℝ≥0∞)⁻¹) * (((bd.C₀ : ℝ≥0) : ℝ≥0∞)⁻¹ ^ 3)
                  = ((6 : ℝ≥0∞)⁻¹) * (((bd.C₀ : ℝ≥0) : ℝ≥0∞) ^ 3)⁻¹ := by
                rw [← ENNReal.inv_pow]
              _ = ((6 : ℝ≥0∞) * ((bd.C₀ : ℝ≥0) : ℝ≥0∞) ^ 3)⁻¹ := by simp [ENNReal.mul_inv]
          simp [h_inv]
        _ = (((6 * bd.C₀ ^ 3 : ℝ≥0) : ℝ≥0∞))⁻¹ *
            ((cfg.r₁ * cfg.δ ^ 2 : ℝ≥0) : ℝ≥0∞) := by
          simp [ENNReal.coe_mul, ENNReal.coe_pow]
    calc
      (((6 * bd.C₀ ^ 3 : ℝ≥0) : ℝ≥0∞))⁻¹ *
          ((cfg.r₁ * cfg.δ ^ 2 : ℝ≥0) : ℝ≥0∞)
          = ((6 : ℝ≥0)⁻¹ : ℝ≥0∞) *
            (((bd.C₀ : ℝ≥0∞)⁻¹ ^ 3) * ((cfg.r₁ : ℝ≥0) : ℝ≥0∞) *
              (((cfg.δ : ℝ≥0) : ℝ≥0∞) ^ 2)) := by
        -- this is the identity from h_factor
        symm; exact h_factor
      _ = ((6 : ℝ≥0)⁻¹ : ℝ≥0∞) * (ENNReal.ofReal (((bd.C₀ : ℝ)⁻¹ * t hi0)) *
          ENNReal.ofReal (((bd.C₀ : ℝ)⁻¹ * t hi1)) *
          ENNReal.ofReal (((bd.C₀ : ℝ)⁻¹ * t hi2))) := by
        rw [hprod_low_val]
      _ ≤ ((6 : ℝ≥0)⁻¹ : ℝ≥0∞) * (ENNReal.ofReal (Metric.thickness ℝ s 0) *
          ENNReal.ofReal (Metric.thickness ℝ s 1) *
          ENNReal.ofReal (Metric.thickness ℝ s 2)) := by
        gcongr
      _ ≤ volume s := hvol_lower
  exact ⟨h_lower, h_upper⟩

/-- **Volume of a factoring body**.

For a ball `B ∈ 𝔅` and a body `W ∈ 𝕎_B`,

`r₁ b a / (6 C₀³) ≤ |W| ≤ 8 C₀³ r₁ b a`,

in the same division-cleared shape as `Kakeya.VeryNotSticky.thickSegVol`, of which this is the
verbatim analogue with the thickness triple `(r₁, δ, δ)` replaced by `(r₁, b, a)`: the input is
`Kakeya.VeryNotSticky.BallData.bodies_thickness` of (C4) instead of
`Kakeya.VeryNotSticky.BallData.segs_thickness`, and nothing else changes.

In particular `0 < |W| < ∞`, positivity now using `0 < cfg.a` and `0 < cfg.b`, which come from
`cfg.hδ` and `cfg.hdims`. -/
theorem thickBodyVol (cfg : VeryNotSticky.{u}) (bd : BallData cfg) {B : bd.bι}
    (hB : B ∈ bd.bs) {j : bd.ω} (hj : j ∈ bd.bodies B) :
    (((6 * bd.C₀ ^ 3 : ℝ≥0) : ℝ≥0∞))⁻¹ * ((cfg.r₁ * cfg.b * cfg.a : ℝ≥0) : ℝ≥0∞) ≤
        volume (bd.Wb j).carrier ∧
      volume (bd.Wb j).carrier ≤
        ((8 * bd.C₀ ^ 3 * cfg.r₁ * cfg.b * cfg.a : ℝ≥0) : ℝ≥0∞) := by
  let s := (bd.Wb j).carrier
  have hconv : Convex ℝ s := (bd.Wb j).convex
  have hbdd : Bornology.IsBounded s := (bd.Wb j).isCompact.isBounded
  have hfinrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hthick : HasThicknesses s bd.C₀ ![(cfg.r₁ : ℝ), (cfg.b : ℝ), (cfg.a : ℝ)] :=
    bd.bodies_thickness B hB j hj
  let t : Fin 3 → ℝ := ![(cfg.r₁ : ℝ), (cfg.b : ℝ), (cfg.a : ℝ)]
  have ht_nonneg : ∀ k : Fin 3, 0 ≤ t k := by
    intro k; fin_cases k <;> simp [t, show 0 ≤ (cfg.r₁ : ℝ) from by positivity,
      show 0 ≤ (cfg.b : ℝ) from by positivity,
      show 0 ≤ (cfg.a : ℝ) from by positivity]
  have hC0pos : 0 < (bd.C₀ : ℝ) := by
    have hC0_one : (1 : ℝ) ≤ (bd.C₀ : ℝ) := by exact_mod_cast bd.hC₀
    linarith
  have hδpos : 0 < (cfg.δ : ℝ) := by exact_mod_cast cfg.hδ
  have hapos : 0 < (cfg.a : ℝ) := by
    have hδa : (cfg.δ : ℝ) ≤ (cfg.a : ℝ) := by exact_mod_cast cfg.hdims.1
    linarith
  have hbpos : 0 < (cfg.b : ℝ) := by
    have hab : (cfg.a : ℝ) ≤ (cfg.b : ℝ) := by exact_mod_cast cfg.hdims.2.1
    linarith
  have hr₁pos : 0 < (cfg.r₁ : ℝ) := by
    have := Real.rpow_pos_of_pos (by exact_mod_cast cfg.hδ) cfg.exscal
    simpa [r₁] using this
  -- The triple of index-specific bounds from HasThicknesses
  have hthick_vals : ∀ k : Fin 3,
      (bd.C₀ : ℝ)⁻¹ * t k ≤ Metric.thickness ℝ s (k : ℕ) ∧
      Metric.thickness ℝ s (k : ℕ) ≤ (bd.C₀ : ℝ) * t k :=
    hthick
  -- We will need the three specific indices
  let hi0 : Fin 3 := 0
  let hi1 : Fin 3 := 1
  let hi2 : Fin 3 := 2
  rcases hthick_vals hi0 with ⟨h0_low, h0_up⟩
  rcases hthick_vals hi1 with ⟨h1_low, h1_up⟩
  rcases hthick_vals hi2 with ⟨h2_low, h2_up⟩
  have h0val : (hi0 : ℕ) = 0 := rfl
  have h1val : (hi1 : ℕ) = 1 := rfl
  have h2val : (hi2 : ℕ) = 2 := rfl
  have h0t : t hi0 = (cfg.r₁ : ℝ) := by
    simp [t, hi0]
  have h1t : t hi1 = (cfg.b : ℝ) := by
    simp [t, hi1]
  have h2t : t hi2 = (cfg.a : ℝ) := by
    simp [t, hi2]
  -- *** UPPER BOUND ***
  have h_upper : volume s ≤ ((8 * bd.C₀ ^ 3 * cfg.r₁ * cfg.b * cfg.a : ℝ≥0) : ℝ≥0∞) := by
    have hvol := volume_le_prod_ethickness s
    rw [hfinrank] at hvol
    have h8 : (2 : ℝ≥0∞) ^ (3 : ℕ) = (8 : ℝ≥0∞) := by norm_num
    rw [h8] at hvol
    have hprod : ∏ i ∈ Finset.range 3, Metric.ethickness ℝ s i =
        Metric.ethickness ℝ s 0 * Metric.ethickness ℝ s 1 * Metric.ethickness ℝ s 2 := by
      simp [Finset.prod_range_succ]
    rw [hprod] at hvol
    have he0 : Metric.ethickness ℝ s 0 = ENNReal.ofReal (Metric.thickness ℝ s 0) :=
      Metric.ethickness_thickness' hbdd 0
    have he1 : Metric.ethickness ℝ s 1 = ENNReal.ofReal (Metric.thickness ℝ s 1) :=
      Metric.ethickness_thickness' hbdd 1
    have he2 : Metric.ethickness ℝ s 2 = ENNReal.ofReal (Metric.thickness ℝ s 2) :=
      Metric.ethickness_thickness' hbdd 2
    rw [he0, he1, he2] at hvol
    have hup0 : ENNReal.ofReal (Metric.thickness ℝ s 0) ≤
        ENNReal.ofReal ((bd.C₀ : ℝ) * t hi0) := by
      have htemp : Metric.thickness ℝ s 0 ≤ (bd.C₀ : ℝ) * t hi0 := by
        simpa [h0val, h0t] using h0_up
      exact ENNReal.ofReal_le_ofReal htemp
    have hup1 : ENNReal.ofReal (Metric.thickness ℝ s 1) ≤
        ENNReal.ofReal ((bd.C₀ : ℝ) * t hi1) := by
      have htemp : Metric.thickness ℝ s 1 ≤ (bd.C₀ : ℝ) * t hi1 := by
        simpa [h1val, h1t] using h1_up
      exact ENNReal.ofReal_le_ofReal htemp
    have hup2 : ENNReal.ofReal (Metric.thickness ℝ s 2) ≤
        ENNReal.ofReal ((bd.C₀ : ℝ) * t hi2) := by
      have htemp : Metric.thickness ℝ s 2 ≤ (bd.C₀ : ℝ) * t hi2 := by
        simpa [h2val, h2t] using h2_up
      exact ENNReal.ofReal_le_ofReal htemp
    have hprod_bound :
        (ENNReal.ofReal (Metric.thickness ℝ s 0) *
            ENNReal.ofReal (Metric.thickness ℝ s 1) *
          ENNReal.ofReal (Metric.thickness ℝ s 2)) ≤
        ((bd.C₀ ^ 3 * cfg.r₁ * cfg.b * cfg.a : ℝ≥0) : ℝ≥0∞) := by
      calc
        (ENNReal.ofReal (Metric.thickness ℝ s 0) * ENNReal.ofReal (Metric.thickness ℝ s 1) *
            ENNReal.ofReal (Metric.thickness ℝ s 2))
            ≤ (ENNReal.ofReal ((bd.C₀ : ℝ) * t hi0) * ENNReal.ofReal ((bd.C₀ : ℝ) * t hi1) *
                ENNReal.ofReal ((bd.C₀ : ℝ) * t hi2)) := by
              gcongr
        _ = ((bd.C₀ : ℝ≥0∞) * ((cfg.r₁ : ℝ≥0) : ℝ≥0∞)) *
            ((bd.C₀ : ℝ≥0∞) * ((cfg.b : ℝ≥0) : ℝ≥0∞)) *
            ((bd.C₀ : ℝ≥0∞) * ((cfg.a : ℝ≥0) : ℝ≥0∞)) := by
          calc
            ENNReal.ofReal ((bd.C₀ : ℝ) * t hi0) * ENNReal.ofReal ((bd.C₀ : ℝ) * t hi1) *
                ENNReal.ofReal ((bd.C₀ : ℝ) * t hi2)
                = (ENNReal.ofReal (bd.C₀ : ℝ) * ENNReal.ofReal (t hi0)) *
                  (ENNReal.ofReal (bd.C₀ : ℝ) * ENNReal.ofReal (t hi1)) *
                  (ENNReal.ofReal (bd.C₀ : ℝ) * ENNReal.ofReal (t hi2)) := by
              simp [ENNReal.ofReal_mul (by positivity : 0 ≤ (bd.C₀ : ℝ))]
            _ = (ENNReal.ofReal (bd.C₀ : ℝ) * ENNReal.ofReal (cfg.r₁ : ℝ)) *
                (ENNReal.ofReal (bd.C₀ : ℝ) * ENNReal.ofReal (cfg.b : ℝ)) *
                (ENNReal.ofReal (bd.C₀ : ℝ) * ENNReal.ofReal (cfg.a : ℝ)) := by
              simp [h0t, h1t, h2t]
            _ = ((bd.C₀ : ℝ≥0∞) * ((cfg.r₁ : ℝ≥0) : ℝ≥0∞)) *
                ((bd.C₀ : ℝ≥0∞) * ((cfg.b : ℝ≥0) : ℝ≥0∞)) *
                ((bd.C₀ : ℝ≥0∞) * ((cfg.a : ℝ≥0) : ℝ≥0∞)) := by
              simp [ENNReal.ofReal_coe_nnreal]
        _ = ((bd.C₀ : ℝ≥0∞) ^ 3 * ((cfg.r₁ : ℝ≥0) : ℝ≥0∞) *
            ((cfg.b : ℝ≥0) : ℝ≥0∞) * ((cfg.a : ℝ≥0) : ℝ≥0∞)) := by ring
        _ = ((bd.C₀ ^ 3 * cfg.r₁ * cfg.b * cfg.a : ℝ≥0) : ℝ≥0∞) := by
          simp [ENNReal.coe_mul, ENNReal.coe_pow, mul_assoc]
    calc
      volume s ≤ (8 : ℝ≥0∞) * (ENNReal.ofReal (Metric.thickness ℝ s 0) *
          ENNReal.ofReal (Metric.thickness ℝ s 1) * ENNReal.ofReal (Metric.thickness ℝ s 2)) := hvol
      _ ≤ (8 : ℝ≥0∞) * ((bd.C₀ ^ 3 * cfg.r₁ * cfg.b * cfg.a : ℝ≥0) : ℝ≥0∞) := by
        gcongr
      _ = ((8 * bd.C₀ ^ 3 * cfg.r₁ * cfg.b * cfg.a : ℝ≥0) : ℝ≥0∞) := by
        simp [ENNReal.coe_mul, mul_assoc]
  -- *** LOWER BOUND ***
  have h_lower :
      (((6 * bd.C₀ ^ 3 : ℝ≥0) : ℝ≥0∞))⁻¹ *
          ((cfg.r₁ * cfg.b * cfg.a : ℝ≥0) : ℝ≥0∞) ≤
        volume s := by
    have hvol_lower := hconv.ethickness_prod_le_volume
    rw [hfinrank] at hvol_lower
    have hc3_val : (Metric.lt_volume_convexHull.c 3 : ℝ≥0∞) = ((6 : ℝ≥0)⁻¹ : ℝ≥0∞) := by
      simp [Metric.lt_volume_convexHull.c]; norm_num
    rw [hc3_val] at hvol_lower
    have hprod : ∏ i ∈ Finset.range 3, Metric.ethickness ℝ s i =
        Metric.ethickness ℝ s 0 * Metric.ethickness ℝ s 1 * Metric.ethickness ℝ s 2 := by
      simp [Finset.prod_range_succ]
    rw [hprod] at hvol_lower
    have he0 : Metric.ethickness ℝ s 0 = ENNReal.ofReal (Metric.thickness ℝ s 0) :=
      Metric.ethickness_thickness' hbdd 0
    have he1 : Metric.ethickness ℝ s 1 = ENNReal.ofReal (Metric.thickness ℝ s 1) :=
      Metric.ethickness_thickness' hbdd 1
    have he2 : Metric.ethickness ℝ s 2 = ENNReal.ofReal (Metric.thickness ℝ s 2) :=
      Metric.ethickness_thickness' hbdd 2
    rw [he0, he1, he2] at hvol_lower
    have hlow0 : ENNReal.ofReal (((bd.C₀ : ℝ)⁻¹ * t hi0)) ≤
        ENNReal.ofReal (Metric.thickness ℝ s 0) := by
      have htemp : ((bd.C₀ : ℝ)⁻¹ * t hi0) ≤ Metric.thickness ℝ s 0 := by
        simpa [h0val, h0t] using h0_low
      exact ENNReal.ofReal_le_ofReal htemp
    have hlow1 : ENNReal.ofReal (((bd.C₀ : ℝ)⁻¹ * t hi1)) ≤
        ENNReal.ofReal (Metric.thickness ℝ s 1) := by
      have htemp : ((bd.C₀ : ℝ)⁻¹ * t hi1) ≤ Metric.thickness ℝ s 1 := by
        simpa [h1val, h1t] using h1_low
      exact ENNReal.ofReal_le_ofReal htemp
    have hlow2 : ENNReal.ofReal (((bd.C₀ : ℝ)⁻¹ * t hi2)) ≤
        ENNReal.ofReal (Metric.thickness ℝ s 2) := by
      have htemp : ((bd.C₀ : ℝ)⁻¹ * t hi2) ≤ Metric.thickness ℝ s 2 := by
        simpa [h2val, h2t] using h2_low
      exact ENNReal.ofReal_le_ofReal htemp
    have hprod_low_val : ENNReal.ofReal (((bd.C₀ : ℝ)⁻¹ * t hi0)) *
        ENNReal.ofReal (((bd.C₀ : ℝ)⁻¹ * t hi1)) *
        ENNReal.ofReal (((bd.C₀ : ℝ)⁻¹ * t hi2)) =
        ((bd.C₀ : ℝ≥0∞)⁻¹ ^ 3) * ((cfg.r₁ : ℝ≥0) : ℝ≥0∞) * ((cfg.b : ℝ≥0) : ℝ≥0∞) *
          ((cfg.a : ℝ≥0) : ℝ≥0∞) := by
      calc
        ENNReal.ofReal (((bd.C₀ : ℝ)⁻¹ * t hi0)) *
            ENNReal.ofReal (((bd.C₀ : ℝ)⁻¹ * t hi1)) *
            ENNReal.ofReal (((bd.C₀ : ℝ)⁻¹ * t hi2))
            = (ENNReal.ofReal ((bd.C₀ : ℝ)⁻¹) * ENNReal.ofReal (t hi0)) *
              (ENNReal.ofReal ((bd.C₀ : ℝ)⁻¹) * ENNReal.ofReal (t hi1)) *
              (ENNReal.ofReal ((bd.C₀ : ℝ)⁻¹) * ENNReal.ofReal (t hi2)) := by
          simp [ENNReal.ofReal_mul (by positivity : 0 ≤ (bd.C₀ : ℝ)⁻¹)]
        _ = ((ENNReal.ofReal (bd.C₀ : ℝ))⁻¹ * ENNReal.ofReal (t hi0)) *
            ((ENNReal.ofReal (bd.C₀ : ℝ))⁻¹ * ENNReal.ofReal (t hi1)) *
            ((ENNReal.ofReal (bd.C₀ : ℝ))⁻¹ * ENNReal.ofReal (t hi2)) := by
          simp [ENNReal.ofReal_inv_of_pos hC0pos]
        _ = ((bd.C₀ : ℝ≥0∞)⁻¹ * ENNReal.ofReal (t hi0)) *
            ((bd.C₀ : ℝ≥0∞)⁻¹ * ENNReal.ofReal (t hi1)) *
            ((bd.C₀ : ℝ≥0∞)⁻¹ * ENNReal.ofReal (t hi2)) := by
          simp [ENNReal.ofReal_coe_nnreal]
        _ = ((bd.C₀ : ℝ≥0∞)⁻¹ * ((cfg.r₁ : ℝ≥0) : ℝ≥0∞)) *
            ((bd.C₀ : ℝ≥0∞)⁻¹ * ((cfg.b : ℝ≥0) : ℝ≥0∞)) *
            ((bd.C₀ : ℝ≥0∞)⁻¹ * ((cfg.a : ℝ≥0) : ℝ≥0∞)) := by
          simp [h0t, h1t, h2t, ENNReal.ofReal_coe_nnreal]
        _ = ((bd.C₀ : ℝ≥0∞)⁻¹ ^ 3) * ((cfg.r₁ : ℝ≥0) : ℝ≥0∞) *
            ((cfg.b : ℝ≥0) : ℝ≥0∞) * ((cfg.a : ℝ≥0) : ℝ≥0∞) := by
          simp [mul_assoc, mul_comm, mul_left_comm, pow_succ]
    have hprod_lower_bound : ENNReal.ofReal (((bd.C₀ : ℝ)⁻¹ * t hi0)) *
        ENNReal.ofReal (((bd.C₀ : ℝ)⁻¹ * t hi1)) *
        ENNReal.ofReal (((bd.C₀ : ℝ)⁻¹ * t hi2)) ≤
        (ENNReal.ofReal (Metric.thickness ℝ s 0) * ENNReal.ofReal (Metric.thickness ℝ s 1) *
          ENNReal.ofReal (Metric.thickness ℝ s 2)) := by
      gcongr
    have h_mid :
        ((6 : ℝ≥0)⁻¹ : ℝ≥0∞) *
            (((bd.C₀ : ℝ≥0∞)⁻¹ ^ 3) * ((cfg.r₁ : ℝ≥0) : ℝ≥0∞) *
              ((cfg.b : ℝ≥0) : ℝ≥0∞) * ((cfg.a : ℝ≥0) : ℝ≥0∞)) ≤
          volume s := by
      calc
        ((6 : ℝ≥0)⁻¹ : ℝ≥0∞) * (((bd.C₀ : ℝ≥0∞)⁻¹ ^ 3) * ((cfg.r₁ : ℝ≥0) : ℝ≥0∞) *
            ((cfg.b : ℝ≥0) : ℝ≥0∞) * ((cfg.a : ℝ≥0) : ℝ≥0∞))
            = ((6 : ℝ≥0)⁻¹ : ℝ≥0∞) * (ENNReal.ofReal (((bd.C₀ : ℝ)⁻¹ * t hi0)) *
                ENNReal.ofReal (((bd.C₀ : ℝ)⁻¹ * t hi1)) *
                ENNReal.ofReal (((bd.C₀ : ℝ)⁻¹ * t hi2))) := by
          rw [hprod_low_val]
        _ ≤ ((6 : ℝ≥0)⁻¹ : ℝ≥0∞) * (ENNReal.ofReal (Metric.thickness ℝ s 0) *
            ENNReal.ofReal (Metric.thickness ℝ s 1) *
            ENNReal.ofReal (Metric.thickness ℝ s 2)) := by
          gcongr
        _ ≤ volume s := hvol_lower
    have h_inv_comb : ((6 : ℝ≥0)⁻¹ : ℝ≥0∞) * ((bd.C₀ : ℝ≥0∞)⁻¹ ^ 3) =
        (((6 * bd.C₀ ^ 3 : ℝ≥0) : ℝ≥0∞))⁻¹ := by
      calc
        ((6 : ℝ≥0)⁻¹ : ℝ≥0∞) * ((bd.C₀ : ℝ≥0∞)⁻¹ ^ 3)
            = ((6 : ℝ≥0∞)⁻¹) * ((bd.C₀ : ℝ≥0∞)⁻¹ ^ 3) := rfl
        _ = ((6 : ℝ≥0∞)⁻¹) * ((bd.C₀ : ℝ≥0∞) ^ 3)⁻¹ := by
          rw [← ENNReal.inv_pow]
        _ = (((6 : ℝ≥0∞) * (bd.C₀ : ℝ≥0∞) ^ 3))⁻¹ := by
          have h6_ne_zero : (6 : ℝ≥0∞) ≠ 0 := by norm_num
          have hC0_ne_top : (bd.C₀ : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
          rw [(ENNReal.mul_inv (Or.inl h6_ne_zero) (Or.inl (by norm_num : (6 : ℝ≥0∞) ≠ ⊤))).symm]
        _ = (((6 * bd.C₀ ^ 3 : ℝ≥0) : ℝ≥0∞))⁻¹ := by
          simp
    have h_factor :
        ((6 : ℝ≥0)⁻¹ : ℝ≥0∞) *
            (((bd.C₀ : ℝ≥0∞)⁻¹ ^ 3) * ((cfg.r₁ : ℝ≥0) : ℝ≥0∞) *
              ((cfg.b : ℝ≥0) : ℝ≥0∞) * ((cfg.a : ℝ≥0) : ℝ≥0∞)) =
          (((6 * bd.C₀ ^ 3 : ℝ≥0) : ℝ≥0∞))⁻¹ *
            ((cfg.r₁ * cfg.b * cfg.a : ℝ≥0) : ℝ≥0∞) := by
      calc
        ((6 : ℝ≥0)⁻¹ : ℝ≥0∞) * (((bd.C₀ : ℝ≥0∞)⁻¹ ^ 3) * ((cfg.r₁ : ℝ≥0) : ℝ≥0∞) *
            ((cfg.b : ℝ≥0) : ℝ≥0∞) * ((cfg.a : ℝ≥0) : ℝ≥0∞))
            = (((6 : ℝ≥0)⁻¹ : ℝ≥0∞) * ((bd.C₀ : ℝ≥0∞)⁻¹ ^ 3)) *
                ((cfg.r₁ : ℝ≥0) : ℝ≥0∞) * ((cfg.b : ℝ≥0) : ℝ≥0∞) *
                  ((cfg.a : ℝ≥0) : ℝ≥0∞) := by
          simp [mul_assoc]
        _ = (((6 * bd.C₀ ^ 3 : ℝ≥0) : ℝ≥0∞))⁻¹ * ((cfg.r₁ : ℝ≥0) : ℝ≥0∞) *
            ((cfg.b : ℝ≥0) : ℝ≥0∞) * ((cfg.a : ℝ≥0) : ℝ≥0∞) := by
          rw [h_inv_comb]
        _ = (((6 * bd.C₀ ^ 3 : ℝ≥0) : ℝ≥0∞))⁻¹ *
            ((cfg.r₁ * cfg.b * cfg.a : ℝ≥0) : ℝ≥0∞) := by
          simp [ENNReal.coe_mul, mul_assoc]
    have h_eq :
        (((6 * bd.C₀ ^ 3 : ℝ≥0) : ℝ≥0∞))⁻¹ *
            ((cfg.r₁ * cfg.b * cfg.a : ℝ≥0) : ℝ≥0∞) =
          ((6 : ℝ≥0)⁻¹ : ℝ≥0∞) *
            ((bd.C₀ : ℝ≥0∞)⁻¹ ^ 3 * ((cfg.r₁ : ℝ≥0) : ℝ≥0∞) *
              ((cfg.b : ℝ≥0) : ℝ≥0∞) * ((cfg.a : ℝ≥0) : ℝ≥0∞)) :=
      h_factor.symm
    exact h_eq ▸ h_mid
  exact ⟨h_lower, h_upper⟩

/-- **A block segment is a small body inside its factoring body**.

For a ball `B ∈ 𝔅` and a segment `T_B ∈ 𝕋_B` lying, by (C4), in the body `W = W_{blk T_B}` of
its own block, the volume ratio `|W| / |T_B|` is positive and finite, and

`|T_B| ≤ C_{lem:ml2thickCard}(C₀) (δ² / (a b)) |W|`, `C_{lem:ml2thickCard}(C₀) = 48 C₀⁶`,

the constant of blueprint `def:ml2thickCardConstant`. The four conjuncts are exactly the
display of the blueprint lemma: `0 < |T_B|`, `|T_B| ≤ |W|`, `|W| ≠ ∞`, and the ratio bound
with the division by `a b` cleared to the left-hand side.

This is the only form in which the counting steps use the two volume lemmas: it is
`Kakeya.VeryNotSticky.thickSegVol` and `Kakeya.VeryNotSticky.thickBodyVol` multiplied together
(the containment `|T_B| ≤ |W|` coming instead from
`Kakeya.VeryNotSticky.BallData.segs_le` by monotonicity of the measure), and it is what makes
the reciprocal ratio `(|W| / |T_B|)^ϱ` of `Kakeya.VeryNotSticky.thickBlockDensity_ge` and the
multiplication by `|W| / |T_B|` in `Kakeya.VeryNotSticky.thickBlockCard_ge` legitimate. -/
theorem thickSegVolRatio (cfg : VeryNotSticky.{u}) (bd : BallData cfg) {B : bd.bι}
    (hB : B ∈ bd.bs) {p : bd.σ} (hp : p ∈ bd.segs B) :
    0 < volume (bd.Y p).carrier ∧
      volume (bd.Y p).carrier ≤ volume (bd.Wb (bd.blk p)).carrier ∧
      volume (bd.Wb (bd.blk p)).carrier ≠ ⊤ ∧
      ((cfg.a * cfg.b : ℝ≥0) : ℝ≥0∞) * volume (bd.Y p).carrier ≤
        ((48 * bd.C₀ ^ 6 * cfg.δ ^ 2 : ℝ≥0) : ℝ≥0∞) *
          volume (bd.Wb (bd.blk p)).carrier := by
  let T := (bd.Y p).carrier
  let W := (bd.Wb (bd.blk p)).carrier
  have hSegVol := thickSegVol cfg bd hB hp
  rcases hSegVol with ⟨hTlow, hTup⟩
  -- (1) 0 < volume T: from the lower bound of thickSegVol
  have hr₁pos : 0 < (cfg.r₁ : ℝ≥0) := by
    have : 0 < (cfg.r₁ : ℝ) := by
      dsimp only [r₁]
      have h := Real.rpow_pos_of_pos (by exact_mod_cast cfg.hδ) cfg.exscal
      exact_mod_cast h
    exact_mod_cast this
  have hC₀pos : 0 < (bd.C₀ : ℝ) := by
    have hC₀1 : (1 : ℝ) ≤ (bd.C₀ : ℝ) := by exact_mod_cast bd.hC₀
    linarith
  have hC₀pos_nn : 0 < bd.C₀ := by
    have hC₀1 : (1 : ℝ≥0) ≤ bd.C₀ := bd.hC₀
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 1) hC₀1
  have hC₀_nonzero_real : (6 : ℝ) * (bd.C₀ : ℝ) ^ 3 ≠ 0 := by
    positivity
  have hC₀_nonzero_nn : (6 * bd.C₀ ^ 3 : ℝ≥0) ≠ 0 := by
    have hpos : 0 < (6 * bd.C₀ ^ 3 : ℝ≥0) := by positivity
    exact hpos.ne.symm
  have hTpos : 0 < volume T := by
    have hC₀_nn_pos : 0 < (6 * bd.C₀ ^ 3 : ℝ≥0) := by positivity
    have hC₀_enn_ne_zero : ((6 * bd.C₀ ^ 3 : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
      simpa using hC₀_nn_pos.ne.symm
    have hC₀_enn_ne_top : ((6 * bd.C₀ ^ 3 : ℝ≥0) : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
    have h_inv_pos : 0 < (((6 * bd.C₀ ^ 3 : ℝ≥0) : ℝ≥0∞))⁻¹ :=
      ENNReal.inv_pos.mpr hC₀_enn_ne_top
    have h_rd_pos : 0 < ((cfg.r₁ * cfg.δ ^ 2 : ℝ≥0) : ℝ≥0∞) := by
      have : 0 < (cfg.r₁ * cfg.δ ^ 2 : ℝ≥0) := mul_pos hr₁pos (pow_pos (by
        exact_mod_cast cfg.hδ) 2)
      exact_mod_cast this
    have h_mul_ne_zero :
        (((6 * bd.C₀ ^ 3 : ℝ≥0) : ℝ≥0∞))⁻¹ *
            ((cfg.r₁ * cfg.δ ^ 2 : ℝ≥0) : ℝ≥0∞) ≠
          0 := by
      intro h
      rcases mul_eq_zero.mp h with (h' | h')
      · exact h_inv_pos.ne.symm h'
      · exact h_rd_pos.ne.symm h'
    have hpos :
        0 < (((6 * bd.C₀ ^ 3 : ℝ≥0) : ℝ≥0∞))⁻¹ *
          ((cfg.r₁ * cfg.δ ^ 2 : ℝ≥0) : ℝ≥0∞) :=
      pos_iff_ne_zero.mpr h_mul_ne_zero
    exact lt_of_lt_of_le hpos hTlow
  -- (2) volume T ≤ volume W: from segs_le by measure_mono
  have hTW : volume T ≤ volume W := by
    have h_sub : T ⊆ W := by
      have hle : (bd.Y p).toConvexSpaceBody ≤ bd.Wb (bd.blk p) := bd.segs_le B hB p hp
      exact hle
    exact measure_mono h_sub
  -- (3) volume W ≠ ⊤: from compactness
  have hWfin : volume W ≠ ⊤ := (bd.Wb (bd.blk p)).isCompact.measure_lt_top.ne
  -- (4) ratio bound
  have hratio : ((cfg.a * cfg.b : ℝ≥0) : ℝ≥0∞) * volume T ≤
      ((48 * bd.C₀ ^ 6 * cfg.δ ^ 2 : ℝ≥0) : ℝ≥0∞) * volume W := by
    have hWlow :
        (((6 * bd.C₀ ^ 3 : ℝ≥0) : ℝ≥0∞))⁻¹ *
            ((cfg.r₁ * cfg.b * cfg.a : ℝ≥0) : ℝ≥0∞) ≤
          volume W := by
      have hj : bd.blk p ∈ bd.bodies B := bd.blk_mem B hB p hp
      rcases thickBodyVol cfg bd hB hj with ⟨hWlow', _⟩
      exact hWlow'
    -- NNReal equality: (a*b)*(8*C₀³*r₁*δ²) = (48*C₀⁶*δ²)*((6*C₀³)⁻¹*(r₁*b*a))
    have h_nn_id :
        (cfg.a * cfg.b : ℝ≥0) *
            (8 * bd.C₀ ^ 3 * cfg.r₁ * cfg.δ ^ 2 : ℝ≥0) =
          (48 * bd.C₀ ^ 6 * cfg.δ ^ 2 : ℝ≥0) *
            ((6 * bd.C₀ ^ 3 : ℝ≥0)⁻¹ * (cfg.r₁ * cfg.b * cfg.a : ℝ≥0)) := by
      apply NNReal.eq
      field_simp [hC₀_nonzero_real]
      ring_nf
    have h_id_enn :
        ((cfg.a * cfg.b : ℝ≥0) : ℝ≥0∞) *
            ((8 * bd.C₀ ^ 3 * cfg.r₁ * cfg.δ ^ 2 : ℝ≥0) : ℝ≥0∞) =
          ((48 * bd.C₀ ^ 6 * cfg.δ ^ 2 : ℝ≥0) : ℝ≥0∞) *
              (((6 * bd.C₀ ^ 3 : ℝ≥0) : ℝ≥0∞))⁻¹ *
            ((cfg.r₁ * cfg.b * cfg.a : ℝ≥0) : ℝ≥0∞) := by
      calc
        ((cfg.a * cfg.b : ℝ≥0) : ℝ≥0∞) *
            ((8 * bd.C₀ ^ 3 * cfg.r₁ * cfg.δ ^ 2 : ℝ≥0) : ℝ≥0∞)
            = (((cfg.a * cfg.b : ℝ≥0) *
              (8 * bd.C₀ ^ 3 * cfg.r₁ * cfg.δ ^ 2 : ℝ≥0)) : ℝ≥0∞) := by simp
        _ = (((48 * bd.C₀ ^ 6 * cfg.δ ^ 2 : ℝ≥0) *
            ((6 * bd.C₀ ^ 3 : ℝ≥0)⁻¹ *
              (cfg.r₁ * cfg.b * cfg.a : ℝ≥0)) : ℝ≥0) : ℝ≥0∞) := by
          simpa using congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) h_nn_id
        _ = (((48 * bd.C₀ ^ 6 * cfg.δ ^ 2 : ℝ≥0) : ℝ≥0∞) *
            (((6 * bd.C₀ ^ 3 : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) *
            ((cfg.r₁ * cfg.b * cfg.a : ℝ≥0) : ℝ≥0∞)) := by
          simp [mul_assoc]
        _ = ((48 * bd.C₀ ^ 6 * cfg.δ ^ 2 : ℝ≥0) : ℝ≥0∞) *
            (((6 * bd.C₀ ^ 3 : ℝ≥0) : ℝ≥0∞))⁻¹ *
            ((cfg.r₁ * cfg.b * cfg.a : ℝ≥0) : ℝ≥0∞) := by
          rw [ENNReal.coe_inv hC₀_nonzero_nn]
    calc
      ((cfg.a * cfg.b : ℝ≥0) : ℝ≥0∞) * volume T
          ≤ ((cfg.a * cfg.b : ℝ≥0) : ℝ≥0∞) *
            ((8 * bd.C₀ ^ 3 * cfg.r₁ * cfg.δ ^ 2 : ℝ≥0) : ℝ≥0∞) := by
        gcongr
      _ = ((48 * bd.C₀ ^ 6 * cfg.δ ^ 2 : ℝ≥0) : ℝ≥0∞) *
          (((6 * bd.C₀ ^ 3 : ℝ≥0) : ℝ≥0∞))⁻¹ *
          ((cfg.r₁ * cfg.b * cfg.a : ℝ≥0) : ℝ≥0∞) := by
        rw [h_id_enn]
      _ = ((48 * bd.C₀ ^ 6 * cfg.δ ^ 2 : ℝ≥0) : ℝ≥0∞) *
          ((((6 * bd.C₀ ^ 3 : ℝ≥0) : ℝ≥0∞))⁻¹ *
            ((cfg.r₁ * cfg.b * cfg.a : ℝ≥0) : ℝ≥0∞)) := by
        simp [mul_assoc]
      _ ≤ ((48 * bd.C₀ ^ 6 * cfg.δ ^ 2 : ℝ≥0) : ℝ≥0∞) * volume W :=
        mul_le_mul' (le_refl _) hWlow
  exact ⟨hTpos, hTW, hWfin, hratio⟩

/-- **GWZ (9.4), density form: the mass of a block in its body** (blueprint
`lem:ml2thickBlockDensity`, display `blockDensityLower`).

For a ball `B ∈ 𝔅`, a body `W = W_{blk p₀} ∈ 𝕎_B` and any segment `T_B = Y p₀` of the block
`𝕋_{B,W}`,

`(|W| / |T_B|)^ϱ ≤ C_bias Δ(𝕋_{B,W}, W)`,

written here in the equivalent division-cleared shape `C_bias⁻¹ (|W|/|T_B|)^ϱ ≤ Δ(𝕋_{B,W}, W)`
so that no positivity or finiteness side condition is needed in `[0, ∞]`.

The block `𝕋_{B,W}` is `(bd.segs B).filter fun p => bd.blk p = bd.blk p₀` and the family of
bodies is `fun p => (bd.Y p).toConvexSpaceBody`, both written out inline rather than through
abbreviations; the density `Δ` is `Kakeya.densityIn`.

The whole quantitative content is the per-ball biased comparison
`Kakeya.VeryNotSticky.BallData.biasedDensity` of (C4) — blueprint equation `factmaxmodbias`,
with the constant `Kakeya.VeryNotSticky.BallData.Cbias` — applied at the comparison body
`K = T_B`, which is legitimate because `T_B ≤ W` by
`Kakeya.VeryNotSticky.BallData.segs_le`. Two further ingredients turn that application into
the display: a member of a family sees density at least one (blueprint
`lem:ml2thickDeltaMember`, pure bookkeeping about `Kakeya.densityIn`, obtained here from
`Kakeya.le_densityIn` and subsumed in this proof), and the positive finite volume of a segment
and of a body, which is what makes the reciprocal volume ratio legitimate — that is
`Kakeya.VeryNotSticky.thickSegVol` and `Kakeya.VeryNotSticky.thickBodyVol`. The power
manipulation in `[0, ∞]` that clears the ratio is blueprint `lem:ml2thickRpowClear`, also
inlined. -/
theorem thickBlockDensity_ge (cfg : VeryNotSticky.{u}) (bd : BallData cfg) {B : bd.bι}
    (hB : B ∈ bd.bs) {p₀ : bd.σ} (hp₀ : p₀ ∈ bd.segs B) :
    (bd.Cbias : ℝ≥0∞)⁻¹ *
        (volume (bd.Wb (bd.blk p₀)).carrier / volume (bd.Y p₀).carrier) ^ cfg.ϱ ≤
      densityIn ((bd.segs B).filter fun p => bd.blk p = bd.blk p₀)
        (fun p => (bd.Y p).toConvexSpaceBody) (bd.Wb (bd.blk p₀)) := by
  let s := (bd.segs B).filter fun p => bd.blk p = bd.blk p₀
  let Wf := fun p : bd.σ => (bd.Y p).toConvexSpaceBody
  let K := (bd.Y p₀).toConvexSpaceBody
  let W := bd.Wb (bd.blk p₀)
  have hj : bd.blk p₀ ∈ bd.bodies B := bd.blk_mem B hB p₀ hp₀
  have hKle : K ≤ W := bd.segs_le B hB p₀ hp₀
  have hp₀' : p₀ ∈ s := by
    simp [s, hp₀]
  -- Positive finite volume for K (the segment)
  have hKfin : volume K.carrier ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have hKpos : 0 < volume K.carrier := by
    have hconv : Convex ℝ K.carrier := K.convex
    have hbdd : Bornology.IsBounded K.carrier := K.isCompact.isBounded
    have hfinrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
    have hδpos : 0 < (cfg.δ : ℝ) := by exact_mod_cast cfg.hδ
    have hr₁pos : 0 < (cfg.r₁ : ℝ) := by
      dsimp only [r₁]
      have := Real.rpow_pos_of_pos (by exact_mod_cast cfg.hδ) cfg.exscal
      exact_mod_cast this
    have hC₀pos : 0 < (bd.C₀ : ℝ) := by
      have hC₀1 : (1 : ℝ) ≤ (bd.C₀ : ℝ) := by exact_mod_cast bd.hC₀
      linarith
    have h_ethick_ne_zero : ∀ i ∈ Finset.range (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))),
        Metric.ethickness ℝ K.carrier i ≠ 0 := by
      intro i hi
      rw [Finset.mem_range, hfinrank] at hi
      have hthick := bd.segs_thickness B hB p₀ hp₀
      let k : Fin 3 := ⟨i, hi⟩
      rcases hthick k with ⟨hle, _⟩
      have h_val_pos : 0 < (![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)] k) := by
        match k with
        | 0 => simp [hr₁pos]
        | 1 => simp [hδpos]
        | 2 => simp [hδpos]
      have hthickpos : 0 < Metric.thickness ℝ K.carrier i := by
        have htemp : ((bd.C₀ : ℝ)⁻¹ * (![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)] k)) ≤
          Metric.thickness ℝ K.carrier i := by
          simpa using hle
        have hprodpos : 0 < (bd.C₀ : ℝ)⁻¹ * (![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)] k) :=
          mul_pos (by
            have : 0 < (bd.C₀ : ℝ) := hC₀pos
            exact inv_pos.mpr this)
            h_val_pos
        linarith
      rw [Metric.ethickness_thickness' hbdd i]
      rw [ENNReal.ofReal_ne_zero_iff]
      exact hthickpos
    exact hconv.volume_pos_of_ethickness_ne_zero h_ethick_ne_zero
  -- Positive finite volume for W (the body)
  have hWfin : volume W.carrier ≠ ⊤ := W.isCompact.measure_lt_top.ne
  have hWpos : 0 < volume W.carrier := by
    have hconv : Convex ℝ W.carrier := W.convex
    have hbdd : Bornology.IsBounded W.carrier := W.isCompact.isBounded
    have hfinrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
    have hthick := bd.bodies_thickness B hB (bd.blk p₀) hj
    have hδpos : 0 < (cfg.δ : ℝ) := by exact_mod_cast cfg.hδ
    have hapos : 0 < (cfg.a : ℝ) := by
      have hδa : (cfg.δ : ℝ) ≤ (cfg.a : ℝ) := by exact_mod_cast cfg.hdims.1
      have hδpos' : 0 < (cfg.δ : ℝ) := by exact_mod_cast cfg.hδ
      linarith
    have hbpos : 0 < (cfg.b : ℝ) := by
      have hab : (cfg.a : ℝ) ≤ (cfg.b : ℝ) := by exact_mod_cast cfg.hdims.2.1
      linarith
    have hr₁pos : 0 < (cfg.r₁ : ℝ) := by
      dsimp only [r₁]
      have := Real.rpow_pos_of_pos (by exact_mod_cast cfg.hδ) cfg.exscal
      exact_mod_cast this
    have hC₀pos : 0 < (bd.C₀ : ℝ) := by
      have hC₀1 : (1 : ℝ) ≤ (bd.C₀ : ℝ) := by exact_mod_cast bd.hC₀
      linarith
    have h_ethick_ne_zero : ∀ i ∈ Finset.range (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))),
        Metric.ethickness ℝ W.carrier i ≠ 0 := by
      intro i hi
      rw [Finset.mem_range, hfinrank] at hi
      let k : Fin 3 := ⟨i, hi⟩
      rcases hthick k with ⟨hle, _⟩
      have h_val_pos : 0 < (![(cfg.r₁ : ℝ), (cfg.b : ℝ), (cfg.a : ℝ)] k) := by
        match k with
        | 0 => simp [hr₁pos]
        | 1 => simp [hbpos]
        | 2 => simp [hapos]
      have hthickpos : 0 < Metric.thickness ℝ W.carrier i := by
        have htemp : ((bd.C₀ : ℝ)⁻¹ * (![(cfg.r₁ : ℝ), (cfg.b : ℝ), (cfg.a : ℝ)] k)) ≤
          Metric.thickness ℝ W.carrier i := by
          simpa using hle
        have hprodpos : 0 < (bd.C₀ : ℝ)⁻¹ * (![(cfg.r₁ : ℝ), (cfg.b : ℝ), (cfg.a : ℝ)] k) :=
          mul_pos (by
            have : 0 < (bd.C₀ : ℝ) := hC₀pos
            exact inv_pos.mpr this)
            h_val_pos
        linarith
      rw [Metric.ethickness_thickness' hbdd i]
      rw [ENNReal.ofReal_ne_zero_iff]
      exact hthickpos
    exact hconv.volume_pos_of_ethickness_ne_zero h_ethick_ne_zero
  have h1 : 1 ≤ densityIn s Wf K := by
    calc
      1 = volume K.carrier / volume K.carrier :=
        (ENNReal.div_self hKpos.ne.symm hKfin).symm
      _ ≤ densityIn s Wf K := le_densityIn s Wf K hp₀' (le_refl K)
  have hbias := bd.biasedDensity B hB (bd.blk p₀) hj K hKle
  -- hbias: densityIn s Wf K ≤ (bd.Cbias : ENNReal) * (|K| / |W|)^ϱ * densityIn s Wf W
  have hineq : 1 ≤ (bd.Cbias : ℝ≥0∞) * (volume K.carrier / volume W.carrier) ^ cfg.ϱ *
      densityIn s Wf W :=
    h1.trans hbias
  -- `Afwd` is the factor of the biased comparison and `Ainv` its reciprocal; they must not be
  -- called `B`, which is the ball fixed above.
  set Afwd : ℝ≥0∞ :=
    (bd.Cbias : ℝ≥0∞) * (volume K.carrier / volume W.carrier) ^ cfg.ϱ with hAfwd_def
  set Ainv : ℝ≥0∞ :=
    (bd.Cbias : ℝ≥0∞)⁻¹ * (volume W.carrier / volume K.carrier) ^ cfg.ϱ with hAinv_def
  have hCbias0 : (bd.Cbias : ℝ≥0∞) ≠ 0 := by
    have h1Cbias : (1 : ℝ≥0∞) ≤ (bd.Cbias : ℝ≥0∞) := by exact_mod_cast bd.hCbias
    have hpos : (0 : ℝ≥0∞) < (bd.Cbias : ℝ≥0∞) :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) h1Cbias
    exact hpos.ne.symm
  have hCbiastop : (bd.Cbias : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hKpos' : volume K.carrier ≠ 0 := hKpos.ne.symm
  have hWpos' : volume W.carrier ≠ 0 := hWpos.ne.symm
  have h_div_mul :
      (volume W.carrier / volume K.carrier) *
          (volume K.carrier / volume W.carrier) =
        1 := by
    calc
      (volume W.carrier / volume K.carrier) * (volume K.carrier / volume W.carrier)
          = (volume W.carrier * (volume K.carrier)⁻¹) *
            (volume K.carrier * (volume W.carrier)⁻¹) := rfl
      _ = volume W.carrier * ((volume K.carrier)⁻¹ * volume K.carrier) *
          (volume W.carrier)⁻¹ := by ring
      _ = volume W.carrier * 1 * (volume W.carrier)⁻¹ := by
        rw [ENNReal.inv_mul_cancel hKpos' hKfin]
      _ = volume W.carrier * (volume W.carrier)⁻¹ := by simp
      _ = 1 := ENNReal.mul_inv_cancel hWpos' hWfin
  have hBA : Ainv * Afwd = 1 := by
    calc
      Ainv * Afwd = ((bd.Cbias : ℝ≥0∞)⁻¹ * (volume W.carrier / volume K.carrier) ^ cfg.ϱ) *
            ((bd.Cbias : ℝ≥0∞) * (volume K.carrier / volume W.carrier) ^ cfg.ϱ) := rfl
      _ = ((bd.Cbias : ℝ≥0∞)⁻¹ * (bd.Cbias : ℝ≥0∞)) *
          (((volume W.carrier / volume K.carrier) ^ cfg.ϱ) *
           ((volume K.carrier / volume W.carrier) ^ cfg.ϱ)) := by
        simp [mul_assoc, mul_comm, mul_left_comm]
      _ = 1 * (((volume W.carrier / volume K.carrier) ^ cfg.ϱ) *
               ((volume K.carrier / volume W.carrier) ^ cfg.ϱ)) := by
        simp [ENNReal.inv_mul_cancel hCbias0 hCbiastop]
      _ = ((volume W.carrier / volume K.carrier) *
          (volume K.carrier / volume W.carrier)) ^ cfg.ϱ := by
        have hϱ_nonneg : 0 ≤ cfg.ϱ := le_of_lt cfg.hϱ
        simp [← ENNReal.mul_rpow_of_nonneg (volume W.carrier / volume K.carrier)
          (volume K.carrier / volume W.carrier) hϱ_nonneg]
      _ = 1 ^ cfg.ϱ := by rw [h_div_mul]
      _ = 1 := by simp
  calc
    Ainv = Ainv * 1 := by simp
    _ ≤ Ainv * (Afwd * densityIn s Wf W) :=
      mul_le_mul' (le_refl Ainv) hineq
    _ = (Ainv * Afwd) * densityIn s Wf W := by ring
    _ = 1 * densityIn s Wf W := by rw [hBA]
    _ = densityIn s Wf W := by simp

/-- **GWZ (9.4), cardinality form: a block is large** (blueprint `lem:ml2thickTTcard`, display
`TBWbig`).

With `C_{lem:ml2thickCard}(C₀) = 48 C₀^6` the density–cardinality conversion constant of
blueprint `def:ml2thickCardConstant`,

`|𝕋_{B,W}| ≥ (48 C₀^6 C_bias)⁻¹ (|W| / |T_B|)^{1+ϱ}`,

which is GWZ's `|𝕋_{B,W}| ⪆ (|W|/|T_B|)^{1+ϱ}` with its comparison constant made explicit.
The constant is written out inline, `48 * bd.C₀ ^ 6 * bd.Cbias`, rather than through a named
definition: it is used only here and its two factors are already named fields.

This is `Kakeya.VeryNotSticky.thickBlockDensity_ge` combined with the density–cardinality
conversion of blueprint `lem:ml2thickCard` at `K = W` — where the filtered family
`𝕋_{B,W}[W]` is all of `𝕋_{B,W}`, every segment lying in the body of its block by
`Kakeya.VeryNotSticky.BallData.segs_le` — after multiplying by the ratio `|W|/|T_B|`, which is
positive and finite by `Kakeya.VeryNotSticky.thickSegVolRatio`. The conversion constant is the
ratio by which the volumes of two segments of the same ball can differ, and it comes from the
thickness comparison `Kakeya.VeryNotSticky.BallData.segs_thickness` of (C3) through the two
volume/thickness bounds of the convex-body chapter, i.e. it is the two-sided bound
`Kakeya.VeryNotSticky.thickSegVol` applied to two segments at once; the conversion itself
 is not formalized separately. -/
theorem thickBlockCard_ge (cfg : VeryNotSticky.{u}) (bd : BallData cfg) {B : bd.bι}
    (hB : B ∈ bd.bs) {p₀ : bd.σ} (hp₀ : p₀ ∈ bd.segs B) :
    (((48 * bd.C₀ ^ 6 * bd.Cbias : ℝ≥0) : ℝ≥0∞))⁻¹ *
        (volume (bd.Wb (bd.blk p₀)).carrier / volume (bd.Y p₀).carrier) ^ (1 + cfg.ϱ) ≤
      (((bd.segs B).filter fun p => bd.blk p = bd.blk p₀).card : ℝ≥0∞) := by
  let block := (bd.segs B).filter fun p => bd.blk p = bd.blk p₀
  let W := bd.Wb (bd.blk p₀)
  let T := bd.Y p₀
  let Vbody := fun p : bd.σ => (bd.Y p).toConvexSpaceBody
  have hWfinite : volume W.carrier ≠ ⊤ := W.isCompact.measure_lt_top.ne
  have hTfinite : volume T.carrier ≠ ⊤ := T.isCompact.measure_lt_top.ne
  have hδpos : 0 < (cfg.δ : ℝ) := by exact_mod_cast cfg.hδ
  have hC₀pos : 0 < (bd.C₀ : ℝ) := by
    have hC₀1 : (1 : ℝ) ≤ (bd.C₀ : ℝ) := by exact_mod_cast bd.hC₀
    linarith
  have hr₁pos : 0 < (cfg.r₁ : ℝ) := by
    dsimp only [r₁]
    have := Real.rpow_pos_of_pos (by exact_mod_cast cfg.hδ) cfg.exscal; exact_mod_cast this
  have hapos : 0 < (cfg.a : ℝ) := by
    have hδpos' : 0 < (cfg.δ : ℝ) := hδpos
    have hδa : (cfg.δ : ℝ) ≤ (cfg.a : ℝ) := by exact_mod_cast cfg.hdims.1
    linarith
  have hbpos : 0 < (cfg.b : ℝ) := by
    have hapos' : 0 < (cfg.a : ℝ) := hapos
    have hab : (cfg.a : ℝ) ≤ (cfg.b : ℝ) := by exact_mod_cast cfg.hdims.2.1
    linarith
  have hC₀_ne_zero : (bd.C₀ : ℝ) ≠ 0 := by linarith
  have hTpos : 0 < volume T.carrier := by
    have hthick := bd.segs_thickness B hB p₀ hp₀
    have hconv_T : Convex ℝ (T.carrier) := T.toConvexSpaceBody.convex
    have hbdd_T : Bornology.IsBounded (T.carrier) := T.isCompact.isBounded
    have hfinrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
    have hthick_ne_zero : ∀ i ∈ Finset.range (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))),
        Metric.ethickness ℝ (T.carrier) i ≠ 0 := by
      intro i hi
      rw [Finset.mem_range, hfinrank] at hi
      let k : Fin 3 := ⟨i, hi⟩
      rcases hthick k with ⟨hle, _⟩
      have h_val_pos : 0 < (![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)] k) := by
        match k with | 0 => simp [hr₁pos] | 1 => simp [hδpos] | 2 => simp [hδpos]
      have hpos : 0 < Metric.thickness ℝ (T.carrier) i := by
        have htemp : ((bd.C₀ : ℝ)⁻¹ * (![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)] k)) ≤
          Metric.thickness ℝ (T.carrier) i := by simpa [T] using hle
        have hprodpos : 0 < (bd.C₀ : ℝ)⁻¹ * (![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)] k) :=
          mul_pos (inv_pos.mpr hC₀pos) h_val_pos
        linarith
      rw [Metric.ethickness_thickness' hbdd_T i]
      rw [ENNReal.ofReal_ne_zero_iff]
      exact hpos
    exact hconv_T.volume_pos_of_ethickness_ne_zero hthick_ne_zero
  have hT_ne_zero : volume T.carrier ≠ 0 := hTpos.ne.symm
  have hWpos : 0 < volume W.carrier := by
    have hbodies_thick := bd.bodies_thickness B hB (bd.blk p₀) (bd.blk_mem B hB p₀ hp₀)
    have hconv_W : Convex ℝ (W.carrier) := W.convex
    have hbdd_W : Bornology.IsBounded (W.carrier) := W.isCompact.isBounded
    have hfinrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
    have hthick_ne_zero : ∀ i ∈ Finset.range (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))),
        Metric.ethickness ℝ (W.carrier) i ≠ 0 := by
      intro i hi
      rw [Finset.mem_range, hfinrank] at hi
      let k : Fin 3 := ⟨i, hi⟩
      rcases hbodies_thick k with ⟨hle, _⟩
      have h_val_pos : 0 < (![(cfg.r₁ : ℝ), (cfg.b : ℝ), (cfg.a : ℝ)] k) := by
        match k with | 0 => simp [hr₁pos] | 1 => simp [hbpos] | 2 => simp [hapos]
      have hpos : 0 < Metric.thickness ℝ (W.carrier) i := by
        have htemp : ((bd.C₀ : ℝ)⁻¹ * (![(cfg.r₁ : ℝ), (cfg.b : ℝ), (cfg.a : ℝ)] k)) ≤
          Metric.thickness ℝ (W.carrier) i := by simpa [W] using hle
        have hprodpos : 0 < (bd.C₀ : ℝ)⁻¹ * (![(cfg.r₁ : ℝ), (cfg.b : ℝ), (cfg.a : ℝ)] k) :=
          mul_pos (inv_pos.mpr hC₀pos) h_val_pos
        linarith
      rw [Metric.ethickness_thickness' hbdd_W i]
      rw [ENNReal.ofReal_ne_zero_iff]
      exact hpos
    exact hconv_W.volume_pos_of_ethickness_ne_zero hthick_ne_zero
  have hW_ne_zero : volume W.carrier ≠ 0 := hWpos.ne.symm
  have hseg_le : ∀ p ∈ block, Vbody p ≤ W := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp_seg, hblk⟩
    have h := bd.segs_le B hB p hp_seg; rw [hblk] at h; exact h
  have hdens_eq : densityIn block Vbody W =
      (∑ p ∈ block, volume (Vbody p).carrier) / volume W.carrier := densityIn_of_all_le hseg_le
  have hdens_lower := thickBlockDensity_ge cfg bd hB hp₀
  rw [hdens_eq] at hdens_lower
  set volCompConst : ℝ≥0∞ := (48 : ℝ≥0∞) * (bd.C₀ : ℝ≥0∞) ^ 6 with hvc_def
  have hD_ne_zero : volCompConst ≠ 0 := by
    rw [hvc_def]
    have hC₀ENNpos : (0 : ℝ≥0∞) < (bd.C₀ : ℝ≥0∞) := by
      have hC₀1 : (1 : ℝ≥0∞) ≤ (bd.C₀ : ℝ≥0∞) := by exact_mod_cast bd.hC₀
      exact lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) hC₀1
    positivity
  have hD_finite : volCompConst ≠ ⊤ := by
    rw [hvc_def]
    refine ENNReal.mul_ne_top (by norm_num : (48 : ℝ≥0∞) ≠ ⊤) (by
      have hC₀_ne_top : (bd.C₀ : ℝ≥0∞) ≠ ⊤ := by
            simp
      exact ENNReal.pow_ne_top hC₀_ne_top)
  have hC₀ENNpos : (0 : ℝ≥0∞) < (bd.C₀ : ℝ≥0∞) := by
    have hC₀1 : (1 : ℝ≥0∞) ≤ (bd.C₀ : ℝ≥0∞) := by exact_mod_cast bd.hC₀
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) hC₀1
  have segment_volume_comp (p q : bd.σ) (hp : p ∈ bd.segs B) (hq : q ∈ bd.segs B) :
      volume ((bd.Y p).toConvexSpaceBody).carrier ≤
        volCompConst * volume ((bd.Y q).toConvexSpaceBody).carrier := by
    have hthick_p :
        HasThicknesses ((bd.Y p).carrier) bd.C₀
          ![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)] :=
      bd.segs_thickness B hB p hp
    have hthick_q :
        HasThicknesses ((bd.Y q).carrier) bd.C₀
          ![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)] :=
      bd.segs_thickness B hB q hq
    have hbdd_p : Bornology.IsBounded ((bd.Y p).carrier) := (bd.Y p).isCompact.isBounded
    have hbdd_q : Bornology.IsBounded ((bd.Y q).carrier) := (bd.Y q).isCompact.isBounded
    have hconv_q : Convex ℝ ((bd.Y q).carrier) := (bd.Y q).toConvexSpaceBody.convex
    have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
    let n : ℕ := 3
    have hcmp : ∀ k : Fin 3,
        ENNReal.ofReal (Metric.thickness ℝ ((bd.Y p).carrier) (k : ℕ)) ≤
          ((bd.C₀ : ℝ≥0∞) ^ 2) *
            ENNReal.ofReal (Metric.thickness ℝ ((bd.Y q).carrier) (k : ℕ)) := by
      intro k
      rcases hthick_p k with ⟨hpl_p, hpu_p⟩
      rcases hthick_q k with ⟨hpl_q, hqu_q⟩
      calc
        ENNReal.ofReal (Metric.thickness ℝ ((bd.Y p).carrier) (k : ℕ))
            ≤ ENNReal.ofReal ((bd.C₀ : ℝ) * ![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)] k) :=
              ENNReal.ofReal_le_ofReal (hpu_p)
        _ = (bd.C₀ : ℝ≥0∞) * ENNReal.ofReal (![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)] k) := by
          simp [ENNReal.ofReal_mul (by positivity : 0 ≤ (bd.C₀ : ℝ))]
        _ ≤ (bd.C₀ : ℝ≥0∞) *
            ENNReal.ofReal
              ((bd.C₀ : ℝ) * Metric.thickness ℝ ((bd.Y q).carrier) (k : ℕ)) := by
          have h_ref :
              ![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)] k ≤
                (bd.C₀ : ℝ) * Metric.thickness ℝ ((bd.Y q).carrier) (k : ℕ) := by
            calc
              ![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)] k
                  = ((bd.C₀ : ℝ) * ((bd.C₀ : ℝ)⁻¹)) *
                    ![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)] k := by
                    field_simp [hC₀_ne_zero]
              _ = (bd.C₀ : ℝ) *
                  (((bd.C₀ : ℝ)⁻¹ * ![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)] k)) := by
                ring
              _ ≤ (bd.C₀ : ℝ) * Metric.thickness ℝ ((bd.Y q).carrier) (k : ℕ) :=
                mul_le_mul_of_nonneg_left hpl_q (by positivity)
          gcongr
        _ = (bd.C₀ : ℝ≥0∞) *
            ((bd.C₀ : ℝ≥0∞) *
              ENNReal.ofReal (Metric.thickness ℝ ((bd.Y q).carrier) (k : ℕ))) := by
          simp [ENNReal.ofReal_mul (by positivity : 0 ≤ (bd.C₀ : ℝ))]
        _ = ((bd.C₀ : ℝ≥0∞) ^ 2) *
            ENNReal.ofReal (Metric.thickness ℝ ((bd.Y q).carrier) (k : ℕ)) := by ring
    have h_upper_p : volume ((bd.Y p).carrier) ≤ (2 : ℝ≥0∞) ^ (n : ℕ) *
        ∏ i ∈ Finset.range n, ENNReal.ofReal (Metric.thickness ℝ ((bd.Y p).carrier) i) := by
      have htemp : volume ((bd.Y p).carrier) ≤
          (2 : ℝ≥0∞) ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) *
            ∏ i ∈ Finset.range (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))),
              ENNReal.ofReal (Metric.thickness ℝ ((bd.Y p).carrier) i) :=
        volume_le_prod_thickness hbdd_p
      simpa [hn, n] using htemp
    have h_prod_cmp :
        ∏ i ∈ Finset.range n,
            ENNReal.ofReal (Metric.thickness ℝ ((bd.Y p).carrier) i) ≤
          ((bd.C₀ : ℝ≥0∞) ^ 6) * ∏ i ∈ Finset.range n,
            ENNReal.ofReal (Metric.thickness ℝ ((bd.Y q).carrier) i) := by
      calc
        ∏ i ∈ Finset.range n, ENNReal.ofReal (Metric.thickness ℝ ((bd.Y p).carrier) i)
            ≤ ∏ i ∈ Finset.range n, (((bd.C₀ : ℝ≥0∞) ^ 2) *
                ENNReal.ofReal (Metric.thickness ℝ ((bd.Y q).carrier) i)) :=
          Finset.prod_le_prod' fun i hi => by
            simpa using hcmp (⟨i, by simpa [n] using hi⟩ : Fin 3)
        _ = ((bd.C₀ : ℝ≥0∞) ^ 2) ^ n *
            ∏ i ∈ Finset.range n, ENNReal.ofReal (Metric.thickness ℝ ((bd.Y q).carrier) i) := by
          simp [Finset.prod_mul_distrib, Finset.prod_const]
        _ = ((bd.C₀ : ℝ≥0∞) ^ 6) *
            ∏ i ∈ Finset.range n, ENNReal.ofReal (Metric.thickness ℝ ((bd.Y q).carrier) i) := by
          dsimp [n]; ring
    have h_ethick_q :
        ∏ i ∈ Finset.range n,
            ENNReal.ofReal (Metric.thickness ℝ ((bd.Y q).carrier) i) =
          ∏ i ∈ Finset.range n, Metric.ethickness ℝ ((bd.Y q).carrier) i := by
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [Metric.ethickness_thickness' hbdd_q i]
    have h_lower_q : ((6 : ℝ≥0∞)⁻¹) *
        ∏ i ∈ Finset.range n, Metric.ethickness ℝ ((bd.Y q).carrier) i ≤
          volume ((bd.Y q).carrier) := by
      have htemp : (Metric.lt_volume_convexHull.c n : ℝ≥0∞) *
          ∏ i ∈ Finset.range n, Metric.ethickness ℝ ((bd.Y q).carrier) i ≤
            volume ((bd.Y q).carrier) :=
        by simpa [n, hn] using hconv_q.ethickness_prod_le_volume
      have h_cvol : (Metric.lt_volume_convexHull.c n : ℝ≥0∞) = (6 : ℝ≥0∞)⁻¹ := by
        dsimp [Metric.lt_volume_convexHull.c, n]; norm_num
      rw [h_cvol] at htemp; exact htemp
    have h_prod_q : ∏ i ∈ Finset.range n, Metric.ethickness ℝ ((bd.Y q).carrier) i ≤
        (6 : ℝ≥0∞) * volume ((bd.Y q).carrier) := by
      have htemp' :
          (6⁻¹ : ℝ≥0∞) *
              ∏ i ∈ Finset.range n, Metric.ethickness ℝ ((bd.Y q).carrier) i ≤
            volume ((bd.Y q).carrier) := h_lower_q
      calc
        ∏ i ∈ Finset.range n, Metric.ethickness ℝ ((bd.Y q).carrier) i
            = (6 : ℝ≥0∞) * ((6⁻¹ : ℝ≥0∞) *
                ∏ i ∈ Finset.range n, Metric.ethickness ℝ ((bd.Y q).carrier) i) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
        _ ≤ (6 : ℝ≥0∞) * volume ((bd.Y q).carrier) :=
          mul_le_mul_of_nonneg_left htemp' (by norm_num)
    calc
      volume ((bd.Y p).toConvexSpaceBody).carrier = volume ((bd.Y p).carrier) := rfl
      _ ≤ (2 : ℝ≥0∞) ^ (n : ℕ) * ∏ i ∈ Finset.range n,
            ENNReal.ofReal (Metric.thickness ℝ ((bd.Y p).carrier) i) := h_upper_p
      _ ≤ (2 : ℝ≥0∞) ^ (n : ℕ) * (((bd.C₀ : ℝ≥0∞) ^ 6) *
          ∏ i ∈ Finset.range n,
            ENNReal.ofReal (Metric.thickness ℝ ((bd.Y q).carrier) i)) := by gcongr
      _ = (2 : ℝ≥0∞) ^ (n : ℕ) * ((bd.C₀ : ℝ≥0∞) ^ 6) *
          ∏ i ∈ Finset.range n,
            ENNReal.ofReal (Metric.thickness ℝ ((bd.Y q).carrier) i) := by
        simp [mul_assoc]
      _ = (2 : ℝ≥0∞) ^ (n : ℕ) * ((bd.C₀ : ℝ≥0∞) ^ 6) *
          ∏ i ∈ Finset.range n, Metric.ethickness ℝ ((bd.Y q).carrier) i := by rw [h_ethick_q]
      _ ≤ (2 : ℝ≥0∞) ^ (n : ℕ) * ((bd.C₀ : ℝ≥0∞) ^ 6) *
          ((6 : ℝ≥0∞) * volume ((bd.Y q).carrier)) := by gcongr
      _ = (2 : ℝ≥0∞) ^ (n : ℕ) * (6 : ℝ≥0∞) *
          ((bd.C₀ : ℝ≥0∞) ^ 6) * volume ((bd.Y q).carrier) := by
        simp [mul_assoc, mul_comm, mul_left_comm]
      _ = (48 : ℝ≥0∞) * ((bd.C₀ : ℝ≥0∞) ^ 6) *
          volume ((bd.Y q).carrier) := by
        dsimp [n]
        norm_num
      _ = volCompConst * volume ((bd.Y q).toConvexSpaceBody).carrier := by
        simp [hvc_def]
  have hvol_comp : ∀ p ∈ block,
      volume (Vbody p).carrier ≤ volCompConst * volume T.carrier := by
    intro p hp
    have hp_seg : p ∈ bd.segs B := (Finset.mem_filter.mp hp).1
    simpa using segment_volume_comp p p₀ hp_seg hp₀
  have hsum_upper : ∑ p ∈ block, volume (Vbody p).carrier ≤
      (block.card : ℝ≥0∞) * (volCompConst * volume T.carrier) := by
    calc
      ∑ p ∈ block, volume (Vbody p).carrier
          ≤ ∑ p ∈ block, (volCompConst * volume T.carrier) :=
            Finset.sum_le_sum fun p hp => hvol_comp p hp
      _ = (block.card : ℝ≥0∞) * (volCompConst * volume T.carrier) := by simp
  have hA_mul_V :
      ((bd.Cbias : ℝ≥0∞)⁻¹ *
            (volume W.carrier / volume T.carrier) ^ cfg.ϱ) *
          volume W.carrier ≤
        ∑ p ∈ block, volume (Vbody p).carrier := by
    have htemp :
        ((bd.Cbias : ℝ≥0∞)⁻¹ *
              (volume W.carrier / volume T.carrier) ^ cfg.ϱ) *
            volume W.carrier ≤
          ((∑ p ∈ block, volume (Vbody p).carrier) / volume W.carrier) *
            volume W.carrier :=
      mul_le_mul_of_nonneg_right hdens_lower (by positivity : 0 ≤ volume W.carrier)
    have hcalc : ((∑ p ∈ block, volume (Vbody p).carrier) / volume W.carrier) * volume W.carrier =
        ∑ p ∈ block, volume (Vbody p).carrier := by
      calc
        ((∑ p ∈ block, volume (Vbody p).carrier) / volume W.carrier) * volume W.carrier
            = (∑ p ∈ block, volume (Vbody p).carrier) *
              ((volume W.carrier)⁻¹ * volume W.carrier) := by
              calc
                ((∑ p ∈ block, volume (Vbody p).carrier) / volume W.carrier) * volume W.carrier
                    = ((∑ p ∈ block, volume (Vbody p).carrier) *
                        (volume W.carrier)⁻¹) *
                      volume W.carrier := by
                  rw [div_eq_mul_inv]
                _ = (∑ p ∈ block, volume (Vbody p).carrier) *
                    ((volume W.carrier)⁻¹ * volume W.carrier) := by
                  rw [mul_assoc]
        _ = (∑ p ∈ block, volume (Vbody p).carrier) * 1 := by
          rw [ENNReal.inv_mul_cancel hW_ne_zero hWfinite]
        _ = ∑ p ∈ block, volume (Vbody p).carrier := by simp
    rw [hcalc] at htemp; exact htemp
  have h_combined :
      ((bd.Cbias : ℝ≥0∞)⁻¹ *
            (volume W.carrier / volume T.carrier) ^ cfg.ϱ) *
          volume W.carrier ≤
        (block.card : ℝ≥0∞) * (volCompConst * volume T.carrier) :=
    le_trans hA_mul_V hsum_upper
  set r := volume W.carrier / volume T.carrier with hr_def
  have h_r_V : r * volume T.carrier = volume W.carrier := by
    calc
      r * volume T.carrier = (volume W.carrier / volume T.carrier) * volume T.carrier := rfl
      _ = (volume W.carrier * (volume T.carrier)⁻¹) * volume T.carrier := by rw [div_eq_mul_inv]
      _ = volume W.carrier * ((volume T.carrier)⁻¹ * volume T.carrier) := by rw [mul_assoc]
      _ = volume W.carrier * 1 := by rw [ENNReal.inv_mul_cancel hT_ne_zero hTfinite]
      _ = volume W.carrier := by simp
  have h_r_ne_zero : r ≠ 0 := by
    intro hzero
    have : volume W.carrier = 0 := by
      calc
        volume W.carrier = r * volume T.carrier := Eq.symm h_r_V
        _ = 0 * volume T.carrier := by rw [hzero]
        _ = 0 := by simp
    exact hWpos.ne' this
  have h_r_finite : r ≠ ⊤ := by
    intro hinf
    have : volume W.carrier = ⊤ := by
      calc
        volume W.carrier = r * volume T.carrier := Eq.symm h_r_V
        _ = ⊤ * volume T.carrier := by rw [hinf]
        _ = ⊤ := by simp [hT_ne_zero]
    exact hWfinite this
  have hr_add : r ^ cfg.ϱ * r = r ^ (1 + cfg.ϱ) := by
    calc
      r ^ cfg.ϱ * r = r ^ cfg.ϱ * r ^ (1 : ℝ) := by simp
      _ = r ^ (cfg.ϱ + (1 : ℝ)) := by
        rw [← ENNReal.rpow_add (cfg.ϱ) (1 : ℝ) h_r_ne_zero h_r_finite]
      _ = r ^ (1 + cfg.ϱ) := by rw [add_comm]
  have h_combined' : ((bd.Cbias : ℝ≥0∞)⁻¹ * (r ^ cfg.ϱ * r)) * volume T.carrier ≤
      (block.card : ℝ≥0∞) * (volCompConst * volume T.carrier) := by
    calc
      ((bd.Cbias : ℝ≥0∞)⁻¹ * (r ^ cfg.ϱ * r)) * volume T.carrier
          = ((bd.Cbias : ℝ≥0∞)⁻¹ * r ^ cfg.ϱ) * (r * volume T.carrier) := by
            simp [mul_assoc, mul_comm, mul_left_comm]
      _ = ((bd.Cbias : ℝ≥0∞)⁻¹ *
            (volume W.carrier / volume T.carrier) ^ cfg.ϱ) *
          volume W.carrier := by
        rw [h_r_V, hr_def]
      _ ≤ (block.card : ℝ≥0∞) * (volCompConst * volume T.carrier) := h_combined
  have h_combined'' : ((bd.Cbias : ℝ≥0∞)⁻¹ * r ^ (1 + cfg.ϱ)) * volume T.carrier ≤
      (block.card : ℝ≥0∞) * (volCompConst * volume T.carrier) := by
    rw [← hr_add]; exact h_combined'
  have h_cancel :
      (bd.Cbias : ℝ≥0∞)⁻¹ * r ^ (1 + cfg.ϱ) ≤
        (block.card : ℝ≥0∞) * volCompConst := by
    have htemp : volume T.carrier * ((bd.Cbias : ℝ≥0∞)⁻¹ * r ^ (1 + cfg.ϱ)) ≤
      volume T.carrier * ((block.card : ℝ≥0∞) * volCompConst) := by
      calc
        volume T.carrier * ((bd.Cbias : ℝ≥0∞)⁻¹ * r ^ (1 + cfg.ϱ))
            = ((bd.Cbias : ℝ≥0∞)⁻¹ * r ^ (1 + cfg.ϱ)) * volume T.carrier := mul_comm _ _
        _ ≤ (block.card : ℝ≥0∞) * (volCompConst * volume T.carrier) := h_combined''
        _ = ((block.card : ℝ≥0∞) * volCompConst) * volume T.carrier := by
          simp [mul_assoc, mul_comm, mul_left_comm]
        _ = volume T.carrier * ((block.card : ℝ≥0∞) * volCompConst) := mul_comm _ _
    exact (ENNReal.mul_le_mul_iff_right hT_ne_zero hTfinite).mp htemp
  have h_final :
      volCompConst⁻¹ * ((bd.Cbias : ℝ≥0∞)⁻¹ * r ^ (1 + cfg.ϱ)) ≤
        (block.card : ℝ≥0∞) := by
    calc
      volCompConst⁻¹ * ((bd.Cbias : ℝ≥0∞)⁻¹ * r ^ (1 + cfg.ϱ))
          ≤ volCompConst⁻¹ * ((block.card : ℝ≥0∞) * volCompConst) :=
        mul_le_mul_of_nonneg_left h_cancel (by positivity)
      _ = (block.card : ℝ≥0∞) * (volCompConst⁻¹ * volCompConst) := by
        simp [mul_assoc, mul_comm, mul_left_comm]
      _ = (block.card : ℝ≥0∞) * 1 := by rw [ENNReal.inv_mul_cancel hD_ne_zero hD_finite]
      _ = (block.card : ℝ≥0∞) := by simp
  calc
    (((48 * bd.C₀ ^ 6 * bd.Cbias : ℝ≥0) : ℝ≥0∞))⁻¹ * r ^ (1 + cfg.ϱ)
        = ((volCompConst * (bd.Cbias : ℝ≥0∞))⁻¹) * r ^ (1 + cfg.ϱ) := by
          simp [volCompConst, hvc_def]
    _ = (volCompConst⁻¹ * (bd.Cbias : ℝ≥0∞)⁻¹) * r ^ (1 + cfg.ϱ) := by
        rw [ENNReal.mul_inv (Or.inl hD_ne_zero) (Or.inl hD_finite)]
    _ = volCompConst⁻¹ * ((bd.Cbias : ℝ≥0∞)⁻¹ * r ^ (1 + cfg.ϱ)) := by simp [mul_assoc]
    _ ≤ (block.card : ℝ≥0∞) := h_final
    _ = (((bd.segs B).filter fun p => bd.blk p = bd.blk p₀).card : ℝ≥0∞) := rfl

private lemma exists_nat_between {t : ℝ} {N : ℕ} (h0 : 0 ≤ t) (hN : t ≤ (N : ℝ))
    (hNpos : 0 < N) : ∃ m : ℕ, m < N ∧ (m : ℝ) ≤ t ∧ t ≤ (m : ℝ) + 1 := by
  by_cases htN : t < (N : ℝ)
  · let m : ℕ := Nat.floor t
    have hm_le : (m : ℝ) ≤ t := Nat.floor_le h0
    have hm_lt : m < N := (Nat.floor_lt h0).mpr htN
    have ht_m1 : t ≤ (m : ℝ) + 1 := le_of_lt (Nat.lt_floor_add_one t)
    exact ⟨m, hm_lt, hm_le, ht_m1⟩
  · have hN_le_t : (N : ℝ) ≤ t := le_of_not_gt htN
    have ht_eq : t = (N : ℝ) := le_antisymm hN hN_le_t
    let m : ℕ := N - 1
    have hm_lt : m < N := Nat.sub_lt hNpos (by simp)
    have hm_le : (m : ℝ) ≤ t := by
      rw [ht_eq]
      exact_mod_cast (Nat.sub_le N 1)
    have ht_m1 : t ≤ (m : ℝ) + 1 := by
      rw [ht_eq]
      have hsucc : (N - 1 : ℕ) + 1 = N := Nat.sub_add_cancel (Nat.succ_le_of_lt hNpos)
      have hc : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by exact_mod_cast hsucc
      rw [← hc]
    exact ⟨m, hm_lt, hm_le, ht_m1⟩

private lemma exists_cell_index {s τ u : ℝ} (hs : 0 < s) (hτ : 0 < τ) (hu : |u| ≤ τ) :
    ∃ m : ℕ, m < Nat.ceil (2 * τ / s) ∧
      (u + τ) ∈ Set.Icc ((m : ℝ) * s) (((m : ℝ) + 1) * s) := by
  have hu_pos : 0 ≤ u + τ := by
    have h1 := (abs_le.mp hu).1
    linarith
  let t : ℝ := (u + τ) / s
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have hM_ge' : 2 * τ / s ≤ (Nat.ceil (2 * τ / s) : ℝ) := by
    exact (Nat.ceil_le (a := 2 * τ / s) (n := Nat.ceil (2 * τ / s))).mp (by rfl)
  have ht_le : t ≤ (Nat.ceil (2 * τ / s) : ℝ) := by
    calc
      (u + τ) / s ≤ (2 * τ) / s := by
        exact div_le_div_of_nonneg_right (by linarith [(abs_le.mp hu).2]) hs.le
      _ ≤ (Nat.ceil (2 * τ / s) : ℝ) := hM_ge'
  have hMpos : 0 < Nat.ceil (2 * τ / s) := by
    exact (Nat.one_le_ceil_iff).mpr (by positivity)
  obtain ⟨m, hm_lt, hm_le, ht_m1⟩ := exists_nat_between ht0 ht_le hMpos
  refine ⟨m, hm_lt, ?_, ?_⟩
  · calc
      (m : ℝ) * s ≤ t * s := mul_le_mul_of_nonneg_right hm_le hs.le
      _ = u + τ := by
        dsimp [t]
        field_simp
  · calc
      u + τ = t * s := by
        dsimp [t]
        field_simp
      _ ≤ ((m : ℝ) + 1) * s := mul_le_mul_of_nonneg_right ht_m1 hs.le

private noncomputable def gridOf (a : ℝ) (τ : Fin 3 → ℝ) : Finset (EuclideanSpace ℝ (Fin 3)) :=
  let s : ℝ := a / Real.sqrt 3
  Finset.univ.image (fun m : (i : Fin 3) → Fin (Nat.ceil (2 * τ i / s)) =>
    WithLp.toLp 2 (fun i => -τ i + (m i : ℝ) * s + s / 2))

private lemma grid_cover (a : ℝ) {C₀ : ℝ} (ha : 0 < a) (hC₀ : 1 ≤ C₀) :
    ∀ (τ : Fin 3 → ℝ), (∀ i, 0 < τ i) → (∀ i, C₀⁻¹ * a ≤ τ i) →
      (∀ x : EuclideanSpace ℝ (Fin 3), (∀ i, |x i| ≤ τ i) → ∃ c ∈ gridOf a τ, dist x c < a) ∧
      (((gridOf a τ).card : ℝ) * a ^ 3 ≤ (2 * Real.sqrt 3 + C₀) ^ 3 * ∏ i, τ i) := by
  intro τ hτ hτa
  let s : ℝ := a / Real.sqrt 3
  have hs : 0 < s := by dsimp [s]; positivity
  let M : Fin 3 → ℕ := fun i => Nat.ceil (2 * τ i / s)
  have hsM : gridOf a τ = Finset.univ.image (fun m : (i : Fin 3) → Fin (M i) =>
      WithLp.toLp 2 (fun i => -τ i + (m i : ℝ) * s + s / 2)) := by
    dsimp [gridOf, s, M]
  have hcard : (gridOf a τ).card ≤ (∏ i : Fin 3, (M i : ℕ)) := by
    calc
      (gridOf a τ).card ≤ ((Finset.univ : Finset (∀ i : Fin 3, Fin (M i))).card) := by
        rw [hsM]
        exact Finset.card_image_le
      _ = ∏ i : Fin 3, (M i : ℕ) := by
        simp
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have h1 : ∀ i, (1 : ℝ) ≤ C₀ * τ i / a := by
    intro i
    rw [le_div_iff₀ ha]
    have hA : a ≤ C₀ * τ i := by
      have h := hτa i
      calc
        a = C₀ * (C₀⁻¹ * a) := by field_simp [hC₀pos.ne']
        _ ≤ C₀ * τ i := mul_le_mul_of_nonneg_left h (by linarith)
    simpa using hA
  have hM_le : ∀ i, (M i : ℝ) ≤ (2 * Real.sqrt 3 + C₀) * τ i / a := by
    intro i
    have hc : (1 : ℝ) ≤ C₀ * τ i / a := h1 i
    have hnonneg : 0 ≤ 2 * τ i / s :=
      div_nonneg (mul_nonneg (by norm_num) (le_of_lt (hτ i))) (le_of_lt hs)
    have h_sq : 2 * τ i / s = 2 * Real.sqrt 3 * τ i / a := by
      dsimp [s]
      field_simp
    calc
      (M i : ℝ) ≤ 2 * τ i / s + 1 := by
        exact le_of_lt (by simpa [M] using Nat.ceil_lt_add_one hnonneg)
      _ = (2 * Real.sqrt 3 * τ i / a) + 1 := by rw [h_sq]
      _ ≤ (2 * Real.sqrt 3 + C₀) * τ i / a := by
        calc
          (2 * Real.sqrt 3 * τ i / a) + 1 ≤ (2 * Real.sqrt 3 * τ i + C₀ * τ i) / a := by
            rw [add_div]
            exact add_le_add_right hc (2 * Real.sqrt 3 * τ i / a)
          _ = (2 * Real.sqrt 3 + C₀) * τ i / a := by ring
  have hM_nonneg : ∀ i, (0 : ℝ) ≤ (M i : ℝ) := by
    intro i
    exact_mod_cast (Nat.zero_le (M i))
  have hprodA : (∏ i : Fin 3, (2 * Real.sqrt 3 + C₀) * τ i / a) =
      ((2 * Real.sqrt 3 + C₀) ^ 3 * ∏ i, τ i) / a ^ 3 := by
    calc
      (∏ i : Fin 3, (2 * Real.sqrt 3 + C₀) * τ i / a)
          = (∏ i : Fin 3, (2 * Real.sqrt 3 + C₀) * τ i) * ∏ i : Fin 3, a⁻¹ := by
            rw [← Finset.prod_mul_distrib]
            apply Finset.prod_congr rfl
            intro i hi
            field_simp
      _ = ((2 * Real.sqrt 3 + C₀) ^ 3 * ∏ i, τ i) * (a⁻¹) ^ 3 := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const]
        simp [mul_comm, mul_left_comm]
      _ = ((2 * Real.sqrt 3 + C₀) ^ 3 * ∏ i, τ i) / a ^ 3 := by
        field_simp
  have hprod : (∏ i : Fin 3, (M i : ℝ)) * a ^ 3 ≤ (2 * Real.sqrt 3 + C₀) ^ 3 * ∏ i, τ i := by
    calc
      (∏ i : Fin 3, (M i : ℝ)) * a ^ 3
          ≤ (∏ i : Fin 3, (2 * Real.sqrt 3 + C₀) * τ i / a) * a ^ 3 := by
            have hle : ∏ i : Fin 3, (M i : ℝ) ≤ ∏ i : Fin 3, (2 * Real.sqrt 3 + C₀) * τ i / a := by
              exact Finset.prod_le_prod (fun i _ => hM_nonneg i) (fun i _ => hM_le i)
            exact mul_le_mul_of_nonneg_right hle (by positivity)
      _ = (2 * Real.sqrt 3 + C₀) ^ 3 * ∏ i, τ i := by
        rw [hprodA]
        field_simp
  refine ⟨?_, ?_⟩
  · intro x hxb
    have hcells : ∀ i, ∃ m : ℕ, m < M i ∧
        (x i + τ i) ∈ Set.Icc ((m : ℝ) * s) (((m : ℝ) + 1) * s) := by
      intro i
      exact exists_cell_index hs (hτ i) (hxb i)
    let mfunc : (i : Fin 3) → Fin (M i) := fun i => ⟨(hcells i).choose, (hcells i).choose_spec.1⟩
    let c : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (fun i => -τ i + (mfunc i : ℝ) * s + s / 2)
    refine ⟨c, ?_, ?_⟩
    · rw [hsM]
      refine Finset.mem_image.mpr ⟨mfunc, Finset.mem_univ _, rfl⟩
    · have hcoord : ∀ i, ‖(x - c) i‖ ≤ s / 2 := by
        intro i
        have hcell := (hcells i).choose_spec.2
        rw [Set.mem_Icc] at hcell
        have hlo : (mfunc i : ℝ) * s ≤ x i + τ i := hcell.1
        have hhi : x i + τ i ≤ ((mfunc i : ℝ) + 1) * s := hcell.2
        have hcoord_eq : (x - c) i = (x i + τ i) - ((mfunc i : ℝ) + 1 / 2) * s := by
          simp only [PiLp.sub_apply, c]
          rw [WithLp.ofLp_toLp]
          ring
        have habs : |(x i + τ i) - ((mfunc i : ℝ) + 1 / 2) * s| ≤ s / 2 := by
          rw [abs_le]
          constructor <;> nlinarith
        rw [Real.norm_eq_abs, hcoord_eq]
        exact habs
      have hy2 : (∑ i : Fin 3, ‖(x - c) i‖ ^ 2) ≤ ∑ _i : Fin 3, (s / 2) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact pow_le_pow_left₀ (norm_nonneg _) (hcoord i) 2
      have hy' : ‖x - c‖ ≤ a / 2 := by
        rw [EuclideanSpace.norm_eq]
        rw [Real.sqrt_le_iff]
        constructor
        · positivity
        · calc
            (∑ i : Fin 3, ‖(x - c) i‖ ^ 2) ≤ ∑ _i : Fin 3, (s / 2) ^ 2 := hy2
            _ = 3 * (s / 2) ^ 2 := by simp
            _ = (a / 2) ^ 2 := by
              dsimp [s]
              field_simp
              rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      have hlt : a / 2 < a := by linarith
      rw [dist_eq_norm]
      exact lt_of_le_of_lt hy' hlt
  · have hcount : ((gridOf a τ).card : ℝ) * a ^ 3 ≤ (2 * Real.sqrt 3 + C₀) ^ 3 * ∏ i, τ i := by
      calc
        ((gridOf a τ).card : ℝ) * a ^ 3 ≤ (∏ i : Fin 3, (M i : ℝ)) * a ^ 3 := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
        _ ≤ (2 * Real.sqrt 3 + C₀) ^ 3 * ∏ i, τ i := hprod
    exact hcount

/-- The `Fin 3` product of thicknesses equals the `Finset.range 3` product used by
`Convex.prod_thickness_le_volumeReal`. -/
private lemma fin3_thickness_prod (s : Set (EuclideanSpace ℝ (Fin 3))) :
    (∏ i : Fin 3, Metric.thickness ℝ s (i : ℕ)) =
      ∏ i ∈ Finset.range 3, Metric.thickness ℝ s i := by
  exact Fin.prod_univ_eq_prod_range (fun i : ℕ => Metric.thickness ℝ s i) 3

/-- Four-factor reassociation in a commutative monoid: `a*b*c*d = a*c*(b*d)`. -/
private lemma four_mul_reassoc {α : Type*} [CommMonoid α] (a b c d : α) :
    a * b * c * d = a * c * (b * d) := by
  simp [mul_comm, mul_left_comm]

/-- From `K * P * Cs ≤ M * A * Q`, cancel the nonzero finite `Cs` by multiplying through by
`Cs⁻¹` on the right: `K * P ≤ M * Q * (A / Cs)`. -/
private lemma mul_le_div_cancel {K P Cs M A Q : ℝ≥0∞} (hCs0 : Cs ≠ 0) (hCsT : Cs ≠ ⊤)
    (h : K * P * Cs ≤ M * A * Q) : K * P ≤ M * Q * (A / Cs) := by
  have hm : (K * P * Cs) * Cs⁻¹ ≤ (M * A * Q) * Cs⁻¹ :=
    mul_le_mul_of_nonneg_right h (by simp)
  calc
    K * P = (K * P * Cs) * Cs⁻¹ := by
      symm
      rw [mul_assoc, ENNReal.mul_inv_cancel hCs0 hCsT, mul_one]
    _ ≤ (M * A * Q) * Cs⁻¹ := hm
    _ = M * Q * (A / Cs) := by
      rw [ENNReal.div_eq_inv_mul]
      ring

/-- **From a density inside a factoring body to the density form of the goal** (blueprint
`lem:ml2thickBallDensity`, the second half of the old `lem:ml2thickDensity`: the passage from
`denseInsideWexplicit` to `eqgoaldensexplicit`).

Given a ball `B ∈ 𝔅` and a body `W ∈ 𝕎_B` in which the shaded union of the block `𝕋_{B,W}`
is dense at the explicit constant `K C_{lem:ml2thickBallSelect}(C₀)`,

`K C_{lem:ml2thickBallSelect}(C₀) δ^{2β} |W| ≤ δ^{2ν} |U(𝕋_{B,W}, Y_B) ∩ W| a^{2β}`,

the pair `(𝕋, Y)` satisfies the density form of the goal at the constant `K` and the same
gain `ν`, i.e. `Kakeya.VeryNotSticky.goalDensity K ν`.

Both the constant `K` and the gain `ν` are arbitrary: nothing in the argument uses their
values, and in particular no parameter budget, no thickness hypothesis and no admissibility
of `K` is needed. The caller — `Kakeya.VeryNotSticky.goalMult_of_a_ge` — instantiates it at
`K = C ^ 2` for the `C` produced by
`Kakeya.VeryNotSticky.goalMult_of_a_ge_of_goalDensity` and at the thick-case gain
`ν = ϱ β τ / 8` of blueprint `def:ml2thickGain`.

The ball-selection constant of blueprint `def:ml2thickBallSelectConstant`,
`C_{lem:ml2thickBallSelect}(C₀) = 8π(2√3 + C₀)³`, is written out inline as an
`ENNReal.ofReal`; it pays for the passage from a density in the body `W` to a density in an
`a`-ball, which is blueprint `lem:ml2thickBallSelect` — pure convex geometry, proved by
covering the outer prism of `W` by a grid of cubes of side `a/√3` and pigeonholing. Its
hypothesis is the comparability `τ₂(W) ≥ C₀⁻¹ a` of (C4), i.e.
`Kakeya.VeryNotSticky.BallData.bodies_thickness`. That lemma is not formalized separately.

The remaining step is the chain of containments `U(𝕋_{B,W}, Y_B) ∩ W ⊆ U(𝕋, Y)`: the block is
a subfamily of `𝕋_B`, and the per-ball shading is dominated by the global one through
`Kakeya.VeryNotSticky.BallData.back` of (C5), read on the working shading, and
`Kakeya.VeryNotSticky.BallData.Yg_subset`. -/
theorem goalDensity_of_denseInBody (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
    {K : ℝ≥0∞} {ν : ℝ}
    (hdense : ∃ B ∈ bd.bs, ∃ j ∈ bd.bodies B,
      K * ENNReal.ofReal (8 * Real.pi * (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3) *
          (cfg.δ : ℝ≥0∞) ^ (2 * cfg.β) * volume (bd.Wb j).carrier ≤
        (cfg.δ : ℝ≥0∞) ^ (2 * ν) *
          volume ((⋃ p ∈ (bd.segs B).filter fun p => bd.blk p = j, (bd.Y p).shade) ∩
            (bd.Wb j).carrier) *
          (cfg.a : ℝ≥0∞) ^ (2 * cfg.β)) :
    cfg.goalDensity K cfg.a ν := by
  rcases hdense with ⟨B, hB, j, hj, hdense_main⟩
  let E := EuclideanSpace ℝ (Fin 3)
  let s : Set E := (bd.Wb j).carrier
  -- basic positivity and finiteness of the configuration numbers
  have hβpos : 0 < cfg.β := cfg.hβ
  have hfinrank : Module.finrank ℝ E = 3 := by simp [E]
  have hδ_real : 0 < (cfg.δ : ℝ) := by exact_mod_cast cfg.hδ
  have ha_real : 0 < (cfg.a : ℝ) := by
    have hδa : (cfg.δ : ℝ) ≤ (cfg.a : ℝ) := by exact_mod_cast cfg.hdims.1
    linarith
  have hC₀_real : 0 < (bd.C₀ : ℝ) := by
    have hc : (1 : ℝ) ≤ (bd.C₀ : ℝ) := by exact_mod_cast bd.hC₀
    linarith
  have hC₀_ge1 : (1 : ℝ) ≤ (bd.C₀ : ℝ) := by exact_mod_cast bd.hC₀
  -- the outer prism of the body and its orthonormal basis (an isometry)
  let P : PrismNDim 3 E E :=
    outerPrism hfinrank (s := s)
      (hs := (bd.Wb j).isCompact) (hsne := (bd.Wb j).nonempty)
  let φ : E ≃ₗᵢ[ℝ] E := P.basis.repr
  have hs_sub_prism : s ⊆ P.carrier :=
    outerPrism.self_subset hfinrank (bd.Wb j).isCompact (bd.Wb j).nonempty
  -- the axis-aligned half-widths of the prism are exactly the thicknesses
  have hthick_prism : ∀ k : Fin 3, (P.thicknesses k : ℝ) = Metric.thickness ℝ s k := by
    intro k
    rw [outerPrism.thicknesses_eq hfinrank (bd.Wb j).isCompact (bd.Wb j).nonempty k]
    rfl
  -- thickness lower bounds: `C₀⁻¹ a ≤ τ k` for every k
  let t : Fin 3 → ℝ := ![(cfg.r₁ : ℝ), (cfg.b : ℝ), (cfg.a : ℝ)]
  let τ : Fin 3 → ℝ := fun k => Metric.thickness ℝ s k
  have hthick : HasThicknesses s bd.C₀ t := bd.bodies_thickness B hB j hj
  have hτa : ∀ k : Fin 3, (bd.C₀ : ℝ)⁻¹ * (cfg.a : ℝ) ≤ τ k := by
    intro k
    have htk_le : (cfg.a : ℝ) ≤ t k := by
      fin_cases k
      · simp only [t, Nat.reduceAdd, Fin.zero_eta, Fin.isValue]
        have hab : (cfg.a : ℝ) ≤ (cfg.b : ℝ) := by exact_mod_cast cfg.hdims.2.1
        have hbr : (cfg.b : ℝ) ≤ (cfg.r₁ : ℝ) := by
          dsimp [r₁]
          exact_mod_cast cfg.hdims.2.2
        exact le_trans hab hbr
      · simp only [t, Nat.reduceAdd, Fin.mk_one, Fin.isValue]
        exact_mod_cast cfg.hdims.2.1
      · exact le_rfl
    rcases hthick k with ⟨hlo, _⟩
    calc
      (bd.C₀ : ℝ)⁻¹ * (cfg.a : ℝ) ≤ (bd.C₀ : ℝ)⁻¹ * t k :=
        mul_le_mul_of_nonneg_left htk_le (inv_nonneg.mpr hC₀_real.le)
      _ ≤ Metric.thickness ℝ s k := hlo
  have hτpos : ∀ k : Fin 3, 0 < τ k := by
    intro k
    have hpos : 0 < (bd.C₀ : ℝ)⁻¹ * (cfg.a : ℝ) := by positivity
    exact lt_of_lt_of_le hpos (hτa k)
  -- the grid covering the coordinate box, together with its counting bound
  have hgrid := grid_cover (a := (cfg.a : ℝ)) (C₀ := (bd.C₀ : ℝ)) ha_real hC₀_ge1
    (τ := τ) hτpos hτa
  let G : Finset E := gridOf (cfg.a : ℝ) τ
  -- ambient grid centres: translate the coordinate grid back by the isometry
  let gm : E → E := fun c => P.center +ᵥ φ.symm c
  -- the body (in the prism) is covered by the ambient a-balls
  have hcover_s : s ⊆ ⋃ c ∈ G, Metric.ball (gm c) (cfg.a : ℝ) := by
    intro x hx
    have hxp : x ∈ P.carrier := hs_sub_prism hx
    rw [PrismNDim.mem_carrier_iff] at hxp
    have hbox : ∀ i : Fin 3, |φ (x -ᵥ P.center) i| ≤ τ i := by
      intro i
      have hi := hxp i
      rw [hthick_prism i] at hi
      exact hi
    rcases hgrid.1 (φ (x -ᵥ P.center)) hbox with ⟨c, hcG, hdist⟩
    apply Set.mem_iUnion₂.mpr
    refine ⟨c, ?hcG, ?_⟩
    · simpa [G] using hcG
    · simp only [Metric.mem_ball]
      -- `dist x (P.center +ᵥ φ.symm c) < a`; transport the isometry
      have hφeq : φ (x - (P.center +ᵥ φ.symm c)) = φ (x -ᵥ P.center) - c := by
        rw [vadd_eq_add, vsub_eq_sub, ← sub_sub]
        rw [map_sub, map_sub]
        rw [φ.apply_symm_apply]
      have htr : dist x (P.center +ᵥ φ.symm c) = dist (φ (x -ᵥ P.center)) c := by
        rw [dist_eq_norm, dist_eq_norm]
        calc
          ‖x - (P.center +ᵥ φ.symm c)‖ = ‖φ (x - (P.center +ᵥ φ.symm c))‖ :=
            (φ.norm_map _).symm
          _ = ‖φ (x -ᵥ P.center) - c‖ := by
            exact congrArg (Norm.norm : E → ℝ) hφeq
      change dist x (P.center +ᵥ φ.symm c) < (cfg.a : ℝ)
      rwa [htr]
  -- the block shade `Z` is covered by the intersection with the balls
  set Z : Set E := ⋃ p ∈ (bd.segs B).filter (fun p => bd.blk p = j), (bd.Y p).shade with hZ
  have hcover_Z : Z ∩ s ⊆ ⋃ c ∈ G, (Z ∩ Metric.ball (gm c) (cfg.a : ℝ)) := by
    intro x hx
    have hxZ : x ∈ Z := hx.1
    have hxs : x ∈ s := hx.2
    rcases Set.mem_iUnion₂.mp (hcover_s hxs) with ⟨c, hcG, hxball⟩
    exact Set.mem_iUnion₂.mpr ⟨c, hcG, (by exact ⟨hxZ, hxball⟩)⟩
  -- the shaded union is upgraded to the global one
  set Sg : Set E := ⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade with hSg
  have hZ_sub_sg : Z ⊆ Sg := by
    intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨p, hp, hxY⟩
    have hp_seg : p ∈ bd.segs B := (Finset.mem_filter.mp hp).1
    have hback := bd.back B hB p hp_seg
    rcases Set.mem_iUnion₂.mp (hback hxY) with ⟨i, hi, hxTi⟩
    refine Set.mem_iUnion₂.mpr ⟨i, ?_, ?_⟩
    · exact (bd.fam_subset B hB p hp_seg) hi
    · simpa using bd.Yg_subset i (bd.fam_subset B hB p hp_seg hi) hxTi
  -- volumes: `A ≤ ∑ c, |Z ∩ ball|` and the grid-count bound
  set svol : ℝ≥0∞ := volume s with hsvol
  set A : ℝ≥0∞ := volume (Z ∩ s) with hA
  set C : ℝ≥0∞ := ENNReal.ofReal (8 * Real.pi * (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3) with hC
  set V : ℝ≥0∞ := volume (ball (0 : E) (cfg.a : ℝ)) with hV_def
  set δe : ℝ≥0∞ := (cfg.δ : ℝ≥0∞) with hδe
  set ae : ℝ≥0∞ := (cfg.a : ℝ≥0∞) with hae
  have hvol_one : ∀ c : E, volume (ball c (cfg.a : ℝ)) = V := by
    intro c
    dsimp [V]
    rw [EuclideanSpace.volume_ball_fin_three c (cfg.a : ℝ),
      EuclideanSpace.volume_ball_fin_three (0 : E) (cfg.a : ℝ)]
  have hA_le_sum : A ≤ ∑ c ∈ G, volume (Z ∩ ball (gm c) (cfg.a : ℝ)) := by
    calc
      A = volume (Z ∩ s) := rfl
      _ ≤ volume (⋃ c ∈ G, (Z ∩ ball (gm c) (cfg.a : ℝ))) :=
        MeasureTheory.measure_mono hcover_Z
      _ ≤ ∑ c ∈ G, volume (Z ∩ ball (gm c) (cfg.a : ℝ)) :=
        MeasureTheory.measure_biUnion_finset_le G (fun c => Z ∩ ball (gm c) (cfg.a : ℝ))
  -- the volume of a single a-ball
  have hV : V = ENNReal.ofReal ((cfg.a : ℝ) ^ 3) * ENNReal.ofReal (Real.pi * 4 / 3) := by
    dsimp [V]
    rw [EuclideanSpace.volume_ball_fin_three]
    rw [(ENNReal.ofReal_pow (le_of_lt ha_real) 3).symm]
  have hC_expand : C = (6 : ℝ≥0∞) * ENNReal.ofReal (Real.pi * 4 / 3) *
      ENNReal.ofReal ((2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3) := by
    rw [hC]
    rw [show (6 : ℝ≥0∞) = ENNReal.ofReal (6 : ℝ) by exact (ENNReal.ofReal_ofNat 6).symm]
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  -- the body volume is finite and positive
  have hvol_le_top : volume s ≠ ⊤ := by
    have hle : volume s ≤ ((8 * bd.C₀ ^ 3 * cfg.r₁ * cfg.b * cfg.a : ℝ≥0) : ℝ≥0∞) := by
      simpa [s] using (thickBodyVol cfg bd hB hj).2
    exact (hle.trans_lt ENNReal.coe_lt_top).ne
  have hvol_finite : volume s < ⊤ := lt_top_iff_ne_top.mpr hvol_le_top
  have hconv_s : Convex ℝ s := (bd.Wb j).convex
  have hbdd_s : Bornology.IsBounded s := (bd.Wb j).isCompact.isBounded
  have hvol_real_pos : 0 < MeasureTheory.volume.real s := by
    have hfin : Module.finrank ℝ E = 3 := hfinrank
    have hprod := Convex.prod_thickness_le_volumeReal (K := s) (h1 := hconv_s) (h2 := hbdd_s)
    rw [hfin] at hprod
    have hc3 : (lt_volume_convexHull.c 3 : ℝ) = (1 / 6 : ℝ) := by
      norm_num [lt_volume_convexHull.c]
    have hprod' : (1 / 6 : ℝ) * ∏ i : Fin 3, τ i ≤ MeasureTheory.volume.real s := by
      simpa [τ, hc3, (fin3_thickness_prod s).symm] using hprod
    have hprod_pos : 0 < (1 / 6 : ℝ) * ∏ i : Fin 3, τ i := by
      exact mul_pos (by norm_num) (Finset.prod_pos (fun i _ => hτpos i))
    linarith
  have hvol_pos : 0 < volume s := by
    have hto : ENNReal.ofReal (MeasureTheory.volume.real s) = volume s := by
      exact (ENNReal.ofReal_toReal_eq_iff).mpr hvol_le_top
    rw [← hto]
    exact ENNReal.ofReal_pos.mpr hvol_real_pos
  have hvol_real_eq : ENNReal.ofReal (MeasureTheory.volume.real s) = volume s := by
    exact (ENNReal.ofReal_toReal_eq_iff).mpr hvol_le_top
  -- the grid-count bound: `(G.card : ENNReal) * V ≤ C * svol`
  have hcard_le : (G.card : ℝ≥0∞) * V ≤ C * svol := by
    have hcv :
        (G.card : ℝ) * (cfg.a : ℝ) ^ 3 ≤
          (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3 * ∏ i, τ i := hgrid.2
    have hcvE : ENNReal.ofReal ((G.card : ℝ) * (cfg.a : ℝ) ^ 3) ≤
        ENNReal.ofReal ((2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3 * ∏ i, τ i) := by
      exact ENNReal.ofReal_le_ofReal hcv
    have hprod_le : ∏ i, τ i ≤ 6 * MeasureTheory.volume.real s := by
      have hfin : Module.finrank ℝ E = 3 := hfinrank
      have hprod := Convex.prod_thickness_le_volumeReal (K := s) (h1 := hconv_s) (h2 := hbdd_s)
      rw [hfin] at hprod
      have hc3 : (lt_volume_convexHull.c 3 : ℝ) = (1 / 6 : ℝ) := by
        norm_num [lt_volume_convexHull.c]
      have hprod' : (1 / 6 : ℝ) * ∏ i : Fin 3, τ i ≤ MeasureTheory.volume.real s := by
        simpa [τ, hc3, (fin3_thickness_prod s).symm] using hprod
      nlinarith
    have hprodE : ENNReal.ofReal (∏ i, τ i) ≤ (6 : ℝ≥0∞) * svol := by
      calc
        ENNReal.ofReal (∏ i, τ i) ≤ ENNReal.ofReal (6 * MeasureTheory.volume.real s) :=
          ENNReal.ofReal_le_ofReal hprod_le
        _ = (6 : ℝ≥0∞) * ENNReal.ofReal (MeasureTheory.volume.real s) := by
              rw [ENNReal.ofReal_mul (by norm_num)]
              norm_num [ENNReal.ofReal_ofNat]
        _ = (6 : ℝ≥0∞) * svol := by simp [hvol_real_eq, svol]
    have hnat : (G.card : ℝ≥0∞) = ENNReal.ofReal (G.card : ℝ) :=
      (ENNReal.ofReal_natCast G.card).symm
    calc
      (G.card : ℝ≥0∞) * V
          = ENNReal.ofReal ((G.card : ℝ) * (cfg.a : ℝ) ^ 3) *
              ENNReal.ofReal (Real.pi * 4 / 3) := by
            rw [hV]
            rw [hnat]
            rw [← mul_assoc]
            rw [← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal ((2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3 * ∏ i, τ i) *
          ENNReal.ofReal (Real.pi * 4 / 3) := by
            gcongr
      _ ≤ (6 : ℝ≥0∞) * ENNReal.ofReal (Real.pi * 4 / 3) *
          ENNReal.ofReal ((2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3) * svol := by
            have hprodE' : ENNReal.ofReal (∏ i, τ i) ≤ (6 : ℝ≥0∞) * svol := hprodE
            calc
              ENNReal.ofReal ((2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3 * ∏ i, τ i) *
                  ENNReal.ofReal (Real.pi * 4 / 3)
                  = ENNReal.ofReal ((2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3) *
                      (ENNReal.ofReal (∏ i, τ i) * ENNReal.ofReal (Real.pi * 4 / 3)) := by
                        rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
              _ ≤ ENNReal.ofReal ((2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3) *
                  ((6 : ℝ≥0∞) * svol * ENNReal.ofReal (Real.pi * 4 / 3)) := by
                        gcongr
              _ = (6 : ℝ≥0∞) * ENNReal.ofReal (Real.pi * 4 / 3) *
                  ENNReal.ofReal ((2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3) * svol := by
                        ring_nf
      _ = C * svol := by
            rw [← hC_expand]
  -- the pigeonhole: some ball captures a proportional share
  have hG_nonempty : G.Nonempty := by
    rcases hgrid.1 (0 : E) (by intro i; simpa using (hτpos i).le) with ⟨c, hc, _⟩
    exact ⟨c, hc⟩
  let α : ℝ≥0∞ := A / (C * svol)
  have hCs_ne : C * svol ≠ 0 := by
    have hC_pos : 0 < C := by
      dsimp [C]
      exact ENNReal.ofReal_pos.mpr (by positivity)
    exact mul_ne_zero (ne_of_gt hC_pos) (ne_of_gt hvol_pos)
  have hCs_top : C * svol ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by simp [C]) hvol_le_top
  have hsum_pigeonhole : ∑ c ∈ G, (α * V) ≤ ∑ c ∈ G, volume (Z ∩ ball (gm c) (cfg.a : ℝ)) := by
    have hαV : α * (C * svol) = A := by
      dsimp [α]
      exact ENNReal.div_mul_cancel hCs_ne hCs_top
    calc
      ∑ c ∈ G, (α * V) = (G.card : ℝ≥0∞) * (α * V) := by
        rw [Finset.sum_const]
        simp
      _ = α * ((G.card : ℝ≥0∞) * V) := by
        ring
      _ ≤ α * (C * svol) := by
        exact mul_le_mul_of_nonneg_left hcard_le (by simp)
      _ = A := hαV
      _ ≤ ∑ c ∈ G, volume (Z ∩ ball (gm c) (cfg.a : ℝ)) := hA_le_sum
  obtain ⟨c, hcG, hbc⟩ := ENNReal.exists_le_of_sum_le hG_nonempty hsum_pigeonhole
  have hcV : α * V ≤ volume (Z ∩ ball (gm c) (cfg.a : ℝ)) := hbc
  -- from `hdense_main` (rearranged): `K δ^(2β) ≤ δ^(2ν) a^(2β) * A / (C * svol)`
  have hdense_main' :
      K * δe ^ (2 * cfg.β) ≤
        δe ^ (2 * ν) * ae ^ (2 * cfg.β) * (A / (C * svol)) := by
    have hreassoc :
        K * C * δe ^ (2 * cfg.β) * svol = K * δe ^ (2 * cfg.β) * (C * svol) :=
      four_mul_reassoc K C (δe ^ (2 * cfg.β)) svol
    have h' :
        K * δe ^ (2 * cfg.β) * (C * svol) ≤
          δe ^ (2 * ν) * A * ae ^ (2 * cfg.β) := by
      rw [← hreassoc]
      simpa [hC, hδe, hA, hsvol, hae, hZ] using hdense_main
    exact mul_le_div_cancel hCs_ne hCs_top h'
  -- assemble the per-ball inequality
  have hZball_le :
      volume (Z ∩ ball (gm c) (cfg.a : ℝ)) ≤
        volume (Sg ∩ ball (gm c) (cfg.a : ℝ)) := by
    apply MeasureTheory.measure_mono
    intro x hx
    exact ⟨hZ_sub_sg hx.1, hx.2⟩
  have hgoal_c : K * δe ^ (2 * cfg.β) * V ≤
      δe ^ (2 * ν) * volume (Sg ∩ ball (gm c) (cfg.a : ℝ)) * ae ^ (2 * cfg.β) := by
    calc
      K * δe ^ (2 * cfg.β) * V
          ≤ δe ^ (2 * ν) * ae ^ (2 * cfg.β) * (A / (C * svol)) * V := by
            exact mul_le_mul_of_nonneg_right hdense_main' (by simp)
      _ = δe ^ (2 * ν) * ae ^ (2 * cfg.β) * (α * V) := by
        dsimp [α]
        ring
      _ = δe ^ (2 * ν) * (α * V) * ae ^ (2 * cfg.β) := by
        ring
      _ ≤ δe ^ (2 * ν) * (volume (Z ∩ ball (gm c) (cfg.a : ℝ))) * ae ^ (2 * cfg.β) := by
        gcongr
      _ ≤ δe ^ (2 * ν) * (volume (Sg ∩ ball (gm c) (cfg.a : ℝ))) * ae ^ (2 * cfg.β) := by
        gcongr
  -- finally produce the density-form goal
  refine ⟨gm c, ?_⟩
  have hvol : volume (ball (gm c) (cfg.a : ℝ)) = V := hvol_one (gm c)
  simpa [δe, ae, Sg, hvol] using hgoal_c

/-- **The volume ratio of a body to one of its segments, at the working scales** (blueprint
`lem:ml2thickPcard`, first step of its proof).

`(a/δ)² ≤ 48 C₀^6 (|W| / |T_B|)`.

This is `Kakeya.VeryNotSticky.thickSegVolRatio` — which gives
`a b |T_B| ≤ 48 C₀^6 δ² |W|` together with `0 < |T_B| ≤ |W| < ∞` — combined with `a ≤ b` of
`cfg.hdims` and the division by the positive finite `δ² |T_B|`. It is separated from
`Kakeya.VeryNotSticky.thickBlockCard_ge_scales` because it is the only step of blueprint
`lem:ml2thickPcard` that manipulates quotients in `[0, ∞]`. -/
private theorem thickBodySegRatio_ge (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
    {B : bd.bι} (hB : B ∈ bd.bs) {p₀ : bd.σ} (hp₀ : p₀ ∈ bd.segs B) :
    ((cfg.a : ℝ≥0∞) / (cfg.δ : ℝ≥0∞)) ^ (2 : ℝ) ≤
      ((48 * bd.C₀ ^ 6 : ℝ≥0) : ℝ≥0∞) *
        (volume (bd.Wb (bd.blk p₀)).carrier / volume (bd.Y p₀).carrier) := by
  rw [ENNReal.rpow_two]
  let T : ℝ≥0∞ := volume (bd.Y p₀).carrier
  let W : ℝ≥0∞ := volume (bd.Wb (bd.blk p₀)).carrier
  rcases thickSegVolRatio cfg bd hB hp₀ with ⟨hTpos, hTW, hWtop, hratio0⟩
  -- rephrase the input's four conjuncts against `T`, `W`
  have hTpos : 0 < T := by simpa [T] using hTpos
  have hTW : T ≤ W := by simpa [T, W] using hTW
  have hWtop : W ≠ ⊤ := by simpa [W] using hWtop
  have hrat : (cfg.a : ℝ≥0∞) * (cfg.b : ℝ≥0∞) * T ≤
      48 * (bd.C₀ : ℝ≥0∞) ^ 6 * (cfg.δ : ℝ≥0∞) ^ 2 * W := by
    simpa [T, W, mul_assoc, pow_two] using hratio0
  -- nonzero and finite side conditions
  have hT0 : T ≠ 0 := ne_of_gt hTpos
  have hTtop : T ≠ ⊤ := ne_top_of_le_ne_top hWtop hTW
  have hδ0 : (cfg.δ : ℝ≥0∞) ≠ 0 := by exact_mod_cast (ne_of_gt cfg.hδ)
  -- positive dimensions: `cfg.a ≤ cfg.b`, so `a * a ≤ a * b`
  have hapos : 0 < (cfg.a : ℝ≥0) := lt_of_lt_of_le cfg.hδ cfg.hdims.1
  have hasEnn : (cfg.a : ℝ≥0∞) ≤ (cfg.b : ℝ≥0∞) := by exact_mod_cast cfg.hdims.2.1
  have hL : (cfg.a : ℝ≥0∞) ^ 2 ≤ (cfg.a : ℝ≥0∞) * (cfg.b : ℝ≥0∞) := by
    exact_mod_cast (by
      have := mul_le_mul_of_nonneg_left cfg.hdims.2.1 hapos.le
      simpa [pow_two] using this)
  -- `a ^ 2 * T ≤ 48 C₀^6 δ^2 * W`, from the input ratio
  have hMain0 : (cfg.a : ℝ≥0∞) ^ 2 * T ≤
      48 * (bd.C₀ : ℝ≥0∞) ^ 6 * (cfg.δ : ℝ≥0∞) ^ 2 * W := by
    calc
      (cfg.a : ℝ≥0∞) ^ 2 * T ≤ (cfg.a : ℝ≥0∞) * (cfg.b : ℝ≥0∞) * T :=
        mul_le_mul_of_nonneg_right hL (by simp)
      _ ≤ 48 * (bd.C₀ : ℝ≥0∞) ^ 6 * (cfg.δ : ℝ≥0∞) ^ 2 * W := hrat
  -- clear the positive finite `T` from the right of the bound
  have h' : (cfg.a : ℝ≥0∞) ^ 2 ≤
      (48 * (bd.C₀ : ℝ≥0∞) ^ 6 * (cfg.δ : ℝ≥0∞) ^ 2 * W) / T :=
    (ENNReal.le_div_iff_mul_le (Or.inl hT0) (Or.inl hTtop)).mpr hMain0
  have hquot : (cfg.a : ℝ≥0∞) ^ 2 ≤
      48 * (bd.C₀ : ℝ≥0∞) ^ 6 * (cfg.δ : ℝ≥0∞) ^ 2 * (W / T) := by
    calc
      (cfg.a : ℝ≥0∞) ^ 2 ≤ (48 * (bd.C₀ : ℝ≥0∞) ^ 6 * (cfg.δ : ℝ≥0∞) ^ 2 * W) / T := h'
      _ = 48 * (bd.C₀ : ℝ≥0∞) ^ 6 * (cfg.δ : ℝ≥0∞) ^ 2 * (W / T) := by
        rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
        ring
  -- rewrite the goal: `(a / δ) ^ 2 = a ^ 2 / δ ^ 2`
  have hdiv2 : ((cfg.a : ℝ≥0∞) / (cfg.δ : ℝ≥0∞)) ^ 2 =
      (cfg.a : ℝ≥0∞) ^ 2 / (cfg.δ : ℝ≥0∞) ^ 2 := by
    rw [div_eq_mul_inv, mul_pow, ← ENNReal.inv_pow, ← div_eq_mul_inv]
  rw [hdiv2]
  have hδ2n0 : (cfg.δ : ℝ≥0∞) ^ 2 ≠ 0 := pow_ne_zero 2 hδ0
  have hδ2ntop : (cfg.δ : ℝ≥0∞) ^ 2 ≠ ⊤ := by
    rw [← ENNReal.coe_pow]
    exact ENNReal.coe_ne_top
  rw [ENNReal.div_le_iff hδ2n0 hδ2ntop]
  calc
    (cfg.a : ℝ≥0∞) ^ 2 ≤ 48 * (bd.C₀ : ℝ≥0∞) ^ 6 * (cfg.δ : ℝ≥0∞) ^ 2 * (W / T) := hquot
    _ = 48 * (bd.C₀ : ℝ≥0∞) ^ 6 * (W / T) * (cfg.δ : ℝ≥0∞) ^ 2 := by
      simp [mul_assoc, mul_left_comm, mul_comm]

/-- **The thick-case surplus at the bias exponent** (blueprint `lem:ml2thickPcard`, last step
of its proof, and blueprint `lem:ml2thickPlankF`, same step at the exponent `ϱβ/2`).

In the thick case `δ^{1-τ} ≤ a` one has `δ/a ≤ δ^τ`, hence `(δ/a)^ϱ ≤ δ^{τϱ}`. -/
private theorem thickSurplus_le (cfg : VeryNotSticky.{u}) {τ : ℝ}
    (hthick : cfg.δ ^ (1 - τ) ≤ cfg.a) :
    ((cfg.δ : ℝ≥0∞) / (cfg.a : ℝ≥0∞)) ^ cfg.ϱ ≤ (cfg.δ : ℝ≥0∞) ^ (τ * cfg.ϱ) := by
  have hδ_ne0 : (cfg.δ : ℝ≥0∞) ≠ 0 := by exact_mod_cast (ne_of_gt cfg.hδ)
  have hδ_neT : (cfg.δ : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hϱ_nonneg : 0 ≤ cfg.ϱ := le_of_lt cfg.hϱ
  have ha_pos : (0 : ℝ≥0∞) < (cfg.a : ℝ≥0∞) := by
    have hδa : (cfg.δ : ℝ≥0∞) ≤ (cfg.a : ℝ≥0∞) := by exact_mod_cast cfg.hdims.1
    exact lt_of_lt_of_le (by exact_mod_cast cfg.hδ) hδa
  have ha_ne0 : (cfg.a : ℝ≥0∞) ≠ 0 := ha_pos.ne'
  have ha_neT : (cfg.a : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  -- Step 1: cast hthick to ENNReal
  have hδm1 : (cfg.δ : ℝ≥0∞) ^ (1 - τ) ≤ (cfg.a : ℝ≥0∞) := by
    have hδ_ne0_nn : cfg.δ ≠ 0 := ne_of_gt cfg.hδ
    calc
      (cfg.δ : ℝ≥0∞) ^ (1 - τ) = ((cfg.δ ^ (1 - τ) : ℝ≥0) : ℝ≥0∞) :=
        (ENNReal.coe_rpow_of_ne_zero hδ_ne0_nn (1 - τ)).symm
      _ ≤ (cfg.a : ℝ≥0∞) := by exact_mod_cast hthick
  -- Step 2: δ / a ≤ δ ^ τ
  have hδ_le : (cfg.δ : ℝ≥0∞) ≤ (cfg.δ : ℝ≥0∞) ^ τ * (cfg.a : ℝ≥0∞) := by
    have hδ_decomp : (cfg.δ : ℝ≥0∞) = (cfg.δ : ℝ≥0∞) ^ (1 - τ) * (cfg.δ : ℝ≥0∞) ^ τ := by
      calc
        (cfg.δ : ℝ≥0∞) = (cfg.δ : ℝ≥0∞) ^ (((1 - τ) + τ) : ℝ) := by
          have h : ((1 - τ) + τ : ℝ) = 1 := by ring
          rw [h]
          rw [ENNReal.rpow_one]
        _ = (cfg.δ : ℝ≥0∞) ^ (1 - τ) * (cfg.δ : ℝ≥0∞) ^ τ :=
          ENNReal.rpow_add (1 - τ) τ hδ_ne0 hδ_neT
    calc
      (cfg.δ : ℝ≥0∞) = (cfg.δ : ℝ≥0∞) ^ (1 - τ) * (cfg.δ : ℝ≥0∞) ^ τ := hδ_decomp
      _ ≤ (cfg.a : ℝ≥0∞) * (cfg.δ : ℝ≥0∞) ^ τ :=
        mul_le_mul_of_nonneg_right hδm1 (by positivity)
      _ = (cfg.δ : ℝ≥0∞) ^ τ * (cfg.a : ℝ≥0∞) := mul_comm _ _
  have δa_le : (cfg.δ : ℝ≥0∞) / (cfg.a : ℝ≥0∞) ≤ (cfg.δ : ℝ≥0∞) ^ τ := by
    have hm : (cfg.δ : ℝ≥0∞) * (cfg.a : ℝ≥0∞)⁻¹ ≤
        (cfg.δ : ℝ≥0∞) ^ τ * (cfg.a : ℝ≥0∞) * (cfg.a : ℝ≥0∞)⁻¹ :=
      mul_le_mul_of_nonneg_right hδ_le (by positivity)
    calc
      (cfg.δ : ℝ≥0∞) / (cfg.a : ℝ≥0∞)
          = (cfg.δ : ℝ≥0∞) * (cfg.a : ℝ≥0∞)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ (cfg.δ : ℝ≥0∞) ^ τ * (cfg.a : ℝ≥0∞) * (cfg.a : ℝ≥0∞)⁻¹ := hm
      _ = (cfg.δ : ℝ≥0∞) ^ τ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel ha_ne0 ha_neT, mul_one]
  -- Step 3: raise to the power ϱ and rewrite
  calc
    ((cfg.δ : ℝ≥0∞) / (cfg.a : ℝ≥0∞)) ^ cfg.ϱ
        ≤ ((cfg.δ : ℝ≥0∞) ^ τ) ^ cfg.ϱ := ENNReal.rpow_le_rpow δa_le hϱ_nonneg
    _ = (cfg.δ : ℝ≥0∞) ^ (τ * cfg.ϱ) := (ENNReal.rpow_mul (cfg.δ : ℝ≥0∞) τ cfg.ϱ).symm

/-- **The volume ratio at the working scales, raised to the biased power** (blueprint
`lem:ml2thickPcard`, second step of its proof).

`(a/δ)^{2+2ϱ} ≤ (48 C₀^6)² (|W| / |T_B|)^{1+ϱ}`.

This is `Kakeya.VeryNotSticky.thickBodySegRatio_ge` raised to the power `1 + ϱ > 0`, the
constant `(48 C₀^6)^{1+ϱ}` being enlarged to `(48 C₀^6)²` because `48 C₀^6 ≥ 1` and
`1 + ϱ ≤ 2`. The bound `ϱ ≤ 1` is blueprint `lem:ml2thickBiasSmall`, here read off
`params.slabBias` and `params.scale`. -/
private theorem thickBodySegRatioPow_ge (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ')
    (bd : BallData cfg) {B : bd.bι} (hB : B ∈ bd.bs) {p₀ : bd.σ} (hp₀ : p₀ ∈ bd.segs B) :
    ((cfg.a : ℝ≥0∞) / (cfg.δ : ℝ≥0∞)) ^ (2 + 2 * cfg.ϱ) ≤
      ((48 * bd.C₀ ^ 6 : ℝ≥0) : ℝ≥0∞) ^ (2 : ℝ) *
        (volume (bd.Wb (bd.blk p₀)).carrier / volume (bd.Y p₀).carrier) ^ (1 + cfg.ϱ) := by
  set c : ℝ≥0∞ := ((48 * bd.C₀ ^ 6 : ℝ≥0) : ℝ≥0∞) with hc_def
  set A : ℝ≥0∞ := (cfg.a : ℝ≥0∞) / (cfg.δ : ℝ≥0∞) with hA_def
  set R : ℝ≥0∞ := volume (bd.Wb (bd.blk p₀)).carrier / volume (bd.Y p₀).carrier
    with hR_def
  -- `ϱ ≤ 1` from the bias budget `2^20 · ϱ < exscal < 1/2`
  have hϱ_le_one : cfg.ϱ ≤ 1 := by
    have hslab := params.slabBias
    rw [show Kakeya.VeryNotSticky.parameterSeparationConstant = (2 : ℝ) ^ 20 from rfl]
      at hslab
    have hhalf : (2 : ℝ) ^ 20 * cfg.ϱ < 1 / 2 := by
      nlinarith [hslab, params.scale]
    nlinarith
  have h_nonneg : (0 : ℝ) ≤ 1 + cfg.ϱ := by nlinarith [cfg.hϱ]
  -- the constant `48 C₀^6` is at least one, from `1 ≤ C₀`
  have hc_ge1 : (1 : ℝ≥0∞) ≤ c := by
    have hC06 : (1 : ℝ≥0) ≤ bd.C₀ ^ 6 := one_le_pow₀ bd.hC₀
    have hc_nn : (1 : ℝ≥0) ≤ (48 * bd.C₀ ^ 6 : ℝ≥0) := by
      calc
        (1 : ℝ≥0) ≤ 48 * 1 := by norm_num
        _ ≤ 48 * bd.C₀ ^ 6 := mul_le_mul_of_nonneg_left hC06 (by norm_num)
    rw [hc_def]
    exact_mod_cast hc_nn
  -- raise `thickBodySegRatio_ge` to the power `1 + ϱ ≥ 0`
  have hseg : A ^ (2 : ℝ) ≤ c * R := by
    simpa [A, c, R] using thickBodySegRatio_ge cfg bd hB hp₀
  have hpow : (A ^ (2 : ℝ)) ^ (1 + cfg.ϱ) ≤ (c * R) ^ (1 + cfg.ϱ) :=
    ENNReal.rpow_le_rpow hseg h_nonneg
  calc
    A ^ (2 + 2 * cfg.ϱ) = A ^ (2 * (1 + cfg.ϱ)) := by
      congr 1
      ring
    _ = (A ^ (2 : ℝ)) ^ (1 + cfg.ϱ) := ENNReal.rpow_mul A (2 : ℝ) (1 + cfg.ϱ)
    _ ≤ (c * R) ^ (1 + cfg.ϱ) := hpow
    _ = c ^ (1 + cfg.ϱ) * R ^ (1 + cfg.ϱ) := ENNReal.mul_rpow_of_nonneg c R h_nonneg
    _ ≤ c ^ (2 : ℝ) * R ^ (1 + cfg.ϱ) := by
      exact mul_le_mul_of_nonneg_right
        (ENNReal.rpow_le_rpow_of_exponent_le hc_ge1 (by linarith)) zero_le

/-- **Cardinality of a thick-case block against the working scales** (blueprint
`lem:ml2thickPcard`, first display).

For a ball `B ∈ 𝔅` and a segment `T_B ∈ 𝕋_B`, the block `𝕋_{B,W}` of `T_B` satisfies

`(C_bias (48 C₀^6)³)⁻¹ (a/δ)^{2+2ϱ} ≤ |𝕋_{B,W}|`.

This is `Kakeya.VeryNotSticky.thickBodySegRatioPow_ge` combined with
`Kakeya.VeryNotSticky.thickBlockCard_ge`, whose constant `48 C₀^6 C_bias` accounts for the
third power of `48 C₀^6`.

Split off from `Kakeya.VeryNotSticky.thickPcard_ge` because the two halves of blueprint
`lem:ml2thickPcard` are independent: this one is pure volume counting and mentions no
threshold, while the passage to `M ≥ 1` is where `hδ₂` and the thick-case hypothesis are
spent. -/
private theorem thickBlockCard_ge_scales (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ')
    (bd : BallData cfg) {B : bd.bι} (hB : B ∈ bd.bs) {p₀ : bd.σ} (hp₀ : p₀ ∈ bd.segs B) :
    (((bd.Cbias * (48 * bd.C₀ ^ 6) ^ 3 : ℝ≥0) : ℝ≥0∞))⁻¹ *
        ((cfg.a : ℝ≥0∞) / (cfg.δ : ℝ≥0∞)) ^ (2 + 2 * cfg.ϱ) ≤
      ((((bd.segs B).filter (fun p => bd.blk p = bd.blk p₀)).card : ℕ) : ℝ≥0∞) := by
  set A : ℝ≥0∞ := (cfg.a : ℝ≥0∞) / (cfg.δ : ℝ≥0∞) with hA_def
  set c : ℝ≥0∞ := ((48 * bd.C₀ ^ 6 : ℝ≥0) : ℝ≥0∞) with hc_def
  set Cb : ℝ≥0∞ := (bd.Cbias : ℝ≥0∞) with hCb_def
  set K : ℝ≥0∞ := ((bd.Cbias * (48 * bd.C₀ ^ 6) ^ 3 : ℝ≥0) : ℝ≥0∞) with hK_def
  set N : ℝ≥0∞ :=
    ((((bd.segs B).filter (fun p => bd.blk p = bd.blk p₀)).card : ℕ) : ℝ≥0∞) with hN_def
  set R : ℝ≥0∞ := volume (bd.Wb (bd.blk p₀)).carrier / volume (bd.Y p₀).carrier with hR_def
  -- positivity / finiteness of the constants
  have hC0_nn : (1 : ℝ≥0) ≤ bd.C₀ := bd.hC₀
  have hCb_nn : (1 : ℝ≥0) ≤ bd.Cbias := bd.hCbias
  have hc_ge1 : (1 : ℝ≥0∞) ≤ c := by
    have hC06 : (1 : ℝ≥0) ≤ bd.C₀ ^ 6 := by
      have h := pow_le_pow_left₀ (zero_le_one : (0 : ℝ≥0) ≤ 1) hC0_nn 6
      simpa using h
    have h48 : (1 : ℝ≥0) ≤ (48 : ℝ≥0) := by norm_num
    have hc_nn : (1 : ℝ≥0) ≤ 48 * bd.C₀ ^ 6 := by
      simpa using mul_le_mul h48 hC06 (by positivity) (by positivity)
    rw [hc_def]
    exact_mod_cast hc_nn
  have hc_ne0 : c ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) hc_ge1)
  have hc_neT : c ≠ ⊤ := by
    rw [hc_def]
    exact ENNReal.coe_ne_top
  have hCb_ge1 : (1 : ℝ≥0∞) ≤ Cb := by
    rw [hCb_def]
    exact_mod_cast hCb_nn
  have hCb_ne0 : Cb ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) hCb_ge1)
  have hCb_neT : Cb ≠ ⊤ := by
    rw [hCb_def]
    exact ENNReal.coe_ne_top
  have hKC_ne0 : c * Cb ≠ 0 := mul_ne_zero hc_ne0 hCb_ne0
  have hKC_neT : c * Cb ≠ ⊤ := ENNReal.mul_ne_top hc_neT hCb_neT
  -- `K = Cb * c ^ 3`
  have hK_eq : K = Cb * c ^ (3 : ℕ) := by
    rw [hK_def, hCb_def, hc_def]
    simp [ENNReal.coe_mul, ENNReal.coe_pow]
  have hK_real : Cb * c ^ (3 : ℝ) = K := by
    rw [hK_eq]
    rw [show c ^ (3 : ℕ) = c ^ (3 : ℝ) from (ENNReal.rpow_natCast c 3).symm]
  have hc3_ne0 : c ^ (3 : ℕ) ≠ 0 := pow_ne_zero 3 hc_ne0
  have hc3_neT : c ^ (3 : ℕ) ≠ ⊤ := by
    rw [hc_def, ← ENNReal.coe_pow]
    exact ENNReal.coe_ne_top
  have hK_ne0 : K ≠ 0 := by
    rw [hK_eq]
    exact mul_ne_zero hCb_ne0 hc3_ne0
  have hK_neT : K ≠ ⊤ := by
    rw [hK_eq]
    exact ENNReal.mul_ne_top hCb_neT hc3_neT
  -- `thickBodySegRatioPow_ge` supplies the ratio–power bound directly
  have hseg : A ^ (2 + 2 * cfg.ϱ) ≤ c ^ (2 : ℝ) * R ^ (1 + cfg.ϱ) := by
    simpa [A, c, R] using (thickBodySegRatioPow_ge cfg params bd hB hp₀)
  -- `thickBlockCard_ge` gives `R ^ (1 + ϱ) ≤ (c * Cb) * N`
  have hprod : ((48 * bd.C₀ ^ 6 * bd.Cbias : ℝ≥0) : ℝ≥0∞) = c * Cb := by
    rw [hCb_def, hc_def]
    simp [ENNReal.coe_mul, mul_comm]
  have hblk : (c * Cb)⁻¹ * R ^ (1 + cfg.ϱ) ≤ N := by
    have h := thickBlockCard_ge cfg bd hB hp₀
    simpa [hprod, R] using h
  have hR_le : R ^ (1 + cfg.ϱ) ≤ (c * Cb) * N := by
    have hm := mul_le_mul' (le_refl (c * Cb)) hblk
    calc
      R ^ (1 + cfg.ϱ) = ((c * Cb) * (c * Cb)⁻¹) * R ^ (1 + cfg.ϱ) := by
        rw [ENNReal.mul_inv_cancel hKC_ne0 hKC_neT, one_mul]
      _ = (c * Cb) * ((c * Cb)⁻¹ * R ^ (1 + cfg.ϱ)) := by rw [mul_assoc]
      _ ≤ (c * Cb) * N := hm
  -- collect the constants `c ^ 2 · c = c ^ 3`
  have hcc : c ^ (2 : ℝ) * (c * Cb) = Cb * c ^ (3 : ℝ) := by
    symm
    calc
      Cb * c ^ (3 : ℝ) = Cb * c ^ (2 + 1 : ℝ) := by
        rw [show (3 : ℝ) = 2 + 1 by norm_num]
      _ = Cb * (c ^ (2 : ℝ) * c ^ (1 : ℝ)) := by
        rw [ENNReal.rpow_add (2 : ℝ) (1 : ℝ) hc_ne0 hc_neT]
      _ = Cb * (c ^ (2 : ℝ) * c) := by rw [ENNReal.rpow_one c]
      _ = (c ^ (2 : ℝ) * c) * Cb := by rw [mul_comm]
      _ = c ^ (2 : ℝ) * (c * Cb) := by rw [mul_assoc]
  -- chain
  have hmain : A ^ (2 + 2 * cfg.ϱ) ≤ K * N := by
    calc
      A ^ (2 + 2 * cfg.ϱ) ≤ c ^ (2 : ℝ) * R ^ (1 + cfg.ϱ) := hseg
      _ ≤ c ^ (2 : ℝ) * ((c * Cb) * N) := mul_le_mul' (le_refl _) hR_le
      _ = c ^ (2 : ℝ) * (c * Cb) * N := by rw [← mul_assoc]
      _ = (Cb * c ^ (3 : ℝ)) * N := by rw [hcc]
      _ = K * N := by rw [hK_real]
  have hgoal : K⁻¹ * A ^ (2 + 2 * cfg.ϱ) ≤ N := by
    have hm := mul_le_mul' (le_refl (K⁻¹)) hmain
    calc
      K⁻¹ * A ^ (2 + 2 * cfg.ϱ) ≤ K⁻¹ * (K * N) := hm
      _ = (K⁻¹ * K) * N := by rw [← mul_assoc]
      _ = N := by rw [ENNReal.inv_mul_cancel hK_ne0 hK_neT, one_mul]
  simpa using hgoal

/-- **The plank family of a thick-case block is large** (blueprint `lem:ml2thickPcard`, in the
form in which blueprint `plankF` consumes it).

For a ball `B ∈ 𝔅` and a segment `T_B ∈ 𝕋_B`, the block `𝕋_{B,W}` of `T_B` satisfies

`(a/δ)^{2+ϱ} ≤ |𝕋_{B,W}|`.

Since `|𝒫| = |𝕋_{B,W}|` under the plank presentation of blueprint `lem:ml2thickPlank`, this is
exactly the statement that the non-concentration parameter
`M = Θ (δ/a)^{2+ϱ} |𝒫|` of blueprint `lem:ml2thickMbound` satisfies `M ≥ 1` for every
`Θ ≥ 1`, which is what blueprint `plankF` requires. It is stated in that `Θ`-free form, and
not as the blueprint's intermediate display
`|𝒫| ≥ (C_{lemmafactmaxbias} C_{lem:ml2thickCard}³)⁻¹ (a/δ)^{2+2ϱ}`, because the constant is
already spent here: `hδ₂` is what pays for it.

The chain is: `Kakeya.VeryNotSticky.thickBlockCard_ge_scales` gives
`|𝕋_{B,W}| ≥ (C_bias (48 C₀^6)³)⁻¹ (a/δ)^{2+2ϱ}`. Finally `hδ₂` reads
`C_bias (48 C₀^6)³ ≤ δ^{-τϱ}` and `hthick` gives `δ/a ≤ δ^τ`, hence
`(δ/a)^ϱ ≤ δ^{τϱ} ≤ (C_bias (48 C₀^6)³)⁻¹`, and one power of `(a/δ)^ϱ` is consumed.

The threshold `hδ₂` is genuinely needed here and nowhere else in the thick case: this is the
one place where the blueprint's `M ⪆ (a/δ)^ϱ ≥ 1` is not by itself enough, since a large
constant on the wrong side of the inequality would leave `M < 1`. -/
theorem thickPcard_ge (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ')
    (bd : BallData cfg) (hthick : cfg.δ ^ (1 - τ) ≤ cfg.a)
    (hδ₂ : (bd.Cbias : ℝ≥0∞) * (((48 * bd.C₀ ^ 6) ^ 3 : ℝ≥0) : ℝ≥0∞) ≤
      (cfg.δ : ℝ≥0∞) ^ (-(τ * cfg.ϱ)))
    {B : bd.bι} (hB : B ∈ bd.bs) {p₀ : bd.σ} (hp₀ : p₀ ∈ bd.segs B) :
    ((cfg.a : ℝ≥0∞) / (cfg.δ : ℝ≥0∞)) ^ (2 + cfg.ϱ) ≤
      ((((bd.segs B).filter fun p => bd.blk p = bd.blk p₀).card : ℕ) : ℝ≥0∞) := by
  set A : ℝ≥0∞ := (cfg.a : ℝ≥0∞) / (cfg.δ : ℝ≥0∞) with hA_def
  set K : ℝ≥0∞ := ((bd.Cbias * (48 * bd.C₀ ^ 6) ^ 3 : ℝ≥0) : ℝ≥0∞) with hK_def
  -- basic finiteness / positivity of the working scales
  have hδ_ne0 : (cfg.δ : ℝ≥0∞) ≠ 0 := by exact_mod_cast (ne_of_gt cfg.hδ)
  have hδ_neT : (cfg.δ : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hδa : (cfg.δ : ℝ≥0∞) ≤ (cfg.a : ℝ≥0∞) := by exact_mod_cast cfg.hdims.1
  have ha_pos : (0 : ℝ≥0∞) < (cfg.a : ℝ≥0∞) :=
    lt_of_lt_of_le (by exact_mod_cast cfg.hδ) hδa
  have ha_ne0 : (cfg.a : ℝ≥0∞) ≠ 0 := ne_of_gt ha_pos
  have ha_neT : (cfg.a : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hϱ_nonneg : 0 ≤ cfg.ϱ := le_of_lt cfg.hϱ
  -- A ≠ 0, A ≠ ⊤, A ≥ 1
  have hA_ne0 : A ≠ 0 := by
    rw [hA_def]
    exact ENNReal.div_ne_zero.mpr ⟨ha_ne0, hδ_neT⟩
  have hA_neT : A ≠ ⊤ := by
    rw [hA_def]
    exact ENNReal.div_ne_top ha_neT hδ_ne0
  have hA_ge1 : (1 : ℝ≥0∞) ≤ A := by
    have h1A : (1 : ℝ≥0∞) * (cfg.δ : ℝ≥0∞) ≤ A * (cfg.δ : ℝ≥0∞) := by
      rw [hA_def]
      rw [ENNReal.div_mul_cancel hδ_ne0 hδ_neT]
      simpa using hδa
    exact (ENNReal.mul_le_mul_iff_left hδ_ne0 hδ_neT).mp h1A
  have hAϱ_ne0 : A ^ cfg.ϱ ≠ 0 := by
    have hge : (1 : ℝ≥0∞) ≤ A ^ cfg.ϱ := by
      calc
        (1 : ℝ≥0∞) = (1 : ℝ≥0∞) ^ cfg.ϱ := by simp
        _ ≤ A ^ cfg.ϱ := ENNReal.rpow_le_rpow hA_ge1 hϱ_nonneg
    exact (ne_of_lt (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) hge)).symm
  have hAϱ_neT : A ^ cfg.ϱ ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hϱ_nonneg hA_neT
  -- `hδ₂` reads `K ≤ δ ^ (-(τ * ϱ))`
  have hK_le : K ≤ (cfg.δ : ℝ≥0∞) ^ (-(τ * cfg.ϱ)) := by
    simpa [K, ENNReal.coe_mul] using hδ₂
  -- invert to `δ ^ (τ * ϱ) ≤ K⁻¹`
  have h2 : (cfg.δ : ℝ≥0∞) ^ (τ * cfg.ϱ) ≤ K⁻¹ := by
    have h1' : ((cfg.δ : ℝ≥0∞) ^ (-(τ * cfg.ϱ)))⁻¹ ≤ K⁻¹ := ENNReal.inv_le_inv' hK_le
    simpa [ENNReal.rpow_neg (cfg.δ : ℝ≥0∞) (τ * cfg.ϱ)] using h1'
  -- `(δ / a) ^ ϱ = (A ^ ϱ)⁻¹`
  have hδa_inv : (cfg.δ : ℝ≥0∞) / (cfg.a : ℝ≥0∞) = A⁻¹ := by
    rw [hA_def]
    rw [ENNReal.inv_div (Or.inl hδ_neT) (Or.inl hδ_ne0)]
  have h3 : ((cfg.δ : ℝ≥0∞) / (cfg.a : ℝ≥0∞)) ^ cfg.ϱ = (A ^ cfg.ϱ)⁻¹ := by
    rw [hδa_inv]
    exact ENNReal.inv_rpow A cfg.ϱ
  have hsur : (A ^ cfg.ϱ)⁻¹ ≤ (cfg.δ : ℝ≥0∞) ^ (τ * cfg.ϱ) := by
    rw [← h3]
    exact thickSurplus_le cfg hthick
  -- split `A ^ (2 + 2 * ϱ)`
  have hfac : A ^ (2 + 2 * cfg.ϱ) = A ^ cfg.ϱ * A ^ (2 + cfg.ϱ) := by
    calc
      A ^ (2 + 2 * cfg.ϱ) = A ^ (cfg.ϱ + (2 + cfg.ϱ)) := by congr 1; ring
      _ = A ^ cfg.ϱ * A ^ (2 + cfg.ϱ) := ENNReal.rpow_add cfg.ϱ (2 + cfg.ϱ) hA_ne0 hA_neT
  have hA_split : A ^ (2 + cfg.ϱ) = (A ^ cfg.ϱ)⁻¹ * A ^ (2 + 2 * cfg.ϱ) := by
    calc
      A ^ (2 + cfg.ϱ) = (A ^ cfg.ϱ)⁻¹ * (A ^ cfg.ϱ * A ^ (2 + cfg.ϱ)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hAϱ_ne0 hAϱ_neT, one_mul]
      _ = (A ^ cfg.ϱ)⁻¹ * A ^ (2 + 2 * cfg.ϱ) := by rw [← hfac]
  -- assemble
  have hchain1 :
      (A ^ cfg.ϱ)⁻¹ * A ^ (2 + 2 * cfg.ϱ) ≤
        (cfg.δ : ℝ≥0∞) ^ (τ * cfg.ϱ) * A ^ (2 + 2 * cfg.ϱ) :=
    mul_le_mul' hsur (le_refl _)
  have hchain2 :
      (cfg.δ : ℝ≥0∞) ^ (τ * cfg.ϱ) * A ^ (2 + 2 * cfg.ϱ) ≤ K⁻¹ * A ^ (2 + 2 * cfg.ϱ) :=
    mul_le_mul' h2 (le_refl _)
  have hle : A ^ (2 + cfg.ϱ) ≤ K⁻¹ * A ^ (2 + 2 * cfg.ϱ) := by
    calc
      A ^ (2 + cfg.ϱ) = (A ^ cfg.ϱ)⁻¹ * A ^ (2 + 2 * cfg.ϱ) := hA_split
      _ ≤ (cfg.δ : ℝ≥0∞) ^ (τ * cfg.ϱ) * A ^ (2 + 2 * cfg.ϱ) := hchain1
      _ ≤ K⁻¹ * A ^ (2 + 2 * cfg.ϱ) := hchain2
  have hbk := thickBlockCard_ge_scales cfg params bd hB hp₀
  have hbk' :
      K⁻¹ * A ^ (2 + 2 * cfg.ϱ) ≤
        ((((bd.segs B).filter fun p => bd.blk p = bd.blk p₀).card : ℕ) : ℝ≥0∞) := by
    simpa [A, K] using hbk
  simpa [A] using le_trans hle hbk'


/-- The thick-case gain `ν = ϱ β τ / 8` is positive.

Immediate from `cfg.hϱ`, `cfg.hβ` and `params.hτ`; recorded separately because both
`Kakeya.VeryNotSticky.thickGain_ge` and
`Kakeya.VeryNotSticky.goalMult_of_a_ge_of_goalDensity` consume it. -/
theorem thickGain_pos (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ') :
    0 < cfg.ϱ * cfg.β * τ / 8 := by
  have hϱ := cfg.hϱ
  have hβ := cfg.hβ
  have hτ := params.hτ
  positivity

/-- The thick-case gain `ν = ϱ β τ / 8` is at least `90 η`, so the scale-`a` interface
`Kakeya.VeryNotSticky.exists_aScaleData` is available at it.

This is the exponent budget `params.thick`, i.e. `C_sep η < ϱ β τ` with
`C_sep = Kakeya.VeryNotSticky.parameterSeparationConstant = 2^20`: it gives
`ϱ β τ / 8 > 2^17 η`, and `2^17 ≥ 90`, so the blueprint's requirement `ν ≥ 90 η` in
`lem:ml2aScaleVolume` is met with a large margin. This is exactly the observation recorded at
the end of the note of blueprint subsubsection "Reducing the goal to a density estimate". -/
theorem thickGain_ge (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ') :
    90 * cfg.η ≤ cfg.ϱ * cfg.β * τ / 8 := by
  have hη := cfg.hη
  have hthick := params.thick
  rw [show Kakeya.VeryNotSticky.parameterSeparationConstant = (2 : ℝ) ^ 20 from rfl] at hthick
  have h90 : (90 : ℝ) * cfg.η ≤ ((2 : ℝ) ^ 20 * cfg.η) / 8 := by
    nlinarith
  have hdiv : ((2 : ℝ) ^ 20 * cfg.η) / 8 < (cfg.ϱ * cfg.β * τ) / 8 := by
    nlinarith
  nlinarith

/-- **The interface required by the thick case**.

At the thick-case gain `ν = ϱ β τ / 8` the scale-`a` interface
`Kakeya.VeryNotSticky.AScaleData` is available. This produces one admissible comparison
constant `C` together with the implication that reduces
`Kakeya.VeryNotSticky.goalMult_of_a_ge` to producing the density form
`Kakeya.VeryNotSticky.goalDensity (C^2) ν` (blueprint `eqgoaldens`, in the shape supplied by
blueprint `denseInsideW`) at that one `C`.

This is the precise statement of what blueprint `lem:ml2thick` has to prove, and it makes a
demand that producing `eqgoaldens` in bare `⪆` form does not meet: the estimate is required
with an *explicit* constant, namely `C^2` for the `C` of the scale-`a` interface, which is
quantified before the ball. The thick case is thus *given* `C` and never has to exhibit one.

The constant is produced here rather than universally quantified, and that is essential
rather than stylistic. Demanding `goalDensity (C^2) ν` for *every* admissible `C` would be
vacuous: admissibility is upward closed, since `C` sits on the larger side of both estimates
of `AScaleData`, whereas `goalDensity` is antitone in its constant and caps it — from
`|U(T,Y) ∩ B_a| ≤ |B_a|` the density inequality forces `C^2 ≤ δ^{2ν}(a/δ)^{2β}`. So the
universally quantified hypothesis is unsatisfiable and a lemma assuming it carries no
information.

Everything except the density estimate is discharged: `Kakeya.VeryNotSticky.exists_aScaleData`
supplies the interface at `ν` and at the radius `r = cfg.a`, which is admissible on both sides:
`cfg.a ≤ cfg.a` and `cfg.a ≤ 1` by `Kakeya.VeryNotSticky.cfg_a_le_one`, the latter being the
upper bound `r ≤ 1` of blueprint `lem:ml2aScaleData`, which is not decoration — without it the
interface is refutable, as the docstring of `exists_aScaleData` records. (Its other hypotheses
are `Kakeya.VeryNotSticky.thickGain_pos`,
`Kakeya.VeryNotSticky.thickGain_ge`, the threshold `hthr` below, and, at `M = 1` and
`e = cfg.η`, the absorption hypothesis `hM'`, which reads `1 ≤ δ^0` and is discharged by
`sub_self` and `ENNReal.rpow_zero`), and `Kakeya.VeryNotSticky.goalMult_of_goalDensity`
converts the density form into the multiplicity form. Clause (iv) of blueprint
`lem:ml2aScaleData`, the cap `C² ≤ δ^{-η}`, is **carried into the conclusion**. It used to be destructured as `_` and dropped, and it is exactly what
makes `Kakeya.VeryNotSticky.ThickDensityThresholds.density` satisfiable: without it that field is
refutable at large `C` (`Kakeya.VeryNotSticky.no_forall_aScaleData_le`). Restoring it is a
strengthened conclusion of a proved theorem whose input already contains the strengthening, so it
costs nothing.

**The threshold binder `hthr`** is the eighth clause of Configuration `hyp:ml2scale`
, read at the thick gain `ν_{lem:ml2thick} = ϱβτ/8`, and it
is the only clause of that configuration this statement uses. It is here for one reason:
`Kakeya.VeryNotSticky.exists_aScaleData` assumes it, and a statement that applies that one
must supply every hypothesis of it. The cost is nil in substance — `ϱβτ/8` is a function of
`β` and `ζ` alone, fixed before `δ`, so the clause is one of the two instances of
Configuration `hyp:ml2scale` that blueprint `lem:ml2casesplit` arranges — but it is a genuine
binder, and blueprint `lem:ml2thickFromDens` says so.

It is taken as a bare inequality rather than as a whole `Kakeya.VeryNotSticky.CaseScale`
because that is exactly what the blueprint assumes: `CaseScale` also mentions the per-ball
data `bd` and the thin-case constant `C`, neither of which this statement sees, so no call
site is in a position to hand over a bundle. The one consumer,
`Kakeya.VeryNotSticky.goalMult_of_a_ge`, takes the same bare inequality and passes it
straight through; it reaches that lemma from `Kakeya.VeryNotSticky.exists_goalMult`, which
carries the clause at this gain as `hthrThick`, the thick one of the two instances blueprint
`lem:ml2casesplit` arranges. -/
theorem goalMult_of_a_ge_of_goalDensity (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ')
    {thr : ScaleThresholds} (hthr : cfg.δ ≤ thr.aScale (cfg.ϱ * cfg.β * τ / 8)) :
    ∃ C : ℝ≥0∞, 1 ≤ C ∧ C ≠ ⊤ ∧ C ^ 2 ≤ (cfg.δ : ℝ≥0∞) ^ (-cfg.η) ∧
      cfg.AScaleData C cfg.a (cfg.ϱ * cfg.β * τ / 8) ∧
      (cfg.goalDensity (C ^ 2) cfg.a (cfg.ϱ * cfg.β * τ / 8) →
        cfg.goalMult (cfg.ϱ * cfg.β * τ / 8)) := by
  have hνpos : 0 < cfg.ϱ * cfg.β * τ / 8 := thickGain_pos cfg params
  have hνge : 90 * cfg.η ≤ cfg.ϱ * cfg.β * τ / 8 := thickGain_ge cfg params
  obtain ⟨C, hC, hC', hdata, hcap⟩ :=
    exists_aScaleData cfg le_rfl (cfg_a_le_one cfg) (thickRadius_le_six_rpow_exscal cfg)
      (ν := cfg.ϱ * cfg.β * τ / 8) hνpos hνge (ckt_we_le_thickGain cfg params) hthr
  exact ⟨C, hC, hC', hcap, hdata, fun hdens =>
    goalMult_of_goalDensity cfg hνpos.le le_rfl hC hC' hdata hdens⟩


/-- **The text of `Kakeya.VeryNotSticky.ThickDensityThresholds.density`, as a named `Prop`**
(the `statement_of_universal_*` device, so that any later re-cut of the field is pinned against
this exact proposition).

It is the bare `hthrC` of `Kakeya.VeryNotSticky.goalMult_of_denseInBody_at` with the comparison
constant `C` **removed** and the exponent lowered by one `cfg.η`. The `C` is removable because
`Kakeya.VeryNotSticky.goalMult_of_a_ge_of_goalDensity` produces its own `C` together with
`C² ≤ δ^{-cfg.η}`, so the caller pays the `C` out of one `η` and the field never sees it. That
is what defeats `Kakeya.VeryNotSticky.no_densityAfter_forall_C`, which refutes every `∀ C` form:
there is no `∀ C` here. -/
def statement_of_universal_thickDensity_bare (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
    (τ : ℝ) (CP Θ₀ : ℝ≥0) : Prop :=
  cfg.δ ^ (1 - τ) ≤ cfg.a →
    ENNReal.ofReal (8 * Real.pi * (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3) *
        (denseInBodyC₁ CP (cfg.ϱ * cfg.β * τ / 8) cfg.β : ℝ≥0∞) *
        (denseInBodyΘ CP Θ₀ bd.Cbias : ℝ≥0∞) ≤
      (cfg.δ : ℝ≥0∞) ^ (-(cfg.ϱ * cfg.β * τ / 8 - cfg.η))

open MeasureTheory in
/-- **The thick-case scale thresholds** (blueprint `thickDensityThresholds`, hypotheses
(T3) and (T6) of `lem:ml2thick`, together with the parameter budget of blueprint `plankF`).

`bias` is (T3), the threshold absorbing the anti-clustering constant `C_bias` of (C4) and the
dimensional constant of the factoring into `δ^{-τϱ}`. `plankPres` is the Section 6 plank
presentation of the thick-case blocks, blueprint `lem:ml2thickPlank`,
`lem:ml2thickThickenedVol` and `lem:ml2thickMbound`, in the form
`Kakeya.VeryNotSticky.ThickPlankPresentable`. `plankF` is obligation (d) of
`Kakeya.VeryNotSticky.exists_denseInBody`: the compatibility of the parameters that blueprint
`plankF` produces with the scales of the configuration, without which the thick case cannot
apply the plank estimate at all. `density` is (T6), the threshold at
which `Kakeya.VeryNotSticky.exists_denseInBody` can be run, stated in the form quantified
over the constants that lemma produces, and — like blueprint `lem:ml2thickDensity`, whose
statement begins "suppose we are in the thick case, that is, `δ^{1-τ} ≤ a`" — asserted only
under that thick-case guard.

**The guards on `density`, on `plankF` and on `plankPres` are not optional.** Without it
`density` is refuted in the thin regime: taking `Λ` to be the admissible value
`C² · 8π(2√3+C₀)³ ≥ 1` and using
`|U ∩ W| ≤ |W|` in the conclusion forces `Λ ≤ δ^{ϱβτ/4} · (a/δ)^{2β}`, which at `a = δ` —
allowed by Configuration `hyp:ml2setup`, field `hdims` — reads `Λ ≤ δ^{ϱβτ/4} < 1`. An
unsatisfiable field would make the producing interface
`Kakeya.VeryNotSticky.exists_setup_caseSideData` false rather than merely unproved, and
`Kakeya.VeryNotSticky.exists_goalMult` vacuous. In the thick regime `(a/δ)^{2β} ≥ δ^{-2τβ}`
is large and no such refutation applies. The guard is free for the only consumer:
`exists_goalMult` applies `density` inside the branch of its thick/thin dichotomy where
`δ^{1-τ} ≤ a` has already been produced. `plankPres` carries the same guard: GWZ assert the plank presentation only in the thick case (§9.4,
GWZ ), no producer of it exists in the thin regime, and
both consumers read it under `hthick`.

They are named because they occur twice verbatim, as hypotheses of
`Kakeya.VeryNotSticky.exists_goalMult` and as the field
`Kakeya.VeryNotSticky.CaseSideData.thick` of the bundle
`Kakeya.VeryNotSticky.exists_setup_caseSideData` arranges.
`Kakeya.VeryNotSticky.CaseScale`, the container designed for fixed-scale smallness
assumptions, lists neither, and neither is implied by
`Kakeya.VeryNotSticky.CaseParams`. Their achievability is the `δ`-independence question
recorded in the note at the end of blueprint subsection `thickCaseSection`; they are assumed,
not discharged.

**The two constants `CP` and `Θ`, and the plank-Frostman exponent `ηF`, are parameters of this
structure, not values fixed inside it.** The two constants are the comparison constant
`C_{lem:ml2thickPlank}(C₀)` of blueprint
`def:ml2thickPlankConstant` and the non-concentration constant `C_{lem:ml2thickMbound}(C₀)` of
`def:ml2thickMboundConstant`, and both `plankPres` and `plankF` are stated at that one pair.
That is forced: `plankPres` gets weaker as `CP`, `Θ` grow while `plankF` gets stronger, so
quantifying either field's constant inside the other makes one of them unsatisfiable, and
pinning the pair to a Lean value makes `plankPres` false (at an explicit value) or independent
(at a sealed one). Carrying the pair as data of the enclosing bundle
`Kakeya.VeryNotSticky.CaseSideData` is what leaves both fields satisfiable at once; see the
module docstring of `Kakeya/DimensionThree/MainLemma2/ThickPlankInterface.lean`.

`ηF` is a parameter for a different reason: `plankF` needs it *large* — that is the field
`budget` — while `Kakeya.VeryNotSticky.PlankFrostmanVolumeAt`, which `plankF` also asserts at
it, is false once it is too large. Bound existentially inside
`Kakeya.VeryNotSticky.PlankFrostmanUsable`, as it was, the two demands could not be compared,
and nothing recorded the relation `2η < τ ηF` on which the field's satisfiability rests. Named,
they can be: this structure is instantiated at the exponent
`Kakeya.VeryNotSticky.plankFrostmanExponent cfg.β (ϱβτ/8)`, at which the estimate is available
whenever `K_F(β)` is, and `Kakeya.VeryNotSticky.exists_caseParams` chooses `η` below `τ` times
that exponent. -/
structure ThickDensityThresholds (cfg : VeryNotSticky.{u}) (bd : BallData cfg) (τ : ℝ)
    (CP Θ C_NC : ℝ≥0) (ηF : ℝ) : Prop where
  /-- The comparison constant of blueprint `def:ml2thickPlankConstant` is at least `1`. -/
  hCP : 1 ≤ CP
  /-- The non-concentration constant of blueprint `def:ml2thickMboundConstant` is at least
  `1`. -/
  hΘ : 1 ≤ Θ
  /-- (T3): the anti-clustering and dimensional constants are absorbed into `δ^{-τϱ}` -/
  bias : (bd.Cbias : ℝ≥0∞) * (((48 * bd.C₀ ^ 6) ^ 3 : ℝ≥0) : ℝ≥0∞) ≤
    (cfg.δ : ℝ≥0∞) ^ (-(τ * cfg.ϱ))
  /-- **The Section 6 plank presentation of the thick-case blocks**, in the form
  `Kakeya.VeryNotSticky.ThickPlankPresentable`: every block of every ball of `bd`, presented
  through one of its own segments, admits a family of `a' × b' × 1` planks in the Section 6
  window `B̄(0, 4)` *enclosing* the images of the block, together with a selected subfamily
  carrying the comparabilities, the fullness comparison, the Frostman bound, the volume
  comparison and the non-concentration bound of those three lemmas, all at the one pair
  `(CP, Θ)`. See `Kakeya.VeryNotSticky.ThickPlankPresentation` for why the family must be an
  enclosing one and why the essential distinctness lives on a subfamily.

  It is a field here, rather than a theorem of
  `Kakeya/DimensionThree/MainLemma2/ThickPlankInterface.lean`, precisely so that it can be
  asserted at the *same* `CP` as `plankF`; see the structure docstring. Like `plankF` and
  `density` it is asserted only under the thick-case guard `δ^{1-τ} ≤ a`: GWZ present the thick-case blocks as planks only in §9.4, and both consumers
  (`Kakeya.VeryNotSticky.goalMult_of_a_ge`, `Kakeya.VeryNotSticky.exists_goalMult`) read the
  field inside the thick branch. -/
  plankPres : cfg.δ ^ (1 - τ) ≤ cfg.a → ThickPlankPresentable bd CP Θ C_NC
  /-- The plank-Frostman exponent is positive. -/
  hηF : 0 < ηF
  /-- **The exponent budget of blueprint `plankF`**: `2η < τ ηF`.

  This is the relation without which `plankF` below is unsatisfiable, and it is a relation
  between `δ`-free parameters, of the same kind as the fields of
  `Kakeya.VeryNotSticky.CaseParams`. Under the thick-case guard the second threshold of
  `Kakeya.VeryNotSticky.PlankFrostmanUsable` reads `CP^{1+ηF} δ^{τ ηF - 2η} ≤ c₁` ((C5) at `δ^{2η}`), which holds for `δ` small exactly when the exponent
  `τ ηF - 2η` is positive, i.e. exactly under this field. The factor `2` is R16-A, in lockstep with the second conjunct of
  `Kakeya.VeryNotSticky.PlankFrostmanBudget`, from which the degenerate-regime producers
  (`Kakeya.VeryNotSticky.thickDensityThresholds_degenerate` and its `∀ᶠ` forms) fill it.

  It is a field here, and not of `CaseParams`, only because the exponent it constrains cannot
  be a free real: `Kakeya.VeryNotSticky.PlankFrostmanVolumeAt` is *antitone* in the exponent, so
  it is false above some maximal value, and a budget stated against an unconstrained parameter
  would be met by taking that parameter huge — at which value `plankF` is again false. The
  exponent is therefore tied to one at which the estimate is known to hold, namely
  `Kakeya.VeryNotSticky.plankFrostmanExponent`, and it is against *that* value that
  `Kakeya.VeryNotSticky.exists_caseParams` arranges the relation and
  `Kakeya.VeryNotSticky.exists_setup_caseSideData` receives it as its binder `hplankF`. -/
  budget : 2 * cfg.η < τ * ηF
  /-- **The parameter budget of blueprint `plankF` at the scales of the configuration**
  (obligation (d) of `Kakeya.VeryNotSticky.exists_denseInBody`): the plank estimate has to be
  applicable at parameters `(ηF, b₀)` that fit `cfg`, namely `CP δ/a ≤ b₀` and
  `CP (CP δ/b)^{ηF} ≤ c₁ δ^{2η}`, with `CP` the comparison constant of blueprint
  `def:ml2thickPlankConstant`. (The extra factor `CP` on the second threshold pays for the
  enclosure: the planks of `Kakeya.VeryNotSticky.ThickPlankPresentation` *contain* the images
  `L(T_p)`, so their fullness is smaller than the block's by at most `CP` rather than equal to
  it; see `Kakeya.VeryNotSticky.thickPres_fullness_ge`.) The estimate and the threshold on `b₀`
  are bundled into the single predicate `Kakeya.VeryNotSticky.PlankFrostmanUsable` because
  `Kakeya.VeryNotSticky.PlankFrostmanVolumeAt` is antitone in `b₀` while the threshold wants it
  large; see that declaration.

  **Neither the constant nor the exponent is a quantifier.** `PlankFrostmanUsable` is antitone
  in `CP`, so a field of the form `∀ CP ≥ 1, PlankFrostmanUsable bd τ CP ηF` would be
  unsatisfiable at any fixed `cfg`: taking `CP` large refutes `CP δ/a ≤ b₀`. And `ηF` is a
  parameter of this structure rather than an existential inside the predicate because the field
  `budget` above has to compare it with `cfg.η` from outside. Both are therefore asserted at
  the one value this structure is indexed by — for `CP`, the same one `plankPres` uses.

  **The thick-case guard is not optional**, for the same reason it is not optional on
  `density`. Without `δ^{1-τ} ≤ a` the field is refuted: at `a = b = δ`, allowed by
  Configuration `hyp:ml2setup` (field `hdims`), the second threshold reads
  `CP · CP^{ηF} ≤ c₁ δ^{2η}`, whose right side tends to `0` with `δ` while its left side is at
  least `1`. Under the guard `δ/a ≤ δ^τ` and `δ/b ≤ δ^τ`, so the two thresholds read
  `CP δ^τ ≤ b₀` and `CP^{1+ηF} δ^{τ ηF - 2η} ≤ c₁`, both of which hold for `δ` small once
  `2η < τ ηF`, which is the field `budget` above. -/
  plankF : cfg.δ ^ (1 - τ) ≤ cfg.a → PlankFrostmanUsable bd τ CP C_NC ηF
  /-- The dense-body threshold at the named constants
  `denseInBodyC₁` and `denseInBodyΘ`, required under the thick-case guard
  `δ^(1 - τ) ≤ a` and stated as
  `statement_of_universal_thickDensity_bare`.

  In the GWZ proof, the dense-ball implication
  `(eq:ml2-dense-ball-implication)` is applied in the thick case
  (GWZ). The remaining positive power
  `δ'^(τ e β/2)` absorbs the input and enlargement losses, the
  dense-ball preparation, and fixed constants using
  `16η < min{ε_sc ζ β/100, τ e β/10, β/10}`
  (`eq:ml2-eta-budget`).

  Here the fixed product is
  `8π(2√3 + C₀)^3 * denseInBodyC₁ * denseInBodyΘ`, and the
  available gain is `ϱβτ/8`. These exponents play corresponding
  roles without being asserted equal term by term. The scale-data
  estimate also gives `C² ≤ δ^(-η)`; paying for `C` with this
  bound leaves the threshold exponent `ϱβτ/8 - η`.

  The constants must be chosen witnesses. A bound universal in
  `Θ` and `C₁` permits arbitrarily large constants, and a demand
  `C² * X ≤ Y` for every admissible `C` contradicts the upward
  closure `AScaleData.mono` once an admissible `C` exists. This
  obstruction is proved by `no_forall_aScaleData_le` and
  `no_densityAfter_forall_C`.

  Nor does the bias field alone provide the required threshold:
  `denseInBodyΘ` uses the square of `C_bias`, while
  `bias_budget_below_Cbias_square_cost` gives
  `ϱβτ/8 - η < 2τϱ`. The threshold is therefore carried explicitly.
  `goalMult_of_a_ge_of_bareThreshold` proves its sufficiency, and
  `eventually_thickDensity_bare` supplies it for fixed constants by
  absorption, using `thickGain_ge : ϱβτ/8 - η ≥ 89η > 0`. -/
  density : statement_of_universal_thickDensity_bare cfg bd τ CP Θ


end Kakeya.VeryNotSticky

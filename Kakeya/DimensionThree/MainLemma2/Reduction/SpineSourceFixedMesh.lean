/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.MultiScaleSubmult
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineTwoScale
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineRungWiring
public import Kakeya.DimensionThree.MainLemma2.LineEssDistinct
public import Kakeya.Tube.Rigidity
public import Kakeya.FrostmanTransfer
public import Kakeya.ShadedUniform
public import Kakeya.DimensionThree.MainLemma2.GridRounding
public import Kakeya.StickyKakeya.CrossScale
public import Kakeya.MultiScaleFac.Stopping
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeRoute
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineDichotomyInputs
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCoarseSeam
public import Kakeya.MultiScaleFac.UniformBridgeKT
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineLevelBandDescent
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapePayload
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEveryScale
public import Kakeya.MultiScaleFac.GapsKT
public import Kakeya.GridScale
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCoreWindow
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineParams
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEccentric
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEDMultBound
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCentredHandBack
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSiteClosure

/-!
# Radii and mesh of the fixed source tower

Defines `Kakeya.ML2Core.sourceTowerRadius delta M k`, the radius `(1/40) * delta^(k/M)` of
level `k < M` and `delta` at the bottom, and `SourceTowerMesh`, the arithmetic conditions on
the number of levels `M` (divisibility by `M1 * Mc`, global mesh `512 N / etaOne <= M`, and
parent meshes). `source_exists_fixed_tower_mesh` chooses such an `M`, and
`source_eventually_fixed_tower_radius_conditions` gives the eventual smallness and halving
conditions on the radii. Everything downstream about `SourceThreadedTower` uses these radii.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u

noncomputable def sourceTowerRadius (delta : ℝ≥0) (M k : Nat) : ℝ≥0 :=
  if k < M then (1 / 40) * delta ^ ((k : ℝ) / (M : ℝ)) else delta

structure SourceTowerMesh (N M1 Mc M : Nat) (etaOne : ℝ) (parent : Nat -> ℝ) : Prop where
  sticky_integer_pos : 0 < M1
  coarse_integer_pos : 0 < Mc
  count_pos : 1 <= N
  levels_ge_two : 2 <= M
  divisible : M1 * Mc ∣ M
  first_rung_pos : 0 < etaOne
  parent_pos : ∀ m, m < N -> 0 < parent m
  global_mesh : 512 * (N : ℝ) / etaOne <= (M : ℝ)
  all_parent_meshes : ∀ m, m < N -> 8 / parent m <= (M : ℝ)

theorem source_exists_fixed_tower_mesh {N M1 Mc : Nat} {etaOne : ℝ}
    {parent : Nat -> ℝ} (hN : 1 <= N) (hM1 : 0 < M1) (hMc : 0 < Mc)
    (heta : 0 < etaOne) (hparent : ∀ m, m < N -> 0 < parent m) :
    ∃ M : Nat, SourceTowerMesh N M1 Mc M etaOne parent := by
  classical
  let L := 2 + Nat.ceil (512 * (N : ℝ) / etaOne) +
    (Finset.range N).sup (fun m => Nat.ceil (8 / parent m))
  have hprod : 0 < M1 * Mc := Nat.mul_pos hM1 hMc
  have hLM : L <= M1 * Mc * L := Nat.le_mul_of_pos_left L hprod
  have hglobal : 512 * (N : ℝ) / etaOne <= (L : ℝ) := by
    refine (Nat.le_ceil _).trans ?_
    exact_mod_cast (show Nat.ceil (512 * (N : ℝ) / etaOne) <= L by omega)
  have hparents : ∀ m, m < N -> 8 / parent m <= (L : ℝ) := by
    intro m hm
    refine (Nat.le_ceil _).trans ?_
    have hsup := Finset.le_sup (f := fun m => Nat.ceil (8 / parent m))
      (Finset.mem_range.mpr hm)
    exact_mod_cast (show Nat.ceil (8 / parent m) <= L by omega)
  refine ⟨M1 * Mc * L, hM1, hMc, hN, ?_, dvd_mul_right _ _, heta, hparent, ?_, ?_⟩
  · have : 2 <= L := by omega
    omega
  · exact hglobal.trans (by exact_mod_cast hLM)
  · intro m hm
    exact (hparents m hm).trans (by exact_mod_cast hLM)

theorem source_eventually_fixed_tower_radius_conditions (M : Nat) (hM : 2 <= M)
    {e : ℝ} (he : 0 < e) :
    ∀ᶠ delta : ℝ≥0 in 𝓝[>] 0,
      delta < (400 : ℝ≥0) ^ (-(M : ℝ)) /\ delta ^ e <= (1 / 200 : ℝ≥0) /\
      0 < delta /\ sourceTowerRadius delta M 0 <= 1 /\
      (∀ k, k < M -> 4 * delta <= sourceTowerRadius delta M k) /\
      (∀ k, k < M -> sourceTowerRadius delta M (k + 1) <=
        sourceTowerRadius delta M k / 2) := by
  have hMr : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have htower : (0 : ℝ≥0) < (400 : ℝ≥0) ^ (-(M : ℝ)) := by positivity
  have hshade : (0 : ℝ≥0) < (1 / 200 : ℝ≥0) ^ (1 / e) := by positivity
  filter_upwards [Ioo_mem_nhdsGT htower, Ioo_mem_nhdsGT hshade] with delta ht hs
  have hepow : delta ^ e <= (1 / 200 : ℝ≥0) := by
    have hle := NNReal.rpow_le_rpow hs.2.le he.le
    rw [← NNReal.rpow_mul, one_div_mul_cancel he.ne', NNReal.rpow_one] at hle
    exact hle
  let x : ℝ≥0 := delta ^ (1 / (M : ℝ))
  have hx : x <= (1 / 400 : ℝ≥0) := by
    calc x <= ((400 : ℝ≥0) ^ (-(M : ℝ))) ^ (1 / (M : ℝ)) :=
        NNReal.rpow_le_rpow ht.2.le (by positivity)
      _ = 1 / 400 := by
        rw [← NNReal.rpow_mul]
        have hpow : (-(M : ℝ)) * (1 / (M : ℝ)) = -1 := by
          field_simp
        rw [hpow]
        norm_num
  have hx1 : x <= 1 := hx.trans (by
    norm_num [div_le_iff₀ (show (0 : ℝ≥0) < 400 by norm_num)])
  have hrep : ∀ k : Nat, delta ^ ((k : ℝ) / (M : ℝ)) = x ^ k := by
    intro k
    rw [show (k : ℝ) / (M : ℝ) = (1 / (M : ℝ)) * (k : ℝ) by ring,
      NNReal.rpow_mul, NNReal.rpow_natCast]
  have hbottom : delta = x ^ M := by
    simpa [div_self hMr.ne', NNReal.rpow_one] using hrep M
  have hstep : ∀ k, k < M -> delta <= x ^ k * x := by
    intro k hk
    rw [hbottom, ← pow_succ]
    exact pow_le_pow_of_le_one (by positivity) hx1 (by omega)
  refine ⟨ht.2, hepow, ht.1, ?_, ?_, ?_⟩
  · simp only [sourceTowerRadius, show 0 < M by omega, if_true, Nat.cast_zero,
      zero_div, NNReal.rpow_zero, mul_one]
    norm_num [div_le_iff₀ (show (0 : ℝ≥0) < 40 by norm_num)]
  · intro k hk
    rw [sourceTowerRadius, if_pos hk, hrep]
    have hle := hstep k hk
    have hmul := mul_le_mul_of_nonneg_left hx (show 0 <= x ^ k by positivity)
    nlinarith
  · intro k hk
    simp only [sourceTowerRadius, if_pos hk, hrep]
    by_cases hk1 : k + 1 < M
    · rw [if_pos hk1, pow_succ]
      have hxhalf : x <= (1 / 2 : ℝ≥0) := hx.trans (by
        norm_num [div_le_div_iff₀ (show (0 : ℝ≥0) < 400 by norm_num)
          (show (0 : ℝ≥0) < 2 by norm_num)])
      calc (1 / 40 : ℝ≥0) * (x ^ k * x) <= (1 / 40) * (x ^ k * (1 / 2)) := by
            gcongr
        _ = (1 / 40) * x ^ k / 2 := by ring
    · rw [if_neg hk1]
      have hle := hstep k hk
      have hmul := mul_le_mul_of_nonneg_left hx (show 0 <= x ^ k by positivity)
      nlinarith

end Kakeya.ML2Core

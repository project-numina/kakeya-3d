/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.KatzTaoPlankInputs
public import Kakeya.DimensionThree.Plank.DilatedParentCount
public import Kakeya.DimensionThree.Plank.FrostmanPlankEstimate
public import Kakeya.DimensionThree.Plank.LocalFactorizationGeometry
public import Kakeya.DimensionThree.Plank.Section6PartAProp51
public import Kakeya.DimensionThree.Plank.SlabMultiplicityEstimate

/-!
# GWZ Proposition 6.6(A): local plank factorisation

This module contains the local half of GWZ Proposition 6.6, its coarse-slab fallbacks, the shared
`ℝ≥0`/`ENNReal` real-power algebra, and the master-scale interfaces. The global Part (B) lives in
`GlobalPlankFactorizationEstimate.lean`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Convexity ConvexSpaceBody
open scoped NNReal Real ENNReal Classical

noncomputable section

namespace Kakeya

universe u_section6Estimate

/-- **The plank-window mass constant.**

For a nonempty family of `a × b × 1` planks inside the plank window which is Frostman there with
constant `C · C_F`, the total plank mass `|s| · 8 a b` is at least `|window| / (C · C_F)`; since
`b ≤ 1` this gives the absolute lower bound `C_F · (|s| · a) ≥ |window| / (8 C)`.

The constant is quantified *before* the configuration, which is what
`Kakeya.combineLocalFactorFallback` needs: its `Cm` enters the final loss constant, so it may not
depend on `δ`, `a`, `b` or the family.  Positivity is positivity of the volume of a ball of radius
`Kakeya.plankWindowRadius`. -/
theorem exists_plankWindowMassConst (C : ℝ≥0) (hC1 : 1 ≤ C) :
    ∃ Cm : ℝ≥0, 0 < Cm ∧
      ∀ {ι : Type*} {s : Finset ι} {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
        (V : ι → ShadedPlank a b hab hb1), 0 < a → s.Nonempty →
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ)) →
        ∀ {CF : ℝ≥0∞},
          IsFrostmanIn s (fun i => (V i).toConvexSpaceBody) plankWindow ((C : ℝ≥0∞) * CF) →
          (Cm : ℝ≥0∞) ≤ CF * ((s.card : ℝ≥0∞) * (a : ℝ≥0∞)) := by
  set Vb : ℝ≥0∞ := volume (plankWindow).carrier with hVb_def
  have hVb0 : Vb ≠ 0 := by
    rw [hVb_def]
    exact (Metric.measure_closedBall_pos volume 0
      (by norm_num [plankWindowRadius] : (0 : ℝ) < (plankWindowRadius : ℝ))).ne'
  have hVbtop : Vb ≠ ⊤ := (plankWindow).isCompact.measure_ne_top
  set Cm : ℝ≥0 := Vb.toNNReal / (8 * C) with hCm_def
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 1) hC1
  have h8C : (8 : ℝ≥0) * C ≠ 0 := mul_ne_zero (by norm_num) (ne_of_gt hCpos)
  have hCm_pos : 0 < Cm := by
    rw [hCm_def]
    exact div_pos (ENNReal.toNNReal_pos hVb0 hVbtop) (by positivity)
  refine ⟨Cm, hCm_pos, ?_⟩
  intro ι s a b hab hb1 V ha hs hVball CF hFrost
  have hvol : Vb ≤ ((C : ℝ≥0∞) * CF)
      * ((s.card : ℝ≥0∞) * (8 * (a : ℝ≥0∞) * (b : ℝ≥0∞))) := by
    rw [hVb_def]
    exact volume_plankWindow_le_of_isFrostmanIn V ha hs hVball (CF := (C : ℝ≥0∞) * CF) hFrost
  have hb1enn : (b : ℝ≥0∞) ≤ (1 : ℝ≥0∞) := by exact_mod_cast hb1
  have hmain : Vb ≤ (8 * (C : ℝ≥0∞)) * (CF * ((s.card : ℝ≥0∞) * (a : ℝ≥0∞))) := by
    calc
      Vb ≤ ((C : ℝ≥0∞) * CF) * ((s.card : ℝ≥0∞) * (8 * (a : ℝ≥0∞) * (b : ℝ≥0∞))) := hvol
      _ ≤ ((C : ℝ≥0∞) * CF) * ((s.card : ℝ≥0∞) * (8 * (a : ℝ≥0∞) * (1 : ℝ≥0∞))) := by
        gcongr
      _ = (8 * (C : ℝ≥0∞)) * (CF * ((s.card : ℝ≥0∞) * (a : ℝ≥0∞))) := by
        ring
  rw [hCm_def]
  rw [ENNReal.coe_div h8C, ENNReal.coe_toNNReal hVbtop]
  have hmain' : Vb ≤ (CF * (↑s.card * ↑a)) * (↑(8 * C : ℝ≥0) : ℝ≥0∞) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmain
  rw [ENNReal.div_le_iff]
  · exact hmain'
  · exact ENNReal.coe_ne_zero.mpr h8C
  · exact ENNReal.coe_ne_top


/-- **The outer factor of the large-`b` branch, as `δ`-powers.**

Bookkeeping step between GWZ Lemma 6.9 and `Kakeya.combineLocalFactorFallback`: the outer bound
produced by `Kakeya.ShadedPlank.multiplicity_le_of_maxDensity_of_large` carries `a ^ (-2ε/9)` and
the sub-polynomial overlap constant `Cu ≤ δ ^ (-η)`; both are absorbed into `δ ^ (-ε/3)` using
`δ ≤ a ≤ 1` and `η ≤ ε/9`.  The absolute constants `Cdiv`, `Cpack`, `Csplit` are untouched. -/
theorem outerFallbackDeltaBound {ε η : ℝ} (hε : 0 < ε) {δ a : ℝ≥0} (hδ0 : 0 < δ) (hδa : δ ≤ a)
    (ha1 : a ≤ 1) {Cdiv Cpack Cu Csplit : ℝ≥0} (hηε : η ≤ ε / 9) (hCuδ : Cu ≤ δ ^ (-η))
    {μW : ℝ≥0∞}
    (h : μW ≤ (Cdiv : ℝ≥0∞) * (a : ℝ≥0∞) ^ (-(ε / 9 + ε / 9))
      * ((Cpack * Cu * Csplit : ℝ≥0) : ℝ≥0∞)) :
    μW ≤ ((Cdiv * Cpack * Csplit : ℝ≥0) : ℝ≥0∞) * (δ : ℝ≥0∞) ^ (-(ε / 3)) := by
  have h_a_δ : (a : ℝ≥0∞) ^ (-(ε / 9 + ε / 9)) ≤ (δ : ℝ≥0∞) ^ (-(ε / 9 + ε / 9)) := by
    have hδa_enn : (δ : ℝ≥0∞) ≤ (a : ℝ≥0∞) := by exact_mod_cast hδa
    have he9 : (0 : ℝ) < ε / 9 := by positivity
    have h_nonneg' : 0 ≤ ε / 9 + ε / 9 := by nlinarith
    calc
      (a : ℝ≥0∞) ^ (-(ε / 9 + ε / 9)) = (a : ℝ≥0∞)⁻¹ ^ (ε / 9 + ε / 9) := by
        rw [ENNReal.rpow_neg, ENNReal.inv_rpow]
      _ ≤ (δ : ℝ≥0∞)⁻¹ ^ (ε / 9 + ε / 9) := by
        refine ENNReal.rpow_le_rpow (ENNReal.inv_le_inv.mpr hδa_enn) h_nonneg'
      _ = (δ : ℝ≥0∞) ^ (-(ε / 9 + ε / 9)) := by
        rw [ENNReal.rpow_neg, ENNReal.inv_rpow]
  have hCuδ' : (Cu : ℝ≥0∞) ≤ (δ : ℝ≥0∞) ^ (-(ε / 9)) := by
    have hδnz : (δ : ℝ≥0) ≠ 0 := hδ0.ne'
    have hδ1 : δ ≤ (1 : ℝ≥0) := hδa.trans ha1
    have h_exp : -(ε / 9) ≤ -η := by linarith
    have hCu59 : Cu ≤ δ ^ (-(ε / 9)) :=
      hCuδ.trans (NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 h_exp)
    rw [← ENNReal.coe_rpow_of_ne_zero hδnz (-(ε / 9))]
    exact_mod_cast hCu59
  have hδe0 : (δ : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ0.ne'
  have hδetop : (δ : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hdd : (δ : ℝ≥0∞) ^ (-(ε / 9 + ε / 9)) * (δ : ℝ≥0∞) ^ (-(ε / 9))
      = (δ : ℝ≥0∞) ^ (-(ε / 3)) := by
    calc
      (δ : ℝ≥0∞) ^ (-(ε / 9 + ε / 9)) * (δ : ℝ≥0∞) ^ (-(ε / 9))
          = (δ : ℝ≥0∞) ^ (-(ε / 9 + ε / 9) + (-(ε / 9))) := by
            rw [ENNReal.rpow_add (-(ε / 9 + ε / 9)) (-(ε / 9)) hδe0 hδetop]
      _ = (δ : ℝ≥0∞) ^ (-(ε / 3)) := by
            congr 1
            ring
  calc
    μW ≤ (Cdiv : ℝ≥0∞) * (a : ℝ≥0∞) ^ (-(ε / 9 + ε / 9))
        * ((Cpack * Cu * Csplit : ℝ≥0) : ℝ≥0∞) := h
    _ ≤ (Cdiv : ℝ≥0∞) * (δ : ℝ≥0∞) ^ (-(ε / 9 + ε / 9))
        * ((Cpack * Cu * Csplit : ℝ≥0) : ℝ≥0∞) := by
      gcongr
    _ = (Cdiv : ℝ≥0∞) * (δ : ℝ≥0∞) ^ (-(ε / 9 + ε / 9))
        * (Cpack : ℝ≥0∞) * (Cu : ℝ≥0∞) * (Csplit : ℝ≥0∞) := by
      simp [ENNReal.coe_mul, mul_assoc]
    _ ≤ (Cdiv : ℝ≥0∞) * (δ : ℝ≥0∞) ^ (-(ε / 9 + ε / 9))
        * (Cpack : ℝ≥0∞) * (δ : ℝ≥0∞) ^ (-(ε / 9)) * (Csplit : ℝ≥0∞) := by
      gcongr
    _ = (Cdiv : ℝ≥0∞) * (Cpack : ℝ≥0∞) * (Csplit : ℝ≥0∞)
        * (δ : ℝ≥0∞) ^ (-(ε / 3)) := by
      rw [← hdd]
      ring
    _ = ((Cdiv * Cpack * Csplit : ℝ≥0) : ℝ≥0∞) * (δ : ℝ≥0∞) ^ (-(ε / 3)) := by
      simp [ENNReal.coe_mul, mul_assoc]

/-- Lemma 6.9 plus the standard `a`-to-`δ` conversion, in the exact strength needed by the
large-`b` call to `combineLocalFactorFallback`.  The maximal-density constant remains in the
fixed coefficient; it is not incorrectly treated as a power of the thin scale. -/
theorem outerMultiplicityLargeOfMaxDensity
    {ε : ℝ} (hε : 0 < ε) {δ a b bSmall Kang Δ : ℝ≥0}
    (hδ0 : 0 < δ) (hδa : δ ≤ a) (ha1 : a ≤ 1) (hbSmall0 : 0 < bSmall)
    (hKang : ∀ δ' : ℝ≥0, 0 < δ' → δ' ≤ 1 →
      ((ShadedSlab.numAngleWindows δ' : ℕ) : ℝ≥0∞) ≤
        (Kang : ℝ≥0∞) * (δ' : ℝ≥0∞) ^ (-((ε / 2) / 9)))
    {κ' : Type*} (q : Finset κ') {hab : a ≤ b} {hb1 : b ≤ 1}
    (P : κ' → ShadedPlank a b hab hb1) (hbLarge : bSmall ≤ b) (hq : q.Nonempty)
    (hDensity : maxDensity q (fun j ↦ (P j).toConvexSpaceBody) ≤ (Δ : ℝ≥0∞))
    (hfull : a ^ ((ε / 2) / 9) ≤
      ShadedBody.fullness q (fun j ↦ (P j).toShadedBody)) :
    ShadedBody.multiplicity q (fun j ↦ (P j).toShadedBody) ≤
      ((196520 * Kang * (8 * bSmall ^ 2)⁻¹ * Δ : ℝ≥0) : ℝ≥0∞) *
        (δ : ℝ≥0∞) ^ (-(ε / 6)) := by
  let Cdiv : ℝ≥0 := 196520 * Kang * (8 * bSmall ^ 2)⁻¹
  have ha0 : 0 < a := hδ0.trans_le hδa
  have h69 : ShadedBody.multiplicity q (fun j ↦ (P j).toShadedBody) ≤
      (Cdiv : ℝ≥0∞) * (a : ℝ≥0∞) ^ (-((ε / 2) / 9 + (ε / 2) / 9)) *
        (Δ : ℝ≥0∞) := by
    simpa only [Cdiv] using
      ShadedPlank.multiplicity_le_of_maxDensity_of_large hbSmall0 hKang q P ha0 hbLarge hq
        (η := (ε / 2) / 9) (by positivity) hDensity hfull
  have hout := outerFallbackDeltaBound (ε := ε / 2) (η := 0) (by positivity)
    hδ0 hδa ha1 (Cdiv := Cdiv) (Cpack := Δ) (Cu := 1) (Csplit := 1)
    (by positivity) (by simp) (by simpa only [mul_one] using h69)
  change ShadedBody.multiplicity q (fun j ↦ (P j).toShadedBody) ≤
    ((Cdiv * Δ : ℝ≥0) : ℝ≥0∞) * (δ : ℝ≥0∞) ^ (-(ε / 6))
  simpa only [mul_one, show -(ε / 2 / 3) = -(ε / 6) by ring] using hout

/-- Absorb one `δ ^ (-ε/12)` split coefficient, enlarge the inner loss to `δ ^ (-ε/6)`,
and replace the retained outer-cardinality denominator by that of a subfamily. -/
theorem absorbSplitAndRestrictCard
    {ε β : ℝ} (hβ : β ≤ 1)
    {δ a b : ℝ≥0} (hδ0 : 0 < δ)
    {n n' : ℕ} (hn : n' ≤ n) {N C μT μW : ℝ≥0∞}
    (hC : C ≤ (δ : ℝ≥0∞) ^ (-(ε / 12)))
    (hsplit : μT ≤ C * μW *
      ((δ : ℝ≥0∞) ^ (-(ε / 12)) *
        ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (1 - β) *
        ((a : ℝ≥0∞)⁻¹ * (δ : ℝ≥0∞)) ^ (-2 * β) *
        (((a : ℝ≥0∞) ^ 2)⁻¹ * (δ : ℝ≥0∞) ^ 2 *
          (N / (n : ℝ≥0∞))) ^ (1 - β / 2))) :
    μT ≤ (1 : ℝ≥0∞) * μW *
      ((δ : ℝ≥0∞) ^ (-(ε / 6)) *
        ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (1 - β) *
        ((a : ℝ≥0∞)⁻¹ * (δ : ℝ≥0∞)) ^ (-2 * β) *
        (((a : ℝ≥0∞) ^ 2)⁻¹ * (δ : ℝ≥0∞) ^ 2 *
          (N / (n' : ℝ≥0∞))) ^ (1 - β / 2)) := by
  have hpow : C * (δ : ℝ≥0∞) ^ (-(ε / 12)) ≤
      (δ : ℝ≥0∞) ^ (-(ε / 6)) := by
    calc
      C * (δ : ℝ≥0∞) ^ (-(ε / 12)) ≤
          (δ : ℝ≥0∞) ^ (-(ε / 12)) * (δ : ℝ≥0∞) ^ (-(ε / 12)) := by gcongr
      _ = (δ : ℝ≥0∞) ^ (-(ε / 6)) := by
        rw [← ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hδ0.ne') ENNReal.coe_ne_top]
        congr 1
        ring
  have hcardE : (n' : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by exact_mod_cast hn
  have hdiv : N / (n : ℝ≥0∞) ≤ N / (n' : ℝ≥0∞) :=
    ENNReal.div_le_div_left hcardE N
  have hp : 0 ≤ 1 - β / 2 := by linarith
  have hcard :
      (((a : ℝ≥0∞) ^ 2)⁻¹ * (δ : ℝ≥0∞) ^ 2 * (N / (n : ℝ≥0∞))) ^
          (1 - β / 2) ≤
        (((a : ℝ≥0∞) ^ 2)⁻¹ * (δ : ℝ≥0∞) ^ 2 * (N / (n' : ℝ≥0∞))) ^
          (1 - β / 2) := by
    apply ENNReal.rpow_le_rpow _ hp
    gcongr
  calc
    μT ≤ C * μW *
        ((δ : ℝ≥0∞) ^ (-(ε / 12)) *
          ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (1 - β) *
          ((a : ℝ≥0∞)⁻¹ * (δ : ℝ≥0∞)) ^ (-2 * β) *
          (((a : ℝ≥0∞) ^ 2)⁻¹ * (δ : ℝ≥0∞) ^ 2 *
            (N / (n : ℝ≥0∞))) ^ (1 - β / 2)) := hsplit
    _ = μW * (C * (δ : ℝ≥0∞) ^ (-(ε / 12))) *
        (((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (1 - β) *
          ((a : ℝ≥0∞)⁻¹ * (δ : ℝ≥0∞)) ^ (-2 * β)) *
        (((a : ℝ≥0∞) ^ 2)⁻¹ * (δ : ℝ≥0∞) ^ 2 *
          (N / (n : ℝ≥0∞))) ^ (1 - β / 2) := by ring
    _ ≤ μW * (δ : ℝ≥0∞) ^ (-(ε / 6)) *
        (((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (1 - β) *
          ((a : ℝ≥0∞)⁻¹ * (δ : ℝ≥0∞)) ^ (-2 * β)) *
        (((a : ℝ≥0∞) ^ 2)⁻¹ * (δ : ℝ≥0∞) ^ 2 *
          (N / (n' : ℝ≥0∞))) ^ (1 - β / 2) := by gcongr
    _ = _ := by ring

/-- The final large-`b` algebraic combination.  All genuinely fixed losses are exposed in the
single hypothesis `habsorb`; the Frostman restriction loss `Cfr` is charged with its correct
power, rather than being silently identified with the original Frostman constant. -/
theorem combineLargeAndAbsorb
    {β ε : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hε : 0 < ε)
    {δ a b bSmall Cm Cout Cfr : ℝ≥0}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (ha0 : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1)
    (hbSmall0 : 0 < bSmall) (hbLarge : bSmall ≤ b) (hCm : 0 < Cm) (hCfr : 1 ≤ Cfr)
    {CF : ℝ≥0∞} (hCF1 : 1 ≤ CF) (hCFtop : CF ≠ ⊤)
    {nq nts : ℕ} (hnts : nts ≠ 0) (hnq : nq ≠ 0) {μT μW : ℝ≥0∞}
    (hmass : (Cm : ℝ≥0∞) ≤ ((Cfr : ℝ≥0∞) * CF) *
      ((nts : ℝ≥0∞) * (a : ℝ≥0∞)))
    (hW : μW ≤ (Cout : ℝ≥0∞) * (δ : ℝ≥0∞) ^ (-(ε / 6)))
    (hsplit : μT ≤ (1 : ℝ≥0∞) * μW *
      ((δ : ℝ≥0∞) ^ (-(ε / 6)) *
        ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (1 - β) *
        ((a : ℝ≥0∞)⁻¹ * (δ : ℝ≥0∞)) ^ (-2 * β) *
        (((a : ℝ≥0∞) ^ 2)⁻¹ * (δ : ℝ≥0∞) ^ 2 *
          ((nq : ℝ≥0∞) / (nts : ℝ≥0∞))) ^ (1 - β / 2)))
    (habsorb :
      ((Cout * Cm⁻¹ ^ (1 - β / 2) *
        max 1 (bSmall ^ (5 * β / 2 - 1)) : ℝ≥0) : ℝ≥0∞) *
          (Cfr : ℝ≥0∞) ^ (1 - β / 2) ≤
        (δ : ℝ≥0∞) ^ (-(ε / 2))) :
    μT ≤ (δ : ℝ≥0∞) ^ (-ε) * CF ^ (1 - β / 2) *
      ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (3 * β / 2) *
      (δ : ℝ≥0∞) ^ (-2 * β) *
      ((δ : ℝ≥0∞) ^ 2 * (nq : ℝ≥0∞)) ^ (1 - β / 2) := by
  have hCFlarge1 : 1 ≤ (Cfr : ℝ≥0∞) * CF := one_le_mul (by exact_mod_cast hCfr) hCF1
  have hCFlargeTop : (Cfr : ℝ≥0∞) * CF ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top hCFtop
  have hcomb := combineLocalFactorFallback hβ0 hβ1 (show 0 < ε / 2 by positivity)
    hδ0 hδ1 ha0 hab hb1 hbSmall0 hbLarge hCm le_rfl hCFlarge1 hCFlargeTop
    hnts hnq hmass (Cout := Cout) (Csplit := 1) (by
      simpa only [show -((ε / 2) / 3) = -(ε / 6) by ring] using hW) (by
      simpa only [ENNReal.coe_one, show -((ε / 2) / 3) = -(ε / 6) by ring] using hsplit)
  have hp : 0 ≤ 1 - β / 2 := by linarith
  have hδpow : (δ : ℝ≥0∞) ^ (-(ε / 2)) * (δ : ℝ≥0∞) ^ (-(ε / 2)) =
      (δ : ℝ≥0∞) ^ (-ε) := by
    rw [← ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hδ0.ne') ENNReal.coe_ne_top]
    congr 1
    ring
  refine hcomb.trans ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp]
  calc
    ((1 * Cout * Cm⁻¹ ^ (1 - β / 2) *
          max 1 (bSmall ^ (5 * β / 2 - 1)) : ℝ≥0) : ℝ≥0∞) *
          ((δ : ℝ≥0∞) ^ (-(ε / 2)) *
            ((Cfr : ℝ≥0∞) ^ (1 - β / 2) * CF ^ (1 - β / 2)) *
            ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (3 * β / 2) *
            (δ : ℝ≥0∞) ^ (-2 * β) *
            ((δ : ℝ≥0∞) ^ 2 * (nq : ℝ≥0∞)) ^ (1 - β / 2)) =
        ((((Cout * Cm⁻¹ ^ (1 - β / 2) *
            max 1 (bSmall ^ (5 * β / 2 - 1)) : ℝ≥0) : ℝ≥0∞) *
          (Cfr : ℝ≥0∞) ^ (1 - β / 2)) * (δ : ℝ≥0∞) ^ (-(ε / 2))) *
          (CF ^ (1 - β / 2) *
            ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (3 * β / 2) *
            (δ : ℝ≥0∞) ^ (-2 * β) *
            ((δ : ℝ≥0∞) ^ 2 * (nq : ℝ≥0∞)) ^ (1 - β / 2)) := by ring
    _ ≤ ((δ : ℝ≥0∞) ^ (-(ε / 2)) * (δ : ℝ≥0∞) ^ (-(ε / 2))) *
          (CF ^ (1 - β / 2) *
            ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (3 * β / 2) *
            (δ : ℝ≥0∞) ^ (-2 * β) *
            ((δ : ℝ≥0∞) ^ 2 * (nq : ℝ≥0∞)) ^ (1 - β / 2)) := by gcongr
    _ = _ := by rw [hδpow]; ring


/-- **rpow constant absorption threshold** (choice of `δ₀`). For an absolute constant `C ≥ 1`,
nonnegative power `p` and positive exponent `e`, there is `δ₀ > 0` so that `C^p ≤ δ^(-e)` for all
`0 < δ ≤ δ₀` (take `δ₀ = C^(-p/e)`). Used to absorb the fixed factoring losses into `δ^(-ε)`. -/
theorem rpowConstAbsorb (C : ℝ≥0) (hC : 1 ≤ C) {p e : ℝ} (_hp : 0 ≤ p) (he : 0 < e) :
    ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧ ∀ δ : ℝ≥0, 0 < δ → δ ≤ δ₀ →
      (C : ℝ≥0∞) ^ p ≤ (δ : ℝ≥0∞) ^ (-e) := by
  have hC0 : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 1) hC
  have hC0_ne : C ≠ 0 := hC0.ne'
  have he_ne : e ≠ 0 := by linarith
  set δ₀ : ℝ≥0 := C ^ (-p / e) with hδ₀_def
  have hδ₀_pos : 0 < δ₀ := NNReal.rpow_pos hC0
  refine ⟨δ₀, hδ₀_pos, ?_⟩
  intro δ hδ hδle
  -- lift δ ≤ δ₀ to ENNReal
  have hδle_coe : (δ : ℝ≥0∞) ≤ (δ₀ : ℝ≥0∞) := by exact mod_cast hδle
  have hδ0_ne : (δ : ℝ≥0∞) ≠ 0 := by exact mod_cast hδ.ne'
  have hδ_top_ne : (δ : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hδ₀_top_ne : (δ₀ : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hδ₀_0_ne : (δ₀ : ℝ≥0∞) ≠ 0 := by exact mod_cast hδ₀_pos.ne'
  have hC_enn_ne0 : (C : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hC0_ne
  have hC_enn_ne_top : (C : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  -- Step 1: show that (δ₀ : ENNReal)^(-e) = (C : ENNReal)^p
  have h_eq : (δ₀ : ℝ≥0∞) ^ (-e) = (C : ℝ≥0∞) ^ p := by
    calc
      (δ₀ : ℝ≥0∞) ^ (-e) = ((C : ℝ≥0∞) ^ (-p / e)) ^ (-e) := by
        rw [← ENNReal.coe_rpow_of_ne_zero hC0_ne (-p / e)]
      _ = (C : ℝ≥0∞) ^ ((-p / e) * (-e)) := by rw [ENNReal.rpow_mul]
      _ = (C : ℝ≥0∞) ^ p := by
        field_simp [he_ne]
  -- Step 2: use monotonicity of x ↦ x^e for e > 0, then invert
  have h_e_nonneg : 0 ≤ e := by linarith
  have h_pow_e : (δ : ℝ≥0∞) ^ e ≤ (δ₀ : ℝ≥0∞) ^ e :=
    ENNReal.rpow_le_rpow hδle_coe h_e_nonneg
  have h_inv : ((δ₀ : ℝ≥0∞) ^ e)⁻¹ ≤ ((δ : ℝ≥0∞) ^ e)⁻¹ :=
    (ENNReal.inv_le_inv.mpr h_pow_e)
  calc
    (C : ℝ≥0∞) ^ p = (δ₀ : ℝ≥0∞) ^ (-e) := by rw [h_eq]
    _ = ((δ₀ : ℝ≥0∞) ^ e)⁻¹ := by rw [ENNReal.rpow_neg]
    _ ≤ ((δ : ℝ≥0∞) ^ e)⁻¹ := h_inv
    _ = (δ : ℝ≥0∞) ^ (-e) := by rw [ENNReal.rpow_neg]

/-- Sub-identity for `combineLocalFactor_rpow`: extract the `Csplit` and `(a/b)` powers from
`(Csplit·(b/a))^(β/2)`. -/
theorem splitConstant_aspectRatio_rpow {β : ℝ} (Csplit a b : ℝ≥0) (_ha : a ≠ 0) (_hb : b ≠ 0) :
    (Csplit * (b / a)) ^ (β / 2) = Csplit ^ (β / 2) * (a / b) ^ (-(β / 2)) := by
  rw [NNReal.mul_rpow]
  congr 1
  calc
    (b / a) ^ (β / 2) = ((a / b)⁻¹) ^ (β / 2) := by rw [← inv_div a b]
    _ = ((a / b) ^ (β / 2))⁻¹ := by rw [NNReal.inv_rpow]
    _ = (a / b) ^ (-(β / 2)) := by rw [← NNReal.rpow_neg (a / b) (β / 2)]

/-- Sub-identity for `combineLocalFactor_rpow`: `b^(-2β)·(a⁻¹δ)^(-2β) = (a/b)^(2β)·δ^(-2β)`. -/
theorem transverseScale_rpow {β : ℝ} (a b δ : ℝ≥0) (_ha : a ≠ 0) (_hb : b ≠ 0) (_hδ : δ ≠ 0) :
    b ^ (-2 * β) * (a⁻¹ * δ) ^ (-2 * β) = (a / b) ^ (2 * β) * δ ^ (-2 * β) := by
  have h_inv_pow : (a⁻¹) ^ (-2 * β) = a ^ (2 * β) := by
    calc
      (a⁻¹) ^ (-2 * β) = (a ^ (-2 * β))⁻¹ := by rw [NNReal.inv_rpow]
      _ = (a ^ (-(2 * β)))⁻¹ := by ring
      _ = ((a ^ (2 * β))⁻¹)⁻¹ := by rw [NNReal.rpow_neg a (2 * β)]
      _ = a ^ (2 * β) := by simp
  have h_div_pow : (a / b) ^ (2 * β) = b ^ (-2 * β) * a ^ (2 * β) := by
    calc
      (a / b) ^ (2 * β) = a ^ (2 * β) / b ^ (2 * β) := by rw [NNReal.div_rpow]
      _ = a ^ (2 * β) * (b ^ (2 * β))⁻¹ := by rw [div_eq_mul_inv]
      _ = a ^ (2 * β) * b ^ (-(2 * β)) := by rw [NNReal.rpow_neg b (2 * β)]
      _ = a ^ (2 * β) * b ^ (-2 * β) := by ring
      _ = b ^ (-2 * β) * a ^ (2 * β) := mul_comm _ _
  calc
    b ^ (-2 * β) * (a⁻¹ * δ) ^ (-2 * β) = b ^ (-2 * β) * ((a⁻¹) ^ (-2 * β) * δ ^ (-2 * β)) := by
      rw [NNReal.mul_rpow]
    _ = (b ^ (-2 * β) * (a⁻¹) ^ (-2 * β)) * δ ^ (-2 * β) := by
      simp [mul_assoc]
    _ = (b ^ (-2 * β) * a ^ (2 * β)) * δ ^ (-2 * β) := by rw [h_inv_pow]
    _ = (a / b) ^ (2 * β) * δ ^ (-2 * β) := by rw [h_div_pow]

/-- Sub-identity for `combineLocalFactor_rpow`: the cardinality product; `|ts|` cancels and
`b²·a⁻²` becomes `(a/b)^(β-2)`. -/
theorem fibreCardinality_rpow {β : ℝ} (a b δ : ℝ≥0) (nq nts : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (_hδ : δ ≠ 0)
    (hnts : nts ≠ 0) :
    (b ^ 2 * (nts : ℝ≥0)) ^ (1 - β / 2)
        * ((a ^ 2)⁻¹ * δ ^ 2 * ((nq : ℝ≥0) / (nts : ℝ≥0))) ^ (1 - β / 2)
      = (a / b) ^ (β - 2) * (δ ^ 2 * (nq : ℝ≥0)) ^ (1 - β / 2) := by
  have hnts' : (nts : ℝ≥0) ≠ 0 := by exact_mod_cast hnts
  -- Write (nq/nts) as nq * (nts)⁻¹
  have hdiv : ((nq : ℝ≥0) / (nts : ℝ≥0)) = (nq : ℝ≥0) * ((nts : ℝ≥0)⁻¹) := div_eq_mul_inv _ _
  rw [hdiv]
  -- Combine the two ^(1-β/2) factors
  rw [← NNReal.mul_rpow (z := 1 - β / 2)]
  -- Inside: simplify the base product
  have hbase : b ^ 2 * (nts : ℝ≥0) * ((a ^ 2)⁻¹ * δ ^ 2 * ((nq : ℝ≥0) * ((nts : ℝ≥0)⁻¹))) =
    (a ^ 2)⁻¹ * b ^ 2 * (δ ^ 2 * (nq : ℝ≥0)) := by
    calc
      b ^ 2 * (nts : ℝ≥0) * ((a ^ 2)⁻¹ * δ ^ 2 * ((nq : ℝ≥0) * ((nts : ℝ≥0)⁻¹)))
          = b ^ 2 * ((a ^ 2)⁻¹ * δ ^ 2 * (nq : ℝ≥0)) * ((nts : ℝ≥0) * ((nts : ℝ≥0)⁻¹)) := by ring
      _ = b ^ 2 * ((a ^ 2)⁻¹ * δ ^ 2 * (nq : ℝ≥0)) * (1 : ℝ≥0) := by
        simp [hnts']
      _ = (a ^ 2)⁻¹ * b ^ 2 * (δ ^ 2 * (nq : ℝ≥0)) := by ring
  rw [hbase]
  -- Split back into product of two rpows
  rw [NNReal.mul_rpow (z := 1 - β / 2)]
  -- Now we have ((a^2)⁻¹ * b^2)^(1-β/2) * (δ^2 * (nq:ℝ≥0))^(1-β/2)
  congr 1
  · -- Show ((a^2)⁻¹ * b^2)^(1-β/2) = (a/b)^(β-2)
    have h_exponent : (-(2 : ℝ)) * (1 - β / 2) = β - 2 := by ring
    have h_factor : (a ^ 2)⁻¹ * b ^ 2 = (a / b) ^ (-(2 : ℝ)) := by
      calc
        (a ^ 2)⁻¹ * b ^ 2 = b ^ 2 / a ^ 2 := by field_simp [ha]
        _ = (b / a) ^ 2 := by simp [div_pow]
        _ = ((a / b)⁻¹) ^ 2 := by field_simp [ha, hb]
        _ = ((a / b)⁻¹) ^ (2 : ℝ) := by norm_cast
        _ = ((a / b) ^ (2 : ℝ))⁻¹ := by rw [NNReal.inv_rpow]
        _ = (a / b) ^ (-(2 : ℝ)) := by rw [NNReal.rpow_neg]
    calc
      ((a ^ 2)⁻¹ * b ^ 2) ^ (1 - β / 2) = ((a / b) ^ (-(2 : ℝ))) ^ (1 - β / 2) := by rw [h_factor]
      _ = (a / b) ^ ((-(2 : ℝ)) * (1 - β / 2)) := by
        rw [← NNReal.rpow_mul (a / b) (-(2 : ℝ)) (1 - β / 2)]
      _ = (a / b) ^ (β - 2) := by rw [h_exponent]

/-- Sub-identity for `combineLocalFactor_rpow`: the five `(a/b)` powers collapse to `(a/b)^(3β/2)`. -/
theorem aspectRatio_rpow_collect {β : ℝ} (x : ℝ≥0) (hx : x ≠ 0) :
    x ^ (-(β / 2)) * x * x ^ (1 - β) * x ^ (2 * β) * x ^ (β - 2) = x ^ (3 * β / 2) := by
  calc
    x ^ (-(β / 2)) * x * x ^ (1 - β) * x ^ (2 * β) * x ^ (β - 2)
        = (x ^ (-(β / 2)) * x ^ (1 : ℝ) * x ^ (1 - β) * x ^ (2 * β) * x ^ (β - 2)) := by
      nth_rw 2 [← NNReal.rpow_one x]
    _ = x ^ (-(β / 2) + (1 : ℝ) + (1 - β) + (2 * β) + (β - 2)) := by
      repeat' rw [← NNReal.rpow_add hx]
    _ = x ^ (3 * β / 2) := by
      congr 1
      ring

set_option maxHeartbeats 1000000 in
/-- **Factor-combination rpow identity, `ℝ≥0` form** (for GWZ 6.6(A)). The Frostman-constant-free
core of `combineLocalFactor`: the product of the μ-split factor, the outer 6.4 bound (without its
`CF^(1-β/2)`), and the inner factor collapses, after all rpow cancellations (the `|ts|` cancels,
`b²·a⁻²` folds into `(a/b)^(3β/2)`), to
`Csplit^(1+β/2)·a^(-ε/3)·δ^(-ε/3)·(a/b)^(3β/2)·δ^(-2β)·(δ²·nq)^(1-β/2)`.
Stated over `ℝ≥0` where rpow is unconditional. -/
theorem combineLocalFactor_rpow {β ε : ℝ} {a b δ Csplit : ℝ≥0} {nq nts : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hδ : δ ≠ 0) (hCs : Csplit ≠ 0) (hnts : nts ≠ 0) :
    Csplit * (a ^ (-(ε / 3)) * (Csplit * (b / a)) ^ (β / 2) * (a / b) * b ^ (-2 * β)
        * (b ^ 2 * (nts : ℝ≥0)) ^ (1 - β / 2))
      * (δ ^ (-(ε / 3)) * (a / b) ^ (1 - β) * (a⁻¹ * δ) ^ (-2 * β)
        * ((a ^ 2)⁻¹ * δ ^ 2 * ((nq : ℝ≥0) / (nts : ℝ≥0))) ^ (1 - β / 2))
      = Csplit ^ (1 + β / 2) * a ^ (-(ε / 3)) * δ ^ (-(ε / 3)) * (a / b) ^ (3 * β / 2)
        * δ ^ (-2 * β) * (δ ^ 2 * (nq : ℝ≥0)) ^ (1 - β / 2) := by
  set AB := a / b with hAB
  have ha_div_b_ne_zero : AB ≠ 0 := div_ne_zero ha hb
  have hCs' : Csplit * Csplit ^ (β / 2) = Csplit ^ (1 + β / 2) := by
    calc
      Csplit * Csplit ^ (β / 2) = Csplit ^ (1 : ℝ) * Csplit ^ (β / 2) := by simp
      _ = Csplit ^ ((1 : ℝ) + β / 2) := by rw [← NNReal.rpow_add hCs (1 : ℝ) (β / 2)]
      _ = Csplit ^ (1 + β / 2) := by norm_num
  calc
    Csplit * (a ^ (-(ε / 3)) * (Csplit * (b / a)) ^ (β / 2) * (a / b) * b ^ (-2 * β)
        * (b ^ 2 * (nts : ℝ≥0)) ^ (1 - β / 2))
      * (δ ^ (-(ε / 3)) * (a / b) ^ (1 - β) * (a⁻¹ * δ) ^ (-2 * β)
        * ((a ^ 2)⁻¹ * δ ^ 2 * ((nq : ℝ≥0) / (nts : ℝ≥0))) ^ (1 - β / 2))
    = Csplit * a ^ (-(ε / 3))
        * ((Csplit * (b / a)) ^ (β / 2))
        * (a / b) * b ^ (-2 * β)
        * ((b ^ 2 * (nts : ℝ≥0)) ^ (1 - β / 2))
        * (δ ^ (-(ε / 3)) * (a / b) ^ (1 - β) * (a⁻¹ * δ) ^ (-2 * β)
          * ((a ^ 2)⁻¹ * δ ^ 2 * ((nq : ℝ≥0) / (nts : ℝ≥0))) ^ (1 - β / 2)) := by ring
    _ = Csplit * a ^ (-(ε / 3))
        * (Csplit ^ (β / 2) * (a / b) ^ (-(β / 2)))
        * (a / b) * b ^ (-2 * β)
        * ((b ^ 2 * (nts : ℝ≥0)) ^ (1 - β / 2))
        * (δ ^ (-(ε / 3)) * (a / b) ^ (1 - β) * (a⁻¹ * δ) ^ (-2 * β)
          * ((a ^ 2)⁻¹ * δ ^ 2 * ((nq : ℝ≥0) / (nts : ℝ≥0))) ^ (1 - β / 2)) := by
      rw [splitConstant_aspectRatio_rpow Csplit a b ha hb]
    _ = Csplit * a ^ (-(ε / 3))
        * Csplit ^ (β / 2)
        * ((a / b) ^ (-(β / 2)) * (a / b))
        * b ^ (-2 * β)
        * ((b ^ 2 * (nts : ℝ≥0)) ^ (1 - β / 2))
        * (δ ^ (-(ε / 3)) * (a / b) ^ (1 - β) * (a⁻¹ * δ) ^ (-2 * β)
          * ((a ^ 2)⁻¹ * δ ^ 2 * ((nq : ℝ≥0) / (nts : ℝ≥0))) ^ (1 - β / 2)) := by ring
    _ = (Csplit * Csplit ^ (β / 2)) * a ^ (-(ε / 3))
        * ((a / b) ^ (-(β / 2)) * (a / b))
        * b ^ (-2 * β)
        * ((b ^ 2 * (nts : ℝ≥0)) ^ (1 - β / 2))
        * (δ ^ (-(ε / 3)) * (a / b) ^ (1 - β) * (a⁻¹ * δ) ^ (-2 * β)
          * ((a ^ 2)⁻¹ * δ ^ 2 * ((nq : ℝ≥0) / (nts : ℝ≥0))) ^ (1 - β / 2)) := by ring
    _ = Csplit ^ (1 + β / 2) * a ^ (-(ε / 3))
        * ((a / b) ^ (-(β / 2)) * (a / b))
        * b ^ (-2 * β)
        * ((b ^ 2 * (nts : ℝ≥0)) ^ (1 - β / 2))
        * (δ ^ (-(ε / 3)) * (a / b) ^ (1 - β) * (a⁻¹ * δ) ^ (-2 * β)
          * ((a ^ 2)⁻¹ * δ ^ 2 * ((nq : ℝ≥0) / (nts : ℝ≥0))) ^ (1 - β / 2)) := by
      rw [hCs']
    _ = Csplit ^ (1 + β / 2) * a ^ (-(ε / 3))
        * ((a / b) ^ (-(β / 2)) * (a / b))
        * (b ^ (-2 * β) * (a⁻¹ * δ) ^ (-2 * β))
        * ((b ^ 2 * (nts : ℝ≥0)) ^ (1 - β / 2))
        * (δ ^ (-(ε / 3)) * (a / b) ^ (1 - β)
          * ((a ^ 2)⁻¹ * δ ^ 2 * ((nq : ℝ≥0) / (nts : ℝ≥0))) ^ (1 - β / 2)) := by ring
    _ = Csplit ^ (1 + β / 2) * a ^ (-(ε / 3))
        * ((a / b) ^ (-(β / 2)) * (a / b))
        * ((a / b) ^ (2 * β) * δ ^ (-2 * β))
        * ((b ^ 2 * (nts : ℝ≥0)) ^ (1 - β / 2))
        * (δ ^ (-(ε / 3)) * (a / b) ^ (1 - β)
          * ((a ^ 2)⁻¹ * δ ^ 2 * ((nq : ℝ≥0) / (nts : ℝ≥0))) ^ (1 - β / 2)) := by
      rw [transverseScale_rpow a b δ ha hb hδ]
    _ = Csplit ^ (1 + β / 2) * a ^ (-(ε / 3))
        * ((a / b) ^ (-(β / 2)) * (a / b))
        * ((a / b) ^ (2 * β) * δ ^ (-2 * β))
        * (δ ^ (-(ε / 3)) * (a / b) ^ (1 - β))
        * ((b ^ 2 * (nts : ℝ≥0)) ^ (1 - β / 2)
          * ((a ^ 2)⁻¹ * δ ^ 2 * ((nq : ℝ≥0) / (nts : ℝ≥0))) ^ (1 - β / 2)) := by ring
    _ = Csplit ^ (1 + β / 2) * a ^ (-(ε / 3))
        * ((a / b) ^ (-(β / 2)) * (a / b))
        * ((a / b) ^ (2 * β) * δ ^ (-2 * β))
        * (δ ^ (-(ε / 3)) * (a / b) ^ (1 - β))
        * ((a / b) ^ (β - 2) * (δ ^ 2 * (nq : ℝ≥0)) ^ (1 - β / 2)) := by
      rw [fibreCardinality_rpow a b δ nq nts ha hb hδ hnts]
    _ = Csplit ^ (1 + β / 2) * a ^ (-(ε / 3)) * δ ^ (-(ε / 3))
        * ((a / b) ^ (-(β / 2)) * (a / b) * (a / b) ^ (1 - β) * (a / b) ^ (2 * β) * (a / b) ^ (β - 2))
        * δ ^ (-2 * β)
        * (δ ^ 2 * (nq : ℝ≥0)) ^ (1 - β / 2) := by
      ring
    _ = Csplit ^ (1 + β / 2) * a ^ (-(ε / 3)) * δ ^ (-(ε / 3))
        * ((a / b) ^ (3 * β / 2))
        * δ ^ (-2 * β)
        * (δ ^ 2 * (nq : ℝ≥0)) ^ (1 - β / 2) := by
      rw [aspectRatio_rpow_collect (a / b) ha_div_b_ne_zero]
    _ = Csplit ^ (1 + β / 2) * a ^ (-(ε / 3)) * δ ^ (-(ε / 3)) * (a / b) ^ (3 * β / 2)
        * δ ^ (-2 * β) * (δ ^ 2 * (nq : ℝ≥0)) ^ (1 - β / 2) := rfl

set_option maxHeartbeats 1000000 in
/-- **Combination of the outer/inner factor bounds for GWZ 6.6(A)** (pure `ENNReal`/rpow algebra).
Given the multiplicity split `μqT ≤ Csplit · μW · INNER`, the outer-plank bound `h64out` for `μW`
coming from GWZ Lemma 6.4 with `M = Csplit·(b/a)`, the scale relation `δ ≤ a`, and the
constant-absorption threshold `Csplit^(1+β/2) ≤ δ^(-ε/3)`, the two factors combine (the `|ts|`
cardinalities cancel, and `b²·a⁻²` folds into `(a/b)^(3β/2)`) into the 6.6(A) bound. Not geometry. -/
theorem combineLocalFactor {β ε : ℝ} (_hβpos : 0 < β) (hβle : β ≤ 1) (hε : 0 < ε)
    {a b δ : ℝ≥0} (ha : 0 < a) (hab : a ≤ b) (hδ0 : 0 < δ) (hδa : δ ≤ a)
    {Csplit : ℝ≥0} (hCs1 : 1 ≤ Csplit) {CF : ℝ≥0∞} (_hCF1 : 1 ≤ CF) (_hCFtop : CF ≠ ⊤)
    {nq nts : ℕ} (hnts : nts ≠ 0)
    {μqT μW : ℝ≥0∞}
    (h64out : μW ≤ (a : ℝ≥0∞) ^ (-(ε / 3)) * CF ^ (1 - β / 2)
        * ((Csplit * (b / a) : ℝ≥0) : ℝ≥0∞) ^ (β / 2) * ((a : ℝ≥0∞) / (b : ℝ≥0∞))
        * (b : ℝ≥0∞) ^ (-2 * β) * ((b : ℝ≥0∞) ^ 2 * (nts : ℝ≥0∞)) ^ (1 - β / 2))
    (hsplit : μqT ≤ (Csplit : ℝ≥0∞) * μW
        * ((δ : ℝ≥0∞) ^ (-(ε / 3)) * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (1 - β)
          * ((a : ℝ≥0∞)⁻¹ * (δ : ℝ≥0∞)) ^ (-2 * β)
          * (((a : ℝ≥0∞) ^ 2)⁻¹ * (δ : ℝ≥0∞) ^ 2 * ((nq : ℝ≥0∞) / (nts : ℝ≥0∞)))
              ^ (1 - β / 2)))
    (hthr : (Csplit : ℝ≥0∞) ^ ((1 : ℝ) + β / 2) ≤ (δ : ℝ≥0∞) ^ (-(ε / 3))) :
    μqT ≤ (δ : ℝ≥0∞) ^ (-ε) * CF ^ (1 - β / 2)
        * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (3 * β / 2)
        * (δ : ℝ≥0∞) ^ (-2 * β)
        * ((δ : ℝ≥0∞) ^ 2 * (nq : ℝ≥0∞)) ^ (1 - β / 2) := by
  -- Nonzero facts
  have ha0 : a ≠ 0 := ha.ne'
  have hb0 : b ≠ 0 := (ha.trans_le hab).ne'
  have hδ0' : δ ≠ 0 := hδ0.ne'
  have hCs0 : Csplit ≠ 0 := by
    have hpos : (0 : ℝ≥0) < 1 := by norm_num
    have hpos' : 0 < Csplit := hpos.trans_le hCs1
    exact hpos'.ne'
  have hnts0 : (nts : ℝ≥0) ≠ 0 := by exact_mod_cast hnts
  -- Step 1: combine hsplit and h64out into a single bound
  have hstep : μqT ≤ (Csplit : ℝ≥0∞) * ((a : ℝ≥0∞) ^ (-(ε / 3)) * CF ^ (1 - β / 2)
      * ((Csplit * (b / a) : ℝ≥0) : ℝ≥0∞) ^ (β / 2) * ((a : ℝ≥0∞) / (b : ℝ≥0∞))
      * (b : ℝ≥0∞) ^ (-2 * β) * ((b : ℝ≥0∞) ^ 2 * (nts : ℝ≥0∞)) ^ (1 - β / 2))
      * ((δ : ℝ≥0∞) ^ (-(ε / 3)) * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (1 - β)
        * ((a : ℝ≥0∞)⁻¹ * (δ : ℝ≥0∞)) ^ (-2 * β)
        * (((a : ℝ≥0∞) ^ 2)⁻¹ * (δ : ℝ≥0∞) ^ 2 * ((nq : ℝ≥0∞) / (nts : ℝ≥0∞)))
            ^ (1 - β / 2)) := by
    calc
      μqT ≤ (Csplit : ℝ≥0∞) * μW
          * ((δ : ℝ≥0∞) ^ (-(ε / 3)) * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (1 - β)
            * ((a : ℝ≥0∞)⁻¹ * (δ : ℝ≥0∞)) ^ (-2 * β)
            * (((a : ℝ≥0∞) ^ 2)⁻¹ * (δ : ℝ≥0∞) ^ 2 * ((nq : ℝ≥0∞) / (nts : ℝ≥0∞)))
                ^ (1 - β / 2)) := hsplit
      _ ≤ (Csplit : ℝ≥0∞) * ((a : ℝ≥0∞) ^ (-(ε / 3)) * CF ^ (1 - β / 2)
          * ((Csplit * (b / a) : ℝ≥0) : ℝ≥0∞) ^ (β / 2) * ((a : ℝ≥0∞) / (b : ℝ≥0∞))
          * (b : ℝ≥0∞) ^ (-2 * β) * ((b : ℝ≥0∞) ^ 2 * (nts : ℝ≥0∞)) ^ (1 - β / 2))
          * ((δ : ℝ≥0∞) ^ (-(ε / 3)) * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (1 - β)
            * ((a : ℝ≥0∞)⁻¹ * (δ : ℝ≥0∞)) ^ (-2 * β)
            * (((a : ℝ≥0∞) ^ 2)⁻¹ * (δ : ℝ≥0∞) ^ 2 * ((nq : ℝ≥0∞) / (nts : ℝ≥0∞)))
                ^ (1 - β / 2)) := by
        gcongr
  -- Step 2: the NNReal identity
  have hNN : Csplit * (a ^ (-(ε / 3)) * (Csplit * (b / a)) ^ (β / 2) * (a / b) * b ^ (-2 * β)
        * (b ^ 2 * (nts : ℝ≥0)) ^ (1 - β / 2))
      * (δ ^ (-(ε / 3)) * (a / b) ^ (1 - β) * (a⁻¹ * δ) ^ (-2 * β)
        * ((a ^ 2)⁻¹ * δ ^ 2 * ((nq : ℝ≥0) / (nts : ℝ≥0))) ^ (1 - β / 2))
      = Csplit ^ (1 + β / 2) * a ^ (-(ε / 3)) * δ ^ (-(ε / 3)) * (a / b) ^ (3 * β / 2)
        * δ ^ (-2 * β) * (δ ^ 2 * (nq : ℝ≥0)) ^ (1 - β / 2) :=
    combineLocalFactor_rpow ha0 hb0 hδ0' hCs0 hnts
  -- Step 3: rewrite the hstep RHS into the target form (without the Frostman constant factor)
  set hstepRHS := (Csplit : ℝ≥0∞) * ((a : ℝ≥0∞) ^ (-(ε / 3)) * CF ^ (1 - β / 2)
    * ((Csplit * (b / a) : ℝ≥0) : ℝ≥0∞) ^ (β / 2) * ((a : ℝ≥0∞) / (b : ℝ≥0∞))
    * (b : ℝ≥0∞) ^ (-2 * β) * ((b : ℝ≥0∞) ^ 2 * (nts : ℝ≥0∞)) ^ (1 - β / 2))
    * ((δ : ℝ≥0∞) ^ (-(ε / 3)) * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (1 - β)
      * ((a : ℝ≥0∞)⁻¹ * (δ : ℝ≥0∞)) ^ (-2 * β)
      * (((a : ℝ≥0∞) ^ 2)⁻¹ * (δ : ℝ≥0∞) ^ 2 * ((nq : ℝ≥0∞) / (nts : ℝ≥0∞)))
          ^ (1 - β / 2)) with hhstepRHS
  have h_identity : hstepRHS = CF ^ (1 - β / 2)
      * ((Csplit : ℝ≥0∞) ^ ((1 : ℝ) + β / 2) * (a : ℝ≥0∞) ^ (-(ε / 3))
        * (δ : ℝ≥0∞) ^ (-(ε / 3)) * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (3 * β / 2)
        * (δ : ℝ≥0∞) ^ (-2 * β) * ((δ : ℝ≥0∞) ^ 2 * (nq : ℝ≥0∞)) ^ (1 - β / 2)) := by
    have hnn2 : (0 : ℝ) ≤ 1 - β / 2 := by linarith
    have hcoe_lhs : (((Csplit * (a ^ (-(ε / 3)) * (Csplit * (b / a)) ^ (β / 2) * (a / b) * b ^ (-2 * β) * (b ^ 2 * (nts : ℝ≥0)) ^ (1 - β / 2)) * (δ ^ (-(ε / 3)) * (a / b) ^ (1 - β) * (a⁻¹ * δ) ^ (-2 * β) * ((a ^ 2)⁻¹ * δ ^ 2 * ((nq : ℝ≥0) / (nts : ℝ≥0))) ^ (1 - β / 2))) : ℝ≥0) : ℝ≥0∞)
        = (Csplit : ℝ≥0∞) * ((a : ℝ≥0∞) ^ (-(ε / 3)) * ((Csplit * (b / a) : ℝ≥0) : ℝ≥0∞) ^ (β / 2) * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) * (b : ℝ≥0∞) ^ (-2 * β) * ((b : ℝ≥0∞) ^ 2 * (nts : ℝ≥0∞)) ^ (1 - β / 2)) * ((δ : ℝ≥0∞) ^ (-(ε / 3)) * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (1 - β) * ((a : ℝ≥0∞)⁻¹ * (δ : ℝ≥0∞)) ^ (-2 * β) * (((a : ℝ≥0∞) ^ 2)⁻¹ * (δ : ℝ≥0∞) ^ 2 * ((nq : ℝ≥0∞) / (nts : ℝ≥0∞))) ^ (1 - β / 2)) := by
      have ha_sq0 : (a : ℝ≥0) ^ 2 ≠ 0 := pow_ne_zero 2 ha0
      simp [ENNReal.coe_mul, ENNReal.coe_div hb0, ENNReal.coe_div hnts0,
        ENNReal.coe_inv ha0, ENNReal.coe_inv ha_sq0,
        ENNReal.coe_rpow_of_ne_zero ha0, ENNReal.coe_rpow_of_ne_zero hb0,
        ENNReal.coe_rpow_of_ne_zero hδ0',
        ENNReal.coe_rpow_of_ne_zero (div_ne_zero ha0 hb0),
        ENNReal.coe_rpow_of_ne_zero (mul_ne_zero (inv_ne_zero ha0) hδ0'),
        ENNReal.coe_rpow_of_ne_zero (mul_ne_zero hCs0 (div_ne_zero hb0 ha0)),
        ENNReal.coe_rpow_of_ne_zero (mul_ne_zero (pow_ne_zero 2 hb0) hnts0),
        ENNReal.coe_rpow_of_nonneg ((a ^ 2)⁻¹ * δ ^ 2 * ((nq : ℝ≥0) / (nts : ℝ≥0))) hnn2]
    have hcoe_rhs : (((Csplit ^ (1 + β / 2) * a ^ (-(ε / 3)) * δ ^ (-(ε / 3)) * (a / b) ^ (3 * β / 2) * δ ^ (-2 * β) * (δ ^ 2 * (nq : ℝ≥0)) ^ (1 - β / 2)) : ℝ≥0) : ℝ≥0∞)
        = (Csplit : ℝ≥0∞) ^ ((1 : ℝ) + β / 2) * (a : ℝ≥0∞) ^ (-(ε / 3)) * (δ : ℝ≥0∞) ^ (-(ε / 3)) * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (3 * β / 2) * (δ : ℝ≥0∞) ^ (-2 * β) * ((δ : ℝ≥0∞) ^ 2 * (nq : ℝ≥0∞)) ^ (1 - β / 2) := by
      simp [ENNReal.coe_mul, ENNReal.coe_div hb0,
        ENNReal.coe_rpow_of_ne_zero ha0,
        ENNReal.coe_rpow_of_ne_zero hδ0', ENNReal.coe_rpow_of_ne_zero hCs0,
        ENNReal.coe_rpow_of_ne_zero (div_ne_zero ha0 hb0),
        ENNReal.coe_rpow_of_nonneg (δ ^ 2 * (nq : ℝ≥0)) hnn2]
    rw [hhstepRHS, ← hcoe_rhs, ← hNN, hcoe_lhs]
    ring
  -- Now hstep gives μqT ≤ hstepRHS = CF^(1-β/2) * (Csplit^(1+β/2) * a^(-(ε/3)) * δ^(-(ε/3)) *...)
  have hstep' : μqT ≤ CF ^ (1 - β / 2)
      * ((Csplit : ℝ≥0∞) ^ ((1 : ℝ) + β / 2) * (a : ℝ≥0∞) ^ (-(ε / 3))
        * (δ : ℝ≥0∞) ^ (-(ε / 3)) * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (3 * β / 2)
        * (δ : ℝ≥0∞) ^ (-2 * β) * ((δ : ℝ≥0∞) ^ 2 * (nq : ℝ≥0∞)) ^ (1 - β / 2)) :=
    hstep.trans h_identity.le
  -- Step 4: the δ ≤ a implies a^(-(ε/3)) ≤ δ^(-(ε/3))
  have h_a_pow_inv : (a : ℝ≥0∞) ^ (-(ε / 3)) ≤ (δ : ℝ≥0∞) ^ (-(ε / 3)) := by
    have hδa_enn : (δ : ℝ≥0∞) ≤ (a : ℝ≥0∞) := by exact mod_cast hδa
    have h_nonneg : 0 ≤ ε / 3 := by nlinarith
    calc
      (a : ℝ≥0∞) ^ (-(ε / 3)) = ((a : ℝ≥0∞)⁻¹) ^ (ε / 3) := by
        rw [ENNReal.rpow_neg, ENNReal.inv_rpow]
      _ ≤ ((δ : ℝ≥0∞)⁻¹) ^ (ε / 3) := by
        refine ENNReal.rpow_le_rpow ?_ h_nonneg
        exact (ENNReal.inv_le_inv.mpr hδa_enn)
      _ = (δ : ℝ≥0∞) ^ (-(ε / 3)) := by
        rw [ENNReal.rpow_neg, ENNReal.inv_rpow]
  -- Step 5: δ^(-ε) splits into three factors
  have h_delta_pow_split : (δ : ℝ≥0∞) ^ (-ε)
      = (δ : ℝ≥0∞) ^ (-(ε / 3)) * (δ : ℝ≥0∞) ^ (-(ε / 3)) * (δ : ℝ≥0∞) ^ (-(ε / 3)) := by
    have hδ_nonzero : (δ : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ0'
    have hδ_not_top : (δ : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
    calc
      (δ : ℝ≥0∞) ^ (-ε) = (δ : ℝ≥0∞) ^ (-(ε / 3) + (-(ε / 3)) + (-(ε / 3))) := by ring
      _ = ((δ : ℝ≥0∞) ^ (-(ε / 3) + (-(ε / 3)))) * (δ : ℝ≥0∞) ^ (-(ε / 3)) := by
        rw [ENNReal.rpow_add (-(ε / 3) + (-(ε / 3))) (-(ε / 3)) hδ_nonzero hδ_not_top]
      _ = ((δ : ℝ≥0∞) ^ (-(ε / 3)) * (δ : ℝ≥0∞) ^ (-(ε / 3))) * (δ : ℝ≥0∞) ^ (-(ε / 3)) := by
        rw [ENNReal.rpow_add (-(ε / 3)) (-(ε / 3)) hδ_nonzero hδ_not_top]
      _ = (δ : ℝ≥0∞) ^ (-(ε / 3)) * (δ : ℝ≥0∞) ^ (-(ε / 3)) * (δ : ℝ≥0∞) ^ (-(ε / 3)) := by ring
  -- Step 6: key inequality using hthr and h_a_pow_inv
  have h_key_ineq : (Csplit : ℝ≥0∞) ^ ((1 : ℝ) + β / 2) * (a : ℝ≥0∞) ^ (-(ε / 3))
      * (δ : ℝ≥0∞) ^ (-(ε / 3)) ≤ (δ : ℝ≥0∞) ^ (-ε) := by
    calc
      (Csplit : ℝ≥0∞) ^ ((1 : ℝ) + β / 2) * (a : ℝ≥0∞) ^ (-(ε / 3))
          * (δ : ℝ≥0∞) ^ (-(ε / 3))
        ≤ (δ : ℝ≥0∞) ^ (-(ε / 3)) * (a : ℝ≥0∞) ^ (-(ε / 3))
          * (δ : ℝ≥0∞) ^ (-(ε / 3)) := by
          gcongr
        _ = ((a : ℝ≥0∞) ^ (-(ε / 3)) * (δ : ℝ≥0∞) ^ (-(ε / 3)))
          * (δ : ℝ≥0∞) ^ (-(ε / 3)) := by ring
        _ ≤ ((δ : ℝ≥0∞) ^ (-(ε / 3)) * (δ : ℝ≥0∞) ^ (-(ε / 3)))
          * (δ : ℝ≥0∞) ^ (-(ε / 3)) := by
          gcongr
        _ = (δ : ℝ≥0∞) ^ (-(ε / 3)) * (δ : ℝ≥0∞) ^ (-(ε / 3)) * (δ : ℝ≥0∞) ^ (-(ε / 3)) := by ring
        _ = (δ : ℝ≥0∞) ^ (-ε) := by rw [h_delta_pow_split]
  -- Step 7: final inequality
  calc
    μqT ≤ CF ^ (1 - β / 2)
        * ((Csplit : ℝ≥0∞) ^ ((1 : ℝ) + β / 2) * (a : ℝ≥0∞) ^ (-(ε / 3))
          * (δ : ℝ≥0∞) ^ (-(ε / 3)) * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (3 * β / 2)
          * (δ : ℝ≥0∞) ^ (-2 * β) * ((δ : ℝ≥0∞) ^ 2 * (nq : ℝ≥0∞)) ^ (1 - β / 2)) :=
      hstep'
    _ = CF ^ (1 - β / 2) * ((Csplit : ℝ≥0∞) ^ ((1 : ℝ) + β / 2) * (a : ℝ≥0∞) ^ (-(ε / 3))
        * (δ : ℝ≥0∞) ^ (-(ε / 3))) * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (3 * β / 2)
        * (δ : ℝ≥0∞) ^ (-2 * β) * ((δ : ℝ≥0∞) ^ 2 * (nq : ℝ≥0∞)) ^ (1 - β / 2) := by
      ring
    _ ≤ CF ^ (1 - β / 2) * (δ : ℝ≥0∞) ^ (-ε) * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (3 * β / 2)
        * (δ : ℝ≥0∞) ^ (-2 * β) * ((δ : ℝ≥0∞) ^ 2 * (nq : ℝ≥0∞)) ^ (1 - β / 2) := by
      gcongr
    _ = (δ : ℝ≥0∞) ^ (-ε) * CF ^ (1 - β / 2)
        * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (3 * β / 2)
        * (δ : ℝ≥0∞) ^ (-2 * β)
        * ((δ : ℝ≥0∞) ^ 2 * (nq : ℝ≥0∞)) ^ (1 - β / 2) := by ring

/-- **Absorbing the Frostman-transfer constant, high branch of GWZ Proposition 6.6(A).**

The `μ`-split hands Lemma 6.4 the transferred Frostman constant `Csplit · C_F` rather than `C_F`, so
after `Kakeya.combineLocalFactor` the bound carries `(Csplit · C_F) ^ (1 - β/2)` and a `δ ^ (-3ε/4)`.
Splitting the power and absorbing `Csplit ^ (1 - β/2)` into the remaining `δ ^ (-ε/4)` restores the
target shape.

The three trailing factors are abstract: in the application `Q = (a/b) ^ (3β/2)`,
`R = δ ^ (-2β)`, `S = (δ² |𝒯|) ^ (1 - β/2)`. Keeping them opaque is deliberate — it makes visible
that this step cannot disturb the eccentricity exponent `3β/2`. -/
theorem absorbSplitFrostmanConstant {β ε : ℝ} (hβle : β ≤ 1) {δ : ℝ≥0} (hδ0 : 0 < δ)
    {Csplit : ℝ≥0} {CF Q R S μ : ℝ≥0∞}
    (hthr2 : (Csplit : ℝ≥0∞) ^ (1 - β / 2) ≤ (δ : ℝ≥0∞) ^ (-(ε / 4)))
    (h : μ ≤ (δ : ℝ≥0∞) ^ (-(3 * ε / 4)) * ((Csplit : ℝ≥0∞) * CF) ^ (1 - β / 2)
          * Q * R * S) :
    μ ≤ (δ : ℝ≥0∞) ^ (-ε) * CF ^ (1 - β / 2) * Q * R * S := by
  have hδ_nonzero : (δ : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ0.ne'
  have hδ_not_top : (δ : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have h_δ_split : (δ : ℝ≥0∞) ^ (-ε) =
      (δ : ℝ≥0∞) ^ (-(3 * ε / 4)) * (δ : ℝ≥0∞) ^ (-(ε / 4)) := by
    calc
      (δ : ℝ≥0∞) ^ (-ε) = (δ : ℝ≥0∞) ^ ((-(3 * ε / 4)) + (-(ε / 4))) := by
        rw [show -ε = -(3 * ε / 4) + -(ε / 4) by ring]
      _ = (δ : ℝ≥0∞) ^ (-(3 * ε / 4)) * (δ : ℝ≥0∞) ^ (-(ε / 4)) :=
        ENNReal.rpow_add (-(3 * ε / 4)) (-(ε / 4)) hδ_nonzero hδ_not_top
  have h_CF_split : ((Csplit : ℝ≥0∞) * CF) ^ (1 - β / 2) =
      (Csplit : ℝ≥0∞) ^ (1 - β / 2) * CF ^ (1 - β / 2) := by
    have h_nonneg : 0 ≤ 1 - β / 2 := by linarith
    rw [ENNReal.mul_rpow_of_nonneg _ _ h_nonneg]
  calc
    μ ≤ (δ : ℝ≥0∞) ^ (-(3 * ε / 4)) * ((Csplit : ℝ≥0∞) * CF) ^ (1 - β / 2)
        * Q * R * S := h
    _ = ((Csplit : ℝ≥0∞) * CF) ^ (1 - β / 2) * (δ : ℝ≥0∞) ^ (-(3 * ε / 4))
        * Q * R * S := by ring
    _ = (CF ^ (1 - β / 2) * (Csplit : ℝ≥0∞) ^ (1 - β / 2)) * (δ : ℝ≥0∞) ^ (-(3 * ε / 4))
        * Q * R * S := by
      rw [h_CF_split]
      ring
    _ = CF ^ (1 - β / 2) * ((Csplit : ℝ≥0∞) ^ (1 - β / 2) * (δ : ℝ≥0∞) ^ (-(3 * ε / 4)))
        * Q * R * S := by ring
    _ ≤ CF ^ (1 - β / 2) * ((δ : ℝ≥0∞) ^ (-(ε / 4)) * (δ : ℝ≥0∞) ^ (-(3 * ε / 4)))
        * Q * R * S := by
      gcongr
    _ = CF ^ (1 - β / 2) * (δ : ℝ≥0∞) ^ (-ε) * Q * R * S := by
      calc
        CF ^ (1 - β / 2) * ((δ : ℝ≥0∞) ^ (-(ε / 4)) * (δ : ℝ≥0∞) ^ (-(3 * ε / 4)))
            * Q * R * S
        = CF ^ (1 - β / 2) * ((δ : ℝ≥0∞) ^ (-(3 * ε / 4)) * (δ : ℝ≥0∞) ^ (-(ε / 4)))
            * Q * R * S := by ring
        _ = CF ^ (1 - β / 2) * ((δ : ℝ≥0∞) ^ ((-(3 * ε / 4)) + (-(ε / 4))))
            * Q * R * S := by
          rw [ENNReal.rpow_add (-(3 * ε / 4)) (-(ε / 4)) hδ_nonzero hδ_not_top]
        _ = CF ^ (1 - β / 2) * (δ : ℝ≥0∞) ^ (-ε) * Q * R * S := by
          rw [show -(3 * ε / 4) + -(ε / 4) = -ε by ring]
    _ = (δ : ℝ≥0∞) ^ (-ε) * CF ^ (1 - β / 2) * Q * R * S := by ring


/-- **The whole small-`b` branch of GWZ Proposition 6.6(A), as scalar algebra.**

Everything geometric has already happened: `h64out` is the corrected Lemma 6.4 output for the outer
plank family, with concentration parameter `M = Cbig · (b/a)` where `Cbig = Cgeom · Cu · Csplit` is
the cross-parent loss, and Frostman constant the transferred `Csplit · C_F`; `hsplitineq` is the
Proposition 5.1 `μ`-split with its inner rescaled-tube factor.

Two constants have to be absorbed, and they are absorbed separately, which is the point of stating
this as its own lemma:

* `hthrBig` absorbs `Cbig ^ (1 + β/2)` — the `Cbig` that `Kakeya.combineLocalFactor` pays once for
  the split and once more as `M ^ (β/2)`.  This is the *only* new contribution of the cross-parent
  repair, and `Kakeya.crossParentThreshold` supplies it.
* `hthr2` absorbs `Csplit ^ (1 - β/2)`, the pre-existing Frostman-transfer loss.

The eccentricity factor `(a/b) ^ (3β/2)` in the conclusion is produced by
`Kakeya.combineLocalFactor` from `(a/b) ^ (-(β/2)) · (a/b) · (a/b) ^ (1-β)` and is untouched by
either absorption step (both go through `Kakeya.absorbSplitFrostmanConstant`, whose trailing factors
are opaque). -/
theorem localHighBranchBound {β ε : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1) (hε : 0 < ε)
    {δ a b : ℝ≥0} (hδ0 : 0 < δ) (ha_pos : 0 < a) (hab : a ≤ b) (hδa : δ ≤ a)
    {Csplit Cbig : ℝ≥0} (hCs1 : 1 ≤ Csplit) (hCsb : Csplit ≤ Cbig) (hCb1 : 1 ≤ Cbig)
    {CF : ℝ≥0∞} (hCF1 : 1 ≤ CF) (hCFtop : CF ≠ ⊤)
    {nq nts : ℕ} (hnts : nts ≠ 0)
    {μqT μW : ℝ≥0∞}
    (h64out : μW ≤ (a : ℝ≥0∞) ^ (-(ε / 4)) * ((Csplit : ℝ≥0∞) * CF) ^ (1 - β / 2)
        * ((Cbig * (b / a) : ℝ≥0) : ℝ≥0∞) ^ (β / 2) * ((a : ℝ≥0∞) / (b : ℝ≥0∞))
        * (b : ℝ≥0∞) ^ (-2 * β) * ((b : ℝ≥0∞) ^ 2 * (nts : ℝ≥0∞)) ^ (1 - β / 2))
    (hsplitineq : μqT ≤ (Csplit : ℝ≥0∞) * μW
        * ((δ : ℝ≥0∞) ^ (-(ε / 4)) * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (1 - β)
          * ((a : ℝ≥0∞)⁻¹ * (δ : ℝ≥0∞)) ^ (-2 * β)
          * (((a : ℝ≥0∞) ^ 2)⁻¹ * (δ : ℝ≥0∞) ^ 2 * ((nq : ℝ≥0∞) / (nts : ℝ≥0∞)))
              ^ (1 - β / 2)))
    (hthrBig : (Cbig : ℝ≥0∞) ^ ((1 : ℝ) + β / 2) ≤ (δ : ℝ≥0∞) ^ (-(ε / 4)))
    (hthr2 : (Csplit : ℝ≥0∞) ^ (1 - β / 2) ≤ (δ : ℝ≥0∞) ^ (-(ε / 4))) :
    μqT ≤ (δ : ℝ≥0∞) ^ (-ε) * CF ^ (1 - β / 2)
        * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (3 * β / 2)
        * (δ : ℝ≥0∞) ^ (-2 * β)
        * ((δ : ℝ≥0∞) ^ 2 * (nq : ℝ≥0∞)) ^ (1 - β / 2) := by
  -- Step 1: combineLocalFactor wants the same constant in `hsplitineq` as in `h64out`'s
  -- `(Cbig * (b/a))^(β/2)` concentration factor, so weaken the split constant `Csplit` to `Cbig`.
  have hsplitBig : μqT ≤ (Cbig : ℝ≥0∞) * μW
      * ((δ : ℝ≥0∞) ^ (-(ε / 4)) * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (1 - β)
        * ((a : ℝ≥0∞)⁻¹ * (δ : ℝ≥0∞)) ^ (-2 * β)
        * (((a : ℝ≥0∞) ^ 2)⁻¹ * (δ : ℝ≥0∞) ^ 2 * ((nq : ℝ≥0∞) / (nts : ℝ≥0∞)))
            ^ (1 - β / 2)) := by
    calc
      μqT ≤ (Csplit : ℝ≥0∞) * μW
          * ((δ : ℝ≥0∞) ^ (-(ε / 4)) * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (1 - β)
            * ((a : ℝ≥0∞)⁻¹ * (δ : ℝ≥0∞)) ^ (-2 * β)
            * (((a : ℝ≥0∞) ^ 2)⁻¹ * (δ : ℝ≥0∞) ^ 2 * ((nq : ℝ≥0∞) / (nts : ℝ≥0∞)))
                ^ (1 - β / 2)) := hsplitineq
      _ ≤ (Cbig : ℝ≥0∞) * μW
          * ((δ : ℝ≥0∞) ^ (-(ε / 4)) * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (1 - β)
            * ((a : ℝ≥0∞)⁻¹ * (δ : ℝ≥0∞)) ^ (-2 * β)
            * (((a : ℝ≥0∞) ^ 2)⁻¹ * (δ : ℝ≥0∞) ^ 2 * ((nq : ℝ≥0∞) / (nts : ℝ≥0∞)))
                ^ (1 - β / 2)) := by
        gcongr
  -- Step 2: rewrite the exponents so that `combineLocalFactor` applies with `ε' = 3ε/4`
  have h_eq : (3 * ε / 4) / 3 = ε / 4 := by ring
  have h64out' : μW ≤ (a : ℝ≥0∞) ^ (-((3 * ε / 4) / 3)) * ((Csplit : ℝ≥0∞) * CF) ^ (1 - β / 2)
      * ((Cbig * (b / a) : ℝ≥0) : ℝ≥0∞) ^ (β / 2) * ((a : ℝ≥0∞) / (b : ℝ≥0∞))
      * (b : ℝ≥0∞) ^ (-2 * β) * ((b : ℝ≥0∞) ^ 2 * (nts : ℝ≥0∞)) ^ (1 - β / 2) := by
    simpa [h_eq] using h64out
  have hsplitineq' : μqT ≤ (Cbig : ℝ≥0∞) * μW
      * ((δ : ℝ≥0∞) ^ (-((3 * ε / 4) / 3)) * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (1 - β)
        * ((a : ℝ≥0∞)⁻¹ * (δ : ℝ≥0∞)) ^ (-2 * β)
        * (((a : ℝ≥0∞) ^ 2)⁻¹ * (δ : ℝ≥0∞) ^ 2 * ((nq : ℝ≥0∞) / (nts : ℝ≥0∞)))
            ^ (1 - β / 2)) := by
    simpa [h_eq] using hsplitBig
  have hthr_combined : (Cbig : ℝ≥0∞) ^ ((1 : ℝ) + β / 2)
      ≤ (δ : ℝ≥0∞) ^ (-((3 * ε / 4) / 3)) := by
    simpa [h_eq] using hthrBig
  -- Step 3: apply `combineLocalFactor` with `ε' = 3ε/4` and the transferred Frostman constant
  have hε'pos : 0 < 3 * ε / 4 := by nlinarith
  have hCsplit_enn : 1 ≤ (Csplit : ℝ≥0∞) := by exact_mod_cast hCs1
  have hCFsplit1 : 1 ≤ (Csplit : ℝ≥0∞) * CF := by
    calc
      (1 : ℝ≥0∞) ≤ (Csplit : ℝ≥0∞) := hCsplit_enn
      _ = (Csplit : ℝ≥0∞) * (1 : ℝ≥0∞) := by simp
      _ ≤ (Csplit : ℝ≥0∞) * CF := mul_le_mul_of_nonneg_left hCF1 (by positivity)
  have hCFsplit_top : (Csplit : ℝ≥0∞) * CF ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top hCFtop
  have h_combined : μqT ≤ (δ : ℝ≥0∞) ^ (-(3 * ε / 4)) * ((Csplit : ℝ≥0∞) * CF) ^ (1 - β / 2)
      * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (3 * β / 2)
      * (δ : ℝ≥0∞) ^ (-2 * β)
      * ((δ : ℝ≥0∞) ^ 2 * (nq : ℝ≥0∞)) ^ (1 - β / 2) :=
    combineLocalFactor hβpos hβle hε'pos ha_pos hab hδ0 hδa (Csplit := Cbig) hCb1
      (CF := (Csplit : ℝ≥0∞) * CF) hCFsplit1 hCFsplit_top hnts
      (h64out := h64out') (hsplit := hsplitineq') (hthr := hthr_combined)
  -- Step 4: absorb the Frostman-transfer constant `Csplit ^ (1 - β/2)` into `δ ^ (-ε/4)`
  exact absorbSplitFrostmanConstant hβle hδ0 hthr2 h_combined

/-! ### Conditional analytic assembly

The following implication takes `Section6PartAAnalyticAssembly β` as an explicit
hypothesis. It also assumes `ParentOverlapAtDilatedPlanks`, which does not follow
from the parent system's bounded overlap alone. These assumptions describe the
analytic and geometric inputs of the implication.
-/

/-- **Absorbing a fixed constant into `δ ^ (-η)`, in `ℝ≥0`.**

For an absolute `C ≥ 1` and `η > 0` there is a threshold below which `C ≤ δ ^ (-η)`; take
`δ₀ = C ^ (-1/η)`.  This is the `ℝ≥0` companion of `Kakeya.rpowConstAbsorb` (which lives in
`ENNReal` and carries an extra power), and it is what lets the paper-facing wrapper feed the
*absolute* overlap constant of the constructed parent system into the internal theorem's
`Cu ≤ δ ^ (-η)` slot. -/
theorem exists_threshold_le_rpow_neg (C : ℝ≥0) (hC : 1 ≤ C) {η : ℝ} (hη : 0 < η) :
    ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧ ∀ δ : ℝ≥0, 0 < δ → δ ≤ δ₀ → C ≤ δ ^ (-η) := by
  have hC0 : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 1) hC
  have hη_ne : η ≠ 0 := by linarith
  set δ₀ : ℝ≥0 := C ^ (-1 / η) with hδ₀_def
  have hδ₀_pos : 0 < δ₀ := by
    rw [hδ₀_def]
    exact NNReal.rpow_pos hC0
  refine ⟨δ₀, hδ₀_pos, ?_⟩
  intro δ hδ hδle
  have hscalar : (-1 / η) * (-η) = (1 : ℝ) := by
    field_simp [hη_ne]
  have hδ₀_neg : δ₀ ^ (-η) = C := by
    rw [hδ₀_def]
    calc
      (C ^ (-1 / η)) ^ (-η) = C ^ ((-1 / η) * (-η)) := by rw [NNReal.rpow_mul]
      _ = C := by simp [hscalar]
  have hη_nonneg : 0 ≤ η := le_of_lt hη
  have h_pow_e : δ ^ η ≤ δ₀ ^ η := NNReal.rpow_le_rpow hδle hη_nonneg
  have hδrpow_pos : 0 < δ ^ η := NNReal.rpow_pos hδ
  have hδ₀rpow_pos : 0 < δ₀ ^ η := NNReal.rpow_pos hδ₀_pos
  have h_inv : (δ₀ ^ η)⁻¹ ≤ (δ ^ η)⁻¹ := (inv_le_inv₀ hδ₀rpow_pos hδrpow_pos).mpr h_pow_e
  calc
    C = δ₀ ^ (-η) := by rw [hδ₀_neg]
    _ = (δ₀ ^ η)⁻¹ := by rw [NNReal.rpow_neg]
    _ ≤ (δ ^ η)⁻¹ := h_inv
    _ = δ ^ (-η) := by rw [NNReal.rpow_neg]


/-- Absorb a fixed multiplicative loss across a positive real-power exponent gap. -/
theorem rpow_le_of_le_mul_of_loss_le {δ C F G : ℝ≥0} {small large : ℝ}
    (hδ0 : 0 < δ) (hC : C ≤ δ ^ (-(large - small)))
    (hF : δ ^ small ≤ F) (hFG : F ≤ C * G) : δ ^ large ≤ G := by
  have hδne : δ ≠ 0 := ne_of_gt hδ0
  have hle : δ ^ small ≤ δ ^ (-(large - small)) * G :=
    hF.trans <| hFG.trans <| mul_le_mul_of_nonneg_right hC (by positivity)
  have hmul : δ ^ (large - small) * δ ^ small ≤
      δ ^ (large - small) * (δ ^ (-(large - small)) * G) := by
    gcongr
  calc
    δ ^ large = δ ^ (large - small) * δ ^ small := by
      rw [← NNReal.rpow_add hδne]
      congr 1
      ring
    _ ≤ δ ^ (large - small) * (δ ^ (-(large - small)) * G) := hmul
    _ = G := by
      rw [← mul_assoc, ← NNReal.rpow_add hδne]
      simp

/-- **GWZ Lemma 6.1 (Katz--Tao case) read at the master scale, as an interface.**

The repository's Lemma 6.1 (`Kakeya.KatzTaoEstimate.plankEstimate`,
`Kakeya.KatzTaoEstimate.plankEstimate_of_isKatzTao`) states the fullness hypothesis, the
Katz--Tao hypothesis and the sub-polynomial loss all at the *plank* scale `a`:
`a ^ η ≤ λ(𝒫, Y)`, `Δ_max(𝒫) ≤ a ^ (-η)` and `μ ≤ a ^ (-ε) · (a/b) ^ (γβ) · |s| ^ β`.

Section 6 cannot feed it the outer plank family produced by GWZ Proposition 5.1.  Proposition 5.1
item 2 gives only `λ(𝒲, Y_𝒲) ⪆ λ(𝒯, Y) ^ 2`, hence — with the master-scale fullness hypothesis
`λ(𝒯, Y) ≥ δ ^ η` of Proposition 6.6 — only `λ(𝒲, Y_𝒲) ⪆ δ ^ (2η)`.  Writing `a = δ ^ t` with
`t ∈ [0, 1]`, the plank-scale hypothesis `a ^ ηₒ ≤ λ(𝒲, Y_𝒲)` needs `t · ηₒ ≥ 2η`, which fails for
every fixed `η > 0` as soon as `a` stays above a fixed constant (`t → 0`); and `a` is only known to
satisfy `δ ≤ ρ ≤ a ≤ b ≤ b₀`.  So the plank-scale reading is *not* available to Proposition 6.6(B),
while the master-scale reading below is: `δ ^ (2η) ≥ δ ^ ηₒ` as soon as the fine exponent is chosen
with `2η ≤ ηₒ`, which is exactly what the Proposition 5.1 leaf is free to do.

This declaration is therefore the master-scale (`δ`-scale) reading of GWZ Lemma 6.1 in the
Katz--Tao case: fullness `δ ^ η ≤ λ`, density `Δ_max ≤ δ ^ (-η)`, slab non-concentration with
`δ ^ (-η)`, and the correspondingly weaker loss `δ ^ (-ε)` in place of `a ^ (-ε)` (weaker because
`δ ≤ a`).  It is GWZ's own reading — in the paper every `⪅` and every fullness exponent in
Section 6 is at the master scale `δ` — and it is *not* derivable from the plank-scale version in the
repository, whose hypotheses are strictly stronger.  It is passed as an explicit hypothesis, in the
style of `Kakeya.KatzTaoEstimate` and `Kakeya.FrostmanEstimate`, rather than silently assumed;
proving it (by rerunning the Lemma 6.1 argument with all losses measured at `δ`) is the one item of
migration debt this interface repair creates. -/
def PlankEstimateAtMasterScale (β : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∃ b₀ > (0 : ℝ≥0),
    ∀ {ι : Type*} (s : Finset ι) {δ a b : ℝ≥0} (hab : a ≤ b) (hb1 : b ≤ 1)
      (V : ι → ShadedPlank a b hab hb1),
      0 < δ → δ ≤ a → b ≤ b₀ →
      (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ)) →
      (s : Set ι).Pairwise
        (fun i j => _root_.IsEssentiallyDistinct (V i).carrier (V j).carrier) →
      δ ^ η ≤ ShadedBody.fullness s (fun i => (V i).toShadedBody) →
      IsKatzTao s (fun i => (V i).toConvexSpaceBody) (δ ^ (-η)) →
      ∀ (γ : ℝ), 0 ≤ γ → γ ≤ 1 →
      (∀ (φ : ℝ≥0) (hφR : φ ≤ Rslab), a / b ≤ φ →
          ∀ (S : Prism3D φ Rslab Rslab hφR le_rfl),
          ((Plank.inWideSlabFamily s (fun i => (V i).toPrism3D) S).card : ℝ≥0)
            ≤ δ ^ (-η) * φ ^ γ * (s.card : ℝ≥0)) →
        ShadedBody.multiplicity s (fun i => (V i).toShadedBody) ≤
          (δ : ℝ≥0∞) ^ (-ε) * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (γ * β)
            * (s.card : ℝ≥0∞) ^ β

/-- **GWZ Lemma 6.1 at the master scale, density form.**

`Kakeya.PlankEstimateAtMasterScale` is the master-scale reading of
`Kakeya.KatzTaoEstimate.plankEstimate_of_isKatzTao`: it *consumes* a Katz--Tao bound and its
conclusion carries no `Δ_max` factor.  The inner (`γ = 1`) application in Proposition 6.6(B) needs
the other shape — the master-scale reading of `Kakeya.KatzTaoEstimate.plankEstimate` itself, whose
conclusion retains the factor `Δ_max(𝒫) ^ (1 - β)`.  That factor is not decoration: it is what
carries the fine family's maximal density through the split into the final bound of
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation`, via the inner density transfer
`Δ_max(inner) ≤ Cinner · Δ_max(𝒯)` supplied by `Kakeya.factoringAndMultPropGlobal`.

Why the master scale is forced here.  After the interface repair, the inner family produced by
Proposition 5.1 carries its fullness and slab non-concentration data at `δ`, not at the inner plank
scale `a'`: Proposition 5.1 controls the *fine* family at the master scale, and the normalisation
that produces the inner planks cannot manufacture a bound at `a'` out of one at `δ`.  Since
`δ ≤ a' ≤ 1`, the `δ`-scale forms `δ ^ ηᵢ ≤ λ` and `count ≤ δ ^ (-ηᵢ) · φ ^ γ · |qj|` are strictly
weaker than the `a'`-scale forms the plank-scale Lemma 6.1 demands, so the plank-scale reading is
simply not applicable to the inner family.

Essential distinctness is retained as a hypothesis, exactly as in the plank-scale original: it is
what prevents a family from repeating one plank arbitrarily often, and no reading of Lemma 6.1 in
this repository dispenses with it.

Like `Kakeya.PlankEstimateAtMasterScale`, this is passed as an explicit hypothesis rather than
silently assumed; proving it (by rerunning the Lemma 6.1 argument with every loss measured at `δ`)
is migration debt, not a gap that is hidden anywhere. -/
def PlankEstimateAtMasterScaleWithDensity (β : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∃ b₀ > (0 : ℝ≥0),
    ∀ {ι : Type*} (s : Finset ι) {δ a b : ℝ≥0} (hab : a ≤ b) (hb1 : b ≤ 1)
      (V : ι → ShadedPlank a b hab hb1),
      0 < δ → δ ≤ a → b ≤ b₀ →
      (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ)) →
      (s : Set ι).Pairwise
        (fun i j => _root_.IsEssentiallyDistinct (V i).carrier (V j).carrier) →
      δ ^ η ≤ ShadedBody.fullness s (fun i => (V i).toShadedBody) →
      ∀ (γ : ℝ), 0 ≤ γ → γ ≤ 1 →
      (∀ (φ : ℝ≥0) (hφR : φ ≤ Rslab), a / b ≤ φ →
          ∀ (S : Prism3D φ Rslab Rslab hφR le_rfl),
          ((Plank.inWideSlabFamily s (fun i => (V i).toPrism3D) S).card : ℝ≥0)
            ≤ δ ^ (-η) * φ ^ γ * (s.card : ℝ≥0)) →
        ShadedBody.multiplicity s (fun i => (V i).toShadedBody) ≤
          (δ : ℝ≥0∞) ^ (-ε)
            * (maxDensity s (fun i => (V i).toConvexSpaceBody)) ^ (1 - β)
            * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (γ * β) * (s.card : ℝ≥0∞) ^ β

end Kakeya

end

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.WangZahl.EToD

/-!
The `sigma`-direction calculus for the Wang--Zahl assertions.

Source: Wang--Zahl, Definition `defnCDE` and the
paragraph following Proposition `improvingProp` (Section 1.3), where the two
elementary facts

  `FS(T) * (#T) |T|^{1/2} >= 1`      and      `#T <~ delta^{-4}`

are used to (a) raise `sigma`, (b) close the set of admissible `sigma` from
above, and (c) trade a gain in `omega` for a gain in `sigma`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory

namespace Kakeya.WangZahl

noncomputable section

universe u

/-- The Wang--Zahl currency `X = (#T) |T|^{1/2}` of a family of `delta`-tubes.
It is the quantity raised to the power `-sigma` in Assertion `D`. -/
def wzCurrency (δ : ℝ≥0) (n : ℕ) : ℝ≥0∞ :=
  (n : ℝ≥0∞) * (tubeVolume δ) ^ (1 / 2 : ℝ)

/-- **Lower** size bound on the Wang--Zahl currency `X = (#T)|T|^{1/2}`.

This is the observation recorded immediately after Definition `defnCDE` in the
source: a slab of thickness `|T|^{1/2}` containing one tube of the family
forces `FS(T) (#T)|T|^{1/2} >= 1`; with the Frostman hypothesis
`FS(T) <= delta^{-eta}` this gives `X >= C⁻¹ delta^{eta}`. -/
def CurrencyLowerBound (C : ℝ≥0) : Prop :=
  ∀ {δ : ℝ≥0}, 0 < δ → δ ≤ 1 → ∀ {η : ℝ}, 0 < η →
    ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3),
      s.Nonempty → IsTubeShadingFamily s T →
      katzTaoConvexWolffConstant s T ≤ (δ : ℝ≥0∞) ^ (-η) →
      frostmanSlabWolffConstant s T ≤ (δ : ℝ≥0∞) ^ (-η) →
      ((C : ℝ≥0∞))⁻¹ * (δ : ℝ≥0∞) ^ η ≤ wzCurrency δ s.card

/-- **Upper** size bound on the Wang--Zahl currency `X = (#T)|T|^{1/2}`,
obtained from the Katz--Tao hypothesis applied to the unit ball. -/
def CurrencyUpperBound (C : ℝ≥0) : Prop :=
  ∀ {δ : ℝ≥0}, 0 < δ → δ ≤ 1 → ∀ {η : ℝ}, 0 < η →
    ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3),
      s.Nonempty → IsTubeShadingFamily s T →
      katzTaoConvexWolffConstant s T ≤ (δ : ℝ≥0∞) ^ (-η) →
      frostmanSlabWolffConstant s T ≤ (δ : ℝ≥0∞) ^ (-η) →
      wzCurrency δ s.card ≤ (C : ℝ≥0∞) * (δ : ℝ≥0∞) ^ (-η - 1)

/-- Antitonicity of `ENNReal` rpow in the base at a nonpositive exponent. -/
lemma rpow_le_rpow_of_nonpos {x y : ℝ≥0∞} {z : ℝ} (h : x ≤ y) (hz : z ≤ 0) :
    y ^ z ≤ x ^ z := by
  have h1 : x ^ (-z) ≤ y ^ (-z) := ENNReal.rpow_le_rpow h (by linarith)
  have h2 := ENNReal.inv_le_inv.mpr h1
  rwa [ENNReal.rpow_neg, ENNReal.rpow_neg, inv_inv, inv_inv] at h2

/-! ### The upper currency bound, proved -/

/-- Volume of the closed unit ball of `Space3`, as a positive finite number. -/
lemma volume_unitBall_ne_top : volume (Metric.closedBall (0 : Space3) 1) ≠ ⊤ :=
  measure_closedBall_lt_top.ne

lemma volume_unitBall_ne_zero : volume (Metric.closedBall (0 : Space3) 1) ≠ 0 := by
  have h1 : (0 : ℝ≥0∞) < volume (Metric.ball (0 : Space3) 1) :=
    Metric.measure_ball_pos volume 0 one_pos
  exact (h1.trans_le (measure_mono Metric.ball_subset_closedBall)).ne'

/-- Both currency bounds weaken as the constant grows. -/
theorem CurrencyLowerBound.mono {C C' : ℝ≥0} (h : C ≤ C')
    (hC : CurrencyLowerBound.{u} C) : CurrencyLowerBound.{u} C' := by
  intro δ hδ hδ1 η hη ι s T hs hfamily hm hell
  refine le_trans ?_ (hC hδ hδ1 hη s T hs hfamily hm hell)
  gcongr

theorem CurrencyUpperBound.mono {C C' : ℝ≥0} (h : C ≤ C')
    (hC : CurrencyUpperBound.{u} C) : CurrencyUpperBound.{u} C' := by
  intro δ hδ hδ1 η hη ι s T hs hfamily hm hell
  refine le_trans (hC hδ hδ1 hη s T hs hfamily hm hell) ?_
  gcongr

end

end Kakeya.WangZahl

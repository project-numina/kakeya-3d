/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.FlatPrismInnerEstimate

/-!
# GWZ Lemma 6.1 at the master scale and Proposition 6.6(B) over the Part-B datum

`Kakeya.KatzTaoEstimate.plankEstimateAtMasterScale` shows the Katz--Tao (`gamma = 0`) reading
of GWZ Lemma 6.1, `PlankEstimateAtMasterScale beta`, follows from `KatzTaoEstimate beta`, by
specialising the density reading `plankEstimateAtMasterScaleWithDensity` from
`FlatPrismInnerEstimate`. With both readings discharged,
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_of_partBData` states GWZ Proposition 6.6(B)
over `Section6PartBData` from `K_KT(beta)` and `K_F(beta)` alone; its docstring records the
remaining gap to the project statement `tubeMultiplicityOfGlobalPlankFactorisation` and why the
per-scale uniformity binder was removed.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ConvexSpaceBody

noncomputable section

namespace Kakeya

/-- **The master-scale Katz--Tao reading of GWZ Lemma 6.1 is a theorem, not a hypothesis.** -/
theorem KatzTaoEstimate.plankEstimateAtMasterScale {β : ℝ}
    (hβpos : 0 < β) (hβle : β ≤ 1)
    (hKKT : KatzTaoEstimate.{0} (EuclideanSpace ℝ (Fin 3)) β) :
    PlankEstimateAtMasterScale.{0} β := by
  intro ε hε
  obtain ⟨η, hη, b₀, hb₀, hbound⟩ :=
    KatzTaoEstimate.plankEstimateAtMasterScaleWithDensity hβpos hβle hKKT (ε / 2) (by positivity)
  refine ⟨min η (ε / 2), lt_min hη (by positivity), b₀, hb₀, ?_⟩
  intro ι s δ a b hab hb1 V hδ hδa hbb₀ hwin hed hfull hKT γ hγ0 hγ1 hslab
  have hδ1 : δ ≤ 1 := hδa.trans (hab.trans hb1)
  have hηmin : min η (ε / 2) ≤ η := min_le_left _ _
  have hηε : min η (ε / 2) ≤ ε / 2 := min_le_right _ _
  -- fullness transfers
  have hfull' : (δ : ℝ≥0) ^ η ≤ ShadedBody.fullness s (fun i => (V i).toShadedBody) :=
    le_trans (NNReal.rpow_le_rpow_of_exponent_ge hδ hδ1 hηmin) hfull
  -- slab transfers
  have hslab' : ∀ (φ : ℝ≥0) (hφR : φ ≤ Rslab), a / b ≤ φ →
      ∀ (S : Prism3D φ Rslab Rslab hφR le_rfl),
      ((Plank.inWideSlabFamily s (fun i => (V i).toPrism3D) S).card : ℝ≥0)
        ≤ δ ^ (-η) * φ ^ γ * (s.card : ℝ≥0) := by
    intro φ hφR hφ S
    refine (hslab φ hφR hφ S).trans ?_
    have hrp : (δ : ℝ≥0) ^ (-(min η (ε / 2))) ≤ (δ : ℝ≥0) ^ (-η) :=
      NNReal.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hηmin)
    exact mul_le_mul_left (mul_le_mul_left hrp _) _
  have hmain := hbound s hab hb1 V hδ hδa hbb₀ hwin hed hfull' γ hγ0 hγ1 hslab'
  refine hmain.trans ?_
  have hδ0' : ((δ : ℝ≥0∞)) ≠ 0 := by
    simpa using hδ.ne'
  have hδtop : ((δ : ℝ≥0∞)) ≠ ⊤ := ENNReal.coe_ne_top
  have hδ1' : ((δ : ℝ≥0∞)) ≤ 1 := by exact_mod_cast hδ1
  have hdens : maxDensity s (fun i => (V i).toConvexSpaceBody) ^ (1 - β)
      ≤ (δ : ℝ≥0∞) ^ (-(ε / 2)) := by
    have h1 : maxDensity s (fun i => (V i).toConvexSpaceBody) ^ (1 - β)
        ≤ ((δ : ℝ≥0∞) ^ (-(min η (ε / 2)))) ^ (1 - β) :=
      ENNReal.rpow_le_rpow hKT (by linarith)
    refine h1.trans ?_
    rw [← ENNReal.rpow_mul]
    refine ENNReal.rpow_le_rpow_of_exponent_ge hδ1' ?_
    nlinarith [min_le_right η (ε / 2), lt_min hη (show (0:ℝ) < ε/2 by positivity)]
  calc
    (δ : ℝ≥0∞) ^ (-(ε / 2)) * maxDensity s (fun i => (V i).toConvexSpaceBody) ^ (1 - β)
        * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (γ * β) * (s.card : ℝ≥0∞) ^ β
      ≤ (δ : ℝ≥0∞) ^ (-(ε / 2)) * (δ : ℝ≥0∞) ^ (-(ε / 2))
        * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (γ * β) * (s.card : ℝ≥0∞) ^ β := by
        gcongr
    _ = (δ : ℝ≥0∞) ^ (-ε) * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (γ * β)
        * (s.card : ℝ≥0∞) ^ β := by
        rw [← ENNReal.rpow_add _ _ hδ0' hδtop]
        ring_nf

end Kakeya

end

end

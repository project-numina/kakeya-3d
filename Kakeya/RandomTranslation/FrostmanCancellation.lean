/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.FrostmanConstant
public import Kakeya.RandomTranslation.RigidMotionED
public import Kakeya.Tube.EDPacking.ConvexCount

/-!
# The canonical Frostman cancellation of GWZ Lemma 3.8

GWZ take `J = C_F(𝕋)` random rigid copies, where `C_F(𝕋)` is the **actual** Frostman constant of the
family. The whole argument rests on the resulting cancellation

`J · 𝔼[X_j] ≲ 1`,

with a bound depending only on the dimension — not on `C_F`, not on `δ`, and not on `|s|`. This file
proves it.

## The algebra

Writing `|T_δ| ≍ δ^(n-1)` for the volume of a `δ`-tube and `Δ_max` for the maximal density,

```
C_F · |s| · |T_δ|²  ≤  (Δ_max / Δ(𝕋, B₁)) · |s| · |T_δ|²
                    =  Δ_max · |B₁| · |T_δ|
                    ≤  C_dim,
```

where the middle step uses `Δ(𝕋, B₁) ≥ |s| · c_n δ^(n-1) / |B₁|` (each tube has volume at least
`c_n δ^(n-1)`, `Tube.le_volume`) and the last uses `Δ_max ≲ δ^(-(n-1))` for a pairwise
essentially distinct family (`Kakeya.maxDensity_le_of_ED`). The two powers of `δ^(n-1)` cancel
against `Δ_max`'s `δ^(-(n-1))`, which is exactly why the exponent `2` in GWZ (106) is essential.

The passage from `Δ_max / Δ(𝕋,B₁)` to the canonical `ConvexSpaceBody.frostmanConstant` is
`ConvexSpaceBody.IsFrostmanIn.of_maxDensity_le` followed by
`ConvexSpaceBody.frostmanConstant_le_of_isFrostmanIn`; no near-maximiser of the `sInf` is needed.

`J = ⌈C_F⌉₊` differs from `C_F` by at most `1`, which is absorbed harmlessly.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Set

namespace Kakeya

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **The rpow/natural-power cancellation.** `Kakeya.maxDensity_le_of_ED` produces the factor
`δ^(-(n-1))` as a real `rpow` inside `ENNReal.ofReal`, whereas the tube-volume lower bound produces
`δ^(n-1)` as a natural power in `ENNReal`. This isolates the one place where the two must be
reconciled, keeping it out of the main argument. -/
theorem ofReal_rpow_neg_mul_pow_eq_one {n : ℕ} (hn : 1 ≤ n) {δ : ℝ≥0} (hδ : 0 < δ) :
    ENNReal.ofReal ((δ : ℝ) ^ (-((n : ℝ) - 1))) * (δ : ℝ≥0∞) ^ (n - 1) = 1 := by
  have hδr : (0 : ℝ) < (δ : ℝ) := NNReal.coe_pos.mpr hδ
  have hP : (δ : ℝ≥0∞) ^ (n - 1) = ENNReal.ofReal ((δ : ℝ) ^ (n - 1)) := by
    rw [ENNReal.ofReal_pow hδr.le, ENNReal.ofReal_coe_nnreal]
  rw [hP, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδr.le _)]
  have hcast : (((n - 1 : ℕ) : ℝ)) = (n : ℝ) - 1 := by
    have : (1 : ℕ) ≤ n := hn
    push_cast [Nat.cast_sub this]
    ring
  rw [← Real.rpow_natCast (δ : ℝ) (n - 1), hcast]
  rw [← Real.rpow_add hδr]
  norm_num

/-- **The core cancellation.** For a pairwise essentially distinct family of `δ`-tubes in the unit
ball, the canonical Frostman constant times `|s| · δ^(2(n-1))` is bounded by a dimensional
constant.

The statement is normalised by the fixed dimensional constant `cₙ = Tube.le_volume.c n` (the least
volume of a `δ`-tube, in units of `δ^(n-1)`) so that no division appears; since `0 < cₙ` this is
equivalent to the unnormalised form. -/
theorem frostmanConstant_mul_card_mul_pow_le [Nontrivial E] (hn : 1 < Module.finrank ℝ E) :
    ∃ (C : ℝ≥0∞) (δ₀ : ℝ≥0), C ≠ ⊤ ∧ 0 < δ₀ ∧
      ∀ {δ : ℝ≥0}, 0 < δ → δ ≤ δ₀ →
      ∀ {ι : Type*} (s : Finset ι) (T : ι → Tube δ E),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
        (s : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        ((Tube.le_volume.c (Module.finrank ℝ E) : ℝ≥0) : ℝ≥0∞)
            * (ConvexSpaceBody.frostmanConstant s (fun i => (T i).toConvexSpaceBody)
                  ConvexSpaceBody.closedUnitBall
                * (s.card : ℝ≥0∞) * (δ : ℝ≥0∞) ^ (2 * (Module.finrank ℝ E - 1)))
          ≤ C := by
  classical
  obtain ⟨Cₘ, δ₀r, hCₘpos, hδ₀rpos, _hδ₀rle₁, hΔmax⟩ :=
    Kakeya.maxDensity_le_of_ED (E := E) hn
  set n : ℕ := Module.finrank ℝ E
  set B₁ : ConvexSpaceBody E := ConvexSpaceBody.closedUnitBall
  set cₙ : ℝ≥0 := Tube.le_volume.c n
  set δ₀ : ℝ≥0 := δ₀r.toNNReal
  let C : ℝ≥0∞ := ENNReal.ofReal Cₘ * volume B₁.carrier
  have hδ₀eq : (δ₀ : ℝ) = δ₀r := by
    change (δ₀r.toNNReal : ℝ) = δ₀r
    exact Real.coe_toNNReal δ₀r hδ₀rpos.le
  have hδ₀pos : 0 < δ₀ := by
    rw [← NNReal.coe_pos]
    rw [hδ₀eq]
    exact hδ₀rpos
  refine ⟨C, δ₀, ?_, hδ₀pos, ?_⟩
  · dsimp [C]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top B₁.isCompact.measure_lt_top.ne
  · intro δ hδpos hδle ι s T hSub hED
    by_cases hs : s = ∅
    · subst s
      simp
    · have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs
      let w : ι → ConvexSpaceBody E := fun i => (T i).toConvexSpaceBody
      let S : ℝ≥0∞ := ∑ i ∈ s, volume (w i).carrier
      let F : ℝ≥0∞ := ConvexSpaceBody.frostmanConstant s w B₁
      let D : ℝ≥0∞ := Kakeya.densityIn s w B₁
      let M : ℝ≥0∞ := Kakeya.maxDensity s w
      let P : ℝ≥0∞ := (δ : ℝ≥0∞) ^ (n - 1)
      let xa : ℝ := (δ : ℝ) ^ (-((n : ℝ) - 1))
      have hWB : ∀ i ∈ s, w i ≤ B₁ := by
        intro i hi
        exact SetLike.coe_subset_coe.mp (by
          calc
            (w i : Set E) = (T i).carrier := rfl
            _ ⊆ Metric.closedBall (0 : E) 1 := hSub i hi
            _ = (B₁ : Set E) := rfl)
      have hTvol : ∀ i ∈ s, (cₙ : ℝ≥0∞) * P ≤ volume (w i).carrier := by
        intro i hi
        simpa [w, P, cₙ, ENNReal.coe_mul, ENNReal.coe_pow] using (Tube.le_volume (T i))
      have hδne0 : δ ≠ 0 := ne_of_gt hδpos
      have hδne0e : (δ : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hδne0
      have hPne : P ≠ 0 := by
        dsimp [P]
        exact pow_ne_zero (n - 1) hδne0e
      have hcₙne : (cₙ : ℝ≥0∞) ≠ 0 :=
        ENNReal.coe_ne_zero.mpr (Tube.le_volume.c_pos n).ne'
      have hcP : (cₙ : ℝ≥0∞) * P ≠ 0 := mul_ne_zero hcₙne hPne
      have hcPpos : 0 < (cₙ : ℝ≥0∞) * P := lt_of_le_of_ne zero_le hcP.symm
      have hDpos : 0 < D := by
        rw [Kakeya.densityIn_pos_iff]
        obtain ⟨i, hi⟩ := hsne
        refine ⟨i, hi, ?_, ?_⟩
        · exact lt_of_lt_of_le hcPpos (hTvol i hi)
        · exact hWB i hi
      have hDne : D ≠ 0 := ne_of_gt hDpos
      have hDtop : D ≠ ⊤ := Kakeya.densityIn_ne_top s w B₁
      have hDS : D * volume B₁.carrier = S := by
        have h := Kakeya.sum_volume_eq_densityIn_mul_volume' (K := B₁) hWB
        simpa [D, S, w] using h.symm
      have hDiv : (M / D) * D = M := ENNReal.div_mul_cancel hDne hDtop
      have hIsF : ConvexSpaceBody.IsFrostmanIn s w B₁ (M / D) :=
        ConvexSpaceBody.IsFrostmanIn.of_maxDensity_le
          (le_of_eq (ENNReal.div_mul_cancel hDne hDtop).symm)
      have hCF : F ≤ M / D := ConvexSpaceBody.frostmanConstant_le_of_isFrostmanIn hIsF
      have hkey1 : F * D ≤ M := by
        calc
          F * D ≤ (M / D) * D := mul_le_mul hCF le_rfl zero_le zero_le
          _ = M := hDiv
      have hkey : F * S ≤ M * volume B₁.carrier := by
        calc
          F * S = F * (D * volume B₁.carrier) := by rw [hDS]
          _ = (F * D) * volume B₁.carrier := by rw [mul_assoc]
          _ ≤ M * volume B₁.carrier := mul_le_mul hkey1 le_rfl zero_le zero_le
      have hS_lower : (s.card : ℝ≥0∞) * ((cₙ : ℝ≥0∞) * P) ≤ S := by
        dsimp [S]
        calc
          (s.card : ℝ≥0∞) * ((cₙ : ℝ≥0∞) * P) = ∑ _i ∈ s, (cₙ : ℝ≥0∞) * P := by
            rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ∑ i ∈ s, volume (w i).carrier := Finset.sum_le_sum (fun i hi => hTvol i hi)
      have hδler : (δ : ℝ) ≤ δ₀r := by
        rw [← hδ₀eq]
        exact NNReal.coe_le_coe.mpr hδle
      have hΔmaxle : M ≤ ENNReal.ofReal (Cₘ * xa) := by
        dsimp [M, xa, w]
        simpa using hΔmax hδpos hδler s T hED
      have hpow2 : (δ : ℝ≥0∞) ^ (2 * (n - 1)) = P * P := by
        rw [two_mul, pow_add]
      have hDstep : (cₙ : ℝ≥0∞) * (F * (s.card : ℝ≥0∞) * P) ≤ M * volume B₁.carrier := by
        calc
          (cₙ : ℝ≥0∞) * (F * (s.card : ℝ≥0∞) * P)
              = F * ((s.card : ℝ≥0∞) * ((cₙ : ℝ≥0∞) * P)) := by ac_rfl
          _ ≤ F * S := mul_le_mul_right hS_lower F
          _ ≤ M * volume B₁.carrier := hkey
      have hDstep2 :
          (cₙ : ℝ≥0∞) * (F * (s.card : ℝ≥0∞) * P * P) ≤ M * volume B₁.carrier * P := by
        calc
          (cₙ : ℝ≥0∞) * (F * (s.card : ℝ≥0∞) * P * P)
              = ((cₙ : ℝ≥0∞) * (F * (s.card : ℝ≥0∞) * P)) * P := by ac_rfl
          _ ≤ (M * volume B₁.carrier) * P := mul_le_mul_left hDstep P
      have hDstep3 : (cₙ : ℝ≥0∞) * (F * (s.card : ℝ≥0∞) * P * P) ≤
          ENNReal.ofReal (Cₘ * xa) * volume B₁.carrier * P := by
        calc
          (cₙ : ℝ≥0∞) * (F * (s.card : ℝ≥0∞) * P * P) ≤ M * volume B₁.carrier * P := hDstep2
          _ ≤ ENNReal.ofReal (Cₘ * xa) * volume B₁.carrier * P :=
            mul_le_mul (mul_le_mul hΔmaxle le_rfl zero_le zero_le) le_rfl zero_le zero_le
      have hxP : ENNReal.ofReal xa * P = 1 := by
        dsimp [xa, P]
        exact ofReal_rpow_neg_mul_pow_eq_one (le_of_lt hn) hδpos
      have hcan : ENNReal.ofReal (Cₘ * xa) * P = ENNReal.ofReal Cₘ := by
        calc
          ENNReal.ofReal (Cₘ * xa) * P
              = (ENNReal.ofReal Cₘ * ENNReal.ofReal xa) * P := by
                  rw [ENNReal.ofReal_mul hCₘpos.le]
          _ = ENNReal.ofReal Cₘ * (ENNReal.ofReal xa * P) := by ac_rfl
          _ = ENNReal.ofReal Cₘ * 1 := by rw [hxP]
          _ = ENNReal.ofReal Cₘ := by rw [mul_one]
      have hfin : (cₙ : ℝ≥0∞) * (F * (s.card : ℝ≥0∞) * P * P) ≤
          ENNReal.ofReal Cₘ * volume B₁.carrier := by
        calc
          (cₙ : ℝ≥0∞) * (F * (s.card : ℝ≥0∞) * P * P) ≤
              ENNReal.ofReal (Cₘ * xa) * volume B₁.carrier * P := hDstep3
          _ = (ENNReal.ofReal (Cₘ * xa) * P) * volume B₁.carrier := by ac_rfl
          _ = ENNReal.ofReal Cₘ * volume B₁.carrier := by rw [hcan]
      have hgoal :
          (cₙ : ℝ≥0∞) * (F * (s.card : ℝ≥0∞) * (δ : ℝ≥0∞) ^ (2 * (n - 1))) ≤ C := by
        calc
          (cₙ : ℝ≥0∞) * (F * (s.card : ℝ≥0∞) * (δ : ℝ≥0∞) ^ (2 * (n - 1)))
              = (cₙ : ℝ≥0∞) * (F * (s.card : ℝ≥0∞) * P * P) := by
                  rw [hpow2]
                  ac_rfl
          _ ≤ ENNReal.ofReal Cₘ * volume B₁.carrier := hfin
          _ = C := by rfl
      simpa [F, w, B₁] using hgoal

end

end Kakeya

end

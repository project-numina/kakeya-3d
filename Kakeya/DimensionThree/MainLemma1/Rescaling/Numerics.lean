/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Rescaling.Bracket

/-!
# Main Lemma 1, Case (ii): The bracket powers and the numeric bookkeeping

Split out of `Kakeya/DimensionThree/MainLemma1/Rescaling.lean`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya

namespace ml1Boot

/-- **Both signs of the bracket exponent**.

If `C⁻¹ δ̃ ^ h ≤ Q ≤ C δ̃ ^ (-h)` with `C ≥ 1`, `h ≥ 0` and `0 < δ̃ ≤ 1`, then
`Q ^ e ≤ C δ̃ ^ (-h)` for every `e ∈ [-1, 1]`.  This is what lets the sign of
`e = γ/2 + β' - 1` be left open in `Kakeya.ml1Boot.multiplicity_coarse_le`. -/
theorem bracket_rpow_le {δt : ℝ≥0} (hδt1 : δt ≤ 1) {C : ℝ≥0}
    (hC : 1 ≤ C) {h : ℝ} (hh : 0 ≤ h) {Q : ℝ≥0∞}
    (hlb : (C : ℝ≥0∞)⁻¹ * (δt : ℝ≥0∞) ^ h ≤ Q)
    (hub : Q ≤ (C : ℝ≥0∞) * (δt : ℝ≥0∞) ^ (-h))
    {e : ℝ} (he0 : -1 ≤ e) (he1 : e ≤ 1) :
    Q ^ e ≤ (C : ℝ≥0∞) * (δt : ℝ≥0∞) ^ (-h) := by
  set B : ℝ≥0∞ := (C : ℝ≥0∞) * (δt : ℝ≥0∞) ^ (-h) with hB
  have hD : (δt : ℝ≥0∞) ≤ 1 := by exact_mod_cast hδt1
  have hC' : 1 ≤ (C : ℝ≥0∞) := by exact_mod_cast hC
  have hDpow1 : 1 ≤ (δt : ℝ≥0∞) ^ (-h) := by
    have := ENNReal.rpow_le_rpow_of_exponent_ge hD (neg_nonpos.mpr hh)
    simpa using this
  have hB1 : 1 ≤ B := by
    unfold B
    calc
      (1 : ℝ≥0∞) ≤ (C : ℝ≥0∞) := hC'
      _ = (C : ℝ≥0∞) * (1 : ℝ≥0∞) := by rw [mul_one]
      _ ≤ (C : ℝ≥0∞) * (δt : ℝ≥0∞) ^ (-h) := mul_le_mul_right hDpow1 (C : ℝ≥0∞)
  have inner : ∀ {R : ℝ≥0∞} {f : ℝ}, R ≤ B → 0 ≤ f → f ≤ 1 → R ^ f ≤ B := by
    intro R f hRleB hf0 hf1
    by_cases hR1 : R ≤ 1
    · have h1 : R ^ f ≤ (1 : ℝ≥0∞) ^ f := ENNReal.rpow_le_rpow hR1 hf0
      have h2 : (1 : ℝ≥0∞) ^ f = 1 := by simp
      rw [h2] at h1
      exact le_trans h1 hB1
    · have h1R : 1 ≤ R := le_of_not_ge hR1
      have hRle : R ^ f ≤ R := by
        have := ENNReal.rpow_le_rpow_of_exponent_le h1R hf1
        simpa using this
      exact le_trans hRle hRleB
  by_cases he : 0 ≤ e
  · exact inner hub he he1
  · have hne0 : 0 ≤ -e := by linarith
    have hne1 : -e ≤ 1 := by linarith
    have hC0e : (C : ℝ≥0∞) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hC')
    have hBinQ : B⁻¹ ≤ Q := by
      calc
        B⁻¹ = ((C : ℝ≥0∞) * (δt : ℝ≥0∞) ^ (-h))⁻¹ := by rw [hB]
        _ = (C : ℝ≥0∞)⁻¹ * ((δt : ℝ≥0∞) ^ (-h))⁻¹ := by
            rw [ENNReal.mul_inv (Or.inl hC0e) (Or.inl ENNReal.coe_ne_top)]
        _ = (C : ℝ≥0∞)⁻¹ * (δt : ℝ≥0∞) ^ h := by
            congr 1
            rw [← ENNReal.rpow_neg]
            congr 1
            linarith
        _ ≤ Q := hlb
    have hQinvB : Q⁻¹ ≤ B := by
      simpa using (ENNReal.inv_le_inv.mpr hBinQ)
    have hstep : (Q⁻¹) ^ (-e) ≤ B := inner hQinvB hne0 hne1
    have hconj : Q ^ e = (Q⁻¹) ^ (-e) := by
      rw [ENNReal.inv_rpow, ← ENNReal.rpow_neg]
      congr 1
      linarith
    rw [hconj]
    exact hstep

/-- **Factoring `|𝕋̃_b| ^ β'` through the bracket `b² |𝕋̃_b|`**.

Let `Q = b² P` be the bracketed term, two-sidedly comparable to `1` in the sense
`C⁻¹ δ̃ ^ h ≤ Q ≤ C δ̃ ^ (-h)`, and let `e = γ/2 + β' - 1 ∈ [-1, 1]`.  Then

`P ^ β' ≤ C δ̃ ^ (-h) b ^ (-2 β') Q ^ (1 - γ/2)`.

This is the algebraic identity `P ^ β' = b ^ (-2β') Q ^ β' = b ^ (-2β') Q ^ (1 - γ/2) Q ^ e`
together with `Kakeya.ml1Boot.bracket_rpow_le`, which bounds `Q ^ e` by `C δ̃ ^ (-h)` whatever
the sign of `e`.  It is the step of `Kakeya.ml1Boot.multiplicity_coarse_le` that turns the
Katz–Tao output, phrased in `|𝕋̃_b| ^ β'`, into the shape of `multTildeTb`, phrased in the
bracket. -/
theorem card_rpow_le_bracket {b δt : ℝ≥0} (hb0 : 0 < b)
    (hδt1 : δt ≤ 1)
    {β' γ : ℝ}
    (he0 : -1 ≤ γ / 2 + β' - 1) (he1 : γ / 2 + β' - 1 ≤ 1)
    {P : ℝ≥0∞} (hP0 : P ≠ 0) (hPtop : P ≠ ⊤)
    {C : ℝ≥0} (hC : 1 ≤ C) {h : ℝ} (hh : 0 ≤ h)
    (hlb : (C : ℝ≥0∞)⁻¹ * (δt : ℝ≥0∞) ^ h ≤ (b : ℝ≥0∞) ^ (2 : ℕ) * P)
    (hub : (b : ℝ≥0∞) ^ (2 : ℕ) * P ≤ (C : ℝ≥0∞) * (δt : ℝ≥0∞) ^ (-h)) :
    P ^ β' ≤ (C : ℝ≥0∞) * (δt : ℝ≥0∞) ^ (-h) * (b : ℝ≥0∞) ^ (-2 * β')
      * ((b : ℝ≥0∞) ^ (2 : ℕ) * P) ^ (1 - γ / 2) := by
  set Q : ℝ≥0∞ := (b : ℝ≥0∞) ^ (2 : ℕ) * P with hQ
  set e : ℝ := γ / 2 + β' - 1 with he
  have hbE0 : (b : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hb0.ne'
  have hbEtop : (b : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hb2top : (b : ℝ≥0∞) ^ (2 : ℕ) ≠ ⊤ := ENNReal.pow_ne_top hbEtop
  have hQ0 : Q ≠ 0 := by
    dsimp [Q]
    exact mul_ne_zero (pow_ne_zero 2 hbE0) hP0
  have hQtop : Q ≠ ⊤ := by
    dsimp [Q]
    exact ENNReal.mul_ne_top hb2top hPtop
  have hb2pow : ((b : ℝ≥0∞) ^ (2 : ℕ)) ^ β' = (b : ℝ≥0∞) ^ (2 * β') := by
    rw [pow_two]
    rw [ENNReal.mul_rpow_of_ne_top hbEtop hbEtop β']
    rw [← ENNReal.rpow_add (x := (b : ℝ≥0∞)) β' β' hbE0 hbEtop]
    congr 1
    ring
  have hQpowβ : Q ^ β' = (b : ℝ≥0∞) ^ (2 * β') * P ^ β' := by
    dsimp [Q]
    rw [ENNReal.mul_rpow_of_ne_top hb2top hPtop β', hb2pow]
  have hbneg_add : (b : ℝ≥0∞) ^ (-2 * β') * (b : ℝ≥0∞) ^ (2 * β') = 1 := by
    rw [← ENNReal.rpow_add (x := (b : ℝ≥0∞)) (-2 * β') (2 * β') hbE0 hbEtop]
    rw [show -2 * β' + 2 * β' = 0 by ring]
    simp
  have hId : P ^ β' = (b : ℝ≥0∞) ^ (-2 * β') * Q ^ β' := by
    calc
      P ^ β' = (b : ℝ≥0∞) ^ (-2 * β') * (b : ℝ≥0∞) ^ (2 * β') * P ^ β' := by
        rw [hbneg_add]
        simp
      _ = (b : ℝ≥0∞) ^ (-2 * β') * ((b : ℝ≥0∞) ^ (2 * β') * P ^ β') := by
        rw [mul_assoc]
      _ = (b : ℝ≥0∞) ^ (-2 * β') * Q ^ β' := by
        rw [← hQpowβ]
  have hQpow : Q ^ β' = Q ^ (1 - γ / 2) * Q ^ e := by
    have hβeq : (1 - γ / 2) + e = β' := by
      dsimp [e]
      ring
    calc
      Q ^ β' = Q ^ ((1 - γ / 2) + e) := by rw [← hβeq]
      _ = Q ^ (1 - γ / 2) * Q ^ e := ENNReal.rpow_add (x := Q) (1 - γ / 2) e hQ0 hQtop
  have hbracket : Q ^ e ≤ (C : ℝ≥0∞) * (δt : ℝ≥0∞) ^ (-h) := by
    apply bracket_rpow_le hδt1 hC hh
    · simpa [hQ] using hlb
    · simpa [hQ] using hub
    · simpa [he] using he0
    · simpa [he] using he1
  calc
    P ^ β' = (b : ℝ≥0∞) ^ (-2 * β') * Q ^ β' := hId
    _ = (b : ℝ≥0∞) ^ (-2 * β') * (Q ^ (1 - γ / 2) * Q ^ e) := by rw [hQpow]
    _ ≤ (b : ℝ≥0∞) ^ (-2 * β') *
        (Q ^ (1 - γ / 2) * ((C : ℝ≥0∞) * (δt : ℝ≥0∞) ^ (-h))) := by
        gcongr
    _ = (C : ℝ≥0∞) * (δt : ℝ≥0∞) ^ (-h) * (b : ℝ≥0∞) ^ (-2 * β') * Q ^ (1 - γ / 2) := by
        ac_rfl

/-- **The exponent budget of the endgame**.

With `g = γ - β'` the exponent gap, `h = 30 ε + ap'` the density exponent and
`δ̃ ≤ b ≤ δ̃ ^ (1 - 5 ε)`,

`δ̃ ^ (-ε - 2 h) b ^ (-2 β') ≤ δ̃ ^ g b ^ (-2 γ)`.

Substituting `b ^ (-2β') = b ^ (-2γ) b ^ (2g)` and `b ≤ δ̃ ^ (1 - 5 ε)` reduces this to
`g ≤ -ε - 2h + 2 g (1 - 5 ε)`, which follows from the first conclusion
`g ≤ -72 ε - 2 ap' + 2 g` of `Kakeya.ml1Boot.numerics_strong` together with
`2 (1 - 5 ε) g ≥ 2 g - 10 ε` and `2 h = 60 ε + 2 ap'`, the total power of `δ̃` being
`-61 ε - 2 ap' + 2 g`.
The hypothesis is stated as that inequality rather than through the parameter package, so that
the lemma is pure arithmetic; `ap'` is `η'_{j-1}(γ)`.

The density exponent is `30 ε` and not `8 ε` because the plank data is produced at the parent
scale `δ̃ ^ (6 ε)` and the parent count is budgeted at `ρ ^ (-5)`, and the `b`-window is
`[δ̃, δ̃ ^ (1 - 5 ε)]` and not `[δ̃, δ̃ ^ (1 - ε)]`
because `Kakeya.ml1Boot.plankWidth_le` now speaks on the `5 ε`-window; see blueprint
`note:ml1bootWindowConsumers`(3). -/
theorem exponent_budget {ε β' γ ap' : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hap' : 0 ≤ ap')
    (hgap0 : 0 < γ - β') (hgap1 : γ - β' ≤ 1)
    (hnum : γ - β' ≤ -72 * ε - 2 * ap' + 2 * (γ - β'))
    {δt b : ℝ≥0} (hδt0 : 0 < δt) (hδt1 : δt ≤ 1) (hδb : δt ≤ b)
    (hb : b ≤ δt ^ (1 - 5 * ε)) :
    (δt : ℝ≥0∞) ^ (-ε - 2 * (30 * ε + ap')) * (b : ℝ≥0∞) ^ (-2 * β')
      ≤ (δt : ℝ≥0∞) ^ (γ - β') * (b : ℝ≥0∞) ^ (-2 * γ) := by
  let g : ℝ := γ - β'
  have hg0 : 0 < g := hgap0
  have hg1 : g ≤ 1 := hgap1
  have hpow1 : -2 * β' = -2 * γ + 2 * g := by dsimp [g]; linarith
  have hDt0 : (δt : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hδt0)
  have hDtTop : (δt : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hb0n : 0 < b := lt_of_lt_of_le hδt0 hδb
  have hb0 : (b : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hb0n)
  have hbTop : (b : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hDt1 : (δt : ℝ≥0∞) ≤ 1 := by exact_mod_cast hδt1
  have hfact : (b : ℝ≥0∞) ^ (-2 * β') = (b : ℝ≥0∞) ^ (-2 * γ) * (b : ℝ≥0∞) ^ (2 * g) := by
    calc
      (b : ℝ≥0∞) ^ (-2 * β') = (b : ℝ≥0∞) ^ (-2 * γ + 2 * g) := by rw [hpow1]
      _ = (b : ℝ≥0∞) ^ (-2 * γ) * (b : ℝ≥0∞) ^ (2 * g) :=
        ENNReal.rpow_add (-2 * γ) (2 * g) hb0 hbTop
  have hmain : (δt : ℝ≥0∞) ^ (-ε - 2 * (30 * ε + ap')) * (b : ℝ≥0∞) ^ (2 * g)
      ≤ (δt : ℝ≥0∞) ^ g := by
    have hb' : (b : ℝ≥0∞) ≤ (δt : ℝ≥0∞) ^ (1 - 5 * ε) := by
      rw [← ENNReal.coe_rpow_of_ne_zero (ne_of_gt hδt0)]
      exact ENNReal.coe_le_coe.mpr hb
    have hε1le : ε ≤ 1 := hε1
    have hap'nn : 0 ≤ ap' := hap'
    have hgexp : g ≤ -ε - 2 * (30 * ε + ap') + 2 * g * (1 - 5 * ε) := by
      nlinarith [hnum, hgap0, hgap1, hε0, hε1le, hap'nn]
    have hpow_b : (b : ℝ≥0∞) ^ (2 * g) ≤ (δt : ℝ≥0∞) ^ (2 * g * (1 - 5 * ε)) := by
      have hbco :
          (δt ^ (1 - 5 * ε) : ℝ≥0∞) ^ (2 * g) = (δt : ℝ≥0∞) ^ (2 * g * (1 - 5 * ε)) := by
        rw [← ENNReal.rpow_mul]
        congr 1
        ring
      have hn : 0 ≤ 2 * g := mul_nonneg (by norm_num) hg0.le
      calc
        (b : ℝ≥0∞) ^ (2 * g) ≤ (δt ^ (1 - 5 * ε) : ℝ≥0∞) ^ (2 * g) :=
          ENNReal.rpow_le_rpow hb' hn
        _ = (δt : ℝ≥0∞) ^ (2 * g * (1 - 5 * ε)) := hbco
    calc
      (δt : ℝ≥0∞) ^ (-ε - 2 * (30 * ε + ap')) * (b : ℝ≥0∞) ^ (2 * g)
          ≤ (δt : ℝ≥0∞) ^ (-ε - 2 * (30 * ε + ap'))
              * (δt : ℝ≥0∞) ^ (2 * g * (1 - 5 * ε)) := by
            exact mul_le_mul_right hpow_b ((δt : ℝ≥0∞) ^ (-ε - 2 * (30 * ε + ap')))
      _ = (δt : ℝ≥0∞) ^ (-ε - 2 * (30 * ε + ap') + 2 * g * (1 - 5 * ε)) := by
            rw [← ENNReal.rpow_add (-ε - 2 * (30 * ε + ap')) (2 * g * (1 - 5 * ε)) hDt0 hDtTop]
      _ ≤ (δt : ℝ≥0∞) ^ g := by
            exact ENNReal.rpow_le_rpow_of_exponent_ge hDt1 hgexp
  let D : ℝ≥0∞ := (δt : ℝ≥0∞) ^ (-ε - 2 * (30 * ε + ap'))
  let Bm : ℝ≥0∞ := (b : ℝ≥0∞) ^ (-2 * γ)
  let Bp : ℝ≥0∞ := (b : ℝ≥0∞) ^ (2 * g)
  calc
    D * (b : ℝ≥0∞) ^ (-2 * β')
        = D * (Bm * Bp) := by rw [hfact]
    _ = D * Bp * Bm := by ring
    _ ≤ (δt : ℝ≥0∞) ^ g * Bm := by
          exact mul_le_mul_left hmain Bm
    _ = (δt : ℝ≥0∞) ^ (γ - β') * Bm := by
          simp [g]
    _ = (δt : ℝ≥0∞) ^ (γ - β') * (b : ℝ≥0∞) ^ (-2 * γ) := by rfl

/-- **`Kakeya.ml1Boot.exponent_budget` with the loss widened from `ε` to `ε₂ ≤ 2 ε`.**

The budget `hnum` is *unchanged*.  `Kakeya.ml1Boot.exponent_budget` needs only `71 ε` where
`hnum` supplies `72 ε`, and `2 g (1 - 5 ε) ≥ 2 g - 10 ε` gives back `10 ε (1 - g) ≥ 0`; the
slack is therefore a full `ε`, and widening the loss to `2 ε` is exactly what it pays for.
This is the whole exponent cost of routing the coarse bound through
`Kakeya.ml1Boot.multiplicity_coarse_raw_ball`, and it is already funded. -/
theorem exponent_budget_loss {ε ε₂ β' γ ap' : ℝ} (hε0 : 0 < ε) (_hε1 : ε ≤ 1) (_hap' : 0 ≤ ap')
    (hε₂ : ε₂ ≤ 2 * ε)
    (hgap0 : 0 < γ - β') (hgap1 : γ - β' ≤ 1)
    (hnum : γ - β' ≤ -72 * ε - 2 * ap' + 2 * (γ - β'))
    {δt b : ℝ≥0} (hδt0 : 0 < δt) (hδt1 : δt ≤ 1) (hδb : δt ≤ b)
    (hb : b ≤ δt ^ (1 - 5 * ε)) :
    (δt : ℝ≥0∞) ^ (-ε₂ - 2 * (30 * ε + ap')) * (b : ℝ≥0∞) ^ (-2 * β')
      ≤ (δt : ℝ≥0∞) ^ (γ - β') * (b : ℝ≥0∞) ^ (-2 * γ) := by
  let g : ℝ := γ - β'
  have hg0 : 0 < g := hgap0
  have hg1 : g ≤ 1 := hgap1
  have hpow1 : -2 * β' = -2 * γ + 2 * g := by dsimp [g]; linarith
  have hDt0 : (δt : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hδt0)
  have hDtTop : (δt : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hb0n : 0 < b := lt_of_lt_of_le hδt0 hδb
  have hb0 : (b : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hb0n)
  have hbTop : (b : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hDt1 : (δt : ℝ≥0∞) ≤ 1 := by exact_mod_cast hδt1
  have hfact : (b : ℝ≥0∞) ^ (-2 * β') = (b : ℝ≥0∞) ^ (-2 * γ) * (b : ℝ≥0∞) ^ (2 * g) := by
    calc
      (b : ℝ≥0∞) ^ (-2 * β') = (b : ℝ≥0∞) ^ (-2 * γ + 2 * g) := by rw [hpow1]
      _ = (b : ℝ≥0∞) ^ (-2 * γ) * (b : ℝ≥0∞) ^ (2 * g) :=
        ENNReal.rpow_add (-2 * γ) (2 * g) hb0 hbTop
  have hmain : (δt : ℝ≥0∞) ^ (-ε₂ - 2 * (30 * ε + ap')) * (b : ℝ≥0∞) ^ (2 * g)
      ≤ (δt : ℝ≥0∞) ^ g := by
    have hb' : (b : ℝ≥0∞) ≤ (δt : ℝ≥0∞) ^ (1 - 5 * ε) := by
      rw [← ENNReal.coe_rpow_of_ne_zero (ne_of_gt hδt0)]
      exact ENNReal.coe_le_coe.mpr hb
    have hgexp : g ≤ -ε₂ - 2 * (30 * ε + ap') + 2 * g * (1 - 5 * ε) := by
      nlinarith [hnum, hgap0, hgap1, hε0, _hε1, _hap', hε₂]
    have hpow_b : (b : ℝ≥0∞) ^ (2 * g) ≤ (δt : ℝ≥0∞) ^ (2 * g * (1 - 5 * ε)) := by
      have hbco :
          (δt ^ (1 - 5 * ε) : ℝ≥0∞) ^ (2 * g) = (δt : ℝ≥0∞) ^ (2 * g * (1 - 5 * ε)) := by
        rw [← ENNReal.rpow_mul]
        congr 1
        ring
      have hn : 0 ≤ 2 * g := mul_nonneg (by norm_num) hg0.le
      calc
        (b : ℝ≥0∞) ^ (2 * g) ≤ (δt ^ (1 - 5 * ε) : ℝ≥0∞) ^ (2 * g) :=
          ENNReal.rpow_le_rpow hb' hn
        _ = (δt : ℝ≥0∞) ^ (2 * g * (1 - 5 * ε)) := hbco
    calc
      (δt : ℝ≥0∞) ^ (-ε₂ - 2 * (30 * ε + ap')) * (b : ℝ≥0∞) ^ (2 * g)
          ≤ (δt : ℝ≥0∞) ^ (-ε₂ - 2 * (30 * ε + ap'))
              * (δt : ℝ≥0∞) ^ (2 * g * (1 - 5 * ε)) :=
            mul_le_mul_right hpow_b ((δt : ℝ≥0∞) ^ (-ε₂ - 2 * (30 * ε + ap')))
      _ = (δt : ℝ≥0∞) ^ (-ε₂ - 2 * (30 * ε + ap') + 2 * g * (1 - 5 * ε)) := by
            rw [← ENNReal.rpow_add (-ε₂ - 2 * (30 * ε + ap')) (2 * g * (1 - 5 * ε)) hDt0 hDtTop]
      _ ≤ (δt : ℝ≥0∞) ^ g := ENNReal.rpow_le_rpow_of_exponent_ge hDt1 hgexp
  let D : ℝ≥0∞ := (δt : ℝ≥0∞) ^ (-ε₂ - 2 * (30 * ε + ap'))
  let Bm : ℝ≥0∞ := (b : ℝ≥0∞) ^ (-2 * γ)
  let Bp : ℝ≥0∞ := (b : ℝ≥0∞) ^ (2 * g)
  calc
    D * (b : ℝ≥0∞) ^ (-2 * β')
        = D * (Bm * Bp) := by rw [hfact]
    _ = D * Bp * Bm := by ring
    _ ≤ (δt : ℝ≥0∞) ^ g * Bm := mul_le_mul_left hmain Bm
    _ = (δt : ℝ≥0∞) ^ (γ - β') * Bm := by simp [g]
    _ = (δt : ℝ≥0∞) ^ (γ - β') * (b : ℝ≥0∞) ^ (-2 * γ) := by rfl

/-! ### The numeric bookkeeping -/

/-- **The numeric bookkeeping of the endgame**.

For an admissible parameter package `p`, every `γ ∈ [γ₀, 1]`
and every `1 ≤ j ≤ N`, with `g(γ) = γ - β'(γ)` the exponent gap of
`Kakeya.ml1Boot.gap`:

* (i) `-12 ε - 2 η'_{j-1} + 2 g(γ) ≥ g(γ)`;
* (ii) `10 η'_{j-1} ≤ g(γ) / 2`.

The eccentricity exponent `η'_{j-1} = Kakeya.ml1Boot.Params.etaPrime β γ₀ (j - 1)` is
`γ`-free (blueprint `def:ml1bootParams`(iv)); only the gap `g(γ)` on the right depends on
`γ`.

Both follow from `ε ≤ g₀ / 96` and `η'_{j-1} ≤ g₀ / 40`
(`Kakeya.ml1Boot.Params.Spec`) together with the monotonicity of the gap
(`Kakeya.ml1Boot.gap_spec`); the essential point is that they hold
*uniformly* in `γ ∈ [γ₀, 1]`, which is what makes
`Kakeya.ml1Boot.exists_uniform_step` a uniform statement.

The blueprint's `12 ε` in place of GWZ's `8 ε` pays for the conversion of `b ^ (-2β')` into
`b ^ (-2γ)` in `Kakeya.ml1Boot.multiplicity_coarse_le` and for the loss exponent of
`Kakeya.KatzTaoEstimate.multiplicity_bound`.

`Kakeya.ml1Boot.multiplicity_coarse_le` now needs the stronger form with `72 ε`; that is
`Kakeya.ml1Boot.numerics_strong`.

The package enters as `p` together with its specification `hp` rather than as the seven data
out of which `Kakeya.ml1Boot.params` builds it, matching
`Kakeya.ml1Boot.exists_caseTwoData`; `Kakeya.ml1Boot.params_spec` is what a caller applies.
The remaining binders `hβ0`, `hγ₀` are what `Kakeya.ml1Boot.gap_spec` needs and are not part
of `Kakeya.ml1Boot.Params.Spec`. -/
theorem numerics {β γ₀ : ℝ} (hβ0 : 0 ≤ β) (hγ₀ : γ₀ ∈ Set.Ioc β 1)
    {p : Params} (hp : p.Spec β γ₀) :
    ∀ γ ∈ Set.Icc γ₀ 1, ∀ j, 1 ≤ j → j ≤ p.N →
      gap β γ ≤ -12 * p.ε - 2 * p.etaPrime β γ₀ (j - 1) + 2 * gap β γ ∧
        10 * p.etaPrime β γ₀ (j - 1) ≤ gap β γ / 2 := by
  intro γ hγ j hj1 hjN
  have hεg0 : 96 * p.ε ≤ gap β γ₀ := hp.ninetySixEpsLe
  have hη' : p.etaPrime β γ₀ (j - 1) ≤ gap β γ₀ / 40 := hp.etaPrimeLeGap j hj1 hjN
  have hgap := gap_spec hβ0
  have hgap0 : 0 < gap β γ₀ := hgap.2.1 γ₀ hγ₀
  have hγ₀leγ : γ₀ ≤ γ := hγ.1
  have hγoc : γ ∈ Set.Ioc β 1 := ⟨lt_of_lt_of_le hγ₀.1 hγ₀leγ, hγ.2⟩
  have hmono : gap β γ₀ ≤ gap β γ := hgap.2.2 hγ₀ hγoc hγ₀leγ
  constructor
  · have h1 : 12 * p.ε + 2 * p.etaPrime β γ₀ (j - 1) ≤ gap β γ := by
      nlinarith [hεg0, hη', hmono, hgap0]
    nlinarith
  · nlinarith [hη', hmono, hgap0]

end ml1Boot

end Kakeya

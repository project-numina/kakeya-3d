/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.ThickCase
public import Kakeya.DimensionThree.MainLemma2.DenseInBodyNamed

/-!
# Named constants for density inside a body

`Kakeya.VeryNotSticky.exists_denseInBody` and its auxiliary lemmas return
`∃ Θ C₁ : ℝ≥0, 1 ≤ Θ ∧ 1 ≤ C₁ ∧ …`. Quantitative thresholds must use a
suitable pair of witnesses: requiring `Λ C₁ Θ ≤ δ^{-ν}` for every pair
`(Θ, C₁)` would allow arbitrarily large constants to defeat the threshold.

The proof supplies an explicit pair.
`Kakeya.VeryNotSticky.exists_denseConst_of_plankF` calls
`Kakeya.VeryNotSticky.exists_nnreal_const_of_le` at `Θ := CP * Θ`; the latter
returns `⟨Θ * Cb * Cb, max 1 (64 * B1.toNNReal * CP ^ (ν + 3β) * CP)⟩`.
The subsequent lemmas preserve this pair:

* `Kakeya.VeryNotSticky.denseInBodyΘ CP Θ₀ C_bias = CP Θ₀ C_bias²`.
  Its scale dependence occurs through `C_bias` (the maximal-density
  factorization estimate).
* `Kakeya.VeryNotSticky.denseInBodyC₁ CP ν β =
  max 1 (64 |B̄(0,4)| CP^{ν+3β} CP)`. This constant is independent of
  `δ` and depends on `CP`, the two exponents, and the ambient dimension.

The chain
`thickPlankF_conclude_of_plankF → denseConst_at_of_plankF →
denseInBodyRaw_at_of_thickPlankPresentation → exists_denseInBodyRaw_at →
exists_denseInBody_at` establishes the estimates at these named constants.
Each `_at` form implies its existential companion, as recorded by
`exists_denseInBody_at_imp` and the analogous lemmas.

`thickPlankF_conclude_of_plankF` separates the quantitative estimate from
choosing its witnesses, so both the named and existential forms follow from
the same estimate. The definitions `denseInBodyΘ` and `denseInBodyC₁` are
provided by `DenseInBodyNamed.lean`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric

noncomputable section

namespace Kakeya.VeryNotSticky

open Kakeya

universe u

/-! ### The arithmetic step, at the named constants -/

/-- **`Kakeya.VeryNotSticky.exists_nnreal_const_of_le`, with its witnesses named.**

The existing lemma is applied at `Θ := CP * Θ`; its two witnesses are then exactly
`denseInBodyΘ CP Θ Cb` and `denseInBodyC₁ CP ν β`, the second because
`Kakeya.VeryNotSticky.denseInBodyRaw_of_thickPlankPresentation` instantiates its `B1` at the
volume of the window ball. -/
theorem le_denseInBodyConst_of_le {CP Θ Cb : ℝ≥0} (hCP : 1 ≤ CP) (_hCb : 1 ≤ Cb)
    {ν β : ℝ} {X Y : ℝ≥0∞}
    (h : X ≤ 64 * volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) Plank.windowRadius) *
        (CP : ℝ≥0∞) ^ (ν + 3 * β) *
        ((CP : ℝ≥0∞) * (Θ : ℝ≥0∞) * (Cb : ℝ≥0∞)) *
        ((CP : ℝ≥0∞) * (Cb : ℝ≥0∞)) * Y) :
    X ≤ (denseInBodyΘ CP Θ Cb : ℝ≥0∞) * (denseInBodyC₁ CP ν β : ℝ≥0∞) * Y := by
  set B1 : ℝ≥0∞ :=
    volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) Plank.windowRadius) with hB1def
  have hB1 : B1 ≠ ⊤ := by
    rw [hB1def]; exact (MeasureTheory.measure_closedBall_lt_top).ne
  have hCP0 : CP ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hCP)
  have hC : (64 : ℝ≥0∞) * B1 * (CP : ℝ≥0∞) ^ (ν + 3 * β) * (CP : ℝ≥0∞) ≤
      ((denseInBodyC₁ CP ν β : ℝ≥0) : ℝ≥0∞) := by
    calc
      (64 : ℝ≥0∞) * B1 * (CP : ℝ≥0∞) ^ (ν + 3 * β) * (CP : ℝ≥0∞)
          = ((64 * B1.toNNReal * CP ^ (ν + 3 * β) * CP : ℝ≥0) : ℝ≥0∞) := by
            simp [ENNReal.coe_rpow_of_ne_zero hCP0, hB1]
      _ ≤ ((denseInBodyC₁ CP ν β : ℝ≥0) : ℝ≥0∞) := by
            exact ENNReal.coe_le_coe.2 (le_max_right _ _)
  refine h.trans ?_
  calc
    64 * B1 * (CP : ℝ≥0∞) ^ (ν + 3 * β) *
          ((CP : ℝ≥0∞) * (Θ : ℝ≥0∞) * (Cb : ℝ≥0∞)) *
          ((CP : ℝ≥0∞) * (Cb : ℝ≥0∞)) * Y
        = (CP : ℝ≥0∞) * (Θ : ℝ≥0∞) * (Cb : ℝ≥0∞) * (Cb : ℝ≥0∞) *
            ((64 : ℝ≥0∞) * B1 * (CP : ℝ≥0∞) ^ (ν + 3 * β) * (CP : ℝ≥0∞)) * Y := by
          ring
    _ ≤ (CP : ℝ≥0∞) * (Θ : ℝ≥0∞) * (Cb : ℝ≥0∞) * (Cb : ℝ≥0∞) *
        ((denseInBodyC₁ CP ν β : ℝ≥0) : ℝ≥0∞) * Y := by
          gcongr
    _ = (denseInBodyΘ CP Θ Cb : ℝ≥0∞) * ((denseInBodyC₁ CP ν β : ℝ≥0) : ℝ≥0∞) * Y := by
          rw [denseInBodyΘ]
          push_cast
          ring

/-! ### The plank half, factored -/

/-- **The whole of `Kakeya.VeryNotSticky.exists_denseConst_of_plankF` except its last line.**

Hypotheses and proof are those of the existing lemma; what is different is that the conclusion
is the *bound at the explicit product* that `Kakeya.VeryNotSticky.thickPlankF_conclude`
delivers, before it is split into two `ℝ≥0` factors. Both the existing existential and the named
form of this file follow from it, the first by
`Kakeya.VeryNotSticky.exists_nnreal_const_of_le` and the second by
`Kakeya.VeryNotSticky.le_denseInBodyConst_of_le`.

It is stated separately, rather than obtained by editing the existing lemma, so that no existing
proof term changes. -/
theorem thickPlankF_conclude_of_plankF {CP Θ Cb : ℝ≥0} (hCP : 1 ≤ CP) (hΘ : 1 ≤ Θ)
    (hCb : 1 ≤ Cb) {d na nb a' b' N Ns UP W UW B1 : ℝ≥0∞} {ν β ϱ : ℝ}
    (hN0 : N ≠ 0) (hNtop : N ≠ ⊤)
    (hd0 : d ≠ 0) (hdtop : d ≠ ⊤) (hna0 : na ≠ 0) (hnatop : na ≠ ⊤)
    (hnb0 : nb ≠ 0) (hnb1 : nb ≤ 1)
    (hν : 0 ≤ ν) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (ha' : (CP : ℝ≥0∞)⁻¹ * (d / nb) ≤ a') (hb' : (CP : ℝ≥0∞)⁻¹ * (d / na) ≤ b')
    (hNs : (CP : ℝ≥0∞)⁻¹ * N ≤ Ns)
    (hplank : a' ^ ν * ((CP : ℝ≥0∞) * (Cb : ℝ≥0∞)) ^ (β / 2 - 1) * b' ^ (2 * β) *
        (((Θ : ℝ≥0∞) * (Cb : ℝ≥0∞) * (d / na) ^ (2 + ϱ) * N)⁻¹ * b' ^ (2 : ℝ) * Ns) ^
          (β / 2) ≤ 64 * UP)
    (hvol : UP * W ≤ B1 * UW) :
    d ^ ν * (na / d) ^ (ϱ * β / 2) * (d ^ (2 * β) * W) ≤
      64 * B1 * (CP : ℝ≥0∞) ^ (ν + 3 * β) *
        ((CP : ℝ≥0∞) * (Θ : ℝ≥0∞) * (Cb : ℝ≥0∞)) *
        ((CP : ℝ≥0∞) * (Cb : ℝ≥0∞)) * (na ^ (2 * β) * UW) := by
  let CPe : ℝ≥0∞ := (CP : ℝ≥0∞)
  let Θe : ℝ≥0∞ := (Θ : ℝ≥0∞)
  let Cbe : ℝ≥0∞ := (Cb : ℝ≥0∞)
  let Y : ℝ≥0∞ := (d / na) ^ (2 + ϱ)
  let X : ℝ≥0∞ := (Θe * Cbe) * Y * N
  let M : ℝ≥0∞ := (((CPe * Θe * Cbe) * Y * N)⁻¹ * b' ^ (2 : ℝ) * N) ^ (β / 2)
  let M' : ℝ≥0∞ := (((Θe * Cbe) * Y * N)⁻¹ * b' ^ (2 : ℝ) * Ns) ^ (β / 2)
  have hCP1 : (1 : ℝ≥0∞) ≤ CPe := by
    dsimp [CPe]; exact_mod_cast hCP
  have hCP0 : CPe ≠ 0 := by
    dsimp [CPe]; exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hCP))
  have hCPtop : CPe ≠ ⊤ := by
    dsimp [CPe]; exact ENNReal.coe_ne_top
  have hΘ1 : (1 : ℝ≥0∞) ≤ Θe := by
    dsimp [Θe]; exact_mod_cast hΘ
  have hΘ0 : Θe ≠ 0 := by
    dsimp [Θe]; exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hΘ))
  have hΘtop : Θe ≠ ⊤ := by
    dsimp [Θe]; exact ENNReal.coe_ne_top
  have hCb1 : (1 : ℝ≥0∞) ≤ Cbe := by
    dsimp [Cbe]; exact_mod_cast hCb
  have hCb0 : Cbe ≠ 0 := by
    dsimp [Cbe]; exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hCb))
  have hCbtop : Cbe ≠ ⊤ := by
    dsimp [Cbe]; exact ENNReal.coe_ne_top
  have hΘF1 : (1 : ℝ≥0∞) ≤ CPe * Θe * Cbe := one_le_mul (one_le_mul hCP1 hΘ1) hCb1
  have hΘFtop : CPe * Θe * Cbe ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hCPtop hΘtop) hCbtop
  have hΘF0 : CPe * Θe * Cbe ≠ 0 := mul_ne_zero (mul_ne_zero hCP0 hΘ0) hCb0
  have hNs' : CPe⁻¹ * N ≤ Ns := by simpa [CPe] using hNs
  have hXdef : X = (Θe * Cbe) * Y * N := rfl
  have hCPeX : (CPe * Θe * Cbe) * Y * N = CPe * X := by
    dsimp [X]; ring
  have hmono : ((CPe * Θe * Cbe) * Y * N)⁻¹ * b' ^ (2 : ℝ) * N ≤
      ((Θe * Cbe) * Y * N)⁻¹ * b' ^ (2 : ℝ) * Ns := by
    calc
      ((CPe * Θe * Cbe) * Y * N)⁻¹ * b' ^ (2 : ℝ) * N
          = (CPe * X)⁻¹ * b' ^ (2 : ℝ) * N := by rw [hCPeX]
      _ = (CPe⁻¹ * X⁻¹) * b' ^ (2 : ℝ) * N := by
              rw [ENNReal.mul_inv (Or.inl hCP0) (Or.inl hCPtop)]
      _ = X⁻¹ * b' ^ (2 : ℝ) * (CPe⁻¹ * N) := by ring
      _ ≤ X⁻¹ * b' ^ (2 : ℝ) * Ns := by gcongr
      _ = ((Θe * Cbe) * Y * N)⁻¹ * b' ^ (2 : ℝ) * Ns := by rw [← hXdef]
  have hβ2 : (0 : ℝ) ≤ β / 2 := by nlinarith
  have hmonopow : M ≤ M' := by
    dsimp [M, M']; exact ENNReal.rpow_le_rpow hmono hβ2
  have hprod := thickPlankF_product_lower (CP := CPe) (Cb := Cbe) (Θ := CPe * Θe * Cbe)
    (d := d) (na := na) (nb := nb) (a' := a') (b' := b') (N := N) (ν := ν) (β := β) (ϱ := ϱ)
    hCP0 hCPtop hCP1 hCb1 hΘF1 hΘFtop hN0 hNtop hd0 hdtop hna0 hnatop hnb0 hnb1 hν hβ0 hβ1
    (by simpa [CPe] using ha') (by simpa [CPe] using hb')
  have hMle : a' ^ ν * (CPe * Cbe) ^ (β / 2 - 1) * b' ^ (2 * β) * M ≤
      a' ^ ν * (CPe * Cbe) ^ (β / 2 - 1) * b' ^ (2 * β) * M' := by gcongr
  have hP : CPe ^ (-ν) * d ^ ν * (CPe * Cbe)⁻¹ * (CPe ^ (-(2 * β)) * (d / na) ^ (2 * β)) *
      (CPe ^ (-β) * (CPe * Θe * Cbe)⁻¹ * (na / d) ^ (ϱ * β / 2)) ≤ 64 * UP := by
    calc
      CPe ^ (-ν) * d ^ ν * (CPe * Cbe)⁻¹ * (CPe ^ (-(2 * β)) * (d / na) ^ (2 * β)) *
          (CPe ^ (-β) * (CPe * Θe * Cbe)⁻¹ * (na / d) ^ (ϱ * β / 2))
          ≤ a' ^ ν * (CPe * Cbe) ^ (β / 2 - 1) * b' ^ (2 * β) * M := by
              simpa [M] using hprod
      _ ≤ a' ^ ν * (CPe * Cbe) ^ (β / 2 - 1) * b' ^ (2 * β) * M' := hMle
      _ ≤ 64 * UP := by simpa [CPe, Θe, Cbe, Y, M'] using hplank
  have hcon := thickPlankF_conclude (CP := CPe) (Cb := Cbe) (Θ := CPe * Θe * Cbe)
    (d := d) (na := na) (UP := UP) (W := W) (UW := UW) (B1 := B1)
    (ν := ν) (β := β) (ϱ := ϱ)
    hCP0 hCPtop hCb0 hCbtop hΘF0 hΘFtop hd0 hdtop hna0 hnatop hβ0 hν hP hvol
  simpa [CPe, Θe, Cbe] using hcon

/-- **`Kakeya.VeryNotSticky.exists_denseConst_of_plankF`, at the named constants.**

Same hypotheses; the two produced constants are `Kakeya.VeryNotSticky.denseInBodyΘ CP Θ Cb`
and `Kakeya.VeryNotSticky.denseInBodyC₁ CP ν β`, the localizing ball being the window ball. -/
theorem denseConst_at_of_plankF {CP Θ Cb : ℝ≥0} (hCP : 1 ≤ CP) (hΘ : 1 ≤ Θ)
    (hCb : 1 ≤ Cb) {d na nb a' b' N Ns UP W UW : ℝ≥0∞} {ν β ϱ : ℝ}
    (hN0 : N ≠ 0) (hNtop : N ≠ ⊤)
    (hd0 : d ≠ 0) (hdtop : d ≠ ⊤) (hna0 : na ≠ 0) (hnatop : na ≠ ⊤)
    (hnb0 : nb ≠ 0) (hnb1 : nb ≤ 1)
    (hν : 0 ≤ ν) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (ha' : (CP : ℝ≥0∞)⁻¹ * (d / nb) ≤ a') (hb' : (CP : ℝ≥0∞)⁻¹ * (d / na) ≤ b')
    (hNs : (CP : ℝ≥0∞)⁻¹ * N ≤ Ns)
    (hplank : a' ^ ν * ((CP : ℝ≥0∞) * (Cb : ℝ≥0∞)) ^ (β / 2 - 1) * b' ^ (2 * β) *
        (((Θ : ℝ≥0∞) * (Cb : ℝ≥0∞) * (d / na) ^ (2 + ϱ) * N)⁻¹ * b' ^ (2 : ℝ) * Ns) ^
          (β / 2) ≤ 64 * UP)
    (hvol : UP * W ≤
      volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) Plank.windowRadius) * UW) :
    d ^ ν * (na / d) ^ (ϱ * β / 2) * (d ^ (2 * β) * W) ≤
      (denseInBodyΘ CP Θ Cb : ℝ≥0∞) * (denseInBodyC₁ CP ν β : ℝ≥0∞) *
        (na ^ (2 * β) * UW) :=
  le_denseInBodyConst_of_le hCP hCb
    (thickPlankF_conclude_of_plankF hCP hΘ hCb hN0 hNtop hd0 hdtop hna0 hnatop hnb0 hnb1
      hν hβ0 hβ1 ha' hb' hNs hplank hvol)

/-! ### The three interface twins -/

/-- **`Kakeya.VeryNotSticky.denseInBodyRaw_of_thickPlankPresentation`, at the named
constants.** -/
theorem denseInBodyRaw_at_of_thickPlankPresentation {cfg : VeryNotSticky.{u}}
    (bd : BallData cfg) {τ : ℝ} (hτ : 0 < τ) (hβ1 : cfg.β ≤ 1)
    {CP Θ C_NC : ℝ≥0} (hCP : 1 ≤ CP) (hΘ : 1 ≤ Θ) {ηF : ℝ} (hηF : 0 < ηF)
    (hbudget : PlankFrostmanUsable bd τ CP C_NC ηF)
    {B : bd.bι} {p₀ : bd.σ} (hp₀ : p₀ ∈ bd.segs B)
    (hpres : ThickPlankPresentation bd B (bd.blk p₀) CP Θ C_NC)
    (hfull : bd.c₁ * cfg.δ ^ (2 * cfg.η) ≤
      ShadedBody.fullness ((bd.segs B).filter fun p => bd.blk p = bd.blk p₀) bd.Y)
    (hPcard : ((cfg.a : ℝ≥0∞) / (cfg.δ : ℝ≥0∞)) ^ (2 + cfg.ϱ) ≤
      ((((bd.segs B).filter fun p => bd.blk p = bd.blk p₀).card : ℕ) : ℝ≥0∞)) :
    DenseInBodyRaw bd (cfg.ϱ * cfg.β * τ / 8)
      (denseInBodyΘ CP Θ bd.Cbias)
      (denseInBodyC₁ CP (cfg.ϱ * cfg.β * τ / 8) cfg.β) B (bd.blk p₀) := by
  have hp₀s : p₀ ∈ (bd.segs B).filter fun p => bd.blk p = bd.blk p₀ :=
    Finset.mem_filter.mpr ⟨hp₀, rfl⟩
  have hcard : ((bd.segs B).filter fun p => bd.blk p = bd.blk p₀).card ≠ 0 :=
    Finset.card_ne_zero_of_mem hp₀s
  have hN0 : ((((bd.segs B).filter fun p => bd.blk p = bd.blk p₀).card : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast hcard
  have hd0 : (cfg.δ : ℝ≥0∞) ≠ 0 := by simpa using (ne_of_gt cfg.hδ)
  have hna0 : (cfg.a : ℝ≥0∞) ≠ 0 := by simpa using (ne_of_gt (cfg_a_pos cfg))
  have hnb0 : (cfg.b : ℝ≥0∞) ≠ 0 := by simpa using (ne_of_gt (cfg_b_pos cfg))
  have hnb1 : (cfg.b : ℝ≥0∞) ≤ 1 := by exact_mod_cast (cfg_b_le_one cfg)
  have hν : (0 : ℝ) ≤ cfg.ϱ * cfg.β * τ / 8 := by
    have h1 : 0 < cfg.ϱ := cfg.hϱ
    have h2 : 0 < cfg.β := cfg.hβ
    positivity
  exact denseConst_at_of_plankF hCP hΘ bd.hCbias hN0 (ENNReal.natCast_ne_top _)
    hd0 ENNReal.coe_ne_top hna0 ENNReal.coe_ne_top hnb0 hnb1 hν cfg.hβ hβ1
    (thickPres_inv_le_a' hpres hCP) (thickPres_inv_le_b' hpres hCP)
    hpres.sel_card
    (thickPlankF_apply bd hCP hΘ hηF hbudget hpres hfull hPcard)
    hpres.volume_le

/-- **`Kakeya.VeryNotSticky.exists_denseInBodyRaw`, at the named constants.** -/
theorem exists_denseInBodyRaw_at {cfg : VeryNotSticky.{u}} (bd : BallData cfg) {τ : ℝ}
    (hτ : 0 < τ) (hβ1 : cfg.β ≤ 1) {CP Θ₀ C_NC : ℝ≥0} (hCP : 1 ≤ CP) (hΘ₀ : 1 ≤ Θ₀)
    {ηF : ℝ} (hηF : 0 < ηF)
    (hbudget : PlankFrostmanUsable bd τ CP C_NC ηF)
    (hpres : ThickPlankPresentable bd CP Θ₀ C_NC)
    (hPcard : ∀ B ∈ bd.bs, ∀ p₀ ∈ bd.segs B,
      ((cfg.a : ℝ≥0∞) / (cfg.δ : ℝ≥0∞)) ^ (2 + cfg.ϱ) ≤
        ((((bd.segs B).filter fun p => bd.blk p = bd.blk p₀).card : ℕ) : ℝ≥0∞)) :
    ∃ B ∈ bd.bs, ∃ j ∈ bd.bodies B,
      DenseInBodyRaw bd (cfg.ϱ * cfg.β * τ / 8)
        (denseInBodyΘ CP Θ₀ bd.Cbias)
        (denseInBodyC₁ CP (cfg.ϱ * cfg.β * τ / 8) cfg.β) B j := by
  obtain ⟨B, hB, p₀, hp₀, hfull⟩ := exists_thickFullBlock bd
  obtain ⟨pres⟩ := hpres B hB p₀ hp₀
  exact ⟨B, hB, bd.blk p₀, bd.blk_mem B hB p₀ hp₀,
    denseInBodyRaw_at_of_thickPlankPresentation bd hτ hβ1 hCP hΘ₀ hηF hbudget hp₀ pres hfull
      (hPcard B hB p₀ hp₀)⟩

/-- `Kakeya.VeryNotSticky.exists_denseInBody` at the named constants.
Fixing `Θ` and `C₁` makes the threshold a direct inequality in the
configuration constants. It does not require the inequality to hold
for every pair of density witnesses. -/
theorem exists_denseInBody_at (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ')
    (bd : BallData cfg) (hβ1 : cfg.β ≤ 1) (hthick : cfg.δ ^ (1 - τ) ≤ cfg.a)
    (hδ₂ : (bd.Cbias : ℝ≥0∞) * (((48 * bd.C₀ ^ 6) ^ 3 : ℝ≥0) : ℝ≥0∞) ≤
      (cfg.δ : ℝ≥0∞) ^ (-(τ * cfg.ϱ)))
    {CP Θ₀ C_NC : ℝ≥0} (hCP : 1 ≤ CP) (hΘ₀ : 1 ≤ Θ₀) {ηF : ℝ} (hηF : 0 < ηF)
    (hbudget : PlankFrostmanUsable bd τ CP C_NC ηF)
    (hpres : ThickPlankPresentable bd CP Θ₀ C_NC) :
    ∀ Λ : ℝ≥0∞, 1 ≤ Λ → Λ ≠ ⊤ →
      Λ * (denseInBodyC₁ CP (cfg.ϱ * cfg.β * τ / 8) cfg.β : ℝ≥0∞) *
          (denseInBodyΘ CP Θ₀ bd.Cbias : ℝ≥0∞) ≤
        (cfg.δ : ℝ≥0∞) ^ (-(cfg.ϱ * cfg.β * τ / 8)) →
      ∃ B ∈ bd.bs, ∃ j ∈ bd.bodies B,
        Λ * (cfg.δ : ℝ≥0∞) ^ (2 * cfg.β) * volume (bd.Wb j).carrier ≤
          (cfg.δ : ℝ≥0∞) ^ (2 * (cfg.ϱ * cfg.β * τ / 8)) *
            volume ((⋃ p ∈ (bd.segs B).filter fun p => bd.blk p = j, (bd.Y p).shade) ∩
              (bd.Wb j).carrier) *
            (cfg.a : ℝ≥0∞) ^ (2 * cfg.β) := by
  let ν : ℝ := cfg.ϱ * cfg.β * τ / 8
  let d : ℝ≥0∞ := (cfg.δ : ℝ≥0∞)
  let na : ℝ≥0∞ := (cfg.a : ℝ≥0∞)
  let A : ℝ≥0∞ := na / d
  have hδe_pos : (0 : ℝ≥0∞) < (cfg.δ : ℝ≥0∞) := by exact_mod_cast cfg.hδ
  have hd0 : d ≠ 0 := by dsimp [d]; exact hδe_pos.ne.symm
  have hdtop : d ≠ ⊤ := by dsimp [d]; exact ENNReal.coe_ne_top
  have hδ0 : (cfg.δ : ℝ≥0) ≠ 0 := ne_of_gt cfg.hδ
  have hϱp : 0 < cfg.ϱ := cfg.hϱ
  have hβp : 0 < cfg.β := cfg.hβ
  have hτp : 0 < τ := params.hτ
  have hνpos : 0 < ν := by dsimp [ν]; positivity
  have h_rhs_nonneg : 0 ≤ cfg.ϱ * cfg.β / 2 := by positivity
  have hthickE : d ^ (1 - τ) ≤ na := by
    dsimp [d, na]
    rw [← ENNReal.coe_rpow_of_ne_zero hδ0 (1 - τ)]
    exact_mod_cast hthick
  have h_pow_split : d ^ (1 - τ) = d ^ (-τ) * d := by
    rw [show (1 : ℝ) - τ = (-τ) + (1 : ℝ) by ring]
    rw [ENNReal.rpow_add (-τ) (1 : ℝ) hd0 hdtop, ENNReal.rpow_one]
  have hthickE' : d ^ (-τ) * d ≤ na := by rw [h_pow_split] at hthickE; exact hthickE
  have hdiv : d ^ (-τ) ≤ A := by
    dsimp [A]
    rw [ENNReal.le_div_iff_mul_le (Or.inl hd0) (Or.inl hdtop)]
    exact hthickE'
  have hsurplus : d ^ (-(4 * ν)) ≤ A ^ (cfg.ϱ * cfg.β / 2) := by
    have h := ENNReal.rpow_le_rpow hdiv h_rhs_nonneg
    rwa [show (-(4 * ν)) = (-τ) * (cfg.ϱ * cfg.β / 2) by dsimp [ν]; ring,
      ENNReal.rpow_mul d (-τ) (cfg.ϱ * cfg.β / 2)]
  obtain ⟨B, hB, j, hj, hraw⟩ :=
    exists_denseInBodyRaw_at bd params.hτ hβ1 hCP hΘ₀ hηF hbudget hpres
      (fun B' hB' => fun p₀ hp₀ => thickPcard_ge cfg params bd hthick hδ₂ hB' hp₀)
  set Θ : ℝ≥0 := denseInBodyΘ CP Θ₀ bd.Cbias with hΘdef
  set C₁ : ℝ≥0 := denseInBodyC₁ CP ν cfg.β with hC₁def
  let X : ℝ≥0∞ := d ^ (2 * cfg.β) * volume (bd.Wb j).carrier
  let Y : ℝ≥0∞ :=
    na ^ (2 * cfg.β) *
      volume ((⋃ p ∈ (bd.segs B).filter fun p => bd.blk p = j, (bd.Y p).shade) ∩
        (bd.Wb j).carrier)
  have hraw' : d ^ ν * A ^ (cfg.ϱ * cfg.β / 2) * X ≤ (Θ : ℝ≥0∞) * (C₁ : ℝ≥0∞) * Y := by
    simpa [DenseInBodyRaw, X, Y, ν, d, na, A, hΘdef, hC₁def] using hraw
  have hidem : d ^ (-(3 * ν)) * X ≤ (Θ : ℝ≥0∞) * (C₁ : ℝ≥0∞) * Y := by
    have hsum : d ^ (-(4 * ν)) * X ≤ A ^ (cfg.ϱ * cfg.β / 2) * X :=
      mul_le_mul_of_nonneg_right hsurplus (by positivity : 0 ≤ X)
    have hud : d ^ ν * (d ^ (-(4 * ν)) * X) ≤ d ^ ν * (A ^ (cfg.ϱ * cfg.β / 2) * X) :=
      mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ d ^ ν)
    have hle : d ^ ν * d ^ (-(4 * ν)) * X ≤ (Θ : ℝ≥0∞) * (C₁ : ℝ≥0∞) * Y := by
      calc
        d ^ ν * d ^ (-(4 * ν)) * X = d ^ ν * (d ^ (-(4 * ν)) * X) := by simp [mul_assoc]
        _ ≤ d ^ ν * (A ^ (cfg.ϱ * cfg.β / 2) * X) := hud
        _ = d ^ ν * A ^ (cfg.ϱ * cfg.β / 2) * X := by simp [mul_assoc]
        _ ≤ (Θ : ℝ≥0∞) * (C₁ : ℝ≥0∞) * Y := hraw'
    have hp : d ^ ν * d ^ (-(4 * ν)) = d ^ (-(3 * ν)) := by
      rw [← ENNReal.rpow_add ν (-(4 * ν)) hd0 hdtop]
      congr 1
      ring
    rwa [← hp]
  intro Λ hΛ1 hΛtop hthr
  refine ⟨B, hB, j, hj, ?_⟩
  have hΛstep : Λ * (d ^ (-(3 * ν)) * X) ≤ d ^ (-ν) * Y := by
    calc
      Λ * (d ^ (-(3 * ν)) * X) ≤ Λ * ((Θ : ℝ≥0∞) * (C₁ : ℝ≥0∞) * Y) :=
        mul_le_mul_of_nonneg_left hidem (by positivity : 0 ≤ Λ)
      _ = (Λ * (C₁ : ℝ≥0∞) * (Θ : ℝ≥0∞)) * Y := by
        simp [mul_assoc, mul_comm]
      _ ≤ d ^ (-ν) * Y := mul_le_mul_of_nonneg_right hthr (by positivity : 0 ≤ Y)
  have hcancel : d ^ (3 * ν) * d ^ (-(3 * ν)) = 1 := by
    rw [← ENNReal.rpow_add (3 * ν) (-(3 * ν)) hd0 hdtop]
    rw [show ((3 : ℝ) * ν + (-(3 * ν)) = 0) by ring, ENNReal.rpow_zero]
  have hpow : d ^ (3 * ν) * d ^ (-ν) = d ^ (2 * ν) := by
    rw [← ENNReal.rpow_add (3 * ν) (-ν) hd0 hdtop]
    congr 1
    ring
  have hΛX : Λ * X ≤ d ^ (2 * ν) * Y := by
    calc
      Λ * X = d ^ (3 * ν) * (Λ * (d ^ (-(3 * ν)) * X)) := by
        rw [show d ^ (3 * ν) * (Λ * (d ^ (-(3 * ν)) * X))
            = (d ^ (3 * ν) * d ^ (-(3 * ν))) * (Λ * X) by ring, hcancel, one_mul]
      _ ≤ d ^ (3 * ν) * (d ^ (-ν) * Y) :=
        mul_le_mul_of_nonneg_left hΛstep (by positivity : 0 ≤ d ^ (3 * ν))
      _ = d ^ (2 * ν) * Y := by rw [← mul_assoc, hpow]
  calc
    Λ * (cfg.δ : ℝ≥0∞) ^ (2 * cfg.β) * volume (bd.Wb j).carrier = Λ * X := by
      dsimp [X, d]; ring
    _ ≤ d ^ (2 * ν) * Y := hΛX
    _ = (cfg.δ : ℝ≥0∞) ^ (2 * (cfg.ϱ * cfg.β * τ / 8)) *
          volume ((⋃ p ∈ (bd.segs B).filter fun p => bd.blk p = j, (bd.Y p).shade) ∩
            (bd.Wb j).carrier) *
          (cfg.a : ℝ≥0∞) ^ (2 * cfg.β) := by
      dsimp [Y, d, na, ν]; ring

/-! ### Sufficiency of the threshold at named constants -/

/-! ### A universal comparison-constant threshold is impossible

Consider a condition beginning with
`∀ C : ENNReal, 1 ≤ C → C ≠ ⊤ → cfg.AScaleData C cfg.a ν →`
and requiring `C² * K(C₀) * C₁' * Θ' ≤ δ^(-ν)` at fixed positive
factors. Since `AScaleData` is upward closed in `C`, this condition is
false whenever an admissible `C` exists.
`goalMult_of_a_ge_of_goalDensity` supplies such a constant under the
scale threshold. The two theorems below establish the obstruction first
abstractly and then for this density-threshold expression.

The applicable estimate is a threshold at the particular comparison
constant supplied by the scale argument, as used in
`Kakeya.VeryNotSticky.goalMult_of_denseInBody_at`. Its bound must be
controlled explicitly, rather than quantified over all admissible constants.
-/

/-- **The honest per-`C` consumer step**, the one thing the thick case actually needs from a
repaired `density` field.

No quantifier over `C`: the caller hands over the comparison constant the scale layer produced,
its `AScaleData`, the implication `goalDensity (C²) → goalMult` that came with it, and the
threshold **at that `C`**. This is satisfiable — unlike its `∀ C` wrapper
`Kakeya.VeryNotSticky.goalMult_of_a_ge_of_thresholds_at`, whose hypothesis
`Kakeya.VeryNotSticky.no_densityAfter_forall_C` refutes. -/
theorem goalMult_of_denseInBody_at (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ')
    (bd : BallData cfg) (hβ1 : cfg.β ≤ 1) (hthick : cfg.δ ^ (1 - τ) ≤ cfg.a)
    (hδ₂ : (bd.Cbias : ℝ≥0∞) * (((48 * bd.C₀ ^ 6) ^ 3 : ℝ≥0) : ℝ≥0∞) ≤
      (cfg.δ : ℝ≥0∞) ^ (-(τ * cfg.ϱ)))
    {CP Θ₀ C_NC : ℝ≥0} (hCP : 1 ≤ CP) (hΘ₀ : 1 ≤ Θ₀) {ηF : ℝ} (hηF : 0 < ηF)
    (hbudget : PlankFrostmanUsable bd τ CP C_NC ηF)
    (hpres : ThickPlankPresentable bd CP Θ₀ C_NC)
    {C : ℝ≥0∞} (hC1 : 1 ≤ C) (hCtop : C ≠ ⊤)
    (himp : cfg.goalDensity (C ^ 2) cfg.a (cfg.ϱ * cfg.β * τ / 8) →
      cfg.goalMult (cfg.ϱ * cfg.β * τ / 8))
    (hthrC : C ^ 2 * ENNReal.ofReal (8 * Real.pi * (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3) *
        (denseInBodyC₁ CP (cfg.ϱ * cfg.β * τ / 8) cfg.β : ℝ≥0∞) *
        (denseInBodyΘ CP Θ₀ bd.Cbias : ℝ≥0∞) ≤
      (cfg.δ : ℝ≥0∞) ^ (-(cfg.ϱ * cfg.β * τ / 8))) :
    cfg.goalMult (cfg.ϱ * cfg.β * τ / 8) := by
  have hK1 : (1 : ℝ) ≤ 8 * Real.pi * (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3 := by
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hs : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
    have hC₀ : (1 : ℝ) ≤ (bd.C₀ : ℝ) := by exact_mod_cast bd.hC₀
    have hbase : (1 : ℝ) ≤ 2 * Real.sqrt 3 + (bd.C₀ : ℝ) := by linarith
    have hcube : (1 : ℝ) ≤ (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3 := one_le_pow₀ hbase
    have h8pi : (24 : ℝ) ≤ 8 * Real.pi := by linarith
    calc
      (1 : ℝ) ≤ 24 * 1 := by norm_num
      _ ≤ (8 * Real.pi) * (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3 :=
          mul_le_mul h8pi hcube (by norm_num) (by linarith)
      _ = 8 * Real.pi * (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3 := by ring
  have hKe : (1 : ℝ≥0∞) ≤
      ENNReal.ofReal (8 * Real.pi * (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3) := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal hK1
  have hCsq : (1 : ℝ≥0∞) ≤ C ^ 2 := one_le_pow₀ hC1
  have hΛ1 : (1 : ℝ≥0∞) ≤
      C ^ 2 * ENNReal.ofReal (8 * Real.pi * (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3) :=
    one_le_mul hCsq hKe
  have hΛtop : C ^ 2 * ENNReal.ofReal (8 * Real.pi * (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3)
      ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.pow_ne_top hCtop) ENNReal.ofReal_ne_top
  have h := exists_denseInBody_at cfg params bd hβ1 hthick hδ₂ hCP hΘ₀ hηF hbudget hpres
    (C ^ 2 * ENNReal.ofReal (8 * Real.pi * (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3))
    hΛ1 hΛtop hthrC
  exact himp (goalDensity_of_denseInBody cfg bd (K := C ^ 2)
    (ν := cfg.ϱ * cfg.β * τ / 8) h)

/-! ### The named pair is a legal pair of witnesses -/

/-! ### F33 — the re-cut of `Kakeya.VeryNotSticky.ThickDensityThresholds.density`

The bare, `C`-free threshold and the thick-case entry point that reads it. Both live here,
downstream of `goalMult_of_denseInBody_at`, because that is the first module in which the
named-constant density estimate is available; `MainLemma2/ThickCase.lean`, where the field
is declared, is upstream of it. -/

/-- **The bare, `C`-free threshold suffices**: with it the thick branch reaches
`cfg.goalMult (ϱβτ/8)` and `Kakeya.VeryNotSticky.ThickDensityThresholds.density` is never read. -/
theorem goalMult_of_a_ge_of_bareThreshold (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ')
    (bd : BallData cfg) (hβ1 : cfg.β ≤ 1) (hthick : cfg.δ ^ (1 - τ) ≤ cfg.a)
    {thr : ScaleThresholds} (hthr : cfg.δ ≤ thr.aScale (cfg.ϱ * cfg.β * τ / 8))
    (hδ₂ : (bd.Cbias : ℝ≥0∞) * (((48 * bd.C₀ ^ 6) ^ 3 : ℝ≥0) : ℝ≥0∞) ≤
      (cfg.δ : ℝ≥0∞) ^ (-(τ * cfg.ϱ)))
    {CP Θ₀ C_NC : ℝ≥0} (hCP : 1 ≤ CP) (hΘ₀ : 1 ≤ Θ₀) {ηF : ℝ} (hηF : 0 < ηF)
    (hbudget : PlankFrostmanUsable bd τ CP C_NC ηF)
    (hpres : ThickPlankPresentable bd CP Θ₀ C_NC)
    (hbare : ENNReal.ofReal (8 * Real.pi * (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3) *
        (denseInBodyC₁ CP (cfg.ϱ * cfg.β * τ / 8) cfg.β : ℝ≥0∞) *
        (denseInBodyΘ CP Θ₀ bd.Cbias : ℝ≥0∞) ≤
      (cfg.δ : ℝ≥0∞) ^ (-(cfg.ϱ * cfg.β * τ / 8 - cfg.η))) :
    cfg.goalMult (cfg.ϱ * cfg.β * τ / 8) := by
  obtain ⟨C, hC1, hCtop, hCsq, hdata, himp⟩ := goalMult_of_a_ge_of_goalDensity cfg params hthr
  refine goalMult_of_denseInBody_at cfg params bd hβ1 hthick hδ₂ hCP hΘ₀ hηF hbudget hpres
    hC1 hCtop himp ?_
  have hδ0 : (cfg.δ : ℝ≥0∞) ≠ 0 := by
    simpa using (ENNReal.coe_pos.mpr cfg.hδ).ne'
  have hδtop : (cfg.δ : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hsplit : (cfg.δ : ℝ≥0∞) ^ (-cfg.η) *
      (cfg.δ : ℝ≥0∞) ^ (-(cfg.ϱ * cfg.β * τ / 8 - cfg.η)) =
      (cfg.δ : ℝ≥0∞) ^ (-(cfg.ϱ * cfg.β * τ / 8)) := by
    rw [← ENNReal.rpow_add _ _ hδ0 hδtop]
    congr 1
    ring
  calc C ^ 2 * ENNReal.ofReal (8 * Real.pi * (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3) *
        (denseInBodyC₁ CP (cfg.ϱ * cfg.β * τ / 8) cfg.β : ℝ≥0∞) *
        (denseInBodyΘ CP Θ₀ bd.Cbias : ℝ≥0∞)
      = C ^ 2 * (ENNReal.ofReal (8 * Real.pi * (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3) *
          (denseInBodyC₁ CP (cfg.ϱ * cfg.β * τ / 8) cfg.β : ℝ≥0∞) *
          (denseInBodyΘ CP Θ₀ bd.Cbias : ℝ≥0∞)) := by ring
    _ ≤ (cfg.δ : ℝ≥0∞) ^ (-cfg.η) *
          (cfg.δ : ℝ≥0∞) ^ (-(cfg.ϱ * cfg.β * τ / 8 - cfg.η)) := by
        exact mul_le_mul' hCsq hbare
    _ = (cfg.δ : ℝ≥0∞) ^ (-(cfg.ϱ * cfg.β * τ / 8)) := hsplit

end Kakeya.VeryNotSticky

end

end

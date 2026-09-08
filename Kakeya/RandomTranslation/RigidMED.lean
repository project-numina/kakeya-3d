/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Asymptotics
public import Kakeya.RandomTranslation.RigidMotionChernoff

/-!
# The CF-free ED multiplicity cap `rigidMED`

The old random-copy argument capped the essential-distinctness multiplicity of the randomised family
by the deterministic `J`-fold union bound

`M_ED := ⌈CF⌉₊ * C_pack_ext + 1`,

which is linear in the Frostman constant and therefore forces the small-scale threshold to depend on
`CF`. That is the defect this construction avoids.

The replacement is **polylogarithmic in `1/δ` and completely free of `CF`**:

`rigidMED C δ = ⌈C · (1 + log (1/δ))⌉₊ + 1`,

where `C` is a dimensional constant coming from the Chernoff threshold
(`Kakeya.edBadCount_chernoff_tail`) and the polynomial cardinality of the test-tube net.

## The absorption lemmas

Downstream, `RandCF`'s smallness envelopes need the cap to be absorbed by an arbitrary negative
power of `δ`. Since `rigidMED` is polylogarithmic this is automatic, and rather than prove one
absorption lemma per envelope conjunct we prove a single workhorse,
`Kakeya.eventually_le_rpow_neg_of_le_polylog`: *any* quantity dominated by
`C · (1 + log (1/δ))^k` is eventually `≤ δ^(-η)`, for every `η > 0` and every fixed degree `k`.
The linear and quadratic forms actually consumed (the old `S6` conjunct was quadratic in the cap)
are then immediate corollaries.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Metric Set Filter Topology

namespace Kakeya

/-- **Robust polylog-versus-power absorption.** For every positive constant `C`, every exponent
`η > 0` and every fixed degree `k`, a degree-`k` polynomial in `log (1/δ)` is eventually
dominated by `δ^(-η)` as `δ → 0⁺`. -/
theorem absorb_polylog_le_rpow_neg {C η : ℝ} (hC : 0 < C) (hη : 0 < η) (k : ℕ) :
    ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), C * (1 + Real.log (1 / δ)) ^ k ≤ δ ^ (-η) := by
  by_cases hk : k = 0
  · filter_upwards [absorb_const_le_rpow_neg hC hη] with δ hδ
    simpa [hk] using hδ
  · let η' : ℝ := η / (2 * (k : ℝ))
    have hη' : 0 < η' := by
      dsimp [η']
      positivity
    have hk_ne : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    have hlog_le : ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), Real.log (1 / δ) ≤ δ ^ (-(η' / 2)) := by
      have h := absorb_log_le_rpow_neg (C := (1 : ℝ)) (M := (1 : ℝ)) (η := η' / 4)
        (by norm_num) (by norm_num) (by positivity)
      filter_upwards [h] with δ h'
      have hE : (-(2 * (η' / 4)) : ℝ) = -(η' / 2) := by ring
      rw [hE] at h'
      simpa using h'
    have hconst1 : ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), (1 : ℝ) ≤ δ ^ (-(η' / 2)) :=
      absorb_const_le_rpow_neg (C := (1 : ℝ)) (η := η' / 2) (by norm_num) (by positivity)
    have hconst2 : ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), (2 : ℝ) ≤ δ ^ (-(η' / 2)) :=
      absorb_const_le_rpow_neg (C := (2 : ℝ)) (η := η' / 2) (by norm_num) (by positivity)
    have hdiff : ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), 1 + Real.log (1 / δ) ≤ δ ^ (-η') := by
      filter_upwards [hconst1, hlog_le, hconst2, self_mem_nhdsWithin]
          with δ hlog1 hlog hconst2 (hδpos : 0 < δ)
      calc
        1 + Real.log (1 / δ) ≤ δ ^ (-(η' / 2)) + δ ^ (-(η' / 2)) := add_le_add hlog1 hlog
        _ = (2 : ℝ) * δ ^ (-(η' / 2)) := by ring
        _ ≤ δ ^ (-(η' / 2)) * δ ^ (-(η' / 2)) :=
          mul_le_mul_of_nonneg_right hconst2 (Real.rpow_nonneg hδpos.le _)
        _ = δ ^ (-(η' / 2) + -(η' / 2)) := (Real.rpow_add hδpos _ _).symm
        _ = δ ^ (-η') := by congr 1; ring
    have hC_add : ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), C ≤ δ ^ (-(η / 2)) :=
      absorb_const_le_rpow_neg hC (by positivity)
    have hδle1 : ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), δ ≤ 1 := by
      refine Filter.eventually_of_mem (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)) ?_
      intro δ hδ
      exact le_of_lt hδ.2
    have hlog_nonneg : ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), 0 ≤ 1 + Real.log (1 / δ) := by
      filter_upwards [self_mem_nhdsWithin, hδle1] with δ hδpos hδle1
      have hone : (1 : ℝ) ≤ 1 / δ := by
        rw [le_div_iff₀ hδpos]
        nlinarith
      have hge : (0 : ℝ) ≤ Real.log (1 / δ) := Real.log_nonneg hone
      nlinarith
    filter_upwards [hdiff, hC_add, self_mem_nhdsWithin, hlog_nonneg]
      with δ hdiff hC_add (hδpos : 0 < δ) hlog_nonneg
    have hpow : (δ ^ (-η')) ^ k = δ ^ (-(η' * (k : ℝ))) := by
      rw [← Real.rpow_natCast (δ ^ (-η')) k]
      rw [← Real.rpow_mul hδpos.le (-η') (k : ℝ)]
      congr 1
      ring
    have hη'k : η' * (k : ℝ) = η / 2 := by
      dsimp [η']
      field_simp [hk_ne]
    calc
      C * (1 + Real.log (1 / δ)) ^ k ≤ δ ^ (-(η / 2)) * (δ ^ (-η')) ^ k := by
        exact mul_le_mul hC_add (pow_le_pow_left₀ hlog_nonneg hdiff k)
          (pow_nonneg hlog_nonneg k) (Real.rpow_nonneg hδpos.le _)
      _ = δ ^ (-(η / 2)) * δ ^ (-(η' * (k : ℝ))) := by rw [hpow]
      _ = δ ^ (-(η / 2)) * δ ^ (-(η / 2)) := by rw [hη'k]
      _ = δ ^ (-(η / 2) + -(η / 2)) := (Real.rpow_add hδpos _ _).symm
      _ = δ ^ (-η) := by congr 1; ring

/-- The workhorse form: anything dominated by a degree-`k` polylogarithm is eventually dominated by
`δ^(-η)`. Stated for `NNReal` scales, which is what the `RandCF` envelopes use. -/
theorem eventually_le_rpow_neg_of_le_polylog {C η : ℝ} (hC : 0 < C) (hη : 0 < η) (k : ℕ)
    {f : ℝ≥0 → ℝ}
    (hf : ∀ δ : ℝ≥0, 0 < δ → (δ : ℝ) ≤ 1 →
      f δ ≤ C * (1 + Real.log (1 / (δ : ℝ))) ^ k) :
    ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0, f δ ≤ (δ : ℝ) ^ (-η) := by
  have hmain : ∀ᶠ (δ : ℝ≥0) in 𝓝[>] (0 : ℝ≥0),
      C * (1 + Real.log (1 / (δ : ℝ))) ^ k ≤ (δ : ℝ) ^ (-η) :=
    nnreal_eventually_of_real_eventually (absorb_polylog_le_rpow_neg hC hη k)
  have hle1 : ∀ᶠ (δ : ℝ≥0) in 𝓝[>] (0 : ℝ≥0), (δ : ℝ) ≤ 1 := by
    have hx : ∀ᶠ (x : ℝ) in 𝓝[>] (0 : ℝ), x ≤ 1 := by
      refine Filter.eventually_of_mem (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)) ?_
      intro x hx
      exact le_of_lt hx.2
    exact nnreal_eventually_of_real_eventually hx
  filter_upwards [hmain, self_mem_nhdsWithin, hle1] with δ hmain hpos hle1
  exact (hf δ hpos hle1).trans hmain

/-- **The CF-free ED multiplicity cap.** Polylogarithmic in `1/δ`; the constant `C` is dimensional
(it comes from the Chernoff threshold and the polynomial size of the test-tube net). -/
noncomputable def rigidMED (C : ℝ) (δ : ℝ≥0) : ℕ :=
  ⌈C * (1 + Real.log (1 / (δ : ℝ)))⌉₊ + 1

/-- `rigidMED` is dominated by a degree-one polylogarithm. -/
theorem rigidMED_le_polylog {C : ℝ} (hC : 0 < C) (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : (δ : ℝ) ≤ 1) :
    ((rigidMED C δ : ℕ) : ℝ) ≤ (C + 2) * (1 + Real.log (1 / (δ : ℝ))) ^ 1 := by
  let L : ℝ := 1 + Real.log (1 / (δ : ℝ))
  have hδR : 0 < (δ : ℝ) := NNReal.coe_pos.mpr hδ
  have hone : (1 : ℝ) ≤ 1 / (δ : ℝ) := one_le_one_div hδR hδ1
  have hlog : 0 ≤ Real.log (1 / (δ : ℝ)) := Real.log_nonneg hone
  have hL : (1 : ℝ) ≤ L := by
    dsimp [L]
    linarith
  have hx : 0 ≤ C * L := by
    exact mul_nonneg (le_of_lt hC) (by linarith)
  have hceil : ((⌈C * L⌉₊ : ℕ) : ℝ) ≤ C * L + 1 := (Nat.ceil_lt_add_one hx).le
  have hcard : ((rigidMED C δ : ℕ) : ℝ) = ((⌈C * L⌉₊ : ℕ) : ℝ) + 1 := by
    simp [rigidMED, L]
  have hp : (1 + Real.log (1 / (δ : ℝ))) ^ 1 = L := by
    dsimp [L]
    rw [pow_one]
  rw [hp]
  calc
    ((rigidMED C δ : ℕ) : ℝ) = ((⌈C * L⌉₊ : ℕ) : ℝ) + 1 := hcard
    _ ≤ C * L + 1 + 1 := by nlinarith [hceil]
    _ = C * L + 2 := by ring
    _ ≤ (C + 2) * L := by nlinarith [hL]

end Kakeya

end

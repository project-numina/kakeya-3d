/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineDefectCoveringBridge

/-!
# The covering bridge's two remaining rows: the anisotropic pull-back, and the grid

`Reduction/SpineDefectCoveringBridge.lean` transcribes `lem:defect-covering-bridge` and left exactly two rows open: `BridgeAnisotropicPullback` (the estimate
`eq:defect-pullback-line`) and `hgrid` (the location of `m` on the radius grid).  This leaf closes both.

## The anisotropic pull-back — `exists_bridgeAnisotropicPullback`

`anisoInvLin ea ρ y = 8·(y_∥ + ρ y_⊥)` is the source's `L₀^{-1}`, the **anisotropic**
inverse of the normalisation `L`.  This is precisely what the tree could not express: `Kakeya.ML2Reduction.carrier_subset_dilate_of_normaliseBody_subset_dilate` pulls back through
`normaliseBody`, whose contraction is the **isotropic** factor `8`, and lands in a dilated *tube*;
Mathlib's image lemmas for balls (`Metric.smul_image_closedBall`,
`LinearIsometryEquiv.image_closedBall`, `IsometryEquiv.image_closedBall`) cover only the isometric
and scalar cases.  A search of the whole tree for producers of `_ ⊆ lineNbhd _ _ _` returns only
`Conjunct6LineED.lean`'s core comparison and one negative statement.  So the estimate is built
here, from the inner-product geometry.

The proof follows the source line by line:

* `transverse_projection_norm_le` is  — with `d_W·e_a ≥ 1/6`, the component of `e_a`
  normal to the pulled-back line has norm at most `6 ρ_a`.  The bound is sharp in the source's
  own constants: `‖·‖² = ρ_a²‖d_⊥‖²/(d₁² + ρ_a²‖d_⊥‖²) ≤ 36 ρ_a²`.
* `norm_sub_unitProj_le` is the elementary fact that projecting off a unit vector does not
  increase norms; it is used three times.
* `exists_bridgeAnisotropicPullback` gives the following estimate: for `‖v‖ ≤ σ` the normal component of
  `L₀^{-1}v = 8(v_∥ + ρ_a v_⊥)` is at most `48 ρ_a σ + 8 ρ_a σ = 56 ρ_a σ`.  The longitudinal
  expansion is absorbed by the choice of the line parameter `s₀`, which is the Lean content of
   ("the pulled-back line itself absorbs it").

`hdir`, the cone `d_W · e_a ≥ 1/6` of `eq:defect-cover-direction`, is the source's
own *preceding* step — proved there from the geometry of the covered `b`-cell, not
from this estimate — and is carried here as a named hypothesis.

## The grid — `bridgeGrid`

`bridgeGrid M δ k` is `ρ_k = (1/40)δ^{k/M}` for `k < M` and `ρ_M = δ`.
`bridgeGrid_step` is the one-step ratio `q ρ_k ≤ ρ_{k+1} ≤ 40 q ρ_k`; both ends are
equalities on this grid, the left for `k+1 < M` and the right at the last step.
`bridgeGrid_hgrid_of_maximal` is the bridge's `hgrid` itself;
`bridgeGrid_m_gt_a` and `bridgeGrid_m_lt_b` are the two location rows; and
`bridgeGrid_window_lower` / `bridgeGrid_window_upper` are the two window endpoints, which are what put `m` in the range where `eq:defect-bridge-floor` is available.

Constants copied, never fitted: `1/40` and the grid exponent `k/M`, `40` in the step
ratio, `56`, `1/6`, `6ρ_a`, `2` in `δ̃ = ρ_b/(2ρ_a)`.
-/

@[expose] public section

open Real RealInnerProductSpace

namespace Kakeya.ML2Core

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


section Grid


/-- **The source's radius grid**:
`ρ_k = (1/40)·δ^{k/M}` for `0 ≤ k < M`, and `ρ_M = δ`. -/
noncomputable def bridgeGrid (M : ℕ) (δ : ℝ) (k : ℕ) : ℝ :=
  if k < M then (1 / 40) * δ ^ ((k : ℝ) / (M : ℝ)) else δ

theorem bridgeGrid_pos {M : ℕ} {δ : ℝ} (hδ0 : 0 < δ) (k : ℕ) : 0 < bridgeGrid M δ k := by
  unfold bridgeGrid
  split
  · positivity
  · exact hδ0

/-- **The one-step ratio**: `q ρ_k ≤ ρ_{k+1} ≤ 40 q ρ_k` with `q = δ^{1/M}`.
Both ends are equalities on the grid: the left one for `k+1 < M`, the right one at the last
step `k+1 = M`, where `ρ_M = δ = 40 q ρ_{M-1}`. -/
theorem bridgeGrid_step {M : ℕ} {δ : ℝ} (hM : 0 < M) (hδ0 : 0 < δ) {k : ℕ} (hk : k < M) :
    δ ^ (1 / (M : ℝ)) * bridgeGrid M δ k ≤ bridgeGrid M δ (k + 1) ∧
      bridgeGrid M δ (k + 1) ≤ 40 * (δ ^ (1 / (M : ℝ)) * bridgeGrid M δ k) := by
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hadd : δ ^ (1 / (M : ℝ)) * δ ^ ((k : ℝ) / (M : ℝ))
      = δ ^ (((k : ℝ) + 1) / (M : ℝ)) := by
    rw [← Real.rpow_add hδ0]
    congr 1
    field_simp
    ring
  have hkey : δ ^ (1 / (M : ℝ)) * ((1 / 40) * δ ^ ((k : ℝ) / (M : ℝ)))
      = (1 / 40) * δ ^ (((k : ℝ) + 1) / (M : ℝ)) := by
    calc δ ^ (1 / (M : ℝ)) * ((1 / 40) * δ ^ ((k : ℝ) / (M : ℝ)))
        = (1 / 40) * (δ ^ (1 / (M : ℝ)) * δ ^ ((k : ℝ) / (M : ℝ))) := by ring
      _ = (1 / 40) * δ ^ (((k : ℝ) + 1) / (M : ℝ)) := by rw [hadd]
  rcases lt_or_ge (k + 1) M with h | h
  · have h1 : bridgeGrid M δ k = (1 / 40) * δ ^ ((k : ℝ) / (M : ℝ)) := by
      unfold bridgeGrid; rw [if_pos hk]
    have h2 : bridgeGrid M δ (k + 1) = (1 / 40) * δ ^ ((((k : ℕ) + 1 : ℕ) : ℝ) / (M : ℝ)) := by
      unfold bridgeGrid; rw [if_pos h]
    rw [h1, h2, hkey]
    push_cast
    constructor
    · exact le_of_eq (by ring_nf)
    · nlinarith [Real.rpow_pos_of_pos hδ0 (((k : ℝ) + 1) / (M : ℝ))]
  · have hkM : k + 1 = M := le_antisymm hk h
    have h1 : bridgeGrid M δ k = (1 / 40) * δ ^ ((k : ℝ) / (M : ℝ)) := by
      unfold bridgeGrid; rw [if_pos hk]
    have h2 : bridgeGrid M δ (k + 1) = δ := by
      unfold bridgeGrid; rw [if_neg (by omega)]
    have h3 : δ ^ (1 / (M : ℝ)) * ((1 / 40) * δ ^ ((k : ℝ) / (M : ℝ))) = δ / 40 := by
      rw [hkey]
      have : ((k : ℝ) + 1) / (M : ℝ) = 1 := by
        have : ((k : ℝ) + 1) = (M : ℝ) := by exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hkM
        rw [this]; field_simp
      rw [this, Real.rpow_one]; ring
    rw [h1, h2, h3]
    constructor <;> linarith


/-- **The upper window endpoint**: `σ ≥ δ̃^{1-ε_sc}` with `δ̃ = x/2` and
`ε ≤ ε_sc` give `x/(56 σ) ≤ x^ε`; "the fixed factor `2` is dominated by `56`". -/
theorem bridgeGrid_window_upper {σ x ε εsc : ℝ}
    (hσ0 : 0 < σ) (hx0 : 0 < x) (hx1 : x ≤ 1) (hεsc0 : 0 < εsc) (hεsc1 : εsc < 1)
    (hε : ε ≤ εsc)
    (hσlo : (x / 2) ^ (1 - εsc) ≤ σ) :
    x / (56 * σ) ≤ x ^ ε := by
  have hhalf : (x / 2) ^ (1 - εsc) = x ^ (1 - εsc) * (1 / 2 : ℝ) ^ (1 - εsc) := by
    rw [show x / 2 = x * (1 / 2 : ℝ) by ring, Real.mul_rpow hx0.le (by norm_num)]
  have hpow : (1 / 2 : ℝ) ^ (1 - εsc) ≥ 1 / 2 := by
    calc (1 / 2 : ℝ) ^ (1 - εsc) ≥ (1 / 2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
      _ = 1 / 2 := by rw [Real.rpow_one]
  have hx1e : x ^ (1 - εsc) * x ^ εsc = x := by rw [← Real.rpow_add hx0]; simp
  have hxe : x ^ εsc ≤ x ^ ε := Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hε
  have h1 : x ^ (1 - εsc) * (1 / 2 : ℝ) ≤ σ := by
    refine le_trans ?_ hσlo
    rw [hhalf]
    have := Real.rpow_pos_of_pos hx0 (1 - εsc)
    nlinarith
  rw [div_le_iff₀ (by positivity)]
  nlinarith [Real.rpow_pos_of_pos hx0 (1 - εsc), Real.rpow_pos_of_pos hx0 εsc,
    Real.rpow_pos_of_pos hx0 ε]

end Grid

end Kakeya.ML2Core

end

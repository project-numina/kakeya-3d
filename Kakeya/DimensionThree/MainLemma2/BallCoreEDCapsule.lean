/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.BallCoreEDSegments

/-!
# R31's geometry at a general dilation `K`, and the fibre-count threshold

`Kakeya/DimensionThree/MainLemma2/BallCoreEDSegments.lean` reduces GWZ §9.3 steps 6–8 to three
Euclidean-geometry statements about two capsules and a piece of the ball cover
(`Kakeya.VeryNotSticky.CapsuleComparability`, `CapsuleCoreLine`, `CapsuleClassCount`), and
records that the first of them has **no slack**: it puts the shading of a comparable tube inside
the representative's `δ`-capsule, i.e. within `δ` — not `C₀ δ` — of its core line
(`Kakeya.VeryNotSticky.capsuleComparability_forces_delta_alignment`). GWZ's word *comparable*
(GWZ) means containment in a bounded **dilate**, and the dilate is what the existing
`BallDataCore` has nowhere to put.

This file treats the dilation as a parameter `K` and proves the estimates for every `K ≥ 1`.

## The dilated capsule

`Kakeya.VeryNotSticky.segCarrierSetAt K T c L` is the closed `K δ`-neighbourhood of the same core
window that `segCarrierSet` thickens by `δ`; `segCarrierSetAt 1 = segCarrierSet`. Its thickness
profile is computed exactly:

* `Kakeya.VeryNotSticky.hasThicknesses_segCarrierSetAt` — profile `![4L, δ, δ]` at the constant
  `4 K`, **not** `4`. This is the price of the dilate in `BallDataCore.segs_thickness`, and it is
  what makes `core.C₀ = C₀` under `hC₀ : 4 ≤ C₀` available only at `K = 1`;
* `Kakeya.VeryNotSticky.thickness_segCarrierSetAt_le_two_nsmul` — `segs_dims` survives at every
  `K` with the same constant `2`;
* `Kakeya.VeryNotSticky.volume_segCarrierSetAt_le` — the upper half of the `segs_density` price.

## The three obligations at general `K`

`Kakeya.VeryNotSticky.CapsuleComparableAt core K` is the formal reading of "comparable": two
capsules of one ball that are not essentially distinct each lie in the `K`-dilate of the other.
From it:

* (C1) `Kakeya.VeryNotSticky.capsuleShade_subset_dilate_of_comparableAt`;
* (C2) `Kakeya.VeryNotSticky.dilatedCapsule_subset_coreLine_of_comparableAt`, at the radius
  `2 K δ` — so a `BallDataCore` absorbs it exactly when `2 K ≤ core.C₀`;
* (C3) `Kakeya.VeryNotSticky.capsuleClassCount_of_dilateCount`, which replaces the
  measure-theoretic `¬ IsEssentiallyDistinct` in the count by the explicit containment
  `capsule j ⊆ K`-dilate of `capsule i`.

The bridges `Kakeya.VeryNotSticky.capsuleCoreLine_of_comparableAt`,
`capsuleComparability_of_comparableAt_one` and `capsuleInputs_of_comparableAt_one` supply the corresponding input of `Kakeya.VeryNotSticky.exists_core_edSegments_of_cover_of_capsule` at the specified dilation. Clause (C1) for the undilated structure follows only at `K = 1`.

## The fibre-count threshold

`Kakeya.VeryNotSticky.eventually_classCount_le_fibreBudget`: for `0 < η` and any `δ`-free `M₀`,
eventually in `δ` one has `M₀ · δ^{-2 exscal} ≤ δ^{-(η + 2 exscal)}`. This is the shape
`Kakeya.VeryNotSticky.eventually_slabScale_of_uniform_bounds` consumes, so the `δ`-smallness gap
in the fibre-count budget closes by one `filter_upwards` whichever value the class count takes.

and
`Kakeya.VeryNotSticky.exists_core_edSegments_of_cover_of_capsule` is untouched.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

namespace Kakeya.VeryNotSticky

universe u

/-! ### The δ-threshold of the fibre-count budget -/


/-! ### The `K`-dilated capsule -/

variable {δ : ℝ≥0}

/-- **The `K`-dilated tube segment**: the closed `K δ`-neighbourhood of the same core window
that `Kakeya.VeryNotSticky.segCarrierSet` thickens by `δ`. GWZ's `T_B` is a `δ×δ×r₁`-tube "of
the form `T ∩ B`" and the tubes of `𝕋(T_B)` are only *comparable* to it (GWZ):
comparability of convex bodies is containment in a bounded **dilate**, and `K` is that dilate,
retained as an explicit parameter. `K = 1` is `segCarrierSet`. -/
noncomputable def segCarrierSetAt (K : ℝ≥0) (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) (L : ℝ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  cthickening ((K : ℝ) * (δ : ℝ))
    (segment ℝ (corePt T (segStart T c L)) (corePt T (segStart T c L + 2 * L)))

@[simp] theorem segCarrierSetAt_one (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) (L : ℝ) :
    segCarrierSetAt 1 T c L = segCarrierSet T c L := by
  simp [segCarrierSetAt, segCarrierSet]

theorem segCarrierSetAt_mono {K K' : ℝ≥0} (hKK' : K ≤ K')
    (T : Tube δ (EuclideanSpace ℝ (Fin 3))) (c : EuclideanSpace ℝ (Fin 3)) (L : ℝ) :
    segCarrierSetAt K T c L ⊆ segCarrierSetAt K' T c L := by
  refine cthickening_mono ?_ _
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hKK') δ.coe_nonneg

theorem segCarrierSet_subset_segCarrierSetAt {K : ℝ≥0} (hK : 1 ≤ K)
    (T : Tube δ (EuclideanSpace ℝ (Fin 3))) (c : EuclideanSpace ℝ (Fin 3)) (L : ℝ) :
    segCarrierSet T c L ⊆ segCarrierSetAt K T c L := by
  rw [← segCarrierSetAt_one T c L]
  exact segCarrierSetAt_mono hK T c L

theorem isClosed_segCarrierSetAt (K : ℝ≥0) (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) (L : ℝ) : IsClosed (segCarrierSetAt K T c L) :=
  isClosed_cthickening

/-- The core window of a segment sits in the closed ball of radius `L` about its midpoint. -/
theorem segment_subset_closedBall_mid (T : Tube δ (EuclideanSpace ℝ (Fin 3))) (a L : ℝ)
    (hL : 0 ≤ L) :
    segment ℝ (corePt T a) (corePt T (a + 2 * L)) ⊆ closedBall (corePt T (a + L)) L := by
  intro z hz
  obtain ⟨u, hu, rfl⟩ := segment_subset_corePt_image T (by linarith) hz
  rw [Metric.mem_closedBall, dist_corePt]
  rcases hu with ⟨h1, h2⟩
  rw [abs_le]
  constructor <;> linarith

theorem segCarrierSetAt_subset_closedBall (K : ℝ≥0)
    (T : Tube δ (EuclideanSpace ℝ (Fin 3))) (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ}
    (hL : 0 ≤ L) :
    segCarrierSetAt K T c L ⊆
      closedBall (corePt T (segStart T c L + L)) ((K : ℝ) * (δ : ℝ) + L) := by
  refine subset_trans (cthickening_subset_of_subset _
    (segment_subset_closedBall_mid T (segStart T c L) L hL)) ?_
  rw [cthickening_closedBall (by positivity) hL]

theorem isBounded_segCarrierSetAt (K : ℝ≥0) (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ} (hL : 0 ≤ L) :
    Bornology.IsBounded (segCarrierSetAt K T c L) :=
  Metric.isBounded_closedBall.subset (segCarrierSetAt_subset_closedBall K T c hL)

/-- **The dilated capsule still lies along the core line**, at the dilated radius. -/
theorem segCarrierSetAt_subset_cthickening_line (K : ℝ≥0)
    (T : Tube δ (EuclideanSpace ℝ (Fin 3))) (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ}
    (hL : 0 ≤ L) {C : ℝ} (hC : (K : ℝ) * (δ : ℝ) ≤ C) :
    segCarrierSetAt K T c L ⊆ cthickening C
      (AffineSubspace.mk' (corePt T (segStart T c L)) (Submodule.span ℝ {T.direction}) :
        Set (EuclideanSpace ℝ (Fin 3))) := by
  have hline : segment ℝ (corePt T (segStart T c L)) (corePt T (segStart T c L + 2 * L)) ⊆
      (AffineSubspace.mk' (corePt T (segStart T c L)) (Submodule.span ℝ {T.direction}) :
        Set (EuclideanSpace ℝ (Fin 3))) := by
    intro z hz
    obtain ⟨u, _, rfl⟩ := segment_subset_corePt_image T (by linarith) hz
    have : corePt T u = (u - segStart T c L) • T.direction +ᵥ corePt T (segStart T c L) := by
      simp only [corePt, vadd_eq_add]; module
    rw [this]
    exact AffineSubspace.vadd_mem_mk' _
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  refine subset_trans ?_ (Metric.cthickening_mono hC _)
  exact Metric.cthickening_subset_of_subset ((K : ℝ) * (δ : ℝ)) hline


/-! ### The thickness profile of the dilated capsule: the price in `C₀` -/

theorem closedBall_subset_segCarrierSetAt (K : ℝ≥0)
    (T : Tube δ (EuclideanSpace ℝ (Fin 3))) (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ}
    (hL : 0 ≤ L) :
    closedBall (corePt T (coreParam T c)) ((K : ℝ) * (δ : ℝ)) ⊆ segCarrierSetAt K T c L :=
  Metric.closedBall_subset_cthickening (corePt_coreParam_mem_window T c hL) _

theorem le_thickness_segCarrierSetAt (K : ℝ≥0)
    (T : Tube δ (EuclideanSpace ℝ (Fin 3))) (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ}
    (hL : 0 ≤ L) {n : ℕ} (hn : n < 3) :
    (K : ℝ) * (δ : ℝ) ≤ Metric.thickness ℝ (segCarrierSetAt K T c L) n := by
  have hbdd := isBounded_segCarrierSetAt K T c hL
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
  have hcoe : ((K * δ : ℝ≥0) : ℝ) = (K : ℝ) * (δ : ℝ) := by push_cast; ring
  have h1 : (((K * δ : ℝ≥0)) : ℝ≥0∞) ≤
      Metric.ethickness ℝ (closedBall (corePt T (coreParam T c)) ((K * δ : ℝ≥0) : ℝ)) n :=
    le_ethickness_closedBall (V := EuclideanSpace ℝ (Fin 3)) (K * δ) (by rw [hfr]; exact hn)
  rw [hcoe] at h1
  have h2 : Metric.ethickness ℝ (closedBall (corePt T (coreParam T c)) ((K : ℝ) * (δ : ℝ))) n ≤
      Metric.ethickness ℝ (segCarrierSetAt K T c L) n :=
    Metric.ethickness_monotone (closedBall_subset_segCarrierSetAt K T c hL) n
  have h3 : ENNReal.ofReal ((K : ℝ) * (δ : ℝ)) ≤
      Metric.ethickness ℝ (segCarrierSetAt K T c L) n := by
    calc ENNReal.ofReal ((K : ℝ) * (δ : ℝ)) = (((K * δ : ℝ≥0)) : ℝ≥0∞) := by
          rw [← hcoe]; exact ENNReal.ofReal_coe_nnreal
      _ ≤ _ := h1.trans h2
  rw [Metric.ethickness_thickness' hbdd n] at h3
  exact (ENNReal.ofReal_le_ofReal_iff (Metric.thickness_nonneg _ _)).1 h3

theorem thickness_segCarrierSetAt_le (K : ℝ≥0)
    (T : Tube δ (EuclideanSpace ℝ (Fin 3))) (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ}
    (hL : 0 ≤ L) {n : ℕ} (hn : 1 ≤ n) :
    Metric.thickness ℝ (segCarrierSetAt K T c L) n ≤ (K : ℝ) * (δ : ℝ) := by
  have hrank : Module.rank ℝ
      (AffineSubspace.mk' (corePt T (segStart T c L))
        (Submodule.span ℝ {T.direction})).direction ≤ (n : Cardinal) := by
    rw [AffineSubspace.direction_mk']
    refine le_trans (rank_span_le _) ?_
    simp only [Cardinal.mk_fintype]
    exact_mod_cast Nat.one_le_cast.2 hn
  exact Metric.thickness_le_of_cthickening (by positivity) hrank
    (segCarrierSetAt_subset_cthickening_line K T c hL (le_refl _))

theorem le_thickness_segCarrierSetAt_zero (K : ℝ≥0)
    (T : Tube δ (EuclideanSpace ℝ (Fin 3))) (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ}
    (hL : 0 ≤ L) :
    L ≤ Metric.thickness ℝ (segCarrierSetAt K T c L) 0 := by
  have hbdd := isBounded_segCarrierSetAt K T c hL
  have hmemL : corePt T (segStart T c L) ∈ segCarrierSetAt K T c L :=
    Metric.self_subset_cthickening _ (left_mem_segment ℝ _ _)
  have hmemR : corePt T (segStart T c L + 2 * L) ∈ segCarrierSetAt K T c L :=
    Metric.self_subset_cthickening _ (right_mem_segment ℝ _ _)
  have hd : dist (corePt T (segStart T c L)) (corePt T (segStart T c L + 2 * L)) = 2 * L := by
    rw [dist_corePt, show segStart T c L - (segStart T c L + 2 * L) = -(2 * L) by ring,
      abs_neg, abs_of_nonneg (by linarith)]
  have h := Metric.half_dist_le_ethickness_zero (𝕜 := ℝ) hmemL hmemR
  rw [hd, Metric.ethickness_thickness' hbdd 0] at h
  have := (ENNReal.ofReal_le_ofReal_iff (Metric.thickness_nonneg _ _)).1 h
  linarith

theorem thickness_segCarrierSetAt_zero_le (K : ℝ≥0)
    (T : Tube δ (EuclideanSpace ℝ (Fin 3))) (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ}
    (hL : 0 ≤ L) :
    Metric.thickness ℝ (segCarrierSetAt K T c L) 0 ≤ (K : ℝ) * (δ : ℝ) + L :=
  Metric.thickness_le_of_subset_closedBall (segCarrierSetAt_subset_closedBall K T c hL)
    (by positivity) 0

/-- **The price of the dilate, in the constant of `BallDataCore.segs_thickness`.** The
`K`-dilated capsule of half-length `L = r₁/4` has the profile `![4L, δ, δ] = ![r₁, δ, δ]` at the
constant `4 K`, not `4`: `thickness` in the two thin directions is *exactly* `K δ`
(`le_thickness_segCarrierSetAt`, `thickness_segCarrierSetAt_le`). So a `BallDataCore` whose
segments are `K`-dilated capsules has `C₀ = 4 K`, and `core.C₀ = C₀` at `hC₀ : 4 ≤ C₀` is
available only for `K = 1`. -/
theorem hasThicknesses_segCarrierSetAt {K : ℝ≥0} (hK : 1 ≤ K)
    (T : Tube δ (EuclideanSpace ℝ (Fin 3))) (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ}
    (hL : 0 ≤ L) (hδL : (δ : ℝ) ≤ L) :
    Kakeya.HasThicknesses (segCarrierSetAt K T c L) (4 * K) ![4 * L, (δ : ℝ), (δ : ℝ)] := by
  have hKR : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hδ0 : (0 : ℝ) ≤ (δ : ℝ) := δ.coe_nonneg
  have hKpos : (0 : ℝ) < (K : ℝ) := by linarith
  have h0l := le_thickness_segCarrierSetAt_zero K T c hL
  have h0u := thickness_segCarrierSetAt_zero_le K T c hL
  have h1l := le_thickness_segCarrierSetAt K T c hL (n := 1) (by norm_num)
  have h1u := thickness_segCarrierSetAt_le K T c hL (n := 1) (by norm_num)
  have h2l := le_thickness_segCarrierSetAt K T c hL (n := 2) (by norm_num)
  have h2u := thickness_segCarrierSetAt_le K T c hL (n := 2) (by norm_num)
  have hc : ((4 * K : ℝ≥0) : ℝ) = 4 * (K : ℝ) := by push_cast; ring
  intro k
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  have hI : (4 * (K : ℝ))⁻¹ * (4 * L) ≤ L := by
    rw [inv_mul_eq_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hII : (K : ℝ) * (δ : ℝ) + L ≤ 4 * (K : ℝ) * (4 * L) := by nlinarith
  have hIII : (4 * (K : ℝ))⁻¹ * (δ : ℝ) ≤ (K : ℝ) * (δ : ℝ) := by
    have : (4 * (K : ℝ))⁻¹ ≤ (K : ℝ) := by
      rw [inv_le_iff_one_le_mul₀ (by positivity)]
      nlinarith
    nlinarith
  have hIV : (K : ℝ) * (δ : ℝ) ≤ 4 * (K : ℝ) * (δ : ℝ) := by nlinarith
  rcases hk with rfl | rfl | rfl <;> refine ⟨?_, ?_⟩ <;>
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, hc] <;> linarith

/-- **`segs_dims` for dilated capsules**: any two `K`-dilated capsules of the same half-length
have `2`-comparable thickness profiles, exactly as in the undilated case. -/
theorem thickness_segCarrierSetAt_le_two_nsmul {K : ℝ≥0} (hK : 1 ≤ K)
    (T T' : Tube δ (EuclideanSpace ℝ (Fin 3))) (c c' : EuclideanSpace ℝ (Fin 3)) {L : ℝ}
    (hL : 0 ≤ L) (hKδL : (K : ℝ) * (δ : ℝ) ≤ L) :
    Metric.thickness ℝ (segCarrierSetAt K T c L) ≤
      2 • Metric.thickness ℝ (segCarrierSetAt K T' c' L) := by
  intro n
  have hδ0 : (0 : ℝ) ≤ (δ : ℝ) := δ.coe_nonneg
  have hKR : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hsm : (2 • Metric.thickness ℝ (segCarrierSetAt K T' c' L)) n =
      2 * Metric.thickness ℝ (segCarrierSetAt K T' c' L) n := by simp
  have hnn : ∀ m : ℕ, 0 ≤ Metric.thickness ℝ (segCarrierSetAt K T' c' L) m :=
    fun m => Metric.thickness_nonneg _ _
  rw [hsm]
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n
    · have h0u := thickness_segCarrierSetAt_zero_le K T c hL
      have h0l := le_thickness_segCarrierSetAt_zero K T' c' hL
      have := hnn 0
      have hKd : 0 ≤ (K : ℝ) * (δ : ℝ) := by positivity
      linarith
    · have h1u := thickness_segCarrierSetAt_le K T c hL (n := 1) (by norm_num)
      have h1l := le_thickness_segCarrierSetAt K T' c' hL (n := 1) (by norm_num)
      have := hnn 1
      linarith
    · have h2u := thickness_segCarrierSetAt_le K T c hL (n := 2) (by norm_num)
      have h2l := le_thickness_segCarrierSetAt K T' c' hL (n := 2) (by norm_num)
      have := hnn 2
      linarith
  · have hz : Metric.thickness ℝ (segCarrierSetAt K T c L) n = 0 := by
      refine Metric.thickness_eq_zero_of_finrank_le (𝕜 := ℝ) ?_
      have h3 : Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by
        rw [← Module.finrank_eq_rank]; simp
      rw [h3]
      exact_mod_cast Nat.cast_le.2 hn
    rw [hz]
    have := Metric.thickness_nonneg (𝕜 := ℝ) (segCarrierSetAt K T' c' L) n
    linarith


/-! ### The volume price of the dilate -/


/-! ### The three R31 obligations at general dilation `K` -/

section Obligations

variable {cfg : VeryNotSticky.{u}} (core : BallDataCore cfg)


/-! ### Comparability and core-line containment -/


end Obligations

end Kakeya.VeryNotSticky

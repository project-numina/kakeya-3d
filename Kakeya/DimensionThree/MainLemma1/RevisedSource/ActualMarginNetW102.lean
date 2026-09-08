/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.GeneralLineEDAnalyticBridgeW95
public import Kakeya.Uniform.GridNet

/-!
# Scaled grid nets for the small-bin tree (W102)

Wraps `Tube.grid_net_tight` and `Tube.grid_overlap_tight` at radius `α · ρ`, a parameterized
fraction of a target parent radius `ρ`.  `exists_scaled_grid_net_w102` gives the covering,
separation and localization clauses of the net; `scaled_grid_node_rescale_w102` records that
`Tube.rescale` changes only the radius of a node; `scaled_grid_overlap_w102` is the same-radius
packing bound, and `scaled_grid_overlap_target_w102` the packing bound against a target
`ρ`-tube, with the packing base supplied by the caller (see `ActualMarginCpackW102`).
-/

@[expose] public section

open scoped NNReal

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped ENNReal NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

universe uE

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/- The existing tight packing proof is scale-parametric once both the net and
  the test tube have the same radius.  This wrapper keeps that fact explicit
  for the small-bin radius used by the prospective weighted selector. -/

/- Target-radius packing for a small-bin net.  The caller supplies the
   parameter-dependent packing base; this is the honest constant change needed
   when the target tube is wider than the net nodes. -/
theorem scaled_grid_overlap_target_w102
    {delta rho alpha : ℝ≥0} (hrho : 0 < rho)
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1)
    (G : Finset (Tube (alpha * rho) E))
    (hsep : ∀ a ∈ G, ∀ b ∈ G, a ≠ b ->
      (alpha * rho : ℝ) / 32 ≤ ‖a.x - b.x‖ + ‖a.y - b.y‖)
    (V : Tube rho E) (Cpack : Nat)
    (hCpack : (24 * (rho : ℝ) + ((alpha * rho : ℝ≥0) : ℝ) / 128) /
        (((alpha * rho : ℝ≥0) : ℝ) / 128) ≤
      (Cpack : ℝ) * Module.finrank ℝ E + 1) :
    (G.filter (fun W => ∃ (U : Tube delta E),
        U.carrier ⊆ Metric.closedBall (0 : E) 1 ∧
        U.toConvexSpaceBody ≤ (W.rescale rho).toConvexSpaceBody ∧
        U.toConvexSpaceBody ≤ V.toConvexSpaceBody)).card ≤
      2 * (Cpack * Module.finrank ℝ E + 1) ^
        (2 * Module.finrank ℝ E) := by
  classical
  set n : Nat := Module.finrank ℝ E with hn_def
  have hn_pos : 0 < n := Module.finrank_pos
  set r : ℝ := (rho : ℝ) with hr_def
  have hr_pos : 0 < r := by rw [hr_def]; exact_mod_cast hrho
  have hrα_pos : 0 < ((alpha * rho : ℝ≥0) : ℝ) := by
    exact_mod_cast mul_pos halpha hrho
  have hrα_le : ((alpha * rho : ℝ≥0) : ℝ) ≤ r := by
    rw [NNReal.coe_mul, hr_def]
    exact mul_le_of_le_one_left (by exact_mod_cast hrho.le) (by exact_mod_cast halpha1)
  set F := G.filter (fun W => ∃ (U : Tube delta E),
      U.carrier ⊆ Metric.closedBall (0 : E) 1 ∧
      U.toConvexSpaceBody ≤ (W.rescale rho).toConvexSpaceBody ∧
      U.toConvexSpaceBody ≤ V.toConvexSpaceBody) with hF
  have hFG : ∀ W ∈ F, W ∈ G := fun W hW => (Finset.mem_filter.mp hW).1
  have hsep_endpoints : ∀ W ∈ F, ∀ W' ∈ F, W ≠ W' →
      ((alpha * rho : ℝ≥0) : ℝ) / 32 ≤ ‖W.x - W'.x‖ + ‖W.y - W'.y‖ :=
    fun W hW W' hW' hne => hsep W (hFG W hW) W' (hFG W' hW') hne
  have hloc24 : ∀ W ∈ F,
      (‖W.x - V.x‖ ≤ 24 * r ∧ ‖W.y - V.y‖ ≤ 24 * r) ∨
      (‖W.x - V.y‖ ≤ 24 * r ∧ ‖W.y - V.x‖ ≤ 24 * r) := by
    intro W hW
    obtain ⟨_, U, _hU1, hUW, hUV⟩ := Finset.mem_filter.mp hW
    have hWr : W.toConvexSpaceBody ≤ (W.rescale rho).toConvexSpaceBody := by
      simpa only [Tube.toConvexSpaceBody_rescale_self] using
        (Tube.rescale_le_rescale_of_radius_le W hrα_le)
    have hW0 : W.toConvexSpaceBody ≤
        (U.rescale (4 * rho)).toConvexSpaceBody := by
      exact hWr.trans (Tube.rescale_le_of_le U (W.rescale rho) hUW)
    have hV0 : V.toConvexSpaceBody ≤
        (U.rescale (4 * rho)).toConvexSpaceBody :=
      Tube.rescale_le_of_le U V hUV
    have hWend := Tube.endpoints_close_of_body_le W
      (U.rescale (4 * rho)) hW0
    have hVend := Tube.endpoints_close_of_body_le V
      (U.rescale (4 * rho)) hV0
    have hVscale : ((4 * rho : ℝ≥0) : ℝ) = 4 * r := by
      rw [hr_def, NNReal.coe_mul]; norm_num
    simp only [Tube.rescale, Tube.mk'_x, Tube.mk'_y, hVscale] at hWend
    simp only [Tube.rescale, Tube.mk'_x, Tube.mk'_y, hVscale] at hVend
    ring_nf at hWend hVend
    rcases hWend with ⟨hWx, hWy⟩ | ⟨hWx, hWy⟩ <;>
      rcases hVend with ⟨hVx, hVy⟩ | ⟨hVx, hVy⟩
    · left; refine ⟨?_, ?_⟩
      · have ht := norm_sub_le_norm_sub_add_norm_sub W.x U.x V.x
        have hu : ‖U.x - V.x‖ ≤ 12 * r := by simpa [norm_sub_rev, mul_comm] using hVx
        have hw : ‖W.x - U.x‖ ≤ 12 * r := by simpa [mul_comm] using hWx
        linarith [ht, hw, hu]
      · have ht := norm_sub_le_norm_sub_add_norm_sub W.y U.y V.y
        have hu : ‖U.y - V.y‖ ≤ 12 * r := by simpa [norm_sub_rev, mul_comm] using hVy
        have hw : ‖W.y - U.y‖ ≤ 12 * r := by simpa [mul_comm] using hWy
        linarith [ht, hw, hu]
    · right; refine ⟨?_, ?_⟩
      · have ht := norm_sub_le_norm_sub_add_norm_sub W.x U.x V.y
        have hu : ‖U.x - V.y‖ ≤ 12 * r := by simpa [norm_sub_rev, mul_comm] using hVy
        have hw : ‖W.x - U.x‖ ≤ 12 * r := by simpa [mul_comm] using hWx
        linarith [ht, hw, hu]
      · have ht := norm_sub_le_norm_sub_add_norm_sub W.y U.y V.x
        have hu : ‖U.y - V.x‖ ≤ 12 * r := by simpa [norm_sub_rev, mul_comm] using hVx
        have hw : ‖W.y - U.y‖ ≤ 12 * r := by simpa [mul_comm] using hWy
        linarith [ht, hw, hu]
    · right; refine ⟨?_, ?_⟩
      · have ht := norm_sub_le_norm_sub_add_norm_sub W.x U.y V.y
        have hu : ‖U.y - V.y‖ ≤ 12 * r := by simpa [norm_sub_rev, mul_comm] using hVy
        have hw : ‖W.x - U.y‖ ≤ 12 * r := by simpa [mul_comm] using hWx
        linarith [ht, hw, hu]
      · have ht := norm_sub_le_norm_sub_add_norm_sub W.y U.x V.x
        have hu : ‖U.x - V.x‖ ≤ 12 * r := by simpa [norm_sub_rev, mul_comm] using hVx
        have hw : ‖W.y - U.x‖ ≤ 12 * r := by simpa [mul_comm] using hWy
        linarith [ht, hw, hu]
    · left; refine ⟨?_, ?_⟩
      · have ht := norm_sub_le_norm_sub_add_norm_sub W.x U.y V.x
        have hu : ‖U.y - V.x‖ ≤ 12 * r := by simpa [norm_sub_rev, mul_comm] using hVx
        have hw : ‖W.x - U.y‖ ≤ 12 * r := by simpa [mul_comm] using hWx
        linarith [ht, hw, hu]
      · have ht := norm_sub_le_norm_sub_add_norm_sub W.y U.x V.y
        have hu : ‖U.x - V.y‖ ≤ 12 * r := by simpa [norm_sub_rev, mul_comm] using hVy
        have hw : ‖W.y - U.x‖ ≤ 12 * r := by simpa [mul_comm] using hWy
        linarith [ht, hw, hu]
  set Fp : Finset (Tube (alpha * rho) E) :=
    F.filter (fun W => ‖W.x - V.x‖ ≤ 24 * r ∧ ‖W.y - V.y‖ ≤ 24 * r) with hFp
  set Fm : Finset (Tube (alpha * rho) E) := F \ Fp with hFm
  have hsep_pos : (0 : ℝ) < ((alpha * rho : ℝ≥0) : ℝ) / 32 := by positivity
  have hratio : (24 * r + (((alpha * rho : ℝ≥0) : ℝ) / 32) / 4) /
      ((((alpha * rho : ℝ≥0) : ℝ) / 32) / 4) ≤
      (Cpack : ℝ) * n + 1 := by
    convert hCpack using 1; ring
  have hpart_bound : ∀ (Gp : Finset (Tube (alpha * rho) E)) (cx cy : E),
      (∀ W ∈ Gp, W ∈ F) →
      (∀ W ∈ Gp, ‖W.x - cx‖ ≤ 24 * r) →
      (∀ W ∈ Gp, ‖W.y - cy‖ ≤ 24 * r) →
      Gp.card ≤ (Cpack * n + 1) ^ (2 * n) := by
    intro Gp cx cy hGF hGx hGy
    have hsepG : ∀ a ∈ Gp, ∀ b ∈ Gp, a ≠ b →
        ((alpha * rho : ℝ≥0) : ℝ) / 32 ≤ ‖a.x - b.x‖ + ‖a.y - b.y‖ :=
      fun a ha b hb hab => hsep_endpoints a (hGF a ha) b (hGF b hb) hab
    have hpack := Tube.card_le_of_L1_separated_in_box (E := E) Gp
      (fun W => W.x) (fun W => W.y) cx cy hsep_pos hsepG hGx hGy
    have hbase : 0 ≤ (24 * r + (((alpha * rho : ℝ≥0) : ℝ) / 32) / 4) /
        ((((alpha * rho : ℝ≥0) : ℝ) / 32) / 4) := by positivity
    have hmono := pow_le_pow_left₀ hbase hratio (2 * n)
    have hcardR : (Gp.card : ℝ) ≤ ((Cpack : ℝ) * n + 1) ^ (2 * n) :=
      le_trans hpack hmono
    exact_mod_cast hcardR
  have hFpF : ∀ W ∈ Fp, W ∈ F := fun W hW => (Finset.mem_filter.mp hW).1
  have hFpx : ∀ W ∈ Fp, ‖W.x - V.x‖ ≤ 24 * r :=
    fun W hW => (Finset.mem_filter.mp hW).2.1
  have hFpy : ∀ W ∈ Fp, ‖W.y - V.y‖ ≤ 24 * r :=
    fun W hW => (Finset.mem_filter.mp hW).2.2
  have hFp_card := hpart_bound Fp V.x V.y hFpF hFpx hFpy
  have hFmF : ∀ W ∈ Fm, W ∈ F := fun W hW => (Finset.mem_sdiff.mp hW).1
  have hFmx : ∀ W ∈ Fm, ‖W.x - V.y‖ ≤ 24 * r := by
    intro W hW
    obtain ⟨hWF, hWnp⟩ := Finset.mem_sdiff.mp hW
    rcases hloc24 W hWF with hpos | hneg
    · exact absurd (Finset.mem_filter.mpr ⟨hWF, hpos⟩) hWnp
    · exact hneg.1
  have hFmy : ∀ W ∈ Fm, ‖W.y - V.x‖ ≤ 24 * r := by
    intro W hW
    obtain ⟨hWF, hWnp⟩ := Finset.mem_sdiff.mp hW
    rcases hloc24 W hWF with hpos | hneg
    · exact absurd (Finset.mem_filter.mpr ⟨hWF, hpos⟩) hWnp
    · exact hneg.2
  have hFm_card := hpart_bound Fm V.y V.x hFmF hFmx hFmy
  have hFsplit : F.card ≤ Fp.card + Fm.card := by
    have hFeq : F.card = (Fp ∪ Fm).card := by
      congr 1
      rw [hFm, Finset.union_sdiff_of_subset (Finset.filter_subset _ _)]
    rw [hFeq]; exact Finset.card_union_le _ _
  change F.card ≤ 2 * (Cpack * n + 1) ^ (2 * n)
  calc F.card ≤ Fp.card + Fm.card := hFsplit
    _ ≤ (Cpack * n + 1) ^ (2 * n) + (Cpack * n + 1) ^ (2 * n) :=
      Nat.add_le_add hFp_card hFm_card
    _ = 2 * (Cpack * n + 1) ^ (2 * n) := by ring

end
end Kakeya.ml1Boot.TrialRestartW94

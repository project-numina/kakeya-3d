/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.AxisFootNormalizationGeometryW103
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.GeneralLineEDAnalyticBridgeW95
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.TrialGeometryEntryW96
public import Kakeya.ConvexBody.Counting

/-!
# Line essential distinctness under the axis-foot normalization (W103)

Shows that `lineEssentiallyDistinctW94` is preserved, up to a fixed amplification, by the
axis-foot normalization `axisFootTubeW103` of `AxisFootNormalizationGeometryW103`.
`axisFoot_line_pullback_w103` pulls a line neighbourhood of a normalized tube back to a line
neighbourhood of the original tube at radius `12 R K r`; `line_aperture_card_w103` bounds the
number of family members near a given line by `lineAmplificationBoundW95 * C` using the
radius-five line bins of `GeneralLineEDAnalyticBridgeW95`; and
`axisFoot_family_lineED_w103` concludes line essential distinctness of the normalized family
with constant `lineAmplificationBoundW95 3 1 5 * lineAmplificationBoundW95 3 2 (60 R) * C`.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped ENNReal NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
attribute [local instance] Classical.propDecidable

universe uE uI

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

theorem axisFoot_line_pullback_w103 {r theta R : ℝ≥0} (hr : 0 < r)
    (hrt : r <= theta) (ht1 : theta <= 1) (hR : 0 < R)
    (top : Tube theta E) (T : Tube r E) (hT : T.toConvexSpaceBody <= top.toConvexSpaceBody)
    (L : E ≃ᵃ[ℝ] E) (hL : L.toAffineMap = top.rescaleMap (R : ℝ))
    (K : ℝ) (hK : 0 <= K) (x : E)
    (hx : ∃ t : ℝ, dist (L x) ((axisFootTubeW103 (r / theta) L T).center +
      t • (axisFootTubeW103 (r / theta) L T).direction) <= K * ((r / theta : ℝ≥0) : ℝ)) :
    x ∈ VeryNotSticky.lineNbhd T.center T.direction ((12 * (R : ℝ) * K) * r) := by
  let W := axisFootTubeW103 (r / theta) L T
  let v := L.linear T.direction
  let u := W.direction
  have hv : ‖v‖ ≠ 0 := by
    apply norm_ne_zero_iff.mpr
    intro h
    have hz : T.direction = 0 := L.linear.injective (h.trans (map_zero L.linear).symm)
    have := T.norm_direction
    rw [hz, norm_zero] at this
    norm_num at this
  obtain ⟨t, hdist⟩ := hx
  let a : ℝ := inner ℝ (L T.center) u
  let b : ℝ := (t - a) / ‖v‖
  let z : E := T.center + b • T.direction
  have hLz : L z = W.center + t • u := by
    rw [show W.center = L T.center - a • u from axisFootTube_center_w103 L T]
    have hz : L z = L T.center + b • v := by
      dsimp only [z, v]
      rw [add_comm T.center, show L (b • T.direction + T.center) =
        L.linear (b • T.direction) + L T.center from L.map_vadd T.center (b • T.direction),
        map_smul, add_comm]
    rw [hz, show u = ‖v‖⁻¹ • v from axisFootTube_direction_w103 L T]
    dsimp [b]
    module
  have huv : top.rescaleMap (R : ℝ) (z + (x - z)) =
      top.rescaleMap (R : ℝ) z + (L x - L z) := by
    have hxeq : L x = top.rescaleMap (R : ℝ) x := congrArg (fun f : E →ᵃ[ℝ] E => f x) hL
    have hzeq : L z = top.rescaleMap (R : ℝ) z := congrArg (fun f : E →ᵃ[ℝ] E => f z) hL
    rw [add_sub_cancel, hxeq, hzeq]
    abel
  have hnear : ‖L x - L z‖ <= K * ((r / theta : ℝ≥0) : ℝ) := by
    rw [hLz, ← dist_eq_norm]
    exact hdist
  have hperp : ‖T.direction - inner ℝ top.direction T.direction • top.direction‖ <=
      2 * (theta : ℝ) := Tube.perp_norm_direction_le_of_subset top T hT
  have hbound := (Tube.norm_rescale_symm_vector_le (hr.trans_le hrt) ht1
    (show (0 : ℝ) < R from hR) top T (by norm_num : (0 : ℝ) <= 2)
    (by positivity : (0 : ℝ) <= K * ((r / theta : ℝ≥0) : ℝ)) hperp huv hnear).2
  apply VeryNotSticky.mem_lineNbhd_of_dist_le (b + inner ℝ T.direction (x - z))
  have heq : x - (T.center + (b + inner ℝ T.direction (x - z)) • T.direction) =
      (x - z) - inner ℝ T.direction (x - z) • T.direction := by
    dsimp [z]
    module
  rw [dist_eq_norm, heq]
  convert hbound using 1
  rw [NNReal.coe_div]
  have htne : (theta : ℝ) ≠ 0 := (show (0 : ℝ) < theta from hr.trans_le hrt).ne'
  field_simp [htne]
  ring

theorem line_aperture_card_w103 {iota : Type uI} {r : ℝ≥0} (hr : 0 < r) (hr1 : r <= 1)
    (F : Finset iota) (T : iota -> Tube r E) (C : ℝ≥0)
    (hline : lineEssentiallyDistinctW94 F T C)
    (B K : ℝ) (hB : 0 <= B) (hK : 1 <= K)
    (hcenter : ∀ i ∈ F, ‖(T i).center‖ <= B) (o v : E) (hv : ‖v‖ = 1) :
    ((nearLineFamilyW95 F T o v K).card : ℝ≥0) <=
      (lineAmplificationBoundW95 (Module.finrank ℝ E) B K : ℝ≥0) * C := by
  obtain ⟨G, assign, hG, hGcard, hassign, hcover⟩ :=
    exists_radius_five_line_bins_w95 hr hr1 F T B K hB hK hcenter o v hv
  let fibres := fun k => F.filter (fun i => liesInFiveDeltaLineTubeW94 (T i) (T k).center (T k).direction)
  have hfibres : ∀ k, ((fibres k).card : ℝ≥0) <= C := fun k =>
    hline (T k).center (T k).direction (T k).norm_direction
  have hcovered : nearLineFamilyW95 F T o v K ⊆ G.biUnion fibres := by
    intro i hi
    refine Finset.mem_biUnion.mpr ⟨assign i, hassign i hi, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1, ?_⟩⟩
    exact (pointwise_line_neighbourhood_iff_w95 (T i) (T (assign i)).center
      (T (assign i)).direction (T (assign i)).norm_direction).mpr (hcover i hi)
  calc
    ((nearLineFamilyW95 F T o v K).card : ℝ≥0) <= ((G.biUnion fibres).card : ℝ≥0) := by
      exact_mod_cast Finset.card_le_card hcovered
    _ <= ∑ k ∈ G, ((fibres k).card : ℝ≥0) := by exact_mod_cast Finset.card_biUnion_le
    _ <= ∑ _k ∈ G, C := Finset.sum_le_sum (fun k hk => hfibres k)
    _ = (G.card : ℝ≥0) * C := by rw [Finset.sum_const, nsmul_eq_mul]
    _ <= (lineAmplificationBoundW95 (Module.finrank ℝ E) B K : ℝ≥0) * C := by
      apply mul_le_mul_left
      exact_mod_cast hGcard

theorem axisFoot_family_lineED_w103 {iota : Type uI} {r theta R : ℝ≥0}
    (hr : 0 < r) (hrt : r <= theta) (ht1 : theta <= 1) (hR : 1 <= R)
    (hRn : Tube.normalization.C (Module.finrank ℝ E) <= R)
    (top : Tube theta E) (F : Finset iota) (T : iota -> Tube r E)
    (hT : ∀ i ∈ F, (T i).toConvexSpaceBody <= top.toConvexSpaceBody)
    (hcenter : ∀ i ∈ F, ‖(T i).center‖ <= 2)
    (C : ℝ≥0) (hline : lineEssentiallyDistinctW94 F T C)
    (L : E ≃ᵃ[ℝ] E) (hL : L.toAffineMap = top.rescaleMap (R : ℝ)) :
    lineEssentiallyDistinctW94 F (fun i => axisFootTubeW103 (r / theta) L (T i))
      ((lineAmplificationBoundW95 (Module.finrank ℝ E) 1 5 : ℝ≥0) *
        (lineAmplificationBoundW95 (Module.finrank ℝ E) 2 (60 * (R : ℝ)) : ℝ≥0) * C) := by
  let W := fun i => axisFootTubeW103 (r / theta) L (T i)
  let Cold : ℝ≥0 := (lineAmplificationBoundW95 (Module.finrank ℝ E) 2 (60 * (R : ℝ)) : ℝ≥0) * C
  have hd : 0 < r / theta := div_pos hr (hr.trans_le hrt)
  have hd1 : r / theta <= 1 := (div_le_one (hr.trans_le hrt)).mpr hrt
  have hWcenter : ∀ i ∈ F, ‖(W i).center‖ <= 1 := by
    intro i hi
    exact (axisFootTube_image_w103 hr hrt ht1 hR hRn top (T i) (hT i hi) L hL).2.trans (by norm_num)
  intro o v hv
  let H := F.filter (fun i => liesInFiveDeltaLineTubeW94 (W i) o v)
  have hHnear : H = nearLineFamilyW95 F W o v 5 := by
    apply Finset.filter_congr
    intro i hi
    exact pointwise_line_neighbourhood_iff_w95 (W i) o v hv
  obtain ⟨G, assign, hG, hGcard, hassign, hcover⟩ :=
    exists_radius_five_line_bins_w95 hd hd1 F W 1 5 (by norm_num) (by norm_num) hWcenter o v hv
  let fibres := fun j => nearLineFamilyW95 F T (T j).center (T j).direction (60 * (R : ℝ))
  have hK : (1 : ℝ) <= 60 * R := by have hh : (1 : ℝ) <= R := hR; nlinarith
  have hfibres : ∀ j, ((fibres j).card : ℝ≥0) <= Cold := fun j =>
    line_aperture_card_w103 hr (hrt.trans ht1) F T C hline 2 (60 * (R : ℝ))
      (by norm_num) hK hcenter (T j).center (T j).direction (T j).norm_direction
  have hcovered : H ⊆ G.biUnion fibres := by
    intro i hi
    have hni : i ∈ nearLineFamilyW95 F W o v 5 := hHnear ▸ hi
    have hiF : i ∈ F := (Finset.mem_filter.mp hi).1
    let j := assign i
    have hjG : j ∈ G := hassign i hni
    have hjF : j ∈ F := (Finset.mem_filter.mp (hG hjG)).1
    refine Finset.mem_biUnion.mpr ⟨j, hjG, Finset.mem_filter.mpr ⟨hiF, ?_⟩⟩
    intro x hx
    have hWi := (axisFootTube_image_w103 hr hrt ht1 hR hRn top (T i) (hT i hiF) L hL).1
      ⟨x, hx, rfl⟩
    have hlineij := (pointwise_line_neighbourhood_iff_w95 (W i) (W j).center (W j).direction
      (W j).norm_direction).mpr (hcover i hni)
    have hh := axisFoot_line_pullback_w103 hr hrt ht1 (zero_lt_one.trans_le hR)
      top (T j) (hT j hjF) L hL 5 (by norm_num) x (hlineij (L x) hWi)
    convert hh using 1; ring
  calc
    (H.card : ℝ≥0) <= ((G.biUnion fibres).card : ℝ≥0) := by exact_mod_cast Finset.card_le_card hcovered
    _ <= ∑ j ∈ G, ((fibres j).card : ℝ≥0) := by exact_mod_cast Finset.card_biUnion_le
    _ <= ∑ _j ∈ G, Cold := Finset.sum_le_sum (fun j hj => hfibres j)
    _ = (G.card : ℝ≥0) * Cold := by rw [Finset.sum_const, nsmul_eq_mul]
    _ <= (lineAmplificationBoundW95 (Module.finrank ℝ E) 1 5 : ℝ≥0) * Cold := by
      apply mul_le_mul_left
      exact_mod_cast hGcard
    _ = _ := by dsimp [Cold]; ring

end

end Kakeya.ml1Boot.TrialRestartW94

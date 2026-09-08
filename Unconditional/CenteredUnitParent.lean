/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Unconditional.CenteredCoarseIncidence
import Kakeya.DimensionThree.MainLemma2.CanonicalCentredCover

/-!
# Centered Unit Parent

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

open MeasureTheory

namespace KakeyaLink.DirectCenteredRoute

open Kakeya Kakeya.ml1Boot.TrialRestartW94

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

omit [Nontrivial E] in
theorem centered_dilate_le_unit_parent
    {rho : NNReal} (U V : _root_.Tube rho E)
    (hU : U.IsCentred) (hV : V.IsCentred) (hmid : ‖U.midpoint‖ ≤ (3 / 4 : Real))
    (hcontain : U.carrier ⊆ (Kakeya.Tube.dilate V 128).carrier) :
    U.toConvexSpaceBody ≤ (V.rescale (1024 * rho)).toConvexSpaceBody := by
  have hline : U.carrier ⊆ Metric.cthickening (128 * (rho : Real))
      (Set.range (fun t : Real => V.center + t • V.direction)) := by
    have h := hcontain.trans (dilate_carrier_subset_axis_neighborhood V (by norm_num : (0 : Real) < 128))
    simpa only [VeryNotSticky.lineNbhd_eq_cthickening_range] using h
  obtain ⟨s, hs, hdirection, hmidpoint⟩ :=
    _root_.Tube.params_close_of_carrier_subset_line U hU hmid V.norm_direction
      (by norm_num : (1 : Real) ≤ 128) hline
  have hcenter : V.center = V.midpoint := by
    simp only [_root_.Tube.center, _root_.Tube.midpoint, midpoint_eq_smul_add]
    norm_num
  have hfoot : _root_.Tube.lineFoot V.center V.direction = V.midpoint := by
    unfold _root_.Tube.lineFoot
    rw [hcenter, hV, zero_smul, sub_zero]
  rw [hfoot] at hmidpoint
  have hrescaleMid : (V.rescale (1024 * rho)).midpoint = V.midpoint := by
    simp only [_root_.Tube.rescale, _root_.Tube.midpoint, _root_.Tube.mk'_x, _root_.Tube.mk'_y]
  have hrescaleDir : (V.rescale (1024 * rho)).direction = V.direction := by
    simp only [_root_.Tube.rescale, _root_.Tube.direction, _root_.Tube.mk'_x, _root_.Tube.mk'_y]
  rcases hs with rfl | rfl
  · apply _root_.Tube.tube_le_rescale_of_close U V hmidpoint
      (by simpa only [one_smul] using hdirection)
    simp only [NNReal.coe_mul, NNReal.coe_ofNat]
    nlinarith [rho.coe_nonneg]
  · change U.toConvexSpaceBody ≤ ((V.rescale (1024 * rho)).reverse).toConvexSpaceBody
    apply _root_.Tube.le_of_params_close U ((V.rescale (1024 * rho)).reverse)
      (by simpa only [_root_.Tube.reverse_midpoint, hrescaleMid] using hmidpoint)
      (by simpa only [_root_.Tube.reverse_direction, hrescaleDir, neg_one_smul] using hdirection)
    simp only [NNReal.coe_mul, NNReal.coe_ofNat]
    nlinarith [rho.coe_nonneg]

theorem centered_common_leaf_le_unit_parent
    {originalDelta fineDelta rho : NNReal}
    (hrho1 : rho ≤ 1) (hscale : fineDelta ≤ rho)
    (original : _root_.Tube originalDelta E) (fine : _root_.Tube fineDelta E)
    (coarse : _root_.Tube rho E)
    (hfineCenter : fine.IsCentred) (hcoarseCenter : coarse.IsCentred)
    (hfineMid : ‖fine.midpoint‖ ≤ (3 / 4 : Real))
    (hfine : (fun x : E => (1 / 8 : Real) • x) '' original.carrier ⊆ fine.carrier)
    (hcoarse : (fun x : E => (1 / 8 : Real) • x) '' original.carrier ⊆ coarse.carrier) :
    fine.toConvexSpaceBody ≤ (coarse.rescale (1024 * rho)).toConvexSpaceBody := by
  have hcontain := homothetic_common_leaf_subset_dilate
    (show (rho : Real) ≤ 1 from hrho1) le_rfl original coarse (fine.rescale rho)
    hcoarse (hfine.trans (fine.le_rescale hscale))
  have hcenterFine : (fine.rescale rho).IsCentred := by
    simpa only [_root_.Tube.IsCentred, _root_.Tube.rescale, _root_.Tube.midpoint,
      _root_.Tube.direction, _root_.Tube.mk'_x, _root_.Tube.mk'_y] using hfineCenter
  have hcenterCoarse : (coarse.rescale rho).IsCentred := by
    simpa only [_root_.Tube.IsCentred, _root_.Tube.rescale, _root_.Tube.midpoint,
      _root_.Tube.direction, _root_.Tube.mk'_x, _root_.Tube.mk'_y] using hcoarseCenter
  have hmid : ‖(fine.rescale rho).midpoint‖ ≤ (3 / 4 : Real) := by
    simpa only [_root_.Tube.rescale, _root_.Tube.midpoint,
      _root_.Tube.mk'_x, _root_.Tube.mk'_y] using hfineMid
  have h := centered_dilate_le_unit_parent (fine.rescale rho) (coarse.rescale rho)
    hcenterFine hcenterCoarse hmid hcontain
  exact (show fine.toConvexSpaceBody ≤ (fine.rescale rho).toConvexSpaceBody from
    fine.le_rescale hscale).trans h

def unitParentVolumeCost (n : Nat) : ENNReal :=
  (_root_.Tube.volume_le.C n : ENNReal) / (_root_.Tube.le_volume.c n : ENNReal) *
    (1024 : ENNReal) ^ (n - 1)


theorem unitParentVolumeCost_ne_top (n : Nat) : unitParentVolumeCost n ≠ ⊤ := by
  unfold unitParentVolumeCost
  have hc : (_root_.Tube.le_volume.c n : ENNReal) ≠ 0 := by
    exact_mod_cast (_root_.Tube.le_volume.c_pos n).ne'
  exact ENNReal.mul_ne_top (ENNReal.div_ne_top ENNReal.coe_ne_top hc) (by finiteness)

theorem unit_parent_volume_le
    {rho : NNReal} (hsmall : 1024 * rho ≤ 1) (T : _root_.Tube rho E) :
    volume (T.rescale (1024 * rho)).carrier ≤
      unitParentVolumeCost (Module.finrank Real E) * volume T.carrier := by
  let n := Module.finrank Real E
  have hc : (_root_.Tube.le_volume.c n : ENNReal) ≠ 0 := by
    exact_mod_cast (_root_.Tube.le_volume.c_pos n).ne'
  calc
    volume (T.rescale (1024 * rho)).carrier ≤
        (_root_.Tube.volume_le.C n : ENNReal) *
          (1024 : ENNReal) ^ (n - 1) * (rho : ENNReal) ^ (n - 1) := by
      simpa only [n, ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_ofNat,
        mul_pow, mul_assoc] using (T.rescale (1024 * rho)).volume_le hsmall
    _ = unitParentVolumeCost n *
        ((_root_.Tube.le_volume.c n : ENNReal) * (rho : ENNReal) ^ (n - 1)) := by
      unfold unitParentVolumeCost
      calc
        _ = ((_root_.Tube.volume_le.C n : ENNReal) /
            (_root_.Tube.le_volume.c n : ENNReal) * (_root_.Tube.le_volume.c n : ENNReal)) *
            ((1024 : ENNReal) ^ (n - 1) * (rho : ENNReal) ^ (n - 1)) := by
          rw [ENNReal.div_mul_cancel hc ENNReal.coe_ne_top]
          ring
        _ = _ := by ring
    _ ≤ _ := mul_le_mul' le_rfl T.le_volume


end KakeyaLink.DirectCenteredRoute

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceCentringReductionProofW102

/-!
# Density and Frostman bounds for the centred image of a subfamily

Two consequences of the `1/8`-homothety centring of `CentringShadingW102` and the volume bound
`half_radius_carrier_volume_w102`, stated for an arbitrary nonempty subfamily `b` whose parent
representatives may lie outside `b`.
`Kakeya.ml1Boot.TrialRestartW94.centred_image_maxDensity_w103` bounds `maxDensity` of the
parent image by `384` times that of `b`, and
`Kakeya.ml1Boot.TrialRestartW94.centred_image_frostman_w103` bounds the unit-ball Frostman
constant of the parent image by `196608 * B` times that of `b`, where `B` bounds the complete
fibre cardinalities of `parent` over `b`.  The Frostman bound is consumed by the revised
original entry `RevisedOriginalEntryW111`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ConvexSpaceBody ShadedBody

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

universe uE uI

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

/-- The centred image of any nonempty original subfamily retains its maximal
density bound, even when the chosen parent representatives lie outside it. -/
theorem centred_image_maxDensity_w103
    (hdim : Module.finrank ℝ E = 3)
    {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}
    (hdsmall : delta <= 1 / 200)
    (b : Finset iota) (hb : b.Nonempty) (Y : iota -> Tube delta E)
    (parent : iota -> iota) (Z : iota -> Tube (delta / 2) E)
    (hcover : ∀ i ∈ b,
      (fun x : E => (1 / 8 : ℝ) • x) '' (Y i).carrier ⊆ (Z (parent i)).carrier) :
    maxDensity (b.image parent) (fun j => (Z j).toConvexSpaceBody) <=
      384 * maxDensity b (fun i => (Y i).toConvexSpaceBody) := by
  obtain ⟨i0, hi0⟩ := hb
  let N : iota -> ConvexSpaceBody E := fun i =>
    (Y i).toConvexSpaceBody.homothety 0 (1 / 8 : ℝ)
  have hNcar : ∀ i, (N i).carrier =
      (fun x : E => (1 / 8 : ℝ) • x) '' (Y i).carrier := by
    intro i
    change AffineMap.homothety (0 : E) (1 / 8 : ℝ) '' (Y i).carrier = _
    apply Set.image_congr
    intro x hx
    simp [AffineMap.homothety_apply]
  have hNvol : ∀ i, volume (N i).carrier =
      (1 / 512 : ℝ≥0∞) * volume (Y i).carrier := by
    intro i
    rw [hNcar, volume_source_centring_image_w102 hdim]
  have hvol : volume (Z (parent i0)).carrier <= 384 * volume (N i0).carrier := by
    rw [hNvol, ← mul_assoc]
    exact half_radius_carrier_volume_w102 hdim hdsmall (Y i0) (Z (parent i0))
  have hsumN (H : Finset iota) :
      (∑ i ∈ H, volume (N i).carrier) = (H.card : ℝ≥0∞) * volume (N i0).carrier := by
    simp_rw [hNvol]
    rw [← Finset.mul_sum, Tube.sum_volume_carrier_eq_card_mul Y (Y i0) H]
    ring
  refine Kakeya.maxDensity_le_of_forall_sum_le ?_
  intro K
  let Q := (b.image parent).filter (fun j => (Z j).toConvexSpaceBody <= K)
  let H := b.filter (fun i => N i <= K)
  have hsub : Q ⊆ H.image parent := by
    intro j hj
    obtain ⟨hjim, hjK⟩ := Finset.mem_filter.mp hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hjim
    refine Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, ?_⟩, rfl⟩
    rw [← SetLike.coe_subset_coe] at hjK ⊢
    change (N i).carrier ⊆ K.carrier
    rw [hNcar]
    exact (hcover i hi).trans hjK
  have hcard : Q.card <= H.card :=
    (Finset.card_le_card hsub).trans (Finset.card_image_le)
  change (∑ j ∈ Q, volume (Z j).carrier) <= _
  calc
    _ = (Q.card : ℝ≥0∞) * volume (Z (parent i0)).carrier :=
      Tube.sum_volume_carrier_eq_card_mul Z (Z (parent i0)) Q
    _ <= (H.card : ℝ≥0∞) * (384 * volume (N i0).carrier) :=
      mul_le_mul' (by exact_mod_cast hcard) hvol
    _ = 384 * (∑ i ∈ H, volume (N i).carrier) := by rw [hsumN]; ring
    _ <= 384 * (maxDensity b N * volume K.carrier) :=
      mul_le_mul' le_rfl (Kakeya.sum_volume_le_maxDensity_mul_volume b N K)
    _ = _ := by
      rw [show maxDensity b N = maxDensity b (fun i => (Y i).toConvexSpaceBody) from
        Kakeya.maxDensity_homothety b _ 0 (by norm_num), mul_assoc]

theorem centred_image_frostman_w103
    (hdim : Module.finrank ℝ E = 3)
    {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}
    (hdsmall : delta <= 1 / 200)
    (b : Finset iota) (hb : b.Nonempty) (Y : iota -> Tube delta E)
    (parent : iota -> iota) (Z : iota -> Tube (delta / 2) E)
    (B : ℝ≥0)
    (hY : ∀ i ∈ b, (Y i).carrier ⊆ Metric.closedBall 0 1)
    (hZ : ∀ j ∈ b.image parent, (Z j).carrier ⊆ Metric.closedBall 0 1)
    (hcover : ∀ i ∈ b,
      (fun x : E => (1 / 8 : ℝ) • x) '' (Y i).carrier ⊆ (Z (parent i)).carrier)
    (hfibres : ∀ j ∈ b.image parent, ((completeFibreW94 b parent j).card : ℝ≥0) <= B) :
    ConvexSpaceBody.frostmanConstant (b.image parent) (fun j => (Z j).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall <=
      (196608 : ℝ≥0∞) * (B : ℝ≥0∞) *
        ConvexSpaceBody.frostmanConstant b (fun i => (Y i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall := by
  obtain ⟨i0, hi0⟩ := hb
  have hmap : ∀ i ∈ b, parent i ∈ b.image parent :=
    fun i hi => Finset.mem_image_of_mem _ hi
  have hcard : (b.card : ℝ≥0∞) <= (B : ℝ≥0∞) * ((b.image parent).card : ℝ≥0∞) := by
    calc
      _ = ∑ j ∈ b.image parent, ((completeFibreW94 b parent j).card : ℝ≥0∞) := by
        simpa only [completeFibreW94, Finset.sum_const, nsmul_eq_mul, mul_one] using
          (Finset.sum_fiberwise_of_maps_to hmap (fun _ => (1 : ℝ≥0∞))).symm
      _ <= ∑ j ∈ b.image parent, (B : ℝ≥0∞) := by
        apply Finset.sum_le_sum
        intro j hj
        exact_mod_cast hfibres j hj
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hvolume : (1 / 512 : ℝ≥0∞) * volume (Y i0).carrier <= volume (Z (parent i0)).carrier := by
    rw [← volume_source_centring_image_w102 hdim]
    exact measure_mono (hcover i0 hi0)
  have hsum : (1 / 512 : ℝ≥0∞) * (∑ i ∈ b, volume (Y i).carrier) <=
      (B : ℝ≥0∞) * (∑ j ∈ b.image parent, volume (Z j).carrier) := by
    rw [Tube.sum_volume_carrier_eq_card_mul Y (Y i0) b,
      Tube.sum_volume_carrier_eq_card_mul Z (Z (parent i0)) (b.image parent)]
    calc
      _ <= (1 / 512 : ℝ≥0∞) *
          (((B : ℝ≥0∞) * ((b.image parent).card : ℝ≥0∞)) * volume (Y i0).carrier) :=
        mul_le_mul' le_rfl (mul_le_mul' hcard le_rfl)
      _ = (B : ℝ≥0∞) * (((b.image parent).card : ℝ≥0∞) *
          ((1 / 512 : ℝ≥0∞) * volume (Y i0).carrier)) := by ring
      _ <= _ := mul_le_mul' le_rfl (mul_le_mul' le_rfl hvolume)
  have hsum' : (∑ i ∈ b, volume (Y i).carrier) <=
      ((512 : ℝ≥0∞) * (B : ℝ≥0∞)) * (∑ j ∈ b.image parent, volume (Z j).carrier) := by
    have h := mul_le_mul' (le_refl (512 : ℝ≥0∞)) hsum
    have h512 : (512 : ℝ≥0∞) * (1 / 512 : ℝ≥0∞) = 1 := by
      rw [one_div]
      exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
    rw [← mul_assoc, h512, one_mul, ← mul_assoc] at h
    exact h
  have hYbody : ∀ i ∈ b, (Y i).toConvexSpaceBody <= ConvexSpaceBody.closedUnitBall := hY
  have hZbody : ∀ j ∈ b.image parent, (Z j).toConvexSpaceBody <= ConvexSpaceBody.closedUnitBall := hZ
  have hanchor : densityIn b (fun i => (Y i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall <=
      ((512 : ℝ≥0∞) * (B : ℝ≥0∞)) *
        densityIn (b.image parent) (fun j => (Z j).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall := by
    simp only [densityIn, Finset.filter_eq_self.mpr hYbody, Finset.filter_eq_self.mpr hZbody]
    rw [← mul_div_assoc]
    exact ENNReal.div_le_div_right hsum' _
  have hold := isFrostmanIn_frostmanConstant.maxDensity_le_of_carrier_subset hYbody
  apply ConvexSpaceBody.frostmanConstant_le_of_isFrostmanIn
  apply IsFrostmanIn.of_maxDensity_le
  calc
    _ <= 384 * maxDensity b (fun i => (Y i).toConvexSpaceBody) :=
      centred_image_maxDensity_w103 hdim hdsmall b ⟨i0, hi0⟩ Y parent Z hcover
    _ <= 384 * (ConvexSpaceBody.frostmanConstant b (fun i => (Y i).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall *
          densityIn b (fun i => (Y i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall) :=
      mul_le_mul' le_rfl hold
    _ <= 384 * (ConvexSpaceBody.frostmanConstant b (fun i => (Y i).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall * (((512 : ℝ≥0∞) * (B : ℝ≥0∞)) *
          densityIn (b.image parent) (fun j => (Z j).toConvexSpaceBody)
            ConvexSpaceBody.closedUnitBall)) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl hanchor)
    _ = _ := by ring

end
end Kakeya.ml1Boot.TrialRestartW94

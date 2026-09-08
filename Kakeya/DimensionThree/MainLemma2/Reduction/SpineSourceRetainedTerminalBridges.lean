/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceParentIndependent
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceZeroDefectData
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceQSelectedMiddle

/-!
# Bridges from the parent data to the zero-defect terminal interfaces

Field-by-field projections `source_parent_to_zero_window_schedule`,
`source_parent_to_zero_retained_state`, `source_actual_parent_to_zero_floor`,
`source_parent_to_zero_measured_failure` and `source_parent_to_zero_eccentric_factors` map
the `SourceParent*` structures to their `SourceZero*` counterparts.
`source_exists_retained_outer_density` bounds the level-`a` maximal density by
`delta ^ (-2 * eta J)` under `SourceParentUpperWindow`, paying the root-cover and window
constants before `a`, `b` are chosen. `ML2Assembly.sourceQ_retained_middle_original_bounds`
restates the R4 density rows from the genuine retained upper window.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

open ML2Assembly

universe u

variable {iota : Type u} {delta : ℝ≥0} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace ℝ (Fin 3))} {M C : Nat}

/-- Actual global density, including the occupied a=0 root family. All fixed
root-cover and window constants are paid before the runtime a,b are chosen. -/
theorem source_exists_retained_outer_density
    (N M J A0 A1 C : Nat) (hM : 2 <= M)
    (_hC : 1 <= C) (_hA0 : 1 <= A0) (_hA1 : 1 <= A1)
    (eta : Nat -> ℝ) (e : ℝ) (heta : 0 < eta J) :
    ∀ᶠ delta : ℝ≥0 in 𝓝[>] 0,
      forall {iota : Type u} (S : Finset iota)
        (T : iota -> Tube delta (EuclideanSpace ℝ (Fin 3)))
        (Q : SourceThreadedTower S T M C), SourceTowerGeometry Q A0 A1 ->
      forall a b : Nat, SourceParentUpperWindow Q A0 A1 N eta e a b J ->
      Kakeya.maxDensity (Q.indexSet a) (fun i => (Q.tube a i).toConvexSpaceBody) <=
        (delta : ℝ≥0∞) ^ (-2 * eta J) := by
  classical
  let D : Nat := sourceTowerWindowConstant C A0 A1
  let K : ℝ≥0 := 1280 ^ 6 * (D : ℝ≥0) ^ N
  have hD : 1 <= D := by
    dsimp [D, sourceTowerWindowConstant]
    omega
  have hDN : (1 : ℝ≥0∞) <= (D : ℝ≥0∞) ^ N := by
    exact one_le_pow₀ (by exact_mod_cast hD)
  filter_upwards [source_eventually_fixed_tower_radius_conditions M hM (by norm_num : (0 : ℝ) < 1),
    Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg
      (ENNReal.coe_ne_top (r := K)) heta,
    Ioo_mem_nhdsGT (by norm_num : (0 : ℝ≥0) < 1)] with delta ht hK hd
  intro iota S T Q hgeometry a b hwindow
  have hM0 : 0 < M := by omega
  have hroot : sourceTowerRadius delta M 0 = (1 / 40 : ℝ≥0) := by
    simp [sourceTowerRadius, hM0]
  have hrootcard : ((Q.indexSet 0).card : ℝ≥0∞) <= (1280 : ℝ≥0∞) ^ 6 := by
    have hh := hgeometry.coarse_card 0 hM0
    rw [hroot] at hh
    norm_num at hh
    exact_mod_cast hh
  have hδ1 : (delta : ℝ≥0∞) <= 1 := by exact_mod_cast hd.2.le
  have hone : (1 : ℝ≥0∞) <= (delta : ℝ≥0∞) ^ (-eta J) := by
    simpa using ENNReal.rpow_le_rpow_of_exponent_ge hδ1 (neg_nonpos.mpr heta.le)
  have hbound : Kakeya.maxDensity (Q.indexSet a)
      (fun i => (Q.tube a i).toConvexSpaceBody) <= (K : ℝ≥0∞) *
        (delta : ℝ≥0∞) ^ (-eta J) := by
    by_cases ha : a = 0
    · subst a
      refine (Kakeya.maxDensity_le_card _ _).trans (hrootcard.trans ?_)
      calc
        (1280 : ℝ≥0∞) ^ 6 <= (1280 : ℝ≥0∞) ^ 6 * (D : ℝ≥0∞) ^ N :=
          le_mul_of_one_le_right' hDN
        _ <= (K : ℝ≥0∞) * (delta : ℝ≥0∞) ^ (-eta J) := by
          simpa [K] using le_mul_of_one_le_right' (a := (K : ℝ≥0∞)) hone
    · have haM : a < M := hwindow.coarse_lt_fine.trans_le hwindow.fine_bound
      have haradius : (delta : ℝ) <= (sourceTowerRadius delta M a : ℝ) := by
        have hh := ht.2.2.2.2.1 a haM
        exact_mod_cast (show delta <= sourceTowerRadius delta M a by nlinarith)
      have hratio : (sourceTowerRadius delta M 0 : ℝ) /
          (sourceTowerRadius delta M a : ℝ) <= (delta : ℝ)⁻¹ := by
        rw [hroot]
        have hδ : (0 : ℝ) < delta := by exact_mod_cast hd.1
        norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
        calc (1 / 40 : ℝ) / (sourceTowerRadius delta M a : ℝ) <=
            1 / (sourceTowerRadius delta M a : ℝ) := by gcongr; norm_num
          _ <= (delta : ℝ)⁻¹ := by simpa [one_div] using one_div_le_one_div_of_le hδ haradius
      have hpow : ENNReal.ofReal
          (((sourceTowerRadius delta M 0 : ℝ) / (sourceTowerRadius delta M a : ℝ)) ^ eta J) <=
          (delta : ℝ≥0∞) ^ (-eta J) := by
        have hp := Real.rpow_le_rpow (by positivity) hratio heta.le
        have hp' := ENNReal.ofReal_le_ofReal hp
        simpa [Real.inv_rpow (show (0 : ℝ) <= delta by positivity),
          ← Real.rpow_neg (show (0 : ℝ) <= delta by positivity),
          ← ENNReal.ofReal_rpow_of_pos (show (0 : ℝ) < delta by exact_mod_cast hd.1)] using hp'
      have hcover : Q.indexSet a <= (Q.indexSet 0).biUnion (Q.fibre 0 a) := by
        intro j hj
        obtain ⟨i, hi, hij⟩ := Q.place_surjective a haM.le j hj
        refine Finset.mem_biUnion.mpr ⟨Q.place 0 i, Q.place_mem 0 hM0.le i hi, ?_⟩
        exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩, hij⟩
      calc
        Kakeya.maxDensity (Q.indexSet a) (fun i => (Q.tube a i).toConvexSpaceBody) <=
            ∑ j ∈ Q.indexSet 0, Kakeya.maxDensity (Q.fibre 0 a j)
              (fun i => (Q.tube a i).toConvexSpaceBody) :=
          Kakeya.maxDensity_le_sum_of_subset_biUnion _ hcover
        _ <= ∑ j ∈ Q.indexSet 0,
            (D : ℝ≥0∞) ^ N * (delta : ℝ≥0∞) ^ (-eta J) := by
          refine Finset.sum_le_sum fun j hj => (hwindow.coarse_density (by omega) j hj).trans ?_
          exact mul_le_mul_right hpow _
        _ = ((Q.indexSet 0).card : ℝ≥0∞) *
            ((D : ℝ≥0∞) ^ N * (delta : ℝ≥0∞) ^ (-eta J)) := by simp
        _ <= (1280 : ℝ≥0∞) ^ 6 *
            ((D : ℝ≥0∞) ^ N * (delta : ℝ≥0∞) ^ (-eta J)) := by gcongr
        _ = (K : ℝ≥0∞) * (delta : ℝ≥0∞) ^ (-eta J) := by simp [K, mul_assoc]
  refine hbound.trans ?_
  calc
    (K : ℝ≥0∞) * (delta : ℝ≥0∞) ^ (-eta J) <=
        (delta : ℝ≥0∞) ^ (-eta J) * (delta : ℝ≥0∞) ^ (-eta J) := by gcongr
    _ = (delta : ℝ≥0∞) ^ (-2 * eta J) := by
      rw [← ENNReal.rpow_add _ _ (by exact_mod_cast hd.1.ne') ENNReal.coe_ne_top]
      congr 1
      ring

end Kakeya.ML2Core

namespace Kakeya.ML2Assembly

open ML2Core ML2Reduction VeryNotSticky

universe u

/-- The original R4 density rows need the genuine retained upper window.
No lower row at the former tau exponent is reconstructed. -/
theorem sourceQ_retained_middle_original_bounds
    {iota : Type u} {delta : ℝ≥0} {S : Finset iota}
    {T : iota -> Tube delta (EuclideanSpace ℝ (Fin 3))} {M C : Nat}
    (Q : SourceThreadedTower S T M C) {a p b N J : Nat} {jp : iota} {F : Finset iota}
    (Z : iota -> ShadedTube (sourceTowerRadius delta M b) (EuclideanSpace ℝ (Fin 3)))
    {rho : ℝ≥0} {e zeta etaC q gamma etaD R : ℝ} {A0 A1 : Nat}
    (hinput : SourceQCoverInput Q a p b jp F Z rho e zeta etaC)
    (eta : Nat -> ℝ)
    (hwindow : SourceParentUpperWindow Q A0 A1 N eta e a b J)
    (hsit : Tube.IsRescalingSituation (sourceTowerRadius delta M p)
      (sourceTowerRadius delta M b) rho R 3) (hR : 0 < R)
    (he : 0 < e) (_hrho : rho <= 1) (hS : (S.card : ℝ) <= (delta : ℝ) ^ (-(5 : ℝ)))
    (hfull : rho ^ gamma <= (outerLoss R)⁻¹ * ShadedBody.fullness F
      (fun i => (Z i).toShadedBody))
    (hnormalized : (outerLoss R : ℝ≥0∞) * ENNReal.ofReal
      (((sourceTowerRadius delta M a : ℝ) / (sourceTowerRadius delta M b : ℝ)) ^ eta J) <=
        (rho : ℝ≥0∞) ^ (-q))
    (horiginal : ENNReal.ofReal
      (((sourceTowerRadius delta M a : ℝ) / (sourceTowerRadius delta M b : ℝ)) ^ eta J) <=
        (rho : ℝ≥0∞) ^ (-(etaD - q))) :
    (forall i, i ∈ F -> (Z i).carrier <= (Q.tube p jp).carrier) /\
    0 < sourceQMiddleCardPower e /\
    (F.card : ℝ) <= (rho : ℝ) ^ (-(sourceQMiddleCardPower e : ℝ)) /\
    Kakeya.maxDensity F (fun i => (Z i).toConvexSpaceBody) <=
      (rho : ℝ≥0∞) ^ (-(etaD - q)) /\
    Kakeya.maxDensity F (fun i =>
      (outerFamily hsit.pos_ambient (Q.tube p jp) hR rho Z i).toConvexSpaceBody) <=
        (rho : ℝ≥0∞) ^ (-q) /\
    (rho : ℝ≥0∞) ^ gamma <= ShadedBody.fullness F (fun i =>
      (outerFamily hsit.pos_ambient (Q.tube p jp) hR rho Z i).toShadedBody) := by
  classical
  have hassign : forall k l, k <= l -> l <= M -> forall i, i ∈ S -> forall j, j ∈ S ->
      Q.place l i = Q.place l j -> Q.place k i = Q.place k j := by
    intro k l hkl
    induction l, hkl using Nat.le_induction with
    | base => exact fun _ _ _ _ _ h => h
    | succ l hkl ih =>
      intro hl i hi j hj heq
      apply ih (by omega) i hi j hj
      rw [Q.parent_composition l (by omega) i hi, Q.parent_composition l (by omega) j hj, heq]
  have hcontains : forall k l, k <= l -> l <= M -> forall i, i ∈ S ->
      (Q.tube l (Q.place l i)).toConvexSpaceBody <=
        (Q.tube k (Q.place k i)).toConvexSpaceBody := by
    intro k l hkl
    induction l, hkl using Nat.le_induction with
    | base => exact fun _ _ _ => le_rfl
    | succ l hkl ih =>
      intro hl i hi
      refine le_trans ?_ (ih (by omega) i hi)
      rw [Q.parent_composition l (by omega) i hi]
      exact Q.parent_containment l (by omega) _ (Q.place_mem (l + 1) hl i hi)
  have hpM : p <= M := hinput.parent_lt_middle.le.trans hinput.middle_bound
  obtain ⟨i0, hi0, hi0p⟩ := Q.place_surjective p hpM jp hinput.parent_member
  let ja := Q.place a i0
  have hja : ja ∈ Q.indexSet a := Q.place_mem a (hinput.coarse_le_parent.trans hpM) i0 hi0
  have hFcoarse : F <= Q.fibre a b ja := by
    intro i hi
    obtain ⟨x, hx, hxi⟩ := Finset.mem_image.mp (hinput.family_subset hi)
    obtain ⟨hxS, hxp⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hxS, ?_⟩, hxi⟩
    exact hassign a p hinput.coarse_le_parent hpM x hxS i0 hi0 (hxp.trans hi0p.symm)
  have hsub : forall i, i ∈ F -> (Z i).carrier <= (Q.tube p jp).carrier := by
    intro i hi
    obtain ⟨x, hx, hxi⟩ := Finset.mem_image.mp (hinput.family_subset hi)
    obtain ⟨hxS, hxp⟩ := Finset.mem_filter.mp hx
    have hh := hcontains p b hinput.parent_lt_middle.le hinput.middle_bound x hxS
    rw [hxi, hxp] at hh
    change (Q.tube b i).carrier <= (Q.tube p jp).carrier at hh
    simpa only [← hinput.family_tubes i] using hh
  have hdelta : (0 : ℝ) < delta := by exact_mod_cast hinput.delta_pos
  have hdelta1 : (delta : ℝ) <= 1 := by
    have hbound : (40 : ℝ≥0) ^ (-(M : ℝ)) <= 1 :=
      NNReal.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.mpr (Nat.cast_nonneg _))
    exact_mod_cast hinput.delta_small.le.trans hbound
  have hK : 0 < sourceQMiddleCardPower e := by unfold sourceQMiddleCardPower; omega
  have hKreal : 0 < (sourceQMiddleCardPower e : ℝ) := by exact_mod_cast hK
  have hpower : 5 <= e * (sourceQMiddleCardPower e : ℝ) / 2 := by
    have hc : 10 / e <= (sourceQMiddleCardPower e : ℝ) := by
      exact (Nat.le_ceil _).trans (by unfold sourceQMiddleCardPower; norm_cast; omega)
    have hh := (div_le_iff₀ he).mp hc
    nlinarith
  have hcard : (F.card : ℝ) <= (rho : ℝ) ^ (-(sourceQMiddleCardPower e : ℝ)) := by
    have hc : F.card <= S.card :=
      (Finset.card_le_card hinput.family_subset).trans
        (Finset.card_image_le.trans (Finset.card_filter_le S _))
    have hrhoδ : (rho : ℝ) <= (delta : ℝ) ^ (e / 2) :=
      hinput.rho_upper.trans (by nlinarith [Real.rpow_nonneg hdelta.le (e / 2)])
    calc
      (F.card : ℝ) <= (S.card : ℝ) := by exact_mod_cast hc
      _ <= (delta : ℝ) ^ (-(5 : ℝ)) := hS
      _ <= (delta : ℝ) ^ ((e / 2) * (-(sourceQMiddleCardPower e : ℝ))) := by
        apply Real.rpow_le_rpow_of_exponent_ge hdelta hdelta1
        nlinarith
      _ = ((delta : ℝ) ^ (e / 2)) ^ (-(sourceQMiddleCardPower e : ℝ)) :=
        Real.rpow_mul hdelta.le _ _
      _ <= (rho : ℝ) ^ (-(sourceQMiddleCardPower e : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hsit.pos_out) hrhoδ (neg_nonpos.mpr hKreal.le)
  have hmax : Kakeya.maxDensity F (fun i => (Z i).toConvexSpaceBody) <=
      ENNReal.ofReal
        (((sourceTowerRadius delta M a : ℝ) / (sourceTowerRadius delta M b : ℝ)) ^ eta J) := by
    rw [Kakeya.maxDensity_congr (fun i _ => congrArg Tube.toConvexSpaceBody (hinput.family_tubes i))]
    exact (Kakeya.maxDensity_mono _ hFcoarse).trans (hwindow.middle_density ja hja)
  have hR1 : 1 <= R := (show (1 : ℝ) <= (Tube.normalization.C 3 : ℝ) by
    exact_mod_cast Tube.normalization.one_le_C 3).trans hsit.normalizationConst_le_radius
  have hratio : (sourceTowerRadius delta M b : ℝ) /
      (sourceTowerRadius delta M p : ℝ) <= 4 * (rho : ℝ) := by
    rw [hinput.rho_eq]
    simp only [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_ofNat]
    have hp : (0 : ℝ) < sourceTowerRadius delta M p := by exact_mod_cast hsit.pos_ambient
    field_simp
    nlinarith [NNReal.coe_nonneg (sourceTowerRadius delta M b)]
  refine ⟨hsub, hK, hcard, hmax.trans horiginal, ?_, ?_⟩
  · exact (outerFamily_maxDensity_le (by simp) hsit hR hR1 hratio hsub).trans
      ((mul_le_mul_right hmax _).trans hnormalized)
  · have hh := hfull.trans (outerFamily_le_fullness (by simp) hsit hR hR1 hratio hsub)
    simpa only [ENNReal.coe_rpow_of_ne_zero hsit.pos_out.ne'] using
      (show ((rho ^ gamma : ℝ≥0) : ℝ≥0∞) <= _ by exact_mod_cast hh)

end Kakeya.ML2Assembly

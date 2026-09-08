/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceStickyScales

/-!
# Sticky density interpolation and terminal SSF preparation

`SourceStickyOccupied` restricts the terminal density to occupied cover nodes;
`SourceStickySSFPreparation` is a single terminal SSF refinement on the source tower.
`source_exists_sticky_density_interpolation_constants` produces constants `K`, `J`
independent of `delta`, `M` and the family such that a level-density bound `H` on the tower
gives `IsKatzTaoAtEveryScale` with constant `K * delta^(-J/M) * H` for every occupied shaded
uniform set. `source_exists_terminal_ssf_preparation` builds the preparation from
`ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf` under a polynomial cardinal ceiling.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube

namespace Kakeya.ML2Core

universe u

section Interpolation

variable {iota : Type u} {delta : ℝ≥0} {ambient : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace ℝ (Fin 3))} {M C : Nat}

/-- No empty or unused cover nodes are counted by the terminal density. -/
def SourceStickyOccupied {R : Finset iota}
    {W : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3))}
    {Cu : ℝ≥0} (U : ShadedUniformTubeSet R W (ssfGridLen delta) Cu) : Prop :=
  ∀ k, k <= ssfGridLen delta -> ∀ j ∈ U.tubeUniform.cover.indexSet k,
    ∃ i ∈ R, U.tubeUniform.cover.assign k i = j

/-- A single terminal SSF refinement. Q remains the source potential's tower;
the SSF hierarchy is used only on this terminal branch. -/
structure SourceStickySSFPreparation
    (Q : SourceThreadedTower ambient T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3))) (a : ℝ) where
  retained : Finset iota
  shading : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3))
  uniform : ShadedUniformTubeSet retained shading (ssfGridLen delta) (ssfUniformConst 3)
  subset : retained <= ambient
  nonempty : retained.Nonempty
  tube_identity : ∀ i, (shading i).toTube = T i
  shade_subset : ∀ i, (shading i).shade <= (Z i).shade
  ball : ∀ i ∈ retained, (shading i).carrier <= Metric.closedBall 0 1
  occupied : SourceStickyOccupied uniform
  cardinality : (ambient.card : ℝ) <= (delta : ℝ) ^ (-a) * (retained.card : ℝ)
  mass : (∑ i ∈ ambient, volume (Z i).shade) <=
    ENNReal.ofReal ((delta : ℝ) ^ (-a)) * ∑ i ∈ retained, volume (shading i).shade
  fullness : ShadedBody.fullness' ambient (fun i => (Z i).toShadedBody) <=
    ENNReal.ofReal ((delta : ℝ) ^ (-a)) *
      ShadedBody.fullness' retained (fun i => (shading i).toShadedBody)
  multiplicity : ShadedBody.multiplicity ambient (fun i => (Z i).toShadedBody) <=
    ENNReal.ofReal ((delta : ℝ) ^ (-a)) *
      ShadedBody.multiplicity retained (fun i => (shading i).toShadedBody)
  union_subset : (⋃ i ∈ retained, (shading i).shade) <= (⋃ i ∈ ambient, (Z i).shade)
  assigned_profile_mono : ∀ k l,
    Q.assignedProfile retained k l <= Q.assignedProfile ambient k l

/-- New geometric bridge required by the SSF boundary. K and J are independent
of delta, M, the family and the chosen terminal hierarchy. Their construction
must use occupied nodes, bounded overlap and the source geometry. -/
theorem source_exists_sticky_density_interpolation_constants (C A0 A1 : Nat)
    (_hC : 1 <= C) (_hA0 : 1 <= A0) (_hA1 : 1 <= A1) :
    ∃ (K : ℝ) (J : Nat), 1 <= K /\ 1 <= J /\
      ∀ {iota : Type u} {delta : ℝ≥0} {ambient : Finset iota}
        {T : iota -> Tube delta (EuclideanSpace ℝ (Fin 3))} {M : Nat},
        2 <= M -> 0 < delta -> delta < (400 : ℝ≥0) ^ (-(M : ℝ)) ->
      ∀ Q : SourceThreadedTower ambient T M C, SourceTowerGeometry Q A0 A1 ->
      ∀ H : ℝ≥0∞, 1 <= H -> H ≠ ⊤ ->
        (∀ l, l <= M -> Kakeya.maxDensity (Q.indexSet l)
          (fun j => (Q.tube l j).toConvexSpaceBody) <= H) ->
      ∀ (R : Finset iota), R <= ambient ->
      ∀ W : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3)),
        (∀ i, (W i).toTube = T i) ->
      ∀ U : ShadedUniformTubeSet R W (ssfGridLen delta) (ssfUniformConst 3),
        SourceStickyOccupied U ->
        U.tubeUniform.IsKatzTaoAtEveryScale
          (ENNReal.ofReal (K * (delta : ℝ) ^ (-((J : ℝ) / (M : ℝ)))) * H) := by
  classical
  let cu : ℝ≥0 := ssfUniformConst 3
  let cv : ℝ≥0 := Tube.le_volume.c 3
  let Cv : ℝ≥0 := Tube.volume_le.C 3
  let D : ℝ≥0 := cu * Cv / cv
  let K : ℝ≥0 := max 1 (125 * D * 40 ^ 2)
  have hcv : 0 < cv := Tube.le_volume.c_pos 3
  have hK : (1 : ℝ≥0) <= K := le_max_left _ _
  refine ⟨(K : ℝ), 2, by exact_mod_cast hK, by omega, ?_⟩
  intro iota delta ambient T M hM hd0 hd Q hgeom H hH hHfin hlevels R hR W hW U hocc
  have hd1 : delta <= 1 := hd.le.trans
    (NNReal.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by simp))
  obtain ⟨fine, hfine⟩ := source_exists_sticky_scale_bracket hM hd0 hd
  intro k hk
  let rho := sourceTowerRadius delta M (fine k)
  let sigma := gridScale delta (ssfGridLen delta) k
  obtain ⟨hl1, hlM, hrs, hratio⟩ := hfine k hk
  have hr0 : 0 < rho := by
    dsimp [rho, sourceTowerRadius]
    split_ifs <;> positivity
  have hs0 : 0 < sigma := gridScale_pos hd0 _ _
  have hs1 : sigma <= 1 := gridScale_le_one hd1 _ _
  let L : ℝ≥0 := D * (sigma / rho) ^ 2
  have hcoef : (L : ℝ≥0∞) * ((cv : ℝ≥0∞) * (rho : ℝ≥0∞) ^ 2) =
      (cu : ℝ≥0∞) * ((Cv : ℝ≥0∞) * (sigma : ℝ≥0∞) ^ 2) := by
    have hh : L * (cv * rho ^ 2) = cu * (Cv * sigma ^ 2) := by
      dsimp [L, D]
      field_simp
    exact_mod_cast hh
  have hcharge : Kakeya.maxDensity (U.tubeUniform.cover.indexSet k)
      (fun j => (U.tubeUniform.cover.tube k j).toConvexSpaceBody) <=
        (125 : ℝ≥0∞) * (L : ℝ≥0∞) * H := by
    rw [Kakeya.maxDensity_le_iff]
    intro A
    let Ap := A.cthickening (4 * (rho : ℝ))
    let P := (U.tubeUniform.cover.indexSet k).filter
      (fun j => (U.tubeUniform.cover.tube k j).toConvexSpaceBody <= A)
    let F := (Q.indexSet (fine k)).filter
      (fun j => (Q.tube (fine k) j).toConvexSpaceBody <= Ap)
    let meet : iota -> Finset iota := fun q =>
      (U.tubeUniform.cover.indexSet k).filter (fun j => ∃ i ∈ R,
        (W i).toConvexSpaceBody <= (U.tubeUniform.cover.tube k j).toConvexSpaceBody ∧
        (W i).toConvexSpaceBody <= ((Q.tube (fine k) q).rescale sigma).toConvexSpaceBody)
    have hPsub : P <= F.biUnion meet := by
      intro j hj
      obtain ⟨hjn, hjA⟩ := Finset.mem_filter.mp hj
      obtain ⟨i, hi, hij⟩ := hocc k hk j hjn
      have hleaf : (W i).toConvexSpaceBody <=
          (U.tubeUniform.cover.tube k j).toConvexSpaceBody := by
        simpa only [hij] using U.tubeUniform.cover.le_tube_assign k hk i hi
      have hQleaf : (W i).toConvexSpaceBody <=
          (Q.tube (fine k) (Q.place (fine k) i)).toConvexSpaceBody := by
        rw [hW]
        exact Q.leaf_containment (fine k) hlM i (hR hi)
      have hAp : (Q.tube (fine k) (Q.place (fine k) i)).toConvexSpaceBody <= Ap :=
        StickyKakeya.tube_le_cthickening_of_common_leaf (W i).toTube
          (Q.tube (fine k) (Q.place (fine k) i)) hQleaf (hleaf.trans hjA)
      apply Finset.mem_biUnion.mpr
      refine ⟨Q.place (fine k) i,
        Finset.mem_filter.mpr ⟨Q.place_mem (fine k) hlM i (hR hi), hAp⟩, ?_⟩
      exact Finset.mem_filter.mpr ⟨hjn, i, hi, hleaf,
        hQleaf.trans ((Q.tube (fine k) (Q.place (fine k) i)).le_rescale hrs)⟩
    have hmeet : ∀ q, ((meet q).card : ℝ≥0) <= cu := by
      intro q
      exact U.tubeUniform.boundedOverlap k hk ((Q.tube (fine k) q).rescale sigma)
    have hcard : (P.card : ℝ≥0∞) <= (F.card : ℝ≥0∞) * (cu : ℝ≥0∞) := by
      have hcount : P.card <= ∑ q ∈ F, (meet q).card :=
        (Finset.card_le_card hPsub).trans Finset.card_biUnion_le
      have hcount' : (P.card : ℝ≥0) <= ∑ q ∈ F, ((meet q).card : ℝ≥0) := by
        exact_mod_cast hcount
      have hh : (P.card : ℝ≥0) <= (F.card : ℝ≥0) * cu := by
        refine hcount'.trans ?_
        calc
          _ <= ∑ _q ∈ F, cu := Finset.sum_le_sum fun q _ => hmeet q
          _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
      exact_mod_cast hh
    have hPvol : (∑ j ∈ P, volume (U.tubeUniform.cover.tube k j).carrier) <=
        (P.card : ℝ≥0∞) * ((Cv : ℝ≥0∞) * (sigma : ℝ≥0∞) ^ 2) := by
      calc
        _ <= ∑ _j ∈ P, (Cv : ℝ≥0∞) * (sigma : ℝ≥0∞) ^ 2 := by
          apply Finset.sum_le_sum
          intro j _
          simpa [Cv, sigma] using Tube.volume_le hs1 (U.tubeUniform.cover.tube k j)
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    have hFvol : (F.card : ℝ≥0∞) * ((cv : ℝ≥0∞) * (rho : ℝ≥0∞) ^ 2) <=
        ∑ q ∈ F, volume (Q.tube (fine k) q).carrier := by
      rw [← nsmul_eq_mul]
      apply Finset.card_nsmul_le_sum
      intro q _
      simpa [cv, rho] using Tube.le_volume (Q.tube (fine k) q)
    have hFdens : (∑ q ∈ F, volume (Q.tube (fine k) q).carrier) <= H * volume Ap.carrier := by
      exact (Kakeya.densityIn_le_iff _ _ Ap H).mp
        ((Kakeya.le_maxDensity _ _ Ap).trans (hlevels (fine k) hlM))
    apply (Kakeya.densityIn_le_iff _ _ A _).mpr
    change (∑ j ∈ P, volume (U.tubeUniform.cover.tube k j).carrier) <= _
    rcases P.eq_empty_or_nonempty with hPe | hPne
    · simp [hPe]
    · obtain ⟨j, hj⟩ := hPne
      have hball : Metric.closedBall (U.tubeUniform.cover.tube k j).x (sigma : ℝ) <= A.carrier := by
        apply Set.Subset.trans ?_ (Finset.mem_filter.mp hj).2
        change Metric.closedBall (U.tubeUniform.cover.tube k j).x (sigma : ℝ) <=
          (U.tubeUniform.cover.tube k j).carrier
        rw [(U.tubeUniform.cover.tube k j).carrier_eq]
        exact fun _ hx => Set.mem_biUnion (left_mem_segment ℝ _ _) hx
      have hApvol : volume Ap.carrier <= (125 : ℝ≥0∞) * volume A.carrier := by
        have hthick : Ap.carrier <= (A.cthickening (4 * (sigma : ℝ))).carrier := by
          apply Metric.cthickening_mono
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast hrs) (by norm_num)
        refine (measure_mono hthick).trans ?_
        have hh := StickyKakeya.volume_cthickening_four_mul_le
          (by exact_mod_cast hs0 : (0 : ℝ) < (sigma : ℝ)) (le_refl sigma) A hball
        norm_num [div_self (show (sigma : ℝ) ≠ 0 by exact_mod_cast hs0.ne')] at hh ⊢
        exact hh
      calc
        _ <= (P.card : ℝ≥0∞) * ((Cv : ℝ≥0∞) * (sigma : ℝ≥0∞) ^ 2) := hPvol
        _ <= ((F.card : ℝ≥0∞) * (cu : ℝ≥0∞)) *
            ((Cv : ℝ≥0∞) * (sigma : ℝ≥0∞) ^ 2) := mul_le_mul_left hcard _
        _ = (L : ℝ≥0∞) * ((F.card : ℝ≥0∞) * ((cv : ℝ≥0∞) * (rho : ℝ≥0∞) ^ 2)) := by
          rw [mul_left_comm (L : ℝ≥0∞), hcoef]
          ring
        _ <= (L : ℝ≥0∞) * ∑ q ∈ F, volume (Q.tube (fine k) q).carrier := mul_le_mul_right hFvol _
        _ <= (L : ℝ≥0∞) * (H * volume Ap.carrier) := mul_le_mul_right hFdens _
        _ <= (L : ℝ≥0∞) * (H * ((125 : ℝ≥0∞) * volume A.carrier)) := by gcongr
        _ = _ := by ring
  have hratio' : sigma / rho <= 40 * delta ^ (-(1 / (M : ℝ))) :=
    (div_le_iff₀ hr0).mpr hratio
  have hpower : (delta ^ (-(1 / (M : ℝ)))) ^ (2 : Nat) = delta ^ (-(2 / (M : ℝ))) := by
    rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul]
    congr 1
    push_cast
    ring
  have hbound : (125 : ℝ≥0) * L <= K * delta ^ (-(2 / (M : ℝ))) := by
    calc
      _ <= 125 * (D * (40 * delta ^ (-(1 / (M : ℝ)))) ^ 2) := by
        dsimp [L]
        gcongr
      _ = (125 * D * 40 ^ 2) * delta ^ (-(2 / (M : ℝ))) := by
        rw [mul_pow, hpower]
        ring
      _ <= _ := mul_le_mul_of_nonneg_right (le_max_right 1 _) (by positivity)
  have hbound' : (125 : ℝ≥0∞) * (L : ℝ≥0∞) <=
      ENNReal.ofReal ((K : ℝ) * (delta : ℝ) ^ (-((2 : Nat) / (M : ℝ)))) := by
    have hh : ((125 * L : ℝ≥0) : ℝ≥0∞) <=
        ((K * delta ^ (-(2 / (M : ℝ))) : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast hbound
    simpa only [ENNReal.coe_mul, ENNReal.coe_ofNat, ENNReal.ofReal_mul (NNReal.coe_nonneg K),
      ENNReal.ofReal_coe_nnreal, ← NNReal.coe_rpow, ENNReal.ofReal_coe_nnreal, Nat.cast_ofNat] using hh
  exact hcharge.trans (mul_le_mul_left hbound' H)

/-- Source leaf-mass comparability pays actual mass, not just cardinality.
The polynomial card ceiling is a proved source input available to the caller. -/
theorem source_exists_terminal_ssf_preparation (K0 : Nat) {a : ℝ} (ha : 0 < a) :
    ∃ delta0 : ℝ≥0, 0 < delta0 /\ delta0 <= 1 /\
      ∀ {iota : Type u} {delta : ℝ≥0} {ambient : Finset iota}
        {T : iota -> Tube delta (EuclideanSpace ℝ (Fin 3))} {M C : Nat},
        0 < delta -> delta < delta0 -> ambient.Nonempty ->
      ∀ (Q : SourceThreadedTower ambient T M C)
        (Z : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3))),
        SourceTowerStatistics Q Z ->
        (∀ i ∈ ambient, (Z i).carrier <= Metric.closedBall 0 1) ->
        (ambient.card : ℝ) <= (delta : ℝ) ^ (-(K0 : ℝ)) ->
        0 < ∑ i ∈ ambient, volume (Z i).shade ->
        Nonempty (SourceStickySSFPreparation Q Z a) := by
  classical
  obtain ⟨d0, hd0, hd1, hprepare⟩ := ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf
    (E := EuclideanSpace ℝ (Fin 3)) K0 (a / 4) (a / 4) (by linarith) (by linarith)
  let d2 : ℝ≥0 := (1 / 2 : ℝ≥0) ^ (2 / a)
  have hd2 : 0 < d2 := by dsimp [d2]; positivity
  refine ⟨min d0 d2, lt_min hd0 hd2, (min_le_left _ _).trans hd1, ?_⟩
  intro iota delta ambient T M C hdelta0 hdelta hne Q Z hstats hball hcard hmasspos
  have hdelta1 : delta <= 1 := (hdelta.le.trans (min_le_left _ _)).trans hd1
  obtain ⟨R, hR, V, hV, hshade, hRcard, hfull, ⟨U⟩⟩ :=
    hprepare hdelta0 (hdelta.le.trans (min_le_left _ _)) ambient Z hball hcard
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  rw [hn] at U
  have hRne : R.Nonempty := by
    by_contra h
    have he : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    rw [he, Finset.card_empty, Nat.cast_zero, mul_zero] at hRcard
    have hcpos : (0 : ℝ) < (ambient.card : ℝ) := by exact_mod_cast hne.card_pos
    linarith
  have hVtubes : ∀ i, (V i).toTube = T i := fun i => (hV i).trans (hstats.same_tubes i)
  have hcell : ∀ i ∈ ambient, Q.cell M i = {i} := by
    intro i hi
    ext j
    simp only [SourceThreadedTower.cell, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro hj
      simpa only [Q.bottom_place j hj.1] using hj.2
    · intro hji
      subst j
      exact ⟨hi, Q.bottom_place i hi⟩
  have hcomp : ∀ i ∈ ambient, ∀ j ∈ ambient,
      volume (Z i).shade <= 2 * volume (Z j).shade := by
    intro i hi j hj
    have hh := hstats.fibre_mass M le_rfl i (by simpa [Q.bottom_index] using hi)
      j (by simpa [Q.bottom_index] using hj)
    simpa only [hcell i hi, hcell j hj, Finset.sum_singleton] using hh
  have hsumfull : ∀ (S : Finset iota) (Y : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3))),
      (∑ i ∈ S, volume (Y i).shade) = ShadedBody.fullness' S (fun i => (Y i).toShadedBody) *
        ∑ i ∈ S, volume (Y i).carrier := by
    intro S Y
    simpa only [← ShadedBody.coe_fullness] using
      ShadedBody.sum_volumeReal_shade_eq_fullness_mul S (fun i => (Y i).toShadedBody)
  have hden : (∑ i ∈ R, volume (V i).carrier) = ∑ i ∈ R, volume (Z i).carrier := by
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun t : Tube delta (EuclideanSpace ℝ (Fin 3)) => volume t.carrier) (hV i)
  have hshrink : (∑ i ∈ R, volume (Z i).shade) <=
      ENNReal.ofReal ((delta : ℝ) ^ (-(a / 4))) * ∑ i ∈ R, volume (V i).shade := by
    rw [hsumfull R Z, hsumfull R V, hden, ← mul_assoc]
    exact mul_le_mul_left hfull _
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image R (fun i => volume (Z i).shade) hRne
  have hselect : (∑ i ∈ ambient, volume (Z i).shade) <=
      (2 * ENNReal.ofReal ((delta : ℝ) ^ (-(a / 4)))) * ∑ i ∈ R, volume (Z i).shade := by
    have hcardE : (ambient.card : ℝ≥0∞) <=
        ENNReal.ofReal ((delta : ℝ) ^ (-(a / 4))) * (R.card : ℝ≥0∞) := by
      have hh := ENNReal.ofReal_le_ofReal hRcard
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast] at hh
      exact hh
    have hminsum : (R.card : ℝ≥0∞) * volume (Z j).shade <= ∑ i ∈ R, volume (Z i).shade := by
      rw [← nsmul_eq_mul]
      exact Finset.card_nsmul_le_sum R _ _ hmin
    calc
      _ <= ∑ _i ∈ ambient, 2 * volume (Z j).shade :=
        Finset.sum_le_sum fun i hi => hcomp i hi j (hR hj)
      _ = 2 * ((ambient.card : ℝ≥0∞) * volume (Z j).shade) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
      _ <= 2 * ((ENNReal.ofReal ((delta : ℝ) ^ (-(a / 4))) * (R.card : ℝ≥0∞)) *
          volume (Z j).shade) := by gcongr
      _ = (2 * ENNReal.ofReal ((delta : ℝ) ^ (-(a / 4)))) *
          ((R.card : ℝ≥0∞) * volume (Z j).shade) := by ring
      _ <= _ := mul_le_mul_right hminsum _
  have habs : (2 : ℝ≥0∞) * ENNReal.ofReal ((delta : ℝ) ^ (-(a / 4))) *
      ENNReal.ofReal ((delta : ℝ) ^ (-(a / 4))) <= ENNReal.ofReal ((delta : ℝ) ^ (-a)) := by
    have hdhalf : delta ^ (a / 2) <= (1 / 2 : ℝ≥0) := by
      have hh := NNReal.rpow_le_rpow (hdelta.le.trans (min_le_right _ _)) (by linarith : 0 <= a / 2)
      change delta ^ (a / 2) <= d2 ^ (a / 2) at hh
      rw [show d2 ^ (a / 2) = (1 / 2 : ℝ≥0) by
        dsimp [d2]
        rw [← NNReal.rpow_mul, show 2 / a * (a / 2) = 1 by field_simp, NNReal.rpow_one]] at hh
      exact hh
    have htwo : (2 : ℝ) <= (delta : ℝ) ^ (-(a / 2)) := by
      rw [Real.rpow_neg (by positivity), le_inv_comm₀ (by norm_num)
        (Real.rpow_pos_of_pos (by exact_mod_cast hdelta0) _)]
      have hh : (delta : ℝ) ^ (a / 2) <= (1 : ℝ) / 2 := by exact_mod_cast hdhalf
      simpa only [one_div] using hh
    have hh : 2 * (delta : ℝ) ^ (-(a / 4)) * (delta : ℝ) ^ (-(a / 4)) <=
        (delta : ℝ) ^ (-a) := by
      calc
        _ <= (delta : ℝ) ^ (-(a / 2)) * (delta : ℝ) ^ (-(a / 4)) *
            (delta : ℝ) ^ (-(a / 4)) := by gcongr
        _ = _ := by
          rw [← Real.rpow_add (by exact_mod_cast hdelta0),
            ← Real.rpow_add (by exact_mod_cast hdelta0)]
          congr 1
          ring
    simpa only [ENNReal.ofReal_mul (by positivity : (0 : ℝ) <= 2 *
        (delta : ℝ) ^ (-(a / 4))), ENNReal.ofReal_mul (by norm_num : (0 : ℝ) <= 2),
      ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hh
  have hmass : (∑ i ∈ ambient, volume (Z i).shade) <=
      ENNReal.ofReal ((delta : ℝ) ^ (-a)) * ∑ i ∈ R, volume (V i).shade := by
    refine hselect.trans ?_
    calc
      _ <= (2 * ENNReal.ofReal ((delta : ℝ) ^ (-(a / 4)))) *
          (ENNReal.ofReal ((delta : ℝ) ^ (-(a / 4))) * ∑ i ∈ R, volume (V i).shade) :=
        mul_le_mul_right hshrink _
      _ = _ := by rw [← mul_assoc]
      _ <= _ := mul_le_mul_left habs _
  have hunion : (⋃ i ∈ R, (V i).shade) <= (⋃ i ∈ ambient, (Z i).shade) :=
    Set.iUnion₂_mono' fun i hi => ⟨i, hR hi, hshade i⟩
  have hfullpay : ShadedBody.fullness' ambient (fun i => (Z i).toShadedBody) <=
      ENNReal.ofReal ((delta : ℝ) ^ (-a)) * ShadedBody.fullness' R (fun i => (V i).toShadedBody) := by
    have hdenle : (∑ i ∈ R, volume (V i).carrier) <= ∑ i ∈ ambient, volume (Z i).carrier :=
      hden.trans_le (Finset.sum_le_sum_of_subset hR)
    unfold ShadedBody.fullness'
    rw [← mul_div_assoc]
    exact ENNReal.div_le_div hmass hdenle
  let G : GridCoverSystem R (fun i => (V i).toTube) (ssfGridLen delta) := {
    U.tubeUniform.cover with
    indexSet := fun k => R.image (U.tubeUniform.cover.assign k)
    assign_mem := fun k _ i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩
  }
  have hGsub : ∀ k, k <= ssfGridLen delta -> G.indexSet k <= U.tubeUniform.cover.indexSet k := by
    intro k hk j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact U.tubeUniform.cover.assign_mem k hk i hi
  let Ut : UniformTubeSet R (fun i => (V i).toTube) (ssfGridLen delta) (ssfUniformConst 3) := {
    U.tubeUniform with
    cover := G
    tube_injOn := fun k hk => (U.tubeUniform.tube_injOn k hk).mono (hGsub k hk)
    boundedOverlap := by
      intro k hk B
      exact (show (((G.indexSet k).filter _).card : ℝ≥0) <=
        (((U.tubeUniform.cover.indexSet k).filter _).card : ℝ≥0) by
          exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (hGsub k hk))).trans
        (U.tubeUniform.boundedOverlap k hk B)
    card_class_le := fun k hk j hj => U.tubeUniform.card_class_le k hk j (hGsub k hk hj)
    le_card_class := fun k hk j hj => U.tubeUniform.le_card_class k hk j (hGsub k hk hj)
  }
  let U' : ShadedUniformTubeSet R V (ssfGridLen delta) (ssfUniformConst 3) := { U with tubeUniform := Ut }
  refine ⟨{
    retained := R
    shading := V
    uniform := U'
    subset := hR
    nonempty := hRne
    tube_identity := hVtubes
    shade_subset := hshade
    ball := ?_
    occupied := ?_
    cardinality := ?_
    mass := hmass
    fullness := hfullpay
    multiplicity := ShadedBody.multiplicity_le_mul_of_sum_shade_le_of_biUnion_subset
      ambient (fun i => (Z i).toShadedBody) R (fun i => (V i).toShadedBody)
        (ENNReal.ofReal ((delta : ℝ) ^ (-a))) hunion hmass
    union_subset := hunion
    assigned_profile_mono := ?_
  }⟩
  · intro i hi
    have heq := congrArg (fun t : Tube delta (EuclideanSpace ℝ (Fin 3)) => t.carrier) (hV i)
    rw [heq]
    exact hball i (hR hi)
  · intro k hk j hj
    exact Finset.mem_image.mp hj
  · exact hRcard.trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hdelta0)
        (by exact_mod_cast hdelta1) (by linarith)) (by positivity))
  · intro k l
    refine Finset.sup_le fun j hj => ?_
    refine (Kakeya.maxDensity_mono _ (Finset.image_subset_image
      (Finset.filter_subset_filter _ hR))).trans ?_
    exact Finset.le_sup (f := fun j => Kakeya.maxDensity (Q.retainedAssignedFibre ambient k l j)
      (fun i => (Q.tube l i).toConvexSpaceBody)) (Finset.image_subset_image hR hj)

end Interpolation

end Kakeya.ML2Core

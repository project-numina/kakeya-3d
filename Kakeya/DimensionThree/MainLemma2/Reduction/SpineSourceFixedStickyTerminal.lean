/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceStickyInterpolation

/-!
# Sticky terminal exit on the fixed source tower

The sticky (SSF Katz--Tao) terminal branch on a `SourceThreadedTower`.
`Kakeya.ML2Core.SourceStickyFiniteReindex` and `source_exists_sticky_finite_reindex` reindex a
`ShadedUniformTubeSet` over `Fin n` preserving all quantities, so the Type-only Katz--Tao API
applies. `SourceRecordedStickyParameters` and
`source_exists_recorded_stickyKatzTao_parameters` record the usable SSF conclusion;
`source_sticky_terminal_payment` pays the terminal preparation once. The fixed-`M` theorems
`source_exists_fixed_sticky_parameters` and `source_exists_assigned_good_sticky_exit`
produce the absolute-accuracy multiplicity and mass exits, and
`source_sticky_absolute_accuracy_margin` leaves room for later payments.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube

namespace Kakeya.ML2Core

universe u

/-- A finite reindexing includes every occupied leaf and every grid node. It
preserves the actual SSF hierarchy, shading and all quantities used by Sticky. -/
structure SourceStickyFiniteReindex {iota : Type u} {delta Cu : ℝ≥0}
    (R : Finset iota) (W : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3)))
    (U : ShadedUniformTubeSet R W (ssfGridLen delta) Cu) where
  size : Nat
  decode : Fin size -> iota
  decode_injective : Function.Injective decode
  support : Finset (Fin size)
  shading : Fin size -> ShadedTube delta (EuclideanSpace ℝ (Fin 3))
  uniform : ShadedUniformTubeSet support shading (ssfGridLen delta) Cu
  support_identity : (open scoped Classical in support.image decode) = R
  shading_identity : ∀ j, shading j = W (decode j)
  nodes_identity : ∀ k, k <= ssfGridLen delta ->
    (open scoped Classical in (uniform.tubeUniform.cover.indexSet k).image decode) =
      U.tubeUniform.cover.indexSet k
  assignment_identity : ∀ k, k <= ssfGridLen delta -> ∀ j ∈ support,
    decode (uniform.tubeUniform.cover.assign k j) = U.tubeUniform.cover.assign k (decode j)
  node_tube_identity : ∀ k, k <= ssfGridLen delta ->
    ∀ j ∈ uniform.tubeUniform.cover.indexSet k,
      uniform.tubeUniform.cover.tube k j = U.tubeUniform.cover.tube k (decode j)
  tube_branching_identity : uniform.tubeUniform.branchingN = U.tubeUniform.branchingN
  shade_branching_identity : uniform.branchingN = U.branchingN
  local_branching_identity : uniform.localN = U.localN
  cardinality_identity : support.card = R.card
  mass_identity : (∑ j ∈ support, volume (shading j).shade) = ∑ i ∈ R, volume (W i).shade
  union_identity : (⋃ j ∈ support, (shading j).shade) = (⋃ i ∈ R, (W i).shade)
  fullness_identity : ShadedBody.fullness' support (fun j => (shading j).toShadedBody) =
    ShadedBody.fullness' R (fun i => (W i).toShadedBody)
  multiplicity_identity : ShadedBody.multiplicity support (fun j => (shading j).toShadedBody) =
    ShadedBody.multiplicity R (fun i => (W i).toShadedBody)
  density_identity : Kakeya.maxDensity support (fun j => (shading j).toConvexSpaceBody) =
    Kakeya.maxDensity R (fun i => (W i).toConvexSpaceBody)
  every_scale_identity : ∀ A : ℝ≥0∞,
    uniform.tubeUniform.IsKatzTaoAtEveryScale A ↔ U.tubeUniform.IsKatzTaoAtEveryScale A

/-- A literal parameter choice ed SSF Katz--Tao consequence.
This proposition is an OUTPUT of the parameter producer, never a new axiom. -/
def SourceRecordedStickyParameters (eps eta delta0 : ℝ) : Prop :=
  ∀ {delta : ℝ≥0}, 0 < delta -> (delta : ℝ) <= delta0 ->
  ∀ {iota : Type u} (R : Finset iota)
    (W : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3))),
    (∀ i ∈ R, (W i).carrier <= Metric.closedBall 0 1) ->
  ∀ {Cu : ℝ≥0} (U : ShadedUniformTubeSet R W (ssfGridLen delta) Cu),
    ENNReal.ofReal ((delta : ℝ) ^ eta) <=
      ShadedBody.fullness' R (fun i => (W i).toShadedBody) ->
    ConvexSpaceBody.IsKatzTao R (fun i => (W i).toConvexSpaceBody)
      (ENNReal.ofReal ((delta : ℝ) ^ (-eta))) ->
    U.tubeUniform.IsKatzTaoAtEveryScale (ENNReal.ofReal ((delta : ℝ) ^ (-eta))) ->
    ShadedBody.multiplicity R (fun i => (W i).toShadedBody) <=
      ENNReal.ofReal ((delta : ℝ) ^ (-eps))

/-- The exact usable SSF Katz--Tao conclusion in every finite-family universe.
Its only external dependency is the Sticky Frostman hypothesis it carries.
The baseline Type-only Katz--Tao API requires an explicit finite reindexing. -/
theorem source_exists_recorded_stickyKatzTao_parameters
    (hSFE : StickyKakeya.StickyFrostmanHypothesis.{0, 0}) {eps : ℝ} (heps : 0 < eps) :
    ∃ eta delta0 : ℝ, 0 < eta /\ 0 < delta0 /\
      ∀ {delta : ℝ≥0}, 0 < delta -> (delta : ℝ) <= delta0 ->
      ∀ {iota : Type u} (R : Finset iota)
        (W : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ R, (W i).carrier <= Metric.closedBall 0 1) ->
      ∀ {Cu : ℝ≥0} (U : ShadedUniformTubeSet R W (ssfGridLen delta) Cu),
        ENNReal.ofReal ((delta : ℝ) ^ eta) <=
          ShadedBody.fullness' R (fun i => (W i).toShadedBody) ->
        ConvexSpaceBody.IsKatzTao R (fun i => (W i).toConvexSpaceBody)
          (ENNReal.ofReal ((delta : ℝ) ^ (-eta))) ->
        U.tubeUniform.IsKatzTaoAtEveryScale
          (ENNReal.ofReal ((delta : ℝ) ^ (-eta))) ->
        ShadedBody.multiplicity R (fun i => (W i).toShadedBody) <=
          ENNReal.ofReal ((delta : ℝ) ^ (-eps)) := by
  exact StickyKakeya.stickyKatzTaoEstimate_apply.{u, 0}
    (E := EuclideanSpace ℝ (Fin 3))
    (StickyKakeya.stickyKatzTaoEstimate_of_stickyFrostmanEstimate
      (hSFE finrank_euclideanSpace_fin)) eps heps

/-- Pay terminal preparation exactly once on the same actual shaded family. -/
theorem source_sticky_terminal_payment {iota : Type u} {delta : ℝ≥0}
    {R : Finset iota} {T : iota -> Tube delta (EuclideanSpace ℝ (Fin 3))}
    {M C : Nat} (Q : SourceThreadedTower R T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3)))
    {a epsSticky : ℝ} (P : SourceStickySSFPreparation Q Z a)
    (hdelta0 : 0 < delta) (_hdelta1 : delta <= 1)
    (hsticky : ShadedBody.multiplicity P.retained (fun i => (P.shading i).toShadedBody) <=
      ENNReal.ofReal ((delta : ℝ) ^ (-epsSticky))) :
    ShadedBody.multiplicity R (fun i => (Z i).toShadedBody) <=
      ENNReal.ofReal ((delta : ℝ) ^ (-(epsSticky + a))) /\
    (∑ i ∈ R, volume (Z i).shade) <=
      ENNReal.ofReal ((delta : ℝ) ^ (-(epsSticky + a))) *
        volume (⋃ i ∈ R, (Z i).shade) := by
  have hmul : ShadedBody.multiplicity R (fun i => (Z i).toShadedBody) <=
      ENNReal.ofReal ((delta : ℝ) ^ (-(epsSticky + a))) := by
    calc
      _ <= ENNReal.ofReal ((delta : ℝ) ^ (-a)) *
          ENNReal.ofReal ((delta : ℝ) ^ (-epsSticky)) :=
        P.multiplicity.trans (mul_le_mul_right hsticky _)
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add (by exact_mod_cast hdelta0)]
        congr 2
        ring
  exact ⟨hmul, (ShadedBody.multiplicity_le_iff R (fun i => (Z i).toShadedBody)).mp hmul⟩

/-- New fixed-M theorem derived from the recorded SSF boundary, not a new
external version of source part (A). M1 and etaB precede every later M and delta.
The endpoint retains a strict positive margin after the one terminal loss. -/
theorem source_exists_fixed_sticky_parameters
    (hSFE : StickyKakeya.StickyFrostmanHypothesis.{0, 0}) (C A0 A1 : Nat)
    (hC : 1 <= C) (hA0 : 1 <= A0) (hA1 : 1 <= A1)
    {eps : ℝ} (heps : 0 < eps) (_heps1 : eps < 1) :
    ∃ (M1 : Nat) (etaB epsSticky a etaSSF deltaSSF : ℝ),
      2 <= M1 /\ 0 < etaB /\ 0 < epsSticky /\ 0 < a /\
      0 < etaSSF /\ 0 < deltaSSF /\ epsSticky + a < eps /\
      etaB + a < etaSSF /\ SourceRecordedStickyParameters.{u} epsSticky etaSSF deltaSSF /\
      ∀ M : Nat, 2 <= M -> M1 ∣ M ->
      ∃ delta0 : ℝ≥0, 0 < delta0 /\ delta0 <= 1 /\
        (delta0 : ℝ) <= deltaSSF /\
        delta0 <= (400 : ℝ≥0) ^ (-(M : ℝ)) /\
        ∀ {iota : Type u} {delta : ℝ≥0} {R : Finset iota}
          {T : iota -> Tube delta (EuclideanSpace ℝ (Fin 3))},
          0 < delta -> delta < delta0 ->
        ∀ (Q : SourceThreadedTower R T M C)
          (Z : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3))),
          SourceFixedTowerInput Q A0 A1 etaB -> SourceTowerStatistics Q Z ->
          ENNReal.ofReal ((delta : ℝ) ^ etaB) <=
            ShadedBody.fullness' R (fun i => (Z i).toShadedBody) ->
          (∀ k, k <= M -> Kakeya.maxDensity (Q.indexSet k)
            (fun j => (Q.tube k j).toConvexSpaceBody) <=
              ENNReal.ofReal ((delta : ℝ) ^ (-etaB))) ->
        ∃ P : SourceStickySSFPreparation Q Z a,
          ENNReal.ofReal ((delta : ℝ) ^ etaSSF) <=
            ShadedBody.fullness' P.retained (fun i => (P.shading i).toShadedBody) /\
          ConvexSpaceBody.IsKatzTao P.retained (fun i => (P.shading i).toConvexSpaceBody)
            (ENNReal.ofReal ((delta : ℝ) ^ (-etaSSF))) /\
          P.uniform.tubeUniform.IsKatzTaoAtEveryScale
            (ENNReal.ofReal ((delta : ℝ) ^ (-etaSSF))) /\
          ShadedBody.multiplicity P.retained (fun i => (P.shading i).toShadedBody) <=
            ENNReal.ofReal ((delta : ℝ) ^ (-epsSticky)) /\
          ShadedBody.multiplicity R (fun i => (Z i).toShadedBody) <=
            ENNReal.ofReal ((delta : ℝ) ^ (-(epsSticky + a))) /\
          (∑ i ∈ R, volume (Z i).shade) <=
            ENNReal.ofReal ((delta : ℝ) ^ (-(epsSticky + a))) *
              volume (⋃ i ∈ R, (Z i).shade) := by
  classical
  obtain ⟨etaSSF, deltaSSF, heta, hdssf, hrecord⟩ :=
    source_exists_recorded_stickyKatzTao_parameters hSFE (eps := eps / 2) (by linarith)
  obtain ⟨K, J, hK, hJ, hinterp⟩ :=
    source_exists_sticky_density_interpolation_constants C A0 A1 hC hA0 hA1
  let etaB : ℝ := min (etaSSF / 8) (1 / 2)
  let a : ℝ := min (eps / 4) (etaSSF / 8)
  have hetaB : 0 < etaB := lt_min (by positivity) (by norm_num)
  have ha : 0 < a := lt_min (by positivity) (by positivity)
  have hBa : etaB + a < etaSSF := by
    have hB := min_le_left (etaSSF / 8) (1 / 2 : ℝ)
    have hA := min_le_right (eps / 4) (etaSSF / 8)
    dsimp [etaB, a]
    linarith
  have hacc : eps / 2 + a < eps := by
    have hh := min_le_left (eps / 4) (etaSSF / 8)
    dsimp [a]
    linarith
  let M1 : Nat := max 2 (Nat.ceil (4 * (J : ℝ) / etaSSF))
  have hM1 : 2 <= M1 := le_max_left _ _
  have hsize : 4 * (J : ℝ) / etaSSF <= (M1 : ℝ) :=
    (Nat.le_ceil _).trans (by
      have hh : Nat.ceil (4 * (J : ℝ) / etaSSF) <= M1 := le_max_right _ _
      exact_mod_cast hh)
  obtain ⟨dPrep, hdPrep, hdPrep1, hPrep⟩ := source_exists_terminal_ssf_preparation 4 ha
  obtain ⟨dK, hdK, hdK1, hKabs⟩ := ML2Reduction.exists_threshold_const_le_rpow
    (A := K) (g := etaSSF / 4) (by positivity)
  obtain ⟨dCard, hdCard, hdCard1, hCardAbs⟩ := ML2Reduction.exists_threshold_const_le_rpow
    (A := ((Tube.card_le_of_densityIn_le.C 3 : ℝ≥0) : ℝ)) (g := 1) (by norm_num)
  refine ⟨M1, etaB, eps / 2, a, etaSSF, deltaSSF, hM1, hetaB, by linarith,
    ha, heta, hdssf, hacc, hBa, hrecord, ?_⟩
  intro M hM hdiv
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hMge : M1 <= M := Nat.le_of_dvd (by omega) hdiv
  have hJM : (J : ℝ) / (M : ℝ) <= etaSSF / 4 := by
    have hh : 4 * (J : ℝ) / etaSSF <= (M : ℝ) := hsize.trans (by exact_mod_cast hMge)
    rw [div_le_iff₀ heta] at hh
    rw [div_le_iff₀ hMpos]
    nlinarith
  let dS : ℝ≥0 := ⟨deltaSSF, hdssf.le⟩
  let dKr : ℝ≥0 := ⟨dK, hdK.le⟩
  let dCr : ℝ≥0 := ⟨dCard, hdCard.le⟩
  let d0 : ℝ≥0 := min dPrep (min dS (min dKr (min dCr ((400 : ℝ≥0) ^ (-(M : ℝ))))))
  have hd00 : 0 < d0 := lt_min hdPrep (lt_min hdssf (lt_min hdK (lt_min hdCard (by positivity))))
  have hd0p : d0 <= dPrep := min_le_left _ _
  have hd0s : d0 <= dS := (min_le_right _ _).trans (min_le_left _ _)
  have hd0k : d0 <= dKr := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hd0c : d0 <= dCr := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hd0t : d0 <= (400 : ℝ≥0) ^ (-(M : ℝ)) := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨d0, hd00, hd0p.trans hdPrep1, by exact_mod_cast hd0s, hd0t, ?_⟩
  intro iota delta R T hd0 hdd0 Q Z hinput hstats hfull hlevels
  have hd1 : delta <= 1 := (hdd0.le.trans hd0p).trans hdPrep1
  have hdpos : (0 : ℝ) < (delta : ℝ) := by exact_mod_cast hd0
  have hdle1 : (delta : ℝ) <= 1 := by exact_mod_cast hd1
  have hZbody : ∀ i, (Z i).toConvexSpaceBody = (T i).toConvexSpaceBody := fun i =>
    congrArg Tube.toConvexSpaceBody (hstats.same_tubes i)
  have hball : ∀ i ∈ R, (Z i).carrier <= Metric.closedBall 0 1 := by
    intro i hi
    rw [hZbody i]
    exact (hinput.geometry.original_ball i hi).trans (Metric.closedBall_subset_closedBall (by norm_num))
  have hZd : Kakeya.maxDensity R (fun i => (Z i).toConvexSpaceBody) <=
      ENNReal.ofReal ((delta : ℝ) ^ (-etaB)) := by
    simpa only [hZbody] using hinput.maximal_density
  have hcardraw : (R.card : ℝ) <=
      ((Tube.card_le_of_densityIn_le.C 3 : ℝ≥0) : ℝ) *
        (delta : ℝ) ^ (-etaB) * (delta : ℝ) ^ (-(2 : ℝ)) := by
    have hZd' : Kakeya.maxDensity R (fun i => (Z i).toConvexSpaceBody) <=
        (delta : ℝ≥0∞) ^ (-etaB) := by
      rw [← ENNReal.ofReal_rpow_of_pos hdpos] at hZd
      simpa only [ENNReal.ofReal_coe_nnreal] using hZd
    have hraw := Tube.card_le_of_densityIn_le (E := EuclideanSpace ℝ (Fin 3))
      (δ := delta) (s := R) (T := fun i => (Z i).toTube) hd0.ne' hball
      ((Kakeya.le_maxDensity R (fun i => (Z i).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall).trans hZd')
    have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
    rw [hn] at hraw
    norm_num at hraw
    have hzpow : (delta : ℝ≥0∞) ^ (-2 : Int) = (delta : ℝ≥0∞) ^ (-2 : ℝ) := by
      rw [← ENNReal.rpow_intCast]
      norm_num
    rw [hzpow, ← ENNReal.coe_rpow_of_ne_zero hd0.ne' (-etaB),
      ← ENNReal.coe_rpow_of_ne_zero hd0.ne' (-2 : ℝ), ← ENNReal.coe_mul,
      ← ENNReal.coe_mul, show (R.card : ℝ≥0∞) = ((R.card : ℝ≥0) : ℝ≥0∞) by simp,
      ENNReal.coe_le_coe, ← NNReal.coe_le_coe] at hraw
    simpa [NNReal.coe_rpow] using hraw
  have hcard : (R.card : ℝ) <= (delta : ℝ) ^ (-(4 : ℝ)) := by
    have hconst := hCardAbs (delta : ℝ) hdpos (by exact_mod_cast hdd0.le.trans hd0c)
    have hB1 : etaB <= 1 := (min_le_right _ _).trans (by norm_num)
    calc
      _ <= ((Tube.card_le_of_densityIn_le.C 3 : ℝ≥0) : ℝ) *
          (delta : ℝ) ^ (-etaB) * (delta : ℝ) ^ (-(2 : ℝ)) := hcardraw
      _ <= (delta : ℝ) ^ (-(1 : ℝ)) * (delta : ℝ) ^ (-etaB) *
          (delta : ℝ) ^ (-(2 : ℝ)) := by gcongr
      _ = (delta : ℝ) ^ (-(3 + etaB)) := by
        rw [← Real.rpow_add hdpos, ← Real.rpow_add hdpos]
        congr 1
        ring
      _ <= _ := Real.rpow_le_rpow_of_exponent_ge hdpos hdle1 (by linarith)
  have hmass : 0 < ∑ i ∈ R, volume (Z i).shade := by
    have hfp : 0 < ShadedBody.fullness' R (fun i => (Z i).toShadedBody) :=
      (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hdpos _)).trans_le hfull
    exact pos_iff_ne_zero.mpr fun hz => by simp [ShadedBody.fullness', hz] at hfp
  obtain ⟨P⟩ := hPrep hd0 (hdd0.trans_le hd0p) hinput.geometry.nonempty Q Z hstats hball
    (by simpa using hcard) hmass
  have hPlower : ENNReal.ofReal ((delta : ℝ) ^ (etaB + a)) <=
      ShadedBody.fullness' P.retained (fun i => (P.shading i).toShadedBody) := by
    have hh := mul_le_mul_right (hfull.trans P.fullness)
      (ENNReal.ofReal ((delta : ℝ) ^ a))
    have hcancel : ENNReal.ofReal ((delta : ℝ) ^ a) *
        ENNReal.ofReal ((delta : ℝ) ^ (-a)) = 1 := by
      rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add hdpos]
      simp
    rw [← mul_assoc, hcancel, one_mul] at hh
    simpa only [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) <= (delta : ℝ) ^ a),
      ← Real.rpow_add hdpos, add_comm a etaB] using hh
  have hPfull : ENNReal.ofReal ((delta : ℝ) ^ etaSSF) <=
      ShadedBody.fullness' P.retained (fun i => (P.shading i).toShadedBody) :=
    (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hdpos hdle1 hBa.le)).trans hPlower
  have hPbody : ∀ i, (P.shading i).toConvexSpaceBody = (T i).toConvexSpaceBody := fun i =>
    congrArg Tube.toConvexSpaceBody (P.tube_identity i)
  have hPd : ConvexSpaceBody.IsKatzTao P.retained (fun i => (P.shading i).toConvexSpaceBody)
      (ENNReal.ofReal ((delta : ℝ) ^ (-etaSSF))) := by
    rw [ConvexSpaceBody.IsKatzTao_def]
    simp only [hPbody]
    refine ((Kakeya.maxDensity_mono _ P.subset).trans hinput.maximal_density).trans ?_
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hdpos hdle1 (by linarith [ha]))
  have hH1 : (1 : ℝ≥0∞) <= ENNReal.ofReal ((delta : ℝ) ^ (-etaB)) := by
    have hh := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hdpos hdle1 (neg_nonpos.mpr hetaB.le)
    simpa using ENNReal.ofReal_le_ofReal hh
  have hPi := hinterp hM hd0 (hdd0.trans_le hd0t) Q hinput.geometry
    (ENNReal.ofReal ((delta : ℝ) ^ (-etaB))) hH1 ENNReal.ofReal_ne_top hlevels
    P.retained P.subset P.shading P.tube_identity P.uniform P.occupied
  have hPscale : P.uniform.tubeUniform.IsKatzTaoAtEveryScale
      (ENNReal.ofReal ((delta : ℝ) ^ (-etaSSF))) := by
    refine hPi.mono ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hconst := hKabs (delta : ℝ) hdpos (by exact_mod_cast hdd0.le.trans hd0k)
    calc
      _ <= ((delta : ℝ) ^ (-(etaSSF / 4)) *
          (delta : ℝ) ^ (-((J : ℝ) / (M : ℝ)))) * (delta : ℝ) ^ (-etaB) := by gcongr
      _ = (delta : ℝ) ^ (-(etaSSF / 4 + (J : ℝ) / (M : ℝ) + etaB)) := by
        rw [← Real.rpow_add hdpos, ← Real.rpow_add hdpos]
        congr 1
        ring
      _ <= _ := Real.rpow_le_rpow_of_exponent_ge hdpos hdle1 (by
        have hh : etaB <= etaSSF / 8 := min_le_left _ _
        linarith)
  have hPsticky := hrecord hd0 (by exact_mod_cast hdd0.le.trans hd0s)
    P.retained P.shading P.ball P.uniform hPfull hPd hPscale
  have hpaid := source_sticky_terminal_payment Q Z P hd0 hd1 hPsticky
  exact ⟨P, hPfull, hPd, hPscale, hPsticky, hpaid.1, hpaid.2⟩

/-- Actual absolute-accuracy exit from the SAME fixed-Q assigned good array.
The finite B-power is absorbed only after N, B and the positive exponent margin
are fixed; neither the tower nor its potential is replaced at a restart. -/
theorem source_exists_assigned_good_sticky_exit
    (hSFE : StickyKakeya.StickyFrostmanHypothesis.{0, 0}) (C A0 A1 : Nat)
    (hC : 1 <= C) (hA0 : 1 <= A0) (hA1 : 1 <= A1)
    {accuracy : ℝ} (haccuracy : 0 < accuracy) (haccuracy1 : accuracy < 1) :
    ∃ (M1 : Nat) (etaB : ℝ), 2 <= M1 /\ 0 < etaB /\
      ∀ M : Nat, 2 <= M -> M1 ∣ M ->
      ∀ (N : Nat) (B : ℝ≥0) (e eta0 : ℝ),
        1 <= B -> 0 < e -> 5 * e < etaB -> 0 < eta0 -> 3 * eta0 <= etaB ->
      ∃ delta0 : ℝ≥0, 0 < delta0 /\ delta0 <= 1 /\
        delta0 <= (400 : ℝ≥0) ^ (-(M : ℝ)) /\
        ∀ {iota : Type u} {delta : ℝ≥0} {R : Finset iota}
          {T : iota -> Tube delta (EuclideanSpace ℝ (Fin 3))},
          0 < delta -> delta < delta0 ->
        ∀ (Q : SourceThreadedTower R T M C)
          (Z : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3))),
          SourceFixedTowerInput Q A0 A1 eta0 -> SourceTowerStatistics Q Z ->
          ENNReal.ofReal ((delta : ℝ) ^ (3 * eta0)) <=
            ShadedBody.fullness' R (fun i => (Z i).toShadedBody) ->
          SourceFixedKTArrayGood Q B N e ->
          ShadedBody.multiplicity R (fun i => (Z i).toShadedBody) <=
            ENNReal.ofReal ((delta : ℝ) ^ (-accuracy)) /\
          (∑ i ∈ R, volume (Z i).shade) <=
            ENNReal.ofReal ((delta : ℝ) ^ (-accuracy)) *
              volume (⋃ i ∈ R, (Z i).shade) := by
  obtain ⟨M1, etaB, epsSticky, a, etaSSF, deltaSSF, hM1, hetaB, hepsSticky, ha,
    hetaSSF, hdeltaSSF, hmargin, hgapSSF, hrecord, hfixed⟩ :=
    source_exists_fixed_sticky_parameters hSFE C A0 A1 hC hA0 hA1 haccuracy haccuracy1
  refine ⟨M1, etaB, hM1, hetaB, ?_⟩
  intro M hM hdiv N B e eta0 hB he hegap heta0 hetagap
  obtain ⟨d0, hd0, hd1, hdSSF, hdtower, happly⟩ := hfixed M hM hdiv
  let L : ℝ≥0 := (1280 ^ 6 : ℝ≥0) * B ^ (N + 1)
  obtain ⟨dB, hdB, hdB1, hBabs⟩ := ML2Reduction.exists_threshold_const_le_rpow
    (A := (L : ℝ)) (g := etaB - 5 * e) (by linarith)
  let dBN : ℝ≥0 := ⟨dB, hdB.le⟩
  refine ⟨min d0 dBN, lt_min hd0 hdB, (min_le_left _ _).trans hd1,
    (min_le_left _ _).trans hdtower, ?_⟩
  intro iota delta R T hdelta0 hdelta Q Z hinput hstats hfull hgood
  have hdelta1 : delta <= 1 := (hdelta.le.trans (min_le_left _ _)).trans hd1
  have hdpos : (0 : ℝ) < (delta : ℝ) := by exact_mod_cast hdelta0
  have hdle1 : (delta : ℝ) <= 1 := by exact_mod_cast hdelta1
  have hinput' : SourceFixedTowerInput Q A0 A1 etaB := {
    geometry := hinput.geometry
    neighbour_sharing := hinput.neighbour_sharing
    maximal_density := hinput.maximal_density.trans
      (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hdpos hdle1 (by linarith)))
  }
  have hfull' : ENNReal.ofReal ((delta : ℝ) ^ etaB) <=
      ShadedBody.fullness' R (fun i => (Z i).toShadedBody) :=
    (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hdpos hdle1 hetagap)).trans hfull
  have hlevels := source_sticky_level_density_of_assigned_good Q hM hinput.geometry hB he.le
    hdelta0 hdelta1 hgood
  have hlevels' : ∀ k, k <= M -> Kakeya.maxDensity (Q.indexSet k)
      (fun i => (Q.tube k i).toConvexSpaceBody) <= ENNReal.ofReal ((delta : ℝ) ^ (-etaB)) := by
    intro k hk
    refine (hlevels k hk).trans ?_
    have hconst := hBabs (delta : ℝ) hdpos (by exact_mod_cast hdelta.le.trans (min_le_right _ _))
    have hbound : (L : ℝ) * (delta : ℝ) ^ (-(5 * e)) <= (delta : ℝ) ^ (-etaB) := by
      calc
        _ <= (delta : ℝ) ^ (-(etaB - 5 * e)) * (delta : ℝ) ^ (-(5 * e)) := by gcongr
        _ = _ := by
          rw [← Real.rpow_add hdpos]
          congr 1
          ring
    have hLE : ENNReal.ofReal (L : ℝ) = (1280 ^ 6 : ℝ≥0∞) * (B : ℝ≥0∞) ^ (N + 1) := by
      simp [L]
    rw [← hLE, ← ENNReal.ofReal_mul (NNReal.coe_nonneg L)]
    exact ENNReal.ofReal_le_ofReal hbound
  obtain ⟨P, hPfull, hPd, hPscale, hPsticky, hmult, hmass⟩ :=
    happly hdelta0 (hdelta.trans_le (min_le_left _ _)) Q Z hinput' hstats hfull' hlevels'
  have hpay : ENNReal.ofReal ((delta : ℝ) ^ (-(epsSticky + a))) <=
      ENNReal.ofReal ((delta : ℝ) ^ (-accuracy)) :=
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hdpos hdle1 (by linarith))
  exact ⟨hmult.trans hpay, hmass.trans (mul_le_mul_left hpay _)⟩

end Kakeya.ML2Core

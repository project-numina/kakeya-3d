/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Bootstrap
public import Kakeya.FrostmanTransfer
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.TrialGeometryEntryW96
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceSameMassOuterFullnessW100
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourcePassNumericsConstructionW104
public import Kakeya.DimensionThree.MainLemma1.Factoring
public import Kakeya.RelativePlank
public import Kakeya.Factoring.Pigeonhole
public import Kakeya.DimensionThree.MainLemma1.Cases
public import Kakeya.DimensionThree.MainLemma1.Setup
public import Kakeya.DimensionThree.MainLemma1.Rescaling.MiddleAverage
public import Kakeya.DimensionThree.MainLemma1.ScalarFactorization
public import Kakeya.DimensionThree.MainLemma1.AnalyticEndgame
public import Kakeya.DimensionThree.MainLemma1.CoarseBallUpstreamW50
public import Kakeya.Factoring.DilatedTubePresentation
public import Kakeya.DimensionThree.MainLemma1.ParentConflictCover
public import Kakeya.DimensionThree.MainLemma1.Rescaling.KatzTao
public import Kakeya.Factoring.WeightedFullness
public import Kakeya.DimensionThree.MainLemma1.NoEDHonestCoarseConsumerW52
public import Kakeya.DimensionThree.MainLemma1.ThreePass
public import Kakeya.DimensionThree.MainLemma1.W44NormalizationCardPort
public import Kakeya.MultiScaleFac
public import Kakeya.Asymptotics
public import Kakeya.DimensionThree.MainLemma1.UpstreamCountedRawProducerW50Module
public import Kakeya.Multiplicity
public import Kakeya.Tube.Rigidity
public import Kakeya.DimensionThree.MainLemma1.Rescaling.CoarseDensity
public import Kakeya.DimensionThree.MainLemma1.CoarseFibre
public import Kakeya.Factoring.RhoTubes
public import Kakeya.Tube.Dilate
public import Kakeya.Factoring.RhoTubesUndilated
public import Kakeya.DimensionThree.MainLemma1.W44NoEDNormalization
public import Kakeya.DimensionThree.MainLemma1.Rescaling.Numerics
public import Kakeya.DimensionThree.MainLemma1.Rescaling.BallRadius
public import Kakeya.Factoring.RhoFreeParentCount
public import Kakeya.DimensionThree.MainLemma1.EndpointHierarchySelectedPacketModuleSafeW53
public import Kakeya.DimensionThree.MainLemma1.EndpointPacketHierarchyModuleBridgeSafeW48
public import Kakeya.DimensionThree.MainLemma1.EndpointMiddleSplitModuleSafeW53
public import Kakeya.DimensionThree.MainLemma1.Rescaling.UniformEveryScale
public import Kakeya.DimensionThree.MainLemma1.QuotientAwareQV5W58
public import Kakeya.DimensionThree.MainLemma1.Envelope
public import Kakeya.DimensionThree.MainLemma1.Rescaling.Thresholds
public import Kakeya.StickyKakeya.BallReduction
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceConstructionDefinitionsW97
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceQuotientGridW97
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceWindowTrialW98
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceTerminalOriginalInputW104
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceCentringReductionProofW102
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.CentringBandDensityW103
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.ProtectedLineBudgetW103
public import Kakeya.DimensionThree.FrostmanEstimateOne

/-!
# The revised-source entry to Main Lemma 1

The top of the revised-source tower.  In `Kakeya.ml1Boot.RevisedSourceRepairW110`:
`StickyWitnessW110` (from `StickyKakeya.StickyFrostmanEstimate`), `SourceStructureW110`
(the `Params` carrier with the source ladder inequalities and step `p.c`),
`AnalyticScheduleW110` and `InputChoiceW110` (analytic thresholds and the working/input
exponents, chosen before `delta` and the family), the hypothesis packages `OriginalInputW110`
and `BandedInputW110`, and the certified output `OriginalRunW110`.  The main producer is
`exists_certified_original_runs_w110`, which runs the same-mass two-scale construction
(`exists_same_mass_balanced_selections_w110`), the eligible Inner Trial calls, the persistent
canonical restart and the final exponent payment; `original_run_transport_w110` converts a run
into the multiplicity bound, and `source_structure_gives_frostman_w110` yields
`FrostmanEstimate E (gamma - G.p.c)`.  The namespace `Kakeya.ml1Boot.FixedMStickyExitW110`
holds `mixed_grid_frostman_transfer_w110` and `eventually_fixed_m_sticky_exit_w110`.  The file
ends with the public boundary: `exists_uniform_step_general_from_revised_w110`, its
dimension-three specialisation, the monotone step function, and
`frostmanEstimate_from_revised_w110`, the Main Lemma 1 statement on `EuclideanSpace Real (Fin 3)`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ConvexSpaceBody ShadedBody Filter
open scoped ENNReal NNReal Topology

namespace Kakeya.ml1Boot.RevisedSourceRepairW110

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

universe uE uI

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open TrialRestartW94

/-- A genuine sticky theorem witness, selected before the ladder and gamma. -/
structure StickyWitnessW110 (E : Type uE) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (gammaZero : ℝ) where
  etaStar : ℝ
  etaStar_pos : 0 < etaStar
  actual_sticky :
    ∀ᶠ (delta : ℝ≥0) in 𝓝[>] 0,
      ∀ {iota : Type uI} (s : Finset iota) (Y : iota -> ShadedTube delta E),
        (∀ i ∈ s, (Y i).carrier ⊆ Metric.closedBall 0 1) ->
        ∀ {C : ℝ≥0}, C <= ShadedTube.ssfUniformConst (Module.finrank ℝ E) ->
        ∀ U : ShadedTube.ShadedUniformTubeSet s Y (Tube.ssfGridLen delta) C,
          (delta : ℝ≥0∞) ^ etaStar <=
            (ShadedBody.fullness s (fun i => (Y i).toShadedBody) : ℝ≥0∞) ->
          U.tubeUniform.IsFrostmanAtEveryScale ((delta : ℝ≥0∞) ^ (-etaStar)) ->
          (delta : ℝ≥0∞) ^ (gammaZero / 4) <= volume (⋃ i ∈ s, (Y i).shade)

theorem exists_sticky_witness_w110
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{uE, uI} (E := E))
    {gammaZero : ℝ} (hgammaZero : 0 < gammaZero) :
    Nonempty (StickyWitnessW110.{uE, uI} E gammaZero) := by
  obtain ⟨eta, heta, hactual⟩ :=
    StickyKakeya.volume_iUnionShade_ge_of_isFrostmanAtEveryScale (E := E) hSFE
      (show 0 < gammaZero / 4 by positivity)
  refine ⟨{ etaStar := eta, etaStar_pos := heta, actual_sticky := ?_ }⟩
  filter_upwards [hactual] with delta hdelta
  intro iota s Y hball C hC U hfull hCF
  apply hdelta s Y hball hC U _ hCF
  apply ENNReal.coe_le_coe.mp
  simpa only [ENNReal.coe_rpow_of_nonneg _ heta.le] using hfull

/-- The existing Params type is only a carrier of N, epsilon and zeta.
This package does NOT assert Params.Spec or certify p.etaGamma. The source
ladder inequalities and the source step replace those claims explicitly. -/
structure SourceStructureW110 (beta gammaZero etaStar : ℝ) where
  p : Params
  xi : Fin (p.N + 1) -> ℝ
  xiMin : ℝ
  M : Nat
  numerics : SourcePassNumericsW95 p (betaPrime beta gammaZero) gammaZero xi xiMin M
  etaStar_eq : p.ηStar = etaStar
  sticky_margin : 5 * p.ε <= etaStar / 4
  step_eq : p.c = min (min xiMin (gammaZero / 4))
    ((gammaZero - betaPrime beta gammaZero) / 2)

/-- Choose all structural data before gamma, hKT, hKF and requested loss.
The shifted beta is fixed at gammaZero, covering the public beta = 0 case. -/
theorem exists_source_structure_w110
    {beta gammaZero etaStar : ℝ} (hbeta : 0 <= beta)
    (hgammaZero : gammaZero ∈ Set.Ioc beta 1) (hetaStar : 0 < etaStar) :
    Nonempty (SourceStructureW110 beta gammaZero etaStar) := by
  have hgammaPos : 0 < gammaZero := hbeta.trans_lt hgammaZero.1
  have hbp : 0 < betaPrime beta gammaZero :=
    (half_pos hgammaPos).trans_le (le_max_right _ _)
  have hbpGap : betaPrime beta gammaZero < gammaZero :=
    max_lt hgammaZero.1 (half_lt_self hgammaPos)
  obtain ⟨p, xi, xiMin, M, hp, heps⟩ :=
    exists_source_pass_numerics_w104 hbp hbpGap hgammaZero.2
      (show 0 < etaStar / 20 by positivity)
  let p' : Params := { p with
    ηStar := etaStar
    c := min (min xiMin (gammaZero / 4)) ((gammaZero - betaPrime beta gammaZero) / 2) }
  refine ⟨{
    p := p'
    xi := xi
    xiMin := xiMin
    M := M
    numerics := ?_
    etaStar_eq := rfl
    sticky_margin := ?_
    step_eq := rfl }⟩
  · exact {
      beta_pos := hp.beta_pos
      gammaZero_gt := hp.gammaZero_gt
      gammaZero_le := hp.gammaZero_le
      N_large := hp.N_large
      epsilon_eq := hp.epsilon_eq
      epsilon_pos := hp.epsilon_pos
      epsilon_small := hp.epsilon_small
      gap := hp.gap
      zeta_pos := hp.zeta_pos
      zeta_mono := hp.zeta_mono
      zeta_top := hp.zeta_top
      xi_pos := hp.xi_pos
      xi_beta := hp.xi_beta
      xi_next := hp.xi_next
      rung_next := hp.rung_next
      rung_xi := hp.rung_xi
      xiMin_pos := hp.xiMin_pos
      xiMin_lower := hp.xiMin_lower
      xiMin_attained := hp.xiMin_attained
      M_pos := hp.M_pos
      M_zeta := hp.M_zeta
      M_xi := hp.M_xi
      M_profile := hp.M_profile
      M_next := hp.M_next }
  · change 5 * p.ε <= etaStar / 4
    linarith only [heps]

theorem shifted_estimate_for_source_w110 [Nontrivial E]
    {beta gammaZero : ℝ} (hbeta : 0 <= beta)
    (hgammaZero : gammaZero ∈ Set.Ioc beta 1)
    (hKT : KatzTaoEstimate.{uI} E beta) :
    0 < betaPrime beta gammaZero ∧ betaPrime beta gammaZero < gammaZero ∧
      KatzTaoEstimate.{uI} E (betaPrime beta gammaZero) := by
  have hgammaPos : 0 < gammaZero := hbeta.trans_lt hgammaZero.1
  exact ⟨(half_pos hgammaPos).trans_le (le_max_right _ _),
    max_lt hgammaZero.1 (half_lt_self hgammaPos), hKT.mono (le_max_left _ _)⟩

theorem source_step_positive_w110
    {beta gammaZero etaStar : ℝ} (G : SourceStructureW110 beta gammaZero etaStar) :
    0 < G.p.c ∧ G.p.c <= 1 ∧ G.p.c <= gammaZero / 4 ∧
      G.p.c <= G.xiMin ∧ G.p.c < gammaZero - betaPrime beta gammaZero := by
  have hgammaPos : 0 < gammaZero := G.numerics.beta_pos.trans G.numerics.gammaZero_gt
  have hgap : 0 < gammaZero - betaPrime beta gammaZero := sub_pos.mpr G.numerics.gammaZero_gt
  rw [G.step_eq]
  have hx : min (min G.xiMin (gammaZero / 4))
      ((gammaZero - betaPrime beta gammaZero) / 2) <= min G.xiMin (gammaZero / 4) :=
    min_le_left _ _
  have hg := hx.trans (min_le_right _ _)
  refine ⟨lt_min (lt_min G.numerics.xiMin_pos (by positivity)) (half_pos hgap),
    hg.trans ?_, hg, hx.trans (min_le_left _ _), ?_⟩
  · linarith only [G.numerics.gammaZero_le]
  · exact (min_le_right _ _).trans_lt (half_lt_self hgap)

/-- The full family-uniform KT conclusion at the returned threshold.
The all-indices ball condition is exactly the production lemma's condition. -/
def ActualKTThresholdW110 (beta loss eta : ℝ) : Prop :=
  ∀ᶠ (delta : ℝ≥0) in 𝓝[>] 0,
    ∀ {iota : Type uI} (s : Finset iota) (Y : iota -> ShadedTube delta E),
      (∀ i, (Y i).carrier ⊆ Metric.closedBall 0 1) ->
      (delta : ℝ) ^ eta <=
        (ShadedBody.fullness s (fun i => (Y i).toShadedBody) : ℝ) ->
      ShadedBody.multiplicity s (fun i => (Y i).toShadedBody) <=
        (delta : ℝ≥0∞) ^ (-loss) *
          (Kakeya.maxDensity s (fun i => (Y i).toConvexSpaceBody)) ^ (1 - beta) *
          (s.card : ℝ≥0∞) ^ beta

/-- The actual auxiliary-scale KF conclusion, including CF of this family.
eta and the reference-scale cutoff precede rho and the family. -/
def ActualKFThresholdW110 (gamma loss eta : ℝ) : Prop :=
  ∀ᶠ (delta : ℝ≥0) in 𝓝[>] 0,
    ∀ rho : ℝ≥0, delta <= rho -> rho <= 1 ->
    ∀ {iota : Type uI} (s : Finset iota) (Y : iota -> ShadedTube rho E),
      s.Nonempty ->
      (∀ i ∈ s, (Y i).carrier ⊆ Metric.closedBall 0 1) ->
      (s : Set iota).Pairwise
        (fun i j => IsEssentiallyDistinct (Y i).carrier (Y j).carrier) ->
      (delta : ℝ≥0∞) ^ eta <=
        (ShadedBody.fullness s (fun i => (Y i).toShadedBody) : ℝ≥0∞) ->
      ShadedBody.multiplicity s (fun i => (Y i).toShadedBody) <=
        (delta : ℝ≥0∞) ^ (-loss) *
          frostmanConstIn s (fun i => (Y i).toConvexSpaceBody)
            ConvexSpaceBody.closedUnitBall ^ (1 - gamma / 2) *
          (rho : ℝ≥0∞) ^ (-2 * gamma) *
          ((s.card : ℝ≥0∞) * (rho : ℝ≥0∞) ^
            (Module.finrank ℝ E - 1)) ^ (1 - gamma / 2)

/-- Full analytic witnesses, not positive functions standing for witnesses.
The geometry constants are parameters: they precede every threshold. -/
structure AnalyticScheduleW110 [Nontrivial E]
    {beta gammaZero etaStar : ℝ} (G : SourceStructureW110 beta gammaZero etaStar)
    (gamma : ℝ) (Ctw Ccell : ℝ≥0) where
  etaKT : ℝ
  etaKF : ℝ
  etaKT_pos : 0 < etaKT
  etaKF_pos : 0 < etaKF
  actual_KT : ActualKTThresholdW110.{uE, uI} (E := E)
    (betaPrime beta gammaZero) (G.p.η 0) etaKT
  actual_KF : ActualKFThresholdW110.{uE, uI} (E := E) gamma (G.p.η 0) etaKF
  inner : LabelledDetailedTrialThresholdsW94.{uE, uI} (E := E)
    G.p G.xi gamma Ctw Ccell G.M
  auxiliary : AuxiliaryHalfEtaThresholdsW97.{uE, uI} (E := E)
    G.p G.xi gamma Ctw Ccell G.M
  inner_window : ∀ m : Fin (G.p.N + 1), m.val < G.p.N ->
    windowDetailedTrialAtThresholdW98.{uE, uI} (E := E) gamma G.p.ε (G.xi m)
      (G.p.η (m.val + 1)) Ctw Ccell G.M
      (inner.inner m) (inner.cutoff m) (inner.Ktr m)
  auxiliary_window : ∀ m : Fin (G.p.N + 1), m.val < G.p.N ->
    windowDetailedTrialAtThresholdW98.{uE, uI} (E := E) gamma G.p.ε (G.xi m)
      (G.p.η (m.val + 1) / 2) Ctw Ccell G.M
      (auxiliary.inner m) (auxiliary.cutoff m) (auxiliary.Ktr m)

/-- Package the proved window-aware trial at both rung choices and the
actual KT/KF witnesses. -/
theorem exists_actual_analytic_schedule_w110 [Nontrivial E]
    (hdim : Module.finrank ℝ E = 3)
    {beta gammaZero etaStar : ℝ} (G : SourceStructureW110 beta gammaZero etaStar)
    {gamma : ℝ} (hgamma : gamma ∈ Set.Icc gammaZero 1)
    (hKT : KatzTaoEstimate.{uI} E beta) (hKF : FrostmanEstimate.{uI} E gamma)
    (Ctw Ccell : ℝ≥0) (hCtw : 1 <= Ctw) (hCcell : 1 <= Ccell) :
    Nonempty (AnalyticScheduleW110.{uE, uI} (E := E) G gamma Ctw Ccell) := by
  classical
  let p := G.p
  let betaS := betaPrime beta gammaZero
  let xi := G.xi
  let M := G.M
  have hp : SourcePassNumericsW95 p betaS gammaZero xi G.xiMin M := G.numerics
  have hKT' : KatzTaoEstimate.{uI} E betaS := hKT.mono (le_max_left _ _)
  have hbetagamma : betaS < gamma := hp.gammaZero_gt.trans_le hgamma.1
  have hgap : 3 * p.ε / 2 <= (gamma - betaS) / 1000 := by
    linarith only [hp.gap, hgamma.1]
  have heps32 : 32 * p.ε <= 1 := by
    linarith only [hp.gap, hp.gammaZero_le, hp.beta_pos]
  have heps1 : p.ε <= 1 := hp.epsilon_small.le.trans (by norm_num)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hp.M_pos
  have hdenom : 0 < p.ε ^ 2 * betaS := mul_pos (sq_pos_of_pos hp.epsilon_pos) hp.beta_pos
  have hnext : ∀ m : Fin (p.N + 1), m.val < p.N ->
      4000 * xi m / (p.ε ^ 2 * betaS) <= p.η (m.val + 1) / 2 := by
    intro m hm
    apply (div_le_iff₀ hdenom).mpr
    nlinarith only [hp.xi_next m hm]
  have hMmin : ∀ m : Fin (p.N + 1), m.val < p.N ->
      (1 : ℝ) / M <= min (xi m) p.ε / 100 := by
    intro m hm
    have hxiMin1 : G.xiMin <= 1 := by
      obtain ⟨k, hk, hkMin⟩ := hp.xiMin_attained
      have hbeta1 : betaS <= 1 := hp.gammaZero_gt.le.trans hp.gammaZero_le
      have heps3 : p.ε ^ 3 <= 1 := pow_le_one₀ hp.epsilon_pos.le heps1
      have hprod : p.ε ^ 3 * betaS <= 1 := mul_le_one₀ heps3 hp.beta_pos.le hbeta1
      rw [← hkMin]
      nlinarith only [hp.xi_beta k hk, hprod]
    have hleft : p.ε * G.xiMin / 200 <= xi m / 100 := by
      have hprod : p.ε * G.xiMin <= G.xiMin :=
        mul_le_of_le_one_left hp.xiMin_pos.le heps1
      linarith only [hprod, hp.xiMin_lower m hm, hp.xi_pos m hm]
    have hright : p.ε * G.xiMin / 200 <= p.ε / 100 := by
      have hprod : p.ε * G.xiMin <= p.ε :=
        mul_le_of_le_one_right hp.epsilon_pos.le hxiMin1
      linarith only [hprod, hp.epsilon_pos]
    rw [← min_div_div_right (by norm_num : (0 : ℝ) <= 100)]
    exact le_min (hp.M_xi.trans hleft) (hp.M_xi.trans hright)
  have hMhalf : ∀ m : Fin (p.N + 1), m.val < p.N ->
      (160000 : ℝ) / (p.ε * (p.η (m.val + 1) / 2)) <= M := by
    intro m hm
    have hz : 0 < p.η (m.val + 1) := hp.zeta_pos _ (by omega)
    have hzero : p.η 0 <= p.ε * p.η (m.val + 1) / 100 :=
      (hp.zeta_mono 0 m.val (Nat.zero_le _) (by omega)).trans (hp.rung_next m.val hm)
    have hmul := mul_le_mul_of_nonneg_left hzero hp.epsilon_pos.le
    have hmargin := mul_le_mul_of_nonneg_right heps32 (mul_nonneg hp.epsilon_pos.le hz.le)
    have hsmall : (1 : ℝ) / M <= p.ε * p.η (m.val + 1) / 320000 := by
      nlinarith only [hp.M_zeta, hmul, hmargin]
    apply (div_le_iff₀ (mul_pos hp.epsilon_pos (half_pos hz))).mpr
    have hsmall' := (div_le_iff₀ hMpos).mp hsmall
    nlinarith only [hsmall']
  have hlabels : ∀ (half : Bool) (m : Fin (p.N + 1)),
      ∃ (inner : ℝ) (cutoff : ℝ≥0) (Ktr : Nat),
        0 < inner ∧ 0 < cutoff ∧ cutoff < 1 ∧ 1 <= Ktr ∧
        (m.val < p.N -> windowDetailedTrialAtThresholdW98.{uE, uI} (E := E)
          gamma p.ε (xi m) (if half then p.η (m.val + 1) / 2 else p.η (m.val + 1))
          Ctw Ccell M inner cutoff Ktr) := by
    intro half m
    by_cases hm : m.val < p.N
    · have hz : 0 < p.η (m.val + 1) := hp.zeta_pos _ (by omega)
      have hzlower : p.η (m.val + 1) / 2 <=
          (if half then p.η (m.val + 1) / 2 else p.η (m.val + 1)) := by
        cases half <;> simp only [Bool.false_eq_true, reduceIte] <;> linarith only [hz]
      have hzpos := (half_pos hz).trans_le hzlower
      have hscale : (160000 : ℝ) /
          (p.ε * (if half then p.η (m.val + 1) / 2 else p.η (m.val + 1))) <= M :=
        (div_le_div_of_nonneg_left (by norm_num)
          (mul_pos hp.epsilon_pos (half_pos hz))
          (mul_le_mul_of_nonneg_left hzlower hp.epsilon_pos.le)).trans (hMhalf m hm)
      obtain ⟨inner, cutoff, Ktr, hinner, hcutoff, hcutoff1, hKtr, htrial⟩ :=
        exists_literal_window_trial_threshold_w98 hdim betaS gamma p.ε (xi m)
          (if half then p.η (m.val + 1) / 2 else p.η (m.val + 1))
          hp.beta_pos hbetagamma hgamma.2 hp.epsilon_pos hp.epsilon_small hgap
          (hp.xi_pos m hm) (hp.xi_beta m hm) ((hnext m hm).trans hzlower)
          Ctw Ccell hCtw hCcell M hp.M_pos (hMmin m hm) hscale hKT' hKF
      exact ⟨inner, cutoff, Ktr, hinner, hcutoff, hcutoff1, hKtr, fun _ => htrial⟩
    · exact ⟨1, 1 / 2, 1, by norm_num, by norm_num, by norm_num, le_rfl,
        fun hm' => (hm hm').elim⟩
  choose inner cutoff Ktr hinner hcutoff hcutoff1 hKtr htrial using hlabels
  let full : LabelledDetailedTrialThresholdsW94.{uE, uI} (E := E)
      p xi gamma Ctw Ccell M :=
    { inner := inner false, cutoff := cutoff false, Ktr := Ktr false,
      inner_pos := hinner false, cutoff_pos := hcutoff false,
      cutoff_lt_one := hcutoff1 false, Ktr_pos := hKtr false,
      actual_trial := by
        intro m hm d hd hd0 iota inst F Y rho cells input
        rcases htrial false m hm hd hd0 F Y rho cells input with hg | hd
        · exact Or.inl hg
        · exact Or.inr (hd.map fun drop => drop.toDetailedTrialDropW94) }
  let aux : AuxiliaryHalfEtaThresholdsW97.{uE, uI} (E := E)
      p xi gamma Ctw Ccell M :=
    { inner := inner true, cutoff := cutoff true, Ktr := Ktr true,
      inner_pos := hinner true, cutoff_pos := hcutoff true,
      cutoff_lt_one := hcutoff1 true, Ktr_pos := hKtr true,
      actual_trial := by
        intro m hm d hd hd0 iota inst F Y rho cells input
        rcases htrial true m hm hd hd0 F Y rho cells input with hg | hd
        · exact Or.inl hg
        · exact Or.inr (hd.map fun drop => drop.toDetailedTrialDropW94) }
  have heta : 0 < p.η 0 := hp.zeta_pos 0 (Nat.zero_le _)
  obtain ⟨etaKT, hetaKT, hactualKT⟩ :=
    KatzTaoEstimate.multiplicity_bound_generalize (E := E) hp.beta_pos.le hKT' (p.η 0) heta
  obtain ⟨etaKF, hetaKF, hactualKF⟩ :=
    FrostmanEstimate.multiplicity_bound_auxScale E
      (hp.beta_pos.trans hbetagamma).le hgamma.2 (by rw [hdim]; norm_num) hKF (p.η 0) heta
  refine ⟨{
    etaKT := etaKT
    etaKF := etaKF
    etaKT_pos := hetaKT
    etaKF_pos := hetaKF
    actual_KT := ?_
    actual_KF := hactualKF
    inner := full
    auxiliary := aux
    inner_window := ?_
    auxiliary_window := ?_ }⟩
  · filter_upwards [hactualKT, self_mem_nhdsWithin] with delta hdelta hd
    intro iota s Y hball hfull
    exact hdelta delta hd le_rfl s Y hball (by exact_mod_cast hfull)
  · intro m hm
    exact htrial false m hm
  · intro m hm
    exact htrial true m hm

/-- The working exponent, then the public input exponent, are selected
after the actual schedule. Extra smallness reserves pay initial banding,
finite restarts and the requested final loss; they are outputs, not inputs. -/
structure InputChoiceW110 [Nontrivial E]
    {beta gammaZero etaStar gamma : ℝ}
    {G : SourceStructureW110 beta gammaZero etaStar} {Ctw Ccell : ℝ≥0}
    (A : AnalyticScheduleW110.{uE, uI} (E := E) G gamma Ctw Ccell)
    (accuracy : ℝ) where
  workingEta : ℝ
  inputEta : ℝ
  working_pos : 0 < workingEta
  input_pos : 0 < inputEta
  input_eq : inputEta = workingEta / 8
  ladder_reserve : workingEta <= G.p.η 0 / 1000
  sticky_reserve : workingEta <= etaStar / 10
  inner_reserve : ∀ m : Fin (G.p.N + 1), m.val < G.p.N ->
    workingEta <= G.p.ε * min (A.inner.inner m) (A.auxiliary.inner m) / 1000
  gain_reserve : workingEta <= G.p.ε * G.xiMin / 1000
  cf_reserve : ∀ m : Fin (G.p.N + 1), m.val < G.p.N ->
    workingEta <= G.p.ε * G.xi m / 160000
  KT_reserve : workingEta <= A.etaKT / 1000
  KF_reserve : workingEta <= A.etaKF / 1000
  requested_loss_reserve : workingEta <= accuracy / 1000
  unit_reserve : workingEta <= 1 / 1000

theorem exists_input_choice_w110 [Nontrivial E]
    {beta gammaZero etaStar gamma : ℝ}
    {G : SourceStructureW110 beta gammaZero etaStar} {Ctw Ccell : ℝ≥0}
    (A : AnalyticScheduleW110.{uE, uI} (E := E) G gamma Ctw Ccell)
    {accuracy : ℝ} (haccuracy : 0 < accuracy) :
    Nonempty (InputChoiceW110 A accuracy) := by
  classical
  have hp := G.numerics
  have heta : 0 < G.p.η 0 := hp.zeta_pos 0 (Nat.zero_le _)
  have hepsilon := hp.epsilon_pos
  have hxiMin := hp.xiMin_pos
  have hsticky : 0 < etaStar := by
    have hm := G.sticky_margin
    have he := hp.epsilon_pos
    linarith only [hm, he]
  let fixed : ℝ := min (G.p.η 0 / 1000) (min (etaStar / 10)
    (min (G.p.ε * G.xiMin / 1000) (min (G.p.ε * G.xiMin / 160000)
      (min (A.etaKT / 1000) (min (A.etaKF / 1000)
        (min (accuracy / 1000) (1 / 1000)))))))
  have hfixed : 0 < fixed := by
    dsimp only [fixed]
    exact lt_min (by positivity) (lt_min (by positivity)
      (lt_min (by positivity) (lt_min (by positivity)
        (lt_min (div_pos A.etaKT_pos (by norm_num))
          (lt_min (div_pos A.etaKF_pos (by norm_num))
            (lt_min (by positivity) (by norm_num)))))))
  let budget : Fin (G.p.N + 1) -> ℝ := fun m =>
    min fixed (G.p.ε * min (A.inner.inner m) (A.auxiliary.inner m) / 1000)
  have hbudget : ∀ m, 0 < budget m := by
    intro m
    exact lt_min hfixed (div_pos (mul_pos hp.epsilon_pos
      (lt_min (A.inner.inner_pos m) (A.auxiliary.inner_pos m))) (by norm_num))
  obtain ⟨m0, hm0, hmin⟩ := Finset.exists_min_image Finset.univ budget Finset.univ_nonempty
  let e := budget m0
  have he : 0 < e := hbudget m0
  have hbound : e <= fixed := min_le_left _ _
  have hbounds : e <= G.p.η 0 / 1000 ∧ e <= etaStar / 10 ∧
      e <= G.p.ε * G.xiMin / 1000 ∧ e <= G.p.ε * G.xiMin / 160000 ∧
      e <= A.etaKT / 1000 ∧ e <= A.etaKF / 1000 ∧
      e <= accuracy / 1000 ∧ e <= 1 / 1000 := by
    simpa only [fixed, le_min_iff] using hbound
  refine ⟨{
    workingEta := e
    inputEta := e / 8
    working_pos := he
    input_pos := by positivity
    input_eq := rfl
    ladder_reserve := hbounds.1
    sticky_reserve := hbounds.2.1
    inner_reserve := ?_
    gain_reserve := hbounds.2.2.1
    cf_reserve := ?_
    KT_reserve := hbounds.2.2.2.2.1
    KF_reserve := hbounds.2.2.2.2.2.1
    requested_loss_reserve := hbounds.2.2.2.2.2.2.1
    unit_reserve := hbounds.2.2.2.2.2.2.2 }⟩
  · intro m hm
    exact (hmin m (Finset.mem_univ m)).trans (min_le_right _ _)
  · intro m hm
    exact hbounds.2.2.2.1.trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (hp.xiMin_lower m hm) hp.epsilon_pos.le) (by norm_num))

/-- Exactly the family hypotheses of FrostmanEstimate at one input exponent. -/
structure OriginalInputW110 {iota : Type uI} {delta : ℝ≥0}
    (s : Finset iota) (Y : iota -> ShadedTube delta E) (eta : ℝ) : Prop where
  ball : ∀ i ∈ s, (Y i).carrier ⊆ Metric.closedBall 0 1
  essentially_distinct : (s : Set iota).Pairwise
    (fun i j => IsEssentiallyDistinct (Y i).carrier (Y j).carrier)
  frostman : IsFrostmanIn s (fun i => (Y i).toConvexSpaceBody)
    ConvexSpaceBody.closedUnitBall ((delta : ℝ≥0∞) ^ (-eta))
  fullness : (delta : ℝ≥0∞) ^ eta <=
    (ShadedBody.fullness s (fun i => (Y i).toShadedBody) : ℝ≥0∞)

/-- The existing banding conclusion, with its paid original shaded-mass
share exposed. -/
structure BandedInputW110 {iota : Type uI} {delta : ℝ≥0}
    (s : Finset iota) (Y : iota -> ShadedTube delta E) (workingEta : ℝ) where
  s2 : Finset iota
  subset : s2 ⊆ s
  nonempty : s2.Nonempty
  hereditary_fullness : ∀ t ⊆ s2, t.Nonempty ->
    (delta : ℝ≥0∞) ^ workingEta <=
      (ShadedBody.fullness t (fun i => (Y i).toShadedBody) : ℝ≥0∞)
  frostman : frostmanConstIn s2 (fun i => (Y i).toConvexSpaceBody)
    ConvexSpaceBody.closedUnitBall <= (delta : ℝ≥0∞) ^ (-workingEta)
  uniform : Tube.UniformTubeSet s2 (fun i => (Y i).toTube) (Tube.ssfGridLen delta)
    (Tube.uniformConst (Module.finrank ℝ E))
  original_mass_retention :
    (delta : ℝ≥0∞) ^ workingEta * (∑ i ∈ s, volume (Y i).shade) <=
      ∑ i ∈ s2, volume (Y i).shade

theorem band_at_selected_working_exponent_w110 [Nontrivial E]
    (hdim : Module.finrank ℝ E = 3)
    {beta gammaZero etaStar gamma : ℝ}
    {G : SourceStructureW110 beta gammaZero etaStar} {Ctw Ccell : ℝ≥0}
    {A : AnalyticScheduleW110.{uE, uI} (E := E) G gamma Ctw Ccell}
    {accuracy : ℝ} (I : InputChoiceW110 A accuracy) :
    ∀ᶠ (delta : ℝ≥0) in 𝓝[>] 0,
      ∀ {iota : Type uI} (s : Finset iota) (Y : iota -> ShadedTube delta E),
        OriginalInputW110 s Y I.inputEta ->
        Nonempty (BandedInputW110 s Y I.workingEta) := by
  classical
  let η : ℝ := I.inputEta
  let θ : ℝ := I.workingEta
  have hη : 0 < η := I.input_pos
  have hθ : 0 < θ := I.working_pos
  have hηθ : η ≤ θ / 8 := by exact le_of_eq I.input_eq
  have hθ4 : (0 : ℝ) < θ / 4 := by positivity
  have hθ8 : (0 : ℝ) < θ / 8 := by positivity
  obtain ⟨δU, hδUpos, _hδUle1, hU⟩ :=
    Tube.exists_uniformTubeSet_subfamily_ssf (E := E) 7 (θ / 4) hθ4
  obtain ⟨δ2, hδ2pos, _hδ2le1, h2thr⟩ := exists_threshold_natCast_le_rpow 2 (θ / 8) hθ8
  filter_upwards [eventually_card_le_rpow_neg_seven (E := E) hdim,
      eventually_le_nhdsGT (c := δU) hδUpos,
      eventually_le_nhdsGT (c := δ2) hδ2pos,
      eventually_le_nhdsGT (c := (1 : ℝ≥0)) one_pos,
      self_mem_nhdsWithin]
    with δ hcard7 hδU hδ2 hδ1 hδmem
  have hδ0 : (0 : ℝ≥0) < δ := hδmem
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hδe0 : (δ : ℝ≥0∞) ≠ 0 := (ENNReal.coe_pos.mpr hδ0).ne'
  have hδetop : (δ : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hδE1 : ((δ : ℝ≥0) : ℝ≥0∞) ≤ 1 := by exact_mod_cast hδ1
  have h2E : (2 : ℝ≥0∞) ≤ (δ : ℝ≥0∞) ^ (-(θ / 8)) := by
    rw [ennreal_coe_nnreal_rpow hδR (-(θ / 8)),
      show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by simp]
    exact ENNReal.ofReal_le_ofReal (by exact_mod_cast h2thr hδ0 hδ2)
  intro ι s V hin
  have hball := hin.ball
  have hED := hin.essentially_distinct
  have hfull := hin.fullness
  have hfro := ConvexSpaceBody.frostmanConstIn_le hin.frostman
  set F : ℝ≥0∞ := (ShadedBody.fullness s (fun i => (V i).toShadedBody) : ℝ≥0∞) with hF_def
  have hFtop : F ≠ ⊤ := by rw [hF_def]; exact ENNReal.coe_ne_top
  have hFpos : 0 < F :=
    lt_of_lt_of_le (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hδ0) hδetop) hfull
  have hs : s.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s with rfl | h
    · exact absurd hFpos (by simp [hF_def])
    · exact h
  obtain ⟨j₀, hj₀⟩ := hs
  set v : ℝ≥0∞ := volume (V j₀).carrier with hv_def
  have hvpos : 0 < v := by
    have hc : 0 < (_root_.Tube.le_volume.c (Module.finrank ℝ E) : ℝ≥0∞) :=
      ENNReal.coe_pos.mpr (_root_.Tube.le_volume.c_pos (Module.finrank ℝ E))
    have hδp : 0 < (δ : ℝ≥0∞) ^ (Module.finrank ℝ E - 1) :=
      ENNReal.pow_pos (ENNReal.coe_pos.mpr hδ0) (Module.finrank ℝ E - 1)
    exact lt_of_lt_of_le (ENNReal.mul_pos hc.ne' hδp.ne')
      (by simpa [hv_def] using _root_.Tube.le_volume (V j₀).toTube)
  have hvtop : v ≠ ⊤ := (V j₀).isCompact.measure_ne_top
  have hcarr : ∀ i, volume (V i).carrier = v := fun i => by
    simpa [hv_def] using
      _root_.Tube.volume_carrier_eq_volume_carrier (V i).toTube (V j₀).toTube
  have hsumcar : ∀ X : Finset ι, ∑ i ∈ X, volume (V i).carrier = (X.card : ℝ≥0∞) * v :=
    fun X => by
      simpa [hv_def] using
        _root_.Tube.sum_volume_carrier_eq_card_mul (fun i => (V i).toTube) (V j₀).toTube X
  have hM : ∑ i ∈ s, volume (V i).shade = F * ((s.card : ℝ≥0∞) * v) := by
    rw [← hsumcar s, hF_def]
    exact ShadedBody.sum_volumeReal_shade_eq_fullness_mul s (fun i => (V i).toShadedBody)
  -- **Step 1.**  Discard the tubes of below-average shade density.
  set sa : Finset ι :=
    ShadedBody.discardLowShading s (fun i => (V i).toShadedBody) (2⁻¹ : ℝ≥0) with hsa_def
  have hsa_sub : sa ⊆ s := ShadedBody.discardLowShading_subset _ _ _
  have hmass_a : (2 : ℝ≥0∞)⁻¹ * (∑ i ∈ s, volume (V i).shade)
      ≤ ∑ i ∈ sa, volume (V i).shade := by
    have h := ShadedBody.one_sub_mul_sum_volume_shade_le_sum_discardLowShading s
      (fun i => (V i).toShadedBody) (c := (2⁻¹ : ℝ≥0)) (by norm_num)
    have hhalf : ((1 - (2⁻¹ : ℝ≥0) : ℝ≥0) : ℝ≥0∞) = (2 : ℝ≥0∞)⁻¹ := by
      norm_num
    rwa [hhalf] at h
  have hband_a : ∀ i ∈ sa, (2 : ℝ≥0∞)⁻¹ * F * v ≤ volume (V i).shade := by
    intro i hi
    have h := ShadedBody.le_volume_shade_of_mem_discardLowShading (c := (2⁻¹ : ℝ≥0)) hi
    have hc : (((2⁻¹ : ℝ≥0)) : ℝ≥0∞) = (2 : ℝ≥0∞)⁻¹ := by norm_num
    rwa [hc, ← hF_def, hcarr i] at h
  have hcount_a : (2 : ℝ≥0∞)⁻¹ * F * (s.card : ℝ≥0∞) ≤ (sa.card : ℝ≥0∞) := by
    have hupper : ∑ i ∈ sa, volume (V i).shade ≤ (sa.card : ℝ≥0∞) * v := by
      calc ∑ i ∈ sa, volume (V i).shade
          ≤ ∑ i ∈ sa, volume (V i).carrier :=
            Finset.sum_le_sum fun i _ => measure_mono (V i).shade_subset
        _ = (sa.card : ℝ≥0∞) * v := hsumcar sa
    have hchain : (2 : ℝ≥0∞)⁻¹ * F * (s.card : ℝ≥0∞) * v ≤ (sa.card : ℝ≥0∞) * v := by
      calc (2 : ℝ≥0∞)⁻¹ * F * (s.card : ℝ≥0∞) * v
          = (2 : ℝ≥0∞)⁻¹ * (F * ((s.card : ℝ≥0∞) * v)) := by ring
        _ = (2 : ℝ≥0∞)⁻¹ * (∑ i ∈ s, volume (V i).shade) := by rw [hM]
        _ ≤ ∑ i ∈ sa, volume (V i).shade := hmass_a
        _ ≤ (sa.card : ℝ≥0∞) * v := hupper
    exact (ENNReal.mul_le_mul_iff_right hvpos.ne' hvtop).mp
      (by simpa [mul_comm] using hchain)
  have hsane : sa.Nonempty := by
    rw [← Finset.card_pos, ← Nat.cast_pos (α := ℝ≥0∞)]
    refine lt_of_lt_of_le ?_ hcount_a
    have hcs : (0 : ℝ≥0∞) < (s.card : ℝ≥0∞) := by
      exact_mod_cast Finset.card_pos.mpr ⟨j₀, hj₀⟩
    exact ENNReal.mul_pos
      (ENNReal.mul_pos (show ((2 : ℝ≥0∞))⁻¹ ≠ 0 by simp) hFpos.ne').ne' hcs.ne'
  -- **Step 2.**  Uniformize the tubes on the truncated index set.
  have hcards : (s.card : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ)) :=
    hcard7 δ le_rfl s (fun i => (V i).toTube) (by simpa using hball) (by simpa using hED)
  have hcards_a : (sa.card : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ)) :=
    le_trans (by exact_mod_cast Finset.card_le_card hsa_sub) hcards
  obtain ⟨s₂, h₂a, hcardret, hunif⟩ :=
    hU hδ0 hδU sa (fun i => (V i).toTube)
      (fun i hi => by simpa using hball i (hsa_sub hi)) hcards_a
  have hs₂s : s₂ ⊆ s := h₂a.trans hsa_sub
  have hs₂ne : s₂.Nonempty := by
    rw [← Finset.card_pos]
    rcases Nat.eq_zero_or_pos s₂.card with hz | hpos
    · exfalso
      rw [hz] at hcardret
      norm_num at hcardret
      exact (Finset.not_nonempty_iff_eq_empty.mpr hcardret) hsane
    · exact hpos
  have hcardE : (sa.card : ℝ≥0∞)
      ≤ (δ : ℝ≥0∞) ^ (-(θ / 4)) * (s₂.card : ℝ≥0∞) := by
    rw [ennreal_coe_nnreal_rpow hδR (-(θ / 4)), ← ENNReal.ofReal_natCast sa.card,
      ← ENNReal.ofReal_natCast s₂.card, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδR.le _)]
    exact ENNReal.ofReal_le_ofReal hcardret
  have hκcard : (δ : ℝ≥0∞) ^ (θ / 2) * (s.card : ℝ≥0∞) ≤ (s₂.card : ℝ≥0∞) := by
    have hkey : (δ : ℝ≥0∞) ^ (θ / 2)
        ≤ (δ : ℝ≥0∞) ^ (θ / 4) * ((2 : ℝ≥0∞)⁻¹ * (δ : ℝ≥0∞) ^ η) := by
      have h2 : (2 : ℝ≥0∞) * (δ : ℝ≥0∞) ^ (θ / 2)
          ≤ (δ : ℝ≥0∞) ^ (θ / 4) * (δ : ℝ≥0∞) ^ η := by
        calc (2 : ℝ≥0∞) * (δ : ℝ≥0∞) ^ (θ / 2)
            ≤ (δ : ℝ≥0∞) ^ (-(θ / 8)) * (δ : ℝ≥0∞) ^ (θ / 2) := mul_le_mul_left h2E _
          _ = (δ : ℝ≥0∞) ^ (-(θ / 8) + θ / 2) := by
              rw [← ENNReal.rpow_add _ _ hδe0 hδetop]
          _ ≤ (δ : ℝ≥0∞) ^ (θ / 4 + η) :=
              ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith)
          _ = (δ : ℝ≥0∞) ^ (θ / 4) * (δ : ℝ≥0∞) ^ η := by
              rw [← ENNReal.rpow_add _ _ hδe0 hδetop]
      calc (δ : ℝ≥0∞) ^ (θ / 2) = (2 : ℝ≥0∞)⁻¹ * (2 * (δ : ℝ≥0∞) ^ (θ / 2)) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
        _ ≤ (2 : ℝ≥0∞)⁻¹ * ((δ : ℝ≥0∞) ^ (θ / 4) * (δ : ℝ≥0∞) ^ η) :=
            mul_le_mul_right h2 _
        _ = (δ : ℝ≥0∞) ^ (θ / 4) * ((2 : ℝ≥0∞)⁻¹ * (δ : ℝ≥0∞) ^ η) := by ring
    calc (δ : ℝ≥0∞) ^ (θ / 2) * (s.card : ℝ≥0∞)
        ≤ ((δ : ℝ≥0∞) ^ (θ / 4) * ((2 : ℝ≥0∞)⁻¹ * (δ : ℝ≥0∞) ^ η))
            * (s.card : ℝ≥0∞) := mul_le_mul_left hkey _
      _ = (δ : ℝ≥0∞) ^ (θ / 4) * ((2 : ℝ≥0∞)⁻¹ * (δ : ℝ≥0∞) ^ η
            * (s.card : ℝ≥0∞)) := by ring
      _ ≤ (δ : ℝ≥0∞) ^ (θ / 4) * ((2 : ℝ≥0∞)⁻¹ * F * (s.card : ℝ≥0∞)) := by
            gcongr
      _ ≤ (δ : ℝ≥0∞) ^ (θ / 4) * (sa.card : ℝ≥0∞) := by
            exact mul_le_mul_right hcount_a _
      _ ≤ (δ : ℝ≥0∞) ^ (θ / 4) * ((δ : ℝ≥0∞) ^ (-(θ / 4)) * (s₂.card : ℝ≥0∞)) := by
            exact mul_le_mul_right hcardE _
      _ = (s₂.card : ℝ≥0∞) := by
            rw [← mul_assoc, ← ENNReal.rpow_add _ _ hδe0 hδetop]
            simp
  refine ⟨⟨s₂, hs₂s, hs₂ne, ?_, ?_, Classical.choice hunif, ?_⟩⟩
  -- **The fullness clause**, termwise on `sa` and hence on every nonempty subfamily.
  · have hstep : (δ : ℝ≥0∞) ^ θ ≤ (2 : ℝ≥0∞)⁻¹ * F := by
      have h2 : (2 : ℝ≥0∞) * (δ : ℝ≥0∞) ^ θ ≤ F := by
        calc (2 : ℝ≥0∞) * (δ : ℝ≥0∞) ^ θ
            ≤ (δ : ℝ≥0∞) ^ (-(θ / 8)) * (δ : ℝ≥0∞) ^ θ := mul_le_mul_left h2E _
          _ = (δ : ℝ≥0∞) ^ (-(θ / 8) + θ) := by
              rw [← ENNReal.rpow_add _ _ hδe0 hδetop]
          _ ≤ (δ : ℝ≥0∞) ^ η :=
              ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith)
          _ ≤ F := hfull
      calc (δ : ℝ≥0∞) ^ θ = (2 : ℝ≥0∞)⁻¹ * (2 * (δ : ℝ≥0∞) ^ θ) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
        _ ≤ (2 : ℝ≥0∞)⁻¹ * F := mul_le_mul_right h2 _
    have hterm : ∀ i ∈ sa,
        (δ : ℝ≥0∞) ^ θ * volume ((fun i => (V i).toShadedBody) i).carrier
          ≤ volume ((fun i => (V i).toShadedBody) i).shade := by
      intro i hi
      refine le_trans ?_ (hband_a i hi)
      have hcv : volume ((fun i => (V i).toShadedBody) i).carrier = v := hcarr i
      rw [hcv]
      exact mul_le_mul_left hstep v
    intro t ht htne
    exact ml1Boot.le_fullness_of_termwise (fun i => (V i).toShadedBody)
      (fun i _ => by rw [hcarr i]; exact hvpos)
      (fun i _ => by rw [hcarr i]; exact hvtop) hterm (ht.trans h₂a) htne
  -- The same chosen family's Frostman bound.
  · have hκpos : ((δ : ℝ≥0∞) ^ (θ / 2)) ≠ 0 :=
      (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hδ0) hδetop).ne'
    have hWK : ∀ i ∈ s, (V i).toConvexSpaceBody
        ≤ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) := by
      intro i hi
      change (V i).carrier ⊆ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier
      rw [ConvexSpaceBody.closedUnitBall_carrier]
      exact hball i hi
    have hf := ConvexSpaceBody.frostmanConstIn_subfamily_le
      (s := s) (s' := s₂) (W := fun i => (V i).toConvexSpaceBody)
      (K := (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E))
      (κ := (δ : ℝ≥0∞) ^ (θ / 2)) (v := v) ⟨j₀, hj₀⟩ (fun i _ => hcarr i) hWK hs₂s
      hκpos hκcard
    rw [← ENNReal.rpow_neg] at hf
    refine hf.trans ?_
    calc (δ : ℝ≥0∞) ^ (-(θ / 2)) * ConvexSpaceBody.frostmanConstIn s
            (fun i => (V i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall
        ≤ (δ : ℝ≥0∞) ^ (-(θ / 2)) * (δ : ℝ≥0∞) ^ (-η) := mul_le_mul_right hfro _
      _ = (δ : ℝ≥0∞) ^ (-(θ / 2) + -η) := by rw [← ENNReal.rpow_add _ _ hδe0 hδetop]
      _ ≤ (δ : ℝ≥0∞) ^ (-θ) := ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith)
  · have hpow : (δ : ℝ≥0∞) ^ θ ≤ (2 : ℝ≥0∞)⁻¹ * (δ : ℝ≥0∞) ^ (θ / 2) := by
      have htwo : (2 : ℝ≥0∞) * (δ : ℝ≥0∞) ^ θ ≤ (δ : ℝ≥0∞) ^ (θ / 2) := by
        calc
          _ ≤ (δ : ℝ≥0∞) ^ (-(θ / 8)) * (δ : ℝ≥0∞) ^ θ :=
            mul_le_mul' h2E le_rfl
          _ = (δ : ℝ≥0∞) ^ (-(θ / 8) + θ) := by
            rw [← ENNReal.rpow_add _ _ hδe0 hδetop]
          _ ≤ _ := ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith only [hθ])
      calc
        _ = (2 : ℝ≥0∞)⁻¹ * (2 * (δ : ℝ≥0∞) ^ θ) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
        _ ≤ _ := mul_le_mul' le_rfl htwo
    calc
      _ = (δ : ℝ≥0∞) ^ θ * (F * ((s.card : ℝ≥0∞) * v)) := by rw [hM]
      _ ≤ ((2 : ℝ≥0∞)⁻¹ * (δ : ℝ≥0∞) ^ (θ / 2)) *
          (F * ((s.card : ℝ≥0∞) * v)) := mul_le_mul' hpow le_rfl
      _ = (2 : ℝ≥0∞)⁻¹ * F * ((δ : ℝ≥0∞) ^ (θ / 2) * (s.card : ℝ≥0∞)) * v := by ring
      _ ≤ (2 : ℝ≥0∞)⁻¹ * F * (s₂.card : ℝ≥0∞) * v :=
        mul_le_mul' (mul_le_mul' le_rfl hκcard) le_rfl
      _ = ∑ _i ∈ s₂, (2 : ℝ≥0∞)⁻¹ * F * v := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := Finset.sum_le_sum (fun i hi => hband_a i (h₂a hi))

/-- The output is indexed by the original s and Y. Same-tube, subshade and
retained mass are inherited from the actual retained-state definition.
The terminal multiplicity price and the transport price are both explicit. -/
structure OriginalRunW110 [Nontrivial E] {iota : Type uI} {delta : ℝ≥0}
    (s : Finset iota) (Y : iota -> ShadedTube delta E)
    (gamma step accuracy : ℝ) where
  terminal : RetainedStateW94 s Y
  transport_budget : (delta : ℝ≥0∞) ^ (accuracy / 4) <= terminal.retained
  terminal_estimate :
    ShadedBody.multiplicity terminal.active (fun i => (terminal.shading i).toShadedBody) <=
      (delta : ℝ≥0∞) ^ (-accuracy / 4 - 2 * (gamma - step)) *
        ((terminal.active.card : ℝ≥0∞) * (delta : ℝ≥0∞) ^
          (Module.finrank ℝ E - 1)) ^ (1 - (gamma - step) / 2)

end

end Kakeya.ml1Boot.RevisedSourceRepairW110

namespace Kakeya.ml1Boot.FixedMStickyExitW110

noncomputable section
set_option autoImplicit false

universe uE uI

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open TrialRestartW94 RevisedLiteralProfileInterfaceFormalizerW87
open RevisedSourceRepairW110

/-- Quantitative transfer between two potentially different grids,
including the mesh factor of degree eight. -/
theorem mixed_grid_frostman_transfer_w110 [Nontrivial E]
    (hdim : Module.finrank ℝ E = 3)
    {iota : Type uI} [DecidableEq iota] {radius : ℝ≥0}
    (hradius : 0 < radius) (hradius_one : radius <= 1)
    {M J : Nat} (hM : 1 <= M) (hJ : 1 <= J)
    (A B : Finset iota) (Z : iota -> ShadedTube radius E)
    (hA : A.Nonempty) (hB : B.Nonempty) (hBA : B ⊆ A)
    (hball : ∀ i ∈ A, (Z i).carrier ⊆ Metric.closedBall 0 1)
    {Cold Cnew Ctw Ccell : ℝ≥0} (hCtw : 1 <= Ctw)
    (U : CanonicalProfileNetW87 A (fun i => (Z i).toTube) M Cold)
    (hregular : SourceRegularizedWorkingTowerW95 U Ctw Ccell)
    (V : Tube.UniformTubeSet B (fun i => (Z i).toTube) J Cnew)
    {L : ℝ≥0} (hcard : (A.card : ℝ≥0) <= L * (B.card : ℝ≥0))
    {H : ℝ≥0∞} (hEvery : U.IsFrostmanAtEveryScale H) :
    V.IsFrostmanAtEveryScale
      ((trialNearbyParentCountW96 Ctw : ℝ≥0∞) *
        ((Tube.volume_le.C 3 / Tube.le_volume.c 3 : ℝ≥0) : ℝ≥0∞) *
        (Cold : ℝ≥0∞) ^ (2 : Nat) * (Cnew : ℝ≥0∞) ^ (3 : Nat) *
        (L : ℝ≥0∞) * (radius : ℝ≥0∞) ^ (-(8 : ℝ) / (M : ℝ)) * H) := by
  classical
  intro j hj jnew hjnew
  let k := Nat.ceil ((M : ℝ) * j / J)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  have hk : k <= M := by
    apply Nat.ceil_le.mpr
    apply (div_le_iff₀ hJpos).mpr
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hj) hMpos.le
  have hkLower : (j : ℝ) / J <= (k : ℝ) / M := by
    apply (le_div_iff₀ hMpos).mpr
    simpa [k, mul_div_assoc, mul_comm] using Nat.le_ceil ((M : ℝ) * j / J)
  have hkUpper : (k : ℝ) / M <= (j : ℝ) / J + 1 / M := by
    apply (div_le_iff₀ hMpos).mpr
    have h := (Nat.ceil_lt_add_one
      (show (0 : ℝ) <= (M : ℝ) * j / J by positivity)).le
    dsimp only [k]
    convert h using 1; field_simp
  let r := Tube.gridScale radius M k
  let s := Tube.gridScale radius J j
  have hrpos : 0 < r := Tube.gridScale_pos hradius M k
  have hspos : 0 < s := Tube.gridScale_pos hradius J j
  have hrone : r <= 1 := Tube.gridScale_le_one hradius_one M k
  have hsone : s <= 1 := Tube.gridScale_le_one hradius_one J j
  have hdr : radius <= r := by
    rw [← Tube.gridScale_self radius (show 0 < M by omega)]
    exact Tube.gridScale_antitone hradius hradius_one M hk
  have hds : radius <= s := by
    rw [← Tube.gridScale_self radius (show 0 < J by omega)]
    exact Tube.gridScale_antitone hradius hradius_one J hj
  have hrs : r <= s := NNReal.rpow_le_rpow_of_exponent_ge hradius hradius_one hkLower
  let q : ℝ≥0 := s / r
  have hq : 1 <= q := (one_le_div hrpos).mpr hrs
  have hqmesh : q ^ (8 : Nat) <= radius ^ (-(8 : ℝ) / (M : ℝ)) := by
    have hqeq : q = radius ^ ((j : ℝ) / J - (k : ℝ) / M) := by
      exact (NNReal.rpow_sub hradius.ne' _ _).symm
    rw [hqeq, ← NNReal.rpow_natCast, ← NNReal.rpow_mul]
    apply NNReal.rpow_le_rpow_of_exponent_ge hradius hradius_one
    norm_num
    have ht : -(1 / (M : ℝ)) <= (j : ℝ) / J - (k : ℝ) / M := by
      linarith only [hkUpper]
    calc
      -(8 : ℝ) / M = 8 * (-(1 / (M : ℝ))) := by ring
      _ <= 8 * ((j : ℝ) / J - (k : ℝ) / M) :=
        mul_le_mul_of_nonneg_left ht (by norm_num)
      _ = _ := by ring
  have hnodeCount : ((V.cover.indexSet j).card : ℝ≥0) <=
      Cnew * ((U.cover.indexSet k).card : ℝ≥0) := by
    have hcov : V.cover.indexSet j ⊆ (U.cover.indexSet k).biUnion (fun old =>
        (V.cover.indexSet j).filter (fun new => ∃ i ∈ B,
          (Z i).toConvexSpaceBody <= (V.cover.tube j new).toConvexSpaceBody ∧
          (Z i).toConvexSpaceBody <=
            ((U.cover.tube k old).rescale s).toConvexSpaceBody)) := by
      intro new hnew
      obtain ⟨i, hi⟩ := MultiScaleFac.coverClass_nonempty_of_mem_parent V hj hB hnew
      simp only [Tube.coverClass, Finset.mem_filter] at hi
      obtain ⟨hiB, hassign⟩ := hi
      refine Finset.mem_biUnion.mpr ⟨U.cover.assign k i,
        U.cover.assign_mem k hk i (hBA hiB), Finset.mem_filter.mpr ⟨hnew,
        i, hiB, ?_, (U.cover.le_tube_assign k hk i (hBA hiB)).trans
          ((U.cover.tube k (U.cover.assign k i)).le_rescale hrs)⟩⟩
      have h := V.cover.le_tube_assign j hj i hiB
      rwa [hassign] at h
    calc
      ((V.cover.indexSet j).card : ℝ≥0) <=
          ((∑ old ∈ U.cover.indexSet k,
            ((V.cover.indexSet j).filter (fun new => ∃ i ∈ B,
              (Z i).toConvexSpaceBody <= (V.cover.tube j new).toConvexSpaceBody ∧
              (Z i).toConvexSpaceBody <=
                ((U.cover.tube k old).rescale s).toConvexSpaceBody)).card : Nat) : ℝ≥0) := by
        exact_mod_cast (Finset.card_le_card hcov).trans Finset.card_biUnion_le
      _ = ∑ old ∈ U.cover.indexSet k,
          (((V.cover.indexSet j).filter (fun new => ∃ i ∈ B,
            (Z i).toConvexSpaceBody <= (V.cover.tube j new).toConvexSpaceBody ∧
            (Z i).toConvexSpaceBody <=
              ((U.cover.tube k old).rescale s).toConvexSpaceBody)).card : ℝ≥0) := by
        push_cast
        rfl
      _ <= ∑ _old ∈ U.cover.indexSet k, Cnew :=
        Finset.sum_le_sum fun old _ => V.boundedOverlap j hj ((U.cover.tube k old).rescale s)
      _ = Cnew * ((U.cover.indexSet k).card : ℝ≥0) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hbranch : U.branchingN k <= Cold * L * Cnew ^ 2 * V.branchingN j := by
    have hpartU : A.card = ∑ old ∈ U.cover.indexSet k,
        (Tube.coverClass A (U.cover.assign k) old).card := by
      simp only [Tube.coverClass]
      convert (Finset.card_eq_sum_card_fiberwise fun i hi => U.cover.assign_mem k hk i hi) using 1
      apply Finset.sum_congr rfl
      intro old hold
      congr 1
      ext i
      simp only [Finset.mem_filter]
    have hpartV : B.card = ∑ new ∈ V.cover.indexSet j,
        (Tube.coverClass B (V.cover.assign j) new).card := by
      simp only [Tube.coverClass]
      convert (Finset.card_eq_sum_card_fiberwise fun i hi => V.cover.assign_mem j hj i hi) using 1
      apply Finset.sum_congr rfl
      intro new hnew
      congr 1
      ext i
      simp only [Finset.mem_filter]
    have hE1 : ((U.cover.indexSet k).card : ℝ≥0) * U.branchingN k <=
        Cold * (A.card : ℝ≥0) := by
      calc
        _ = ∑ _old ∈ U.cover.indexSet k, U.branchingN k := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ <= ∑ old ∈ U.cover.indexSet k,
            Cold * ((Tube.coverClass A (U.cover.assign k) old).card : ℝ≥0) :=
          Finset.sum_le_sum fun old hold => U.le_card_class k hk old hold
        _ = Cold * (A.card : ℝ≥0) := by
          rw [← Finset.mul_sum, hpartU]
          push_cast
          rfl
    have hE2 : (B.card : ℝ≥0) <=
        ((V.cover.indexSet j).card : ℝ≥0) * (Cnew * V.branchingN j) := by
      calc
        _ = ∑ new ∈ V.cover.indexSet j,
            ((Tube.coverClass B (V.cover.assign j) new).card : ℝ≥0) := by
          rw [hpartV]
          push_cast
          rfl
        _ <= ∑ _new ∈ V.cover.indexSet j, Cnew * V.branchingN j :=
          Finset.sum_le_sum fun new hnew => V.card_class_le j hj new hnew
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    have hnpos : 0 < ((U.cover.indexSet k).card : ℝ≥0) := by
      obtain ⟨i, hi⟩ := hA
      exact_mod_cast Finset.card_pos.mpr ⟨_, U.cover.assign_mem k hk i hi⟩
    apply le_of_mul_le_mul_right (a := ((U.cover.indexSet k).card : ℝ≥0)) _ hnpos
    calc
      _ = ((U.cover.indexSet k).card : ℝ≥0) * U.branchingN k := mul_comm _ _
      _ <= Cold * (A.card : ℝ≥0) := hE1
      _ <= Cold * (L * (B.card : ℝ≥0)) := mul_le_mul_right hcard Cold
      _ <= Cold * (L * (((V.cover.indexSet j).card : ℝ≥0) *
          (Cnew * V.branchingN j))) := by gcongr
      _ <= Cold * (L * ((Cnew * ((U.cover.indexSet k).card : ℝ≥0)) *
          (Cnew * V.branchingN j))) := by gcongr
      _ = _ := by ring
  let W : iota -> ConvexSpaceBody E := fun i => (Z i).toConvexSpaceBody
  obtain ⟨i0, hi0⟩ := hB
  let v := volume (W i0).carrier
  let Knew := (V.cover.tube j jnew).toConvexSpaceBody
  let u := volume Knew.carrier
  let Kvol : ℝ≥0 := Tube.volume_le.C 3 / Tube.le_volume.c 3
  let classNew := Tube.coverClass B (V.cover.assign j) jnew
  have hcmem : ∀ i ∈ classNew, i ∈ B ∧ V.cover.assign j i = jnew := by
    intro i hi
    simpa only [classNew, Tube.coverClass, Finset.mem_filter] using hi
  have hcW : ∀ i ∈ classNew, W i <= Knew := by
    intro i hi
    have h := V.cover.le_tube_assign j hj i (hcmem i hi).1
    rwa [(hcmem i hi).2] at h
  have hRHS : densityIn classNew W Knew = (classNew.card : ℝ≥0∞) * v / u := by
    rw [densityIn_of_all_le hcW]
    have hv : ∀ i ∈ classNew, volume (W i).carrier = v :=
      fun i _ => Tube.volume_carrier_eq_volume_carrier (Z i).toTube (Z i0).toTube
    rw [Finset.sum_congr rfl hv, Finset.sum_const, nsmul_eq_mul]
  intro K' hK'
  let F := classNew.filter (fun i => W i <= K')
  let oldNodes := F.image (U.cover.assign k)
  have hFmem : ∀ i ∈ F, i ∈ B ∧ V.cover.assign j i = jnew ∧ W i <= K' := by
    intro i hi
    obtain ⟨hic, hiK⟩ := Finset.mem_filter.mp hi
    exact ⟨(hcmem i hic).1, (hcmem i hic).2, hiK⟩
  have hOldMem : ∀ old ∈ oldNodes, old ∈ U.cover.indexSet k := by
    intro old hold
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hold
    exact U.cover.assign_mem k hk i (hBA (hFmem i hi).1)
  have hOldCount : (oldNodes.card : ℝ≥0) <=
      (trialNearbyParentCountW96 Ctw : ℝ≥0) * q ^ (6 : Nat) := by
    have hsub : oldNodes ⊆ commonFineMeetingParentsW96 A (fun i => (Z i).toTube)
        (U.cover.indexSet k) (U.cover.tube k) (V.cover.tube j jnew) := by
      intro old hold
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hold
      obtain ⟨hiB, hia, _⟩ := hFmem i hi
      refine Finset.mem_filter.mpr ⟨U.cover.assign_mem k hk i (hBA hiB),
        i, hBA hiB, U.cover.le_tube_assign k hk i (hBA hiB), ?_⟩
      have h := V.cover.le_tube_assign j hj i hiB
      rwa [hia] at h
    have hcount := card_assigned_parents_meeting_exact_cell_w96 hdim hradius hdr hds hrone
      A (fun i => (Z i).toTube) (U.cover.indexSet k) (U.cover.tube k)
      (V.cover.tube j jnew) Ctw hCtw hball (hregular.parent_ball k hk)
      (hregular.parent_line_ed k hk)
    have hqR : (1 : ℝ) <= (s : ℝ) / r := by exact_mod_cast hq
    rw [max_eq_right hqR] at hcount
    have hcount' : (oldNodes.card : ℝ) <=
        (trialNearbyParentCountW96 Ctw : ℝ) * ((s : ℝ) / r) ^ (6 : Nat) :=
      (show (oldNodes.card : ℝ) <=
        ((commonFineMeetingParentsW96 A (fun i => (Z i).toTube)
          (U.cover.indexSet k) (U.cover.tube k) (V.cover.tube j jnew)).card : ℝ) by
        exact_mod_cast Finset.card_le_card hsub).trans hcount
    exact_mod_cast hcount'
  have hnum : ∑ i ∈ F, volume (W i).carrier <=
      ∑ old ∈ oldNodes, ∑ i ∈ Tube.coverClass A (U.cover.assign k) old
        with W i <= K', volume (W i).carrier := by
    have hfib : (∑ old ∈ oldNodes, ∑ i ∈ F with U.cover.assign k i = old,
        volume (W i).carrier) = ∑ i ∈ F, volume (W i).carrier :=
      Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem _ hi) _
    rw [← hfib]
    refine Finset.sum_le_sum fun old _ => Finset.sum_le_sum_of_subset ?_
    intro i hi
    obtain ⟨hiF, hia⟩ := Finset.mem_filter.mp hi
    simp only [Tube.coverClass, Finset.mem_filter]
    exact ⟨⟨hBA (hFmem i hiF).1, hia⟩, (hFmem i hiF).2.2⟩
  have hstep1 : densityIn classNew W K' <=
      ∑ old ∈ oldNodes, densityIn (Tube.coverClass A (U.cover.assign k) old) W K' := by
    calc
      _ = (∑ i ∈ F, volume (W i).carrier) / volume K'.carrier := rfl
      _ <= (∑ old ∈ oldNodes, ∑ i ∈ Tube.coverClass A (U.cover.assign k) old
          with W i <= K', volume (W i).carrier) / volume K'.carrier :=
        ENNReal.div_le_div_right hnum _
      _ = _ := by simp only [densityIn, div_eq_mul_inv, Finset.sum_mul]
  have hstep2 : ∀ old ∈ oldNodes,
      densityIn (Tube.coverClass A (U.cover.assign k) old) W K' <=
        H * densityIn (Tube.coverClass A (U.cover.assign k) old) W
          (U.cover.tube k old).toConvexSpaceBody := by
    intro old hold
    have hcOld : ∀ i ∈ Tube.coverClass A (U.cover.assign k) old,
        W i <= (U.cover.tube k old).toConvexSpaceBody := by
      intro i hi
      simp only [Tube.coverClass, Finset.mem_filter] at hi
      have h := U.cover.le_tube_assign k hk i hi.1
      rwa [hi.2] at h
    exact (le_maxDensity _ _ K').trans
      ((hEvery k hk old (hOldMem old hold)).maxDensity_le_of_carrier_subset hcOld)
  have hstep3 : ∀ old ∈ oldNodes,
      densityIn (Tube.coverClass A (U.cover.assign k) old) W
          (U.cover.tube k old).toConvexSpaceBody <=
        ((Cold : ℝ≥0∞) ^ 2 * (L : ℝ≥0∞) * (Cnew : ℝ≥0∞) ^ 3) *
          (Kvol : ℝ≥0∞) * (q : ℝ≥0∞) ^ 2 * densityIn classNew W Knew := by
    intro old hold
    have hcOld : ∀ i ∈ Tube.coverClass A (U.cover.assign k) old,
        W i <= (U.cover.tube k old).toConvexSpaceBody := by
      intro i hi
      simp only [Tube.coverClass, Finset.mem_filter] at hi
      have h := U.cover.le_tube_assign k hk i hi.1
      rwa [hi.2] at h
    have hvols : ∀ i ∈ Tube.coverClass A (U.cover.assign k) old,
        volume (W i).carrier = v :=
      fun i _ => Tube.volume_carrier_eq_volume_carrier (Z i).toTube (Z i0).toTube
    have hcardN : ((Tube.coverClass A (U.cover.assign k) old).card : ℝ≥0) <=
        Cold ^ 2 * L * Cnew ^ 3 * (classNew.card : ℝ≥0) := by
      calc
        _ <= Cold * U.branchingN k := U.card_class_le k hk old (hOldMem old hold)
        _ <= Cold * (Cold * L * Cnew ^ 2 * V.branchingN j) := mul_le_mul_right hbranch Cold
        _ <= Cold * (Cold * L * Cnew ^ 2 * (Cnew * (classNew.card : ℝ≥0))) := by
          gcongr
          exact V.le_card_class j hj jnew hjnew
        _ = _ := by ring
    have hcardE : ((Tube.coverClass A (U.cover.assign k) old).card : ℝ≥0∞) <=
        (Cold : ℝ≥0∞) ^ 2 * (L : ℝ≥0∞) * (Cnew : ℝ≥0∞) ^ 3 *
          (classNew.card : ℝ≥0∞) := by exact_mod_cast hcardN
    let uold := volume (U.cover.tube k old).carrier
    have huo : uold ≠ 0 := (Tube.volume_pos_and_lt_top hrpos hrone _).1.ne'
    have hut : uold ≠ ⊤ := (Tube.volume_pos_and_lt_top hrpos hrone _).2.ne
    have hu : u ≠ 0 := (Tube.volume_pos_and_lt_top hspos hsone _).1.ne'
    have hutop : u ≠ ⊤ := (Tube.volume_pos_and_lt_top hspos hsone _).2.ne
    have hucomp : u <= (Kvol : ℝ≥0∞) * (q : ℝ≥0∞) ^ 2 * uold := by
      have hupper : u <= (Tube.volume_le.C 3 : ℝ≥0∞) * (s : ℝ≥0∞) ^ 2 := by
        simpa only [hdim, Nat.reduceSub] using Tube.volume_le hsone (V.cover.tube j jnew)
      have hlower : (Tube.le_volume.c 3 : ℝ≥0∞) * (r : ℝ≥0∞) ^ 2 <= uold := by
        simpa only [hdim, Nat.reduceSub] using Tube.le_volume (U.cover.tube k old)
      have heq : Kvol * q ^ 2 * (Tube.le_volume.c 3 * r ^ 2) = Tube.volume_le.C 3 * s ^ 2 := by
        dsimp [Kvol, q]
        field_simp [(Tube.le_volume.c_pos 3).ne', hrpos.ne']
      calc
        u <= (Tube.volume_le.C 3 : ℝ≥0∞) * (s : ℝ≥0∞) ^ 2 := hupper
        _ = (Kvol : ℝ≥0∞) * (q : ℝ≥0∞) ^ 2 *
            ((Tube.le_volume.c 3 : ℝ≥0∞) * (r : ℝ≥0∞) ^ 2) := by
          exact_mod_cast heq.symm
        _ <= _ := mul_le_mul_right hlower _
    rw [densityIn_of_all_le hcOld, Finset.sum_congr rfl hvols,
      Finset.sum_const, nsmul_eq_mul, hRHS]
    apply (ENNReal.div_le_iff huo hut).mpr
    calc
      _ <= ((Cold : ℝ≥0∞) ^ 2 * (L : ℝ≥0∞) * (Cnew : ℝ≥0∞) ^ 3 *
          (classNew.card : ℝ≥0∞)) * v := mul_le_mul_left hcardE v
      _ = ((Cold : ℝ≥0∞) ^ 2 * (L : ℝ≥0∞) * (Cnew : ℝ≥0∞) ^ 3) *
          (((classNew.card : ℝ≥0∞) * v / u) * u) := by
        rw [ENNReal.div_mul_cancel hu hutop]
        ring
      _ <= ((Cold : ℝ≥0∞) ^ 2 * (L : ℝ≥0∞) * (Cnew : ℝ≥0∞) ^ 3) *
          (((classNew.card : ℝ≥0∞) * v / u) *
            ((Kvol : ℝ≥0∞) * (q : ℝ≥0∞) ^ 2 * uold)) := by gcongr
      _ = _ := by ring
  calc
    densityIn classNew W K' <=
        ∑ old ∈ oldNodes, densityIn (Tube.coverClass A (U.cover.assign k) old) W K' := hstep1
    _ <= ∑ _old ∈ oldNodes, H *
        (((Cold : ℝ≥0∞) ^ 2 * (L : ℝ≥0∞) * (Cnew : ℝ≥0∞) ^ 3) *
          (Kvol : ℝ≥0∞) * (q : ℝ≥0∞) ^ 2 * densityIn classNew W Knew) :=
      Finset.sum_le_sum fun old hold => (hstep2 old hold).trans
        (mul_le_mul_right (hstep3 old hold) H)
    _ = (oldNodes.card : ℝ≥0∞) * (H *
        (((Cold : ℝ≥0∞) ^ 2 * (L : ℝ≥0∞) * (Cnew : ℝ≥0∞) ^ 3) *
          (Kvol : ℝ≥0∞) * (q : ℝ≥0∞) ^ 2 * densityIn classNew W Knew)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ <= ((trialNearbyParentCountW96 Ctw : ℝ≥0∞) * (q : ℝ≥0∞) ^ 6) * (H *
        (((Cold : ℝ≥0∞) ^ 2 * (L : ℝ≥0∞) * (Cnew : ℝ≥0∞) ^ 3) *
          (Kvol : ℝ≥0∞) * (q : ℝ≥0∞) ^ 2 * densityIn classNew W Knew)) := by
      gcongr
      exact_mod_cast hOldCount
    _ = (trialNearbyParentCountW96 Ctw : ℝ≥0∞) * (Kvol : ℝ≥0∞) *
        (Cold : ℝ≥0∞) ^ 2 * (Cnew : ℝ≥0∞) ^ 3 * (L : ℝ≥0∞) *
        (q : ℝ≥0∞) ^ 8 * H * densityIn classNew W Knew := by ring
    _ <= _ := by
      gcongr
      simpa only [ENNReal.coe_pow, ENNReal.coe_rpow_of_ne_zero hradius.ne'] using
        (ENNReal.coe_le_coe.mpr hqmesh)

/-- Construct the actual capped shaded tower from the fixed-M terminal,
then apply the already fixed sticky witness to that same constructed family. -/
theorem eventually_fixed_m_sticky_exit_w110 [Nontrivial E]
    (hdim : Module.finrank ℝ E = 3)
    {beta gammaZero : ℝ}
    (S : StickyWitnessW110.{uE, uI} E gammaZero)
    (G : SourceStructureW110 beta gammaZero S.etaStar)
    (Cwork Ctw Ccell BF : ℝ≥0)
    (_hCwork : 1 <= Cwork) (hCtw : 1 <= Ctw)
    (_hCcell : 1 <= Ccell) (_hBF : 1 <= BF) :
    ∀ᶠ (radius : ℝ≥0) in 𝓝[>] 0,
      ∀ {iota : Type uI} [DecidableEq iota]
        (A : Finset iota) (Z : iota -> ShadedTube radius E)
        (U : CanonicalProfileNetW87 A
          (fun i => (Z i).toTube) G.M Cwork),
        A.Nonempty ->
        (∀ i ∈ A, (Z i).carrier ⊆ Metric.closedBall 0 1) ->
        (A.card : ℝ) <= (radius : ℝ) ^ (-7 : ℝ) ->
        (radius : ℝ≥0∞) ^ G.p.ε <=
          fullness' A (fun i => (Z i).toShadedBody) ->
        SourceRegularizedWorkingTowerW95 U Ctw Ccell ->
        U.IsFrostmanAtEveryScale
          ((BF : ℝ≥0∞) ^ (G.p.N + 1) *
            (radius : ℝ≥0∞) ^ (-3 * G.p.ε)) ->
        ∃ (B : Finset iota) (W : iota -> ShadedTube radius E)
          (V : ShadedTube.ShadedUniformTubeSet B W
            (Tube.ssfGridLen radius)
            (ShadedTube.ssfUniformConst (Module.finrank ℝ E))),
          B.Nonempty ∧ B ⊆ A ∧
          (∀ i, (W i).toTube = (Z i).toTube) ∧
          (∀ i, (W i).shade ⊆ (Z i).shade) ∧
          (radius : ℝ) ^ (3 * G.p.ε / 2) * (A.card : ℝ)
            <= (B.card : ℝ) ∧
          (radius : ℝ≥0∞) ^ (2 * G.p.ε) *
              (∑ i ∈ A, volume (Z i).shade)
            <= ∑ i ∈ B, volume (W i).shade ∧
          (radius : ℝ≥0∞) ^ (2 * G.p.ε)
            <= fullness' B (fun i => (W i).toShadedBody) ∧
          V.tubeUniform.IsFrostmanAtEveryScale
            ((radius : ℝ≥0∞) ^ (-5 * G.p.ε)) ∧
          (radius : ℝ≥0∞) ^ (gammaZero / 4)
            <= volume (⋃ i ∈ B, (W i).shade) := by
  classical
  let eps : ℝ := G.p.ε
  have heps : 0 < eps := G.numerics.epsilon_pos
  have hmesh : (8 : ℝ) / G.M ≤ eps / 4 := by
    have hz := (G.numerics.zeta_mono 0 G.p.N (Nat.zero_le _) le_rfl).trans G.numerics.zeta_top
    have hes := G.numerics.epsilon_small
    have hm := G.numerics.M_zeta
    have hprod := mul_le_mul_of_nonneg_left hz heps.le
    have hsquare := mul_le_mul_of_nonneg_left hes.le heps.le
    dsimp only [eps] at *
    rw [show (8 : ℝ) / G.M = 8 * (1 / (G.M : ℝ)) by ring]
    nlinarith only [hm, hprod, hsquare, heps]
  let Ccap := ShadedTube.ssfUniformConst (Module.finrank ℝ E)
  let K : ℝ≥0 := 2 * trialNearbyParentCountW96 Ctw *
    (Tube.volume_le.C 3 / Tube.le_volume.c 3) * Cwork ^ (2 : Nat) *
      Ccap ^ (3 : Nat) * BF ^ (G.p.N + 1)
  obtain ⟨dC, hdC, _hdC1, hC⟩ := exists_threshold_natCast_le_rpow
    (Nat.ceil (max (K : ℝ) 4)) (eps / 2) (by positivity)
  obtain ⟨d2, hd2, _hd21, h2⟩ := exists_threshold_natCast_le_rpow 2 (eps / 4) (by positivity)
  obtain ⟨dU, hdU, _hdU1, hU⟩ := ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf
    (E := E) 7 (eps / 4) (eps / 4) (by positivity) (by positivity)
  obtain ⟨dJ, hdJ, _hdJ1, hJ⟩ := Tube.exists_threshold_polylog_pow_ssfGridLen_le
    1 le_rfl 0 1 1 one_pos
  filter_upwards [self_mem_nhdsWithin, eventually_le_nhdsGT (c := (1 : ℝ≥0)) one_pos,
    eventually_le_nhdsGT hdC, eventually_le_nhdsGT hd2, eventually_le_nhdsGT hdU,
    eventually_le_nhdsGT hdJ, S.actual_sticky]
    with radius hradius hradius1 hrC hr2 hrU hrJ hsticky
  have hr : 0 < radius := hradius
  have hrR : (0 : ℝ) < radius := hr
  have hr0 : (radius : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hr.ne'
  have hrTop : (radius : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hr1 : (radius : ℝ≥0∞) ≤ 1 := by exact_mod_cast hradius1
  have hcast (a : ℝ) : ENNReal.ofReal ((radius : ℝ) ^ a) =
      (radius : ℝ≥0∞) ^ a := (ennreal_coe_nnreal_rpow hrR a).symm
  have hconstR : max (K : ℝ) 4 ≤ (radius : ℝ) ^ (-(eps / 2)) :=
    (Nat.le_ceil _).trans (hC hr hrC)
  have hK : (K : ℝ≥0∞) ≤ (radius : ℝ≥0∞) ^ (-(eps / 2)) := by
    have h := ENNReal.ofReal_le_ofReal ((le_max_left (K : ℝ) 4).trans hconstR)
    simpa only [ENNReal.ofReal_coe_nnreal, hcast] using h
  have hfour : (4 : ℝ≥0∞) ≤ (radius : ℝ≥0∞) ^ (-(eps / 2)) := by
    have h := ENNReal.ofReal_le_ofReal ((le_max_right (K : ℝ) 4).trans hconstR)
    simpa only [ENNReal.ofReal_ofNat, hcast] using h
  have htwo : (2 : ℝ≥0∞) ≤ (radius : ℝ≥0∞) ^ (-(eps / 4)) := by
    have h2R : (2 : ℝ) ≤ (radius : ℝ) ^ (-(eps / 4)) := by
      exact_mod_cast h2 hr hr2
    have h := ENNReal.ofReal_le_ofReal h2R
    simpa only [ENNReal.ofReal_ofNat, hcast] using h
  have hhalfPower (a : ℝ) :
      (radius : ℝ≥0∞) ^ (a + eps / 4) ≤ (2 : ℝ≥0∞)⁻¹ * (radius : ℝ≥0∞) ^ a := by
    have h := mul_le_mul' htwo (le_refl ((radius : ℝ≥0∞) ^ (a + eps / 4)))
    rw [← ENNReal.rpow_add _ _ hr0 hrTop] at h
    have heq : -(eps / 4) + (a + eps / 4) = a := by ring
    rw [heq] at h
    calc
      _ = (2 : ℝ≥0∞)⁻¹ * (2 * (radius : ℝ≥0∞) ^ (a + eps / 4)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
      _ ≤ _ := mul_le_mul' le_rfl h
  have hquarterPower : (radius : ℝ≥0∞) ^ (2 * eps) ≤
      (4 : ℝ≥0∞)⁻¹ * (radius : ℝ≥0∞) ^ (3 * eps / 2) := by
    have h := mul_le_mul' hfour (le_refl ((radius : ℝ≥0∞) ^ (2 * eps)))
    rw [← ENNReal.rpow_add _ _ hr0 hrTop] at h
    have heq : -(eps / 2) + 2 * eps = 3 * eps / 2 := by ring
    rw [heq] at h
    calc
      _ = (4 : ℝ≥0∞)⁻¹ * (4 * (radius : ℝ≥0∞) ^ (2 * eps)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
      _ ≤ _ := mul_le_mul' le_rfl h
  intro iota _ A Z U hA hball hcard hfull hregular hEvery
  let lam : ℝ≥0∞ := fullness' A (fun i => (Z i).toShadedBody)
  have hlamPos : 0 < lam := (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hr) hrTop).trans_le hfull
  have hlamTop : lam ≠ ⊤ := fullness'_ne_top _ _
  let i0 := hA.choose
  let v : ℝ≥0∞ := volume (Z i0).carrier
  have hvPos : 0 < v := by
    apply lt_of_lt_of_le _ (Tube.le_volume (Z i0).toTube)
    exact ENNReal.mul_pos (ENNReal.coe_ne_zero.mpr (Tube.le_volume.c_pos _).ne')
      (pow_ne_zero _ hr0)
  have hvTop : v ≠ ⊤ := (Z i0).isCompact.measure_ne_top
  have hvol (i : iota) : volume (Z i).carrier = v :=
    Tube.volume_carrier_eq_volume_carrier (Z i).toTube (Z i0).toTube
  have hcar (F : Finset iota) :
      (∑ i ∈ F, volume (Z i).carrier) = (F.card : ℝ≥0∞) * v :=
    Tube.sum_volume_carrier_eq_card_mul (fun i => (Z i).toTube) (Z i0).toTube F
  have hmass : (∑ i ∈ A, volume (Z i).shade) = lam * ((A.card : ℝ≥0∞) * v) := by
    rw [sum_volumeReal_shade_eq_fullness_mul A (fun i => (Z i).toShadedBody),
      coe_fullness, hcar]
  let D := discardLowShading A (fun i => (Z i).toShadedBody) (2⁻¹ : ℝ≥0)
  have hDA : D ⊆ A := discardLowShading_subset _ _ _
  have hmassD : (2 : ℝ≥0∞)⁻¹ * (∑ i ∈ A, volume (Z i).shade) ≤
      ∑ i ∈ D, volume (Z i).shade := by
    have h := one_sub_mul_sum_volume_shade_le_sum_discardLowShading A
      (fun i => (Z i).toShadedBody) (c := (2⁻¹ : ℝ≥0)) (by norm_num)
    simpa only [show ((1 - (2⁻¹ : ℝ≥0) : ℝ≥0) : ℝ≥0∞) = (2 : ℝ≥0∞)⁻¹ by norm_num]
      using h
  have hterm : ∀ i ∈ D, (2 : ℝ≥0∞)⁻¹ * lam * v ≤ volume (Z i).shade := by
    intro i hi
    have h := le_volume_shade_of_mem_discardLowShading (c := (2⁻¹ : ℝ≥0)) hi
    simpa only [show ((2⁻¹ : ℝ≥0) : ℝ≥0∞) = (2 : ℝ≥0∞)⁻¹ by norm_num,
      coe_fullness, hvol] using h
  have hcardD : (2 : ℝ≥0∞)⁻¹ * lam * (A.card : ℝ≥0∞) ≤ (D.card : ℝ≥0∞) := by
    have hupper : (∑ i ∈ D, volume (Z i).shade) ≤ (D.card : ℝ≥0∞) * v := by
      rw [← hcar]
      exact Finset.sum_le_sum fun i _ => measure_mono (Z i).shade_subset
    have h := hmassD.trans hupper
    rw [hmass] at h
    apply (ENNReal.mul_le_mul_iff_right hvPos.ne' hvTop).mp
    simpa only [mul_assoc, mul_left_comm, mul_comm] using h
  have hD : D.Nonempty := by
    have hpos : (0 : ℝ≥0∞) < (D.card : ℝ≥0∞) :=
      (ENNReal.mul_pos (ENNReal.mul_pos (by norm_num) hlamPos.ne').ne'
        (by exact_mod_cast hA.card_pos.ne')).trans_le hcardD
    exact Finset.card_pos.mp (by exact_mod_cast hpos)
  have hDcard : (D.card : ℝ) ≤ (radius : ℝ) ^ (-7 : ℝ) :=
    (Nat.cast_le.mpr (Finset.card_le_card hDA)).trans hcard
  obtain ⟨B, hBD, W, hWTube, hWShade, hcardU, hfullU, ⟨V⟩⟩ :=
    hU hr hrU D Z (fun i hi => hball i (hDA hi))
      (by simpa only [Nat.cast_ofNat] using hDcard)
  have hBA : B ⊆ A := hBD.trans hDA
  have hB : B.Nonempty := by
    by_contra h
    have hzero := Finset.not_nonempty_iff_eq_empty.mp h
    rw [hzero] at hcardU
    simp only [Finset.card_empty, Nat.cast_zero, mul_zero] at hcardU
    exact (by exact_mod_cast hD.card_pos : (0 : ℝ) < D.card).not_ge hcardU
  have hcardUE : (D.card : ℝ≥0∞) ≤ (radius : ℝ≥0∞) ^ (-(eps / 4)) * (B.card : ℝ≥0∞) := by
    have h := ENNReal.ofReal_le_ofReal hcardU
    simpa only [ENNReal.ofReal_mul (Real.rpow_nonneg hrR.le _), ENNReal.ofReal_natCast, hcast] using h
  have hcardLower : (radius : ℝ≥0∞) ^ (eps / 4) *
      ((2 : ℝ≥0∞)⁻¹ * lam) * (A.card : ℝ≥0∞) ≤ (B.card : ℝ≥0∞) := by
    calc
      _ = (radius : ℝ≥0∞) ^ (eps / 4) * ((2 : ℝ≥0∞)⁻¹ * lam * (A.card : ℝ≥0∞)) := by ring
      _ ≤ (radius : ℝ≥0∞) ^ (eps / 4) *
          ((radius : ℝ≥0∞) ^ (-(eps / 4)) * (B.card : ℝ≥0∞)) :=
        mul_le_mul' le_rfl (hcardD.trans hcardUE)
      _ = _ := by rw [← mul_assoc, ← ENNReal.rpow_add _ _ hr0 hrTop]; simp
  have hfullBZ : (2 : ℝ≥0∞)⁻¹ * lam ≤ fullness' B (fun i => (Z i).toShadedBody) := by
    rw [fullness', hcar]
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl (ENNReal.mul_pos (by exact_mod_cast hB.card_pos.ne') hvPos.ne').ne')
      (Or.inl (ENNReal.mul_ne_top (by finiteness) hvTop))).mpr
    calc
      _ = ∑ _i ∈ B, (2 : ℝ≥0∞)⁻¹ * lam * v := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := Finset.sum_le_sum fun i hi => hterm i (hBD hi)
  have hfullW : (radius : ℝ≥0∞) ^ (eps / 4) * ((2 : ℝ≥0∞)⁻¹ * lam) ≤
      fullness' B (fun i => (W i).toShadedBody) := by
    rw [hcast] at hfullU
    calc
      _ ≤ (radius : ℝ≥0∞) ^ (eps / 4) *
          ((radius : ℝ≥0∞) ^ (-(eps / 4)) * fullness' B (fun i => (W i).toShadedBody)) :=
        mul_le_mul' le_rfl (hfullBZ.trans hfullU)
      _ = _ := by rw [← mul_assoc, ← ENNReal.rpow_add _ _ hr0 hrTop]; simp
  have hpowerLam : (2 : ℝ≥0∞)⁻¹ * (radius : ℝ≥0∞) ^ (5 * eps / 4) ≤
      (radius : ℝ≥0∞) ^ (eps / 4) * ((2 : ℝ≥0∞)⁻¹ * lam) := by
    calc
      _ = (radius : ℝ≥0∞) ^ (eps / 4) * ((2 : ℝ≥0∞)⁻¹ * (radius : ℝ≥0∞) ^ eps) := by
        have hp : (radius : ℝ≥0∞) ^ (eps / 4) * (radius : ℝ≥0∞) ^ eps =
            (radius : ℝ≥0∞) ^ (5 * eps / 4) := by
          rw [← ENNReal.rpow_add _ _ hr0 hrTop]
          congr 1
          ring
        rw [← hp]
        ring
      _ ≤ _ := mul_le_mul' le_rfl (mul_le_mul' le_rfl hfull)
  have hcountStrong : ((2 : ℝ≥0∞)⁻¹ * (radius : ℝ≥0∞) ^ (5 * eps / 4)) *
      (A.card : ℝ≥0∞) ≤ (B.card : ℝ≥0∞) :=
    (mul_le_mul' hpowerLam le_rfl).trans hcardLower
  have hpowerCard : (radius : ℝ≥0∞) ^ (3 * eps / 2) ≤
      (2 : ℝ≥0∞)⁻¹ * (radius : ℝ≥0∞) ^ (5 * eps / 4) := by
    convert hhalfPower (5 * eps / 4) using 1; congr 1; ring
  have hcardPaidE := (mul_le_mul' hpowerCard (le_refl (A.card : ℝ≥0∞))).trans hcountStrong
  have hcardPaid : (radius : ℝ) ^ (3 * eps / 2) * (A.card : ℝ) ≤ (B.card : ℝ) := by
    have h := ENNReal.toReal_mono (by finiteness : (B.card : ℝ≥0∞) ≠ ⊤) hcardPaidE
    have hx : ((radius : ℝ≥0∞) ^ (3 * eps / 2)).toReal = (radius : ℝ) ^ (3 * eps / 2) := by
      rw [← hcast, ENNReal.toReal_ofReal (Real.rpow_nonneg hrR.le _)]
    simpa only [ENNReal.toReal_mul, hx, ENNReal.toReal_natCast] using h
  have hfullPaid : (radius : ℝ≥0∞) ^ (2 * eps) ≤ fullness' B (fun i => (W i).toShadedBody) :=
    (ENNReal.rpow_le_rpow_of_exponent_ge hr1 (by linarith only [heps] :
      3 * eps / 2 ≤ 2 * eps)).trans (hpowerCard.trans (hpowerLam.trans hfullW))
  have hcarW : (∑ i ∈ B, volume (W i).carrier) = (B.card : ℝ≥0∞) * v := by
    have hbody : ∀ i, (W i).carrier = (Z i).carrier :=
      fun i => congrArg (fun T : Tube radius E => T.carrier) (hWTube i)
    simp_rw [hbody]
    exact hcar B
  have hmassW : (∑ i ∈ B, volume (W i).shade) =
      fullness' B (fun i => (W i).toShadedBody) * ((B.card : ℝ≥0∞) * v) := by
    rw [sum_volumeReal_shade_eq_fullness_mul B (fun i => (W i).toShadedBody),
      coe_fullness, hcarW]
  have hmassLower : (4 : ℝ≥0∞)⁻¹ * (radius : ℝ≥0∞) ^ (eps / 2) * lam *
      (∑ i ∈ A, volume (Z i).shade) ≤ ∑ i ∈ B, volume (W i).shade := by
    rw [hmass, hmassW]
    calc
      _ = ((radius : ℝ≥0∞) ^ (eps / 4) * ((2 : ℝ≥0∞)⁻¹ * lam)) *
          (((radius : ℝ≥0∞) ^ (eps / 4) * ((2 : ℝ≥0∞)⁻¹ * lam) * (A.card : ℝ≥0∞)) * v) := by
        have hp : (radius : ℝ≥0∞) ^ (eps / 4) * (radius : ℝ≥0∞) ^ (eps / 4) =
            (radius : ℝ≥0∞) ^ (eps / 2) := by
          rw [← ENNReal.rpow_add _ _ hr0 hrTop]
          congr 1
          ring
        calc
          _ = (4 : ℝ≥0∞)⁻¹ * ((radius : ℝ≥0∞) ^ (eps / 4) *
              (radius : ℝ≥0∞) ^ (eps / 4)) * lam * (lam * ((A.card : ℝ≥0∞) * v)) := by rw [hp]
          _ = _ := by
            have hc : (4 : ℝ≥0∞)⁻¹ = (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ := by
              rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
              norm_num
            rw [hc]
            ring
      _ ≤ _ := mul_le_mul' hfullW (mul_le_mul' hcardLower le_rfl)
  have hmassPaid : (radius : ℝ≥0∞) ^ (2 * eps) * (∑ i ∈ A, volume (Z i).shade) ≤
      ∑ i ∈ B, volume (W i).shade := by
    apply le_trans _ hmassLower
    apply mul_le_mul' _ le_rfl
    calc
      _ ≤ (4 : ℝ≥0∞)⁻¹ * (radius : ℝ≥0∞) ^ (3 * eps / 2) := hquarterPower
      _ = (4 : ℝ≥0∞)⁻¹ * (radius : ℝ≥0∞) ^ (eps / 2) * (radius : ℝ≥0∞) ^ eps := by
        rw [mul_assoc, ← ENNReal.rpow_add _ _ hr0 hrTop]
        congr 2
        ring
      _ ≤ _ := mul_le_mul' le_rfl hfull
  let L : ℝ≥0 := 2 * radius ^ (-(5 * eps / 4))
  have hL : (A.card : ℝ≥0) ≤ L * (B.card : ℝ≥0) := by
    apply ENNReal.coe_le_coe.mp
    simp only [L, ENNReal.coe_mul, ENNReal.coe_ofNat, ENNReal.coe_natCast,
      ENNReal.coe_rpow_of_ne_zero hr.ne']
    calc
      _ = (2 * (radius : ℝ≥0∞) ^ (-(5 * eps / 4))) *
          (((2 : ℝ≥0∞)⁻¹ * (radius : ℝ≥0∞) ^ (5 * eps / 4)) * (A.card : ℝ≥0∞)) := by
        calc
          _ = (2 * (2 : ℝ≥0∞)⁻¹) * ((radius : ℝ≥0∞) ^ (-(5 * eps / 4)) *
              (radius : ℝ≥0∞) ^ (5 * eps / 4)) * (A.card : ℝ≥0∞) := by
            rw [← ENNReal.rpow_add _ _ hr0 hrTop,
              ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
            simp
          _ = _ := by ring
      _ ≤ _ := mul_le_mul' le_rfl hcountStrong
  let VZ := V.tubeUniform.copyTubes (fun i => (hWTube i).symm)
  have htransfer := mixed_grid_frostman_transfer_w110 hdim hr hradius1 G.numerics.M_pos
    (Nat.succ_le_iff.mpr (hJ hr hrJ).1) A B Z hA hB hBA hball hCtw U hregular VZ hL hEvery
  have hprice : (trialNearbyParentCountW96 Ctw : ℝ≥0∞) *
      ((Tube.volume_le.C 3 / Tube.le_volume.c 3 : ℝ≥0) : ℝ≥0∞) *
      (Cwork : ℝ≥0∞) ^ (2 : Nat) * (Ccap : ℝ≥0∞) ^ (3 : Nat) *
      (L : ℝ≥0∞) * (radius : ℝ≥0∞) ^ (-(8 : ℝ) / (G.M : ℝ)) *
      ((BF : ℝ≥0∞) ^ (G.p.N + 1) * (radius : ℝ≥0∞) ^ (-3 * eps)) ≤
        (radius : ℝ≥0∞) ^ (-5 * eps) := by
    calc
      _ = (K : ℝ≥0∞) * (radius : ℝ≥0∞) ^ (-(5 * eps / 4)) *
          (radius : ℝ≥0∞) ^ (-(8 : ℝ) / (G.M : ℝ)) *
          (radius : ℝ≥0∞) ^ (-3 * eps) := by
        simp only [K, L, ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_ofNat, ENNReal.coe_natCast,
          ENNReal.coe_rpow_of_ne_zero hr.ne']
        ring
      _ ≤ (radius : ℝ≥0∞) ^ (-(eps / 2)) * (radius : ℝ≥0∞) ^ (-(5 * eps / 4)) *
          (radius : ℝ≥0∞) ^ (-(eps / 4)) * (radius : ℝ≥0∞) ^ (-3 * eps) := by
        apply mul_le_mul' _ le_rfl
        apply mul_le_mul' (mul_le_mul' hK le_rfl)
        exact ENNReal.rpow_le_rpow_of_exponent_ge hr1
          (by simpa only [neg_div] using neg_le_neg hmesh)
      _ = _ := by
        rw [← ENNReal.rpow_add _ _ hr0 hrTop, ← ENNReal.rpow_add _ _ hr0 hrTop,
          ← ENNReal.rpow_add _ _ hr0 hrTop]
        congr 1
        ring
  have hVEvery : V.tubeUniform.IsFrostmanAtEveryScale ((radius : ℝ≥0∞) ^ (-5 * eps)) := by
    have hpaid := htransfer.mono hprice
    have hbody : ∀ i, (W i).toConvexSpaceBody = (Z i).toConvexSpaceBody :=
      fun i => congrArg Tube.toConvexSpaceBody (hWTube i)
    intro k hk j hj
    simpa only [VZ, Tube.UniformTubeSet.copyTubes, hbody] using hpaid k hk j hj
  have hWBall : ∀ i ∈ B, (W i).carrier ⊆ Metric.closedBall 0 1 := by
    intro i hi
    rw [hWTube i]
    exact hball i (hBA hi)
  have hstickyFull : (radius : ℝ≥0∞) ^ S.etaStar ≤
      (fullness B (fun i => (W i).toShadedBody) : ℝ≥0∞) := by
    rw [coe_fullness]
    apply le_trans _ hfullPaid
    exact ENNReal.rpow_le_rpow_of_exponent_ge hr1
      (by have hm := G.sticky_margin; have hs := S.etaStar_pos; dsimp only [eps]; linarith)
  have hstickyEvery := hVEvery.mono (ENNReal.rpow_le_rpow_of_exponent_ge hr1
    (by have hm := G.sticky_margin; have hs := S.etaStar_pos; dsimp only [eps]; linarith :
      -S.etaStar ≤ -5 * eps))
  have hunion := hsticky B W hWBall le_rfl V hstickyFull hstickyEvery
  exact ⟨B, W, V, hB, hBA, hWTube, hWShade, hcardPaid, hmassPaid, hfullPaid, hVEvery, hunion⟩

end

end Kakeya.ml1Boot.FixedMStickyExitW110

namespace Kakeya.ml1Boot.RevisedSourceRepairW110

noncomputable section
set_option autoImplicit false

universe uE uI

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open TrialRestartW94

private theorem eventually_original_good_payment_w111
    {xi c gamma accuracy : ℝ}
    (hxi : 0 < xi) (hc : 0 < c) (hcx : c <= xi)
    (hgamma : gamma ∈ Set.Icc (0 : ℝ) 1)
    (haccuracy : 0 < accuracy)
    (K : ℝ≥0∞) (hK : K ≠ ⊤) :
    ∀ᶠ (delta : ℝ≥0) in 𝓝[>] 0,
      ∀ (n : Nat), 1 <= n ->
      K * (delta : ℝ≥0∞) ^ (16 * xi) *
          (delta : ℝ≥0∞) ^ (-2 * gamma) *
          ((n : ℝ≥0∞) * (delta : ℝ≥0∞) ^ (2 : Nat)) ^ (1 - gamma / 2) <=
        (delta : ℝ≥0∞) ^ (-accuracy / 4 - 2 * (gamma - c)) *
          ((n : ℝ≥0∞) * (delta : ℝ≥0∞) ^ (2 : Nat)) ^
            (1 - (gamma - c) / 2) := by
  have hgap : 3 * c - accuracy / 4 < 16 * xi := by
    linarith only [hcx, hxi, haccuracy]
  filter_upwards [eventually_mul_rpow_le_rpow hK hgap,
    self_mem_nhdsWithin] with delta hpay hd
  have hdpos : 0 < delta := hd
  have hd0 : (delta : ℝ≥0∞) ≠ 0 := (ENNReal.coe_pos.mpr hdpos).ne'
  have hdtop : (delta : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hq : 0 <= 1 - gamma / 2 := by linarith only [hgamma.2]
  have hr : 0 <= c / 2 := (half_pos hc).le
  intro n hn
  let X : ℝ≥0∞ := (n : ℝ≥0∞) * (delta : ℝ≥0∞) ^ (2 : Nat)
  have hnE : (1 : ℝ≥0∞) <= n := by exact_mod_cast hn
  have hX : (delta : ℝ≥0∞) ^ (2 : Nat) <= X :=
    le_mul_of_one_le_left zero_le hnE
  have hgain : (delta : ℝ≥0∞) ^ c <= X ^ (c / 2) := by
    calc
      (delta : ℝ≥0∞) ^ c = ((delta : ℝ≥0∞) ^ (2 : Nat)) ^ (c / 2) := by
        rw [← ENNReal.rpow_natCast_mul]
        congr 1
        norm_num
        ring
      _ <= X ^ (c / 2) := ENNReal.rpow_le_rpow hX hr
  have hsplit : (delta : ℝ≥0∞) ^ (3 * c - accuracy / 4) *
      (delta : ℝ≥0∞) ^ (-2 * gamma) =
      (delta : ℝ≥0∞) ^ (-accuracy / 4 - 2 * (gamma - c)) *
        (delta : ℝ≥0∞) ^ c := by
    rw [← ENNReal.rpow_add _ _ hd0 hdtop, ← ENNReal.rpow_add _ _ hd0 hdtop]
    congr 1
    ring
  calc
    K * (delta : ℝ≥0∞) ^ (16 * xi) * (delta : ℝ≥0∞) ^ (-2 * gamma) *
        X ^ (1 - gamma / 2) <=
        (delta : ℝ≥0∞) ^ (3 * c - accuracy / 4) *
          (delta : ℝ≥0∞) ^ (-2 * gamma) * X ^ (1 - gamma / 2) :=
      mul_le_mul' (mul_le_mul' hpay le_rfl) le_rfl
    _ = (delta : ℝ≥0∞) ^ (-accuracy / 4 - 2 * (gamma - c)) *
        ((delta : ℝ≥0∞) ^ c * X ^ (1 - gamma / 2)) := by
      rw [hsplit, mul_assoc]
    _ <= (delta : ℝ≥0∞) ^ (-accuracy / 4 - 2 * (gamma - c)) *
        (X ^ (c / 2) * X ^ (1 - gamma / 2)) :=
      mul_le_mul' le_rfl (mul_le_mul' hgain le_rfl)
    _ = (delta : ℝ≥0∞) ^ (-accuracy / 4 - 2 * (gamma - c)) *
        X ^ (1 - (gamma - c) / 2) := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ hr hq]
      congr 2
      ring

/-- The Main Lemma 1 construction. Constants are chosen before A, A
before I, and all before delta and the family. The same-mass two-scale
construction, actual eligible Inner Trial calls, good/drop alternatives,
persistent canonical restart and final exponent payment belong here.
There is no supplied analytic callback, trace or original-s conclusion. -/
theorem exists_certified_original_runs_w110 [Nontrivial E]
    (hdim : Module.finrank ℝ E = 3)
    {beta gammaZero : ℝ} (hbeta : 0 <= beta)
    (hgammaZero : gammaZero ∈ Set.Ioc beta 1)
    (S : StickyWitnessW110.{uE, uI} E gammaZero)
    (G : SourceStructureW110 beta gammaZero S.etaStar)
    {gamma : ℝ} (hgamma : gamma ∈ Set.Icc gammaZero 1)
    (hKT : KatzTaoEstimate.{uI} E beta) (hKF : FrostmanEstimate.{uI} E gamma)
    {accuracy : ℝ} (haccuracy : 0 < accuracy) :
    ∃ (Ctw Ccell : ℝ≥0), 1 <= Ctw ∧ 1 <= Ccell ∧
      ∃ (A : AnalyticScheduleW110.{uE, uI} (E := E) G gamma Ctw Ccell)
        (I : InputChoiceW110 A accuracy),
        ∀ᶠ (delta : ℝ≥0) in 𝓝[>] 0,
          ∀ {iota : Type uI} (s : Finset iota) (Y : iota -> ShadedTube delta E),
            OriginalInputW110 s Y I.inputEta ->
            BandedInputW110 s Y I.workingEta ->
            Nonempty (OriginalRunW110 s Y gamma G.p.c accuracy) := by
  classical
  have hp := G.numerics
  have heps := hp.epsilon_pos
  have hxi := hp.xiMin_pos
  have hstep := source_step_positive_w110 G
  have hgammaPos : 0 < gamma := (hbeta.trans_lt hgammaZero.1).trans_le hgamma.1
  have hq : 0 <= 1 - gamma / 2 := by linarith [hgamma.2]
  obtain ⟨_, _, hKTPrime⟩ := shifted_estimate_for_source_w110 hbeta hgammaZero hKT
  obtain ⟨Cline, hCline, hline⟩ := eventually_source_line_budget_of_protected_ED_w103 hdim
  obtain ⟨A0, F0, hA0, hF0, hcentre⟩ := exists_source_centring_reduction_w101 (E := E) hdim
  have hA01 : 1 <= A0 := by rw [hA0]; norm_num
  have hF01 : 1 <= F0 := by rw [hF0]; norm_num
  let bLoss := min G.xiMin (min (G.p.ε / 4) (accuracy / 100))
  have hbLoss : 0 < bLoss := lt_min hxi (lt_min (by positivity) (by positivity))
  have hbLossXi : bLoss <= G.xiMin := min_le_left _ _
  have hbLossEps : bLoss <= G.p.ε / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hbLossAccuracy : bLoss <= accuracy / 100 :=
    (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨Cgood, Cwork, Ctw, Ccell, BF, eInput, deltaRun,
    hCgood, hCwork, hCtw, hCcell, hBF, heInput, heInputSmall,
    hdeltaRun, hdeltaRun1, hRun⟩ :=
    exists_source_input_alternative_w104 hdim hp hgamma hKTPrime hKF A0 hA01 bLoss hbLoss
  obtain ⟨A⟩ := exists_actual_analytic_schedule_w110 hdim G hgamma hKT hKF Ctw Ccell hCtw hCcell
  obtain ⟨J⟩ := exists_input_choice_w110 A haccuracy
  let working := min J.workingEta (min (eInput / 4) (G.xiMin / 100))
  have hw : 0 < working := lt_min J.working_pos (lt_min (by positivity) (by positivity))
  have hwJ : working <= J.workingEta := min_le_left _ _
  have hwInput : working <= eInput / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hwXi : working <= G.xiMin / 100 := (min_le_right _ _).trans (min_le_right _ _)
  let I : InputChoiceW110 A accuracy :=
    { workingEta := working
      inputEta := working / 8
      working_pos := hw
      input_pos := by positivity
      input_eq := rfl
      ladder_reserve := hwJ.trans J.ladder_reserve
      sticky_reserve := hwJ.trans J.sticky_reserve
      inner_reserve := fun m hm => hwJ.trans (J.inner_reserve m hm)
      gain_reserve := hwJ.trans J.gain_reserve
      cf_reserve := fun m hm => hwJ.trans (J.cf_reserve m hm)
      KT_reserve := hwJ.trans J.KT_reserve
      KF_reserve := hwJ.trans J.KF_reserve
      requested_loss_reserve := hwJ.trans J.requested_loss_reserve
      unit_reserve := hwJ.trans J.unit_reserve }
  let B : ℝ≥0 := F0 * Cline
  have hB : 1 <= B := one_le_mul hF01 hCline
  have hB0 : (B : ℝ≥0∞) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hB))
  have hfullPay := eventually_mul_rpow_le_rpow (K := (384 : ℝ≥0∞) * B)
    (by finiteness) (show eInput / 4 < eInput / 2 by linarith)
  have hCFPay := eventually_mul_rpow_le_rpow (K := (196608 : ℝ≥0∞) * B)
    (by finiteness) (show -eInput < -(eInput / 4) by linarith)
  let Kgood : ℝ≥0∞ := (B : ℝ≥0∞) * Cgood * (2 : ℝ≥0∞) ^ (2 * gamma)
  have hGoodPayment : ∀ᶠ (delta : ℝ≥0) in 𝓝[>] 0,
      ∀ n : Nat, 1 <= n ->
        Kgood * (delta : ℝ≥0∞) ^ (16 * G.xiMin) *
            (delta : ℝ≥0∞) ^ (-2 * gamma) *
            ((n : ℝ≥0∞) * (delta : ℝ≥0∞) ^ (2 : Nat)) ^ (1 - gamma / 2) <=
          (delta : ℝ≥0∞) ^ (-accuracy / 4 - 2 * (gamma - G.p.c)) *
            ((n : ℝ≥0∞) * (delta : ℝ≥0∞) ^ (2 : Nat)) ^
              (1 - (gamma - G.p.c) / 2) := by
    exact eventually_original_good_payment_w111 hxi hstep.1 hstep.2.2.2.1
      ⟨hgammaPos.le, hgamma.2⟩ haccuracy Kgood (by dsimp only [Kgood]; finiteness)
  have hStickyUnion : ∀ᶠ (radius : ℝ≥0) in 𝓝[>] 0,
      ∀ {iota : Type uI} [DecidableEq iota]
        (T : Finset iota) (W : iota -> ShadedTube radius E)
        (U : RevisedLiteralProfileInterfaceFormalizerW87.CanonicalProfileNetW87
          T (fun i => (W i).toTube) G.M Cwork),
        T.Nonempty -> (∀ i ∈ T, (W i).carrier ⊆ Metric.closedBall 0 1) ->
        (T.card : ℝ) <= (radius : ℝ) ^ (-7 : ℝ) ->
        (radius : ℝ≥0∞) ^ G.p.ε <= fullness' T (fun i => (W i).toShadedBody) ->
        SourceRegularizedWorkingTowerW95 U Ctw Ccell ->
        U.IsFrostmanAtEveryScale
          ((BF : ℝ≥0∞) ^ (G.p.N + 1) * (radius : ℝ≥0∞) ^ (-3 * G.p.ε)) ->
        (radius : ℝ≥0∞) ^ (gammaZero / 4) <= volume (⋃ i ∈ T, (W i).shade) := by
    have hexit := FixedMStickyExitW110.eventually_fixed_m_sticky_exit_w110
      hdim S G Cwork Ctw Ccell BF hCwork hCtw hCcell hBF
    filter_upwards [hexit] with radius hfinal
    intro iota _ T W U hT hball hcard hfull hregular hevery
    obtain ⟨Bnew, Wnew, Vnew, hBnew, hBT, hsameNew, hshadeNew,
      hcardNew, hmassNew, hfullNew, hfrostmanNew, hvolumeNew⟩ :=
      hfinal T W U hT hball hcard hfull hregular hevery
    apply hvolumeNew.trans
    apply measure_mono
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨i, hBT hi, hshadeNew i hxi⟩
  obtain ⟨deltaSticky, hdeltaSticky, hStickyAt⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp hStickyUnion
  have hCardPay := eventually_mul_rpow_le_rpow (K := (cardBound.C : ℝ≥0∞))
    ENNReal.coe_ne_top (show (-7 : ℝ) < -4 by norm_num)
  let Cvol : ℝ≥0∞ := Tube.volume_le.C (Module.finrank ℝ E)
  let Ccard : ℝ≥0∞ := cardBound.C
  let Ksticky : ℝ≥0∞ := Cvol * Ccard * (2 : ℝ≥0∞) ^ (gammaZero / 4)
  have hStickyPay := eventually_finite_const_le_rpow_neg (c := Ksticky)
    (by dsimp only [Ksticky, Cvol, Ccard]; finiteness)
    (show 0 < accuracy / 4 by positivity)
  refine ⟨Ctw, Ccell, hCtw, hCcell, A, I, ?_⟩
  filter_upwards [hline, hfullPay, hCFPay, hGoodPayment, hCardPay, hStickyPay, self_mem_nhdsWithin,
    eventually_le_nhdsGT (show (0 : ℝ≥0) < deltaRun / 2 by positivity),
    eventually_le_nhdsGT (half_pos hdeltaSticky),
    eventually_le_nhdsGT (show (0 : ℝ≥0) < 1 / 200 by norm_num)] with
    delta hline hfullPay hCFPay hGoodPayment hCardPay hStickyPay hd hdRun hdSticky hdsmall
  intro iota s Y hinput band
  have hdpos : 0 < delta := hd
  have hd1 : delta <= 1 := hdsmall.trans
    (div_le_self (show (0 : ℝ≥0) <= 1 from zero_le) (by norm_num))
  have hd0 : (delta : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hd.ne'
  have hd1E : (delta : ℝ≥0∞) <= 1 := by exact_mod_cast hd1
  have hr : 0 < delta / 2 := div_pos hdpos (by norm_num)
  have hrdelta : delta / 2 <= delta := div_le_self (show (0 : ℝ≥0) <= delta from zero_le) (by norm_num)
  have hr1 : delta / 2 <= 1 := hrdelta.trans hd1
  have hrRun : delta / 2 < deltaRun :=
    (hrdelta.trans hdRun).trans_lt (by exact half_lt_self hdeltaRun)
  have hs : s.Nonempty := band.nonempty.mono band.subset
  have hbandBall := fun i hi => hinput.ball i (band.subset hi)
  have hbandED := hinput.essentially_distinct.mono (Finset.coe_subset.mpr band.subset)
  obtain ⟨F, parent, Z, hF, hFband, himage, hballZ, hcentredZ, hlineZ,
    hcoverZ, hfibres, hvolZ, hshadeZ, hunionZ, hunionVolZ,
    hcardZLower, hcardZ, hmuZLower, hmuZUpper, hfullZ, hmaxZ, hmassZ⟩ :=
    hcentre hd hdsmall band.s2 Y Cline hCline band.nonempty hbandBall
      (hline band.s2 (fun i => (Y i).toTube) hbandBall hbandED)
  have hballZ1 : ∀ j ∈ F, (Z j).carrier ⊆ Metric.closedBall 0 1 := by
    intro j hj
    exact (hballZ j hj).trans (Metric.closedBall_subset_closedBall (by norm_num))
  have hbandFull : (delta : ℝ≥0∞) ^ working <=
      fullness' band.s2 (fun i => (Y i).toShadedBody) := by
    simpa only [← ShadedBody.coe_fullness] using
      band.hereditary_fullness band.s2 Finset.Subset.rfl band.nonempty
  have hfullInput : ((delta / 2 : ℝ≥0) : ℝ≥0∞) ^ eInput <=
      fullness' F (fun i => (Z i).toShadedBody) := by
    have hlower : (delta : ℝ≥0∞) ^ (eInput / 2) <=
        fullness' F (fun i => (Z i).toShadedBody) := by
      have hpaid : ((384 : ℝ≥0∞) * B) * (delta : ℝ≥0∞) ^ (eInput / 2) <=
          fullness' band.s2 (fun i => (Y i).toShadedBody) :=
        hfullPay.trans ((ENNReal.rpow_le_rpow_of_exponent_ge hd1E hwInput).trans hbandFull)
      have hdivide : (delta : ℝ≥0∞) ^ (eInput / 2) <=
          fullness' band.s2 (fun i => (Y i).toShadedBody) /
            ((384 : ℝ≥0∞) * B) := by
        apply (ENNReal.le_div_iff_mul_le (Or.inl (by simp [hB0]))
          (Or.inl (by finiteness))).mpr
        simpa only [mul_comm] using hpaid
      exact hdivide.trans (by simpa only [B, ENNReal.coe_mul, mul_assoc] using hfullZ)
    exact (ENNReal.rpow_le_rpow (by exact_mod_cast hrdelta) heInput.le).trans
      ((ENNReal.rpow_le_rpow_of_exponent_ge hd1E (by linarith)).trans hlower)
  have hCFZ : frostmanConstIn F (fun i => (Z i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall <=
        (196608 : ℝ≥0∞) * B * (delta : ℝ≥0∞) ^ (-working) := by
    have h := centred_image_frostman_w103 hdim hdsmall band.s2 band.nonempty
      (fun i => (Y i).toTube) parent (fun i => (Z i).toTube) B hbandBall
      (by simpa only [himage] using hballZ1) hcoverZ
      (by simpa only [himage, B] using hfibres)
    rw [himage] at h
    simp only [← frostmanConstIn_eq_frostmanConstant] at h
    exact h.trans (mul_le_mul' le_rfl band.frostman)
  have hCFInput : frostmanConstIn F (fun i => (Z i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall <= ((delta / 2 : ℝ≥0) : ℝ≥0∞) ^ (-eInput) := by
    calc
      _ <= (196608 : ℝ≥0∞) * B * (delta : ℝ≥0∞) ^ (-working) := hCFZ
      _ <= (196608 : ℝ≥0∞) * B * (delta : ℝ≥0∞) ^ (-(eInput / 4)) :=
        mul_le_mul' le_rfl (ENNReal.rpow_le_rpow_of_exponent_ge hd1E (by linarith))
      _ <= (delta : ℝ≥0∞) ^ (-eInput) := hCFPay
      _ <= _ := by
        rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
        exact ENNReal.inv_le_inv.mpr
          (ENNReal.rpow_le_rpow (by exact_mod_cast hrdelta) heInput.le)
  have hmassOriginal : (∑ i ∈ s, volume (Y i).shade) <=
      (delta : ℝ≥0∞) ^ (-working) * (∑ i ∈ band.s2, volume (Y i).shade) := by
    rw [ENNReal.rpow_neg]
    have hp0 : (delta : ℝ≥0∞) ^ working ≠ 0 := by simp [ENNReal.rpow_eq_zero_iff, hd0]
    have hpTop : (delta : ℝ≥0∞) ^ working ≠ ⊤ := by finiteness
    calc
      _ = ((delta : ℝ≥0∞) ^ working)⁻¹ *
          ((delta : ℝ≥0∞) ^ working * (∑ i ∈ s, volume (Y i).shade)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hp0 hpTop, one_mul]
      _ <= _ := mul_le_mul_right band.original_mass_retention _
  have hmuOriginal : ShadedBody.multiplicity s (fun i => (Y i).toShadedBody) <=
      (delta : ℝ≥0∞) ^ (-working) * (B : ℝ≥0∞) *
        ShadedBody.multiplicity F (fun i => (Z i).toShadedBody) := by
    have hmu := multiplicity_le_mul_of_subset_of_shade_mass band.subset
      (fun i => (Y i).toShadedBody) hmassOriginal
    calc
      _ <= (delta : ℝ≥0∞) ^ (-working) *
          ShadedBody.multiplicity band.s2 (fun i => (Y i).toShadedBody) := hmu
      _ <= (delta : ℝ≥0∞) ^ (-working) * ((B : ℝ≥0∞) *
          ShadedBody.multiplicity F (fun i => (Z i).toShadedBody)) :=
        mul_le_mul_right (by simpa only [B, ENNReal.coe_mul] using hmuZUpper) _
      _ = _ := by rw [mul_assoc]
  have hFS : F ⊆ s := hFband.trans band.subset
  have hcardFS : F.card <= s.card := Finset.card_le_card hFS
  have hscalar : ShadedBody.multiplicity s (fun i => (Y i).toShadedBody) <=
      (delta : ℝ≥0∞) ^ (-accuracy / 4 - 2 * (gamma - G.p.c)) *
        ((s.card : ℝ≥0∞) * (delta : ℝ≥0∞) ^
          (Module.finrank ℝ E - 1)) ^ (1 - (gamma - G.p.c) / 2) := by
    rcases hRun hr hrRun F Z hF hballZ1 hcentredZ hlineZ hfullInput hCFInput with
      hgood | hevery
    · have hgain : 0 <= 18 * G.xiMin - bLoss := by linarith
      have hscaleGain : ((delta / 2 : ℝ≥0) : ℝ≥0∞) ^ (18 * G.xiMin - bLoss) <=
          (delta : ℝ≥0∞) ^ (18 * G.xiMin - bLoss) :=
        ENNReal.rpow_le_rpow (by exact_mod_cast hrdelta) hgain
      have hscaleNegative : ((delta / 2 : ℝ≥0) : ℝ≥0∞) ^ (-2 * gamma) =
          (delta : ℝ≥0∞) ^ (-2 * gamma) * (2 : ℝ≥0∞) ^ (2 * gamma) := by
        rw [← ENNReal.coe_rpow_of_ne_zero hr.ne', NNReal.div_rpow,
          ENNReal.coe_div (by simp), ENNReal.coe_rpow_of_ne_zero hdpos.ne',
          ENNReal.coe_rpow_of_ne_zero (by norm_num : (2 : ℝ≥0) ≠ 0)]
        norm_num only [ENNReal.coe_ofNat]
        rw [show -2 * gamma = -(2 * gamma) by ring, ENNReal.rpow_neg (2 : ℝ≥0∞),
          div_eq_mul_inv, inv_inv]
      have hscaledCard : (F.card : ℝ≥0∞) * ((delta / 2 : ℝ≥0) : ℝ≥0∞) ^ (2 : Nat) <=
          (s.card : ℝ≥0∞) * (delta : ℝ≥0∞) ^ (2 : Nat) := by
        exact mul_le_mul' (by exact_mod_cast hcardFS)
          (pow_le_pow_left' (by exact_mod_cast hrdelta) 2)
      have hrow : ShadedBody.multiplicity s (fun i => (Y i).toShadedBody) <=
          Kgood * (delta : ℝ≥0∞) ^ (16 * G.xiMin) * (delta : ℝ≥0∞) ^ (-2 * gamma) *
            ((s.card : ℝ≥0∞) * (delta : ℝ≥0∞) ^ (2 : Nat)) ^ (1 - gamma / 2) := by
        calc
          _ <= (delta : ℝ≥0∞) ^ (-working) * (B : ℝ≥0∞) *
              ((Cgood : ℝ≥0∞) * ((delta / 2 : ℝ≥0) : ℝ≥0∞) ^ (18 * G.xiMin - bLoss) *
                ((delta / 2 : ℝ≥0) : ℝ≥0∞) ^ (-2 * gamma) *
                ((F.card : ℝ≥0∞) * ((delta / 2 : ℝ≥0) : ℝ≥0∞) ^ (2 : Nat)) ^
                  (1 - gamma / 2)) :=
            hmuOriginal.trans (mul_le_mul_right hgood _)
          _ <= (delta : ℝ≥0∞) ^ (-working) * (B : ℝ≥0∞) *
              ((Cgood : ℝ≥0∞) * (delta : ℝ≥0∞) ^ (18 * G.xiMin - bLoss) *
                ((delta : ℝ≥0∞) ^ (-2 * gamma) * (2 : ℝ≥0∞) ^ (2 * gamma)) *
                ((s.card : ℝ≥0∞) * (delta : ℝ≥0∞) ^ (2 : Nat)) ^ (1 - gamma / 2)) := by
            rw [hscaleNegative]
            gcongr
          _ = Kgood * ((delta : ℝ≥0∞) ^ (-working) *
                (delta : ℝ≥0∞) ^ (18 * G.xiMin - bLoss)) * (delta : ℝ≥0∞) ^ (-2 * gamma) *
                ((s.card : ℝ≥0∞) * (delta : ℝ≥0∞) ^ (2 : Nat)) ^ (1 - gamma / 2) := by
            dsimp only [Kgood]
            ring
          _ <= _ := by
            rw [← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
            exact mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl
              (ENNReal.rpow_le_rpow_of_exponent_ge hd1E (by linarith))) le_rfl) le_rfl
      exact hrow.trans (by simpa only [hdim] using hGoodPayment s.card hs.card_pos)
    · obtain ⟨T, W, U, hT, hTF, hsame, hshade, hretained, hregular, hfrostman⟩ := hevery
      have hTball : ∀ i ∈ T, (W i).carrier ⊆ Metric.closedBall 0 1 := by
        intro i hi
        rw [hsame i hi]
        exact hballZ1 i (hTF hi)
      have hcardOriginal : (s.card : ℝ≥0∞) <=
          (cardBound.C : ℝ≥0∞) * (delta : ℝ≥0∞) ^ (-4 : ℝ) :=
        card_le hdim hdpos hd1 s (fun i => (Y i).toTube) hinput.ball hinput.essentially_distinct
      have hcardT : (T.card : ℝ≥0∞) <= ((delta / 2 : ℝ≥0) : ℝ≥0∞) ^ (-7 : ℝ) := by
        calc
          _ <= (s.card : ℝ≥0∞) := by exact_mod_cast Finset.card_le_card (hTF.trans hFS)
          _ <= (delta : ℝ≥0∞) ^ (-7 : ℝ) := hcardOriginal.trans hCardPay
          _ <= _ := by
            rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
            exact ENNReal.inv_le_inv.mpr
              (ENNReal.rpow_le_rpow (by exact_mod_cast hrdelta) (by norm_num))
      have hcardTReal : (T.card : ℝ) <= ((delta / 2 : ℝ≥0) : ℝ) ^ (-7 : ℝ) := by
        have h := ENNReal.toReal_mono (by finiteness) hcardT
        simpa only [ENNReal.toReal_natCast, ← ENNReal.toReal_rpow, ENNReal.coe_toReal] using h
      obtain ⟨i0, hi0⟩ := hF
      obtain ⟨hv, hvTop⟩ := Tube.volume_pos_and_lt_top hr hr1 (Z i0).toTube
      have hrE : (0 : ℝ≥0∞) < (delta / 2 : ℝ≥0) := ENNReal.coe_pos.mpr hr
      obtain ⟨_, hfullT, _, _⟩ := retained_state_fullness_card_frostman_w94
        F T (fun i => (Z i).toShadedBody) (fun i => (W i).toShadedBody)
        ConvexSpaceBody.closedUnitBall (volume (Z i0).carrier)
        (((delta / 2 : ℝ≥0) : ℝ≥0∞) ^ eInput)
        (((delta / 2 : ℝ≥0) : ℝ≥0∞) ^ (-eInput))
        (((delta / 2 : ℝ≥0) : ℝ≥0∞) ^ bLoss)
        ⟨i0, hi0⟩ hTF hv hvTop
        (fun i hi => Tube.volume_carrier_eq_volume_carrier (Z i).toTube (Z i0).toTube)
        hballZ1 ConvexSpaceBody.closedUnitBall_volume_pos
        ConvexSpaceBody.closedUnitBall.isCompact.measure_lt_top
        (fun i hi => congrArg Tube.toConvexSpaceBody (hsame i hi)) hshade
        (ENNReal.rpow_pos hrE ENNReal.coe_ne_top) (by finiteness) hfullInput hCFInput
        (by finiteness) (ENNReal.rpow_pos hrE ENNReal.coe_ne_top) (by finiteness) hretained
      have heInputEps : eInput <= G.p.ε / 4 := by
        have hzeta := (hp.zeta_mono 0 G.p.N (Nat.zero_le _) le_rfl).trans hp.zeta_top
        linarith
      have hfullTEps : ((delta / 2 : ℝ≥0) : ℝ≥0∞) ^ G.p.ε <=
          fullness' T (fun i => (W i).toShadedBody) := by
        rw [← ENNReal.rpow_add _ _ hrE.ne' ENNReal.coe_ne_top] at hfullT
        exact (ENNReal.rpow_le_rpow_of_exponent_ge
          (by exact_mod_cast hr1) (by linarith)).trans hfullT
      have hrSticky : delta / 2 < deltaSticky :=
        (hrdelta.trans hdSticky).trans_lt (half_lt_self hdeltaSticky)
      have hvolumeT := hStickyAt ⟨hr, hrSticky⟩ T W U hT hTball hcardTReal hfullTEps
        hregular.some hfrostman
      have hunionTF : (⋃ i ∈ T, (W i).shade) ⊆ ⋃ i ∈ F, (Z i).shade := by
        intro x hx
        obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
        exact Set.mem_iUnion₂.mpr ⟨i, hTF hi, hshade i hi hxi⟩
      have hvolumeOriginal : ((delta / 2 : ℝ≥0) : ℝ≥0∞) ^ (gammaZero / 4) <=
          volume (⋃ i ∈ s, (Y i).shade) := by
        calc
          _ <= volume (⋃ i ∈ F, (Z i).shade) := hvolumeT.trans (measure_mono hunionTF)
          _ = (1 / 512 : ℝ≥0∞) * volume (⋃ i ∈ band.s2, (Y i).shade) := hunionVolZ
          _ <= volume (⋃ i ∈ band.s2, (Y i).shade) := by
            exact mul_le_of_le_one_left' (by norm_num)
          _ <= _ := measure_mono (Set.iUnion₂_subset fun i hi =>
            Set.subset_iUnion₂ (s := fun i (_ : i ∈ s) => (Y i).shade) i (band.subset hi))
      let advanced : ℝ := gamma - G.p.c
      let X : ℝ≥0∞ := (s.card : ℝ≥0∞) * (delta : ℝ≥0∞) ^ (2 : Nat)
      have ha0 : 0 < advanced := by
        dsimp only [advanced]
        linarith [hstep.2.2.1, hgamma.1, hgammaZero.1]
      have ha1 : advanced <= 1 := by dsimp only [advanced]; linarith [hgamma.2]
      have haGamma : gammaZero / 4 <= advanced := by
        dsimp only [advanced]
        linarith [hstep.2.2.1, hgamma.1]
      have hX0 : X ≠ 0 := by
        dsimp only [X]
        exact mul_ne_zero (by exact_mod_cast hs.card_pos.ne') (pow_ne_zero _ hd0)
      have hXTop : X ≠ ⊤ := by dsimp only [X]; finiteness
      have hXbound : X <= Ccard * (delta : ℝ≥0∞) ^ (-2 : ℝ) := by
        calc
          _ <= Ccard * (delta : ℝ≥0∞) ^ (-4 : ℝ) *
              (delta : ℝ≥0∞) ^ (2 : Nat) := mul_le_mul_left hcardOriginal _
          _ = _ := by
            rw [mul_assoc, ← ENNReal.rpow_natCast,
              ← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
            norm_num
      have hXpower : X ^ (advanced / 2) <= Ccard * (delta : ℝ≥0∞) ^ (-advanced) := by
        calc
          _ <= (Ccard * (delta : ℝ≥0∞) ^ (-2 : ℝ)) ^ (advanced / 2) :=
            ENNReal.rpow_le_rpow hXbound (by positivity)
          _ = Ccard ^ (advanced / 2) * (delta : ℝ≥0∞) ^ (-advanced) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
            congr 2
            ring
          _ <= _ := by
            apply mul_le_mul' _ le_rfl
            have hCcard : (1 : ℝ≥0∞) <= Ccard := ENNReal.one_le_coe_iff.mpr cardBound.one_le_C
            simpa only [ENNReal.rpow_one] using
              ENNReal.rpow_le_rpow_of_exponent_le hCcard (show advanced / 2 <= 1 by linarith)
      have hXsplit : X <= Ccard * (delta : ℝ≥0∞) ^ (-advanced) * X ^ (1 - advanced / 2) := by
        calc
          X = X ^ (advanced / 2) * X ^ (1 - advanced / 2) := by
            rw [← ENNReal.rpow_add _ _ hX0 hXTop,
              show advanced / 2 + (1 - advanced / 2) = (1 : ℝ) by ring, ENNReal.rpow_one]
          _ <= _ := mul_le_mul_left hXpower _
      have hscaleInv : (((delta / 2 : ℝ≥0) : ℝ≥0∞) ^ (gammaZero / 4))⁻¹ =
          (delta : ℝ≥0∞) ^ (-(gammaZero / 4)) * (2 : ℝ≥0∞) ^ (gammaZero / 4) := by
        rw [← ENNReal.rpow_neg, ← ENNReal.coe_rpow_of_ne_zero hr.ne', NNReal.div_rpow,
          ENNReal.coe_div (by simp), ENNReal.coe_rpow_of_ne_zero hdpos.ne',
          ENNReal.coe_rpow_of_ne_zero (by norm_num : (2 : ℝ≥0) ≠ 0)]
        norm_num only [ENNReal.coe_ofNat]
        rw [ENNReal.rpow_neg (2 : ℝ≥0∞), div_eq_mul_inv, inv_inv]
      have hbound := Kakeya.multiplicity_le_div_of_le_volume_iUnionShade hd1 s Y
        (ENNReal.rpow_pos hrE ENNReal.coe_ne_top) hvolumeOriginal
      change ShadedBody.multiplicity s (fun i => (Y i).toShadedBody) <=
        (delta : ℝ≥0∞) ^ (-accuracy / 4 - 2 * advanced) *
          ((s.card : ℝ≥0∞) * (delta : ℝ≥0∞) ^
            (Module.finrank ℝ E - 1)) ^ (1 - advanced / 2)
      rw [hdim]
      calc
        _ <= Cvol * X / (((delta / 2 : ℝ≥0) : ℝ≥0∞) ^ (gammaZero / 4)) := by
          simpa only [Cvol, X, hdim] using hbound
        _ <= Cvol * (Ccard * (delta : ℝ≥0∞) ^ (-advanced) * X ^ (1 - advanced / 2)) /
            (((delta / 2 : ℝ≥0) : ℝ≥0∞) ^ (gammaZero / 4)) :=
          ENNReal.div_le_div_right (mul_le_mul_right hXsplit _) _
        _ = Ksticky * (delta : ℝ≥0∞) ^ (-(gammaZero / 4)) *
            (delta : ℝ≥0∞) ^ (-advanced) * X ^ (1 - advanced / 2) := by
          rw [div_eq_mul_inv, hscaleInv]
          dsimp only [Ksticky]
          ring
        _ <= (delta : ℝ≥0∞) ^ (-(accuracy / 4)) * (delta : ℝ≥0∞) ^ (-(gammaZero / 4)) *
            (delta : ℝ≥0∞) ^ (-advanced) * X ^ (1 - advanced / 2) := by
          exact mul_le_mul' (mul_le_mul' (mul_le_mul' hStickyPay le_rfl) le_rfl) le_rfl
        _ = (delta : ℝ≥0∞) ^ (-accuracy / 4 - gammaZero / 4 - advanced) *
            X ^ (1 - advanced / 2) := by
          rw [← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top,
            ← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
          congr 2
          ring
        _ <= _ := mul_le_mul'
          (ENNReal.rpow_le_rpow_of_exponent_ge hd1E (by linarith)) le_rfl
  let terminal : RetainedStateW94 s Y :=
    { active := s
      shading := Y
      active_nonempty := hs
      active_subset := Finset.Subset.rfl
      same_tube := fun _ _ => rfl
      subshade := fun _ _ => Set.Subset.rfl
      retained := 1
      retained_pos := by norm_num
      retained_finite := by norm_num
      mass_retention := by simp }
  refine ⟨{ terminal := terminal, transport_budget := ?_, terminal_estimate := hscalar }⟩
  exact ENNReal.rpow_le_one hd1E (by positivity)

/-- Paid transport to the literal caller s, including its own cardinality. -/
theorem original_run_transport_w110 [Nontrivial E]
    {delta : ℝ≥0} (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    {iota : Type uI} (s : Finset iota) (Y : iota -> ShadedTube delta E)
    {gamma step accuracy eta : ℝ} (haccuracy : 0 < accuracy)
    (hadvanced : gamma - step ∈ Set.Icc (0 : ℝ) 1)
    (_hinput : OriginalInputW110 s Y eta)
    (run : OriginalRunW110 s Y gamma step accuracy) :
    ShadedBody.multiplicity s (fun i => (Y i).toShadedBody) <=
      (delta : ℝ≥0∞) ^ (-accuracy - 2 * (gamma - step)) *
        ((s.card : ℝ≥0∞) * (delta : ℝ≥0∞) ^
          (Module.finrank ℝ E - 1)) ^ (1 - (gamma - step) / 2) := by
  classical
  have hd0 : (delta : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hd1 : (delta : ℝ≥0∞) <= 1 := by exact_mod_cast hdelta_one
  have hp0 : (delta : ℝ≥0∞) ^ (accuracy / 4) ≠ 0 := by
    simp [ENNReal.rpow_eq_zero_iff, hd0]
  have hpTop : (delta : ℝ≥0∞) ^ (accuracy / 4) ≠ ⊤ := by finiteness
  have hmass : (∑ i ∈ s, volume (Y i).shade) <=
      (delta : ℝ≥0∞) ^ (-accuracy / 4) *
        (∑ i ∈ run.terminal.active, volume (run.terminal.shading i).shade) := by
    have hret := (mul_le_mul' run.transport_budget
      (le_refl (∑ i ∈ s, volume (Y i).shade))).trans run.terminal.mass_retention
    have hexp : -accuracy / 4 = -(accuracy / 4) := by ring
    rw [hexp, ENNReal.rpow_neg]
    calc
      _ = ((delta : ℝ≥0∞) ^ (accuracy / 4))⁻¹ *
          ((delta : ℝ≥0∞) ^ (accuracy / 4) *
            (∑ i ∈ s, volume (Y i).shade)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hp0 hpTop, one_mul]
      _ <= _ := mul_le_mul_right hret _
  have hunion : (⋃ i ∈ run.terminal.active, (run.terminal.shading i).shade) ⊆
      ⋃ i ∈ s, (Y i).shade := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr
      ⟨i, run.terminal.active_subset hi, run.terminal.subshade i hi hxi⟩
  have hmu := multiplicity_le_mul_of_shade_mass
    (fun i => (Y i).toShadedBody)
    (fun i => (run.terminal.shading i).toShadedBody) hunion hmass
  have hq : 0 <= 1 - (gamma - step) / 2 := by linarith [hadvanced.2]
  have hcard : (run.terminal.active.card : ℝ≥0∞) <= (s.card : ℝ≥0∞) := by
    exact_mod_cast Finset.card_le_card run.terminal.active_subset
  calc
    _ <= (delta : ℝ≥0∞) ^ (-accuracy / 4) *
        ShadedBody.multiplicity run.terminal.active
          (fun i => (run.terminal.shading i).toShadedBody) := hmu
    _ <= (delta : ℝ≥0∞) ^ (-accuracy / 4) *
        ((delta : ℝ≥0∞) ^ (-accuracy / 4 - 2 * (gamma - step)) *
          ((run.terminal.active.card : ℝ≥0∞) * (delta : ℝ≥0∞) ^
            (Module.finrank ℝ E - 1)) ^ (1 - (gamma - step) / 2)) :=
      mul_le_mul_right run.terminal_estimate _
    _ <= (delta : ℝ≥0∞) ^ (-accuracy / 4) *
        ((delta : ℝ≥0∞) ^ (-accuracy / 4 - 2 * (gamma - step)) *
          ((s.card : ℝ≥0∞) * (delta : ℝ≥0∞) ^
            (Module.finrank ℝ E - 1)) ^ (1 - (gamma - step) / 2)) := by
      gcongr
    _ = (delta : ℝ≥0∞) ^ (-accuracy / 2 - 2 * (gamma - step)) *
        ((s.card : ℝ≥0∞) * (delta : ℝ≥0∞) ^
          (Module.finrank ℝ E - 1)) ^ (1 - (gamma - step) / 2) := by
      rw [← mul_assoc, ← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
      congr 2
      ring
    _ <= _ := mul_le_mul' (ENNReal.rpow_le_rpow_of_exponent_ge hd1
      (by linarith)) le_rfl

/-- The input quantifier places eta as an output after
gamma, hKT, hKF and accuracy, and before delta or any tube family. -/
theorem source_structure_gives_frostman_w110 [Nontrivial E]
    (hdim : Module.finrank ℝ E = 3)
    {beta gammaZero : ℝ} (hbeta : 0 <= beta)
    (hgammaZero : gammaZero ∈ Set.Ioc beta 1)
    (S : StickyWitnessW110.{uE, uI} E gammaZero)
    (G : SourceStructureW110 beta gammaZero S.etaStar)
    {gamma : ℝ} (hgamma : gamma ∈ Set.Icc gammaZero 1)
    (hKT : KatzTaoEstimate.{uI} E beta) (hKF : FrostmanEstimate.{uI} E gamma) :
    FrostmanEstimate.{uI} E (gamma - G.p.c) := by
  intro accuracy haccuracy
  obtain ⟨Ctw, Ccell, hCtw, hCcell, A, I, hrun⟩ :=
    exists_certified_original_runs_w110 hdim hbeta hgammaZero S G hgamma hKT hKF haccuracy
  refine ⟨I.inputEta, I.input_pos, ?_⟩
  have hband := band_at_selected_working_exponent_w110 hdim I
  have hstep := source_step_positive_w110 G
  have hadvanced : gamma - G.p.c ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hgamma.1, hgamma.2, hgammaZero.1]
  filter_upwards [hrun, hband, self_mem_nhdsWithin,
    eventually_le_nhdsGT (show (0 : ℝ≥0) < 1 by norm_num)] with delta hrun hband hd hd1
  intro iota s Y hball hed hCF hfull
  have hinput : OriginalInputW110 s Y I.inputEta :=
    ⟨hball, hed, hCF, by
      rw [← ENNReal.coe_rpow_of_nonneg _ I.input_pos.le]
      exact ENNReal.coe_le_coe.mpr hfull⟩
  obtain ⟨band⟩ := hband s Y hinput
  obtain ⟨run⟩ := hrun s Y hinput band
  exact original_run_transport_w110 hd hd1 s Y haccuracy hadvanced hinput run

/-- Same statement shape and assumptions as `exists_uniform_step_general`. -/
theorem exists_uniform_step_general_from_revised_w110
    (hdim : Module.finrank ℝ E = 3)
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{uE, uI} (E := E))
    {beta gammaZero : ℝ} (hbeta : 0 <= beta)
    (hgammaZero : gammaZero ∈ Set.Ioc beta 1) :
    (frostmanStepSet.{uI} E beta gammaZero).Nonempty := by
  letI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by rw [hdim]; norm_num)
  obtain ⟨S⟩ := exists_sticky_witness_w110 hSFE (lt_of_le_of_lt hbeta hgammaZero.1)
  obtain ⟨G⟩ := exists_source_structure_w110 hbeta hgammaZero S.etaStar_pos
  have hstep := source_step_positive_w110 G
  refine ⟨G.p.c, ⟨hstep.1, hstep.2.1⟩, ?_⟩
  intro gamma hgamma hKT hKF
  exact source_structure_gives_frostman_w110 hdim hbeta hgammaZero S G hgamma hKT hKF

set_option maxHeartbeats 2000000 in
-- Specializing the sticky estimate also checks its dimension-three argument.
/-- The existing dimension-three specialization can retain its header. -/
theorem exists_uniform_step_from_revised_w110
    (hSFE : StickyKakeya.StickyFrostmanHypothesis.{0, uI})
    {beta gammaZero : ℝ} (hbeta : 0 <= beta)
    (hgammaZero : gammaZero ∈ Set.Ioc beta 1) :
    (frostmanStepSet.{uI} (EuclideanSpace ℝ (Fin 3)) beta gammaZero).Nonempty := by
  exact exists_uniform_step_general_from_revised_w110 finrank_euclideanSpace_fin
    (hSFE finrank_euclideanSpace_fin) hbeta hgammaZero

/-- The existing envelope theorem is reused after the new uniform step. -/
theorem frostman_step_function_from_revised_w110
    (hSFE : StickyKakeya.StickyFrostmanHypothesis.{0, uI}) {beta : ℝ}
    (hbeta : 0 <= beta) (_hbeta_one : beta < 1) :
    ∃ nu : ℝ -> ℝ, MonotoneOn nu (Set.Ioc beta 1) ∧
      (∀ gamma ∈ Set.Ioc beta 1, 0 < nu gamma) ∧
      ∀ gamma ∈ Set.Ioc beta 1,
        KatzTaoEstimate.{uI} (EuclideanSpace ℝ (Fin 3)) beta ->
        FrostmanEstimate.{uI} (EuclideanSpace ℝ (Fin 3)) gamma ->
        FrostmanEstimate.{uI} (EuclideanSpace ℝ (Fin 3)) (gamma - nu gamma) := by
  exact exists_monotoneOn_frostmanStep finrank_euclideanSpace_fin
    (fun _ hgammaZero => exists_uniform_step_from_revised_w110 hSFE hbeta hgammaZero)

/-- The exact four-public-boundary Main Lemma 1 statement, with explicit hypotheses.
The other three protected public declarations need no statement change. -/
theorem frostmanEstimate_from_revised_w110
    (hSFE : StickyKakeya.StickyFrostmanHypothesis.{0, uI}) {beta gamma : ℝ}
    (hbeta : 0 <= beta) (hbeta_gamma : beta < gamma) (hgamma : gamma <= 1)
    (hKT : KatzTaoEstimate.{uI} (EuclideanSpace ℝ (Fin 3)) beta) :
    FrostmanEstimate.{uI} (EuclideanSpace ℝ (Fin 3)) gamma := by
  have hbeta_one : beta < 1 := lt_of_lt_of_le hbeta_gamma hgamma
  obtain ⟨nu, hmono, hpos, hstep⟩ :=
    frostman_step_function_from_revised_w110 hSFE hbeta hbeta_one
  let exponents : Set ℝ :=
    {g | FrostmanEstimate.{uI} (EuclideanSpace ℝ (Fin 3)) g}
  have hclosure : Set.Ioc beta 1 ⊆ exponents := by
    apply ioc_subset_of_sub_mem_of_monotoneOn (s := exponents) (f := nu)
    · intro g g' hle hg
      exact FrostmanEstimate.mono (hE := finrank_euclideanSpace_fin) (hββ' := hle) hg
    · exact frostmanEstimate_one
    · intro g hg hgmem
      exact hstep g hg hKT hgmem
    · exact hmono
    · exact hpos
  exact hclosure ⟨hbeta_gamma, hgamma⟩

end

end Kakeya.ml1Boot.RevisedSourceRepairW110

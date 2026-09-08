/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.TrialCarrierAnalyticGeometryW97
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.TrialBalancedFibresW97
public import Kakeya.DimensionThree.MainLemma1.Rescaling.KatzTao
public import Kakeya.DimensionThree.MainLemma1.Rescaling.FineAverageDilate
public import Kakeya.DimensionThree.CardBound

/-!
# Small-width analytic Good (R1, N1, S4)

Analytic side of the trial. `actual_raw_eccentricity_good_transfer_w97` (R1) transfers the
parent-presentation estimate on the factored `H` to the original `F` at exponent
`trialSourceKappaW97`. `trial_source_analytic_numeric_budget_w97`,
`trial_analytic_extra_costs_eventually_w97` and `exists_trial_analytic_payment_schedule_w97`
(N1a-c) derive the numeric gaps and pay band/product costs for small `d`.
`exists_actual_small_width_analytic_application_w97` (S4a) applies the tube product, the
Katz-Tao estimate and the fine Frostman estimate, and
`actual_small_width_good_from_factored_family_w97` (S4) is the caller-facing conclusion
`detailedInnerGoodW94 F Y gamma epsilon xi` from the G0-G2 factored data.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

universe uE uI

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

def trialSourceKappaW97 (gamma epsilon xi : ℝ) : ℝ :=
  (40 * xi / epsilon + 6 * xi) / (3 * gamma)

def trialCoarseDensityConstantW97 : ℝ≥0 :=
  max 1 (max trialOuterCarrierConstantW97 16)

/-- R1 invokes the raw parent-presentation donor on the actual factored H,
then transfers its estimate to ORIGINAL F at the literal source exponent. -/
theorem actual_raw_eccentricity_good_transfer_w97
    (hdim : Module.finrank ℝ E = 3)
    (beta gamma epsilon xi : ℝ)
    (hbeta : 0 < beta) (hbetagamma : beta < gamma) (hgamma : gamma <= 1)
    (hepsilon : 0 < epsilon) (hxi : 0 < xi)
    (hKT : KatzTaoEstimate.{uI} E beta) (hKF : FrostmanEstimate.{uI} E gamma) :
    ∃ etaMax : ℝ, 0 < etaMax ∧ etaMax <= xi / 100 ∧
      ∀ etaLambda : ℝ, 0 < etaLambda -> etaLambda <= etaMax ->
      ∀ᶠ (d : ℝ≥0) in 𝓝[>] 0,
      ∀ {iota pi : Type uI} [DecidableEq iota] [DecidableEq pi]
        (F H : Finset iota) (Y : iota -> ShadedTube d E)
        (a b rho : ℝ≥0) (J : Finset pi) (Tparent : pi -> Tube rho E)
        (parent : iota -> pi) (P : ℝ≥0∞),
        F.Nonempty -> H.Nonempty -> H ⊆ F ->
        d <= a -> a <= b -> b <= rho -> rho <= 1 ->
        (∀ i ∈ F, (Y i).carrier ⊆ Metric.closedBall 0 1) ->
        (H : Set iota).Pairwise (fun i j => IsEssentiallyDistinct (Y i).carrier (Y j).carrier) ->
        FlatPrismParentPresentation (D := 1) H Y J Tparent parent ->
        (∀ S ∈ J, ∃ Fz : ConvexSpaceBody.Factorization (completeFibreW94 H parent S)
          (fun i => (Y i).toConvexSpaceBody) 2,
          IsPlankFamilyOfDimensions plankPigeonhole.C a b Fz.parts
            (fun q => q.convexHull_biUnion (fun i => (Y i).toConvexSpaceBody))) ->
        1 <= P -> P < ⊤ -> P <= (d : ℝ≥0∞) ^ (-etaMax) ->
        P ^ (1 + (1 - gamma / 2)) <= (d : ℝ≥0∞) ^ (-xi / 10) ->
        (∑ i ∈ F, volume (Y i).shade) <= P * ∑ i ∈ H, volume (Y i).shade ->
        (d : ℝ≥0∞) ^ etaLambda <= fullness' F (fun i => (Y i).toShadedBody) ->
        frostmanConstIn F (fun i => (Y i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall <=
          (d : ℝ≥0∞) ^ (-xi / 160) ->
        let lambda := fullness' F (fun i => (Y i).toShadedBody)
        lambda / P <= fullness' H (fun i => (Y i).toShadedBody) ∧
          lambda / P * (F.card : ℝ≥0∞) <= (H.card : ℝ≥0∞) ∧
          frostmanConstIn H (fun i => (Y i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall <=
            (P / lambda) * frostmanConstIn F (fun i => (Y i).toConvexSpaceBody)
              ConvexSpaceBody.closedUnitBall ∧
          ShadedBody.multiplicity F (fun i => (Y i).toShadedBody) <=
            P * ShadedBody.multiplicity H (fun i => (Y i).toShadedBody) ∧
          ShadedBody.multiplicity H (fun i => (Y i).toShadedBody) <=
            (d : ℝ≥0∞) ^ (-xi) *
              (frostmanConstIn H (fun i => (Y i).toConvexSpaceBody)
                ConvexSpaceBody.closedUnitBall) ^ (1 - gamma / 2) *
              ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (3 * gamma / 2) *
              (d : ℝ≥0∞) ^ (-2 * gamma) *
              ((H.card : ℝ≥0∞) * (d : ℝ≥0∞) ^ (2 : Nat)) ^ (1 - gamma / 2) ∧
          (((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (3 * gamma / 2) <=
            (d : ℝ≥0∞) ^ (20 * xi / epsilon + 3 * xi) ->
              detailedInnerGoodW94 F Y gamma epsilon xi) ∧
          (¬ detailedInnerGoodW94 F Y gamma epsilon xi ->
            (b : ℝ≥0∞) / (a : ℝ≥0∞) <
              (d : ℝ≥0∞) ^ (-trialSourceKappaW97 gamma epsilon xi)) := by
  classical
  have hgamma0 : 0 < gamma := hbeta.trans hbetagamma
  have hp0 : 0 <= 1 - gamma / 2 := by linarith
  have hp1 : 1 - gamma / 2 <= 1 := by linarith
  have hCw : 1 <= plankPigeonhole.C := by
    norm_num [plankPigeonhole.C, Metric.volume_comparison.C, Metric.lt_volume_convexHull.c]
  obtain ⟨etaRaw, hetaRaw, hraw⟩ :=
    multiplicity_le_of_factorsThroughFlatPrisms_of_parentPresentation hdim hgamma0.le hgamma
      (KatzTaoEstimate.mono hbetagamma.le hKT) hKF plankPigeonhole.C hCw 1 xi hxi
  let etaMax := min (etaRaw / 4) (xi / 100)
  have hmax : 0 < etaMax := by dsimp [etaMax]; positivity
  have hmaxRaw : etaMax <= etaRaw / 4 := min_le_left _ _
  have hmaxXi : etaMax <= xi / 100 := min_le_right _ _
  let Cunif : ℝ≥0 := max 1 (Tube.overlapConstBOTight 3 : ℝ≥0)
  have hCunif : 1 <= Cunif := le_max_left _ _
  refine ⟨etaMax, hmax, hmaxXi, ?_⟩
  intro etaLambda hetaLambda hetaMax
  have hetaRawLoss : etaLambda + etaMax <= etaRaw := by linarith
  filter_upwards [hraw,
      eventually_finite_const_le_rpow_neg (c := (Cunif : ℝ≥0∞)) ENNReal.coe_ne_top hetaRaw,
      (nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ≥0) < 1 / 4)) :
        ∀ᶠ d : ℝ≥0 in 𝓝[>] 0, d < 1 / 4), self_mem_nhdsWithin]
    with d hrawD hCunifD hdquarter hd
  intro iota pi _ _ F H Y a b rho J Tparent parent P hF hH hHF hda hab hbrho hrho
    hball hED hparent hFz hP hPfin hPd hPpower hmass hfull hCF
  let lambda := fullness' F (fun i => (Y i).toShadedBody)
  have hd1 : d <= 1 := hdquarter.le.trans
    ((div_le_one (by norm_num : (0 : ℝ≥0) < 4)).mpr (by norm_num))
  have hdE0 : (d : ℝ≥0∞) ≠ 0 := by exact_mod_cast hd.ne'
  have hdEt : (d : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hdE1 : (d : ℝ≥0∞) <= 1 := by exact_mod_cast hd1
  have hdPow0 (x : ℝ) : (d : ℝ≥0∞) ^ x ≠ 0 :=
    (ENNReal.rpow_pos (by exact_mod_cast hd) hdEt).ne'
  have hdPowt (x : ℝ) : (d : ℝ≥0∞) ^ x ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hdE0 hdEt
  have hlambda : 0 < lambda := (ENNReal.rpow_pos (by exact_mod_cast hd) hdEt).trans_le hfull
  have hlambdat : lambda ≠ ⊤ := fullness'_ne_top F _
  have hP0 : P ≠ 0 := (zero_lt_one.trans_le hP).ne'
  have ha0 : a ≠ 0 := (hd.trans_le hda).ne'
  have hb0 : b ≠ 0 := ((hd.trans_le hda).trans_le hab).ne'
  let v := volume (Y hF.choose).carrier
  have hv : 0 < v := (Tube.volume_pos_and_lt_top hd hd1 (Y hF.choose).toTube).1
  have hvfinite : v < ⊤ := (Y hF.choose).toConvexSpaceBody.isCompact.measure_lt_top
  have hvol : ∀ i, volume (Y i).carrier = v := fun i =>
    Tube.volume_carrier_eq_volume_carrier (Y i).toTube (Y hF.choose).toTube
  have hcar (t : Finset iota) : (∑ i ∈ t, volume (Y i).carrier) = (t.card : ℝ≥0∞) * v := by
    simp only [hvol, Finset.sum_const, nsmul_eq_mul]
  have hFcard0 : (F.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast hF.card_pos.ne'
  have hcarF : 0 < ∑ i ∈ F, volume (Y i).carrier := by
    rw [hcar]
    exact ENNReal.mul_pos hFcard0 hv.ne'
  have href : ShadedBody.IsRefinement H (fun i => (Y i).toShadedBody)
      F (fun i => (Y i).toShadedBody) := ⟨hHF, fun _ _ => ⟨rfl, Set.Subset.rfl⟩⟩
  have hrefC := ShadedBody.isCRefinement_of_isRefinement_of_sum_le
    H (fun i => (Y i).toShadedBody) F (fun i => (Y i).toShadedBody)
    (C := P.toNNReal) href (by simpa only [ENNReal.coe_toNNReal hPfin.ne] using hmass)
  have hretain : lambda / P <= fullness' H (fun i => (Y i).toShadedBody) := by
    have h := ShadedBody.IsCRefinement.mul_fullness_le _ _ _ _ hcarF hrefC
    have hPnn : P.toNNReal ≠ 0 := (ENNReal.toNNReal_pos hP0 hPfin.ne).ne'
    have h' := ENNReal.coe_le_coe.mpr h
    simpa only [ENNReal.coe_mul, ENNReal.coe_inv hPnn, ENNReal.coe_toNNReal hPfin.ne,
      ShadedBody.coe_fullness, lambda, div_eq_mul_inv, mul_comm] using h'
  have hcard : lambda / P * (F.card : ℝ≥0∞) <= (H.card : ℝ≥0∞) := by
    have hmassF : (∑ i ∈ F, volume (Y i).shade) = lambda * ((F.card : ℝ≥0∞) * v) := by
      have h := ShadedBody.sum_volumeReal_shade_eq_fullness_mul F (fun i => (Y i).toShadedBody)
      simpa only [ShadedBody.coe_fullness, hcar] using h
    have hmassH : (∑ i ∈ H, volume (Y i).shade) <= (H.card : ℝ≥0∞) * v := by
      rw [← hcar]
      exact Finset.sum_le_sum fun i _ => measure_mono (Y i).shade_subset
    have hh := hmass.trans (mul_le_mul_right hmassH P)
    rw [hmassF] at hh
    have hcount : lambda * (F.card : ℝ≥0∞) <= P * (H.card : ℝ≥0∞) := by
      apply (ENNReal.mul_le_mul_iff_right hv.ne' hvfinite.ne).mp
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hh
    have hc := (ENNReal.inv_mul_le_iff hP0 hPfin.ne).mpr hcount
    simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hc
  have hCFH : frostmanConstIn H (fun i => (Y i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall <=
      (P / lambda) * frostmanConstIn F (fun i => (Y i).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall := by
    have hk : lambda / P ≠ 0 := (ENNReal.div_pos hlambda.ne' hPfin.ne).ne'
    have hf := frostmanConstIn_subfamily_le (K := ConvexSpaceBody.closedUnitBall)
      hF (fun i _ => hvol i) (fun i hi => hball i hi) hHF hk hcard
    rw [ENNReal.inv_div (Or.inl hPfin.ne) (Or.inl hP0)] at hf
    exact hf
  have hmu : ShadedBody.multiplicity F (fun i => (Y i).toShadedBody) <=
      P * ShadedBody.multiplicity H (fun i => (Y i).toShadedBody) :=
    ShadedBody.multiplicity_le_mul_of_sum_shade_le_of_biUnion_subset _ _ _ _ P
      (Set.iUnion₂_mono' fun i hi => ⟨i, hHF hi, Set.Subset.rfl⟩) hmass
  have hfullRaw : (d : ℝ≥0∞) ^ etaRaw <= fullness' H (fun i => (Y i).toShadedBody) := by
    calc
      _ <= (d : ℝ≥0∞) ^ (etaLambda + etaMax) :=
        ENNReal.rpow_le_rpow_of_exponent_ge hdE1 hetaRawLoss
      _ = (d : ℝ≥0∞) ^ etaLambda / (d : ℝ≥0∞) ^ (-etaMax) := by
        rw [← ENNReal.rpow_sub _ _ hdE0 hdEt]; congr 1; ring
      _ <= lambda / P := ENNReal.div_le_div hfull hPd
      _ <= _ := hretain
  have hflat : IsFlatPrismFamily etaRaw Cunif H Y := {
    nonempty := hH
    unif := nonempty_isFlatPrismUniform_ssf hd hdquarter.le H Y
      (fun i hi => hball i (hHF hi)) hED hCunif (by rw [hdim]; exact le_max_right _ _)
    ball := fun i hi => hball i (hHF hi)
    essDistinct := hED
    fullness := by simpa only [ShadedBody.coe_fullness] using hfullRaw }
  have hrawH := hrawD Cunif hCunif hCunifD a b rho hda hab (hbrho.trans hrho)
    (hda.trans (hab.trans hbrho)) (by simpa only [one_mul] using hbrho) hrho
    Y Tparent parent hflat hparent hFz
  have hcostCF : P *
      (frostmanConstIn H (fun i => (Y i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall) ^
        (1 - gamma / 2) <= (d : ℝ≥0∞) ^ (-xi / 5) := by
    have hCFscale : frostmanConstIn H (fun i => (Y i).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall <= P * (d : ℝ≥0∞) ^ (-etaLambda - xi / 160) := by
      calc
        _ <= (P / lambda) * (d : ℝ≥0∞) ^ (-xi / 160) :=
          hCFH.trans (mul_le_mul' le_rfl hCF)
        _ <= (P / (d : ℝ≥0∞) ^ etaLambda) * (d : ℝ≥0∞) ^ (-xi / 160) :=
          mul_le_mul' (ENNReal.div_le_div le_rfl hfull) le_rfl
        _ = _ := by
          rw [div_eq_mul_inv, ← ENNReal.rpow_neg, mul_assoc,
            ← ENNReal.rpow_add _ _ hdE0 hdEt]
          congr 2
          ring
    calc
      _ <= P * (P * (d : ℝ≥0∞) ^ (-etaLambda - xi / 160)) ^ (1 - gamma / 2) :=
        mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hCFscale hp0)
      _ = P ^ (1 + (1 - gamma / 2)) *
          (d : ℝ≥0∞) ^ ((-etaLambda - xi / 160) * (1 - gamma / 2)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0, ← ENNReal.rpow_mul,
          ← mul_assoc, ENNReal.rpow_add _ _ hP0 hPfin.ne, ENNReal.rpow_one]
      _ <= (d : ℝ≥0∞) ^ (-xi / 10) *
          (d : ℝ≥0∞) ^ ((-etaLambda - xi / 160) * (1 - gamma / 2)) :=
        mul_le_mul' hPpower le_rfl
      _ = (d : ℝ≥0∞) ^ (-xi / 10 + (-etaLambda - xi / 160) * (1 - gamma / 2)) :=
        (ENNReal.rpow_add _ _ hdE0 hdEt).symm
      _ <= (d : ℝ≥0∞) ^ (-xi / 5) :=
        ENNReal.rpow_le_rpow_of_exponent_ge hdE1 (by
          have hetaXi := hetaMax.trans hmaxXi
          nlinarith)
  have hGood : ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (3 * gamma / 2) <=
      (d : ℝ≥0∞) ^ (20 * xi / epsilon + 3 * xi) -> detailedInnerGoodW94 F Y gamma epsilon xi := by
    intro hecc
    dsimp only [detailedInnerGoodW94]
    calc
      _ <= P * ShadedBody.multiplicity H (fun i => (Y i).toShadedBody) := hmu
      _ <= P * ((d : ℝ≥0∞) ^ (-xi) *
          (frostmanConstIn H (fun i => (Y i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall) ^
            (1 - gamma / 2) * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (3 * gamma / 2) *
          (d : ℝ≥0∞) ^ (-2 * gamma) *
          ((H.card : ℝ≥0∞) * (d : ℝ≥0∞) ^ (2 : Nat)) ^ (1 - gamma / 2)) :=
        mul_le_mul' le_rfl hrawH
      _ = (d : ℝ≥0∞) ^ (-xi) *
          (P * (frostmanConstIn H (fun i => (Y i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall) ^
            (1 - gamma / 2)) * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (3 * gamma / 2) *
          (d : ℝ≥0∞) ^ (-2 * gamma) *
          ((H.card : ℝ≥0∞) * (d : ℝ≥0∞) ^ (2 : Nat)) ^ (1 - gamma / 2) := by ring
      _ <= (d : ℝ≥0∞) ^ (-xi) * (d : ℝ≥0∞) ^ (-xi / 5) *
          (d : ℝ≥0∞) ^ (20 * xi / epsilon + 3 * xi) * (d : ℝ≥0∞) ^ (-2 * gamma) *
          ((F.card : ℝ≥0∞) * (d : ℝ≥0∞) ^ (2 : Nat)) ^ (1 - gamma / 2) := by
        gcongr
      _ = (d : ℝ≥0∞) ^ (20 * xi / epsilon + 9 * xi / 5) *
          (d : ℝ≥0∞) ^ (-2 * gamma) *
          ((F.card : ℝ≥0∞) * (d : ℝ≥0∞) ^ (2 : Nat)) ^ (1 - gamma / 2) := by
        rw [← ENNReal.rpow_add _ _ hdE0 hdEt, ← ENNReal.rpow_add _ _ hdE0 hdEt]
        congr 3
        ring
      _ <= _ := by
        rw [mul_comm ((d : ℝ≥0∞) ^ (2 : Nat)) (F.card : ℝ≥0∞)]
        exact mul_le_mul' (mul_le_mul'
          (ENNReal.rpow_le_rpow_of_exponent_ge hdE1 (by linarith)) le_rfl) le_rfl
  refine ⟨hretain, hcard, hCFH, hmu, hrawH, hGood, ?_⟩
  intro hnotGood
  have hecc : (d : ℝ≥0∞) ^ (20 * xi / epsilon + 3 * xi) <
      ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (3 * gamma / 2) :=
    lt_of_not_ge fun h => hnotGood (hGood h)
  have hinv := ENNReal.inv_lt_inv' hecc
  apply (ENNReal.rpow_lt_rpow_iff (by positivity : 0 < 3 * gamma / 2)).mp
  calc
    ((b : ℝ≥0∞) / (a : ℝ≥0∞)) ^ (3 * gamma / 2) =
        (((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ (3 * gamma / 2))⁻¹ := by
      rw [← ENNReal.inv_rpow, ENNReal.inv_div (Or.inl ENNReal.coe_ne_top)
        (Or.inl (by exact_mod_cast hb0))]
    _ < ((d : ℝ≥0∞) ^ (20 * xi / epsilon + 3 * xi))⁻¹ := hinv
    _ = ((d : ℝ≥0∞) ^ (-trialSourceKappaW97 gamma epsilon xi)) ^ (3 * gamma / 2) := by
      rw [← ENNReal.rpow_neg, ← ENNReal.rpow_mul]
      congr 1
      dsimp [trialSourceKappaW97]
      field_simp
      ring

/-- N1a: the numerical gaps follow from the frozen P1 hypotheses. -/
theorem trial_source_analytic_numeric_budget_w97
    (beta gamma epsilon xi : ℝ)
    (hbeta : 0 < beta) (hbetagamma : beta < gamma) (hgamma : gamma <= 1)
    (hepsilon : 0 < epsilon) (hepsilon_lt : epsilon < 1 / 3)
    (hgap : 3 * epsilon / 2 <= (gamma - beta) / 1000)
    (hxi : 0 < xi) (hxiupper : xi <= 4 * epsilon ^ (3 : Nat) * beta / 25000)
    (L : Nat) (_hL : 1 <= L) (hLmin : (1 : ℝ) / L <= min xi epsilon / 100) :
    epsilon <= 1 / 1500 ∧ 5 * epsilon < 1 ∧
      750 * epsilon <= gamma - betaPrime beta gamma ∧
      74 * epsilon <= gamma - betaPrime beta gamma ∧
      10 * epsilon <= (gamma - betaPrime beta gamma) / 2 ∧
      (12 : ℝ) / L <= 12 * epsilon / 100 ∧
      0 < trialSourceKappaW97 gamma epsilon xi ∧
      trialSourceKappaW97 gamma epsilon xi <= epsilon / 100 ∧
      20 * xi / epsilon <= epsilon / 100 ∧
      12 * epsilon + (12 : ℝ) / L + trialSourceKappaW97 gamma epsilon xi <=
        (1213 : ℝ) * epsilon / 100 ∧
      20 * xi / epsilon < 17 * epsilon / 2 := by
  have hgamma0 : 0 < gamma := hbeta.trans hbetagamma
  have heps : epsilon <= 1 / 1500 := by linarith
  have heps1 : epsilon <= 1 := by linarith
  have hbetaPrime : 750 * epsilon <= gamma - betaPrime beta gamma := by
    have hmax : max beta (gamma / 2) <= gamma - 750 * epsilon :=
      max_le (by linarith) (by linarith)
    dsimp [betaPrime]
    linarith
  have hLbound : (12 : ℝ) / L <= 12 * epsilon / 100 := by
    have h := hLmin.trans (div_le_div_of_nonneg_right (min_le_right xi epsilon) (by norm_num))
    calc
      (12 : ℝ) / L = 12 * ((1 : ℝ) / L) := by ring
      _ <= 12 * (epsilon / 100) := mul_le_mul_of_nonneg_left h (by norm_num)
      _ = _ := by ring
  have hquad : xi <= epsilon ^ (2 : Nat) * gamma / 10000 := by
    calc
      xi <= 4 * epsilon ^ (3 : Nat) * beta / 25000 := hxiupper
      _ <= 4 * epsilon ^ (3 : Nat) * gamma / 25000 := by gcongr
      _ <= epsilon ^ (2 : Nat) * gamma / 10000 := by
        have h := mul_nonneg (mul_nonneg (sq_nonneg epsilon) hgamma0.le)
          (sub_nonneg.mpr heps)
        nlinarith
  have hquot : xi / epsilon <= epsilon * gamma / 10000 := by
    apply (div_le_iff₀ hepsilon).mpr
    nlinarith [hquad]
  have hlinear : xi <= epsilon * gamma / 10000 := by
    apply hquad.trans
    gcongr
    nlinarith
  have hkappa0 : 0 < trialSourceKappaW97 gamma epsilon xi := by
    dsimp [trialSourceKappaW97]
    positivity
  have hkappa : trialSourceKappaW97 gamma epsilon xi <= epsilon / 100 := by
    dsimp [trialSourceKappaW97]
    apply (div_le_iff₀ (by positivity : 0 < 3 * gamma)).mpr
    have hprod : 0 <= epsilon * gamma := by positivity
    rw [mul_div_assoc]
    nlinarith [hquot, hlinear]
  have hxiBudget : 20 * xi / epsilon <= epsilon / 100 := by
    have hg : epsilon * gamma <= epsilon := by nlinarith
    rw [mul_div_assoc]
    nlinarith [hquot]
  exact ⟨heps, by linarith, hbetaPrime, by linarith, by linarith, hLbound,
    hkappa0, hkappa, hxiBudget, by linarith, by linarith⟩

/-- N1b: the analytic-only band and tube-product costs are paid from actual
fine ED cardinality. This is not a polylog assertion about the product donor. -/
theorem trial_analytic_extra_costs_eventually_w97
    (nu Ccard : ℝ) (hnu : 0 < nu) (hCcard : 1 <= Ccard) :
    ∀ᶠ (d : ℝ≥0) in 𝓝[>] 0, ∀ n nb : Nat, 1 <= nb -> nb <= n ->
      (n : ℝ) <= Ccard * (d : ℝ) ^ (-4 : ℝ) ->
      (dyadicPigeonholeNatConstant n : ℝ≥0∞) <= (d : ℝ≥0∞) ^ (-nu) ∧
        (trialTubeProductCostW97 d nb : ℝ≥0∞) <= (d : ℝ≥0∞) ^ (-nu) := by
  let alpha : ℝ := nu / 10
  have halpha : 0 < alpha := by dsimp [alpha]; positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let Blog : ℝ≥0 := 1 + ⟨1 / (alpha * Real.log 2), by positivity⟩
  have hlog : ∀ n : Nat, 0 < n ->
      (dyadicPigeonholeNatConstant n : ℝ≥0) <= Blog * (n : ℝ≥0) ^ alpha := by
    intro n hn
    have hn1 : (1 : ℝ≥0) <= (n : ℝ≥0) := by exact_mod_cast hn
    have hpow : (1 : ℝ) <= (n : ℝ) ^ alpha := by
      exact_mod_cast NNReal.one_le_rpow hn1 halpha.le
    have hlogn : (Nat.log 2 n : ℝ) <= (n : ℝ) ^ alpha / (alpha * Real.log 2) := by
      calc
        _ <= Real.logb 2 n := Real.natLog_le_logb n 2
        _ = Real.log n / Real.log 2 := rfl
        _ <= ((n : ℝ) ^ alpha / alpha) / Real.log 2 := by
          gcongr
          exact Real.log_natCast_le_rpow_div n halpha
        _ = _ := by ring
    rw [← NNReal.coe_le_coe]
    dsimp only [Blog, dyadicPigeonholeNatConstant]
    push_cast
    change (Nat.log 2 n : ℝ) + 1 <=
      (1 + 1 / (alpha * Real.log 2)) * (n : ℝ) ^ alpha
    calc
      _ <= (n : ℝ) ^ alpha / (alpha * Real.log 2) + (n : ℝ) ^ alpha :=
        add_le_add hlogn hpow
      _ = _ := by ring
  obtain ⟨Ceps, hCeps⟩ := shadingMultiplicityEstimateForRhoTubesDilate.C_leApprox 3 alpha halpha
  let CcardNN := Real.toNNReal Ccard
  have hCcardNN : (CcardNN : ℝ) = Ccard := Real.coe_toNNReal _ (by linarith)
  let K : ℝ≥0 := max Blog Ceps * CcardNN ^ alpha
  filter_upwards [eventually_mul_rpow_le_rpow (K := (K : ℝ≥0∞)) ENNReal.coe_ne_top
      (p := -nu / 2) (q := -nu) (by linarith),
      eventually_le_one_nhdsGT, self_mem_nhdsWithin] with d hpay hd1 hd
  intro n nb hnb hnbn hncard
  have hn : 0 < n := lt_of_lt_of_le (by omega : 0 < nb) hnbn
  have hd0 : d ≠ 0 := hd.ne'
  have hncardNN : (n : ℝ≥0) <= CcardNN * d ^ (-4 : ℝ) := by
    rw [← NNReal.coe_le_coe]
    simpa only [NNReal.coe_mul, NNReal.coe_rpow, hCcardNN, NNReal.coe_natCast] using hncard
  have hcardpow : (n : ℝ≥0) ^ alpha <= CcardNN ^ alpha * d ^ (-4 * alpha) := by
    calc
      _ <= (CcardNN * d ^ (-4 : ℝ)) ^ alpha := NNReal.rpow_le_rpow hncardNN halpha.le
      _ = _ := by rw [NNReal.mul_rpow, ← NNReal.rpow_mul]
  have hnbpow : (nb : ℝ≥0) ^ alpha <= CcardNN ^ alpha * d ^ (-4 * alpha) :=
    (NNReal.rpow_le_rpow (by exact_mod_cast hnbn) halpha.le).trans hcardpow
  have hlogbound : (dyadicPigeonholeNatConstant n : ℝ≥0) <= K * d ^ (-nu / 2) := by
    calc
      _ <= Blog * (n : ℝ≥0) ^ alpha := hlog n hn
      _ <= max Blog Ceps * (CcardNN ^ alpha * d ^ (-4 * alpha)) :=
        mul_le_mul' (le_max_left _ _) hcardpow
      _ = K * d ^ (-4 * alpha) := by dsimp [K]; ring
      _ <= K * d ^ (-nu / 2) := mul_le_mul_right
        (NNReal.rpow_le_rpow_of_exponent_ge hd hd1
          (by change -nu / 2 <= -4 * (nu / 10); linarith)) K
  have hCbound : trialTubeProductCostW97 d nb <= K * d ^ (-nu / 2) := by
    calc
      _ <= Ceps * 1 ^ (3 : Nat) * d ^ (-alpha) * (nb : ℝ≥0) ^ alpha :=
        hCeps nb (by omega) d hd hd1 1 le_rfl
      _ <= max Blog Ceps * d ^ (-alpha) * (CcardNN ^ alpha * d ^ (-4 * alpha)) := by
        simp only [one_pow, mul_one]
        exact mul_le_mul' (mul_le_mul' (le_max_right _ _) le_rfl) hnbpow
      _ = K * d ^ (-nu / 2) := by
        calc
          _ = K * (d ^ (-alpha) * d ^ (-4 * alpha)) := by dsimp [K]; ring
          _ = K * d ^ (-alpha + -4 * alpha) := by rw [← NNReal.rpow_add hd0]
          _ = _ := by congr 2; dsimp [alpha]; ring
  exact ⟨(show (dyadicPigeonholeNatConstant n : ℝ≥0∞) <=
    (K : ℝ≥0∞) * (d : ℝ≥0∞) ^ (-nu / 2) by exact_mod_cast hlogbound).trans hpay,
    (show (trialTubeProductCostW97 d nb : ℝ≥0∞) <=
      (K : ℝ≥0∞) * (d : ℝ≥0∞) ^ (-nu / 2) by exact_mod_cast hCbound).trans hpay⟩

/-- N1c: choose g and the paid exponents after the opaque analytic eta's,
then obtain one uniform cutoff for the concrete coarse/fine payments. -/
theorem exists_trial_analytic_payment_schedule_w97
    (epsilon xi etaP etaRaw etaCoarse etaFine : ℝ)
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 1500)
    (hxi : 0 < xi) (hxiSmall : 20 * xi / epsilon <= epsilon / 100)
    (hetaP : 0 < etaP) (hetaPSmall : etaP <= epsilon / 100)
    (hetaRaw : 0 < etaRaw) (hetaCoarse : 0 < etaCoarse) (hetaFine : 0 < etaFine)
    (kappa : ℝ) (hkappa : kappa <= epsilon / 100)
    (Cinner : ℝ≥0) :
    ∃ (g nu etaMax : ℝ),
      0 < g ∧ g <= epsilon / 100 ∧ g <= etaFine / 4 ∧
      g <= (1 - 5 * epsilon) * etaCoarse / 4 ∧
      0 < nu ∧ nu <= g / 10 ∧ nu <= xi / 100 ∧ nu <= etaP / 100 ∧
      0 < etaMax ∧ etaMax <= etaP / 4 ∧ etaMax <= etaRaw / 4 ∧
      etaMax <= xi / 100 ∧ etaMax <= g / 10 ∧
      ∀ etaLambda : ℝ, 0 < etaLambda -> etaLambda <= etaMax ->
      ∀ᶠ (d : ℝ≥0) in 𝓝[>] 0, ∀ P Lc C : ℝ≥0∞,
        1 <= P -> P < ⊤ -> 1 <= Lc -> Lc < ⊤ -> 1 <= C -> C < ⊤ ->
        P <= (d : ℝ≥0∞) ^ (-nu) -> Lc <= (d : ℝ≥0∞) ^ (-nu) ->
        C <= (d : ℝ≥0∞) ^ (-nu) ->
        (d : ℝ≥0∞) ^ g <= (d : ℝ≥0∞) ^ etaLambda / (P * Lc * C) ∧
        (d : ℝ≥0∞) ^ ((1 - 5 * epsilon) * etaCoarse) <=
          (d : ℝ≥0∞) ^ etaLambda / (P * Lc * C) ∧
        (16 * P * Lc * C / (d : ℝ≥0∞) ^ etaLambda) * (d : ℝ≥0∞) ^ (-xi / 160) <=
          (trialCoarseDensityConstantW97 : ℝ≥0∞) * (d : ℝ≥0∞) ^ (-epsilon) ∧
        (Cinner : ℝ≥0∞) * (d : ℝ≥0∞) ^ (-kappa) <=
          (d : ℝ≥0∞) ^ (-epsilon / 10) ∧
        16 * (fineNormalizeDilate.C 1 : ℝ≥0∞) * (d : ℝ≥0∞) ^ etaFine <=
          (d : ℝ≥0∞) ^ (2 * g) / 16 ∧
        ((d : ℝ≥0∞) ^ (2 * g) / 16)⁻¹ * (d : ℝ≥0∞) ^ (-epsilon / 10) <=
          2 * (d : ℝ≥0∞) ^ (-epsilon / 5) ∧
        16 / (d : ℝ≥0∞) ^ g * ((fineAverageDilate.C 1 1 : ℝ≥0∞) *
          (d : ℝ≥0∞) ^ (-3 * epsilon / 10)) <= (d : ℝ≥0∞) ^ (-epsilon / 2) ∧
        2 * P * Lc * C <= (d : ℝ≥0∞) ^ (-epsilon) ∧
        (trialComparableCarrierScaleW96 plankPigeonhole.C : ℝ≥0∞) <=
          (d : ℝ≥0∞) ^ (-7 * epsilon / 2) := by
  have heps1 : 5 * epsilon < 1 := by linarith
  let g := min (epsilon / 100) (min (etaFine / 4) ((1 - 5 * epsilon) * etaCoarse / 4))
  have hg : 0 < g := by dsimp [g]; positivity
  have hgeps : g <= epsilon / 100 := min_le_left _ _
  have hgfine : g <= etaFine / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hgcoarse : g <= (1 - 5 * epsilon) * etaCoarse / 4 :=
    (min_le_right _ _).trans (min_le_right _ _)
  let nu := min (g / 10) (min (xi / 100) (etaP / 100))
  have hnu : 0 < nu := by dsimp [nu]; positivity
  have hnug : nu <= g / 10 := min_le_left _ _
  have hnuxi : nu <= xi / 100 := (min_le_right _ _).trans (min_le_left _ _)
  have hnueta : nu <= etaP / 100 := (min_le_right _ _).trans (min_le_right _ _)
  let etaMax := min (etaP / 4) (min (etaRaw / 4) (min (xi / 100) (g / 10)))
  have hmax : 0 < etaMax := by dsimp [etaMax]; positivity
  have hmaxP : etaMax <= etaP / 4 := min_le_left _ _
  have hmaxRaw : etaMax <= etaRaw / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hmaxXi : etaMax <= xi / 100 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hmaxG : etaMax <= g / 10 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨g, nu, etaMax, hg, hgeps, hgfine, hgcoarse, hnu, hnug, hnuxi, hnueta,
    hmax, hmaxP, hmaxRaw, hmaxXi, hmaxG, ?_⟩
  intro etaLambda hetaLambda hetaMax
  have hetag : etaLambda <= g / 10 := hetaMax.trans hmaxG
  have hxiEps : xi <= epsilon / 2000 := by
    have h := (div_le_iff₀ hepsilon).mp hxiSmall
    have hsq : epsilon * epsilon <= epsilon := by nlinarith
    nlinarith
  have hCDelta : (16 : ℝ≥0∞) <= (trialCoarseDensityConstantW97 : ℝ≥0∞) := by
    exact_mod_cast (le_max_right trialOuterCarrierConstantW97 16).trans
      (le_max_right 1 (max trialOuterCarrierConstantW97 16))
  filter_upwards [eventually_mul_rpow_le_rpow (K := (Cinner : ℝ≥0∞)) ENNReal.coe_ne_top
      (p := -kappa) (q := -epsilon / 10) (by linarith),
      eventually_mul_rpow_le_rpow (K := 256 * (fineNormalizeDilate.C 1 : ℝ≥0∞))
        (by finiteness) (p := etaFine) (q := 2 * g) (by linarith),
      eventually_mul_rpow_le_rpow (K := (16 : ℝ≥0∞)) (by norm_num)
        (p := -2 * g - epsilon / 10) (q := -epsilon / 5) (by linarith),
      eventually_mul_rpow_le_rpow (K := 16 * (fineAverageDilate.C 1 1 : ℝ≥0∞))
        (by finiteness) (p := -g - 3 * epsilon / 10) (q := -epsilon / 2) (by linarith),
      eventually_mul_rpow_le_rpow (K := (2 : ℝ≥0∞)) (by norm_num)
        (p := -3 * nu) (q := -epsilon) (by linarith),
      eventually_finite_const_le_rpow_neg
        (c := (trialComparableCarrierScaleW96 plankPigeonhole.C : ℝ≥0∞))
        ENNReal.coe_ne_top (a := 7 * epsilon / 2) (by positivity),
      eventually_le_one_nhdsGT, self_mem_nhdsWithin]
    with d hinner hnorm hfrob hfine hcost hkB hd1 hd
  intro P Lc C hP hPfin hLc hLcfin hC hCfin hPd hLcd hCd
  have hd0 : (d : ℝ≥0∞) ≠ 0 := by exact_mod_cast hd.ne'
  have hdtop : (d : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hdE1 : (d : ℝ≥0∞) <= 1 := by exact_mod_cast hd1
  have hp0 : ∀ x : ℝ, (d : ℝ≥0∞) ^ x ≠ 0 := fun x =>
    (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hd0) hdtop).ne'
  have hpt : ∀ x : ℝ, (d : ℝ≥0∞) ^ x ≠ ⊤ :=
    fun x => ENNReal.rpow_ne_top_of_ne_zero hd0 hdtop
  have hmul : ∀ x y : ℝ, (d : ℝ≥0∞) ^ x * (d : ℝ≥0∞) ^ y =
      (d : ℝ≥0∞) ^ (x + y) := fun x y => (ENNReal.rpow_add x y hd0 hdtop).symm
  have hdiv : ∀ x y : ℝ, (d : ℝ≥0∞) ^ x / (d : ℝ≥0∞) ^ y =
      (d : ℝ≥0∞) ^ (x - y) := fun x y => (ENNReal.rpow_sub x y hd0 hdtop).symm
  have hpayment : P * Lc * C <= (d : ℝ≥0∞) ^ (-3 * nu) := by
    calc
      _ <= (d : ℝ≥0∞) ^ (-nu) * (d : ℝ≥0∞) ^ (-nu) * (d : ℝ≥0∞) ^ (-nu) :=
        mul_le_mul' (mul_le_mul' hPd hLcd) hCd
      _ = _ := by rw [hmul, hmul]; congr 1; ring
  have hlambda : (d : ℝ≥0∞) ^ g <= (d : ℝ≥0∞) ^ etaLambda / (P * Lc * C) := by
    calc
      _ <= (d : ℝ≥0∞) ^ (etaLambda + 3 * nu) :=
        ENNReal.rpow_le_rpow_of_exponent_ge hdE1 (by linarith)
      _ = (d : ℝ≥0∞) ^ etaLambda / (d : ℝ≥0∞) ^ (-3 * nu) := by
        rw [hdiv]; congr 1; ring
      _ <= _ := ENNReal.div_le_div le_rfl hpayment
  have hcoarse : (d : ℝ≥0∞) ^ ((1 - 5 * epsilon) * etaCoarse) <=
      (d : ℝ≥0∞) ^ etaLambda / (P * Lc * C) :=
    (ENNReal.rpow_le_rpow_of_exponent_ge hdE1 (by linarith)).trans hlambda
  have houterCF : (16 * P * Lc * C / (d : ℝ≥0∞) ^ etaLambda) *
      (d : ℝ≥0∞) ^ (-xi / 160) <=
        (trialCoarseDensityConstantW97 : ℝ≥0∞) * (d : ℝ≥0∞) ^ (-epsilon) := by
    calc
      _ = 16 * (P * Lc * C / (d : ℝ≥0∞) ^ etaLambda) *
          (d : ℝ≥0∞) ^ (-xi / 160) := by simp only [div_eq_mul_inv]; ring
      _ <= 16 * ((d : ℝ≥0∞) ^ (-3 * nu) / (d : ℝ≥0∞) ^ etaLambda) *
          (d : ℝ≥0∞) ^ (-xi / 160) := by gcongr
      _ = 16 * (d : ℝ≥0∞) ^ (-3 * nu - etaLambda - xi / 160) := by
        rw [hdiv, mul_assoc, hmul]; congr 2; ring
      _ <= (trialCoarseDensityConstantW97 : ℝ≥0∞) * (d : ℝ≥0∞) ^ (-epsilon) :=
        mul_le_mul' hCDelta (ENNReal.rpow_le_rpow_of_exponent_ge hdE1 (by linarith))
  have hnormalize : 16 * (fineNormalizeDilate.C 1 : ℝ≥0∞) * (d : ℝ≥0∞) ^ etaFine <=
      (d : ℝ≥0∞) ^ (2 * g) / 16 := by
    have h := ENNReal.div_le_div_right hnorm (16 : ℝ≥0∞)
    have halg (z x : ℝ≥0∞) : 16 * z * x = 256 * z * x / 16 := by
      rw [div_eq_mul_inv]
      calc
        _ = (16 * (16 : ℝ≥0∞)⁻¹) * (16 * z * x) := by
          rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
        _ = _ := by ring
    rw [← halg] at h
    exact h
  have hfrost : ((d : ℝ≥0∞) ^ (2 * g) / 16)⁻¹ * (d : ℝ≥0∞) ^ (-epsilon / 10) <=
      2 * (d : ℝ≥0∞) ^ (-epsilon / 5) := by
    calc
      _ = 16 * (d : ℝ≥0∞) ^ (-2 * g - epsilon / 10) := by
        rw [ENNReal.inv_div (Or.inl (by norm_num)) (Or.inl (by norm_num)),
          div_eq_mul_inv, ← ENNReal.rpow_neg, mul_assoc, hmul]
        congr 2
        ring
      _ <= (d : ℝ≥0∞) ^ (-epsilon / 5) := hfrob
      _ <= _ := le_mul_of_one_le_left' (by norm_num)
  have hfinepay : 16 / (d : ℝ≥0∞) ^ g * ((fineAverageDilate.C 1 1 : ℝ≥0∞) *
      (d : ℝ≥0∞) ^ (-3 * epsilon / 10)) <= (d : ℝ≥0∞) ^ (-epsilon / 2) := by
    calc
      _ = (16 * (fineAverageDilate.C 1 1 : ℝ≥0∞)) *
          (d : ℝ≥0∞) ^ (-g - 3 * epsilon / 10) := by
        rw [div_eq_mul_inv, ← ENNReal.rpow_neg]
        calc
          _ = (16 * (fineAverageDilate.C 1 1 : ℝ≥0∞)) *
            ((d : ℝ≥0∞) ^ (-g) * (d : ℝ≥0∞) ^ (-3 * epsilon / 10)) := by ring
          _ = _ := by rw [hmul]; congr 2; ring
      _ <= _ := hfine
  refine ⟨hlambda, hcoarse, houterCF, hinner, hnormalize, hfrost, hfinepay, ?_, ?_⟩
  · calc
      _ = 2 * (P * Lc * C) := by ring
      _ <= 2 * (d : ℝ≥0∞) ^ (-3 * nu) := mul_le_mul' le_rfl hpayment
      _ <= _ := hcost
  · convert hkB using 1; congr 1; ring

/-- S4a: the actual tube product, coarse KT application and average-fullness
fine KF application are constructed here. No analytic bound is an input. -/
theorem exists_actual_small_width_analytic_application_w97
    (hdim : Module.finrank ℝ E = 3)
    (beta gamma epsilon xi : ℝ)
    (hbeta : 0 < beta) (hbetagamma : beta < gamma) (hgamma : gamma <= 1)
    (hepsilon : 0 < epsilon) (hepsilon_lt : epsilon < 1 / 3)
    (hgap : 3 * epsilon / 2 <= (gamma - beta) / 1000)
    (hxi : 0 < xi) (hxiupper : xi <= 4 * epsilon ^ (3 : Nat) * beta / 25000)
    (Cinner : ℝ≥0)
    (hKT : KatzTaoEstimate.{uI} E beta) (hKF : FrostmanEstimate.{uI} E gamma) :
    ∃ (etaMax nu : ℝ), 0 < etaMax ∧ 0 < nu ∧
      ∀ etaLambda : ℝ, 0 < etaLambda -> etaLambda <= etaMax ->
      ∀ᶠ (d : ℝ≥0) in 𝓝[>] 0,
      ∀ {iota : Type uI} [DecidableEq iota]
        (F H : Finset iota) (Y : iota -> ShadedTube d E) (R : ℝ≥0)
        (J : Finset (Finset iota)) (B : Finset iota -> Tube R E)
        (parent : iota -> Finset iota) (P : ℝ≥0∞),
        F.Nonempty -> H.Nonempty -> H ⊆ F ->
        d <= R -> R <= d ^ (1 - 5 * epsilon) -> R <= 1 / 4 ->
        (∀ i ∈ F, (Y i).carrier ⊆ Metric.closedBall 0 1) ->
        (H : Set iota).Pairwise (fun i j => IsEssentiallyDistinct (Y i).carrier (Y j).carrier) ->
        H.image parent = J ->
        (∀ i ∈ H, (Y i).toConvexSpaceBody <= (B (parent i)).toConvexSpaceBody) ->
        (∀ j ∈ J, (B j).carrier ⊆ Metric.closedBall 0 2) ->
        1 <= P -> P < ⊤ -> P <= (d : ℝ≥0∞) ^ (-nu) ->
        (∑ i ∈ F, volume (Y i).shade) <= P * ∑ i ∈ H, volume (Y i).shade ->
        (d : ℝ≥0∞) ^ etaLambda <= fullness' F (fun i => (Y i).toShadedBody) ->
        frostmanConstIn F (fun i => (Y i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall <=
          (d : ℝ≥0∞) ^ (-xi / 160) ->
        maxDensity J (fun j => (B j).toConvexSpaceBody) <=
          (trialCoarseDensityConstantW97 : ℝ≥0∞) * (d : ℝ≥0∞) ^ (-31 * epsilon) ->
        (∀ j ∈ J, frostmanConstIn (completeFibreW94 H parent j)
          (fun i => (Y i).toConvexSpaceBody) (B j).toConvexSpaceBody <=
            (Cinner : ℝ≥0∞) * (d : ℝ≥0∞) ^ (-trialSourceKappaW97 gamma epsilon xi)) ->
        ∃ (Hb : Finset iota) (Jb : Finset (Finset iota))
          (G : ShadedBody.ShadedFactorFamily E iota (Finset iota))
          (Yi : iota -> ShadedTube d E) (Yo : Finset iota -> ShadedTube R E)
          (j : Finset iota),
          Jb ⊆ J ∧ Hb = H.filter (fun i => parent i ∈ Jb) ∧
          G.outerSet ⊆ Jb ∧ j ∈ G.outerSet ∧
          G.innerSet = Hb.filter (fun i => parent i ∈ G.outerSet) ∧ G.parent = parent ∧
          (∀ k ∈ G.outerSet, G.fiber k = completeFibreW94 H parent k) ∧
          (∀ i ∈ G.innerSet, (Yi i).toTube = (Y i).toTube ∧
            (Yi i).toShadedBody = G.innerBody i) ∧
          (∀ k ∈ G.outerSet, (Yo k).toTube = B k ∧ (Yo k).toShadedBody = G.outerBody k) ∧
          fullness' G.innerSet G.innerBody <= fullness' (G.fiber j) G.innerBody ∧
          ShadedBody.multiplicity G.outerSet G.outerBody <=
            (d : ℝ≥0∞) ^ (10 * epsilon) * (R : ℝ≥0∞) ^ (-2 * gamma) *
              ((G.outerSet.card : ℝ≥0∞) * (R : ℝ≥0∞) ^ (2 : Nat)) ^ (1 - gamma / 2) ∧
          ShadedBody.multiplicity (G.fiber j) G.innerBody <=
            (d : ℝ≥0∞) ^ (-epsilon / 2) * ((d / R : ℝ≥0) : ℝ≥0∞) ^ (-2 * gamma) *
              (((G.fiber j).card : ℝ≥0∞) * ((d / R : ℝ≥0) : ℝ≥0∞) ^ (2 : Nat)) ^
                (1 - gamma / 2) ∧
          ((G.fiber j).card : ℝ≥0∞) * (G.outerSet.card : ℝ≥0∞) <= 2 * (F.card : ℝ≥0∞) ∧
          ShadedBody.multiplicity F (fun i => (Y i).toShadedBody) <=
            P * (dyadicPigeonholeNatConstant H.card : ℝ≥0∞) *
              (trialTubeProductCostW97 d Hb.card : ℝ≥0∞) *
              ShadedBody.multiplicity G.outerSet G.outerBody *
              ShadedBody.multiplicity (G.fiber j) G.innerBody ∧
          ShadedBody.multiplicity F (fun i => (Y i).toShadedBody) <=
            (d : ℝ≥0∞) ^ (17 * epsilon / 2) * (d : ℝ≥0∞) ^ (-2 * gamma) *
              ((F.card : ℝ≥0∞) * (d : ℝ≥0∞) ^ (2 : Nat)) ^ (1 - gamma / 2) ∧
          detailedInnerGoodW94 F Y gamma epsilon xi := by
  classical
  have hgamma0 : 0 < gamma := hbeta.trans hbetagamma
  have hbeta1 : beta < 1 := hbetagamma.trans_le hgamma
  have hp0 : 0 <= 1 - gamma / 2 := by linarith
  have hp1 : 1 - gamma / 2 <= 1 := by linarith
  have hmin : 0 < min xi epsilon := lt_min hxi hepsilon
  let L : Nat := Nat.ceil (100 / min xi epsilon) + 1
  have hL : 1 <= L := by dsimp [L]; omega
  have hLreal : 100 / min xi epsilon <= (L : ℝ) := by
    have h := Nat.le_ceil (100 / min xi epsilon)
    dsimp only [L]
    push_cast
    linarith
  have hLmin : (1 : ℝ) / L <= min xi epsilon / 100 := by
    apply (div_le_iff₀ (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hL))).mpr
    have h := (div_le_iff₀ hmin).mp hLreal
    nlinarith
  obtain ⟨heps, heps5, hgap750, hgap74, hgap10, hL12, hkappa0, hkappa,
    hxiBudget, hcombined, hGoodGap⟩ := trial_source_analytic_numeric_budget_w97
      beta gamma epsilon xi hbeta hbetagamma hgamma hepsilon hepsilon_lt hgap hxi hxiupper L hL hLmin
  have hCDelta : 1 <= trialCoarseDensityConstantW97 := le_max_left _ _
  obtain ⟨etaCoarse, hetaCoarse, hcoarse⟩ := multiplicity_coarse_le_of_const_ball
    hdim hbeta.le hbeta1 hgamma0 hgamma hKT
    (ε := epsilon) (ε₂ := 3 * epsilon / 2) (ap' := epsilon)
    hepsilon heps5 hepsilon (by linarith) (by linarith) (by linarith) hgap10
    hCDelta 2 (by norm_num)
  obtain ⟨etaFine, hetaFine, hfine⟩ := multiplicity_le_fine_avg_dilate hdim 1
    hgamma0.le hgamma hKF (epsilon / 10) (by positivity)
  obtain ⟨g, nu, etaMax, hg, hgeps, hgfine, hgcoarse, hnu, hnug, hnuxi, hnuP,
    hmax, hmaxP, hmaxRaw, hmaxXi, hmaxG, hschedule⟩ :=
    exists_trial_analytic_payment_schedule_w97 epsilon xi (epsilon / 100) 1 etaCoarse etaFine
      hepsilon heps hxi hxiBudget (by positivity) le_rfl (by norm_num) hetaCoarse hetaFine
      (trialSourceKappaW97 gamma epsilon xi) hkappa Cinner
  refine ⟨etaMax, nu, hmax, hnu, ?_⟩
  intro etaLambda hetaLambda hetaMax
  filter_upwards [hcoarse, hfine (epsilon / 10) (epsilon / 2) g (by positivity),
      hschedule etaLambda hetaLambda hetaMax,
      trial_analytic_extra_costs_eventually_w97 nu (cardBound.C : ℝ) hnu
        (by exact_mod_cast cardBound.one_le_C),
      eventually_le_one_nhdsGT, self_mem_nhdsWithin]
    with d hcoarseD hfineD hscheduleD hextra hd1 hd
  intro iota _ F H Y R J B parent P hF hH hHF hdR hRwindow hRquarter hball hED
    himage hcontain hBball hP hPfinite hPd hmass hfull hCF hmaxDensity hlocalCF
  have hR1 : R <= 1 := hRquarter.trans
    ((div_le_one (by norm_num : (0 : ℝ≥0) < 4)).mpr (by norm_num))
  have hdE0 : (d : ℝ≥0∞) ≠ 0 := by exact_mod_cast hd.ne'
  have hdEt : (d : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hdE1 : (d : ℝ≥0∞) <= 1 := by exact_mod_cast hd1
  have hR0 : R ≠ 0 := (hd.trans_le hdR).ne'
  have hRE0 : (R : ℝ≥0∞) ≠ 0 := by exact_mod_cast hR0
  have hREt : (R : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  let lambda : ℝ≥0∞ := (d : ℝ≥0∞) ^ etaLambda
  have hlambda : 0 < lambda := ENNReal.rpow_pos (by exact_mod_cast hd) hdEt
  have hlambdat : lambda < ⊤ := lt_top_iff_ne_top.mpr
    (ENNReal.rpow_ne_top_of_ne_zero hdE0 hdEt)
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hmassF : 0 < ∑ i ∈ F, volume (Y i).shade := by
    have hpos := hlambda.trans_le hfull
    by_contra hnot
    have hz := nonpos_iff_eq_zero.mp (not_lt.mp hnot)
    simp only [fullness', hz, ENNReal.zero_div, lt_self_iff_false] at hpos
  have hmassH : 0 < ∑ i ∈ H, volume (Y i).shade := by
    by_contra hnot
    have hz := nonpos_iff_eq_zero.mp (not_lt.mp hnot)
    rw [hz, mul_zero] at hmass
    exact not_le_of_gt hmassF hmass
  obtain ⟨k, Jb, Hb, FF, hk, hJbdef, hJbne, hJbJ, hHbdef, hHbne, hHbH,
    hHbimage, hwhole, hFFinner, hFFouter, hFFparent, hFFY, hFFB, hFFwhole,
    hmassHb, hpaidHb⟩ := exists_balanced_whole_fibres_factorFamily_w97
      F H Y hHF hmassH J B parent himage hcontain P hPfinite hmass
  let Lc := dyadicPigeonholeNatConstant H.card
  have hLc1 : (1 : ℝ≥0∞) <= (Lc : ℝ≥0∞) := by
    dsimp [Lc, dyadicPigeonholeNatConstant]
    exact_mod_cast Nat.le_add_left 1 (Nat.log 2 H.card)
  have hband : ∀ j ∈ Jb, 2 ^ k <= (completeFibreW94 H parent j).card ∧
      (completeFibreW94 H parent j).card < 2 * 2 ^ k := by
    intro j hj
    rw [hJbdef] at hj
    simpa only [pow_succ, Nat.mul_comm] using (Finset.mem_filter.mp hj).2
  obtain ⟨G, Yi, Yo, hGone, hGoJb, hGinner, hGine, hGparent, hGimage,
    hGiBody, hGoBody, hGwhole, hYi, hYo, hYishade, hfullO, hfullI, hpaidG,
    hproduct, hcardProduct, hGCF, hGlocalCF, j, hj, havg⟩ :=
    exists_actual_tube_product_with_original_frostman_w97 hdim hd hdR hR1 F H Hb Y
      hF hHF hHbH hball Jb B parent hHbimage hwhole (fun j hj => hBball j (hJbJ hj))
      FF hFFinner hFFouter hFFparent hFFY hFFB P (Lc : ℝ≥0∞) lambda hP0 hPfinite
      (zero_lt_one.trans_le hLc1) (by simp) hlambda hlambdat hfull hpaidHb
      (2 ^ k) (one_le_pow₀ (by norm_num)) hband
  let C := trialTubeProductCostW97 d Hb.card
  have hC1 : (1 : ℝ≥0∞) <= (C : ℝ≥0∞) := by
    exact_mod_cast shadingMultiplicityEstimateForRhoTubesDilate.one_le_C 3 Hb.card d 1
  have hcardH : (H.card : ℝ) <= (cardBound.C : ℝ) * (d : ℝ) ^ (-4 : ℝ) := by
    have hc := card_le hdim hd hd1 H (fun i => (Y i).toTube) (fun i hi => hball i (hHF hi)) hED
    have ht : (cardBound.C : ℝ≥0∞) * (d : ℝ≥0∞) ^ (-4 : ℝ) ≠ ⊤ := by finiteness
    have hcR := (ENNReal.toReal_le_toReal (by simp) ht).mpr hc
    simpa only [ENNReal.toReal_natCast, ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
      ENNReal.coe_toReal] using hcR
  obtain ⟨hLcd, hCd⟩ := hextra H.card Hb.card hHbne.card_pos (Finset.card_le_card hHbH) hcardH
  obtain ⟨hfullPay, hcoarseFullPay, hcoarseCFPay, hinnerPay, hnormPay,
    hfrostPay, hfinePay, hproductPay, hkBPay⟩ :=
    hscheduleD P (Lc : ℝ≥0∞) (C : ℝ≥0∞) hP hPfinite hLc1 (by simp) hC1 (by simp)
      hPd hLcd hCd
  have hGsubHb : G.innerSet ⊆ Hb := by rw [hGinner]; exact Finset.filter_subset _ _
  have hGoJ : G.outerSet ⊆ J := hGoJb.trans hJbJ
  have hfibsub : ∀ l, G.fiber l ⊆ G.innerSet := by
    intro l i hi
    have hi' : i ∈ G.innerSet ∧ G.parent i = l := by
      simpa only [ShadedBody.ShadedFactorFamily.fiber, Finset.mem_filter] using hi
    exact hi'.1
  have hYiCarrier : ∀ i ∈ Hb, (Yi i).carrier = (Y i).carrier := fun i hi =>
    congrArg (fun T : Tube d E => T.carrier) (hYi i hi).1
  have hYoCarrier : ∀ l ∈ G.outerSet, (Yo l).carrier = (B l).carrier := fun l hl =>
    congrArg (fun T : Tube R E => T.carrier) (hYo l hl).1
  have hYoConvex : ∀ l ∈ G.outerSet, (Yo l).toConvexSpaceBody = (B l).toConvexSpaceBody :=
    fun l hl => congrArg Tube.toConvexSpaceBody (hYo l hl).1
  have hfullOuter : fullness' G.outerSet (fun l => (Yo l).toShadedBody) =
      fullness' G.outerSet G.outerBody := by
    unfold fullness'
    congr 1
    · exact Finset.sum_congr rfl fun l hl => congrArg (fun Z : ShadedBody E => volume Z.shade) (hYo l hl).2
    · exact Finset.sum_congr rfl fun l hl => congrArg (fun Z : ShadedBody E => volume Z.carrier) (hYo l hl).2
  have hfullFiber : fullness' (G.fiber j) (fun i => (Yi i).toShadedBody) =
      fullness' (G.fiber j) G.innerBody := by
    unfold fullness'
    congr 1
    · exact Finset.sum_congr rfl fun i hi => congrArg (fun Z : ShadedBody E => volume Z.shade)
        (hYi i (hGsubHb (hfibsub j hi))).2
    · exact Finset.sum_congr rfl fun i hi => congrArg (fun Z : ShadedBody E => volume Z.carrier)
        (hYi i (hGsubHb (hfibsub j hi))).2
  have hmultOuter : ShadedBody.multiplicity G.outerSet (fun l => (Yo l).toShadedBody) =
      ShadedBody.multiplicity G.outerSet G.outerBody :=
    Tube.multiplicity_congr_of_shading_eq _ _ _ fun l hl => congrArg ShadedBody.shade (hYo l hl).2
  have hmultFiber : ShadedBody.multiplicity (G.fiber j) (fun i => (Yi i).toShadedBody) =
      ShadedBody.multiplicity (G.fiber j) G.innerBody :=
    Tube.multiplicity_congr_of_shading_eq _ _ _ fun i hi =>
      congrArg ShadedBody.shade (hYi i (hGsubHb (hfibsub j hi))).2
  have hcoarseActual : ShadedBody.multiplicity G.outerSet G.outerBody <=
      (d : ℝ≥0∞) ^ (10 * epsilon) * (R : ℝ≥0∞) ^ (-2 * gamma) *
        ((G.outerSet.card : ℝ≥0∞) * (R : ℝ≥0∞) ^ (2 : Nat)) ^ (1 - gamma / 2) := by
    rw [← hmultOuter]
    apply hcoarseD R hdR hRwindow (by exact_mod_cast hRquarter) G.outerSet Yo hGone
    · intro l hl
      rw [hYoCarrier l hl]
      simpa only [NNReal.coe_ofNat] using hBball l (hGoJ hl)
    · rw [ShadedBody.coe_fullness, hfullOuter]
      exact hcoarseFullPay.trans hfullO
    · rw [maxDensity_congr hYoConvex]
      have hbound := (maxDensity_mono (W := fun l => (B l).toConvexSpaceBody) hGoJ).trans hmaxDensity
      convert hbound using 1 <;> congr 2; ring
    · rw [frostmanConstIn_congr G.outerSet hYoConvex]
      have hbound := hGCF.trans (mul_le_mul' le_rfl hCF)
      exact hbound.trans hcoarseCFPay
  have hfineActual : ShadedBody.multiplicity (G.fiber j) G.innerBody <=
      (d : ℝ≥0∞) ^ (-epsilon / 2) * ((d / R : ℝ≥0) : ℝ≥0∞) ^ (-2 * gamma) *
        (((G.fiber j).card : ℝ≥0∞) * ((d / R : ℝ≥0) : ℝ≥0∞) ^ (2 : Nat)) ^
          (1 - gamma / 2) := by
    have hfibreNe : (G.fiber j).Nonempty := by
      have hjimage : j ∈ G.innerSet.image parent := hGimage.symm ▸ hj
      obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp hjimage
      refine ⟨i, ?_⟩
      simp only [ShadedBody.ShadedFactorFamily.fiber, Finset.mem_filter]
      exact ⟨hi, by simpa only [hGparent] using hij⟩
    have hYicontain : ∀ i ∈ G.fiber j, (Yi i).toConvexSpaceBody <= (B j).toConvexSpaceBody := by
      intro i hi
      have hiHb := hGsubHb (hfibsub j hi)
      have hiHf : i ∈ completeFibreW94 H parent j := by rwa [hGwhole j hj] at hi
      obtain ⟨hiH, hij⟩ := Finset.mem_filter.mp hiHf
      rw [congrArg Tube.toConvexSpaceBody (hYi i hiHb).1]
      simpa only [hij] using hcontain i hiH
    have hYiED : (G.fiber j : Set iota).Pairwise
        (fun i l => IsEssentiallyDistinct (Yi i).carrier (Yi l).carrier) := by
      intro i hi l hl hil
      rw [hYiCarrier i (hGsubHb (hfibsub j hi)), hYiCarrier l (hGsubHb (hfibsub j hl))]
      exact hED (hHbH (hGsubHb (hfibsub j hi))) (hHbH (hGsubHb (hfibsub j hl))) hil
    have hYiCF : frostmanConstIn (G.fiber j) (fun i => (Yi i).toConvexSpaceBody)
        (B j).toConvexSpaceBody <= (d : ℝ≥0∞) ^ (-epsilon / 10) := by
      rw [frostmanConstIn_congr (G.fiber j) (fun i hi =>
        congrArg ShadedBody.toConvexSpaceBody (hYi i (hGsubHb (hfibsub j hi))).2)]
      rw [hGlocalCF j hj]
      exact (hlocalCF j (hGoJ hj)).trans hinnerPay
    have hYiFull : (d : ℝ≥0∞) ^ g <= fullness (G.fiber j) (fun i => (Yi i).toShadedBody) := by
      rw [ShadedBody.coe_fullness, hfullFiber]
      exact hfullPay.trans (hfullI.trans havg)
    rw [← hmultFiber]
    rw [show -epsilon / 2 = -(epsilon / 2) by ring]
    apply hfineD R hdR hR1 (B j) Yi (B j).toConvexSpaceBody 1 1
      (R := 2) le_rfl le_rfl hfibreNe (hBball j (hGoJ hj))
    · simp [Kakeya.Tube.dilate_one]
    · simp [Kakeya.Tube.dilate_one]
    · exact hYicontain
    · exact hYiED
    · simpa only [neg_div] using hYiCF
    · exact hYiFull
    · exact hnormPay
    · convert hfrostPay using 1 <;> (try simp only [ENNReal.coe_one, mul_one]) <;> congr 2 <;> ring
    · convert hfinePay using 1 <;> (try simp only [ENNReal.coe_one, one_mul]) <;> congr 3 <;> ring
  have hmuF : ShadedBody.multiplicity F (fun i => (Y i).toShadedBody) <=
      P * (Lc : ℝ≥0∞) * (C : ℝ≥0∞) * ShadedBody.multiplicity G.outerSet G.outerBody *
        ShadedBody.multiplicity (G.fiber j) G.innerBody := by
    have hmuHb := ShadedBody.multiplicity_le_mul_of_sum_shade_le_of_biUnion_subset
      F (fun i => (Y i).toShadedBody) Hb (fun i => (Y i).toShadedBody) (P * (Lc : ℝ≥0∞))
      (Set.iUnion₂_mono' fun i hi => ⟨i, hHF (hHbH hi), Set.Subset.rfl⟩) hpaidHb
    exact hmuHb.trans (by simpa only [mul_assoc] using mul_le_mul_right (hproduct j hj) (P * (Lc : ℝ≥0∞)))
  have hcombinedActual : ShadedBody.multiplicity F (fun i => (Y i).toShadedBody) <=
      (d : ℝ≥0∞) ^ (17 * epsilon / 2) * (d : ℝ≥0∞) ^ (-2 * gamma) *
        ((F.card : ℝ≥0∞) * (d : ℝ≥0∞) ^ (2 : Nat)) ^ (1 - gamma / 2) := by
    let q : ℝ≥0∞ := ((d / R : ℝ≥0) : ℝ≥0∞)
    have hq0 : q ≠ 0 := by
      dsimp [q]
      exact_mod_cast (div_ne_zero hd.ne' hR0)
    have hRq : (R : ℝ≥0∞) * q = d := by
      dsimp [q]
      rw [ENNReal.coe_div hR0, mul_comm, ENNReal.div_mul_cancel hRE0 hREt]
    have hdimCancel : (R : ℝ≥0∞) ^ (-2 * gamma) * q ^ (-2 * gamma) =
        (d : ℝ≥0∞) ^ (-2 * gamma) := by
      rw [← ENNReal.mul_rpow_of_ne_zero hRE0 hq0, hRq]
    have hcardCancel : ((G.outerSet.card : ℝ≥0∞) * (R : ℝ≥0∞) ^ (2 : Nat)) ^
        (1 - gamma / 2) * (((G.fiber j).card : ℝ≥0∞) * q ^ (2 : Nat)) ^
          (1 - gamma / 2) <= 2 * ((F.card : ℝ≥0∞) * (d : ℝ≥0∞) ^ (2 : Nat)) ^
            (1 - gamma / 2) := by
      rw [← ENNReal.mul_rpow_of_nonneg _ _ hp0]
      have hid : (G.outerSet.card : ℝ≥0∞) * (R : ℝ≥0∞) ^ (2 : Nat) *
          ((G.fiber j).card * q ^ (2 : Nat)) =
            ((G.fiber j).card * (G.outerSet.card : ℝ≥0∞)) * (d : ℝ≥0∞) ^ (2 : Nat) := by
        rw [← hRq]
        ring
      rw [hid]
      calc
        _ <= (2 * (F.card : ℝ≥0∞) * (d : ℝ≥0∞) ^ (2 : Nat)) ^ (1 - gamma / 2) :=
          ENNReal.rpow_le_rpow (mul_le_mul' (hcardProduct j hj) le_rfl) hp0
        _ = (2 : ℝ≥0∞) ^ (1 - gamma / 2) *
            ((F.card : ℝ≥0∞) * (d : ℝ≥0∞) ^ (2 : Nat)) ^ (1 - gamma / 2) := by
          rw [mul_assoc, ENNReal.mul_rpow_of_nonneg _ _ hp0]
        _ <= _ := mul_le_mul' (by
          calc
            (2 : ℝ≥0∞) ^ (1 - gamma / 2) <= (2 : ℝ≥0∞) ^ (1 : ℝ) :=
              ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) hp1
            _ = 2 := ENNReal.rpow_one _) le_rfl
    have hprodActual : ShadedBody.multiplicity G.outerSet G.outerBody *
        ShadedBody.multiplicity (G.fiber j) G.innerBody <=
          2 * (d : ℝ≥0∞) ^ (19 * epsilon / 2) * (d : ℝ≥0∞) ^ (-2 * gamma) *
            ((F.card : ℝ≥0∞) * (d : ℝ≥0∞) ^ (2 : Nat)) ^ (1 - gamma / 2) := by
      calc
        _ <= ((d : ℝ≥0∞) ^ (10 * epsilon) * (R : ℝ≥0∞) ^ (-2 * gamma) *
            ((G.outerSet.card : ℝ≥0∞) * (R : ℝ≥0∞) ^ (2 : Nat)) ^ (1 - gamma / 2)) *
            ((d : ℝ≥0∞) ^ (-epsilon / 2) * q ^ (-2 * gamma) *
              (((G.fiber j).card : ℝ≥0∞) * q ^ (2 : Nat)) ^ (1 - gamma / 2)) :=
          mul_le_mul' hcoarseActual hfineActual
        _ = ((d : ℝ≥0∞) ^ (10 * epsilon) * (d : ℝ≥0∞) ^ (-epsilon / 2)) *
            ((R : ℝ≥0∞) ^ (-2 * gamma) * q ^ (-2 * gamma)) *
            (((G.outerSet.card : ℝ≥0∞) * (R : ℝ≥0∞) ^ (2 : Nat)) ^ (1 - gamma / 2) *
              (((G.fiber j).card : ℝ≥0∞) * q ^ (2 : Nat)) ^ (1 - gamma / 2)) := by ring
        _ <= (d : ℝ≥0∞) ^ (19 * epsilon / 2) * (d : ℝ≥0∞) ^ (-2 * gamma) *
            (2 * ((F.card : ℝ≥0∞) * (d : ℝ≥0∞) ^ (2 : Nat)) ^ (1 - gamma / 2)) := by
          rw [hdimCancel, ← ENNReal.rpow_add _ _ hdE0 hdEt,
            show 10 * epsilon + -epsilon / 2 = 19 * epsilon / 2 by ring]
          exact mul_le_mul' le_rfl hcardCancel
        _ = _ := by ring
    calc
      _ <= (P * (Lc : ℝ≥0∞) * (C : ℝ≥0∞)) *
          (ShadedBody.multiplicity G.outerSet G.outerBody *
            ShadedBody.multiplicity (G.fiber j) G.innerBody) := by simpa only [mul_assoc] using hmuF
      _ <= (P * (Lc : ℝ≥0∞) * (C : ℝ≥0∞)) *
          (2 * (d : ℝ≥0∞) ^ (19 * epsilon / 2) * (d : ℝ≥0∞) ^ (-2 * gamma) *
            ((F.card : ℝ≥0∞) * (d : ℝ≥0∞) ^ (2 : Nat)) ^ (1 - gamma / 2)) :=
        mul_le_mul' le_rfl hprodActual
      _ = (2 * P * (Lc : ℝ≥0∞) * (C : ℝ≥0∞)) * (d : ℝ≥0∞) ^ (19 * epsilon / 2) *
          (d : ℝ≥0∞) ^ (-2 * gamma) *
            ((F.card : ℝ≥0∞) * (d : ℝ≥0∞) ^ (2 : Nat)) ^ (1 - gamma / 2) := by ring
      _ <= (d : ℝ≥0∞) ^ (-epsilon) * (d : ℝ≥0∞) ^ (19 * epsilon / 2) *
          (d : ℝ≥0∞) ^ (-2 * gamma) *
            ((F.card : ℝ≥0∞) * (d : ℝ≥0∞) ^ (2 : Nat)) ^ (1 - gamma / 2) := by
        exact mul_le_mul' (mul_le_mul' (mul_le_mul' hproductPay le_rfl) le_rfl) le_rfl
      _ = _ := by
        rw [← ENNReal.rpow_add _ _ hdE0 hdEt]
        congr 3
        ring
  refine ⟨Hb, Jb, G, Yi, Yo, j, hJbJ, hHbdef, hGoJb, hj, hGinner, hGparent,
    hGwhole, (fun i hi => hYi i (hGsubHb hi)), hYo, havg, hcoarseActual, hfineActual,
    hcardProduct j hj, hmuF, hcombinedActual, ?_⟩
  dsimp only [detailedInnerGoodW94]
  rw [mul_comm ((d : ℝ≥0∞) ^ (2 : Nat)) (F.card : ℝ≥0∞)]
  exact hcombinedActual.trans (mul_le_mul' (mul_le_mul'
    (ENNReal.rpow_le_rpow_of_exponent_ge hdE1 hGoodGap.le) le_rfl) le_rfl)

/-- S4: caller-facing actual small-width Good. All carrier, balanced-fibre
and analytic witnesses are constructed from the SAME G0-G2 output data. -/
theorem actual_small_width_good_from_factored_family_w97
    (hdim : Module.finrank ℝ E = 3)
    (beta gamma epsilon xi : ℝ)
    (hbeta : 0 < beta) (hbetagamma : beta < gamma) (hgamma : gamma <= 1)
    (hepsilon : 0 < epsilon) (hepsilon_lt : epsilon < 1 / 3)
    (hgap : 3 * epsilon / 2 <= (gamma - beta) / 1000)
    (hxi : 0 < xi) (hxiupper : xi <= 4 * epsilon ^ (3 : Nat) * beta / 25000)
    (L : Nat) (hL : 1 <= L) (hLmin : (1 : ℝ) / L <= min xi epsilon / 100)
    (Ctw : ℝ≥0) (hCtw : 1 <= Ctw)
    (hKT : KatzTaoEstimate.{uI} E beta) (hKF : FrostmanEstimate.{uI} E gamma) :
    ∃ (etaMax nu : ℝ), 0 < etaMax ∧ 0 < nu ∧
      ∀ etaLambda : ℝ, 0 < etaLambda -> etaLambda <= etaMax ->
      ∀ᶠ (d : ℝ≥0) in 𝓝[>] 0,
      ∀ {iota pi : Type uI} [DecidableEq iota] [DecidableEq pi]
        (F H : Finset iota) (Y : iota -> ShadedTube d E)
        (a b rho : ℝ≥0) (J0 : Finset pi) (Tcentral : pi -> Tube rho E)
        (pcentral : iota -> pi) (U : pi -> Finset iota) (D0 P : ℝ≥0∞),
        F.Nonempty -> H.Nonempty -> H ⊆ F ->
        d <= a -> a <= b -> b <= rho -> rho <= 1 ->
        d ^ (2 * epsilon + 2 / (L : ℝ)) < rho -> rho <= d ^ (2 * epsilon) ->
        b <= d ^ (1 - 3 * epsilon / 2) ->
        (b : ℝ≥0∞) / (a : ℝ≥0∞) < (d : ℝ≥0∞) ^ (-trialSourceKappaW97 gamma epsilon xi) ->
        (∀ i ∈ F, (Y i).carrier ⊆ Metric.closedBall 0 1) ->
        (∀ i ∈ H, (Y i).toTube.IsCentred) ->
        (H : Set iota).Pairwise (fun i j => IsEssentiallyDistinct (Y i).carrier (Y j).carrier) ->
        H.image pcentral = J0 ->
        FlatPrismParentPresentation (D := 1) H Y J0 Tcentral pcentral ->
        (∀ S ∈ J0, (Tcentral S).carrier ⊆ Metric.closedBall 0 2) ->
        lineEssentiallyDistinctW94 J0 Tcentral Ctw ->
        0 < D0 -> D0 < ⊤ ->
        (∀ i ∈ H, i ∈ U (pcentral i)) ->
        (∀ S ∈ J0, ∀ i ∈ U S, (Y i).toConvexSpaceBody <= (Tcentral S).toConvexSpaceBody) ->
        (∀ S ∈ J0, maxDensity (U S) (fun i => (Y i).toConvexSpaceBody) <= 2 * D0) ->
        (Fz : (S : pi) -> ConvexSpaceBody.Factorization (completeFibreW94 H pcentral S)
          (fun i => (Y i).toConvexSpaceBody) 2) ->
        (∀ S ∈ J0, IsPlankFamilyOfDimensions plankPigeonhole.C a b (Fz S).parts
          (fun q => q.convexHull_biUnion (fun i => (Y i).toConvexSpaceBody))) ->
        (∀ S ∈ J0, ∀ q ∈ (Fz S).parts, (D0 / 2) *
          volume (q.convexHull_biUnion (fun i => (Y i).toConvexSpaceBody)).carrier <=
            ∑ i ∈ q, volume (Y i).carrier) ->
        1 <= P -> P < ⊤ -> P <= (d : ℝ≥0∞) ^ (-nu) ->
        (∑ i ∈ F, volume (Y i).shade) <= P * ∑ i ∈ H, volume (Y i).shade ->
        (d : ℝ≥0∞) ^ etaLambda <= fullness' F (fun i => (Y i).toShadedBody) ->
        frostmanConstIn F (fun i => (Y i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall <=
          (d : ℝ≥0∞) ^ (-xi / 160) ->
        detailedInnerGoodW94 F Y gamma epsilon xi := by
  classical
  obtain ⟨heps, heps5, hgap750, hgap74, hgap10, hL12, hkappa0, hkappa,
    hxiBudget, hcombined, hGoodGap⟩ := trial_source_analytic_numeric_budget_w97
      beta gamma epsilon xi hbeta hbetagamma hgamma hepsilon hepsilon_lt hgap hxi hxiupper L hL hLmin
  obtain ⟨etaMax, nu, hmax, hnu, hsmall⟩ := exists_actual_small_width_analytic_application_w97
    hdim beta gamma epsilon xi hbeta hbetagamma hgamma hepsilon hepsilon_lt hgap hxi hxiupper
    (trialInnerCarrierConstantW97 Ctw) hKT hKF
  let kB := trialComparableCarrierScaleW96 plankPigeonhole.C
  have hkB : 1 <= kB := by
    dsimp [kB, trialComparableCarrierScaleW96]
    exact le_add_of_nonneg_left (by positivity)
  refine ⟨etaMax, nu, hmax, hnu, ?_⟩
  intro etaLambda hetaLambda hetaMax
  filter_upwards [hsmall etaLambda hetaLambda hetaMax,
      eventually_finite_const_le_rpow_neg (c := (kB : ℝ≥0∞)) ENNReal.coe_ne_top
        (a := 7 * epsilon / 2) (by positivity),
      ENNReal.eventually_coe_rpow_le_of_pos (ρ := 1 - 5 * epsilon) (by linarith)
        (by norm_num : (0 : ℝ≥0∞) < (1 / 4 : ℝ≥0)),
      eventually_le_one_nhdsGT, self_mem_nhdsWithin]
    with d hsmallD hkBD hquarter hd1 hd
  intro iota pi _ _ F H Y a b rho J0 Tcentral pcentral U D0 P hF hH hHF hda hab hbrho hrho
    hrholower hrhoupper hbwidth hecc hball hcentred hED himage hparent hparentBall hline
    hD0 hD0finite hreference hUparent hUdensity Fz hdims hblockmass
    hP hPfinite hPd hmass hfull hCF
  let R := kB * b
  have hdR : d <= R := hda.trans (hab.trans (by simpa [R] using mul_le_mul_left hkB b))
  have hRwindow : R <= d ^ (1 - 5 * epsilon) := by
    have hkBD' : kB <= d ^ (-7 * epsilon / 2) := by
      rw [show -7 * epsilon / 2 = -(7 * epsilon / 2) by ring]
      apply ENNReal.coe_le_coe.mp
      rw [ENNReal.coe_rpow_of_ne_zero hd.ne']
      exact hkBD
    calc
      R <= d ^ (-7 * epsilon / 2) * d ^ (1 - 3 * epsilon / 2) := mul_le_mul' hkBD' hbwidth
      _ = _ := by rw [← NNReal.rpow_add hd.ne']; congr 1; ring
  have hRquarter : R <= 1 / 4 := hRwindow.trans (by
    apply ENNReal.coe_le_coe.mp
    rw [ENNReal.coe_rpow_of_ne_zero hd.ne']
    exact hquarter)
  have hR1 : R <= 1 := hRquarter.trans
    ((div_le_one (by norm_num : (0 : ℝ≥0) < 4)).mpr (by norm_num))
  obtain ⟨B, attached, label, rep, J, pB, FF, hQ, hB, hlabelimage, hlabelwhole,
    hJ, hJQ, hrepimage, hrepB, hBinj, hpB, himageB, hFFinner, hFFouter, hFFparent,
    hFFY, hFFB, hmerge, hsum, houter, hinner⟩ :=
    exists_actual_carriers_outer_density_and_local_frostman_w97 hdim hd hda hab hbrho hrho
      hR1 H Y hH (fun i hi => hball i (hHF hi)) hcentred J0 Tcentral pcentral himage
      hparent hparentBall Ctw hCtw hline U D0 hD0 hD0finite hreference hUparent hUdensity
      Fz hdims hblockmass
  have hBball : ∀ j ∈ J, (B j).carrier ⊆ Metric.closedBall 0 2 :=
    fun j hj => (hB j (hJQ hj)).2.2.2.1
  have hcontain : ∀ i ∈ H, (Y i).toConvexSpaceBody <= (B (pB i)).toConvexSpaceBody := by
    intro i hi
    have hiFF : i ∈ FF.innerSet := hFFinner.symm ▸ hi
    have h := FF.inner_le_parent i hiFF
    simpa only [hFFY, hFFB, hFFparent] using h
  have hfibre : ∀ j, FF.fiber j = completeFibreW94 H pB j := by
    intro j
    ext i
    simp only [ShadedBody.FactorFamily.fiber, completeFibreW94,
      hFFinner, hFFparent, Finset.mem_filter]
  have hlocal : ∀ j ∈ J, frostmanConstIn (completeFibreW94 H pB j)
      (fun i => (Y i).toConvexSpaceBody) (B j).toConvexSpaceBody <=
        (trialInnerCarrierConstantW97 Ctw : ℝ≥0∞) *
          (d : ℝ≥0∞) ^ (-trialSourceKappaW97 gamma epsilon xi) := by
    intro j hj
    rw [← hfibre j]
    exact (hinner j hj).2.trans (mul_le_mul' le_rfl hecc.le)
  have hdE0 : (d : ℝ≥0∞) ≠ 0 := by exact_mod_cast hd.ne'
  have hdEt : (d : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hdE1 : (d : ℝ≥0∞) <= 1 := by exact_mod_cast hd1
  have hrhopow : (rho : ℝ≥0∞) ^ (-6 : ℝ) <=
      (d : ℝ≥0∞) ^ (-12 * epsilon - 12 / (L : ℝ)) := by
    have h := NNReal.rpow_le_rpow_of_nonpos (NNReal.rpow_pos hd) hrholower.le
      (by norm_num : (-6 : ℝ) <= 0)
    rw [← NNReal.rpow_mul] at h
    have hid : (2 * epsilon + 2 / (L : ℝ)) * (-6) = -12 * epsilon - 12 / (L : ℝ) := by ring
    rw [hid] at h
    have hrho0 : rho ≠ 0 := (hd.trans_le (hda.trans (hab.trans hbrho))).ne'
    rw [← ENNReal.coe_rpow_of_ne_zero hrho0, ← ENNReal.coe_rpow_of_ne_zero hd.ne']
    exact ENNReal.coe_le_coe.mpr h
  have houterPaid : maxDensity J (fun j => (B j).toConvexSpaceBody) <=
      (trialCoarseDensityConstantW97 : ℝ≥0∞) * (d : ℝ≥0∞) ^ (-31 * epsilon) := by
    have hC : (trialOuterCarrierConstantW97 : ℝ≥0∞) <= (trialCoarseDensityConstantW97 : ℝ≥0∞) := by
      exact_mod_cast (le_max_left trialOuterCarrierConstantW97 16).trans
        (le_max_right 1 (max trialOuterCarrierConstantW97 16))
    calc
      _ <= (trialOuterCarrierConstantW97 : ℝ≥0∞) * (rho : ℝ≥0∞) ^ (-6 : ℝ) *
          ((b : ℝ≥0∞) / (a : ℝ≥0∞)) := houter
      _ <= (trialCoarseDensityConstantW97 : ℝ≥0∞) *
          (d : ℝ≥0∞) ^ (-12 * epsilon - 12 / (L : ℝ)) *
          (d : ℝ≥0∞) ^ (-trialSourceKappaW97 gamma epsilon xi) :=
        mul_le_mul' (mul_le_mul' hC hrhopow) hecc.le
      _ = (trialCoarseDensityConstantW97 : ℝ≥0∞) *
          (d : ℝ≥0∞) ^ (-12 * epsilon - 12 / (L : ℝ) - trialSourceKappaW97 gamma epsilon xi) := by
        rw [mul_assoc, ← ENNReal.rpow_add _ _ hdE0 hdEt]
        congr 2
      _ <= _ := mul_le_mul' le_rfl (ENNReal.rpow_le_rpow_of_exponent_ge hdE1 (by linarith))
  obtain ⟨Hb, Jb, G, Yi, Yo, j, hJb, hHb, hGo, hj, hGi, hGp, hGwhole, hYi, hYo,
    havg, hcoarse, hfine, hcard, hmu, hcombinedActual, hgood⟩ :=
    hsmallD F H Y R J B pB P hF hH hHF hdR hRwindow hRquarter hball hED himageB
      hcontain hBball hP hPfinite hPd hmass hfull hCF houterPaid hlocal
  exact hgood

end

end Kakeya.ml1Boot.TrialRestartW94

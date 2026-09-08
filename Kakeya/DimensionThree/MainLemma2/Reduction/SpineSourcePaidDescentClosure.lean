/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourcePaidReachableDescent
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceChosenTowerRealization
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceClosure

/-!
# Conditional closure of Main Lemma 2 from a fixed-Q paid descent producer

Scale-independent descent parameters are packaged in
`Kakeya.ML2Core.SourcePaidDescentParameters`, whose entrance powers and log-base-two `loss`
are fixed before the input scale (`source_exists_paid_descent_scalar_budget`,
`source_eventually_paid_descent_loss`, `source_eventually_half_scale_terminal_payment`).
`SourceFixedQDescentRun` and the open producer obligation `SourceFixedQDescentProducer`
describe one actual entrance with a fixed tower `Q`; `source_dichotomy_of_fixedQ_descent`
turns such a producer into the mass-form Dichotomy. The closing theorems
`Kakeya.ML2Assembly.source_pointwiseCore_of_fixedQ_producers` and
`source_mainLemma2Statement_of_fixedQ_producers` derive `PointwiseCore` and
`VNSUniform.MainLemma2Statement` from `SourcePointwiseFixedQProducers`. Conditional only.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube

namespace Kakeya.ML2Core

universe u

/-- All scale-independent choices of this conditional closure. The actual positive gain
and the paid absolute Sticky accuracy are separate obligations of the terminal producer. -/
structure SourcePaidDescentParameters (beta c : ℝ) where
  M : Nat
  K : Nat
  h : ℝ
  eta0 : ℝ
  q : ℝ
  a0 : ℝ
  eta : ℝ
  stickyAccuracy : ℝ
  stickyPayment : ℝ
  gain : ℝ
  levels_ge_two : 2 <= M
  loss_power_pos : 1 <= K
  potential_step_pos : 0 < h
  input_ceiling_pos : 0 < eta0
  entrance_payment_pos : 0 < q
  descent_payment_pos : 0 < a0
  descent_payment_le : a0 <= eta0
  entrance_fullness_budget : 4 * q <= eta0
  gain_budget : 3 * q + a0 < c
  dichotomy_exponent_pos : 0 < eta
  dichotomy_exponent_le_one : eta <= 1
  dichotomy_exponent_le_entrance : eta <= q
  sticky_accuracy_pos : 0 < stickyAccuracy
  sticky_payment_nonneg : 0 <= stickyPayment
  sticky_margin : stickyAccuracy + stickyPayment <= beta / 2 - c
  actual_gain_margin : 5 * c <= gain

/-- Source S:6136-6146 fixes this exact log-base-two loss before the input scale. -/
noncomputable def SourcePaidDescentParameters.loss {beta c : ℝ}
    (P : SourcePaidDescentParameters beta c) (d : ℝ≥0) : ℝ≥0∞ :=
  sourceFixedPreparationLoss P.K d

/-- The three entrance powers and the final descent power fit below c. -/
theorem source_exists_paid_descent_scalar_budget {eta0 c : ℝ}
    (heta : 0 < eta0) (hc : 0 < c) :
    ∃ q a0 : ℝ, 0 < q /\ 0 < a0 /\ a0 <= eta0 /\
      4 * q <= eta0 /\ 3 * q + a0 < c := by
  let x : ℝ := min eta0 c / 8
  have hx : 0 < x := by dsimp [x]; positivity
  have he : x <= eta0 / 8 := by dsimp [x]; gcongr; exact min_le_left _ _
  have hc' : x <= c / 8 := by dsimp [x]; gcongr; exact min_le_right _ _
  exact ⟨x, x, hx, hx, by linarith, by linarith, by linarith⟩

/-- A single eventual threshold pays every restart AND the final terminal trial. -/
theorem source_eventually_paid_descent_loss {beta c : ℝ}
    (P : SourcePaidDescentParameters beta c) :
    ∀ᶠ d : ℝ≥0 in 𝓝[>] 0,
      0 < d /\ d < 1 /\ 1 <= P.loss d /\ P.loss d ≠ ⊤ /\
      P.loss d ^ (sourceAssignedPotentialCeiling P.M P.h + 1) <=
        (d : ℝ≥0∞) ^ (-P.a0) := by
  have hbound := Kakeya.VeryNotSticky.eventually_ofReal_polylog_pow_le_rpow_neg
    (A := 2) (B := 1) (by norm_num) (by norm_num)
    (P.K * (sourceAssignedPotentialCeiling P.M P.h + 1)) P.descent_payment_pos
  filter_upwards [hbound, Ioo_mem_nhdsGT (show (0 : ℝ≥0) < 1 by norm_num)]
    with d hbound hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.1
  have hd1 : (d : ℝ) <= 1 := by exact_mod_cast hd.2.le
  have hlog : 0 <= Real.logb 2 (1 / (d : ℝ)) :=
    Real.logb_nonneg (by norm_num) (by rw [one_le_div hd0]; exact hd1)
  have hbase : (1 : ℝ) <= 2 + Real.logb 2 (1 / (d : ℝ)) := by linarith
  refine ⟨hd.1, hd.2, ?_, ENNReal.ofReal_ne_top, ?_⟩
  · change 1 <= ENNReal.ofReal _
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (one_le_pow₀ hbase)
  · change ENNReal.ofReal _ ^ _ <= _
    rw [← ENNReal.ofReal_pow (pow_nonneg (by linarith :
      (0 : ℝ) <= 2 + Real.logb 2 (1 / (d : ℝ))) P.K), ← pow_mul]
    simpa only [one_mul, one_div] using hbound

/-- The remaining positive margins absorb the FIXED factor two in d=delta/2. -/
theorem source_eventually_half_scale_terminal_payment {beta c : ℝ}
    (P : SourcePaidDescentParameters beta c) (_hc : 0 < c) :
    ∀ᶠ delta : ℝ≥0 in 𝓝[>] 0,
      0 < delta /\ delta < 1 /\
      (((delta / 2 : ℝ≥0) : ℝ≥0∞) ^
          (-(P.stickyAccuracy + P.stickyPayment) - 3 * P.q - P.a0) <=
        (delta : ℝ≥0∞) ^ (-(beta / 2))) /\
      (((delta / 2 : ℝ≥0) : ℝ≥0∞) ^ (P.gain - 3 * P.q - P.a0) <=
        (delta : ℝ≥0∞) ^ (4 * c)) := by
  let p : ℝ := -(P.stickyAccuracy + P.stickyPayment) - 3 * P.q - P.a0
  let g : ℝ := P.gain - 3 * P.q - P.a0
  have hp : -(beta / 2) < p := by
    dsimp [p]
    linarith [P.sticky_margin, P.gain_budget]
  have hg : 4 * c < g := by
    dsimp [g]
    linarith [P.actual_gain_margin, P.gain_budget]
  have hfinite (e : ℝ) : (((1 / 2 : ℝ≥0) : ℝ≥0∞)) ^ e ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero (by norm_num) ENNReal.coe_ne_top
  have hsticky := Kakeya.VeryNotSticky.eventually_ennreal_mul_rpow_le_rpow (hfinite p) hp
  have hgain := Kakeya.VeryNotSticky.eventually_ennreal_mul_rpow_le_rpow (hfinite g) hg
  filter_upwards [hsticky, hgain,
    Ioo_mem_nhdsGT (show (0 : ℝ≥0) < 1 by norm_num)] with delta hs hg hd
  have hscale (e : ℝ) : (((delta / 2 : ℝ≥0) : ℝ≥0∞)) ^ e =
      (((1 / 2 : ℝ≥0) : ℝ≥0∞)) ^ e * (delta : ℝ≥0∞) ^ e := by
    rw [show delta / 2 = (1 / 2 : ℝ≥0) * delta by ring, ENNReal.coe_mul,
      ENNReal.mul_rpow_of_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top]
  exact ⟨hd.1, hd.2, (hscale p).trans_le hs, (hscale g).trans_le hg⟩

/-- An actual entrance and one fixed Q, with the trial law left explicitly open.
Only definitions are used from the construction modules. -/
structure SourceFixedQDescentRun {beta c : ℝ} (P : SourcePaidDescentParameters beta c)
    {iota : Type u} {delta : ℝ≥0} (S : Finset iota)
    (Z : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3))) where
  canonicalFamily : Finset iota
  initialFamily : Finset iota
  normalized : iota -> ShadedTube (delta / 2) (EuclideanSpace ℝ (Fin 3))
  normalizationMap : iota -> iota
  normalization : SourceCanonicalNormalization S canonicalFamily Z normalized normalizationMap P.q
  initial_subset : initialFamily <= canonicalFamily
  tower : SourceThreadedTower initialFamily (fun i => (normalized i).toTube)
    P.M sourceThreadConstant
  geometry : SourceTowerGeometry tower sourceBottomED sourceLevelED
  neighbour_sharing : SourceTowerNeighbourSharing tower
  tower_mass_retention : (∑ i ∈ canonicalFamily, volume (normalized i).shade) <=
    sourceTowerSelectionLoss P.M canonicalFamily.card *
      ∑ i ∈ initialFamily, volume (normalized i).shade
  entrance_cost : sourceCentringCost delta P.q *
    sourceTowerSelectionLoss P.M canonicalFamily.card <=
      ((delta / 2 : ℝ≥0) : ℝ≥0∞) ^ (-(3 * P.q))
  initial : SourcePaidState initialFamily (fun i => (normalized i).toTube) normalized
  initial_family_identity : initial.family = initialFamily
  initial_shading_identity : initial.shaded = normalized
  entrance_multiplicity : ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <=
    ((delta / 2 : ℝ≥0) : ℝ≥0∞) ^ (-(3 * P.q)) * initial.multiplicity
  original_cardinality : initialFamily.card <= S.card
  original_density : Kakeya.maxDensity initialFamily
    (fun i => (normalized i).toConvexSpaceBody) <=
      ((delta / 2 : ℝ≥0) : ℝ≥0∞) ^ (-P.eta0)
  initial_fullness : ((delta / 2 : ℝ≥0) : ℝ≥0∞) ^ P.eta0 <= initial.fullness
  initial_cardinality_bound : (initialFamily.card : ℝ) <=
    ((delta / 2 : ℝ≥0) : ℝ) ^ (-5 : ℝ)
  actual_reachable_trial : SourceReachablePaidTrialLaw tower P.h P.eta0
    (P.stickyAccuracy + P.stickyPayment) P.gain beta (P.loss (delta / 2)) initial

end Kakeya.ML2Core

namespace Kakeya.ML2Assembly

universe u

open Kakeya.ML2Core

end Kakeya.ML2Assembly

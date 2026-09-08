/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.PartialEstimates
public import Kakeya.Bootstrap
public import Kakeya.Asymptotics
public import Kakeya.DimensionThree.FrostmanEstimateOne

/-!
# The two-parameter partial estimates `K_KT(β, ω)` and `K_F(β, ω)`

Guth-Wang-Zahl state Main Lemma 2 with an exponent drop `ν = ν(β)` produced before the
accuracy `ε`, but their proof produces `ν` only after `ε`.  The detailed Wang-Zahl paper
avoids this by carrying a *second* parameter `ω` in each assertion: a budget standing in the
same power of `δ` as the accuracy, out of which a fixed accuracy can be paid.  Wang-Zahl
Definition 1.5 defines `D(σ, ω)` and `E(σ, ω)`; the gain of Wang-Zahl Proposition 1.7 is
taken in `ω` rather than in `σ`; the `σ`-gain follows by a trade against the packing bound;
and `ω = 0` is recovered by soft closedness.

This module builds the corresponding layer over the development's own one-parameter
`Kakeya.KatzTaoEstimate` and `Kakeya.FrostmanEstimate`, together with the outer-scheme
machinery that consumes it.  Nothing here modifies the one-parameter definitions or any part
of the existing Main Lemma 2 reduction; the module states the corresponding implications.

Contents.

* `Kakeya.KatzTaoEstimateOmega` and `Kakeya.FrostmanEstimateOmega`: the two-parameter
  assertions, with `δ ^ (-ε)` replaced by `δ ^ (-ω - ε)`.  They specialize at `ω = 0` to the
  one-parameter definitions (`Kakeya.katzTaoEstimateOmega_zero`,
  `Kakeya.frostmanEstimateOmega_zero`).
* The elementary transfer lemmas: monotonicity in `ω` and in `β`, the passage from the
  one-parameter assertion, and the `ω`-absorption
  `Kakeya.KatzTaoEstimateOmega.of_forall_gt`.  The absorption is *not* a limit: at accuracy
  `ε` one instantiates the hypothesis at `ω' = ω + ε/2` and inner accuracy `ε/2`.  It cannot
  be written as a limit, because the witnesses `η` and `δ₀` are produced after both `ω'` and
  `ε`, with no uniformity in either.
* The packing bound `Kakeya.eventually_card_le_rpow_neg_three`, and the two consequences that
  need it: the `ω`-to-`β` trade `Kakeya.KatzTaoEstimateOmega.trade` and closedness in `β`
  at fixed `ω` (`Kakeya.KatzTaoEstimateOmega.of_forall_gt_beta`).
* The two-parameter descent `Kakeya.ioc_subset_of_sub_mem_of_monotoneOn_param`, which is the
  existing single-parameter `Kakeya.ioc_subset_of_sub_mem_of_monotoneOn` read at a fixed `ω`.
* The assembly `Kakeya.katzTaoEstimate_of_mainLemma2Omega`: from a two-parameter Main Lemma 2
  in the shape of Wang-Zahl Proposition 1.7, taken as a hypothesis, the one-parameter
  `K_KT(β)` follows for every `β ∈ (0, 1]`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Topology ConvexSpaceBody Filter ShadedBody

namespace Kakeya

universe u

section Definitions

variable
  (E : Type*)
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The two-parameter Katz-Tao estimate `K_KT(β, ω)`.

This is `Kakeya.KatzTaoEstimate` with the accuracy factor `δ ^ (-ε)` of the conclusion
replaced by `δ ^ (-ω - ε)`.  The budget `ω` is a parameter of the assertion, hence available
*before* the accuracy `ε`, which is what lets an input be read at an accuracy fixed in
advance. -/
def KatzTaoEstimateOmega (β ω : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0,
    ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) (δ ^ (- η)) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
      ∑ i ∈ s, volume (T i).shade ≤
        δ ^ (- ω - ε) * s.card ^ β * volume (⋃ i ∈ s, (T i).shade)

end Definitions

section Transfer

variable
  {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `K_KT(·, ω)` is monotone in the exponent `β` at fixed budget, by the same argument as
`Kakeya.KatzTaoEstimate.mono`.  The step is accuracy-preserving: the accuracy witness `η` is
unchanged. -/
theorem KatzTaoEstimateOmega.mono {β β' ω : ℝ} (hββ' : β ≤ β')
    (h : KatzTaoEstimateOmega.{u} E β ω) : KatzTaoEstimateOmega.{u} E β' ω := by
  intro ε hε
  obtain ⟨η, hη, hh⟩ := h ε hε
  refine ⟨η, hη, ?_⟩
  filter_upwards [hh] with δ hh_δ
  intro ι s T hball hKT hfull
  by_cases hcard : s.card = 0
  · have hs : s = ∅ := Finset.card_eq_zero.mp hcard
    subst hs; simp
  refine (hh_δ s T hball hKT hfull).trans ?_
  have hone : (1 : ℝ≥0∞) ≤ (s.card : ℝ≥0∞) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hcard
  gcongr

end Transfer

section Packing

variable
  {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end Packing

section MultiplicityBound

variable
  {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- For any divisor `c > 0` and exponent `η > 0`, eventually
`exp(-δ^(-η)/c) ≤ 1/5` as `δ → 0⁺`. -/
private lemma absorb_exp_le_div_five {c η : ℝ} (hc : 0 < c) (hη : 0 < η) :
    ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), Real.exp (-δ ^ (-η) / c) ≤ 1/5 := by
  filter_upwards [absorb_const_le_rpow_neg
    (mul_pos hc (Real.log_pos (by norm_num : (1 : ℝ) < 5))) hη] with δ hδ
  rw [show (-δ ^ (-η) / c : ℝ) = -(δ ^ (-η) / c) from by ring]
  refine (Real.exp_le_exp.mpr (show -(δ ^ (-η) / c) ≤ -Real.log 5 by
    rw [neg_le_neg_iff, le_div_iff₀ hc]; linarith)).trans ?_
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 5)]
  norm_num

/-- Eventually `2^β ≤ δ^(-ε)` as `δ → 0⁺`, for any `β : ℝ` and `ε > 0`. -/
private lemma absorb_two_rpow_le_rpow_neg (β : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), (2 : ℝ) ^ β ≤ δ ^ (-ε) :=
  absorb_const_le_rpow_neg (Real.rpow_pos_of_pos two_pos β) hε

/-- Eventually `4 * K^4 ≤ δ^(-η)` as `δ → 0⁺`, for `K, η > 0`. -/
private lemma absorb_four_K4_le_rpow_neg {K η : ℝ} (_hK : 0 < K) (hη : 0 < η) :
    ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), 4 * K ^ 4 ≤ δ ^ (-η) :=
  absorb_const_le_rpow_neg (by positivity) hη

/-- Eventually `exp(-δ^(η/2 - 2η/2) / (8K^2)) ≤ 1/5` as `δ → 0⁺`. -/
private lemma absorb_exp_K_le_div_five {K η : ℝ} (_hK : 0 < K) (hη : 0 < η) :
    ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ),
      Real.exp (-δ ^ (η / 2 - 2 * η / 2) / (8 * K ^ 2)) ≤ 1/5 := by
  filter_upwards [absorb_exp_le_div_five (by positivity : (0 : ℝ) < 8 * K^2)
    (half_pos hη)] with δ hδ
  rwa [show (η / 2 - 2 * η / 2 : ℝ) = -(η / 2) from by ring]

/-- Eventually `δ ≤ 1/5` as `δ → 0⁺`. -/
private lemma absorb_delta_le_div_five :
    ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), δ ≤ 1/5 := by
  apply Filter.eventually_of_mem (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1/5))
  intro δ hδ
  simp only [Set.mem_Ioo] at hδ
  linarith [hδ.2]

/-- The lower volume bound for a `δ`-tube, in `ℝ`-valued (`volume.real`) form.
-/
private lemma tube_le_volume_real {δ : ℝ≥0} (T : ShadedTube δ E) :
    (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) * (δ : ℝ) ^ (Module.finrank ℝ E - 1) ≤
      volume.real T.carrier := by
  have hreal := ENNReal.toReal_mono T.isCompact'.measure_lt_top.ne (Tube.le_volume T.toTube)
  simpa [MeasureTheory.Measure.real, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.coe_toReal] using hreal

/-- **The ω-form of [GWZ, Lemma 3.7]**: `K_KT(β, ω)` implies a multiplicity bound for families of
`δ`-tubes at any value of `Δ_max(𝕋)`.

This is `Kakeya.KatzTaoEstimate.multiplicity_bound` verbatim with the accuracy factor `δ^{-ε}` of
the conclusion replaced by `δ^{-ω-ε}`, and it is proved by that lemma's proof with the same
replacement.  The budget rides through the passage to a random subfamily
(`Kakeya.exists_random_subset`) as a scalar and changes no step of it: the assertion is read at
accuracy `ε/4`, returning `δ^{-ω-ε/4}` in place of `δ^{-ε/4}`, and the three subsequent absorptions
— the factor `2^β`, the refinement loss `δ^{-2η_K}` and the density factor — are each free of `ω`.
The final exponent comparison is `2η_K + ω + ε/2 ≤ ω + ε`, in which `ω` cancels, so it is the same
comparison `2η_K ≤ ε/2` that the `ω = 0` proof makes; in particular no sign hypothesis on `ω` is
needed.

The scale charged is the single scale `δ`, the family's own thickness.  Charging it elsewhere is
what `note:ml2redOmegaFailureMode` prices; the own-scale discipline of the window branch is arranged
by the consumers in `Kakeya/DimensionThree/MainLemma2/Reduction/OmegaInputs.lean`, which read this
lemma at the leaf scale rather than at the configuration scale. -/
theorem KatzTaoEstimateOmega.multiplicity_bound {β ω : ℝ} (hβ_0 : 0 ≤ β)
    (h : KatzTaoEstimateOmega.{u} E β ω) :
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E),
        (∀ i, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) : ℝ) ≥ (δ : ℝ) ^ η →
        multiplicity s (fun i ↦ (T i).toShadedBody) ≤
          (δ : ℝ≥0∞) ^ (-ω - ε) *
            (maxDensity s (fun i ↦ (T i).toConvexSpaceBody)) ^ (1 - β) *
            (s.card : ℝ≥0∞) ^ β := by
  intro ε hε
  obtain ⟨η1, hη1_pos, hKKT⟩ := h (ε / 4) (by linarith)
  set η_K := min (η1 / 2) (ε / 8) with hη_K_def
  have hη_K_pos : 0 < η_K := lt_min (half_pos hη1_pos) (by linarith)
  refine ⟨η_K / 2, half_pos hη_K_pos, ?_⟩
  set c_low : ℝ := (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) with hc_low_def
  have hc_low_pos : 0 < c_low := NNReal.coe_pos.mpr (Tube.le_volume.c_pos _)
  set c_up : ℝ := (Tube.volume_le.C (Module.finrank ℝ E) : ℝ) with hc_up_def
  set K_unif : ℝ := c_up / c_low with hK_unif_def
  have hK_unif_pos : 0 < K_unif := div_pos (NNReal.coe_pos.mpr (Tube.volume_le.C_pos _)) hc_low_pos
  haveI : ProperSpace E := FiniteDimensional.proper ℝ E
  -- Density test family constants: the discretization constants of
  -- `exists_localized_finite_test_family_maxDensity` at radius `R = 1`. The exponent is padded by
  -- `+1` so that the multiplicative constant `Ctest` can be absorbed into `δ ^ (-Mtest)` for
  -- small `δ` (the `hδ_lt_invCtest` conjunct below).
  set Ctest : ℝ := (exists_volume_bounded_prism_discretization.C (Module.finrank ℝ E) : ℝ)
    with hCtest_def
  set Mtest : ℝ := exists_volume_bounded_prism_discretization.M (Module.finrank ℝ E) + 1
    with hMtest_def
  have hCtest_pos : 0 < Ctest :=
    NNReal.coe_pos.mpr (exists_volume_bounded_prism_discretization.C_pos _)
  have hMtest_pos : 0 < Mtest := by
    rw [hMtest_def]
    linarith [exists_volume_bounded_prism_discretization.M_pos (Module.finrank ℝ E)]
  filter_upwards [hKKT,
      (nnreal_eventually_of_real_eventually (p := fun δ => δ < 1)
        (nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one))),
      (nnreal_eventually_of_real_eventually (p := fun δ => 0 < δ)
        (self_mem_nhdsWithin : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ)),
      nnreal_eventually_of_real_eventually
        (absorb_two_rpow_le_rpow_neg β (ε := ε / 4) (by linarith)),
      nnreal_eventually_of_real_eventually
        (absorb_four_K4_le_rpow_neg (K := K_unif) (η := η_K / 2) hK_unif_pos (half_pos hη_K_pos)),
      nnreal_eventually_of_real_eventually
        (absorb_log_le_rpow_neg (C := Ctest) (M := 8 * Mtest + 8) (η := η_K)
          hCtest_pos (by linarith) hη_K_pos),
      nnreal_eventually_of_real_eventually
        (absorb_exp_K_le_div_five (K := K_unif) (η := η_K) hK_unif_pos hη_K_pos),
      nnreal_eventually_of_real_eventually absorb_delta_le_div_five,
      nnreal_eventually_of_real_eventually (p := fun δ => δ < 1 / Ctest)
        (nhdsWithin_le_nhds (Iio_mem_nhds (one_div_pos.mpr hCtest_pos)))]
    with δNN hδ_KKT hδ_lt_one hδ_pos h_2β_le hδ_small_K hδ_small_b
         hδ5_c hδ5_b hδ_lt_invCtest
  set δ : ℝ := (δNN : ℝ) with hδ_def
  have hδNN_pos : (0 : ℝ≥0) < δNN := by exact_mod_cast hδ_pos
  intro ι s T hB hfull
  set W := fun i ↦ (T i).toConvexSpaceBody with hW
  set V := fun i ↦ (T i).toShadedBody with hV
  set Δ : ℝ := (maxDensity s W).toReal with hΔ_def
  have hT_vol_lb_real : ∀ i,
      c_low * δ ^ (Module.finrank ℝ E - 1) ≤ volume.real (T i).carrier :=
    fun i => tube_le_volume_real (T i)
  rcases eq_or_ne s ∅ with rfl | hs
  · simp only [ShadedBody.multiplicity_empty]
    exact bot_le
  · obtain ⟨i₀, hi₀⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    have hvol_pos : 0 < volume (W i₀).carrier :=
      (ENNReal.toReal_pos_iff.mp (lt_of_lt_of_le
        (mul_pos hc_low_pos (pow_pos hδ_pos _)) (hT_vol_lb_real i₀))).1
    have hΔ_pos : 0 < Δ :=
      ENNReal.toReal_pos
        (zero_lt_one.trans_le (one_le_maxDensity ⟨i₀, hi₀, hvol_pos⟩)).ne'
        (maxDensity_ne_top s W)
    have hT_unif : ∀ i ∈ s, ∀ j ∈ s,
        volume.real (T i).carrier ≤ K_unif * volume.real (T j).carrier := fun i _ j _ =>
      calc volume.real (T i).carrier
          ≤ c_up * δ ^ (Module.finrank ℝ E - 1) :=
            by
              have hRHS_fin :
                  (Tube.volume_le.C (Module.finrank ℝ E) : ℝ≥0∞) *
                      (δNN : ℝ≥0∞) ^ (Module.finrank ℝ E - 1) ≠ ⊤ :=
                ENNReal.mul_ne_top ENNReal.coe_ne_top
                  (ENNReal.pow_ne_top ENNReal.coe_ne_top)
              have hreal := ENNReal.toReal_mono hRHS_fin
                (Tube.volume_le (by exact_mod_cast hδ_lt_one.le) (T i).toTube)
              simpa [MeasureTheory.Measure.real, hc_up_def, hδ_def,
                ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal] using hreal
        _ = K_unif * (c_low * δ ^ (Module.finrank ℝ E - 1)) := by
              rw [hK_unif_def, ← mul_assoc, div_mul_cancel₀ _ hc_low_pos.ne']
        _ ≤ K_unif * volume.real (T j).carrier :=
              mul_le_mul_of_nonneg_left (hT_vol_lb_real j) hK_unif_pos.le
    have htest_real : ∃ KTest : Finset (ConvexSpaceBody E),
        (∀ K ∈ KTest, K ≤ ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall (E := E))) ∧
        (KTest.card : ℝ) ≤ (δ : ℝ) ^ (-Mtest) ∧ ∀ u : Finset ι, u ⊆ s →
        ∃ K ∈ KTest, (maxDensity u (fun i ↦ (T i).toConvexSpaceBody)).toReal ≤
        Ctest * (densityIn u (fun i ↦ (T i).toConvexSpaceBody) K).toReal := by
      obtain ⟨KTest, hKT_sub, hKT_card, hKT_test⟩ :=
        exists_localized_finite_test_family_maxDensity.{u, _} (E := E) (r := δNN) (R := 1)
          hδNN_pos (by exact_mod_cast hδ_lt_one.le) le_rfl
      refine ⟨KTest, ?_, ?_, fun u _hu => ?_⟩
      · -- The test bodies sit in `B(0,1)`, hence a fortiori in its unit thickening.
        intro K hK x hx
        exact Metric.self_subset_cthickening _
          (by simpa only [NNReal.coe_one, ConvexSpaceBody.closedUnitBall_carrier]
            using hKT_sub K hK hx)
      · -- Absorb the multiplicative constant `Ctest` into the padded exponent `Mtest = M + 1`.
        set M : ℝ := exists_volume_bounded_prism_discretization.M (Module.finrank ℝ E) with hM_def
        have hcard_real : (KTest.card : ℝ) ≤ Ctest * δ ^ (-M) := by
          rw [NNReal.one_rpow, mul_one] at hKT_card
          rw [hCtest_def, hδ_def]
          exact_mod_cast hKT_card
        have hCtest_le : Ctest ≤ δ ^ (-1 : ℝ) := by
          rw [Real.rpow_neg_one, inv_eq_one_div, le_div_iff₀ hδ_pos]
          calc Ctest * δ = δ * Ctest := mul_comm _ _
            _ ≤ 1 := ((lt_div_iff₀ hCtest_pos).mp hδ_lt_invCtest).le
        have hsplit : δ ^ (-Mtest) = δ ^ (-M) * δ ^ (-1 : ℝ) := by
          rw [← Real.rpow_add hδ_pos, hMtest_def]
          congr 1
          ring
        calc (KTest.card : ℝ) ≤ Ctest * δ ^ (-M) := hcard_real
          _ ≤ δ ^ (-1 : ℝ) * δ ^ (-M) :=
              mul_le_mul_of_nonneg_right hCtest_le (Real.rpow_nonneg hδ_pos.le _)
          _ = δ ^ (-M) * δ ^ (-1 : ℝ) := mul_comm _ _
          _ = δ ^ (-Mtest) := hsplit.symm
      · obtain ⟨K, hK_mem, hK_le⟩ :=
          hKT_test u (fun i ↦ (T i).toConvexSpaceBody)
            (fun i _ => by simpa only [NNReal.coe_one] using hB i)
            (fun i _ => by
              rw [Metric.ethickness.scale_eq]
              exact (T i).toTube.le_ethickness_finrank_sub_one)
        refine ⟨K, hK_mem, ?_⟩
        have h_ennr := ENNReal.toReal_mono
          (ENNReal.mul_ne_top ENNReal.coe_ne_top (densityIn_ne_top _ _ _)) hK_le
        rwa [ENNReal.toReal_mul, ENNReal.coe_toReal, ← hCtest_def] at h_ennr
    obtain ⟨s', hs'_sub, hs'_ne, hs'_card_ub, hs'_KT, hs'_full, hs'_mu⟩ :=
        exists_random_subset E (η₁ := η_K / 2) (c := 2 * η_K) (half_pos hη_K_pos)
          (by linarith) s T hB (Finset.nonempty_iff_ne_empty.mpr hs) hδ_pos
          K_unif hK_unif_pos hT_unif hδ_small_K
          Mtest Ctest hMtest_pos hCtest_pos htest_real
          hδ_small_b hδ5_c hδ5_b hfull
    have hηK_le_half : η_K ≤ η1 / 2 := min_le_left _ _
    have hs'_KT' : IsKatzTao s' W ((δNN : ℝ≥0∞) ^ (-η1)) :=
      hs'_KT.mono <| by
        rw [ennreal_coe_nnreal_rpow hδ_pos]
        exact ENNReal.ofReal_le_ofReal
          (Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le (by linarith))
    have hs'_full' : (δNN : ℝ≥0) ^ η1 ≤ ShadedBody.fullness s' V := by
      rw [← NNReal.coe_le_coe, NNReal.coe_rpow]
      calc (δ : ℝ) ^ η1
          ≤ (δ : ℝ) ^ η_K := Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le
            (by linarith [hη_K_pos])
        _ = (δ : ℝ) ^ (2 * (η_K / 2)) := by congr 1; ring
        _ ≤ _ := hs'_full
    -- ENNReal multiplicity bound for `s'`, obtained from `hδ_KKT`.
    have hmu_s'_le_enn : ShadedBody.multiplicity s' V ≤
        (δNN : ℝ≥0∞) ^ (-ω - ε / 4) * (s'.card : ℝ≥0∞) ^ β := by
      rw [ShadedBody.multiplicity_le_iff, mul_assoc]
      have : ∀ i ∈ s', (T i).carrier ⊆ Metric.closedBall 0 1 := fun i hi => hB i
      exact (hδ_KKT s' T this hs'_KT' hs'_full').trans_eq (mul_assoc _ _ _)
    -- The ℝ-valued multiplicity bound for `s'` (derived by `.toReal`).
    have h_mu_s'_R_le : multiplicityRLocal E s' V ≤
        δ ^ (-ω - ε / 4) * (s'.card : ℝ) ^ β := by
      have h_top : (δNN : ℝ≥0∞) ^ (-ω - ε / 4) * (s'.card : ℝ≥0∞) ^ β ≠ ⊤ :=
        ENNReal.mul_ne_top (by rw [ennreal_coe_nnreal_rpow hδ_pos]; exact ENNReal.ofReal_ne_top)
          (ENNReal.rpow_ne_top_of_nonneg hβ_0 (ENNReal.natCast_ne_top _))
      simpa [multiplicityRLocal, ENNReal.toReal_mul, ennreal_coe_nnreal_rpow_toReal hδ_pos,
        ← ENNReal.toReal_rpow] using ENNReal.toReal_mono h_top hmu_s'_le_enn
    have h_mu_s_R_le : multiplicityRLocal E s V ≤
        δ ^ (-ω - ε) * Δ ^ (1 - β) * (s.card : ℝ) ^ β := by
      calc multiplicityRLocal E s V
        _ ≤ δ ^ (-(2 * η_K)) * Δ * multiplicityRLocal E s' V := hs'_mu
        _ ≤ δ ^ (-(2 * η_K)) * Δ * (δ ^ (-ω - ε / 4) * (s'.card : ℝ) ^ β) :=
              mul_le_mul_of_nonneg_left
                h_mu_s'_R_le
                (mul_nonneg (Real.rpow_nonneg hδ_pos.le _) ENNReal.toReal_nonneg)
        _ ≤ δ ^ (-(2 * η_K)) * Δ * (δ ^ (-ω - ε / 4) * (2 * (s.card : ℝ) * Δ⁻¹) ^ β) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow (Nat.cast_nonneg _) hs'_card_ub hβ_0)
                (Real.rpow_nonneg hδ_pos.le _))
              (mul_nonneg (Real.rpow_nonneg hδ_pos.le _) ENNReal.toReal_nonneg)
        _ ≤ δ ^ (-(2 * η_K)) * Δ * (δ ^ (-ω - ε / 2) * ((s.card : ℝ) * Δ⁻¹) ^ β) := by
              apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Real.rpow_nonneg hδ_pos.le _)
                ENNReal.toReal_nonneg)
              rw [show (2 : ℝ) * s.card * Δ⁻¹ = (2 : ℝ) * (s.card * Δ⁻¹) from by ring,
                  Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2)
                (mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.mpr ENNReal.toReal_nonneg)),
                show δ ^ (-ω - ε / 4) * ((2 : ℝ) ^ β * (s.card * Δ⁻¹) ^ β)
                  = (δ ^ (-ω - ε / 4) * (2 : ℝ) ^ β) * (s.card * Δ⁻¹) ^ β from by ring]
              exact mul_le_mul_of_nonneg_right
                (calc δ ^ (-ω - ε / 4) * (2 : ℝ) ^ β
                    ≤ δ ^ (-ω - ε / 4) * δ ^ (-(ε / 4)) :=
                      mul_le_mul_of_nonneg_left h_2β_le (Real.rpow_nonneg hδ_pos.le _)
                  _ = δ ^ (-ω - ε / 2) := by rw [← Real.rpow_add hδ_pos]; congr 1; ring)
                (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg _)
                  (inv_nonneg.mpr ENNReal.toReal_nonneg)) _)
        _ = δ ^ (-(2 * η_K + ω + ε / 2)) * Δ ^ (1 - β) * (s.card : ℝ) ^ β := by
              rw [Real.mul_rpow (Nat.cast_nonneg _) (inv_nonneg.mpr ENNReal.toReal_nonneg),
              show (Δ⁻¹ : ℝ) ^ β = Δ ^ (-β) from by rw [Real.inv_rpow ENNReal.toReal_nonneg,
                  ← Real.rpow_neg ENNReal.toReal_nonneg],
              show δ ^ (-(2 * η_K)) * Δ * (δ ^ (-ω - ε / 2) * ((s.card) ^ β * Δ ^ (-β)))
                      = (δ ^ (-(2 * η_K)) * δ ^ (-ω - ε / 2)) * (Δ * Δ ^ (-β)) * (s.card) ^ β
                      from by ring,
               ← Real.rpow_add hδ_pos,
               show -(2 * η_K) + (-ω - ε / 2) = -(2 * η_K + ω + ε / 2) from by ring,
              show Δ * Δ ^ (-β) = Δ ^ (1 : ℝ) * Δ ^ (-β) from by rw [Real.rpow_one],
                ← Real.rpow_add hΔ_pos, show (1 : ℝ) + -β = 1 - β from by ring]
        _ ≤ δ ^ (-ω - ε) * Δ ^ (1 - β) * (s.card : ℝ) ^ β := by
              apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
              apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ENNReal.toReal_nonneg _)
              exact Real.rpow_le_rpow_of_exponent_ge hδ_pos (le_of_lt hδ_lt_one)
                (by linarith [min_le_right (η1 / 2) (ε / 8)])
    -- Lift the real-valued bound to ENNReal and match the goal.
    have h_mu_ne_top : ShadedBody.multiplicity s V ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) (ShadedBody.multiplicity_le_card s V)
    refine ((ENNReal.le_ofReal_iff_toReal_le h_mu_ne_top
      (mul_nonneg (mul_nonneg (Real.rpow_nonneg hδ_pos.le _)
        (Real.rpow_nonneg ENNReal.toReal_nonneg _))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))).2 h_mu_s_R_le).trans ?_
    have h_card_eq : ENNReal.ofReal ((s.card : ℝ) ^ β) = (s.card : ℝ≥0∞) ^ β := by
      rw [show ((s.card : ℝ) ^ β : ℝ) = ((s.card : ℝ≥0∞) ^ β).toReal from by
            rw [← ENNReal.toReal_rpow]; simp,
          ENNReal.ofReal_toReal (ENNReal.rpow_ne_top_of_nonneg hβ_0 (ENNReal.natCast_ne_top _))]
    rw [show (δ ^ (-ω - ε) * Δ ^ (1 - β) * (s.card : ℝ) ^ β : ℝ)
          = δ ^ (-ω - ε) * (Δ ^ (1 - β) * (s.card : ℝ) ^ β) from by ring,
        ENNReal.ofReal_mul (Real.rpow_nonneg hδ_pos.le _),
        ENNReal.ofReal_mul (Real.rpow_nonneg ENNReal.toReal_nonneg _),
        ← ennreal_coe_nnreal_rpow hδ_pos,
        show ENNReal.ofReal (Δ ^ (1 - β)) = (maxDensity s W) ^ (1 - β) from by
          rw [← ENNReal.ofReal_rpow_of_pos hΔ_pos, hΔ_def,
              ENNReal.ofReal_toReal (maxDensity_ne_top s W)],
        h_card_eq, mul_assoc]

end MultiplicityBound

section Bootstrap

end Bootstrap

section Assembly

end Assembly

end Kakeya

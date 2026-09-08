/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceWeightedBiasedFactoring
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSiteClosure

/-! # The actual biased-factor loss at a polynomially controlled normalized scale -/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric ConvexSpaceBody

namespace Kakeya.ML2Assembly

universe u v w x y

/-- Fixed data chosen before the runtime scale and all parent families. -/
structure SourceBiasedLossParameters where
  bias : ℝ
  bias_pos : 0 < bias
  cardCoefficient : ℝ≥0
  cardCoefficient_one_le : 1 <= cardCoefficient
  thicknessCoefficient : ℝ≥0
  thicknessCoefficient_pos : 0 < thicknessCoefficient
  thicknessCoefficient_le_one : thicknessCoefficient <= 1
  cardPower : ℝ≥0
  thicknessPower : ℝ≥0

/-- The geometric caller's exact polynomial cardinality and thickness bounds. -/
structure SourceBiasedPolynomialScale (P : SourceBiasedLossParameters)
    (delta : ℝ≥0) (card : Nat) (d : ℝ≥0) : Prop where
  delta_pos : 0 < delta
  delta_le_one : delta <= 1
  card_pos : 0 < card
  card_le : (card : ℝ) <= (P.cardCoefficient : ℝ) *
    (delta : ℝ) ^ (-(P.cardPower : ℝ))
  thickness_pos : 0 < d
  thickness_le_one : d <= 1
  thickness_ge : (P.thicknessCoefficient : ℝ) *
    (delta : ℝ) ^ (P.thicknessPower : ℝ) <= (d : ℝ)

/-- E1: the exact API loss has fixed logarithmic degree `n + 1`. -/
theorem sourceBiased_exists_loss_coefficient (n : Nat) (P : SourceBiasedLossParameters) :
    exists C : ℝ≥0, 1 <= C ∧
      forall (delta d : ℝ≥0) (card : Nat), SourceBiasedPolynomialScale P delta card d ->
        nonempty_biasedFactorization.L n card d P.bias <=
          (C : ℝ≥0∞) * Kakeya.ML2Core.polylogLoss (n + 1) delta := by
  let l2 : ℝ := Real.log 2
  let A : ℝ := (Real.log (P.cardCoefficient : ℝ) + P.bias *
    ((n : ℝ) * l2 - Real.log (Metric.lt_volume_convexHull.c n : ℝ) -
      (n : ℝ) * Real.log (P.thicknessCoefficient : ℝ))) / l2
  let B : ℝ := ((P.cardPower : ℝ) + P.bias * n * (P.thicknessPower : ℝ)) / l2
  let C1 : ℝ := 1 + |A| + |B|
  let C2 : ℝ := 1 + |Real.log (P.thicknessCoefficient : ℝ) / l2| +
    |(P.thicknessPower : ℝ) / l2|
  have hC1 : 1 <= C1 := by dsimp only [C1]; linarith [abs_nonneg A, abs_nonneg B]
  have hC2 : 1 <= C2 := by
    dsimp only [C2]
    linarith [abs_nonneg (Real.log (P.thicknessCoefficient : ℝ) / l2),
      abs_nonneg ((P.thicknessPower : ℝ) / l2)]
  have hcoef : 1 <= C1 * C2 ^ n := one_le_mul_of_one_le_of_one_le hC1 (one_le_pow₀ hC2)
  refine ⟨Real.toNNReal (C1 * C2 ^ n), ?_, ?_⟩
  · rw [← Real.toNNReal_one]
    exact Real.toNNReal_le_toNNReal hcoef
  intro delta d card hs
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hs.thickness_pos
  have hdelta0 : (0 : ℝ) < delta := by exact_mod_cast hs.delta_pos
  have hcard0 : (0 : ℝ) < card := by exact_mod_cast hs.card_pos
  have hc0 : (0 : ℝ) < P.cardCoefficient := by
    exact_mod_cast (zero_lt_one.trans_le P.cardCoefficient_one_le)
  have ht0 : (0 : ℝ) < P.thicknessCoefficient := by exact_mod_cast P.thicknessCoefficient_pos
  have hv0 : (0 : ℝ) < Metric.lt_volume_convexHull.c n := by
    exact_mod_cast Metric.lt_volume_convexHull.c_pos n
  have hl20 : 0 < l2 := Real.log_pos (by norm_num)
  have hlogdelta : Real.log (delta : ℝ) <= 0 :=
    Real.log_nonpos hdelta0.le (by exact_mod_cast hs.delta_le_one)
  let X : ℝ := 1 - Real.log (delta : ℝ)
  have hX : 1 <= X := by dsimp [X]; linarith
  have hlogcard : Real.log (card : ℝ) <= Real.log (P.cardCoefficient : ℝ) -
      (P.cardPower : ℝ) * Real.log (delta : ℝ) := by
    have hh := Real.log_le_log hcard0 hs.card_le
    rw [Real.log_mul hc0.ne' (Real.rpow_pos_of_pos hdelta0 _).ne', Real.log_rpow hdelta0] at hh
    simpa [sub_eq_add_neg] using hh
  have hlogd : Real.log (P.thicknessCoefficient : ℝ) +
      (P.thicknessPower : ℝ) * Real.log (delta : ℝ) <= Real.log (d : ℝ) := by
    have hh := Real.log_le_log (mul_pos ht0 (Real.rpow_pos_of_pos hdelta0 _)) hs.thickness_ge
    rwa [Real.log_mul ht0.ne' (Real.rpow_pos_of_pos hdelta0 _).ne', Real.log_rpow hdelta0] at hh
  have hfirst : 1 + Real.logb 2 ((card : ℝ) *
      ((2 : ℝ) ^ n / ((Metric.lt_volume_convexHull.c n : ℝ) * (d : ℝ) ^ n)) ^ P.bias)
      <= C1 * X := by
    have hn : (0 : ℝ) <= n := Nat.cast_nonneg n
    have hh : Real.log (card : ℝ) + P.bias *
        ((n : ℝ) * l2 - (Real.log (Metric.lt_volume_convexHull.c n : ℝ) +
          (n : ℝ) * Real.log (d : ℝ))) <= A * l2 - B * l2 * Real.log (delta : ℝ) := by
      have hscale := mul_le_mul_of_nonneg_left hlogd (mul_nonneg P.bias_pos.le hn)
      dsimp [A, B]
      field_simp [hl20.ne']
      nlinarith
    have hlog : Real.logb 2 ((card : ℝ) *
        ((2 : ℝ) ^ n / ((Metric.lt_volume_convexHull.c n : ℝ) * (d : ℝ) ^ n)) ^ P.bias)
        <= A + B * (-Real.log (delta : ℝ)) := by
      rw [Real.logb, Real.log_mul hcard0.ne' (Real.rpow_pos_of_pos (by positivity) _).ne',
        Real.log_rpow (by positivity), Real.log_div (by positivity) (by positivity),
        Real.log_mul hv0.ne' (pow_pos hd0 n).ne', Real.log_pow, Real.log_pow]
      apply (div_le_iff₀ hl20).2
      dsimp [l2] at hh ⊢
      nlinarith
    have habsA := le_abs_self A
    have habsB := le_abs_self B
    have hhB := mul_le_mul_of_nonneg_right habsB (neg_nonneg.mpr hlogdelta)
    calc
      _ <= 1 + |A| + |B| * (-Real.log (delta : ℝ)) := by linarith only [hlog, habsA, hhB]
      _ <= C1 * X := by
        dsimp only [C1, X]
        nlinarith only [hlogdelta, abs_nonneg B,
          mul_nonneg (abs_nonneg A) (neg_nonneg.mpr hlogdelta)]
  have hsecond : 1 + Real.logb 2 (1 / (d : ℝ)) <= C2 * X := by
    have hh : Real.logb 2 (1 / (d : ℝ)) <=
        -(Real.log (P.thicknessCoefficient : ℝ) / l2) +
          ((P.thicknessPower : ℝ) / l2) * (-Real.log (delta : ℝ)) := by
      rw [Real.logb, one_div, Real.log_inv]
      apply (div_le_iff₀ hl20).2
      dsimp [l2]
      field_simp [hl20.ne']
      linarith
    have hca := neg_le_abs (Real.log (P.thicknessCoefficient : ℝ) / l2)
    have hcb := mul_le_mul_of_nonneg_right (le_abs_self ((P.thicknessPower : ℝ) / l2))
      (neg_nonneg.mpr hlogdelta)
    dsimp [C2, X]
    nlinarith [abs_nonneg (Real.log (P.thicknessCoefficient : ℝ) / l2),
      abs_nonneg ((P.thicknessPower : ℝ) / l2),
      mul_nonneg (abs_nonneg (Real.log (P.thicknessCoefficient : ℝ) / l2))
        (neg_nonneg.mpr hlogdelta)]
  have hX0 : 0 <= X := zero_le_one.trans hX
  calc
    nonempty_biasedFactorization.L n card d P.bias <=
        ENNReal.ofReal (C1 * X) * ENNReal.ofReal (C2 * X) ^ n := by
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal hfirst)
        (pow_le_pow_left' (ENNReal.ofReal_le_ofReal hsecond) n)
    _ = ENNReal.ofReal (C1 * C2 ^ n) * ENNReal.ofReal (X ^ (n + 1)) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hX0,
        ENNReal.ofReal_pow (by positivity), mul_pow, pow_succ]
      ring
    _ <= _ := by
      have hp : ENNReal.ofReal (X ^ (n + 1)) <= Kakeya.ML2Core.polylogLoss (n + 1) delta :=
        ENNReal.ofReal_le_ofReal (le_max_right _ _)
      exact mul_le_mul' (le_refl (ENNReal.ofReal (C1 * C2 ^ n))) hp

/-- E2: one further fixed logarithmic power absorbs that coefficient at a positive threshold. -/
theorem sourceBiased_exists_polylog_threshold (n : Nat) (P : SourceBiasedLossParameters) :
    exists delta0 : ℝ≥0, 0 < delta0 ∧ delta0 <= 1 ∧
      forall (delta d : ℝ≥0) (card : Nat), delta < delta0 ->
        SourceBiasedPolynomialScale P delta card d ->
        1 <= nonempty_biasedFactorization.L n card d P.bias ∧
        nonempty_biasedFactorization.L n card d P.bias < ⊤ ∧
        nonempty_biasedFactorization.L n card d P.bias <=
          Kakeya.ML2Core.polylogLoss (n + 2) delta := by
  obtain ⟨C, hC, hbound⟩ := sourceBiased_exists_loss_coefficient n P
  let delta0 : ℝ≥0 := Real.toNNReal (Real.exp (-(C : ℝ)))
  have hzero : 0 < delta0 := Real.toNNReal_pos.mpr (Real.exp_pos _)
  have hone : delta0 <= 1 := by
    apply Real.toNNReal_le_one.mpr
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr C.coe_nonneg)
  refine ⟨delta0, hzero, hone, ?_⟩
  intro delta d card hsmall hs
  refine ⟨nonempty_biasedFactorization.one_le_L hs.thickness_pos hs.thickness_le_one
    P.bias_pos hs.card_pos, nonempty_biasedFactorization.L_lt_top, (hbound delta d card hs).trans ?_⟩
  have hdelta : (0 : ℝ) < delta := by exact_mod_cast hs.delta_pos
  have hdexp : (delta : ℝ) <= Real.exp (-(C : ℝ)) := by
    have hh : (delta : ℝ) < (delta0 : ℝ) := by exact_mod_cast hsmall
    simpa [delta0, Real.toNNReal_of_nonneg (Real.exp_pos _).le] using hh.le
  have hlog := Real.log_le_log hdelta hdexp
  rw [Real.log_exp] at hlog
  have hX : (C : ℝ) <= 1 - Real.log (delta : ℝ) := by linarith
  have hX0 : 0 <= 1 - Real.log (delta : ℝ) := C.coe_nonneg.trans hX
  have heq (k : Nat) : Kakeya.ML2Core.polylogLoss k delta =
      ENNReal.ofReal ((1 - Real.log (delta : ℝ)) ^ k) := by
    rw [Kakeya.ML2Core.polylogLoss, max_eq_right (Kakeya.ML2Core.one_le_polylog hs.delta_le_one k)]
  rw [heq, heq]
  calc (C : ℝ≥0∞) * ENNReal.ofReal ((1 - Real.log (delta : ℝ)) ^ (n + 1)) <=
      ENNReal.ofReal (1 - Real.log (delta : ℝ)) *
        ENNReal.ofReal ((1 - Real.log (delta : ℝ)) ^ (n + 1)) := by
        apply mul_le_mul_left
        simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hX
    _ = ENNReal.ofReal ((1 - Real.log (delta : ℝ)) ^ (n + 2)) := by
      rw [show n + 2 = (n + 1) + 1 by omega,
        pow_succ (1 - Real.log (delta : ℝ)) (n + 1),
        ENNReal.ofReal_mul (pow_nonneg hX0 (n + 1))]
      exact mul_comm _ _

variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  {iota : Type u} [DecidableEq iota]
  {kappa : Type v} [DecidableEq kappa] {jota : Type x} [DecidableEq jota]

/-- The unchanged geometric inputs of B5, with no loss-bound field. -/
structure SourceBiasedParentGeometry
    (J : Finset jota) (F : jota -> Finset iota) (I : jota -> Finset kappa)
    (Z : iota -> ShadedBody E) (V : jota -> kappa -> ConvexSpaceBody E)
    (parent : jota -> ConvexSpaceBody E) (f : jota -> E ≃ᵃ[ℝ] E)
    (comparison d : jota -> ℝ≥0) : Prop where
  parents_nonempty : J.Nonempty
  parent_fibres_disjoint : (J : Set jota).PairwiseDisjoint F
  mass_pos : forall j, j ∈ J -> 0 < ∑ i ∈ F j, volume (Z i).shade
  thickness_pos : forall j, j ∈ J -> 0 < d j
  contained : forall j, j ∈ J -> forall i, i ∈ I j -> V j i <= parent j
  normalized_ball : forall j, j ∈ J -> (parent j).mapAffine (f j) <= closedUnitBall
  normalized_thickness : forall j, j ∈ J -> forall i, i ∈ I j ->
    (d j : ℝ≥0∞) <= ethickness.scale ℝ ((V j i).mapAffine (f j)).carrier
  comparison_one_le : forall j, j ∈ J -> 1 <= comparison j
  reference_comparison : forall j, j ∈ J ->
    volume (sourceAffineReference (f j)).carrier <=
      (comparison j : ℝ≥0∞) * volume (parent j).carrier

/-- B5's actual selections, full affine data and unchanged eight aggregate conclusions. -/
structure SourceBiasedParentAggregation
    (J : Finset jota) {F : jota -> Finset iota} {I : jota -> Finset kappa}
    (p : forall j, SourceDescendantPartition (F j) (I j))
    (Z : iota -> ShadedBody E) (V : jota -> kappa -> ConvexSpaceBody E)
    (parent : jota -> ConvexSpaceBody E) (f : jota -> E ≃ᵃ[ℝ] E)
    (comparison d : jota -> ℝ≥0) (bias : ℝ) (L0 : ℝ≥0∞) where
  data : (j : {j // j ∈ J}) -> SourceAffineWeightedParent (p j.val) Z (V j.val)
    (parent j.val) (f j.val) (comparison j.val) (d j.val) bias
  retained : Finset iota
  retained_eq : retained =
    J.attach.biUnion (fun j => sourceDescendantUnion (p j.val) (data j).selection.selected)
  retained_subset : retained ⊆ J.biUnion F
  retained_nonempty : retained.Nonempty
  exact_parent_inter : forall j : {j // j ∈ J}, retained ∩ F j.val =
    sourceDescendantUnion (p j.val) (data j).selection.selected
  retained_disjoint : ((J.attach : Set {j // j ∈ J}).PairwiseDisjoint
    (fun j => sourceDescendantUnion (p j.val) (data j).selection.selected))
  original_mass_eq : (∑ i ∈ J.biUnion F, volume (Z i).shade) =
    ∑ j ∈ J, ∑ i ∈ F j, volume (Z i).shade
  retained_mass_eq : (∑ i ∈ retained, volume (Z i).shade) =
    ∑ j ∈ J.attach, ∑ i ∈ sourceDescendantUnion (p j.val) (data j).selection.selected,
      volume (Z i).shade
  mass_loss : (∑ i ∈ J.biUnion F, volume (Z i).shade) <=
    L0 * ∑ i ∈ retained, volume (Z i).shade

omit [DecidableEq jota] in
/-- E4: positive mass, complete cells and the actual normalization give the scalar side conditions. -/
theorem sourceBiased_parent_polynomialScale
    (P : SourceBiasedLossParameters) {delta : ℝ≥0} (hdelta : 0 < delta)
    (hdelta1 : delta <= 1)
    (J : Finset jota) (F : jota -> Finset iota) (I : jota -> Finset kappa)
    (p : forall j, SourceDescendantPartition (F j) (I j))
    (Z : iota -> ShadedBody E) (V : jota -> kappa -> ConvexSpaceBody E)
    (parent : jota -> ConvexSpaceBody E) (f : jota -> E ≃ᵃ[ℝ] E)
    (comparison d : jota -> ℝ≥0)
    (hgeometry : SourceBiasedParentGeometry J F I Z V parent f comparison d)
    (hcard : forall j, j ∈ J -> ((I j).card : ℝ) <=
      (P.cardCoefficient : ℝ) * (delta : ℝ) ^ (-(P.cardPower : ℝ)))
    (hthickness : forall j, j ∈ J -> (P.thicknessCoefficient : ℝ) *
      (delta : ℝ) ^ (P.thicknessPower : ℝ) <= (d j : ℝ)) :
    forall j, j ∈ J -> SourceBiasedPolynomialScale P delta (I j).card (d j) := by
  intro j hj
  have hF : (F j).Nonempty := by
    by_contra hh
    have hpos := hgeometry.mass_pos j hj
    simp [Finset.not_nonempty_iff_eq_empty.mp hh] at hpos
  have hI : (I j).Nonempty := by
    by_contra hh
    have heq := (p j).union_eq
    simp [Finset.not_nonempty_iff_eq_empty.mp hh] at heq
    exact hF.ne_empty heq.symm
  obtain ⟨i, hi⟩ := hI
  have hball : ((V j i).mapAffine (f j)).carrier ⊆ Metric.closedBall (0 : E) 1 :=
    ((mapAffine_le_mapAffine_iff (f j)).mpr (hgeometry.contained j hj i hi)).trans
      (hgeometry.normalized_ball j hj)
  have hd1 : d j <= 1 := by
    have hn : 0 < Module.finrank ℝ E := Module.finrank_pos
    have hscale : ethickness.scale ℝ ((V j i).mapAffine (f j)).carrier <=
        ethickness ℝ ((V j i).mapAffine (f j)).carrier 0 :=
      Finset.inf_le (Finset.mem_range.mpr hn)
    have hh := ((hgeometry.normalized_thickness j hj i hi).trans hscale).trans
      (Metric.ethickness_le_of_subset_closedBall (𝕜 := ℝ) 1 hball 0)
    exact_mod_cast hh
  exact ⟨hdelta, hdelta1, Finset.card_pos.mpr ⟨i, hi⟩, hcard j hj,
    hgeometry.thickness_pos j hj, hd1, hthickness j hj⟩

end Kakeya.ML2Assembly

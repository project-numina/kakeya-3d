/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceDirectWindowData

/-!
# Ordinary cell stages and their literal fragments

Geometry of the ordinary (non-eccentric) B5 stage.
`Kakeya.ML2Core.SourceDirectCommonWindowNormalization` and
`source_direct_common_window_normalization` give the common affine normalization;
`SourceDirectOrdinaryCellStage` and `source_direct_exists_ordinary_cell_stage` build one
immediate stage on the after-family.  The fragment part defines `sourceOrdinaryUsedParts` and
`sourceOrdinaryFragmentParts` (literal intersections of new and old parts), proves they partition
(`source_ordinary_fragment_partition`), establishes their quantitative geometry
(`SourceOrdinaryFragmentGeometry`, `source_ordinary_fragment_geometry`), transports the
factorization (`source_ordinary_fragment_factorization`) with constant
`sourceOrdinaryFragmentConstant`, and bounds that constant by `sourceParentPlankConstant`
(`source_direct_ordinary_fragment_budget`).
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

universe u

variable {iota : Type u} {delta : ℝ≥0} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace ℝ (Fin 3))} {M C : Nat}

/-- Actual common affine normalization, including identities absent from the
older existential interface. All geometry is attached to the same maps. -/
structure SourceDirectCommonWindowNormalization
    (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3)))
    (a m : Nat) (P : ML2Assembly.SourceBiasedLossParameters) where
  partition : forall j, ML2Assembly.SourceDescendantPartition (Q.cell a j) (Q.fibre a m j)
  normalization : iota -> EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)
  comparison : iota -> ℝ≥0
  thickness : iota -> ℝ≥0
  assign_eq : forall j, (partition j).assign = Q.place m
  common_map : forall j, (normalization j : EuclideanSpace ℝ (Fin 3) ->
    EuclideanSpace ℝ (Fin 3)) = AffineMap.homothety 0 (3 : ℝ)⁻¹
  thickness_eq : forall j, thickness j = delta / 3
  geometry : ML2Assembly.SourceBiasedParentGeometry
    (Q.indexSet a) (Q.cell a) (Q.fibre a m)
    (fun i => (Z i).toShadedBody) (fun _ i => (Q.tube m i).toConvexSpaceBody)
    (fun j => (Q.tube a j).toConvexSpaceBody) normalization comparison thickness
  polynomial : forall j, j ∈ Q.indexSet a ->
    ML2Assembly.SourceBiasedPolynomialScale P delta (Q.fibre a m j).card (thickness j)

/-- Additive extraction of the actual 1/3 construction. -/
theorem source_direct_common_window_normalization
    (M A0 A1 C : Nat) (hM : 2 <= M) (_hC : 1 <= C)
    {bias : ℝ} (hbias : 0 < bias) :
    exists P : ML2Assembly.SourceBiasedLossParameters,
      P.bias = bias /\ P.cardCoefficient = 32 ^ 6 /\
      P.thicknessCoefficient = 1 / 3 /\ P.cardPower = 6 /\ P.thicknessPower = 1 /\
    exists delta0 : ℝ≥0, 0 < delta0 /\ delta0 <= 1 /\
    forall delta : ℝ≥0, 0 < delta -> delta < delta0 ->
    forall {iota : Type u} (S : Finset iota)
      (T : iota -> Tube delta (EuclideanSpace ℝ (Fin 3)))
      (Q : SourceThreadedTower S T M C), SourceTowerGeometry Q A0 A1 ->
    forall Z : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3)),
      (forall i, (Z i).toTube = T i) ->
      (forall i, i ∈ S -> 0 < volume (Z i).shade) ->
    forall a m : Nat, a < m -> m < M ->
      Nonempty (SourceDirectCommonWindowNormalization Q Z a m P) := by
  classical
  let P : ML2Assembly.SourceBiasedLossParameters :=
    ⟨bias, hbias, 32 ^ 6, by norm_num, 1 / 3, by norm_num,
      by norm_num [div_le_iff₀ (show (0 : ℝ≥0) < 3 by norm_num)], 6, 1⟩
  obtain ⟨eps, heps, hall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (source_eventually_fixed_tower_radius_conditions M hM (e := 1) zero_lt_one)
  refine ⟨P, rfl, rfl, rfl, rfl, rfl, min eps 1, lt_min heps zero_lt_one, min_le_right _ _, ?_⟩
  intro delta hdelta hsmall iota S T Q hgeometry Z hZT hshade a m ham hmM
  have hdelta1 : delta <= 1 := hsmall.le.trans (min_le_right _ _)
  have hscale := hall ⟨hdelta, hsmall.trans_le (min_le_left _ _)⟩
  have hradius : forall k, k < M -> delta <= sourceTowerRadius delta M k := by
    intro k hk
    exact (show delta <= 4 * delta by nlinarith).trans (hscale.2.2.2.2.1 k hk)
  have hradiusPos : forall k, k < M -> 0 < sourceTowerRadius delta M k :=
    fun k hk => hdelta.trans_le (hradius k hk)
  have hdescendant : forall k l, k <= l -> l <= M -> forall i, i ∈ S ->
      (Q.tube l (Q.place l i)).toConvexSpaceBody <=
        (Q.tube k (Q.place k i)).toConvexSpaceBody := by
    intro k l hkl
    induction l, hkl using Nat.le_induction with
    | base => intros; exact le_rfl
    | succ l hkl ih =>
      intro hl i hi
      have hstep := Q.parent_containment l (by omega) (Q.place (l + 1) i)
        (Q.place_mem (l + 1) hl i hi)
      rw [← Q.parent_composition l (by omega) i hi] at hstep
      exact hstep.trans (ih (by omega) i hi)
  let partition : forall j,
      ML2Assembly.SourceDescendantPartition (Q.cell a j) (Q.fibre a m j) := fun j =>
    { cells := fun k => (Q.cell a j).filter (fun i => Q.place m i = k)
      assign := Q.place m
      assigned_mem := fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩
      cells_eq := fun _ _ => rfl
      cells_nonempty := by
        intro k hk
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
        exact ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩⟩
      union_eq := by
        ext i
        simp only [Finset.mem_biUnion, Finset.mem_filter]
        constructor
        · rintro ⟨k, hk, hi, heq⟩; exact hi
        · intro hi
          exact ⟨Q.place m i, Finset.mem_image.mpr ⟨i, hi, rfl⟩, hi, rfl⟩
      disjoint := by
        intro k hk l hl hne
        rw [Function.onFun, Finset.disjoint_left]
        intro i hi hil
        exact hne ((Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp hil).2) }
  let f : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    AffineEquiv.homothetyUnitsMulHom 0 (Units.mk0 (3 : ℝ)⁻¹ (by norm_num))
  have hf : (f : EuclideanSpace ℝ (Fin 3) -> EuclideanSpace ℝ (Fin 3)) =
      AffineMap.homothety 0 (3 : ℝ)⁻¹ := rfl
  let comparison : iota -> ℝ≥0 := fun j => max 1
    (volume (ML2Assembly.sourceAffineReference f).carrier /
      volume (Q.tube a j).carrier).toNNReal
  have hparentPos : forall j, 0 < volume (Q.tube a j).carrier := by
    intro j
    refine lt_of_lt_of_le ?_ (Tube.le_volume (Q.tube a j))
    have hc := Tube.le_volume.c_pos
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
    have hr := hradiusPos a (by omega)
    positivity
  have hreference : forall j,
      volume (ML2Assembly.sourceAffineReference f).carrier <=
        (comparison j : ℝ≥0∞) * volume (Q.tube a j).carrier := by
    intro j
    have hfinite : volume (ML2Assembly.sourceAffineReference f).carrier /
        volume (Q.tube a j).carrier ≠ ⊤ := ENNReal.div_ne_top
      (ML2Assembly.sourceAffineReference f).isCompact.measure_ne_top (hparentPos j).ne'
    calc
      volume (ML2Assembly.sourceAffineReference f).carrier =
          ((volume (ML2Assembly.sourceAffineReference f).carrier /
            volume (Q.tube a j).carrier).toNNReal : ℝ≥0∞) *
              volume (Q.tube a j).carrier := by
        rw [ENNReal.coe_toNNReal hfinite,
          ENNReal.div_mul_cancel (hparentPos j).ne'
            (Q.tube a j).toConvexSpaceBody.isCompact.measure_ne_top]
      _ <= (comparison j : ℝ≥0∞) * volume (Q.tube a j).carrier := by
        gcongr
        exact le_max_right _ _
  have hgeo : ML2Assembly.SourceBiasedParentGeometry (Q.indexSet a) (Q.cell a)
      (Q.fibre a m) (fun i => (Z i).toShadedBody)
      (fun _ i => (Q.tube m i).toConvexSpaceBody)
      (fun j => (Q.tube a j).toConvexSpaceBody) (fun _ => f) comparison
      (fun _ => delta / 3) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨i, hi⟩ := hgeometry.nonempty
      exact ⟨Q.place a i, Q.place_mem a (by omega) i hi⟩
    · intro j hj k hk hne
      rw [Function.onFun, Finset.disjoint_left]
      intro i hi hik
      exact hne ((Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp hik).2)
    · intro j hj
      obtain ⟨i, hi, hplace⟩ := Q.place_surjective a (by omega) j hj
      exact (hshade i hi).trans_le (Finset.single_le_sum_of_canonicallyOrdered
        (f := fun i => volume (Z i).shade) (Finset.mem_filter.mpr ⟨hi, hplace⟩))
    · intro j hj; positivity
    · intro j hj k hk
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨hi, heq⟩ := Finset.mem_filter.mp hi
      simpa only [heq] using hdescendant a m ham.le hmM.le i hi
    · intro j hj
      change f '' (Q.tube a j).carrier ⊆ Metric.closedBall 0 1
      rw [hf]
      exact Kakeya.exists_finite_test_family_maxDensity_closedBall.homothety_subset_closedBall_one
        (R := 3) (by norm_num) (hgeometry.coarse_ball a (by omega) j hj)
    · intro j hj k hk
      rw [ConvexSpaceBody.mapAffine_carrier, hf]
      exact Kakeya.exists_finite_test_family_maxDensity_closedBall.le_scale_homothety_inv
        (R := 3) (by norm_num)
        ((show (delta : ℝ≥0∞) <= (sourceTowerRadius delta M m : ℝ≥0∞) by
          exact_mod_cast hradius m hmM).trans (Q.tube m k).le_ethickness_scale)
    · intro j hj; exact le_max_left _ _
    · intro j hj; exact hreference j
  refine ⟨{
    partition := partition
    normalization := fun _ => f
    comparison := comparison
    thickness := fun _ => delta / 3
    assign_eq := fun _ => rfl
    common_map := fun _ => hf
    thickness_eq := fun _ => rfl
    geometry := hgeo
    polynomial := ?_ }⟩
  apply ML2Assembly.sourceBiased_parent_polynomialScale P hdelta hdelta1
    (Q.indexSet a) (Q.cell a) (Q.fibre a m) partition
    (fun i => (Z i).toShadedBody) (fun _ i => (Q.tube m i).toConvexSpaceBody)
    (fun j => (Q.tube a j).toConvexSpaceBody) (fun _ => f) comparison
    (fun _ => delta / 3) hgeo
  · intro j hj
    have hsub : Q.fibre a m j ⊆ Q.indexSet m := by
      intro k hk
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
      exact Q.place_mem m hmM.le i (Finset.mem_filter.mp hi).1
    calc
      ((Q.fibre a m j).card : ℝ) <= ((Q.indexSet m).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      _ <= (32 / (sourceTowerRadius delta M m : ℝ)) ^ 6 :=
        hgeometry.coarse_card m hmM
      _ <= (32 / (delta : ℝ)) ^ 6 := by
        gcongr
        exact_mod_cast hradius m hmM
      _ = (P.cardCoefficient : ℝ) * (delta : ℝ) ^ (-(P.cardPower : ℝ)) := by
        change (32 / (delta : ℝ)) ^ 6 = 32 ^ 6 * (delta : ℝ) ^ (-(6 : ℝ))
        rw [Real.rpow_neg (by positivity)]
        norm_num [div_eq_mul_inv, mul_pow, inv_pow]
  · intro j hj
    simp only [P, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat, Real.rpow_one]
    ring_nf
    exact le_rfl

/-- A genuine immediate B5 stage. Its factors are on the actual after-family;
no statistics or common physical dimension bin is asserted here. -/
structure SourceDirectOrdinaryCellStage (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3)))
    (G : Finset iota) (QG : SourceThreadedTower G T M C)
    (a m : Nat) (bias : ℝ) (A : ℝ≥0) (K : Nat) where
  parameters : ML2Assembly.SourceBiasedLossParameters
  internal_bias : parameters.bias = bias / 16
  card_coefficient : parameters.cardCoefficient = 32 ^ 6
  thickness_coefficient : parameters.thicknessCoefficient = 1 / 3
  card_power : parameters.cardPower = 6
  thickness_power : parameters.thicknessPower = 1
  normalized : SourceDirectCommonWindowNormalization Q Z a m parameters
  actual : forall j, j ∈ Q.indexSet a ->
    ML2Assembly.SourceAffineWeightedParent (normalized.partition j)
      (fun i => (Z i).toShadedBody) (fun k => (Q.tube m k).toConvexSpaceBody)
      (Q.tube a j).toConvexSpaceBody (normalized.normalization j)
      (normalized.comparison j) (normalized.thickness j) (bias / 16)
  restriction : SourceTowerRestriction Q QG
  before_nonempty : S.Nonempty
  after_nonempty : G.Nonempty
  whole_cell : SourceWholeCellStep Q S G m
  same_coarse : QG.indexSet a = Q.indexSet a
  same_tubes : forall i, (Z i).toTube = T i
  selected_fibre : forall j, forall hj : j ∈ Q.indexSet a,
    QG.fibre a m j = (actual j hj).selection.selected
  selected_leaves : G = (Q.indexSet a).attach.biUnion (fun j =>
    ML2Assembly.sourceDescendantUnion (normalized.partition j.val)
      (actual j.val j.property).selection.selected)
  local_leaves : forall j, forall hj : j ∈ Q.indexSet a,
    G ∩ Q.cell a j = ML2Assembly.sourceDescendantUnion (normalized.partition j)
      (actual j hj).selection.selected
  C0 : ℝ≥0
  coefficient_one : 1 <= C0
  coefficient_bound : C0 <= A * delta ^ (-4 * (bias / 16))
  factor : forall j, j ∈ Q.indexSet a ->
    Factorization (QG.fibre a m j) (fun k => (QG.tube m k).toConvexSpaceBody) C0
  factor_parts : forall j, forall hj : j ∈ Q.indexSet a,
    (factor j hj).parts = (actual j hj).selection.parts
  hull_ratio : forall j, forall hj : j ∈ Q.indexSet a,
    forall part, part ∈ (actual j hj).selection.parts ->
      (delta : ℝ≥0∞) ^ (4 : ℝ) <=
        volume (part.convexHull_biUnion
          (fun k => (Q.tube m k).toConvexSpaceBody)).carrier /
        volume (ML2Assembly.sourceAffineReference (normalized.normalization j)).carrier
  stageLoss : ℝ≥0∞
  loss_one : 1 <= stageLoss
  loss_finite : stageLoss < ⊤
  local_loss : forall j, j ∈ Q.indexSet a ->
    nonempty_biasedFactorization.L 3 (Q.fibre a m j).card
      (normalized.thickness j) (bias / 16) <= stageLoss
  mass : (∑ i ∈ S, volume (Z i).shade) <= stageLoss * ∑ i ∈ G, volume (Z i).shade
  loss_bound : stageLoss <= sourceFixedPreparationLoss K delta

/-- The ordinary coefficient pays the actual q=4 hull/reference lower ratio.
All scale-independent constants precede the runtime tower and level. -/
theorem source_direct_exists_ordinary_cell_stage
    (M A0 A1 C : Nat) (hM : 2 <= M) (hC : 1 <= C)
    (bias : ℝ) (hbias : 0 < bias) :
    exists (A : ℝ≥0) (K : Nat) (delta0 : ℝ≥0),
      1 <= A /\ 1 <= K /\ 0 < delta0 /\ delta0 <= 1 /\
      delta0 <= (400 : ℝ≥0) ^ (-(M : ℝ)) /\
    forall delta : ℝ≥0, 0 < delta -> delta < delta0 ->
    forall {iota : Type u} (S : Finset iota)
      (T : iota -> Tube delta (EuclideanSpace ℝ (Fin 3)))
      (Q : SourceThreadedTower S T M C), SourceTowerGeometry Q A0 A1 ->
    forall Z : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3)),
      (forall i, (Z i).toTube = T i) ->
      (forall i, i ∈ S -> 0 < volume (Z i).shade) ->
    forall a m : Nat, a < m -> m < M ->
    exists (G : Finset iota) (QG : SourceThreadedTower G T M C),
      Nonempty (SourceDirectOrdinaryCellStage Q Z G QG a m bias A K) := by
  classical
  have hb : 0 < bias / 16 := by positivity
  obtain ⟨P, hPb, hPc, hPt, hPcp, hPtp, eps, heps, heps1, hnorm⟩ :=
    source_direct_common_window_normalization M A0 A1 C hM hC hb
  obtain ⟨epsL, hepsL, hepsL1, hpoly⟩ := ML2Assembly.sourceBiased_exists_polylog_threshold 3 P
  let A : ℝ≥0 := max 2 (nonempty_biasedFactorization.C 3 (bias / 16))
  let delta0 := min (min eps epsL) (min (1 / 1296) ((400 : ℝ≥0) ^ (-(M : ℝ))))
  have hA2 : 2 <= A := le_max_left _ _
  have hA1 : 1 <= A := le_trans (by norm_num) hA2
  refine ⟨A, 5, delta0, hA1, by norm_num, ?_, ?_, ?_, ?_⟩
  · dsimp [delta0]; positivity
  · exact (min_le_left _ _).trans ((min_le_left _ _).trans heps1)
  · exact (min_le_right _ _).trans (min_le_right _ _)
  intro delta hd hs iota S T Q hgeo Z hZT hshade a m ham hmM
  have hsN : delta < eps := hs.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hsL : delta < epsL := hs.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hd1 : delta <= 1 := hsN.le.trans heps1
  have hdsmall : delta <= 1 / 1296 := hs.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  obtain ⟨N⟩ := hnorm delta hd hsN S T Q hgeo Z hZT hshade a m ham hmM
  have hlocal : forall j, j ∈ Q.indexSet a ->
      nonempty_biasedFactorization.L 3 (Q.fibre a m j).card
        (N.thickness j) (bias / 16) <= polylogLoss 5 delta := by
    intro j hj
    simpa only [hPb] using (hpoly delta (N.thickness j) _ hsL (N.polynomial j hj)).2.2
  have hLf : polylogLoss 5 delta < ⊤ := by
    unfold polylogLoss
    finiteness
  obtain ⟨D, G, hGeq, hGsub, hGne, hGlocal, _, _, _, hmass⟩ :=
    ML2Assembly.sourceBiased_exists_parentAggregation
      (Q.indexSet a) N.geometry.parents_nonempty (Q.cell a) (Q.fibre a m) N.partition
      N.geometry.parent_fibres_disjoint (fun i => (Z i).toShadedBody)
      (fun _ k => (Q.tube m k).toConvexSpaceBody) (fun j => (Q.tube a j).toConvexSpaceBody)
      N.normalization N.comparison N.thickness (bias / 16) hb
      (polylogLoss 5 delta) hLf N.geometry.mass_pos N.geometry.thickness_pos
      N.geometry.contained N.geometry.normalized_ball N.geometry.normalized_thickness
      (fun j hj => ⟨N.geometry.comparison_one_le j hj, N.geometry.reference_comparison j hj⟩)
      (by simpa using hlocal)
  have hunion : (Q.indexSet a).biUnion (Q.cell a) = S := by
    ext i
    simp only [Finset.mem_biUnion, SourceThreadedTower.cell, Finset.mem_filter]
    exact ⟨fun ⟨j, hj, hi, heq⟩ => hi,
      fun hi => ⟨Q.place a i, Q.place_mem a (by omega) i hi, hi, rfl⟩⟩
  have hGS : G <= S := by
    change G ⊆ S
    simpa only [hunion] using hGsub
  have hmem (j : {j // j ∈ Q.indexSet a}) (i : iota) :
      i ∈ ML2Assembly.sourceDescendantUnion (N.partition j.val) (D j).selection.selected ↔
        i ∈ Q.cell a j.val ∧ Q.place m i ∈ (D j).selection.selected := by
    simp only [ML2Assembly.sourceDescendantUnion, Finset.mem_biUnion]
    constructor
    · rintro ⟨k, hk, hi⟩
      rw [(N.partition j.val).cells_eq k ((D j).selection.selected_subset hk)] at hi
      obtain ⟨hi, heq⟩ := Finset.mem_filter.mp hi
      rw [N.assign_eq] at heq
      exact ⟨hi, heq ▸ hk⟩
    · rintro ⟨hi, hk⟩
      refine ⟨Q.place m i, hk, ?_⟩
      rw [(N.partition j.val).cells_eq _ ((D j).selection.selected_subset hk), N.assign_eq]
      exact Finset.mem_filter.mpr ⟨hi, rfl⟩
  have hcoarse (b : Nat) (hbM : b <= M) : forall c, c <= b ->
      forall i, i ∈ S -> forall j, j ∈ S ->
        Q.place b i = Q.place b j -> Q.place c i = Q.place c j := by
    induction b with
    | zero => intro c hc i hi j hj heq; simpa only [Nat.eq_zero_of_le_zero hc] using heq
    | succ b ih =>
      intro c hc i hi j hj heq
      by_cases heq' : c = b + 1
      · simpa only [heq'] using heq
      · apply ih (by omega) c (by omega) i hi j hj
        rw [Q.parent_composition b (by omega) i hi,
          Q.parent_composition b (by omega) j hj, heq]
  have hsat : forall i, i ∈ G -> forall k, k ∈ S -> Q.place m k = Q.place m i -> k ∈ G := by
    intro i hi k hk hki
    let j : {j // j ∈ Q.indexSet a} := ⟨Q.place a i, Q.place_mem a (by omega) i (hGS hi)⟩
    have hic : i ∈ Q.cell a j.val := Finset.mem_filter.mpr ⟨hGS hi, rfl⟩
    have him := (hmem j i).mp ((hGlocal j) ▸ Finset.mem_inter.mpr ⟨hi, hic⟩)
    have hkc : k ∈ Q.cell a j.val := Finset.mem_filter.mpr
      ⟨hk, hcoarse m hmM.le a ham.le k hk i (hGS hi) hki⟩
    have hkm := (hmem j k).mpr ⟨hkc, hki ▸ him.2⟩
    rw [← hGlocal j] at hkm
    exact (Finset.mem_inter.mp hkm).1
  have hocc (k : Nat) (hk : k <= M) : Q.assignedFootprint G k <= Q.indexSet k := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact Q.place_mem k hk i (hGS hi)
  let QG : SourceThreadedTower G T M C := {
    indexSet := Q.assignedFootprint G
    place := Q.place
    parent := Q.parent
    tube := Q.tube
    tube_injective := fun k hk i hi j hj => Q.tube_injective k hk (hocc k hk hi) (hocc k hk hj)
    place_mem := fun k _ i hi => Finset.mem_image_of_mem _ hi
    place_surjective := fun k _ j hj => Finset.mem_image.mp hj
    leaf_containment := fun k hk i hi => Q.leaf_containment k hk i (hGS hi)
    parent_mem := by
      intro k hk j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      rw [← Q.parent_composition k hk i (hGS hi)]
      exact Finset.mem_image_of_mem _ hi
    parent_composition := fun k hk i hi => Q.parent_composition k hk i (hGS hi)
    parent_containment := fun k hk j hj => Q.parent_containment k hk j (hocc (k + 1) (by omega) hj)
    bottom_index := by
      ext i
      constructor
      · intro hi
        obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
        rw [Q.bottom_place j (hGS hj)] at hji
        exact hji ▸ hj
      · intro hi
        exact Finset.mem_image.mpr ⟨i, hi, Q.bottom_place i (hGS hi)⟩
    bottom_place := fun i hi => Q.bottom_place i (hGS hi)
    bottom_body := fun i hi => Q.bottom_body i (hGS hi)
    containment_multiplicity := by
      intro k hk i hi
      exact (Finset.card_le_card (Finset.filter_subset_filter _ (hocc k hk))).trans
        (Q.containment_multiplicity k hk i (hGS hi)) }
  have hrest : SourceTowerRestriction Q QG := {
    subset := hGS
    assignment := rfl
    parent := rfl
    tubes := rfl
    occupied := fun _ _ => rfl
    full_retained_fibres := fun _ _ _ => rfl }
  have hcell (j : iota) : QG.cell a j = G ∩ Q.cell a j := by
    ext i
    simp only [SourceThreadedTower.cell, Finset.mem_filter, Finset.mem_inter]
    change (i ∈ G ∧ Q.place a i = j) ↔ (i ∈ G ∧ i ∈ S ∧ Q.place a i = j)
    exact ⟨fun h => ⟨h.1, hGS h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  have hfibre (j : {j // j ∈ Q.indexSet a}) : QG.fibre a m j.val = (D j).selection.selected := by
    change (QG.cell a j.val).image (Q.place m) = _
    rw [hcell, hGlocal j]
    ext k
    constructor
    · rintro hk
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
      exact ((hmem j i).mp hi).2
    · intro hk
      obtain ⟨i, hi⟩ := (N.partition j.val).cells_nonempty k ((D j).selection.selected_subset hk)
      have hic := hi
      rw [(N.partition j.val).cells_eq k ((D j).selection.selected_subset hk), N.assign_eq] at hic
      refine Finset.mem_image.mpr ⟨i, ?_, (Finset.mem_filter.mp hic).2⟩
      exact Finset.mem_biUnion.mpr ⟨k, hk, hi⟩
  have hsame : QG.indexSet a = Q.indexSet a := by
    apply Finset.Subset.antisymm (hocc a (by omega))
    intro j hj
    obtain ⟨k, hk⟩ := (D ⟨j, hj⟩).selection.selected_nonempty
    rw [← hfibre ⟨j, hj⟩] at hk
    obtain ⟨i, hi, hki⟩ := Finset.mem_image.mp hk
    obtain ⟨hi, heq⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_image.mpr ⟨i, hi, heq⟩
  have hwhole : SourceWholeCellStep Q S G m := {
    selected := Q.assignedFootprint G m
    selected_subset := Finset.image_subset_image hGS
    leaves_eq := by
      ext i
      simp only [Finset.mem_filter]
      constructor
      · intro hi; exact ⟨hGS hi, Finset.mem_image_of_mem _ hi⟩
      · rintro ⟨hi, hpi⟩
        obtain ⟨k, hk, hki⟩ := Finset.mem_image.mp hpi
        exact hsat k hk i hi hki.symm
    complete := by
      intro j hj
      obtain ⟨k, hk, hkj⟩ := Finset.mem_image.mp hj
      ext i
      simp only [Finset.mem_filter]
      exact ⟨fun h => ⟨hGS h.1, h.2⟩,
        fun h => ⟨hsat k hk i h.1 (h.2.trans hkj.symm), h.2⟩⟩ }
  let C0 : ℝ≥0 := A * delta ^ (-4 * (bias / 16))
  have hpow : 1 <= delta ^ (-4 * (bias / 16)) := NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos hd hd1 (by linarith)
  have hAC : A <= C0 := le_mul_of_one_le_right' hpow
  have hC01 : 1 <= C0 := hA1.trans hAC
  have hC02 : 2 <= C0 := hA2.trans hAC
  have hCf : (nonempty_biasedFactorization.C 3 (bias / 16) : ℝ≥0∞) *
      (delta : ℝ≥0∞) ^ (-4 * (bias / 16)) <= (C0 : ℝ≥0∞) := by
    simpa only [C0, ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hd.ne'] using
      mul_le_mul_left
        (show (nonempty_biasedFactorization.C 3 (bias / 16) : ℝ≥0∞) <= A from
          ENNReal.coe_le_coe.mpr (le_max_right _ _)) ((delta : ℝ≥0∞) ^ (-4 * (bias / 16)))
  have hratio (j : {j // j ∈ Q.indexSet a}) (part : Finset iota)
      (hp : part ∈ (D j).selection.parts) :
      (delta : ℝ≥0∞) ^ (4 : ℝ) <=
        volume (part.convexHull_biUnion (fun k => (Q.tube m k).toConvexSpaceBody)).carrier /
        volume (ML2Assembly.sourceAffineReference (N.normalization j.val)).carrier := by
    rw [← (D j).ratio_map part hp]
    obtain ⟨k, hk⟩ := (D j).selection.factor.nonempty_of_mem_parts
      ((D j).selection.factor_parts.symm ▸ hp)
    have hkI : k ∈ Q.fibre a m j.val := (D j).selection.selected_subset
      ((D j).selection.factor.le ((D j).selection.factor_parts.symm ▸ hp) hk)
    have hv := ((Q.tube m k).toConvexSpaceBody.mapAffine (N.normalization j.val)).convex.le_volume_of_le_scale
      (N.geometry.normalized_thickness j.val j.property k hkI)
    rw [N.thickness_eq] at hv
    have hh : volume ((Q.tube m k).toConvexSpaceBody.mapAffine (N.normalization j.val)).carrier <=
        volume (part.convexHull_biUnion
          (fun k => (Q.tube m k).toConvexSpaceBody.mapAffine (N.normalization j.val))).carrier :=
      measure_mono (Finset.le_convexHull_biUnion
        (fun k => (Q.tube m k).toConvexSpaceBody.mapAffine (N.normalization j.val)) hk)
    have hball : volume (closedUnitBall (E := EuclideanSpace ℝ (Fin 3))).carrier <= 8 := by
      simpa only [closedUnitBall_carrier, finrank_euclideanSpace_fin, show (2 : ℝ≥0∞) ^ 3 = 8 by norm_num] using
        (volume_closedBall_le_two_pow_finrank (E := EuclideanSpace ℝ (Fin 3)))
    apply (ENNReal.le_div_iff_mul_le (.inl closedUnitBall_volume_pos.ne')
      (.inl closedUnitBall.isCompact.measure_ne_top)).mpr
    calc (delta : ℝ≥0∞) ^ (4 : ℝ) * volume (closedUnitBall (E := EuclideanSpace ℝ (Fin 3))).carrier
        <= (delta : ℝ≥0∞) ^ (4 : ℝ) * 8 := by gcongr
      _ <= (Metric.lt_volume_convexHull.c 3 : ℝ≥0∞) * ((delta / 3 : ℝ≥0) : ℝ≥0∞) ^ 3 := by
        have he : delta ^ 4 * 8 <= (1 / 6 : ℝ≥0) * (delta / 3) ^ 3 := by
          have hmul := mul_le_mul_left hdsmall (delta ^ 3)
          nlinarith
        have he' := ENNReal.coe_le_coe.mpr he
        norm_num [ENNReal.rpow_natCast, Metric.lt_volume_convexHull.c,
          ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_div] at he' ⊢
        exact he'
      _ <= _ := le_trans (by simpa only [finrank_euclideanSpace_fin] using hv) hh
  have hfactor (j : {j // j ∈ Q.indexSet a}) :
      exists F : Factorization (QG.fibre a m j.val)
        (fun k => (QG.tube m k).toConvexSpaceBody) C0, F.parts = (D j).selection.parts := by
    let V := fun k => (Q.tube m k).toConvexSpaceBody
    have hcost (part : Finset iota) (hp : part ∈ (D j).selection.parts) :
        (nonempty_biasedFactorization.C 3 (bias / 16) : ℝ≥0∞) *
          (volume (part.convexHull_biUnion V).carrier /
            volume (ML2Assembly.sourceAffineReference (N.normalization j.val)).carrier) ^ (-(bias / 16)) <= C0 := by
      refine le_trans ?_ hCf
      apply mul_le_mul_right
      rw [show -4 * (bias / 16) = -(4 * (bias / 16)) by ring,
        ENNReal.rpow_neg, ENNReal.rpow_neg]
      have hr := ENNReal.rpow_le_rpow (hratio j part hp) hb.le
      rw [← ENNReal.rpow_mul] at hr
      exact ENNReal.inv_le_inv.mpr hr
    have hcapture (part : Finset iota) (hp : part ∈ (D j).selection.parts) :
        Kakeya.maxDensity (D j).selection.selected V <=
          (C0 : ℝ≥0∞) * Kakeya.densityIn part V (part.convexHull_biUnion V) := by
      let r := volume (part.convexHull_biUnion V).carrier /
        volume (ML2Assembly.sourceAffineReference (N.normalization j.val)).carrier
      have hr0 : r ≠ 0 := ENNReal.div_ne_zero.mpr
        ⟨((D j).hull_pos part hp).ne', (D j).reference_finite.ne⟩
      have hrt : r ≠ ⊤ := ENNReal.div_ne_top ((D j).hull_finite part hp).ne (D j).reference_pos.ne'
      have hc0 : (nonempty_biasedFactorization.C 3 (bias / 16) : ℝ≥0∞) ≠ 0 := by
        dsimp [nonempty_biasedFactorization.C]
        positivity
      have hc := (D j).capture_reference part hp
      simp only [show Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 by simp] at hc
      have hcancel :
          ((nonempty_biasedFactorization.C 3 (bias / 16) : ℝ≥0∞) * r ^ (-(bias / 16))) *
          ((nonempty_biasedFactorization.C 3 (bias / 16) : ℝ≥0∞)⁻¹ * r ^ (bias / 16)) = 1 := by
        rw [ENNReal.rpow_neg]
        calc _ = ((nonempty_biasedFactorization.C 3 (bias / 16) : ℝ≥0∞) *
            (nonempty_biasedFactorization.C 3 (bias / 16) : ℝ≥0∞)⁻¹) *
            ((r ^ (bias / 16))⁻¹ * r ^ (bias / 16)) := by ring
          _ = 1 := by rw [ENNReal.mul_inv_cancel hc0 ENNReal.coe_ne_top,
            ENNReal.inv_mul_cancel (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hr0) hrt).ne'
              (ENNReal.rpow_ne_top_of_ne_zero hr0 hrt), one_mul]
      have hcap : Kakeya.maxDensity (D j).selection.selected V <=
          ((nonempty_biasedFactorization.C 3 (bias / 16) : ℝ≥0∞) * r ^ (-(bias / 16))) *
            Kakeya.densityIn part V (part.convexHull_biUnion V) := by
        calc _ = ((nonempty_biasedFactorization.C 3 (bias / 16) : ℝ≥0∞) * r ^ (-(bias / 16))) *
            ((nonempty_biasedFactorization.C 3 (bias / 16) : ℝ≥0∞)⁻¹ * r ^ (bias / 16) *
              Kakeya.maxDensity (D j).selection.selected V) := by rw [← mul_assoc, hcancel, one_mul]
          _ <= _ := mul_le_mul_right hc _
      exact hcap.trans (mul_le_mul_left (hcost part hp) _)
    have hdim (part : Finset iota) (hp : part ∈ (D j).selection.parts) (k : Nat) :
        ethickness ℝ
          (part.convexHull_biUnion (fun k => (V k).mapAffine (N.normalization j.val))).carrier k =
          (1 / 3 : ℝ≥0∞) * ethickness ℝ (part.convexHull_biUnion V).carrier k := by
      rw [← (D j).hull_map part hp, ConvexSpaceBody.mapAffine_carrier, N.common_map,
        Metric.ethickness_homothety_image _ (by norm_num : (3 : ℝ)⁻¹ ≠ 0)]
      norm_num [V]
    have hsim : forall part, part ∈ (D j).selection.parts ->
        forall part', part' ∈ (D j).selection.parts -> forall k : Nat,
          ethickness ℝ (part.convexHull_biUnion V).carrier k <=
            (C0 : ℝ≥0∞) * ethickness ℝ (part'.convexHull_biUnion V).carrier k := by
      intro part hp part' hp' k
      by_cases hk : k < 3
      · have hh := (D j).selection.dimensions part hp part' hp' ⟨k, by simpa using hk⟩
        rw [hdim part hp k, hdim part' hp' k] at hh
        have hh' : ethickness ℝ (part.convexHull_biUnion V).carrier k <=
            2 * ethickness ℝ (part'.convexHull_biUnion V).carrier k := by
          apply (ENNReal.mul_le_mul_iff_right (by norm_num : (1 / 3 : ℝ≥0∞) ≠ 0) (by norm_num)).mp
          simpa only [mul_left_comm (2 : ℝ≥0∞)] using hh
        exact hh'.trans (mul_le_mul_left (by exact_mod_cast hC02) _)
      · rw [ethickness_eq_zero_of_finrank_le (show Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) <= k by simpa using Nat.le_of_not_gt hk)]
        exact zero_le
    have hkt : ConvexSpaceBody.IsKatzTao (D j).selection.parts
        (fun part => part.convexHull_biUnion V) C0 := by
      obtain ⟨part, hp⟩ := (D j).selection.parts_nonempty
      exact ((D j).outer_katzTao part hp).trans (by simpa using hcost part hp)
    let F0 : Factorization (D j).selection.selected V C0 := {
      toFinpartition := (D j).selection.factor.toFinpartition
      isKatzTao := by simpa only [(D j).selection.factor_parts] using hkt
      maxDensity_le_mul := by simpa only [(D j).selection.factor_parts] using hcapture
      simDims := by
        intro part hp part' hp' k
        exact hsim part ((D j).selection.factor_parts ▸ hp) part'
          ((D j).selection.factor_parts ▸ hp') k }
    change exists F : Factorization (QG.fibre a m j.val) V C0, F.parts = (D j).selection.parts
    rw [hfibre j]
    exact ⟨F0, (D j).selection.factor_parts⟩
  choose F hF using hfactor
  refine ⟨G, QG, ⟨{
    parameters := P
    internal_bias := hPb
    card_coefficient := hPc
    thickness_coefficient := hPt
    card_power := hPcp
    thickness_power := hPtp
    normalized := N
    actual := fun j hj => D ⟨j, hj⟩
    restriction := hrest
    before_nonempty := hgeo.nonempty
    after_nonempty := hGne
    whole_cell := hwhole
    same_coarse := hsame
    same_tubes := hZT
    selected_fibre := fun j hj => hfibre ⟨j, hj⟩
    selected_leaves := hGeq
    local_leaves := fun j hj => hGlocal ⟨j, hj⟩
    C0 := C0
    coefficient_one := hC01
    coefficient_bound := le_rfl
    factor := fun j hj => F ⟨j, hj⟩
    factor_parts := fun j hj => hF ⟨j, hj⟩
    hull_ratio := fun j hj => hratio ⟨j, hj⟩
    stageLoss := polylogLoss 5 delta
    loss_one := by
      unfold polylogLoss
      exact ENNReal.one_le_ofReal.mpr (le_max_left _ _)
    loss_finite := hLf
    local_loss := hlocal
    mass := by simpa only [hunion] using hmass
    loss_bound := ?_ }⟩⟩
  rw [polylogLoss, max_eq_right (one_le_polylog hd1 5), sourceFixedPreparationLoss]
  apply ENNReal.ofReal_le_ofReal
  have hdR : (0 : ℝ) < delta := by exact_mod_cast hd
  have hlog : Real.log (delta : ℝ) <= 0 := Real.log_nonpos hdR.le (by exact_mod_cast hd1)
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htwo1 : Real.log 2 <= 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hbase : 1 - Real.log (delta : ℝ) <= 2 + Real.logb 2 (1 / (delta : ℝ)) := by
    rw [Real.logb, one_div, Real.log_inv]
    have hh : -Real.log (delta : ℝ) <= -Real.log (delta : ℝ) / Real.log 2 := by
      apply (le_div_iff₀ htwo).mpr
      exact mul_le_of_le_one_right (neg_nonneg.mpr hlog) htwo1
    linarith
  exact pow_le_pow_left₀ (by linarith) hbase 5

/-- The used old tags are exactly those with a nonempty literal intersection. -/
noncomputable def sourceOrdinaryUsedParts {I : Finset iota}
    (F : Finpartition I) (J : Finset iota) : Finset (Finset iota) :=
  F.parts.filter (fun part => (part ∩ J).Nonempty)

/-- Quantitative geometric rows on exactly the literal final fragments. -/
structure SourceOrdinaryFragmentGeometry {I J : Finset iota}
    (V : iota -> ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (C0 L : ℝ≥0) (F : Factorization I V C0) : Prop where
  old_positive : forall part, part ∈ sourceOrdinaryUsedParts F.toFinpartition J ->
    0 < volume (part.convexHull_biUnion V).carrier
  retained_positive : forall part, part ∈ sourceOrdinaryUsedParts F.toFinpartition J ->
    0 < volume ((part ∩ J).convexHull_biUnion V).carrier
  contained : forall part, part ∈ sourceOrdinaryUsedParts F.toFinpartition J ->
    (part ∩ J).convexHull_biUnion V <= part.convexHull_biUnion V
  old_volume : forall part, part ∈ sourceOrdinaryUsedParts F.toFinpartition J ->
    volume (part.convexHull_biUnion V).carrier <=
      (C0 * L : ℝ≥0) * volume ((part ∩ J).convexHull_biUnion V).carrier
  capture : forall part, part ∈ sourceOrdinaryUsedParts F.toFinpartition J ->
    Kakeya.maxDensity J V <= (C0 * L : ℝ≥0) *
      Kakeya.densityIn (part ∩ J) V ((part ∩ J).convexHull_biUnion V)
  simultaneous_test : forall K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)),
    exists Kplus : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)),
      volume Kplus.carrier <= (384 * (2 ^ 50 * C0 * L) ^ 3 : ℝ≥0) * volume K.carrier /\
      forall part, part ∈ sourceOrdinaryUsedParts F.toFinpartition J ->
        (part ∩ J).convexHull_biUnion V <= K -> part.convexHull_biUnion V <= Kplus
  thickness : forall part, part ∈ sourceOrdinaryUsedParts F.toFinpartition J ->
    forall k : Nat, ethickness ℝ (part.convexHull_biUnion V).carrier k <=
      (2 ^ 50 * C0 * L : ℝ≥0) * ethickness ℝ ((part ∩ J).convexHull_biUnion V).carrier k

end Kakeya.ML2Core

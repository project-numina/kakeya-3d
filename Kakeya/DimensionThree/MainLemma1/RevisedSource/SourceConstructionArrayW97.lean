/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceConstructionDefinitionsW97
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.ActualWorkingTowerW96
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.CoarseNodePrefixW112
public import Kakeya.MultiScaleSubmult

/-!
# Relative Frostman array and stopping (A1-A6)

Builds the relative Frostman array `actualRelativeCFArrayW97` over a regularized working tower
and proves its structural properties: `actual_descendants_partition_three_levels_w97` (A1,
partition of descendant fibres), `actual_relative_cf_composition_w97` (A2, two-scale
composition), `actual_relative_cf_crude_and_prefix_w97` (A3, crude exponent two and prefix
bounds), `actual_top_relative_cf_w97` (A4, root entry). `exists_same_array_stopping_w97` (A5)
is the literal finite stopping argument on one array, and
`exists_extended_regularized_stopping_w97` (A6) constructs the `M*M` regularized tower whose
`M`-spaced restriction is the visible tower, with the stopping block on the same final `A`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ConvexSpaceBody ShadedBody

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

universe uE uI

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

open RevisedLiteralProfileInterfaceFormalizerW87

def actualRelativeCFArrayW97
    {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}
    {A : Finset iota} {Y : iota -> ShadedTube delta E} {M : Nat} {Ccan : ℝ≥0}
    (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan) (k l : Nat) : ℝ≥0∞ :=
  (U.cover.indexSet k).sup (actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k l)

/-- A2 uses the lower actual-family two-scale donor, not nodesUnder. -/
theorem actual_relative_cf_composition_w97 :
    ∃ C : ℝ≥0, 1 <= C ∧
      ∀ {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}, 0 < delta -> delta <= 1 ->
      ∀ {A : Finset iota} {Y : iota -> ShadedTube delta E} {M : Nat} {Ccan Ctw Ccell : ℝ≥0}
        (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan),
        A.Nonempty -> SourceRegularizedWorkingTowerW95 U Ctw Ccell ->
        (∀ i ∈ A, (Y i).carrier ⊆ Metric.closedBall 0 1) ->
        ∀ k l m : Nat, k < l -> l < m -> m <= M ->
          4 * Tube.gridScale delta M m <= Tube.gridScale delta M l ->
          (∀ R ∈ U.cover.indexSet k,
            actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k m R <=
              2 * (C : ℝ≥0∞) ^ (2 : Nat) * actualRelativeCFArrayW97 U k l *
                actualRelativeCFArrayW97 U l m) ∧
          actualRelativeCFArrayW97 U k m <=
            2 * (C : ℝ≥0∞) ^ (2 : Nat) * actualRelativeCFArrayW97 U k l *
              actualRelativeCFArrayW97 U l m := by
  obtain ⟨Ctwo, hCtwo, htwo⟩ := Kakeya.MultiScaleSubmult.maxDensity_le_two_fibreDeltaMax
    (E := E) 5 (by norm_num) 1 one_pos
  let C : ℝ≥0 := max 1 (Real.toNNReal Ctwo)
  refine ⟨C, le_max_left _ _, ?_⟩
  intro iota inst delta hd hd1 A Y M Ccan Ctw Ccell U hA hregular hball k l m hkl hlm hm hgap
  have hdescendant_partition {delta : ℝ≥0}
      {iota : Type uI} [DecidableEq iota]
      (A : Finset iota) (Y : iota -> ShadedTube delta E)
      (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
      (hregular : SourceRegularizedWorkingTowerW95 U Ctw Ccell)
      (k l m : Nat) (hkl : k < l) (hlm : l < m) (hm : m <= M) :
      ∃ parent : iota -> iota,
        (∀ i ∈ A, parent (U.cover.assign m i) = U.cover.assign l i) ∧
        ∀ R ∈ U.cover.indexSet k,
          (actualDescendantsW95 A U.cover.assign k m R).image parent =
            actualDescendantsW95 A U.cover.assign k l R ∧
          (∀ Q ∈ actualDescendantsW95 A U.cover.assign k l R,
            (actualDescendantsW95 A U.cover.assign k m R).filter (fun W => parent W = Q) =
              actualDescendantsW95 A U.cover.assign l m Q) ∧
          ((actualDescendantsW95 A U.cover.assign k l R).card : ℝ≥0) * hregular.countBand l m <=
            ((actualDescendantsW95 A U.cover.assign k m R).card : ℝ≥0) ∧
          ((actualDescendantsW95 A U.cover.assign k m R).card : ℝ≥0) <
            2 * ((actualDescendantsW95 A U.cover.assign k l R).card : ℝ≥0) * hregular.countBand l m := by
    let parent : iota -> iota := fun Q => if hQ : Q ∈ A.image (U.cover.assign m) then
      U.cover.assign l (Finset.mem_image.mp hQ).choose else Q
    have hparent : ∀ i ∈ A, parent (U.cover.assign m i) = U.cover.assign l i := by
      intro i hi
      have hj : U.cover.assign m i ∈ A.image (U.cover.assign m) := Finset.mem_image.mpr ⟨i, hi, rfl⟩
      dsimp only [parent]
      rw [dif_pos hj]
      exact U.cover.assign_eq_of_le hlm.le hm
        (Finset.mem_image.mp hj).choose_spec.1 hi (Finset.mem_image.mp hj).choose_spec.2
    refine ⟨parent, hparent, ?_⟩
    intro R hR
    let Dkm := actualDescendantsW95 A U.cover.assign k m R
    let Dkl := actualDescendantsW95 A U.cover.assign k l R
    let Dlm := actualDescendantsW95 A U.cover.assign l m
    have himage : Dkm.image parent = Dkl := by
      ext Q
      constructor
      · intro hQ
        obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hQ
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hW
        obtain ⟨hiA, hiR⟩ := Finset.mem_filter.mp hi
        rw [hparent i hiA]
        exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hiA, hiR⟩, rfl⟩
      · intro hQ
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
        obtain ⟨hiA, hiR⟩ := Finset.mem_filter.mp hi
        exact Finset.mem_image.mpr ⟨U.cover.assign m i,
          Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hiA, hiR⟩, rfl⟩, hparent i hiA⟩
    have hfibre : ∀ Q ∈ Dkl, Dkm.filter (fun W => parent W = Q) = Dlm Q := by
      intro Q hQ
      obtain ⟨i0, hi0, hi0Q⟩ := Finset.mem_image.mp hQ
      obtain ⟨hi0A, hi0R⟩ := Finset.mem_filter.mp hi0
      ext W
      constructor
      · intro hW
        obtain ⟨hW, hWQ⟩ := Finset.mem_filter.mp hW
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hW
        obtain ⟨hiA, hiR⟩ := Finset.mem_filter.mp hi
        have hiQ : U.cover.assign l i = Q := (hparent i hiA).symm.trans hWQ
        exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hiA, hiQ⟩, rfl⟩
      · intro hW
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hW
        obtain ⟨hiA, hiQ⟩ := Finset.mem_filter.mp hi
        have hiR : U.cover.assign k i = R :=
          (U.cover.assign_eq_of_le hkl.le (by omega) hiA hi0A (hiQ.trans hi0Q.symm)).trans hi0R
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hiA, hiR⟩, rfl⟩,
            (hparent i hiA).trans hiQ⟩
    have hQmem : ∀ Q ∈ Dkl, Q ∈ U.cover.indexSet l := by
      intro Q hQ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
      exact U.cover.assign_mem l (by omega) i (Finset.mem_filter.mp hi).1
    have hsum : (Dkm.card : ℝ≥0) = ∑ Q ∈ Dkl, ((Dlm Q).card : ℝ≥0) := by
      have hmaps : ∀ W ∈ Dkm, parent W ∈ Dkl := by
        intro W hW
        rw [← himage]
        exact Finset.mem_image.mpr ⟨W, hW, rfl⟩
      calc
        (Dkm.card : ℝ≥0) = ∑ Q ∈ Dkl, ((Dkm.filter (fun W => parent W = Q)).card : ℝ≥0) := by
          simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
            (Finset.sum_fiberwise_of_maps_to hmaps (fun _ => (1 : ℝ≥0))).symm
        _ = ∑ Q ∈ Dkl, ((Dlm Q).card : ℝ≥0) := Finset.sum_congr rfl (fun Q hQ => by rw [hfibre Q hQ])
    have hDkl : Dkl.Nonempty := by
      have hRimage : R ∈ A.image (U.cover.assign k) := (hregular.surjective k (by omega)) ▸ hR
      obtain ⟨i, hi, hiR⟩ := Finset.mem_image.mp hRimage
      exact ⟨U.cover.assign l i, Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hiR⟩, rfl⟩⟩
    refine ⟨himage, hfibre, ?_, ?_⟩
    · calc
        (Dkl.card : ℝ≥0) * hregular.countBand l m = ∑ Q ∈ Dkl, hregular.countBand l m := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ <= ∑ Q ∈ Dkl, ((Dlm Q).card : ℝ≥0) := Finset.sum_le_sum
          (fun Q hQ => hregular.count_lower l m hlm hm Q (hQmem Q hQ))
        _ = (Dkm.card : ℝ≥0) := hsum.symm
    · calc
        (Dkm.card : ℝ≥0) = ∑ Q ∈ Dkl, ((Dlm Q).card : ℝ≥0) := hsum
        _ < ∑ Q ∈ Dkl, 2 * hregular.countBand l m := by
          apply Finset.sum_lt_sum
          · exact fun Q hQ => (hregular.count_upper l m hlm hm Q (hQmem Q hQ)).le
          · obtain ⟨Q, hQ⟩ := hDkl
            exact ⟨Q, hQ, hregular.count_upper l m hlm hm Q (hQmem Q hQ)⟩
        _ = 2 * (Dkl.card : ℝ≥0) * hregular.countBand l m := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
  have hactual_two_scale {delta : ℝ≥0} (hd : 0 < delta) (hd1 : delta <= 1)
      {iota : Type uI} [DecidableEq iota]
      (A : Finset iota) (Y : iota -> ShadedTube delta E)
      (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
      (hregular : SourceRegularizedWorkingTowerW95 U Ctw Ccell)
      (k l m : Nat) (hkl : k < l) (hlm : l < m) (hm : m <= M)
      (hgap : 4 * Tube.gridScale delta M m <= Tube.gridScale delta M l)
      (R : iota) (hR : R ∈ U.cover.indexSet k) :
      Kakeya.maxDensity (actualDescendantsW95 A U.cover.assign k m R)
        (fun W => (U.cover.tube m W).toConvexSpaceBody) <=
      ENNReal.ofReal Ctwo ^ (2 : Nat) *
        Kakeya.maxDensity (actualDescendantsW95 A U.cover.assign k l R)
          (fun Q => (U.cover.tube l Q).toConvexSpaceBody) *
        (actualDescendantsW95 A U.cover.assign k l R).sup
          (fun Q => Kakeya.maxDensity (actualDescendantsW95 A U.cover.assign l m Q)
            (fun W => (U.cover.tube m W).toConvexSpaceBody)) := by
    obtain ⟨parent, hparent, hpartition⟩ := hdescendant_partition A Y U hregular k l m hkl hlm hm
    obtain ⟨himage, hfibre, _, _⟩ := hpartition R hR
    let Q1 := actualDescendantsW95 A U.cover.assign k l R
    let Q2 := actualDescendantsW95 A U.cover.assign k m R
    let W1 := fun Q => (U.cover.tube l Q).toConvexSpaceBody
    let W2 := fun Q => (U.cover.tube m Q).toConvexSpaceBody
    change Q2.image parent = Q1 at himage
    have hQmem (a b : Nat) (hb : b <= M) (S : iota)
        (Q : iota) (hQ : Q ∈ actualDescendantsW95 A U.cover.assign a b S) :
        Q ∈ U.cover.indexSet b := by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
      exact U.cover.assign_mem b hb i (Finset.mem_filter.mp hi).1
    have hQ2ne : Q2.Nonempty := by
      have hRi : R ∈ A.image (U.cover.assign k) := (hregular.surjective k (by omega)) ▸ hR
      obtain ⟨i, hi, hiR⟩ := Finset.mem_image.mp hRi
      exact ⟨U.cover.assign m i, Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hiR⟩, rfl⟩⟩
    have hQ1ne : Q1.Nonempty := himage ▸ hQ2ne.image parent
    have hcontain : ∀ W ∈ Q2, W2 W <= W1 (parent W) := by
      intro W hW
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hW
      have hiA := (Finset.mem_filter.mp hi).1
      change (U.cover.tube m (U.cover.assign m i)).toConvexSpaceBody <=
        (U.cover.tube l (parent (U.cover.assign m i))).toConvexSpaceBody
      rw [hparent i hiA]
      have hnested (n : Nat) (hln : l <= n) (hn : n <= M) :
          (U.cover.tube n (U.cover.assign n i)).toConvexSpaceBody <=
            (U.cover.tube l (U.cover.assign l i)).toConvexSpaceBody := by
        induction n, hln using Nat.le_induction with
        | base => exact le_rfl
        | succ n hln ih => exact (U.cover.tube_nested n hn i hiA).trans (ih (by omega))
      exact hnested m hlm.le hm
    obtain ⟨u, hu⟩ : ∃ u : E, ‖u‖ = 1 := exists_norm_eq E zero_le_one
    let amb : Tube 4 E := Tube.ofMidpointDirection 4 0 u hu
    have hambmid : _root_.midpoint ℝ amb.x amb.y = 0 := by
      rw [midpoint_eq_smul_add]
      change (⅟(2 : ℝ)) • ((0 - (1 / 2 : ℝ) • u) + (0 + (1 / 2 : ℝ) • u)) = 0
      simp
    have hamb_ball : amb.carrier ⊆ Metric.closedBall (0 : E) 5 := by
      intro z hz
      have h := Tube.carrier_subset_closedBall_midpoint (E := E) amb hz
      rw [hambmid, Metric.mem_closedBall] at h
      rw [Metric.mem_closedBall]
      have h4 : ((4 : ℝ≥0) : ℝ) = 4 := by norm_num
      rw [h4] at h
      linarith
    have hball_amb : Metric.closedBall (0 : E) 4 ⊆ amb.carrier := by
      intro z hz
      rw [amb.carrier_eq]
      refine Set.mem_biUnion (midpoint_mem_segment amb.x amb.y) ?_
      rw [hambmid]
      simpa using hz
    let rho : Fin 3 -> ℝ≥0 := fun j => match j with
      | ⟨0, _⟩ => 4
      | ⟨1, _⟩ => Tube.gridScale delta M l
      | ⟨_ + 2, _⟩ => Tube.gridScale delta M m
    let tb : ∀ j : Fin 3, iota -> Tube (rho j) E := fun j => match j with
      | ⟨0, _⟩ => fun _ => amb
      | ⟨1, _⟩ => U.cover.tube l
      | ⟨_ + 2, _⟩ => U.cover.tube m
    let Q : Fin 3 -> Finset iota := fun j => match j with
      | ⟨0, _⟩ => {R}
      | ⟨1, _⟩ => Q1
      | ⟨_ + 2, _⟩ => Q2
    let proj : Fin 2 -> iota -> iota := fun j => match j with
      | ⟨0, _⟩ => fun _ => R
      | ⟨_ + 1, _⟩ => parent
    have hgap1 : 4 * rho 1 <= rho 0 := by
      change 4 * Tube.gridScale delta M l <= 4
      calc
        4 * Tube.gridScale delta M l <= 4 * 1 := mul_le_mul' le_rfl (Tube.gridScale_le_one hd1 M l)
        _ = 4 := by norm_num
    have hmaps : ∀ j : Fin 2, ∀ W ∈ Q j.succ, proj j W ∈ Q j.castSucc := by
      intro j
      fin_cases j
      · exact fun W hW => Finset.mem_singleton_self R
      · intro W hW
        change parent W ∈ Q1
        rw [← himage]
        exact Finset.mem_image_of_mem parent hW
    have hnest : ∀ j : Fin 2, ∀ W ∈ Q j.succ,
        (tb j.succ W).toConvexSpaceBody <= (tb j.castSucc (proj j W)).toConvexSpaceBody := by
      intro j
      fin_cases j
      · intro W hW
        change (U.cover.tube l W).toConvexSpaceBody <= amb.toConvexSpaceBody
        apply SetLike.coe_subset_coe.mpr
        exact (hregular.parent_ball l (by omega) W (hQmem k l (by omega) R W hW)).trans
          ((Metric.closedBall_subset_closedBall (by norm_num : (2 : ℝ) <= 4)).trans hball_amb)
      · exact hcontain
    have hball : ∀ j : Fin 3, ∀ W ∈ Q j, (tb j W).carrier ⊆ Metric.closedBall (0 : E) 5 := by
      intro j
      fin_cases j
      · exact fun W hW => hamb_ball
      · intro W hW
        exact (hregular.parent_ball l (by omega) W (hQmem k l (by omega) R W hW)).trans
          (Metric.closedBall_subset_closedBall (by norm_num))
      · intro W hW
        exact (hregular.parent_ball m hm W (hQmem k m hm R W hW)).trans
          (Metric.closedBall_subset_closedBall (by norm_num))
    have hne : ∀ j : Fin 2, (Q j.castSucc).Nonempty := by
      intro j
      fin_cases j
      · exact Finset.singleton_nonempty R
      · exact hQ1ne
    have hcard : ((Q 0).card : ℝ) <= 1 * (5 + 3) ^ (2 * Module.finrank ℝ E) := by
      change (({R} : Finset iota).card : ℝ) <= _
      rw [Finset.card_singleton, one_mul]
      exact_mod_cast one_le_pow₀ (by norm_num : (1 : ℝ) <= 5 + 3)
    have h := htwo rho (by norm_num [rho]) (by norm_num [rho])
      (Tube.gridScale_pos hd M m) hgap1 hgap tb Q proj hmaps hnest hcard hball hne
    rw [Fin.prod_univ_two] at h
    change Kakeya.maxDensity Q2 W2 <= ENNReal.ofReal Ctwo ^ (2 : Nat) *
      (Kakeya.MultiScaleSubmult.fibreDeltaMax Q1 W1 ({R} : Finset iota) (fun _ => R) *
        Kakeya.MultiScaleSubmult.fibreDeltaMax Q2 W2 Q1 parent) at h
    have hfirst : Kakeya.MultiScaleSubmult.fibreDeltaMax Q1 W1 ({R} : Finset iota) (fun _ => R) =
        Kakeya.maxDensity Q1 W1 := by
      unfold Kakeya.MultiScaleSubmult.fibreDeltaMax
      rw [Finset.sup_singleton]
      congr 1
      ext W
      simp
    have hlast : Kakeya.MultiScaleSubmult.fibreDeltaMax Q2 W2 Q1 parent =
        Q1.sup (fun S => Kakeya.maxDensity (actualDescendantsW95 A U.cover.assign l m S) W2) := by
      unfold Kakeya.MultiScaleSubmult.fibreDeltaMax
      apply Finset.sup_congr rfl
      intro S hS
      congr 1
      ext W
      simpa only [Finset.mem_filter] using Finset.ext_iff.mp (hfibre S hS) W
    rw [hfirst, hlast] at h
    simpa only [mul_assoc] using h
  have hactual_cf_composition {delta : ℝ≥0} (hd : 0 < delta) (hd1 : delta <= 1)
      {iota : Type uI} [DecidableEq iota]
      (A : Finset iota) (Y : iota -> ShadedTube delta E)
      (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
      (hregular : SourceRegularizedWorkingTowerW95 U Ctw Ccell)
      (k l m : Nat) (hkl : k < l) (hlm : l < m) (hm : m <= M)
      (hgap : 4 * Tube.gridScale delta M m <= Tube.gridScale delta M l)
      (R : iota) (hR : R ∈ U.cover.indexSet k) :
      actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k m R <=
        2 * ENNReal.ofReal Ctwo ^ (2 : Nat) *
          (U.cover.indexSet k).sup (actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k l) *
          (U.cover.indexSet l).sup (actualRelativeFrostmanW95 A U.cover.assign U.cover.tube l m) := by
    let D := actualDescendantsW95 A U.cover.assign
    let V := fun n Q => (U.cover.tube n Q).toConvexSpaceBody
    let v := fun n => volume (U.cover.tube n R).carrier
    let X := fun a b => (U.cover.indexSet a).sup (actualRelativeFrostmanW95 A U.cover.assign U.cover.tube a b)
    have hvpos (n : Nat) : 0 < v n := (Tube.volume_pos_and_lt_top
      (Tube.gridScale_pos hd M n) (Tube.gridScale_le_one hd1 M n) (U.cover.tube n R)).1
    have hvfinite (n : Nat) : v n < ⊤ := (Tube.volume_pos_and_lt_top
      (Tube.gridScale_pos hd M n) (Tube.gridScale_le_one hd1 M n) (U.cover.tube n R)).2
    have hcontained (a b : Nat) (hab : a <= b) (hb : b <= M) (S : iota) :
        ∀ W ∈ D a b S, V b W <= V a S := by
      intro W hW
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hW
      obtain ⟨hiA, hiS⟩ := Finset.mem_filter.mp hi
      have hnest (n : Nat) (han : a <= n) (hn : n <= M) :
          (U.cover.tube n (U.cover.assign n i)).toConvexSpaceBody <=
            (U.cover.tube a (U.cover.assign a i)).toConvexSpaceBody := by
        induction n, han using Nat.le_induction with
        | base => exact le_rfl
        | succ n han ih => exact (U.cover.tube_nested n hn i hiA).trans (ih (by omega))
      simpa only [hiS] using hnest b hab hb
    have hsum (a b : Nat) (S : iota) :
        (∑ W ∈ D a b S, volume (V b W).carrier) = ((D a b S).card : ℝ≥0∞) * v b := by
      calc
        (∑ W ∈ D a b S, volume (V b W).carrier) = ∑ W ∈ D a b S, v b :=
          Finset.sum_congr rfl (fun W hW => Tube.volume_carrier_eq_volume_carrier (U.cover.tube b W) (U.cover.tube b R))
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    have hmax (a b : Nat) (hab : a < b) (hb : b <= M) (S : iota) (hS : S ∈ U.cover.indexSet a) :
        Kakeya.maxDensity (D a b S) (V b) <= X a b * (((D a b S).card : ℝ≥0∞) * v b / v a) := by
      have h := (isFrostmanIn_frostmanConstIn (D a b S) (V b) (V a S)).maxDensity_le_of_carrier_subset
        (hcontained a b hab.le hb S)
      have hden : Kakeya.densityIn (D a b S) (V b) (V a S) = ((D a b S).card : ℝ≥0∞) * v b / v a := by
        rw [Kakeya.densityIn_of_all_le (hcontained a b hab.le hb S), hsum a b S]
        rw [show volume (V a S).carrier = v a from Tube.volume_carrier_eq_volume_carrier (U.cover.tube a S) (U.cover.tube a R)]
      rw [hden] at h
      exact h.trans (mul_le_mul' (Finset.le_sup
        (f := actualRelativeFrostmanW95 A U.cover.assign U.cover.tube a b) hS) le_rfl)
    have hQmem : ∀ Q ∈ D k l R, Q ∈ U.cover.indexSet l := by
      intro Q hQ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
      exact U.cover.assign_mem l (by omega) i (Finset.mem_filter.mp hi).1
    have hsup : (D k l R).sup (fun Q => Kakeya.maxDensity (D l m Q) (V m)) <=
        X l m * (2 * (hregular.countBand l m : ℝ≥0∞) * v m / v l) := by
      apply Finset.sup_le
      intro Q hQ
      have hn : ((D l m Q).card : ℝ≥0∞) <= 2 * (hregular.countBand l m : ℝ≥0∞) := by
        exact_mod_cast (hregular.count_upper l m hlm hm Q (hQmem Q hQ)).le
      calc
        Kakeya.maxDensity (D l m Q) (V m) <= X l m * (((D l m Q).card : ℝ≥0∞) * v m / v l) :=
          hmax l m hlm hm Q (hQmem Q hQ)
        _ <= _ := by gcongr
    have hn : ((D k l R).card : ℝ≥0∞) * (hregular.countBand l m : ℝ≥0∞) <=
        ((D k m R).card : ℝ≥0∞) := by
      obtain ⟨parent, hparent, hpartition⟩ := hdescendant_partition A Y U hregular k l m hkl hlm hm
      exact_mod_cast (hpartition R hR).2.2.1
    have hmaxTwo := hactual_two_scale hd hd1 A Y U hregular k l m hkl hlm hm hgap R hR
    have hmaxNormalized : Kakeya.maxDensity (D k m R) (V m) <=
        ENNReal.ofReal Ctwo ^ (2 : Nat) *
          (X k l * (((D k l R).card : ℝ≥0∞) * v l / v k)) *
          (X l m * (2 * (hregular.countBand l m : ℝ≥0∞) * v m / v l)) := by
      exact hmaxTwo.trans (mul_le_mul' (mul_le_mul' le_rfl (hmax k l hkl (by omega) R hR)) hsup)
    apply frostmanConstIn_le
    apply IsFrostmanIn.of_maxDensity_mul_volume_le (hcontained k m (by omega) hm R) (hvpos k).ne'
    change Kakeya.maxDensity (D k m R) (V m) * v k <=
      (2 * ENNReal.ofReal Ctwo ^ (2 : Nat) * X k l * X l m) *
        (∑ W ∈ D k m R, volume (V m W).carrier)
    rw [hsum k m R]
    calc
      Kakeya.maxDensity (D k m R) (V m) * v k <=
          (ENNReal.ofReal Ctwo ^ (2 : Nat) *
            (X k l * (((D k l R).card : ℝ≥0∞) * v l / v k)) *
            (X l m * (2 * (hregular.countBand l m : ℝ≥0∞) * v m / v l))) * v k :=
        mul_le_mul' hmaxNormalized le_rfl
      _ = (2 * ENNReal.ofReal Ctwo ^ (2 : Nat) * X k l * X l m) *
          (((D k l R).card : ℝ≥0∞) * (hregular.countBand l m : ℝ≥0∞) * v m) *
          (v l * (v l)⁻¹) * ((v k)⁻¹ * v k) := by simp only [div_eq_mul_inv]; ring
      _ = (2 * ENNReal.ofReal Ctwo ^ (2 : Nat) * X k l * X l m) *
          (((D k l R).card : ℝ≥0∞) * (hregular.countBand l m : ℝ≥0∞) * v m) := by
        rw [ENNReal.mul_inv_cancel (hvpos l).ne' (hvfinite l).ne,
          ENNReal.inv_mul_cancel (hvpos k).ne' (hvfinite k).ne]
        simp
      _ <= _ := mul_le_mul' le_rfl (mul_le_mul' hn le_rfl)
  have hCbound : ENNReal.ofReal Ctwo <= (C : ℝ≥0∞) := by
    exact ENNReal.coe_le_coe.mpr (le_max_right (1 : ℝ≥0) (Real.toNNReal Ctwo))
  have hparent : ∀ R ∈ U.cover.indexSet k,
      actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k m R <=
        2 * (C : ℝ≥0∞) ^ (2 : Nat) * actualRelativeCFArrayW97 U k l *
          actualRelativeCFArrayW97 U l m := by
    intro R hR
    refine (hactual_cf_composition hd hd1 A Y U hregular k l m hkl hlm hm hgap R hR).trans ?_
    change 2 * ENNReal.ofReal Ctwo ^ (2 : Nat) * actualRelativeCFArrayW97 U k l *
      actualRelativeCFArrayW97 U l m <= _
    gcongr
  exact ⟨hparent, Finset.sup_le hparent⟩

/-- A3: the crude exponent is relative-scale two; prefix CF uses the same
final count bands and exact nested assigned families. -/
theorem actual_relative_cf_crude_and_prefix_w97 (hdim : Module.finrank ℝ E = 3) :
    ∃ Cvol : ℝ≥0, 1 <= Cvol ∧
      ∀ {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}, 0 < delta -> delta <= 1 ->
      ∀ {A : Finset iota} {Y : iota -> ShadedTube delta E} {M : Nat} {Ccan Ctw Ccell : ℝ≥0}
        (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan),
        A.Nonempty -> SourceRegularizedWorkingTowerW95 U Ctw Ccell ->
        (∀ k l : Nat, k < l -> l <= M -> ∀ R ∈ U.cover.indexSet k,
          actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k l R <=
            (Cvol : ℝ≥0∞) * ((Tube.gridScale delta M k : ℝ≥0∞) /
              (Tube.gridScale delta M l : ℝ≥0∞)) ^ (2 : Nat)) ∧
        (∀ k m b : Nat, k < m -> m < b -> b <= M ->
          (∀ R ∈ U.cover.indexSet k,
            actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k m R <=
              2 * actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k b R) ∧
          actualRelativeCFArrayW97 U k m <= 4 * actualRelativeCFArrayW97 U k b) := by
  let Cvol : ℝ≥0 := max 1 (Tube.volume_le.C 3 / Tube.le_volume.c 3)
  refine ⟨Cvol, le_max_left _ _, ?_⟩
  intro iota inst delta hd hd1 A Y M Ccan Ctw Ccell U hA hregular
  have hrelative_crude {delta : ℝ≥0} (hd : 0 < delta) (hd1 : delta <= 1)
      {iota : Type uI} [DecidableEq iota]
      (A : Finset iota) (Y : iota -> ShadedTube delta E)
      (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
      (hregular : SourceRegularizedWorkingTowerW95 U Ctw Ccell)
      (k l : Nat) (hkl : k < l) (hl : l <= M) (R : iota) (hR : R ∈ U.cover.indexSet k) :
      1 <= actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k l R ∧
        actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k l R <=
          ((Tube.volume_le.C 3 : ℝ≥0∞) / (Tube.le_volume.c 3 : ℝ≥0∞)) *
            (((Tube.gridScale delta M k : ℝ≥0∞) / (Tube.gridScale delta M l : ℝ≥0∞)) ^ (2 : Nat)) := by
    let D := actualDescendantsW95 A U.cover.assign k l R
    have hRimage : R ∈ A.image (U.cover.assign k) := (hregular.surjective k (by omega)) ▸ hR
    obtain ⟨i0, hi0, hi0R⟩ := Finset.mem_image.mp hRimage
    have hD : D.Nonempty := ⟨U.cover.assign l i0, Finset.mem_image.mpr
      ⟨i0, Finset.mem_filter.mpr ⟨hi0, hi0R⟩, rfl⟩⟩
    have hcontained : ∀ Q ∈ D,
        (U.cover.tube l Q).toConvexSpaceBody <= (U.cover.tube k R).toConvexSpaceBody := by
      intro Q hQ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
      obtain ⟨hiA, hiR⟩ := Finset.mem_filter.mp hi
      have hnest : ∀ n, k <= n -> n <= M ->
          (U.cover.tube n (U.cover.assign n i)).toConvexSpaceBody <=
            (U.cover.tube k (U.cover.assign k i)).toConvexSpaceBody := by
        intro n hkn
        induction n, hkn using Nat.le_induction with
        | base => exact fun _ => le_rfl
        | succ n hkn ih =>
          intro hn
          exact (U.cover.tube_nested n hn i hiA).trans (ih (by omega))
      simpa only [hiR] using hnest l hkl.le hl
    obtain ⟨Q0, hQ0⟩ := hD
    let v := volume (U.cover.tube l Q0).carrier
    let P := (U.cover.tube k R).toConvexSpaceBody
    let V := fun Q => (U.cover.tube l Q).toConvexSpaceBody
    have hvol : ∀ Q ∈ D, volume (V Q).carrier = v := fun Q hQ =>
      Tube.volume_carrier_eq_volume_carrier (U.cover.tube l Q) (U.cover.tube l Q0)
    have hvl := Tube.volume_pos_and_lt_top (Tube.gridScale_pos hd M l)
      (Tube.gridScale_le_one hd1 M l) (U.cover.tube l Q0)
    have hvk := Tube.volume_pos_and_lt_top (Tube.gridScale_pos hd M k)
      (Tube.gridScale_le_one hd1 M k) (U.cover.tube k R)
    have hdensity : Kakeya.densityIn D V P = (D.card : ℝ≥0∞) * v / volume P.carrier := by
      rw [Kakeya.densityIn_of_all_le hcontained]
      congr 1
      calc
        (∑ i ∈ D, volume (V i).carrier) = ∑ i ∈ D, v := Finset.sum_congr rfl hvol
        _ = (D.card : ℝ≥0∞) * v := by rw [Finset.sum_const, nsmul_eq_mul]
    have hdensity_pos : 0 < Kakeya.densityIn D V P := by
      rw [hdensity]
      exact ENNReal.div_pos (mul_ne_zero
        (by exact_mod_cast (Finset.card_pos.mpr (show D.Nonempty from ⟨Q0, hQ0⟩)).ne') hvl.1.ne') hvk.2.ne
    have hCFvol : frostmanConstIn D V P <= volume P.carrier / v := by
      apply frostmanConstIn_le
      intro Q hQP
      have hcancel : volume P.carrier / v * Kakeya.densityIn D V P = (D.card : ℝ≥0∞) := by
        rw [hdensity, div_eq_mul_inv, div_eq_mul_inv]
        calc
          volume P.carrier * v⁻¹ * ((D.card : ℝ≥0∞) * v * (volume P.carrier)⁻¹) =
              (D.card : ℝ≥0∞) * (v * v⁻¹) * (volume P.carrier * (volume P.carrier)⁻¹) := by ring
          _ = (D.card : ℝ≥0∞) := by
            rw [ENNReal.mul_inv_cancel hvl.1.ne' hvl.2.ne,
              ENNReal.mul_inv_cancel hvk.1.ne' hvk.2.ne]
            simp
      rw [hcancel]
      exact Kakeya.densityIn_le_card D V Q
    refine ⟨(isFrostmanIn_frostmanConstIn D V P).one_le hdensity_pos, ?_⟩
    have hparentVolume : volume P.carrier <= (Tube.volume_le.C 3 : ℝ≥0∞) *
        ((Tube.gridScale delta M k : ℝ≥0∞) ^ (2 : Nat)) := by
      simpa only [hdim, Nat.reduceSub] using
        Tube.volume_le (Tube.gridScale_le_one hd1 M k) (U.cover.tube k R)
    have hchildVolume : (Tube.le_volume.c 3 : ℝ≥0∞) *
        ((Tube.gridScale delta M l : ℝ≥0∞) ^ (2 : Nat)) <= v := by
      simpa only [hdim, Nat.reduceSub] using Tube.le_volume (U.cover.tube l Q0)
    have hc0 : (Tube.le_volume.c 3 : ℝ≥0∞) ≠ 0 :=
      (ENNReal.coe_pos.mpr (Tube.le_volume.c_pos 3)).ne'
    calc
      actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k l R <= volume P.carrier / v := hCFvol
      _ <= ((Tube.volume_le.C 3 : ℝ≥0∞) * (Tube.gridScale delta M k : ℝ≥0∞) ^ (2 : Nat)) /
          ((Tube.le_volume.c 3 : ℝ≥0∞) * (Tube.gridScale delta M l : ℝ≥0∞) ^ (2 : Nat)) :=
        ENNReal.div_le_div hparentVolume hchildVolume
      _ = _ := by
        simp only [div_eq_mul_inv, ENNReal.mul_inv (Or.inl hc0) (Or.inl ENNReal.coe_ne_top),
          ENNReal.inv_pow, mul_pow]
        ring
  have hdescendant_partition {delta : ℝ≥0}
      {iota : Type uI} [DecidableEq iota]
      (A : Finset iota) (Y : iota -> ShadedTube delta E)
      (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
      (hregular : SourceRegularizedWorkingTowerW95 U Ctw Ccell)
      (k l m : Nat) (hkl : k < l) (hlm : l < m) (hm : m <= M) :
      ∃ parent : iota -> iota,
        (∀ i ∈ A, parent (U.cover.assign m i) = U.cover.assign l i) ∧
        ∀ R ∈ U.cover.indexSet k,
          (actualDescendantsW95 A U.cover.assign k m R).image parent =
            actualDescendantsW95 A U.cover.assign k l R ∧
          (∀ Q ∈ actualDescendantsW95 A U.cover.assign k l R,
            (actualDescendantsW95 A U.cover.assign k m R).filter (fun W => parent W = Q) =
              actualDescendantsW95 A U.cover.assign l m Q) ∧
          ((actualDescendantsW95 A U.cover.assign k l R).card : ℝ≥0) * hregular.countBand l m <=
            ((actualDescendantsW95 A U.cover.assign k m R).card : ℝ≥0) ∧
          ((actualDescendantsW95 A U.cover.assign k m R).card : ℝ≥0) <
            2 * ((actualDescendantsW95 A U.cover.assign k l R).card : ℝ≥0) * hregular.countBand l m := by
    let parent : iota -> iota := fun Q => if hQ : Q ∈ A.image (U.cover.assign m) then
      U.cover.assign l (Finset.mem_image.mp hQ).choose else Q
    have hparent : ∀ i ∈ A, parent (U.cover.assign m i) = U.cover.assign l i := by
      intro i hi
      have hj : U.cover.assign m i ∈ A.image (U.cover.assign m) := Finset.mem_image.mpr ⟨i, hi, rfl⟩
      dsimp only [parent]
      rw [dif_pos hj]
      exact U.cover.assign_eq_of_le hlm.le hm
        (Finset.mem_image.mp hj).choose_spec.1 hi (Finset.mem_image.mp hj).choose_spec.2
    refine ⟨parent, hparent, ?_⟩
    intro R hR
    let Dkm := actualDescendantsW95 A U.cover.assign k m R
    let Dkl := actualDescendantsW95 A U.cover.assign k l R
    let Dlm := actualDescendantsW95 A U.cover.assign l m
    have himage : Dkm.image parent = Dkl := by
      ext Q
      constructor
      · intro hQ
        obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hQ
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hW
        obtain ⟨hiA, hiR⟩ := Finset.mem_filter.mp hi
        rw [hparent i hiA]
        exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hiA, hiR⟩, rfl⟩
      · intro hQ
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
        obtain ⟨hiA, hiR⟩ := Finset.mem_filter.mp hi
        exact Finset.mem_image.mpr ⟨U.cover.assign m i,
          Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hiA, hiR⟩, rfl⟩, hparent i hiA⟩
    have hfibre : ∀ Q ∈ Dkl, Dkm.filter (fun W => parent W = Q) = Dlm Q := by
      intro Q hQ
      obtain ⟨i0, hi0, hi0Q⟩ := Finset.mem_image.mp hQ
      obtain ⟨hi0A, hi0R⟩ := Finset.mem_filter.mp hi0
      ext W
      constructor
      · intro hW
        obtain ⟨hW, hWQ⟩ := Finset.mem_filter.mp hW
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hW
        obtain ⟨hiA, hiR⟩ := Finset.mem_filter.mp hi
        have hiQ : U.cover.assign l i = Q := (hparent i hiA).symm.trans hWQ
        exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hiA, hiQ⟩, rfl⟩
      · intro hW
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hW
        obtain ⟨hiA, hiQ⟩ := Finset.mem_filter.mp hi
        have hiR : U.cover.assign k i = R :=
          (U.cover.assign_eq_of_le hkl.le (by omega) hiA hi0A (hiQ.trans hi0Q.symm)).trans hi0R
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hiA, hiR⟩, rfl⟩,
            (hparent i hiA).trans hiQ⟩
    have hQmem : ∀ Q ∈ Dkl, Q ∈ U.cover.indexSet l := by
      intro Q hQ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
      exact U.cover.assign_mem l (by omega) i (Finset.mem_filter.mp hi).1
    have hsum : (Dkm.card : ℝ≥0) = ∑ Q ∈ Dkl, ((Dlm Q).card : ℝ≥0) := by
      have hmaps : ∀ W ∈ Dkm, parent W ∈ Dkl := by
        intro W hW
        rw [← himage]
        exact Finset.mem_image.mpr ⟨W, hW, rfl⟩
      calc
        (Dkm.card : ℝ≥0) = ∑ Q ∈ Dkl, ((Dkm.filter (fun W => parent W = Q)).card : ℝ≥0) := by
          simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
            (Finset.sum_fiberwise_of_maps_to hmaps (fun _ => (1 : ℝ≥0))).symm
        _ = ∑ Q ∈ Dkl, ((Dlm Q).card : ℝ≥0) := Finset.sum_congr rfl (fun Q hQ => by rw [hfibre Q hQ])
    have hDkl : Dkl.Nonempty := by
      have hRimage : R ∈ A.image (U.cover.assign k) := (hregular.surjective k (by omega)) ▸ hR
      obtain ⟨i, hi, hiR⟩ := Finset.mem_image.mp hRimage
      exact ⟨U.cover.assign l i, Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hiR⟩, rfl⟩⟩
    refine ⟨himage, hfibre, ?_, ?_⟩
    · calc
        (Dkl.card : ℝ≥0) * hregular.countBand l m = ∑ Q ∈ Dkl, hregular.countBand l m := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ <= ∑ Q ∈ Dkl, ((Dlm Q).card : ℝ≥0) := Finset.sum_le_sum
          (fun Q hQ => hregular.count_lower l m hlm hm Q (hQmem Q hQ))
        _ = (Dkm.card : ℝ≥0) := hsum.symm
    · calc
        (Dkm.card : ℝ≥0) = ∑ Q ∈ Dkl, ((Dlm Q).card : ℝ≥0) := hsum
        _ < ∑ Q ∈ Dkl, 2 * hregular.countBand l m := by
          apply Finset.sum_lt_sum
          · exact fun Q hQ => (hregular.count_upper l m hlm hm Q (hQmem Q hQ)).le
          · obtain ⟨Q, hQ⟩ := hDkl
            exact ⟨Q, hQ, hregular.count_upper l m hlm hm Q (hQmem Q hQ)⟩
        _ = 2 * (Dkl.card : ℝ≥0) * hregular.countBand l m := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
  have hrelative_prefix {delta : ℝ≥0} (hd : 0 < delta) (hd1 : delta <= 1)
      {iota : Type uI} [DecidableEq iota]
      (A : Finset iota) (Y : iota -> ShadedTube delta E)
      (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
      (hregular : SourceRegularizedWorkingTowerW95 U Ctw Ccell)
      (k m b : Nat) (hkm : k < m) (hmb : m < b) (hb : b <= M)
      (R : iota) (hR : R ∈ U.cover.indexSet k) :
      actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k m R <=
        2 * actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k b R := by
    obtain ⟨parent, hparent, hpartition⟩ := hdescendant_partition A Y U hregular k m b hkm hmb hb
    obtain ⟨himage, hfibre, _, _⟩ := hpartition R hR
    let fine := actualDescendantsW95 A U.cover.assign k b R
    let out := actualDescendantsW95 A U.cover.assign k m R
    let V := fun Q => (U.cover.tube b Q).toConvexSpaceBody
    let W := fun Q => (U.cover.tube m Q).toConvexSpaceBody
    let K := (U.cover.tube k R).toConvexSpaceBody
    change fine.image parent = out at himage
    have hnested (a c : Nat) (hac : a <= c) (hc : c <= M) (i : iota) (hi : i ∈ A) :
        (U.cover.tube c (U.cover.assign c i)).toConvexSpaceBody <=
          (U.cover.tube a (U.cover.assign a i)).toConvexSpaceBody := by
      revert hc
      induction c, hac using Nat.le_induction with
      | base => exact fun _ => le_rfl
      | succ c hac ih =>
        intro hc
        exact (U.cover.tube_nested c hc i hi).trans (ih (by omega))
    have hmaps : ∀ Q ∈ fine, parent Q ∈ out := by
      intro Q hQ
      rw [← himage]
      exact Finset.mem_image.mpr ⟨Q, hQ, rfl⟩
    have hVW : ∀ Q ∈ fine, V Q <= W (parent Q) := by
      intro Q hQ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
      have hiA := (Finset.mem_filter.mp hi).1
      change (U.cover.tube b (U.cover.assign b i)).toConvexSpaceBody <=
        (U.cover.tube m (parent (U.cover.assign b i))).toConvexSpaceBody
      rw [hparent i hiA]
      exact hnested m b hmb.le hb i hiA
    have hWK : ∀ Q ∈ out, W Q <= K := by
      intro Q hQ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
      obtain ⟨hiA, hiR⟩ := Finset.mem_filter.mp hi
      simpa only [hiR] using hnested k m hkm.le (by omega) i hiA
    have hne : ∀ Q ∈ out, (fine.filter (fun P => parent P = Q)).Nonempty := by
      intro Q hQ
      rw [← himage] at hQ
      obtain ⟨P, hP, hPQ⟩ := Finset.mem_image.mp hQ
      exact ⟨P, Finset.mem_filter.mpr ⟨hP, hPQ⟩⟩
    have hQmem : ∀ Q ∈ out, Q ∈ U.cover.indexSet m := by
      intro Q hQ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
      exact U.cover.assign_mem m (by omega) i (Finset.mem_filter.mp hi).1
    let vb := volume (U.cover.tube b R).carrier
    let vm := volume (U.cover.tube m R).carrier
    have hdensity (Q : iota) (hQ : Q ∈ out) :
        Kakeya.densityIn (fine.filter (fun P => parent P = Q)) V (W Q) =
          ((actualDescendantsW95 A U.cover.assign m b Q).card : ℝ≥0∞) * vb / vm := by
      have hcontained : ∀ P ∈ fine.filter (fun P => parent P = Q), V P <= W Q := by
        intro P hP
        obtain ⟨hPf, hPQ⟩ := Finset.mem_filter.mp hP
        simpa only [hPQ] using hVW P hPf
      rw [Kakeya.densityIn_of_all_le hcontained]
      have hsum : (∑ P ∈ fine.filter (fun P => parent P = Q), volume (V P).carrier) =
          ((fine.filter (fun P => parent P = Q)).card : ℝ≥0∞) * vb := by
        calc
          (∑ P ∈ fine.filter (fun P => parent P = Q), volume (V P).carrier) =
              ∑ P ∈ fine.filter (fun P => parent P = Q), vb :=
            Finset.sum_congr rfl (fun P hP => Tube.volume_carrier_eq_volume_carrier
              (U.cover.tube b P) (U.cover.tube b R))
          _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
      rw [hsum, hfibre Q hQ]
      congr 1
      exact Tube.volume_carrier_eq_volume_carrier (U.cover.tube m Q) (U.cover.tube m R)
    have hunif : ∀ Q ∈ out, ∀ Q' ∈ out,
        Kakeya.densityIn (fine.filter (fun P => parent P = Q)) V (W Q) <=
          2 * Kakeya.densityIn (fine.filter (fun P => parent P = Q')) V (W Q') := by
      intro Q hQ Q' hQ'
      have hcountNN : ((actualDescendantsW95 A U.cover.assign m b Q).card : ℝ≥0) <=
          2 * ((actualDescendantsW95 A U.cover.assign m b Q').card : ℝ≥0) :=
        (hregular.count_upper m b hmb hb Q (hQmem Q hQ)).le.trans
          (mul_le_mul' le_rfl (hregular.count_lower m b hmb hb Q' (hQmem Q' hQ')))
      have hcount : ((actualDescendantsW95 A U.cover.assign m b Q).card : ℝ≥0∞) <=
          2 * ((actualDescendantsW95 A U.cover.assign m b Q').card : ℝ≥0∞) := by exact_mod_cast hcountNN
      rw [hdensity Q hQ, hdensity Q' hQ']
      calc
        ((actualDescendantsW95 A U.cover.assign m b Q).card : ℝ≥0∞) * vb / vm <=
            (2 * ((actualDescendantsW95 A U.cover.assign m b Q').card : ℝ≥0∞)) * vb / vm :=
          ENNReal.div_le_div_right (mul_le_mul' hcount le_rfl) vm
        _ = _ := by simp only [div_eq_mul_inv]; ring
    exact frostmanConstIn_le (isFrostmanIn_parents_of_uniform_fibres
      (q := fine) (out := out) (V := V) (W := W) (par := parent)
      (fib := fun Q => fine.filter (fun P => parent P = Q))
      (isFrostmanIn_frostmanConstIn fine V K)
      (fun Q hQ => (Tube.volume_pos_and_lt_top (Tube.gridScale_pos hd M b)
        (Tube.gridScale_le_one hd1 M b) (U.cover.tube b Q)).1)
      hmaps hVW hWK (fun _ => rfl) hne hunif)
  have hCvol : (Tube.volume_le.C 3 : ℝ≥0∞) / (Tube.le_volume.c 3 : ℝ≥0∞) <=
      (Cvol : ℝ≥0∞) := by
    rw [← ENNReal.coe_div (Tube.le_volume.c_pos 3).ne']
    exact ENNReal.coe_le_coe.mpr (le_max_right _ _)
  constructor
  · intro k l hkl hl R hR
    refine (hrelative_crude hd hd1 A Y U hregular k l hkl hl R hR).2.trans ?_
    exact mul_le_mul' hCvol le_rfl
  · intro k m b hkm hmb hb
    have hparent := hrelative_prefix hd hd1 A Y U hregular k m b hkm hmb hb
    refine ⟨hparent, Finset.sup_le (fun R hR => ?_)⟩
    calc
      actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k m R <=
          2 * actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k b R := hparent R hR
      _ <= 2 * actualRelativeCFArrayW97 U k b := mul_le_mul' le_rfl
        (Finset.le_sup (f := actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k b) hR)
      _ <= 4 * actualRelativeCFArrayW97 U k b := mul_le_mul' (by norm_num) le_rfl

/-- A4: the root set need not be a singleton; its actual line cap pays the top entry. -/
theorem actual_top_relative_cf_w97 (hdim : Module.finrank ℝ E = 3) :
    ∃ Croot : ℝ≥0, 1 <= Croot ∧
      ∀ {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}, 0 < delta -> delta <= 1 ->
      ∀ {A : Finset iota} {Y : iota -> ShadedTube delta E} {M : Nat} {Ccan Ctw Ccell : ℝ≥0}
        (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan),
        1 <= M -> A.Nonempty -> SourceRegularizedWorkingTowerW95 U Ctw Ccell ->
        (∀ i ∈ A, (Y i).carrier ⊆ Metric.closedBall 0 1) ->
        ∀ F0 : ℝ≥0∞,
          frostmanConstIn A (fun i => (Y i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall <= F0 ->
          ((U.cover.indexSet 0).card : ℝ≥0) <= Ctw ∧
          actualRelativeCFArrayW97 U 0 M <= (Croot : ℝ≥0∞) * (Ctw : ℝ≥0∞) * F0 := by
  let CrootENN : ℝ≥0∞ := 2 * (Tube.volume_le.C 3 : ℝ≥0∞) /
    volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier
  have hCrootFinite : CrootENN ≠ ⊤ := ENNReal.div_ne_top (by finiteness)
    (ConvexSpaceBody.closedUnitBall_volume_pos (E := E)).ne'
  let Croot : ℝ≥0 := max 1 CrootENN.toNNReal
  refine ⟨Croot, le_max_left _ _, ?_⟩
  intro iota inst delta hd hd1 A Y M Ccan Ctw Ccell U hM hA hregular hball F0 hCF
  have hrelative_top {delta : ℝ≥0} (hd : 0 < delta) (hd1 : delta <= 1)
      {iota : Type uI} [DecidableEq iota]
      (A : Finset iota) (Y : iota -> ShadedTube delta E)
      (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
      (hregular : SourceRegularizedWorkingTowerW95 U Ctw Ccell)
      (hball : ∀ i ∈ A, (Y i).carrier ⊆ Metric.closedBall 0 1)
      (F0 : ℝ≥0∞) (hCF : frostmanConstIn A (fun i => (Y i).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall <= F0)
      (R : iota) (hR : R ∈ U.cover.indexSet 0) :
      ((U.cover.indexSet 0).card : ℝ≥0) <= Ctw ∧
      actualRelativeFrostmanW95 A U.cover.assign U.cover.tube 0 M R <=
        (2 * (Tube.volume_le.C 3 : ℝ≥0∞) / volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier) *
          (Ctw : ℝ≥0∞) * F0 := by
    let roots := U.cover.indexSet 0
    let fibres := completeFibreW94 A (U.cover.assign 0)
    let V := fun i => (Y i).toConvexSpaceBody
    let P := (U.cover.tube 0 R).toConvexSpaceBody
    let v := volume (Y R).carrier
    let vB := volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier
    have hM : 0 < M := lt_of_lt_of_le Nat.zero_lt_one hM
    have hbottom : ∀ Q, actualDescendantsW95 A U.cover.assign 0 M Q = fibres Q := by
      intro Q
      ext i
      constructor
      · intro hi
        obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
        have hjA := (Finset.mem_filter.mp hj).1
        have hji' : j = i := (hregular.bottom_assign j hjA).symm.trans hji
        exact hji' ▸ hj
      · intro hi
        exact Finset.mem_image.mpr ⟨i, hi, hregular.bottom_assign i (Finset.mem_filter.mp hi).1⟩
    have hroots : (roots.card : ℝ≥0) <= Ctw := by
      obtain ⟨u, hu⟩ : ∃ u : E, ‖u‖ = 1 := exists_norm_eq E zero_le_one
      have hfilter : roots.filter (fun Q => liesInFiveDeltaLineTubeW94 (U.cover.tube 0 Q) 0 u) = roots := by
        apply Finset.filter_true_of_mem
        intro Q hQ x hx
        refine ⟨0, ?_⟩
        have hxball := hregular.parent_ball 0 (Nat.zero_le _) Q hQ hx
        have hx2 : dist x 0 <= 2 := Metric.mem_closedBall.mp hxball
        simpa only [zero_smul, zero_add, Tube.gridScale_zero, NNReal.coe_one, mul_one] using
          (show dist x 0 <= 5 by linarith)
      have hline := hregular.parent_line_ed 0 (Nat.zero_le _) 0 u hu
      change ((roots.filter (fun Q => liesInFiveDeltaLineTubeW94 (U.cover.tube 0 Q) 0 u)).card : ℝ≥0) <= Ctw at hline
      rwa [hfilter] at hline
    have hcount : ∀ Q ∈ roots, ((fibres Q).card : ℝ≥0) <= 2 * ((fibres R).card : ℝ≥0) := by
      intro Q hQ
      have hupper := (hregular.count_upper 0 M (by omega) le_rfl Q hQ).le
      have hlower := hregular.count_lower 0 M (by omega) le_rfl R hR
      rw [hbottom Q] at hupper
      rw [hbottom R] at hlower
      exact hupper.trans (mul_le_mul' le_rfl hlower)
    have hcountA : (A.card : ℝ≥0∞) <= 2 * (Ctw : ℝ≥0∞) * ((fibres R).card : ℝ≥0∞) := by
      have hNN : (A.card : ℝ≥0) <= 2 * Ctw * ((fibres R).card : ℝ≥0) := by
        calc
          (A.card : ℝ≥0) = ∑ Q ∈ roots, ((fibres Q).card : ℝ≥0) := by
            have hsum := (Finset.sum_fiberwise_of_maps_to (U.cover.assign_mem 0 (Nat.zero_le _))
              (fun _ => (1 : ℝ≥0))).symm
            simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
            refine hsum.trans (Finset.sum_congr rfl (fun Q hQ => ?_))
            congr 2
          _ <= ∑ Q ∈ roots, 2 * ((fibres R).card : ℝ≥0) := Finset.sum_le_sum hcount
          _ = (roots.card : ℝ≥0) * (2 * ((fibres R).card : ℝ≥0)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
          _ <= Ctw * (2 * ((fibres R).card : ℝ≥0)) := mul_le_mul' hroots le_rfl
          _ = 2 * Ctw * ((fibres R).card : ℝ≥0) := by ring
      exact_mod_cast hNN
    have hsum (D : Finset iota) : (∑ i ∈ D, volume (V i).carrier) = (D.card : ℝ≥0∞) * v := by
      calc
        (∑ i ∈ D, volume (V i).carrier) = ∑ i ∈ D, v := Finset.sum_congr rfl
          (fun i hi => Tube.volume_carrier_eq_volume_carrier (Y i).toTube (Y R).toTube)
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    have hdensityA : Kakeya.densityIn A V ConvexSpaceBody.closedUnitBall = (A.card : ℝ≥0∞) * v / vB := by
      rw [Kakeya.densityIn_of_all_le (fun i hi => hball i hi), hsum A]
    have hmaxA : Kakeya.maxDensity A V <= F0 * ((A.card : ℝ≥0∞) * v / vB) := by
      have h := ((isFrostmanIn_frostmanConstIn A V ConvexSpaceBody.closedUnitBall).mono hCF).maxDensity_le_of_carrier_subset
        (fun i hi => hball i hi)
      rwa [hdensityA] at h
    have hPvolume : volume P.carrier <= (Tube.volume_le.C 3 : ℝ≥0∞) := by
      have h := Tube.volume_le (Tube.gridScale_le_one hd1 M 0) (U.cover.tube 0 R)
      simpa only [hdim, Nat.reduceSub, Tube.gridScale_zero, ENNReal.coe_one, one_pow, mul_one] using h
    have hsub : fibres R ⊆ A := Finset.filter_subset _ _
    have hcontained : ∀ i ∈ fibres R, V i <= P := by
      intro i hi
      obtain ⟨hiA, hiR⟩ := Finset.mem_filter.mp hi
      simpa only [hiR] using U.cover.le_tube_assign 0 (Nat.zero_le _) i hiA
    have hPpos : 0 < volume P.carrier := (Tube.volume_pos_and_lt_top
      (Tube.gridScale_pos hd M 0) (Tube.gridScale_le_one hd1 M 0) (U.cover.tube 0 R)).1
    have hFr : IsFrostmanIn (fibres R) V P
        ((2 * (Tube.volume_le.C 3 : ℝ≥0∞) / vB) * (Ctw : ℝ≥0∞) * F0) := by
      apply IsFrostmanIn.of_maxDensity_mul_volume_le hcontained hPpos.ne'
      rw [hsum (fibres R)]
      calc
        Kakeya.maxDensity (fibres R) V * volume P.carrier <=
            (F0 * ((A.card : ℝ≥0∞) * v / vB)) * (Tube.volume_le.C 3 : ℝ≥0∞) :=
          mul_le_mul' ((Kakeya.maxDensity_mono V hsub).trans hmaxA) hPvolume
        _ <= (F0 * ((2 * (Ctw : ℝ≥0∞) * ((fibres R).card : ℝ≥0∞)) * v / vB)) *
            (Tube.volume_le.C 3 : ℝ≥0∞) := by gcongr
        _ = _ := by simp only [div_eq_mul_inv]; ring
    refine ⟨hroots, ?_⟩
    unfold actualRelativeFrostmanW95
    rw [hbottom R, frostmanConstIn_congr (fibres R)
      (fun i hi => hregular.bottom_tube i (hsub hi)) (U.cover.tube 0 R).toConvexSpaceBody]
    exact frostmanConstIn_le hFr
  have hCbound : CrootENN <= (Croot : ℝ≥0∞) := by
    rw [← ENNReal.coe_toNNReal hCrootFinite]
    exact ENNReal.coe_le_coe.mpr (le_max_right _ _)
  obtain ⟨i, hi⟩ := hA
  have hroot := (hrelative_top hd hd1 A Y U hregular hball F0 hCF
    (U.cover.assign 0 i) (U.cover.assign_mem 0 (Nat.zero_le _) i hi)).1
  refine ⟨hroot, Finset.sup_le (fun R hR => ?_)⟩
  refine (hrelative_top hd hd1 A Y U hregular hball F0 hCF R hR).2.trans ?_
  exact mul_le_mul' (mul_le_mul' hCbound le_rfl) le_rfl

/-- A5: literal finite stopping on ONE array; eta(0) is source eta_1. -/
theorem exists_same_array_stopping_w97
    (M N : Nat) (hM : 1 <= M) (hN : 1 <= N)
    (B Ecoef : ℝ≥0) (hB : 1 <= B) (hE : 1 <= Ecoef)
    (dCrude epsilon : ℝ) (hdCrude : 1 <= dCrude)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon < 1 / 2)
    (hNlarge : epsilon ^ (-2 : ℝ) <= (N : ℝ))
    (delta : ℝ≥0) (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (rho : Nat -> ℝ≥0) (hrho : ∀ k, k <= M -> 0 < rho k)
    (hrhoStrict : ∀ k l, k < l -> l <= M -> rho l < rho k)
    (eta : Nat -> ℝ) (heta : ∀ j, j <= N -> 0 < eta j)
    (hetaMono : ∀ j k, j <= k -> k <= N -> eta j <= eta k)
    (hetaTop : eta N <= epsilon)
    (hetaStep : ∀ j, j < N -> eta j <= epsilon / 2 * eta (j + 1))
    (hspanLower : delta <= rho M / rho 0)
    (hspanUpper : rho M / rho 0 <= delta ^ (epsilon ^ (2 : Nat)))
    (X : Nat -> Nat -> ℝ≥0∞)
    (hXone : ∀ k l, k < l -> l <= M -> 1 <= X k l)
    (hXfinite : ∀ k l, k < l -> l <= M -> X k l < ⊤)
    (hH1 : ∀ k l m, k < l -> l < m -> m <= M -> X k m <= (B : ℝ≥0∞) * X k l * X l m)
    (hH2 : ∀ k l, k < l -> l <= M -> X k l <= (B : ℝ≥0∞) *
      ((rho l : ℝ≥0∞) / (rho k : ℝ≥0∞)) ^ (-dCrude))
    (hH3 : X 0 M <= ((rho M : ℝ≥0∞) / (rho 0 : ℝ≥0∞)) ^ (-eta 0))
    (hH4 : ∀ a m b, a < m -> m < b -> b <= M -> X a m <= (Ecoef : ℝ≥0∞) * X a b)
    (hcalibration : (Ecoef : ℝ≥0∞) <= (delta : ℝ≥0∞) ^ (-epsilon ^ (2 : Nat) * eta 0 / 2)) :
    (∀ k, k < M -> X k M <= (B : ℝ≥0∞) ^ (N + 1) *
      (delta : ℝ≥0∞) ^ (-(dCrude + 1) * epsilon)) ∨
    ∃ a b J : Nat, a < b ∧ b <= M ∧ 1 <= J ∧ J <= N ∧
      rho b / rho a <= delta ^ epsilon ∧
      X a b <= ((rho b : ℝ≥0∞) / (rho a : ℝ≥0∞)) ^ (-eta (J - 1)) ∧
      (b < M -> X b M <= (B : ℝ≥0∞) ^ N *
        ((rho M : ℝ≥0∞) / (rho b : ℝ≥0∞)) ^ (-eta (J - 1))) ∧
      (∀ m, a < m -> m < b ->
        ((rho b : ℝ≥0∞) / (rho a : ℝ≥0∞)) ^ (1 - epsilon) <=
          (rho m : ℝ≥0∞) / (rho a : ℝ≥0∞) ->
        (rho m : ℝ≥0∞) / (rho a : ℝ≥0∞) <=
          ((rho b : ℝ≥0∞) / (rho a : ℝ≥0∞)) ^ epsilon ->
        ((rho b : ℝ≥0∞) / (rho m : ℝ≥0∞)) ^ (-eta J) < X m b) := by
  let t (k : Nat) : ℝ := Real.log (rho k : ℝ)
  let x (k l : Nat) : ℝ := Real.log (X k l).toReal
  let D : ℝ := -Real.log (delta : ℝ)
  let bcost : ℝ := Real.log (B : ℝ)
  let ecost : ℝ := Real.log (Ecoef : ℝ)
  have hdR : (0 : ℝ) < delta := hdelta
  have hdR1 : (delta : ℝ) < 1 := hdeltaOne
  have hD : 0 < D := neg_pos.mpr (Real.log_neg hdR hdR1)
  have hbR : (0 : ℝ) < B := lt_of_lt_of_le zero_lt_one hB
  have heR : (0 : ℝ) < Ecoef := lt_of_lt_of_le zero_lt_one hE
  have hb0 : 0 <= bcost := Real.log_nonneg hB
  have hrR (k : Nat) (hk : k <= M) : (0 : ℝ) < rho k := hrho k hk
  have ht (k l : Nat) (hkl : k < l) (hl : l <= M) : t l < t k :=
    Real.log_lt_log (hrR l hl) (hrhoStrict k l hkl hl)
  have hxpos (k l : Nat) (hkl : k < l) (hl : l <= M) : 0 < X k l :=
    lt_of_lt_of_le zero_lt_one (hXone k l hkl hl)
  have hlog_le {v w : ℝ≥0∞} (hv : 0 < v) (hvf : v < ⊤)
      (hw : 0 < w) (hwf : w < ⊤) :
      Real.log v.toReal <= Real.log w.toReal ↔ v <= w := by
    rw [Real.log_le_log_iff (ENNReal.toReal_pos hv.ne' hvf.ne)
      (ENNReal.toReal_pos hw.ne' hwf.ne), ENNReal.toReal_le_toReal hvf.ne hwf.ne]
  have hlog_mul {v w : ℝ≥0∞} (hv : 0 < v) (hvf : v < ⊤)
      (hw : 0 < w) (hwf : w < ⊤) :
      Real.log (v * w).toReal = Real.log v.toReal + Real.log w.toReal := by
    rw [ENNReal.toReal_mul, Real.log_mul (ENNReal.toReal_pos hv.ne' hvf.ne).ne'
      (ENNReal.toReal_pos hw.ne' hwf.ne).ne']
  have hlog_rpow {v : ℝ≥0∞} (hv : 0 < v) (hvf : v < ⊤) (q : ℝ) :
      Real.log (v ^ q).toReal = q * Real.log v.toReal := by
    rw [← ENNReal.toReal_rpow, Real.log_rpow (ENNReal.toReal_pos hv.ne' hvf.ne)]
  have hratioPos (k l : Nat) (hk : k <= M) (hl : l <= M) :
      0 < (rho l : ℝ≥0∞) / (rho k : ℝ≥0∞) := by
    exact ENNReal.div_pos (by exact_mod_cast (hrho l hl).ne') (by simp)
  have hratioFinite (k l : Nat) (hk : k <= M) (hl : l <= M) :
      (rho l : ℝ≥0∞) / (rho k : ℝ≥0∞) < ⊤ := by
    exact ENNReal.div_lt_top (by simp) (by exact_mod_cast (hrho k hk).ne')
  have hlog_ratio (k l : Nat) (hk : k <= M) (hl : l <= M) :
      Real.log (((rho l : ℝ≥0∞) / (rho k : ℝ≥0∞)).toReal) = t l - t k := by
    simp only [ENNReal.toReal_div, ENNReal.coe_toReal, Real.log_div
      (hrR l hl).ne' (hrR k hk).ne', t]
  have hlog_ratio_pow (k l : Nat) (hk : k <= M) (hl : l <= M) (q : ℝ) :
      Real.log ((((rho l : ℝ≥0∞) / (rho k : ℝ≥0∞)) ^ (-q)).toReal) =
        q * (t k - t l) := by
    rw [hlog_rpow (hratioPos k l hk hl) (hratioFinite k l hk hl), hlog_ratio k l hk hl]
    ring
  have hlog_delta_pow (q : ℝ) : Real.log (((delta : ℝ≥0∞) ^ q).toReal) = -q * D := by
    rw [hlog_rpow (by exact_mod_cast hdelta) (by simp)]
    simp only [ENNReal.coe_toReal, D]
    ring
  have hspan : epsilon ^ 2 * D <= t 0 - t M ∧ t 0 - t M <= D := by
    have hlo : (delta : ℝ) <= (rho M : ℝ) / rho 0 := by exact_mod_cast hspanLower
    have hhi : (rho M : ℝ) / rho 0 <= (delta : ℝ) ^ (epsilon ^ (2 : Nat)) := by
      exact_mod_cast hspanUpper
    have hlo' := Real.log_le_log hdR hlo
    have hhi' := Real.log_le_log (div_pos (hrR M le_rfl) (hrR 0 (Nat.zero_le _))) hhi
    rw [Real.log_div (hrR M le_rfl).ne' (hrR 0 (Nat.zero_le _)).ne'] at hlo' hhi'
    rw [Real.log_rpow hdR] at hhi'
    dsimp [t, D]
    constructor <;> nlinarith
  have h1 (k l m : Nat) (hkl : k < l) (hlm : l < m) (hm : m <= M) :
      x k m <= bcost + x k l + x l m := by
    have hpB : (0 : ℝ≥0∞) < B := by exact_mod_cast hbR
    have hfkl := hXfinite k l hkl (hlm.le.trans hm)
    have hflm := hXfinite l m hlm hm
    have h := (hlog_le (hxpos k m (hkl.trans hlm) hm) (hXfinite k m (hkl.trans hlm) hm)
      (ENNReal.mul_pos (ENNReal.mul_pos hpB.ne' (hxpos k l hkl (hlm.le.trans hm)).ne').ne'
        (hxpos l m hlm hm).ne') (by finiteness)).mpr (hH1 k l m hkl hlm hm)
    rw [hlog_mul (ENNReal.mul_pos hpB.ne' (hxpos k l hkl (hlm.le.trans hm)).ne')
      (by finiteness) (hxpos l m hlm hm) (hXfinite l m hlm hm),
      hlog_mul hpB (by simp) (hxpos k l hkl (hlm.le.trans hm))
        (hXfinite k l hkl (hlm.le.trans hm))] at h
    exact h
  have h2 (k l : Nat) (hkl : k < l) (hl : l <= M) :
      x k l <= bcost + dCrude * (t k - t l) := by
    have hpB : (0 : ℝ≥0∞) < B := by exact_mod_cast hbR
    have hrp : 0 < ((rho l : ℝ≥0∞) / (rho k : ℝ≥0∞)) ^ (-dCrude) :=
      ENNReal.rpow_pos (hratioPos k l (hkl.le.trans hl) hl)
        (hratioFinite k l (hkl.le.trans hl) hl).ne
    have hfinite : ((rho l : ℝ≥0∞) / (rho k : ℝ≥0∞)) ^ (-dCrude) < ⊤ := by
      exact lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero
        (hratioPos k l (hkl.le.trans hl) hl).ne' (hratioFinite k l (hkl.le.trans hl) hl).ne)
    have h := (hlog_le (hxpos k l hkl hl) (hXfinite k l hkl hl)
      (ENNReal.mul_pos hpB.ne' hrp.ne') (by finiteness)).mpr (hH2 k l hkl hl)
    rw [hlog_mul hpB (by simp) hrp hfinite, hlog_ratio_pow k l (hkl.le.trans hl) hl] at h
    exact h
  have h3 : x 0 M <= eta 0 * (t 0 - t M) := by
    have hp : 0 < ((rho M : ℝ≥0∞) / (rho 0 : ℝ≥0∞)) ^ (-eta 0) :=
      ENNReal.rpow_pos (hratioPos 0 M (Nat.zero_le _) le_rfl)
        (hratioFinite 0 M (Nat.zero_le _) le_rfl).ne
    have hf : ((rho M : ℝ≥0∞) / (rho 0 : ℝ≥0∞)) ^ (-eta 0) < ⊤ :=
      lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero
        (hratioPos 0 M (Nat.zero_le _) le_rfl).ne' (hratioFinite 0 M (Nat.zero_le _) le_rfl).ne)
    have h := (hlog_le (hxpos 0 M hM le_rfl) (hXfinite 0 M hM le_rfl) hp hf).mpr hH3
    rwa [hlog_ratio_pow 0 M (Nat.zero_le _) le_rfl] at h
  have h4 (a m b : Nat) (ham : a < m) (hmb : m < b) (hb : b <= M) :
      x a m <= ecost + x a b := by
    have hpE : (0 : ℝ≥0∞) < Ecoef := by exact_mod_cast heR
    have hp := hxpos a b (ham.trans hmb) hb
    have hf := hXfinite a b (ham.trans hmb) hb
    have h := (hlog_le (hxpos a m ham (hmb.le.trans hb))
      (hXfinite a m ham (hmb.le.trans hb))
      (ENNReal.mul_pos hpE.ne' hp.ne') (by finiteness)).mpr (hH4 a m b ham hmb hb)
    rw [hlog_mul hpE (by simp) hp hf] at h
    exact h
  have hcal : ecost <= epsilon ^ 2 * eta 0 / 2 * D := by
    have hpD : (0 : ℝ≥0∞) < delta := by exact_mod_cast hdelta
    have hf : (delta : ℝ≥0∞) ^ (-epsilon ^ (2 : Nat) * eta 0 / 2) < ⊤ :=
      lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero hpD.ne' (by simp))
    have h := (hlog_le (by exact_mod_cast heR) (by simp)
      (ENNReal.rpow_pos hpD (by simp)) hf).mpr hcalibration
    rw [hlog_delta_pow] at h
    simp only [ENNReal.coe_toReal] at h
    dsimp [ecost]
    nlinarith only [h]
  have hengine :
      (∀ k, k < M -> x k M <= ((N : ℝ) + 1) * bcost + (dCrude + 1) * epsilon * D) ∨
      ∃ a b J : Nat, a < b ∧ b <= M ∧ 1 <= J ∧ J <= N ∧
        epsilon * D <= t a - t b ∧
        x a b <= eta (J - 1) * (t a - t b) ∧
        (b < M -> x b M <= (N : ℝ) * bcost + eta (J - 1) * (t b - t M)) ∧
        (∀ m, a < m -> m < b ->
          epsilon * (t a - t b) <= t a - t m ->
          t a - t m <= (1 - epsilon) * (t a - t b) ->
          eta J * (t m - t b) < x m b) := by
    let Part (J : Nat) (c : Nat -> Nat) : Prop :=
      1 <= J ∧ J <= N ∧ c 0 = 0 ∧ c J = M ∧
      (∀ i, i <= J -> c i <= M) ∧
      (∀ i, i < J -> c i < c (i + 1) ∧
        epsilon ^ 2 * D <= t (c i) - t (c (i + 1)) ∧
        x (c i) (c (i + 1)) <= eta (J - 1) * (t (c i) - t (c (i + 1))))
    have hstart : ∃ c, Part 1 c := by
      refine ⟨fun i => if i = 0 then 0 else M, le_rfl, hN, ?_, ?_, ?_, ?_⟩
      · simp
      · simp
      · intro i hi
        dsimp only
        split_ifs <;> omega
      · intro i hi
        have hi0 : i = 0 := by omega
        subst i
        simpa using And.intro (show 0 < M by omega) (And.intro hspan.1 h3)
    let J := Nat.findGreatest (fun j => ∃ c, Part j c) N
    obtain ⟨c, hc⟩ := Nat.findGreatest_spec (P := fun j => ∃ c, Part j c) hN hstart
    change Part J c at hc
    obtain ⟨hJ, hJN, hc0, hcJ, hcM, hcp⟩ := hc
    have hmax (K : Nat) (hKN : K <= N) (c' : Nat -> Nat) (hc' : Part K c') : K <= J :=
      Nat.le_findGreatest hKN ⟨c', hc'⟩
    have hcmono (i j : Nat) (hij : i <= j) (hj : j <= J) : c i <= c j := by
      induction j, hij using Nat.le_induction with
      | base => exact le_rfl
      | succ j hij ih =>
        exact (ih (by omega)).trans (hcp j (by omega)).1.le
    have hct (i : Nat) (hi : i <= J) : t (c i) - t M <= D := by
      have hzero : 0 <= c i := Nat.zero_le _
      have hle : t (c i) <= t 0 := by
        rcases eq_or_lt_of_le hzero with hz | hz
        · simp only [← hz, le_refl]
        · exact (ht 0 (c i) hz (hcM i hi)).le
      linarith [hspan.2]
    have hetaJ : 0 < eta (J - 1) := heta (J - 1) (by omega)
    have hetaJE : eta (J - 1) <= epsilon :=
      (hetaMono (J - 1) N (by omega) le_rfl).trans hetaTop
    have htail : ∀ n i : Nat, i + n = J -> 0 < n ->
        x (c i) M <= (n : ℝ) * bcost + eta (J - 1) * (t (c i) - t M) := by
      intro n
      induction n with
      | zero => intro i hi hn; omega
      | succ n ih =>
        intro i hi hn
        have hiJ : i < J := by omega
        by_cases hn0 : n = 0
        · subst n
          have hei : c (i + 1) = M := by rw [show i + 1 = J by omega, hcJ]
          have hentry := (hcp i hiJ).2.2
          rw [hei] at hentry
          norm_num only [Nat.cast_one, one_mul]
          linarith only [hentry, hb0]
        · have hin : i + 1 + n = J := by omega
          have hrec := ih (i + 1) hin (by omega)
          have hnext : c (i + 1) < M := by
            calc c (i + 1) < c (i + 1 + 1) := (hcp (i + 1) (by omega)).1
                 _ <= c J := hcmono _ _ (by omega) le_rfl
                 _ = M := hcJ
          have hcomp := h1 (c i) (c (i + 1)) M (hcp i hiJ).1 hnext le_rfl
          have hentry := (hcp i hiJ).2.2
          simp only [Nat.cast_succ]
          nlinarith only [hcomp, hentry, hrec]
    by_cases hlong : ∃ j, j < J ∧ epsilon * D <= t (c j) - t (c (j + 1))
    · obtain ⟨j, hj, hjlong⟩ := hlong
      have hcount : (J : ℝ) * epsilon ^ 2 * D + (epsilon - epsilon ^ 2) * D <= D := by
        have hsum := Finset.sum_le_sum (s := Finset.range J)
          (f := fun i => epsilon ^ 2 * D + if i = j then (epsilon - epsilon ^ 2) * D else 0)
          (g := fun i => t (c i) - t (c (i + 1))) (by
            intro i hi
            have hiJ := Finset.mem_range.mp hi
            by_cases hij : i = j
            · subst i
              simp only [ite_true]
              nlinarith only [hjlong]
            · simp only [if_neg hij, add_zero]
              exact (hcp i hiJ).2.1)
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr hj),
          Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_range_sub', hc0, hcJ] at hsum
        nlinarith only [hsum, hspan.2]
      have hJltN : J < N := by
        have hep2 : 0 < epsilon ^ (2 : Nat) := pow_pos hepsilon _
        have hlarge : 1 <= (N : ℝ) * epsilon ^ (2 : Nat) := by
          have hn := hNlarge
          rw [Real.rpow_neg hepsilon.le, Real.rpow_two] at hn
          have hmul := mul_le_mul_of_nonneg_right hn hep2.le
          rwa [inv_mul_cancel₀ hep2.ne'] at hmul
        have hepSub : 0 < epsilon - epsilon ^ (2 : Nat) := by
          nlinarith only [hepsilon, hepsilonHalf]
        have hstrict : (J : ℝ) * epsilon ^ (2 : Nat) < 1 := by
          have hpos := mul_pos hepSub hD
          nlinarith only [hcount, hpos, hD]
        exact_mod_cast (show (J : ℝ) < N by nlinarith only [hstrict, hlarge, hep2])
      have hfail : ∀ m, c j < m -> m < c (j + 1) ->
          epsilon * (t (c j) - t (c (j + 1))) <= t (c j) - t m ->
          t (c j) - t m <= (1 - epsilon) * (t (c j) - t (c (j + 1))) ->
          eta J * (t m - t (c (j + 1))) < x m (c (j + 1)) := by
        intro m hjm hmj hwinL hwinU
        by_contra hnot
        have hsecond : x m (c (j + 1)) <= eta J * (t m - t (c (j + 1))) :=
          le_of_not_gt hnot
        have hlen : 0 < t (c j) - t (c (j + 1)) :=
          sub_pos.mpr (ht (c j) (c (j + 1)) (hcp j hj).1 (hcM (j + 1) (by omega)))
        have hetaNext : 0 < eta J := heta J hJN
        have hgap := hetaStep (J - 1) (by omega)
        rw [Nat.sub_add_cancel hJ] at hgap
        have he0 := hetaMono 0 J (Nat.zero_le _) hJN
        have heold := hetaMono (J - 1) J (by omega) hJN
        have hcal' : ecost <= epsilon / 2 * eta J * (t (c j) - t (c (j + 1))) := by
          calc ecost <= epsilon ^ 2 * eta 0 / 2 * D := hcal
               _ <= epsilon ^ 2 * eta J / 2 * D := by gcongr
               _ = epsilon / 2 * eta J * (epsilon * D) := by ring
               _ <= epsilon / 2 * eta J * (t (c j) - t (c (j + 1))) := by gcongr
        have hfirst : x (c j) m <= eta J * (t (c j) - t m) := by
          have hpref := h4 (c j) m (c (j + 1)) hjm hmj (hcM (j + 1) (by omega))
          have hentry := (hcp j hj).2.2
          have hgap' := mul_le_mul_of_nonneg_right hgap hlen.le
          have hwin' := mul_le_mul_of_nonneg_left hwinL hetaNext.le
          nlinarith only [hpref, hentry, hgap', hwin', hcal']
        have hnewL : epsilon ^ 2 * D <= t (c j) - t m := by
          have h := mul_le_mul_of_nonneg_left hjlong hepsilon.le
          nlinarith only [h, hwinL]
        have hnewR : epsilon ^ 2 * D <= t m - t (c (j + 1)) := by
          have h := mul_le_mul_of_nonneg_left hjlong hepsilon.le
          nlinarith only [h, hwinU]
        let c' (i : Nat) := if i <= j then c i else if i = j + 1 then m else c (i - 1)
        have hleft (i : Nat) (hi : i <= j) : c' i = c i := by simp [c', hi]
        have hmid : c' (j + 1) = m := by simp [c']
        have hright (i : Nat) (hi : j + 1 < i) : c' i = c (i - 1) := by
          simp [c', show ¬ i <= j by omega, show i ≠ j + 1 by omega]
        have hnew : Part (J + 1) c' := by
          refine ⟨by omega, by omega, ?_, ?_, ?_, ?_⟩
          · rw [hleft 0 (Nat.zero_le _), hc0]
          · rw [hright (J + 1) (by omega), Nat.add_sub_cancel, hcJ]
          · intro i hi
            by_cases hij : i <= j
            · rw [hleft i hij]
              exact hcM i (by omega)
            · by_cases hi1 : i = j + 1
              · subst i
                rw [hmid]
                exact hmj.le.trans (hcM (j + 1) (by omega))
              · rw [hright i (by omega)]
                exact hcM (i - 1) (by omega)
          · intro i hi
            simp only [Nat.add_sub_cancel]
            by_cases hij : i < j
            · rw [hleft i hij.le, hleft (i + 1) (by omega)]
              obtain ⟨hp, hl, hx⟩ := hcp i (by omega)
              refine ⟨hp, hl, hx.trans ?_⟩
              exact mul_le_mul_of_nonneg_right heold
                (sub_nonneg.mpr (ht (c i) (c (i + 1)) hp (hcM (i + 1) (by omega))).le)
            · by_cases hijEq : i = j
              · subst i
                rw [hleft j le_rfl, hmid]
                exact ⟨hjm, hnewL, hfirst⟩
              · by_cases hi1 : i = j + 1
                · subst i
                  rw [hmid, hright (j + 1 + 1) (by omega)]
                  simp only [Nat.add_sub_cancel]
                  exact ⟨hmj, hnewR, hsecond⟩
                · rw [hright i (by omega), hright (i + 1) (by omega), Nat.add_sub_cancel]
                  have hei : i - 1 + 1 = i := by omega
                  obtain ⟨hp, hl, hx⟩ := hcp (i - 1) (by omega)
                  rw [hei] at hp hl hx
                  refine ⟨hp, hl, hx.trans ?_⟩
                  exact mul_le_mul_of_nonneg_right heold
                    (sub_nonneg.mpr (ht (c (i - 1)) (c i) hp (hcM i (by omega))).le)
        have hbad := hmax (J + 1) (by omega) c' hnew
        omega
      right
      refine ⟨c j, c (j + 1), J, (hcp j hj).1, hcM (j + 1) (by omega),
        hJ, hJN, hjlong, (hcp j hj).2.2, ?_, hfail⟩
      intro hb
      have hj1 : j + 1 < J := by
        by_contra h
        have he : j + 1 = J := by omega
        rw [he, hcJ] at hb
        omega
      have h := htail (J - (j + 1)) (j + 1) (by omega) (by omega)
      have hn : ((J - (j + 1) : Nat) : ℝ) <= N := by exact_mod_cast (show J - (j + 1) <= N by omega)
      nlinarith only [h, mul_le_mul_of_nonneg_right hn hb0]
    · left
      intro k hk
      let j := Nat.findGreatest (fun i => c i <= k) J
      have hjc : c j <= k := Nat.findGreatest_spec (P := fun i => c i <= k)
        (Nat.zero_le J) (by simpa only [hc0] using Nat.zero_le k)
      have hjle : j <= J := Nat.findGreatest_le _
      have hj : j < J := by
        by_contra h
        have he : j = J := by omega
        rw [he, hcJ] at hjc
        omega
      have hkc : k < c (j + 1) := by
        by_contra h
        have hnext := Nat.le_findGreatest (P := fun i => c i <= k)
          (show j + 1 <= J by omega) (le_of_not_gt h)
        change j + 1 <= j at hnext
        omega
      have hshort : t (c j) - t (c (j + 1)) < epsilon * D := by
        by_contra h
        exact hlong ⟨j, hj, le_of_not_gt h⟩
      have hpartial : t k - t (c (j + 1)) <= epsilon * D := by
        have htk : t k <= t (c j) := by
          rcases eq_or_lt_of_le hjc with he | he
          · rw [he]
          · exact (ht (c j) k he hk.le).le
        linarith
      have hcrude := h2 k (c (j + 1)) hkc (hcM (j + 1) (by omega))
      have hcrude' : x k (c (j + 1)) <= bcost + dCrude * epsilon * D := by
        have h := mul_le_mul_of_nonneg_left hpartial (by linarith : 0 <= dCrude)
        nlinarith only [hcrude, h]
      by_cases hend : j + 1 = J
      · rw [hend, hcJ] at hcrude'
        have hnb : 0 <= (N : ℝ) * bcost := mul_nonneg (Nat.cast_nonneg _) hb0
        have hed : 0 <= epsilon * D := (mul_pos hepsilon hD).le
        nlinarith only [hcrude', hnb, hed]
      · have hj1 : j + 1 < J := by omega
        have hnext : c (j + 1) < M := by
          calc c (j + 1) < c (j + 1 + 1) := (hcp (j + 1) hj1).1
               _ <= c J := hcmono _ _ (by omega) le_rfl
               _ = M := hcJ
        have hsub := htail (J - (j + 1)) (j + 1) (by omega) (by omega)
        have hcomp := h1 k (c (j + 1)) M hkc hnext le_rfl
        have hcost : ((J - (j + 1) : Nat) : ℝ) + 2 <= (N : ℝ) + 1 := by
          exact_mod_cast (show J - (j + 1) + 2 <= N + 1 by omega)
        have hcost' := mul_le_mul_of_nonneg_right hcost hb0
        have hspan' := hct (j + 1) (by omega)
        have hetaCost : eta (J - 1) * (t (c (j + 1)) - t M) <= epsilon * D := by
          calc eta (J - 1) * (t (c (j + 1)) - t M) <= eta (J - 1) * D := by gcongr
               _ <= epsilon * D := by gcongr
        nlinarith only [hcomp, hcrude', hsub, hcost', hetaCost]
  have hrpowPos (k l : Nat) (hk : k <= M) (hl : l <= M) (q : ℝ) :
      0 < ((rho l : ℝ≥0∞) / (rho k : ℝ≥0∞)) ^ q :=
    ENNReal.rpow_pos (hratioPos k l hk hl) (hratioFinite k l hk hl).ne
  have hrpowFinite (k l : Nat) (hk : k <= M) (hl : l <= M) (q : ℝ) :
      ((rho l : ℝ≥0∞) / (rho k : ℝ≥0∞)) ^ q < ⊤ :=
    lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero
      (hratioPos k l hk hl).ne' (hratioFinite k l hk hl).ne)
  have hBpos (n : Nat) : (0 : ℝ≥0∞) < (B : ℝ≥0∞) ^ n := by
    have hb : (0 : ℝ≥0∞) < B := by exact_mod_cast hbR
    exact pos_iff_ne_zero.mpr (pow_ne_zero n hb.ne')
  have hBlog (n : Nat) : Real.log (((B : ℝ≥0∞) ^ n).toReal) = (n : ℝ) * bcost := by
    rw [ENNReal.toReal_pow, Real.log_pow]
    rfl
  rcases hengine with hall | ⟨a, b, J, hab, hb, hJ, hJN, hlong, hmid, htail, hlow⟩
  · left
    intro k hk
    have hdpos : (0 : ℝ≥0∞) < delta := by exact_mod_cast hdelta
    have hp : 0 < (delta : ℝ≥0∞) ^ (-(dCrude + 1) * epsilon) :=
      ENNReal.rpow_pos hdpos (by simp)
    have hf : (delta : ℝ≥0∞) ^ (-(dCrude + 1) * epsilon) < ⊤ :=
      lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero hdpos.ne' (by simp))
    apply (hlog_le (hxpos k M hk le_rfl) (hXfinite k M hk le_rfl)
      (ENNReal.mul_pos (hBpos (N + 1)).ne' hp.ne') (by finiteness)).mp
    rw [hlog_mul (hBpos (N + 1)) (by finiteness) hp hf, hBlog, hlog_delta_pow]
    have h := hall k hk
    simp only [Nat.cast_add, Nat.cast_one]
    dsimp [x] at h
    nlinarith only [h]
  · right
    have ha : a <= M := hab.le.trans hb
    refine ⟨a, b, J, hab, hb, hJ, hJN, ?_, ?_, ?_, ?_⟩
    · apply NNReal.coe_le_coe.mp
      change (rho b : ℝ) / (rho a : ℝ) <= (delta : ℝ) ^ epsilon
      apply (Real.log_le_log_iff (div_pos (hrR b hb) (hrR a ha))
        (Real.rpow_pos_of_pos hdR epsilon)).mp
      rw [Real.log_div (hrR b hb).ne' (hrR a ha).ne', Real.log_rpow hdR]
      dsimp [t, D] at hlong
      nlinarith only [hlong]
    · apply (hlog_le (hxpos a b hab hb) (hXfinite a b hab hb)
        (hrpowPos a b ha hb _) (hrpowFinite a b ha hb _)).mp
      rwa [hlog_ratio_pow a b ha hb]
    · intro hbM
      apply (hlog_le (hxpos b M hbM le_rfl) (hXfinite b M hbM le_rfl)
        (ENNReal.mul_pos (hBpos N).ne' (hrpowPos b M hb le_rfl _).ne') (by
          exact ENNReal.mul_lt_top (by finiteness) (hrpowFinite b M hb le_rfl _))).mp
      rw [hlog_mul (hBpos N) (by finiteness) (hrpowPos b M hb le_rfl _)
        (hrpowFinite b M hb le_rfl _), hBlog, hlog_ratio_pow b M hb le_rfl]
      exact htail hbM
    · intro m ham hmb hwinL hwinU
      have hm : m <= M := hmb.le.trans hb
      have hwL := (hlog_le (hrpowPos a b ha hb (1 - epsilon))
        (hrpowFinite a b ha hb (1 - epsilon)) (hratioPos a m ha hm)
        (hratioFinite a m ha hm)).mpr hwinL
      have hwU := (hlog_le (hratioPos a m ha hm) (hratioFinite a m ha hm)
        (hrpowPos a b ha hb epsilon) (hrpowFinite a b ha hb epsilon)).mpr hwinU
      rw [hlog_rpow (hratioPos a b ha hb) (hratioFinite a b ha hb),
        hlog_ratio a b ha hb, hlog_ratio a m ha hm] at hwL hwU
      have hstrict := hlow m ham hmb (by nlinarith only [hwU]) (by nlinarith only [hwL])
      apply lt_of_not_ge
      intro hbad
      have h := (hlog_le (hxpos m b hmb hb) (hXfinite m b hmb hb)
        (hrpowPos m b hm hb _) (hrpowFinite m b hm hb _)).mpr hbad
      rw [hlog_ratio_pow m b hm hb] at h
      exact (not_lt_of_ge h) hstrict

end

end Kakeya.ml1Boot.TrialRestartW94

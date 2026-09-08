/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Unconditional.ConversionLogAbsorption
import Unconditional.DirectConversionStatement
import Unconditional.GeometryAdapters
import Kakeya.MultiScaleFac.GridUniformBand
import Kakeya.Tube.Dilate
import Unconditional.RelativeWeightedCore
import Unconditional.BalancedQuotientFrostman
import Unconditional.MergedClassFrostman
import Unconditional.CenteredUnitParent
import Unconditional.AtomCorePullback
import Unconditional.AtomMassFrostman
import Unconditional.WeightedTupleSelection
import Unconditional.FiniteParentRecords
import Unconditional.GeometricAtomInput
import Unconditional.OriginalAtomProjection
import Unconditional.AtomWeightLevel
import Unconditional.RestoredFineSupport
import Unconditional.GridCenteredParentCover
import Kakeya.DimensionThree.MainLemma2.ShadedDividingScales

/-!
# Finite Parent Preparation

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

open MeasureTheory
open scoped BigOperators Classical

namespace KakeyaLink

open Kakeya.Assouad Kakeya.Streamlined JointSelection

universe uI

/-- The actual finite-parent preparation required by the complete direct endpoint consumer. -/
theorem exists_finiteParentPreparation (m : ℕ) (hm : 0 < m)
    (alpha : ℝ) (halpha : 0 < alpha) :
    ∃ inputLoss dNorm : ℝ,
      0 < inputLoss ∧ 0 < dNorm ∧
      ∀ {delta : NNReal}, 0 < delta → (delta : ℝ) ≤ dNorm →
      ∀ {I : Type uI} (s : Finset I) (V : I → ShadedTube delta Kakeya.Point3),
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall (0 : Kakeya.Point3) 1) →
      ∀ {C : NNReal}, C ≤ ShadedTube.ssfUniformConst (Module.finrank ℝ Kakeya.Point3) →
      ∀ input : ShadedTube.ShadedUniformTubeSet s V (Tube.ssfGridLen delta) C,
        ENNReal.ofReal ((delta : ℝ) ^ inputLoss) ≤
          ShadedBody.fullness' s (fun i => (V i).toShadedBody) →
        input.tubeUniform.IsFrostmanAtEveryScale
          (ENNReal.ofReal ((delta : ℝ) ^ (-inputLoss))) →
      ∀ gridIndex : Fin (m + 1) → ℕ,
        0 < Tube.ssfGridLen delta →
        (∀ k, gridIndex k ≤ Tube.ssfGridLen delta) →
        (∀ k, (Tube.gridScale delta (Tube.ssfGridLen delta) (gridIndex k) : ℝ) ≤
          1 / (1024 * 200 * (32 * numinaRepresentativeDilation))) →
        ∃ selected : Finset I, ∃ refined : I → ShadedTube delta Kakeya.Point3,
        ∃ H : ENNReal,
        ∃ prepared : FiniteParentCoverData selected refined (m + 1) H,
          (∀ k, prepared.rho k =
            1024 * Tube.gridScale delta (Tube.ssfGridLen delta) (gridIndex k)) ∧
          selected.Nonempty ∧
          (∀ i ∈ selected, (refined i).carrier ⊆ Metric.closedBall 0 1) ∧
          (toTubeFamily selected (fun i => (refined i).toTube)).IsEssentiallyDistinct ∧
          H ≤ Kakeya.realRpowENN (delta : ℝ) (-2 * alpha) ∧
          Kakeya.realRpowENN (delta : ℝ) alpha ≤
            ShadedBody.fullness' selected (fun i => (refined i).toShadedBody) ∧
          volume (⋃ i ∈ selected, (refined i).shade) ≤ volume (⋃ i ∈ s, (V i).shade) ∧
          (∀ k, ∀ j ∈ prepared.parentSet k,
            ConvexSpaceBody.IsFrostmanIn
              (Tube.coverClass selected (prepared.assign k) j)
              (fun i => (refined i).toConvexSpaceBody)
              (prepared.parentTube k j).toConvexSpaceBody
              (Kakeya.realRpowENN (delta : ℝ) (-alpha))) := by
  classical
  have hFixedTreeUniform {I : Type uI} {delta : NNReal}
      (s : Finset I) (T : I → Tube delta Kakeya.Point3) (N : ℕ)
      (G : Tube.GridCoverSystem s T N) (hs : s.Nonempty) (C : NNReal)
      (hInj : ∀ k ≤ N, Set.InjOn (G.tube k) (G.indexSet k : Set I))
      (hOverlap : ∀ k ≤ N, ∀ W : Tube (Tube.gridScale delta N k) Kakeya.Point3,
        (((G.indexSet k).filter fun j => ∃ i ∈ s,
          (T i).toConvexSpaceBody ≤ (G.tube k j).toConvexSpaceBody ∧
          (T i).toConvexSpaceBody ≤ W.toConvexSpaceBody).card : NNReal) ≤ C)
      (C0 : ℝ) (hC0 : 0 < C0) (hRoot : ((G.indexSet 0).card : ℝ) ≤ C0) :
      ∃ selected : Finset I, selected ⊆ s ∧ selected.Nonempty ∧
        (s.card : ℝ) ≤
          C0 * ((⌊Real.logb 2 (s.card : ℝ)⌋₊ + 1 : ℝ) ^ N) * (selected.card : ℝ) ∧
        ∃ U : Tube.UniformTubeSet selected T N (max 2 C),
          U.cover.assign = G.assign ∧ U.cover.tube = G.tube ∧
          (∀ k ≤ N, U.cover.indexSet k ⊆ G.indexSet k) := by
    obtain ⟨selected, branch, parent, hsub, hcard, hParent, hAssign, hActive, hBand⟩ :=
      Tube.exists_pruned_subset_noroot_notop s N hs G.indexSet G.assign
        (fun k hk i hi => G.assign_mem k hk i hi)
        (fun k hk i j hi hj hij => G.nested k (by omega) i hi j hj hij)
        C0 hC0 hRoot
    have hden : 0 < C0 * ((⌊Real.logb 2 (s.card : ℝ)⌋₊ + 1 : ℝ) ^ N) :=
      mul_pos hC0 (pow_pos (by positivity) N)
    have hmain : (s.card : ℝ) ≤
        C0 * ((⌊Real.logb 2 (s.card : ℝ)⌋₊ + 1 : ℝ) ^ N) * (selected.card : ℝ) := by
      simpa only [mul_comm] using (div_le_iff₀ hden).mp hcard
    have hnonempty : selected.Nonempty := by
      by_contra he
      have hempty := Finset.not_nonempty_iff_eq_empty.mp he
      have hpositive : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
      simp only [hempty, Finset.card_empty, Nat.cast_zero, mul_zero] at hmain
      exact (not_le_of_gt hpositive) hmain
    have hTwo : (2 : NNReal) ≤ max 2 C := le_max_left _ _
    have hOne : (1 : NNReal) ≤ max 2 C := (by norm_num : (1 : NNReal) ≤ 2).trans hTwo
    let U : Tube.UniformTubeSet selected T N (max 2 C) := {
      cover := {
        indexSet := parent
        assign := G.assign
        tube := G.tube
        assign_mem := fun k hk i hi => hAssign k hk hi
        le_tube_assign := fun k hk i hi => G.le_tube_assign k hk i (hsub hi)
        nested := fun k hk i hi j hj hij => G.nested k hk i (hsub hi) j (hsub hj) hij
        tube_nested := fun k hk i hi => G.tube_nested k hk i (hsub hi)
      }
      branchingN := fun k => branch k
      tube_injOn := fun k hk =>
        Set.InjOn.mono (Finset.coe_subset.mpr (hParent k hk)) (hInj k hk)
      boundedOverlap := by
        intro k hk W
        have hf : (parent k).filter (fun j => ∃ i ∈ selected,
            (T i).toConvexSpaceBody ≤ (G.tube k j).toConvexSpaceBody ∧
            (T i).toConvexSpaceBody ≤ W.toConvexSpaceBody) ⊆
            (G.indexSet k).filter (fun j => ∃ i ∈ s,
            (T i).toConvexSpaceBody ≤ (G.tube k j).toConvexSpaceBody ∧
            (T i).toConvexSpaceBody ≤ W.toConvexSpaceBody) := by
          intro j hj
          obtain ⟨hj, i, hi, hbody⟩ := Finset.mem_filter.mp hj
          exact Finset.mem_filter.mpr ⟨hParent k hk hj, i, hsub hi, hbody⟩
        exact (show (_ : NNReal) ≤ _ from Nat.cast_le.mpr (Finset.card_le_card hf)).trans
          ((hOverlap k hk W).trans (le_max_right _ _))
      card_class_le := by
        intro k hk j hj
        have hb : ((Tube.coverClass selected (G.assign k) j).card : NNReal) ≤
            2 * (branch k : NNReal) := by
          exact_mod_cast (show (Tube.coverClass selected (G.assign k) j).card ≤
            2 * branch k from (hBand k hk j hj).2.le)
        exact hb.trans (mul_le_mul_of_nonneg_right hTwo (by positivity))
      le_card_class := by
        intro k hk j hj
        have hb : (branch k : NNReal) ≤
            ((Tube.coverClass selected (G.assign k) j).card : NNReal) := by
          exact_mod_cast (hBand k hk j hj).1
        apply hb.trans
        calc
          _ = 1 * ((Tube.coverClass selected (G.assign k) j).card : NNReal) := by rw [one_mul]
          _ ≤ _ := mul_le_mul_of_nonneg_right hOne (by positivity)
    }
    exact ⟨selected, hsub, hnonempty, hmain, U, rfl, rfl, hParent⟩
  have hRetainedUniform {I : Type uI} {delta : NNReal} {s selected : Finset I}
      {T : I → Tube delta Kakeya.Point3} {N : ℕ} {C L : NNReal}
      (U : Tube.UniformTubeSet s T N C) (hsub : selected ⊆ s)
      (hC : 1 ≤ C) (hL : 1 ≤ L)
      (hShare : ∀ k ≤ N, ∀ j ∈ selected.image (U.cover.assign k),
        ((Tube.coverClass s (U.cover.assign k) j).card : NNReal) ≤
          L * ((Tube.coverClass selected (U.cover.assign k) j).card : NNReal)) :
      ∃ U' : Tube.UniformTubeSet selected T N (C ^ 2 * L),
        (∀ k, U'.cover.indexSet k = selected.image (U.cover.assign k)) ∧
        U'.cover.assign = U.cover.assign ∧ U'.cover.tube = U.cover.tube ∧
        (∀ k ≤ N, ∀ A : ENNReal,
          (∀ j ∈ U.cover.indexSet k, ConvexSpaceBody.IsFrostmanIn
            (Tube.coverClass s (U.cover.assign k) j)
            (fun i => (T i).toConvexSpaceBody) (U.cover.tube k j).toConvexSpaceBody A) →
          ∀ j ∈ U'.cover.indexSet k, ConvexSpaceBody.IsFrostmanIn
            (Tube.coverClass selected (U'.cover.assign k) j)
            (fun i => (T i).toConvexSpaceBody) (U'.cover.tube k j).toConvexSpaceBody
            (A * (L : ENNReal))) := by
    have hCpos : 0 < C := zero_lt_one.trans_le hC
    have hLpos : 0 < L := zero_lt_one.trans_le hL
    have hCLpos : 0 < C * L := mul_pos hCpos hLpos
    have hCL : 1 ≤ C * L := one_le_mul_of_one_le_of_one_le hC hL
    have hCu : C ≤ C ^ 2 * L := by
      calc
        C = C * 1 := (mul_one _).symm
        _ ≤ C * (C * L) := mul_le_mul_of_nonneg_left hCL zero_le
        _ = _ := by ring
    have hCnew : 1 ≤ C ^ 2 * L := hC.trans hCu
    have hParent k (hk : k ≤ N) j (hj : j ∈ selected.image (U.cover.assign k)) :
        j ∈ U.cover.indexSet k := by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact U.cover.assign_mem k hk i (hsub hi)
    have hBand k (hk : k ≤ N) j (hj : j ∈ selected.image (U.cover.assign k)) :
        U.branchingN k / (C * L) ≤
            ((Tube.coverClass selected (U.cover.assign k) j).card : NNReal) ∧
        ((Tube.coverClass selected (U.cover.assign k) j).card : NNReal) ≤
          (C ^ 2 * L) * (U.branchingN k / (C * L)) := by
      constructor
      · apply (div_le_iff₀ hCLpos).mpr
        calc
          _ ≤ C * ((Tube.coverClass s (U.cover.assign k) j).card : NNReal) :=
            U.le_card_class k hk j (hParent k hk j hj)
          _ ≤ C * (L * ((Tube.coverClass selected (U.cover.assign k) j).card : NNReal)) :=
            mul_le_mul_of_nonneg_left (hShare k hk j hj) zero_le
          _ = _ := by ring
      · calc
          _ ≤ ((Tube.coverClass s (U.cover.assign k) j).card : NNReal) :=
            Nat.cast_le.mpr (Finset.card_le_card (Tube.coverClass_subset_of_subset hsub _ _))
          _ ≤ C * U.branchingN k := U.card_class_le k hk j (hParent k hk j hj)
          _ = _ := by field_simp
    obtain ⟨U', hIndex, hAssign, hTube, hBranch⟩ :=
      Kakeya.MultiScaleFac.exists_restrict_uniformTubeSet_of_supplied_band U hsub
        hCu (le_refl (C ^ 2 * L)) hCnew (fun k => U.branchingN k / (C * L)) hBand
    refine ⟨U', hIndex, funext hAssign, funext hTube, ?_⟩
    intro k hk A hFrostman j hj
    rw [hIndex] at hj
    rw [hAssign, hTube]
    refine (hFrostman j (hParent k hk j hj)).of_le_of_subset
      ?_ (Tube.coverClass_subset_of_subset hsub _ _) ?_
    · intro i hi
      obtain ⟨hi, hAssigni⟩ := Finset.mem_filter.mp hi
      have h := U.cover.le_tube_assign k hk i hi
      rwa [hAssigni] at h
    · change (∑ i ∈ Tube.coverClass s (U.cover.assign k) j, volume (T i).carrier) ≤ _
      rw [Tube.sum_volume_carrier_eq_card_mul T (T j),
        Tube.sum_volume_carrier_eq_card_mul T (T j)]
      have hShareENN : ((Tube.coverClass s (U.cover.assign k) j).card : ENNReal) ≤
          (L : ENNReal) * ((Tube.coverClass selected (U.cover.assign k) j).card : ENNReal) := by
        exact_mod_cast hShare k hk j hj
      calc
        _ ≤ ((L : ENNReal) * ((Tube.coverClass selected (U.cover.assign k) j).card : ENNReal)) *
            volume (T j).carrier := mul_le_mul_left hShareENN _
        _ = _ := by ring
  have hWeightedCoreCount {I : Type uI} (s initial : Finset I)
      (hsub : initial ⊆ s) (hi : initial.Nonempty) (N : ℕ) (assign : ℕ → I → I)
      (weight : I → ℝ) (b : ℝ) (hb : 0 < b) (B K : NNReal)
      (hB : 1 ≤ B) (hK : 1 ≤ K)
      (hWeight : ∀ i ∈ s, b ≤ weight i ∧ weight i ≤ (B : ℝ) * b)
      (hCard : (s.card : NNReal) ≤ K * (initial.card : NNReal)) :
      ∃ selected : Finset I, selected ⊆ initial ∧ selected.Nonempty ∧
        (∑ i ∈ initial, weight i) ≤ 2 * (∑ i ∈ selected, weight i) ∧
        (∀ k ≤ N, ∀ j ∈ selected.image (assign k),
          ((Tube.coverClass s (assign k) j).card : NNReal) ≤
            (2 * (N + 2 : NNReal) * B ^ 2 * K) *
              ((Tube.coverClass selected (assign k) j).card : NNReal)) := by
    have hBounds (t : Finset I) (ht : t ⊆ s) :
        b * (t.card : ℝ) ≤ ∑ i ∈ t, weight i ∧
        (∑ i ∈ t, weight i) ≤ (B : ℝ) * b * (t.card : ℝ) := by
      constructor
      · simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm] using
          Finset.sum_le_sum (s := t) (fun i hi => (hWeight i (ht hi)).1)
      · simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm] using
          Finset.sum_le_sum (s := t) (fun i hi => (hWeight i (ht hi)).2)
    have hPositive : 0 < ∑ i ∈ initial, weight i :=
      (mul_pos hb (show (0 : ℝ) < initial.card from by exact_mod_cast hi.card_pos)).trans_le
        (hBounds initial hsub).1
    have hNonneg i (hi : i ∈ s) : 0 ≤ weight i := hb.le.trans (hWeight i hi).1
    have hTotalPositive : 0 < ∑ i ∈ s, weight i := hPositive.trans_le
      (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ => hNonneg i hi))
    have hCardReal : (s.card : ℝ) ≤ (K : ℝ) * (initial.card : ℝ) := by
      exact_mod_cast hCard
    have hTotalRatio : (∑ i ∈ s, weight i) ≤
        (B : ℝ) * (K : ℝ) * (∑ i ∈ initial, weight i) := by
      calc
        _ ≤ (B : ℝ) * b * (s.card : ℝ) := (hBounds s (Finset.Subset.refl _)).2
        _ ≤ (B : ℝ) * b * ((K : ℝ) * (initial.card : ℝ)) := by gcongr
        _ = (B : ℝ) * (K : ℝ) * (b * (initial.card : ℝ)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hBounds initial hsub).1 (by positivity)
    obtain ⟨selected, hselected, hnonempty, hhalf, hcore⟩ :=
      DirectCenteredRoute.exists_relative_weighted_fiber_core_half
        (Finset.range (N + 1)) assign s initial hsub weight hNonneg hPositive
    refine ⟨selected, hselected, hnonempty, hhalf, ?_⟩
    intro k hk j hj
    have hNode := hcore k (Finset.mem_range.mpr (by omega)) j hj
    have hOrigBounds := hBounds (Tube.coverClass s (assign k) j) (Finset.filter_subset _ _)
    have hNewBounds := hBounds (Tube.coverClass selected (assign k) j)
      ((Finset.filter_subset _ _).trans (hselected.trans hsub))
    have hden : 0 < 2 * ((N : ℝ) + 2) * (∑ i ∈ s, weight i) := by positivity
    have hNode' : ((∑ i ∈ initial, weight i) /
        (2 * ((N : ℝ) + 2) * (∑ i ∈ s, weight i))) *
          (∑ i ∈ Tube.coverClass s (assign k) j, weight i) ≤
        ∑ i ∈ Tube.coverClass selected (assign k) j, weight i := by
      simpa only [Finset.card_range, Nat.cast_add, Nat.cast_one, add_assoc,
        show (1 : ℝ) + 1 = 2 by norm_num, Tube.coverClass] using hNode
    have hScaled := (div_le_iff₀ hden).mp
      (show ((∑ i ∈ initial, weight i) *
          (∑ i ∈ Tube.coverClass s (assign k) j, weight i)) /
          (2 * ((N : ℝ) + 2) * (∑ i ∈ s, weight i)) ≤
        ∑ i ∈ Tube.coverClass selected (assign k) j, weight i from by
          simpa only [div_mul_eq_mul_div] using hNode')
    have hReal : ((Tube.coverClass s (assign k) j).card : ℝ) ≤
        (2 * ((N : ℝ) + 2) * (B : ℝ) ^ 2 * (K : ℝ)) *
          ((Tube.coverClass selected (assign k) j).card : ℝ) := by
      apply le_of_mul_le_mul_left (a := (∑ i ∈ initial, weight i) * b) ?_
        (mul_pos hPositive hb)
      calc
        _ = (∑ i ∈ initial, weight i) *
            (b * ((Tube.coverClass s (assign k) j).card : ℝ)) := by ring
        _ ≤ (∑ i ∈ initial, weight i) *
            (∑ i ∈ Tube.coverClass s (assign k) j, weight i) :=
          mul_le_mul_of_nonneg_left hOrigBounds.1 hPositive.le
        _ ≤ (∑ i ∈ Tube.coverClass selected (assign k) j, weight i) *
            (2 * ((N : ℝ) + 2) * (∑ i ∈ s, weight i)) := hScaled
        _ ≤ ((B : ℝ) * b * ((Tube.coverClass selected (assign k) j).card : ℝ)) *
            (2 * ((N : ℝ) + 2) *
              ((B : ℝ) * (K : ℝ) * (∑ i ∈ initial, weight i))) := by
          apply mul_le_mul hNewBounds.2
            (mul_le_mul_of_nonneg_left hTotalRatio (by positivity))
            hden.le (by positivity)
        _ = _ := by ring
    exact_mod_cast hReal
  have hWeightedUniform {I : Type uI} {delta : NNReal}
      (s initial : Finset I) (hsub : initial ⊆ s) (hi : initial.Nonempty)
      (T : I → Tube delta Kakeya.Point3) (N : ℕ) (C : NNReal)
      (U : Tube.UniformTubeSet s T N C) (hC : 1 ≤ C)
      (weight : I → ℝ) (b : ℝ) (hb : 0 < b) (B K : NNReal)
      (hB : 1 ≤ B) (hK : 1 ≤ K)
      (hWeight : ∀ i ∈ s, b ≤ weight i ∧ weight i ≤ (B : ℝ) * b)
      (hCard : (s.card : NNReal) ≤ K * (initial.card : NNReal)) :
      let L : NNReal := 2 * (N + 2 : NNReal) * B ^ 2 * K
      ∃ selected : Finset I, selected ⊆ initial ∧ selected.Nonempty ∧
        (∑ i ∈ initial, weight i) ≤ 2 * (∑ i ∈ selected, weight i) ∧
        ∃ U' : Tube.UniformTubeSet selected T N (C ^ 2 * L),
          (∀ k, U'.cover.indexSet k = selected.image (U.cover.assign k)) ∧
          U'.cover.assign = U.cover.assign ∧ U'.cover.tube = U.cover.tube ∧
          (∀ k ≤ N, ∀ A : ENNReal,
            (∀ j ∈ U.cover.indexSet k, ConvexSpaceBody.IsFrostmanIn
              (Tube.coverClass s (U.cover.assign k) j)
              (fun i => (T i).toConvexSpaceBody) (U.cover.tube k j).toConvexSpaceBody A) →
            ∀ j ∈ U'.cover.indexSet k, ConvexSpaceBody.IsFrostmanIn
              (Tube.coverClass selected (U'.cover.assign k) j)
              (fun i => (T i).toConvexSpaceBody) (U'.cover.tube k j).toConvexSpaceBody
              (A * (L : ENNReal))) := by
    dsimp only
    obtain ⟨selected, hselected, hnonempty, hhalf, hShare⟩ :=
      hWeightedCoreCount s initial hsub hi N U.cover.assign weight b hb B K hB hK hWeight hCard
    have hL : 1 ≤ 2 * (N + 2 : NNReal) * B ^ 2 * K :=
      one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le
          (one_le_mul_of_one_le_of_one_le (by norm_num)
            (by exact_mod_cast (show 1 ≤ N + 2 by omega)))
          (one_le_pow₀ hB)) hK
    obtain ⟨U', hIndex, hAssign, hTube, hFr⟩ :=
      hRetainedUniform U (hselected.trans hsub) hC hL hShare
    exact ⟨selected, hselected, hnonempty, hhalf, U', hIndex, hAssign, hTube, hFr⟩
  have hGroupedQuotientFrostman {I : Type uI}
      (source retained : Finset I) (hsub : retained ⊆ source)
      (body : I → ConvexSpaceBody Kakeya.Point3)
      (oldParent coarseParent quotientMap : I → I)
      (oldAnchor : I → ConvexSpaceBody Kakeya.Point3)
      (newAnchor : ConvexSpaceBody Kakeya.Point3) (coarseLabel : I)
      (quotient : Finset I) (newBody : I → ConvexSpaceBody Kakeya.Point3)
      (A L Q oldVolume newVolume anchorVolume : ENNReal)
      (hAnchorVolume : anchorVolume ≠ 0)
      (hOldVolume : ∀ i ∈ source, volume (body i).carrier = oldVolume)
      (hBodyPositive : ∀ i ∈ source, 0 < volume (body i).carrier)
      (hOldAnchorVolume : ∀ a ∈ retained.image oldParent,
        volume (oldAnchor a).carrier = anchorVolume)
      (hOldInside : ∀ i ∈ source, body i ≤ oldAnchor (oldParent i))
      (hOldFrostman : ∀ a ∈ retained.image oldParent,
        ConvexSpaceBody.IsFrostmanIn (source.filter fun i => oldParent i = a)
          body (oldAnchor a) A)
      (hRetained : ∀ a ∈ retained.image oldParent,
        ((source.filter fun i => oldParent i = a).card : ENNReal) ≤
          L * ((retained.filter fun i => oldParent i = a).card : ENNReal))
      (hNewVolume : ∀ q ∈ quotient, volume (newBody q).carrier = newVolume)
      (hNewInside : ∀ q ∈ quotient, newBody q ≤ newAnchor)
      (hMap : ∀ i ∈ retained, coarseParent (oldParent i) = coarseLabel →
        quotientMap i ∈ quotient)
      (hCover : ∀ i ∈ retained, coarseParent (oldParent i) = coarseLabel →
        body i ≤ newBody (quotientMap i))
      (hSurj : ∀ q ∈ quotient,
        (retained.filter fun i => coarseParent (oldParent i) = coarseLabel ∧
          quotientMap i = q).Nonempty)
      (hBalanced : ∀ q ∈ quotient, ∀ q' ∈ quotient,
        ((retained.filter fun i => coarseParent (oldParent i) = coarseLabel ∧
          quotientMap i = q).card : ENNReal) ≤ Q *
        ((retained.filter fun i => coarseParent (oldParent i) = coarseLabel ∧
          quotientMap i = q').card : ENNReal)) :
      ConvexSpaceBody.IsFrostmanIn quotient newBody newAnchor
        (Q * (A * L * (volume newAnchor.carrier / anchorVolume))) := by
    let grouped := retained.filter fun i => coarseParent (oldParent i) = coarseLabel
    have hGroupedSub : grouped ⊆ retained := Finset.filter_subset _ _
    have hParentSub : grouped.image oldParent ⊆ retained.image oldParent :=
      Finset.image_subset_image hGroupedSub
    have hFiber (a : I) (ha : a ∈ grouped.image oldParent) :
        grouped.filter (fun i => oldParent i = a) =
          retained.filter (fun i => oldParent i = a) := by
      obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp ha
      have hlabel : coarseParent a = coarseLabel := by
        rw [← hia]
        exact (Finset.mem_filter.mp hi).2
      ext i
      simp only [grouped, Finset.mem_filter]
      constructor
      · exact fun h => ⟨h.1.1, h.2⟩
      · intro h
        exact ⟨⟨h.1, h.2 ▸ hlabel⟩, h.2⟩
    have hRetainedFrostman a (ha : a ∈ grouped.image oldParent) :
        ConvexSpaceBody.IsFrostmanIn (grouped.filter fun i => oldParent i = a)
          body (oldAnchor a) (A * L) := by
      rw [hFiber a ha]
      refine (hOldFrostman a (hParentSub ha)).of_le_of_subset ?_
        (Finset.filter_subset_filter _ hsub) ?_
      · intro i hi
        obtain ⟨hi, hia⟩ := Finset.mem_filter.mp hi
        simpa only [hia] using hOldInside i hi
      · have hSum (t : Finset I) (ht : t ⊆ source) :
            (∑ i ∈ t, volume (body i).carrier) = (t.card : ENNReal) * oldVolume := by
          rw [Finset.sum_congr rfl (fun i hi => hOldVolume i (ht hi)),
            Finset.sum_const, nsmul_eq_mul]
        rw [hSum _ (Finset.filter_subset _ _),
          hSum _ ((Finset.filter_subset _ _).trans hsub)]
        calc
          _ ≤ (L * ((retained.filter fun i => oldParent i = a).card : ENNReal)) * oldVolume :=
            mul_le_mul_left (hRetained a (hParentSub ha)) _
          _ = _ := by ring
    have hGroupedNew i (hi : i ∈ grouped) : body i ≤ newAnchor := by
      obtain ⟨hi, hlabel⟩ := Finset.mem_filter.mp hi
      exact (hCover i hi hlabel).trans (hNewInside _ (hMap i hi hlabel))
    have hMerged := DirectCenteredRoute.frostman_merge_equal_volume_anchors
      grouped oldParent body oldAnchor newAnchor (A * L) anchorVolume hAnchorVolume
      (fun a ha => hOldAnchorVolume a (hParentSub ha))
      (fun i hi => hOldInside i (hsub (hGroupedSub hi))) hGroupedNew hRetainedFrostman
    by_cases hNewZero : volume newAnchor.carrier = 0
    · exact ConvexSpaceBody.IsFrostmanIn.of_volume_eq_zero hNewZero
    have hQuotient := DirectCenteredRoute.frostman_balanced_quotient
      grouped body newAnchor newAnchor _ Q hMerged hGroupedNew hNewZero
      (fun i hi => hBodyPositive i (hsub (hGroupedSub hi))) quotient quotientMap newBody
      (fun i hi => hMap i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2)
      (fun i hi => hCover i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2)
      hNewInside (by simpa only [grouped, Finset.filter_filter] using hSurj)
      oldVolume newVolume (fun i hi => hOldVolume i (hsub (hGroupedSub hi))) hNewVolume
      (by simpa only [grouped, Finset.filter_filter] using hBalanced)
    simpa only [ENNReal.div_self hNewZero newAnchor.isCompact.measure_ne_top, mul_one] using hQuotient
  have hOriginalCoordinateQuotientFrostman {I : Type uI} {delta eta rho : NNReal}
      (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
      (source retained : Finset I) (hsub : retained ⊆ source)
      (T : I → Tube delta Kakeya.Point3) (N k : ℕ) (hk : k ≤ N) (C : NNReal)
      (U : Tube.UniformTubeSet source T N C) (A L Q : ENNReal)
      (hFrostman : ∀ a ∈ U.cover.indexSet k,
        ConvexSpaceBody.IsFrostmanIn (Tube.coverClass source (U.cover.assign k) a)
          (fun i => (T i).toConvexSpaceBody) (U.cover.tube k a).toConvexSpaceBody A)
      (coarseParent quotientMap : I → I) (coarseLabel : I)
      (quotient : Finset I) (newTube : I → Tube eta Kakeya.Point3)
      (newAnchor : Tube rho Kakeya.Point3)
      (hRetained : ∀ a ∈ retained.image (U.cover.assign k),
        ((Tube.coverClass source (U.cover.assign k) a).card : ENNReal) ≤
          L * ((Tube.coverClass retained (U.cover.assign k) a).card : ENNReal))
      (hNewInside : ∀ q ∈ quotient, (newTube q).toConvexSpaceBody ≤ newAnchor.toConvexSpaceBody)
      (hMap : ∀ i ∈ retained, coarseParent (U.cover.assign k i) = coarseLabel →
        quotientMap i ∈ quotient)
      (hCover : ∀ i ∈ retained, coarseParent (U.cover.assign k i) = coarseLabel →
        (T i).toConvexSpaceBody.homothety 0 (1 / 8) ≤ (newTube (quotientMap i)).toConvexSpaceBody)
      (hSurj : ∀ q ∈ quotient,
        (retained.filter fun i => coarseParent (U.cover.assign k i) = coarseLabel ∧
          quotientMap i = q).Nonempty)
      (hBalanced : ∀ q ∈ quotient, ∀ q' ∈ quotient,
        ((retained.filter fun i => coarseParent (U.cover.assign k i) = coarseLabel ∧
          quotientMap i = q).card : ENNReal) ≤ Q *
        ((retained.filter fun i => coarseParent (U.cover.assign k i) = coarseLabel ∧
          quotientMap i = q').card : ENNReal)) :
      ConvexSpaceBody.IsFrostmanIn quotient (fun q => (newTube q).toConvexSpaceBody)
        newAnchor.toConvexSpaceBody
        (512 * Q * A * L *
          (volume newAnchor.carrier / volume (U.cover.tube k coarseLabel).carrier)) := by
    have hr : (1 / 8 : ℝ) ≠ 0 := by norm_num
    have hFactor : ENNReal.ofReal |(1 / 8 : ℝ) ^ Module.finrank ℝ Kakeya.Point3| = 1 / 512 := by
      have hdim : Module.finrank ℝ Kakeya.Point3 = 3 := by simp
      rw [hdim, show |(1 / 8 : ℝ) ^ 3| = 1 / 512 by norm_num,
        ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num
    have hVolume (W : ConvexSpaceBody Kakeya.Point3) :
        volume (W.homothety 0 (1 / 8)).carrier = (1 / 512) * volume W.carrier := by
      rw [ConvexSpaceBody.volume_homothety, hFactor]
    have hAnchorPositive : 0 < volume (U.cover.tube k coarseLabel).carrier :=
      (Tube.volume_pos_and_lt_top (Tube.gridScale_pos hdelta N k)
        (Tube.gridScale_le_one hdeltaOne N k) _).1
    have hParent a (ha : a ∈ retained.image (U.cover.assign k)) : a ∈ U.cover.indexSet k := by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      exact U.cover.assign_mem k hk i (hsub hi)
    have hMain := hGroupedQuotientFrostman source retained hsub
      (fun i => (T i).toConvexSpaceBody.homothety 0 (1 / 8))
      (U.cover.assign k) coarseParent quotientMap
      (fun a => (U.cover.tube k a).toConvexSpaceBody.homothety 0 (1 / 8))
      newAnchor.toConvexSpaceBody coarseLabel quotient
      (fun q => (newTube q).toConvexSpaceBody) A L Q
      ((1 / 512) * volume (T coarseLabel).carrier) (volume (newTube coarseLabel).carrier)
      ((1 / 512) * volume (U.cover.tube k coarseLabel).carrier)
      (mul_ne_zero (by norm_num) hAnchorPositive.ne')
      (fun i _ => by rw [hVolume, Tube.volume_carrier_eq_volume_carrier (T i) (T coarseLabel)])
      (fun i _ => by
        rw [hVolume]
        exact ENNReal.mul_pos (by norm_num) (Tube.volume_pos_and_lt_top hdelta hdeltaOne (T i)).1.ne')
      (fun a _ => by
        rw [hVolume, Tube.volume_carrier_eq_volume_carrier (U.cover.tube k a)
          (U.cover.tube k coarseLabel)])
      (fun i hi => (ConvexSpaceBody.homothety_le_homothety_iff 0 hr).mpr
        (U.cover.le_tube_assign k hk i hi))
      (fun a ha => (ConvexSpaceBody.IsFrostmanIn.homothety 0 hr).mpr (hFrostman a (hParent a ha)))
      hRetained (fun q _ => Tube.volume_carrier_eq_volume_carrier (newTube q) (newTube coarseLabel))
      hNewInside hMap hCover hSurj hBalanced
    have hConst : Q * (A * L * (volume newAnchor.carrier /
        ((1 / 512) * volume (U.cover.tube k coarseLabel).carrier))) =
        512 * Q * A * L *
          (volume newAnchor.carrier / volume (U.cover.tube k coarseLabel).carrier) := by
      simp only [div_eq_mul_inv]
      rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
      norm_num
      ring
    rw [hConst] at hMain
    exact hMain
  have hActualDescendedQuotientFrostman {I : Type uI} {delta eta rho : NNReal}
      (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
      (source retained : Finset I) (hsub : retained ⊆ source)
      (T : I → Tube delta Kakeya.Point3) (N k : ℕ) (hk : k ≤ N) (C : NNReal)
      (U : Tube.UniformTubeSet source T N C) (A L Q : ENNReal)
      (hFrostman : ∀ a ∈ U.cover.indexSet k,
        ConvexSpaceBody.IsFrostmanIn (Tube.coverClass source (U.cover.assign k) a)
          (fun i => (T i).toConvexSpaceBody) (U.cover.tube k a).toConvexSpaceBody A)
      (coarseParent quotientMap descended : I → I) (coarseLabel : I)
      (newTube : I → Tube eta Kakeya.Point3) (newAnchor : Tube rho Kakeya.Point3)
      (hRetained : ∀ a ∈ retained.image (U.cover.assign k),
        ((Tube.coverClass source (U.cover.assign k) a).card : ENNReal) ≤
          L * ((Tube.coverClass retained (U.cover.assign k) a).card : ENNReal))
      (hDescended : ∀ i ∈ retained, descended (quotientMap i) = coarseParent (U.cover.assign k i))
      (hNewInside : ∀ q ∈ Tube.coverClass (retained.image quotientMap) descended coarseLabel,
        (newTube q).toConvexSpaceBody ≤ newAnchor.toConvexSpaceBody)
      (hCover : ∀ i ∈ retained,
        (T i).toConvexSpaceBody.homothety 0 (1 / 8) ≤ (newTube (quotientMap i)).toConvexSpaceBody)
      (hBalanced : ∀ q ∈ retained.image quotientMap, ∀ q' ∈ retained.image quotientMap,
        ((retained.filter fun i => quotientMap i = q).card : ENNReal) ≤ Q *
          ((retained.filter fun i => quotientMap i = q').card : ENNReal)) :
      ConvexSpaceBody.IsFrostmanIn
        (Tube.coverClass (retained.image quotientMap) descended coarseLabel)
        (fun q => (newTube q).toConvexSpaceBody) newAnchor.toConvexSpaceBody
        (512 * Q * A * L *
          (volume newAnchor.carrier / volume (U.cover.tube k coarseLabel).carrier)) := by
    let quotient := Tube.coverClass (retained.image quotientMap) descended coarseLabel
    have hFiber q (hq : q ∈ quotient) :
        (retained.filter fun i => coarseParent (U.cover.assign k i) = coarseLabel ∧
          quotientMap i = q) = retained.filter fun i => quotientMap i = q := by
      have hLabel : descended q = coarseLabel := (Finset.mem_filter.mp hq).2
      ext i
      simp only [Finset.mem_filter]
      constructor
      · exact fun h => ⟨h.1, h.2.2⟩
      · intro h
        refine ⟨h.1, ?_, h.2⟩
        rw [← hDescended i h.1, h.2]
        exact hLabel
    apply hOriginalCoordinateQuotientFrostman hdelta hdeltaOne source retained hsub
      T N k hk C U A L Q hFrostman coarseParent quotientMap coarseLabel quotient
      newTube newAnchor hRetained hNewInside
    · intro i hi hlabel
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image_of_mem quotientMap hi, (hDescended i hi).trans hlabel⟩
    · exact fun i hi _ => hCover i hi
    · intro q hq
      rw [hFiber q hq]
      obtain ⟨i, hi, hq⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hq).1
      exact ⟨i, Finset.mem_filter.mpr ⟨hi, hq⟩⟩
    · intro q hq q' hq'
      rw [hFiber q hq, hFiber q' hq']
      exact hBalanced q (Finset.mem_filter.mp hq).1 q' (Finset.mem_filter.mp hq').1
  have hUnitParentRatio {sigma rho : NNReal} (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
      (hscale : sigma ≤ rho) (hsmall : 1024 * sigma ≤ 1)
      (coarse : Tube sigma Kakeya.Point3) (oldAnchor : Tube rho Kakeya.Point3) :
      volume (coarse.rescale (1024 * sigma)).carrier / volume oldAnchor.carrier ≤
        DirectCenteredRoute.unitParentVolumeCost 3 := by
    have hOldVolume := Tube.volume_pos_and_lt_top hrho hrhoOne oldAnchor
    apply (ENNReal.div_le_iff hOldVolume.1.ne' hOldVolume.2.ne).mpr
    have hdim : Module.finrank ℝ Kakeya.Point3 = 3 := by simp
    calc
      _ ≤ DirectCenteredRoute.unitParentVolumeCost 3 * volume coarse.carrier := by
        simpa only [hdim] using DirectCenteredRoute.unit_parent_volume_le hsmall coarse
      _ ≤ DirectCenteredRoute.unitParentVolumeCost 3 * volume (coarse.rescale rho).carrier := by
        exact mul_le_mul_right
          (measure_mono (μ := volume)
            (show coarse.carrier ⊆ (coarse.rescale rho).carrier from coarse.le_rescale hscale)) _
      _ = _ := by rw [Tube.volume_carrier_eq_volume_carrier (coarse.rescale rho) oldAnchor]
  have hOriginalMergedCoordinate {I : Type uI} {delta : NNReal}
      (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
      (source : Finset I) (T : I → Tube delta Kakeya.Point3)
      (N k : ℕ) (hk : k ≤ N) (C : NNReal)
      (U : Tube.UniformTubeSet source T N C) (A : ENNReal)
      (hFrostman : ∀ a ∈ U.cover.indexSet k,
        ConvexSpaceBody.IsFrostmanIn (Tube.coverClass source (U.cover.assign k) a)
          (fun i => (T i).toConvexSpaceBody) (U.cover.tube k a).toConvexSpaceBody A)
      (coarseParent : I → I) (coarseLabel : I) (newAnchor : ConvexSpaceBody Kakeya.Point3)
      (hInside : ∀ i ∈ source, coarseParent (U.cover.assign k i) = coarseLabel →
        (T i).toConvexSpaceBody.homothety 0 (1 / 8) ≤ newAnchor) :
      ConvexSpaceBody.IsFrostmanIn
        (source.filter fun i => coarseParent (U.cover.assign k i) = coarseLabel)
        (fun i => (T i).toConvexSpaceBody.homothety 0 (1 / 8)) newAnchor
        (512 * A * (volume newAnchor.carrier / volume (U.cover.tube k coarseLabel).carrier)) := by
    let grouped := source.filter fun i => coarseParent (U.cover.assign k i) = coarseLabel
    have hr : (1 / 8 : ℝ) ≠ 0 := by norm_num
    have hVolume (W : ConvexSpaceBody Kakeya.Point3) :
        volume (W.homothety 0 (1 / 8)).carrier = (1 / 512) * volume W.carrier := by
      have hdim : Module.finrank ℝ Kakeya.Point3 = 3 := by simp
      rw [ConvexSpaceBody.volume_homothety, hdim,
        show |(1 / 8 : ℝ) ^ 3| = 1 / 512 by norm_num,
        ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num
    have hParent a (ha : a ∈ grouped.image (U.cover.assign k)) : a ∈ U.cover.indexSet k := by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      exact U.cover.assign_mem k hk i (Finset.mem_filter.mp hi).1
    have hFiber a (ha : a ∈ grouped.image (U.cover.assign k)) :
        grouped.filter (fun i => U.cover.assign k i = a) = Tube.coverClass source (U.cover.assign k) a := by
      obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp ha
      have hlabel : coarseParent a = coarseLabel := by
        rw [← hia]
        exact (Finset.mem_filter.mp hi).2
      ext i
      simp only [grouped, Tube.coverClass, Finset.mem_filter]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2 ▸ hlabel⟩, h.2⟩⟩
    have hAnchorPositive := (Tube.volume_pos_and_lt_top (Tube.gridScale_pos hdelta N k)
      (Tube.gridScale_le_one hdeltaOne N k) (U.cover.tube k coarseLabel)).1
    have h := DirectCenteredRoute.frostman_merge_equal_volume_anchors
      grouped (U.cover.assign k) (fun i => (T i).toConvexSpaceBody.homothety 0 (1 / 8))
      (fun a => (U.cover.tube k a).toConvexSpaceBody.homothety 0 (1 / 8)) newAnchor A
      ((1 / 512) * volume (U.cover.tube k coarseLabel).carrier)
      (mul_ne_zero (by norm_num) hAnchorPositive.ne')
      (fun a _ => by
        rw [hVolume, Tube.volume_carrier_eq_volume_carrier (U.cover.tube k a) (U.cover.tube k coarseLabel)])
      (fun i hi => (ConvexSpaceBody.homothety_le_homothety_iff 0 hr).mpr
        (U.cover.le_tube_assign k hk i (Finset.mem_filter.mp hi).1))
      (fun i hi => hInside i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2)
      (fun a ha => by
        rw [hFiber a ha]
        exact (ConvexSpaceBody.IsFrostmanIn.homothety 0 hr).mpr (hFrostman a (hParent a ha)))
    have hConst : A * (volume newAnchor.carrier /
        ((1 / 512) * volume (U.cover.tube k coarseLabel).carrier)) =
        512 * A * (volume newAnchor.carrier / volume (U.cover.tube k coarseLabel).carrier) := by
      simp only [div_eq_mul_inv]
      rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
      norm_num
      ring
    rw [hConst] at h
    exact h
  have hActualSourceAtomCore {I Atoms : Type uI} [decAtoms : DecidableEq Atoms] {delta : NNReal}
      (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
      (source : Finset I) (T : I → Tube delta Kakeya.Point3) (N : ℕ) (C : NNReal)
      (U : Tube.UniformTubeSet source T N C) (A R : ENNReal)
      (hFrostman : U.IsFrostmanAtEveryScale A)
      (d : ℕ) (gridIndex : Fin d → ℕ) (hGrid : ∀ k, gridIndex k ≤ N)
      (code : I → Atoms) (atomParent : Fin d → Atoms → I)
      (coarseParent : Fin d → I → I)
      (hFactor : ∀ i ∈ source, ∀ k,
        atomParent k (code i) = coarseParent k (U.cover.assign (gridIndex k) i))
      (initial : Finset Atoms) (hInitial : initial ⊆ source.image code)
      (hInitialNonempty : (source.filter fun i => code i ∈ initial).Nonempty)
      (newAnchor : Fin d → I → ConvexSpaceBody Kakeya.Point3)
      (hInside : ∀ k, ∀ i ∈ source,
        (T i).toConvexSpaceBody.homothety 0 (1 / 8) ≤ newAnchor k (atomParent k (code i)))
      (hRatio : ∀ k, ∀ j ∈ initial.image (atomParent k),
        volume (newAnchor k j).carrier / volume (U.cover.tube (gridIndex k) j).carrier ≤ R) :
      ∃ selected : Finset Atoms, selected ⊆ initial ∧ selected.Nonempty ∧
        (source.filter fun i => code i ∈ selected).Nonempty ∧
        (source.filter fun i => code i ∈ initial).card ≤
          2 * (source.filter fun i => code i ∈ selected).card ∧
        (∀ k, ∀ j ∈ selected.image (atomParent k),
          ConvexSpaceBody.IsFrostmanIn
            ((source.filter fun i => code i ∈ selected).filter fun i => atomParent k (code i) = j)
            (fun i => (T i).toConvexSpaceBody.homothety 0 (1 / 8)) (newAnchor k j)
            ((512 * A * R) * ENNReal.ofReal
              ((((source.filter fun i => code i ∈ initial).card : ℝ) /
                (2 * ((d : ℝ) + 1) * (source.card : ℝ)))⁻¹))) ∧
        (∀ k, ∀ j ∈ selected.image (atomParent k),
          (((source.filter fun i => code i ∈ initial).card : ℝ) /
            (2 * ((d : ℝ) + 1) * (source.card : ℝ))) *
            ((source.filter fun i => atomParent k (code i) = j).card : ℝ) ≤
          (((source.filter fun i => code i ∈ selected).filter
            fun i => atomParent k (code i) = j).card : ℝ)) := by
    have hdec : decAtoms = Classical.decEq Atoms := Subsingleton.elim _ _
    subst decAtoms
    let i0 := hInitialNonempty.choose
    have hVolume (W : ConvexSpaceBody Kakeya.Point3) :
        volume (W.homothety 0 (1 / 8)).carrier = (1 / 512) * volume W.carrier := by
      have hdim : Module.finrank ℝ Kakeya.Point3 = 3 := by simp
      rw [ConvexSpaceBody.volume_homothety, hdim,
        show |(1 / 8 : ℝ) ^ 3| = 1 / 512 by norm_num,
        ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num
    have hMerged k (j : I) (hj : j ∈ initial.image (atomParent k)) :
        ConvexSpaceBody.IsFrostmanIn
          (source.filter fun i => atomParent k (code i) = j)
          (fun i => (T i).toConvexSpaceBody.homothety 0 (1 / 8)) (newAnchor k j)
          (512 * A * R) := by
      have h := hOriginalMergedCoordinate hdelta hdeltaOne source T N (gridIndex k)
        (hGrid k) C U A (hFrostman (gridIndex k) (hGrid k)) (coarseParent k) j (newAnchor k j)
        (fun i hi hij => by
          have h := hInside k i hi
          rwa [hFactor i hi k, hij] at h)
      have hClasses : (source.filter fun i => atomParent k (code i) = j) =
          source.filter fun i => coarseParent k (U.cover.assign (gridIndex k) i) = j := by
        apply Finset.filter_congr
        intro i hi
        rw [hFactor i hi k]
      rw [hClasses]
      exact h.mono (mul_le_mul_right (hRatio k j hj) _)
    have hpositive : 0 < ∑ _i ∈ source.filter (fun i => code i ∈ initial), (1 : ℝ) := by
      simpa using (show (0 : ℝ) < (source.filter fun i => code i ∈ initial).card from
        by exact_mod_cast hInitialNonempty.card_pos)
    obtain ⟨selected, hselected, hnonempty, hpullback, hhalf, hcore⟩ :=
      DirectCenteredRoute.exists_relative_atom_core_pullback source code
        (Finset.univ : Finset (Fin d)) atomParent initial (by
          intro a ha
          exact Finset.mem_image.mpr (Finset.mem_image.mp (hInitial ha)))
        (fun _ => (1 : ℝ)) (fun _ _ => by norm_num)
        (by simpa only [Finset.filter_congr_decidable] using hpositive)
    let theta := ((source.filter fun i => code i ∈ initial).card : ℝ) /
      (2 * ((d : ℝ) + 1) * (source.card : ℝ))
    have htheta : 0 < theta := by
      have hs : source.Nonempty := hInitialNonempty.mono (Finset.filter_subset _ _)
      have hsCard : (0 : ℝ) < source.card := by exact_mod_cast hs.card_pos
      have hiCard : (0 : ℝ) < (source.filter fun i => code i ∈ initial).card := by
        exact_mod_cast hInitialNonempty.card_pos
      dsimp [theta]
      positivity
    have hCount k j (hj : j ∈ selected.image (atomParent k)) :
        theta * ((source.filter fun i => atomParent k (code i) = j).card : ℝ) ≤
        (((source.filter fun i => code i ∈ selected).filter fun i => atomParent k (code i) = j).card : ℝ) := by
      simpa only [theta, Finset.filter_congr_decidable, Finset.card_univ, Fintype.card_fin, Finset.sum_const,
        nsmul_eq_mul, mul_one] using hcore k (Finset.mem_univ _) j hj
    have hHalf : (source.filter fun i => code i ∈ initial).card ≤
        2 * (source.filter fun i => code i ∈ selected).card := by
      have hReal : ((source.filter fun i => code i ∈ initial).card : ℝ) ≤
          2 * ((source.filter fun i => code i ∈ selected).card : ℝ) := by
        simpa only [Finset.filter_congr_decidable, Finset.sum_const, nsmul_eq_mul, mul_one] using hhalf
      exact_mod_cast hReal
    refine ⟨selected, hselected, hnonempty, ?_, hHalf, ?_, hCount⟩
    · simpa only [Finset.filter_congr_decidable] using hpullback
    intro k j hj
    exact DirectCenteredRoute.frostman_pullback_of_relative_card_core source selected code (atomParent k)
      (fun i => (T i).toConvexSpaceBody.homothety 0 (1 / 8)) (newAnchor k)
      ((1 / 512) * volume (T i0).carrier) (512 * A * R)
      (fun i _ => by rw [hVolume, Tube.volume_carrier_eq_volume_carrier (T i) (T i0)])
      (hInside k) (fun j hj => hMerged k j (Finset.image_subset_image hselected hj))
      theta htheta (by simpa only [Finset.filter_congr_decidable] using hCount k) j hj
  have hActualAtomQuotientConstruction {I Atoms : Type uI} [decAtoms : DecidableEq Atoms] {delta eta : NNReal}
      (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
      (source : Finset I) (T : I → Tube delta Kakeya.Point3) (N : ℕ) (C : NNReal)
      (U : Tube.UniformTubeSet source T N C) (A R Q : ENNReal)
      (hFrostman : U.IsFrostmanAtEveryScale A)
      (d : ℕ) (gridIndex : Fin d → ℕ) (hGrid : ∀ k, gridIndex k ≤ N)
      (code : I → Atoms) (projection : Atoms → I) (atomParent : Fin d → Atoms → I)
      (coarseParent : Fin d → I → I)
      (hFactor : ∀ i ∈ source, ∀ k,
        atomParent k (code i) = coarseParent k (U.cover.assign (gridIndex k) i))
      (initial : Finset Atoms) (hInitial : initial ⊆ source.image code)
      (hInitialNonempty : (source.filter fun i => code i ∈ initial).Nonempty)
      (hInitialInj : Set.InjOn projection (initial : Set Atoms))
      (hInitialBalance : ∀ a ∈ initial, ∀ b ∈ initial,
        ((source.filter fun i => code i = a).card : ENNReal) ≤
          Q * ((source.filter fun i => code i = b).card : ENNReal))
      (newTube : I → Tube eta Kakeya.Point3)
      (newAnchor : Fin d → I → ConvexSpaceBody Kakeya.Point3)
      (hCoarseInside : ∀ k, ∀ i ∈ source,
        (T i).toConvexSpaceBody.homothety 0 (1 / 8) ≤ newAnchor k (atomParent k (code i)))
      (hCover : ∀ i ∈ source, code i ∈ initial →
        (T i).toConvexSpaceBody.homothety 0 (1 / 8) ≤ (newTube (projection (code i))).toConvexSpaceBody)
      (hFineInside : ∀ k, ∀ i ∈ source, code i ∈ initial →
        (newTube (projection (code i))).toConvexSpaceBody ≤ newAnchor k (atomParent k (code i)))
      (hRatio : ∀ k, ∀ j ∈ initial.image (atomParent k),
        volume (newAnchor k j).carrier / volume (U.cover.tube (gridIndex k) j).carrier ≤ R) :
      ∃ selected : Finset Atoms, ∃ descended : Fin d → I → I,
        selected ⊆ initial ∧ selected.Nonempty ∧
        (source.filter fun i => code i ∈ selected).Nonempty ∧
        (source.filter fun i => code i ∈ initial).card ≤
          2 * (source.filter fun i => code i ∈ selected).card ∧
        (∀ i ∈ source.filter (fun i => code i ∈ selected), ∀ k,
          descended k (projection (code i)) = atomParent k (code i)) ∧
        (∀ k, ∀ j ∈ selected.image (atomParent k),
          ConvexSpaceBody.IsFrostmanIn
            (Tube.coverClass (selected.image projection) (descended k) j)
            (fun q => (newTube q).toConvexSpaceBody) (newAnchor k j)
            (Q * ((512 * A * R) * ENNReal.ofReal
              ((((source.filter fun i => code i ∈ initial).card : ℝ) /
                (2 * ((d : ℝ) + 1) * (source.card : ℝ)))⁻¹)))) ∧
        (∀ k, ∀ j ∈ selected.image (atomParent k),
          (((source.filter fun i => code i ∈ initial).card : ℝ) /
            (2 * ((d : ℝ) + 1) * (source.card : ℝ))) *
            ((source.filter fun i => atomParent k (code i) = j).card : ℝ) ≤
          (((source.filter fun i => code i ∈ selected).filter
            fun i => atomParent k (code i) = j).card : ℝ)) := by
    have hdec : decAtoms = Classical.decEq Atoms := Subsingleton.elim _ _
    subst decAtoms
    obtain ⟨selected, hselected, hSelectedNonempty, hRawNonempty, hHalf, hRawFr, hRawCount⟩ :=
      hActualSourceAtomCore hdelta hdeltaOne source T N C U A R hFrostman d gridIndex hGrid
        code atomParent coarseParent hFactor initial hInitial hInitialNonempty newAnchor
        hCoarseInside hRatio
    let raw := source.filter fun i => code i ∈ selected
    have hRawSub : raw ⊆ source := Finset.filter_subset _ _
    have hInj : Set.InjOn projection (selected : Set Atoms) :=
      hInitialInj.mono (Finset.coe_subset.mpr hselected)
    obtain ⟨descended, hDescended⟩ := DirectCenteredRoute.exists_descended_coarse_labels
      raw hRawNonempty (fun i => projection (code i)) (fun k i => atomParent k (code i))
      (fun i hi j hj hij k => congrArg (atomParent k)
        (hInj (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2 hij))
    have hBalanced := DirectCenteredRoute.pullback_quotient_fibers_balanced source code projection
      selected hInj Q (fun a ha b hb => by
        simpa only [Finset.filter_congr_decidable] using hInitialBalance a (hselected ha) b (hselected hb))
    have hLift q (hq : q ∈ selected.image projection) :
        ∃ i ∈ raw, projection (code i) = q := by
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp (hInitial (hselected ha))
      exact ⟨i, Finset.mem_filter.mpr ⟨hi, hia ▸ ha⟩, congrArg projection hia⟩
    refine ⟨selected, descended, hselected, hSelectedNonempty, hRawNonempty, hHalf, hDescended, ?_, hRawCount⟩
    intro k j hj
    let group := raw.filter fun i => atomParent k (code i) = j
    let quotient := Tube.coverClass (selected.image projection) (descended k) j
    have hGroupSub : group ⊆ raw := Finset.filter_subset _ _
    have hRawInside i (hi : i ∈ group) :
        (T i).toConvexSpaceBody.homothety 0 (1 / 8) ≤ newAnchor k j := by
      obtain ⟨hi, hij⟩ := Finset.mem_filter.mp hi
      exact hij ▸ hCoarseInside k i (hRawSub hi)
    have hNewInside q (hq : q ∈ quotient) : (newTube q).toConvexSpaceBody ≤ newAnchor k j := by
      obtain ⟨hq, hqj⟩ := Finset.mem_filter.mp hq
      obtain ⟨i, hi, hiq⟩ := hLift q hq
      have hlabel : atomParent k (code i) = j := by rw [← hDescended i hi k, hiq]; exact hqj
      have h := hFineInside k i (hRawSub hi) (hselected (Finset.mem_filter.mp hi).2)
      rwa [hiq, hlabel] at h
    have hFiber q (hq : q ∈ quotient) :
        group.filter (fun i => projection (code i) = q) =
          raw.filter (fun i => projection (code i) = q) := by
      have hqj := (Finset.mem_filter.mp hq).2
      ext i
      simp only [group, Finset.mem_filter]
      constructor
      · exact fun h => ⟨h.1.1, h.2⟩
      · intro h
        refine ⟨⟨h.1, ?_⟩, h.2⟩
        rw [← hDescended i h.1 k, h.2]
        exact hqj
    by_cases hNewZero : volume (newAnchor k j).carrier = 0
    · exact ConvexSpaceBody.IsFrostmanIn.of_volume_eq_zero hNewZero
    have h := DirectCenteredRoute.frostman_balanced_quotient group
      (fun i => (T i).toConvexSpaceBody.homothety 0 (1 / 8))
      (newAnchor k j) (newAnchor k j) _ Q (hRawFr k j hj) hRawInside hNewZero
      (fun i hi => by
        rw [ConvexSpaceBody.volume_homothety]
        exact ENNReal.mul_pos
          (ENNReal.ofReal_pos.mpr (abs_pos.mpr (pow_ne_zero _ (by norm_num)))).ne'
          (Tube.volume_pos_and_lt_top hdelta hdeltaOne (T i)).1.ne')
      quotient (fun i => projection (code i)) (fun q => (newTube q).toConvexSpaceBody)
      (fun i hi => by
        obtain ⟨hi, hij⟩ := Finset.mem_filter.mp hi
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_image_of_mem projection (Finset.mem_filter.mp hi).2,
            (hDescended i hi k).trans hij⟩)
      (fun i hi => hCover i (hRawSub (hGroupSub hi))
        (hselected (Finset.mem_filter.mp (hGroupSub hi)).2)) hNewInside
      (fun q hq => by
        rw [hFiber q hq]
        obtain ⟨i, hi, hiq⟩ := hLift q (Finset.mem_filter.mp hq).1
        exact ⟨i, Finset.mem_filter.mpr ⟨hi, hiq⟩⟩)
      (volume ((T j).toConvexSpaceBody.homothety 0 (1 / 8)).carrier)
      (volume (newTube j).carrier)
      (fun i _ => by
        rw [ConvexSpaceBody.volume_homothety, ConvexSpaceBody.volume_homothety,
          Tube.volume_carrier_eq_volume_carrier (T i) (T j)])
      (fun q _ => Tube.volume_carrier_eq_volume_carrier (newTube q) (newTube j))
      (fun q hq q' hq' => by
        rw [hFiber q hq, hFiber q' hq']
        simpa only [Finset.filter_congr_decidable, raw] using
          hBalanced q (Finset.mem_filter.mp hq).1 q' (Finset.mem_filter.mp hq').1)
    simpa only [ENNReal.div_self hNewZero (newAnchor k j).isCompact.measure_ne_top, mul_one] using h
  have hSelectComparableBandClasses {Atoms I : Type uI} [decAtoms : DecidableEq Atoms]
      (band : Finset Atoms) (weight : Atoms → ℝ) (hpositive : 0 < ∑ a ∈ band, weight a)
      (d : ℕ) (parent : Fin d → Atoms → I) :
      ∃ initial : Finset Atoms, initial ⊆ band ∧ initial.Nonempty ∧
        (∑ a ∈ band, weight a) ≤
          (1 + Real.logb 2 (band.card : ℝ)) ^ d * (∑ a ∈ initial, weight a) ∧
        (∀ k, ∀ a ∈ initial.image (parent k), ∀ b ∈ initial.image (parent k),
          ((band.filter fun i => parent k i = a).card : ℝ) ≤
            2 * ((band.filter fun i => parent k i = b).card : ℝ)) := by
    have hdec : decAtoms = Classical.decEq Atoms := Subsingleton.elim _ _
    subst decAtoms
    have hBand : band.Nonempty := by
      by_contra h
      simp only [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hpositive
      exact (lt_irrefl _) hpositive
    have hCard : (1 : ℝ) ≤ band.card := by exact_mod_cast hBand.card_pos
    let feature := fun a k => ((band.filter fun b => parent k b = parent k a).card : ℝ)
    obtain ⟨initial, hsub, hretained, hcompare⟩ := Real.dyadic_pigeonhole band weight
      feature (by norm_num : (0 : ℝ) < 1) hCard (by
        intro a ha
        constructor
        · intro k
          change (1 : ℝ) ≤ (band.filter fun b => parent k b = parent k a).card
          have hpos : 0 < (band.filter fun b => parent k b = parent k a).card :=
            Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, rfl⟩⟩
          exact_mod_cast hpos
        · intro k
          change ((band.filter fun b => parent k b = parent k a).card : ℝ) ≤ band.card
          exact_mod_cast Finset.card_le_card (Finset.filter_subset (fun b => parent k b = parent k a) band))
    simp only [div_one] at hretained
    refine ⟨initial, hsub, ?_, hretained, ?_⟩
    · by_contra h
      simp only [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty, mul_zero] at hretained
      exact (not_le_of_gt hpositive) hretained
    · intro k a ha b hb
      obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
      exact hcompare a' ha' b' hb' k
  have hSameCoreClassRatio {I Atoms : Type uI} [decAtoms : DecidableEq Atoms] (source : Finset I) (code : I → Atoms)
      (band selected : Finset Atoms) (hsub : selected ⊆ band)
      (parent : Atoms → I) (b theta : ℝ) (hb : 0 < b) (htheta : 0 < theta)
      (hWeights : ∀ a ∈ band,
        b ≤ ((source.filter fun i => code i = a).card : ℝ) ∧
        ((source.filter fun i => code i = a).card : ℝ) ≤ 2 * b)
      (hBandClasses : ∀ a ∈ selected.image parent, ∀ b ∈ selected.image parent,
        ((band.filter fun i => parent i = a).card : ℝ) ≤
          2 * ((band.filter fun i => parent i = b).card : ℝ))
      (hRawCore : ∀ j ∈ selected.image parent,
        theta * ((source.filter fun i => parent (code i) = j).card : ℝ) ≤
          (((source.filter fun i => code i ∈ selected).filter fun i => parent (code i) = j).card : ℝ)) :
      ∀ a ∈ selected.image parent, ∀ c ∈ selected.image parent,
        ((selected.filter fun i => parent i = a).card : ℝ) ≤
          (4 / theta) * ((selected.filter fun i => parent i = c).card : ℝ) := by
    have hdec : decAtoms = Classical.decEq Atoms := Subsingleton.elim _ _
    subst decAtoms
    have hSum (atoms : Finset Atoms) (j : I) :
        (∑ a ∈ atoms.filter (fun a => parent a = j),
          ((source.filter fun i => code i = a).card : ℝ)) =
          (((source.filter fun i => code i ∈ atoms).filter fun i => parent (code i) = j).card : ℝ) := by
      simpa only [Finset.filter_congr_decidable, Finset.sum_const, nsmul_eq_mul, mul_one] using
        DirectCenteredRoute.sum_atom_weights_filter source atoms code parent (fun _ => (1 : ℝ)) j
    have hLower j : b * ((band.filter fun a => parent a = j).card : ℝ) ≤
        ((source.filter fun i => parent (code i) = j).card : ℝ) := by
      calc
        _ = ∑ _a ∈ band.filter (fun a => parent a = j), b := by simp [mul_comm]
        _ ≤ ∑ a ∈ band.filter (fun a => parent a = j),
            ((source.filter fun i => code i = a).card : ℝ) :=
          Finset.sum_le_sum (fun a ha => (hWeights a (Finset.mem_filter.mp ha).1).1)
        _ = _ := hSum band j
        _ ≤ _ := by
          exact_mod_cast Finset.card_le_card
            (Finset.filter_subset_filter (fun i => parent (code i) = j) (Finset.filter_subset _ _))
    have hUpper j :
        (((source.filter fun i => code i ∈ selected).filter fun i => parent (code i) = j).card : ℝ) ≤
          2 * b * ((selected.filter fun a => parent a = j).card : ℝ) := by
      rw [← hSum selected j]
      calc
        _ ≤ ∑ _a ∈ selected.filter (fun a => parent a = j), 2 * b :=
          Finset.sum_le_sum (fun a ha => (hWeights a (hsub (Finset.mem_filter.mp ha).1)).2)
        _ = _ := by simp [mul_comm]
    have hFloor j (hj : j ∈ selected.image parent) :
        theta * ((band.filter fun a => parent a = j).card : ℝ) ≤
          2 * ((selected.filter fun a => parent a = j).card : ℝ) := by
      apply le_of_mul_le_mul_left (a := b) ?_ hb
      calc
        _ = theta * (b * ((band.filter fun a => parent a = j).card : ℝ)) := by ring
        _ ≤ theta * ((source.filter fun i => parent (code i) = j).card : ℝ) :=
          mul_le_mul_of_nonneg_left (hLower j) htheta.le
        _ ≤ _ := hRawCore j hj
        _ ≤ _ := hUpper j
        _ = _ := by ring
    intro a ha c hc
    have hSelSub : ((selected.filter fun i => parent i = a).card : ℝ) ≤
        ((band.filter fun i => parent i = a).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hsub)
    have h := mul_le_mul_of_nonneg_left
      (hSelSub.trans (hBandClasses a ha c hc)) htheta.le
    have h' := hFloor c hc
    have hFinal : ((selected.filter fun i => parent i = a).card : ℝ) * theta ≤
        4 * ((selected.filter fun i => parent i = c).card : ℝ) := by nlinarith
    simpa only [div_mul_eq_mul_div] using (le_div_iff₀ htheta).mpr hFinal
  have hDenseSource {I : Type uI} {delta : NNReal}
      (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
      (source : Finset I) (V : I → ShadedTube delta Kakeya.Point3)
      (hsource : source.Nonempty) (density : ENNReal) (hdensity : 0 < density)
      (hfullness : density ≤ ShadedBody.fullness' source (fun i => (V i).toShadedBody)) :
      ∃ selected : Finset I, selected ⊆ source ∧ selected.Nonempty ∧
        (density / 2) * (source.card : ENNReal) ≤ (selected.card : ENNReal) ∧
        (∀ i ∈ selected, (density / 2) * volume (V i).carrier ≤ volume (V i).shade) := by
    let body := fun i => (V i).toShadedBody
    let selected := ShadedBody.discardLowShading source body (1 / 2)
    have hsub : selected ⊆ source := ShadedBody.discardLowShading_subset _ _ _
    have hpointwise : ∀ i ∈ selected,
        (density / 2) * volume (V i).carrier ≤ volume (V i).shade := by
      intro i hi
      have h := ShadedBody.le_volume_shade_of_mem_discardLowShading hi
      rw [ShadedBody.coe_fullness] at h
      have hhalf : ((1 / 2 : NNReal) : ENNReal) = (1 / 2 : ENNReal) := by norm_num
      rw [hhalf] at h
      change (1 / 2 : ENNReal) * ShadedBody.fullness' source body *
        volume (V i).carrier ≤ volume (V i).shade at h
      calc
        _ = (1 / 2 : ENNReal) * density * volume (V i).carrier := by
          simp only [div_eq_mul_inv]
          ring
        _ ≤ _ := (mul_le_mul_left (mul_le_mul_right hfullness _) _).trans h
    have hmass : (1 / 2 : ENNReal) * (∑ i ∈ source, volume (V i).shade) ≤
        ∑ i ∈ selected, volume (V i).shade := by
      have h := ShadedBody.one_sub_mul_sum_volume_shade_le_sum_discardLowShading
        source body (c := (1 / 2 : NNReal)) (by norm_num)
      convert h using 1 <;> norm_num [body, selected]
    obtain ⟨i0, hi0⟩ := hsource
    let volume0 := volume (V i0).carrier
    have hvolume0 : volume0 ≠ 0 :=
      (Tube.volume_pos_and_lt_top hdelta hdeltaOne (V i0).toTube).1.ne'
    have hvolumeTop : volume0 ≠ ⊤ := (V i0).isCompact.measure_ne_top
    have hvolumes (s : Finset I) :
        (∑ i ∈ s, volume (V i).carrier) = (s.card : ENNReal) * volume0 := by
      calc
        _ = ∑ i ∈ s, volume0 := Finset.sum_congr rfl (fun i _ =>
          Tube.volume_carrier_eq_volume_carrier (V i).toTube (V i0).toTube)
        _ = _ := by simp
    have hcard : (density / 2) * (source.card : ENNReal) ≤ (selected.card : ENNReal) := by
      apply (ENNReal.mul_le_mul_iff_left hvolume0 hvolumeTop).mp
      calc
        (density / 2) * (source.card : ENNReal) * volume0 =
            (1 / 2 : ENNReal) * (density * ∑ i ∈ source, volume (V i).carrier) := by
          rw [hvolumes]
          simp only [div_eq_mul_inv]
          ring
        _ ≤ (1 / 2 : ENNReal) * ∑ i ∈ source, volume (V i).shade :=
          mul_le_mul_right (ENNReal.mul_le_of_le_div hfullness) _
        _ ≤ ∑ i ∈ selected, volume (V i).shade := hmass
        _ ≤ ∑ i ∈ selected, volume (V i).carrier :=
          Finset.sum_le_sum (fun i _ => measure_mono (V i).shade_subset)
        _ = _ := hvolumes selected
    refine ⟨selected, hsub, ?_, hcard, hpointwise⟩
    have hpos : 0 < (selected.card : ENNReal) :=
      (ENNReal.mul_pos_iff.mpr ⟨ENNReal.div_pos hdensity.ne' (by norm_num),
        by exact_mod_cast Finset.card_pos.mpr (show source.Nonempty from ⟨i0, hi0⟩)⟩).trans_le hcard
    exact Finset.card_pos.mp (by exact_mod_cast hpos)
  clear hFixedTreeUniform hRetainedUniform hWeightedCoreCount hWeightedUniform
    hGroupedQuotientFrostman hOriginalCoordinateQuotientFrostman hActualDescendedQuotientFrostman
  have hWeightedED {I : Type uI} {delta : NNReal} (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
      (source : Finset I) (tube : I → Tube delta Kakeya.Point3)
      (hcenter : ∀ i ∈ source, ‖(tube i).center‖ ≤ 1)
      (A : ℕ) (hA : 1 ≤ A) (hline : Kakeya.VeryNotSticky.IsLineEssDistinct A source tube)
      (weight : I → ENNReal) :
      ∃ selected ⊆ source,
        (selected : Set I).Pairwise
          (fun i j => _root_.IsEssentiallyDistinct (tube i).carrier (tube j).carrier) ∧
        (∑ i ∈ source, weight i) ≤
          (Kakeya.ml1Boot.TrialRestartW94.lineSelectionMultiplicityW95 3 1 A : ENNReal) *
            ∑ i ∈ selected, weight i := by
    let K := Kakeya.Tube.tubeOverlapCoreClose.C 3
    let M := Kakeya.ml1Boot.TrialRestartW94.lineSelectionMultiplicityW95 3 1 A
    have hK : 1 ≤ K := (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C 3).le
    have hB : 0 < Kakeya.ml1Boot.TrialRestartW94.lineAmplificationBoundW95 3 1 K := by
      apply Nat.ceil_pos.mpr
      have hKm : 0 ≤ K - 1 := sub_nonneg.mpr hK
      positivity
    have hM : 1 ≤ M := Nat.mul_pos hB (by omega)
    have hline' := Kakeya.ml1Boot.TrialRestartW94.lineED_five_implies_lineEDAt_w95
      hdelta hdeltaOne source tube A hline 1 K (by norm_num) hK hcenter
    obtain ⟨selected, hsub, hED, hweight, _⟩ :=
      Kakeya.VeryNotSticky.exists_pairwise_of_isLineEssDistinctAt (E := Kakeya.Point3)
        hdelta hdeltaOne (by simpa only [show Module.finrank ℝ Kakeya.Point3 = 3 by simp] using hline') weight
    have hdim : Module.finrank ℝ Kakeya.Point3 = 3 := by simp
    change (∑ i ∈ source, weight i) ≤ ((M - 1 + 1 : ℕ) : ENNReal) *
      ∑ i ∈ selected, weight i at hweight
    rw [Nat.sub_add_cancel hM] at hweight
    exact ⟨selected, hsub, hED, hweight⟩
  have hCardLogEnvelope (C : Real) (hC : 0 < C) (q : Real) :
      ∃ D delta0 : Real, 0 < D ∧ 0 < delta0 ∧ delta0 ≤ 1 / 200 ∧
        ∀ delta : Real, 0 < delta → delta ≤ delta0 →
        ∀ cardinality : Nat, (cardinality : Real) ≤ C * delta ^ (-q) →
          0 ≤ 1 + Real.logb 2 (2 * (cardinality : Real)) ∧
          1 + Real.logb 2 (2 * (cardinality : Real)) ≤ D * Real.log (1 / delta) := by
    let a := Real.log (2 * C) / Real.log 2 + 1
    let b := q / Real.log 2
    let D := |a| + |b| + 1
    have hD : 1 ≤ D := by dsimp [D]; linarith [abs_nonneg a, abs_nonneg b]
    refine ⟨D, min (1 / 200) (Real.exp (-1)), by linarith,
      lt_min (by norm_num) (Real.exp_pos _), min_le_left _ _, ?_⟩
    intro delta hdelta hsmall cardinality hcardinality
    let x := Real.log (1 / delta)
    have hx : 1 ≤ x := by
      have h := Real.log_le_log hdelta (hsmall.trans (min_le_right _ _))
      rw [Real.log_exp] at h
      dsimp [x]
      rw [one_div, Real.log_inv]
      linarith
    have hx0 : 0 ≤ x := by linarith
    by_cases hzero : cardinality = 0
    · subst cardinality
      simp only [Nat.cast_zero, mul_zero, Real.logb_zero, add_zero]
      exact ⟨by norm_num, by nlinarith⟩
    have hcardpos : 0 < (cardinality : Real) := by
      exact_mod_cast Nat.pos_of_ne_zero hzero
    have hcardone : 1 ≤ (cardinality : Real) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hzero
    have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hnonneg : 0 ≤ Real.logb 2 (2 * (cardinality : Real)) := by
      rw [Real.logb]
      exact div_nonneg (Real.log_nonneg (by linarith)) hlogTwo.le
    refine ⟨by linarith, ?_⟩
    have hpoly : 2 * (cardinality : Real) ≤ (2 * C) * delta ^ (-q) := by nlinarith
    have hlog := Real.log_le_log (by positivity : 0 < 2 * (cardinality : Real)) hpoly
    have hproduct : Real.log ((2 * C) * delta ^ (-q)) = Real.log (2 * C) + q * x := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hdelta]
      dsimp [x]
      rw [one_div, Real.log_inv]
      ring
    have hraw : 1 + Real.logb 2 (2 * (cardinality : Real)) ≤ a + b * x := by
      calc
        _ = Real.log (2 * (cardinality : Real)) / Real.log 2 + 1 := by
          rw [Real.logb]; ring
        _ ≤ Real.log ((2 * C) * delta ^ (-q)) / Real.log 2 + 1 := by gcongr
        _ = _ := by rw [hproduct]; dsimp [a, b]; ring
    have ha : a ≤ |a| := le_abs_self _
    have hb : b * x ≤ |b| * x := mul_le_mul_of_nonneg_right (le_abs_self _) hx0
    have hax : |a| ≤ |a| * x := by nlinarith [abs_nonneg a]
    dsimp [D]
    nlinarith
  
  have hRestoredDensity {delta : NNReal} (hdeltaOne : delta ≤ 1)
      (Z : ShadedTube (delta / 2) Kakeya.Point3) (density : ENNReal)
      (hdensity : density * volume Z.carrier ≤ 384 * volume Z.shade) :
      density * volume (Z.toTube.rescale delta).carrier ≤
        (384 * ((Tube.volume_le.C 3 : ENNReal) / (Tube.le_volume.c 3 : ENNReal) * 4)) *
          volume Z.shade := by
    let C : ENNReal := Tube.volume_le.C 3
    let c : ENNReal := Tube.le_volume.c 3
    have hc : c ≠ 0 := by
      dsimp [c]
      exact_mod_cast (Tube.le_volume.c_pos 3).ne'
    have hcTop : c ≠ ⊤ := ENNReal.coe_ne_top
    have hhalf : (delta : ENNReal) = 2 * ((delta / 2 : NNReal) : ENNReal) := by
      exact_mod_cast (show delta = 2 * (delta / 2) by ring)
    have hupper : volume (Z.toTube.rescale delta).carrier ≤ C * (delta : ENNReal) ^ 2 := by
      simpa [C] using (Z.toTube.rescale delta).volume_le hdeltaOne
    have hlower : c * ((delta / 2 : NNReal) : ENNReal) ^ 2 ≤ volume Z.carrier := by
      simpa [c] using Z.toTube.le_volume
    have hvolume : volume (Z.toTube.rescale delta).carrier ≤ (C / c * 4) * volume Z.carrier := by
      calc
        _ ≤ C * (delta : ENNReal) ^ 2 := hupper
        _ = (C / c * 4) * (c * ((delta / 2 : NNReal) : ENNReal) ^ 2) := by
          rw [hhalf, mul_pow]
          calc
            _ = ((C / c) * c) * (4 * ((delta / 2 : NNReal) : ENNReal) ^ 2) := by
              rw [ENNReal.div_mul_cancel hc hcTop]
              ring
            _ = _ := by ring
        _ ≤ _ := mul_le_mul' le_rfl hlower
    calc
      _ ≤ density * ((C / c * 4) * volume Z.carrier) := mul_le_mul_right hvolume _
      _ = (C / c * 4) * (density * volume Z.carrier) := by ring
      _ ≤ (C / c * 4) * (384 * volume Z.shade) := mul_le_mul_right hdensity _
      _ = _ := by dsimp [C, c]; ring
  
  have hHereditaryShade {I : Type uI} {delta : NNReal} (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
      (source selected : Finset I) (hselected : selected ⊆ source) (hne : selected.Nonempty)
      (V : I → ShadedTube delta Kakeya.Point3) (density cost : ENNReal)
      (hcostZero : cost ≠ 0) (hcostTop : cost ≠ ⊤)
      (hdense : ∀ i ∈ source, density * volume (V i).carrier ≤ cost * volume (V i).shade)
      (originalUnion : Set Kakeya.Point3)
      (hunion : volume (⋃ i ∈ source, (V i).shade) ≤ volume originalUnion) :
      density / cost ≤ ShadedBody.fullness' selected (fun i => (V i).toShadedBody) ∧
        volume (⋃ i ∈ selected, (V i).shade) ≤ volume originalUnion := by
    have htotal : 0 < ∑ i ∈ selected, volume (V i).carrier := by
      obtain ⟨j, hj⟩ := hne
      exact (Tube.volume_pos_and_lt_top hdelta hdeltaOne (V j).toTube).1.trans_le
        (Finset.single_le_sum (f := fun i => volume (V i).carrier) (fun i _ => zero_le) hj)
    have hfinite : (∑ i ∈ selected, volume (V i).carrier) ≠ ⊤ := by
      exact ENNReal.sum_ne_top.mpr (fun i _ =>
        (Tube.volume_pos_and_lt_top hdelta hdeltaOne (V i).toTube).2.ne)
    refine ⟨?_, (measure_mono ?_).trans hunion⟩
    · apply (ENNReal.le_div_iff_mul_le (Or.inl htotal.ne') (Or.inl hfinite)).mpr
      have hsum : density * (∑ i ∈ selected, volume (V i).carrier) ≤
          cost * ∑ i ∈ selected, volume (V i).shade := by
        simpa only [Finset.mul_sum] using Finset.sum_le_sum (fun i hi => hdense i (hselected hi))
      change density / cost * (∑ i ∈ selected, volume (V i).carrier) ≤
        ∑ i ∈ selected, volume (V i).shade
      rw [div_eq_mul_inv]
      calc
        _ = (cost : ENNReal)⁻¹ * (density * ∑ i ∈ selected, volume (V i).carrier) := by ring
        _ ≤ (cost : ENNReal)⁻¹ * (cost * ∑ i ∈ selected, volume (V i).shade) := by gcongr
        _ = _ := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hcostZero hcostTop, one_mul]
    · intro x hx
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
      exact Set.mem_iUnion₂.mpr ⟨i, hselected hi, hxi⟩
  
  let coarseDegree := Kakeya.ml1Boot.TrialRestartW94.lineAmplificationBoundW95 3 1 128 * (2 * 223 ^ 6)
  let lineBound := Kakeya.ml1Boot.TrialRestartW94.lineAmplificationBoundW95 3 1 10 * (2 * 223 ^ 6)
  let edLoss := Kakeya.ml1Boot.TrialRestartW94.lineSelectionMultiplicityW95 3 1 lineBound
  have hLineBound : 1 ≤ lineBound := by
    norm_num [lineBound, Kakeya.ml1Boot.TrialRestartW94.lineAmplificationBoundW95]
  have hEDLoss : 0 < edLoss := by
    have hK := (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C 3).le
    have hB : 0 < Kakeya.ml1Boot.TrialRestartW94.lineAmplificationBoundW95 3 1
        (Kakeya.Tube.tubeOverlapCoreClose.C 3) := by
      apply Nat.ceil_pos.mpr
      have hKm : 0 ≤ Kakeya.Tube.tubeOverlapCoreClose.C 3 - 1 := sub_nonneg.mpr hK
      positivity
    exact Nat.mul_pos hB (lt_of_lt_of_le Nat.zero_lt_one hLineBound)
  let packingCoefficient : ℝ := (edLoss : ℝ) * Tube.card_le_of_EssDistinct.C 3
  have hPackingCoefficient : 0 < packingCoefficient := by
    exact mul_pos (by exact_mod_cast hEDLoss) Tube.card_le_of_EssDistinct.C_pos
  obtain ⟨logCoefficient, dLog, hLogCoefficient, hdLog, hdLogSmall, hCardLog⟩ :=
    hCardLogEnvelope packingCoefficient hPackingCoefficient 6
  let thetaCoefficient : ℝ := 8 * (m + 2) * (coarseDegree : ℝ) ^ (m + 1) *
    (edLoss : ℝ) * logCoefficient ^ (m + 2)
  let shadeCost : ENNReal := 384 * ((Tube.volume_le.C 3 : ENNReal) /
    (Tube.le_volume.c 3 : ENNReal) * 4)
  have hPreparationAtRadius {delta : NNReal} (hdelta : 0 < delta) (hsmall : delta ≤ 1 / 200)
      (hlogSmall : (delta : ℝ) ≤ dLog)
      {I : Type uI} (s : Finset I) (V : I → ShadedTube delta Kakeya.Point3)
      (hball : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1)
      {C : NNReal} (input : ShadedTube.ShadedUniformTubeSet s V (Tube.ssfGridLen delta) C)
      (density A : ENNReal) (hdensity : 0 < density)
      (hfullness : density ≤ ShadedBody.fullness' s (fun i => (V i).toShadedBody))
      (hFrostman : input.tubeUniform.IsFrostmanAtEveryScale A)
      (gridIndex : Fin (m + 1) → ℕ) (hN : 0 < Tube.ssfGridLen delta)
      (hGrid : ∀ k, gridIndex k ≤ Tube.ssfGridLen delta)
      (hGridSmall : ∀ k, Tube.gridScale delta (Tube.ssfGridLen delta) (gridIndex k) ≤ 1 / 1024) :
      ∃ selected : Finset I, ∃ refined : I → ShadedTube delta Kakeya.Point3,
      ∃ theta : ℝ, ∃ prepared : FiniteParentCoverData selected refined (m + 1)
        (ENNReal.ofReal (4 / theta)),
        0 < theta ∧ selected.Nonempty ∧
        (∀ k, prepared.rho k = 1024 * Tube.gridScale delta (Tube.ssfGridLen delta) (gridIndex k)) ∧
        (∀ i ∈ selected, (refined i).carrier ⊆ Metric.closedBall 0 1) ∧
        (toTubeFamily selected (fun i => (refined i).toTube)).IsEssentiallyDistinct ∧
        volume (⋃ i ∈ selected, (refined i).shade) ≤ volume (⋃ i ∈ s, (V i).shade) ∧
        (∀ k, ∀ j ∈ prepared.parentSet k,
          ConvexSpaceBody.IsFrostmanIn (Tube.coverClass selected (prepared.assign k) j)
            (fun i => (refined i).toConvexSpaceBody) (prepared.parentTube k j).toConvexSpaceBody
            (2 * ((512 * A * DirectCenteredRoute.unitParentVolumeCost 3) * ENNReal.ofReal theta⁻¹))) ∧
        ENNReal.ofReal theta⁻¹ ≤ ENNReal.ofReal thetaCoefficient *
          ENNReal.ofReal (Real.log (1 / (delta : ℝ))) ^ (m + 2) / density ∧
        density / (2 * shadeCost) ≤
          ShadedBody.fullness' selected (fun i => (refined i).toShadedBody) := by
    have hdeltaOne : delta ≤ 1 := hsmall.trans (by exact_mod_cast (show (1 : ℝ) / 200 ≤ 1 by norm_num))
    have hs : s.Nonempty := by
      by_contra h
      simp only [Finset.not_nonempty_iff_eq_empty.mp h, ShadedBody.fullness',
        Finset.sum_empty, ENNReal.zero_div] at hfullness
      exact (not_le_of_gt hdensity) hfullness
    obtain ⟨dense, hDenseSub, hDenseNe, hDenseCard, hDensePoint⟩ :=
      hDenseSource hdelta hdeltaOne s V hs density hdensity hfullness
    let scale := fun k : Fin (m + 1) => Tube.gridScale delta (Tube.ssfGridLen delta) (gridIndex k)
    have hScalePos k : 0 < scale k := Tube.gridScale_pos hdelta _ _
    have hScaleOne k : scale k ≤ 1 := (hGridSmall k).trans
      (by exact_mod_cast (show (1 : ℝ) / 1024 ≤ 1 by norm_num))
    have hdeltaScale k : delta ≤ scale k := by
      have h := Tube.gridScale_antitone hdelta hdeltaOne (Tube.ssfGridLen delta) (hGrid k)
      rwa [Tube.gridScale_self delta hN] at h
    have hCoarse k := DirectCenteredRoute.exists_grid_centered_parent_cover
      (show Module.finrank ℝ Kakeya.Point3 = 3 by simp) hdelta s (fun i => (V i).toTube)
      hs hball input.tubeUniform.cover (gridIndex k) (hGrid k)
      ((hGridSmall k).trans (by exact_mod_cast (show (1 : ℝ) / 1024 ≤ 1 / 200 by norm_num)))
    choose coarseSet coarseMap coarse hCoarseNe hCoarseSub hCoarseImage hCoarseRawImage
      hCoarseCenter hCoarseMid hCoarseBall hCoarseLine hCoarseNodeCover hCoarseCover using hCoarse
    let coarseParent := fun k i => coarseMap k (input.tubeUniform.cover.assign (gridIndex k) i)
    have hCoarseMem k i (hi : i ∈ s) : coarseParent k i ∈ coarseSet k := by
      rw [← hCoarseRawImage k]
      exact Finset.mem_image_of_mem _ hi
    have hHalfPos k : 0 < scale k / 2 := div_pos (hScalePos k) (by norm_num)
    have hHalfOne k : scale k / 2 ≤ 1 := (div_le_self zero_le (by norm_num)).trans (hScaleOne k)
    have hHalfScale k : delta / 2 ≤ scale k / 2 :=
      div_le_div_of_nonneg_right (hdeltaScale k) (by norm_num)
    obtain ⟨fineSet, fineParent, Z, coherent, band, oldDescended,
      hFineNe, hFineSub, hFineImage, hFineBall, hFineCenter, hFineLine, hFineCover,
      hFineUnion, hFineDensity, hCoherentSub, hBandSub, hBandNe, hCoherentInj,
      hCoherentCard, hBandRawNe, hBandDense, hBandMass, hBandBalance, hOldDescended⟩ :=
      DirectCenteredRoute.exists_balanced_geometric_original_atoms
        (show Module.finrank ℝ Kakeya.Point3 = 3 by simp) hdelta hsmall s dense V
        hDenseSub hDenseNe (fun i hi => hball i (hDenseSub hi)) (density / 2) hDensePoint
        (fun k => scale k / 2) hHalfPos hHalfOne hHalfScale coarseSet coarse coarseParent
        hCoarseMem hCoarseLine (fun k j hj => by
          have h := hCoarseMid k j hj
          have heq : (coarse k j).center = (coarse k j).midpoint := by
            simp only [Tube.center, Tube.midpoint, midpoint_eq_smul_add]
            norm_num
          rw [heq]
          exact h.trans (by norm_num)) hCoarseCover
    let Atoms := Option I × (Fin (m + 1) → I)
    let code := DirectCenteredRoute.denseJointCode dense fineParent coarseParent
    have hBandSource : band ⊆ s.image code := hBandSub.trans hCoherentSub
    obtain ⟨projection, hProjectionInj, hProjection, hProjectionSub⟩ :=
      DirectCenteredRoute.exists_original_fine_projection s dense fineParent coarseParent
        band hBandSource hBandNe (hCoherentInj.mono (Finset.coe_subset.mpr hBandSub)) hBandDense
    obtain ⟨level, hLevel, hLevelBounds⟩ := DirectCenteredRoute.exists_atom_weight_level
      s code band hBandSource hBandNe hBandBalance
    let parent := fun k (a : Atoms) => a.2 k
    let newParent := fun k j => (coarse k j).rescale (1024 * scale k)
    have hNewCoarseCover k i (hi : i ∈ s) :
        (V i).toConvexSpaceBody.homothety 0 (1 / 8) ≤
          (newParent k (parent k (code i))).toConvexSpaceBody := by
      have hscale : scale k / 2 ≤ 1024 * scale k :=
        (div_le_self zero_le (by norm_num)).trans (le_mul_of_one_le_left zero_le (by norm_num))
      have h := (hCoarseCover k i hi).trans ((coarse k _).le_rescale hscale)
      change AffineMap.homothety (0 : Kakeya.Point3) (1 / 8) '' (V i).carrier ⊆ _
      simpa [AffineMap.homothety_apply, parent, code, DirectCenteredRoute.denseJointCode] using h
    have hFineRestoredInside k i (hi : i ∈ dense) :
        ((Z (fineParent i)).toTube.rescale delta).toConvexSpaceBody ≤
          (newParent k (coarseParent k i)).toConvexSpaceBody := by
      have hq : fineParent i ∈ fineSet := by
        rw [← hFineImage]
        exact Finset.mem_image_of_mem fineParent hi
      have h0 := DirectCenteredRoute.centered_common_leaf_le_unit_parent
        (hHalfOne k) (hHalfScale k) (V i).toTube (Z (fineParent i)).toTube
        (coarse k (coarseParent k i))
        (by simpa only [Kakeya.ml1Boot.TrialRestartW94.centredTubeW94, Tube.IsCentred,
          Tube.center, midpoint_eq_smul_add, invOf_eq_inv, Tube.midpoint, one_div] using hFineCenter _ hq)
        (hCoarseCenter k _ (hCoarseMem k i (hDenseSub hi)))
        ((Z (fineParent i)).toTube.norm_midpoint_le_of_subset_ball
          (div_pos hdelta (by norm_num)) (hFineBall _ hq))
        (hFineCover i hi) (hCoarseCover k i (hDenseSub hi))
      have hBudget : 1024 * (scale k / 2) + delta ≤ 1024 * scale k := by
        have h := show (delta : ℝ) ≤ scale k from hdeltaScale k
        apply NNReal.coe_le_coe.mp
        simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_ofNat]
        linarith [NNReal.coe_nonneg (scale k)]
      have h := Tube.rescale_le_rescale_of_body_le (Z (fineParent i)).toTube
        ((coarse k (coarseParent k i)).rescale (1024 * (scale k / 2)))
        (div_le_self zero_le (by norm_num)) hBudget h0
      simpa only [Tube.rescale_rescale] using h
    let refined : I → ShadedTube delta Kakeya.Point3 := fun i => {
      toTube := (Z i).toTube.rescale delta
      shade := (Z i).shade
      measurableSet_shade := (Z i).measurableSet_shade
      shade_subset := (Z i).shade_subset.trans
        ((Z i).toTube.le_rescale (div_le_self zero_le (by norm_num)))
    }
    have hRefinedBall i (hi : i ∈ fineSet) : (refined i).carrier ⊆ Metric.closedBall 0 1 := by
      exact DirectCenteredRoute.restored_fine_carrier_subset_unit_ball
        (hsmall.trans (by exact_mod_cast (show (1 : ℝ) / 200 ≤ 1 / 2 by norm_num)))
        (Z i).toTube (hFineBall i hi)
    have hFineNorm j (hj : j ∈ fineSet) : ‖(Z j).toTube.center‖ ≤ 1 := by
      have h := (Z j).toTube.norm_midpoint_le_of_subset_ball
        (div_pos hdelta (by norm_num)) (hFineBall j hj)
      simpa only [Tube.center, midpoint_eq_smul_add, Tube.midpoint, invOf_eq_inv,
        one_div] using h.trans (by norm_num : (3 / 4 : ℝ) ≤ 1)
    have hRefinedNorm j (hj : j ∈ fineSet) : ‖(refined j).toTube.center‖ ≤ 1 := by
      simpa only [refined, Tube.rescale, Tube.center, Tube.mk'_x, Tube.mk'_y] using hFineNorm j hj
    let lineA := Kakeya.ml1Boot.TrialRestartW94.lineAmplificationBoundW95 3 1 10 * (2 * 223 ^ 6)
    have hLineA : 1 ≤ lineA := by norm_num [lineA, Kakeya.ml1Boot.TrialRestartW94.lineAmplificationBoundW95]
    have hRefinedLine : Kakeya.VeryNotSticky.IsLineEssDistinct lineA fineSet
        (fun i => (refined i).toTube) := by
      intro o v hv
      have hsub : fineSet.filter (fun i => (refined i).carrier ⊆
          Kakeya.VeryNotSticky.lineNbhd o v (5 * (delta : ℝ))) ⊆
          Kakeya.ml1Boot.TrialRestartW94.nearLineFamilyW95 fineSet
            (fun i => (Z i).toTube) o v 10 := by
        intro i hi
        obtain ⟨hi, hcontain⟩ := Finset.mem_filter.mp hi
        refine Finset.mem_filter.mpr ⟨hi, ?_⟩
        have h := (show (Z i).carrier ⊆ (refined i).carrier from
          (Z i).toTube.le_rescale (div_le_self zero_le (by norm_num))).trans hcontain
        convert h using 1 <;> simp only [NNReal.coe_div, NNReal.coe_ofNat] <;> congr 1 <;> ring
      have h := Kakeya.ml1Boot.TrialRestartW94.line_aperture_card_w103
        (div_pos hdelta (by norm_num)) ((div_le_self zero_le (by norm_num)).trans hdeltaOne)
        fineSet (fun i => (Z i).toTube) (2 * (223 : NNReal) ^ 6) hFineLine
        1 10 (by norm_num) (by norm_num) hFineNorm o v hv
      have hdim : Module.finrank ℝ Kakeya.Point3 = 3 := by simp
      rw [hdim] at h
      exact_mod_cast (show ((fineSet.filter (fun i => (refined i).carrier ⊆
          Kakeya.VeryNotSticky.lineNbhd o v (5 * (delta : ℝ)))).card : NNReal) ≤ _ from
        (show ((fineSet.filter (fun i => (refined i).carrier ⊆
          Kakeya.VeryNotSticky.lineNbhd o v (5 * (delta : ℝ)))).card : NNReal) ≤
          (Kakeya.ml1Boot.TrialRestartW94.nearLineFamilyW95 fineSet
            (fun i => (Z i).toTube) o v 10).card by exact_mod_cast Finset.card_le_card hsub).trans h)
    obtain ⟨packingSelection, hPackingSub, hPackingED, hPackingMass⟩ :=
      hWeightedED hdelta hdeltaOne fineSet (fun i => (refined i).toTube)
        hRefinedNorm lineA hLineA hRefinedLine (fun _ => 1)
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hPackingMass
    have hFineCard : (fineSet.card : ℝ) ≤ packingCoefficient * (delta : ℝ) ^ (-6 : ℝ) := by
      have hcard := Tube.card_le_of_EssDistinct hdelta 1 packingSelection
        (fun i => (refined i).toTube) (fun i hi => hRefinedBall i (hPackingSub hi)) hPackingED
      simp only [show Module.finrank ℝ Kakeya.Point3 = 3 by simp,
        show 2 * 3 = 6 by norm_num] at hcard
      have hmass : (fineSet.card : ℝ) ≤ (edLoss : ℝ) * packingSelection.card := by
        exact_mod_cast hPackingMass
      calc
        _ ≤ (edLoss : ℝ) * packingSelection.card := hmass
        _ ≤ (edLoss : ℝ) * (Tube.card_le_of_EssDistinct.C 3 * (1 / (delta : ℝ)) ^ 6) :=
          mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg _)
        _ = _ := by
          rw [Real.rpow_neg (show 0 ≤ (delta : ℝ) from delta.coe_nonneg)]
          simp only [packingCoefficient, one_div, inv_pow, Real.rpow_ofNat]
          ring
    let rawBand := s.filter fun i => code i ∈ band
    let fineWeight := fun q => ((rawBand.filter fun i => projection (code i) = q).card : ENNReal)
    obtain ⟨edFine, hEDSub, hED, hEDMass⟩ := hWeightedED hdelta hdeltaOne fineSet
      (fun i => (refined i).toTube) hRefinedNorm lineA hLineA hRefinedLine fineWeight
    let edBand := band.filter fun a => projection a ∈ edFine
    have hEDBandSub : edBand ⊆ band := Finset.filter_subset _ _
    let weight := fun a : Atoms => ((s.filter fun i => code i = a).card : ℝ)
    have hRawSum (atoms : Finset Atoms) (ha : atoms ⊆ s.image code) :
        ∑ a ∈ atoms, weight a = ((s.filter fun i => code i ∈ atoms).card : ℝ) := by
      dsimp only [weight]
      exact_mod_cast Finset.sum_card_fiberwise_eq_card_filter s atoms code
    have hBandFine i (hi : i ∈ rawBand) : projection (code i) ∈ fineSet := by
      rw [hProjection i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2, ← hFineImage]
      exact Finset.mem_image_of_mem fineParent (hBandDense hi)
    have hFineSum (F : Finset I) :
        ∑ q ∈ F, fineWeight q = ((rawBand.filter fun i => projection (code i) ∈ F).card : ENNReal) := by
      dsimp only [fineWeight]
      exact_mod_cast Finset.sum_card_fiberwise_eq_card_filter rawBand F (fun i => projection (code i))
    have hFullFineSum : ∑ q ∈ fineSet, fineWeight q = (rawBand.card : ENNReal) := by
      rw [hFineSum, Finset.filter_eq_self.mpr hBandFine]
    have hEDRaw : rawBand.filter (fun i => projection (code i) ∈ edFine) =
        s.filter fun i => code i ∈ edBand := by
      ext i
      simp only [rawBand, edBand, Finset.mem_filter, and_assoc]
    rw [hFullFineSum, hFineSum, hEDRaw] at hEDMass
    have hEDRawNe : (s.filter fun i => code i ∈ edBand).Nonempty := by
      by_contra h
      have hzero := Finset.not_nonempty_iff_eq_empty.mp h
      rw [hzero, Finset.card_empty, Nat.cast_zero, mul_zero] at hEDMass
      have hpositive : (0 : ENNReal) < rawBand.card := by exact_mod_cast hBandRawNe.card_pos
      exact (not_le_of_gt hpositive) hEDMass
    have hEDWeight : 0 < ∑ a ∈ edBand, weight a := by
      rw [hRawSum edBand (hEDBandSub.trans hBandSource)]
      exact_mod_cast hEDRawNe.card_pos
    obtain ⟨initial, hInitialSub, hInitialNe, hInitialMass, hInitialClasses⟩ :=
      hSelectComparableBandClasses edBand weight hEDWeight (m + 1) parent
    have hInitialSource : initial ⊆ s.image code := hInitialSub.trans (hEDBandSub.trans hBandSource)
    have hInitialRawNe : (s.filter fun i => code i ∈ initial).Nonempty := by
      obtain ⟨a, ha⟩ := hInitialNe
      obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp (hInitialSource ha)
      exact ⟨i, Finset.mem_filter.mpr ⟨hi, hia ▸ ha⟩⟩
    have hInitialBand : initial ⊆ band := hInitialSub.trans hEDBandSub
    have hInitialCover i (hi : i ∈ s) (hai : code i ∈ initial) :
        (V i).toConvexSpaceBody.homothety 0 (1 / 8) ≤
          (refined (projection (code i))).toConvexSpaceBody := by
      have hidense := hBandDense (Finset.mem_filter.mpr ⟨hi, hInitialBand hai⟩)
      rw [hProjection i hi (hInitialBand hai)]
      have h := (hFineCover i hidense).trans
        ((Z (fineParent i)).toTube.le_rescale (div_le_self zero_le (by norm_num)))
      change AffineMap.homothety (0 : Kakeya.Point3) (1 / 8) '' (V i).carrier ⊆ _
      simpa [AffineMap.homothety_apply] using h
    have hInitialFineInside k i (hi : i ∈ s) (hai : code i ∈ initial) :
        (refined (projection (code i))).toConvexSpaceBody ≤
          (newParent k (parent k (code i))).toConvexSpaceBody := by
      rw [hProjection i hi (hInitialBand hai)]
      exact hFineRestoredInside k i (hBandDense (Finset.mem_filter.mpr ⟨hi, hInitialBand hai⟩))
    have hParentRatio k j :
        volume (newParent k j).carrier /
          volume (input.tubeUniform.cover.tube (gridIndex k) j).carrier ≤
            DirectCenteredRoute.unitParentVolumeCost 3 := by
      have hsmallR : 1024 * scale k ≤ 1 := by
        have h := show (scale k : ℝ) ≤ 1 / 1024 from hGridSmall k
        apply NNReal.coe_le_coe.mp
        simp only [NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_one]
        linarith
      have h := hUnitParentRatio (hScalePos k) (hScaleOne k) le_rfl hsmallR
        ((coarse k j).rescale (scale k)) (input.tubeUniform.cover.tube (gridIndex k) j)
      simpa only [Tube.rescale_rescale] using h
    obtain ⟨selectedAtoms, assigned, hSelectedSub, hSelectedNe, hSelectedRawNe,
        hHalf, hAssigned, hSelectedFrostman, hCoreCount⟩ :=
      hActualAtomQuotientConstruction hdelta hdeltaOne s (fun i => (V i).toTube)
        (Tube.ssfGridLen delta) C input.tubeUniform A (DirectCenteredRoute.unitParentVolumeCost 3) 2
        hFrostman (m + 1) gridIndex hGrid code projection parent coarseMap (fun _ _ _ => rfl)
        initial hInitialSource hInitialRawNe (hProjectionInj.mono (Finset.coe_subset.mpr hInitialBand))
        (fun a ha b hb => hBandBalance a (hInitialBand ha) b (hInitialBand hb))
        (fun i => (refined i).toTube) (fun k j => (newParent k j).toConvexSpaceBody)
        hNewCoarseCover hInitialCover hInitialFineInside (fun k j _ => hParentRatio k j)
    let selected := selectedAtoms.image projection
    let theta := ((s.filter fun i => code i ∈ initial).card : ℝ) /
      (2 * ((m + 1 : ℕ) + 1 : ℝ) * (s.card : ℝ))
    have htheta : 0 < theta := by
      have h1 : (0 : ℝ) < (s.filter fun i => code i ∈ initial).card := by exact_mod_cast hInitialRawNe.card_pos
      have h2 : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
      dsimp only [theta]
      positivity
    have hAtomSource : selectedAtoms ⊆ s.image code := hSelectedSub.trans hInitialSource
    have hSelectedBand : selectedAtoms ⊆ edBand := hSelectedSub.trans hInitialSub
    have hSelectedInj : Set.InjOn projection (selectedAtoms : Set Atoms) :=
      hProjectionInj.mono (Finset.coe_subset.mpr (hSelectedBand.trans hEDBandSub))
    have hAssignedAtom k a (ha : a ∈ selectedAtoms) : assigned k (projection a) = parent k a := by
      obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp (hAtomSource ha)
      have h := hAssigned i (Finset.mem_filter.mpr ⟨hi, hia ▸ ha⟩) k
      simpa only [hia] using h
    have hParentImage k : selected.image (assigned k) = selectedAtoms.image (parent k) := by
      simp only [selected, Finset.image_image]
      apply Finset.image_congr
      exact fun a ha => hAssignedAtom k a ha
    have hClassImage k j : Tube.coverClass selected (assigned k) j =
        (selectedAtoms.filter fun a => parent k a = j).image projection := by
      ext q
      constructor
      · intro hq
        obtain ⟨hq, hqj⟩ := Finset.mem_filter.mp hq
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
        exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr
          ⟨ha, (hAssignedAtom k a ha).symm.trans hqj⟩, rfl⟩
      · intro hq
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
        obtain ⟨ha, haj⟩ := Finset.mem_filter.mp ha
        exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem projection ha,
          (hAssignedAtom k a ha).trans haj⟩
    have hClassCard k j : (Tube.coverClass selected (assigned k) j).card =
        (selectedAtoms.filter fun a => parent k a = j).card := by
      rw [hClassImage]
      exact Finset.card_image_of_injOn (hSelectedInj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))
    have hClassRatio k a (ha : a ∈ selected.image (assigned k)) b (hb : b ∈ selected.image (assigned k)) :
        ((Tube.coverClass selected (assigned k) a).card : ENNReal) ≤
          ENNReal.ofReal (4 / theta) * ((Tube.coverClass selected (assigned k) b).card : ENNReal) := by
      rw [hParentImage] at ha hb
      have h := hSameCoreClassRatio s code edBand selectedAtoms hSelectedBand (parent k)
        level theta hLevel htheta (fun a ha => hLevelBounds a (hEDBandSub ha))
        (fun a ha b hb => hInitialClasses k a (Finset.image_subset_image hSelectedSub ha)
          b (Finset.image_subset_image hSelectedSub hb)) (hCoreCount k) a ha b hb
      rw [hClassCard, hClassCard]
      have ho := ENNReal.ofReal_le_ofReal h
      simpa only [ENNReal.ofReal_mul (by positivity : 0 ≤ 4 / theta), ENNReal.ofReal_natCast] using ho
    have hSelectedFine : selected ⊆ edFine := by
      intro q hq
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
      exact (Finset.mem_filter.mp (hSelectedBand ha)).2
    have hContain k q (hq : q ∈ selected) :
        (refined q).toConvexSpaceBody ≤ (newParent k (assigned k q)).toConvexSpaceBody := by
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp (hAtomSource ha)
      rw [hAssignedAtom k a ha, ← hia]
      exact hInitialFineInside k i hi (hSelectedSub (hia ▸ ha))
    let prepared : FiniteParentCoverData selected refined (m + 1) (ENNReal.ofReal (4 / theta)) := {
      rho := fun k => 1024 * scale k
      parentSet := fun k => selected.image (assigned k)
      assign := assigned
      parentTube := newParent
      assign_mem := fun k i hi => Finset.mem_image_of_mem (assigned k) hi
      fine_containment := hContain
      class_ratio := hClassRatio
    }
    refine ⟨selected, refined, theta, prepared, htheta, hSelectedNe.image projection,
      fun _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun i hi => hRefinedBall i (hEDSub (hSelectedFine hi))
    · exact (toTubeFamily_isEssentiallyDistinct_iff _ _).mpr
        (hED.mono (Finset.coe_subset.mpr hSelectedFine))
    · calc
        _ ≤ volume (⋃ i ∈ fineSet, (Z i).shade) := by
          apply measure_mono
          intro x hx
          obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp hx
          exact Set.mem_iUnion₂.mpr ⟨i, hEDSub (hSelectedFine hi), hx⟩
        _ = (1 / 512 : ENNReal) * volume (⋃ i ∈ dense, (V i).shade) := hFineUnion
        _ ≤ volume (⋃ i ∈ dense, (V i).shade) := mul_le_of_le_one_left' (by norm_num)
        _ ≤ _ := measure_mono (Set.iUnion₂_mono' fun i hi => ⟨i, hDenseSub hi, Set.Subset.refl _⟩)
    · intro k j hj
      exact hSelectedFrostman k j ((hParentImage k) ▸ hj)
    · have hdensityTop : density ≠ ⊤ :=
        ne_top_of_le_ne_top (ShadedBody.fullness'_ne_top s (fun i => (V i).toShadedBody)) hfullness
      have hdensityReal : 0 < density.toReal := ENNReal.toReal_pos hdensity.ne' hdensityTop
      have hDenseCardR : density.toReal / 2 * (s.card : ℝ) ≤ dense.card := by
        have h := ENNReal.toReal_mono (by simp : (dense.card : ENNReal) ≠ ⊤) hDenseCard
        simpa only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_natCast,
          ENNReal.toReal_ofNat] using h
      have hEDMassR : (rawBand.card : ℝ) ≤
          (edLoss : ℝ) * (s.filter fun i => code i ∈ edBand).card := by exact_mod_cast hEDMass
      let Lc := 1 + Real.logb 2 (2 * (coherent.card : ℝ))
      let Le := 1 + Real.logb 2 (edBand.card : ℝ)
      have hCoherentPoly : (coherent.card : ℝ) ≤ packingCoefficient * (delta : ℝ) ^ (-6 : ℝ) :=
        (by exact_mod_cast hCoherentCard : (coherent.card : ℝ) ≤ fineSet.card).trans hFineCard
      have hEDPoly : (edBand.card : ℝ) ≤ packingCoefficient * (delta : ℝ) ^ (-6 : ℝ) :=
        (by exact_mod_cast Finset.card_le_card (hEDBandSub.trans hBandSub) :
          (edBand.card : ℝ) ≤ coherent.card).trans hCoherentPoly
      have hLc := hCardLog (delta : ℝ) hdelta hlogSmall coherent.card hCoherentPoly
      have hLe := hCardLog (delta : ℝ) hdelta hlogSmall edBand.card hEDPoly
      have hEdCardOne : (1 : ℝ) ≤ edBand.card := by
        exact_mod_cast (hInitialNe.mono hInitialSub).card_pos
      have hLeNonneg : 0 ≤ Le := by
        have hlog : 0 ≤ Real.log (edBand.card : ℝ) := Real.log_nonneg hEdCardOne
        have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
        dsimp [Le, Real.logb]
        positivity
      have hLeUpper : Le ≤ logCoefficient * Real.log (1 / (delta : ℝ)) := by
        apply le_trans (b := 1 + Real.logb 2 (2 * (edBand.card : ℝ))) ?_ hLe.2
        dsimp [Le, Real.logb]
        apply add_le_add_right
        apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num)).le
        apply Real.log_le_log (lt_of_lt_of_le zero_lt_one hEdCardOne)
        nlinarith only [hEdCardOne]
      have hInitialMassR : ((s.filter fun i => code i ∈ edBand).card : ℝ) ≤
          Le ^ (m + 1) * (s.filter fun i => code i ∈ initial).card := by
        rw [hRawSum edBand (hEDBandSub.trans hBandSource), hRawSum initial hInitialSource] at hInitialMass
        exact hInitialMass
      have hBandMassR : (dense.card : ℝ) ≤ (coarseDegree : ℝ) ^ (m + 1) *
          (2 * Lc) * rawBand.card := by
        simpa only [Nat.cast_pow] using hBandMass
      have hchain : density.toReal / 2 * (s.card : ℝ) ≤
          2 * (coarseDegree : ℝ) ^ (m + 1) * (edLoss : ℝ) * Lc * Le ^ (m + 1) *
            (s.filter fun i => code i ∈ initial).card := by
        calc
          _ ≤ (dense.card : ℝ) := hDenseCardR
          _ ≤ (coarseDegree : ℝ) ^ (m + 1) * (2 * Lc) * rawBand.card := hBandMassR
          _ ≤ (coarseDegree : ℝ) ^ (m + 1) * (2 * Lc) *
              ((edLoss : ℝ) * (s.filter fun i => code i ∈ edBand).card) := by
            exact mul_le_mul_of_nonneg_left hEDMassR
              (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (mul_nonneg (by norm_num) hLc.1))
          _ ≤ (coarseDegree : ℝ) ^ (m + 1) * (2 * Lc) *
              ((edLoss : ℝ) * (Le ^ (m + 1) * (s.filter fun i => code i ∈ initial).card)) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hInitialMassR (Nat.cast_nonneg _))
              (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (mul_nonneg (by norm_num) hLc.1))
          _ = _ := by ring
      have hInitialCardPos : (0 : ℝ) < (s.filter fun i => code i ∈ initial).card := by
        exact_mod_cast hInitialRawNe.card_pos
      have hshare : density.toReal * (s.card : ℝ) /
          (s.filter fun i => code i ∈ initial).card ≤
          4 * (coarseDegree : ℝ) ^ (m + 1) * (edLoss : ℝ) * Lc * Le ^ (m + 1) := by
        apply (div_le_iff₀ hInitialCardPos).mpr
        nlinarith only [hchain]
      have hthetaInv : theta⁻¹ =
          2 * ((m : ℝ) + 2) * (s.card : ℝ) / (s.filter fun i => code i ∈ initial).card := by
        dsimp [theta]
        simp only [inv_div, Nat.cast_add, Nat.cast_one]
        ring
      have hcross : density.toReal * theta⁻¹ ≤
          thetaCoefficient * Real.log (1 / (delta : ℝ)) ^ (m + 2) := by
        calc
          _ = (2 * ((m : ℝ) + 2)) *
              (density.toReal * (s.card : ℝ) / (s.filter fun i => code i ∈ initial).card) := by
            rw [hthetaInv]
            ring
          _ ≤ (2 * ((m : ℝ) + 2)) *
              (4 * (coarseDegree : ℝ) ^ (m + 1) * (edLoss : ℝ) * Lc * Le ^ (m + 1)) :=
            mul_le_mul_of_nonneg_left hshare
              (mul_nonneg (by norm_num) (add_nonneg (Nat.cast_nonneg _) (by norm_num)))
          _ ≤ (2 * ((m : ℝ) + 2)) *
              (4 * (coarseDegree : ℝ) ^ (m + 1) * (edLoss : ℝ) *
                (logCoefficient * Real.log (1 / (delta : ℝ))) *
                (logCoefficient * Real.log (1 / (delta : ℝ))) ^ (m + 1)) := by
            apply mul_le_mul_of_nonneg_left _
              (mul_nonneg (by norm_num) (add_nonneg (Nat.cast_nonneg _) (by norm_num)))
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left hLc.2
                (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (Nat.cast_nonneg _) _))
                  (Nat.cast_nonneg _))
            · exact pow_le_pow_left₀ hLeNonneg hLeUpper _
            · exact pow_nonneg hLeNonneg _
            · exact mul_nonneg
                (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (Nat.cast_nonneg _) _))
                  (Nat.cast_nonneg _)) (hLc.1.trans hLc.2)
          _ = _ := by
            dsimp [thetaCoefficient]
            rw [mul_pow, show m + 2 = (m + 1) + 1 by rfl, pow_succ, pow_succ]
            ring
      have hquotient : theta⁻¹ ≤
          (thetaCoefficient * Real.log (1 / (delta : ℝ)) ^ (m + 2)) / density.toReal := by
        apply (le_div_iff₀ hdensityReal).mpr
        simpa only [mul_comm] using hcross
      have hlogPos : 0 ≤ Real.log (1 / (delta : ℝ)) := by
        apply Real.log_nonneg
        apply (le_div_iff₀ (show 0 < (delta : ℝ) from hdelta)).mpr
        simpa only [one_mul] using (show (delta : ℝ) ≤ 1 from hdeltaOne)
      have h := ENNReal.ofReal_mono hquotient
      rw [ENNReal.ofReal_div_of_pos hdensityReal, ENNReal.ofReal_toReal hdensityTop,
        ENNReal.ofReal_mul (show 0 ≤ thetaCoefficient from
          mul_nonneg
            (mul_nonneg
              (mul_nonneg (mul_nonneg (by norm_num)
                (add_nonneg (Nat.cast_nonneg _) (by norm_num)))
                (pow_nonneg (Nat.cast_nonneg _) _)) (Nat.cast_nonneg _))
            (pow_nonneg hLogCoefficient.le _)),
        ENNReal.ofReal_pow hlogPos] at h
      exact h
    · have hcostZero : shadeCost ≠ 0 := by
        dsimp [shadeCost]
        have hC : (Tube.volume_le.C 3 : ENNReal) ≠ 0 := by
          exact_mod_cast (Tube.volume_le.C_pos 3).ne'
        exact mul_ne_zero (by norm_num)
          (mul_ne_zero (ENNReal.div_ne_zero.mpr ⟨hC, ENNReal.coe_ne_top⟩) (by norm_num))
      have hcostTop : shadeCost ≠ ⊤ := by
        dsimp [shadeCost]
        have hc : (Tube.le_volume.c 3 : ENNReal) ≠ 0 := by
          exact_mod_cast (Tube.le_volume.c_pos 3).ne'
        finiteness
      have hpoint i (hi : i ∈ fineSet) :
          (density / 2) * volume (refined i).carrier ≤ shadeCost * volume (refined i).shade :=
        hRestoredDensity hdeltaOne (Z i) (density / 2) (hFineDensity i hi)
      have h := (hHereditaryShade hdelta hdeltaOne fineSet selected
        (hSelectedFine.trans hEDSub) (hSelectedNe.image projection) refined
        (density / 2) shadeCost hcostZero hcostTop hpoint
        (⋃ i ∈ fineSet, (refined i).shade) le_rfl).1
      have hdiv : density / 2 / shadeCost = density / (2 * shadeCost) := by
        simp only [div_eq_mul_inv]
        rw [ENNReal.mul_inv (a := (2 : ENNReal)) (b := shadeCost)
          (Or.inl (by norm_num)) (Or.inl (by norm_num))]
        ring
      rwa [hdiv] at h
  let inputLoss := alpha / 4
  have hInputLoss : 0 < inputLoss := by dsimp [inputLoss]; positivity
  let R := DirectCenteredRoute.unitParentVolumeCost 3
  let overhead : ENNReal := (4 + 1024 * R) * ENNReal.ofReal thetaCoefficient
  have hRtop : R ≠ ⊤ := DirectCenteredRoute.unitParentVolumeCost_ne_top 3
  have hOverhead : overhead ≠ ⊤ := by dsimp [overhead]; finiteness
  have hShadeZero : (2 * shadeCost : ENNReal) ≠ 0 := by
    dsimp [shadeCost]
    have hC : (Tube.volume_le.C 3 : ENNReal) ≠ 0 := by
      exact_mod_cast (Tube.volume_le.C_pos 3).ne'
    exact mul_ne_zero (by norm_num) (mul_ne_zero (by norm_num)
      (mul_ne_zero (ENNReal.div_ne_zero.mpr ⟨hC, ENNReal.coe_ne_top⟩) (by norm_num)))
  have hShadeTop : (2 * shadeCost : ENNReal) ≠ ⊤ := by
    dsimp [shadeCost]
    have hc : (Tube.le_volume.c 3 : ENNReal) ≠ 0 := by
      exact_mod_cast (Tube.le_volume.c_pos 3).ne'
    finiteness
  obtain ⟨dF, hdF, _, hF⟩ := Kakeya.Assouad.exists_logPower_mul_rpow_threshold
    overhead hOverhead (m + 2) (alpha := -2 * inputLoss) (beta := -alpha)
    (by dsimp [inputLoss]; linarith)
  obtain ⟨dH, hdH, _, hH⟩ := Kakeya.Assouad.exists_logPower_mul_rpow_threshold
    overhead hOverhead (m + 2) (alpha := -inputLoss) (beta := -2 * alpha)
    (by dsimp [inputLoss]; linarith)
  obtain ⟨dD, hdD, _, hD⟩ := Kakeya.Assouad.exists_logPower_mul_rpow_threshold
    (2 * shadeCost) hShadeTop 0 (alpha := alpha) (beta := inputLoss)
    (by dsimp [inputLoss]; linarith)
  refine ⟨inputLoss, min (1 / 200) (min dLog (min dF (min dH dD))),
    hInputLoss, by positivity, ?_⟩
  intro delta hdelta hsmall I s V hball C hC input hfullness hFrostman gridIndex hN hGrid hGridSmall
  have hd : (0 : ℝ) < delta := hdelta
  have hsmall200 : delta ≤ 1 / 200 := by exact_mod_cast hsmall.trans (min_le_left _ _)
  have hRest := (le_min_iff.mp hsmall).2
  obtain ⟨hsmallLog, hsmallF, hsmallH, hsmallD⟩ := by
    simpa only [le_min_iff] using hRest
  have hSmallGrid k : Tube.gridScale delta (Tube.ssfGridLen delta) (gridIndex k) ≤ 1 / 1024 := by
    apply NNReal.coe_le_coe.mp
    apply (hGridSmall k).trans
    have hA : 1 ≤ numinaRepresentativeDilation := by
      exact (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C 3).le
    have hden : 0 < 1024 * 200 * (32 * numinaRepresentativeDilation) := by positivity
    apply (div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 1024)).mpr
    change (1 : ℝ) * 1024 ≤ 1 * (1024 * 200 * (32 * numinaRepresentativeDilation))
    nlinarith only [hA]
  have hDensityPos : 0 < ENNReal.ofReal ((delta : ℝ) ^ inputLoss) :=
    ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hd _)
  obtain ⟨selected, refined, theta, prepared, htheta, hSelected, hRho, hSupport, hED,
    hUnion, hClassFrostman, hTheta, hFullness⟩ :=
    hPreparationAtRadius hdelta hsmall200 hsmallLog s V hball input
      (ENNReal.ofReal ((delta : ℝ) ^ inputLoss))
      (ENNReal.ofReal ((delta : ℝ) ^ (-inputLoss))) hDensityPos hfullness hFrostman
      gridIndex hN hGrid hSmallGrid
  have hInverse : (ENNReal.ofReal ((delta : ℝ) ^ inputLoss))⁻¹ =
      Kakeya.realRpowENN (delta : ℝ) (-inputLoss) := by
    change _ = ENNReal.ofReal ((delta : ℝ) ^ (-inputLoss))
    rw [Real.rpow_neg hd.le,
      ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hd _)]
  rw [div_eq_mul_inv, hInverse] at hTheta
  have hSquare : Kakeya.realRpowENN (delta : ℝ) (-inputLoss) *
      Kakeya.realRpowENN (delta : ℝ) (-inputLoss) =
      Kakeya.realRpowENN (delta : ℝ) (-2 * inputLoss) := by
    change ENNReal.ofReal ((delta : ℝ) ^ (-inputLoss)) *
      ENNReal.ofReal ((delta : ℝ) ^ (-inputLoss)) =
        ENNReal.ofReal ((delta : ℝ) ^ (-2 * inputLoss))
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hd.le _), ← Real.rpow_add hd]
    congr 1
    ring
  have hUniform : ENNReal.ofReal (4 / theta) ≤
      Kakeya.realRpowENN (delta : ℝ) (-2 * alpha) := by
    calc
      _ = 4 * ENNReal.ofReal theta⁻¹ := by
        rw [div_eq_mul_inv, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
        norm_num
      _ ≤ 4 * (ENNReal.ofReal thetaCoefficient *
          ENNReal.ofReal (Real.log (1 / (delta : ℝ))) ^ (m + 2) *
            Kakeya.realRpowENN (delta : ℝ) (-inputLoss)) := mul_le_mul_right hTheta 4
      _ ≤ overhead * ENNReal.ofReal (Real.log (1 / (delta : ℝ))) ^ (m + 2) *
          Kakeya.realRpowENN (delta : ℝ) (-inputLoss) := by
        dsimp [overhead]
        calc
          _ ≤ (4 + 1024 * R) * (ENNReal.ofReal thetaCoefficient *
              ENNReal.ofReal (Real.log (1 / (delta : ℝ))) ^ (m + 2) *
                Kakeya.realRpowENN (delta : ℝ) (-inputLoss)) :=
            mul_le_mul_left (le_add_right le_rfl) _
          _ = _ := by ring
      _ ≤ _ := hH (delta : ℝ) hd hsmallH
  have hFinalDensity : Kakeya.realRpowENN (delta : ℝ) alpha ≤
      ShadedBody.fullness' selected (fun i => (refined i).toShadedBody) := by
    apply le_trans ?_ hFullness
    apply (ENNReal.le_div_iff_mul_le (Or.inl hShadeZero) (Or.inl hShadeTop)).mpr
    simpa [Kakeya.realRpowENN, mul_comm] using hD (delta : ℝ) hd hsmallD
  have hFinalFrostman : 2 * ((512 * ENNReal.ofReal ((delta : ℝ) ^ (-inputLoss)) * R) *
      ENNReal.ofReal theta⁻¹) ≤ Kakeya.realRpowENN (delta : ℝ) (-alpha) := by
    calc
      _ ≤ 2 * ((512 * ENNReal.ofReal ((delta : ℝ) ^ (-inputLoss)) * R) *
          (ENNReal.ofReal thetaCoefficient *
            ENNReal.ofReal (Real.log (1 / (delta : ℝ))) ^ (m + 2) *
              Kakeya.realRpowENN (delta : ℝ) (-inputLoss))) :=
          mul_le_mul_right (mul_le_mul_right hTheta _) _
      _ = (1024 * R * ENNReal.ofReal thetaCoefficient) *
          ENNReal.ofReal (Real.log (1 / (delta : ℝ))) ^ (m + 2) *
            Kakeya.realRpowENN (delta : ℝ) (-2 * inputLoss) := by
        rw [← hSquare]
        have hAlg (a b c r : ENNReal) :
            2 * ((512 * a * r) * (b * c * a)) = (1024 * r * b) * c * (a * a) := by ring
        exact hAlg (ENNReal.ofReal ((delta : ℝ) ^ (-inputLoss)))
          (ENNReal.ofReal thetaCoefficient)
          (ENNReal.ofReal (Real.log (1 / (delta : ℝ))) ^ (m + 2)) R
      _ ≤ overhead * ENNReal.ofReal (Real.log (1 / (delta : ℝ))) ^ (m + 2) *
          Kakeya.realRpowENN (delta : ℝ) (-2 * inputLoss) := by
        dsimp [overhead]
        exact mul_le_mul_left (mul_le_mul_left
          (mul_le_mul_left (le_add_left le_rfl) _) _) _
      _ ≤ _ := hF (delta : ℝ) hd hsmallF
  refine ⟨selected, refined, ENNReal.ofReal (4 / theta), prepared, hRho,
    hSelected, hSupport, hED, hUniform, hFinalDensity, hUnion, ?_⟩
  intro k j hj
  exact (hClassFrostman k j hj).mono hFinalFrostman

end KakeyaLink

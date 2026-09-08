/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Unconditional.AmbientTransport
import Unconditional.NuminaAnalytic
import Unconditional.GeometryAdapters
import Unconditional.CoaxialJohnTransfer
import Unconditional.FiniteParentRecords
import Unconditional.FiniteJointGeometry
import Unconditional.SparseGridSchedule
import Unconditional.ConversionLogAbsorption
import Unconditional.ScaleToOrdinaryCWA
import Unconditional.SingleParentScale
import Unconditional.CoaxialFixedSupport
import Unconditional.FiniteParentPreparation
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers

/-!
# Direct Conversion

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace KakeyaLink

open Kakeya.Assouad Kakeya.Streamlined JointSelection

universe uE uI

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem directConversion : DirectConversionStatement.{uE, uI} := by
  classical
  have finiteParentPreparation (m : ℕ) (hm : 0 < m)
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
    exact KakeyaLink.exists_finiteParentPreparation.{uI} m hm alpha halpha
  have finiteJohnConsumer {I : Type uI} {delta : NNReal} (hdelta : 0 < (delta : ℝ))
      {s : Finset I} {V : I → ShadedTube delta Kakeya.Point3}
      {coordinateCount : ℕ} {H : ENNReal}
      (input : FiniteParentCoverData s V coordinateCount H)
      {representatives : FiniteCoarseRepresentativeData input}
      {density weightLoss : ENNReal}
      (selection : JointLocalizedSelectionData (toTubeShading s V) density weightLoss)
      {coordinate : Fin coordinateCount} {uniformLoss : ENNReal}
      (data : JointFiniteGeometricScaleData input representatives selection coordinate uniformLoss)
      (hparentRadius : 0 < (input.rho coordinate : ℝ))
      {frostmanConstant : ENNReal}
      (hfrostman : ∀ j ∈ input.parentSet coordinate,
        ConvexSpaceBody.IsFrostmanIn
          (Tube.coverClass s (input.assign coordinate) j)
          (fun i => (V i).toConvexSpaceBody)
          (input.parentTube coordinate j).toConvexSpaceBody frostmanConstant)
      (parent : Fin data.selectedParents.card)
      (normalization : WZ2PaperAssouadUnitRescalingData
        ((canonicalReanchoredParents numinaRepresentativeDilation selection.center
          (toTubeFamily data.selectedParents (input.parentTube coordinate))).tube parent)) :
      WZ2PaperBodyConvexWolffBound
        (wz2PaperPureUnitRescaledFullFiberBodyFamily
          (fine := selection.localized.family)
          (coarse := canonicalReanchoredParents numinaRepresentativeDilation selection.center
            (toTubeFamily data.selectedParents (input.parentTube coordinate)))
          parent normalization)
        (27 * ((212776173 : ENNReal) *
          (frostmanConstant * (H * uniformLoss * (weightLoss / density))) *
            ENNReal.ofReal ((8 * numinaRepresentativeDilation) ^ 3))) := by
    classical
    have groupedMass (s t : Finset I) (ht : t ⊆ s)
        (assign : I → I) (body : I → ConvexSpaceBody Kakeya.Point3)
        (parent : I → ConvexSpaceBody Kakeya.Point3)
        (anchorVolume constant ratio : ENNReal)
        (hvolume : ∀ j ∈ t.image assign, volume (parent j).carrier = anchorVolume)
        (hcontained : ∀ j ∈ t.image assign, ∀ i ∈ s.filter (fun i => assign i = j),
          body i ≤ parent j)
        (hfrost : ∀ j ∈ t.image assign,
          ConvexSpaceBody.IsFrostmanIn (s.filter (fun i => assign i = j)) body
            (parent j) constant)
        (hmass : ∀ j ∈ t.image assign,
          (∑ i ∈ s.filter (fun i => assign i = j), volume (body i).carrier) ≤
            ratio * ∑ i ∈ t.filter (fun i => assign i = j), volume (body i).carrier)
        (K : Set Kakeya.Point3) (hK : Convex ℝ K) :
        (∑ i ∈ t.filter (fun i => (body i).carrier ⊆ K), volume (body i).carrier) *
            anchorVolume ≤
          constant * ratio * (∑ i ∈ t, volume (body i).carrier) * volume K := by
      classical
      let active := t.image assign
      have hclass (j : I) (hj : j ∈ active) :
          (∑ i ∈ (t.filter (fun i => assign i = j)).filter
            (fun i => (body i).carrier ⊆ K), volume (body i).carrier) * anchorVolume ≤
          constant * ratio *
            (∑ i ∈ t.filter (fun i => assign i = j), volume (body i).carrier) * volume K := by
        have hsub : (t.filter (fun i => assign i = j)).filter
              (fun i => (body i).carrier ⊆ K) ⊆
            (s.filter (fun i => assign i = j)).filter
              (fun i => (body i).carrier ⊆ K) := by
          intro i hi
          simpa only [Finset.mem_filter] using
            And.intro (And.intro (ht (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1)
              (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2)
              (Finset.mem_filter.mp hi).2
        calc
          _ ≤ (∑ i ∈ (s.filter (fun i => assign i = j)).filter
              (fun i => (body i).carrier ⊆ K), volume (body i).carrier) *
                volume (parent j).carrier := by
            rw [hvolume j hj]
            exact mul_le_mul_right'
              (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => zero_le)) _
          _ ≤ constant *
              (∑ i ∈ s.filter (fun i => assign i = j), volume (body i).carrier) * volume K :=
            Analytic.frostman_containedMass_mul_volume_le _ body (parent j) constant
              (hcontained j hj) (hfrost j hj) K hK
          _ ≤ constant * (ratio *
              ∑ i ∈ t.filter (fun i => assign i = j), volume (body i).carrier) * volume K :=
            mul_le_mul_right' (mul_le_mul_left' (hmass j hj) constant) _
          _ = _ := by ring
      have hsum :
          (∑ j ∈ active, ∑ i ∈ (t.filter (fun i => assign i = j)).filter
            (fun i => (body i).carrier ⊆ K), volume (body i).carrier) =
          ∑ i ∈ t.filter (fun i => (body i).carrier ⊆ K), volume (body i).carrier := by
        have hfilters (j : I) :
            (t.filter (fun i => assign i = j)).filter (fun i => (body i).carrier ⊆ K) =
            (t.filter (fun i => (body i).carrier ⊆ K)).filter (fun i => assign i = j) := by
          ext i
          simp only [Finset.mem_filter]
          tauto
        simp_rw [hfilters]
        exact Finset.sum_fiberwise_of_maps_to
          (fun i hi => Finset.mem_image.mpr ⟨i, (Finset.mem_filter.mp hi).1, rfl⟩) _
      have hsumAll :
          (∑ j ∈ active, ∑ i ∈ t.filter (fun i => assign i = j), volume (body i).carrier) =
            ∑ i ∈ t, volume (body i).carrier :=
        Finset.sum_fiberwise_of_maps_to
          (fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩) _
      rw [← hsum, ← hsumAll, Finset.sum_mul]
      simpa only [Finset.mul_sum, Finset.sum_mul] using Finset.sum_le_sum hclass
    have weightedJohn {delta rho : ℝ} (hdelta : 0 < delta) (hrho : 0 < rho)
        {source target : TubeFamily delta}
        (sourceIndex : Fin target.card ↪ Fin source.card)
        (shift : Fin target.card → ℝ)
        (directionEq : ∀ i,
          (source.tube (sourceIndex i)).direction = (target.tube i).direction)
        (baseEq : ∀ i,
          (source.tube (sourceIndex i)).base =
            (target.tube i).base + shift i • (target.tube i).direction)
        (shiftBound : ∀ i, |shift i| ≤ 1)
        {coarse : TubeFamily rho} (parent : Fin coarse.card)
        (targetSupported : ∀ i, (target.tube i).carrier ⊆ (coarse.tube parent).carrier)
        (normalization : WZ2PaperAssouadUnitRescalingData (coarse.tube parent))
        {anchorVolume constant parentRatio massRatio : ENNReal}
        (sourceFrostman : ∀ K : Set Kakeya.Point3, Convex ℝ K →
          source.toBodyFamily.containedMass K * anchorVolume ≤
            constant * source.toBodyFamily.mass * volume K)
        (parentVolumeBound : volume (coarse.tube parent).carrier ≤ parentRatio * anchorVolume)
        (massBound : source.toBodyFamily.mass ≤ massRatio * target.toBodyFamily.mass) :
        WZ2PaperBodyConvexWolffBound
          { card := target.card
            body := fun i => ⟨normalization.map '' (target.tube i).carrier⟩ }
          (27 * ((212776173 : ENNReal) * constant * parentRatio * massRatio)) := by
      let sub : TubeSubfamily target :=
        { family := target
          embedding := Function.Embedding.refl _
          tube_eq := fun _ => rfl }
      have hone : wz2PaperCenteredDilatedCarrier 1 (coarse.tube parent) =
          (coarse.tube parent).carrier := by simp [wz2PaperCenteredDilatedCarrier]
      have hfrost : ∀ K : Set Kakeya.Point3, Convex ℝ K →
          target.toBodyFamily.containedMass K * volume (coarse.tube parent).carrier ≤
            ((212776173 : ENNReal) * constant * parentRatio * massRatio) *
              target.toBodyFamily.mass * volume K := by
        intro K hK
        have hcount := coaxial_weighted_containedMass_bound hdelta sourceIndex shift
          directionEq baseEq shiftBound sourceFrostman K hK
        calc
          _ ≤ target.toBodyFamily.containedMass K * (parentRatio * anchorVolume) :=
            mul_le_mul_right parentVolumeBound _
          _ = parentRatio * (target.toBodyFamily.containedMass K * anchorVolume) := by ring
          _ ≤ parentRatio *
              (((212776173 : ENNReal) * (constant * source.toBodyFamily.mass)) * volume K) :=
            mul_le_mul_right hcount _
          _ ≤ parentRatio *
              (((212776173 : ENNReal) *
                (constant * (massRatio * target.toBodyFamily.mass))) * volume K) := by
            gcongr
          _ = _ := by ring
      exact gwz_frostman_to_john_rescaled_convex_wolff hdelta hrho
        (A := 1) (by norm_num) parent sub
        (fun i => by simpa only [hone] using targetSupported i)
        normalization ((212776173 : ENNReal) * constant * parentRatio * massRatio)
        (fun K hK _ => by simpa only [hone] using hfrost K hK)
    classical
    let fine := selection.localized.family
    let coarse := canonicalReanchoredParents numinaRepresentativeDilation selection.center
      (toTubeFamily data.selectedParents (input.parentTube coordinate))
    let indices := wz2PaperOrdinaryFullFiberIndices fine coarse parent
    let sub := TubeSubfamily.fromFinset fine indices
    let originalIndex : Fin sub.family.card → I := fun i =>
      finsetIndex s (selection.localized.sourceIndex (sub.embedding i))
    have originalInjective : Function.Injective originalIndex :=
      (finsetIndex_injective s).comp
        (selection.localized.sourceIndex.injective.comp sub.embedding.injective)
    let t := Finset.univ.image originalIndex
    have ht : t ⊆ s := by
      intro i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
      exact finsetIndex_mem s _
    let source := toTubeFamily t (fun i => (V i).toTube)
    let sourceIndex : Fin sub.family.card ↪ Fin source.card := {
      toFun := fun i => t.equivFin ⟨originalIndex i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
      inj' := by
        intro i j hij
        exact originalInjective
          (congrArg (fun x : {i // i ∈ t} => (x : I)) (t.equivFin.injective hij)) }
    have sourceIndexOriginal (i : Fin sub.family.card) :
        finsetIndex t (sourceIndex i) = originalIndex i := by
      simp [sourceIndex, finsetIndex]
    let assign := input.assign coordinate
    let selectedClass := selectedNuminaOldClass selection assign
    have fullClassContained (j : I) (hj : j ∈ t.image assign) :
        selectedClass j ⊆ indices := by
      obtain ⟨old, hold, hj⟩ := Finset.mem_image.mp hj
      obtain ⟨witness, _, rfl⟩ := Finset.mem_image.mp hold
      have hwitness : sub.embedding witness ∈ indices :=
        ((indices.orderIsoOfFin rfl) witness).property
      have hrepresentative :
          representatives.representative coordinate j = finsetIndex data.selectedParents parent := by
        dsimp only [indices, fine, coarse] at hwitness
        rw [data.full_fiber_grouping] at hwitness
        simpa only [← hj] using (Finset.mem_filter.mp hwitness).2
      intro i hi
      dsimp only [indices, fine, coarse]
      rw [data.full_fiber_grouping]
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hiassign := (Finset.mem_filter.mp hi).2
      change assign (finsetIndex s (selection.localized.sourceIndex i)) = j at hiassign
      change representatives.representative coordinate
        (assign (finsetIndex s (selection.localized.sourceIndex i))) = _
      rw [hiassign, hrepresentative]
    have classImage (j : I) (hj : j ∈ t.image assign) :
        t.filter (fun i => assign i = j) =
          (selectedClass j).image (fun i => finsetIndex s (selection.localized.sourceIndex i)) := by
      ext old
      constructor
      · intro hold
        obtain ⟨hold, hassign⟩ := Finset.mem_filter.mp hold
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hold
        exact Finset.mem_image.mpr ⟨sub.embedding i,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hassign⟩, rfl⟩
      · intro hold
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hold
        have himem := fullClassContained j hj hi
        let q := (indices.orderIsoOfFin rfl).symm ⟨i, himem⟩
        have hq : sub.embedding q = i :=
          congrArg Subtype.val ((indices.orderIsoOfFin rfl).apply_symm_apply ⟨i, himem⟩)
        refine Finset.mem_filter.mpr ⟨?_, (Finset.mem_filter.mp hi).2⟩
        exact Finset.mem_image.mpr ⟨q, Finset.mem_univ _, by simp only [originalIndex, hq]⟩
    have sameVolume (i : Fin fine.card) :
        volume (V (finsetIndex s (selection.localized.sourceIndex i))).carrier =
          volume (fine.tube i).carrier := by
      rw [← toDeltaTube_carrier (V (finsetIndex s (selection.localized.sourceIndex i))).toTube]
      exact tube_volume_eq _ _
    have classMass (j : I) (hj : j ∈ t.image assign) :
        (∑ i ∈ t.filter (fun i => assign i = j), volume (V i).carrier) =
          ∑ i ∈ selectedClass j, volume (fine.tube i).carrier := by
      rw [classImage j hj, Finset.sum_image]
      · exact Finset.sum_congr rfl (fun i _ => sameVolume i)
      · exact ((finsetIndex_injective s).comp selection.localized.sourceIndex.injective).injOn
    let oldParent := finsetIndex s (selection.localized.sourceIndex
      ⟨0, selection.nonempty⟩)
    let anchorVolume := volume (input.parentTube coordinate oldParent).carrier
    let massRatio := H * uniformLoss * (weightLoss / density)
    have sourceFrostman : ∀ K : Set Kakeya.Point3, Convex ℝ K →
        source.toBodyFamily.containedMass K * anchorVolume ≤
          (frostmanConstant * massRatio) * source.toBodyFamily.mass * volume K := by
      intro K hK
      rw [toTubeFamily_toBodyFamily, toBodyFamily_containedMass, toBodyFamily_mass]
      apply groupedMass s t ht assign (fun i => (V i).toConvexSpaceBody)
        (fun j => (input.parentTube coordinate j).toConvexSpaceBody)
        anchorVolume frostmanConstant massRatio
      · intro j _
        exact Tube.volume_carrier_eq_volume_carrier _ _
      · intro j _ i hi
        have h := input.fine_containment coordinate i
          (Finset.mem_filter.mp hi).1
        change (V i).toConvexSpaceBody ≤
          (input.parentTube coordinate (assign i)).toConvexSpaceBody at h
        simpa only [(Finset.mem_filter.mp hi).2] using h
      · intro j hj
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
        exact hfrostman _
          (input.assign_mem coordinate i (ht hi))
      · intro j hj
        have hnonempty : (selectedClass j).Nonempty := by
          obtain ⟨i, hi, hj⟩ := Finset.mem_image.mp hj
          have hiclass : i ∈ t.filter (fun i => assign i = j) :=
            Finset.mem_filter.mpr ⟨hi, hj⟩
          rw [classImage j (Finset.mem_image.mpr ⟨i, hi, hj⟩)] at hiclass
          obtain ⟨q, hq, _⟩ := Finset.mem_image.mp hiclass
          exact ⟨q, hq⟩
        have h := data.old_class_mass_ratio j (Finset.card_pos.mpr hnonempty)
        rw [← classMass j hj] at h
        exact h
      · exact hK
    have sourceMass : source.toBodyFamily.mass = sub.family.toBodyFamily.mass := by
      rw [toTubeFamily_mass]
      dsimp only [t]
      rw [Finset.sum_image originalInjective.injOn]
      change (∑ i, volume (V (originalIndex i)).carrier) =
        ∑ i, volume (sub.family.tube i).carrier
      apply Finset.sum_congr rfl
      intro i _
      rw [sub.tube_eq]
      exact sameVolume (sub.embedding i)
    have result := weightedJohn (source := source) (target := sub.family) (coarse := coarse) hdelta
      (show 0 < 8 * numinaRepresentativeDilation *
        (input.rho coordinate : ℝ) by
        have hA : 1 < numinaRepresentativeDilation :=
          Kakeya.Tube.tubeOverlapCoreClose.one_lt_C 3
        have hr := hparentRadius
        positivity)
      sourceIndex
      (fun i => selection.localized.axialShift (sub.embedding i))
      (by
        intro i
        change (toDeltaTube (V (finsetIndex t (sourceIndex i))).toTube).direction = _
        rw [sourceIndexOriginal]
        exact (selection.localized.direction_eq (sub.embedding i)).symm)
      (by
        intro i
        change (toDeltaTube (V (finsetIndex t (sourceIndex i))).toTube).base = _
        rw [sourceIndexOriginal]
        exact selection.localized.source_base_eq (sub.embedding i))
      (fun i => selection.localized.axialShift_bound (sub.embedding i))
      parent
      (by
        intro i
        rw [sub.tube_eq]
        exact (mem_wz2PaperOrdinaryFullFiberIndices_iff
          (fine := fine) (coarse := coarse) parent (sub.embedding i)).mp
          (Finset.orderEmbOfFin_mem indices rfl i))
      normalization sourceFrostman (data.parent_volume_ratio oldParent parent)
      (show source.toBodyFamily.mass ≤ 1 * sub.family.toBodyFamily.mass by rw [one_mul, sourceMass])
    change WZ2PaperBodyConvexWolffBound
      (wz2PaperPureUnitRescaledFullFiberBodyFamily
        (fine := fine) (coarse := coarse) parent normalization)
      (27 * (212776173 * (frostmanConstant * massRatio) *
        ENNReal.ofReal ((8 * numinaRepresentativeDilation) ^ 3) * 1)) at result
    simpa only [mul_one, massRatio] using result
  have finitePureScale {I : Type uI} {delta : NNReal} (hdelta : 0 < (delta : ℝ))
      {s : Finset I} {V : I → ShadedTube delta Kakeya.Point3}
      {coordinateCount : ℕ} {H : ENNReal}
      (input : FiniteParentCoverData s V coordinateCount H)
      {representatives : FiniteCoarseRepresentativeData input}
      {density weightLoss : ENNReal}
      (selection : JointLocalizedSelectionData (toTubeShading s V) density weightLoss)
      {coordinate : Fin coordinateCount} {uniformLoss outputConstant : ENNReal}
      (data : JointFiniteGeometricScaleData input representatives selection coordinate uniformLoss)
      (hparentRadius : 0 < (input.rho coordinate : ℝ))
      {frostmanConstant : ENNReal}
      (hfrostman : ∀ j ∈ input.parentSet coordinate,
        ConvexSpaceBody.IsFrostmanIn
          (Tube.coverClass s (input.assign coordinate) j)
          (fun i => (V i).toConvexSpaceBody)
          (input.parentTube coordinate j).toConvexSpaceBody frostmanConstant)
      (uniformBudget : uniformLoss ≤ outputConstant)
      (johnBudget :
        27 * ((212776173 : ENNReal) *
          (frostmanConstant * (H * uniformLoss * (weightLoss / density))) *
            ENNReal.ofReal ((8 * numinaRepresentativeDilation) ^ 3)) ≤ outputConstant) :
      WZ2PaperPureScaleCoverData selection.localized.family
        (8 * numinaRepresentativeDilation * (input.rho coordinate : ℝ))
        outputConstant := by
    let fine := selection.localized.family
    let coarse := canonicalReanchoredParents numinaRepresentativeDilation selection.center
      (toTubeFamily data.selectedParents (input.parentTube coordinate))
    have hrho : 0 < 8 * numinaRepresentativeDilation *
        (input.rho coordinate : ℝ) := by
      have hA : 1 < numinaRepresentativeDilation :=
        Kakeya.Tube.tubeOverlapCoreClose.one_lt_C 3
      have hscale := hparentRadius
      positivity
    refine {
      delta_pos := hdelta
      rho_pos := hrho
      coarse := coarse
      cover := data.partitioning
      full_fiber_uniform := ?_
      rescaledFiber := ?_ }
    · intro first second
      have h := data.uniform.2 first second
      change ((Finset.univ.filter fun i => data.cover.parent i = first).card : ENNReal) ≤
        uniformLoss * ((Finset.univ.filter fun i => data.cover.parent i = second).card : ENNReal) at h
      change ((wz2PaperOrdinaryFullFiberIndices fine coarse first).card : ENNReal) ≤
        outputConstant * ((wz2PaperOrdinaryFullFiberIndices fine coarse second).card : ENNReal)
      rw [data.full_fiber_eq, data.full_fiber_eq]
      exact h.trans (by gcongr)
    · intro parent
      let normalization := WZ2PaperAssouadUnitRescalingData.ofTube (coarse.tube parent) hrho
      have h := finiteJohnConsumer hdelta input selection data hparentRadius hfrostman parent normalization
      refine ⟨{ normalization := normalization, convex_wolff := ?_ }⟩
      intro K hK
      exact (h K hK).trans (by gcongr)
  have clampedSparseWindow (windowLoss : ℝ) (hwindowLoss : 0 < windowLoss)
      (dilation cutoff : ℝ) (hdilation : 1 ≤ dilation) (hcutoff : 0 < cutoff) :
      ∃ m : ℕ, 0 < m ∧ (1 : ℝ) / m < windowLoss / 16 ∧
        ∃ delta0 : NNReal, 0 < delta0 ∧ delta0 < 1 ∧
        ∀ {delta : NNReal}, 0 < delta → delta ≤ delta0 →
          m ≤ Tube.ssfGridLen delta ∧
          ∀ requested : Kakeya.Assouad.WZ2PaperRequestedScale (delta : ℝ),
            ∃ l : Fin (m + 1),
              let rho := (sparseGridScale delta m (Tube.ssfGridLen delta) l : ℝ)
              let witness := if rho ≤ cutoff then dilation * rho else 2
              requested.1 ≤ witness ∧
                ENNReal.ofReal witness <
                  Kakeya.realRpowENN (delta : ℝ) (-windowLoss) * ENNReal.ofReal requested.1 := by
    classical
    let overhead := max dilation (2 / cutoff)
    have hoverhead : 0 ≤ overhead := (by linarith : 0 ≤ dilation).trans (le_max_left _ _)
    obtain ⟨m, hm, hstep, dS, hdS, hdSOne, hschedule⟩ :=
      exists_fixed_sparse_schedule_window_threshold (windowLoss / 2) (by positivity)
        1 le_rfl
    obtain ⟨dC, hdC, _, hconstant⟩ :=
      Kakeya.Assouad.exists_delta_realRpowENN_bound (ENNReal.ofReal overhead)
        ENNReal.ofReal_ne_top (show 0 < windowLoss / 2 by positivity)
    let dCnn : NNReal := ⟨dC, hdC.le⟩
    refine ⟨m, hm, by convert hstep using 1; ring, min dS dCnn, lt_min hdS hdC,
      (min_le_left _ _).trans_lt hdSOne, ?_⟩
    intro delta hdelta hsmall
    have hd : 0 < (delta : ℝ) := hdelta
    obtain ⟨hmN, _, hschedule⟩ := hschedule hdelta (hsmall.trans (min_le_left _ _))
    refine ⟨hmN, ?_⟩
    intro requested
    obtain ⟨l, hrequested, hwindow⟩ := hschedule requested
    simp only [one_mul] at hrequested hwindow
    let rho := (sparseGridScale delta m (Tube.ssfGridLen delta) l : ℝ)
    have hrho : 0 < rho := Tube.gridScale_pos hdelta _ _
    have hoverheadPower : ENNReal.ofReal overhead ≤
        Kakeya.realRpowENN (delta : ℝ) (-(windowLoss / 2)) := by
      exact hconstant (delta : ℝ) hd (hsmall.trans (min_le_right _ _))
    have hproduct :
        Kakeya.realRpowENN (delta : ℝ) (-(windowLoss / 2)) *
          (Kakeya.realRpowENN (delta : ℝ) (-(windowLoss / 2)) *
            ENNReal.ofReal requested.1) =
        Kakeya.realRpowENN (delta : ℝ) (-windowLoss) * ENNReal.ofReal requested.1 := by
      rw [← mul_assoc]
      congr 1
      unfold Kakeya.realRpowENN
      have hreal : Real.rpow (delta : ℝ) (-(windowLoss / 2)) *
          Real.rpow (delta : ℝ) (-(windowLoss / 2)) =
          Real.rpow (delta : ℝ) (-windowLoss) := by
        calc
          _ = Real.rpow (delta : ℝ) (-(windowLoss / 2) + -(windowLoss / 2)) :=
            (Real.rpow_add hd _ _).symm
          _ = _ := by congr 1; ring
      exact (ENNReal.ofReal_mul
        (Real.rpow_nonneg hd.le (-(windowLoss / 2)))).symm.trans
          (congrArg ENNReal.ofReal hreal)
    have hupper : ENNReal.ofReal (overhead * rho) <
        Kakeya.realRpowENN (delta : ℝ) (-windowLoss) * ENNReal.ofReal requested.1 := by
      rw [ENNReal.ofReal_mul hoverhead]
      calc
        _ ≤ Kakeya.realRpowENN (delta : ℝ) (-(windowLoss / 2)) * ENNReal.ofReal rho :=
          mul_le_mul_left hoverheadPower _
        _ < Kakeya.realRpowENN (delta : ℝ) (-(windowLoss / 2)) *
            (Kakeya.realRpowENN (delta : ℝ) (-(windowLoss / 2)) *
              ENNReal.ofReal requested.1) := by
          have hpowZero : Kakeya.realRpowENN (delta : ℝ) (-(windowLoss / 2)) ≠ 0 :=
            (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hd _)).ne'
          exact ENNReal.mul_lt_mul_right hpowZero ENNReal.ofReal_ne_top hwindow
        _ = _ := hproduct
    refine ⟨l, ?_⟩
    change requested.1 ≤ (if rho ≤ cutoff then dilation * rho else 2) ∧
      ENNReal.ofReal (if rho ≤ cutoff then dilation * rho else 2) <
        Kakeya.realRpowENN (delta : ℝ) (-windowLoss) * ENNReal.ofReal requested.1
    by_cases hsmallRho : rho ≤ cutoff
    · simp only [hsmallRho, if_true]
      refine ⟨hrequested.trans (by nlinarith), ?_⟩
      exact (ENNReal.ofReal_mono
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hrho.le)).trans_lt hupper
    · simp only [hsmallRho, if_false]
      refine ⟨requested.2.2.trans (by norm_num), ?_⟩
      have hratio : 2 ≤ (2 / cutoff) * rho := by
        have := le_of_lt (lt_of_not_ge hsmallRho)
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ hcutoff).mpr
        nlinarith
      exact (ENNReal.ofReal_mono (hratio.trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hrho.le))).trans_lt hupper
  have firstSparseScale (m : ℕ) (hm : 0 < m) (cutoff : ℝ) (hcutoff : 0 < cutoff) :
      ∃ delta0 : NNReal, 0 < delta0 ∧ delta0 < 1 ∧
        ∀ {delta : NNReal}, 0 < delta → delta ≤ delta0 →
          2 * m ≤ Tube.ssfGridLen delta ∧
            (delta : ℝ) ^ ((1 : ℝ) / m) ≤
              (sparseGridScale delta m (Tube.ssfGridLen delta) ⟨1, by omega⟩ : ℝ) ∧
            (sparseGridScale delta m (Tube.ssfGridLen delta) ⟨1, by omega⟩ : ℝ) ≤ cutoff := by
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    obtain ⟨dG, hdG, hdGOne, hgrid⟩ := ScaleParameters.exists_ssfGridLen_step_threshold
      (1 / (2 * (m : ℝ))) (by positivity)
    obtain ⟨dC, hdC, _, hconstant⟩ :=
      Kakeya.Assouad.exists_delta_mul_rpow_le_rpow (1 / cutoff) (by positivity)
        (alpha := 1 / (2 * (m : ℝ))) (beta := 0) (by positivity)
    let dCnn : NNReal := ⟨dC, hdC.le⟩
    refine ⟨min dG dCnn, lt_min hdG hdC, (min_le_left _ _).trans_lt hdGOne, ?_⟩
    intro delta hdelta hsmall
    have hd : (0 : ℝ) < delta := hdelta
    have hdOne : (delta : ℝ) < 1 := (hsmall.trans (min_le_left _ _)).trans_lt hdGOne
    obtain ⟨hN, hstep⟩ := hgrid hdelta (hsmall.trans (min_le_left _ _))
    let N := Tube.ssfGridLen delta
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hlargeN : 2 * (m : ℝ) ≤ N :=
      ((one_div_lt_one_div hNR (by positivity)).mp hstep).le
    have hlargeNnat : 2 * m ≤ N := by exact_mod_cast hlargeN
    let k := N / m
    have hmod : ((N % m : ℕ) : ℝ) < m := by exact_mod_cast Nat.mod_lt N hm
    have hdivision : ((N % m : ℕ) : ℝ) + (m : ℝ) * k = N := by
      exact_mod_cast Nat.mod_add_div N m
    have hupper : (k : ℝ) / N ≤ 1 / m := by
      apply (div_le_div_iff₀ hNR hmR).mpr
      simp only [one_mul]
      dsimp [k]
      have h := Nat.div_mul_le_self N m
      exact_mod_cast h
    have hlower : 1 / (2 * (m : ℝ)) ≤ (k : ℝ) / N := by
      apply (div_le_div_iff₀ (by positivity : 0 < 2 * (m : ℝ)) hNR).mpr
      nlinarith
    have hpowerBound : Real.rpow (delta : ℝ) (1 / (2 * (m : ℝ))) ≤ cutoff := by
      have h := hconstant (delta : ℝ) hd (hsmall.trans (min_le_right _ _))
      have hzero : Real.rpow (delta : ℝ) 0 = 1 := Real.rpow_zero _
      rw [hzero] at h
      have := mul_le_mul_of_nonneg_left h hcutoff.le
      rw [← mul_assoc, one_div, mul_inv_cancel₀ hcutoff.ne', one_mul, mul_one] at this
      exact this
    refine ⟨hlargeNnat, ?_, ?_⟩
    · simp only [sparseGridScale, Tube.gridScale, NNReal.coe_rpow, sparseGridIndex, one_mul]
      change Real.rpow (delta : ℝ) (1 / m) ≤ Real.rpow (delta : ℝ) ((k : ℝ) / N)
      exact Real.rpow_le_rpow_of_exponent_ge hd hdOne.le hupper
    · simp only [sparseGridScale, Tube.gridScale, NNReal.coe_rpow, sparseGridIndex, one_mul]
      change Real.rpow (delta : ℝ) ((k : ℝ) / N) ≤ cutoff
      exact (Real.rpow_le_rpow_of_exponent_ge hd hdOne.le hlower).trans hpowerBound
  have finiteGeometry (coordinateCount : ℕ) :
      ∃ logExponent : ℕ, ∃ delta0 : ℝ,
        0 < delta0 ∧ delta0 ≤ 1 / 4 ∧
        ∀ {delta : NNReal}, 0 < delta → (delta : ℝ) ≤ delta0 →
        ∀ {I : Type uI} (s : Finset I) (V : I → ShadedTube delta Kakeya.Point3),
          (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1) →
          (toTubeFamily s (fun i => (V i).toTube)).IsEssentiallyDistinct →
        ∀ {H : ENNReal} (input : FiniteParentCoverData s V coordinateCount H),
        ∀ density : ENNReal, 0 < density → density ≠ ⊤ →
          (toTubeShading s V).IsLambdaDense density → s.Nonempty →
          (∀ k, delta ≤ input.rho k) →
          (∀ k, (input.rho k : ℝ) ≤
            1 / (200 * (32 * numinaRepresentativeDilation))) →
        Nonempty (JointFiniteGeometricSelectionData input density
          (geometricSelectionLoss (delta : ℝ) logExponent)
          (geometricSelectionLoss (delta : ℝ) logExponent)) := by
    exact exists_jointFiniteGeometricSelection coordinateCount
  
  apply directConversionStatement_of_point3
  intro outputLoss houtputLoss
  let A := numinaRepresentativeDilation
  have hA : 1 < A := Kakeya.Tube.tubeOverlapCoreClose.one_lt_C 3
  let cutoff := 1 / (1024 * 200 * (32 * A))
  have hcutoff : 0 < cutoff := by dsimp [cutoff]; positivity
  obtain ⟨m, hm, hstep, dW, hdW, hdWOne, hwindow⟩ :=
    clampedSparseWindow outputLoss houtputLoss (8 * A * 1024) cutoff (by linarith) hcutoff
  obtain ⟨dFirst, hdFirst, hdFirstOne, hfirst⟩ := firstSparseScale m hm cutoff hcutoff
  let alpha := outputLoss / 16
  have halpha : 0 < alpha := by dsimp [alpha]; positivity
  have halphaSmall : alpha < outputLoss := by dsimp [alpha]; linarith
  obtain ⟨logExponent, dG, hdG, hdGSmall, producer⟩ :=
    finiteGeometry (m + 1)
  obtain ⟨inputLoss, dNorm, hinputLoss, hdNorm, normalizer⟩ :=
    finiteParentPreparation m hm alpha halpha
  obtain ⟨dU, hdU, _, uniformAbsorb⟩ := exists_logPower_mul_rpow_threshold
    1 (by simp) logExponent (alpha := 0) (beta := -(outputLoss / 2)) (by linarith)
  let parentRatio := ENNReal.ofReal ((8 * A) ^ 3)
  let johnOverhead := 27 * 212776173 * parentRatio
  obtain ⟨dJ, hdJ, _, johnAbsorb⟩ := exists_logPower_mul_rpow_threshold
    johnOverhead (by dsimp [johnOverhead, parentRatio]; finiteness) (2 * logExponent)
    (alpha := -(4 * alpha)) (beta := -(outputLoss / 2)) (by dsimp [alpha]; linarith)
  let parentTube : Kakeya.DeltaTube 2 := {
    base := 0
    direction := EuclideanSpace.single (0 : Fin 3) 1
    direction_unit := by simp }
  have parentVolumeFinite : volume parentTube.carrier ≠ ⊤ :=
    wz2_paper_ordinary_tube_volume_ne_top parentTube (by norm_num)
  obtain ⟨dL, hdL, _, largeAbsorb⟩ := exists_logPower_mul_rpow_threshold
    (27 * 4 * volume parentTube.carrier) (by finiteness) 0
    (alpha := -(2 * ((1 : ℝ) / m) + outputLoss / 2)) (beta := -outputLoss) (by linarith)
  obtain ⟨dD, hdD, _, densityAbsorb⟩ := exists_logPower_mul_rpow_threshold
    1 (by simp) logExponent (alpha := outputLoss) (beta := alpha) halphaSmall
  let delta0 := min (dW : ℝ) (min (dFirst : ℝ) (min cutoff
    (min dG (min dNorm (min dU (min dJ (min dL dD)))))))
  have hdelta0 : 0 < delta0 := by dsimp [delta0]; positivity
  refine ⟨inputLoss, delta0, hinputLoss, hdelta0, ?_⟩
  intro delta hdelta hsmall I s V hball C hC input hdense hfrostman
  have hd : 0 < (delta : ℝ) := hdelta
  have hall := hsmall
  change (delta : ℝ) ≤ min (dW : ℝ) (min (dFirst : ℝ) (min cutoff
    (min dG (min dNorm (min dU (min dJ (min dL dD))))))) at hall
  simp only [le_min_iff] at hall
  obtain ⟨deltaW, deltaFirst, deltaCutoff, deltaG, deltaNorm, deltaU, deltaJ, deltaL, deltaD⟩ := hall
  have hdOne : (delta : ℝ) < 1 := deltaW.trans_lt hdWOne
  have hNlarge := (hfirst hdelta deltaFirst).1
  let N := Tube.ssfGridLen delta
  let gridIndex : Fin (m + 1) → ℕ := fun l =>
    if (sparseGridScale delta m N l : ℝ) ≤ cutoff then sparseGridIndex m N l.val else N
  have hlevel (l : Fin (m + 1)) : gridIndex l ≤ N := by
    dsimp [gridIndex]
    split
    · exact sparseGridIndex_le hm (by omega)
    · exact le_rfl
  have hscaleSmall (l : Fin (m + 1)) :
      (Tube.gridScale delta N (gridIndex l) : ℝ) ≤ cutoff := by
    dsimp only [gridIndex]
    split
    · assumption
    · rw [Tube.gridScale_self delta (by dsimp [N]; omega)]
      exact deltaCutoff
  obtain ⟨newS, newV, newH, newU, hnewRho, hnewNonempty, hnewBall, hnewED,
      hnewH, hnewDensity, hnewUnion, hnewFrostman⟩ :=
    normalizer hdelta deltaNorm s V hball hC input hdense hfrostman gridIndex
      (by omega) hlevel hscaleSmall
  have hnewRhoPos (l : Fin (m + 1)) : 0 < (newU.rho l : ℝ) := by
    rw [hnewRho l]
    have h := Tube.gridScale_pos hdelta N (gridIndex l)
    positivity
  have hnewDeltaLeRho (l : Fin (m + 1)) : delta ≤ newU.rho l := by
    rw [hnewRho l]
    have h := Tube.gridScale_antitone hdelta (show delta ≤ 1 from hdOne.le) N (hlevel l)
    rw [Tube.gridScale_self delta (by dsimp [N] at *; omega)] at h
    exact h.trans (le_mul_of_one_le_left zero_le (by norm_num))
  have hnewScaleSmall (l : Fin (m + 1)) :
      (newU.rho l : ℝ) ≤ 1 / (200 * (32 * A)) := by
    rw [hnewRho l]
    change 1024 * (Tube.gridScale delta N (gridIndex l) : ℝ) ≤ _
    have h := hscaleSmall l
    dsimp [cutoff] at h
    have hpos : 0 < 200 * (32 * A) := by positivity
    apply (le_div_iff₀ hpos).mpr
    have h := (le_div_iff₀ (by positivity : 0 < 1024 * 200 * (32 * A))).mp h
    nlinarith
  obtain ⟨joint⟩ := producer hdelta deltaG newS newV hnewBall hnewED newU
    (Kakeya.realRpowENN (delta : ℝ) alpha)
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hd _)) ENNReal.ofReal_ne_top
    (toTubeShading_isLambdaDense_of_fullness _ _ hnewDensity) hnewNonempty
    hnewDeltaLeRho hnewScaleSmall
  let selection := joint.selection
  let fine := selection.localized.family
  let source := toTubeFamily newS (fun i => (newV i).toTube)
  let sourceShading := toTubeShading newS newV
  let smallConstant := Kakeya.realRpowENN (delta : ℝ) (-(outputLoss / 2))
  let outputConstant := Kakeya.realRpowENN (delta : ℝ) (-outputLoss)
  have uniformBudget : geometricSelectionLoss (delta : ℝ) logExponent ≤ smallConstant := by
    have h := uniformAbsorb (delta : ℝ) hd deltaU
    simpa [geometricSelectionLoss, Kakeya.realRpowENN, smallConstant] using h
  have fourthPower : Kakeya.realRpowENN (delta : ℝ) (-(4 * alpha)) =
      Kakeya.realRpowENN (delta : ℝ) (-alpha) ^ 4 := by
    rw [show -(4 * alpha) = ((-alpha + -alpha) + -alpha) + -alpha by ring,
      realRpowENN_add hd, realRpowENN_add hd, realRpowENN_add hd]
    ring
  have hnewHpow : newH ≤ Kakeya.realRpowENN (delta : ℝ) (-alpha) ^ 2 := by
    calc
      _ ≤ Kakeya.realRpowENN (delta : ℝ) (-2 * alpha) := hnewH
      _ = _ := by
        rw [show -2 * alpha = -alpha + -alpha by ring, realRpowENN_add hd]
        ring
  have johnBudget :
      27 * (212776173 *
        (Kakeya.realRpowENN (delta : ℝ) (-alpha) *
          (newH *
            geometricSelectionLoss (delta : ℝ) logExponent *
            (geometricSelectionLoss (delta : ℝ) logExponent /
              Kakeya.realRpowENN (delta : ℝ) alpha))) * parentRatio) ≤ smallConstant := by
    calc
      _ ≤ 27 * (212776173 *
          (Kakeya.realRpowENN (delta : ℝ) (-alpha) *
            (Kakeya.realRpowENN (delta : ℝ) (-alpha) ^ 2 *
              geometricSelectionLoss (delta : ℝ) logExponent *
              (geometricSelectionLoss (delta : ℝ) logExponent /
                Kakeya.realRpowENN (delta : ℝ) alpha))) * parentRatio) := by
        gcongr
      _ = johnOverhead * ENNReal.ofReal (Real.log (1 / (delta : ℝ))) ^ (2 * logExponent) *
          Kakeya.realRpowENN (delta : ℝ) (-(4 * alpha)) := by
        rw [div_eq_mul_inv, pure_wz2_realRpowENN_inv hd, fourthPower,
          Nat.mul_comm 2 logExponent, pow_mul]
        dsimp [geometricSelectionLoss, johnOverhead]
        ring
      _ ≤ _ := johnAbsorb (delta : ℝ) hd deltaJ
  let scaleData (l : Fin (m + 1)) := finitePureScale hd newU
    selection (joint.atScale l) (hnewRhoPos l) (hnewFrostman l) uniformBudget johnBudget
  have smallBudget : smallConstant ≤ outputConstant :=
    pure_wz2_rpowENN_antitone hd hdOne.le (by linarith)
  have outputOne : 1 ≤ outputConstant := by
    have h := pure_wz2_rpowENN_antitone hd hdOne.le (show -outputLoss ≤ 0 by linarith)
    simpa [Kakeya.realRpowENN, outputConstant] using h
  have sourceSupported : PureWZ2FixedBallSupport source 1 := by
    intro i
    change (toDeltaTube (newV (finsetIndex newS i)).toTube).carrier ⊆ _
    rw [toDeltaTube_carrier]
    exact hnewBall _ (finsetIndex_mem _ _)
  have targetSupported : PureWZ2FixedBallSupport fine 2 := by
    simpa only [one_add_one_eq_two] using coaxial_target_fixedBallSupport sourceSupported selection.localized.sourceIndex
      selection.localized.axialShift (fun i => (selection.localized.direction_eq i).symm)
      selection.localized.source_base_eq selection.localized.axialShift_bound
  let first : Fin (m + 1) := ⟨1, by omega⟩
  have hfirstSmall : (sparseGridScale delta m N first : ℝ) ≤ cutoff :=
    (hfirst hdelta deltaFirst).2.2
  have firstScaleLower : Real.rpow (delta : ℝ) ((1 : ℝ) / m) ≤
      8 * A * (newU.rho first : ℝ) := by
    rw [hnewRho first]
    change _ ≤ 8 * A * (1024 * (Tube.gridScale delta N (gridIndex first) : ℝ))
    rw [← mul_assoc]
    dsimp only [gridIndex]
    rw [if_pos hfirstSmall]
    exact (hfirst hdelta deltaFirst).2.1.trans
      (le_mul_of_one_le_left (NNReal.coe_nonneg _) (by nlinarith))
  have largeBudget :
      27 * (((4 * Kakeya.realRpowENN (delta : ℝ) (-2 * ((1 : ℝ) / m))) * smallConstant) *
        volume parentTube.carrier) ≤ outputConstant := by
    have h := largeAbsorb (delta : ℝ) hd deltaL
    simp only [pow_zero, mul_one] at h
    have algebra :
        27 * (((4 * Kakeya.realRpowENN (delta : ℝ) (-2 * ((1 : ℝ) / m))) * smallConstant) *
          volume parentTube.carrier) =
        (27 * 4 * volume parentTube.carrier) *
          Kakeya.realRpowENN (delta : ℝ) (-(2 * ((1 : ℝ) / m) + outputLoss / 2)) := by
      rw [show -(2 * ((1 : ℝ) / m) + outputLoss / 2) =
        -2 * ((1 : ℝ) / m) + -(outputLoss / 2) by ring, realRpowENN_add hd]
      dsimp [smallConstant]
      ring
    rw [algebra]
    exact h
  let largeData := singleParentScaleOfBodyCWA hd (by norm_num : (0 : ℝ) < 2)
    fine parentTube
    (by
      intro i point hpoint
      exact Metric.mem_cthickening_of_dist_le point 0 2
        (Kakeya.unitSegment parentTube.base parentTube.direction)
        ⟨0, by norm_num, by simp [parentTube]⟩
        (Metric.mem_closedBall.mp (targetSupported i hpoint)))
    ((scaleData first).ordinaryCWA selection.nonempty firstScaleLower) outputOne largeBudget
  have cwa : WZ2PaperPureCWAAtNearbyScales fine outputConstant := by
    refine ⟨hd, ⟨outputOne, ENNReal.ofReal_ne_top⟩, selection.ordinary_distinct, ?_⟩
    intro requested
    obtain ⟨l, hlo, hhi⟩ := (hwindow hdelta deltaW).2 requested
    by_cases hsmallScale : (sparseGridScale delta m N l : ℝ) ≤ cutoff
    · rw [if_pos hsmallScale] at hlo hhi
      refine ⟨{
        rho := (8 * A * 1024) * (sparseGridScale delta m N l : ℝ)
        requested_le := hlo
        within_factor := hhi
        scaleData := ?_ }⟩
      have hindex : gridIndex l = sparseGridIndex m N l.val := if_pos hsmallScale
      have data := (scaleData l).mono smallBudget
      change WZ2PaperPureScaleCoverData fine
        (8 * A * (newU.rho l : ℝ)) outputConstant at data
      rw [hnewRho l] at data
      change WZ2PaperPureScaleCoverData fine
        (8 * A * (1024 * (Tube.gridScale delta N (gridIndex l) : ℝ))) outputConstant at data
      rw [hindex, ← mul_assoc] at data
      exact data
    · rw [if_neg hsmallScale] at hlo hhi
      exact ⟨{ rho := 2, requested_le := hlo, within_factor := hhi, scaleData := largeData }⟩
  have densityBudget : Kakeya.realRpowENN (delta : ℝ) outputLoss ≤
      wz2PaperPureRefinementFraction (delta : ℝ) logExponent *
        Kakeya.realRpowENN (delta : ℝ) alpha := by
    have h := densityAbsorb (delta : ℝ) hd deltaD
    simp only [one_mul] at h
    have logPos : 0 < ENNReal.ofReal (Real.log (1 / (delta : ℝ))) := by
      apply ENNReal.ofReal_pos.mpr
      exact Real.log_pos ((lt_div_iff₀ hd).mpr (by simpa using hdOne))
    have cancellation : wz2PaperPureRefinementFraction (delta : ℝ) logExponent *
        ENNReal.ofReal (Real.log (1 / (delta : ℝ))) ^ logExponent = 1 := by
      rw [wz2PaperPureRefinementFraction, ← mul_pow,
        ENNReal.inv_mul_cancel logPos.ne' (by simp), one_pow]
    have scaled := mul_le_mul_right h (wz2PaperPureRefinementFraction (delta : ℝ) logExponent)
    simpa only [← mul_assoc, cancellation, one_mul] using scaled
  have logPos : 0 < ENNReal.ofReal (Real.log (1 / (delta : ℝ))) := by
    apply ENNReal.ofReal_pos.mpr
    exact Real.log_pos ((lt_div_iff₀ hd).mpr (by simpa using hdOne))
  have cancellation : wz2PaperPureRefinementFraction (delta : ℝ) logExponent *
      geometricSelectionLoss (delta : ℝ) logExponent = 1 := by
    rw [wz2PaperPureRefinementFraction, geometricSelectionLoss, ← mul_pow,
      ENNReal.inv_mul_cancel logPos.ne' (by simp), one_pow]
  have retained : wz2PaperPureRefinementFraction (delta : ℝ) logExponent *
      sourceShading.mass ≤ selection.localized.shading.mass := by
    calc
      _ ≤ wz2PaperPureRefinementFraction (delta : ℝ) logExponent *
          (geometricSelectionLoss (delta : ℝ) logExponent * selection.localized.shading.mass) :=
        mul_le_mul_right selection.retained_mass _
      _ = _ := by rw [← mul_assoc, cancellation, one_mul]
  have massBound : fine.toBodyFamily.mass ≤ source.toBodyFamily.mass := by
    rw [tubeFamily_mass_eq_card_mul_volume, tubeFamily_mass_eq_card_mul_volume]
    apply mul_le_mul_left
    change (fine.card : ENNReal) ≤ (source.card : ENNReal)
    have h := Fintype.card_le_of_injective selection.localized.sourceIndex
      selection.localized.sourceIndex.injective
    simp only [Fintype.card_fin] at h
    exact_mod_cast h
  refine ⟨fine, selection.localized.shading, selection.nonempty, cwa, ?_, ?_⟩
  · exact ScaleParameters.isLambdaDense_of_retained_mass sourceShading selection.localized.shading
      (toTubeShading_isLambdaDense_of_fullness _ _ hnewDensity)
      massBound retained densityBudget
  · apply le_trans (b := volume sourceShading.union)
    have hsub : selection.localized.shading.union ⊆ sourceShading.union := by
      intro point hpoint
      obtain ⟨i, hi⟩ := hpoint
      exact ⟨selection.localized.sourceIndex i, selection.localized.subshading i hi⟩
    exact measure_mono hsub
    · simpa only [sourceShading, toTubeShading_union] using hnewUnion


end KakeyaLink

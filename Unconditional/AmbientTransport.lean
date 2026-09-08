/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Unconditional.DirectConversionStatement
import Kakeya.DimensionThree.IsometryTransport

/-!
# Ambient Transport

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

open MeasureTheory

noncomputable section

namespace KakeyaLink

universe uE uF uI

section Hierarchy

variable {E : Type uE} {F : Type uF}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
  {ι : Type uI}

/-- Isometric transport keeps every grid index and assignment unchanged. -/
def mapGridCoverSystem {delta : NNReal} {s : Finset ι} {T : ι → Tube delta E}
    {N : ℕ} (G : Tube.GridCoverSystem s T N) (f : E ≃ₗᵢ[ℝ] F) :
    Tube.GridCoverSystem s (fun i => (T i).mapLinearIsometryEquiv f) N where
  indexSet := G.indexSet
  assign := G.assign
  tube := fun k i => (G.tube k i).mapLinearIsometryEquiv f
  assign_mem := by
    exact G.assign_mem
  le_tube_assign := by
    intro k hk i hi
    simpa only [Tube.mapLinearIsometryEquiv_toConvexSpaceBody,
      ConvexSpaceBody.mapLinearIsometryEquiv_le_mapLinearIsometryEquiv_iff] using
      G.le_tube_assign k hk i hi
  nested := by
    exact G.nested
  tube_nested := by
    intro k hk i hi
    simpa only [Tube.mapLinearIsometryEquiv_toConvexSpaceBody,
      ConvexSpaceBody.mapLinearIsometryEquiv_le_mapLinearIsometryEquiv_iff] using
      G.tube_nested k hk i hi

/-- Isometric transport preserves the hierarchy's uniform constant and branching. -/
def mapUniformTubeSet {delta : NNReal} {s : Finset ι} {T : ι → Tube delta E}
    {N : ℕ} {C : NNReal} (U : Tube.UniformTubeSet s T N C)
    (f : E ≃ₗᵢ[ℝ] F) :
    Tube.UniformTubeSet s (fun i => (T i).mapLinearIsometryEquiv f) N C where
  cover := mapGridCoverSystem U.cover f
  branchingN := U.branchingN
  tube_injOn := by
    intro k hk i hi j hj hij
    apply U.tube_injOn k hk hi hj
    have hx := congrArg Tube.x hij
    have hy := congrArg Tube.y hij
    have hxy : (U.cover.tube k i).x = (U.cover.tube k j).x := f.injective hx
    have hyy : (U.cover.tube k i).y = (U.cover.tube k j).y := f.injective hy
    apply Tube.ext _ hxy hyy
    rw [(U.cover.tube k i).carrier_eq, (U.cover.tube k j).carrier_eq, hxy, hyy]
  boundedOverlap := by
    classical
    intro k hk W
    have htest (i : ι) :
        (T i).toConvexSpaceBody.mapLinearIsometryEquiv f ≤ W.toConvexSpaceBody ↔
          (T i).toConvexSpaceBody ≤
            (W.mapLinearIsometryEquiv f.symm).toConvexSpaceBody := by
      rw [← ConvexSpaceBody.mapLinearIsometryEquiv_le_mapLinearIsometryEquiv_iff
        (f := f.symm)]
      simp only [ConvexSpaceBody.mapLinearIsometryEquiv_symm_mapLinearIsometryEquiv,
        Tube.mapLinearIsometryEquiv_toConvexSpaceBody]
    simpa only [mapGridCoverSystem, Tube.mapLinearIsometryEquiv_toConvexSpaceBody,
      ConvexSpaceBody.mapLinearIsometryEquiv_le_mapLinearIsometryEquiv_iff, htest] using
      U.boundedOverlap k hk (W.mapLinearIsometryEquiv f.symm)
  card_class_le := by
    exact U.card_class_le
  le_card_class := by
    exact U.le_card_class

/-- The local shaded branching function is pulled back by the same isometry. -/
def mapShadedUniformTubeSet {delta : NNReal} {s : Finset ι}
    {V : ι → ShadedTube delta E} {N : ℕ} {C : NNReal}
    (U : ShadedTube.ShadedUniformTubeSet s V N C) (f : E ≃ₗᵢ[ℝ] F) :
    ShadedTube.ShadedUniformTubeSet s
      (fun i => (V i).mapLinearIsometryEquiv f) N C where
  tubeUniform := mapUniformTubeSet U.tubeUniform f
  branchingN := U.branchingN
  localN := fun y k => U.localN (f.symm y) k
  card_shadeClass_le := by
    classical
    intro y hy k hk i hi hyi
    have hmem (j : ι) : y ∈ ((V j).mapLinearIsometryEquiv f).shade ↔
        f.symm y ∈ (V j).shade := by
      change y ∈ f '' (V j).shade ↔ _
      exact Set.mem_image_equiv (f := f.toEquiv)
    have hy' : f.symm y ∈ ⋃ j ∈ s, (V j).shade := by
      simpa only [Set.mem_iUnion, hmem] using hy
    have hclass : ShadedTube.shadeClass s (fun j => (V j).mapLinearIsometryEquiv f)
        (U.tubeUniform.cover.assign k) (U.tubeUniform.cover.assign k i) y =
        ShadedTube.shadeClass s V (U.tubeUniform.cover.assign k)
          (U.tubeUniform.cover.assign k i) (f.symm y) := by
      ext j
      simp only [ShadedTube.shadeClass, Finset.mem_filter, hmem]
    simpa only [mapUniformTubeSet, mapGridCoverSystem, hclass] using
      U.card_shadeClass_le (f.symm y) hy' k hk i hi ((hmem i).mp hyi)
  le_card_shadeClass := by
    classical
    intro y hy k hk i hi hyi
    have hmem (j : ι) : y ∈ ((V j).mapLinearIsometryEquiv f).shade ↔
        f.symm y ∈ (V j).shade := by
      change y ∈ f '' (V j).shade ↔ _
      exact Set.mem_image_equiv (f := f.toEquiv)
    have hy' : f.symm y ∈ ⋃ j ∈ s, (V j).shade := by
      simpa only [Set.mem_iUnion, hmem] using hy
    have hclass : ShadedTube.shadeClass s (fun j => (V j).mapLinearIsometryEquiv f)
        (U.tubeUniform.cover.assign k) (U.tubeUniform.cover.assign k i) y =
        ShadedTube.shadeClass s V (U.tubeUniform.cover.assign k)
          (U.tubeUniform.cover.assign k i) (f.symm y) := by
      ext j
      simp only [ShadedTube.shadeClass, Finset.mem_filter, hmem]
    simpa only [mapUniformTubeSet, mapGridCoverSystem, hclass] using
      U.le_card_shadeClass (f.symm y) hy' k hk i hi ((hmem i).mp hyi)
  branchingN_le := by
    intro y hy k hk
    have hmem (j : ι) : y ∈ ((V j).mapLinearIsometryEquiv f).shade ↔
        f.symm y ∈ (V j).shade := by
      change y ∈ f '' (V j).shade ↔ _
      exact Set.mem_image_equiv (f := f.toEquiv)
    apply U.branchingN_le (f.symm y) _ k hk
    simpa only [Set.mem_iUnion, hmem] using hy
  le_branchingN := by
    intro y hy k hk
    have hmem (j : ι) : y ∈ ((V j).mapLinearIsometryEquiv f).shade ↔
        f.symm y ∈ (V j).shade := by
      change y ∈ f '' (V j).shade ↔ _
      exact Set.mem_image_equiv (f := f.toEquiv)
    apply U.le_branchingN (f.symm y) _ k hk
    simpa only [Set.mem_iUnion, hmem] using hy

/-- The assigned-class Frostman bound survives at each unchanged grid node. -/
theorem mapUniformTubeSet_isFrostmanAtEveryScale {delta : NNReal} {s : Finset ι}
    {T : ι → Tube delta E} {N : ℕ} {C : NNReal}
    (U : Tube.UniformTubeSet s T N C) (f : E ≃ₗᵢ[ℝ] F) {A : ENNReal}
    (h : U.IsFrostmanAtEveryScale A) :
    (mapUniformTubeSet U f).IsFrostmanAtEveryScale A := by
  intro k hk j hj
  simpa only [mapUniformTubeSet, mapGridCoverSystem,
    Tube.mapLinearIsometryEquiv_toConvexSpaceBody] using
    (h k hk j hj).mapLinearIsometryEquiv f

end Hierarchy

/-- The original direct conversion restricted only in its ambient space. -/
def DirectConversionPoint3Statement : Prop :=
  ∀ outputLoss : ℝ, 0 < outputLoss →
    ∃ inputLoss conversionDelta0 : ℝ,
      0 < inputLoss ∧ 0 < conversionDelta0 ∧
      ∀ {delta : NNReal}, 0 < delta → (delta : ℝ) ≤ conversionDelta0 →
      ∀ {ι : Type uI} (s : Finset ι) (V : ι → ShadedTube delta Kakeya.Point3),
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall (0 : Kakeya.Point3) 1) →
        ∀ {C : NNReal}, C ≤ ShadedTube.ssfUniformConst (Module.finrank ℝ Kakeya.Point3) →
        ∀ (U : ShadedTube.ShadedUniformTubeSet s V (Tube.ssfGridLen delta) C),
          ENNReal.ofReal ((delta : ℝ) ^ inputLoss) ≤
            ShadedBody.fullness' s (fun i => (V i).toShadedBody) →
          U.tubeUniform.IsFrostmanAtEveryScale
            (ENNReal.ofReal ((delta : ℝ) ^ (-inputLoss))) →
          ∃ family : Kakeya.Streamlined.TubeFamily (delta : ℝ),
          ∃ shading : Kakeya.Streamlined.TubeShading family,
            family.Nonempty ∧
            Kakeya.Assouad.WZ2PaperPureCWAAtNearbyScales family
              (Kakeya.realRpowENN (delta : ℝ) (-outputLoss)) ∧
            shading.IsLambdaDense (Kakeya.realRpowENN (delta : ℝ) outputLoss) ∧
            volume shading.union ≤ volume (⋃ i ∈ s, (V i).shade)

/-- Fixed coordinates suffice without restricting the source index universe. -/
theorem directConversionStatement_of_point3
    (h : DirectConversionPoint3Statement.{uI}) : DirectConversionStatement.{uE, uI} := by
  intro E _ _ _ _ _ _ hdim outputLoss houtputLoss
  obtain ⟨inputLoss, delta0, hinputLoss, hdelta0, hconvert⟩ := h outputLoss houtputLoss
  refine ⟨inputLoss, delta0, hinputLoss, hdelta0, ?_⟩
  intro delta hdelta hsmall ι s V hball C hC U hfull hFrostman
  let f : E ≃ₗᵢ[ℝ] Kakeya.Point3 := Kakeya.dimThreeLinearIsometryEquiv E hdim
  let V' : ι → ShadedTube delta Kakeya.Point3 :=
    fun i => (V i).mapLinearIsometryEquiv f
  have hball' : ∀ i ∈ s, (V' i).carrier ⊆ Metric.closedBall 0 1 := by
    intro i hi
    dsimp only [V']
    rw [ShadedTube.mapLinearIsometryEquiv_carrier]
    calc
      f '' (V i).carrier ⊆ f '' Metric.closedBall 0 1 := Set.image_mono (hball i hi)
      _ = Metric.closedBall 0 1 := by simpa using f.image_closedBall (0 : E) 1
  have hC' : C ≤ ShadedTube.ssfUniformConst (Module.finrank ℝ Kakeya.Point3) := by
    simpa only [← f.toLinearEquiv.finrank_eq] using hC
  let U' := mapShadedUniformTubeSet U f
  have hfull' : ENNReal.ofReal ((delta : ℝ) ^ inputLoss) ≤
      ShadedBody.fullness' s (fun i => (V' i).toShadedBody) := by
    simpa only [V', ← ShadedBody.coe_fullness,
      ShadedTube.fullness_mapLinearIsometryEquiv] using hfull
  have hFrostman' : U'.tubeUniform.IsFrostmanAtEveryScale
      (ENNReal.ofReal ((delta : ℝ) ^ (-inputLoss))) :=
    mapUniformTubeSet_isFrostmanAtEveryScale U.tubeUniform f hFrostman
  obtain ⟨family, shading, hne, hCWA, hdense, hvol⟩ :=
    hconvert hdelta hsmall s V' hball' hC' U' hfull' hFrostman'
  refine ⟨family, shading, hne, hCWA, hdense, ?_⟩
  simpa only [V', ShadedTube.volume_iUnion_mapLinearIsometryEquiv_shade] using hvol

end KakeyaLink

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.PartialEstimates
public import Kakeya.Mathlib.Analysis.InnerProductSpace

/-!
# Transport between three-dimensional real inner-product spaces

This file supplies the cross-space isometric transport needed to apply the coordinate model in
`EuclideanSpace ℝ (Fin 3)` to a theorem stated in an arbitrary real inner-product space of
finrank three.  The index types are unchanged by the transport.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric

noncomputable section

namespace Kakeya

/-- The coordinate isometry associated to the standard orthonormal basis of a real
three-dimensional inner-product space. -/
def dimThreeLinearIsometryEquiv (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hdim : Module.finrank ℝ E = 3) :
    E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  ((stdOrthonormalBasis ℝ E).reindex (finCongr hdim)).repr

end Kakeya

namespace Metric

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Affine thickness is invariant under a surjective linear isometry. -/
theorem ethickness_image_linearIsometryEquiv (f : E ≃ₗᵢ[ℝ] F) (X : Set E) (n : ℕ) :
    ethickness ℝ (f '' X) n = ethickness ℝ X n := by
  apply le_antisymm
  · have h := (f.isometry.lipschitz.ethickness_image_le
      (f := f.toLinearEquiv.toAffineEquiv.toAffineMap) X) n
    simpa [Pi.smul_apply, ENNReal.smul_def, smul_eq_mul] using h
  · have h := (f.symm.isometry.lipschitz.ethickness_image_le
      (f := f.symm.toLinearEquiv.toAffineEquiv.toAffineMap) (f '' X)) n
    have hss : f.symm.toLinearEquiv.toAffineEquiv.toAffineMap '' (f '' X) = X := by
      rw [Set.image_image]
      simp
    rw [hss] at h
    simpa [Pi.smul_apply, ENNReal.smul_def, smul_eq_mul] using h

end Metric

namespace ConvexSpaceBody

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The image of a convex space body under a linear isometry equivalence between two spaces. -/
def mapLinearIsometryEquiv (K : ConvexSpaceBody E) (f : E ≃ₗᵢ[ℝ] F) : ConvexSpaceBody F where
  carrier := f '' K.carrier
  convex' :=
    (K.convex'.convex.affine_image f.toLinearEquiv.toAffineEquiv.toAffineMap).isConvexSet
  isCompact' := K.isCompact'.image f.continuous
  nonempty' := K.nonempty'.image f

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
@[simp]
theorem mapLinearIsometryEquiv_carrier (K : ConvexSpaceBody E) (f : E ≃ₗᵢ[ℝ] F) :
    (K.mapLinearIsometryEquiv f).carrier = f '' K.carrier := rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
@[simp]
theorem mapLinearIsometryEquiv_symm_mapLinearIsometryEquiv
    (K : ConvexSpaceBody E) (f : E ≃ₗᵢ[ℝ] F) :
    (K.mapLinearIsometryEquiv f).mapLinearIsometryEquiv f.symm = K := by
  apply ConvexSpaceBody.ext
  change f.symm '' (f '' K.carrier) = K.carrier
  rw [Set.image_image]
  simp

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
@[simp]
theorem symm_mapLinearIsometryEquiv_mapLinearIsometryEquiv
    (K : ConvexSpaceBody F) (f : E ≃ₗᵢ[ℝ] F) :
    (K.mapLinearIsometryEquiv f.symm).mapLinearIsometryEquiv f = K := by
  apply ConvexSpaceBody.ext
  change f '' (f.symm '' K.carrier) = K.carrier
  rw [Set.image_image]
  simp

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
@[simp]
theorem mapLinearIsometryEquiv_le_mapLinearIsometryEquiv_iff
    {K L : ConvexSpaceBody E} (f : E ≃ₗᵢ[ℝ] F) :
    K.mapLinearIsometryEquiv f ≤ L.mapLinearIsometryEquiv f ↔ K ≤ L := by
  change f '' K.carrier ⊆ f '' L.carrier ↔ K.carrier ⊆ L.carrier
  exact Set.image_subset_image_iff f.injective

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The shortest affine scale is invariant under a linear isometry equivalence. -/
@[simp]
theorem mapLinearIsometryEquiv_scale (K : ConvexSpaceBody E) (f : E ≃ₗᵢ[ℝ] F) :
    (K.mapLinearIsometryEquiv f).scale = K.scale := by
  rw [scale, scale, ← f.toLinearEquiv.finrank_eq]
  rw [← Metric.toReal_ethickness (K.mapLinearIsometryEquiv f).isCompact'.isBounded,
    ← Metric.toReal_ethickness K.isCompact'.isBounded]
  congr 1
  exact Metric.ethickness_image_linearIsometryEquiv f K.carrier _

/-- Closed metric collars commute with a linear isometry equivalence. -/
@[simp]
theorem mapLinearIsometryEquiv_cthickening (K : ConvexSpaceBody E) (f : E ≃ₗᵢ[ℝ] F)
    (r : ℝ≥0) :
    (K.cthickening r).mapLinearIsometryEquiv f =
      (K.mapLinearIsometryEquiv f).cthickening r := by
  apply ConvexSpaceBody.ext
  change f '' Metric.cthickening (r : ℝ) K.carrier =
    Metric.cthickening (r : ℝ) (f '' K.carrier)
  exact Metric.image_cthickening_isometryEquiv f.toIsometryEquiv (r : ℝ) K.carrier

end ConvexSpaceBody

namespace Tube

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- A linear isometry equivalence sends a tube to the tube with the transported endpoints. -/
def mapLinearIsometryEquiv {δ : ℝ≥0} (T : Tube δ E) (f : E ≃ₗᵢ[ℝ] F) : Tube δ F :=
  Tube.mk' δ (x := f T.x) (y := f T.y) (by simpa using T.dist_eq_one)

@[simp]
theorem mapLinearIsometryEquiv_x {δ : ℝ≥0} (T : Tube δ E) (f : E ≃ₗᵢ[ℝ] F) :
    (T.mapLinearIsometryEquiv f).x = f T.x := rfl

@[simp]
theorem mapLinearIsometryEquiv_y {δ : ℝ≥0} (T : Tube δ E) (f : E ≃ₗᵢ[ℝ] F) :
    (T.mapLinearIsometryEquiv f).y = f T.y := rfl

@[simp]
theorem mapLinearIsometryEquiv_center {δ : ℝ≥0} (T : Tube δ E)
    (f : E ≃ₗᵢ[ℝ] F) :
    (T.mapLinearIsometryEquiv f).center = f T.center := by
  simp [Tube.center, midpoint_eq_smul_add]

@[simp]
theorem mapLinearIsometryEquiv_carrier {δ : ℝ≥0} (T : Tube δ E)
    (f : E ≃ₗᵢ[ℝ] F) : (T.mapLinearIsometryEquiv f).carrier = f '' T.carrier := by
  have hseg : segment ℝ (f T.x) (f T.y) = f '' segment ℝ T.x T.y := by
    simpa using
      (image_segment ℝ f.toLinearEquiv.toAffineEquiv.toAffineMap T.x T.y).symm
  rw [(T.mapLinearIsometryEquiv f).carrier_eq, mapLinearIsometryEquiv_x,
    mapLinearIsometryEquiv_y, T.carrier_eq, Set.image_iUnion₂, hseg, Set.biUnion_image]
  refine Set.iUnion₂_congr fun z _ ↦ ?_
  exact (f.image_closedBall z δ).symm

@[simp]
theorem mapLinearIsometryEquiv_toConvexSpaceBody {δ : ℝ≥0} (T : Tube δ E)
    (f : E ≃ₗᵢ[ℝ] F) :
    (T.mapLinearIsometryEquiv f).toConvexSpaceBody =
      T.toConvexSpaceBody.mapLinearIsometryEquiv f := by
  apply ConvexSpaceBody.ext
  exact T.mapLinearIsometryEquiv_carrier f

end Tube

namespace ShadedBody

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

/-- Cross-space isometric transport of a shaded convex body. -/
def mapLinearIsometryEquiv (V : ShadedBody E) (f : E ≃ₗᵢ[ℝ] F) : ShadedBody F where
  toConvexSpaceBody := V.toConvexSpaceBody.mapLinearIsometryEquiv f
  shade := f '' V.shade
  measurableSet_shade := by
    rw [show f '' V.shade = (f.symm : F → E) ⁻¹' V.shade by
      exact congrFun
        (Set.image_eq_preimage_of_inverse f.symm_apply_apply f.apply_symm_apply) V.shade]
    exact f.symm.continuous.measurable V.measurableSet_shade
  shade_subset := Set.image_mono V.shade_subset

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
@[simp]
theorem mapLinearIsometryEquiv_carrier (V : ShadedBody E) (f : E ≃ₗᵢ[ℝ] F) :
    (V.mapLinearIsometryEquiv f).carrier = f '' V.carrier := rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
@[simp]
theorem mapLinearIsometryEquiv_shade (V : ShadedBody E) (f : E ≃ₗᵢ[ℝ] F) :
    (V.mapLinearIsometryEquiv f).shade = f '' V.shade := rfl

end ShadedBody

namespace Kakeya

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

/-- Linear isometry equivalences preserve Euclidean volume across ambient spaces. -/
theorem volume_image_linearIsometryEquiv (f : E ≃ₗᵢ[ℝ] F) (A : Set E) :
    volume (f '' A) = volume A := by
  rw [show f '' A = (f.symm : F → E) ⁻¹' A by
    exact congrFun
      (Set.image_eq_preimage_of_inverse f.symm_apply_apply f.apply_symm_apply) A]
  let e : F ≃ᵐ E := f.symm.toHomeomorph.toMeasurableEquiv
  have he : MeasurePreserving e volume volume := f.symm.measurePreserving
  exact he.measure_preimage_equiv A

end Kakeya

namespace ShadedTube

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

/-- Cross-space isometric transport of a shaded tube. -/
def mapLinearIsometryEquiv {δ : ℝ≥0} (V : ShadedTube δ E)
    (f : E ≃ₗᵢ[ℝ] F) : ShadedTube δ F where
  __ := V.toTube.mapLinearIsometryEquiv f
  shade := f '' V.shade
  measurableSet_shade := by
    rw [show f '' V.shade = (f.symm : F → E) ⁻¹' V.shade by
      exact congrFun
        (Set.image_eq_preimage_of_inverse f.symm_apply_apply f.apply_symm_apply) V.shade]
    exact f.symm.continuous.measurable V.measurableSet_shade
  shade_subset := by
    rw [Tube.mapLinearIsometryEquiv_carrier]
    exact Set.image_mono V.shade_subset

@[simp]
theorem mapLinearIsometryEquiv_toTube {δ : ℝ≥0} (V : ShadedTube δ E)
    (f : E ≃ₗᵢ[ℝ] F) :
    (V.mapLinearIsometryEquiv f).toTube = V.toTube.mapLinearIsometryEquiv f := rfl

@[simp]
theorem mapLinearIsometryEquiv_carrier {δ : ℝ≥0} (V : ShadedTube δ E)
    (f : E ≃ₗᵢ[ℝ] F) : (V.mapLinearIsometryEquiv f).carrier = f '' V.carrier := by
  exact Tube.mapLinearIsometryEquiv_carrier V.toTube f

@[simp]
theorem mapLinearIsometryEquiv_shade {δ : ℝ≥0} (V : ShadedTube δ E)
    (f : E ≃ₗᵢ[ℝ] F) : (V.mapLinearIsometryEquiv f).shade = f '' V.shade := rfl

@[simp]
theorem mapLinearIsometryEquiv_toConvexSpaceBody {δ : ℝ≥0} (V : ShadedTube δ E)
    (f : E ≃ₗᵢ[ℝ] F) :
    (V.mapLinearIsometryEquiv f).toConvexSpaceBody =
      V.toConvexSpaceBody.mapLinearIsometryEquiv f := by
  exact Tube.mapLinearIsometryEquiv_toConvexSpaceBody V.toTube f

variable {ι : Type*}

/-- Fullness of a shaded-tube family is invariant under cross-space isometric transport. -/
@[simp]
theorem fullness_mapLinearIsometryEquiv {δ : ℝ≥0} (s : Finset ι)
    (V : ι → ShadedTube δ E) (f : E ≃ₗᵢ[ℝ] F) :
    ShadedBody.fullness s (fun i => (V i).mapLinearIsometryEquiv f |>.toShadedBody) =
      ShadedBody.fullness s (fun i => (V i).toShadedBody) := by
  unfold ShadedBody.fullness ShadedBody.fullness'
  have hshade : (∑ i ∈ s, volume ((V i).mapLinearIsometryEquiv f).shade) =
      ∑ i ∈ s, volume (V i).shade := by
    exact Finset.sum_congr rfl fun i _ => Kakeya.volume_image_linearIsometryEquiv f (V i).shade
  have hcarrier : (∑ i ∈ s, volume ((V i).mapLinearIsometryEquiv f).carrier) =
      ∑ i ∈ s, volume (V i).carrier := by
    exact Finset.sum_congr rfl fun i _ => by
      rw [mapLinearIsometryEquiv_carrier]
      exact Kakeya.volume_image_linearIsometryEquiv f (V i).carrier
  rw [hshade, hcarrier]

/-- The shading-union volume of a shaded-tube family is invariant under isometric transport. -/
@[simp]
theorem volume_iUnion_mapLinearIsometryEquiv_shade {δ : ℝ≥0} (s : Finset ι)
    (V : ι → ShadedTube δ E) (f : E ≃ₗᵢ[ℝ] F) :
    volume (⋃ i ∈ s, ((V i).mapLinearIsometryEquiv f).shade) =
      volume (⋃ i ∈ s, (V i).shade) := by
  rw [show (⋃ i ∈ s, ((V i).mapLinearIsometryEquiv f).shade) =
      f '' (⋃ i ∈ s, (V i).shade) by simp [Set.image_iUnion₂]]
  exact Kakeya.volume_image_linearIsometryEquiv f _

/-- Multiplicity of a shaded-tube family is invariant under isometric transport. -/
@[simp]
theorem multiplicity_mapLinearIsometryEquiv {δ : ℝ≥0} (s : Finset ι)
    (V : ι → ShadedTube δ E) (f : E ≃ₗᵢ[ℝ] F) :
    ShadedBody.multiplicity s (fun i => (V i).mapLinearIsometryEquiv f |>.toShadedBody) =
      ShadedBody.multiplicity s (fun i => (V i).toShadedBody) := by
  unfold ShadedBody.multiplicity
  rw [volume_iUnion_mapLinearIsometryEquiv_shade]
  congr 1
  exact Finset.sum_congr rfl fun i _ => Kakeya.volume_image_linearIsometryEquiv f (V i).shade

end ShadedTube

namespace ConvexSpaceBody

open Kakeya

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

/-- The volume of a convex body is unchanged by cross-space isometric transport. -/
@[simp]
theorem volume_mapLinearIsometryEquiv (K : ConvexSpaceBody E) (f : E ≃ₗᵢ[ℝ] F) :
    volume (K.mapLinearIsometryEquiv f).carrier = volume K.carrier := by
  exact volume_image_linearIsometryEquiv f K.carrier

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
/-- The closed unit ball is carried to the closed unit ball. -/
@[simp]
theorem closedUnitBall_mapLinearIsometryEquiv (f : E ≃ₗᵢ[ℝ] F) :
    (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).mapLinearIsometryEquiv f =
      ConvexSpaceBody.closedUnitBall := by
  apply ConvexSpaceBody.ext
  change f '' Metric.closedBall 0 1 = Metric.closedBall 0 1
  simp

end ConvexSpaceBody

namespace ShadedBody

open Kakeya

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  {ι : Type*}

/-- Shading volume is unchanged by cross-space isometric transport. -/
@[simp]
theorem volume_mapLinearIsometryEquiv_shade (V : ShadedBody E) (f : E ≃ₗᵢ[ℝ] F) :
    volume (V.mapLinearIsometryEquiv f).shade = volume V.shade := by
  exact volume_image_linearIsometryEquiv f V.shade

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The transported shading union is the image of the original shading union. -/
theorem iUnion_shade_mapLinearIsometryEquiv (s : Finset ι) (V : ι → ShadedBody E)
    (f : E ≃ₗᵢ[ℝ] F) :
    (⋃ i ∈ s, ((V i).mapLinearIsometryEquiv f).shade) =
      f '' (⋃ i ∈ s, (V i).shade) := by
  simp [Set.image_iUnion₂]

/-- The total union volume is unchanged by cross-space isometric transport. -/
@[simp]
theorem volume_iUnion_mapLinearIsometryEquiv_shade (s : Finset ι) (V : ι → ShadedBody E)
    (f : E ≃ₗᵢ[ℝ] F) :
    volume (⋃ i ∈ s, ((V i).mapLinearIsometryEquiv f).shade) =
      volume (⋃ i ∈ s, (V i).shade) := by
  rw [iUnion_shade_mapLinearIsometryEquiv]
  exact volume_image_linearIsometryEquiv f _

/-- Fullness is unchanged by cross-space isometric transport. -/
@[simp]
theorem fullness_mapLinearIsometryEquiv (s : Finset ι) (V : ι → ShadedBody E)
    (f : E ≃ₗᵢ[ℝ] F) :
    fullness s (fun i => (V i).mapLinearIsometryEquiv f) = fullness s V := by
  unfold fullness fullness'
  have hshade : (∑ i ∈ s, volume ((V i).mapLinearIsometryEquiv f).shade) =
      ∑ i ∈ s, volume (V i).shade := by
    exact Finset.sum_congr rfl fun i _ => volume_mapLinearIsometryEquiv_shade (V i) f
  have hcarrier : (∑ i ∈ s, volume ((V i).mapLinearIsometryEquiv f).carrier) =
      ∑ i ∈ s, volume (V i).carrier := by
    exact Finset.sum_congr rfl fun i _ =>
      ConvexSpaceBody.volume_mapLinearIsometryEquiv (V i).toConvexSpaceBody f
  rw [hshade, hcarrier]

/-- Multiplicity is unchanged by cross-space isometric transport. -/
@[simp]
theorem multiplicity_mapLinearIsometryEquiv (s : Finset ι) (V : ι → ShadedBody E)
    (f : E ≃ₗᵢ[ℝ] F) :
    multiplicity s (fun i => (V i).mapLinearIsometryEquiv f) = multiplicity s V := by
  unfold multiplicity
  rw [volume_iUnion_mapLinearIsometryEquiv_shade]
  congr 1
  exact Finset.sum_congr rfl fun i _ => volume_mapLinearIsometryEquiv_shade (V i) f

end ShadedBody

namespace Kakeya

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  {ι : Type*}

/-- Density in a container is unchanged when the family and container are transported together. -/
@[simp]
theorem densityIn_mapLinearIsometryEquiv (s : Finset ι) (W : ι → ConvexSpaceBody E)
    (K : ConvexSpaceBody E) (f : E ≃ₗᵢ[ℝ] F) :
    densityIn s (fun i => (W i).mapLinearIsometryEquiv f)
      (K.mapLinearIsometryEquiv f) = densityIn s W K := by
  classical
  unfold densityIn
  have hfilter : s.filter (fun i => (W i).mapLinearIsometryEquiv f ≤
      K.mapLinearIsometryEquiv f) = s.filter (fun i => W i ≤ K) := by
    apply Finset.filter_congr
    intro i _
    exact ConvexSpaceBody.mapLinearIsometryEquiv_le_mapLinearIsometryEquiv_iff f
  rw [hfilter]
  congr 1
  · exact Finset.sum_congr rfl fun i _ =>
      ConvexSpaceBody.volume_mapLinearIsometryEquiv (W i) f
  · exact ConvexSpaceBody.volume_mapLinearIsometryEquiv K f

/-- Maximum density is unchanged by cross-space isometric transport. -/
@[simp]
theorem maxDensity_mapLinearIsometryEquiv (s : Finset ι) (W : ι → ConvexSpaceBody E)
    (f : E ≃ₗᵢ[ℝ] F) :
    maxDensity s (fun i => (W i).mapLinearIsometryEquiv f) = maxDensity s W := by
  apply le_antisymm
  · rw [maxDensity_le_iff]
    intro K
    have hK : K = (K.mapLinearIsometryEquiv f.symm).mapLinearIsometryEquiv f := by simp
    rw [hK, densityIn_mapLinearIsometryEquiv]
    exact le_maxDensity s W (K.mapLinearIsometryEquiv f.symm)
  · rw [maxDensity_le_iff]
    intro K
    rw [← densityIn_mapLinearIsometryEquiv s W K f]
    exact le_maxDensity s (fun i => (W i).mapLinearIsometryEquiv f)
      (K.mapLinearIsometryEquiv f)

end Kakeya

namespace ConvexSpaceBody

open Kakeya

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  {ι : Type*} {s : Finset ι} {W : ι → ConvexSpaceBody E} {K : ConvexSpaceBody E}
  {C : ℝ≥0∞}

/-- A Frostman condition is preserved, with the same constant, by isometric transport. -/
theorem IsFrostmanIn.mapLinearIsometryEquiv (h : IsFrostmanIn s W K C)
    (f : E ≃ₗᵢ[ℝ] F) :
    IsFrostmanIn s (fun i => (W i).mapLinearIsometryEquiv f)
      (K.mapLinearIsometryEquiv f) C := fun K' hK' ↦ by
  convert h (K'.mapLinearIsometryEquiv f.symm) (by
    have := ConvexSpaceBody.mapLinearIsometryEquiv_le_mapLinearIsometryEquiv_iff
      (K := K') (L := K.mapLinearIsometryEquiv f) f.symm
    simpa using this.mpr hK') using 1
  · nth_rw 1 [← ConvexSpaceBody.symm_mapLinearIsometryEquiv_mapLinearIsometryEquiv
      (K := K') (f := f)]
    exact densityIn_mapLinearIsometryEquiv s W (K'.mapLinearIsometryEquiv f.symm) f
  · exact congrArg (C * ·) (densityIn_mapLinearIsometryEquiv s W K f)


/-- A Katz--Tao condition is preserved, with the same constant, by isometric transport. -/
theorem IsKatzTao.mapLinearIsometryEquiv (h : IsKatzTao s W C) (f : E ≃ₗᵢ[ℝ] F) :
    IsKatzTao s (fun i => (W i).mapLinearIsometryEquiv f) C := by
  rw [IsKatzTao_def, maxDensity_mapLinearIsometryEquiv]
  exact h


end ConvexSpaceBody

section EssentiallyDistinct

open Kakeya
open scoped NNReal ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

/-- Essential distinctness is preserved by cross-space isometric transport. -/
theorem IsEssentiallyDistinct.mapLinearIsometryEquiv {U V : Set E}
    (h : IsEssentiallyDistinct U V) (f : E ≃ₗᵢ[ℝ] F) :
    IsEssentiallyDistinct (f '' U) (f '' V) := by
  unfold IsEssentiallyDistinct at *
  rw [← Set.image_inter f.injective]
  simpa only [Kakeya.volume_image_linearIsometryEquiv] using h


end EssentiallyDistinct

namespace Kakeya

universe u

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

/-- The partial Katz--Tao estimate is invariant under a linear isometry equivalence of ambient
spaces. -/
theorem KatzTaoEstimate.mapLinearIsometryEquiv {β : ℝ} (h : KatzTaoEstimate.{u} E β)
    (f : E ≃ₗᵢ[ℝ] F) : KatzTaoEstimate.{u} F β := by
  intro ε hε
  obtain ⟨η, hη, hev⟩ := h ε hε
  refine ⟨η, hη, ?_⟩
  filter_upwards [hev] with δ hδ
  intro ι s T hball hKT hfull
  let T' : ι → ShadedTube δ E := fun i => (T i).mapLinearIsometryEquiv f.symm
  have hball' : ∀ i ∈ s, (T' i).carrier ⊆ Metric.closedBall 0 1 := by
    intro i hi
    dsimp only [T']
    rw [ShadedTube.mapLinearIsometryEquiv_carrier]
    calc
      f.symm '' (T i).carrier ⊆ f.symm '' Metric.closedBall 0 1 :=
        Set.image_mono (hball i hi)
      _ = Metric.closedBall 0 1 := by
        simp
  have hKT' : ConvexSpaceBody.IsKatzTao s (fun i => (T' i).toConvexSpaceBody)
      (δ ^ (-η)) := by
    simpa only [T', ShadedTube.mapLinearIsometryEquiv_toConvexSpaceBody] using
      hKT.mapLinearIsometryEquiv f.symm
  have hfull' : ShadedBody.fullness s (fun i => (T' i).toShadedBody) ≥ δ ^ η := by
    simpa only [T', ShadedTube.fullness_mapLinearIsometryEquiv] using hfull
  have hres := hδ s T' hball' hKT' hfull'
  have hsum : (∑ i ∈ s, volume (T' i).shade) = ∑ i ∈ s, volume (T i).shade := by
    exact Finset.sum_congr rfl fun i _ => by
      simpa only [T', ShadedTube.mapLinearIsometryEquiv_shade] using
        volume_image_linearIsometryEquiv f.symm (T i).shade
  have hunion : volume (⋃ i ∈ s, (T' i).shade) = volume (⋃ i ∈ s, (T i).shade) := by
    simpa only [T'] using
      ShadedTube.volume_iUnion_mapLinearIsometryEquiv_shade s T f.symm
  rw [hsum, hunion] at hres
  exact hres

/-- The partial Frostman estimate is invariant under a linear isometry equivalence of ambient
spaces. -/
theorem FrostmanEstimate.mapLinearIsometryEquiv {β : ℝ} (h : FrostmanEstimate.{u} E β)
    (f : E ≃ₗᵢ[ℝ] F) : FrostmanEstimate.{u} F β := by
  intro ε hε
  obtain ⟨η, hη, hev⟩ := h ε hε
  refine ⟨η, hη, ?_⟩
  filter_upwards [hev] with δ hδ
  intro ι s T hball hED hFrost hfull
  let T' : ι → ShadedTube δ E := fun i => (T i).mapLinearIsometryEquiv f.symm
  have hball' : ∀ i ∈ s, (T' i).carrier ⊆ Metric.closedBall 0 1 := by
    intro i hi
    dsimp only [T']
    rw [ShadedTube.mapLinearIsometryEquiv_carrier]
    calc
      f.symm '' (T i).carrier ⊆ f.symm '' Metric.closedBall 0 1 :=
        Set.image_mono (hball i hi)
      _ = Metric.closedBall 0 1 := by
        simp
  have hED' : (s : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct (T' i).carrier (T' j).carrier) := by
    intro i hi j hj hij
    simpa only [T', ShadedTube.mapLinearIsometryEquiv_carrier] using
      (hED hi hj hij).mapLinearIsometryEquiv f.symm
  have hFrost' : ConvexSpaceBody.IsFrostmanIn s (fun i => (T' i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall (δ ^ (-η)) := by
    simpa only [T', ShadedTube.mapLinearIsometryEquiv_toConvexSpaceBody,
      ConvexSpaceBody.closedUnitBall_mapLinearIsometryEquiv] using
      hFrost.mapLinearIsometryEquiv f.symm
  have hfull' : ShadedBody.fullness s (fun i => (T' i).toShadedBody) ≥ δ ^ η := by
    simpa only [T', ShadedTube.fullness_mapLinearIsometryEquiv] using hfull
  have hres := hδ s T' hball' hED' hFrost' hfull'
  have hmult : ShadedBody.multiplicity s (fun i => (T' i).toShadedBody) =
      ShadedBody.multiplicity s (fun i => (T i).toShadedBody) := by
    simpa only [T'] using ShadedTube.multiplicity_mapLinearIsometryEquiv s T f.symm
  rw [hmult, f.toLinearEquiv.finrank_eq] at hres
  exact hres

end Kakeya

namespace Kakeya

universe v

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A universe-polymorphic partial Katz--Tao estimate may be used on `Type 0` index families.

The plank estimate internally introduces representative index types in `Type 0`.  Reindexing a
`Type 0` family along `Equiv.ulift` puts it in `Type v`; all sums, unions, density, fullness and
cardinality terms are unchanged. -/
theorem KatzTaoEstimate.toTypeZero {β : ℝ} (h : KatzTaoEstimate.{v} E β) :
    KatzTaoEstimate.{0} E β := by
  intro ε hε
  obtain ⟨η, hη, hev⟩ := h ε hε
  refine ⟨η, hη, ?_⟩
  filter_upwards [hev] with δ hδ
  intro ι s T hB hKT hFull
  let e : ι ↪ ULift.{v} ι := ⟨fun i => ⟨i⟩, by
    intro i j hij
    exact congrArg ULift.down hij⟩
  let s' : Finset (ULift.{v} ι) := s.map e
  let T' : ULift.{v} ι → ShadedTube δ E := fun i => T i.down
  have hB' : ∀ i ∈ s', (T' i).carrier ⊆ Metric.closedBall 0 1 := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp (by simpa only [s'] using hi)
    change (T j).carrier ⊆ Metric.closedBall 0 1
    exact hB j hj
  have hKT' : ConvexSpaceBody.IsKatzTao s'
      (fun i => (T' i).toConvexSpaceBody) (δ ^ (-η)) := by
    rw [ConvexSpaceBody.isKatzTao_iff] at hKT ⊢
    intro K
    simpa [s', T', e, densityIn, Finset.sum_map, Finset.filter_map] using hKT K
  have hFull' : ShadedBody.fullness s' (fun i => (T' i).toShadedBody) ≥ δ ^ η := by
    simpa [s', T', e, ShadedBody.fullness, ShadedBody.fullness', Finset.sum_map] using hFull
  have hBound := hδ s' T' hB' hKT' hFull'
  have hcard : s'.card = s.card := Finset.card_map _
  have hsum : ∑ i ∈ s', volume (T' i).shade = ∑ i ∈ s, volume (T i).shade :=
    Finset.sum_map _ _ _
  have hUnion : (⋃ i ∈ s', (T' i).shade) = ⋃ i ∈ s, (T i).shade := by
    ext x
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨i, hi, hxi⟩
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
      exact ⟨j, hj, hxi⟩
    · rintro ⟨i, hi, hxi⟩
      exact ⟨e i, Finset.mem_map_of_mem e hi, hxi⟩
  simpa only [hsum, hUnion, hcard] using hBound

end Kakeya

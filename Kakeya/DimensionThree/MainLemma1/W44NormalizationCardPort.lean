/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Cases

/-!
The card-retaining fine-normalization construction used by the WZ
middle route.  It is isolated in an internal namespace because the current public projection in
`Cases.lean` omits the card-retention conclusion even though the underlying selection supplies it.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya
namespace ml1Boot
namespace W44NormalizationPort

noncomputable section

universe u

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Reading off the four conclusions from `Tube.IsComparableReplacementFree`.**

The package hands back the retained index set `u'`, and its four fields plus two generic
transport lemmas give the three quantitative clauses at the constants recorded here:
multiplicity is exact and pays only the selection constant `C₁`
(`ShadedBody.multiplicity_le_of_isCRefinement` against the refinement clause), fullness pays the
comparability constant `Cv` on top of it (`ShadedBody.IsCRefinement.coe_mul_fullness_le`), and
the Frostman constant pays `C₁` for the passage to the subfamily
(`ConvexSpaceBody.frostmanConstIn_subfamily_le`, applicable because all members of `𝕍` are
`σ`-tubes and hence of equal volume) and `Cv` for the comparability.  The factor `Λ ^ 2` is the
density spread, and enters through the refinement constant `(C₁ Λ ^ 2)⁻¹`. -/
lemma of_comparableReplacementFree {ι : Type*} {u : Finset ι} {σ : ℝ≥0}
    {𝕎 : ι → ShadedBody E} {𝕍 : ι → ShadedTube σ E} {K : ConvexSpaceBody E}
    {Cv Λ C₁ : ℝ≥0} (hΛ : 1 ≤ Λ) (hCv : 1 ≤ Cv) (hC₁ : 1 ≤ C₁)
    (hVK : ∀ i ∈ u, (𝕍 i).toConvexSpaceBody ≤ K)
    (h : _root_.Tube.IsComparableReplacementFree u 𝕎 𝕍 K Cv Λ C₁) :
    ∃ u' ⊆ u, u'.Nonempty ∧
      (u' : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (𝕍 i).carrier (𝕍 j).carrier) ∧
        (u.card : ℝ≥0∞) ≤ (C₁ : ℝ≥0∞) * (u'.card : ℝ≥0∞) ∧
        ShadedBody.multiplicity u 𝕎
          ≤ (C₁ : ℝ≥0∞) * (Λ : ℝ≥0∞) ^ 2
            * ShadedBody.multiplicity u' (fun i => (𝕍 i).toShadedBody) ∧
        (ShadedBody.fullness u 𝕎 : ℝ≥0∞)
          ≤ ((Cv : ℝ≥0∞) * (C₁ : ℝ≥0∞)) * (Λ : ℝ≥0∞) ^ 2
            * (ShadedBody.fullness u' (fun i => (𝕍 i).toShadedBody) : ℝ≥0∞) ∧
        frostmanConstIn u' (fun i => (𝕍 i).toConvexSpaceBody) K
          ≤ (C₁ : ℝ≥0∞) * (Cv : ℝ≥0∞)
            * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K := by
  rcases h.select with ⟨u', hu'sub, hu'ne, hpair, hu'card, hcref⟩
  let ce : ℝ≥0∞ := ((C₁ * Λ ^ 2)⁻¹ : ℝ≥0)
  have hL0 : Λ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hΛ)
  have hC₁0 : C₁ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hC₁)
  have hC₁Λ : (C₁ * Λ ^ 2 : ℝ≥0) ≠ 0 := mul_ne_zero hC₁0 (pow_ne_zero 2 hL0)
  have hC₁ΛE0 : ((C₁ * Λ ^ 2 : ℝ≥0) : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hC₁Λ
  have hce0 : ce ≠ 0 := by
    dsimp [ce]
    rw [ENNReal.coe_inv hC₁Λ]
    intro hz
    have hcan := ENNReal.inv_mul_cancel hC₁ΛE0
      (ENNReal.coe_ne_top : ((C₁ * Λ ^ 2 : ℝ≥0) : ℝ≥0∞) ≠ ⊤)
    rw [hz, zero_mul] at hcan
    exact zero_ne_one hcan
  have hce_top : ce ≠ ⊤ := by
    dsimp [ce]
    exact ENNReal.coe_ne_top
  have cRef_ne0 : (C₁ * Λ ^ 2 : ℝ≥0)⁻¹ ≠ 0 :=
    ENNReal.coe_ne_zero.mp (by simpa [ce] using hce0)
  have hcoef : ce⁻¹ = (C₁ : ℝ≥0∞) * (Λ : ℝ≥0∞) ^ 2 := by
    change (((C₁ * Λ ^ 2)⁻¹ : ℝ≥0) : ℝ≥0∞)⁻¹ = (C₁ : ℝ≥0∞) * (Λ : ℝ≥0∞) ^ 2
    rw [ENNReal.coe_inv hC₁Λ]
    rw [InvolutiveInv.inv_inv]
    rw [ENNReal.coe_mul, ENNReal.coe_pow]
  refine ⟨u', hu'sub, hu'ne, hpair, hu'card, ?_, ?_, ?_⟩
  · rw [← h.multiplicity]
    calc
      ShadedBody.multiplicity u (fun i => (𝕍 i).toShadedBody)
          ≤ ce⁻¹ * ShadedBody.multiplicity u' (fun i => (𝕍 i).toShadedBody) := by
            exact ShadedBody.multiplicity_le_of_isCRefinement (s := u)
              (V := fun i => (𝕍 i).toShadedBody) (s' := u')
              (V' := fun i => (𝕍 i).toShadedBody) (c := (C₁ * Λ ^ 2)⁻¹) cRef_ne0 hcref
      _ = (C₁ : ℝ≥0∞) * (Λ : ℝ≥0∞) ^ 2
              * ShadedBody.multiplicity u' (fun i => (𝕍 i).toShadedBody) := by
            rw [hcoef]
  · have hfullNN : ShadedBody.fullness u 𝕎
        ≤ (Cv : ℝ≥0) * ShadedBody.fullness u (fun i => (𝕍 i).toShadedBody) := by
      have hCv0 : Cv ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hCv)
      calc
        ShadedBody.fullness u 𝕎
            = (Cv : ℝ≥0) * ((Cv : ℝ≥0)⁻¹ * ShadedBody.fullness u 𝕎) := by
              rw [← mul_assoc, mul_inv_cancel₀ hCv0, one_mul]
        _ ≤ (Cv : ℝ≥0) * ShadedBody.fullness u (fun i => (𝕍 i).toShadedBody) := by
              exact mul_le_mul_right h.fullness (Cv : ℝ≥0)
    have hfull1 : (ShadedBody.fullness u 𝕎 : ℝ≥0∞)
        ≤ (Cv : ℝ≥0∞) * (ShadedBody.fullness u (fun i => (𝕍 i).toShadedBody) : ℝ≥0∞) := by
      exact_mod_cast hfullNN
    have hcfull : ce * (ShadedBody.fullness u (fun i => (𝕍 i).toShadedBody) : ℝ≥0∞)
        ≤ (ShadedBody.fullness u' (fun i => (𝕍 i).toShadedBody) : ℝ≥0∞) := by
      simpa [ce] using (IsCRefinement.coe_mul_fullness_le hcref)
    have hfull2 : (ShadedBody.fullness u (fun i => (𝕍 i).toShadedBody) : ℝ≥0∞)
        ≤ (C₁ : ℝ≥0∞) * (Λ : ℝ≥0∞) ^ 2
            * (ShadedBody.fullness u' (fun i => (𝕍 i).toShadedBody) : ℝ≥0∞) := by
      have hmm := mul_le_mul_right hcfull ce⁻¹
      rwa [← mul_assoc, ENNReal.inv_mul_cancel hce0 hce_top, one_mul, hcoef] at hmm
    calc
      (ShadedBody.fullness u 𝕎 : ℝ≥0∞)
          ≤ (Cv : ℝ≥0∞) * (ShadedBody.fullness u (fun i => (𝕍 i).toShadedBody) : ℝ≥0∞) :=
            hfull1
      _ ≤ (Cv : ℝ≥0∞)
            * ((C₁ : ℝ≥0∞) * (Λ : ℝ≥0∞) ^ 2
                * (ShadedBody.fullness u' (fun i => (𝕍 i).toShadedBody) : ℝ≥0∞)) := by
            gcongr
      _ = ((Cv : ℝ≥0∞) * (C₁ : ℝ≥0∞)) * (Λ : ℝ≥0∞) ^ 2
            * (ShadedBody.fullness u' (fun i => (𝕍 i).toShadedBody) : ℝ≥0∞) := by ring
  · rcases hu'ne with ⟨i₀, hi₀⟩
    have hu'ne_nonempty : u.Nonempty := ⟨i₀, hu'sub hi₀⟩
    let v : ℝ≥0∞ := volume ((𝕍 i₀).toConvexSpaceBody).carrier
    have hvol : ∀ i ∈ u, volume ((𝕍 i).toConvexSpaceBody).carrier = v := by
      intro i hi
      dsimp [v]
      simpa using _root_.Tube.volume_carrier_eq_volume_carrier
        (by simpa using (𝕍 i).toTube) (by simpa using (𝕍 i₀).toTube)
    have hC₁E0 : (C₁ : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hC₁0
    have hC₁Etop : (C₁ : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
    have hcardκ : (C₁ : ℝ≥0∞)⁻¹ * (u.card : ℝ≥0∞) ≤ (u'.card : ℝ≥0∞) := by
      calc
        (C₁ : ℝ≥0∞)⁻¹ * (u.card : ℝ≥0∞)
            ≤ (C₁ : ℝ≥0∞)⁻¹ * ((C₁ : ℝ≥0∞) * (u'.card : ℝ≥0∞)) := by
              exact mul_le_mul_right hu'card _
        _ = (u'.card : ℝ≥0∞) := by
              rw [← mul_assoc, ENNReal.inv_mul_cancel hC₁E0 hC₁Etop, one_mul]
    have hκ0 : (C₁ : ℝ≥0∞)⁻¹ ≠ 0 := by
      intro hz
      have hcan := ENNReal.inv_mul_cancel hC₁E0 hC₁Etop
      rw [hz, zero_mul] at hcan
      exact zero_ne_one hcan
    have hsubF := ConvexSpaceBody.frostmanConstIn_subfamily_le (s := u)
      (W := fun i => (𝕍 i).toConvexSpaceBody) (K := K)
      (v := v) (κ := (C₁ : ℝ≥0∞)⁻¹)
      hu'ne_nonempty hvol hVK hu'sub hκ0 hcardκ
    have hF1 : frostmanConstIn u' (fun i => (𝕍 i).toConvexSpaceBody) K
        ≤ (C₁ : ℝ≥0∞) * frostmanConstIn u (fun i => (𝕍 i).toConvexSpaceBody) K := by
      simpa [InvolutiveInv.inv_inv] using hsubF
    calc
      frostmanConstIn u' (fun i => (𝕍 i).toConvexSpaceBody) K
          ≤ (C₁ : ℝ≥0∞) * frostmanConstIn u (fun i => (𝕍 i).toConvexSpaceBody) K := hF1
      _ ≤ (C₁ : ℝ≥0∞)
            * ((Cv : ℝ≥0∞) * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K) := by
            exact mul_le_mul_right h.frostmanConstIn (C₁ : ℝ≥0∞)
      _ = (C₁ : ℝ≥0∞) * (Cv : ℝ≥0∞)
            * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K := by ring

/-- **The ambient enlargement to `B₁`**, in the form the fine normalization uses it: reading a
Frostman constant at the unit ball rather than at a smaller body `K'` containing every member
costs exactly the volume ratio `|B₁| / |K'|`
(`ConvexSpaceBody.frostmanConstIn_ambient_mono`), and `hratio` bounds that ratio by `Cv`. -/
lemma frostmanConstIn_closedUnitBall_le_of_ambient
    {ι : Type*} {u : Finset ι} {𝕎 : ι → ShadedBody E} {K' : ConvexSpaceBody E} {Cv : ℝ≥0}
    (hK' : K' ≤ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E))
    (hK'vol : volume K'.carrier ≠ 0)
    (hWK' : ∀ i ∈ u, (𝕎 i).toConvexSpaceBody ≤ K')
    (hratio : volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier
      ≤ (Cv : ℝ≥0∞) * volume K'.carrier) :
    frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody)
        (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E)
      ≤ (Cv : ℝ≥0∞) * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K' := by
  have hmono := frostmanConstIn_ambient_mono hK' hK'vol hWK'
  have hK'voltop : volume K'.carrier ≠ ⊤ := K'.isCompact'.measure_ne_top
  have hdiv : volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier
      / volume K'.carrier ≤ (Cv : ℝ≥0∞) := by
    rw [ENNReal.div_le_iff_le_mul (Or.inl hK'vol) (Or.inl hK'voltop)]
    exact hratio
  calc
    frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody)
        (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E)
        ≤ volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier
          / volume K'.carrier
          * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K' := hmono
    _ ≤ (Cv : ℝ≥0∞) * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K' := by
          gcongr

-- All `δ`-tubes are isometric, so their affine images under one map have a common volume: this
-- is the hypothesis `hcommon` of `Tube.exists_comparableReplacement_affine`.
lemma volume_affineImage_carrier_eq {δ : ℝ≥0} (S S' : ShadedTube δ E)
    (L : E ≃ᵃ[ℝ] E) (hcont : Continuous L) (hemb : MeasurableEmbedding L) :
    volume ((S.toShadedBody).affineImage L.toAffineMap hcont hemb).carrier
      = volume ((S'.toShadedBody).affineImage L.toAffineMap hcont hemb).carrier := by
  change volume (L.toAffineMap '' S.carrier) = volume (L.toAffineMap '' S'.carrier)
  rw [Kakeya.volume_affineImage L S.carrier, Kakeya.volume_affineImage L S'.carrier]
  rw [_root_.Tube.volume_carrier_eq_volume_carrier S.toTube S'.toTube]

-- An affine equivalence multiplies carrier and shade by the same Jacobian, so a two-sided
-- density bracket is carried over verbatim: the hypothesis `hZ` of
-- `Tube.exists_comparableReplacement_affine`, read at the common volume of the images.
lemma affineImage_shade_bounds {δ : ℝ≥0} (S S' : ShadedTube δ E)
    (L : E ≃ᵃ[ℝ] E) (hcont : Continuous L) (hemb : MeasurableEmbedding L)
    {Λ : ℝ≥0} {μ₀ : ℝ≥0∞}
    (h₁ : (Λ : ℝ≥0∞)⁻¹ * μ₀ * volume S.carrier ≤ volume S.shade)
    (h₂ : volume S.shade ≤ (Λ : ℝ≥0∞) * μ₀ * volume S.carrier) :
    (Λ : ℝ≥0∞)⁻¹ * μ₀
          * volume ((S'.toShadedBody).affineImage L.toAffineMap hcont hemb).carrier
        ≤ volume ((S.toShadedBody).affineImage L.toAffineMap hcont hemb).shade ∧
      volume ((S.toShadedBody).affineImage L.toAffineMap hcont hemb).shade
        ≤ (Λ : ℝ≥0∞) * μ₀
          * volume ((S'.toShadedBody).affineImage L.toAffineMap hcont hemb).carrier := by
  -- An affine equivalence multiplies every volume by the same Jacobian `J`, so the two-sided
  -- density bracket carried over from `h₁` and `h₂` is unchanged.
  let J : ℝ≥0∞ := ENNReal.ofReal |LinearMap.det (L.linear : E →ₗ[ℝ] E)|
  have hprimed : volume ((S'.toShadedBody).affineImage L.toAffineMap hcont hemb).carrier
      = volume ((S.toShadedBody).affineImage L.toAffineMap hcont hemb).carrier :=
    (volume_affineImage_carrier_eq S S' L hcont hemb).symm
  have hcarrier : volume ((S.toShadedBody).affineImage L.toAffineMap hcont hemb).carrier
      = J * volume S.carrier := by
    dsimp [J]
    change volume (L.toAffineMap '' S.carrier) = J * volume S.carrier
    exact Kakeya.volume_affineImage L S.carrier
  have hshade : volume ((S.toShadedBody).affineImage L.toAffineMap hcont hemb).shade
      = J * volume S.shade := by
    dsimp [J]
    change volume (L.toAffineMap '' S.shade) = J * volume S.shade
    exact Kakeya.volume_affineImage L S.shade
  constructor
  · rw [hprimed, hcarrier, hshade]
    calc
      (Λ : ℝ≥0∞)⁻¹ * μ₀ * (J * volume S.carrier)
          = J * ((Λ : ℝ≥0∞)⁻¹ * μ₀ * volume S.carrier) := by ring
      _ ≤ J * volume S.shade := by
            exact mul_le_mul (le_rfl : J ≤ J) h₁ (by positivity) (by positivity)
  · rw [hshade, hprimed, hcarrier]
    calc
      J * volume S.shade ≤ J * ((Λ : ℝ≥0∞) * μ₀ * volume S.carrier) := by
            exact mul_le_mul (le_rfl : J ≤ J) h₂ (by positivity) (by positivity)
      _ = (Λ : ℝ≥0∞) * μ₀ * (J * volume S.carrier) := by ring

-- A `δ`-tube of positive scale has positive volume (`Tube.le_volume`), and an affine
-- equivalence has nonzero Jacobian: the hypothesis `hW` of
-- `Tube.exists_comparableReplacement_affine`.
lemma volume_affineImage_carrier_pos [Nontrivial E] {δ : ℝ≥0} (hδ : 0 < δ)
    (S : ShadedTube δ E) (L : E ≃ᵃ[ℝ] E) (hcont : Continuous L)
    (hemb : MeasurableEmbedding L) :
    0 < volume ((S.toShadedBody).affineImage L.toAffineMap hcont hemb).carrier := by
  have hδpos : 0 < (δ : ℝ≥0∞) := ENNReal.coe_pos.mpr hδ
  have hpow : 0 < (δ : ℝ≥0∞) ^ (Module.finrank ℝ E - 1) := by positivity
  have hc : (0 : ℝ≥0∞) < (_root_.Tube.le_volume.c (Module.finrank ℝ E) : ℝ≥0∞) :=
    ENNReal.coe_pos.mpr (_root_.Tube.le_volume.c_pos (Module.finrank ℝ E))
  have hSpos : 0 < volume (S.toShadedBody).carrier := by
    calc
      0 < (_root_.Tube.le_volume.c (Module.finrank ℝ E) : ℝ≥0∞) * (δ : ℝ≥0∞) ^
          (Module.finrank ℝ E - 1) := by positivity
      _ ≤ volume (S.toShadedBody).carrier := by simpa using (_root_.Tube.le_volume S.toTube)
  have hdet : LinearMap.det (L.linear : E →ₗ[ℝ] E) ≠ 0 :=
    (LinearEquiv.isUnit_det' L.linear).ne_zero
  have hJ : 0 < ENNReal.ofReal |LinearMap.det (L.linear : E →ₗ[ℝ] E)| := by
    rw [ENNReal.ofReal_pos]
    exact abs_pos.mpr hdet
  change 0 < volume (L.toAffineMap '' (S.toShadedBody).carrier)
  rw [Kakeya.volume_affineImage]
  positivity

/-- **`Tube.rescale_outer_tube` with the image-core length freed to the radius `R`.**

`Tube.rescale_outer_tube` consumes its packaged `Tube.IsNormalizationDistortion` at exactly two
fields: `image_subset_cthickening`, which is proved unconditionally by
`Tube.normalization_image_subset_cthickening` (no containment hypothesis at all), and
`dist_le_C`, which it uses only to run the chain
`dist (Ψ x) (Ψ y) = dist (Φ x) (Φ y) / (4 R) ≤ C_N / (4 R) ≤ R / (4 R) = 1/4 ≤ 1`.

So the packaged structure is stronger than the route needs: what the route needs is
`dist (Φ x) (Φ y) ≤ R`, and the packaged field supplies that only via `C_N ≤ R`.  The
distinction is invisible at `R = C_N` but decisive over a dilate: for `T ⊆ c · T₀` the image
core has length at most `√(1 + 4 c²)`, which exceeds the hardwired `C_N = 64` once
`c > 31.99…`, while the dilated instance runs at `R = (1 + 2 c) C_N` and so satisfies the
relaxed hypothesis for *every* `c`.  Freeing the field here is therefore what makes
`Kakeya.ml1Boot.exists_fineNormalization_dilate` provable at an unbounded dilation ratio.

`Kakeya/Tube/Rescale.lean` is not ours to extend, so this is the local restatement; the proof is
that of `Tube.rescale_outer_tube` with the two `hdist` projections replaced by `hcth` and
`hlen`. -/
private lemma rescale_outer_tube_of_dist_le [Nontrivial E] {θ ρ σ : ℝ≥0} {R : ℝ}
    (hsit : _root_.Tube.IsRescalingSituation θ ρ σ R 3) (hn : Module.finrank ℝ E = 3)
    (hR : 0 < R) (hρσ : (ρ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ))
    (T₀ : Tube θ E) (T : Tube ρ E)
    (hcth : T₀.normalization '' T.carrier ⊆
      Metric.cthickening
        ((_root_.Tube.normalization.C (Module.finrank ℝ E) : ℝ) * ((ρ : ℝ) / (θ : ℝ)))
        (segment ℝ (T₀.normalization T.x) (T₀.normalization T.y)))
    (hlen : dist (T₀.normalization T.x) (T₀.normalization T.y) ≤ R)
    (hball : T₀.normalization '' T.carrier ⊆ Metric.closedBall T₀.x R)
    (hxy : T₀.rescaleMap R T.x ≠ T₀.rescaleMap R T.y) :
    T₀.rescaleMap R '' T.carrier ⊆ (_root_.Tube.centredExtension σ hxy).carrier ∧
      (_root_.Tube.centredExtension σ hxy).carrier ⊆ Metric.closedBall (0 : E) 1 ∧
      volume (_root_.Tube.centredExtension σ hxy).carrier
        ≤ ENNReal.ofReal ((4 * R) ^ 6) * volume (T₀.rescaleMap R '' T.carrier) := by
  let τ : ℝ := (ρ : ℝ) / (θ : ℝ)
  let C0 : ℝ := (_root_.Tube.normalization.C (Module.finrank ℝ E) : ℝ)
  have hθpos : (0 : ℝ) < (θ : ℝ) := by exact_mod_cast hsit.pos_ambient
  have hρ_nonneg : 0 ≤ τ := by
    dsimp [τ]
    exact div_nonneg (by positivity) (le_of_lt hθpos)
  have h4Rpos : (0 : ℝ) < 4 * R := by positivity
  have h4R0 : (4 : ℝ) * R ≠ 0 := ne_of_gt h4Rpos
  have hC0_nonneg : 0 ≤ C0 := by
    dsimp [C0]
    positivity
  have hC0_le_R : C0 ≤ R := by
    dsimp [C0]
    simpa [hn] using hsit.normalizationConst_le_radius
  have hRdiv : R / (4 * R) = (1 : ℝ) / 4 := by
    field_simp [h4R0, (by norm_num : (4 : ℝ) ≠ 0)]
  -- (1) Thickness: `Ψ(T) ⊆ V`.
  have hth0 : T₀.rescaleMap R '' T.carrier ⊆
      Metric.cthickening (C0 * τ / (4 * R))
        (segment ℝ (T₀.rescaleMap R T.x) (T₀.rescaleMap R T.y)) := by
    exact _root_.Tube.rescaleMap_image_subset_cthickening T₀ hR (r := C0 * τ)
      (A := T.carrier) (p := T.x) (q := T.y)
      (mul_nonneg hC0_nonneg hρ_nonneg) hcth
  have hrad : C0 * τ / (4 * R) ≤ (σ : ℝ) := by
    have h1 : C0 * τ ≤ R * τ := mul_le_mul_of_nonneg_right hC0_le_R hρ_nonneg
    have h2 : C0 * τ / (4 * R) ≤ (R * τ) / (4 * R) := by
      exact div_le_div_of_nonneg_right h1 (le_of_lt h4Rpos)
    have h3 : (R * τ) / (4 * R) = τ / 4 := by
      field_simp [h4R0, (by norm_num : (4 : ℝ) ≠ 0)]
    have h4 : τ / 4 ≤ (σ : ℝ) := by
      have : τ ≤ 4 * (σ : ℝ) := by simpa [τ] using hρσ
      linarith
    calc
      C0 * τ / (4 * R) ≤ (R * τ) / (4 * R) := h2
      _ = τ / 4 := h3
      _ ≤ (σ : ℝ) := h4
  have hth1 : T₀.rescaleMap R '' T.carrier ⊆
      Metric.cthickening (σ : ℝ) (segment ℝ (T₀.rescaleMap R T.x) (T₀.rescaleMap R T.y)) := by
    exact hth0.trans (Metric.cthickening_mono hrad
      (segment ℝ (T₀.rescaleMap R T.x) (T₀.rescaleMap R T.y)))
  have hlen1 : dist (T₀.rescaleMap R T.x) (T₀.rescaleMap R T.y) ≤ 1 := by
    calc
      dist (T₀.rescaleMap R T.x) (T₀.rescaleMap R T.y)
          = dist (T₀.normalization T.x) (T₀.normalization T.y) / (4 * R) := by
            simpa [τ, C0] using _root_.Tube.dist_rescaleMap T₀ hR T.x T.y
      _ ≤ R / (4 * R) := div_le_div_of_nonneg_right hlen (le_of_lt h4Rpos)
      _ = 1 / 4 := hRdiv
      _ ≤ 1 := by norm_num
  have hth2 : T₀.rescaleMap R '' T.carrier ⊆ (_root_.Tube.centredExtension σ hxy).carrier := by
    exact hth1.trans (_root_.Tube.cthickening_subset_centredExtension hxy hlen1)
  -- (2) Position: `V ⊆ B̄(0,1)`.
  have hpx : dist (T₀.normalization T.x) T₀.x ≤ R := by
    have hmem : T₀.normalization T.x ∈ T₀.normalization '' T.carrier :=
      ⟨T.x, _root_.Tube.x_mem_carrier T, rfl⟩
    exact Metric.mem_closedBall.mp (hball hmem)
  have hpy : dist (T₀.normalization T.y) T₀.x ≤ R := by
    have hmem : T₀.normalization T.y ∈ T₀.normalization '' T.carrier :=
      ⟨T.y, _root_.Tube.y_mem_carrier T, rfl⟩
    exact Metric.mem_closedBall.mp (hball hmem)
  have hpx0 : dist (T₀.rescaleMap R T.x) (0 : E) ≤ 1 / 4 := by
    calc
      dist (T₀.rescaleMap R T.x) (0 : E)
          = dist (T₀.rescaleMap R T.x) (T₀.rescaleMap R T₀.x) := by
            rw [← _root_.Tube.rescaleMap_apply_x]
      _ = dist (T₀.normalization T.x) (T₀.normalization T₀.x) / (4 * R) :=
            _root_.Tube.dist_rescaleMap T₀ hR T.x T₀.x
      _ = dist (T₀.normalization T.x) T₀.x / (4 * R) := by rw [_root_.Tube.normalization_apply_x]
      _ ≤ R / (4 * R) := div_le_div_of_nonneg_right hpx (le_of_lt h4Rpos)
      _ = 1 / 4 := hRdiv
  have hpy0 : dist (T₀.rescaleMap R T.y) (0 : E) ≤ 1 / 4 := by
    calc
      dist (T₀.rescaleMap R T.y) (0 : E)
          = dist (T₀.rescaleMap R T.y) (T₀.rescaleMap R T₀.x) := by
            rw [← _root_.Tube.rescaleMap_apply_x]
      _ = dist (T₀.normalization T.y) (T₀.normalization T₀.x) / (4 * R) :=
            _root_.Tube.dist_rescaleMap T₀ hR T.y T₀.x
      _ = dist (T₀.normalization T.y) T₀.x / (4 * R) := by rw [_root_.Tube.normalization_apply_x]
      _ ≤ R / (4 * R) := div_le_div_of_nonneg_right hpy (le_of_lt h4Rpos)
      _ = 1 / 4 := hRdiv
  have hpos : (_root_.Tube.centredExtension σ hxy).carrier ⊆ Metric.closedBall (0 : E) 1 := by
    exact _root_.Tube.centredExtension_subset_closedBall hxy hpx0 hpy0 hsit.out_le_quarter
  -- (3) Volume: `|V| ≤ (4R)^6 |W|`.
  have hvol0 : volume (_root_.Tube.centredExtension σ hxy).carrier
      ≤ ENNReal.ofReal
            ((_root_.Tube.volume_le.C 3 : ℝ) / (_root_.Tube.le_volume.c 3 : ℝ) * (4 * R) ^ 3)
          * volume (T₀.rescaleMap R '' T.carrier) := by
    simpa [hn] using _root_.Tube.volume_centredExtension_le_mul_volume_rescale_image
      (n := 3) hsit hR T₀ T hxy
  have hC64R : (64 : ℝ) ≤ R := by
    have hC : (64 : ℝ) ≤ (_root_.Tube.normalization.C 3 : ℝ) := by
      norm_num [_root_.Tube.normalization.C]
    exact le_trans hC hsit.normalizationConst_le_radius
  have hbig : (256 : ℝ) ≤ 4 * R := by linarith
  have hpow256 : (256 : ℝ) ^ 3 ≤ (4 * R) ^ 3 :=
    pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 256) hbig 3
  have h12 : (12 : ℝ) ≤ (4 * R) ^ 3 := by nlinarith
  have hcoef : (_root_.Tube.volume_le.C 3 : ℝ) / (_root_.Tube.le_volume.c 3 : ℝ) * (4 * R) ^ 3
      ≤ (4 * R) ^ 6 := by
    have hvp12 : (_root_.Tube.volume_le.C 3 : ℝ) / (_root_.Tube.le_volume.c 3 : ℝ) ≤ 12 :=
      _root_.Tube.volume_ratio_three_le_twelve
    calc
      (_root_.Tube.volume_le.C 3 : ℝ) / (_root_.Tube.le_volume.c 3 : ℝ) * (4 * R) ^ 3
          ≤ 12 * (4 * R) ^ 3 := by gcongr
      _ ≤ (4 * R) ^ 3 * (4 * R) ^ 3 := by gcongr
      _ = (4 * R) ^ 6 := by ring
  have hvol : volume (_root_.Tube.centredExtension σ hxy).carrier
      ≤ ENNReal.ofReal ((4 * R) ^ 6) * volume (T₀.rescaleMap R '' T.carrier) := by
    exact hvol0.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hcoef) le_rfl)
  exact ⟨hth2, hpos, hvol⟩

/-- **The selection constant of the downstairs route is dominated by the normalization loss, at a
free normalized radius `R` and a free tilt `κ`.**

`Kakeya.ml1Boot.fineNormalize_C_dominates` is the same statement hardwired to the undilated
instance `(R, κ) = (C_N, 2)`, and the dilated half of the normalization runs at
`(R, κ) = ((1 + 2 c) C_N, max 2 (2 c))`, so it needs the parametric form.  The coupling
hypothesis `κ + 2 ≤ R` holds at both instances — `4 ≤ 64` and `2 c + 4 ≤ 64 + 128 c` — and is
what keeps the selection ratio `4 (κ + 2) R C_n` below `4 R² C_n`.

The third clause carries a factor `125` that the undilated form does not.  It is the price of
descending the ambient volume comparison from `c · T_τ` to the sub-body `K`: the `c`-dilate has
volume `c³ |T_τ|`, and `c ≥ 1/5` — forced, not assumed, since a `δ`-tube fits inside `c · T_τ`
only if `1 ≤ c + 4 c τ` (`Kakeya.ml1Boot.volume_ambient_le_mul_volume_dilate`) — bounds `c⁻³` by
`125`.  There is room for it: the comparison reduces to `125 ≤ 4 ^ 24 R ^ 12`. -/
private lemma fineNormalize_C_dominates_gen {R κ c₁ : ℝ≥0}
    (hCR : _root_.Tube.normalization.C 3 ≤ R) (hκR : κ + 2 ≤ R)
    (hc₁ : c₁ = _root_.Tube.essDistinctTubesInSelfDilate.C 3
      (4 * ((κ : ℝ) + 2) * (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3)) :
    c₁ ≤ fineNormalize.C R κ ∧
      ((4 * R) ^ 6 : ℝ≥0) * c₁ ≤ fineNormalize.C R κ ∧
      (125 : ℝ≥0) * ((4 * R) ^ 12 : ℝ≥0) * c₁ ≤ fineNormalize.C R κ := by
  let ratio : ℝ := 4 * ((κ : ℝ) + 2) * (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3
  let D : ℝ≥0 := (Kakeya.Tube.tubeOverlapCoreClose.C 3).toNNReal
  let u : ℝ≥0 := 4 * (κ + 2) * R * D
  have hR1 : (1 : ℝ≥0) ≤ R := le_trans (_root_.Tube.normalization.one_le_C 3) hCR
  have hκ1 : (1 : ℝ≥0) ≤ κ + 2 := by
    exact le_trans (by norm_num : (1 : ℝ≥0) ≤ 2)
      (le_add_of_nonneg_left (by positivity : (0 : ℝ≥0) ≤ κ))
  have hD0 : (0 : ℝ) ≤ Kakeya.Tube.tubeOverlapCoreClose.C 3 :=
    le_of_lt (lt_trans (by norm_num : (0 : ℝ) < (1 : ℝ))
      (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C 3))
  have hD1 : (1 : ℝ≥0) ≤ D := by
    dsimp [D]; rw [← NNReal.coe_le_coe, Real.toNNReal_of_nonneg hD0]
    exact le_of_lt (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C 3)
  have hratio0 : (0 : ℝ) ≤ ratio := by
    dsimp [ratio]
    positivity
  have hu_re : ratio = (u : ℝ) := by
    dsimp [u, ratio, D]
    norm_num
    exact Or.inl hD0
  have hu : ratio.toNNReal = u := by
    apply NNReal.coe_injective
    rw [Real.toNNReal_of_nonneg hratio0]
    exact hu_re
  have hu1 : (1 : ℝ≥0) ≤ u :=
    one_le_mul (one_le_mul (one_le_mul (by norm_num : (1 : ℝ≥0) ≤ 4) hκ1) hR1) hD1
  have hu6 : u ^ 6 ≤ u ^ 12 := pow_le_pow_right₀ hu1 (by norm_num)
  have hule : u ≤ 4 * R ^ 2 * D := by
    dsimp [u]
    calc
      4 * (κ + 2) * R * D
          ≤ 4 * R * R * D := by
            exact mul_le_mul
              (mul_le_mul (mul_le_mul le_rfl hκR (by positivity) (by positivity))
                le_rfl (by positivity) (by positivity))
              le_rfl (by positivity) (by positivity)
      _ = 4 * R ^ 2 * D := by ring
  have hu12' : 125 * u ^ 12 ≤ ((4 * R) ^ 6) ^ 6 * D ^ 12 := by
    calc
      125 * u ^ 12 ≤ 125 * (4 * R ^ 2 * D) ^ 12 := by
            exact mul_le_mul le_rfl (pow_le_pow_left₀ (by positivity : (0 : ℝ≥0) ≤ u) hule 12)
              (by positivity) (by positivity)
      _ = 125 * 4 ^ 12 * R ^ 24 * D ^ 12 := by
            ring_nf
      _ ≤ (4 : ℝ≥0) ^ 36 * R ^ 36 * D ^ 12 := by
            exact mul_le_mul
              (mul_le_mul (by norm_num : (125 * 4 ^ 12 : ℝ≥0) ≤ 4 ^ 36)
                (pow_le_pow_right₀ hR1 (by norm_num)) (by positivity) (by positivity))
              le_rfl (by positivity) (by positivity)
      _ = ((4 * R) ^ 6) ^ 6 * D ^ 12 := by
            ring_nf
  have hu12 : u ^ 12 ≤ ((4 * R) ^ 6) ^ 6 * D ^ 12 := by
    exact le_trans
      (le_mul_of_one_le_left (by positivity) (by norm_num : (1 : ℝ≥0) ≤ 125))
      hu12'
  have hbase : (1 : ℝ≥0) ≤ 4 * R := one_le_mul (by norm_num : (1 : ℝ≥0) ≤ 4) hR1
  have hpw6 : (4 * R) ^ 6 ≤ (4 * R) ^ 12 := pow_le_pow_right₀ hbase (by norm_num)
  have hkey : c₁ ≤ _root_.Tube.comparableReplacement.C 3 ((4 * R) ^ 6) := by
    rw [hc₁]
    unfold _root_.Tube.essDistinctTubesInSelfDilate.C
      _root_.Tube.essDistinctTubesInSelfDilate.thinC
      _root_.Tube.essDistinctTubesInSelfDilate.fatC
      _root_.Tube.comparableReplacement.C _root_.Tube.comparableReplacement.Kstar
    set A : ℝ≥0 :=
      24 * (2 ^ (3 - 1) * Metric.coveringNumber_mul_pow_le_volume_cthickening.C (3 - 1)) ^ 2
        * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C (2 * 3 - 1))⁻¹
        * (32 * (3 : ℝ≥0)) ^ (2 * 3 - 1) with hA
    set B : ℝ≥0 := 6 ^ (2 * 3) * (Tube.card_le_of_EssDistinct.C 3).toNNReal with hB
    calc
      A * ratio.toNNReal ^ (2 * 3) + B * ratio.toNNReal ^ (4 * 3)
          = A * u ^ 6 + B * u ^ 12 := by rw [hu]
      _ ≤ A * u ^ 12 + B * u ^ 12 := by
            exact add_le_add (mul_le_mul le_rfl hu6 (by positivity) (by positivity)) le_rfl
      _ = (A + B) * u ^ 12 := by ring
      _ ≤ (A + B) * (((4 * R) ^ 6) ^ 6 * D ^ 12) := by
            exact mul_le_mul le_rfl hu12 (by positivity) (by positivity)
      _ ≤ 1 + (A + B) * (((4 * R) ^ 6) ^ 6 * D ^ 12) := le_add_self
      _ = _root_.Tube.comparableReplacement.C 3 ((4 * R) ^ 6) := by
            rw [hA, hB]
            unfold _root_.Tube.comparableReplacement.C _root_.Tube.comparableReplacement.Kstar
            norm_num
            ring
  have hkey125 : 125 * c₁ ≤ _root_.Tube.comparableReplacement.C 3 ((4 * R) ^ 6) := by
    rw [hc₁]
    unfold _root_.Tube.essDistinctTubesInSelfDilate.C
      _root_.Tube.essDistinctTubesInSelfDilate.thinC
      _root_.Tube.essDistinctTubesInSelfDilate.fatC
      _root_.Tube.comparableReplacement.C _root_.Tube.comparableReplacement.Kstar
    set A : ℝ≥0 :=
      24 * (2 ^ (3 - 1) * Metric.coveringNumber_mul_pow_le_volume_cthickening.C (3 - 1)) ^ 2
        * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C (2 * 3 - 1))⁻¹
        * (32 * (3 : ℝ≥0)) ^ (2 * 3 - 1) with hA
    set B : ℝ≥0 := 6 ^ (2 * 3) * (Tube.card_le_of_EssDistinct.C 3).toNNReal with hB
    calc
      125 * (A * ratio.toNNReal ^ (2 * 3) + B * ratio.toNNReal ^ (4 * 3))
          = 125 * (A * u ^ 6 + B * u ^ 12) := by rw [hu]
      _ = 125 * (A * u ^ 6) + 125 * (B * u ^ 12) := by ring
      _ ≤ 125 * (A * u ^ 12) + 125 * (B * u ^ 12) := by
            exact add_le_add
              (mul_le_mul le_rfl (mul_le_mul le_rfl hu6 (by positivity) (by positivity))
                (by positivity) (by positivity))
              le_rfl
      _ = 125 * (A + B) * u ^ 12 := by ring
      _ = (A + B) * (125 * u ^ 12) := by ring
      _ ≤ (A + B) * (((4 * R) ^ 6) ^ 6 * D ^ 12) := by
            exact mul_le_mul le_rfl hu12' (by positivity) (by positivity)
      _ ≤ 1 + (A + B) * (((4 * R) ^ 6) ^ 6 * D ^ 12) := le_add_self
      _ = _root_.Tube.comparableReplacement.C 3 ((4 * R) ^ 6) := by
            rw [hA, hB]
            unfold _root_.Tube.comparableReplacement.C _root_.Tube.comparableReplacement.Kstar
            norm_num
            ring
  constructor
  · unfold fineNormalize.C
    rw [hc₁]
    exact le_add_self
  constructor
  · unfold fineNormalize.C
    exact le_trans
      (le_trans (mul_le_mul hpw6 le_rfl (by positivity) (by positivity))
        (mul_le_mul le_rfl hkey (by positivity) (by positivity)))
      le_self_add
  · unfold fineNormalize.C
    calc
      (125 : ℝ≥0) * ((4 * R) ^ 12 : ℝ≥0) * c₁
          = (4 * R) ^ 12 * (125 * c₁) := by ring
      _ ≤ (4 * R) ^ 12 * _root_.Tube.comparableReplacement.C 3 ((4 * R) ^ 6) := by
            exact mul_le_mul le_rfl hkey125 (by positivity) (by positivity)
      _ ≤ (4 * R) ^ 12 * _root_.Tube.comparableReplacement.C 3 ((4 * R) ^ 6)
            + _root_.Tube.essDistinctTubesInSelfDilate.C 3
                (4 * ((κ : ℝ) + 2) * (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3) :=
            le_self_add

/-- **Normalizing a fine fibre to the unit ball, over an arbitrary ambient body**.

This is the route shared by the two halves of the fine normalization, with the ambient body `P`
and the normalized ambient radius `R` left free.  Both halves are this lemma instantiated:
`Kakeya.ml1Boot.exists_fineNormalization` at `(P, R, κ) = (T_τ, C_N, 2)`, and
`Kakeya.ml1Boot.exists_fineNormalization_dilate` at
`(P, R, κ) = (K, (1 + 2 c) C_N, max 2 (2 c))` — see the "Not a corollary of the undilated half"
note at the latter for why neither is derivable from the other.

Everything the route needs from the ambient body is isolated into four hypotheses, and nothing
else here mentions `P`:

* `hsub`, the members sit in `P`;
* `hball`, the normalization `Φ_{T_τ}` carries `P` into `B̄(T_τ.x, R)` — this is what fixes `R`,
  and it is the *only* place the shape of `P` enters the geometry;
* `hlen`, each image core has length at most `R` — the relaxed form of
  `Tube.IsNormalizationDistortion.dist_le_C` discussed at
  `Kakeya.ml1Boot.rescale_outer_tube_of_dist_le`;
* `hperp`, each member is tilted against the axis of `T_τ` by at most `κ τ`.

The remaining two, `hPvol` and `hratio`, are the ambient enlargement to `B₁`: `Cw` is the loss
of replacing the ambient body by the unit ball, and it is the *only* route by which a
volume-ratio parameter such as the `M` of the dilated half can reach the Frostman clause.  The
constants are returned raw — the selection constant `C₁`, the comparability constant `(4 R) ^ 6`
and `Cw`, in the combinations the four clauses actually pay — so that each instance does its own
domination against `Kakeya.ml1Boot.fineNormalize.C R κ`.

The output scale is `Kakeya.ml1Boot.fineScale δ τ` and not the bare ratio `δ / τ`; with `δ / τ`
this statement is false at both instances, refuted by
`Kakeya.ml1Boot.not_exists_fineNormalization` and
`Kakeya.ml1Boot.not_exists_fineNormalization_dilate`.

## The construction-visibility clauses

The last four clauses of the conclusion are not part of the blueprint lemma.  They expose the
data the route already builds, so that a consumer can see *which* family `V` is rather than only
that one exists.  Writing `Ψ = Tube.rescaleMap T_τ R` for the normalization-and-homothety of the
proof, they say that the intermediate family — the `Ψ`-image of the input — sits inside the
output with the same shade and comparable volume, and that `Ψ` carries the ambient body into
`B(0, 1/4)`:

* `Ψ(T i) ⊆ V i` for every `i ∈ u`;
* `(V i).shade = Ψ((T i).shade)` for every `i ∈ u`;
* `|V i| ≤ (4 R) ^ 6 |Ψ(T i)|` for every `i ∈ u`;
* `Ψ(P) ⊆ B(0, 1/4)`.

They cost nothing: they are the local hypotheses `hsub'`, `hshade`, `hvol` and `hK'c` that the
selection package `Tube.exists_comparableReplacement_affine` is fed with anyway, restated
through `hWcarrier` in terms of `Ψ` rather than of the local abbreviation `𝕎`.

What the proof does **not** have, and so what is deliberately absent here, is the `hdilate`
clause of `ConvexSpaceBody.frostmanConstIn_ge_of_comparable` — for every `K' ≤ K` a `L ≤ K`
with `K' ≤ L`, `|L| ≤ C |K'|` and `V i ≤ L` whenever `Ψ(T i) ≤ K'`.  `Tube.exists_comparableReplacement_affine`
never forms such an `L`; its Frostman item is the one-sided
`Tube.comparableTransport_oneSided`, which needs only `Ψ(T i) ⊆ V i ⊆ K` and the volume
bracket.  Also absent is any clause about indices outside `u`: `hsub`, `hlen` and `hperp` are
hypothesised on `u` alone, so nothing at all is known about `V i` for `i ∉ u`, even though `V`
is a total function. -/
theorem exists_fineNormalization_core [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {δ τ : ℝ≥0} (hδ : 0 < δ) (hδτ : δ ≤ τ) (hτ1 : τ ≤ 1)
    {Λ : ℝ≥0} (hΛ : 1 ≤ Λ) {μ₀ : ℝ≥0∞} (hμ₀ : 0 < μ₀)
    {ι : Type*} {u : Finset ι} (Tτ : Tube τ E) (T : ι → ShadedTube δ E)
    (P : ConvexSpaceBody E) {R κ Cw : ℝ≥0}
    (hR : _root_.Tube.normalization.C 3 ≤ R)
    (hu : u.Nonempty)
    (hsub : ∀ i ∈ u, (T i).carrier ⊆ P.carrier)
    (hball : Tτ.normalization '' P.carrier ⊆ Metric.closedBall Tτ.x (R : ℝ))
    (hlen : ∀ i ∈ u,
      dist (Tτ.normalization (T i).x) (Tτ.normalization (T i).y) ≤ (R : ℝ))
    (hperp : ∀ i ∈ u, ‖(T i).toTube.direction
        - (inner ℝ Tτ.direction (T i).toTube.direction : ℝ) • Tτ.direction‖
      ≤ (κ : ℝ) * (τ : ℝ))
    (hPvol : volume P.carrier ≠ 0)
    (hratio : volume (Metric.closedBall (0 : E) 1)
      ≤ (Cw : ℝ≥0∞) * volume (Tτ.rescaleMap (R : ℝ) '' P.carrier))
    (hED : (u : Set ι).Pairwise fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier)
    (hdens : ∀ i ∈ u, (Λ : ℝ≥0∞)⁻¹ * μ₀ * volume (T i).carrier ≤ volume (T i).shade ∧
      volume (T i).shade ≤ (Λ : ℝ≥0∞) * μ₀ * volume (T i).carrier) :
    ∃ u' ⊆ u, u'.Nonempty ∧ ∃ V : ι → ShadedTube (fineScale δ τ) E,
      (u' : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier) ∧
        (∀ i ∈ u', (V i).carrier ⊆ Metric.closedBall 0 1) ∧
        ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
          ≤ (_root_.Tube.essDistinctTubesInSelfDilate.C 3
              (4 * ((κ : ℝ) + 2) * (R : ℝ)
                * Kakeya.Tube.tubeOverlapCoreClose.C 3) : ℝ≥0∞)
            * (Λ : ℝ≥0∞) ^ 2
            * ShadedBody.multiplicity u' (fun i => (V i).toShadedBody) ∧
        (ShadedBody.fullness u (fun i => (T i).toShadedBody) : ℝ≥0∞)
          ≤ (((4 * R) ^ 6 : ℝ≥0) : ℝ≥0∞)
            * (_root_.Tube.essDistinctTubesInSelfDilate.C 3
                (4 * ((κ : ℝ) + 2) * (R : ℝ)
                  * Kakeya.Tube.tubeOverlapCoreClose.C 3) : ℝ≥0∞)
            * (Λ : ℝ≥0∞) ^ 2
            * (ShadedBody.fullness u' (fun i => (V i).toShadedBody) : ℝ≥0∞) ∧
        frostmanConstIn u' (fun i => (V i).toConvexSpaceBody)
            ConvexSpaceBody.closedUnitBall
          ≤ (_root_.Tube.essDistinctTubesInSelfDilate.C 3
                (4 * ((κ : ℝ) + 2) * (R : ℝ)
                  * Kakeya.Tube.tubeOverlapCoreClose.C 3) : ℝ≥0∞)
            * (((4 * R) ^ 6 : ℝ≥0) : ℝ≥0∞) * (Cw : ℝ≥0∞)
            * frostmanConstIn u (fun i => (T i).toConvexSpaceBody) P ∧
        -- the construction-visibility clauses: `V` is comparable to the image of `T` under the
        -- explicit rescaling map `Ψ = Tube.rescaleMap Tτ R`
        (∀ i ∈ u, Tτ.rescaleMap (R : ℝ) '' (T i).carrier ⊆ (V i).carrier) ∧
        (∀ i ∈ u, (V i).shade = Tτ.rescaleMap (R : ℝ) '' (T i).shade) ∧
        (∀ i ∈ u, volume (V i).carrier
          ≤ (((4 * R) ^ 6 : ℝ≥0) : ℝ≥0∞)
            * volume (Tτ.rescaleMap (R : ℝ) '' (T i).carrier)) ∧
        Tτ.rescaleMap (R : ℝ) '' P.carrier ⊆ Metric.closedBall (0 : E) (1 / 4) := by
  classical
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (by rw [hdim]; norm_num)
  have hτ0 : 0 < τ := lt_of_lt_of_le hδ hδτ
  let i₀ : ι := Classical.choose hu
  have hi₀ : i₀ ∈ u := Classical.choose_spec hu
  have hδτ0 : 0 < (δ / τ : ℝ≥0) := by
    rw [← NNReal.coe_lt_coe]
    rw [NNReal.coe_div]
    exact div_pos (by exact_mod_cast hδ) (by exact_mod_cast hτ0)
  have hpos : 0 < fineScale δ τ := by
    dsimp [fineScale]
    exact lt_min hδτ0 (by norm_num)
  have hquarter : (fineScale δ τ : ℝ) ≤ 1 / 4 := by
    exact_mod_cast (fineScale_bounds hδτ hτ0).2.1
  have hratioσ : (fineScale δ τ : ℝ) ≤ (δ : ℝ) / (τ : ℝ) := by
    exact_mod_cast (fineScale_bounds hδτ hτ0).1
  have hρσ : (δ : ℝ) / (τ : ℝ) ≤ 4 * (fineScale δ τ : ℝ) := by
    exact_mod_cast (fineScale_bounds hδτ hτ0).2.2
  have hR1n : (1 : ℝ≥0) ≤ R := le_trans (_root_.Tube.normalization.one_le_C 3) hR
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR1n
  have hR0 : 0 < (R : ℝ) := lt_of_lt_of_le zero_lt_one hR1
  have hsit : _root_.Tube.IsRescalingSituation τ δ (fineScale δ τ) (R : ℝ) 3 :=
    ⟨hτ0, hδτ, hτ1, hpos, hquarter, hratioσ, by exact_mod_cast hR⟩
  obtain ⟨L, hL⟩ := _root_.Tube.exists_rescaleEquiv hτ0 hR0 Tτ
  have hcont : Continuous L := AffineEquiv.continuous_of_finiteDimensional L
  have hemb : MeasurableEmbedding L :=
    (AffineEquiv.toContinuousAffineEquiv L).toHomeomorph.measurableEmbedding
  have hxy : ∀ i : ι, Tτ.rescaleMap (R : ℝ) (T i).x ≠ Tτ.rescaleMap (R : ℝ) (T i).y := by
    intro i h
    rw [← hL] at h
    exact (fun hne => hne (L.injective h)) (fun hxy => by
      have := (T i).toTube.dist_eq_one
      rw [hxy] at this
      simp at this)
  set 𝕎 : ι → ShadedBody E := fun i => ((T i).toShadedBody).affineImage L.toAffineMap hcont hemb
  set 𝕍 : ι → ShadedTube (fineScale δ τ) E := fun i =>
    { toTube := _root_.Tube.centredExtension (fineScale δ τ) (hxy i)
      shade := (𝕎 i).shade ∩ (_root_.Tube.centredExtension (fineScale δ τ) (hxy i)).carrier
      measurableSet_shade :=
        (𝕎 i).measurableSet_shade.inter
          (_root_.Tube.centredExtension (fineScale δ τ) (hxy i)).isCompact.measurableSet
      shade_subset := Set.inter_subset_right }
  have hballi : ∀ i ∈ u, Tτ.normalization '' (T i).carrier ⊆ Metric.closedBall Tτ.x (R : ℝ) := by
    intro i hi
    exact (Set.image_mono (hsub i hi)).trans hball
  have houter := fun i hi => rescale_outer_tube_of_dist_le
    (hsit := hsit) (hn := hdim) (hR := hR0) (hρσ := hρσ) (T₀ := Tτ)
    (T := (T i).toTube)
    (hcth := _root_.Tube.normalization_image_subset_cthickening hτ0 hτ1 Tτ (T i).toTube)
    (hlen := hlen i hi) (hball := hballi i hi) (hxy := hxy i)
  have hofR : ENNReal.ofReal ((4 * (R : ℝ)) ^ 6) = (((4 * R) ^ 6 : ℝ≥0) : ℝ≥0∞) := by
    have h4R : ENNReal.ofReal (4 * (R : ℝ)) = ((4 * R : ℝ≥0) : ℝ≥0∞) := by
      rw [show (4 : ℝ) * (R : ℝ) = ((4 * R : ℝ≥0) : ℝ) by
        rw [NNReal.coe_mul]
        norm_num]
      rw [ENNReal.ofReal_coe_nnreal]
    have hRnonneg : (0 : ℝ) ≤ 4 * (R : ℝ) := by positivity
    calc
      ENNReal.ofReal ((4 * (R : ℝ)) ^ 6) = (ENNReal.ofReal (4 * (R : ℝ))) ^ 6 := by
            rw [ENNReal.ofReal_pow hRnonneg]
      _ = ((4 * R : ℝ≥0) : ℝ≥0∞) ^ 6 := by rw [h4R]
      _ = (((4 * R) ^ 6 : ℝ≥0) : ℝ≥0∞) := by
            rw [ENNReal.coe_pow]
  have hWcarrier : ∀ i ∈ u, (𝕎 i).carrier = Tτ.rescaleMap (R : ℝ) '' (T i).carrier := by
    intro i hi
    dsimp [𝕎]
    change L.toAffineMap '' (T i).carrier = Tτ.rescaleMap (R : ℝ) '' (T i).carrier
    rw [← hL]
  have hsub' : ∀ i ∈ u, (𝕎 i).carrier ⊆ (𝕍 i).carrier := by
    intro i hi
    rw [hWcarrier i hi]
    simpa [𝕍] using (houter i hi).1
  have h𝕍ball : ∀ i ∈ u, (𝕍 i).toTube.carrier ⊆ Metric.closedBall (0 : E) 1 := by
    intro i hi
    simpa [𝕍] using (houter i hi).2.1
  have hshade : ∀ i ∈ u, (𝕍 i).shade = (𝕎 i).shade := by
    intro i hi
    dsimp [𝕍]
    exact (Set.inter_eq_left).mpr ((𝕎 i).shade_subset.trans (hsub' i hi))
  have hCv : 1 ≤ (4 * R) ^ 6 := by
    exact one_le_pow₀ (one_le_mul (by norm_num) hR1n)
  have hVK : ∀ i ∈ u,
      (𝕍 i).toConvexSpaceBody ≤ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) := by
    intro i hi
    change (𝕍 i).carrier ⊆ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier
    rw [ConvexSpaceBody.closedUnitBall_carrier]
    simpa [𝕍] using h𝕍ball i hi
  let c' : ℝ := 4 * ((κ : ℝ) + 2) * (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3
  have hc'1 : (1 : ℝ) ≤ c' := by
    dsimp [c']
    have hκ0 : (0 : ℝ) ≤ (κ : ℝ) := NNReal.coe_nonneg κ
    have hRgr : (1 : ℝ) ≤ (R : ℝ) := hR1
    have hCnR : (1 : ℝ) ≤ (Kakeya.Tube.tubeOverlapCoreClose.C 3 : ℝ) := by
      exact_mod_cast (le_of_lt (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C 3))
    have hk : (1 : ℝ) ≤ 4 * ((κ : ℝ) + 2) := by
      nlinarith
    have hk0 : (0 : ℝ) ≤ 4 * ((κ : ℝ) + 2) := le_trans zero_le_one hk
    have hb1 : (1 : ℝ) ≤ (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3 := by
      calc
        1 = 1 * 1 := by norm_num
        _ ≤ (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3 := by
              exact mul_le_mul hRgr hCnR (by norm_num) (by positivity)
    have hb10 : (0 : ℝ) ≤ (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3 := le_trans zero_le_one hb1
    calc
      1 ≤ 1 * 1 := by norm_num
      _ ≤ (4 * ((κ : ℝ) + 2)) * ((R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3) := by
            exact mul_le_mul hk hb1 (by positivity) hk0
      _ = 4 * ((κ : ℝ) + 2) * (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3 := by ring
  let c₁ : ℝ≥0 := _root_.Tube.essDistinctTubesInSelfDilate.C 3
    (4 * ((κ : ℝ) + 2) * (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3)
  have hc₁ : c₁ = _root_.Tube.essDistinctTubesInSelfDilate.C 3
      (4 * ((κ : ℝ) + 2) * (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3) := by
    rfl
  have hC₁ : (1 : ℝ≥0) ≤ c₁ := by
    let 𝕋 : ι → Tube δ E := fun i => (T i).toTube
    have hpw₀ : (({i₀} : Finset ι) : Set ι).Pairwise
        (fun i j => IsEssentiallyDistinct (𝕋 i).carrier (𝕋 j).carrier) := by
      simp
    have hsub₀ : ∀ j ∈ ({i₀} : Finset ι), (𝕋 j).carrier
        ⊆ (Kakeya.Tube.dilate (𝕋 i₀) c').carrier := by
      intro j hj
      have hji : j = i₀ := by simpa using hj
      subst j
      exact _root_.Tube.subset_dilate (𝕋 i₀) hc'1
    have hcount : (({i₀} : Finset ι).card : ℝ≥0∞)
        ≤ (_root_.Tube.essDistinctTubesInSelfDilate.C (Module.finrank ℝ E) c' : ℝ≥0∞) :=
      _root_.Tube.essDistinctTubesInSelfDilate hc'1 hδ (le_trans hδτ hτ1 : δ ≤ 1) (𝕋 i₀)
        ({i₀} : Finset ι) 𝕋 hpw₀ hsub₀
    exact ENNReal.coe_le_coe.mp (by simpa [c₁, c', hdim] using hcount)
  have hVtube : ∀ i ∈ u, (𝕍 i).toTube = _root_.Tube.centredExtension (fineScale δ τ) (hxy i) := by
    intro i hi
    rfl
  have hvol : ∀ i ∈ u, volume (𝕍 i).carrier
      ≤ (((4 * R) ^ 6 : ℝ≥0) : ℝ≥0∞) * volume (𝕎 i).carrier := by
    intro i hi
    calc
      volume (𝕍 i).carrier
          = volume (_root_.Tube.centredExtension (fineScale δ τ) (hxy i)).carrier := by
            simp [𝕍]
      _ ≤ ENNReal.ofReal ((4 * (R : ℝ)) ^ 6) * volume (Tτ.rescaleMap (R : ℝ) '' (T i).carrier) :=
            (houter i hi).2.2
      _ = (((4 * R) ^ 6 : ℝ≥0) : ℝ≥0∞) * volume (Tτ.rescaleMap (R : ℝ) '' (T i).carrier) := by
            rw [hofR]
      _ = (((4 * R) ^ 6 : ℝ≥0) : ℝ≥0∞) * volume (𝕎 i).carrier := by
            rw [hWcarrier i hi]
  let W : ℝ≥0∞ := volume (𝕎 i₀).carrier
  have hW : 0 < W := by
    dsimp [W]
    simpa [𝕎] using volume_affineImage_carrier_pos hδ (T i₀) L hcont hemb
  have hcommon : ∀ i ∈ u, volume (𝕎 i).carrier = W := by
    intro i hi
    dsimp [W]
    simpa [𝕎] using volume_affineImage_carrier_eq (T i) (T i₀) L hcont hemb
  have hZ : ∀ i ∈ u, (Λ : ℝ≥0∞)⁻¹ * μ₀ * W ≤ volume (𝕎 i).shade ∧
      volume (𝕎 i).shade ≤ (Λ : ℝ≥0∞) * μ₀ * W := by
    intro i hi
    have hz := affineImage_shade_bounds (S := T i) (S' := T i₀) L hcont hemb
      (hdens i hi).1 (hdens i hi).2
    dsimp [W, 𝕎] at hz ⊢
    exact hz
  let 𝕋 : ι → Tube δ E := fun i => (T i).toTube
  have himg : ∀ i ∈ u, (Tτ.rescaleMap (R : ℝ)) '' (T i).carrier ⊆ ((𝕍 i).toTube).carrier := by
    intro i hi
    simpa [𝕍] using (houter i hi).1
  have hpackage : _root_.Tube.IsComparableReplacementFree u 𝕎 𝕍
      (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) ((4 * R) ^ 6) Λ c₁ := by
    simpa [hc₁, hdim] using
      (_root_.Tube.exists_comparableReplacement_affine (n := 3) (R := (R : ℝ))
      (κ := ((κ : ℝ≥0) : ℝ)) (s := u) hu hsit (by exact NNReal.coe_nonneg κ)
      hδ (le_trans hδτ hτ1 : δ ≤ 1) Tτ
      𝕋 hxy 𝕎 𝕍
      (K := (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E)) (C := (4 * R) ^ 6) (Λ := Λ)
      (W := W) (μ₀ := μ₀) hCv hΛ hW hμ₀ hcommon hVtube hperp
      (by simpa [𝕋] using hED) himg hshade hsub' hVK hvol hZ)
  let K' : ConvexSpaceBody E := (P).affineImage L.toAffineMap hcont
  have hK'c : K'.carrier ⊆ Metric.closedBall (0 : E) (1 / 4) := by
    rintro _ ⟨z, hzP, rfl⟩
    have hz : Tτ.normalization z ∈ Metric.closedBall Tτ.x (R : ℝ) := by
      exact (hball ⟨z, hzP, rfl⟩)
    have hdistz : dist (Tτ.normalization z) Tτ.x ≤ (R : ℝ) := Metric.mem_closedBall.mp hz
    have h4Rpos : (0 : ℝ) < 4 * (R : ℝ) := by positivity
    have h4R0 : (4 : ℝ) * (R : ℝ) ≠ 0 := ne_of_gt h4Rpos
    have hRdiv : (R : ℝ) / (4 * (R : ℝ)) = (1 : ℝ) / 4 := by
      field_simp [h4R0, (by norm_num : (4 : ℝ) ≠ 0)]
    rw [hL]
    calc
      dist (Tτ.rescaleMap (R : ℝ) z) (0 : E)
          = dist (Tτ.rescaleMap (R : ℝ) z) (Tτ.rescaleMap (R : ℝ) Tτ.x) := by
            rw [← _root_.Tube.rescaleMap_apply_x]
        _ = dist (Tτ.normalization z) (Tτ.normalization Tτ.x) / (4 * (R : ℝ)) :=
            _root_.Tube.dist_rescaleMap Tτ hR0 z Tτ.x
        _ = dist (Tτ.normalization z) Tτ.x / (4 * (R : ℝ)) := by
            rw [_root_.Tube.normalization_apply_x]
        _ ≤ (R : ℝ) / (4 * (R : ℝ)) := div_le_div_of_nonneg_right hdistz (le_of_lt h4Rpos)
        _ = (1 : ℝ) / 4 := hRdiv
        _ ≤ 1 / 4 := le_rfl
  have hK' : (K' : ConvexSpaceBody E) ≤ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) := by
    change K'.carrier ⊆ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier
    rw [ConvexSpaceBody.closedUnitBall_carrier]
    exact hK'c.trans (Metric.closedBall_subset_closedBall (by norm_num))
  have hK'vol : volume K'.carrier ≠ 0 := by
    have h1 : volume ((P).affineImage L.toAffineMap hcont).carrier ≠ 0 := by
      rw [ConvexSpaceBody.volume_affineImage]
      have hA : ENNReal.ofReal |LinearMap.det (L.linear : E →ₗ[ℝ] E)| ≠ 0 := by
        exact (ENNReal.ofReal_eq_zero.not).mpr
          (not_le.mpr (abs_pos.mpr (LinearEquiv.isUnit_det' L.linear).ne_zero))
      have hB : volume P.carrier ≠ 0 := hPvol
      exact mul_ne_zero hA hB
    simpa [K'] using h1
  have hWK' : ∀ i ∈ u, (𝕎 i).toConvexSpaceBody ≤ K' := by
    intro i hi
    change (𝕎 i).carrier ⊆ K'.carrier
    rw [hWcarrier i hi]
    rw [← hL]
    exact Set.image_mono (hsub i hi)
  have hratio' : volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier
      ≤ (Cw : ℝ≥0∞) * volume K'.carrier := by
    simpa [K', ← hL, ConvexSpaceBody.closedUnitBall_carrier] using hratio
  have hfrodsman : frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody)
      (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E)
      ≤ (Cw : ℝ≥0∞) * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K' :=
    frostmanConstIn_closedUnitBall_le_of_ambient (u := u) (𝕎 := 𝕎) (K' := K')
      (Cv := Cw) hK' hK'vol hWK' hratio'
  have hF_rel : frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K'
      = frostmanConstIn u (fun i => (T i).toConvexSpaceBody) P := by
    have h := ConvexSpaceBody.frostmanConstIn_affineImage u (fun i => (T i).toConvexSpaceBody)
      P L hcont
    dsimp [𝕎, K']
    exact h
  obtain ⟨u', hu'sub, hu'ne, hVD, _hcard, hmult, hfull, hfrost⟩ :=
    of_comparableReplacementFree (u := u) (𝕎 := 𝕎) (𝕍 := 𝕍)
      (K := (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E)) (Cv := (4 * R) ^ 6)
      (Λ := Λ) (C₁ := c₁) hΛ hCv hC₁ hVK hpackage
  refine ⟨u', hu'sub, hu'ne, 𝕍, ?_⟩
  constructor
  · simpa [𝕍] using hVD
  constructor
  · intro i hi
    simpa [𝕍] using h𝕍ball i (hu'sub hi)
  constructor
  · calc
      ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
          = ShadedBody.multiplicity u 𝕎 := by
            simpa [𝕎] using (ShadedBody.multiplicity_affineImage u
              (fun i => (T i).toShadedBody) L hcont hemb).symm
      _ ≤ (c₁ : ℝ≥0∞) * (Λ : ℝ≥0∞) ^ 2
          * ShadedBody.multiplicity u' (fun i => (𝕍 i).toShadedBody) := hmult
  constructor
  · calc
      (ShadedBody.fullness u (fun i => (T i).toShadedBody) : ℝ≥0∞)
          = (ShadedBody.fullness u 𝕎 : ℝ≥0∞) := by
            simpa [𝕎] using (ShadedBody.fullness_affineImage u
              (fun i => (T i).toShadedBody) L hcont hemb).symm
      _ ≤ (((4 * R) ^ 6 : ℝ≥0) : ℝ≥0∞) * (c₁ : ℝ≥0∞) * (Λ : ℝ≥0∞) ^ 2
          * (ShadedBody.fullness u' (fun i => (𝕍 i).toShadedBody) : ℝ≥0∞) := hfull
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · calc
        frostmanConstIn u' (fun i => (𝕍 i).toConvexSpaceBody)
            (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E)
            ≤ (c₁ : ℝ≥0∞) * (((4 * R) ^ 6 : ℝ≥0) : ℝ≥0∞)
              * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody)
                  (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) := by simpa using hfrost
        _ ≤ (c₁ : ℝ≥0∞) * (((4 * R) ^ 6 : ℝ≥0) : ℝ≥0∞)
            * ((Cw : ℝ≥0∞)
              * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K') := by
              exact mul_le_mul_right hfrodsman ((c₁ : ℝ≥0∞) * (((4 * R) ^ 6 : ℝ≥0) : ℝ≥0∞))
        _ = (c₁ : ℝ≥0∞) * (((4 * R) ^ 6 : ℝ≥0) : ℝ≥0∞)
            * ((Cw : ℝ≥0∞)
              * frostmanConstIn u (fun i => (T i).toConvexSpaceBody) P) := by
              rw [hF_rel]
        _ = (c₁ : ℝ≥0∞) * (((4 * R) ^ 6 : ℝ≥0) : ℝ≥0∞) * (Cw : ℝ≥0∞)
            * frostmanConstIn u (fun i => (T i).toConvexSpaceBody) P := by ring
    · intro i hi
      rw [← hWcarrier i hi]
      exact hsub' i hi
    · intro i hi
      rw [hshade i hi]
      simp [𝕎, ← hL]
    · intro i hi
      simpa [hWcarrier i hi] using hvol i hi
    · simpa [K', ← hL] using hK'c

end
end W44NormalizationPort
end ml1Boot
end Kakeya

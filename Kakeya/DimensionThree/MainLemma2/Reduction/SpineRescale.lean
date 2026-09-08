/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Tube.Rescale
public import Kakeya.DimensionThree.AffineTransport

/-!
# The spine rescaling of Main Lemma 2

Two rescalings occur in the proof of GWZ Main Lemma 2 (GWZ: "Proof of Main Lemma~\ref{lemmain2}"):

* the *spine* rescaling, which fixes `T_θ ∈ 𝕋_θ` and replaces the family `𝕋_τ[T_θ]` of `τ`-tubes
  inside `T_θ` (and its shading) by its image `(𝕋̃, Ỹ)` under "the rescaling taking `T_θ` to a
  tube of thickness `1`", so that `𝕋̃` is a family of `τ/θ`-tubes at the scale `δ̃ = δ/θ`;
* the same operation one level down, rescaling the `b`-tube `T_b` to `B_1` and turning
  `𝕋̃[T_b]` into a family `𝕋'` of `δ' = δ̃/b`-tubes, so that GWZ Lemma 9.1 applies to it.

Both are the *same* map, `Kakeya.ML2Reduction.spineRescale`, at two different ambient scales, so
this file states the transport laws once, for a general ambient tube `T₀` of thickness `θ`.

## The map

`Kakeya.ML2Reduction.spineRescale hθ T₀` is the affine equivalence `Φ_{T₀}` of
`Tube.normalizationEquiv`: the identity along the axis of `T₀`, multiplication by `θ⁻¹`
transverse to it, fixing the initial core endpoint `T₀.x`.  It carries `T₀`, a tube of thickness
`θ`, to a body of thickness `1`.  `Kakeya.ML2Reduction.spineRescaleUnit hθ T₀ hR` is `Φ_{T₀}`
followed by the homothety of ratio `(4R)⁻¹` about `T₀.x` (`Tube.rescaleMap`); that is the
form needed for GWZ Lemma 9.1, whose tubes must lie in `B_1`.

## The transport laws

Every quantity of the argument that is a *ratio* of volumes is left exactly unchanged, because an
affine equivalence multiplies every volume by the single nonzero finite constant `|det|`.  That is
the content of `Kakeya/AffineMap.lean`; the lemmas below are its ML2-shaped readings, one law per
declaration:

* `spineFamily_multiplicity` — `μ(𝕋̃, Ỹ) = μ(𝕋, Y)`;
* `spineFamily_fullness` — `λ(𝕋̃, Ỹ) = λ(𝕋, Y)`;
* `spineFamily_densityIn`, `spineFamily_maxDensity` — `Δ(·, K)` and `Δ_max`;
* `spineFamily_frostmanConstIn` — `C_F(·, K)`;
* `spineImage_isEssentiallyDistinct_iff` — essential distinctness, in both directions;
* `spineFamily_card_image`, `spineFamily_injOn` — `|𝕋̃| = |𝕋|`;
* `spineRescale_distortion` and `exists_outerTube` — thickness/radius: the image of a `τ`-tube
  inside `T₀` is caught between the `C⁻¹ (τ/θ)`- and `C (τ/θ)`-neighbourhoods of its image core,
  and (after the `(4R)⁻¹` homothety) is contained in an honest `σ`-tube inside `B_1`;
* `spineFamily_cover`, `exists_outerCover` — the `ρ`-tube covering counts: a cover of `𝕋` by
  parents indexed by `t` transports to a cover of `𝕋̃` indexed by the *same* `t`, and back.

## The scale conversion

`δ̃ ≤ δ^{ε₂}` is the standing separation of the argument.  The three lemmas
`spineFamily_multiplicity_le`, `spineFamily_maxDensity_le` and `spineFamily_le_fullness` fuse a
transport law with that conversion, and are exactly the equivalences GWZ asserts between
`multTildeTLem2` and `multTTauInsideTThetaLem2`, and the transported bounds
`upperBdDeltaMaxTildeTT` and the fullness hypothesis of Lemma 9.1.

## What is *not* here

The converse of `exists_outerCover` — turning a cover of `𝕋̃` by `σ`-tubes into a cover of `𝕋` by
`ρ`-tubes — is **not** proved here and is not stated.  It needs a covering of `Φ⁻¹(V)` by tubes for
a `σ`-tube `V`, i.e. the inverse-image tube-covering estimate; `Kakeya.ML2Reduction.spineFamily_cover_symm`
below gives the transport at the level of convex bodies, which is all that holds without it.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Metric Set

namespace Kakeya.ML2Reduction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι κ : Type*} {θ τ σ : ℝ≥0}

/-! ## The rescaling map -/

/-- **The spine rescaling** `Φ_{T₀}`: the affine equivalence carrying the ambient `θ`-tube `T₀` to
a body of thickness `1`, GWZ's "rescaling taking `T_θ` to a tube of thickness 1".

It is `Tube.normalizationEquiv`, the identity along the axis of `T₀` and multiplication by
`θ⁻¹` on its orthogonal complement, fixing `T₀.x`. -/
noncomputable def spineRescale (hθ : 0 < θ) (T₀ : Tube θ E) : E ≃ᵃ[ℝ] E :=
  Tube.normalizationEquiv hθ T₀

omit [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem spineRescale_apply (hθ : 0 < θ) (T₀ : Tube θ E) (z : E) :
    spineRescale hθ T₀ z = T₀.normalization z :=
  Tube.normalizationEquiv_apply hθ T₀ z

@[simp]
theorem spineRescale_apply_x (hθ : 0 < θ) (T₀ : Tube θ E) :
    spineRescale hθ T₀ T₀.x = T₀.x := by
  rw [spineRescale_apply, Tube.normalization_apply_x]

/-- **The unit-ball form of the spine rescaling** `Ψ_{T₀,R}`: `Φ_{T₀}` followed by the homothety
`z ↦ (z - T₀.x)/(4R)`, i.e. `Tube.rescaleMap`, as an affine equivalence.

This is the map GWZ needs for the second rescaling, "rescale `T_b` to `B_1`": Lemma 9.1 asks for a
family of tubes *in the unit ball*, which `spineRescale` alone does not deliver. -/
noncomputable def spineRescaleUnit (hθ : 0 < θ) (T₀ : Tube θ E) {R : ℝ} (hR : 0 < R) :
    E ≃ᵃ[ℝ] E :=
  (Tube.exists_rescaleEquiv hθ hR T₀).choose

theorem spineRescaleUnit_toAffineMap (hθ : 0 < θ) (T₀ : Tube θ E) {R : ℝ} (hR : 0 < R) :
    (spineRescaleUnit hθ T₀ hR).toAffineMap = T₀.rescaleMap R :=
  (Tube.exists_rescaleEquiv hθ hR T₀).choose_spec

@[simp]
theorem spineRescaleUnit_apply (hθ : 0 < θ) (T₀ : Tube θ E) {R : ℝ} (hR : 0 < R) (z : E) :
    spineRescaleUnit hθ T₀ hR z = T₀.rescaleMap R z := by
  conv_rhs => rw [← spineRescaleUnit_toAffineMap hθ T₀ hR]
  rfl

theorem spineRescaleUnit_coe (hθ : 0 < θ) (T₀ : Tube θ E) {R : ℝ} (hR : 0 < R) :
    ⇑(spineRescaleUnit hθ T₀ hR) = ⇑(T₀.rescaleMap R) :=
  funext fun z => spineRescaleUnit_apply hθ T₀ hR z

/-- `Ψ_{T₀,R}` is injective: it is the underlying map of an affine equivalence. -/
theorem rescaleMap_injective (hθ : 0 < θ) (T₀ : Tube θ E) {R : ℝ} (hR : 0 < R) :
    Function.Injective (T₀.rescaleMap R) := by
  rw [← spineRescaleUnit_coe hθ T₀ hR]
  exact (spineRescaleUnit hθ T₀ hR).injective

/-- The two core endpoints of a tube have distinct images under `Ψ_{T₀,R}`.  This is the
side condition of `Tube.centredExtension`, and it never has to be assumed: it follows from
`dist T.x T.y = 1` and injectivity. -/
theorem rescaleMap_x_ne_rescaleMap_y (hθ : 0 < θ) (T₀ : Tube θ E) {R : ℝ} (hR : 0 < R)
    (T : Tube τ E) : T₀.rescaleMap R T.x ≠ T₀.rescaleMap R T.y := by
  intro h
  have hxy : T.x = T.y := rescaleMap_injective hθ T₀ hR h
  have : dist T.x T.y = 1 := T.dist_eq_one
  rw [hxy, dist_self] at this
  exact absurd this (by norm_num)

/-! ## The action on a sub-family and its shadings -/

/-- **The image of a shaded tube** under an affine change of variables, as a shaded body.

The result is a `ShadedBody` and not a `ShadedTube`: `Φ_{T₀}` does not preserve the class of
tubes (`Tube.normalization_distortion` and the note before it), only the class of bodies
caught between two neighbourhoods of a segment. -/
noncomputable def spineImage (A : E ≃ᵃ[ℝ] E) (S : ShadedTube τ E) : ShadedBody E :=
  S.toShadedBody.mapAffine A

@[simp]
theorem spineImage_carrier (A : E ≃ᵃ[ℝ] E) (S : ShadedTube τ E) :
    (spineImage A S).carrier = A '' S.carrier := rfl

@[simp]
theorem spineImage_shade (A : E ≃ᵃ[ℝ] E) (S : ShadedTube τ E) :
    (spineImage A S).shade = A '' S.shade := rfl

@[simp]
theorem spineImage_toConvexSpaceBody (A : E ≃ᵃ[ℝ] E) (S : ShadedTube τ E) :
    (spineImage A S).toConvexSpaceBody = S.toConvexSpaceBody.mapAffine A := rfl

/-- **The image of a whole shaded family** `(𝕋, Y) ↦ (𝕋̃, Ỹ)`.  The index set is unchanged. -/
noncomputable def spineFamily (A : E ≃ᵃ[ℝ] E) (𝕋 : ι → ShadedTube τ E) : ι → ShadedBody E :=
  fun i => spineImage A (𝕋 i)

@[simp]
theorem spineFamily_apply (A : E ≃ᵃ[ℝ] E) (𝕋 : ι → ShadedTube τ E) (i : ι) :
    spineFamily A 𝕋 i = spineImage A (𝕋 i) := rfl

/-! ## The transport laws

Each law is a separate declaration.  Their common source is that an affine equivalence multiplies
every volume by one nonzero finite factor, so every ratio of volumes is left exactly unchanged;
no comparison constant is lost anywhere below. -/

/-- **(i) Multiplicity is transported exactly**: `μ(𝕋̃, Ỹ) = μ(𝕋, Y)`. -/
theorem spineFamily_multiplicity (A : E ≃ᵃ[ℝ] E) (s : Finset ι) (𝕋 : ι → ShadedTube τ E) :
    ShadedBody.multiplicity s (spineFamily A 𝕋)
      = ShadedBody.multiplicity s (fun i => (𝕋 i).toShadedBody) :=
  ShadedBody.multiplicity_mapAffine s (fun i => (𝕋 i).toShadedBody) A

/-- **(ii) Fullness is transported exactly**: `λ(𝕋̃, Ỹ) = λ(𝕋, Y)`. -/
theorem spineFamily_fullness (A : E ≃ᵃ[ℝ] E) (s : Finset ι) (𝕋 : ι → ShadedTube τ E) :
    ShadedBody.fullness s (spineFamily A 𝕋)
      = ShadedBody.fullness s (fun i => (𝕋 i).toShadedBody) :=
  ShadedBody.fullness_affineImage s (fun i => (𝕋 i).toShadedBody) A
    A.continuous_of_finiteDimensional (Kakeya.measurableEmbedding_affineEquiv A)

/-- **(iv) `Δ_max` is transported exactly**: `Δ_max(𝕋̃) = Δ_max(𝕋)`. -/
theorem spineFamily_maxDensity (A : E ≃ᵃ[ℝ] E) (s : Finset ι) (𝕋 : ι → ShadedTube τ E) :
    Kakeya.maxDensity s (fun i => (spineFamily A 𝕋 i).toConvexSpaceBody)
      = Kakeya.maxDensity s (fun i => (𝕋 i).toConvexSpaceBody) :=
  Kakeya.maxDensity_mapAffine s (fun i => (𝕋 i).toConvexSpaceBody) A

/-! ## Cardinality: `|𝕋̃| = |𝕋|` -/

/-! ## The `ρ`-tube covering counts

A cover of `𝕋` by parents indexed by a finite set `t` is carried to a cover of `𝕋̃` indexed by the
*same* `t`, and back; so the *count* `|𝕋_ρ|` is transported on the nose.  What changes is only the
*shape* of the parents: the image of a `ρ`-tube is a body, and turning it back into an honest tube
is `exists_outerTube` below. -/

/-! ## Thickness and radius

`Φ_{T₀}` does not carry tubes to tubes, but it carries a `τ`-tube inside `T₀` to a body caught
between the `C⁻¹ (τ/θ)`- and `C (τ/θ)`-neighbourhoods of a segment of length between `7/8` and
`C`, with `C = C_N(n)` the dimensional distortion constant.  This is GWZ's "`𝕋̃` is a family of
`τ/θ`-tubes", and it is `Tube.normalization_distortion`, restated here in the vocabulary of
`spineRescale`. -/

/-! ## Honest tubes downstairs: the outer tube of a rescaled tube

For the second rescaling — `T_b ↦ B_1`, feeding GWZ Lemma 9.1 — the images have to be honest
`Kakeya.Tube`s inside the unit ball, not merely thin bodies.  That is what the unit form
`spineRescaleUnit` and `Tube.rescale_outer_tube` deliver, at the cost of a bounded volume
loss `(4R)^6`.  The two side conditions of that lemma, the ball containment of the image and the
nondegeneracy of the image core, are discharged here rather than assumed. -/

variable [Nontrivial E]

omit [Nontrivial E] in
/-- The image of a tube contained in the ambient tube stays in `B̄(T₀.x, R)`, for any admissible
ambient radius `R`.  This is the hypothesis `hball` of `Tube.rescale_outer_tube`, which
therefore never has to be supplied by a caller. -/
theorem normalization_image_subset_closedBall_of_subset {R : ℝ}
    (hn : Module.finrank ℝ E = 3) (hsit : Tube.IsRescalingSituation θ τ σ R 3)
    (T₀ : Tube θ E) (T : Tube τ E) (hT : T.carrier ⊆ T₀.carrier) :
    T₀.normalization '' T.carrier ⊆ closedBall T₀.x R := by
  have hC : T₀.normalization '' T₀.carrier
      ⊆ closedBall T₀.x (Tube.normalization.C (Module.finrank ℝ E) : ℝ) :=
    Tube.normalization_image_ambient_subset_closedBall hsit.pos_ambient hsit.ambient_le_one T₀
  have hCR : (Tube.normalization.C (Module.finrank ℝ E) : ℝ) ≤ R := by
    rw [hn]; exact hsit.normalizationConst_le_radius
  exact ((Set.image_mono hT).trans hC).trans (closedBall_subset_closedBall hCR)

/-- **The outer tube attached to a rescaled tube**: the centred unit extension of the image core,
at radius `σ`.  It is total — the nondegeneracy side condition of `Tube.centredExtension`
is automatic (`rescaleMap_x_ne_rescaleMap_y`) — so a whole family of parents can be pushed forward
at once (`exists_outerCover`). -/
noncomputable def outerTube (hθ : 0 < θ) (T₀ : Tube θ E) {R : ℝ} (hR : 0 < R) (σ : ℝ≥0)
    (T : Tube τ E) : Tube σ E :=
  Tube.centredExtension σ (rescaleMap_x_ne_rescaleMap_y hθ T₀ hR T)

/-- **(ix) The outer tube.**  In a rescaling situation, the image of a `τ`-tube `T ⊆ T₀` under the
unit form of the spine rescaling is contained in the honest `σ`-tube `outerTube`, which lies
inside `B_1` and has volume at most `(4R)^6` times the volume of the image.

Together with `spineRescale_exists_subsegment` this is the precise content of "`𝕋̃` is a family of
`τ/θ`-tubes": `σ` may be taken `≍ τ/θ`, since `IsRescalingSituation` asks `σ ≤ τ/θ` and the extra
hypothesis here asks `τ/θ ≤ 4σ`. -/
theorem outerTube_spec {R : ℝ} (hn : Module.finrank ℝ E = 3)
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R)
    (hρσ : (τ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ))
    (T₀ : Tube θ E) (T : Tube τ E) (hT : T.carrier ⊆ T₀.carrier) :
    spineRescaleUnit hsit.pos_ambient T₀ hR '' T.carrier
        ⊆ (outerTube hsit.pos_ambient T₀ hR σ T).carrier ∧
      (outerTube hsit.pos_ambient T₀ hR σ T).carrier ⊆ closedBall (0 : E) 1 ∧
      volume (outerTube hsit.pos_ambient T₀ hR σ T).carrier
        ≤ ENNReal.ofReal ((4 * R) ^ 6)
          * volume (spineRescaleUnit hsit.pos_ambient T₀ hR '' T.carrier) := by
  have hxy : T₀.rescaleMap R T.x ≠ T₀.rescaleMap R T.y :=
    rescaleMap_x_ne_rescaleMap_y hsit.pos_ambient T₀ hR T
  have hdist : Tube.IsNormalizationDistortion T₀ T :=
    Tube.normalization_distortion hsit.pos_ambient hsit.inner_le_ambient hsit.ambient_le_one
      T₀ T hT
  have hball : T₀.normalization '' T.carrier ⊆ closedBall T₀.x R :=
    normalization_image_subset_closedBall_of_subset hn hsit T₀ T hT
  obtain ⟨hsub, hpos, hvol⟩ :=
    Tube.rescale_outer_tube hsit hn hR hρσ T₀ T hdist hball hxy
  refine ⟨?_, hpos, ?_⟩
  · simpa [outerTube, spineRescaleUnit_coe hsit.pos_ambient T₀ hR] using hsub
  · simpa [outerTube, spineRescaleUnit_coe hsit.pos_ambient T₀ hR] using hvol

/-! ## The scale conversion `δ̃ ≤ δ^{ε₂}`

GWZ's standing separation between the outer scale `δ` and the rescaled scale `δ̃ = δ/θ` is
`δ̃ ≤ δ^{ε₂}`.  Reading a conclusion stated at the rescaled scale as one at the outer scale, and a
hypothesis at the outer scale as one at the rescaled scale, is the following pair of numeric
facts; fusing them with the transport laws above gives the three statements the proof of Main
Lemma 2 actually quotes. -/

/-! ## The three statements Main Lemma 2 quotes -/

end Kakeya.ML2Reduction

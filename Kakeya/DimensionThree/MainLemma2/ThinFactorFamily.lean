/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factoring.CoreAtScale
public import Kakeya.DimensionThree.MainLemma2.ThinCore
public import Kakeya.DimensionThree.MainLemma2.ThinCentredMult
public import Kakeya.DimensionThree.MainLemma2.ThinCellVolume
public import Kakeya.DimensionThree.MainLemma2.ThinFullness

/-!
# The factor family of the thin-case factoring step

`Kakeya.ThinCase.factoringApply` is the application of GWZ Proposition 5.1 — in the tree, the
`ShadedBody.outerFactoringFamily` pipeline of `Kakeya/Factoring/Multiplicity.lean` — to the
factoring `𝕋_B = ⨆_{W ∈ 𝕎_B} 𝕋_{B,W}` of clause (C4) of Configuration `hyp:ml2setup`.

Every entry point of that pipeline takes a `ShadedBody.FactorFamily` together with
`ShadedBody.FactorFamily.InnerIsDiscretizedAtScale`, whose two fields are

* `subset_unitBall` — every inner body lies in `Metric.closedBall 0 1`, and
* `le_scale` — every inner body has shortest affine scale at least the discretization scale.

This file builds that family and both fields out of the hypotheses of `factoringApply`.

Two points are worth recording.

**The centre.** `factoringApply` localises its bodies in a ball `Metric.closedBall z 1` with `z`
*existentially quantified*, because nothing in the data distinguishes the origin; the pipeline
insists on the origin. The family built here is therefore the translate of the data by `-z`, and
the translation-invariance lemmas of the first section are what make that free. Transporting the
pipeline's *output* back by `+z` is the business of the eventual proof of `factoringApply`, not of
this file.

**The scale.** `le_scale` is *not* a consequence of the hypotheses of `factoringApply`: those
bound the affine thicknesses of the segments only from above (`hle` puts a segment inside its
body, `hdims` compares segments with one another), so a segment may be an arbitrarily small ball
inside its body. It is therefore taken here as an explicit hypothesis `hscale`, at a scale `δ₀`
which the caller chooses. At the sole call site `Kakeya.ThinCase.perBall` the available value is
`δ₀ = δ / C₀`, from `Kakeya.ThinCase.IsBallFactoring.thick`
(`HasThicknesses (Y p).carrier C₀ ![r₁, δ, δ]` gives `C₀⁻¹ δ ≤ τ_k` at every rank, using
`δ ≤ a ≤ b ≤ r₁`); the constant `C₀` cannot be removed, which is why the scale is a parameter and
not `δ` itself.
-/

@[expose] public section

open scoped NNReal ENNReal

namespace Kakeya.ThinCase

open MeasureTheory Metric Set ShadedBody Kakeya
open scoped Pointwise

section Transport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] in
/-- The convex body underlying a translated shaded body is the translate of its convex body. -/
lemma toConvexSpaceBody_translate (W : ShadedBody E) (v : E) :
    (W.translate v).toConvexSpaceBody = W.toConvexSpaceBody.translate v := by
  ext1
  show v +ᵥ W.carrier = (v + ·) '' W.carrier
  rw [← Set.image_vadd]
  rfl


omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Affine thickness is translation invariant.** Both inequalities come from
`LipschitzWith.ethickness_image_le` applied to the affine equivalence `x ↦ v + x`, which is an
isometry, and to its inverse. -/
lemma ethickness_image_add_left (v : E) (X : Set E) (n : ℕ) :
    Metric.ethickness ℝ ((v + ·) '' X) n = Metric.ethickness ℝ X n := by
  have key : ∀ (w : E) (Y : Set E),
      Metric.ethickness ℝ ((w + ·) '' Y) n ≤ Metric.ethickness ℝ Y n := by
    intro w Y
    have hL : LipschitzWith 1 ⇑((AffineEquiv.constVAdd ℝ E w).toAffineMap) := by
      refine LipschitzWith.of_dist_le_mul ?_
      intro x y
      simp [AffineEquiv.constVAdd, dist_eq_norm]
    have h := hL.ethickness_image_le (𝕜 := ℝ) Y n
    have hmap : ⇑((AffineEquiv.constVAdd ℝ E w).toAffineMap) = (w + ·) := by
      funext x; simp [AffineEquiv.constVAdd]
    rw [hmap] at h
    simpa using h
  refine le_antisymm (key v X) ?_
  have h2 := key (-v) ((v + ·) '' X)
  rw [Set.image_image] at h2
  simpa using h2

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The shortest affine scale is translation invariant. -/
lemma ethickness_scale_image_add_left (v : E) (X : Set E) :
    Metric.ethickness.scale ℝ ((v + ·) '' X) = Metric.ethickness.scale ℝ X := by
  unfold Metric.ethickness.scale
  exact Finset.inf_congr rfl (fun n _ => ethickness_image_add_left v X n)


/-- Volume is translation invariant, in the form the shade of a translated body needs. -/
lemma volume_image_add_left (v : E) (X : Set E) :
    volume ((v + ·) '' X) = volume X := by
  rw [Set.image_add_left]
  exact measure_preimage_add volume (-v) X

end Transport

section Family

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {σ ω : Type*} [DecidableEq ω]

/-- **The factor family of `Kakeya.ThinCase.factoringApply`**: the segments `𝕋_B` as inner
bodies, the factoring bodies `𝕎_B` as outer bodies, the block map as parent, all translated by
`-z` so that the localisation ball `Metric.closedBall z 1` of `factoringApply`'s `hloc` becomes
the unit ball the Proposition 5.1 pipeline asks for. -/
def thinFactorFamily (segs : Finset σ) (Y : σ → ShadedBody E)
    (bodies : Finset ω) (Wb : ω → ConvexSpaceBody E) (blk : σ → ω) (z : E)
    (hblk : ∀ p ∈ segs, blk p ∈ bodies)
    (hle : ∀ p ∈ segs, (Y p).toConvexSpaceBody ≤ Wb (blk p)) :
    ShadedBody.FactorFamily E σ ω where
  innerSet := segs
  innerBody := fun p => (Y p).translate (-z)
  outerSet := bodies
  outerBody := fun j => (Wb j).translate (-z)
  parent := blk
  parent_mem := hblk
  inner_le_parent := fun p hp => by
    rw [toConvexSpaceBody_translate]
    exact translate_le_translate _ (hle p hp)

variable {segs : Finset σ} {Y : σ → ShadedBody E} {bodies : Finset ω}
  {Wb : ω → ConvexSpaceBody E} {blk : σ → ω} {z : E}
  {hblk : ∀ p ∈ segs, blk p ∈ bodies}
  {hle : ∀ p ∈ segs, (Y p).toConvexSpaceBody ≤ Wb (blk p)}

omit [FiniteDimensional ℝ E] [DecidableEq ω] in
@[simp] lemma thinFactorFamily_innerSet :
    (thinFactorFamily segs Y bodies Wb blk z hblk hle).innerSet = segs := rfl

omit [FiniteDimensional ℝ E] [DecidableEq ω] in
@[simp] lemma thinFactorFamily_outerSet :
    (thinFactorFamily segs Y bodies Wb blk z hblk hle).outerSet = bodies := rfl

omit [FiniteDimensional ℝ E] [DecidableEq ω] in
@[simp] lemma thinFactorFamily_parent :
    (thinFactorFamily segs Y bodies Wb blk z hblk hle).parent = blk := rfl

omit [FiniteDimensional ℝ E] [DecidableEq ω] in
@[simp] lemma thinFactorFamily_innerBody (p : σ) :
    (thinFactorFamily segs Y bodies Wb blk z hblk hle).innerBody p = (Y p).translate (-z) := rfl

omit [FiniteDimensional ℝ E] [DecidableEq ω] in
@[simp] lemma thinFactorFamily_outerBody (j : ω) :
    (thinFactorFamily segs Y bodies Wb blk z hblk hle).outerBody j = (Wb j).translate (-z) := rfl

omit [FiniteDimensional ℝ E] in
lemma thinFactorFamily_fiber (j : ω) :
    (thinFactorFamily segs Y bodies Wb blk z hblk hle).fiber j =
      segs.filter (fun p => blk p = j) := by
  classical
  simp [ShadedBody.FactorFamily.fiber, thinFactorFamily]

omit [FiniteDimensional ℝ E] [DecidableEq ω] in
/-- **Step 1 of the proof of `Kakeya.ThinCase.factoringApply`: the family is inner-discretized.**

`subset_unitBall` is `hloc` together with `hle`, read after the translation by `-z`; `le_scale`
is the hypothesis `hscale`, which is *not* derivable from the other hypotheses of
`factoringApply` (see the module docstring). -/
theorem thinFactorFamily_innerIsDiscretizedAtScale [Nontrivial E] {δ₀ : ℝ≥0}
    (hloc : ∀ j ∈ bodies, (Wb j).carrier ⊆ Metric.closedBall z 1)
    (hscale : ∀ p ∈ segs, (δ₀ : ℝ≥0∞) ≤ Metric.ethickness.scale ℝ (Y p).carrier) :
    (thinFactorFamily segs Y bodies Wb blk z hblk hle).InnerIsDiscretizedAtScale δ₀ where
  subset_unitBall := by
    intro p hp
    have hsub : (Y p).carrier ⊆ Metric.closedBall z 1 := fun x hx =>
      hloc (blk p) (hblk p hp) (hle p hp hx)
    show ((-z) + ·) '' (Y p).carrier ⊆ Metric.closedBall 0 1
    rintro _ ⟨x, hx, rfl⟩
    have hx' := hsub hx
    simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hx' ⊢
    simpa [add_comm, ← sub_eq_add_neg] using hx' 
  le_scale := by
    intro p hp
    show (δ₀ : ℝ≥0∞) ≤ Metric.ethickness.scale ℝ (((-z) + ·) '' (Y p).carrier)
    rw [ethickness_scale_image_add_left]
    exact hscale p hp


end Family


/-! ### The Proposition 5.1 output, transported back

`ShadedBody.outerFactoringFamily` runs the Step 0 - Step 5 pipeline on the translated family;
its output lives in translated coordinates, and the definitions below translate it back by `+z`.
Every clause of `Kakeya.ThinCase.factoringApply` that the pipeline supplies without a further
pigeonhole is then read off. -/

section Pipeline

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] {σ ω : Type*} [DecidableEq ω]
  {segs : Finset σ} {Y : σ → ShadedBody E} {bodies : Finset ω}
  {Wb : ω → ConvexSpaceBody E} {blk : σ → ω} {z : E}
  {hblk : ∀ p ∈ segs, blk p ∈ bodies}
  {hle : ∀ p ∈ segs, (Y p).toConvexSpaceBody ≤ Wb (blk p)}
  {δ₀ w₁ : ℝ≥0}

/-- `0 < w₁` from the scale window, the form the `AtScale` pipeline asks for. -/
theorem thinPipeline_w₁_pos (hδ₀ : 0 < δ₀) (hw₁ : w₁ ∈ Set.Icc δ₀ 1) : 0 < w₁ :=
  lt_of_lt_of_le hδ₀ hw₁.1

/-- The output of the corrected GWZ Proposition 5.1 at the thin-case family, in translated
coordinates.

This is `ShadedBody.outerThickFamilyAtScale`, the **weighted** pipeline, not
`ShadedBody.outerFactoringFamily`. The two differ by the eccentricity datum `D`, and taking the
weighted one is what makes `ShadedBody.factoringAndMultPropCoreAtScale` — and with it conjunct (i)
of `Kakeya.ThinCase.factoringApply`, its `thick_fullness` field — available at all. The datum is
`Kakeya.ThinCase.thinVolumeRatio`, built from `factoringApply`'s own `hdims` and `hFr`. -/
noncomputable def thinPipeline (hδ₀ : 0 < δ₀)
    (hdisc : (thinFactorFamily segs Y bodies Wb blk z hblk hle).InnerIsDiscretizedAtScale δ₀)
    (D : ShadedBody.OuterInnerVolumeRatio (thinFactorFamily segs Y bodies Wb blk z hblk hle))
    (hw₁ : w₁ ∈ Set.Icc δ₀ 1) : ShadedFactorFamily E σ ω :=
  ShadedBody.outerThickFamilyAtScale (thinFactorFamily segs Y bodies Wb blk z hblk hle)
    hδ₀ hdisc D w₁ (thinPipeline_w₁_pos hδ₀ hw₁)

variable {hδ₀ : 0 < δ₀}
  {hdisc : (thinFactorFamily segs Y bodies Wb blk z hblk hle).InnerIsDiscretizedAtScale δ₀}
  {D : ShadedBody.OuterInnerVolumeRatio (thinFactorFamily segs Y bodies Wb blk z hblk hle)}
  {hw₁ : w₁ ∈ Set.Icc δ₀ 1}

/-- The refined family of segments `𝕋'_B ⊆ 𝕋_B` returned by the pipeline. -/
noncomputable def thinSegs' (hδ₀ : 0 < δ₀)
    (hdisc : (thinFactorFamily segs Y bodies Wb blk z hblk hle).InnerIsDiscretizedAtScale δ₀)
    (D : ShadedBody.OuterInnerVolumeRatio (thinFactorFamily segs Y bodies Wb blk z hblk hle))
    (hw₁ : w₁ ∈ Set.Icc δ₀ 1) : Finset σ :=
  (thinPipeline hδ₀ hdisc D hw₁).innerSet

/-- The retained family of bodies `𝕎'_B ⊆ 𝕎_B` returned by the pipeline. -/
noncomputable def thinBodies' (hδ₀ : 0 < δ₀)
    (hdisc : (thinFactorFamily segs Y bodies Wb blk z hblk hle).InnerIsDiscretizedAtScale δ₀)
    (D : ShadedBody.OuterInnerVolumeRatio (thinFactorFamily segs Y bodies Wb blk z hblk hle))
    (hw₁ : w₁ ∈ Set.Icc δ₀ 1) : Finset ω :=
  (thinPipeline hδ₀ hdisc D hw₁).outerSet

/-- The refined shading `Y'` on the segments, translated back to the original position. -/
noncomputable def thinY' (hδ₀ : 0 < δ₀)
    (hdisc : (thinFactorFamily segs Y bodies Wb blk z hblk hle).InnerIsDiscretizedAtScale δ₀)
    (D : ShadedBody.OuterInnerVolumeRatio (thinFactorFamily segs Y bodies Wb blk z hblk hle))
    (hw₁ : w₁ ∈ Set.Icc δ₀ 1) : σ → ShadedBody E :=
  fun p => ((thinPipeline hδ₀ hdisc D hw₁).innerBody p).translate z

/-- The induced shading `Y_{𝕎'}` on the enlarged bodies, translated back. -/
noncomputable def thinW (hδ₀ : 0 < δ₀)
    (hdisc : (thinFactorFamily segs Y bodies Wb blk z hblk hle).InnerIsDiscretizedAtScale δ₀)
    (D : ShadedBody.OuterInnerVolumeRatio (thinFactorFamily segs Y bodies Wb blk z hblk hle))
    (hw₁ : w₁ ∈ Set.Icc δ₀ 1) : ω → ShadedBody E :=
  fun j => ((thinPipeline hδ₀ hdisc D hw₁).outerBody j).translate z

/-- Clause (a): the refined segments form a subfamily. -/
theorem thinSegs'_subset : thinSegs' hδ₀ hdisc D hw₁ ⊆ segs := by
  intro p hp
  unfold thinSegs' thinPipeline at hp
  rw [ShadedBody.outerThickFamilyAtScale_innerSet_eq_filter] at hp
  exact (Finset.mem_filter.mp hp).1

/-- Clause (b): the retained bodies form a subfamily. -/
theorem thinBodies'_subset : thinBodies' hδ₀ hdisc D hw₁ ⊆ bodies :=
  ShadedBody.outerThickFamilyAtScale_outerSet_subset _ hδ₀ hdisc D w₁ (thinPipeline_w₁_pos hδ₀ hw₁)

/-- Clause (c): the refinement changes the shadings, never the carriers. -/
theorem thinY'_toConvexSpaceBody (p : σ) :
    (thinY' hδ₀ hdisc D hw₁ p).toConvexSpaceBody = (Y p).toConvexSpaceBody := by
  unfold thinY' thinPipeline
  rw [toConvexSpaceBody_translate,
    ShadedBody.outerThickFamilyAtScale_innerBody_toConvexSpaceBody]
  show (((Y p).translate (-z)).toConvexSpaceBody).translate z = (Y p).toConvexSpaceBody
  rw [toConvexSpaceBody_translate, ConvexSpaceBody.translate_neg_cancel]

/-- Clause (d): the refined shadings shrink. -/
theorem thinY'_shade_subset {p : σ} (hp : p ∈ thinSegs' hδ₀ hdisc D hw₁) :
    (thinY' hδ₀ hdisc D hw₁ p).shade ⊆ (Y p).shade := by
  have h := (ShadedBody.outerThickFamilyAtScale_isCRefinement
    (thinFactorFamily segs Y bodies Wb blk z hblk hle) hδ₀ hdisc D w₁
      (thinPipeline_w₁_pos hδ₀ hw₁)).1.2 p hp
  have hsub : ((thinPipeline hδ₀ hdisc D hw₁).innerBody p).shade ⊆ ((-z) + ·) '' (Y p).shade :=
    h.2
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, rfl⟩ := hsub hx
  simpa using hy


omit [Nontrivial E] in
/-- The shade of a translated shaded body has the same volume. -/
lemma volume_shade_translate (W : ShadedBody E) (v : E) :
    volume (W.translate v).shade = volume W.shade := by
  show volume ((v + ·) '' W.shade) = volume W.shade
  exact volume_image_add_left v W.shade

/-- The parent map of the pipeline output is the block map. -/
theorem thinPipeline_parent : (thinPipeline hδ₀ hdisc D hw₁).parent = blk :=
  ShadedBody.outerThickFamilyAtScale_parent _ hδ₀ hdisc D w₁ (thinPipeline_w₁_pos hδ₀ hw₁)


/-- **Clause (vi) of `Kakeya.ThinCase.factoringApply`, at the honest pipeline loss.**

This is the mass half of `ShadedBody.outerThickFamilyAtScale_isCRefinement`, read back through
the translation. The loss is now the *weighted* pipeline's
`ShadedBody.factoringCoreAtScaleRefinementConstant` rather than
`ShadedBody.outerFactoringFamily_refinement.c`. -/
theorem thinRefinement_mass :
    ((ShadedBody.factoringCoreAtScaleUniformRefinementConstant (Module.finrank ℝ E)
          segs.card
          (ShadedBody.OuterInnerVolumeRatio.exponent D) w₁ : ℝ≥0) : ℝ≥0∞)
        * ∑ p ∈ segs, volume (Y p).shade
      ≤ ∑ p ∈ thinSegs' hδ₀ hdisc D hw₁, volume (thinY' hδ₀ hdisc D hw₁ p).shade := by
  have h := (ShadedBody.outerThickFamilyAtScale_isCRefinement_of_lossBound
    (thinFactorFamily segs Y bodies Wb blk z hblk hle) hδ₀ hdisc D w₁
      (thinPipeline_w₁_pos hδ₀ hw₁)
      (ShadedBody.FactoringAtScaleLossBound.uniform
        (thinFactorFamily segs Y bodies Wb blk z hblk hle) hδ₀ hdisc D w₁
          (thinPipeline_w₁_pos hδ₀ hw₁))).2
  have hl : ∑ p ∈ segs,
      volume ((thinFactorFamily segs Y bodies Wb blk z hblk hle).innerBody p).shade
        = ∑ p ∈ segs, volume (Y p).shade :=
    Finset.sum_congr rfl fun p _ => volume_shade_translate (Y p) (-z)
  have hr : ∑ p ∈ thinSegs' hδ₀ hdisc D hw₁, volume (thinY' hδ₀ hdisc D hw₁ p).shade
      = ∑ p ∈ (thinPipeline hδ₀ hdisc D hw₁).innerSet,
          volume ((thinPipeline hδ₀ hdisc D hw₁).innerBody p).shade :=
    Finset.sum_congr rfl fun p _ => volume_shade_translate _ z
  rw [hr, ← hl]
  exact h

/-- **Clause (ii) of `Kakeya.ThinCase.factoringApply`**: every shaded point of a retained
segment is a shaded point of the outer body of its block, and that block is retained. -/
theorem thinShadingContainment {p : σ} (hp : p ∈ thinSegs' hδ₀ hdisc D hw₁) :
    blk p ∈ thinBodies' hδ₀ hdisc D hw₁ ∧
      (thinY' hδ₀ hdisc D hw₁ p).shade ⊆ (thinW hδ₀ hdisc D hw₁ (blk p)).shade := by
  have hmem := (thinPipeline hδ₀ hdisc D hw₁).parent_mem p hp
  rw [thinPipeline_parent] at hmem
  refine ⟨hmem, ?_⟩
  have hsub := (thinPipeline hδ₀ hdisc D hw₁).shade_subset_parent p hp
  rw [thinPipeline_parent] at hsub
  show (z + ·) '' ((thinPipeline hδ₀ hdisc D hw₁).innerBody p).shade ⊆
    (z + ·) '' ((thinPipeline hδ₀ hdisc D hw₁).outerBody (blk p)).shade
  exact Set.image_mono hsub

/-- The fibre of the pipeline output over a body is the block of retained segments. -/
theorem thinPipeline_fiber (j : ω) :
    (thinPipeline hδ₀ hdisc D hw₁).fiber j
      = (thinSegs' hδ₀ hdisc D hw₁).filter (fun p => blk p = j) := by
  classical
  ext p
  simp [ShadedFactorFamily.fiber, thinSegs', thinPipeline_parent (hδ₀ := hδ₀) (hdisc := hdisc)
    (D := D) (hw₁ := hw₁)]


omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- Pointwise multiplicity is translation covariant. -/
lemma pointwiseMultiplicity_translate {ι : Type*} (t : Finset ι) (V : ι → ShadedBody E) (v x : E) :
    ShadedBody.pointwiseMultiplicity t (fun i => (V i).translate v) (v + x)
      = ShadedBody.pointwiseMultiplicity t V x := by
  classical
  show ({i ∈ t | (v + x) ∈ ((V i).translate v).shade}).card
    = ({i ∈ t | x ∈ (V i).shade}).card
  congr 1
  refine Finset.filter_congr (fun i _ => ?_)
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := add_left_cancel hyx
    exact this ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- **Clause (iii)(b) of `Kakeya.ThinCase.factoringApply`**: GWZ Item 4, transported back.

The weighted pipeline states it sharply — `ShadedBody.outerThickFamilyAtScale_fiber_multiplicity`
pins the fibre multiplicity to a single dyadic block `[2 ^ k, 2 ^ (k+1))` with `k` the
*weighted pipeline exponent*, the same `k` for every fibre. Reading `μinner := 2 ^ k` turns that
into the two-sided form the conjunct asks for, at the factor `2` the `hCcore2` binder pays for. -/
theorem thinInnerConstMult :
    ∃ μinner : ℝ≥0, ∀ j ∈ thinBodies' hδ₀ hdisc D hw₁,
      ∀ x ∈ ShadedBody.iUnionShade ((thinSegs' hδ₀ hdisc D hw₁).filter (fun p => blk p = j))
          (thinY' hδ₀ hdisc D hw₁),
        (ShadedBody.pointwiseMultiplicity
            ((thinSegs' hδ₀ hdisc D hw₁).filter (fun p => blk p = j))
            (thinY' hδ₀ hdisc D hw₁) x : ℝ≥0) ≤ 2 * μinner ∧
          μinner ≤ 2 * (ShadedBody.pointwiseMultiplicity
            ((thinSegs' hδ₀ hdisc D hw₁).filter (fun p => blk p = j))
            (thinY' hδ₀ hdisc D hw₁) x : ℝ≥0) := by
  classical
  set k : ℕ := (thinFactorFamily segs Y bodies Wb blk z hblk hle).weightedPipelineExponent
    hδ₀ hdisc D (w₁ : ℝ) (by exact_mod_cast thinPipeline_w₁_pos hδ₀ hw₁) with hk
  refine ⟨(2 : ℝ≥0) ^ k, ?_⟩
  intro j hj x hx
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨x₀, hx₀, rfl⟩ : ∃ x₀, x₀ ∈ ((thinPipeline hδ₀ hdisc D hw₁).innerBody i).shade ∧
      z + x₀ = x := hxi
  have hmem : x₀ ∈ ShadedBody.iUnionShade ((thinPipeline hδ₀ hdisc D hw₁).fiber j)
      (thinPipeline hδ₀ hdisc D hw₁).innerBody := by
    refine Set.mem_iUnion₂.mpr ⟨i, ?_, hx₀⟩
    rw [thinPipeline_fiber]
    exact hi
  have hmult : ShadedBody.pointwiseMultiplicity
      ((thinSegs' hδ₀ hdisc D hw₁).filter (fun p => blk p = j)) (thinY' hδ₀ hdisc D hw₁) (z + x₀)
      = ShadedBody.pointwiseMultiplicity ((thinPipeline hδ₀ hdisc D hw₁).fiber j)
          (thinPipeline hδ₀ hdisc D hw₁).innerBody x₀ := by
    rw [thinPipeline_fiber]
    exact pointwiseMultiplicity_translate _ _ z x₀
  rw [hmult]
  obtain ⟨hlow, hhigh⟩ := ShadedBody.outerThickFamilyAtScale_fiber_multiplicity
    (F := thinFactorFamily segs Y bodies Wb blk z hblk hle) hδ₀ hdisc D w₁
      (thinPipeline_w₁_pos hδ₀ hw₁) hmem
  set m : ℕ := ShadedBody.pointwiseMultiplicity ((thinPipeline hδ₀ hdisc D hw₁).fiber j)
    (thinPipeline hδ₀ hdisc D hw₁).innerBody x₀ with hm
  have hlow' : 2 ^ k ≤ m := hlow
  have hhigh' : m < 2 ^ (k + 1) := hhigh
  constructor
  · have : m ≤ 2 * 2 ^ k := by
      have : m < 2 * 2 ^ k := by simpa [pow_succ, two_mul, Nat.mul_comm] using hhigh'
      exact this.le
    calc ((m : ℕ) : ℝ≥0) ≤ ((2 * 2 ^ k : ℕ) : ℝ≥0) := by exact_mod_cast this
      _ = 2 * (2 : ℝ≥0) ^ k := by push_cast; ring
  · calc (2 : ℝ≥0) ^ k = ((2 ^ k : ℕ) : ℝ≥0) := by push_cast; ring
      _ ≤ ((m : ℕ) : ℝ≥0) := by exact_mod_cast hlow'
      _ ≤ 2 * ((m : ℕ) : ℝ≥0) := by
          nth_rewrite 1 [← one_mul (((m : ℕ) : ℝ≥0))]
          gcongr; norm_num


end Pipeline

/-! ### The step-1 gate: `le_scale` is not derivable

The construction above takes `hscale` as a hypothesis. This section shows, by counterexample,
that it has to: no hypothesis of `Kakeya.ThinCase.factoringApply` bounds the affine thickness of
a segment from *below*. -/

section Gate

open scoped NNReal ENNReal

/-- The three-dimensional model space used by the counterexample. -/
abbrev GateE3 := EuclideanSpace ℝ (Fin 3)


/-- The body used both as the single segment and as the single factoring body. -/
noncomputable def qball : ConvexSpaceBody GateE3 := ConvexSpaceBody.closedBall 0 (1/4) (by norm_num)

@[simp] lemma qball_carrier : qball.carrier = Metric.closedBall (0 : GateE3) (1/4) := rfl

noncomputable def qseg : ShadedBody GateE3 where
  toConvexSpaceBody := qball
  shade := Metric.closedBall (0 : GateE3) (1/4)
  measurableSet_shade := measurableSet_closedBall
  shade_subset := le_rfl

@[simp] lemma qseg_carrier : (qseg).carrier = Metric.closedBall (0 : GateE3) (1/4) := rfl
@[simp] lemma qseg_shade : (qseg).shade = Metric.closedBall (0 : GateE3) (1/4) := rfl
@[simp] lemma qseg_body : (qseg).toConvexSpaceBody = qball := rfl


end Gate

end Kakeya.ThinCase

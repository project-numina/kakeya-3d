/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineRescale
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineNonEccentric
public import Kakeya.ShadedUniform
public import Kakeya.Tube.CoverCountComparable

/-!
# Step 10 of GWZ Main Lemma 2: the rescaled family as honest tubes

Blueprint: GWZ, the paragraph of the non-eccentric case that
begins "We will bound `μ(𝕋̃[T_b], Ỹ)` using Lemma `lemmain2vns`, with `ζ = η_j/2`".

## The blocker this file removes

`Kakeya.ML2Reduction.spineFamily` sends a family of `ShadedTube`s to a family of
`ShadedBody`s — the affine image of a tube is not a tube — while GWZ Lemma 9.1
(`Kakeya.multiplicity_le_of_card_isEssDistinct_ge`, abstracted as
GWZ Lemma 9.1 binds `T : ι → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))`.  So step 10
could not even be *stated*.

`Kakeya.ML2Reduction.outerFamily` re-presents the rescaled family as a genuine
`ι → ShadedTube σ E`: each rescaled body is replaced by the outer `σ`-tube
`Kakeya.ML2Reduction.outerTube` that contains it, and the shading is carried across unchanged.
Every quantity Lemma 9.1 reads is then transported, each with its loss:

| quantity | transport | loss |
|---|---|---|
| `∀ i ∈ s, carrier ⊆ B₁` | `outerFamily_carrier_subset_closedBall` | none |
| `|s|` | the index set is unchanged | none |
| `μ(·)` | `outerFamily_multiplicity` | **none** (an equality: multiplicity reads only shades) |
| `λ(·)` | `outerFamily_le_fullness` | `outerLoss R = (4R)^6`, one-sided |
| `Δ_max(·)` | `outerFamily_maxDensity_le` | `outerLoss R = (4R)^6`, one-sided |

The two remaining hypotheses of Lemma 9.1 — the `ShadedTube.ShadedUniformTubeSet` witness and the
`ρ`-tube count clause — are *not* transported here; see the "What is not here" section.

## Pricing the loss

`outerLoss R` is a **constant** (`R` is the ambient normalization radius
`Tube.normalization.C 3 = 64`, fixed before every scale), so
`Kakeya.ML2Reduction.exists_threshold_outerLoss` absorbs it into `δ^{-κ}` for any `κ > 0` below
an explicit threshold, and `Kakeya.ML2Spine.spine_gainBudget_of_loss` shows the spine has room for
any `κ ≤ 40 η_{j-1}/ε₂`.  So the replacement costs nothing in the exponent bookkeeping.

## What is not here, and why

Lemma 9.1 has five hypotheses on the family.  Three are discharged above.  The other two are
carried as explicit hypotheses of `Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer`:

* `huni` — `∃ C, 1 ≤ C ∧ C ≤ σ^{-ηd} ∧ Nonempty (ShadedTube.ShadedUniformTubeSet s U
  (Tube.ssfGridLen δ') C)` on the *outer* family.  A
  `ShadedUniformTubeSet` is built from a tube-level `Tube.UniformTubeSet` by
  `ShadedTube.exists_shadedUniformTubeSet_of_uniformTubeSet`; the tube-level hierarchy on the
  outer family at the grid of `δ'` is a fresh object — the upstairs hierarchy lives on the grid of
  `δ̃` — so it has to be built, not transported.
* `hcnt` — the count clause on the outer family, in the repaired form: at every
  scale of Lemma 9.1's window, *one* essentially distinct all-used `ρ`-tube family over the outer
  tubes, of cardinality `≥ ρ^{-2-ζ}`.  `Kakeya.ML2Spine.spine_tube_card_lower` proves literally
  `(σ/b)^{-2-η_j/2} ≤ |𝕋̃_σ[T_b]|` for the *canonical* `σ`-tube family of the hierarchy, and
  `Kakeya.ML2Reduction.mem_sigmaWindow_of_window_fits` below proves that Lemma 9.1's window
  `[(δ')^{1-ϖ}, (δ')^{ϖ}]` sits inside the `σ`-window `[δ̃^{1-ε₂}, δ̃^{ε₂}]` divided by `b`, which
  is the blueprint's "we choose `ε₂ ≤ ϖ/2`; then this estimate follows from
  `TTSigmaBigCardinalityV1`".  The canonical family lives on the *rescaled bodies*; transporting
  "used" from a body to its outer tube costs a constant dilation, and that transport is paid once,
  in `Kakeya.ML2Reduction.outerCanonicalCover_of_canonicalCover`
  (`Reduction/SpineCountClause.lean`).
  (`Kakeya.ML2Reduction.outerFamily_count_of_spineFamily_count` and the `CoverCountComparable`
  section below are records of the earlier `∀`-over-covers rendering of the clause.)
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Set Topology Filter ShadedBody ConvexSpaceBody

namespace Kakeya.ML2Reduction

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι κ : Type*} {θ τ σ : ℝ≥0}

/-! ## `Δ_max` under a comparable replacement

The one item of `Tube.comparableTransport_oneSided` that was missing: enlarging every body of a
family by at most a factor `C` in volume enlarges `Δ_max` by at most `C`.  Unlike the fullness and
Frostman items this needs no shading and no test body — `Kakeya.maxDensity_le_iff` turns it into
`Tube.densityIn_le_of_comparable` at every test body at once. -/

/-- **`Δ_max` grows by at most the comparability constant.** -/
theorem maxDensity_le_of_comparable {C : ℝ≥0} (hC : 1 ≤ C) (s : Finset ι)
    (𝕎 𝕍 : ι → ConvexSpaceBody E) (hsub : ∀ i ∈ s, 𝕎 i ≤ 𝕍 i)
    (hvol : ∀ i ∈ s, volume (𝕍 i).carrier ≤ (C : ℝ≥0∞) * volume (𝕎 i).carrier) :
    Kakeya.maxDensity s 𝕍 ≤ (C : ℝ≥0∞) * Kakeya.maxDensity s 𝕎 := by
  rw [Kakeya.maxDensity_le_iff]
  intro K
  refine (Tube.densityIn_le_of_comparable hC s 𝕎 𝕍 hsub hvol K).trans ?_
  gcongr
  exact Kakeya.le_maxDensity s 𝕎 K

/-! ## The constant of the outer-tube replacement -/

/-- The volume loss of the outer-tube replacement, `(4R)^6`, as an `NNReal`.  It is the constant
of `Tube.rescale_outer_tube`, read through `Kakeya.ML2Reduction.outerTube_spec`. -/
noncomputable def outerLoss (R : ℝ) : ℝ≥0 := Real.toNNReal ((4 * R) ^ 6)

theorem coe_outerLoss (R : ℝ) : ((outerLoss R : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal ((4 * R) ^ 6) :=
  rfl

theorem one_le_outerLoss {R : ℝ} (hR : 1 ≤ R) : 1 ≤ outerLoss R := by
  have h : (1 : ℝ) ≤ (4 * R) ^ 6 := one_le_pow₀ (by linarith)
  rw [← NNReal.coe_le_coe, NNReal.coe_one, outerLoss,
    Real.coe_toNNReal _ (by positivity : (0 : ℝ) ≤ (4 * R) ^ 6)]
  exact h

theorem outerLoss_ne_zero {R : ℝ} (hR : 1 ≤ R) : outerLoss R ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_outerLoss hR))

/-! ## The outer shaded tube -/

/-- **The rescaled shaded tube, re-presented as an honest `σ`-tube.**

The carrier is the outer tube `Kakeya.ML2Reduction.outerTube` of the rescaled tube; the shade is
the rescaled shade, intersected with that carrier so that the definition is *total* — no
containment hypothesis is needed to write it down.  Under the containment
`S.carrier ⊆ T₀.carrier` the intersection is inert
(`Kakeya.ML2Reduction.outerShadedTube_shade_eq`), so nothing is lost. -/
noncomputable def outerShadedTube (hθ : 0 < θ) (T₀ : Tube θ E) {R : ℝ} (hR : 0 < R) (σ : ℝ≥0)
    (S : ShadedTube τ E) : ShadedTube σ E where
  toTube := outerTube hθ T₀ hR σ S.toTube
  shade := (spineRescaleUnit hθ T₀ hR '' S.shade) ∩ (outerTube hθ T₀ hR σ S.toTube).carrier
  measurableSet_shade :=
    (Kakeya.measurableSet_affineEquiv_image _ S.measurableSet_shade).inter
      (outerTube hθ T₀ hR σ S.toTube).isCompact'.isClosed.measurableSet
  shade_subset := Set.inter_subset_right

@[simp]
theorem outerShadedTube_toTube (hθ : 0 < θ) (T₀ : Tube θ E) {R : ℝ} (hR : 0 < R) (σ : ℝ≥0)
    (S : ShadedTube τ E) :
    (outerShadedTube hθ T₀ hR σ S).toTube = outerTube hθ T₀ hR σ S.toTube := rfl

@[simp]
theorem outerShadedTube_carrier (hθ : 0 < θ) (T₀ : Tube θ E) {R : ℝ} (hR : 0 < R) (σ : ℝ≥0)
    (S : ShadedTube τ E) :
    (outerShadedTube hθ T₀ hR σ S).carrier = (outerTube hθ T₀ hR σ S.toTube).carrier := rfl

@[simp]
theorem outerShadedTube_shade (hθ : 0 < θ) (T₀ : Tube θ E) {R : ℝ} (hR : 0 < R) (σ : ℝ≥0)
    (S : ShadedTube τ E) :
    (outerShadedTube hθ T₀ hR σ S).shade
      = (spineRescaleUnit hθ T₀ hR '' S.shade) ∩ (outerTube hθ T₀ hR σ S.toTube).carrier := rfl

/-- **The rescaled family, re-presented as a family of honest `σ`-tubes.** -/
noncomputable def outerFamily (hθ : 0 < θ) (T₀ : Tube θ E) {R : ℝ} (hR : 0 < R) (σ : ℝ≥0)
    (𝕋 : ι → ShadedTube τ E) : ι → ShadedTube σ E :=
  fun i => outerShadedTube hθ T₀ hR σ (𝕋 i)

@[simp]
theorem outerFamily_apply (hθ : 0 < θ) (T₀ : Tube θ E) {R : ℝ} (hR : 0 < R) (σ : ℝ≥0)
    (𝕋 : ι → ShadedTube τ E) (i : ι) :
    outerFamily hθ T₀ hR σ 𝕋 i = outerShadedTube hθ T₀ hR σ (𝕋 i) := rfl

variable [Nontrivial E]

/-- **The shade of the outer tube is exactly the rescaled shade.**  The intersection in the
definition is inert as soon as the tube sits inside the ambient tube. -/
theorem outerShadedTube_shade_eq {R : ℝ} (hn : Module.finrank ℝ E = 3)
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R)
    (hτσ : (τ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ)) (T₀ : Tube θ E) (S : ShadedTube τ E)
    (hS : S.carrier ⊆ T₀.carrier) :
    (outerShadedTube hsit.pos_ambient T₀ hR σ S).shade
      = spineRescaleUnit hsit.pos_ambient T₀ hR '' S.shade := by
  have h := (outerTube_spec hn hsit hR hτσ T₀ S.toTube hS).1
  refine Set.inter_eq_self_of_subset_left ?_
  exact (Set.image_mono S.shade_subset).trans h

/-- **The outer tube lies in the unit ball**, which is Lemma 9.1's first hypothesis. -/
theorem outerShadedTube_subset_closedBall {R : ℝ} (hn : Module.finrank ℝ E = 3)
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R)
    (hτσ : (τ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ)) (T₀ : Tube θ E) (S : ShadedTube τ E)
    (hS : S.carrier ⊆ T₀.carrier) :
    (outerShadedTube hsit.pos_ambient T₀ hR σ S).carrier ⊆ closedBall (0 : E) 1 :=
  (outerTube_spec hn hsit hR hτσ T₀ S.toTube hS).2.1

/-- **The volume loss of the replacement.** -/
theorem outerShadedTube_volume_le {R : ℝ} (hn : Module.finrank ℝ E = 3)
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R)
    (hτσ : (τ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ)) (T₀ : Tube θ E) (S : ShadedTube τ E)
    (hS : S.carrier ⊆ T₀.carrier) :
    volume (outerShadedTube hsit.pos_ambient T₀ hR σ S).carrier
      ≤ (outerLoss R : ℝ≥0∞)
        * volume (spineImage (spineRescaleUnit hsit.pos_ambient T₀ hR) S).carrier := by
  rw [coe_outerLoss, spineImage_carrier]
  exact (outerTube_spec hn hsit hR hτσ T₀ S.toTube hS).2.2

/-- **The rescaled body sits inside its outer tube.** -/
theorem spineImage_le_outerShadedTube {R : ℝ} (hn : Module.finrank ℝ E = 3)
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R)
    (hτσ : (τ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ)) (T₀ : Tube θ E) (S : ShadedTube τ E)
    (hS : S.carrier ⊆ T₀.carrier) :
    (spineImage (spineRescaleUnit hsit.pos_ambient T₀ hR) S).toConvexSpaceBody
      ≤ (outerShadedTube hsit.pos_ambient T₀ hR σ S).toConvexSpaceBody :=
  (outerTube_spec hn hsit hR hτσ T₀ S.toTube hS).1

/-! ## The outer family, and the transported quantities -/

section Family

variable {R : ℝ} {s : Finset ι} {𝕋 : ι → ShadedTube τ E} {T₀ : Tube θ E}

/-- Every member of the outer family lies in `B₁` — Lemma 9.1's first hypothesis. -/
theorem outerFamily_carrier_subset_closedBall (hn : Module.finrank ℝ E = 3)
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R)
    (hτσ : (τ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ))
    (hsub : ∀ i ∈ s, (𝕋 i).carrier ⊆ T₀.carrier) :
    ∀ i ∈ s, (outerFamily hsit.pos_ambient T₀ hR σ 𝕋 i).carrier ⊆ closedBall (0 : E) 1 :=
  fun i hi => outerShadedTube_subset_closedBall hn hsit hR hτσ T₀ (𝕋 i) (hsub i hi)

/-- On the index set the outer family has exactly the rescaled shades. -/
theorem outerFamily_shade_eq (hn : Module.finrank ℝ E = 3)
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R)
    (hτσ : (τ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ))
    (hsub : ∀ i ∈ s, (𝕋 i).carrier ⊆ T₀.carrier) :
    ∀ i ∈ s, (outerFamily hsit.pos_ambient T₀ hR σ 𝕋 i).toShadedBody.shade
      = (spineFamily (spineRescaleUnit hsit.pos_ambient T₀ hR) 𝕋 i).shade := by
  intro i hi
  rw [spineFamily_apply, spineImage_shade]
  exact outerShadedTube_shade_eq hn hsit hR hτσ T₀ (𝕋 i) (hsub i hi)

/-- **The multiplicity is transported exactly.**  `ShadedBody.multiplicity` reads only the shades
and their union, and the outer replacement changes neither; the rescaling changes both by the same
Jacobian.  This is the transport step 10 needs in the *conclusion* direction. -/
theorem outerFamily_multiplicity (hn : Module.finrank ℝ E = 3)
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R)
    (hτσ : (τ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ))
    (hsub : ∀ i ∈ s, (𝕋 i).carrier ⊆ T₀.carrier) :
    ShadedBody.multiplicity s (fun i => (outerFamily hsit.pos_ambient T₀ hR σ 𝕋 i).toShadedBody)
      = ShadedBody.multiplicity s (fun i => (𝕋 i).toShadedBody) := by
  rw [Tube.multiplicity_congr_of_shading_eq s
    (spineFamily (spineRescaleUnit hsit.pos_ambient T₀ hR) 𝕋)
    (fun i => (outerFamily hsit.pos_ambient T₀ hR σ 𝕋 i).toShadedBody)
    (outerFamily_shade_eq hn hsit hR hτσ hsub)]
  exact spineFamily_multiplicity (spineRescaleUnit hsit.pos_ambient T₀ hR) s 𝕋

/-- **The fullness drops by at most `outerLoss R`.** -/
theorem outerFamily_le_fullness (hn : Module.finrank ℝ E = 3)
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R) (hR1 : 1 ≤ R)
    (hτσ : (τ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ))
    (hsub : ∀ i ∈ s, (𝕋 i).carrier ⊆ T₀.carrier) :
    (outerLoss R)⁻¹ * ShadedBody.fullness s (fun i => (𝕋 i).toShadedBody)
      ≤ ShadedBody.fullness s
          (fun i => (outerFamily hsit.pos_ambient T₀ hR σ 𝕋 i).toShadedBody) := by
  have hfull := Tube.le_fullness_of_volume_le (C := outerLoss R) (one_le_outerLoss hR1) s
    (spineFamily (spineRescaleUnit hsit.pos_ambient T₀ hR) 𝕋)
    (fun i => (outerFamily hsit.pos_ambient T₀ hR σ 𝕋 i).toShadedBody)
    (outerFamily_shade_eq hn hsit hR hτσ hsub)
    (fun i hi => outerShadedTube_volume_le hn hsit hR hτσ T₀ (𝕋 i) (hsub i hi))
  rwa [spineFamily_fullness (spineRescaleUnit hsit.pos_ambient T₀ hR) s 𝕋] at hfull

/-- **`Δ_max` grows by at most `outerLoss R`.** -/
theorem outerFamily_maxDensity_le (hn : Module.finrank ℝ E = 3)
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R) (hR1 : 1 ≤ R)
    (hτσ : (τ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ))
    (hsub : ∀ i ∈ s, (𝕋 i).carrier ⊆ T₀.carrier) :
    Kakeya.maxDensity s
        (fun i => (outerFamily hsit.pos_ambient T₀ hR σ 𝕋 i).toConvexSpaceBody)
      ≤ (outerLoss R : ℝ≥0∞)
        * Kakeya.maxDensity s (fun i => (𝕋 i).toConvexSpaceBody) := by
  have hmax := maxDensity_le_of_comparable (C := outerLoss R) (one_le_outerLoss hR1) s
    (fun i => (spineFamily (spineRescaleUnit hsit.pos_ambient T₀ hR) 𝕋 i).toConvexSpaceBody)
    (fun i => (outerFamily hsit.pos_ambient T₀ hR σ 𝕋 i).toConvexSpaceBody)
    (fun i hi => spineImage_le_outerShadedTube hn hsit hR hτσ T₀ (𝕋 i) (hsub i hi))
    (fun i hi => outerShadedTube_volume_le hn hsit hR hτσ T₀ (𝕋 i) (hsub i hi))
  rwa [spineFamily_maxDensity (spineRescaleUnit hsit.pos_ambient T₀ hR) s 𝕋] at hmax

end Family

/-! ## The scale window of Lemma 9.1 sits inside the `σ`-window of the spine

The blueprint (GWZ: non-eccentric case): "*We have to check that for every
`σ' ∈ [(δ')^{1-ϖ}, (δ')^{ϖ}]` we have `|𝕋'_{σ'}| ≥ (σ')^{-2-ζ}`.  We choose `ε₂ ≤ ϖ/2`.  Then this
estimate follows from `TTSigmaBigCardinalityV1`.*"

The arithmetic is below, and what it really needs is `ε₂ (1 + ϖ) ≤ ϖ`, i.e. the field
`Kakeya.ML2Spine.IsSpine.window_fits` — the *same* condition at both ends of the window, which is
why that field and not `eps₂_le_vnsWindow` is the one spent here. -/

/-! ## Pricing the two losses of step 10 against the spine

Step 10 pays two prices, and neither was accounted for before:

* the **constant** `outerLoss R = (4R)^6` of the outer-tube replacement, charged once against
  `Δ_max` and once against `λ`.  Being a constant it is absorbed by a threshold on the scale
  (`Kakeya.ML2Reduction.exists_threshold_outerLoss`);
* the **exponent** loss of the rescaling itself.  Lemma 9.1 applied at `δ' = δ̃/b` returns
  `(δ')^{ν}`, and `δ' ≤ δ̃^{1-ε₂}` only gives `δ̃^{(1-ε₂)ν}`.  The blueprint writes
  `δ̃^{ν(β,η_j)}`; the honest exponent is `(1-ε₂) ν(β,η_j)`.

The second is a genuine accounting gap: `Kakeya.ML2Spine.IsSpine.gain_budget` does **not** cover
it (`Kakeya.ML2Reduction.rescaleLoss_not_free_of_isSpine_fields`), because the shortfall `ε₂ ν` is
not proportional to `η_{j-1}` while all the slack `Kakeya.ML2Spine.spine_gainBudget_of_loss` has is.
It *is* covered by the concrete spine, because `Kakeya.ML2Spine.spineStep` caps
`η_k ≤ e β ν/34` — see `Kakeya.ML2Reduction.spineRung_gainBudget_of_rescaleLoss`, where the `β`
in that cap is exactly what cancels the `β` in `η'_k = 12 η_k/(e β)`. -/

omit [Nontrivial E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `a ≤ b⁻¹` from `b a ≤ 1`. -/
theorem le_inv_of_mul_le_one {a b : ℝ≥0} (hb : b ≠ 0) (h : b * a ≤ 1) : a ≤ b⁻¹ := by
  calc a = b⁻¹ * (b * a) := by rw [← mul_assoc, inv_mul_cancel₀ hb, one_mul]
    _ ≤ b⁻¹ * 1 := by gcongr
    _ = b⁻¹ := mul_one _

omit [Nontrivial E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The arithmetic of the rescaling loss.**  If the rung is capped by `e β ν/34` — which is what
`Kakeya.ML2Spine.spineStep` does — then the loss `(1-ε₂)` on the gain is affordable, with room left
for an additional multiscale loss `κ ≤ 20 η_k/ε₂`.

The `β` of the cap cancels the `β` of `η'_k = 12 η_k/(e β)`, which is exactly why the abstract
`Kakeya.ML2Spine.IsSpine.gain_budget` cannot reach this conclusion. -/
theorem gainBudget_of_step_le {β ε₂ e X ν κ : ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (he : 0 < e) (_hε₂ : 0 < ε₂) (hε₂' : ε₂ ≤ 1 / 12)
    (hdiv : e ≤ ε₂ / 5) (hX : 0 < X) (hν : 0 < ν) (hstep : X ≤ e * β * ν / 34)
    (hκ : κ ≤ 20 * X / ε₂) :
    10 * X / ε₂ + 2 * (12 * X / (e * β)) + κ ≤ (1 - ε₂) * ν := by
  have h5e : 5 * e ≤ ε₂ := by linarith
  have hXe : X / e ≤ β * ν / 34 := by
    rw [div_le_iff₀ he]; nlinarith [hstep]
  have hXeb : X / (e * β) ≤ ν / 34 := by
    rw [div_le_iff₀ (mul_pos he hβ)]; nlinarith [hstep]
  have hA : 10 * X / ε₂ ≤ 2 * (X / e) := by
    have h := div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ 10 * X)
      (by positivity : (0 : ℝ) < 5 * e) h5e
    calc 10 * X / ε₂ ≤ 10 * X / (5 * e) := h
      _ = 2 * (X / e) := by field_simp; ring
  have hB : 20 * X / ε₂ ≤ 4 * (X / e) := by
    have h := div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ 20 * X)
      (by positivity : (0 : ℝ) < 5 * e) h5e
    calc 20 * X / ε₂ ≤ 20 * X / (5 * e) := h
      _ = 4 * (X / e) := by field_simp; ring
  have hβν : β * ν ≤ ν := by nlinarith
  have hsum : 10 * X / ε₂ + 2 * (12 * X / (e * β)) + κ ≤ 30 * ν / 34 := by
    have e1 : 2 * (12 * X / (e * β)) = 24 * (X / (e * β)) := by ring
    have e2 : X / e ≤ ν / 34 := by nlinarith [hXe]
    rw [e1]
    nlinarith [hA, hB, hXeb, e2, hκ]
  nlinarith [hsum, hν.le, hε₂']

/-- **The gain budget of step 11, with step 10's rescaling loss included, for the constructed
spine.**  Identical in shape to `Kakeya.ML2Spine.spine_gainBudget_of_loss` except that the gain is
read at `(1 - ε₂) ν` instead of `ν`. -/
theorem spineRung_gainBudget_of_rescaleLoss {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    {k : ℕ} (hk : k < ML2Spine.spineCount ϖ ε₁) {κ : ℝ}
    (hκ : κ ≤ 20 * ML2Spine.spineRung β ϖ ε₁ gain dens k / ML2Spine.spineEps₂ ϖ ε₁) :
    10 * ML2Spine.spineRung β ϖ ε₁ gain dens k / ML2Spine.spineEps₂ ϖ ε₁
        + 2 * (12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
            / (ML2Spine.spineDiv ϖ ε₁ * β)) + κ
      ≤ (1 - ML2Spine.spineEps₂ ϖ ε₁)
          * gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) := by
  have hsp := ML2Spine.spineRung_isSpine hβ hβ1 hϖ hε₁ hgain hdens
  have hst := ML2Spine.spineRung_eq_step (β := β) (ϖ := ϖ) (ε₁ := ε₁)
    (gain := gain) (dens := dens) hk
  have hstep : ML2Spine.spineRung β ϖ ε₁ gain dens k
      ≤ ML2Spine.spineDiv ϖ ε₁ * β
          * gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) / 34 := by
    rw [hst]
    exact (min_le_left _ _).trans (min_le_right _ _)
  exact gainBudget_of_step_le hβ hβ1 hsp.div_pos hsp.eps₂_pos hsp.eps₂_lt_twelfth.le
    hsp.div_le (hsp.rung_pos k) (hgain _ (by linarith [hsp.rung_pos (k + 1)])) hstep hκ

/-! ## The count clause transports from the rescaled bodies to the outer tubes -/

end Kakeya.ML2Reduction

/-! ## Step 10 -/

namespace Kakeya.ML2Reduction

universe u

open ShadedBody ConvexSpaceBody

/-- **GWZ Lemma 9.1 at one scale.**  The body of GWZ Lemma 9.1 with the
`∀ᶠ δ in 𝓝[>] 0` stripped off, so that it can be instantiated at a scale — `δ' = δ̃/b` — that
depends on data quantified *after* the outer scale.  Reading the eventual statement as a threshold
is what keeps the quantifier order of step 10 honest. -/
def Lemma91At (β ϖ ζ ν ηd : ℝ) (δ : ℝ≥0) : Prop :=
  ∀ {α : Type u} (s : Finset α) (T : α → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
    (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
    (∀ i ∈ s, (T i).toTube.IsCentred) →
    (∃ C : ℝ≥0, 1 ≤ C ∧ (C : ℝ≥0∞) ≤ (δ : ℝ≥0∞) ^ (-ηd) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) C)) →
    Kakeya.maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-ηd) →
    ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ ηd →
    (∀ ρ : ℝ≥0, ρ ∈ Set.Icc (δ ^ (1 - ϖ)) (δ ^ ϖ) →
      ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
        (tρ : Set κ).Pairwise
          (fun j k ↦ _root_.IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
        (∀ j ∈ tρ, ∃ i ∈ s, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
        (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) →
    ShadedBody.multiplicity s (fun i ↦ (T i).toShadedBody) ≤
      (δ : ℝ≥0∞) ^ ν * (s.card : ℝ≥0∞) ^ β

/-- **`Lemma91At` is ANTITONE in its density exponent `ηd`.** -/
theorem Lemma91At.mono_dens {β ϖ ζ ν ηd ηd' : ℝ} {δ : ℝ≥0} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (h : Lemma91At.{u} β ϖ ζ ν ηd δ) (hle : ηd' ≤ ηd) :
    Lemma91At.{u} β ϖ ζ ν ηd' δ := by
  have hδE0 : (δ : ℝ≥0∞) ≠ 0 := by simpa using ne_of_gt hδ0
  have hδE1 : (δ : ℝ≥0∞) ≤ 1 := by exact_mod_cast hδ1
  have hup : (δ : ℝ≥0∞) ^ (-ηd') ≤ (δ : ℝ≥0∞) ^ (-ηd) :=
    ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith)
  have hdown : (δ : ℝ≥0) ^ ηd ≤ (δ : ℝ≥0) ^ ηd' :=
    NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hle
  intro α s T hball hcen huni hmax hfull hcount
  refine h s T hball hcen ?_ (hmax.trans hup) (le_trans (by exact_mod_cast hdown) hfull) hcount
  obtain ⟨C, hC1, hC2, hC3⟩ := huni
  exact ⟨C, hC1, hC2.trans hup, hC3⟩

/-- **An eventual statement at `0⁺` is a statement below a threshold.**

*Short-name duplicate, deliberate.* `Kakeya.StickyKakeya.exists_threshold_of_eventually_nhdsGT`
(`StickyKakeya/Constants.lean`) proves the same thing with `δ` bound strict-implicitly, and
`Kakeya.VeryNotSticky.exists_threshold_of_eventually_nhdsGT`
(`MainLemma2/BallPolylogAbsorber.lean`) proves a stronger form with `d₀ ≤ 1`. This module does
not import either: the `StickyKakeya` one would put `Kakeya.Sticky`, and with it the project's
Sticky boundary, on this module's import closure, which it avoids. That is the same reason
`MainLemma2/AngularCover.lean` and `Plank/Section6PartBWiring.lean` carry copies of their own. -/
theorem exists_threshold_of_eventually_nhdsGT {P : ℝ≥0 → Prop}
    (h : ∀ᶠ δ in 𝓝[>] (0 : ℝ≥0), P δ) :
    ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧ ∀ δ : ℝ≥0, 0 < δ → δ ≤ δ₀ → P δ := by
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp h
  exact ⟨u, hu, fun δ h0 hle => hsub ⟨h0, hle⟩⟩

/-! ## What the count clause still needs, stated exactly

**Fidelity repair.**  Until this repair the predicate below quantified over an arbitrary
`V : α → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))` with **no lower bound on the size of the
bodies**, while its own docstring's intended proof used "two `ρ`-tubes containing a common body of
diameter `≍ 1` are comparable".  The hypothesis the proof needs was simply absent, and the
statement was **false at every loss `Λ`, at a positive scale `ρ`**: take `k > Λ` pairwise disjoint
vertical `ρ`-tubes, each carrying one *point*, with all `k` points on the core of one horizontal
`ρ`-tube.  That refutation is `Tube.not_coverCountComparableSpec`, and it is repeated here on the
scale-restricted form (`Kakeya.ML2Reduction.not_coverCountComparableNoChord`) so that no hypothesis
on `ρ` can be mistaken for the repair.

The repair adds the missing chord hypothesis, **parametrised by the chord length `d`** rather than
fixed at the convenient `2/5`.  That is not decoration: the call site is the `hcnt` binder of
`Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer`, whose bodies are the *rescaled* bodies
`spineFamily (spineRescaleUnit …) 𝕋 i`, and the chord those bodies carry is the image of the core,
of length in `[1/(4R), 1/4]` — see `Kakeya.ML2Reduction.rescaledCore_dist_ge` and
`Kakeya.ML2Reduction.rescaledCore_dist_le` in `Reduction/SpineCountClause.lean`.  Since the ambient
radius satisfies `R ≥ Tube.normalization.C 3 = 64`, that chord is **never** as long as `2/5`, so the
`2/5`-threshold form is the one hypothesis shape the consumer provably cannot supply.
-/

/-- **The cover-count comparability of step 10's count clause**, at chord length `d` and loss `Λ`.

GWZ writes `|𝕋_ρ|` for "the number of `ρ`-tubes needed to cover `𝕋`", a quantity well defined only
*up to constants*.  The Lean rendering of Lemma 9.1's third bullet takes it literally and demands
the lower bound for **every** essentially distinct `ρ`-tube cover of the family, whereas
`Kakeya.ML2Spine.spine_tube_card_lower` proves it for the
*canonical* cover carried by the tube hierarchy.  The bridge between the two is the comparability
here: an essentially distinct cover all of whose members are *used* is at most `Λ` times any other
cover at the same scale, provided the covered bodies are nondegenerate.

It is a statement of pure tube geometry — no shading, no scale window, no density hypothesis — and
it is now a **theorem** (`Kakeya.ML2Reduction.coverCountComparable`), not a residual input:
a used member `W j` contains some `V i`, which lies in some `W' j'`; the two `ρ`-tubes then share a
chord of length `≥ d`, so `W j ⊆ 32 K · W' j'` with `K = max 1 (2/(5d))`
(`Tube.subset_dilate_of_common_chord_at`), and `Tube.essDistinctTubesInSelfDilate` bounds the fibre
of `j ↦ j'` by `Tube.coverCountLossAt 3 K`.

`Kakeya.ML2Reduction.count_of_coverCountComparable` shows this is *exactly* enough. -/
def CoverCountComparable (d Λ : ℝ) : Prop :=
  ∀ {α κ κ' : Type u} {ρ : ℝ≥0} (V : α → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (s : Finset α) (t : Finset κ) (W : κ → Tube ρ (EuclideanSpace ℝ (Fin 3)))
    (t' : Finset κ') (W' : κ' → Tube ρ (EuclideanSpace ℝ (Fin 3))),
    0 < ρ → ρ ≤ 1 →
    (∀ i ∈ s, ∃ p ∈ (V i).carrier, ∃ q ∈ (V i).carrier, d ≤ dist p q) →
    (∀ i ∈ s, ∃ j ∈ t, V i ≤ (W j).toConvexSpaceBody) →
    (t : Set κ).Pairwise
      (fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) →
    (∀ j ∈ t, ∃ i ∈ s, V i ≤ (W j).toConvexSpaceBody) →
    (∀ i ∈ s, ∃ j ∈ t', V i ≤ (W' j).toConvexSpaceBody) →
    (t.card : ℝ) ≤ Λ * (t'.card : ℝ)

end Kakeya.ML2Reduction

end

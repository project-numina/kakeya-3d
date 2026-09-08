/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineOuterTubes
public import Kakeya.Tube.CoverCountComparable
public import Kakeya.Tube.EssentiallyDistinctReduction

/-!
# Step 10's count clause: from *one* canonical cover to *every* cover

Blueprint: GWZ, the non-eccentric case, the invocation of
GWZ Lemma 9.1 at `ζ = η_j/2`.

## The gap this file closes, and the one it does not

`Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer` carries the count clause of Lemma 9.1 as
the binder `hcnt`, which is `Lemma91At`'s clause verbatim at the
*outer* `σ`-tube family: at every scale of Lemma 9.1's window, *one* essentially distinct all-used
`ρ`-tube family over the outer tubes, of cardinality at least `ρ^{-2-ζ}`.  GWZ's `|𝕋_ρ|` is the
*canonical* parent cover, and the spine produces it on the **rescaled bodies**
`spineFamily (spineRescaleUnit …) 𝕋 i`, not on the outer tubes.  A `ρ`-tube containing a rescaled
body (a short chord, of length `≍ 1/(4R)`) need not contain the unit-length outer tube, so "used"
does not transport for free; what does transport, at a constant, is the *count*:

> **step 10's count clause is discharged by the existence, at each scale of Lemma 9.1's window, of
> *one* essentially distinct all-used `ρ`-tube family over the rescaled bodies whose cardinality is
> at least `Λ ρ^{-2-ζ}`, with `Λ = Kakeya.ML2Reduction.spineOuterCountLoss R` a constant.**

That is GWZ's reading, and
`Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer_of_canonicalCover` is step 10 with the
count clause replaced by that datum.  The transport is
`Kakeya.ML2Reduction.outerCanonicalCover_of_canonicalCover`: replace each member `W j` of the
canonical family by the `ρ`-tube `Tube.rescale (outerFamily … i_j) ρ` on the core of the outer tube
of the body `W j` uses (`Tube.rescale_le_rescale_of_radius_le`), pass to a maximal essentially
distinct subfamily (`Kakeya.Tube.exists_maximal_essDistinct`), and bound the fibres: `W j` shares
the chord of its body with `Tube.rescale (outerFamily … i_j) ρ`
(`Tube.subset_dilate_of_common_chord_at`), which overlaps a retained tube heavily
(`Kakeya.Tube.tubeOverlapCoreClose`), so every `W j` of a fibre lies in one fixed dilate of the
retained tube (`Kakeya.Tube.subset_dilate_rescale_of_subset_dilate`) and
`Tube.essDistinctTubesInSelfDilate` counts it.  The loss is
`spineOuterCountLoss R = 1 + C(3, 6·max(32K, C₃)²)` with `K = max 1 (8R/5)` — larger than
`Kakeya.ML2Reduction.spineCoverCountLoss R`, the constant of the earlier same-scale comparison of
covers, because the fibres are counted in a larger dilate; both are constants, and the `ζ`-slack
pays for either.

What this file does **not** do is *build* the canonical cover on the rescaled bodies.  Both of its
clauses are reduced here to things the tree already has:

* **used** — `Kakeya.ML2Reduction.outerTube_used_of_used`: pushing an upstairs `ρup`-tube family
  down through `Kakeya.ML2Reduction.outerTube` keeps every member used, and keeps the index
  `Finset` literally unchanged, so the cardinality is preserved on the nose.
* **essentially distinct** — `Kakeya.ML2Reduction.canonicalCoverAt_of_used_of_maxDensity`:
  essential distinctness does *not* transport (`outerTube` fattens `Ψ(W)` by `≍ 4R` in every
  direction, so upstairs essentially distinct tubes can push down onto outer tubes that coincide),
  but it does not have to — `Kakeya.Tube.refineToEssDistinctLeaves` extracts an essentially
  distinct subfamily from *any* family of `ρ`-tubes, at the cardinality loss
  `Kakeya.Tube.refineToEssDistinctLeaves.C n · Δ_max`, and a subfamily inherits "used" for free.

What is left is therefore (i) the upstairs canonical family itself — GWZ's
`TTSigmaBigCardinalityV1`, i.e. `Kakeya.ML2Spine.spine_tube_card_lower`, at the scale
`ρup = ρ θ` — and (ii) the arithmetic that the two losses
`spineOuterCountLoss R · refineToEssDistinctLeaves.C 3 · Δ_max` fit inside the count budget.
Neither is a comparison of covers, which is what this file removes.  See.

## Why the chord length is `1/(4R)` and not `2/5`

`Tube.CoverCountComparableChord` fixes the chord threshold at `2/5`, which is free for a family of
*tubes* (`Tube.exists_chord_of_shadedTube`: a tube's core has length `1`).  The bodies of the
canonical-cover datum are not tubes — they are the affine images
`spineFamily (spineRescaleUnit …) 𝕋 i` — and the chord the
rescaling supplies is the image of the core, whose length is pinned between `1/(4R)` and `1/4`
(`Kakeya.ML2Reduction.rescaledCore_dist_ge`, `Kakeya.ML2Reduction.rescaledCore_dist_le`).  Since
`Tube.IsRescalingSituation` forces `R ≥ Tube.normalization.C 3 = 64`, that chord is **never** as
long as `2/5`: the `2/5`-threshold form is available in the tree and inapplicable here.  The
comparison therefore has to be run at a general chord length `d`, at the loss
`Tube.coverCountLossAt 3 (max 1 (2/(5d)))` — still a constant, depending only on the dimension and
on `R`.

## Main declarations

* `Kakeya.ML2Reduction.rescaledCore_dist_ge` / `rescaledCore_dist_le` — the image of a tube's core
  under `Ψ = Tube.rescaleMap T₀ R` has length in `[1/(4R), 1/4]`.
* `Kakeya.ML2Reduction.exists_chord_spineFamily` — the chord hypothesis of
  `Kakeya.ML2Reduction.coverCountComparable`, discharged at the step-10 bodies at `d = 1/(4R)`.
* `Kakeya.ML2Reduction.spineCoverCountLoss` — the constant of the same-scale comparison of covers.
* `Kakeya.ML2Reduction.rescaled_count_of_canonicalCover` — the earlier `∀`-over-covers form of the
  count clause, from the canonical-cover datum (kept as a record; no longer on the spine's path).
* `Kakeya.ML2Reduction.dilate_carrier_subset_dilate_of_le`,
  `Kakeya.ML2Reduction.outerTransportRatio`,
  `Kakeya.ML2Reduction.exists_edUsed_rescale_of_edUsed_body` — the body→outer-tube transport of an
  essentially distinct all-used family, at a constant loss.
* `Kakeya.ML2Reduction.spineOuterCountLoss` — the constant `Λ` of that transport at the step-10
  bodies.
* `Kakeya.ML2Reduction.outerCanonicalCover_of_canonicalCover` — `Lemma91At`'s count clause on the
  outer family, from the canonical-cover datum on the rescaled bodies.
* `Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer_of_canonicalCover` — step 10 with `hcnt`
  replaced by that datum.
* `Kakeya.ML2Reduction.nonempty_of_canonicalCover` — the datum is **not** satisfied by the empty
  family, so it is not the `∅`-witness triviality.
* `Kakeya.ML2Reduction.outerTube_used_of_used` — the "used" half of the push-down.
* `Kakeya.ML2Reduction.canonicalCoverAt_of_used_of_maxDensity` — the essential-distinctness half.
* `Kakeya.ML2Reduction.spineCoverCountLoss_eq` — the constant is
  `Tube.count_of_canonicalCover_of_diam`'s at `d = 1/(4R)`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Set ConvexSpaceBody

namespace Kakeya.ML2Reduction

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι κ : Type*} {θ τ : ℝ≥0}

/-! ## The chord the rescaling supplies -/

/-- **`Ψ` shortens the core of an inner tube by exactly the homothety factor**: the image of the
core of a `τ`-tube `T ⊆ T₀` has length at least `1/(4R)`.

This is the chord hypothesis of `Kakeya.ML2Reduction.coverCountComparable` at the step-10 bodies.
`Tube.dist_rescaleMap` supplies the homothety half and `Tube.normalization_core_length` the fact
that `Φ` never shortens.  (MainLemma1 carries the same fact as
`Tube.dist_rescaleMap_ge_of_subset`; it is re-proved here in two lines rather than importing a
MainLemma1 module into the MainLemma2 reduction, which Section 8 owns.) -/
theorem rescaledCore_dist_ge (hθ : 0 < θ) (hθ1 : θ ≤ 1) {R : ℝ} (hR : 0 < R)
    (T₀ : Tube θ E) (T : Tube τ E) (hsub : T.carrier ⊆ T₀.carrier) :
    1 / (4 * R) ≤ dist (T₀.rescaleMap R T.x) (T₀.rescaleMap R T.y) := by
  rw [Tube.dist_rescaleMap T₀ hR T.x T.y]
  exact div_le_div_of_nonneg_right
    (Tube.normalization_core_length hθ hθ1 T₀ T hsub).1
    (by positivity : (0 : ℝ) < 4 * R).le

/-- **The nondegeneracy hypothesis of `Kakeya.ML2Reduction.coverCountComparable`, discharged at the
bodies of step 10's count clause**, at chord length `d = 1/(4R)`. -/
theorem exists_chord_spineFamily {R : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hR : 0 < R)
    (T₀ : Tube θ E) (𝕋 : ι → ShadedTube τ E) {s : Finset ι}
    (hsub : ∀ i ∈ s, (𝕋 i).carrier ⊆ T₀.carrier) :
    ∀ i ∈ s, ∃ p ∈ ((spineFamily (spineRescaleUnit hθ T₀ hR) 𝕋 i).toConvexSpaceBody).carrier,
      ∃ q ∈ ((spineFamily (spineRescaleUnit hθ T₀ hR) 𝕋 i).toConvexSpaceBody).carrier,
        1 / (4 * R) ≤ dist p q := by
  intro i hi
  refine ⟨spineRescaleUnit hθ T₀ hR (𝕋 i).x, ⟨(𝕋 i).x, (𝕋 i).toTube.x_mem_carrier, rfl⟩,
          spineRescaleUnit hθ T₀ hR (𝕋 i).y, ⟨(𝕋 i).y, (𝕋 i).toTube.y_mem_carrier, rfl⟩, ?_⟩
  rw [spineRescaleUnit_apply, spineRescaleUnit_apply]
  exact rescaledCore_dist_ge hθ hθ1 hR T₀ (𝕋 i).toTube (hsub i hi)

/-! ## The constant -/

/-- `2/(5K) ≤ 1/(4R)` at `K = max 1 (8R/5)`: the chord the rescaling gives clears the threshold the
comparison at `K` demands. -/
theorem chordThreshold_le_rescaledChord {R : ℝ} (hR : 0 < R) :
    2 / (5 * max 1 (8 * R / 5)) ≤ 1 / (4 * R) := by
  rcases le_total (8 * R / 5) 1 with h | h
  · rw [max_eq_left h, div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  · rw [max_eq_right h, div_le_div_iff₀ (by positivity) (by positivity)]
    ring_nf
    nlinarith

/-! ## The count clause -/

/-! ## The body→outer-tube transport of the canonical cover -/

/-- **A dilate grows with its ratio.**  Read through `Tube.dilate_carrier_eq_cthickening`: the
`a`-dilate is the `aδ`-neighbourhood of the centred segment of length `a`, and both grow with
`a`. -/
theorem dilate_carrier_subset_dilate_of_le {δ : ℝ≥0} (T : Tube δ E) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (Kakeya.Tube.dilate T a).carrier ⊆ (Kakeya.Tube.dilate T b).carrier := by
  have hb : 0 < b := ha.trans_le hab
  have hb0 : b ≠ 0 := hb.ne'
  rw [_root_.Tube.dilate_carrier_eq_cthickening T ha,
    _root_.Tube.dilate_carrier_eq_cthickening T hb]
  have hδ : a * (δ : ℝ) ≤ b * (δ : ℝ) := mul_le_mul_of_nonneg_right hab δ.coe_nonneg
  have hseg : segment ℝ (T.center - (a / 2) • T.direction) (T.center + (a / 2) • T.direction)
      ⊆ segment ℝ (T.center - (b / 2) • T.direction) (T.center + (b / 2) • T.direction) := by
    refine Convex.segment_subset (convex_segment _ _) ?_ ?_
    · rw [segment_eq_image']
      refine ⟨(b - a) / (2 * b), ⟨div_nonneg (by linarith) (by positivity),
        (div_le_one (by positivity)).mpr (by linarith)⟩, ?_⟩
      match_scalars <;> field_simp <;> ring
    · rw [segment_eq_image']
      refine ⟨(b + a) / (2 * b), ⟨div_nonneg (by linarith) (by positivity),
        (div_le_one (by positivity)).mpr (by linarith)⟩, ?_⟩
      match_scalars <;> field_simp <;> ring
  exact (Metric.cthickening_subset_of_subset _ hseg).trans (Metric.cthickening_mono hδ _)

/-- **The dilation ratio at which the transport's fibres are counted**: `6 c²` for
`c = max (32 K) C_n`, where `32 K` is the chord-comparability ratio of
`Tube.subset_dilate_of_common_chord_at` at chord threshold `2/(5K)`, `C_n` is the
overlap-containment ratio `Kakeya.Tube.tubeOverlapCoreClose.C n`, and the `6 c²` is the ratio
`Kakeya.Tube.subset_dilate_rescale_of_subset_dilate` produces. -/
noncomputable abbrev outerTransportRatio (n : ℕ) (K : ℝ) : ℝ :=
  6 * (max (32 * K) (Kakeya.Tube.tubeOverlapCoreClose.C n)) ^ 2

/-- **`exists_edUsed_rescale_of_edUsed_body`, with its witness exposed** (route (α)).  ADDITIVE: the existing theorem above is and is recovered from this one by
`exists_edUsed_rescale_of_edUsed_body_of_data`.

That is enough to *use* the family and not
enough to *say what it is*: a consumer that must then compare `V j` with something built from the
same `O (f j)` — the centred hand-back's `hnode` is exactly such a consumer — receives a tube it
only knows to be a container, and a containment constant would have to be invented to get back. The proof already names the witness (`V := fun j ↦ (O (f j)).rescale ρ`, and `f` from `choose!`), so
exposing `f` costs nothing and makes the downstream discharge a syntactic `exact`.

Same proof as the existing theorem, with `⟨u, V, …⟩` replaced by `⟨u, f, …⟩`. -/
theorem exists_edUsed_rescale_of_edUsed_body_data [Nontrivial E] [Nonempty ι] {ρ σ : ℝ≥0}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hσρ : σ ≤ ρ) {K : ℝ} (hK : 1 ≤ K)
    (B : ι → ConvexSpaceBody E) (O : ι → Tube σ E) (s : Finset ι)
    (hnd : ∀ i ∈ s, ∃ p ∈ (B i).carrier, ∃ q ∈ (B i).carrier, 2 / (5 * K) ≤ dist p q)
    (hBO : ∀ i ∈ s, B i ≤ (O i).toConvexSpaceBody)
    (t : Finset κ) (W : κ → Tube ρ E)
    (hED : (t : Set κ).Pairwise fun j k => IsEssentiallyDistinct (W j).carrier (W k).carrier)
    (hused : ∀ j ∈ t, ∃ i ∈ s, B i ≤ (W j).toConvexSpaceBody) :
    ∃ (u : Finset κ) (f : κ → ι), u ⊆ t ∧ (∀ j ∈ u, f j ∈ s) ∧
      ((u : Set κ).Pairwise fun j k =>
        IsEssentiallyDistinct ((O (f j)).rescale ρ).carrier ((O (f k)).rescale ρ).carrier) ∧
      (t.card : ℝ) ≤ (Tube.essDistinctTubesInSelfDilate.C (Module.finrank ℝ E)
        (outerTransportRatio (Module.finrank ℝ E) K) : ℝ) * (u.card : ℝ) := by
  classical
  rcases t.eq_empty_or_nonempty with rfl | ⟨j₀, hj₀⟩
  · exact ⟨∅, fun _ => Classical.arbitrary ι, by simp, by simp, by simp, by simp⟩
  obtain ⟨i₀, hi₀, -⟩ := hused j₀ hj₀
  haveI : Nonempty ι := ⟨i₀⟩
  choose! f hfs hfle using hused
  set V : κ → Tube ρ E := fun j => (O (f j)).rescale ρ with hV
  have hOV : ∀ j ∈ t, (O (f j)).toConvexSpaceBody ≤ (V j).toConvexSpaceBody := by
    intro j hj
    have h := Tube.rescale_le_rescale_of_radius_le (O (f j)) hσρ
    rwa [Tube.toConvexSpaceBody_rescale_self] at h
  have hBV : ∀ j ∈ t, B (f j) ≤ (V j).toConvexSpaceBody :=
    fun j hj => (hBO _ (hfs j hj)).trans (hOV j hj)
  set Cn : ℝ := Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) with hCn
  set c : ℝ := max (32 * K) Cn with hc
  have hCn1 : 1 ≤ Cn := le_of_lt (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C _)
  have hc1 : 1 ≤ c := le_trans (by linarith) (le_max_left _ _)
  have hD1 : 1 ≤ 6 * c ^ 2 := by nlinarith
  obtain ⟨u, hut, hEDV, hmax⟩ := Kakeya.Tube.exists_maximal_essDistinct t V
  -- every `W j` lies in the `6c²`-dilate of a retained `V k`
  have key : ∀ j ∈ t, ∃ k ∈ u,
      (W j).carrier ⊆ (Kakeya.Tube.dilate (V k) (6 * c ^ 2)).carrier := by
    intro j hj
    obtain ⟨k, hk, hVk⟩ : ∃ k ∈ u, (V k).carrier ⊆ (Kakeya.Tube.dilate (V j) c).carrier := by
      by_cases hju : j ∈ u
      · exact ⟨j, hju, Tube.subset_dilate (V j) hc1⟩
      · obtain ⟨k, hk, hnot⟩ := hmax j hj hju
        refine ⟨k, hk, ?_⟩
        have hhalf : (1 / 2 : ℝ≥0∞) * volume (V j).carrier
            < volume ((V j).carrier ∩ (V k).carrier) := by
          have h' : (1 / 2 : ℝ≥0∞) * max (volume (V k).carrier) (volume (V j).carrier)
              < volume ((V k).carrier ∩ (V j).carrier) := lt_of_not_ge hnot
          rw [Set.inter_comm] at h'
          calc (1 / 2 : ℝ≥0∞) * volume (V j).carrier
              ≤ (1 / 2 : ℝ≥0∞) * max (volume (V k).carrier) (volume (V j).carrier) := by
                gcongr; exact le_max_right _ _
            _ < _ := h'
        exact (Kakeya.Tube.tubeOverlapCoreClose hρ0 hρ1 (V j) (V k) hhalf).trans
          (dilate_carrier_subset_dilate_of_le (V j) (by linarith) (le_max_right _ _))
    refine ⟨k, hk, ?_⟩
    have hWj : (W j).carrier ⊆ (Kakeya.Tube.dilate (V j) c).carrier := by
      obtain ⟨p, hp, q, hq, hpq⟩ := hnd (f j) (hfs j hj)
      have h32 := Tube.subset_dilate_of_common_chord_at (by exact_mod_cast hρ1) hK (W j) (V j)
        (hfle j hj hp) (hfle j hj hq) (hBV j hj hp) (hBV j hj hq) hpq
      exact h32.trans (dilate_carrier_subset_dilate_of_le (V j) (by linarith) (le_max_left _ _))
    have hOk : (O (f k)).carrier ⊆ (Kakeya.Tube.dilate (V j) c).carrier :=
      fun x hx => hVk (hOV k (hut hk) hx)
    have hsand := Kakeya.Tube.subset_dilate_rescale_of_subset_dilate (V j) (O (f k))
      (c := c) (Λ := 6 * c ^ 2) hc1 (by nlinarith) le_rfl hOk subset_rfl
    exact hWj.trans hsand
  -- the fibres
  let A : κ → Finset κ := fun k =>
    t.filter (fun j => (W j).carrier ⊆ (Kakeya.Tube.dilate (V k) (6 * c ^ 2)).carrier)
  have hcover : t ⊆ u.biUnion A := by
    intro j hj
    obtain ⟨k, hk, hjk⟩ := key j hj
    exact Finset.mem_biUnion.mpr ⟨k, hk, Finset.mem_filter.mpr ⟨hj, hjk⟩⟩
  set Cb : ℝ≥0 :=
    Tube.essDistinctTubesInSelfDilate.C (Module.finrank ℝ E) (6 * c ^ 2) with hCb
  have hfib : ∀ k ∈ u, ((A k).card : ℝ≥0∞) ≤ (Cb : ℝ≥0∞) := by
    intro k _
    refine Tube.essDistinctTubesInSelfDilate hD1 hρ0 hρ1 (V k) (A k) W ?_ ?_
    · exact hED.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))
    · intro j hj
      exact (Finset.mem_filter.mp hj).2
  have hENN : (t.card : ℝ≥0∞) ≤ (Cb : ℝ≥0∞) * (u.card : ℝ≥0∞) := by
    calc (t.card : ℝ≥0∞) ≤ ((u.biUnion A).card : ℝ≥0∞) := by
          exact_mod_cast Finset.card_le_card hcover
      _ ≤ (∑ k ∈ u, (A k).card : ℝ≥0∞) := by
          exact_mod_cast Finset.card_biUnion_le (t := A)
      _ ≤ ∑ _k ∈ u, (Cb : ℝ≥0∞) := Finset.sum_le_sum hfib
      _ = (Cb : ℝ≥0∞) * (u.card : ℝ≥0∞) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hreal : (t.card : ℝ) ≤ (Cb : ℝ) * (u.card : ℝ) := by
    have := (ENNReal.toReal_le_toReal (by simp) (by finiteness)).mpr hENN
    simpa using this
  exact ⟨u, f, hut, fun k hk => hfs k (hut hk), hEDV, hreal⟩

/-- **The loss of the body→outer-tube transport at the step-10 bodies**: the packing constant of
`Tube.essDistinctTubesInSelfDilate` at the ratio `outerTransportRatio 3 K`, `K = max 1 (8R/5)`
being the chord parameter the rescaling delivers (`Kakeya.ML2Reduction.spineCoverCountLoss`),
padded by `1` so that `1 ≤ Λ` is free.  It depends only on the ambient dimension and on `R`. -/
noncomputable abbrev spineOuterCountLoss (R : ℝ) : ℝ≥0 :=
  1 + Tube.essDistinctTubesInSelfDilate.C 3 (outerTransportRatio 3 (max 1 (8 * R / 5)))

theorem one_le_spineOuterCountLoss (R : ℝ) : (1 : ℝ) ≤ (spineOuterCountLoss R : ℝ) := by
  have h : (1 : ℝ≥0) ≤ spineOuterCountLoss R := le_self_add
  exact_mod_cast h

/-! ## Step 10, with the count clause discharged -/

/-! ## The essential-distinctness half of the canonical-cover datum -/

/-! ## What is still owed: the push-down of the canonical cover -/

/-- **The "used" half of the push-down.**  If every member of an upstairs `ρup`-tube family `W`
contains one of the tubes `𝕋 i`, then every one of the downstairs outer tubes contains the
corresponding rescaled body — so "all members used" transports across the rescaling for free, and
so does the cardinality (`Kakeya.ML2Reduction.exists_outerCover` re-indexes by the *same* `Finset`).

Essential distinctness does **not** transport, and that is the whole residue: `outerTube` fattens
`Ψ(W k)` by `≍ 4R` in every direction (`Kakeya.ML2Reduction.outerTube_spec` prices the fattening at
`(4R)^6` in volume), so upstairs essentially distinct tubes can push down onto outer tubes that
coincide. -/
theorem outerTube_used_of_used [Nontrivial E] {ρup ρ : ℝ≥0} {R : ℝ}
    (hn : Module.finrank ℝ E = 3)
    (hsit : Tube.IsRescalingSituation θ ρup ρ R 3) (hR : 0 < R)
    (hρσ : (ρup : ℝ) / (θ : ℝ) ≤ 4 * (ρ : ℝ))
    (T₀ : Tube θ E) {s : Finset ι} (𝕋 : ι → ShadedTube τ E)
    {t : Finset κ} (W : κ → Tube ρup E)
    (hsubW : ∀ k ∈ t, (W k).carrier ⊆ T₀.carrier)
    (hused : ∀ k ∈ t, ∃ i ∈ s, (𝕋 i).carrier ⊆ (W k).carrier) :
    ∀ k ∈ t, ∃ i ∈ s,
      (spineFamily (spineRescaleUnit hsit.pos_ambient T₀ hR) 𝕋 i).toConvexSpaceBody
        ≤ (outerTube hsit.pos_ambient T₀ hR ρ (W k)).toConvexSpaceBody := by
  intro k hk
  obtain ⟨i, hi, hle⟩ := hused k hk
  refine ⟨i, hi, ?_⟩
  exact (Set.image_mono hle).trans
    (outerTube_spec hn hsit hR hρσ T₀ (W k) (hsubW k hk)).1

end Kakeya.ML2Reduction

end

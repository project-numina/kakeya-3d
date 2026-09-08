/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCentredHandBackUniform

/-!
# The count clause at centred representatives

The cover is read at the contracted radius `ρ / C`, while the conclusion
retains the bound `ρ^(-2-ζ)`. Transport keeps one index per retained node and
pays a named packing constant on the hypothesis side.

The cover `W : κ₀ → Tube (ρ/C)` is essentially distinct before normalization.
Its images remain essentially distinct as convex bodies, because normalization
is a similarity. The output tubes sit on canonical nodes after normalization;
the node map may be many-to-one, so the output cannot retain every index and
still be essentially distinct. `exists_edUsed_subfamily_of_edBodies` selects
an essentially distinct subfamily of nodes and bounds the resulting loss.

The constants are `centringCoverRadiusConstant`, `centringCountLossConstant R`
and `centringCoverFibreConstant`. The count-loss constant is the product
`spineOuterCountLoss R * centringCoverFibreConstant`, while the packing estimate
uses only the second factor. The generic lemmas take these constants as
parameters; the specialized lemmas use their named values.

`normaliseBody_rescale_le_rescale_of_data` gives geometric containment from
the representative's line parameters and the contracted radius.
`card_le_centringCoverFibreConstant_of_normaliseBody` gives the packing bound.
The remaining geometric inputs are the two representative-data conjuncts,
the midpoint bound and the scalar radius inequality.

`countClause_of_contractedCover` and `countTransport_of_contractedCover`
combine these ingredients into the count-transport predicate.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric RealInnerProductSpace Kakeya.ML2Reduction

namespace Kakeya.VeryNotSticky

universe u

/-! ## Essential distinctness across the similarity -/

/-- **Essential distinctness survives `normalise` exactly** — it is a similarity, and
`IsEssentiallyDistinct` is a ratio of volumes.  Stated on `ConvexSpaceBody`, 's
standing rule: the image of a `Tube` is not a `Tube` (its core is `1/8`), and every clause
relating the two sides of `normalise` must avoid the unit-core type. -/
theorem essDistinct_normaliseBody {K L : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    (h : _root_.IsEssentiallyDistinct K.carrier L.carrier) :
    _root_.IsEssentiallyDistinct (normaliseBody K).carrier (normaliseBody L).carrier := by
  have h8 : ((8 : ℝ)⁻¹) ≠ 0 := by norm_num
  have := _root_.IsEssentiallyDistinct.image_homothety
    (0 : EuclideanSpace ℝ (Fin 3)) h8 h
  rw [show (normaliseBody K).carrier
        = AffineMap.homothety (0 : EuclideanSpace ℝ (Fin 3)) ((8 : ℝ)⁻¹) '' K.carrier from
      ConvexSpaceBody.coe_homothety K 0 _,
    show (normaliseBody L).carrier
        = AffineMap.homothety (0 : EuclideanSpace ℝ (Fin 3)) ((8 : ℝ)⁻¹) '' L.carrier from
      ConvexSpaceBody.coe_homothety L 0 _]
  exact this

/-! ## The bodies-variant of `exists_edUsed_rescale_of_edUsed_body` -/

section Bodies

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- **The bodies-variant of `Kakeya.ML2Reduction.exists_edUsed_rescale_of_edUsed_body`**, 's contract: *one index per node, essential distinctness recovered on the far side, the
count paid once at the named constant*.

The existing lemma takes its essentially distinct datum as a **cover** of `ρ`-tubes and needs a
common-chord bridge to compare it with the output tubes.  Here the datum is a family of **bodies**
`Bd j`, each already inside its own output tube `V j`, so the bridge disappears and the whole
geometry collapses to one packing bound:

> `hfibre` — a family of pairwise essentially distinct `Bd`'s all inside one `C_n`-dilate of a
> `ρ`-tube has at most `Cpack` members.

That is deliberately a **parameter**:  defines `centringCoverFibreConstant` from it (and
`centringCountLossConstant R` is that times `spineOuterCountLoss R`), so this lemma is one
substitution away from the specified text.  Everything else — the maximal
essentially distinct selection (`Kakeya.Tube.exists_maximal_essDistinct`), the heavy-overlap
containment (`Kakeya.Tube.tubeOverlapCoreClose`) and the fibre count — is discharged here. -/
theorem exists_edUsed_subfamily_of_edBodies
    {ρ : ℝ≥0} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    {κ : Type*} (t : Finset κ) (V : κ → Tube ρ E) (Bd : κ → ConvexSpaceBody E)
    (hBV : ∀ j ∈ t, Bd j ≤ (V j).toConvexSpaceBody)
    (hED : (t : Set κ).Pairwise
      fun j k ↦ _root_.IsEssentiallyDistinct (Bd j).carrier (Bd k).carrier)
    {Cpack : ℝ}
    (hfibre : ∀ (V₀ : Tube ρ E) (w : Finset κ), w ⊆ t →
      ((w : Set κ).Pairwise
        fun j k ↦ _root_.IsEssentiallyDistinct (Bd j).carrier (Bd k).carrier) →
      (∀ j ∈ w, (Bd j).carrier ⊆ (Kakeya.Tube.dilate V₀
        (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E))).carrier) →
      (w.card : ℝ) ≤ Cpack) :
    ∃ u ⊆ t,
      ((u : Set κ).Pairwise
        fun j k ↦ _root_.IsEssentiallyDistinct (V j).carrier (V k).carrier) ∧
      (t.card : ℝ) ≤ Cpack * (u.card : ℝ) := by
  classical
  obtain ⟨u, hut, hEDV, hmax⟩ := Kakeya.Tube.exists_maximal_essDistinct t V
  set Cn : ℝ := Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) with hCn
  have hCn1 : (1 : ℝ) ≤ Cn := le_of_lt (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C _)
  have hBVc : ∀ j ∈ t, (Bd j).carrier ⊆ (V j).carrier := fun j hj ↦
    SetLike.coe_subset_coe.mpr (hBV j hj)
  have key : ∀ j ∈ t, ∃ k ∈ u,
      (Bd j).carrier ⊆ (Kakeya.Tube.dilate (V k) Cn).carrier := by
    intro j hj
    by_cases hju : j ∈ u
    · exact ⟨j, hju, (hBVc j hj).trans (Tube.subset_dilate (V j) hCn1)⟩
    · obtain ⟨k, hk, hnot⟩ := hmax j hj hju
      have hhalf : (1 / 2 : ℝ≥0∞) * volume (V k).carrier
          < volume ((V k).carrier ∩ (V j).carrier) := by
        have h' : (1 / 2 : ℝ≥0∞) * max (volume (V k).carrier) (volume (V j).carrier)
            < volume ((V k).carrier ∩ (V j).carrier) := lt_of_not_ge hnot
        refine lt_of_le_of_lt ?_ h'
        gcongr
        exact le_max_left _ _
      exact ⟨k, hk, (hBVc j hj).trans
        (Kakeya.Tube.tubeOverlapCoreClose hρ0 hρ1 (V k) (V j) hhalf)⟩
  set A : κ → Finset κ := fun k ↦
    t.filter (fun j ↦ (Bd j).carrier ⊆ (Kakeya.Tube.dilate (V k) Cn).carrier) with hA
  have hcover : t ⊆ u.biUnion A := by
    intro j hj
    obtain ⟨k, hk, hjk⟩ := key j hj
    exact Finset.mem_biUnion.mpr ⟨k, hk, Finset.mem_filter.mpr ⟨hj, hjk⟩⟩
  have hfib : ∀ k ∈ u, ((A k).card : ℝ) ≤ Cpack := by
    intro k _
    refine hfibre (V k) (A k) (Finset.filter_subset _ _)
      (hED.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))) ?_
    intro j hj
    exact (Finset.mem_filter.mp hj).2
  refine ⟨u, hut, hEDV, ?_⟩
  calc (t.card : ℝ) ≤ ((u.biUnion A).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hcover
    _ ≤ ((∑ k ∈ u, (A k).card : ℕ) : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le (t := A)
    _ = ∑ k ∈ u, ((A k).card : ℝ) := by push_cast; ring
    _ ≤ ∑ _k ∈ u, Cpack := Finset.sum_le_sum hfib
    _ = Cpack * (u.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

end Bodies

/-! ## The named contract -/

/-- **The two-radius sibling of `normaliseBody_rescale_le_rescale_of_data`** (the estimate, and untouched).  The transported cover lives at the *contracted* radius `ρ₁ = ρ/C` while the node's
tube is read at `ρ₂ = ρ`, so the discharge of `hnode` is a single `exact` on this one — no radius
bridge, 's Same estimate: the only place the radius enters is the
`‖g‖/8 ≤ ρ₁/8` term, and `(19/64)δ' + ρ₁/8 ≤ 27ρ₂/64` under `ρ₁ ≤ ρ₂`, `δ' ≤ ρ₂`. -/
theorem normaliseBody_rescale_le_rescale_of_data' {δ' ρ₁ ρ₂ : ℝ≥0} (h12 : ρ₁ ≤ ρ₂)
    (hδρ : δ' ≤ ρ₂)
    (T N : Tube δ' (EuclideanSpace ℝ (Fin 3)))
    (hmid : ‖T.midpoint‖ ≤ 1)
    (hfoot : ‖Tube.lineFoot (centringDilate T.midpoint) T.direction - N.midpoint‖
      ≤ (δ' : ℝ) / 4)
    (hdir : ‖T.direction - N.direction‖ ≤ (δ' : ℝ) / 4) :
    normaliseBody (T.rescale ρ₁).toConvexSpaceBody ≤ (N.rescale ρ₂).toConvexSpaceBody := by
  have hρ0 : (0 : ℝ) ≤ (ρ₂ : ℝ) := ρ₂.coe_nonneg
  have hδ0 : (0 : ℝ) ≤ (δ' : ℝ) := δ'.coe_nonneg
  have hδρr : (δ' : ℝ) ≤ (ρ₂ : ℝ) := hδρ
  have h12r : (ρ₁ : ℝ) ≤ (ρ₂ : ℝ) := h12
  have hTm : (T.rescale ρ₁).midpoint = T.midpoint := rfl
  have hTd : (T.rescale ρ₁).direction = T.direction := rfl
  have hNm : (N.rescale ρ₂).midpoint = N.midpoint := rfl
  have hNd : (N.rescale ρ₂).direction = N.direction := rfl
  rw [← SetLike.coe_subset_coe]
  rw [show SetLike.coe (normaliseBody (T.rescale ρ₁).toConvexSpaceBody)
      = normalise 0 '' (T.rescale ρ₁).carrier from normaliseBody_carrier _]
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨s, g, hs, hg, rfl⟩ := (T.rescale ρ₁).exists_decomp_of_mem_carrier hx
  rw [hTm, hTd] at *
  set m : EuclideanSpace ℝ (Fin 3) := T.midpoint with hm
  set d : EuclideanSpace ℝ (Fin 3) := T.direction with hd
  have hdn : ‖d‖ = 1 := T.norm_direction
  set μ : ℝ := ⟪centringDilate m, d⟫ with hμ
  have hfeq : Tube.lineFoot (centringDilate m) d = centringDilate m - μ • d := rfl
  have hmn : ‖centringDilate m‖ ≤ 1 / 8 := by
    rw [show centringDilate m = (8 : ℝ)⁻¹ • m from rfl, norm_smul, norm_inv, Real.norm_ofNat]
    rw [inv_mul_eq_div]
    linarith
  have hμle : |μ| ≤ 1 / 8 := by
    calc |μ| ≤ ‖centringDilate m‖ * ‖d‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 / 8 := by rw [hdn, mul_one]; exact hmn
  set τ : ℝ := μ + s / 8 with hτ
  have hsabs := abs_le.mp hs
  have hμabs := abs_le.mp hμle
  have hτle : |τ| ≤ 1 / 2 := by
    rw [abs_le]; constructor <;> [linarith; linarith]
  refine (N.rescale ρ₂).mem_carrier_of_dist_le
    ((N.rescale ρ₂).midpoint_add_smul_mem_segment (t := τ) hτle) ?_
  rw [dist_eq_norm, hNm, hNd]
  have hkey : normalise 0 (m + s • d + g) - (N.midpoint + τ • N.direction)
      = (Tube.lineFoot (centringDilate m) d - N.midpoint) + τ • (d - N.direction)
        + (8 : ℝ)⁻¹ • g := by
    rw [hfeq, hτ, show normalise 0 (m + s • d + g) = (8 : ℝ)⁻¹ • (m + s • d + g) by
      simp [normalise], show centringDilate m = (8 : ℝ)⁻¹ • m from rfl]
    module
  rw [hkey]
  have hg8 : ‖(8 : ℝ)⁻¹ • g‖ ≤ (ρ₁ : ℝ) / 8 := by
    rw [norm_smul, norm_inv, Real.norm_ofNat, inv_mul_eq_div]
    have : ‖g‖ ≤ (ρ₁ : ℝ) := hg
    linarith
  have hτd : ‖τ • (d - N.direction)‖ ≤ (1 / 2) * ((δ' : ℝ) / 4) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hτle hdir (norm_nonneg _) (by norm_num)
  have hsum := norm_add₃_le (a := Tube.lineFoot (centringDilate m) d - N.midpoint)
    (b := τ • (d - N.direction)) (c := (8 : ℝ)⁻¹ • g)
  calc ‖Tube.lineFoot (centringDilate m) d - N.midpoint + τ • (d - N.direction)
        + (8 : ℝ)⁻¹ • g‖
      ≤ ‖Tube.lineFoot (centringDilate m) d - N.midpoint‖ + ‖τ • (d - N.direction)‖
        + ‖(8 : ℝ)⁻¹ • g‖ := hsum
    _ ≤ (δ' : ℝ) / 4 + (1 / 2) * ((δ' : ℝ) / 4) + (ρ₁ : ℝ) / 8 := by
        gcongr
    _ ≤ (ρ₂ : ℝ) := by linarith

/-! ## The pull-back of the packing bound (PRODUCER-4a)

The three lemmas `hfibre` will be discharged through, all **constant-free** — the ratio `c₀` is a
binder, so nothing here depends on `centringCoverFibreConstant`'s value.  At the site
`c := Tube.tubeOverlapCoreClose.C 3` and `ρ' := ρ / centringCoverRadiusConstant`, the two
hypotheses `hlen`/`hrad` of the last one read `8 · C_n ≤ c₀` and `8 · C · C_n ≤ c₀`, the second
dominating; `c₀ := 16 * centringCoverRadiusConstant * Tube.tubeOverlapCoreClose.C 3` clears both
with a factor two to spare. -/

/-- Essential distinctness pulls back through `normalise 0`. -/
theorem essDistinct_of_normaliseBody {K L : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    (h : _root_.IsEssentiallyDistinct (normaliseBody K).carrier (normaliseBody L).carrier) :
    _root_.IsEssentiallyDistinct K.carrier L.carrier := by
  have h8 : ((8 : ℝ)) ≠ 0 := by norm_num
  have h8i : ((8 : ℝ)⁻¹) ≠ 0 := by norm_num
  rw [show (normaliseBody K).carrier
        = AffineMap.homothety (0 : EuclideanSpace ℝ (Fin 3)) ((8 : ℝ)⁻¹) '' K.carrier from
      ConvexSpaceBody.coe_homothety K 0 _,
    show (normaliseBody L).carrier
        = AffineMap.homothety (0 : EuclideanSpace ℝ (Fin 3)) ((8 : ℝ)⁻¹) '' L.carrier from
      ConvexSpaceBody.coe_homothety L 0 _] at h
  have := _root_.IsEssentiallyDistinct.image_homothety
    (0 : EuclideanSpace ℝ (Fin 3)) h8 h
  have hinv : ∀ A : Set (EuclideanSpace ℝ (Fin 3)),
      AffineMap.homothety (0 : EuclideanSpace ℝ (Fin 3)) (8 : ℝ) ''
        (AffineMap.homothety (0 : EuclideanSpace ℝ (Fin 3)) ((8 : ℝ)⁻¹) '' A) = A := by
    intro A
    have := Kakeya.homothety_inv_image_homothety_image (0 : EuclideanSpace ℝ (Fin 3)) h8i A
    simpa using this
  rwa [hinv K.carrier, hinv L.carrier] at this

/-- `Tube.dilate`'s segment in midpoint–direction form. -/
theorem segment_homothety_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {δ : ℝ≥0} (T : Tube δ E) (r : ℝ) :
    segment ℝ (AffineMap.homothety T.center r T.x) (AffineMap.homothety T.center r T.y)
      = segment ℝ (T.center - (r / 2 : ℝ) • T.direction)
          (T.center + (r / 2 : ℝ) • T.direction) := by
  congr 1 <;>
  · simp only [AffineMap.homothety_apply, Tube.center, Tube.direction, midpoint_eq_smul_add,
      vsub_eq_sub, vadd_eq_add]
    match_scalars <;> (norm_num [invOf_eq_inv]; try ring)

/-- **The pull-back the packing bound needs.**  `normalise 0` contracts by `8`, so a family whose
*images* sit inside the `c`-dilate of a `ρ`-tube has its members inside the `c₀`-dilate of a
`ρ'`-tube on the `8`-scaled axis, for any `c₀` dominating both `8 c` (the core) and
`8 c ρ / ρ'` (the radius).  These two inequalities are what fix `c₀`; nothing else does. -/
theorem carrier_subset_dilate_of_normaliseBody_subset_dilate
    {ρ' ρ : ℝ≥0} {c c₀ : ℝ} (hc0 : 0 < c) (hc₀0 : 0 < c₀)
    (hlen : 8 * c ≤ c₀) (hrad : 8 * (c * (ρ : ℝ)) ≤ c₀ * (ρ' : ℝ))
    (U : Tube ρ' (EuclideanSpace ℝ (Fin 3))) (V₀ : Tube ρ (EuclideanSpace ℝ (Fin 3)))
    (hsub : (normaliseBody U.toConvexSpaceBody).carrier ⊆ (Kakeya.Tube.dilate V₀ c).carrier) :
    U.carrier ⊆ (Kakeya.Tube.dilate
      (Tube.ofMidpointDirection ρ' ((8 : ℝ) • V₀.center) V₀.direction V₀.norm_direction)
      c₀).carrier := by
  set d : EuclideanSpace ℝ (Fin 3) := V₀.direction with hd
  set T' : Tube ρ' (EuclideanSpace ℝ (Fin 3)) :=
    Tube.ofMidpointDirection ρ' ((8 : ℝ) • V₀.center) d V₀.norm_direction with hT'
  have hT'c : T'.center = (8 : ℝ) • V₀.center := by
    rw [hT', Tube.center, Tube.ofMidpointDirection]
    simp only [Tube.mk'_x, Tube.mk'_y, midpoint_eq_smul_add]
    match_scalars <;> (norm_num [invOf_eq_inv]; try ring)
  have hT'd : T'.direction = d := by
    rw [hT']; exact Tube.direction_ofMidpointDirection' _ _ _
  rw [Kakeya.Tube.dilate_carrier_eq_cthickening _ hc₀0, segment_homothety_eq, hT'c, hT'd]
  rw [Kakeya.Tube.dilate_carrier_eq_cthickening _ hc0, segment_homothety_eq, ← hd] at hsub
  intro x hx
  have hxn : normalise 0 x ∈ (normaliseBody U.toConvexSpaceBody).carrier := by
    rw [normaliseBody_carrier]; exact ⟨x, hx, rfl⟩
  have hmem := hsub hxn
  set S : Set (EuclideanSpace ℝ (Fin 3)) :=
    segment ℝ (V₀.center - (c / 2) • d) (V₀.center + (c / 2) • d) with hS
  have hScomp : IsCompact S := isCompact_segment
  have hSne : S.Nonempty := ⟨V₀.center - (c / 2) • d, left_mem_segment _ _ _⟩
  obtain ⟨y, hyS, hy⟩ := hScomp.exists_infEDist_eq_edist hSne (normalise 0 x)
  have hle : dist (normalise 0 x) y ≤ c * (ρ : ℝ) := by
    have h1 : Metric.infEDist (normalise 0 x) S ≤ ENNReal.ofReal (c * (ρ : ℝ)) := by
      rwa [Metric.mem_cthickening_iff] at hmem
    rw [hy, edist_dist] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
  obtain ⟨t, ht, hyt⟩ : ∃ t : ℝ, |t| ≤ c / 2 ∧ y = V₀.center + t • d := by
    rw [hS, segment_eq_image] at hyS
    obtain ⟨θ, hθ, hyθ⟩ := hyS
    refine ⟨(θ - 1 / 2) * c, ?_, ?_⟩
    · rw [abs_mul, abs_of_pos hc0]
      have hθ' : |θ - 1 / 2| ≤ 1 / 2 := by
        rw [abs_le]; constructor <;> [linarith [hθ.1]; linarith [hθ.2]]
      nlinarith
    · rw [← hyθ]; module
  refine Metric.mem_cthickening_of_dist_le x ((8 : ℝ) • y) (c₀ * (ρ' : ℝ)) _ ?_ ?_
  · rw [hyt, smul_add, smul_smul, segment_eq_image]
    have habs := abs_le.mp ht
    refine ⟨(8 * t) / c₀ + 1 / 2, ⟨?_, ?_⟩, ?_⟩
    · have hb1 : -(c₀ / 2) ≤ 8 * t := by nlinarith
      have hd1 : -(1 / 2 : ℝ) ≤ (8 * t) / c₀ := by
        rw [le_div_iff₀ hc₀0]; nlinarith
      linarith
    · have hb2 : 8 * t ≤ c₀ / 2 := by nlinarith
      have hd2 : (8 * t) / c₀ ≤ 1 / 2 := by
        rw [div_le_iff₀ hc₀0]; nlinarith
      linarith
    · have hc₀ne : c₀ ≠ 0 := ne_of_gt hc₀0
      field_simp
      match_scalars <;> (field_simp; try ring)
  · have h8 : dist x ((8 : ℝ) • y) = 8 * dist (normalise 0 x) y := by
      rw [dist_eq_norm, dist_eq_norm,
        show normalise 0 x - y = (8 : ℝ)⁻¹ • (x - (8 : ℝ) • y) by
          simp only [normalise, sub_zero]; module,
        norm_smul, norm_inv, Real.norm_ofNat]
      ring
    rw [h8]
    nlinarith [dist_nonneg (x := normalise 0 x) (y := y)]

/-! ## PRODUCER-4 — `hfibre` is a theorem -/

/-- **The packing bound, proved**.

Pull the clause back through the similarity — essential distinctness survives exactly
(`essDistinct_of_normaliseBody`), and the containment becomes one in a dilate of a `ρ'`-tube on the
`8`-scaled axis (`carrier_subset_dilate_of_normaliseBody_subset_dilate`) — then count there with
the existing `Tube.essDistinctTubesInSelfDilate` at
`c₀ = 16 · centringCoverRadiusConstant · Tube.tubeOverlapCoreClose.C 3`, and pad to the named
constant by `le_add_self` (there is no lower bound for
`Tube.essDistinctTubesInSelfDilate.C`, which is why the constant is `1 + …`).

`hrad` is the only numeric input; it is the radius half of `c₀`'s two defining inequalities, and it
is free at the site, where `ρ' = ρ / centringCoverRadiusConstant`. -/
theorem card_le_centringCoverFibreConstant_of_normaliseBody
    {ρ' ρ : ℝ≥0} (hρ'0 : 0 < ρ') (hρ'1 : ρ' ≤ 1)
    (hrad : 8 * ((Tube.tubeOverlapCoreClose.C 3) * (ρ : ℝ))
      ≤ (16 * ((centringCoverRadiusConstant : ℝ≥0) : ℝ)
          * (Tube.tubeOverlapCoreClose.C 3)) * (ρ' : ℝ))
    {κ₀ : Type*} (w : Finset κ₀) (U : κ₀ → Tube ρ' (EuclideanSpace ℝ (Fin 3)))
    (V₀ : Tube ρ (EuclideanSpace ℝ (Fin 3)))
    (hED : (w : Set κ₀).Pairwise fun j k ↦ _root_.IsEssentiallyDistinct
      (normaliseBody (U j).toConvexSpaceBody).carrier
      (normaliseBody (U k).toConvexSpaceBody).carrier)
    (hsub : ∀ j ∈ w, (normaliseBody (U j).toConvexSpaceBody).carrier
      ⊆ (Kakeya.Tube.dilate V₀ (Tube.tubeOverlapCoreClose.C 3)).carrier) :
    (w.card : ℝ) ≤ (centringCoverFibreConstant : ℝ) := by
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hCn1 : (1 : ℝ) < Tube.tubeOverlapCoreClose.C 3 := Tube.tubeOverlapCoreClose.one_lt_C 3
  have hCr : ((centringCoverRadiusConstant : ℝ≥0) : ℝ) = 2 := by
    unfold centringCoverRadiusConstant; norm_num
  have hc00 : (0 : ℝ) < 16 * ((centringCoverRadiusConstant : ℝ≥0) : ℝ)
      * (Tube.tubeOverlapCoreClose.C 3) := by rw [hCr]; nlinarith
  have hc01 : (1 : ℝ) ≤ 16 * ((centringCoverRadiusConstant : ℝ≥0) : ℝ)
      * (Tube.tubeOverlapCoreClose.C 3) := by rw [hCr]; nlinarith
  have hlen : 8 * (Tube.tubeOverlapCoreClose.C 3)
      ≤ 16 * ((centringCoverRadiusConstant : ℝ≥0) : ℝ)
        * (Tube.tubeOverlapCoreClose.C 3) := by rw [hCr]; nlinarith
  have hUT : ∀ j ∈ w, (U j).carrier ⊆ (Kakeya.Tube.dilate
      (Tube.ofMidpointDirection ρ' ((8 : ℝ) • V₀.center) V₀.direction V₀.norm_direction)
      (16 * ((centringCoverRadiusConstant : ℝ≥0) : ℝ)
        * (Tube.tubeOverlapCoreClose.C 3))).carrier := fun j hj ↦
    carrier_subset_dilate_of_normaliseBody_subset_dilate (by linarith) hc00 hlen hrad
      (U j) V₀ (hsub j hj)
  have hEDU : (w : Set κ₀).Pairwise
      fun j k ↦ _root_.IsEssentiallyDistinct (U j).carrier (U k).carrier := fun j hj k hk hjk ↦
    essDistinct_of_normaliseBody (hED hj hk hjk)
  have hcount := Tube.essDistinctTubesInSelfDilate (E := EuclideanSpace ℝ (Fin 3))
    hc01 hρ'0 hρ'1 _ w U hEDU hUT
  rw [hfr] at hcount
  have hpad : (Tube.essDistinctTubesInSelfDilate.C 3
      (16 * ((centringCoverRadiusConstant : ℝ≥0) : ℝ)
        * (Tube.tubeOverlapCoreClose.C 3)) : ℝ≥0) ≤ centringCoverFibreConstant := by
    rw [centringCoverFibreConstant_eq]; exact le_add_self
  have hN : (w.card : ℝ≥0) ≤ centringCoverFibreConstant := by
    have h : (w.card : ℝ≥0∞) ≤ (centringCoverFibreConstant : ℝ≥0∞) :=
      hcount.trans (by exact_mod_cast hpad)
    exact_mod_cast h
  exact_mod_cast hN

/-! ## The `CountTransport` producer at the specified shape -/

/-- **A7 — the count clause transports to the centred representatives** (
as re-cut ).

The conclusion is `Kakeya.ML2Reduction.Lemma91At`'s count clause at `(s', U')` **verbatim**, with
the bare `ρ^{-2-ζ}`; the antecedent is the caller's `hcanon` at the contracted radius `ρ / C` and
at the named count constant.  The generic form takes both as binders; the site-level
`countTransport_of_contractedCover` instantiates them at `centringCoverRadiusConstant` and at
`centringCountLossConstant R` — the arity matters, `R` being the one bound by `hsit`.

The two geometric binders are what the canonical-cover cover interface does not currently export:

* `hmid`, `hfoot`, `hdir` — `‖midpoint‖ ≤ 1` and the two line-parameter conjuncts of
  `Kakeya.VeryNotSticky.exists_centredRepresentatives_data`, from which the node containment (the
  old `hnode`) is proved by `normaliseBody_rescale_le_rescale_of_data'`;
* `hrad` — one scalar inequality, the radius half of `c₀`'s definition, free at
  `C = centringCoverRadiusConstant`; it replaces the old `hfibre`, which is now the theorem
  `card_le_centringCoverFibreConstant_of_normaliseBody`.

**Where `c₀`'s other defining inequality goes.**  `c₀` is fixed by two: the core half
`8 · c ≤ c₀` and the radius half `8 · (c · ρ) ≤ c₀ · ρ'`.  Only the radius half is carried here,
because only it mentions the scales: the core half is discharged **inside**
`card_le_centringCoverFibreConstant_of_normaliseBody` (its `hlen`), automatically from
`centringCoverRadiusConstant = 2`, and it involves neither `ρ'` nor `C`.

Everything else is discharged: the essential distinctness of the images is exact
(`essDistinct_normaliseBody`), the all-used clause is free (`node_le_rescale`: a node is a
unit-core `δ'`-tube and `δ' ≤ ρ`), and the count is the own display
(`count_le_of_contracted_radius`) after the single packing division. -/
theorem countClause_of_contractedCover
    {b δt δ' : ℝ≥0} {R : ℝ}
    (hsit : Tube.IsRescalingSituation b δt δ' R 3) (hR : 0 < R)
    (hτσ : (δt : ℝ) / (b : ℝ) ≤ 4 * (δ' : ℝ))
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3)))
    {C : ℝ≥0} (hC1 : 1 ≤ C)
    {ζ : ℝ} (hζ : 0 ≤ 2 + ζ)
    {α : Type u} (s' : Finset α)
    (Z' : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3)))
    (U' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3)))
    (hsub : ∀ i ∈ s', (Z' i).carrier ⊆ T₀.carrier)
    {ρ : ℝ≥0} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hδρ : δ' ≤ ρ / C)
    (hmid : ∀ i ∈ s',
      ‖(outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toTube.midpoint‖ ≤ 1)
    (hfoot : ∀ i ∈ s', ‖Tube.lineFoot
        (centringDilate (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toTube.midpoint)
        ((outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toTube.direction)
        - (U' i).toTube.midpoint‖ ≤ (δ' : ℝ) / 4)
    (hdir : ∀ i ∈ s',
      ‖(outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toTube.direction
        - (U' i).toTube.direction‖ ≤ (δ' : ℝ) / 4)
    (hrad : 8 * ((Tube.tubeOverlapCoreClose.C 3) * (ρ : ℝ))
      ≤ (16 * ((centringCoverRadiusConstant : ℝ≥0) : ℝ)
          * (Tube.tubeOverlapCoreClose.C 3)) * ((ρ / C : ℝ≥0) : ℝ)) :
    (∃ (κ₀ : Type u) (t : Finset κ₀) (W : κ₀ → Tube (ρ / C) (EuclideanSpace ℝ (Fin 3))),
      ((t : Set κ₀).Pairwise
        fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
      (∀ j ∈ t, ∃ i ∈ s',
        (spineFamily (spineRescaleUnit hsit.pos_ambient T₀ hR) Z' i).toConvexSpaceBody
          ≤ (W j).toConvexSpaceBody) ∧
      (centringCountLossConstant R : ℝ)
        * ((ρ / C : ℝ≥0) : ℝ) ^ (-2 - ζ) ≤ (t.card : ℝ)) →
    (∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
      ((tρ : Set κ).Pairwise
        fun j k ↦ _root_.IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
      (∀ j ∈ tρ, ∃ i ∈ s', (U' i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
      (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) := by
  classical
  rintro ⟨κ₀, t, W, hEDW, hused, hcount⟩
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hCr1 : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC1
  have hCpos : (0 : ℝ) < (C : ℝ) := by linarith
  have hρCcoe : ((ρ / C : ℝ≥0) : ℝ) = (ρ : ℝ) / (C : ℝ) := NNReal.coe_div _ _
  have hρC0 : 0 < ρ / C := by
    rw [← NNReal.coe_pos, hρCcoe]
    have : (0 : ℝ) < (ρ : ℝ) := hρ0
    positivity
  have hρCle : ρ / C ≤ ρ := by
    rw [← NNReal.coe_le_coe, hρCcoe]
    exact div_le_self ρ.coe_nonneg hCr1
  have hρC1 : ρ / C ≤ 1 := hρCle.trans hρ1
  have hFpos : (0 : ℝ) < (centringCoverFibreConstant : ℝ) := by
    have h1 : (1 : ℝ) ≤ (centringCoverFibreConstant : ℝ) := by
      exact_mod_cast one_le_centringCoverFibreConstant
    linarith
  have hSpos : (0 : ℝ) < (ML2Reduction.spineOuterCountLoss R : ℝ) :=
    lt_of_lt_of_le zero_lt_one (ML2Reduction.one_le_spineOuterCountLoss R)
  have hpow : (0 : ℝ) < ((ρ / C : ℝ≥0) : ℝ) ^ (-2 - ζ) :=
    Real.rpow_pos_of_pos (by rw [hρCcoe]; positivity) _
  -- `t` is nonempty, so `α` is inhabited
  have htne : t.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    rw [hemp] at hcount
    simp only [Finset.card_empty, Nat.cast_zero] at hcount
    have hCC : (0 : ℝ) < (centringCountLossConstant R : ℝ) := by
      rw [centringCountLossConstant_eq]; nlinarith
    nlinarith
  obtain ⟨j₀, hj₀⟩ := htne
  obtain ⟨i₀, hi₀, -⟩ := hused j₀ hj₀
  haveI : Nonempty α := ⟨i₀⟩
  -- STAGE 1: move the essentially distinct datum from the cover tubes to the outer cores,
  -- with the witness exposed (`_data`,  route (α)).
  set K : ℝ := max 1 (8 * R / 5) with hK
  have hK1 : (1 : ℝ) ≤ K := le_max_left _ _
  obtain ⟨u, f, hut, hfs, hEDV, hcard1⟩ :=
    ML2Reduction.exists_edUsed_rescale_of_edUsed_body_data (E := EuclideanSpace ℝ (Fin 3))
      hρC0 hρC1 hδρ hK1
      (fun i ↦ (ML2Reduction.spineFamily
        (ML2Reduction.spineRescaleUnit hsit.pos_ambient T₀ hR) Z' i).toConvexSpaceBody)
      (fun i ↦ (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toTube) s'
      (fun i hi ↦ by
        obtain ⟨p, hp, q, hq, hpq⟩ := ML2Reduction.exists_chord_spineFamily hsit.pos_ambient
          hsit.ambient_le_one hR T₀ Z' hsub i hi
        exact ⟨p, hp, q, hq, (ML2Reduction.chordThreshold_le_rescaledChord hR).trans hpq⟩)
      (fun i hi ↦ ML2Reduction.spineImage_le_outerShadedTube hfr hsit hR hτσ T₀ (Z' i)
        (hsub i hi))
      t W hEDW hused
  -- STAGE 2: normalise and select.  `Bd j` is the image of the term stage 1 exposes.
  set V : κ₀ → Tube ρ (EuclideanSpace ℝ (Fin 3)) :=
    fun j ↦ (U' (f j)).toTube.rescale ρ with hV
  set Bd : κ₀ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    fun j ↦ normaliseBody
      (((outerFamily hsit.pos_ambient T₀ hR δ' Z' (f j)).toTube).rescale (ρ / C)).toConvexSpaceBody
      with hBd
  have hBV : ∀ j ∈ u, Bd j ≤ (V j).toConvexSpaceBody := by
    intro j hj
    exact normaliseBody_rescale_le_rescale_of_data' hρCle (hδρ.trans hρCle)
      ((outerFamily hsit.pos_ambient T₀ hR δ' Z' (f j)).toTube) ((U' (f j)).toTube)
      (hmid (f j) (hfs j hj)) (hfoot (f j) (hfs j hj)) (hdir (f j) (hfs j hj))
  have hEDb : (u : Set κ₀).Pairwise
      fun j k ↦ _root_.IsEssentiallyDistinct (Bd j).carrier (Bd k).carrier := by
    intro j hj k hk hjk
    exact essDistinct_normaliseBody (hEDV hj hk hjk)
  obtain ⟨u', hu'u, hEDV', hcard2⟩ :=
    exists_edUsed_subfamily_of_edBodies hρ0 hρ1 u V Bd hBV hEDb
      (Cpack := (centringCoverFibreConstant : ℝ))
      (fun V₀ w _ hw1 hw2 ↦ by
        have hfr3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
        rw [hfr3] at hw2
        exact card_le_centringCoverFibreConstant_of_normaliseBody hρC0 hρC1 hrad w
          (fun j ↦ ((outerFamily hsit.pos_ambient T₀ hR δ' Z' (f j)).toTube).rescale (ρ / C))
          V₀ hw1 hw2)
  refine ⟨κ₀, u', V, hEDV', fun j hj ↦
    ⟨f j, hfs j (hu'u hj), node_le_rescale (hδρ.trans hρCle) (U' (f j))⟩, ?_⟩
  -- the count: stage 1 charges `Cb ≤ spineOuterCountLoss R`, stage 2 charges the fibre constant,
  -- and the antecedent supplies their product.
  have hCb : (Tube.essDistinctTubesInSelfDilate.C 3 (ML2Reduction.outerTransportRatio 3 K) : ℝ)
      ≤ (ML2Reduction.spineOuterCountLoss R : ℝ) := by
    have h : Tube.essDistinctTubesInSelfDilate.C 3 (ML2Reduction.outerTransportRatio 3 K)
        ≤ ML2Reduction.spineOuterCountLoss R := le_add_self
    exact_mod_cast h
  rw [hfr] at hcard1
  have hstep : (ML2Reduction.spineOuterCountLoss R : ℝ)
      * ((centringCoverFibreConstant : ℝ) * ((ρ / C : ℝ≥0) : ℝ) ^ (-2 - ζ))
      ≤ (ML2Reduction.spineOuterCountLoss R : ℝ)
        * ((centringCoverFibreConstant : ℝ) * (u'.card : ℝ)) := by
    calc (ML2Reduction.spineOuterCountLoss R : ℝ)
          * ((centringCoverFibreConstant : ℝ) * ((ρ / C : ℝ≥0) : ℝ) ^ (-2 - ζ))
        = (centringCountLossConstant R : ℝ) * ((ρ / C : ℝ≥0) : ℝ) ^ (-2 - ζ) := by
          rw [centringCountLossConstant_coe, centringCoverFibreConstant_coe]; ring
      _ ≤ (t.card : ℝ) := hcount
      _ ≤ (Tube.essDistinctTubesInSelfDilate.C 3 (ML2Reduction.outerTransportRatio 3 K) : ℝ)
            * (u.card : ℝ) := hcard1
      _ ≤ (ML2Reduction.spineOuterCountLoss R : ℝ) * (u.card : ℝ) := by
          exact mul_le_mul_of_nonneg_right hCb (Nat.cast_nonneg _)
      _ ≤ (ML2Reduction.spineOuterCountLoss R : ℝ)
            * ((centringCoverFibreConstant : ℝ) * (u'.card : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hcard2 hSpos.le
  have hfin : ((ρ / C : ℝ≥0) : ℝ) ^ (-2 - ζ) ≤ (u'.card : ℝ) := by
    have h1 := le_of_mul_le_mul_left hstep hSpos
    exact le_of_mul_le_mul_left h1 hFpos
  exact count_le_of_contracted_radius hρ0 hC1 (Λ := 1) le_rfl hζ (by rw [one_mul]; exact hfin)

/-! ## the bodies-variant's hypothesis list, on a real family -/

/-! ## The producer at the specified names: `CountTransport` verbatim -/

/-- **A7 at the specified names** — the conclusion is `Kakeya.VeryNotSticky.CountTransport` as the GC
owner re-cut it, **verbatim**, so a caller discharges its `hct` by one application.

Both constants are consumed **by name**: the radius is contracted at
`centringCoverRadiusConstant` (which is what `CountTransport` itself names) and the packing bound
is stated at `centringCoverFibreConstant`.

**No count comparison is needed.**   puts `centringCountLossConstant R` on
`CountTransport`'s own antecedent (`spineOuterCountLoss` occurs zero times in the definition), and
 makes that constant the *product* `spineOuterCountLoss R * centringCoverFibreConstant` —
one factor for each of the transport's two stages — so both divisions cancel and there is nothing
left to pay.  The `hloss` binder of  — a comparison of the then-argument-free
count constant against `spineOuterCountLoss R` — is therefore **retired**: it was stated at an
arity that no longer exists, and at the specified one it is not merely dischargeable but unnecessary. -/
theorem countTransport_of_contractedCover
    {b δt δ' : ℝ≥0} {R : ℝ}
    (hsit : Tube.IsRescalingSituation b δt δ' R 3) (hR : 0 < R)
    (hτσ : (δt : ℝ) / (b : ℝ) ≤ 4 * (δ' : ℝ))
    (hδ'0 : 0 < δ') {ϖ ζ : ℝ} (hϖ : 0 ≤ ϖ) (hζ : 0 ≤ 2 + ζ)
    (hthr : δ' ^ ϖ ≤ 1 / 2)
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} (s' : Finset α)
    (Z' : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3)))
    (U' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3)))
    (hsub : ∀ i ∈ s', (Z' i).carrier ⊆ T₀.carrier)
    (hmid : ∀ i ∈ s',
      ‖(outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toTube.midpoint‖ ≤ 1)
    (hfoot : ∀ i ∈ s', ‖Tube.lineFoot
        (centringDilate (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toTube.midpoint)
        ((outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toTube.direction)
        - (U' i).toTube.midpoint‖ ≤ (δ' : ℝ) / 4)
    (hdir : ∀ i ∈ s',
      ‖(outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toTube.direction
        - (U' i).toTube.direction‖ ≤ (δ' : ℝ) / 4)
    :
    CountTransport hsit hR T₀ 0 ϖ ζ s' Z' U' := by
  intro ρ hρ
  have hδ1 : δ' ≤ 1 := by
    have := hsit.out_le_quarter
    rw [← NNReal.coe_le_coe]
    push_cast
    linarith
  have hρ0 : 0 < ρ := lt_of_lt_of_le (NNReal.rpow_pos hδ'0) hρ.1
  have hρ1 : ρ ≤ 1 := hρ.2.trans (NNReal.rpow_le_one hδ1 hϖ)
  have hC1 : (1 : ℝ≥0) ≤ centringCoverRadiusConstant := by
    unfold centringCoverRadiusConstant; norm_num
  -- `δ'` is below the widened lower endpoint, hence below `ρ / C` throughout the window
  have hδρ : δ' ≤ ρ / centringCoverRadiusConstant := by
    refine le_trans (le_div_rpow_one_sub hδ'0 hthr) ?_
    rw [edWindowContractionConstant_eq_centringCoverRadiusConstant]
    exact div_le_div_of_nonneg_right hρ.1 centringCoverRadiusConstant_pos.le
  -- `hrad` at the site: `C = centringCoverRadiusConstant = 2`, so the right side is `16 C_n ρ`
  have hCn0 : (0 : ℝ) < Tube.tubeOverlapCoreClose.C 3 :=
    lt_trans zero_lt_one (Tube.tubeOverlapCoreClose.one_lt_C 3)
  have hCr : ((centringCoverRadiusConstant : ℝ≥0) : ℝ) = 2 := by
    unfold centringCoverRadiusConstant; norm_num
  have hdivc : ((ρ / centringCoverRadiusConstant : ℝ≥0) : ℝ) = (ρ : ℝ) / 2 := by
    rw [NNReal.coe_div, hCr]
  have hrad : 8 * ((Tube.tubeOverlapCoreClose.C 3) * (ρ : ℝ))
      ≤ (16 * ((centringCoverRadiusConstant : ℝ≥0) : ℝ)
          * (Tube.tubeOverlapCoreClose.C 3))
        * ((ρ / centringCoverRadiusConstant : ℝ≥0) : ℝ) := by
    rw [hdivc, hCr]
    nlinarith [ρ.coe_nonneg]
  exact countClause_of_contractedCover hsit hR hτσ T₀ hC1 hζ s' Z' U' hsub hρ0 hρ1 hδρ
    hmid hfoot hdir hrad

/-! ## `hnode`: the triangle estimate `exists_centredRepresentatives_data` discharges -/

end Kakeya.VeryNotSticky

end

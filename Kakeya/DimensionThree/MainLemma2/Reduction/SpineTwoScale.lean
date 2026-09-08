/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factoring.RhoTubesUndilated
public import Kakeya.ChainUniform

/-!
# The two-scale multiplicity split at the top of the proof of GWZ Main Lemma 2

Blueprint GWZ, "Proof of Main Lemma~\ref{lemmain2}", the step

> We apply Lemma `shadingMultiplicityEstimateForRhoTubes` to `(𝕋,Y)` at scale `τ` and then apply
> it again to `(𝕋_τ, Y_{𝕋_τ})` at scale `θ`.  We obtain some `≈ 1` refinements of these sets of
> tubes, but we will abuse notation and continue to use the same names.

producing the two displays

* `boundMuTTYByTripleProductMainLem2`:
  `μ(𝕋,Y) ⪅ μ(𝕋[T_τ], Y) · μ(𝕋_τ[T_θ], Y_{𝕋_τ}) · μ(𝕋_θ, Y_{𝕋_θ})`
  for all `T_τ ∈ 𝕋_τ` and `T_θ ∈ 𝕋_θ`;
* `lambdabounds`: `λ(𝕋_θ, Y_{𝕋_θ}), λ(𝕋_τ, Y_{𝕋_τ}) ⪆ λ(𝕋,Y)`.

## Lean cannot abuse notation

Each application of GWZ Lemma 5.11 replaces the pair it is applied to by a refinement, and the
blueprint then reuses the old names.  The statements below are therefore *existence* statements:
they produce the refined shadings and the retained subfamilies explicitly, in the idiom of
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_subfamily`
(`Kakeya/DimensionThree/MainLemma2/AScaleResidues.lean`) and of the one- and two-scale certificate
producers of `Kakeya/DimensionThree/MainLemma1/`.  Four shadings occur and they are *four different
objects*:

| blueprint name | here | what it is |
| --- | --- | --- |
| `Y` (after both applications) | `Y'` | the refinement of the given `δ`-shading |
| `Y_{𝕋_τ}` (first application) | `Yτ` | the `τ`-shading the first application manufactures |
| `Y_{𝕋_τ}` (after the second) | `Yτ'` | its refinement, which is what `μ(𝕋_τ[T_θ], ·)` is read on |
| `Y_{𝕋_θ}` | `Yθ` | the `θ`-shading the second application manufactures |

`Yτ'` and `Yτ` are *not* interchangeable: the first display reads the coarse factor of the first
application on `Yτ` and the middle factor of the second application on `Yτ'`, and
`ShadedBody.multiplicity` is monotone in neither direction.  The conjunct
`(Yτ' j).shade ⊆ (Yτ j).shade` records the one relation between them that the proof establishes.

## The `⪅` is a concrete constant, and it is carried

`ShadedBody.shadingMultiplicityEstimateForRhoTubes` is proved in this development at the constant
`ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C n N σ 1`, named
`Kakeya.ML2Reduction.spineScaleLoss` below.  It is **not** absolute: it grows with the cardinality
`N` of the inner family and with `σ⁻¹`.  The two-scale loss is therefore the product
`spineScaleLoss n |𝕋| δ * spineScaleLoss n |𝕋_τ'| τ`, with `|𝕋_τ'|` the cardinality of the
*retained* `τ`-family; the conclusion carries `|𝕋_τ'| ≤ |𝕋_τ|` so that a caller can bound the
second factor by `ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C_leApprox`, which is
monotone in `N`.  Nothing here pretends the loss is `1`.

## Hypotheses

Beyond the scale hierarchy `0 < δ ≤ τ ≤ θ ≤ 1` and the two parent structures, exactly one
geometric hypothesis is carried at each of the two levels: the inner family of each application
must lie in the closed unit ball.  For the `δ`-tubes this is "`𝕋` is a set of `δ`-tubes in `B₁`",
the standing hypothesis of Main Lemma 2.  For the `τ`-tubes it is the same condition one level up,
and it is **forced by the Lean form of Lemma 5.11**, whose `hball` feeds
`ShadedBody.FactorFamily.InnerIsDiscretizedAtScale.subset_unitBall`; the blueprint does not display
it because GWZ work in `B₁` up to absolute constants throughout.  It is not vacuous and it is not a
disguised difficulty: it is the hypothesis the abandoned donor branch's `exists_tripleProduct`
carried in the identical position, and `StickyKakeya.exists_translate_subfamily_unit_ball` is the
route by which a caller holding only `𝕋_τ ⊆ B_R` supplies it.

No uniformity, no Frostman, no Katz--Tao, and no density hypothesis is used: the split below is
what the factoring estimate gives on a bare nested pair of parent families.

## Main statements

* `Kakeya.ML2Reduction.exists_spineOneScale`: one application of GWZ Lemma 5.11 in
  named-output form;
* `Kakeya.ML2Reduction.exists_spineTwoScale`: the two-scale split, `boundMuTTYByTripleProductMainLem2`
  and `lambdabounds` together;
* `Kakeya.ML2Reduction.exists_spineTwoScale_ofChain`: the same for two levels `a ≤ b` of a
  `Tube.ChainCoverSystem`, which is the hierarchy vocabulary the assembly carries
  (`Tube.GridCoverSystem.toChain`, `Tube.UniformTubeSet.toChain`).
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ConvexSpaceBody ShadedBody

namespace Kakeya.ML2Reduction

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-! ## The loss of one application -/

/-- **The loss constant of one application of GWZ Lemma 5.11** at ambient dimension `n`, inner
family of cardinality `N` and inner scale `σ`.

This is `ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C n N σ 1`, the constant at which
`ShadedBody.shadingMultiplicityEstimateForRhoTubesUndilated` is proved.  It is at least `1`
(`Kakeya.ML2Reduction.one_le_spineScaleLoss`) and it is subpolynomial jointly in `N` and `σ⁻¹`
(`ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C_leApprox`), which is the only sense in
which the blueprint's `⪅` is `≈ 1`. -/
noncomputable def spineScaleLoss (n N : ℕ) (σ : ℝ≥0) : ℝ≥0 :=
  ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C n N σ 1

/-- The loss of one application is at least `1`, so its inverse is a genuine loss. -/
theorem one_le_spineScaleLoss (n N : ℕ) (σ : ℝ≥0) : 1 ≤ spineScaleLoss n N σ :=
  ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.one_le_C n N σ 1

theorem spineScaleLoss_ne_zero (n N : ℕ) (σ : ℝ≥0) : spineScaleLoss n N σ ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_spineScaleLoss n N σ))

/-! ## One application of GWZ Lemma 5.11, in named-output form -/

open Classical in
/-- **One passage across two scales** (blueprint `shadingMultiplicityEstimateForRhoTubes`, GWZ
Lemma 5.11), with the produced objects named.

For a family `(𝕍, Z)` of shaded `σ`-tubes in `B₁`, a family `(W_k)_{k ∈ t}` of `ρ`-tubes with
`σ ≤ ρ ≤ 1`, and a parent map `p` placing each `V i` inside `W (p i)`, the estimate returns

* a retained subfamily `t' ⊆ t` of parents;
* a shading `Z_ρ` of the parents, with the same tubes;
* a refinement `Z'` of the given shading, with the same tubes;

satisfying the outer fullness bound `C⁻¹ λ(𝕍, Z) ≤ λ(𝕍_ρ|_{t'}, Z_ρ)`, the refinement bound, the
pointwise containment `Z' i ⊆ Z_ρ (p i)`, and the product estimate
`μ(𝕍, Z) ≤ C · μ(𝕍_ρ|_{t'}, Z_ρ) · μ(𝕍[W_k], Z')` at every retained parent `k ∈ t'`.

This is `ShadedBody.shadingMultiplicityEstimateForRhoTubesUndilated` with the outer family read
through a parent map rather than through a `ShadedBody.FactorFamily`, with the two output shadings
presented as *total* families of `ShadedTube` (off the retained sets they carry the empty shade),
and with the fibre of the product estimate simplified: for `k ∈ t'` the fibre
`{i ∈ 𝕍 : p i ∈ t' ∧ p i = k}` of the refined inner set is the whole fibre `{i ∈ 𝕍 : p i = k}`.

Neither injectivity of `k ↦ W k` nor essential distinctness of the parents nor any per-tube
density hypothesis is needed; `ShadedBody.shadingMultiplicityEstimateForRhoTubesUndilated` asks for
none of them. -/
theorem exists_spineOneScale
    {σ ρ : ℝ≥0} (hσ : 0 < σ) (hσρ : σ ≤ ρ) (hρ1 : ρ ≤ 1)
    {ιf ιc : Type u} {s : Finset ιf} {t : Finset ιc}
    (V : ιf → ShadedTube σ E) (W : ιc → Tube ρ E) (p : ιf → ιc)
    (hball : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall (0 : E) 1)
    (hmaps : ∀ i ∈ s, p i ∈ t)
    (hle : ∀ i ∈ s, (V i).toConvexSpaceBody ≤ (W (p i)).toConvexSpaceBody) :
    ∃ t' ⊆ t, ∃ (Zρ : ιc → ShadedTube ρ E) (Z' : ιf → ShadedTube σ E),
      (∀ k, (Zρ k).toTube = W k) ∧
      (∀ i, (Z' i).toTube = (V i).toTube) ∧
      (∀ i, (Z' i).shade ⊆ (V i).shade) ∧
      (0 < ∑ i ∈ s, volume (V i).shade → t'.Nonempty) ∧
      (0 < ∑ i ∈ s, volume (V i).shade → 0 < ∑ k ∈ t', volume (Zρ k).shade) ∧
      (∀ i ∈ s, p i ∈ t' → (Z' i).shade ⊆ (Zρ (p i)).shade) ∧
      (spineScaleLoss (Module.finrank ℝ E) s.card σ)⁻¹ *
          ShadedBody.fullness s (fun i => (V i).toShadedBody)
        ≤ ShadedBody.fullness t' (fun k => (Zρ k).toShadedBody) ∧
      ShadedBody.IsCRefinement {i ∈ s | p i ∈ t'} (fun i => (Z' i).toShadedBody)
          s (fun i => (V i).toShadedBody)
          (spineScaleLoss (Module.finrank ℝ E) s.card σ)⁻¹ ∧
      (∀ k ∈ t', ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
        ≤ (spineScaleLoss (Module.finrank ℝ E) s.card σ : ℝ≥0∞)
          * ShadedBody.multiplicity t' (fun k' => (Zρ k').toShadedBody)
          * ShadedBody.multiplicity {i ∈ s | p i = k} (fun i => (Z' i).toShadedBody)) := by
  classical
  let F : ShadedBody.FactorFamily E ιf ιc :=
    { innerSet := s
      innerBody := fun i => (V i).toShadedBody
      outerSet := t
      outerBody := fun k => (W k).toConvexSpaceBody
      parent := p
      parent_mem := hmaps
      inner_le_parent := hle }
  obtain ⟨G, hGouter, hGinner, hGparent, hOuterBody, hInnerBody, hne, hfull,
      href, hmult, hcontain, _hvol, _hthick⟩ :=
    ShadedBody.shadingMultiplicityEstimateForRhoTubesUndilated hσ ⟨hσρ, hρ1⟩ F V W
      (fun _ _ => rfl) (fun _ _ => rfl) (fun i hi => hball i hi)
  set t' : Finset ιc := G.outerSet with ht'def
  set Sout : ιc → ShadedBody E := G.outerBody with hSoutdef
  set Sin : ιf → ShadedBody E := G.innerBody with hSindef
  have hGinner' : G.innerSet = {i ∈ s | p i ∈ t'} := hGinner
  have hOutCarrier : ∀ k ∈ t', (Sout k).carrier = (W k).carrier := by
    intro k hk
    exact congrArg (fun b : ConvexSpaceBody E => b.carrier) (hOuterBody k hk)
  have hInBody : ∀ i ∈ s, (Sin i).toConvexSpaceBody = (V i).toConvexSpaceBody :=
    fun i hi => hInnerBody i hi
  -- the two named shadings, total in their index types
  let Zρ : ιc → ShadedTube ρ E := fun k =>
    if hk : k ∈ t' then
      { toTube := W k
        shade := (Sout k).shade
        measurableSet_shade := (Sout k).measurableSet_shade
        shade_subset := by rw [← hOutCarrier k hk]; exact (Sout k).shade_subset }
    else
      { toTube := W k
        shade := ∅
        measurableSet_shade := MeasurableSet.empty
        shade_subset := by simp }
  let Z' : ιf → ShadedTube σ E := fun i =>
    if hi : i ∈ G.innerSet then
      { toTube := (V i).toTube
        shade := (Sin i).shade
        measurableSet_shade := (Sin i).measurableSet_shade
        shade_subset := by
          have hbody : (Sin i).toConvexSpaceBody = (V i).toConvexSpaceBody :=
            hInBody i (by rw [hGinner'] at hi; exact (Finset.mem_filter.mp hi).1)
          change (Sin i).shade ≤ (V i).toConvexSpaceBody.carrier
          rw [← hbody]
          exact (Sin i).shade_subset }
      else
      { toTube := (V i).toTube
        shade := ∅
        measurableSet_shade := MeasurableSet.empty
        shade_subset := by simp }
  have hZρShade : ∀ k ∈ t', (Zρ k).shade = (Sout k).shade := fun k hk => by simp [Zρ, hk]
  have hZρCarrier : ∀ k ∈ t', ((Zρ k).toShadedBody).carrier = (Sout k).carrier := by
    intro k hk
    have : ((Zρ k).toShadedBody).carrier = (W k).carrier := by simp [Zρ, hk]
    rw [this, hOutCarrier k hk]
  have hZ'Shade : ∀ i ∈ G.innerSet, (Z' i).shade = (Sin i).shade := fun i hi => by simp [Z', hi]
  have hZ'Body : ∀ i ∈ G.innerSet,
      ((Z' i).toShadedBody).toConvexSpaceBody = (Sin i).toConvexSpaceBody := by
    intro i hi
    have h1 : ((Z' i).toShadedBody).toConvexSpaceBody = (V i).toConvexSpaceBody := by
      simp [Z', hi]
    rw [h1, hInBody i (by rw [hGinner'] at hi; exact (Finset.mem_filter.mp hi).1)]
  -- the three replacements of `Sout`/`Sin` by `Zρ`/`Z'`
  have houtFullEq : ShadedBody.fullness t' (fun k => (Zρ k).toShadedBody)
      = ShadedBody.fullness t' Sout := by
    unfold ShadedBody.fullness ShadedBody.fullness'
    congr 2
    · exact Finset.sum_congr rfl fun k hk => congrArg volume (hZρShade k hk)
    · exact Finset.sum_congr rfl fun k hk => congrArg volume (hZρCarrier k hk)
  have houtMultEq : ShadedBody.multiplicity t' (fun k => (Zρ k).toShadedBody)
      = ShadedBody.multiplicity t' Sout := by
    unfold ShadedBody.multiplicity
    congr 1
    · exact Finset.sum_congr rfl fun k hk => congrArg volume (hZρShade k hk)
    · exact congrArg volume (Set.iUnion₂_congr fun k hk => hZρShade k hk)
  refine ⟨t', hGouter, Zρ, Z', fun k => by by_cases hk : k ∈ t' <;> simp [Zρ, hk],
    fun i => by by_cases hi : i ∈ G.innerSet <;> simp [Z', hi], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `Z'` shades are contained in the given ones
    intro i
    by_cases hi : i ∈ G.innerSet
    · rw [hZ'Shade i hi]
      have := (href.1.2 i hi).2
      simpa [hSindef] using this
    · simp [Z', hi]
  · -- nonemptiness
    intro hmass
    exact hne hmass
  · -- the retained parents carry mass
    intro hmass
    have hCinv : (0 : ℝ≥0∞) <
        (((spineScaleLoss (Module.finrank ℝ E) s.card σ)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
      refine ENNReal.coe_pos.mpr ?_
      exact pos_iff_ne_zero.mpr
        (inv_ne_zero (spineScaleLoss_ne_zero (Module.finrank ℝ E) s.card σ))
    have hsumInner : 0 < ∑ i ∈ G.innerSet, volume (Sin i).shade := by
      refine lt_of_lt_of_le ?_ href.2
      exact ENNReal.mul_pos (ne_of_gt hCinv) (ne_of_gt hmass)
    obtain ⟨i, hi, hvi⟩ := Finset.sum_pos_iff.mp hsumInner
    have hpMem : G.parent i ∈ t' := G.parent_mem i hi
    have hmono : volume (Sin i).shade ≤ volume (Sout (G.parent i)).shade :=
      measure_mono (G.shade_subset_parent i hi)
    have hpPos : 0 < volume (Zρ (G.parent i)).shade := by
      rw [hZρShade (G.parent i) hpMem]
      exact hvi.trans_le hmono
    exact hpPos.trans_le
      (Finset.single_le_sum (f := fun k => volume (Zρ k).shade) (fun _ _ => by positivity) hpMem)
  · -- pointwise containment `Z' i ⊆ Zρ (p i)`
    intro i hi hip
    have hiG : i ∈ G.innerSet := by rw [hGinner']; exact Finset.mem_filter.mpr ⟨hi, hip⟩
    have h := hcontain i hiG
    rw [hZ'Shade i hiG, hZρShade (p i) hip]
    have hpar : G.parent i = p i := by rw [hGparent]
    simpa [hSindef, hSoutdef, hpar] using h
  · -- outer fullness
    rw [houtFullEq]
    simpa [spineScaleLoss, hSoutdef] using hfull
  · -- the refinement
    have href1 : ShadedBody.IsRefinement {i ∈ s | p i ∈ t'} (fun i => (Z' i).toShadedBody)
        s (fun i => (V i).toShadedBody) := by
      refine ⟨?_, ?_⟩
      · rw [← hGinner']
        exact href.1.1
      · intro i hi
        have hiG : i ∈ G.innerSet := by rw [hGinner']; exact hi
        refine ⟨?_, ?_⟩
        · show ((Z' i).toShadedBody).toConvexSpaceBody = ((V i).toShadedBody).toConvexSpaceBody
          rw [hZ'Body i hiG]
          exact (href.1.2 i hiG).1
        · show ((Z' i).toShadedBody).shade ⊆ ((V i).toShadedBody).shade
          rw [show ((Z' i).toShadedBody).shade = (Z' i).shade from rfl, hZ'Shade i hiG]
          exact (href.1.2 i hiG).2
    refine ⟨href1, ?_⟩
    show (((spineScaleLoss (Module.finrank ℝ E) s.card σ)⁻¹ : ℝ≥0) : ℝ≥0∞) *
        ∑ i ∈ s, volume ((V i).toShadedBody).shade
      ≤ ∑ i ∈ {i ∈ s | p i ∈ t'}, volume ((Z' i).toShadedBody).shade
    rw [← hGinner']
    have hsum : ∑ i ∈ G.innerSet, volume ((Z' i).toShadedBody).shade
        = ∑ i ∈ G.innerSet, volume (Sin i).shade :=
      Finset.sum_congr rfl fun i hi => congrArg volume (hZ'Shade i hi)
    rw [hsum]
    exact href.2
  · -- the product estimate
    intro k hk
    have hfiber : G.fiber k = {i ∈ s | p i = k} := by
      ext i
      simp only [ShadedBody.ShadedFactorFamily.fiber, Finset.mem_filter, hGinner',
        Finset.mem_filter]
      constructor
      · rintro ⟨⟨hi, _⟩, hpi⟩
        exact ⟨hi, by rw [hGparent] at hpi; exact hpi⟩
      · rintro ⟨hi, hpi⟩
        exact ⟨⟨hi, by rw [hpi]; exact hk⟩, by rw [hGparent]; exact hpi⟩
    have hm := hmult k hk
    have hinEq : ShadedBody.multiplicity {i ∈ s | p i = k} (fun i => (Z' i).toShadedBody)
        = ShadedBody.multiplicity (G.fiber k) Sin := by
      rw [hfiber]
      unfold ShadedBody.multiplicity
      have hsub : ∀ i ∈ {i ∈ s | p i = k}, i ∈ G.innerSet := by
        intro i hi
        rw [hGinner']
        rw [Finset.mem_filter] at hi ⊢
        exact ⟨hi.1, by rw [hi.2]; exact hk⟩
      congr 1
      · exact Finset.sum_congr rfl fun i hi => congrArg volume (hZ'Shade i (hsub i hi))
      · exact congrArg volume (Set.iUnion₂_congr fun i hi => hZ'Shade i (hsub i hi))
    rw [houtMultEq, hinEq]
    simpa [spineScaleLoss, hSoutdef, hSindef] using hm

/-! ## The two-scale split -/

/-! ## The split at two levels of a tube hierarchy -/

section Hierarchy

variable {δ : ℝ≥0} {ι : Type u} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {σ : ℕ → ℝ≥0}

open Classical in
/-- **The active level-`k` nodes of a nested cover**: those that carry at least one member of the
family.  The inactive ones are exactly the indices of `Tube.ChainCoverSystem.indexSet` that no
`Tube.ChainCoverSystem.assign` hits, and they are discarded because a level-`a` ancestor can only
be read off a member. -/
noncomputable def activeNodes (𝒞 : Tube.ChainCoverSystem s T N σ) (k : ℕ) : Finset ι :=
  {j ∈ 𝒞.indexSet k | (Tube.coverClass s (𝒞.assign k) j).Nonempty}

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem activeNodes_subset (𝒞 : Tube.ChainCoverSystem s T N σ) (k : ℕ) :
    activeNodes 𝒞 k ⊆ 𝒞.indexSet k := by
  classical
  intro j hj
  exact (Finset.mem_filter.mp hj).1

open Classical in
/-- **The level-`a` ancestor of an active level-`b` node**: read off any member of its class, which
is legitimate because `Tube.ChainCoverSystem.nested` makes the class of a level-`b` node lie inside
a single level-`a` class.  Off the active nodes the value is irrelevant and is the node itself. -/
noncomputable def coarseNode (𝒞 : Tube.ChainCoverSystem s T N σ) (a b : ℕ) (j : ι) : ι :=
  if h : (Tube.coverClass s (𝒞.assign b) j).Nonempty then 𝒞.assign a h.choose else j

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem assign_mem_activeNodes (𝒞 : Tube.ChainCoverSystem s T N σ) {k : ℕ} (hk : k ≤ N)
    {i : ι} (hi : i ∈ s) : 𝒞.assign k i ∈ activeNodes 𝒞 k := by
  classical
  refine Finset.mem_filter.mpr ⟨𝒞.assign_mem k hk i hi, ⟨i, ?_⟩⟩
  simp [Tube.coverClass, hi]

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem coarseNode_mem (𝒞 : Tube.ChainCoverSystem s T N σ) {a b : ℕ} (ha : a ≤ N)
    {j : ι} (hj : j ∈ activeNodes 𝒞 b) : coarseNode 𝒞 a b j ∈ 𝒞.indexSet a := by
  classical
  have h : (Tube.coverClass s (𝒞.assign b) j).Nonempty := (Finset.mem_filter.mp hj).2
  have hmem := h.choose_spec
  simp only [Tube.coverClass, Finset.mem_filter] at hmem
  rw [coarseNode, dif_pos h]
  exact 𝒞.assign_mem a ha _ hmem.1

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem tube_le_coarseNode (𝒞 : Tube.ChainCoverSystem s T N σ) {a b : ℕ} (hab : a ≤ b)
    (hb : b ≤ N) {j : ι} (hj : j ∈ activeNodes 𝒞 b) :
    (𝒞.tube b j).toConvexSpaceBody
      ≤ (𝒞.tube a (coarseNode 𝒞 a b j)).toConvexSpaceBody := by
  classical
  have h : (Tube.coverClass s (𝒞.assign b) j).Nonempty := (Finset.mem_filter.mp hj).2
  have hmem := h.choose_spec
  simp only [Tube.coverClass, Finset.mem_filter] at hmem
  have hchain := 𝒞.tube_assign_le hab hb hmem.1
  rw [hmem.2] at hchain
  rw [coarseNode, dif_pos h]
  exact hchain

end Hierarchy

end Kakeya.ML2Reduction

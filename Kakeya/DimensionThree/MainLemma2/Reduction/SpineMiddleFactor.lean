/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCoreFinal
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEccentric
public import Kakeya.StickyKakeya.BallReduction
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineHupProducer
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCanonicalCoverAt

/-!
# the estimate: the middle factor, from the rescaled world back to the ambient one

Blueprint: GWZ — the passage
"*rescale `T_θ` to `B₁`, converting `𝕋[T_θ]` to `𝕋̃` of thickness `δ̃ = τ/θ`*", and the two
displays `upperBdDeltaMaxTildeTT` and `tildeDeltaLargeDeltamax` that travel with it.

`Kakeya.ML2Core.mass_gain_of_three_factors`  consumes the middle factor as
`μ({j ∈ tτ' | coarseNode 𝒞 a b j = jθ}, Yτ') ≤ δ^{gm} |·|^β` — at the **ambient** scale `δ`.
`Kakeya.ML2Reduction.spine_multiplicity_le_nonEccentric_of_canonicalCover`  and
`Kakeya.ML2Core.eccentric_atPlankScale`  both prove it at the **rescaled** thickness `δ̃`.
This file is the bridge, and it is exact on the multiplicity: the rescaling is an affine
equivalence, and an affine equivalence multiplies every volume by one nonzero finite factor, so
every ratio of volumes — and `ShadedBody.multiplicity` is a ratio of volumes — is unchanged.

## The ledger

```
μ(fibre, Yτ')  =  μ(fibre, outerFamily … Yτ')            exact  (outerFamily_multiplicity)
               ≤  δ̃^{gm̃} · |fibre|^β                     the component estimates on the rescaled family
               ≤  δ^{w · gm̃} · |fibre|^β                  from δ̃ ≤ δ^{w}
```

**No constant is lost in the first step and no constant is lost in the third.** The only price of
the whole rescaling is the *exponent* contraction `gm̃ ↦ w · gm̃`, and `w` is the window exponent
the dividing-scales lemma already supplies (`δ̃ = τ/θ ≤ δ^{e}` on the spine, `e = 1/√N`).

## What this file does and does not close

It closes the **transport**.  It does *not* build the plank factoring of `𝕋̃_ρ`, which is the estimate;
`Kakeya.ML2Reduction.exists_plankFactoringData_of_isUniformAtScale` and
`Kakeya.ML2Reduction.isEccentric_or_isNonEccentric` are existing and are what the estimate must compose, and
`Kakeya.ML2Core.middle_factor_of_cases` is where their `Or` lands.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody

namespace Kakeya.ML2Core

universe u

/-! ## The fibre sits inside its coarse node, after translation -/

section Fibre

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {δ : ℝ≥0} {ι : Type*} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {σ : ℕ → ℝ≥0}

end Fibre

/-! ## The transport itself -/

/-- **the estimate.**  The middle factor, proved at the rescaled thickness `σ = δ̃`, read at the ambient
one.

Two things are worth stating plainly about the ledger.

* **The multiplicity step is an equality, not an inequality.**
  `Kakeya.ML2Reduction.outerFamily_multiplicity` is `μ(s, outerFamily …) = μ(s, 𝕋)`: the rescaling
  is an affine equivalence and the outer-tube replacement only enlarges bodies, which multiplicity
  cannot see. So the outer-tube constant `outerLoss R` — which *is* paid on `Δ_max` and on the
  fullness — is **not** paid here.
* **The exponent contracts by exactly the window width.**  `δ̃ ≤ δ^{w}` turns a gain `gm̃` at `δ̃`
  into a gain `w · gm̃` at `δ`, and that is the whole price. `0 ≤ gm̃` is load-bearing: on a *loss*
  the inequality would run the other way, which is why this lemma is stated for the middle factor
  and not reused for the two outer ones. -/
theorem middle_factor_of_rescaled
    {θ τ σ δ : ℝ≥0} {R : ℝ} (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R)
    (hτσ : (τ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ))
    (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {ι : Type*} {fib : Finset ι} (Y : ι → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    (hsub : ∀ j ∈ fib, (Y j).carrier ⊆ T₀.carrier)
    {Nm : ℕ} {β gm w : ℝ} (hgm : 0 ≤ gm) (hw : 0 ≤ w) (hsep : σ ≤ δ ^ w)
    (hres : ShadedBody.multiplicity fib
        (fun j ↦ (ML2Reduction.outerFamily hsit.pos_ambient T₀ hR σ Y j).toShadedBody)
      ≤ (σ : ℝ≥0∞) ^ gm * (Nm : ℝ≥0∞) ^ β) :
    ShadedBody.multiplicity fib (fun j ↦ (Y j).toShadedBody)
      ≤ (δ : ℝ≥0∞) ^ (w * gm) * (Nm : ℝ≥0∞) ^ β := by
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  rw [← ML2Reduction.outerFamily_multiplicity hn hsit hR hτσ hsub]
  exact hres.trans
    (mul_le_mul' (rpow_le_rpow_of_le_rpow_base hgm hw hsep) le_rfl)

/-! ## The upstairs ED-multiplicity exponent `m`: the counting route is closed -/

/-! ## `hret`'s per-tube comparison, from `HasComparableDensities` -/

section Retention

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end Retention

/-! ## one missing datum: `IsUniformAtScale` from a chain -/

section AtScale

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  {δ : ℝ≥0} {ι : Type*} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {σ : ℕ → ℝ≥0}
  {C : ℝ≥0}

/-! ## The plank scale is a grid level, and that dissolves the exact-radius obstruction -/

end AtScale

/-! ## Step 8 to step 10, with `huni` bypassed -/

/-- **Step 8 ⟹ step 10, at the post-uniformisation family — and `huni`-free.**

The existing `Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer_of_step8` composes step 8 into
step 10 but still carries the **pinned** `huni` binder — uniformity on the *whole* index set with
the *unrefined* outer family — which  (a) shows is an extension, false in general, and
which no uniformiser in the tree produces.

This composition does not. It routes `Kakeya.ML2Reduction.canonicalCover_of_step8`'s output —
which is the `hcanon` binder character for character — into
`Kakeya.ML2Reduction.fine_factor_of_lemma91At_of_canonicalCover`, i.e. into `Lemma91At` applied
**directly at `(s', U')`**, where the uniformity witness `huni` is the *producible* one:
`Kakeya.ML2Reduction.exists_outerShadedUniformTubeSet`'s, on the subfamily it actually returns.

**So the whole count side of step 10 is now a single composition with no undischargeable binder in
it.** What remains inside is `hstep8`'s ED-multiplicity ledger `M ≤ ρ^{-m}`, and the next lemma
shows `m = 0` is admissible there. -/
theorem fine_factor_of_lemma91At_of_step8
    {β ϖ ζ ζ' m ν ηd cst : ℝ} {b δt δ' : ℝ≥0} {R : ℝ}
    (hL : ML2Reduction.Lemma91At.{u} β ϖ ζ ν ηd δ')
    -- the exact negation of the vacuity condition
    -- `Kakeya.VeryNotSticky.lemma91Binders_vacuous_of_exponents` (cited by name only — this is a
    -- hypothesis, not a consumed term, so the witness leaf is NOT imported): Lemma 9.1's binder
    -- list is jointly unsatisfiable whenever `2 + ηd < (1 - ϖ) * (2 + ζ)`, and `hζ` is exactly
    -- its negation, so it is what keeps `hL91` above from being vacuously true.  Corroborated
    -- caller-side by the source's own `ζ ≤ (4/5) ζ_*`.
    (hζ : ζ * (1 - ϖ) ≤ ηd + 2 * ϖ)
    (hsit : Tube.IsRescalingSituation b δt δ' R 3) (hR : 0 < R) (_hR1 : 1 ≤ R)
    (_hτσ : (δt : ℝ) / (b : ℝ) ≤ 4 * (δ' : ℝ)) (hδ'0 : 0 < δ') (_hϖ0 : 0 ≤ ϖ)
    (hwin4 : ((δ' ^ ϖ : ℝ≥0) : ℝ) ≤ 1 / 4)
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {s s' : Finset α} (_hs' : s' ⊆ s)
    (𝕋 : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3)))
    (U' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3)))
    (mm : EuclideanSpace ℝ (Fin 3)) {qc : ℝ} (hqc0 : 0 < qc) (h3qc : 3 * qc ≤ ηd)
    (hcb : Kakeya.VeryNotSticky.CentredHandBack hsit hR T₀ mm qc s s' 𝕋 U')
    (hct : Kakeya.VeryNotSticky.CountTransport hsit hR T₀ mm ϖ ζ s' 𝕋 U')
    (_hsub : ∀ i ∈ s, (𝕋 i).carrier ⊆ T₀.carrier)
    (_hloss : ML2Reduction.outerLoss R ≤ δ' ^ (-cst))
    (_hmax : Kakeya.maxDensity s (fun i ↦ (𝕋 i).toConvexSpaceBody)
      ≤ (δ' : ℝ≥0∞) ^ (-(ηd - cst)))
    (hfull : ShadedBody.fullness s' (fun i ↦ (U' i).toShadedBody) ≥ δ' ^ ηd)
    -- AA/AB: tightened to the constant the producer actually returns
    -- (`ShadedTube.ssfUniformConst 3`, `Kakeya/ShadedUniform.lean`), with the threshold the
    -- loose bracket used to quantify away carried explicitly.  Discharged at wiring time by
    -- `exists_outerShadedUniformTubeSet_ssf` + `exists_threshold_coe_const_le_rpow_neg`.
    -- this binder is ALSO where the line-ED levels row is sourced.  The witness carries
    -- a uniform hierarchy, and `Kakeya.VeryNotSticky.lineEDLevelsAt_C3_of_huni` turns it (with
    -- `hcb`'s `centred`/`contained`/`small` rows and the uniformiser's own grid threshold) into
    -- `LineEDLevelsAt C₃ lineEDLevelsConstant _` at the NAMED constant (
    -- ): the datum is DERIVED here, never an ambient field.
    (huni : ((ShadedTube.ssfUniformConst 3 : ℝ≥0) : ℝ≥0∞) ≤ (δ' : ℝ≥0∞) ^ (-ηd) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s' U' (Tube.ssfGridLen δ')
        (ShadedTube.ssfUniformConst 3)))
    -- CONTRACTED-bottom window `[δ'^{1-ϖ}/C, δ'^{ϖ}]` — the hand-back reads the cover
    -- at `ρ/C`.  A producer must supply this clause on the wide
    -- window.  `hbudget` below did NOT move: `Kakeya.ML2Reduction.budget_descends` carries
    -- it from `ρ` down to `ρ/C`, at the cost of the reading gap `hgap`.
    (hgap : ζ ≤ ζ' - m)
    (hstep8 : ∀ ρ : ℝ≥0, ρ ∈ Set.Icc (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t₈ : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))) (M : ℕ),
        (∀ k ∈ t₈, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t₈, ∃ i ∈ s', (𝕋 i).carrier ⊆ (W k).carrier) ∧
        (∀ i ∈ t₈, (open scoped Classical in t₈.filter (fun j ↦
          ¬ _root_.IsEssentiallyDistinct (W j).carrier (W i).carrier)).card ≤ M) ∧
        (M : ℝ) ≤ (ρ : ℝ) ^ (-m) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t₈.card : ℝ))
    (_hbudget : ∀ ρ : ℝ≥0, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
            (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : ℝ≥0) : ℝ)⌉₊ : ℝ)
          * (ML2Reduction.spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-((ζ' - m) - ζ)))
    -- this is `hbudget` with `centringCountLossConstant R ·` at the head of the left-hand
    -- side, so it IMPLIES `hbudget`; `hbudget` is retained only because keeps its text
    -- tree-wide.  Discharged by `exists_threshold_hup_budget`'s argument at the
    -- new constant, never assumed; `ζ ≤ ζ' - m` (`hgap`) is its side condition.
    (hcntbudget : ∀ ρ : ℝ≥0, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ)
        * (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
              (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : ℝ≥0) : ℝ)⌉₊ : ℝ)
          * (ML2Reduction.spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-((ζ' - m) - ζ))) :
    ShadedBody.multiplicity s' (fun i ↦ (U' i).toShadedBody)
      ≤ (δ' : ℝ≥0∞) ^ ν * (s'.card : ℝ≥0∞) ^ β :=
  ML2Reduction.fine_factor_of_lemma91At_of_canonicalCover' hL hζ hsit hR hδ'0 hqc0 h3qc T₀ mm
    (s := s) 𝕋 U' hcb (Kakeya.VeryNotSticky.huni_loose_of_tight huni)
    (fun ρ hρ ↦ hct ρ hρ (by
      -- The cover is read at the CONTRACTED radius.  `hstep8` moved to the wide window;
      -- `hbudget` did not — `Kakeya.ML2Reduction.budget_descends` carries it down.
      have hmem := Kakeya.VeryNotSticky.mem_widened_window_of_mem hρ
      have hc0 : 0 < ρ / Kakeya.VeryNotSticky.centringCoverRadiusConstant :=
        lt_of_lt_of_le (div_pos (NNReal.rpow_pos hδ'0)
          Kakeya.VeryNotSticky.edWindowContractionConstant_pos) hmem.1
      obtain ⟨κ₀, t₈, W, M, hsubW, hused, hM, hMρ, hcard⟩ := hstep8 _ hmem
      exact ML2Reduction.canonicalCoverAt_of_step8_const
        (Kc := (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ)) hsit hR T₀ 𝕋 hc0
        (le_trans (by exact_mod_cast hmem.2) hwin4) t₈ W hsubW hused hM hMρ hcard
        (ML2Reduction.budget_descends
          (h := ML2Reduction.hbud_of_hcntbudget (NNReal.coe_nonneg _)
            (by simpa using hcntbudget ρ hρ))
          (hρ'0 := by exact_mod_cast hc0)
          (hle := by exact_mod_cast Kakeya.VeryNotSticky.div_centringCoverRadiusConstant_le ρ)
          (he := by linarith))))

open Classical in
/-- **An essentially distinct family enters `hstep8` at `m = 0`.**

`Kakeya.ML2Reduction.hup_of_step8`'s third and fourth clauses are the ED-multiplicity ledger
`#{j ∈ t₈ | ¬ ED (W j) (W i)} ≤ M` and `M ≤ ρ^{-m}`.  On a family that is *already* pairwise
essentially distinct the fibre of `i` is `{i}` (`Kakeya.ML2Core.card_notEssDistinct_le_one`), so
`M = 1` and the ledger is met at **`m = 0`**: `1 ≤ ρ^{-0} = 1`.

**Consequence, and it is the whole of item 1.**  Fed an essentially distinct family, the chain
`hstep8 → hup_of_step8 → canonicalCover_of_step8 → step 10` spends **nothing** of the reading gap
on the extraction, the budget clause of
`Kakeya.ML2Core.fine_factor_of_lemma91At_of_step8` collapses to
`⌈C⌉ · spineOuterCountLoss R ≤ ρ^{-(ζ' - ζ)}` — a threshold on `ρ` whenever `ζ < ζ'`
(`Kakeya.ML2Reduction.exists_threshold_hup_budget`) — and
`Kakeya.ML2Core.not_hup_budget_at_trivial_edMult` becomes moot, because no counting is done.

**No positivity of `ρ` is needed.**  The residue is therefore not an exponent to be bounded but a
family to be exhibited: an essentially distinct `ρ b`-family inside `T₀`, all-used over `s'`, of
cardinality at least `ρ^{-2-ζ'}`. -/
theorem hstep8_of_essDistinct {b δt ρ : ℝ≥0} {ζ' : ℝ}
    {T₀ : Tube b (EuclideanSpace ℝ (Fin 3))}
    {α : Type u} {s' : Finset α} {𝕋 : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3))}
    {κ₀ : Type u} (t : Finset κ₀) (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3)))
    (hED : (t : Set κ₀).Pairwise
      fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier)
    (hsubW : ∀ k ∈ t, (W k).carrier ⊆ T₀.carrier)
    (hused : ∀ k ∈ t, ∃ i ∈ s', (𝕋 i).carrier ⊆ (W k).carrier)
    (hcard : (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ)) :
    ∃ (κ₁ : Type u) (t₈ : Finset κ₁)
      (W' : κ₁ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))) (M : ℕ),
      (∀ k ∈ t₈, (W' k).carrier ⊆ T₀.carrier) ∧
      (∀ k ∈ t₈, ∃ i ∈ s', (𝕋 i).carrier ⊆ (W' k).carrier) ∧
      (∀ i ∈ t₈, (t₈.filter (fun j ↦
        ¬ _root_.IsEssentiallyDistinct (W' j).carrier (W' i).carrier)).card ≤ M) ∧
      (M : ℝ) ≤ (ρ : ℝ) ^ (-(0 : ℝ)) ∧
      (ρ : ℝ) ^ (-2 - ζ') ≤ (t₈.card : ℝ) := by
  refine ⟨κ₀, t, W, 1, hsubW, hused, fun i hi ↦ card_notEssDistinct_le_one W hED hi, ?_, hcard⟩
  rw [neg_zero, Real.rpow_zero]
  norm_num

/-! ## Item 2: the uniform tube set on the rescaled family, and the parent datum from it -/

section Rescaled

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E] [ProperSpace E]

end Rescaled

section NoEd

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end NoEd

/-! ## The residue, isolated: the fine factor from ONE essential-distinctness clause -/

open Classical in
/-- **`hED` is the only thing left, and this is where it is spent.**

Every other input of step 10 is now an existing or new producer.  This theorem takes the
essential-distinctness clause — an essentially distinct all-used `ρ b`-family inside `T₀` with the
step-8 count, at every scale of Lemma 9.1's window — and delivers the fine factor at the
post-uniformisation family `(s', U')`, with

* `m = 0` throughout, by `Kakeya.ML2Core.hstep8_of_essDistinct`: **no exponent is spent on the
  extraction**, so `hbudget` is the bare `⌈C₃⌉ · spineOuterCountLoss R ≤ ρ^{-(ζ' - ζ)}`, a
  threshold on `ρ` for `ζ < ζ'` (`Kakeya.ML2Reduction.exists_threshold_hup_budget`);
* **no `huni`-shaped binder**, by routing through
  `Kakeya.ML2Core.fine_factor_of_lemma91At_of_step8`.

**`hED` is stated as a plain hypothesis — no new `def … : Prop` — and its shape is
`Kakeya.ML2Reduction.hup_of_step8`'s first, second, fourth and fifth clauses at `m = 0`, with the
third replaced by the pairwise-`IsEssentiallyDistinct` it makes redundant.**  So whichever repair
is condition — an `essDistinct` field on `Tube.UniformTubeSet`, or a Section-9-local essentially
distinct cover datum — plugs in by `exact`. -/
theorem fine_factor_of_lemma91At_of_edCover
    {β ϖ ζ ζ' ν ηd cst : ℝ} {b δt δ' : ℝ≥0} {R : ℝ}
    (hL : ML2Reduction.Lemma91At.{u} β ϖ ζ ν ηd δ')
    -- the exact negation of the vacuity condition
    -- `Kakeya.VeryNotSticky.lemma91Binders_vacuous_of_exponents` (cited by name only — this is a
    -- hypothesis, not a consumed term, so the witness leaf is NOT imported): Lemma 9.1's binder
    -- list is jointly unsatisfiable whenever `2 + ηd < (1 - ϖ) * (2 + ζ)`, and `hζ` is exactly
    -- its negation, so it is what keeps `hL91` above from being vacuously true.  Corroborated
    -- caller-side by the source's own `ζ ≤ (4/5) ζ_*`.
    (hζ : ζ * (1 - ϖ) ≤ ηd + 2 * ϖ)
    (hsit : Tube.IsRescalingSituation b δt δ' R 3) (hR : 0 < R) (hR1 : 1 ≤ R)
    (hτσ : (δt : ℝ) / (b : ℝ) ≤ 4 * (δ' : ℝ)) (hδ'0 : 0 < δ') (hϖ0 : 0 ≤ ϖ)
    (hwin4 : ((δ' ^ ϖ : ℝ≥0) : ℝ) ≤ 1 / 4)
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {s s' : Finset α} (hs' : s' ⊆ s)
    (𝕋 : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3)))
    (U' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3)))
    (mm : EuclideanSpace ℝ (Fin 3)) {qc : ℝ} (hqc0 : 0 < qc) (h3qc : 3 * qc ≤ ηd)
    (hcb : Kakeya.VeryNotSticky.CentredHandBack hsit hR T₀ mm qc s s' 𝕋 U')
    (hct : Kakeya.VeryNotSticky.CountTransport hsit hR T₀ mm ϖ ζ s' 𝕋 U')
    (hsub : ∀ i ∈ s, (𝕋 i).carrier ⊆ T₀.carrier)
    (hloss : ML2Reduction.outerLoss R ≤ δ' ^ (-cst))
    (hmax : Kakeya.maxDensity s (fun i ↦ (𝕋 i).toConvexSpaceBody)
      ≤ (δ' : ℝ≥0∞) ^ (-(ηd - cst)))
    (hfull : ShadedBody.fullness s' (fun i ↦ (U' i).toShadedBody) ≥ δ' ^ ηd)
    -- AA/AB: tightened to the constant the producer actually returns
    -- (`ShadedTube.ssfUniformConst 3`, `Kakeya/ShadedUniform.lean`), with the threshold the
    -- loose bracket used to quantify away carried explicitly.  Discharged at wiring time by
    -- `exists_outerShadedUniformTubeSet_ssf` + `exists_threshold_coe_const_le_rpow_neg`.
    -- this binder is ALSO where the line-ED levels row is sourced.  The witness carries
    -- a uniform hierarchy, and `Kakeya.VeryNotSticky.lineEDLevelsAt_C3_of_huni` turns it (with
    -- `hcb`'s `centred`/`contained`/`small` rows and the uniformiser's own grid threshold) into
    -- `LineEDLevelsAt C₃ lineEDLevelsConstant _` at the NAMED constant (
    -- ): the datum is DERIVED here, never an ambient field.
    (huni : ((ShadedTube.ssfUniformConst 3 : ℝ≥0) : ℝ≥0∞) ≤ (δ' : ℝ≥0∞) ^ (-ηd) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s' U' (Tube.ssfGridLen δ')
        (ShadedTube.ssfUniformConst 3)))
    -- CONTRACTED-bottom window `[δ'^{1-ϖ}/C, δ'^{ϖ}]` — the hand-back reads the cover
    -- at `ρ/C`.  A producer must supply this clause on the wide
    -- window.  `hbudget` below did NOT move: `Kakeya.ML2Reduction.budget_descends` carries
    -- it from `ρ` down to `ρ/C`, at the cost of the reading gap `hgap`.
    (hgap : ζ ≤ ζ')
    (hED : ∀ ρ : ℝ≥0, ρ ∈ Set.Icc (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))),
        ((t : Set κ₀).Pairwise
          fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
        (∀ k ∈ t, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t, ∃ i ∈ s', (𝕋 i).carrier ⊆ (W k).carrier) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ))
    (hbudget : ∀ ρ : ℝ≥0, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
            (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : ℝ≥0) : ℝ)⌉₊ : ℝ)
          * (ML2Reduction.spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    -- as in the block above: `hbudget` with `centringCountLossConstant R ·` at the head,
    -- hence implying it; `hbudget` is retained only for text.
    (hcntbudget : ∀ ρ : ℝ≥0, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ)
        * (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
              (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : ℝ≥0) : ℝ)⌉₊ : ℝ)
          * (ML2Reduction.spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ))) :
    ShadedBody.multiplicity s' (fun i ↦ (U' i).toShadedBody)
      ≤ (δ' : ℝ≥0∞) ^ ν * (s'.card : ℝ≥0∞) ^ β := by
  refine fine_factor_of_lemma91At_of_step8 (m := 0) (ζ' := ζ') hL hζ hsit hR hR1 hτσ hδ'0 hϖ0
    hwin4 T₀ hs' 𝕋 U' mm hqc0 h3qc hcb hct hsub hloss hmax hfull huni (by simpa using hgap)
    (fun ρ hρ ↦ ?_) (fun ρ hρ ↦ ?_) (fun ρ hρ ↦ by simpa using hcntbudget ρ hρ)
  · obtain ⟨κ₀, t, W, hEDt, hsubW, hused, hcard⟩ := hED ρ hρ
    exact hstep8_of_essDistinct (T₀ := T₀) (𝕋 := 𝕋) (s' := s') t W hEDt hsubW hused hcard
  · simpa using hbudget ρ hρ

/-! ## The supplier tie: `eventually_outerHuni_ssf`'s conjunct fills the sites' `huni` slot -/

end Kakeya.ML2Core

end

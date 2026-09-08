/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCountClause
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCentredHandBack
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineOuterUniformity

/-!
# Steps 3–11 of the non-eccentric case, assembled

Blueprint: GWZ, the paragraph headed **The non-eccentric
case** inside the proof of Main Lemma 2, whose last display is
`multTildeTLem2`:

```
μ(𝕋̃, Ỹ) ≤ δ̃^{10 η_{j-1}/ε₂} |𝕋̃|^β.
```

That display is the output of this file: `Kakeya.ML2Reduction.spine_multiplicity_le_two_factors`
and its `∀ᶠ`-free assembled form
`Kakeya.ML2Reduction.spine_multiplicity_le_nonEccentric_of_upstairs`.  It is the *same shape* as
the eccentric branch's conclusion
(`Kakeya.ML2Reduction.eccentric_of_maxDensityFactoring_crossed`, whose exponent is
`10 η/ε₂ - η₀/2`), which is what makes the case split of the estimate a `rcases` and not a repackaging.

## The three seams this file closes, and the one it prices

* **Step 8 → Lemma 9.1's count clause** (`window_count_of_spine_window`,
  `upstairsBundle_of_spine_window`).  Step 8 delivers a count at every scale `σ` of the *spine's*
  window `[δ̃^{1-ε₂}, δ̃^{ε₂}]`, in the shape `(σ/b)^{-2-ζ'} ≤ …`; Lemma 9.1 asks for one at every
  scale `ρ` of *its own* window `[(δ')^{1-ϖ}, (δ')^{ϖ}]` at the rescaled thickness
  `δ' = δ̃/b`, in the shape `ρ^{-2-ζ'} ≤ …`.  The two are matched by `σ = ρ b`, which is
  `Kakeya.ML2Reduction.mem_sigmaWindow_of_window_fits` composed with `(ρ b)/b = ρ`.

* **Step 10 over the post-uniformisation family**
  (`fine_factor_of_lemma91At_of_canonicalCover`).  The
  uniformity witness the tree can build lives on a *refined* family `(s', U')`
  (`Kakeya.ML2Reduction.exists_outerShadedUniformTubeSet`), and the `huni` binder of
  `Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer` is pinned to the unrefined
  `(s, outerFamily … 𝕋)`.  So Lemma 9.1 is applied **directly**, at `(s', U')`, through
  `Kakeya.ML2Reduction.Lemma91At`; the count clause at `(s', U')` is
  `count_clause_at_uniformised_of_canonicalCover`, and the two remaining hypotheses transport at
  no loss by `Kakeya.ML2Reduction.maxDensity_eq_of_toTube_eq` and
  `Kakeya.ML2Reduction.carrier_subset_closedBall_of_toTube_eq`.

* **Step 11 with the rescaling loss** (`multiplicity_le_of_two_factors_rescaled`,
  `spine_multiplicity_le_two_factors`).  Step 10's gain is read at `δ' = δ̃/b`, not at `δ̃`.  Since
  `δ' ≤ δ̃^{1-ε₂}` (step 5's `b ≥ δ̃^{ε₂}`), the honest exponent at `δ̃` is `(1-ε₂) ν`, **not** `ν`,
  and the shortfall `ε₂ ν` is *not* covered by `Kakeya.ML2Spine.IsSpine.gain_budget` —
  `Kakeya.ML2Reduction.rescaleLoss_not_free_of_isSpine_fields` exhibits reals satisfying every
  `IsSpine` inequality that bears on the budget for which the weakened form fails.  So step 11 is
  closed here by `Kakeya.ML2Reduction.spineRung_gainBudget_of_rescaleLoss` — the *constructed*
  spine — and **not** by `Kakeya.ML2Spine.spine_gainBudget_of_loss`, whose multiscale budget
  `κ ≤ 40 η_k/ε₂` also shrinks to `κ ≤ 20 η_k/ε₂`.

## What is assumed rather than built

The rescaled datum and its plank factorization enter as explicit hypotheses. The
interface is recorded in the docstring of
`Kakeya.ML2Reduction.spine_multiplicity_le_nonEccentric_of_canonicalCover`.

**One interface is deliberately *not* used**: the upstairs-cover bundle of
`Reduction/SpineCanonicalCover.lean` §1, which buys essential distinctness of the pushed-down
`ρ`-family by dividing by that family's maximal density.  A family of `ρ`-tubes inside `B₁`
satisfies `Δ_max ≥ |t| ρ²/3`, so the bundle's own count clause `ρ^{-2-ζ'} ≤ |t|` forces
`Δ_max ≥ ρ^{-ζ'}/3`, and its slack clause then demands `refineToEssDistinctLeaves.C 3 ≤ 3 ρ^{ζ} ≤ 3`
against a constant that exceeds `4`.  The bundle is therefore unsatisfiable, and any theorem
consuming it is vacuous.  Step 10 is stated below over the **essential-distinctness** binder of
the existing `Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer_of_canonicalCover` instead,
which never divides by a density.  The theorems of `Reduction/SpineCanonicalCover.lean` remain
true — only their §1 hypothesis set is unsatisfiable — but **this file imports neither that module
nor any declaration of it**: its two imports are `Reduction.SpineCountClause` (for
`Kakeya.ML2Reduction.outerCanonicalCover_of_canonicalCover` and
`Kakeya.ML2Reduction.spineOuterCountLoss`) and `Reduction.SpineOuterUniformity` (for the three
free transports of a tube-preserving shade refinement).
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody

namespace Kakeya.ML2Reduction

universe u

/-! ## Step 5's consequence: the rescaled thickness is at most `δ̃^{1-ε₂}` -/

/-- **The rescaled thickness, bounded.**  From `δ' b = δ̃` and step 5's `b ≥ δ̃^{ε₂}`
(`Kakeya.ML2Spine.spine_le_of_maxDensity_le_window`) we get `δ' ≤ δ̃^{1-ε₂}`.

This is the arithmetic already inside `Kakeya.ML2Reduction.mem_sigmaWindow_of_window_fits`,
isolated because step 11 needs it on its own — it is the *only* input to the `(1-ε₂)` factor that
`Kakeya.ML2Reduction.multiplicity_le_rescaleBack` charges. -/
theorem rescaledScale_le {δt b δ' : ℝ≥0} {ε₂ : ℝ}
    (hδ0 : 0 < δt) (hbw : δt ^ ε₂ ≤ b) (hprod : δ' * b = δt) :
    δ' ≤ δt ^ (1 - ε₂) := by
  have h2 : δt ^ (1 - ε₂) * δt ^ ε₂ = δt := by
    rw [← NNReal.rpow_add (ne_of_gt hδ0)]
    simp
  have hpow0 : (0 : ℝ≥0) < δt ^ ε₂ := NNReal.rpow_pos hδ0
  refine le_of_mul_le_mul_right ?_ hpow0
  calc δ' * δt ^ ε₂ ≤ δ' * b := by gcongr
    _ = δt := hprod
    _ = δt ^ (1 - ε₂) * δt ^ ε₂ := h2.symm

/-- **The rescaling loss on a single power.**  `(δ')^ν ≤ δ̃^{(1-ε₂)ν}` whenever
`δ' ≤ δ̃^{1-ε₂}` and `ν ≥ 0`.  This is `Kakeya.ML2Reduction.multiplicity_le_rescaleBack` with the
multiplicity stripped off, so that it can be applied to the *bound* of step 10 rather than to a
multiplicity. -/
theorem rpow_le_rpow_rescaled {δt δ' : ℝ≥0} {ε₂ ν : ℝ}
    (hν : 0 ≤ ν) (hε₂ : ε₂ ≤ 1) (hδ' : δ' ≤ δt ^ (1 - ε₂)) :
    (δ' : ℝ≥0∞) ^ ν ≤ (δt : ℝ≥0∞) ^ ((1 - ε₂) * ν) := by
  have hstep : δ' ^ ν ≤ (δt ^ (1 - ε₂)) ^ ν := NNReal.rpow_le_rpow hδ' hν
  have hcast : ((δ' ^ ν : ℝ≥0) : ℝ≥0∞) ≤ (((δt ^ ((1 - ε₂) * ν) : ℝ≥0)) : ℝ≥0∞) := by
    refine ENNReal.coe_le_coe.mpr ?_
    rw [NNReal.rpow_mul]
    exact hstep
  rwa [ENNReal.coe_rpow_of_nonneg _ hν,
    ENNReal.coe_rpow_of_nonneg _ (mul_nonneg (by linarith) hν)] at hcast

/-! ## Step 11, with step 10's rescaling loss included -/

/-- **Step 11, honest about the scale at which the fine factor is
read.**

`Kakeya.ML2Spine.multiplicity_le_of_two_factors` takes the fine factor at the *ambient* scale
`δ̃`.  Step 10 produces it at the *rescaled* scale `δ' = δ̃/b`, and the conversion costs the factor
`(1-ε₂)` on the gain, so the exponent hypothesis is `θ ≤ (1-ε₂) ν - 2 η' - κ` and **not**
`θ ≤ ν - 2 η' - κ`.  Nothing else changes. -/
theorem multiplicity_le_of_two_factors_rescaled
    {δt δ' : ℝ≥0} {mu mub muf L Cu : ℝ≥0∞} {Nb Nf N : ℕ} {β η' ν κ θ ε₂ : ℝ}
    (hδ0 : (δt : ℝ≥0∞) ≠ 0) (hδ1 : (δt : ℝ≥0∞) ≤ 1) (hβ0 : 0 ≤ β)
    (hν : 0 ≤ ν) (hε₂ : ε₂ ≤ 1) (hδ' : δ' ≤ δt ^ (1 - ε₂))
    (hsplit : mu ≤ L * (mub * muf))
    (hb : mub ≤ (δt : ℝ≥0∞) ^ (-(2 * η')) * (Nb : ℝ≥0∞) ^ β)
    (hf : muf ≤ (δ' : ℝ≥0∞) ^ ν * (Nf : ℝ≥0∞) ^ β)
    (hcard : (Nb : ℝ≥0∞) * (Nf : ℝ≥0∞) ≤ Cu * (N : ℝ≥0∞))
    (hL : L * Cu ^ β ≤ (δt : ℝ≥0∞) ^ (-κ))
    (hexp : θ ≤ (1 - ε₂) * ν - 2 * η' - κ) :
    mu ≤ (δt : ℝ≥0∞) ^ θ * (N : ℝ≥0∞) ^ β := by
  have hf' : muf ≤ (δt : ℝ≥0∞) ^ ((1 - ε₂) * ν) * (Nf : ℝ≥0∞) ^ β := by
    refine hf.trans ?_
    gcongr
    exact rpow_le_rpow_rescaled hν hε₂ hδ'
  exact ML2Spine.multiplicity_le_of_two_factors hδ0 hδ1 hβ0 hsplit hb hf' hcard hL hexp

/-- **Step 11 for the constructed spine.**  The exponent inequality is discharged by
`Kakeya.ML2Reduction.spineRung_gainBudget_of_rescaleLoss`, i.e. by the *construction*
`Kakeya.ML2Spine.spineRung`, and **not** by `Kakeya.ML2Spine.spine_gainBudget_of_loss`: the
`(1-ε₂)` of the rescaling is not affordable from the fields of `Kakeya.ML2Spine.IsSpine` alone
(`Kakeya.ML2Reduction.rescaleLoss_not_free_of_isSpine_fields`).  The price of that repair is
visible in the last binder: the multiscale loss budget is `κ ≤ 20 η_k/ε₂`, half of the
`κ ≤ 40 η_k/ε₂` that `spine_gainBudget_of_loss` grants.

The conclusion is the blueprint's `multTildeTLem2`,
`μ(𝕋̃, Ỹ) ≤ δ̃^{10 η_{j-1}/ε₂} |𝕋̃|^β`, in the exponent shape the eccentric branch also lands in. -/
theorem spine_multiplicity_le_two_factors
    {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ} {k : ℕ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hk : k < ML2Spine.spineCount ϖ ε₁)
    {δt b δ' : ℝ≥0} {mu mub muf L Cu : ℝ≥0∞} {Nb Nf N : ℕ} {κ : ℝ}
    (hδ0 : 0 < δt) (hδ1 : δt ≤ 1)
    (hbw : δt ^ ML2Spine.spineEps₂ ϖ ε₁ ≤ b) (hprod : δ' * b = δt)
    (hsplit : mu ≤ L * (mub * muf))
    (hb : mub ≤ (δt : ℝ≥0∞) ^
          (-(2 * (12 * ML2Spine.spineRung β ϖ ε₁ gain dens k / (ML2Spine.spineDiv ϖ ε₁ * β))))
        * (Nb : ℝ≥0∞) ^ β)
    (hf : muf ≤ (δ' : ℝ≥0∞) ^ (gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2))
        * (Nf : ℝ≥0∞) ^ β)
    (hcard : (Nb : ℝ≥0∞) * (Nf : ℝ≥0∞) ≤ Cu * (N : ℝ≥0∞))
    (hL : L * Cu ^ β ≤ (δt : ℝ≥0∞) ^ (-κ))
    (hκ : κ ≤ 20 * ML2Spine.spineRung β ϖ ε₁ gain dens k / ML2Spine.spineEps₂ ϖ ε₁) :
    mu ≤ (δt : ℝ≥0∞) ^
          (10 * ML2Spine.spineRung β ϖ ε₁ gain dens k / ML2Spine.spineEps₂ ϖ ε₁)
        * (N : ℝ≥0∞) ^ β := by
  have hsp := ML2Spine.spineRung_isSpine (β := β) (ϖ := ϖ) (ε₁ := ε₁) (gain := gain)
    (dens := dens) hβ0 hβ1 hϖ hε₁ hgain hdens
  have hpos : (0 : ℝ) < ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2 := by
    have := hsp.rung_pos (k + 1)
    linarith
  have hν : 0 ≤ gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) := (hgain _ hpos).le
  have hbud := spineRung_gainBudget_of_rescaleLoss hβ0 hβ1 hϖ hε₁ hgain hdens hk hκ
  refine multiplicity_le_of_two_factors_rescaled (by simpa using hδ0.ne')
    (by exact_mod_cast hδ1) hβ0.le hν (hsp.eps₂_le_half.trans (by norm_num))
    (rescaledScale_le hδ0 hbw hprod) hsplit hb hf hcard hL ?_
  linarith

/-! ## Step 8's count clause, read on Lemma 9.1's window -/

/-! ## The count budget of step 10, with the ED-multiplicity carried as a parameter -/

/-! ## Step 10, at the post-uniformisation family

**Which interface this section is stated over, and why not.**  `Reduction/
SpineCanonicalCover.lean` §1 offers an *upstairs-cover* bundle whose sixth and seventh clauses
price essential distinctness against the maximal density of the pushed-down `ρ`-family.  That
bundle is **unsatisfiable**: a family of `ρ`-tubes in `B₁` obeys `Δ_max ≥ |t| ρ²/3`, so the count
clause `ρ^{-2-ζ'} ≤ |t|` forces `Δ_max ≥ ρ^{-ζ'}/3` and the slack clause then demands
`refineToEssDistinctLeaves.C 3 ≤ 3 ρ^ζ ≤ 3`, while that constant exceeds `4`.  Consuming it would
make every theorem below vacuously true.  So step 10 is stated here over the
**essential-distinctness** interface instead — the `hcanon` binder of the existing
`Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer_of_canonicalCover`, which asks for a
pairwise essentially distinct all-used `ρ`-family over the rescaled bodies and never divides by a
density.  That binder is satisfiable — the ceiling `Kakeya.Tube.card_le_of_EssDistinct` allows
`C ρ^{-6}` essentially distinct `ρ`-tubes in `B₁` in dimension 3 while Lemma 9.1 asks only for
`ρ^{-2-ζ}` — and its producer is the maximal-essentially-distinct extraction priced by the
family's **ED-multiplicity** `M` rather than by `Δ_max`: `M` is a counting multiplicity, equals
`1` on an already essentially distinct family, and carries no `ρ`-power floor, which is exactly
why the budget clause `M · spineOuterCountLoss R ≤ ρ^{-(ζ'-ζ)}` is satisfiable where the
`Δ_max`-priced one was not.

`Kakeya.ML2Reduction.count_clause_at_uniformised` is *not* used below for the same reason: it
routes through the upstairs bundle.  Its tail — the `hU`-rewrite that moves the count clause from
the outer family to the uniformised `U'` — is reproved here on top of
`Kakeya.ML2Reduction.outerCanonicalCover_of_canonicalCover`, which is bundle-free. -/

/-- **Step 10, applied where the uniformity witness actually
lives.**

`Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer` pins its `huni` binder to
`(s, outerFamily … 𝕋)` — the whole index set, the unrefined shading — and no uniformiser in the
tree produces that: `Kakeya.ML2Reduction.exists_outerShadedUniformTubeSet` returns a subfamily
`s' ⊆ s` together with a *shade-shrunk* `U'` whose tubes agree with the outer tubes.  So Lemma 9.1
is applied directly, at `(s', U')`, through `Kakeya.ML2Reduction.Lemma91At`, which quantifies over
an arbitrary family.

Of Lemma 9.1's five hypotheses on the family, three are discharged here at **no** loss:

* the unit-ball containment, by `Kakeya.ML2Reduction.carrier_subset_closedBall_of_toTube_eq`
  composed with `Kakeya.ML2Reduction.outerFamily_carrier_subset_closedBall`;
* `Δ_max ≤ (δ')^{-ηd}`, by `Kakeya.ML2Reduction.maxDensity_eq_of_toTube_eq` (the shade does not
  enter `Δ_max`), `Kakeya.maxDensity_mono` for `s' ⊆ s`, and the outer-tube replacement's constant
  `hloss`;
* the count clause, by `Kakeya.ML2Reduction.count_clause_at_uniformised_of_canonicalCover` from
  the essentially distinct cover of the rescaled bodies.

`hcanon` is the `hcanon` binder of
`Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer_of_canonicalCover` character for
character, so a producer plugs in literally.  The ED-multiplicity extraction is such a producer:
its output is this binder, from an upstairs family at `ρ θ` carrying `0 < M`, the two containment
clauses, the ED-multiplicity clause
`∀ i ∈ t, #{ j ∈ t | ¬ ED (outerTube … (W j)) (outerTube … (W i)) } ≤ M`, the budget
`M · spineOuterCountLoss R ≤ ρ^{-(ζ'-ζ)}` and the count `ρ^{-2-ζ'} ≤ |t|`.  The last of those is
what `Kakeya.ML2Reduction.window_count_of_spine_window` above delivers from step 8, and the budget
is priced in exponents by `Kakeya.ML2Reduction.edSlack_of_exponents`.

The fullness floor `hfull` is *not* discharged here: it is the one hypothesis the shade refinement
genuinely moves, and its retention is the `fullness'` clause of
`Kakeya.ML2Reduction.exists_outerShadedUniformTubeSet`.  It is carried as a binder. -/
theorem fine_factor_of_lemma91At_of_canonicalCover
    {β ϖ ζ ν ν₀ ηd cst qc : ℝ} {b δt δ' : ℝ≥0} {R : ℝ}
    (hL : Lemma91At.{u} β ϖ ζ ν₀ ηd δ')
    -- the exact negation of the vacuity condition
    -- `Kakeya.VeryNotSticky.lemma91Binders_vacuous_of_exponents` (cited by name only — this is a
    -- hypothesis, not a consumed term, so the witness leaf is NOT imported): Lemma 9.1's binder
    -- list is jointly unsatisfiable whenever `2 + ηd < (1 - ϖ) * (2 + ζ)`, and `hζ` is exactly
    -- its negation, so it is what keeps `hL` above from being vacuously true.  Corroborated
    -- caller-side by the source's own `ζ ≤ (4/5) ζ_*`.
    --
    -- DECLARED MISMATCH against the eliminator/companion condition (
    -- /-G/-J), resolved -C1: that condition protects LEDGER-BEARING content —
    -- the count clause, the window endpoints, the budget inequalities and the conclusion
    -- exponent — and not the binder list against an inert addition.  A guard may be added here;
    -- a budget or a window may not.  This is where vacuity actually bites (V-1 at the
    -- load-bearing declaration).
    (_hζ : ζ * (1 - ϖ) ≤ ηd + 2 * ϖ)
    (hsit : Tube.IsRescalingSituation b δt δ' R 3) (hR : 0 < R) (_hR1 : 1 ≤ R)
    (_hτσ : (δt : ℝ) / (b : ℝ) ≤ 4 * (δ' : ℝ)) (hδ'0 : 0 < δ') (_hϖ0 : 0 ≤ ϖ)
    (hβ0 : 0 ≤ β) (hqc0 : 0 < qc) (hνqc : ν + 3 * qc ≤ ν₀) (h3qc : 3 * qc ≤ ηd)
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3))) (m : EuclideanSpace ℝ (Fin 3))
    {α : Type u} {s s' : Finset α} (_hs' : s' ⊆ s)
    (𝕋 : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3)))
    (U' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3)))
    (hU : Kakeya.VeryNotSticky.CentredHandBack hsit hR T₀ m qc s s' 𝕋 U')
    (_hsub : ∀ i ∈ s, (𝕋 i).carrier ⊆ T₀.carrier)
    (_hloss : outerLoss R ≤ δ' ^ (-cst))
    (huni : ∃ C : ℝ≥0, 1 ≤ C ∧ (C : ℝ≥0∞) ≤ (δ' : ℝ≥0∞) ^ (-ηd) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s' U' (Tube.ssfGridLen δ') C))
    (hcnt : ∀ ρ : ℝ≥0, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
        (tρ : Set κ).Pairwise
          (fun j k ↦ _root_.IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
        (∀ j ∈ tρ, ∃ i ∈ s', (U' i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
        (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) :
    ShadedBody.multiplicity s
        (fun i ↦ (outerFamily hsit.pos_ambient T₀ hR δ' 𝕋 i).toShadedBody)
      ≤ (δ' : ℝ≥0∞) ^ ν * (s.card : ℝ≥0∞) ^ β := by
  have hδE0 : (δ' : ℝ≥0∞) ≠ 0 := by simpa using ne_of_gt hδ'0
  have hδEt : (δ' : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := ENNReal.coe_ne_top
  have hδ'1 : (δ' : ℝ≥0∞) ≤ 1 := by
    have : (δ' : ℝ) ≤ 1 := le_trans hsit.out_le_quarter (by norm_num)
    exact_mod_cast this
  -- the density and fullness Lemma 9.1 reads, from the hand-back
  have hmax' : Kakeya.maxDensity s' (fun i ↦ (U' i).toConvexSpaceBody)
      ≤ (δ' : ℝ≥0∞) ^ (-ηd) :=
    hU.maxDensity_le.trans (ENNReal.rpow_le_rpow_of_exponent_ge hδ'1 (by linarith))
  have hfull' : ShadedBody.fullness s' (fun i ↦ (U' i).toShadedBody) ≥ δ' ^ ηd := by
    have h : ((δ' ^ ηd : ℝ≥0) : ℝ≥0∞)
        ≤ ((ShadedBody.fullness s' (fun i ↦ (U' i).toShadedBody) : ℝ≥0) : ℝ≥0∞) := by
      rw [ENNReal.coe_rpow_of_ne_zero (ne_of_gt hδ'0)]
      exact (ENNReal.rpow_le_rpow_of_exponent_ge hδ'1 h3qc).trans hU.fullness_ge
    exact_mod_cast h
  -- Lemma 9.1 at the centred representatives
  have hfine : ShadedBody.multiplicity s' (fun i ↦ (U' i).toShadedBody)
      ≤ (δ' : ℝ≥0∞) ^ ν₀ * (s'.card : ℝ≥0∞) ^ β :=
    hL s' U' hU.contained hU.centred huni hmax' hfull' hcnt
  -- the hand-back transports it to the represented family, paying `3 qc`
  have hsplit : (δ' : ℝ≥0∞) ^ (-(3 * qc)) * (δ' : ℝ≥0∞) ^ ν₀
      = (δ' : ℝ≥0∞) ^ (ν₀ - 3 * qc) := by
    rw [← ENNReal.rpow_add _ _ hδE0 hδEt]; ring_nf
  calc ShadedBody.multiplicity s
        (fun i ↦ (outerFamily hsit.pos_ambient T₀ hR δ' 𝕋 i).toShadedBody)
      ≤ (δ' : ℝ≥0∞) ^ (-(3 * qc))
          * ShadedBody.multiplicity s' (fun i ↦ (U' i).toShadedBody) := hU.multiplicity_le
    _ ≤ (δ' : ℝ≥0∞) ^ (-(3 * qc)) * ((δ' : ℝ≥0∞) ^ ν₀ * (s'.card : ℝ≥0∞) ^ β) := by
        gcongr
    _ = (δ' : ℝ≥0∞) ^ (ν₀ - 3 * qc) * (s'.card : ℝ≥0∞) ^ β := by
        rw [← mul_assoc, hsplit]
    _ ≤ (δ' : ℝ≥0∞) ^ ν * (s.card : ℝ≥0∞) ^ β :=
        mul_le_mul' (ENNReal.rpow_le_rpow_of_exponent_ge hδ'1 (by linarith))
          (ENNReal.rpow_le_rpow hU.card_le hβ0)
/-- **The fine factor at the centred representatives** — the companion of
`Kakeya.ML2Reduction.fine_factor_of_lemma91At_of_canonicalCover` whose conclusion stays at
`(s', U')`.

This one is
Lemma 9.1 applied to the centred representatives and nothing else, so a consumer whose own ledger
already transports `(s', U')` back to the represented family — every current caller does, through
`Kakeya.ML2Reduction.multiplicity_le_of_shade_refinement` and
`Kakeya.ML2Reduction.outerFamily_multiplicity` — keeps its shape and threads only. The other one
does that transport itself, at the cost of `3 qc` on the gain (`hνqc`), and is the right entry
point for a consumer that does not.

 with the canonical-cover option (ii)  R5.2. -/
theorem fine_factor_of_lemma91At_of_canonicalCover'
    {β ϖ ζ ν₀ ηd qc : ℝ} {b δt δ' : ℝ≥0} {R : ℝ}
    (hL : Lemma91At.{u} β ϖ ζ ν₀ ηd δ')
    -- the exact negation of the vacuity condition
    -- `Kakeya.VeryNotSticky.lemma91Binders_vacuous_of_exponents` (cited by name only — this is a
    -- hypothesis, not a consumed term, so the witness leaf is NOT imported): Lemma 9.1's binder
    -- list is jointly unsatisfiable whenever `2 + ηd < (1 - ϖ) * (2 + ζ)`, and `hζ` is exactly
    -- its negation, so it is what keeps `hL` above from being vacuously true.  Corroborated
    -- caller-side by the source's own `ζ ≤ (4/5) ζ_*`.
    --
    -- DECLARED MISMATCH against the eliminator/companion condition (
    -- /-G/-J), resolved -C1: that condition protects LEDGER-BEARING content —
    -- the count clause, the window endpoints, the budget inequalities and the conclusion
    -- exponent — and not the binder list against an inert addition.  A guard may be added here;
    -- a budget or a window may not.  This is where vacuity actually bites (V-1 at the
    -- load-bearing declaration).
    (_hζ : ζ * (1 - ϖ) ≤ ηd + 2 * ϖ)
    (hsit : Tube.IsRescalingSituation b δt δ' R 3) (hR : 0 < R)
    (hδ'0 : 0 < δ') (hqc0 : 0 < qc) (h3qc : 3 * qc ≤ ηd)
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3))) (m : EuclideanSpace ℝ (Fin 3))
    {α : Type u} {s s' : Finset α}
    (𝕋 : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3)))
    (U' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3)))
    (hU : Kakeya.VeryNotSticky.CentredHandBack hsit hR T₀ m qc s s' 𝕋 U')
    (huni : ∃ C : ℝ≥0, 1 ≤ C ∧ (C : ℝ≥0∞) ≤ (δ' : ℝ≥0∞) ^ (-ηd) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s' U' (Tube.ssfGridLen δ') C))
    (hcnt : ∀ ρ : ℝ≥0, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
        (tρ : Set κ).Pairwise
          (fun j k ↦ _root_.IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
        (∀ j ∈ tρ, ∃ i ∈ s', (U' i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
        (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) :
    ShadedBody.multiplicity s' (fun i ↦ (U' i).toShadedBody)
      ≤ (δ' : ℝ≥0∞) ^ ν₀ * (s'.card : ℝ≥0∞) ^ β := by
  have hδ'1 : (δ' : ℝ≥0∞) ≤ 1 := by
    have : (δ' : ℝ) ≤ 1 := le_trans hsit.out_le_quarter (by norm_num)
    exact_mod_cast this
  have hmax' : Kakeya.maxDensity s' (fun i ↦ (U' i).toConvexSpaceBody)
      ≤ (δ' : ℝ≥0∞) ^ (-ηd) :=
    hU.maxDensity_le.trans (ENNReal.rpow_le_rpow_of_exponent_ge hδ'1 (by linarith))
  have hfull' : ShadedBody.fullness s' (fun i ↦ (U' i).toShadedBody) ≥ δ' ^ ηd := by
    have h : ((δ' ^ ηd : ℝ≥0) : ℝ≥0∞)
        ≤ ((ShadedBody.fullness s' (fun i ↦ (U' i).toShadedBody) : ℝ≥0) : ℝ≥0∞) := by
      rw [ENNReal.coe_rpow_of_ne_zero (ne_of_gt hδ'0)]
      exact (ENNReal.rpow_le_rpow_of_exponent_ge hδ'1 h3qc).trans hU.fullness_ge
    exact_mod_cast h
  exact hL s' U' hU.contained hU.centred huni hmax' hfull' hcnt

/-! ## The price of the shading refinement -/

/-- **A shade refinement costs exactly its shading mass.**

The uniformiser of the estimate returns a subfamily `s' ⊆ s` and a family `V'` with the same carriers
and *smaller* shades.  Multiplicity is a quotient, and the denominator moves the *helpful* way:
`⋃_{s'} Y' ⊆ ⋃_{s} Y` for free.  So the whole price of the refinement is the numerator, i.e. the
shading-mass retention `∑_s |Y_i| ≤ C ∑_{s'} |Y'_i|`, and there is no second loss hiding in the
union.

This is the bridge from step 10's conclusion at `(s', U')` back to the family step 11 multiplies,
and `C` is the only thing a producer of the refinement owes. -/
theorem multiplicity_le_of_shade_refinement {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} {s s' : Finset ι} (hs : s' ⊆ s) {V V' : ι → ShadedBody E}
    (hshade : ∀ i, (V' i).shade ⊆ (V i).shade) {C : ℝ≥0∞}
    (hsum : ∑ i ∈ s, volume (V i).shade ≤ C * ∑ i ∈ s', volume (V' i).shade) :
    ShadedBody.multiplicity s V ≤ C * ShadedBody.multiplicity s' V' := by
  have hun : volume (⋃ i ∈ s', (V' i).shade) ≤ volume (⋃ i ∈ s, (V i).shade) := by
    refine measure_mono ?_
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨i, hs hi, hshade i hxi⟩
  rw [ShadedBody.multiplicity_eq_div, ShadedBody.multiplicity_eq_div, mul_div_assoc']
  gcongr

/-! ## Steps 3–11, assembled -/

/-- **The non-eccentric case of GWZ Main Lemma 2, steps 3–11, assembled**
.

```
μ(𝕋̃, Ỹ) ≤ δ̃^{10 η_{j-1}/ε₂} |𝕋̃|^β
```

### The hypothesis interface — what the estimate must supply

Neither the rescaled datum `(𝕋̃, Ỹ)` at `δ̃ = τ/θ` nor its plank factoring exists yet, so they
enter below as explicit hypotheses.  Reading the binders in order, a producer owes:

1. **the spine at the rung `k`** — `0 < β ≤ 1`, `0 < ϖ`, `0 < ε₁`, positivity of the two exponent
   functions of `Kakeya.ML2Assembly.Lemma91ParamsAt`, and `k < N`.  Nothing else: every numeric
   constraint is inside `Kakeya.ML2Spine.spineRung_isSpine`;
2. **the scales** `δ̃`, `b`, `δ'` with `δ' b = δ̃`, `0 < δ̃ ≤ 1`, `0 < δ'`, `b ≤ 1`, `δ̃ ≤ b`, and
   **step 5's `δ̃^{ε₂} ≤ b`** (`Kakeya.ML2Spine.spine_le_of_maxDensity_le_window`);
3. **the coarse family** `(t', Zρ)` of `b`-tubes with the unit-ball containment, the fullness floor
   `λ ≥ b^{ηc}` and **step 3's** `Δ_max(𝕋̃_b) ≤ δ̃^{-η'_k}`, together with the eventual statement of
   `Kakeya.ML2Spine.exists_multiplicity_coarse_bound` held at this `b` — that is step 4;
4. **the fine family**: the fibre `fib`, its shading `Z'`, the rescaling situation
   `Tube.IsRescalingSituation b δ̃ δ' R 3`, the coarse tube `T₀` containing every `Z' i`, the
   uniformised `(s', U')` of `Kakeya.ML2Reduction.exists_outerShadedUniformTubeSet` with its two
   defining clauses `hU`/`hUshade`, and Lemma 9.1 as a term at `δ'`;
5. **the essentially distinct cover** `hcanon` — at every scale `ρ` of Lemma 9.1's window, one
   pairwise essentially distinct all-used family of `ρ`-tubes over the rescaled bodies, of
   cardinality at least `spineOuterCountLoss R · ρ^{-2-ζ}`, over the **post**-uniformisation index
   set `s'`.  This is the `hcanon` binder of
   `Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer_of_canonicalCover` verbatim.  It is
   **not** the upstairs bundle of `Reduction/SpineCanonicalCover.lean` §1: that bundle is
   unsatisfiable (see the section header above), so consuming it would make this theorem vacuous;
6. **the shading-mass retention** `hret` of the uniformisation — the *only* price the refinement
   charges (`Kakeya.ML2Reduction.multiplicity_le_of_shade_refinement`);
7. **step 9's split** `hsplit` (`Kakeya.ML2Reduction.exists_spineOneScale`), the **cardinality
   multiplicativity** `hcard` (shape at the two scales `b` and `δ̃`), and the loss budget
   `L · Cf · Cu^β ≤ δ̃^{-κ}` with `κ ≤ 20 η_k/ε₂`.

**The budget in binder 7 is `20 η_k/ε₂`, not the `40 η_k/ε₂` of
`Kakeya.ML2Spine.spine_gainBudget_of_loss`.**  That halving is step 10's rescaling loss, and it is
not optional: see `Kakeya.ML2Reduction.spine_multiplicity_le_two_factors`. -/
theorem spine_multiplicity_le_nonEccentric_of_canonicalCover
    {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ} {k : ℕ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hk : k < ML2Spine.spineCount ϖ ε₁)
    {δt b δ' : ℝ≥0} {R : ℝ}
    (hδ0 : 0 < δt) (hδ1 : δt ≤ 1) (hδ'0 : 0 < δ') (hb1 : b ≤ 1) (hδtb : δt ≤ b)
    (hbw : δt ^ ML2Spine.spineEps₂ ϖ ε₁ ≤ b) (hprod : δ' * b = δt)
    {κc : Type u} {t' : Finset κc} {Zρ : κc → ShadedTube b (EuclideanSpace ℝ (Fin 3))} {ηc : ℝ}
    (hcoarse : ∀ (dt : ℝ≥0), dt ≠ 0 → dt ≤ b → b ≤ 1 →
      ∀ {ι : Type u} (t : Finset ι) (T : ι → ShadedTube b (EuclideanSpace ℝ (Fin 3))),
        (∀ i, (T i).carrier ⊆ closedBall 0 1) →
        (ShadedBody.fullness t (fun i ↦ (T i).toShadedBody) : ℝ) ≥ (b : ℝ) ^ ηc →
        Kakeya.maxDensity t (fun i ↦ (T i).toConvexSpaceBody)
          ≤ (dt : ℝ≥0∞) ^ (-(12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
              / (ML2Spine.spineDiv ϖ ε₁ * β))) →
        ShadedBody.multiplicity t (fun i ↦ (T i).toShadedBody)
          ≤ (dt : ℝ≥0∞) ^ (-(2 * (12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
              / (ML2Spine.spineDiv ϖ ε₁ * β)))) * (t.card : ℝ≥0∞) ^ β)
    (hballb : ∀ j, (Zρ j).carrier ⊆ closedBall 0 1)
    (hfullb : (ShadedBody.fullness t' (fun j ↦ (Zρ j).toShadedBody) : ℝ) ≥ (b : ℝ) ^ ηc)
    (hDb : Kakeya.maxDensity t' (fun j ↦ (Zρ j).toConvexSpaceBody)
      ≤ (δt : ℝ≥0∞) ^ (-(12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
          / (ML2Spine.spineDiv ϖ ε₁ * β))))
    {α : Type u} {fib s' : Finset α} (hs' : s' ⊆ fib)
    {Z' : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3))}
    {U' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))}
    (hsit : Tube.IsRescalingSituation b δt δ' R 3) (hR : 0 < R) (hR1 : 1 ≤ R)
    (hτσ : (δt : ℝ) / (b : ℝ) ≤ 4 * (δ' : ℝ))
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3))) (m : EuclideanSpace ℝ (Fin 3))
    (hsubfib : ∀ i ∈ fib, (Z' i).carrier ⊆ T₀.carrier)
    {cst ζ ηd qc : ℝ} (hqc0 : 0 < qc) (h3qc : 3 * qc ≤ ηd)
    (hcb : Kakeya.VeryNotSticky.CentredHandBack hsit hR T₀ m qc fib s' Z' U')
    (hL91 : Lemma91At.{u} β ϖ ζ
      (gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) + 3 * qc) ηd δ')
    -- the exact negation of the vacuity condition
    -- `Kakeya.VeryNotSticky.lemma91Binders_vacuous_of_exponents` (cited by name only — this is a
    -- hypothesis, not a consumed term, so the witness leaf is NOT imported): Lemma 9.1's binder
    -- list is jointly unsatisfiable whenever `2 + ηd < (1 - ϖ) * (2 + ζ)`, and `hζ` is exactly
    -- its negation, so it is what keeps `hL91` above from being vacuously true.  Corroborated
    -- caller-side by the source's own `ζ ≤ (4/5) ζ_*`.
    (hζ : ζ * (1 - ϖ) ≤ ηd + 2 * ϖ)
    (hloss : outerLoss R ≤ δ' ^ (-cst))
    (_hmax : Kakeya.maxDensity fib (fun i ↦ (Z' i).toConvexSpaceBody)
      ≤ (δ' : ℝ≥0∞) ^ (-(ηd - cst)))
    (hfull : ShadedBody.fullness s' (fun i ↦ (U' i).toShadedBody) ≥ δ' ^ ηd)
    (huni : ∃ C : ℝ≥0, 1 ≤ C ∧ (C : ℝ≥0∞) ≤ (δ' : ℝ≥0∞) ^ (-ηd) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s' U' (Tube.ssfGridLen δ') C))
    (hcnt : ∀ ρ : ℝ≥0, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
        (tρ : Set κ).Pairwise
          (fun j k ↦ _root_.IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
        (∀ j ∈ tρ, ∃ i ∈ s', (U' i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
        (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ))
    {Cf mu L Cu : ℝ≥0∞} {N : ℕ} {κ : ℝ}
    (hCf1 : (1 : ℝ≥0∞) ≤ Cf)
    (hsplit : mu ≤ L * (ShadedBody.multiplicity t' (fun j ↦ (Zρ j).toShadedBody)
      * ShadedBody.multiplicity fib (fun i ↦ (Z' i).toShadedBody)))
    (hcard : (t'.card : ℝ≥0∞) * (fib.card : ℝ≥0∞) ≤ Cu * (N : ℝ≥0∞))
    (hLoss : L * Cf * Cu ^ β ≤ (δt : ℝ≥0∞) ^ (-κ))
    (hκ : κ ≤ 20 * ML2Spine.spineRung β ϖ ε₁ gain dens k / ML2Spine.spineEps₂ ϖ ε₁) :
    mu ≤ (δt : ℝ≥0∞) ^
        (10 * ML2Spine.spineRung β ϖ ε₁ gain dens k / ML2Spine.spineEps₂ ϖ ε₁)
      * (N : ℝ≥0∞) ^ β := by
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  -- step 4: the coarse factor at the ambient scale `δ̃`
  have hb4 := hcoarse δt (ne_of_gt hδ0) hδtb hb1 t' Zρ hballb hfullb hDb
  -- step 10 on the REPRESENTED family: the hand-back's transport is inside the eliminator, so
  -- the `3 qc` is charged once, in `hL91`'s gain ((B) +  R7.1: the
  -- consumer's `hf` exponent is exact, so `ν₀ = gain(…) + 3 qc` and the spine is instantiated at
  -- `gain' := gain − 3 qc`).  `hUshade`, `hret` and `hretm` are deleted: the centred
  -- representative's shading is the `normalise` image, so the first two are FALSE (V-1).
  have h10 := fine_factor_of_lemma91At_of_canonicalCover
    (ν := gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2))
    hL91 hζ hsit hR hR1 hτσ hδ'0 hϖ.le hβ0.le hqc0 le_rfl h3qc T₀ m hs' Z' U' hcb hsubfib hloss
    huni hcnt
  have h10' : ShadedBody.multiplicity fib (fun i ↦ (Z' i).toShadedBody)
      ≤ (δ' : ℝ≥0∞) ^ (gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2))
        * (fib.card : ℝ≥0∞) ^ β := by
    rw [← outerFamily_multiplicity hn hsit hR hτσ hsubfib]
    exact h10
  -- step 9's split; `Cf` keeps its text and needs only `1 ≤ Cf`
  have hsplit2 : mu ≤ (L * Cf) * (ShadedBody.multiplicity t' (fun j ↦ (Zρ j).toShadedBody)
      * ShadedBody.multiplicity fib (fun i ↦ (Z' i).toShadedBody)) := by
    refine hsplit.trans (mul_le_mul' ?_ le_rfl)
    calc L = L * 1 := (mul_one L).symm
      _ ≤ L * Cf := by gcongr
  exact spine_multiplicity_le_two_factors hβ0 hβ1 hϖ hε₁ hgain hdens hk hδ0 hδ1 hbw hprod
    hsplit2 hb4 h10' hcard hLoss hκ

end Kakeya.ML2Reduction

end

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineDescentSite
public import Kakeya.DimensionThree.MainLemma2.VeryNotStickyClosed
public import Kakeya.DimensionThree.MainLemma2.AxialEDObstruction
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSiteClosure

/-!
# Non-vacuity witnesses: the site hypothesis and GWZ Lemma 9.1's binder list

`Kakeya.ML2Core.geometricCoreAt_of_site`, `Kakeya.ML2Core.geometricCoreAt_of_descent` and
`Kakeya.ML2Cap.mainLemma2Statement_of_geometricCoreAt_free` are all axiom-clean, so a **vacuously
discharged** `hsite` would prove Main Lemma 2 from nothing while `check`, `scan`, `axioms` and
`guard` all stayed green.  This leaf supplies the control that no mechanical gate can: a family for which every clause of the hypothesis list actually holds.

## What is proved

* `Kakeya.ML2Wit.exists_siteRows_nonvacuity` — **W1.**  There is a `Cu₀` such that for every
  `ε > 0` there is a `δ < ε` and a concrete `(s, T)` in universe `v` meeting the four input
  clauses of `hsite` (`Kakeya.ML2Wit.SiteInputs`) **and** its whole conclusion row list
  (`Kakeya.ML2Wit.SiteRows`) — the retained `u' ⊆ s`, the hierarchy at the hoisted `Cu₀`, the
  mass ledger, `Kakeya.ML2Core.IsTrialAtGain` and all four absorptions included.  So `hsite` is
  not vacuously true on any tail of `𝓝[>] 0`.
* `Kakeya.ML2Wit.exists_siteWitness_nonvacuity` — **W1′, the closing skeleton's shape.**  The row
  block of `Kakeya.ML2Core.SiteWitness` (the *downward* re-cut: four data existentials, ten rows, no
  `ε₀'`/`g'`) is inhabited at arbitrarily small `δ`, at the same absolute `Cu₀` and — the
  measurement that matters — with **`K = 1`**.  Taking `u' := s` (the ambient family already *is*
  the retained one) and `lam := 1` makes the mass ledger an identity, because
  `Kakeya.ML2Core.stateMass` ignores the shading level, so the outer margin row
  `K · δ^(dm − aL) ≤ 1` reduces to `aL ≤ dm` and the `α ≤ dm − aL ≤ β/48000` cap is met with room
  to spare. `Kakeya.ML2Wit.SiteWitnessRows` makes these site-witness conditions explicit.
* `Kakeya.ML2Wit.SiteHypothesis` and the `example` beside it are a **compatibility**: the row list is
  spelled out here and handed to `Kakeya.ML2Core.geometricCoreAt_of_site`, so a drift between this
  file's transcription and the tree's stops elaboration rather than passing silently.  Measured
  firing control: perturbing one row (`Cu ≤ Cu₀` to `Cu ≤ Cu₀ + 1`) makes the `example` fail.
* `Kakeya.ML2Wit.exists_lemma91BindersNoCount_nonvacuity` — **W2.**  Five of GWZ Lemma 9.1's six
  binders — ball, **centredness**, `1 ≤ C ≤ δ^{-η}` uniformity, `Δ_max ≤ δ^{-η}`, `λ ≥ δ^{η}` —
  hold simultaneously on a family that is *not* axially degenerate (its carriers are pairwise
  disjoint and it has more than `δ^{-1}` members), at arbitrarily small `δ`.  This is the point
  `Kakeya.VeryNotSticky.exists_witnessFamily` cannot make: its family is a set of axial translates
  of one tube, which the centredness binder excludes.  `Kakeya.ML2Wit.lemma91_of_binders` is the
  compatibility: GWZ Lemma 9.1 restated through the two `def`s, so a transcription weaker than the
  tree's does not elaborate (firing control: replacing the centredness clause by `True` breaks it).
* `Kakeya.ML2Wit.lemma91Binders_vacuous_of_exponents` — **the sixth binder is the one that is not
  jointly satisfiable.**  If `(1-ϖ)(2+ζ) > 2 + η` then at every small `δ` *no* family meets both
  the five binders and the `ρ`-count, so GWZ Lemma 9.1 is vacuously true at those exponents.  Two
  bounds meet: `#𝕋_ρ ≤ 2 · 385^6 · #𝕋` (`Kakeya.ML2Wit.card_used_le`, from
  `Kakeya.VeryNotSticky.card_le_of_ed_of_endpoints_confined`) and `#𝕋 ≤ C₃ δ^{-2-η}`
  (`Kakeya.ML2Wit.card_le_of_maxDensity`), against `#𝕋_ρ ≥ ρ^{-2-ζ} = δ^{-(1-ϖ)(2+ζ)}` at the
  window's fine end `ρ = δ^{1-ϖ}`.  The usable tolerance range is `ζ ≤ (η + 2ϖ)/(1-ϖ)`, and
  `Kakeya.ML2Wit.vacuity_range_nonempty` records that the excluded range is not empty.

## The family

`Kakeya.ML2Wit.wcore` is an `M × M` grid of parallel `δ`-tubes at `δ = 1/(24 M)`, spaced `3 δ`
apart in the two transverse coordinates and centred on the third axis.  Three properties do all
the work:

* the carriers are **pairwise disjoint** (`Kakeya.ML2Wit.wcarrier_disjoint`), which gives
  `Δ_max ≤ 1` (`Kakeya.ML2Wit.maxDensity_le_one_of_disjoint`) — the *only* route to a density
  bound below `δ^{-η}` for a family of more than `δ^{-1}` tubes, since
  `Kakeya.maxDensity_le_card` never gets below the cardinality;
* they are **centred** in the sense of `Kakeya.Tube.IsCentred` (`Kakeya.ML2Wit.wcore_isCentred`):
  the core's midpoint is orthogonal to its direction;
* the family is **uniform at an absolute constant** after passing to the retained subfamily of
  `Kakeya.ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf`, which costs `δ^{-1/2}` of the
  cardinality and leaves `≥ δ^{-1}` members.  The shading is then re-set to the whole carrier, so
  no fullness is lost; the hierarchy is untouched because it only reads the tubes.

**Scope.**  A non-vacuity witness says the hypothesis list is inhabited; it does not say the
site's *intended* families satisfy it.  The trial `Kakeya.ML2Core.IsTrialAtGain` is met here
through its sticky exit, which for a disjoint family is an identity
(`∑ |Y_i| = |⋃ Y_i|`), and the loss is `Λ = 1`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric ConvexSpaceBody ShadedBody

namespace Kakeya.ML2Wit

open Kakeya.VeryNotSticky.Produce (E3)

/-! ## Generic: a pairwise disjoint family has maximal density at most one -/

/-! ## The grid family -/

noncomputable def ax (k : Fin 3) : E3 := EuclideanSpace.single k (1 : ℝ)

/-! ## The fully shaded grid family, indexed in an arbitrary universe -/

universe v

/-! ## Generic consequences of disjointness -/

/-! ## The row list of `hsite`, named -/

/-- The conclusion row list of `Kakeya.ML2Core.geometricCoreAt_of_site`'s `hsite`, verbatim
(the C1 shape: the hierarchy sits on a **retained** `u' ⊆ s`, and the chain's mass ledger and its
two outer absorptions stand beside the descent's). -/
def SiteRows (β ϖ ε₁ : ℝ) (gain dens : ℝ → ℝ) (Cu₀ : ℝ≥0) {δ : ℝ≥0} {ι : Type v}
    (s : Finset ι) (T : ι → ShadedTube δ E3) : Prop :=
  ∃ u' : Finset ι, u' ⊆ s ∧
  ∃ (Cu : ℝ≥0) (𝒰 : Tube.UniformTubeSet u' (fun i => (T i).toTube)
      (Tube.ssfGridLen δ) Cu) (lam : ℝ≥0) (Λ K : ℝ≥0∞)
      (ε₀ g ε₀' g' ηin h α : ℝ),
    Cu ≤ Cu₀ ∧
    0 < δ ∧ δ < 1 ∧ 0 < h ∧ 1 ≤ Λ ∧ Λ ≠ ⊤ ∧
    (u'.card : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ)) ∧
    (Cu : ℝ) ≤ (δ : ℝ) ^ (-(1 : ℝ)) ∧
    u'.Nonempty ∧
    Kakeya.maxDensity u' (fun i => (T i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-ηin) ∧
    0 < lam ∧
    ML2Shaded.HasDenseShading lam u' (fun i => (T i).toShadedBody) ∧
    (Λ ^ ML2Core.potentialCeil h 5 δ * (((δ : ℝ≥0) ^ ηin / 2 : ℝ≥0) : ℝ≥0∞)
      ≤ (((δ : ℝ≥0) ^ (ηin - α) / 2 : ℝ≥0) : ℝ≥0∞)) ∧
    ((((δ : ℝ≥0) ^ (ηin - α) / 2 : ℝ≥0) : ℝ≥0∞) ≤ (lam : ℝ≥0∞)) ∧
    ML2Core.IsTrialAtGain ε₀ g β h ηin 𝒰 Λ ∧
    (Λ ^ ML2Core.potentialCeil h 5 δ * (δ : ℝ≥0∞) ^ (-ε₀) ≤ (δ : ℝ≥0∞) ^ (-ε₀')) ∧
    (Λ ^ ML2Core.potentialCeil h 5 δ * (δ : ℝ≥0∞) ^ g ≤ (δ : ℝ≥0∞) ^ g') ∧
    ML2Core.stateMass ((s, T, (1 : ℝ≥0)) : ML2Core.DescentState ι δ)
      ≤ K * ML2Core.stateMass ((u', T, lam) : ML2Core.DescentState ι δ) ∧
    (K * (δ : ℝ≥0∞) ^ (-ε₀') ≤ (δ : ℝ≥0∞) ^ (-(β / 2))) ∧
    (K * (δ : ℝ≥0∞) ^ g'
      ≤ (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens))

/-- `hsite` itself. -/
def SiteHypothesis : Prop :=
  ∀ (β ϖ : ℝ) (gain dens : ℝ → ℝ), 0 < β → β ≤ 1 →
    ML2Assembly.Lemma91ParamsAt.{v} β ϖ gain dens →
    KatzTaoEstimate.{v} (EuclideanSpace ℝ (Fin 3)) β →
    FrostmanEstimate.{v} (EuclideanSpace ℝ (Fin 3)) β →
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∃ Cu₀ : ℝ≥0,
      ∀ᶠ (δ : ℝ≥0) in nhdsWithin 0 (Set.Ioi 0),
        ∀ {ι : Type v} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
          (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
          IsKatzTao s (fun i => (T i).toConvexSpaceBody) ((δ : ℝ≥0∞) ^ (-η)) →
          ShadedBody.fullness s (fun i => (T i).toShadedBody) ≥ δ ^ η →
          (δ : ℝ)⁻¹ ≤ (s.card : ℝ) →
          SiteRows.{v} β ϖ ε₁ gain dens Cu₀ s T

/-- **compatibility.**  `SiteHypothesis` is *the* hypothesis of the existing
`Kakeya.ML2Core.geometricCoreAt_of_site`; if the row list above ever drifts from the tree's, this
`example` stops elaborating. -/
example : SiteHypothesis.{v} → ML2Assembly.GeometricCoreAt.{v} :=
  ML2Core.geometricCoreAt_of_site

/-! ## Centredness -/

/-! ## The packaged witness family -/

/-- The full shading of a shaded tube: same tube, shade the whole carrier. -/
noncomputable def fullShade {δ : ℝ≥0} (Z : ShadedTube δ E3) : ShadedTube δ E3 where
  toTube := Z.toTube
  shade := (Z.toTube).carrier
  measurableSet_shade := (Z.toTube).toConvexSpaceBody.isCompact.measurableSet
  shade_subset := subset_rfl

/-! ## W1 — the site's row list is inhabited

The input family is the whole `M × M` grid; the retained `u'` is what the uniformisation of
`Kakeya.ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf` keeps, at the absolute constant
`Kakeya.ShadedTube.ssfUniformConst 3`.  The uniformisation is run at the exponent `β/4`, which is
what the chain's outer absorption `K · δ^{-ε₀'} ≤ δ^{-β/2}` can pay for: the ledger constant `K`
is the uniformisation's own cardinality loss `δ^{-β/4}`, and the terminal exponent is opened by
the same `β/4` (`g' = 4·spineNu + β/4`), which the second outer absorption then closes. -/

/-! ## W2 — GWZ Lemma 9.1's binder list, minus the `ρ`-count

`Kakeya.VeryNotSticky.exists_witnessFamily` inhabits the *pre-centred* binder list with a family of
axial translates of one tube — a family whose members all lie inside the union of two of them, and
which `Kakeya.Tube.IsCentred` excludes (centred tubes on a common supporting line coincide).  The
witness below is the opposite extreme: pairwise **disjoint** carriers, all centred, and more than
`δ^{-1}` of them, so the axial refutation does not transfer to it. -/

/-! ## The `ρ`-count binder is the one that is *not* jointly satisfiable

The five binders above are met by the grid family, and so is the trial.  The **count** binder is
different, and this section prices it exactly.  Two bounds meet:

* a `ρ`-tube of an all-used, essentially distinct family contains a member of `s`, and only
  `2 · 385^6` pairwise essentially distinct `ρ`-tubes can contain one and the same `δ`-tube
  (`Kakeya.VeryNotSticky.dist_endpoints_le_of_carrier_subset` pins their endpoints to `3ρ`-balls
  and `Kakeya.VeryNotSticky.card_le_of_ed_of_endpoints_confined` counts them), so
  `#𝕋_ρ ≤ 2 · 385^6 · #𝕋`;
* `Δ_max(𝕋) ≤ δ^{-η}` for a family in the unit ball forces `#𝕋 ≤ C₃ · δ^{-2-η}`
  (`Kakeya.Tube.card_le_of_densityIn_le`).

At the fine end `ρ = δ^{1-ϖ}` of the window the count binder asks for `δ^{-(1-ϖ)(2+ζ)}` of them.
So the binder list is **empty at every small `δ`** whenever `(1-ϖ)(2+ζ) > 2 + η`, i.e. whenever
`ζ > (η + 2ϖ)/(1-ϖ)`: for those exponents GWZ Lemma 9.1 is vacuously true. -/

/-! ## W1′ — the closing skeleton's `SiteWitness`, and the `K` this family admits

`Kakeya.ML2Core.SiteWitness` consists of four data
existentials (`u'`, `Cu`/`𝒰`, `lam`, `K`), ten rows, and **no `ε₀'`/`g'`** — the skeleton picks the
exit exponents itself and discharges all four absorption rows internally.  The one non-trivial row
is the outer margin budget `K · δ^(dm − aL) ≤ 1`, where `α ≤ dm − aL ≤ β/48000` bites.

**Measured: this family admits `K = 1`.**  Take `u' := s` — the *ambient* family of the witness is
already the uniformisation's retained subfamily, so nothing has to be retained a second time — and
`lam := 1`.  `Kakeya.ML2Core.stateMass` ignores the shading level
(`Kakeya.ML2Core.stateMass_level`), so `stateMass (s,T,1) = stateMass (u',T,lam)` **on the nose**
and the ledger holds at `K = 1` with no `δ`-power at all.  Row 10 is then
`δ^(dm − aL) ≤ 1`, i.e. exactly `aL ≤ dm`.  So the `α = β/4` failure of the earlier reading is not
a property of the family: it was an artefact of putting the *full grid* in the ambient slot and
paying `δ^{-β/4}` to retain a uniform subfamily.

**Caveat — this says nothing about the site's producer.**  `u' = s`, `lam = 1`, `K = 1` puts the
retention exponent at `α = 0`, trivially inside the budget `α ≤ dm − aL ≤ β/48000`.  That is exactly
right for *non-vacuity*, and exactly wrong as evidence about the real site, which has `u' ⊊ s` and
`K > 1` — there the budget row **binds**, and it is the row a producer has to be designed against
(`Kakeya.ML2Core.absorbK_of_budget` is where everything reduces to `K · δ^(dm − aL) ≤ 1`).  A
witness shows the row list is inhabited; it does not show the site can inhabit it *while retaining a
proper subfamily*, which is the site's actual difficulty.

The side conditions `aL ≤ ηin` and `aL ≤ dm` are universally quantified here, not chosen, so the
witness covers the skeleton's whole admissible window `aL ∈ (0, min ηin dm]`; the hypothesis is
stated at `0 ≤ aL`, which is *weaker* than the skeleton's strict `0 < aL`
(`Kakeya.ML2Core.geometricCoreAt_of_witness_and_trial` instantiates `T-D5` at `aL`), so no
instantiation is lost. -/

open Kakeya.ML2Core in
/-- The existential data in `Kakeya.ML2Core.SiteWitness`. -/
def SiteWitnessRows (ηin dm aL : ℝ) (Cu₀ : ℝ≥0) {δ : ℝ≥0} {ι : Type v}
    (s : Finset ι) (T : ι → ShadedTube δ E3) : Prop :=
      ∃ u' : Finset ι, u' ⊆ s ∧
      ∃ (Cu : ℝ≥0) (_ : Tube.UniformTubeSet u' (fun i => (T i).toTube)
          (Tube.ssfGridLen δ) Cu) (lam : ℝ≥0) (K : ℝ≥0∞),
        Cu ≤ Cu₀ ∧
        (s.card : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ)) ∧
        u'.Nonempty ∧
        Kakeya.maxDensity u' (fun i => (T i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-ηin) ∧
        0 < lam ∧
        ML2Shaded.HasDenseShading lam u' (fun i => (T i).toShadedBody) ∧
        (((δ : ℝ≥0) ^ (ηin - aL) / 2 : ℝ≥0) : ℝ≥0∞) ≤ (lam : ℝ≥0∞) ∧
        stateMass ((s, T, (1 : ℝ≥0)) : DescentState ι δ)
          ≤ K * stateMass ((u', T, lam) : DescentState ι δ) ∧
        K * (δ : ℝ≥0∞) ^ (dm - aL) ≤ 1

/-- The site-witness predicate with its quantitative parameters explicit. -/
def SiteWitnessPred (η ηin dm aL : ℝ) (Cu₀ : ℝ≥0) : Prop :=
  ∀ᶠ (δ : ℝ≥0) in nhdsWithin 0 (Set.Ioi 0),
    ∀ {ι : Type v} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      IsKatzTao s (fun i => (T i).toConvexSpaceBody) ((δ : ℝ≥0∞) ^ (-η)) →
      ShadedBody.fullness s (fun i => (T i).toShadedBody) ≥ δ ^ η →
      (δ : ℝ)⁻¹ ≤ (s.card : ℝ) →
      SiteWitnessRows.{v} ηin dm aL Cu₀ s T

/-- **compatibility.**  `Kakeya.ML2Wit.SiteWitnessPred` is `Kakeya.ML2Core.SiteWitness` on the nose —
`id`, no bridge.  If either transcription drifts, this `example` stops elaborating.  Measured
firing control: perturbing one row (`Cu ≤ Cu₀` to `Cu ≤ Cu₀ + 1`) makes it fail with a type
mismatch. -/
example (η ηin dm aL : ℝ) (Cu₀ : ℝ≥0) :
    SiteWitnessPred.{v} η ηin dm aL Cu₀ → ML2Core.SiteWitness.{v} η ηin dm aL Cu₀ := id

end Kakeya.ML2Wit

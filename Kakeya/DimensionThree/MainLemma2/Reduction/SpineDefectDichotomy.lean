/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineDefectDescent
public import Kakeya.DimensionThree.MainLemma2.ShadedDividingScales
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineTrialOutcome
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineDefectExit
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineRungWiring
public import Kakeya.DimensionThree.MainLemma2.LineEssDistinct
public import Kakeya.Tube.Rigidity
public import Kakeya.FrostmanTransfer
public import Kakeya.ShadedUniform
public import Kakeya.DimensionThree.MainLemma2.GridRounding
public import Kakeya.StickyKakeya.CrossScale
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorTerminal
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineDichotomyInputs
public import Kakeya.DimensionThree.MainLemma2.Reduction.AssemblyPointwise

/-!
# `P3` — the descent, read at the family: from one trial to `Dichotomy`'s two disjuncts

`Kakeya.ML2Core.gain_of_trialDescent` is abstract in `(σ, Φ, P, lam, μ, A, B, Λ)`.  This file
instantiates it at the descent's actual state — a pair `(S, Z)` of a subfamily and its shading —
and produces the two disjuncts of `Kakeya.ML2Assembly.Dichotomy` at the top family, with the
accumulated `Λ ^ P` still in front.  The absorption of `Λ ^ P` is
`Kakeya.ML2Core.exists_threshold_loss_pow_potentialCeil_le` (`T-D5`) and is spent **once**, at the
top, in `Kakeya.ML2Core.dichotomy_disjuncts_of_trialDescent`.

## The two exit exponents are parameters — and why

`Kakeya.ML2Core.TrialOutcomeAt`'s exits are pinned at `ε₀ = β/2` and `g = 4·spineNu`, which are
`Dichotomy`'s own.  But the descent multiplies **both** by `Λ ^ P`, so the *per-trial* exits have to
sit a margin `α` inside `Dichotomy`'s: `β/2 − α` on the left and `4·spineNu + α` on the right.
`Kakeya.ML2Core.TrialOutcomeAtGain` is `TrialOutcomeAt` with those two exponents freed;
`Kakeya.ML2Core.trialOutcomeAt_eq_gain` is the `rfl` that says nothing else moved, so the statement
the floor block targets is untouched.

**Where `α` comes from, measured.**  `Kakeya.ML2Core.exists_dichotomyLeft_or_window_spine` proves
its left disjunct through the budget `hbud : 6ν + β/4 ≤ β/2`, i.e. with `β/4 − 6ν` of margin unused;
and `Kakeya.ML2Inputs.spineNu_le_div_48000` gives `ν ≤ β/48000`, so that margin is at least
`β/4 − 6β/48000 = β·(1/4 − 1/8000) > 0`.  Taking **`α := ν`** leaves the left exit at `β/2 − ν`,
still inside the budget with room to spare, and the right exit at `5ν`, which is what the descent
must be run at to land `Dichotomy`'s `4ν`.  `α` is spent **once**, at the top of the ladder, and
nowhere else.

## Contents

* `TrialOutcomeAtGain`, `trialOutcomeAt_eq_gain`;
* `descentState`, and the four monotonicity facts the descent needs of it;
* `dichotomy_disjuncts_of_trialDescent` — `P3`'s core, at one family;
* `dichotomy_disjuncts_of_trialDescent_absorbed` — the same with `Λ ^ P` spent.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric ConvexSpaceBody ShadedBody

namespace Kakeya.ML2Core

/-! ## The descent's state, and the four facts it needs -/

section State

variable {ι : Type*} {δ : ℝ≥0}

/-- **The descent's state**: the current subfamily, its shading, and its shading level.

`lam` is part of the state because `(B)` decays it — GWZ's
`λ(𝕊*,Z*) ≥ Λ⁻¹λ(𝕊,Z)` — and `Kakeya.ML2Core.gain_of_trialDescent`'s fullness ladder is
what carries that decay across the `P_max` trials while the trial's own *floor* stays fixed. -/
abbrev DescentState (ι : Type*) (δ : ℝ≥0) : Type _ :=
  Finset ι × (ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) × ℝ≥0

/-- The mass `μ(S,Z)`. -/
noncomputable def stateMass (x : DescentState ι δ) : ℝ≥0∞ := ∑ i ∈ x.1, volume (x.2.1 i).shade

/-- The sticky exit's right-hand side. -/
noncomputable def stateLeft (δ : ℝ≥0) (ε₀ : ℝ) (x : DescentState ι δ) : ℝ≥0∞ :=
  (δ : ℝ≥0∞) ^ (-ε₀) * volume (⋃ i ∈ x.1, (x.2.1 i).shade)

/-- The terminal exit's right-hand side. -/
noncomputable def stateRight (δ : ℝ≥0) (g β : ℝ) (x : DescentState ι δ) : ℝ≥0∞ :=
  (δ : ℝ≥0∞) ^ g * (x.1.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ x.1, (x.2.1 i).shade)

variable {S S' : Finset ι} {Z W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

theorem iUnion_shade_subset (hS : S' ⊆ S) (hW : ∀ i, (W i).shade ⊆ (Z i).shade) :
    (⋃ i ∈ S', (W i).shade) ⊆ ⋃ i ∈ S, (Z i).shade := by
  intro y hy
  simp only [Set.mem_iUnion, exists_prop] at hy ⊢
  obtain ⟨i, hi, hyi⟩ := hy
  exact ⟨i, hS hi, hW i hyi⟩

theorem stateLeft_mono (ε₀ : ℝ) (lam lam' : ℝ≥0) (hS : S' ⊆ S)
    (hW : ∀ i, (W i).shade ⊆ (Z i).shade) :
    stateLeft δ ε₀ ((S', W, lam') : DescentState ι δ)
      ≤ stateLeft δ ε₀ ((S, Z, lam) : DescentState ι δ) :=
  mul_le_mul' le_rfl (measure_mono (iUnion_shade_subset hS hW))

theorem stateRight_mono (g : ℝ) {β : ℝ} (hβ : 0 ≤ β) (lam lam' : ℝ≥0) (hS : S' ⊆ S)
    (hW : ∀ i, (W i).shade ⊆ (Z i).shade) :
    stateRight δ g β ((S', W, lam') : DescentState ι δ)
      ≤ stateRight δ g β ((S, Z, lam) : DescentState ι δ) := by
  refine mul_le_mul' (mul_le_mul' le_rfl ?_) (measure_mono (iUnion_shade_subset hS hW))
  exact ENNReal.rpow_le_rpow (by exact_mod_cast Nat.cast_le.mpr (Finset.card_le_card hS)) hβ

end State

/-! ## `P3` -/

section Descent

variable {ι : Type*} {δ Cu : ℝ≥0} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

end Descent

/-! ## The trial's admissibility, and the exact content of `hclosed` -/

section Admissible

variable {ι : Type*} {δ Cu : ℝ≥0} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

/-- **`Kakeya.ML2Core.IsTrialAt`'s binder block, as a predicate on the descent's state.**

Exactly the nine clauses of `IsTrialAt`, read on the triple `(S, Z, lam)`; the tenth, the fixed
floor `δ^{ηin}/2 ≤ lam`, is deliberately absent — after  correction 2 it is
re-established at every step by `Kakeya.ML2Core.gain_of_trialDescent`'s ladder, not carried in the
state. -/
def TrialAdmissible (ηin : ℝ)
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    (x : DescentState ι δ) : Prop :=
  x.1 ⊆ u ∧ x.1.Nonempty ∧
    (∀ i, (x.2.1 i).toTube = (T i).toTube) ∧
    (∀ i, (x.2.1 i).shade ⊆ (T i).shade) ∧
    IsClassHomogeneousOn 𝒰 x.1 ∧
    (∀ i ∈ x.1, (x.2.1 i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) ∧
    Kakeya.maxDensity x.1 (fun i => (x.2.1 i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-ηin) ∧
    0 < x.2.2 ∧
    ML2Shaded.HasDenseShading x.2.2 x.1 (fun i => (x.2.1 i).toShadedBody)

/-- Equal tubes give equal bodies, hence equal carriers: a shaded tube's body is its tube's. -/
theorem toConvexSpaceBody_congr {A B : ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (h : A.toTube = B.toTube) : A.toConvexSpaceBody = B.toConvexSpaceBody := by
  rw [show A.toConvexSpaceBody = A.toTube.toConvexSpaceBody from rfl,
    show B.toConvexSpaceBody = B.toTube.toConvexSpaceBody from rfl, h]

theorem carrier_congr {A B : ShadedTube δ (EuclideanSpace ℝ (Fin 3))} (h : A.toTube = B.toTube) :
    A.carrier = B.carrier := congrArg ConvexSpaceBody.carrier (toConvexSpaceBody_congr h)

/-- Every clause of `TrialAdmissible` transfers under a defect step.
Family containment, nonemptiness, tube and shade compatibility, the ball
condition, and the Katz-Tao bound transfer by restriction and monotonicity.
The defect step's remaining conjuncts supply class homogeneity, dense shading
and positivity of the new shading parameter. -/
theorem trialAdmissible_of_step {ηin : ℝ}
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    {x : DescentState ι δ} (hx : TrialAdmissible ηin 𝒰 x) {S' : Finset ι} (hS' : S' ⊆ x.1)
    {W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {lam' : ℝ≥0} (hne : S'.Nonempty)
    (htube : ∀ i, (W i).toTube = (x.2.1 i).toTube) (hshade : ∀ i, (W i).shade ⊆ (x.2.1 i).shade)
    (hhom : IsClassHomogeneousOn 𝒰 S') (hlam'0 : 0 < lam')
    (hdense : ML2Shaded.HasDenseShading lam' S' (fun i => (W i).toShadedBody)) :
    TrialAdmissible ηin 𝒰 ((S', W, lam') : DescentState ι δ) := by
  obtain ⟨hsu, -, hZtube, hZshade, -, hball, hmax, -, -⟩ := hx
  refine ⟨hS'.trans hsu, hne, fun i => (htube i).trans (hZtube i),
    fun i => (hshade i).trans (hZshade i), hhom, ?_, ?_, hlam'0, hdense⟩
  · intro i hi
    rw [carrier_congr (htube i)]
    exact hball i (hS' hi)
  · refine le_trans ?_ hmax
    refine le_trans (le_of_eq ?_) (Kakeya.maxDensity_mono _ hS')
    exact congrArg _ (funext fun i => toConvexSpaceBody_congr (htube i))

/-- **The trial at free exit exponents.**

`Kakeya.ML2Core.IsTrialAt`'s conclusion is `TrialOutcomeAt`, whose two exits are pinned at
`Dichotomy`'s own `β/2` and `4·spineNu`.  The descent multiplies **both** by `Λ ^ P`, so the exits
it can consume must sit one margin `α` inside `Dichotomy`'s: `β/2 − α` on the left and
`4·spineNu + α` on the right.  `IsTrialAtGain` is `IsTrialAt` with those two exponents freed;
`Kakeya.ML2Core.isTrialAtGain_of_isTrialAt` is the `α = 0` instance.  See
 the parameter comparison for the consequence. -/
def IsTrialAtGain (ε₀ g β h ηin : ℝ)
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    (Λ : ℝ≥0∞) : Prop :=
  ∀ S ⊆ u, ∀ Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)), ∀ lam : ℝ≥0,
    S.Nonempty →
    (∀ i, (Z i).toTube = (T i).toTube) →
    (∀ i, (Z i).shade ⊆ (T i).shade) →
    IsClassHomogeneousOn 𝒰 S →
    (∀ i ∈ S, (Z i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
    Kakeya.maxDensity S (fun i => (Z i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-ηin) →
    ML2Shaded.HasDenseShading lam S (fun i => (Z i).toShadedBody) →
    ML2Shaded.HasComparableDensities lam⁻¹ S (fun i => (Z i).toShadedBody) →
    (δ : ℝ≥0) ^ ηin / 2 ≤ lam →
    (u.card : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ)) →
    TrialOutcomeAtGain h ε₀ g β 𝒰 Λ lam S Z

end Admissible

/-! ## The margin `α`, checked against the `(G₁)` budget -/

section Margin

end Margin

/-! ## `C-G1` — the interface body did not move -/

section CG1

variable {ι : Type*} {δ Cu : ℝ≥0} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

end CG1

/-! ## `P4` — `GeometricCoreAt` from the descent -/

section TopLevel

universe u

/-- **The descent's two disjuncts, read as `Kakeya.ML2Assembly.Dichotomy`.**

`Kakeya.ML2Core.stateMass`, `stateLeft` and `stateRight` were chosen to be `Dichotomy`'s own three
expressions, so this is `Iff.rfl` and the bridge costs nothing. -/
theorem dichotomy_of_descentDisjuncts {β ε₀ g η : ℝ}
    (hdisj : ∀ᶠ (δ : ℝ≥0) in nhdsWithin 0 (Set.Ioi 0),
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        IsKatzTao s (fun i => (T i).toConvexSpaceBody) ((δ : ℝ≥0∞) ^ (-η)) →
        ShadedBody.fullness s (fun i => (T i).toShadedBody) ≥ δ ^ η →
        (δ : ℝ)⁻¹ ≤ (s.card : ℝ) →
        stateMass (s, T, 1) ≤ stateLeft δ ε₀ (s, T, 1) ∨
          stateMass (s, T, 1) ≤ stateRight δ g β (s, T, 1)) :
    ML2Assembly.Dichotomy.{u} β ε₀ g η := hdisj

/-- **`P4`: `Kakeya.ML2Assembly.GeometricCoreAt` from the descent.**

Purely additive, and packaged exactly as `Kakeya.ML2Core.geometricCoreAt_of_rungMiddleFactor`
packages `dichotomy_of_rungFactors`: `GeometricCoreAt`, `Dichotomy` and `Cap/*` keep their texts.
The hypothesis is the descent's own output — the two disjuncts of
`Kakeya.ML2Core.dichotomy_disjuncts_of_trialDescent_absorbed`, at `Dichotomy`'s exponents, after the
margin `α` has been spent. -/
theorem geometricCoreAt_of_descent
    (hdesc : ∀ (β ϖ : ℝ) (gain dens : ℝ → ℝ), 0 < β → β ≤ 1 →
      ML2Assembly.Lemma91ParamsAt.{u} β ϖ gain dens →
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧
        ∀ᶠ (δ : ℝ≥0) in nhdsWithin 0 (Set.Ioi 0),
          ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
            (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
            IsKatzTao s (fun i => (T i).toConvexSpaceBody) ((δ : ℝ≥0∞) ^ (-η)) →
            ShadedBody.fullness s (fun i => (T i).toShadedBody) ≥ δ ^ η →
            (δ : ℝ)⁻¹ ≤ (s.card : ℝ) →
            stateMass (s, T, 1) ≤ stateLeft δ (β / 2) (s, T, 1) ∨
              stateMass (s, T, 1)
                ≤ stateRight δ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens) β (s, T, 1)) :
    ML2Assembly.GeometricCoreAt.{u} := by
  intro β ϖ gain dens hβ0 hβ1 hp hKT hF
  obtain ⟨ε₁, hε₁, η, hη0, hη1, hdisj⟩ := hdesc β ϖ gain dens hβ0 hβ1 hp hKT hF
  exact ⟨ε₁, hε₁, η, hη0, hη1, dichotomy_of_descentDisjuncts hdisj⟩

end TopLevel

/-! ## `P7` — the trichotomy, routed -/

section Trichotomy

variable {ι : Type*} {δ Cu : ℝ≥0} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

end Trichotomy

/-! ## `T-D1″` — the sticky grid family cannot reach `(B)` -/

section StickyGrid

end StickyGrid

/-! ## The profile is a live quantity on real families -/

section Live

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ Cu : ℝ≥0} {u : Finset ι} {T : ι → Tube δ E}

end Live

/-! ## The descent's closure, with every still-open input as a named binder -/

section Closure

variable {ι : Type*} {δ Cu : ℝ≥0} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

/-- **`P3` run on the *shading level* rather than on the aggregate fullness.**

 correction 2: what re-establishes the trial's fixed floor at every step is the
ladder on `lam` — the state's third component — and `(B)`'s `lam ≤ Λ · lam'` is exactly the ledger
it needs.  `Kakeya.ML2Core.dichotomy_disjuncts_of_trialDescent` runs the same induction on
`Kakeya.ML2Core.stateFullness`; both are available because `(B)` carries both ledgers. -/
theorem dichotomy_disjuncts_of_trialDescent_level
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    {Adm : DescentState ι δ → Prop}
    {h ε₀ g β : ℝ} (hβ : 0 ≤ β) {Λ lam0 : ℝ≥0∞} (hΛ : 1 ≤ Λ) {P : ℕ}
    (hΦP : ∀ x, Adm x → potential h 𝒰 x.1 ≤ P)
    (hclosed : ∀ x, Adm x → ∀ S' ⊆ x.1,
      ∀ W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)), ∀ lam' : ℝ≥0, S'.Nonempty →
      (∀ i, (W i).toTube = (x.2.1 i).toTube) → (∀ i, (W i).shade ⊆ (x.2.1 i).shade) →
      IsClassHomogeneousOn 𝒰 S' → 0 < lam' →
      ML2Shaded.HasDenseShading lam' S' (fun i => (W i).toShadedBody) →
      Adm ((S', W, lam') : DescentState ι δ))
    (htrial : ∀ x, Adm x →
      lam0 ≤ Λ ^ (P - potential h 𝒰 x.1) * (x.2.2 : ℝ≥0∞) →
      TrialOutcomeAtGain h ε₀ g β 𝒰 Λ x.2.2 x.1 x.2.1) :
    ∀ x, Adm x → lam0 ≤ (x.2.2 : ℝ≥0∞) →
      stateMass x ≤ Λ ^ P * stateLeft δ ε₀ x ∨ stateMass x ≤ Λ ^ P * stateRight δ g β x := by
  refine gain_of_trialDescent_top (Adm := Adm) (Φ := fun x => potential h 𝒰 x.1) (P := P)
    (lam := fun x => (x.2.2 : ℝ≥0∞)) (μ := stateMass) (A := stateLeft δ ε₀)
    (B := stateRight δ g β) (Λ := Λ) (lam0 := lam0) hΛ hΦP ?_
  intro x hx hlad
  rcases htrial x hx hlad with hL | hR | ⟨S', hS'S, W, hS'ne, htube, hshade, hmass, hfull,
    hpot, hhom, lam', hlam'0, hlamΛ, hdense⟩
  · exact Or.inl (Or.inl hL)
  · exact Or.inl (Or.inr hR)
  · refine Or.inr ⟨((S', W, lam') : DescentState ι δ),
      hclosed x hx S' hS'S W lam' hS'ne htube hshade hhom hlam'0 hdense, hpot, hmass, hlamΛ,
      ?_, ?_⟩
    · exact stateLeft_mono ε₀ x.2.2 lam' hS'S hshade
    · exact stateRight_mono g hβ x.2.2 lam' hS'S hshade

/-- **The ladder re-establishes the trial's fixed floor**.

The source's arithmetic verbatim: the induction hypothesis carries `λ ≥ Λ^{P−P_max}δ^{η₀}`, and
`Λ^{P_max+1} ≤ δ^{-a₀}` upgrades it to the trial's own fixed `λ ≥ δ^{2η₀}`.  Here the upgrade is
the single hypothesis `hbase`, which is where the margin `α` is spent on the fullness side: with
`lam0 := δ^{ηin−α}/2` and `Λ^P ≤ δ^{-α}` it reads `Λ^P·δ^{ηin}/2 ≤ δ^{ηin−α}/2`. -/
theorem floor_of_ladder {Λ lam0 : ℝ≥0∞} (hΛ : 1 ≤ Λ) (hΛtop : Λ ≠ ⊤) {P k : ℕ} (hk : k ≤ P)
    {lam floor : ℝ≥0}
    (hbase : Λ ^ P * (floor : ℝ≥0∞) ≤ lam0)
    (hlad : lam0 ≤ Λ ^ k * (lam : ℝ≥0∞)) : floor ≤ lam := by
  have hΛ0 : Λ ≠ 0 := fun h => by simp [h] at hΛ
  have hpow0 : Λ ^ P ≠ 0 := pow_ne_zero _ hΛ0
  have hpowtop : Λ ^ P ≠ ⊤ := ENNReal.pow_ne_top hΛtop
  have hmono : Λ ^ k * (lam : ℝ≥0∞) ≤ Λ ^ P * (lam : ℝ≥0∞) :=
    mul_le_mul' (pow_le_pow_right' hΛ hk) le_rfl
  have hchain : Λ ^ P * (floor : ℝ≥0∞) ≤ Λ ^ P * (lam : ℝ≥0∞) :=
    hbase.trans (hlad.trans hmono)
  exact_mod_cast (ENNReal.mul_le_mul_iff_right hpow0 hpowtop).mp hchain

/-- **The inputs of the descent's closure, as a named list.**

Every field is an obligation of a *named* owner, and the block is closed exactly when all of them
are discharged.  Nothing here is prose: the remaining work is this binder list.

* `loss_ne_top`, `loss_ge_one` — the per-trial loss is a real subpolynomial factor.  **Site.**
* `card` — the block's own cardinality binder `#u ≤ δ^{-4}`.  **Site**, and it is existing at every
  call of the reduction.
* `trial` — `Kakeya.ML2Core.IsTrialAt`: the trial itself.  **Floor block** for the two terminal
  routes ((F), still owing F4's H5; and (P), still owing F5), **this block** for the sticky exit
  `(G₁)` and for `(B)` via `Kakeya.ML2Core.profileDrop_of_concentration_destroyed`, and the **site**
  for the window package and the `CentredHandBack`-dependent factors that feed both.
* `top` — the top family is admissible.  **Site.**
* `ceiling` — `Φ_h ≤ P` on every admissible state; discharged by
  `Kakeya.ML2Core.potential_le_potentialCeil_five` from the site's `#u ≤ δ^{-4}` and `Cu ≤ δ^{-1}`.
* `base` — the ladder's base, `Λ^P·(δ^{ηin}/2) ≤ lam0`; discharged by
  `Kakeya.ML2Core.exists_threshold_loss_pow_potentialCeil_le` (`T-D5`) at the margin `α`.
* `ladder` — the top state is on the ladder.  **Site.**
* `absorbL`, `absorbR` — `Λ^P` spent once, on each exit; `T-D5` again, at `α := defectMargin`. -/
structure DescentInputs (ε₀ g β ηin h : ℝ) (Λ lam0 : ℝ≥0∞) (P : ℕ)
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    (x₀ : DescentState ι δ) : Prop where
  /-- The per-trial loss is at least one. -/
  loss_ge_one : 1 ≤ Λ
  /-- …and finite. -/
  loss_ne_top : Λ ≠ ⊤
  /-- The block's cardinality binder. -/
  card : (u.card : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ))
  /-- The trial: the floor block's two terminal routes, this block's `(G₁)` and `(B)`. -/
  trial : IsTrialAtGain ε₀ g β h ηin 𝒰 Λ
  /-- The top family is admissible. -/
  top : TrialAdmissible ηin 𝒰 x₀
  /-- The potential's ceiling on every admissible state. -/
  ceiling : ∀ x, TrialAdmissible ηin 𝒰 x → potential h 𝒰 x.1 ≤ P
  /-- The ladder's base: `Λ^P` fits inside the gap between `lam0` and the trial's fixed floor. -/
  base : Λ ^ P * (((δ : ℝ≥0) ^ ηin / 2 : ℝ≥0) : ℝ≥0∞) ≤ lam0
  /-- The top state is on the ladder. -/
  ladder : lam0 ≤ (x₀.2.2 : ℝ≥0∞)

end Closure

/-! ## The floor block's `F7`, wired into the trial's conclusion -/

section FloorWiring

universe u

end FloorWiring

/-! ## The `(G₁)` side pays the margin -/

section StickyPayment

end StickyPayment

end Kakeya.ML2Core

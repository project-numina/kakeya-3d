/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.Assembly

/-!
# The open cardinality band of Main Lemma 2

`Kakeya.ML2Assembly.katzTaoEstimate_sub_of_frostmanEstimate_of_lemma91` splits every family of
`δ`-tubes at the threshold `|𝕋| = δ^{-1}` of Prof. Hong Wang's clarification.  Above the threshold
the GWZ chain runs (`Kakeya.ML2Assembly.Dichotomy`); below it the assembly assumes
`Kakeya.ML2Assembly.SmallCard`.  This module is about `SmallCard`: what it really asks, how much of
it is already paid for, and what the exact residue is.

## The answer, in one line

`SmallCard γ` is **Main Lemma 2's own conclusion, restricted to `|𝕋| < δ^{-1}`**, and the part of
it that is not already implied by `K_KT(β)` is exactly the band

  `δ^{-ε/(2(β-γ))} < |𝕋| < δ^{-1}`,

on which one needs an accuracy-free gain.  Nothing weaker suffices: the three inequalities the
assembly has at its disposal are each *strictly* too weak there, and that is proved here.

## What is proved

Reductions (all `↔` or `→` into the assembly's own `SmallCard`, hence tripwires against drift):

* `Kakeya.ML2Band.bandGoal_iff_smallCard` — `BandGoal γ`, the band-restricted obligation, is
  *equivalent* to `Kakeya.ML2Assembly.SmallCard γ` for every `γ < 1`.  So restricting attention to
  the band loses nothing, and the equivalence breaks the moment `SmallCard` changes;
* `Kakeya.ML2Band.smallCardAt_of_katzTaoEstimate` — `K_KT(β)` alone **proves** `SmallCard γ` at
  every accuracy `ε > β - γ`.  The open part of `SmallCard` is only `ε ≤ β - γ`;
* `Kakeya.ML2Band.smallCardAt_of_bandGoalAt_of_katzTaoEstimate` and
  `Kakeya.ML2Band.smallCard_of_residualBand` — with `K_KT(β)` spent on the low sub-band, the
  residue is the single cut `θ = ε/(2(β-γ))`, i.e. the band displayed above;
* `Kakeya.ML2Band.bandGoalAt_of_one_le_cut` — a cut at `θ ≥ 1` is vacuous, which is why the band
  closes by itself once `ε ≥ 2(β-γ)`.

Sufficient extra inputs, i.e. what would close the band:

* `Kakeya.ML2Band.smallCard_of_bandDichotomy` — the band analogue of
  `Kakeya.ML2Assembly.Dichotomy`: either `μ ≤ δ^{-ε}` or `μ ≤ δ^{g}|𝕋|^{β}`, for families with
  `|𝕋| < δ^{-1}`.  It closes `SmallCard (β - c)` at the budget **`c ≤ g`**, not the `4c ≤ g` the
  large-cardinality branch has to pay: below `δ^{-1}` the crude bound `|𝕋| ≤ δ^{-4}` is replaced
  by `|𝕋| ≤ δ^{-1}`, and the conversion constant drops from `4` to `1`;
* `Kakeya.ML2Band.smallCard_of_bandKakeya` — the stronger, simpler input `μ ≤ δ^{-ε}` on the band.

Sharpness — each of the three inequalities available to the assembly is strictly too weak:

* `Kakeya.ML2Band.trivialRoute_insufficient` — `μ ≤ |𝕋|` costs `θ(1-γ)` at `|𝕋| = δ^{-θ}`;
  `Kakeya.ML2Band.not_katzTaoGoal_of_const_of_cost` turns this into an actual **counterexample**:
  a family of coincident bodies violates the goal as soon as `ε < θ(1-γ)`, so the cost condition of
  `Kakeya.MainLemma2.Reduction.katzTaoGoal_of_card_le_rpow` cannot be relaxed.
  `Kakeya.ML2Band.card_le_of_isKatzTao_const` says where that witness lives: a coincident family is
  Katz--Tao only at a constant `≥ |𝕋|`, so it inhabits exactly the sub-band `|𝕋| ≤ δ^{-η}`;
* `Kakeya.ML2Band.katzTaoRoute_insufficient` — `K_KT(β)` at any accuracy `ε'` is strictly weaker
  than the goal whenever `ε < ε' + θ(β-γ)`.  At the top of the band (`θ = 1`) this holds for every
  `ε ≤ β - γ` and every `ε' > 0`, which is the precise sense in which `K_KT(β)` runs out;
* `Kakeya.ML2Band.absoluteLossRoute_insufficient` — the *first* alternative of the dichotomy,
  `μ ≤ δ^{-ε₀}` at an absolute `ε₀`, is **useless** on the band: it is strictly weaker than the
  goal whenever `ε + θγ < ε₀`.  `Kakeya.ML2Band.absoluteLoss_needs_delta_inv` specialises this to
  the assembly's own parameters (`ε₀ = β/2`, `γ = β/2`, the extreme allowed by `2c ≤ β`) and shows
  the threshold `δ^{-1}` is *exactly* the one that makes
  `Kakeya.MainLemma2.Reduction.katzTaoGoal_of_absoluteLoss_of_card_ge` fire: for every `a < 1` the
  route fails on `|𝕋| ≤ δ^{-a}` once `ε < (1-a)β/2`.  So the band cannot be closed by strengthening
  Theorem 7.3(B); only a genuine `δ`-gain works.

Non-vacuity and the shape of the difficulty:

* `Kakeya.ML2Band.smallCard_of_katzTaoEstimate` — `SmallCard γ` is `K_KT(γ)` with a hypothesis
  discarded, so it is true (it is an instance of the development's own conclusion) and it is *not*
  the kind of obligation that can be discharged by bookkeeping: the assembly asks for it at the
  improved exponent `γ = β - c`;
* `Kakeya.ML2Band.singleton_satisfies_absoluteLoss`, `Kakeya.ML2Band.singleton_fails_gain` — the
  one-element family, which pins down what the single-tube example recorded in the docstring of
  `Kakeya.ML2Assembly.Dichotomy` does and does not refute, and shows why
  `Kakeya.ML2Band.BandDichotomy` has to be a disjunction.

The bilinear case, formally:

* `Kakeya.ML2Band.not_cover_count_of_card_lt_inv` and
  `Kakeya.ML2Band.not_scaleCount_of_card_lt_inv` — the third bullet of GWZ Lemma 9.1
  (`|𝕋_ρ| ≥ ρ^{-2-ζ}` for `ρ = δ^{1-b}`, `b ≤ 1/2`) is **impossible** when `|𝕋| < δ^{-1}`.  This is
  the contrapositive of `Kakeya.MainLemma2.Reduction.delta_inv_le_card_of_scaleCount_bullet` and is
  the formal content of "if `𝕋` is bilinear the count is automatic": the band consists exactly of
  the families that fail the very-not-sticky count at every admissible scale.

## What is *not* here

No broad--narrow decomposition, and no `bilinear` predicate.  The Lean tree has no broadness
apparatus outside the abandoned `Kakeya.DimensionThree.MainLemma2.WangZahl.*` subtree
(`IsBroadAtScale` in `WangZahl/WolffHairbrush.lean`), which Section 9 may not import; the
GWZ-adapted blueprint never mentions broadness.  Building it is a geometric development, not a
bookkeeping one, and nothing in this file pretends otherwise.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Topology Filter ShadedBody ConvexSpaceBody

namespace Kakeya.ML2Band

universe u

/-- Abbreviation for the ambient space of Main Lemma 2. -/
abbrev Space3 := EuclideanSpace ℝ (Fin 3)

/-! ### `BandGoal` is exactly `SmallCard` -/

/-! ### A single accuracy -/

/-! ### The arithmetic of an exponent drop paid for by a cardinality cap -/

/-! ### What `K_KT(β)` alone buys on the band -/

/-! ### Two sufficient inputs for the band -/

/-- **The band dichotomy** — the small-cardinality analogue of `Kakeya.ML2Assembly.Dichotomy`.

For families with `|𝕋| < δ^{-1}`: either the accuracy-quality bound `μ ≤ δ^{-ε}`, or an
accuracy-free gain `μ ≤ δ^{g}|𝕋|^{β}`.

Two remarks on the statement, both of which are the reason it is *this* and not something simpler.

* **The first alternative must be read at the outer `ε`, not at an absolute `ε₀`.**  On the band an
  absolute loss is worthless: `Kakeya.ML2Band.absoluteLossRoute_insufficient` shows
  `δ^{-ε}|𝕋|^{γ} < δ^{-ε₀}` whenever `ε + θγ < ε₀`, and the cut `θ` shrinks with `ε`.  This is the
  exact opposite of the large-cardinality branch, where `|𝕋| ≥ δ^{-1}` makes `|𝕋|^{γ} ≥ δ^{-γ}`
  absorb `ε₀ = β/2` for free (`Kakeya.MainLemma2.Reduction.katzTaoGoal_of_absoluteLoss_of_card_ge`).
* **The second alternative cannot be asked for alone.**  `μ ≥ 1` always, while `δ^{g}|𝕋|^{β} < 1`
  whenever `|𝕋|^{β} < δ^{-g}`; a single fully shaded tube already refutes it.  So the disjunction is
  necessary, and the first alternative is what covers the bottom of the range. -/
def BandDichotomy (β g : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), η ≤ 1 ∧
    ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ℝ≥0∞) ^ (-η)) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (s.card : ℝ) < (δ : ℝ)⁻¹ →
        (∑ i ∈ s, volume (T i).shade
            ≤ (δ : ℝ≥0∞) ^ (-ε) * volume (⋃ i ∈ s, (T i).shade))
          ∨ (∑ i ∈ s, volume (T i).shade
            ≤ (δ : ℝ≥0∞) ^ g * (s.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ s, (T i).shade))

/-- **The Kakeya bound on the band**: `μ ≤ δ^{-ε}` for families with `|𝕋| < δ^{-1}`.

The strongest of the sufficient inputs, and the cleanest statement of what the band really asks:
the Kakeya multiplicity estimate itself, for families of fewer than `δ^{-1}` tubes.  It implies
`Kakeya.ML2Band.BandDichotomy` at every gain (`Kakeya.ML2Band.bandDichotomy_of_bandKakeya`) and
`Kakeya.ML2Assembly.SmallCard γ` at every `γ ≥ 0`. -/
def BandKakeya : Prop :=
  ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), η ≤ 1 ∧
    ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ℝ≥0∞) ^ (-η)) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (s.card : ℝ) < (δ : ℝ)⁻¹ →
        ∑ i ∈ s, volume (T i).shade
          ≤ (δ : ℝ≥0∞) ^ (-ε) * volume (⋃ i ∈ s, (T i).shade)

/-- **`Kakeya.ML2Band.BandKakeya` closes the band at every exponent `γ ≥ 0`**, since `|𝕋| ≥ 1`
makes `|𝕋|^{γ} ≥ 1`.  In particular it closes `SmallCard γ` for every `γ` the assembly may ask
for, with no budget condition at all. -/
theorem smallCard_of_bandKakeya {γ : ℝ} (hγ : 0 ≤ γ) (h : BandKakeya.{u}) :
    ML2Assembly.SmallCard.{u} γ := by
  intro ε hε
  obtain ⟨η, hη0, hη1, hev⟩ := h ε hε
  refine ⟨η, hη0, hη1, ?_⟩
  filter_upwards [hev] with δ hδev
  intro ι s T hball hKT hfull hcard
  rcases Nat.eq_zero_or_pos s.card with h0 | hpos
  · rw [Finset.card_eq_zero.mp h0]; simp
  have hN1 : (1 : ℝ≥0∞) ≤ (s.card : ℝ≥0∞) := by exact_mod_cast hpos
  have hone : (1 : ℝ≥0∞) ≤ (s.card : ℝ≥0∞) ^ γ := by
    calc (1 : ℝ≥0∞) = (s.card : ℝ≥0∞) ^ (0 : ℝ) := ENNReal.rpow_zero.symm
      _ ≤ (s.card : ℝ≥0∞) ^ γ := ENNReal.rpow_le_rpow_of_exponent_le hN1 hγ
  refine (hδev s T hball hKT hfull hcard).trans ?_
  calc (δ : ℝ≥0∞) ^ (-ε) * volume (⋃ i ∈ s, (T i).shade)
      = (δ : ℝ≥0∞) ^ (-ε) * 1 * volume (⋃ i ∈ s, (T i).shade) := by ring
    _ ≤ (δ : ℝ≥0∞) ^ (-ε) * (s.card : ℝ≥0∞) ^ γ
          * volume (⋃ i ∈ s, (T i).shade) := by gcongr

/-- `Kakeya.ML2Band.BandKakeya` is the first alternative of `Kakeya.ML2Band.BandDichotomy`, at
every exponent and every gain. -/
theorem bandDichotomy_of_bandKakeya {β g : ℝ} (h : BandKakeya.{u}) : BandDichotomy.{u} β g := by
  intro ε hε
  obtain ⟨η, hη0, hη1, hev⟩ := h ε hε
  refine ⟨η, hη0, hη1, ?_⟩
  filter_upwards [hev] with δ hδev
  intro ι s T hball hKT hfull hcard
  exact Or.inl (hδev s T hball hKT hfull hcard)

/-! ### Sharpness: the two routes available to the assembly both fail on the band -/

section Sharp

variable {δ : ℝ}

end Sharp

/-! ### The constant family: where the trivial branch stops, and why -/

section Const

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*}

/-- Bridge, dual to `Kakeya.MainLemma2.Reduction.natCast_le_coe_rpow`: a real cardinality *lower*
bound `δ^{-θ} ≤ N` becomes the one in `[0,∞]`. -/
theorem coe_rpow_le_natCast {δ : ℝ≥0} (hδ : 0 < δ) {θ : ℝ} {n : ℕ}
    (h : (δ : ℝ) ^ (-θ) ≤ (n : ℝ)) : (δ : ℝ≥0∞) ^ (-θ) ≤ (n : ℝ≥0∞) := by
  rw [← ENNReal.coe_rpow_of_ne_zero hδ.ne']
  rw [show ((n : ℝ≥0∞)) = ((n : ℝ≥0) : ℝ≥0∞) by simp]
  rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
  simpa [NNReal.coe_rpow] using h

end Const

/-! ### The very-not-sticky count empties the band -/

/-! ### The band is empty at coarse accuracies -/

/-! ### `SmallCard` is true, and what that costs -/

/-- **`SmallCard γ` is `K_KT(γ)` with a hypothesis thrown away.**

So `Kakeya.ML2Assembly.SmallCard γ` is not false — it is an instance of the very statement the
development is proving — but it is also not cheap: the assembly asks for it at `γ = β - c`, i.e. at
the *improved* exponent, which is exactly the conclusion of Main Lemma 2.  This, and not any defect
of the statement, is why the band is open: below `δ^{-1}` the GWZ chain has nothing to say, and
`K_KT(β)` at the *old* exponent runs out at `ε = β - γ`
(`Kakeya.ML2Band.smallCardAt_of_katzTaoEstimate`, `Kakeya.ML2Band.katzTaoRoute_insufficient`). -/
theorem smallCard_of_katzTaoEstimate {γ : ℝ} (h : KatzTaoEstimate.{u} Space3 γ) :
    ML2Assembly.SmallCard.{u} γ := by
  intro ε hε
  obtain ⟨η, hη0, hev⟩ := h ε hε
  refine ⟨min η 1, lt_min hη0 one_pos, min_le_right _ _, ?_⟩
  filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : ℝ≥0) < 1 from zero_lt_one)] with δ hδev hδ
  obtain ⟨hδ0, hδ1⟩ := hδ
  intro ι s T hball hKT hfull _
  exact hδev s T hball
    (ML2Assembly.isKatzTao_of_exponent_le hδ1.le (min_le_left _ _) hKT)
    (ML2Assembly.le_of_rpow_exponent_le hδ0 hδ1.le (min_le_left _ _) hfull)

/-! ### The single-tube example, and what it does and does not refute -/

section Singleton

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*}

end Singleton

end Kakeya.ML2Band

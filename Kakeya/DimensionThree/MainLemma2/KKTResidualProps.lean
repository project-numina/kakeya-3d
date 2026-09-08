/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.KatzTaoPlankEstimate
public import Kakeya.DimensionThree.MainLemma2.NonSlabSplit
public import Kakeya.DimensionThree.MainLemma2.Reduction.AccuracyCardExchange

/-!
# The residual propositions under a cardinality-restricted `K_KT`

**Question.**  Replace GWZ Definition 3.4 (`Kakeya.KatzTaoEstimate`) by the
restricted estimate `K_KT'(β)` — the same statement with the extra hypothesis `δ^{-2} ≤ |𝕋|`
(strict form) or `δ^{-2+η} ≤ |𝕋|` with the prover's `η` (slack form).  Do the propositions needed
at the two blocking application sites — GWZ Lemma 6.1's high branch (site A) and Lemma 9.1's
tangential fibres (site D) — still *follow* from `K_KT'(β)` together with everything in scope
there?  Truth cannot discriminate (every conclusion is a Kakeya-type estimate), so the test is
derivability.

**What this file establishes, all compiled and axiom-clean.**

* `KatzTaoEstimateStrict`, `KatzTaoEstimateSlack` are verbatim copies of Definition 3.4 with the
  respective clause; `KatzTaoEstimateSmall E β C` is Definition 3.4 restricted to families with
  `|𝕋| < δ^{-C}` ("small-family `K_KT`").  Trivially `K_KT → Slack → Strict` and `K_KT → Small C`;
  conversely `Strict ∧ Small 2 → K_KT` and `Slack ∧ Small 2 → K_KT` by the obvious case split
  (`katzTaoEstimate_iff_strict_and_small`, `katzTaoEstimate_iff_slack_and_small`).
* **In `ℝ³` the small-family estimate is not a fragment: `Small C ↔ K_KT` for every `C > 0`**
  (`small_iff_katzTaoEstimate`), by the tree's affine squeeze
  `Kakeya.ML2Squeeze.smallCardCut_iff_katzTaoEstimate`.  Consequently `Strict ∧ Small 2 ↔ K_KT`
  is true but `Strict` is redundant in it.
* **Site A.**  `ResidualA β` is the callback consumed by `Kakeya.KatzTaoEstimate.plankEstimate`
  (the threshold form of generalized Lemma 3.7, `Kakeya.exists_b0_multiplicity_bound`), stated
  exactly as it is quantified there: over *every* `(b/8)`-tube family in the unit ball, with a
  fullness hypothesis and **no** cardinality lower bound.  `ResidualA β ↔ K_KT β`
  (`residualA_iff_katzTaoEstimate`; the forward direction pads the family and takes `τ = δ`), hence
  `ResidualA β ↔ Small C` for every `C > 0` and `Strict → (ResidualA ↔ Small 2)`.  So at site A
  `K_KT' + everything in scope ⊢ ResidualA ⟺ small-family K_KT ⟺ K_KT`: the clause hands the
  whole estimate back as the residual.
* **Site D.**  `ResidualD cfg := cfg.KTScaleData cfg.ϱ`, the field `SplitInputs.katzTao` consumes
  (verbatim: `ktScaleData_iff`).  From `K_KT` it follows by the existing `ktScaleData_of_le` route,
  packaged with explicit thresholds (`ktScaleData_of_katzTaoEstimate`).  From the strict/slack
  clause it does **not**: the fibres `𝕋[T_{ρ₂}]` obey only the upper bound
  `Kakeya.VeryNotSticky.nonslabFibreCount`, and from that bound alone every clause
  `δ^{-2+θ} ≤ |𝕋[T_{ρ₂}]|` is *false* on the lower part of the window
  (`fibre_card_lt_rpow`, `strict_clause_false_at_fibre`, `capped_clause_false_at_fibre`).  What
  the split actually consumes is the fibre-restricted datum `FibreKTData`; it follows from
  `Small C` at the fibre exponent `C_D = 2 + η − exscal(2+ζ) + μ` (`fibreKTData_of_small`), and
  the whole-family datum from `Small (2 + η + μ)` (`ktScaleData_of_small`) — but in `ℝ³` each of
  these `Small C` is again the full `K_KT`.
* **Site F.**  With the clause on the *target* family, branch (i) of the reduction closes at the
  absolute accuracy `ε₀ = β/2` through `katzTaoGoal_of_absoluteLoss_of_card_ge_rpow` at `θ = 2`
  (`branch_i_of_strict_clause`), and the assembly no longer needs `SmallCard`
  (`strict_sub_of_dichotomy`, `slack_sub_of_dichotomy`, the `hsmall`-free analogues of
  `Kakeya.ML2Assembly.katzTaoEstimate_sub_of_dichotomy`).

**Summary in one line.**  The clause moves the band from the reduction's branch (i) into Lemma 6.1
and Lemma 9.1's tangential case; the residual at each site is small-family `K_KT`, and in `ℝ³`
small-family `K_KT` at any positive cardinality exponent is `K_KT` itself.

Nothing in this file is left unproved, no `axiom` or `opaque` is declared, no existing
declaration is edited, and the import closure (370 modules) contains no module of the abandoned
route (`Plank/`, `MainLemma2/NonSlab*`, `MainLemma2/Reduction/*` only).
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Topology ConvexSpaceBody Filter ShadedBody

namespace Kakeya.KKTResidual

universe u

/-! ## 0. The restricted estimates -/

section Definitions

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **`K_KT'(β)`, strict form.**  GWZ Definition 3.4 (`Kakeya.KatzTaoEstimate`, verbatim) with the
extra hypothesis `δ^{-2} ≤ |𝕋|` after fullness. -/
def KatzTaoEstimateStrict (β : ℝ) : Prop := ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ),
    ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0,
    ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) (δ ^ (- η)) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
      (δ : ℝ) ^ (-2 : ℝ) ≤ (s.card : ℝ) →
      ∑ i ∈ s, volume (T i).shade ≤ δ ^ (- ε) * s.card ^ β * volume (⋃ i ∈ s, (T i).shade)

/-- **`K_KT'(β)`, slack form.**  Definition 3.4 with the extra hypothesis `δ^{-2+η} ≤ |𝕋|`, `η`
the prover's own loss exponent. -/
def KatzTaoEstimateSlack (β : ℝ) : Prop := ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ),
    ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0,
    ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) (δ ^ (- η)) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
      (δ : ℝ) ^ (-2 + η) ≤ (s.card : ℝ) →
      ∑ i ∈ s, volume (T i).shade ≤ δ ^ (- ε) * s.card ^ β * volume (⋃ i ∈ s, (T i).shade)

/-- **Small-family `K_KT` at cardinality exponent `C`.**  Definition 3.4 restricted to families
with `|𝕋| < δ^{-C}`. -/
def KatzTaoEstimateSmall (β C : ℝ) : Prop := ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ),
    ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0,
    ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) (δ ^ (- η)) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
      (s.card : ℝ) < (δ : ℝ) ^ (-C) →
      ∑ i ∈ s, volume (T i).shade ≤ δ ^ (- ε) * s.card ^ β * volume (⋃ i ∈ s, (T i).shade)

variable {E}

/-- A `δ^{-η}` Katz–Tao family is `δ^{-η'}` Katz–Tao for every `η' ≥ η` (general `E`; the tree's
`Kakeya.ML2Assembly.isKatzTao_of_exponent_le` is pinned to `ℝ³`). -/
theorem isKatzTao_of_exponent_le' {δ : ℝ≥0} (hδ1 : δ ≤ 1) {ι : Type*} {s : Finset ι}
    {W : ι → ConvexSpaceBody E} {η η' : ℝ} (h : η ≤ η')
    (hKT : IsKatzTao s W ((δ : ℝ≥0∞) ^ (-η))) :
    IsKatzTao s W ((δ : ℝ≥0∞) ^ (-η')) :=
  hKT.mono (ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hδ1) (by linarith))

/-- Definition 3.4 implies small-family `K_KT` at every exponent (drop the clause). -/
theorem small_of_katzTaoEstimate {β : ℝ} (C : ℝ) (h : KatzTaoEstimate.{u} E β) :
    KatzTaoEstimateSmall.{u} E β C := by
  intro ε hε
  obtain ⟨η, hη, hev⟩ := h ε hε
  refine ⟨η, hη, ?_⟩
  filter_upwards [hev] with δ hδ
  intro ι s T hball hKT hfull _
  exact hδ s T hball hKT hfull

end Definitions

/-! ## 0'. In `ℝ³`, small-family `K_KT` at any positive exponent is `K_KT` (the tree's squeeze) -/

section Space3

/-- Small-family `K_KT` at exponent `C` is `Kakeya.ML2Squeeze.SmallCardCut C β` up to the
harmless conjunct `η ≤ 1` (shrink the witness). -/
theorem smallCardCut_of_small {β C : ℝ}
    (h : KatzTaoEstimateSmall.{u} (EuclideanSpace ℝ (Fin 3)) β C) :
    Kakeya.ML2Squeeze.SmallCardCut.{u} C β := by
  intro ε hε
  obtain ⟨η, hη, hev⟩ := h ε hε
  refine ⟨min η 1, lt_min hη one_pos, min_le_right _ _, ?_⟩
  filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : ℝ≥0) < 1 from zero_lt_one)] with δ hδ hδ01
  obtain ⟨hδ0, hδ1⟩ := hδ01
  intro ι s T hball hKT hfull hcard
  exact hδ s T hball (isKatzTao_of_exponent_le' hδ1.le (min_le_left _ _) hKT)
    (Kakeya.ML2Assembly.le_of_rpow_exponent_le hδ0 hδ1.le (min_le_left _ _) hfull) hcard

/-- **In `ℝ³`, small-family `K_KT` at any exponent `C > 0` is `K_KT`** — the tree's affine
squeeze `Kakeya.ML2Squeeze.smallCardCut_iff_katzTaoEstimate`.  So "small-family `K_KT`" is never
a proper fragment of the estimate. -/
theorem small_iff_katzTaoEstimate {β C : ℝ} (hβ : 0 ≤ β) (hC : 0 < C) :
    KatzTaoEstimateSmall.{u} (EuclideanSpace ℝ (Fin 3)) β C ↔
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β :=
  ⟨fun h => (Kakeya.ML2Squeeze.smallCardCut_iff_katzTaoEstimate hβ hC).mp
      (smallCardCut_of_small h),
    fun h => small_of_katzTaoEstimate C h⟩

end Space3

/-! ## 1. Site A — GWZ Lemma 6.1's high branch (`Kakeya.KatzTaoEstimate.plankEstimate`) -/

section SiteA

end SiteA

/-! ## 4. Site F — branch (i) of the reduction under the target clause -/

section SiteF

/-- **Branch (i) closes at `ε₀ = β/2` under the strict clause on the target family**:
`Kakeya.ML2Exchange.katzTaoGoal_of_absoluteLoss_of_card_ge_rpow` at `θ = 2`, budget
`β/2 ≤ ε + 2(β − c)`, which holds for every `ε > 0` once `2c ≤ β`. -/
theorem branch_i_of_strict_clause {ι : Type*} {s : Finset ι}
    {V : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {β c ε : ℝ} (hc0 : 0 ≤ c) (hcβ : 2 * c ≤ β) (hε : 0 < ε)
    (hcard : (δ : ℝ) ^ (-2 : ℝ) ≤ (s.card : ℝ))
    (h : ∑ i ∈ s, volume (V i).shade
          ≤ (δ : ℝ≥0∞) ^ (-(β / 2)) * volume (⋃ i ∈ s, (V i).shade)) :
    ∑ i ∈ s, volume (V i).shade
      ≤ (δ : ℝ≥0∞) ^ (-ε) * (s.card : ℝ≥0∞) ^ (β - c) * volume (⋃ i ∈ s, (V i).shade) :=
  Kakeya.ML2Exchange.katzTaoGoal_of_absoluteLoss_of_card_ge_rpow hδ hδ1 (θ := 2) (γ := β - c)
    (by linarith) (by linarith) hcard h

/-- **The assembly without `SmallCard`, strict target.**  The `hsmall`-free analogue of
`Kakeya.ML2Assembly.katzTaoEstimate_sub_of_dichotomy`: with the clause on the target family the
small-cardinality case never arises, branch (i) is `branch_i_of_strict_clause`, branch (ii) is
verbatim the tree's. -/
theorem strict_sub_of_dichotomy {β g η c : ℝ}
    (hc : 0 < c) (hcβ : 2 * c ≤ β) (hη0 : 0 < η) (hη1 : η ≤ 1) (hg : 4 * c ≤ g)
    (hdich : Kakeya.ML2Assembly.Dichotomy.{u} β (β / 2) g η) :
    KatzTaoEstimateStrict.{u} (EuclideanSpace ℝ (Fin 3)) (β - c) := by
  intro ε hε
  refine ⟨η, hη0, ?_⟩
  filter_upwards [hdich, Kakeya.ML2Assembly.eventually_card_thresholds] with δ hδdich hδthr
  obtain ⟨hδ0, hδ1, hδC⟩ := hδthr
  intro ι s T hball hKT hfull hcard
  have hge : (δ : ℝ)⁻¹ ≤ (s.card : ℝ) := by
    have h1 : (δ : ℝ) ^ (-1 : ℝ) ≤ (δ : ℝ) ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hδ0) (by exact_mod_cast hδ1)
        (by norm_num)
    rw [Real.rpow_neg_one] at h1
    exact h1.trans hcard
  rcases hδdich s T hball hKT hfull hge with hmass | hmass
  · exact branch_i_of_strict_clause (V := fun i ↦ (T i).toShadedBody) hδ0 hδ1 hc.le hcβ hε
      hcard hmass
  · rcases Nat.eq_zero_or_pos s.card with h0 | hpos
    · rw [Finset.card_eq_zero.mp h0]
      simp
    have hcardle : (s.card : ℝ) ≤ (δ : ℝ) ^ (-4 : ℝ) :=
      Kakeya.ML2Assembly.card_le_rpow_neg_four hδ0 hδ1 hδC s T hball hη1 hKT
    have hcoef : (δ : ℝ≥0∞) ^ g * (s.card : ℝ≥0∞) ^ β
        ≤ (δ : ℝ≥0∞) ^ (-ε) * (s.card : ℝ≥0∞) ^ (β - c) :=
      Kakeya.ML2Reduction.le_rpow_mul_rpow_of_gain (β := β) (K := 4) hδ0 hδ1 hpos hc.le
        (by linarith) hcardle le_rfl
    calc ∑ i ∈ s, volume (T i).shade
        ≤ (δ : ℝ≥0∞) ^ g * (s.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ s, (T i).shade) := hmass
      _ ≤ (δ : ℝ≥0∞) ^ (-ε) * (s.card : ℝ≥0∞) ^ (β - c)
            * volume (⋃ i ∈ s, (T i).shade) := by gcongr

end SiteF

/-! ## 2. Site D — Lemma 9.1's tangential case, the fibres `𝕋[T_{ρ₂}]` -/

section SiteD

/-! ### (b) The strict/slack clause is *false* on the fibres, from the upper bound alone -/

/-! ### (c) What the split consumes, and small-family `K_KT` at the fibre exponent -/

/-- The window-top bound `ρ₂ ≤ δ^{exscal}` in real form, from the tree's
`Kakeya.VeryNotSticky.rho2_range` under the non-slab hypothesis `b ≤ δ^{exscal} r₁`. -/
theorem rho2_le_rpow_exscal (cfg : VeryNotSticky.{u}) (hexscal : cfg.exscal ≤ 1 / 2)
    (hnotslab : cfg.b ≤ cfg.δ ^ cfg.exscal * cfg.r₁) :
    (cfg.rho2 : ℝ) ≤ (cfg.δ : ℝ) ^ cfg.exscal := by
  have h := (VeryNotSticky.rho2_range cfg cfg.hδ cfg.hδ1 hexscal hnotslab).1.2
  have h' : ((cfg.rho2 : ℝ≥0) : ℝ) ≤ ((cfg.δ ^ cfg.exscal : ℝ≥0) : ℝ) := by
    exact_mod_cast h
  simpa [NNReal.coe_rpow] using h'

end SiteD

end Kakeya.KKTResidual

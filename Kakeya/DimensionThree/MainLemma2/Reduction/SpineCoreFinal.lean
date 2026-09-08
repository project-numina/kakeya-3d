/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCoreLeft
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCoreAssembly
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCardMultiplicative
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFactors
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEccentric
public import Kakeya.StickyKakeya.BallReduction
public import Kakeya.DimensionThree.MainLemma2.Reduction.AssemblyPointwise

/-!
# The final assembly of the geometric core (rows the component estimates )

Blueprint: GWZ,  — the whole proof of Main
Lemma 2 from GWZ Lemma 9.1.  The target of the assembly is the existing
`Kakeya.ML2Assembly.GeometricCoreAt` (`Reduction/AssemblyPointwise.lean`).

## What is here

* **arithmetic**, `multiplicity_le_of_three_factors`: the three-factor version of
  `Kakeya.ML2Spine.multiplicity_le_of_two_factors`, multiplying fine factor, the middle
  factor (the estimate in the non-eccentric case, the estimate in the eccentric one) and coarse factor
  against product and cardinality bound.
* **the case split as an `Or`-elimination**, `middle_factor_of_cases`: the two branches deliver
  the middle factor at *different* exponents (`10 η_k/ε₂` non-eccentric,
  `10 η/ε₂ - η₀/2` eccentric) and this reads both at their common lower bound, so the estimate spends one
  `rcases` and no repackaging.
* **the scale transport of the middle factor**, `rpow_le_rpow_of_le_rpow_base`: the middle factor
  is proved at the *rescaled* thickness `δ̃ = τ/θ`, and `δ̃ ≤ δ^w` converts its gain to `δ^{w g}`.
* **The cardinality estimate needed for the product bound**, `card_three_factor_le` and
  `filter_assign_eq_of_mem`: the fine fibre `Kakeya.ML2Core.exists_twoScale_with_fine_factor`
  produces is taken inside the *node-restricted* family `{i ∈ s | assign b i ∈ t₁}`, while
  `Kakeya.ML2Reduction.card_class_mul_card_coarseFibre_mul_card_le` states it inside `s`; the two
  `Finset`s are **equal**, not merely comparable, and that closes the `hcard` binder the estimate left
  open.
* **the multiplicity → mass conversion**, `sum_shade_le_of_multiplicity_le`: the exact shape the
  right disjunct of `Kakeya.ML2Core.dichotomy_of_dichotomyLeft_or_gain` states.
* **wiring**, `geometricCoreAt_of_pointwise` (a definitional pin) and
  `dichotomy_of_windowGain`: branch (i) is existing
  (`Kakeya.ML2Core.exists_dichotomyLeft_or_window_dim3`), so the producer of
  `GeometricCoreAt` is reduced to **one** obligation, the window branch's mass gain.
* **compatibility** lives in `Cap/CoreComposition.lean`, not here: the composition needs
  `Kakeya.ML2Cap.mainLemma2Statement_of_geometricCoreAt_free`, and `Cap/` imports `Reduction/`, so
  naming it in this module would close a cycle.

## What is *not* here, and why

the estimate (the packaging of the rescaled datum `(𝕋̃, Ỹ)` at `δ̃ = τ/θ`) and the estimate (the plank factoring
of `𝕋̃_ρ` and the eccentric/non-eccentric case split) **do not exist**: the rows dispatched under
those names delivered `Reduction/SpineDeltaMaxFloor.lean` and `Reduction/SpineEDExtraction.lean`,
which are the `Δ_max`-floor refutation and the essential-distinctness extraction, not the rescaled
datum.  Both `Kakeya.ML2Reduction.spine_multiplicity_le_nonEccentric_of_canonicalCover` 
and `Kakeya.ML2Core.eccentric_atPlankScale`  act on that datum, so **the middle factor has
no producer** and the window branch's gain cannot be closed here.  It is therefore carried as the
single explicit hypothesis of `dichotomy_of_windowGain`, and everything else on the route is
.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody

namespace Kakeya.ML2Core

universe u

/-! ## the estimate, the arithmetic: three factors against one cardinality bound -/

/-- **The three-factor multiplicity bound**.

`Kakeya.ML2Spine.multiplicity_le_of_two_factors` multiplies two factors; GWZ's Main Lemma 2
multiplies *three* — the fine factor at scale `δ` inside a `τ`-node (GWZ 74–79), the middle factor
of `τ`-nodes inside a `θ`-node (GWZ 92–226, the row this file's siblings own) and the coarse factor
of `θ`-nodes (GWZ 81–85) — against `Kakeya.ML2Core.exists_spineTwoScale_ofChain_translated`'s
product and `Kakeya.ML2Reduction.card_class_mul_card_coarseFibre_mul_card_le`'s cardinality bound.

The middle factor's exponent `gm` is a **gain** (positive) while the outer two are losses; the
budget is the single inequality `g ≤ gm - εf - εc - κ`, with `κ` paying the product's loss
constant `L` and the cardinality constant `Cu`.  Nothing here is spine-specific: the exponents are
free reals. -/
theorem multiplicity_le_of_three_factors
    {δ : ℝ≥0} {mu mf mm mc L Cu : ℝ≥0∞} {Nf Nm Nc N : ℕ} {β εf gm εc κ g : ℝ}
    (hδ0 : (δ : ℝ≥0∞) ≠ 0) (hδ1 : (δ : ℝ≥0∞) ≤ 1) (hβ0 : 0 ≤ β)
    (hsplit : mu ≤ L * mf * mm * mc)
    (hf : mf ≤ (δ : ℝ≥0∞) ^ (-εf) * (Nf : ℝ≥0∞) ^ β)
    (hm : mm ≤ (δ : ℝ≥0∞) ^ gm * (Nm : ℝ≥0∞) ^ β)
    (hc : mc ≤ (δ : ℝ≥0∞) ^ (-εc) * (Nc : ℝ≥0∞) ^ β)
    (hcard : (Nf : ℝ≥0∞) * (Nm : ℝ≥0∞) * (Nc : ℝ≥0∞) ≤ Cu * (N : ℝ≥0∞))
    (hL : L * Cu ^ β ≤ (δ : ℝ≥0∞) ^ (-κ))
    (hexp : g ≤ gm - εf - εc - κ) :
    mu ≤ (δ : ℝ≥0∞) ^ g * (N : ℝ≥0∞) ^ β := by
  have hδt : (δ : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := ENNReal.coe_ne_top
  have hstep1 : mf * mm * mc
      ≤ (δ : ℝ≥0∞) ^ (gm - εf - εc)
        * (((Nf : ℝ≥0∞) * (Nm : ℝ≥0∞) * (Nc : ℝ≥0∞)) ^ β) := by
    calc mf * mm * mc
        ≤ ((δ : ℝ≥0∞) ^ (-εf) * (Nf : ℝ≥0∞) ^ β)
            * ((δ : ℝ≥0∞) ^ gm * (Nm : ℝ≥0∞) ^ β)
            * ((δ : ℝ≥0∞) ^ (-εc) * (Nc : ℝ≥0∞) ^ β) := by gcongr
      _ = ((δ : ℝ≥0∞) ^ (-εf) * (δ : ℝ≥0∞) ^ gm * (δ : ℝ≥0∞) ^ (-εc))
            * ((Nf : ℝ≥0∞) ^ β * (Nm : ℝ≥0∞) ^ β * (Nc : ℝ≥0∞) ^ β) := by ring
      _ = (δ : ℝ≥0∞) ^ (gm - εf - εc)
            * (((Nf : ℝ≥0∞) * (Nm : ℝ≥0∞) * (Nc : ℝ≥0∞)) ^ β) := by
          rw [← ENNReal.rpow_add _ _ hδ0 hδt, ← ENNReal.rpow_add _ _ hδ0 hδt,
            ENNReal.mul_rpow_of_nonneg _ _ hβ0, ENNReal.mul_rpow_of_nonneg _ _ hβ0]
          ring_nf
  have hstep2 : (((Nf : ℝ≥0∞) * (Nm : ℝ≥0∞) * (Nc : ℝ≥0∞)) ^ β)
      ≤ Cu ^ β * (N : ℝ≥0∞) ^ β := by
    calc (((Nf : ℝ≥0∞) * (Nm : ℝ≥0∞) * (Nc : ℝ≥0∞)) ^ β)
        ≤ (Cu * (N : ℝ≥0∞)) ^ β := ENNReal.rpow_le_rpow hcard hβ0
      _ = Cu ^ β * (N : ℝ≥0∞) ^ β := ENNReal.mul_rpow_of_nonneg _ _ hβ0
  calc mu ≤ L * mf * mm * mc := hsplit
    _ = L * (mf * mm * mc) := by ring
    _ ≤ L * ((δ : ℝ≥0∞) ^ (gm - εf - εc) * (Cu ^ β * (N : ℝ≥0∞) ^ β)) :=
        mul_le_mul' le_rfl (hstep1.trans (mul_le_mul' le_rfl hstep2))
    _ = (L * Cu ^ β) * ((δ : ℝ≥0∞) ^ (gm - εf - εc) * (N : ℝ≥0∞) ^ β) := by ring
    _ ≤ (δ : ℝ≥0∞) ^ (-κ) * ((δ : ℝ≥0∞) ^ (gm - εf - εc) * (N : ℝ≥0∞) ^ β) := by gcongr
    _ = (δ : ℝ≥0∞) ^ (gm - εf - εc - κ) * (N : ℝ≥0∞) ^ β := by
        rw [← mul_assoc, ← ENNReal.rpow_add _ _ hδ0 hδt]
        ring_nf
    _ ≤ (δ : ℝ≥0∞) ^ g * (N : ℝ≥0∞) ^ β :=
        mul_le_mul' (ENNReal.rpow_le_rpow_of_exponent_ge hδ1 hexp) le_rfl

/-! ## The case split of the estimate, as an `Or`-elimination -/

/-- **The middle factor is proved at the rescaled thickness and consumed at the ambient one.**

`δ̃ = τ/θ` is the thickness of the rescaled family; the window gives `δ̃ ≤ δ^w` for the appropriate
window exponent `w`, and a *gain* `δ̃^{g}` at the rescaled thickness is a gain `δ^{w g}` at the
ambient one.  The direction matters: this is only sound because `g ≥ 0`, i.e. because the middle
factor is the one branch that *gains*. -/
theorem rpow_le_rpow_of_le_rpow_base {δ δt : ℝ≥0} {w g : ℝ}
    (hg : 0 ≤ g) (hw : 0 ≤ w) (hle : δt ≤ δ ^ w) :
    (δt : ℝ≥0∞) ^ g ≤ (δ : ℝ≥0∞) ^ (w * g) := by
  have hstep : δt ^ g ≤ (δ ^ w) ^ g := NNReal.rpow_le_rpow hle hg
  have hcast : ((δt ^ g : ℝ≥0) : ℝ≥0∞) ≤ (((δ ^ (w * g) : ℝ≥0)) : ℝ≥0∞) := by
    refine ENNReal.coe_le_coe.mpr ?_
    rw [NNReal.rpow_mul]
    exact hstep
  rwa [ENNReal.coe_rpow_of_nonneg _ hg,
    ENNReal.coe_rpow_of_nonneg _ (mul_nonneg hw hg)] at hcast

/-! ## The cardinality estimate needed for the product bound — the `hcard` binder, closed -/

section Card

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {δ : ℝ≥0} {ι : Type u} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {σ : ℕ → ℝ≥0}
  {Cu : ℝ≥0}

open Classical in
/-- **The two fine fibres are the same `Finset`, not merely comparable.**

`Kakeya.ML2Core.exists_twoScale_with_fine_factor` takes the fine fibre inside the *node-restricted*
family `{i ∈ s | assign b i ∈ t₁}`, while
`Kakeya.ML2Reduction.card_class_mul_card_coarseFibre_mul_card_le` states its first bracket inside
`s`.  When the node `j` is one of the retained ones (`j ∈ t₁`), a leaf assigned to `j` is
automatically node-restricted, so the two filters are **equal**.  This is what lets the estimate be used
without an adapter, and it is the whole content of the `hcard` binder the estimate carried. -/
theorem filter_assign_eq_of_mem {κ : Type*} (s : Finset ι) (f : ι → κ) (t : Finset κ)
    {j : κ} (hj : j ∈ t) :
    {i ∈ ({i ∈ s | f i ∈ t} : Finset ι) | f i = j} = {i ∈ s | f i = j} := by
  ext i
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨his, _⟩, hij⟩
    exact ⟨his, hij⟩
  · rintro ⟨his, hij⟩
    exact ⟨⟨his, hij ▸ hj⟩, hij⟩

open Classical in
/-- **the estimate, cast into product.**

`Kakeya.ML2Reduction.card_class_mul_card_coarseFibre_mul_card_le` proves the three-factor
cardinality bound in `ℝ≥0` with the fine fibre taken inside `s`; the estimate needs it in `ENNReal` with
the fine fibre taken inside the node-restricted family.  Both moves are free —
`Kakeya.ML2Core.filter_assign_eq_of_mem` for the first and a cast for the second — so **the
`hcard` binder of `Kakeya.ML2Reduction.spine_multiplicity_le_nonEccentric_of_canonicalCover` is
discharged, not carried.**

The hypothesis `jτ ∈ t₁` is the only new one, and the estimate supplies it: `jτ` is chosen *in* the
retained set `tτ' ⊆ t₁`. -/
theorem card_three_factor_le (𝒰 : Tube.ChainUniformTubeSet s T N σ Cu)
    {a b : ℕ} (hab : a ≤ b) (haN : a ≤ N) (hbN : b ≤ N)
    {t₁ tτ' tθ' : Finset ι} (ht₁ : t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover b)
    (htτ : tτ' ⊆ ML2Reduction.activeNodes 𝒰.cover b) (htθ : tθ' ⊆ 𝒰.cover.indexSet a)
    {jτ jθ : ι} (hjτ : jτ ∈ t₁) :
    ((({i ∈ ({i ∈ s | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
          𝒰.cover.assign b i = jτ}).card : ℝ≥0∞))
        * ((({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover a b j = jθ}).card : ℝ≥0∞))
        * ((tθ'.card : ℝ≥0∞))
      ≤ ((Cu ^ 5 : ℝ≥0) : ℝ≥0∞) * (s.card : ℝ≥0∞) := by
  have hmem : jτ ∈ 𝒰.cover.indexSet b :=
    ML2Reduction.activeNodes_subset 𝒰.cover b (ht₁ hjτ)
  have hW6 := ML2Reduction.card_class_mul_card_coarseFibre_mul_card_le 𝒰 hab haN hbN htτ htθ
    (jθ := jθ) hmem
  rw [filter_assign_eq_of_mem s (𝒰.cover.assign b) t₁ hjτ]
  exact_mod_cast hW6

end Card

/-! ## The multiplicity → mass conversion of the estimate -/

/-- **The mass form the right disjunct of `Kakeya.ML2Core.dichotomy_of_dichotomyLeft_or_gain`
states.**  `ShadedBody.multiplicity_le_iff` is an iff, so no hypothesis is spent and the
conversion is exact; the only work is the associativity
`(δ^g · |s|^β) · vol(⋃) = δ^g · |s|^β · vol(⋃)`. -/
theorem sum_shade_le_of_multiplicity_le' {δ : ℝ≥0} {ι : Type*} {s : Finset ι} {c : ℝ≥0∞}
    (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (h : ShadedBody.multiplicity s (fun i ↦ (T i).toShadedBody) ≤ c) :
    ∑ i ∈ s, volume (T i).shade ≤ c * volume (⋃ i ∈ s, (T i).shade) :=
  (ShadedBody.multiplicity_le_iff s (fun i ↦ (T i).toShadedBody)).mp h

/-- The same, with the bound in the exponent shape `Kakeya.ML2Assembly.Dichotomy` states. -/
theorem sum_shade_le_of_multiplicity_le {δ : ℝ≥0} {β g : ℝ} {ι : Type*} {s : Finset ι}
    (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (h : ShadedBody.multiplicity s (fun i ↦ (T i).toShadedBody)
      ≤ (δ : ℝ≥0∞) ^ g * (s.card : ℝ≥0∞) ^ β) :
    ∑ i ∈ s, volume (T i).shade
      ≤ (δ : ℝ≥0∞) ^ g * (s.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ s, (T i).shade) :=
  (ShadedBody.multiplicity_le_iff s (fun i ↦ (T i).toShadedBody)).mp h

/-! ## the estimate: the two branches under one `filter_upwards` -/

/-! ## The `hret` binder: the bookkeeping half, closed -/

/-! ## the estimate, assembled: the compatibility the compiler adjudicates -/

section Assembled

variable {δ : ℝ≥0} {ι : Type u} {s : Finset ι}
  {V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {Nn : ℕ} {σ : ℕ → ℝ≥0} {Cu : ℝ≥0}

open Classical in
/-- **the estimate.**  The three factors, product and cardinality bound, multiplied and
converted to the mass form `Kakeya.ML2Assembly.Dichotomy` states.

Every index set below is written exactly as
`Kakeya.ML2Core.exists_twoScale_with_fine_factor` produces it, and the cardinality bound is
`Kakeya.ML2Core.card_three_factor_le`, so **no adapter stands between the estimate and this row**:
any drift in their statements breaks this declaration.  That is the point of stating it, and it is
why `hprod` and `hfine` are written out rather than abstracted.

The only abstract binders are the *middle* factor `hmid` — the one GWZ proves by rescaling to
`(𝕋̃, Ỹ)` and case-splitting (`Kakeya.ML2Core.middle_factor_of_cases` reads the two branches at a
common exponent) — and the coarse factor `hcoarse`, which
`Kakeya.ML2Core.exists_coarse_factor_at_window` supplies.

The conclusion is on the **node-restricted** family `{i ∈ s | assign b i ∈ t₁}` with `|s|^β` on the
right, because that is what the estimate delivers: the cardinality loss is already paid against the whole
of `s`. -/
theorem mass_gain_of_three_factors
    (𝒰 : Tube.ChainUniformTubeSet s (fun i ↦ (V i).toTube) Nn σ Cu)
    {a b : ℕ} (hab : a ≤ b) (haN : a ≤ Nn) (hbN : b ≤ Nn)
    {t₁ tτ' tθ' : Finset ι} (ht₁ : t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover b)
    (htτ : tτ' ⊆ ML2Reduction.activeNodes 𝒰.cover b) (htθ : tθ' ⊆ 𝒰.cover.indexSet a)
    {jτ jθ : ι} (hjτ : jτ ∈ t₁)
    {Yτ' : ι → ShadedTube (σ b) (EuclideanSpace ℝ (Fin 3))}
    {Yθ : ι → ShadedTube (σ a) (EuclideanSpace ℝ (Fin 3))}
    {Y' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    {L : ℝ≥0∞} {β εf gm εc κ g : ℝ}
    (hδ0 : (δ : ℝ≥0∞) ≠ 0) (hδ1 : (δ : ℝ≥0∞) ≤ 1) (hβ0 : 0 ≤ β)
    (hprod : ShadedBody.multiplicity ({i ∈ s | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
          (fun i ↦ (V i).toShadedBody)
        ≤ L
          * ShadedBody.multiplicity
              ({i ∈ ({i ∈ s | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
                𝒰.cover.assign b i = jτ} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
          * ShadedBody.multiplicity
              ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover a b j = jθ} : Finset ι)
              (fun j ↦ (Yτ' j).toShadedBody)
          * ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody))
    (hfine : ShadedBody.multiplicity
          ({i ∈ ({i ∈ s | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
            𝒰.cover.assign b i = jτ} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
        ≤ (δ : ℝ≥0∞) ^ (-εf)
          * ((({i ∈ ({i ∈ s | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
                𝒰.cover.assign b i = jτ} : Finset ι)).card : ℝ≥0∞) ^ β)
    (hmid : ShadedBody.multiplicity
          ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover a b j = jθ} : Finset ι)
          (fun j ↦ (Yτ' j).toShadedBody)
        ≤ (δ : ℝ≥0∞) ^ gm
          * ((({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover a b j = jθ}
                : Finset ι)).card : ℝ≥0∞) ^ β)
    (hcoarse : ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody)
        ≤ (δ : ℝ≥0∞) ^ (-εc) * ((tθ'.card : ℕ) : ℝ≥0∞) ^ β)
    (hL : L * (((Cu ^ 5 : ℝ≥0) : ℝ≥0∞)) ^ β ≤ (δ : ℝ≥0∞) ^ (-κ))
    (hexp : g ≤ gm - εf - εc - κ) :
    ∑ i ∈ ({i ∈ s | 𝒰.cover.assign b i ∈ t₁} : Finset ι), volume (V i).shade
      ≤ (δ : ℝ≥0∞) ^ g * (s.card : ℝ≥0∞) ^ β
        * volume (⋃ i ∈ ({i ∈ s | 𝒰.cover.assign b i ∈ t₁} : Finset ι), (V i).shade) := by
  refine sum_shade_le_of_multiplicity_le' V ?_
  exact multiplicity_le_of_three_factors hδ0 hδ1 hβ0 hprod hfine hmid hcoarse
    (card_three_factor_le 𝒰 hab haN hbN ht₁ htτ htθ (jθ := jθ) hjτ) hL hexp

end Assembled

/-! ## The upstairs ED-multiplicity exponent `m`: when it is zero -/

section EdMult

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

open Classical in
/-- **A pairwise essentially distinct family has ED-multiplicity `1`.**

`Kakeya.ML2Reduction.hup_of_step8`'s third clause prices the upstairs extraction by the family's
ED-multiplicity `M`, and the whole non-eccentric count chain closes iff `M ≤ ρ^{-m}` with
`m < ζ' - ζ`.  If the family step 8 is read on is *already* pairwise essentially distinct then the
fibre of `i` is `{i}` — a tube is never essentially distinct from itself, and every other member is
— so `M = 1` and **`m = 0`**: no extraction happens and no exponent is spent.

Nothing here is about tubes; it is the combinatorial content of "pairwise", stated on tubes only
because that is where it is used. -/
theorem card_notEssDistinct_le_one {ι : Type*} {t : Finset ι} {ρ : ℝ≥0} (W : ι → Tube ρ E)
    (hED : (t : Set ι).Pairwise
      fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier)
    {i : ι} (hi : i ∈ t) :
    (t.filter (fun j ↦
      ¬ _root_.IsEssentiallyDistinct (W j).carrier (W i).carrier)).card ≤ 1 := by
  have hsub : t.filter (fun j ↦
      ¬ _root_.IsEssentiallyDistinct (W j).carrier (W i).carrier) ⊆ {i} := by
    intro j hj
    obtain ⟨hjt, hjnd⟩ := Finset.mem_filter.mp hj
    by_cases hji : j = i
    · simp [hji]
    · exact absurd (hED hjt hi hji) hjnd
  calc (t.filter (fun j ↦
        ¬ _root_.IsEssentiallyDistinct (W j).carrier (W i).carrier)).card
      ≤ ({i} : Finset ι).card := Finset.card_le_card hsub
    _ = 1 := Finset.card_singleton i

end EdMult

end Kakeya.ML2Core

end

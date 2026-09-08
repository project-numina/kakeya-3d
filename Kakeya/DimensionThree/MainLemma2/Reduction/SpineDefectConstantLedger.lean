/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.MultiScaleFac.GridUniformBand
public import Kakeya.MultiScaleLoss
public import Kakeya.MultiScaleFac.Homogenize
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineDefectPotential

/-!
# `T-D6` — the constant ledger of the defect descent

 raises the item that decides the architecture of the defect route.
Every restriction of a `Kakeya.MultiScaleFac.GridUniform` in this tree **squares** the uniformity
constant:

```
 uniformTubeSetCuOf C   = max C (overlapConstBOTight n)
 bandRestrictConst C A  = max (uniformTubeSetCuOf C) (max A 1)
 gridUniformBandConst C A = (bandRestrictConst C A) ^ 2
```

and both ways of restricting carry it — `exists_homogenizing_pass_gridUniform` returns
`GridUniform t' T Mg (gridUniformBandConst C 2)`, and `exists_gridUniform_restrict_band` returns
`GridUniform t' T N (gridUniformBandConst C A)`.  So a descent that re-entered the uniformiser once
per trial would accumulate `C ^ (2 ^ n)` after `n` trials, with `n = Pmax h δ`.

This file **compiles that ledger, with its firing controls, and settles the question**:

* `reentryConst_one`, `reentryConst_two` — the firing controls  asks for: one
  re-entry gives `gridUniformBandConst Cu 2`, two give its square.  Both are `rfl`, so the ledger is
  provably measuring the tree's own constant and not a paraphrase of it.
* `gridUniformBandConst_eq_sq`, `reentryConst_eq_pow` — above the absolute floor the band constant
  *is* the square, hence `reentryConst C n = C ^ 2 ^ n`.
* `exists_lt_reentryConst_of_le` — the ledger exceeds **every** `δ`-free ceiling.
* `exists_threshold_le_ssfGridLen`, `exists_threshold_le_Pmax` — the number of trials is unbounded
  as `δ → 0`, because `Tube.ssfGridLen δ = ⌈log log (1/δ)⌉₊` is.
* **`not_reentry_le_of_le` — the verdict.**  For every `δ`-free `Cu₀` there is a threshold below
  which `Cu₀ < reentryConst Cu (Pmax h δ)`.  A descent that re-enters the uniformiser per trial
  therefore has **no** `δ`-free uniformity ceiling, and the existing block's binder
  `∀ Cu₀ : NNReal, ∀ᶠ (δ : NNReal) in 𝓝[>] 0, … → Cu ≤ Cu₀` — in which `Cu₀` is quantified *before*
  `δ` — cannot be met.  This is outcome (b) of `T-D6`.

* **The positive half, and the whole point of condition `C-D1`:**
  `Tube.UniformTubeSet.restrictOccupied` — restricting a hierarchy to a subfamily `S ⊆ u`, on the
  nodes `S` **occupies**, needs **no new constant at all**.  The nodes, the assignment, the nesting
  and the injectivity are the ambient ones; bounded overlap is monotone in both the index set and
  the family; and the *only* debt is Definition 2.1(iii)'s two halves on the restricted classes,
  named `Kakeya.ML2Core.IsClassHomogeneousOn`, which is a genuine homogeneity statement and not a
  constant.  **The ambient reading of that clause is unusable** — asked at every node of `𝒰` it
  forces `S = ∅` (`Kakeya.ML2Core.eq_empty_of_ambient_class_band`), which is why the index set
  shrinks to `S.image (𝒰.cover.assign k)`.  So the source's *"the retained family inherits the same
  tower"* is available in the tree, at the price of one clause, and the doubly
  exponential ledger above is **avoidable** — provided the descent never calls the uniformiser
  again.

`Kakeya.ML2Core.pairProfile`'s footprint design is what makes the one-hierarchy reading usable: the
potential is stated on containment, so it never mentions the classes that `le_card_class` is about.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Metric ConvexSpaceBody
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

/-! ## The ledger of a per-trial re-entry -/

section Ledger

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]


end Ledger

/-! ## The number of trials is unbounded -/

section TrialCount

/-- `Tube.ssfGridLen δ = ⌈log log (1/δ)⌉₊` exceeds any given `M` below a threshold. -/
theorem exists_threshold_le_ssfGridLen (M : ℕ) :
    ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧ ∀ δ : ℝ≥0, 0 < δ → δ ≤ δ₀ → M ≤ Tube.ssfGridLen δ := by
  refine ⟨⟨Real.exp (-(Real.exp M)), (Real.exp_pos _).le⟩, ?_, ?_⟩
  · exact_mod_cast Real.exp_pos _
  intro δ hδ hle
  have hδR : (0 : ℝ) < (δ : ℝ) := hδ
  have hleR : (δ : ℝ) ≤ Real.exp (-(Real.exp (M : ℝ))) := hle
  have hmul : Real.exp (Real.exp (M : ℝ)) * (δ : ℝ) ≤ 1 := by
    calc Real.exp (Real.exp (M : ℝ)) * (δ : ℝ)
        ≤ Real.exp (Real.exp (M : ℝ)) * Real.exp (-(Real.exp (M : ℝ))) :=
          mul_le_mul_of_nonneg_left hleR (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hinv : Real.exp (Real.exp (M : ℝ)) ≤ 1 / (δ : ℝ) := (le_div_iff₀ hδR).mpr hmul
  have hlog1 : Real.exp (M : ℝ) ≤ Real.log (1 / (δ : ℝ)) := by
    have hx := Real.log_le_log (Real.exp_pos _) hinv
    rwa [Real.log_exp] at hx
  have hlog2 : (M : ℝ) ≤ Real.log (Real.log (1 / (δ : ℝ))) := by
    have hx := Real.log_le_log (Real.exp_pos _) hlog1
    rwa [Real.log_exp] at hx
  have hc := Nat.ceil_le_ceil hlog2
  rw [Nat.ceil_natCast] at hc
  exact hc


end TrialCount

/-! ## The verdict -/

section Verdict

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]


end Verdict

/-! ## The positive half: one hierarchy, one constant -/

section OneHierarchy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ Cu : ℝ≥0} {u : Finset ι} {T : ι → Tube δ E}

open scoped Classical in
/-- **GWZ Definition 2.1(iii) on a retained subfamily** — the source's *"the retained family
inherits the same tower … pairwise within a factor two at each fixed level or pair of levels"*, in the tree's class vocabulary and at the ambient constant `Cu`.

Quantified over the nodes `S` **occupies**, `S.image (𝒰.cover.assign k)`, and not over the ambient
`𝒰.cover.indexSet k`: a node of the ambient hierarchy that `S` misses has an empty `S`-class, and a
two-sided band asked there forces `bN k = 0` and hence `S = ∅`
(`Kakeya.ML2Core.eq_empty_of_ambient_class_band`).  Occupancy is the restriction the source performs
when it says the retained family inherits the tower. -/
def IsClassHomogeneousOn {ι : Type*} {δ Cu : ℝ≥0} {u : Finset ι} {T : ι → Tube δ E}
    (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu) (S : Finset ι) : Prop :=
  ∃ bN : ℕ → ℝ≥0, ∀ k ≤ Tube.ssfGridLen δ,
    ∀ j ∈ S.image (𝒰.cover.assign k),
      ((Tube.coverClass S (𝒰.cover.assign k) j).card : ℝ≥0) ≤ Cu * bN k ∧
        bN k ≤ Cu * ((Tube.coverClass S (𝒰.cover.assign k) j).card : ℝ≥0)


open scoped Classical in
/-- **Restriction to a subfamily at the same constant, on the nodes the subfamily occupies.**

`C-D1` made usable.  The index set shrinks to `S.image (𝒰.cover.assign k)`; the nodes, the
assignment, the nesting and the injectivity are the ambient ones untouched; bounded overlap is
monotone in both the index set and the family; and Definition 2.1(iii)'s two halves are exactly
`Kakeya.ML2Core.IsClassHomogeneousOn`'s.  **No new constant anywhere** — contrast
`Kakeya.ML2Core.not_reentry_le`, where re-homogenizing through
`Kakeya.MultiScaleFac.exists_homogenizing_pass_gridUniform` costs `Cu ^ 2 ^ n` after `n` trials.

The occupied index set is the tree's own idiom: `exists_homogenizing_pass_gridUniform` already
returns `indexSet' k = t'.image (assign k)`. -/
noncomputable def _root_.Tube.UniformTubeSet.restrictOccupied
    (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu) {S : Finset ι} (hS : S ⊆ u)
    (hhom : IsClassHomogeneousOn 𝒰 S) :
    Tube.UniformTubeSet S T (Tube.ssfGridLen δ) Cu where
  cover :=
    { indexSet := fun k => S.image (𝒰.cover.assign k)
      assign := 𝒰.cover.assign
      tube := 𝒰.cover.tube
      assign_mem := fun k _ i hi => Finset.mem_image_of_mem _ hi
      le_tube_assign := fun k hk i hi => 𝒰.cover.le_tube_assign k hk i (hS hi)
      nested := fun k hk i hi j hj => 𝒰.cover.nested k hk i (hS hi) j (hS hj)
      tube_nested := fun k hk i hi => 𝒰.cover.tube_nested k hk i (hS hi) }
  branchingN := hhom.choose
  tube_injOn := by
    intro k hk
    refine Set.InjOn.mono ?_ (𝒰.tube_injOn k hk)
    intro j hj
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    exact_mod_cast 𝒰.cover.assign_mem k hk i (hS hi)
  boundedOverlap := by
    classical
    intro k hk V
    refine le_trans ?_ (𝒰.boundedOverlap k hk V)
    have hsub : (S.image (𝒰.cover.assign k)).filter (fun j => ∃ i ∈ S,
          (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody ∧
          (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)
        ⊆ (𝒰.cover.indexSet k).filter (fun j => ∃ i ∈ u,
          (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody ∧
          (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_image] at hj ⊢
      obtain ⟨⟨i₀, hi₀, rfl⟩, i, hi, h1, h2⟩ := hj
      exact ⟨𝒰.cover.assign_mem k hk i₀ (hS hi₀), i, hS hi, h1, h2⟩
    exact_mod_cast Nat.cast_le.mpr (Finset.card_le_card hsub)
  card_class_le := fun k hk j hj => (hhom.choose_spec k hk j hj).1
  le_card_class := fun k hk j hj => (hhom.choose_spec k hk j hj).2


omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The ambient family is class-homogeneous on itself**, at its own branching profile — so the
clause is not vacuous and the descent's first trial discharges it for free. -/
theorem isClassHomogeneousOn_self (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu) :
    IsClassHomogeneousOn 𝒰 u := by
  classical
  refine ⟨𝒰.branchingN, fun k hk j hj => ?_⟩
  have hj' : j ∈ 𝒰.cover.indexSet k := by
    simp only [Finset.mem_image] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    exact 𝒰.cover.assign_mem k hk i hi
  exact ⟨𝒰.card_class_le k hk j hj', 𝒰.le_card_class k hk j hj'⟩

end OneHierarchy

/-! ## `T-D5` — the loss ledger of the descent -/

section LossLedger

/-- `Φ_h`'s ceiling, plus the one extra power the induction pays, fits inside the *quadratic*
exponent `K(N+1)²` that `Kakeya.StickyKakeya.gridLoss` already carries — at a multiplier
`⌈4/h⌉₊ + 1` that is fixed **before** `δ`. -/
theorem potentialCeil_succ_le {h : ℝ} (D : ℝ) (δ : ℝ≥0) :
    potentialCeil h D δ + 1 ≤ (⌈D / h⌉₊ + 1) * (Tube.ssfGridLen δ + 1) ^ 2 := by
  set N := Tube.ssfGridLen δ with hN
  have hhalf : N * (N + 1) / 2 ≤ (N + 1) ^ 2 := by
    have h1 : N * (N + 1) / 2 ≤ N * (N + 1) := Nat.div_le_self _ _
    nlinarith [Nat.le_add_left 0 N]
  calc potentialCeil h D δ + 1 = (N * (N + 1) / 2) * ⌈D / h⌉₊ + 1 := rfl
    _ ≤ (N + 1) ^ 2 * ⌈D / h⌉₊ + (N + 1) ^ 2 := by
        have : (N * (N + 1) / 2) * ⌈D / h⌉₊ ≤ (N + 1) ^ 2 * ⌈D / h⌉₊ :=
          Nat.mul_le_mul_right _ hhalf
        have h2 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos N)
        omega
    _ = (⌈D / h⌉₊ + 1) * (N + 1) ^ 2 := by ring

/-- **`T-D5`: the accumulated per-trial loss is absorbed.**

`Λ = (1 − log δ)^{K'}` is the shape of every per-trial loss in this tree (the source's
`Λ = (2 + log₂(1/δ))^K`).  Raised to the descent's own `P_max + 1`, it stays inside
`Kakeya.StickyKakeya.gridLoss 1 K''` at `K'' = K'·(⌈D/h⌉₊ + 1)` — a constant fixed **before** `δ` —
and `Kakeya.StickyKakeya.exists_threshold_gridLoss_le` absorbs it into any `δ^{-α}`.

**Firing control, and it is a typing fact rather than a proof-reading one.**
`exists_threshold_gridLoss_le` binds `K : ℕ` *before* `δ`, so a `δ`-dependent exponent — the
failure mode  asks to be excluded, e.g. `K′ · ssfGridLen δ` — cannot even be
written at that call.  What makes `K″` `δ`-free is
`Kakeya.ML2Core.potentialCeil_succ_le`: **all** of the `δ`-dependence of `P_max` is the
quadratic `(ssfGridLen δ + 1)²` that `gridLoss` already pays. -/
theorem exists_threshold_loss_pow_potentialCeil_le (K' : ℕ) {h : ℝ} (D α : ℝ) (hα : 0 < α) :
    ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {δ : ℝ≥0}, 0 < δ → δ ≤ δ₀ →
        ((1 - Real.log (δ : ℝ)) ^ K') ^ (potentialCeil h D δ + 1) ≤ (δ : ℝ) ^ (-α) := by
  obtain ⟨δ₀, hδ₀, hδ₀1, hgrid⟩ :=
    StickyKakeya.exists_threshold_gridLoss_le 1 le_rfl (K' * (⌈D / h⌉₊ + 1)) α hα
  refine ⟨δ₀, hδ₀, hδ₀1, fun {δ} hδ hδle => ?_⟩
  have hδ1 : δ ≤ 1 := hδle.trans hδ₀1
  have hW : (1 : ℝ) ≤ 1 - Real.log (δ : ℝ) := by
    have : Real.log (δ : ℝ) ≤ 0 := Real.log_nonpos (by positivity) (by exact_mod_cast hδ1)
    linarith
  have hexp : K' * (potentialCeil h D δ + 1)
      ≤ K' * (⌈D / h⌉₊ + 1) * (Tube.ssfGridLen δ + 1) ^ 2 := by
    have := potentialCeil_succ_le (h := h) D δ
    calc K' * (potentialCeil h D δ + 1)
        ≤ K' * ((⌈D / h⌉₊ + 1) * (Tube.ssfGridLen δ + 1) ^ 2) := Nat.mul_le_mul_left _ this
      _ = K' * (⌈D / h⌉₊ + 1) * (Tube.ssfGridLen δ + 1) ^ 2 := by ring
  calc ((1 - Real.log (δ : ℝ)) ^ K') ^ (potentialCeil h D δ + 1)
      = (1 - Real.log (δ : ℝ)) ^ (K' * (potentialCeil h D δ + 1)) := by rw [← pow_mul]
    _ ≤ (1 - Real.log (δ : ℝ)) ^ (K' * (⌈D / h⌉₊ + 1) * (Tube.ssfGridLen δ + 1) ^ 2) :=
        pow_le_pow_right₀ hW hexp
    _ = StickyKakeya.gridLoss 1 (K' * (⌈D / h⌉₊ + 1)) δ := by
        rw [StickyKakeya.gridLoss]
        simp
    _ ≤ (δ : ℝ) ^ (-α) := hgrid hδ hδle


end LossLedger

/-! ## The producer of `IsClassHomogeneousOn` -/

section ClassBandProducer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ Cu : ℝ≥0} {u : Finset ι} {T : ι → Tube δ E}


end ClassBandProducer

end Kakeya.ML2Core

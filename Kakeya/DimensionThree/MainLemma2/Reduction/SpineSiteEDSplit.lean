/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineMiddleFactor
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineLineEDMiddle
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineMiddleProducer
public import Kakeya.DimensionThree.MainLemma2.Reduction.BandSqueeze
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineOuterUniformity
public import Kakeya.Tube.CardEssentiallyDistinct
public import Kakeya.DimensionThree.MainLemma2.Reduction.AssemblyPointwise

/-!
# `hED` / `hstep8`, split into a family and a floor — and where the floor is not

The last open row at all six middle-factor sites is an essentially distinct family of `ρb`-tubes
inside `T₀`, all-used over `s'`, of cardinality at least `ρ^{-2-ζ'}`.  This leaf separates the two
things that row asks for and measures which of them the large-family reading of Main Lemma 2
supplies.

## The split

`edCover_of_supplier_of_floor` factors the row into

* a **supplier** — for each `ρ` of the widened window, an essentially distinct family of
  `ρb`-tubes inside `T₀`, all-used over `s'`, with *whatever* count `N ρ` it happens to have; and
* a **floor** — `ρ^{-2-ζ'} ≤ N ρ`, a scalar row on the supplier's own count.

`hstep8_of_supplier_of_floor` composes that with the existing
`Kakeya.ML2Core.hstep8_of_essDistinct`, so the same two inputs give `hstep8` at `m = 0`, which is
the shape the step-8 site binds.  Neither half is proved here; the point of the split is that they
have different owners and only one of them is geometry.

## The floor is NOT supplied by the large-family reading — measured

The run's target is the large-family Main Lemma 2, whose export
`Kakeya.KKTResidual.KatzTaoEstimateStrict` carries `δ^{-2} ≤ |𝕋|`.  Three measurements, and the
conclusion is negative:

1. `Kakeya.ML2Assembly.Dichotomy` — what `GeometricCoreAt` actually asks a producer to prove —
   carries `(δ : ℝ)⁻¹ ≤ |𝕋|`, **`δ^{-1}`, not `δ^{-2}`**.  `cardFloor_strict_le_dichotomy` shows
   the strict clause implies it, which is exactly how
   `Kakeya.ML2Large.strict_drop_of_geometricCoreAt` gets from one to the other; and
   `not_cardFloor_dichotomy_le_strict` refutes the converse at `δ = 1/4`, so the two are genuinely
   different hypotheses and the stronger one is *spent* at that step, not carried.
2. The six middle-factor sites bind **no** cardinality lower bound of their own.  The only such
   bound anywhere in their signatures is the one inside `hED`/`hstep8` itself — i.e. the floor is
   part of what must be proved, not part of what is assumed.
3. Even granting `δ^{-2} ≤ |𝕋|` at the outer scale, it is a bound on `|𝕋|`, and the floor is a
   bound on the cardinality of a **different** family — a cover by `ρb`-tubes.  The all-used row
   gives a map from the cover to `s'`, and that map is not injective for essentially distinct
   covers (two essentially distinct `ρb`-tubes may both contain the same much thinner `δt`-tube),
   so no comparison between the two cardinalities exists in the tree.

So the floor is an open row with a named owner elsewhere, not a hypothesis this run may help
itself to.  What the tree *does* prove about it is the **ceiling**:
`Kakeya.VeryNotSticky.exists_threshold_exponent_le_four`  says a family meeting the floor
at `ζ'` inside the unit ball forces `ζ' ≤ 4` below an explicit threshold.  Floor and ceiling meet
only in `ζ' ∈ (0, 4]`, which is §AD's band; nothing here reintroduces `ζ' > 4`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Filter Topology Kakeya Kakeya.ML2Reduction

namespace Kakeya.ML2Core

universe u

theorem edCover_of_supplier_of_floor {b δt δ' : ℝ≥0} {ϖ ζ' : ℝ} {N : ℝ≥0 → ℝ}
    {α : Type u} {s' : Finset α}
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3)))
    (𝕋 : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3)))
    (hsup : ∀ ρ : ℝ≥0, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))),
        ((t : Set κ₀).Pairwise
          fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
        (∀ k ∈ t, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t, ∃ i ∈ s', (𝕋 i).carrier ⊆ (W k).carrier) ∧
        N ρ ≤ (t.card : ℝ))
    (hfloor : ∀ ρ : ℝ≥0, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      (ρ : ℝ) ^ (-2 - ζ') ≤ N ρ) :
    ∀ ρ : ℝ≥0, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))),
        ((t : Set κ₀).Pairwise
          fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
        (∀ k ∈ t, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t, ∃ i ∈ s', (𝕋 i).carrier ⊆ (W k).carrier) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ) := by
  intro ρ hρ
  obtain ⟨κ₀, t, W, hED, hsubW, hused, hcard⟩ := hsup ρ hρ
  exact ⟨κ₀, t, W, hED, hsubW, hused, le_trans (hfloor ρ hρ) hcard⟩

theorem hstep8_of_supplier_of_floor {b δt δ' : ℝ≥0} {ϖ ζ' : ℝ} {N : ℝ≥0 → ℝ}
    {α : Type u} {s' : Finset α}
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3)))
    (𝕋 : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3)))
    (hsup : ∀ ρ : ℝ≥0, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))),
        ((t : Set κ₀).Pairwise
          fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
        (∀ k ∈ t, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t, ∃ i ∈ s', (𝕋 i).carrier ⊆ (W k).carrier) ∧
        N ρ ≤ (t.card : ℝ))
    (hfloor : ∀ ρ : ℝ≥0, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      (ρ : ℝ) ^ (-2 - ζ') ≤ N ρ) :
    ∀ ρ : ℝ≥0, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t₈ : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))) (M : ℕ),
        (∀ k ∈ t₈, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t₈, ∃ i ∈ s', (𝕋 i).carrier ⊆ (W k).carrier) ∧
        (∀ i ∈ t₈, (open scoped Classical in t₈.filter (fun j ↦
          ¬ _root_.IsEssentiallyDistinct (W j).carrier (W i).carrier)).card ≤ M) ∧
        (M : ℝ) ≤ (ρ : ℝ) ^ (-(0 : ℝ)) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t₈.card : ℝ) := by
  intro ρ hρ
  obtain ⟨κ₀, t, W, hED, hsubW, hused, hcard⟩ :=
    edCover_of_supplier_of_floor (ζ' := ζ') T₀ 𝕋 hsup hfloor ρ hρ
  exact Kakeya.ML2Core.hstep8_of_essDistinct t W hED hsubW hused hcard

/-- **Site 4's row, separately.**  `Kakeya.ML2Core.middle_factor_of_lineEDNodes_sharp` asks for a
*line*-essentially-distinct family at level count `A`, not a pairwise essentially distinct one, so
it is its own row and not an instance of `edCover_of_supplier_of_floor`.  The split is the same:
a supplier with whatever count it has, and the floor on that count. -/
theorem lineEDCover_of_supplier_of_floor {b δt δ' : ℝ≥0} {ϖ ζ' : ℝ} {N : ℝ≥0 → ℝ} {A : ℕ}
    {α : Type u} {s' : Finset α}
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3)))
    (𝕋 : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3)))
    (hsup : ∀ ρ : ℝ≥0, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))),
        Kakeya.VeryNotSticky.IsLineEssDistinctAt (Tube.tubeOverlapCoreClose.C 3) A t W ∧
        (∀ l ∈ t, (W l).carrier ⊆ T₀.carrier) ∧
        (∀ l ∈ t, ∃ i ∈ s', (𝕋 i).carrier ⊆ (W l).carrier) ∧
        N ρ ≤ (t.card : ℝ))
    (hfloor : ∀ ρ : ℝ≥0, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      (ρ : ℝ) ^ (-2 - ζ') ≤ N ρ) :
    ∀ ρ : ℝ≥0, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))),
        Kakeya.VeryNotSticky.IsLineEssDistinctAt (Tube.tubeOverlapCoreClose.C 3) A t W ∧
        (∀ l ∈ t, (W l).carrier ⊆ T₀.carrier) ∧
        (∀ l ∈ t, ∃ i ∈ s', (𝕋 i).carrier ⊆ (W l).carrier) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ) := by
  intro ρ hρ
  obtain ⟨κ₀, t, W, hline, hsubW, hused, hcard⟩ := hsup ρ hρ
  exact ⟨κ₀, t, W, hline, hsubW, hused, le_trans (hfloor ρ hρ) hcard⟩

/-! ## The source's covering bridge: shape, absorption, tie

 The floor has a producer after all — the source's
`lem:defect-covering-bridge`, which the GC route owes as VNS's *caller*.  Its
conclusion is **not** the sites' slot: the source concludes `θ · σ^{-2-2ζ} ≤ #𝕎`, with a `θ`
prefactor and exponent `2+2ζ`, while the site slot is the bare `σ^{-2-ζ} ≤ #t`.  The three
declarations below keep those apart, in the order source required: shape, then absorption
with its ordering explicit, then the tie.  The bridge's own five inputs are **not** proved here —
one of them is the `goodMassSet` input from the mass-coupled selection. -/

/-- **The absorption, named and isolated**: the source's prefactor is absorbed into the site's
exponent exactly when `σ^ζ ≤ θ`.  This is the whole of the shape difference; nothing else in the
bridge's conclusion moves. -/
theorem floor_absorb_of_rpow_le {σ : ℝ≥0} (hσ0 : 0 < σ) {ζ θ : ℝ}
    (hθ : (σ : ℝ) ^ ζ ≤ θ) :
    (σ : ℝ) ^ (-2 - ζ) ≤ θ * (σ : ℝ) ^ (-2 - 2 * ζ) := by
  have h0 : (0:ℝ) < (σ : ℝ) := hσ0
  have hpow : (0:ℝ) < (σ : ℝ) ^ (-2 - 2 * ζ) := Real.rpow_pos_of_pos h0 _
  calc (σ : ℝ) ^ (-2 - ζ)
      = (σ : ℝ) ^ ζ * (σ : ℝ) ^ (-2 - 2 * ζ) := by
        rw [← Real.rpow_add h0]; ring_nf
    _ ≤ θ * (σ : ℝ) ^ (-2 - 2 * ζ) := mul_le_mul_of_nonneg_right hθ hpow.le

/-- **The tie, at the source's shape.**  A supplier whose count row is the source's
`θ ρ · ρ^{-2-2ζ'} ≤ #t`, together with the ordering `ρ^{ζ'} ≤ θ ρ` on the window, fills the sites'
bare floor slot through `edCover_of_supplier_of_floor`.  The prefactor is carried, never dropped:
`hord` is a hypothesis of this theorem and `not_floor_absorb_without_ordering` shows it cannot be
omitted. -/
theorem edCover_of_sourceBridge {b δt δ' : ℝ≥0} {ϖ ζ' : ℝ} {θ : ℝ≥0 → ℝ}
    {α : Type u} {s' : Finset α}
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3)))
    (𝕋 : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3)))
    (hsup : ∀ ρ : ℝ≥0, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))),
        ((t : Set κ₀).Pairwise
          fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
        (∀ k ∈ t, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t, ∃ i ∈ s', (𝕋 i).carrier ⊆ (W k).carrier) ∧
        θ ρ * (ρ : ℝ) ^ (-2 - 2 * ζ') ≤ (t.card : ℝ))
    (hρ0 : ∀ ρ : ℝ≥0, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) → 0 < ρ)
    (hord : ∀ ρ : ℝ≥0, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      (ρ : ℝ) ^ ζ' ≤ θ ρ) :
    ∀ ρ : ℝ≥0, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))),
        ((t : Set κ₀).Pairwise
          fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
        (∀ k ∈ t, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t, ∃ i ∈ s', (𝕋 i).carrier ⊆ (W k).carrier) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ) :=
  edCover_of_supplier_of_floor (N := fun ρ ↦ θ ρ * (ρ : ℝ) ^ (-2 - 2 * ζ')) T₀ 𝕋 hsup
    (fun ρ hρ ↦ floor_absorb_of_rpow_le (hρ0 ρ hρ) (hord ρ hρ))

end Kakeya.ML2Core

/-! ## The two ties: the split fills the sites' slots by name -/

section Ties

variable {b δt δ' : ℝ≥0} {R : ℝ}
  {hsit : Tube.IsRescalingSituation b δt δ' R 3} {hR : 0 < R}
  {T₀ : Tube b (EuclideanSpace ℝ (Fin 3))}
  {A : Type u} {s s' : Finset A} {qc ϖ ζ ηd β ζ' ν cst : ℝ} {N : ℝ≥0 → ℝ}
  {𝕋 : A → ShadedTube δt (EuclideanSpace ℝ (Fin 3))}
  {U' : A → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))}

-- TIE A : the split fills `hstep8` at `Kakeya.ML2Core.fine_factor_of_lemma91At_of_step8`, m := 0
example
    (hsup : ∀ ρ : ℝ≥0, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))),
        ((t : Set κ₀).Pairwise
          fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
        (∀ k ∈ t, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t, ∃ i ∈ s', (𝕋 i).carrier ⊆ (W k).carrier) ∧
        N ρ ≤ (t.card : ℝ))
    (hfloor : ∀ ρ : ℝ≥0, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      (ρ : ℝ) ^ (-2 - ζ') ≤ N ρ) : True := by
  have _tie := Kakeya.ML2Core.fine_factor_of_lemma91At_of_step8
    (mm := 0) (β := β) (ζ' := ζ') (m := 0) (ν := ν) (cst := cst) (s := s) (s' := s')
    (qc := qc) (ηd := ηd) (ζ := ζ) (ϖ := ϖ)
    (𝕋 := 𝕋) (U' := U') (T₀ := T₀) (hsit := hsit) (hR := hR)
    (hstep8 := Kakeya.ML2Core.hstep8_of_supplier_of_floor (ζ' := ζ') T₀ 𝕋 hsup hfloor)
  trivial

-- TIE B : the split fills `hED` at `Kakeya.ML2Core.fine_factor_of_lemma91At_of_edCover`
example
    (hsup : ∀ ρ : ℝ≥0, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))),
        ((t : Set κ₀).Pairwise
          fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
        (∀ k ∈ t, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t, ∃ i ∈ s', (𝕋 i).carrier ⊆ (W k).carrier) ∧
        N ρ ≤ (t.card : ℝ))
    (hfloor : ∀ ρ : ℝ≥0, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      (ρ : ℝ) ^ (-2 - ζ') ≤ N ρ) : True := by
  have _tie := Kakeya.ML2Core.fine_factor_of_lemma91At_of_edCover
    (mm := 0) (β := β) (ζ' := ζ') (ν := ν) (cst := cst) (s := s) (s' := s')
    (qc := qc) (ηd := ηd) (ζ := ζ) (ϖ := ϖ)
    (𝕋 := 𝕋) (U' := U') (T₀ := T₀) (hsit := hsit) (hR := hR)
    (hED := Kakeya.ML2Core.edCover_of_supplier_of_floor (ζ' := ζ') T₀ 𝕋 hsup hfloor)
  trivial

set_option maxHeartbeats 1600000 in
-- TIE C : the line-ED split fills `hEDline` at `Kakeya.ML2Core.middle_factor_of_lineEDNodes_sharp`
example {ε₁ w ηc : ℝ} {gain dens : ℝ → ℝ} {kk : ℕ} {δ θ τ : ℝ≥0} {Rout : ℝ} {Alev : ℕ}
    {hsitOut : Tube.IsRescalingSituation θ τ δt Rout 3} {hRout : 0 < Rout}
    {Tθ : Tube θ (EuclideanSpace ℝ (Fin 3))} {Y : A → ShadedTube τ (EuclideanSpace ℝ (Fin 3))}
    {κc : Type u} {t' : Finset κc} {Zρ : κc → ShadedTube b (EuclideanSpace ℝ (Fin 3))}
    {Lc Cf Cu : ℝ≥0∞} {Nm : ℕ} {kap : ℝ}
    (hsup : ∀ ρ : ℝ≥0, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))),
        Kakeya.VeryNotSticky.IsLineEssDistinctAt (Tube.tubeOverlapCoreClose.C 3) Alev t W ∧
        (∀ l ∈ t, (W l).carrier ⊆ T₀.carrier) ∧
        (∀ l ∈ t, ∃ i ∈ s',
          (Kakeya.ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).carrier
            ⊆ (W l).carrier) ∧
        N ρ ≤ (t.card : ℝ))
    (hfloor : ∀ ρ : ℝ≥0, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      (ρ : ℝ) ^ (-2 - ζ') ≤ N ρ) : True := by
  have _tie := Kakeya.ML2Core.middle_factor_of_lineEDNodes_sharp
    (mm := 0) (hsitOut := hsitOut) (β := β) (ε₁ := ε₁) (gain := gain) (dens := dens) (k := kk)
    (δ := δ) (w := w) (κc := κc) (t' := t') (Zρ := Zρ) (ηc := ηc) (A := Alev)
    (cst := cst) (ζ := ζ) (ζ' := ζ') (ϖ := ϖ) (ηd := ηd) (qc := qc)
    (L := Lc) (Cf := Cf) (Cu := Cu) (Nm := Nm) (κ := kap) (s' := s') (U' := U') (T₀ := T₀)
    (fib := s)
    (hsit := hsit) (hR := hR)
    (hEDline := Kakeya.ML2Core.lineEDCover_of_supplier_of_floor (ζ' := ζ') T₀
      (Kakeya.ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) hsup hfloor)
  trivial

end Ties

end

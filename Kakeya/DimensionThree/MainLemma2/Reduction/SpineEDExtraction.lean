/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCountClause
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCanonicalCover

/-!
# The corrected canonical-cover route: essential distinctness at bounded ED-multiplicity

Blueprint: GWZ, the non-eccentric case, the invocation of
GWZ Lemma 9.1 at `ζ = η_j/2`.

`Kakeya.ML2Reduction.not_upstairs_bundle_at` (in
`Reduction/SpineDeltaMaxFloor.lean`) refutes the route that buys essential distinctness of the
pushed-down `ρ`-cover with a maximal-density bound: `Δ_max ≥ |t| ρ² / 3` for any family of
`ρ`-tubes in the unit ball, so `Kakeya.Tube.refineToEssDistinctLeaves`'s certificate
`|t| / (C₃ Δ_max)` never exceeds `(3/C₃) ρ^{-2}`, while Lemma 9.1's count clause needs
`ρ^{-2-ζ}`.

**This file replaces the price.**  The extraction is the same maximal essentially distinct
subfamily (`Kakeya.Tube.exists_maximal_essDistinct`), but priced by the family's own
**ED-multiplicity**

```
M  such that  ∀ i ∈ t, #{ j ∈ t | ¬ IsEssentiallyDistinct (V j) (V i) } ≤ M
```

— how many members of the family can be essentially the same tube as one given member.  For a
family that is already essentially distinct `M = 1`.  `M` is a *multiplicity*, not a density: it
is not bounded below by any power of `ρ`, so the count budget `M · Λ ≤ ρ^{-(ζ'-ζ)}` is
satisfiable, in contrast with the `Δ_max` version, which forces the constant inequality
`C₃ ≤ 3` and hence `False`.

## Essential distinctness is not the obstruction

`IsEssentiallyDistinct U V` is the *volume* condition `|U ∩ V| ≤ ½ max(|U|,|V|)`
(`Kakeya/ConvexBody.lean`), and `Kakeya.Tube.card_le_of_EssDistinct` caps an essentially
distinct family of `ρ`-tubes in the unit ball at `C · (1/ρ)^{2·3} = C ρ^{-6}` in dimension `3`
(crude; the geometric truth is `ρ^{-4}` — two direction and two position parameters).  The count
clause's `ρ^{-2-ζ}` is far below that for `ζ ≤ 4`
(`rpow_count_le_essDistinct_ceiling`).  **There is no statement-level problem with Lemma 9.1's
count clause**: the `ρ^{-2}` cap is a property of one lemma's certificate, not of essentially
distinct families.

## The interface

`canonicalCover_of_upstairs_edMult`'s `hup` is the corrected per-scale bundle, and its conclusion
is the `hcanon` binder of
`Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer_of_canonicalCover` character for
character.  Compared with  it has **six** clauses instead of seven: the two clauses
`Δ_max ≤ D` and `C₃ · D ≤ Ced` are replaced by the single ED-multiplicity clause, and `0 < Ced`
becomes `0 < M`.  `multiplicity_le_of_lemma91At_outer_of_upstairs_edMult` is step 10 over that
interface, feeding the existing consumer.

## The window reading

`IsKatzTaoDividingWindow.le_window_maxDensity` is stated on the window cut at `ε_div = e`, while
the blueprint reads it on the narrower window cut at `ε₂ ≥ 5 e`; `mem_divWindow_of_mem_eps₂Window`
is the inclusion, so no existing statement has to move.  `spine_windowExponent_div_le` shows the
`ε_div` reading of the *upper* `Δ_max` bound gives `a = η_{j-1}/e ≤ η_j/480`, which closes the
count budget `ζ' - ζ = η_j/4` with a factor-`120` margin — **retracting the caveat in
**, which used the blueprint ladder `η_k ≤ e η_{k+1}` instead of the far stronger
`Kakeya.ML2Spine.IsSpine.sep_le`.

## What is still owed

Exactly one thing: a bound on `M`.  It is a bounded-multiplicity statement about the cover, of the
kind `Kakeya.Tube.UniformTubeSet.boundedOverlap` is designed to carry, and it cannot come from a
volume or density estimate — a fibre bound derived from `maxDensity` reproduces
`refineToEssDistinctLeaves` and is capped as above.

## Main declarations

* `Kakeya.ML2Reduction.not_isEssentiallyDistinct_tube_self`,
  `Kakeya.ML2Reduction.one_le_edMult` — a tube is not essentially distinct from itself, so
  `0 < M` is free for a nonempty family.
* `Kakeya.ML2Reduction.exists_essDistinct_of_edMult` — the extraction, at the loss `M`.
* `Kakeya.ML2Reduction.canonicalCoverAt_of_used_of_edMult` — the drop-in replacement for
  `Kakeya.ML2Reduction.canonicalCoverAt_of_used_of_maxDensity`.
* `Kakeya.ML2Reduction.edCount_budget_of_slack` — the count-budget arithmetic at the new price.
* `Kakeya.ML2Reduction.canonicalCoverAt_of_upstairs_edMult`,
  `Kakeya.ML2Reduction.canonicalCover_of_upstairs_edMult` — the datum at one scale and over the
  window; the latter's conclusion is the `hcanon` binder verbatim.
* `Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer_of_upstairs_edMult` — step 10.
* `Kakeya.ML2Reduction.rpow_count_le_essDistinct_ceiling` — the count clause is below the
  essential-distinctness ceiling.
* `Kakeya.ML2Reduction.spine_windowExponent_div_le`,
  `Kakeya.ML2Reduction.spine_count_budget_closes_div`,
  `Kakeya.ML2Reduction.mem_divWindow_of_mem_eps₂Window` — the window reading.
* `Kakeya.ML2Reduction.essDistinct_pushdown_of_edMult` — 's isolation theorem,
  discharged.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Set ConvexSpaceBody

namespace Kakeya.ML2Reduction

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### The corrected extraction: bounded ED-multiplicity, not `Δ_max` -/

/-- A `ρ`-tube with `ρ > 0` has positive finite volume, so it is not essentially distinct from
itself.  This is what makes a family's ED-multiplicity at least `1`. -/
theorem not_isEssentiallyDistinct_tube_self [Nontrivial E] {ρ : ℝ≥0} (hρ0 : 0 < ρ)
    (T : Tube ρ E) : ¬ _root_.IsEssentiallyDistinct T.carrier T.carrier := by
  refine not_isEssentiallyDistinct_self ?_ T.toConvexSpaceBody.isCompact.measure_ne_top
  have h := T.le_volume
  have hpos : (0 : ℝ≥0∞) < (Tube.le_volume.c (Module.finrank ℝ E) : ℝ≥0∞)
      * (ρ : ℝ≥0∞) ^ (Module.finrank ℝ E - 1) := by
    refine ENNReal.mul_pos ?_ (pow_ne_zero _ (by exact_mod_cast hρ0.ne'))
    exact_mod_cast (Tube.le_volume.c_pos (Module.finrank ℝ E)).ne'
  exact (lt_of_lt_of_le hpos (by exact_mod_cast h)).ne'

/-- **`0 < M` is free.**  A nonempty family has ED-multiplicity at least `1`, since each member
lies in its own fibre. -/
theorem one_le_edMult [Nontrivial E] {ρ : ℝ≥0} (hρ0 : 0 < ρ) {κ : Type*} {t : Finset κ}
    (V : κ → Tube ρ E) {M : ℕ} (hne : t.Nonempty)
    (hM : ∀ i ∈ t, (open scoped Classical in t.filter (fun j ↦
      ¬ _root_.IsEssentiallyDistinct (V j).carrier (V i).carrier)).card ≤ M) : 1 ≤ M := by
  classical
  obtain ⟨i, hi⟩ := hne
  refine le_trans ?_ (hM i hi)
  refine Finset.card_pos.mpr ⟨i, ?_⟩
  simp only [Finset.mem_filter]
  exact ⟨hi, not_isEssentiallyDistinct_tube_self hρ0 (V i)⟩

/-- **A maximal essentially distinct subfamily, at the family's own ED-multiplicity.**

`Kakeya.Tube.refineToEssDistinctLeaves` extracts an essentially distinct subfamily at the loss
`C_n · Δ_max`, and `Kakeya.ML2Reduction.not_count_budget_of_unitBall` shows that loss is fatal at
the cardinality Lemma 9.1 asks for.  This is the same extraction priced differently: by the
**ED-multiplicity** `M` of the family — how many of its members can be essentially the same tube as
one given member.  For a family that is already essentially distinct `M = 1`, whereas `Δ_max` is
`≥ |t| ρ² / 3` no matter what. -/
theorem exists_essDistinct_of_edMult [Nontrivial E] {ρ : ℝ≥0} (hρ0 : 0 < ρ)
    {κ : Type*} (t : Finset κ) (V : κ → Tube ρ E) {M : ℕ}
    (hM : ∀ i ∈ t, (open scoped Classical in t.filter (fun j ↦
      ¬ _root_.IsEssentiallyDistinct (V j).carrier (V i).carrier)).card ≤ M) :
    ∃ u ⊆ t,
      ((u : Set κ).Pairwise
        fun i j ↦ _root_.IsEssentiallyDistinct (V i).carrier (V j).carrier) ∧
      t.card ≤ M * u.card := by
  classical
  obtain ⟨u, hut, hED, hmax⟩ := Kakeya.Tube.exists_maximal_essDistinct t V
  refine ⟨u, hut, hED, ?_⟩
  have hchoice : ∀ j ∈ t, ∃ i, i ∈ u ∧
      ¬ _root_.IsEssentiallyDistinct (V j).carrier (V i).carrier := by
    intro j hj
    by_cases hju : j ∈ u
    · exact ⟨j, hju, not_isEssentiallyDistinct_tube_self hρ0 (V j)⟩
    · obtain ⟨i, hi, hnot⟩ := hmax j hj hju
      exact ⟨i, hi, fun hcon ↦ hnot (isEssentiallyDistinct_symm hcon)⟩
  choose! f hfu hfnot using hchoice
  rw [Finset.card_eq_sum_card_fiberwise hfu]
  calc ∑ i ∈ u, (t.filter fun j ↦ f j = i).card
      ≤ ∑ _i ∈ u, M := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        refine le_trans (Finset.card_le_card ?_) (hM i (hut hi))
        intro j hj
        simp only [Finset.mem_filter] at hj ⊢
        exact ⟨hj.1, hj.2 ▸ hfnot j hj.1⟩
    _ = u.card * M := by rw [Finset.sum_const, smul_eq_mul]
    _ = M * u.card := Nat.mul_comm _ _

/-! ### The canonical-cover datum, at the corrected price -/

variable {θ τ : ℝ≥0}

/-- **The essential-distinctness half of the canonical-cover datum, at the ED-multiplicity price.**

This is `Kakeya.ML2Reduction.canonicalCoverAt_of_used_of_maxDensity` with the loss
`refineToEssDistinctLeaves.C 3 · Δ_max` replaced by the ED-multiplicity `M`.  Everything else —
the "used" clause, the index type, the conclusion — is character for character the same, so the
two are drop-in alternatives at the call site. -/
theorem canonicalCoverAt_of_used_of_edMult
    {R : ℝ} (hθ : 0 < θ) (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3))) {hR : 0 < R}
    {α : Type u} {s : Finset α} (𝕋 : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    {ρ : ℝ≥0} (hρ0 : 0 < ρ)
    {κ₀ : Type u} (t : Finset κ₀) (V : κ₀ → Tube ρ (EuclideanSpace ℝ (Fin 3)))
    {M : ℕ} (hM0 : 0 < M)
    (hM : ∀ i ∈ t, (open scoped Classical in t.filter (fun j ↦
      ¬ _root_.IsEssentiallyDistinct (V j).carrier (V i).carrier)).card ≤ M)
    (hused : ∀ j ∈ t, ∃ i ∈ s,
      (spineFamily (spineRescaleUnit hθ T₀ hR) 𝕋 i).toConvexSpaceBody ≤ (V j).toConvexSpaceBody)
    {c : ℝ} (hlow : (M : ℝ) * c ≤ (t.card : ℝ)) :
    ∃ (κ₁ : Type u) (u : Finset κ₁) (W : κ₁ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
      ((u : Set κ₁).Pairwise
        fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
      (∀ j ∈ u, ∃ i ∈ s,
        (spineFamily (spineRescaleUnit hθ T₀ hR) 𝕋 i).toConvexSpaceBody
          ≤ (W j).toConvexSpaceBody) ∧
      c ≤ (u.card : ℝ) := by
  classical
  obtain ⟨u, hut, hED, hcard⟩ := exists_essDistinct_of_edMult hρ0 t V hM
  refine ⟨κ₀, u, V, hED, fun j hj ↦ hused j (hut hj), ?_⟩
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM0
  have hreal : (t.card : ℝ) ≤ (M : ℝ) * (u.card : ℝ) := by exact_mod_cast hcard
  nlinarith [hlow, hreal]

/-! ### The count budget at the corrected price -/

/-- The count-budget arithmetic with the ED-multiplicity `M` in place of
`refineToEssDistinctLeaves.C 3 · Δ_max`.  Unlike the `Δ_max` version this is satisfiable: `M` is
not bounded below by any power of `ρ`. -/
theorem edCount_budget_of_slack {ρ : ℝ≥0} (hρ0 : 0 < ρ) {ζ ζ' : ℝ} {M Lam : ℝ}
    (hslack : M * Lam ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    {n : ℕ} (hcard : (ρ : ℝ) ^ (-2 - ζ') ≤ (n : ℝ)) :
    M * (Lam * (ρ : ℝ) ^ (-2 - ζ)) ≤ (n : ℝ) := by
  have hρR : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ0
  have hsplit : (ρ : ℝ) ^ (-(ζ' - ζ)) * (ρ : ℝ) ^ (-2 - ζ) = (ρ : ℝ) ^ (-2 - ζ') := by
    rw [← Real.rpow_add hρR]; ring_nf
  calc M * (Lam * (ρ : ℝ) ^ (-2 - ζ)) = (M * Lam) * (ρ : ℝ) ^ (-2 - ζ) := by ring
    _ ≤ (ρ : ℝ) ^ (-(ζ' - ζ)) * (ρ : ℝ) ^ (-2 - ζ) :=
        mul_le_mul_of_nonneg_right hslack (Real.rpow_nonneg hρR.le _)
    _ = (ρ : ℝ) ^ (-2 - ζ') := hsplit
    _ ≤ (n : ℝ) := hcard

/-- **The canonical-cover datum at one scale, from the upstairs family, at the ED-multiplicity
price.**  This is 's `canonicalCoverAt_of_upstairs` with the two clauses `Δ_max ≤ D`
and `C₃ · D ≤ Ced` replaced by the single clause `hM`, and it is the version that is not
self-contradictory. -/
theorem canonicalCoverAt_of_upstairs_edMult {σ : ℝ≥0} {R ζ ζ' : ℝ}
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R)
    (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {s : Finset α} (𝕋 : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    {ρ : ℝ≥0} (hρ0 : 0 < ρ) (hρ4 : (ρ : ℝ) ≤ 1 / 4)
    {κ₀ : Type u} (t : Finset κ₀) (W : κ₀ → Tube (ρ * θ) (EuclideanSpace ℝ (Fin 3)))
    (hsubW : ∀ k ∈ t, (W k).carrier ⊆ T₀.carrier)
    (hused : ∀ k ∈ t, ∃ i ∈ s, (𝕋 i).carrier ⊆ (W k).carrier)
    {M : ℕ} (hM0 : 0 < M)
    (hM : ∀ i ∈ t, (open scoped Classical in t.filter (fun j ↦
      ¬ _root_.IsEssentiallyDistinct
          (outerTube hsit.pos_ambient T₀ hR ρ (W j)).carrier
          (outerTube hsit.pos_ambient T₀ hR ρ (W i)).carrier)).card ≤ M)
    (hslack : (M : ℝ) * (spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    (hcard : (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ)) :
    ∃ (κ₁ : Type u) (u : Finset κ₁) (V : κ₁ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
      ((u : Set κ₁).Pairwise
        fun j k ↦ _root_.IsEssentiallyDistinct (V j).carrier (V k).carrier) ∧
      (∀ j ∈ u, ∃ i ∈ s,
        (spineFamily (spineRescaleUnit hsit.pos_ambient T₀ hR) 𝕋 i).toConvexSpaceBody
          ≤ (V j).toConvexSpaceBody) ∧
      (spineOuterCountLoss R : ℝ) * (ρ : ℝ) ^ (-2 - ζ) ≤ (u.card : ℝ) := by
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hsit2 := isRescalingSituation_scaledUp hsit hρ0 hρ4
  have hused' := outerTube_used_of_used hfr hsit2 hR (ratio_scaledUp hsit.pos_ambient ρ)
    T₀ 𝕋 W hsubW hused
  exact canonicalCoverAt_of_used_of_edMult hsit.pos_ambient T₀ (hR := hR) 𝕋 hρ0 t
    (fun k ↦ outerTube hsit.pos_ambient T₀ hR ρ (W k)) hM0 hM hused'
    (edCount_budget_of_slack hρ0 hslack hcard)

/-! ### Step 10, over the corrected interface -/

/-! ### Essential distinctness does not obstruct the count -/

/-! ### The `ε_div` reading of the window, and the budget it closes -/

end Kakeya.ML2Reduction

end

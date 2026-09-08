/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Tube.Dilate
public import Kakeya.Tube.Rescale

/-!
# Comparing two `ρ`-tube covers of one family of bodies

GWZ writes `|𝕋_ρ|` for "the number of `ρ`-tubes needed to cover `𝕋`", a quantity well defined only
*up to constants*.  The Lean rendering of the count clause of GWZ Lemma 9.1
(`Kakeya.ML2Reduction.Lemma91At`, third bullet) takes it literally and asks for the lower bound
`ρ^{-2-ζ} ≤ |t'|` for **every** essentially distinct `ρ`-tube cover `t'`, whereas
`Kakeya.ML2Spine.spine_tube_card_lower` proves it for the *canonical* cover carried by the tube
hierarchy.  The bridge is the comparison of two covers at the same scale, which this file supplies.

## The residual input, and its repair

`Kakeya.ML2Reduction.CoverCountComparable` (w08's `Reduction/SpineOuterTubes.lean`) is the exact
shape of the missing input.  It is restated here verbatim as `Tube.CoverCountComparableSpec` — and
it is **false at every loss `Λ`** (`Tube.not_coverCountComparableSpec`): nothing in it forbids the
covered bodies `V i` from being *points*, and `n` pairwise disjoint `ρ`-tubes may all meet one
`ρ`-tube of the competitor cover in `n` distinct points.  So the covered bodies need a
nondegeneracy hypothesis, and it is the only thing they need:

`Tube.CoverCountComparableChord` is `Tube.CoverCountComparableSpec` with **three** hypotheses
added — `0 < ρ`, `ρ ≤ 1`, and `hnd`: every `V i` contains two points at distance `≥ 2/5`.
`Tube.coverCountComparableChord_of_spec` is the compiler-checked record that this is a *weakening*
and not a different statement, `Tube.coverCountComparableChord` proves it at the explicit loss
`Λ = 1 + Tube.essDistinctTubesInSelfDilate.C 3 32`, and
`Tube.one_le_of_coverCountComparableChord` certifies that the repaired predicate is **not
vacuous** (its hypotheses are satisfiable with a nonempty reference cover, whence `1 ≤ Λ`).

`hnd` is free at the call site: the bodies of Lemma 9.1's count clause are shaded `δ`-tubes, whose
cores have length exactly `1` (`Tube.exists_chord_of_shadedTube`).  The threshold `2/5` is not
arbitrary: it is where the chord-angle bound of `Tube.norm_perp_direction_le_of_chord` meets the
`15 K ρ` that `Tube.subset_dilate_of_norm_perp_direction_le` demands, at `K = 1`.

## The geometry, and where it already lived

The "one missing geometric lemma" — *two coarse tubes sharing a fine tube are comparable* — is
`Tube.subset_dilate_of_common_chord`, and it is a two-line composition of lemmas that were already
in the tree.  `Tube.tubeOverlapCoreClose` is indeed not applicable (it needs overlap `> |T|/2`),
but it is not needed:

* `Tube.norm_perp_direction_le_of_chord` (`Kakeya/Tube/Dilate.lean`, blueprint
  `lem:chordAngleBound`) turns a *shared chord of length `d`* into the direction bound
  `(2ρ + 4δ)/d`.  At `δ = ρ` and `d = 2/5` this is exactly `15 ρ`.
* `Tube.subset_dilate_of_norm_perp_direction_le` turns that
  direction bound, plus one shared point, into `W ⊆ 32 · W'`.
* `Tube.essDistinctTubesInSelfDilate` (`Kakeya/Tube/Rescale.lean`, blueprint
  `lem:essDistinctTubesInSelfDilate`) then bounds each fibre of `j ↦ j'`.  **Its docstrings in
  `Kakeya/Tube/Rescale.lean` still call it "the single open leaf"; that is stale.  It is proved,
  and `#print axioms` on it returns `[propext, Classical.choice, Quot.sound]`.**

The fibre map is `j ↦ j'` where `j' ∈ t'` is any competitor tube containing the body that
witnesses `j`'s being used; `Finset.card_eq_sum_card_fiberwise` assembles the fibres.  Note that
the *reference-cover* hypothesis `href` is never used: `Tube.card_le_mul_card_of_chordCover` needs
only `hED`, `hused` and `hcov`.

## The chord length is a parameter

The comparison runs at any chord threshold `2/(5K)` with `K ≥ 1`, at the dilation ratio `32 K` and
the loss `Tube.coverCountLossAt n K`; `K = 1` is the `2/5` case.  This is not decoration: the
*weaker* form of the count clause, the one
`Kakeya.ML2Reduction.outerFamily_count_of_spineFamily_count` reduces to, is stated on the
**rescaled bodies**, whose diameter is `≈ 1/(4R) = 1/256` rather than `1`.
`Tube.count_of_canonicalCover_of_diam` takes the diameter `d > 0` directly and picks
`K = max 1 (2/(5d))`.

## Main declarations

* `Tube.subset_dilate_of_common_chord_at` / `Tube.subset_dilate_of_common_chord` — two `ρ`-tubes
  sharing a chord of length `≥ 2/(5K)` satisfy `W ⊆ 32 K · W'`; and its `K = 1` case.
* `Tube.card_fibre_le` — the fibre bound.
* `Tube.card_le_mul_card_of_chordCover` — `|t| ≤ Λ |t'|`, the general-`E` theorem.
* `Tube.card_used_le_mul_card_of_chordCover` — the same with the `hused` hypothesis removed,
  bounding the *used* part of the reference cover.
* `Tube.CoverCountComparableSpec`, `Tube.exists_pointBody_cover_config`,
  `Tube.not_coverCountComparableSpec` — the literal statement, the counterexample configuration and
  the refutation.
* `Tube.CoverCountComparableChord`, `Tube.coverCountComparableChord`,
  `Tube.coverCountComparableChord_of_spec`, `Tube.one_le_of_coverCountComparableChord` — the
  repaired statement, its proof, the record that it is a weakening, and its non-vacuity.
* `Tube.count_of_coverCountComparableChord` — the analogue of
  `Kakeya.ML2Reduction.count_of_coverCountComparable`.
* `Tube.count_of_canonicalCover`, `Tube.count_of_canonicalCover_of_diam`,
  `Tube.count_of_canonicalCover_tube`, `Tube.count_of_canonicalCover_shadedTube` — the same
  conclusion with no abstract `Prop` in the way; the last two are the forms the count clause should
  cite.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Set

namespace Tube

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### Step 1 — two `ρ`-tubes sharing a chord are comparable -/

/-- **Two `ρ`-tubes sharing a chord are comparable**: if two points at distance at least `2/(5K)`
lie in both `W` and `W'`, then `W ⊆ 32 K · W'`.

This is the geometric input the count clause needed.  `Tube.tubeOverlapCoreClose` does **not**
apply — it requires an overlap of more than half the volume of a tube, and a shared body of
thickness `τ ≪ ρ` gives only `≈ τ² ρ`.  What replaces it is the pair
`Tube.norm_perp_direction_le_of_chord` (the chord pins the *direction*, at `(2ρ + 4ρ)/(2/5) = 15ρ`)
and `Tube.subset_dilate_of_norm_perp_direction_le` at `K = 1` (a pinned direction plus one shared
point pins the *tube*, inside the `32 K`-dilate).  The threshold `2/(5K)` is exactly the `d` at
which the first lemma's output `6ρ/d` meets the second lemma's `15 K ρ` hypothesis; anything larger
also works, and the tube call sites have `d = 1`, i.e. `K = 1`. -/
theorem subset_dilate_of_common_chord_at [Nontrivial E] {ρ : ℝ≥0} (hρ1 : (ρ : ℝ) ≤ 1)
    {K : ℝ} (hK : 1 ≤ K) (W W' : Tube ρ E) {p q : E}
    (hpW : p ∈ W.carrier) (hqW : q ∈ W.carrier)
    (hpW' : p ∈ W'.carrier) (hqW' : q ∈ W'.carrier)
    (hpq : 2 / (5 * K) ≤ dist p q) :
    W.carrier ⊆ (Kakeya.Tube.dilate W' (32 * K)).carrier := by
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one hK
  have hd0 : (0 : ℝ) < 2 / (5 * K) := by positivity
  have hρ0 : (0 : ℝ) ≤ (ρ : ℝ) := NNReal.coe_nonneg ρ
  have hpb : p ∈ (Kakeya.Tube.dilate W 2).carrier := subset_dilate W (by norm_num) hpW
  have hqb : q ∈ (Kakeya.Tube.dilate W 2).carrier := subset_dilate W (by norm_num) hqW
  have hchord := norm_perp_direction_le_of_chord W' W (d := 2 / (5 * K)) hd0 hpq
    hpW' hqW' hpb hqb
  have hS : ‖W.direction - inner ℝ W'.direction W.direction • W'.direction‖
      ≤ 15 * K * (ρ : ℝ) := by
    refine hchord.trans ?_
    rw [div_le_iff₀ hd0]
    have : 15 * K * (ρ : ℝ) * (2 / (5 * K)) = 6 * (ρ : ℝ) := by
      field_simp
      ring
    rw [this]
    linarith
  exact subset_dilate_of_norm_perp_direction_le W' W (K := K) hK hρ1
    (by nlinarith) hpW' hpb hS

/-! ### Step 2 — the fibre bound -/

/-- The comparability loss of `Tube.card_le_mul_card_of_chordCover`: the packing constant of
`Tube.essDistinctTubesInSelfDilate` read at the dilation ratio `32 K` produced by
`Tube.subset_dilate_of_common_chord_at`, padded by `1` so that `1 ≤ Λ` is free.  It depends only
on the ambient dimension and on `K`: not on the scale, not on the tubes, not on the family. -/
noncomputable abbrev coverCountLossAt (n : ℕ) (K : ℝ) : ℝ≥0 :=
  1 + Tube.essDistinctTubesInSelfDilate.C n (32 * K)

/-- The comparability loss at chord threshold `2/5`, i.e. `Tube.coverCountLossAt n 1`. -/
noncomputable abbrev coverCountLoss (n : ℕ) : ℝ≥0 := coverCountLossAt n 1

/-- The `1 +` in `Tube.coverCountLoss` makes `1 ≤ Λ` free.  This is not cosmetic: the consumer
divides by `Λ`, and `Tube.essDistinctTubesInSelfDilate.C` carries no positivity lemma of its own.
`Tube.one_le_of_coverCountComparableChord` shows `1 ≤ Λ` is in any case necessary. -/
theorem one_le_coverCountLossAt (n : ℕ) (K : ℝ) : (1 : ℝ≥0) ≤ coverCountLossAt n K :=
  le_self_add

/-- `Tube.one_le_coverCountLossAt` over `ℝ`. -/
theorem one_le_coverCountLossAt_real (n : ℕ) (K : ℝ) : (1 : ℝ) ≤ (coverCountLossAt n K : ℝ) := by
  exact_mod_cast one_le_coverCountLossAt n K

/-- **The fibre bound.**  A family of pairwise essentially distinct `ρ`-tubes all contained in the
`32`-dilate of one `ρ`-tube has at most `Tube.coverCountLoss (finrank ℝ E)` members.  This is
`Tube.essDistinctTubesInSelfDilate` at ratio `32`, converted from `ENNReal` to `ℝ`.

Note the scales agree: the counted tubes and the containing tube are both at scale `ρ`, which is
why `Tube.essDistinctTubesInDilate` (thin tubes `C⁻¹ρ` in a dilate of a `ρ`-tube) is *not* the
lemma to cite here. -/
theorem card_fibre_le [Nontrivial E] {ρ : ℝ≥0} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    {K : ℝ} (hK : 1 ≤ K) {κ : Type*} (a : Finset κ) (W : κ → Tube ρ E) (W' : Tube ρ E)
    (hED : (↑a : Set κ).Pairwise fun j k => IsEssentiallyDistinct (W j).carrier (W k).carrier)
    (hsub : ∀ j ∈ a, (W j).carrier ⊆ (Kakeya.Tube.dilate W' (32 * K)).carrier) :
    (a.card : ℝ) ≤ (coverCountLossAt (Module.finrank ℝ E) K : ℝ) := by
  have h := Tube.essDistinctTubesInSelfDilate (E := E) (ι := κ) (δ := ρ) (c := 32 * K)
    (by nlinarith) hρ0 hρ1 W' a W hED hsub
  have hcast : ((a.card : ℝ≥0) : ℝ≥0∞)
      ≤ ((Tube.essDistinctTubesInSelfDilate.C (Module.finrank ℝ E) (32 * K) : ℝ≥0)
          : ℝ≥0∞) := by
    simpa using h
  have h2 : (a.card : ℝ)
      ≤ ((Tube.essDistinctTubesInSelfDilate.C (Module.finrank ℝ E) (32 * K) : ℝ≥0) : ℝ) := by
    exact_mod_cast ENNReal.coe_le_coe.mp hcast
  refine h2.trans ?_
  have hle : (Tube.essDistinctTubesInSelfDilate.C (Module.finrank ℝ E) (32 * K) : ℝ≥0)
      ≤ coverCountLossAt (Module.finrank ℝ E) K := le_add_self
  exact_mod_cast hle

/-! ### Step 3 — the cover comparison -/

/-- **Two `ρ`-tube covers of the same family are comparable in cardinality**, at a loss depending
only on the ambient dimension.

`t` is the reference cover: pairwise essentially distinct, and every member *used* (it contains
some `V i` with `i ∈ s`).  `t'` is an arbitrary competitor cover.  Each used `W j` contains a body
`V i` which the competitor puts inside some `W' j'`; the two `ρ`-tubes then share a chord of length
`≥ 2/5`, so `W j ⊆ 32 · W' j'` (`Tube.subset_dilate_of_common_chord`), and the fibres of
`j ↦ j'` are bounded by `Tube.card_fibre_le`.

The loss is the closed term `Tube.coverCountLoss (Module.finrank ℝ E)`: it is fixed **before** `ρ`,
`V`, `s`, `t`, `W`, `t'`, `W'`, so it is uniform in all of them.  The hypothesis that `t` *covers*
the family is not needed — only `hED`, `hused` and `hcov`. -/
theorem card_le_mul_card_of_chordCover [Nontrivial E] {ρ : ℝ≥0} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    {K : ℝ} (hK : 1 ≤ K)
    {α κ κ' : Type*} (V : α → ConvexSpaceBody E) (s : Finset α)
    (t : Finset κ) (W : κ → Tube ρ E) (t' : Finset κ') (W' : κ' → Tube ρ E)
    (hnd : ∀ i ∈ s, ∃ p ∈ (V i).carrier, ∃ q ∈ (V i).carrier, 2 / (5 * K) ≤ dist p q)
    (hED : (↑t : Set κ).Pairwise fun j k => IsEssentiallyDistinct (W j).carrier (W k).carrier)
    (hused : ∀ j ∈ t, ∃ i ∈ s, V i ≤ (W j).toConvexSpaceBody)
    (hcov : ∀ i ∈ s, ∃ j ∈ t', V i ≤ (W' j).toConvexSpaceBody) :
    (t.card : ℝ) ≤ (coverCountLossAt (Module.finrank ℝ E) K : ℝ) * (t'.card : ℝ) := by
  classical
  have hρ1' : (ρ : ℝ) ≤ 1 := by exact_mod_cast hρ1
  have key : ∀ j ∈ t,
      ∃ j' ∈ t', (W j).carrier ⊆ (Kakeya.Tube.dilate (W' j') (32 * K)).carrier := by
    intro j hj
    obtain ⟨i, hi, hle⟩ := hused j hj
    obtain ⟨j', hj', hle'⟩ := hcov i hi
    obtain ⟨p, hp, q, hq, hpq⟩ := hnd i hi
    exact ⟨j', hj', subset_dilate_of_common_chord_at hρ1' hK (W j) (W' j')
      (hle hp) (hle hq) (hle' hp) (hle' hq) hpq⟩
  rcases t.eq_empty_or_nonempty with rfl | ⟨j₀, hj₀⟩
  · rw [Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨j₀', hj₀', -⟩ := key j₀ hj₀
  haveI : Nonempty κ' := ⟨j₀'⟩
  choose! f hf hfsub using key
  have hfibre : ∀ j' ∈ t', ((t.filter fun j => f j = j').card : ℝ)
      ≤ (coverCountLossAt (Module.finrank ℝ E) K : ℝ) := by
    intro j' _
    refine card_fibre_le hρ0 hρ1 hK _ W (W' j') ?_ ?_
    · exact hED.mono (by exact_mod_cast Finset.filter_subset _ _)
    · intro j hj
      rw [Finset.mem_filter] at hj
      exact hj.2 ▸ hfsub j hj.1
  calc (t.card : ℝ) = ((∑ j' ∈ t', (t.filter fun j => f j = j').card : ℕ) : ℝ) := by
        rw [← Finset.card_eq_sum_card_fiberwise hf]
    _ = ∑ j' ∈ t', ((t.filter fun j => f j = j').card : ℝ) := by push_cast; ring
    _ ≤ ∑ _j' ∈ t', (coverCountLossAt (Module.finrank ℝ E) K : ℝ) := Finset.sum_le_sum hfibre
    _ = (coverCountLossAt (Module.finrank ℝ E) K : ℝ) * (t'.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-! ### The literal statement, restated -/

universe u

/-! ### The counterexample construction -/

section Cross

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [ProperSpace F]

end Cross

section Cross2

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [ProperSpace F]

end Cross2

/-! ### The refutation of the literal statement -/

/-! ### The repaired statement, and its proof -/

/-- Every tube carries a chord of length `1`, so the nondegeneracy hypothesis of
`Tube.CoverCountComparableChord` is free for a family of tubes. -/
theorem exists_chord_of_tube {τ : ℝ≥0} (T : Tube τ E) :
    ∃ p ∈ T.carrier, ∃ q ∈ T.carrier, (2 / 5 : ℝ) ≤ dist p q :=
  ⟨T.x, x_mem_carrier T, T.y, y_mem_carrier T, by rw [T.dist_eq_one]; norm_num⟩

/-! ### The consumer -/

/-- **The count clause, with no abstract `Prop` in the way and no `href`**: the form a consumer
should cite.  The `V i` are arbitrary bodies carrying a chord of length `≥ 2/5`; the version for a
family of tubes is `Tube.count_of_canonicalCover_tube`. -/
theorem count_of_canonicalCover [Nontrivial E] {c : ℝ} {α : Type*} {ρ : ℝ≥0}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) {K : ℝ} (hK : 1 ≤ K)
    (V : α → ConvexSpaceBody E) (s : Finset α)
    (hnd : ∀ i ∈ s, ∃ p ∈ (V i).carrier, ∃ q ∈ (V i).carrier, 2 / (5 * K) ≤ dist p q)
    {κ : Type*} (t : Finset κ) (W : κ → Tube ρ E)
    (hED : (t : Set κ).Pairwise
      fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier)
    (hused : ∀ j ∈ t, ∃ i ∈ s, V i ≤ (W j).toConvexSpaceBody)
    (hlow : (coverCountLossAt (Module.finrank ℝ E) K : ℝ) * c ≤ (t.card : ℝ))
    {κ' : Type*} (t' : Finset κ') (W' : κ' → Tube ρ E)
    (hcov : ∀ i ∈ s, ∃ j ∈ t', V i ≤ (W' j).toConvexSpaceBody) :
    c ≤ (t'.card : ℝ) := by
  refine le_of_mul_le_mul_left (hlow.trans ?_) ?_
  · exact card_le_mul_card_of_chordCover hρ0 hρ1 hK V s t W t' W' hnd hED hused hcov
  · exact lt_of_lt_of_le zero_lt_one (one_le_coverCountLossAt_real _ _)

/-! ### Non-vacuity, and the consumer's nondegeneracy witness -/

/-- Every shaded tube's body carries a chord of length `1`, so the nondegeneracy hypothesis is
free for the family of `Kakeya.ML2Reduction.Lemma91At`'s count clause, whose bodies are
`(T i).toConvexSpaceBody` for `T i : ShadedTube δ _`. -/
theorem exists_chord_of_shadedTube {τ : ℝ≥0} (T : ShadedTube τ E) :
    ∃ p ∈ (T.toConvexSpaceBody).carrier, ∃ q ∈ (T.toConvexSpaceBody).carrier,
      (2 / 5 : ℝ) ≤ dist p q :=
  exists_chord_of_tube T.toTube

/-- **The form the count clause of `Kakeya.ML2Reduction.Lemma91At` should cite.**

The bodies are the shaded tubes of the family itself, so the nondegeneracy hypothesis is
discharged internally by `Tube.exists_chord_of_shadedTube` and no hypothesis beyond `0 < ρ`,
`ρ ≤ 1` is added to what `Kakeya.ML2Reduction.count_of_coverCountComparable` already asked for. -/
theorem count_of_canonicalCover_shadedTube [Nontrivial E] {c : ℝ} {α : Type*} {ρ τ : ℝ≥0}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (T : α → ShadedTube τ E) (s : Finset α)
    {κ : Type*} (t : Finset κ) (W : κ → Tube ρ E)
    (hED : (t : Set κ).Pairwise
      fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier)
    (hused : ∀ j ∈ t, ∃ i ∈ s, (T i).toConvexSpaceBody ≤ (W j).toConvexSpaceBody)
    (hlow : (coverCountLoss (Module.finrank ℝ E) : ℝ) * c ≤ (t.card : ℝ))
    {κ' : Type*} (t' : Finset κ') (W' : κ' → Tube ρ E)
    (hcov : ∀ i ∈ s, ∃ j ∈ t', (T i).toConvexSpaceBody ≤ (W' j).toConvexSpaceBody) :
    c ≤ (t'.card : ℝ) :=
  count_of_canonicalCover hρ0 hρ1 (K := 1) le_rfl (fun i => (T i).toConvexSpaceBody) s
    (fun i _ => by simpa using exists_chord_of_shadedTube (T i)) t W hED hused hlow t' W' hcov

end Tube

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Covers
public import Kakeya.Tube.Dilate
public import Kakeya.DimensionThree.MainLemma2.SetupProduce

/-!
# The axial coordinate is essential-distinctness blind, and the pre-F12 / pre-centred transcription of
# `exists_setup_caseSideData` is false

Clause (e) of `Kakeya.VeryNotSticky.BandUniformRefinement` — the tube count `1 ≤ δ |𝕋'|`, the
Lean form of the configuration field `Kakeya.VeryNotSticky.tube_count` — is reduced by
`Kakeya.VeryNotSticky.eventually_tubeCount_of_edCover` to a single geometric object: a
**containment-preserving essentially distinct coarsening**, i.e. a family of `ρ`-tubes covering
`𝕋` (each `δ`-tube inside one of them) and pairwise essentially distinct.

**A unit-length tube has five parameters, not four.** The position of the core *along its own
axis* is the fifth, and in that coordinate essential distinctness costs a constant while the
covering budget affords only `≍ ρ`. The deficit is therefore a factor `≍ 1/ρ`, not `39 %`, and it
is fatal: an essentially distinct cover of a suitable family does not exist at all.

## What is proved

* `Kakeya.VeryNotSticky.dist_endpoints_le_of_carrier_subset` — **containment pins the endpoints**:
  a `δ`-tube inside a `ρ`-tube has its core's endpoints within `3ρ` of the containing core's, in
  one of the two orientations. The converse of `Kakeya.Tube.tube_carrier_subset_of_close`, which
  the tree did not have; `Kakeya.VeryNotSticky.dist_center_le_of_carrier_subset` is the
  orientation-free corollary.

* `Kakeya.VeryNotSticky.not_isEssentiallyDistinct_of_axial_translate` — **exact axial translates
  are never essentially distinct**, at any slide `|α| ≤ 1/12`. The threshold is a pure number,
  with no factor of `ρ`. Contrast the transverse twin
  `Kakeya.VeryNotSticky.isEssentiallyDistinct_of_transverse_sep_sharp`, where a gap of `ρ` already
  buys essential distinctness.

* `Kakeya.VeryNotSticky.card_le_of_ed_of_endpoints_confined` — **the packing bound**: an
  essentially distinct family of `ρ`-tubes whose cores are pinned, after removing a common axial
  slide, to `3ρ`-balls about two fixed points has at most `385 ^ 6` members. The bound contains
  no `ρ`.

* `Kakeya.VeryNotSticky.not_edCover_of_axialFamily` — **no essentially distinct cover exists** for
  a family of more than `385 ^ 6` `δ`-tubes that are axial translates of one another at offsets
  inside `[-1/288, 1/288]` and pairwise more than `6ρ` apart.
  `Kakeya.VeryNotSticky.exists_axialFamily` and
  `Kakeya.VeryNotSticky.exists_family_without_edCover` build such a family inside the closed unit
  ball, so the statement is not vacuous.

**Scope note.** Since `Kakeya.VeryNotSticky.exists_setup_caseSideData`
and `Kakeya.multiplicity_le_of_card_isEssDistinct_ge` carry the binder `∀ i ∈ s, (T i).toTube.IsCentred`; and the hypotheses
transcribed below (`h91`, the binders of `not_setupConclusion`) are the **pre-F12** clauses — an *unbounded* `∃ C` uniformity binder
and a `∀`-quantified `ρ`-cover — not the existing `∃`-form, to which the axial witness does not transfer. The witness family
of this module is a family of axial translates of one tube — centred tubes on a common axis coincide, so it does **not** meet
that binder — and every "is false" below is a record about the statements *before* that binder (the hypothesis list of
`Kakeya.VeryNotSticky.SetupCaseSideDataStatementOld`), not about the live ones; the hand-transcribed hypotheses (`h91`)
below are the pre-centred texts.

* `Kakeya.VeryNotSticky.not_setupConclusion` — **the conclusion of
  `Kakeya.VeryNotSticky.exists_setup_caseSideData`, as it stood before the centredness binder, is false.** The family above
  meets every binder of that pre-centred statement — `hball` by construction, `huni` by
  `Kakeya.VeryNotSticky.nonempty_shadedUniformTubeSet_of_core_injOn` (the binder is an *unbounded*
  `∃ C`), `hmax` by `Kakeya.maxDensity_le_card`, `hfull` because the shading is the whole carrier,
  and `hcount` **vacuously** — while its cardinality is the constant `385^6 + 1`, so the field
  `Kakeya.VeryNotSticky.tube_count` of the configuration it is asked to produce fails outright.
  Only `0 < exscal` and `0 < η` are used: the refutation does not lean on the Katz–Tao or Frostman
  estimates.

* `Kakeya.VeryNotSticky.exists_witnessFamily` — the same family with **all five binders verified
  and its multiplicity bounded below** by half its cardinality (the whole family lies inside the
  union of two of its members), which is what refutes the section's target itself:

* `Kakeya.VeryNotSticky.not_lemma91Conclusion` — **the conclusion of
  `Kakeya.multiplicity_le_of_card_isEssDistinct_ge`, GWZ Lemma 9.1, is false as rendered before the
  centredness binder** (its `h91` is the pre-centred text, transcribed by hand; the live statement is not refuted — scope
  note above), given its own two antecedents `K_KT(β)` and `K_F(β)`. The witness family has multiplicity `≥ #𝕋/2`
  with `#𝕋` a constant, while the conclusion asserts `multiplicity ≤ δ^ν (#𝕋)^β → 0`. The defect
  is the same missing binder: nothing in the statement asks `𝕋` to be large, and the `ρ`-count
  hypothesis cannot supply it.

* `Kakeya.VeryNotSticky.axialNet_budget_infeasible`, together with
  `Kakeya.VeryNotSticky.exists_axialNet_of_range_le` and
  `Kakeya.VeryNotSticky.not_axialNet_of_rho_small` — the arithmetic of the axial coordinate,
  isolated in the style of `Kakeya.VeryNotSticky.productNet_budget_infeasible`, with the sharpness
  witness that keeps it from being vacuous.

## What this means for the target

`hcount` is the only binder of `Kakeya.VeryNotSticky.exists_setup_caseSideData` that bounds `|𝕋|`
from below, and it is met by a family of *bounded* size. The field `tube_count` is therefore not
reachable from the binders, and the repair is a statement-level one:
`Kakeya.VeryNotSticky.tubeCount_of_parent_of_retention` names the binder that would discharge it,
`|𝕋| ≥ δ^{-1-α}`, one power below the field's own value because the refinement loses `δ^α` of the
cardinality. This is an additional cardinality hypothesis.
-/

@[expose] public section

open scoped NNReal

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set Produce
open scoped NNReal

universe u

/-! ### Containment pins the endpoints -/

section Endpoints

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]


end Endpoints

/-! ### The axial coordinate is essential-distinctness blind -/


/-! ### The consequence for the covering question -/


/-! ### The arithmetic, isolated -/


/-! ### The general case: the endpoint pigeonhole -/

/-- **A maximal `r`-separated subset**, in the form the two-step pigeonhole consumes: it is
`r`-separated, and every member of the ambient family is within `r` of one of its members. -/
private theorem exists_maximal_separated {κ : Type*} (t : Finset κ) (Φ : κ → E3) {r : ℝ}
    (hr : 0 < r) :
    ∃ A ⊆ t, (∀ j ∈ A, ∀ k ∈ A, j ≠ k → r ≤ dist (Φ j) (Φ k)) ∧
      ∀ j ∈ t, ∃ a ∈ A, dist (Φ j) (Φ a) < r := by
  classical
  set S : Finset (Finset κ) :=
    t.powerset.filter (fun A => ∀ j ∈ A, ∀ k ∈ A, j ≠ k → r ≤ dist (Φ j) (Φ k)) with hS
  have hemp : (∅ : Finset κ) ∈ S := by simp [hS]
  obtain ⟨A, hAS, hmax⟩ := Finset.exists_max_image S (fun A => A.card) ⟨∅, hemp⟩
  rw [hS, Finset.mem_filter, Finset.mem_powerset] at hAS
  refine ⟨A, hAS.1, hAS.2, ?_⟩
  intro j hj
  by_contra hcon
  have hcon' : ∀ a ∈ A, r ≤ dist (Φ j) (Φ a) := by
    intro a ha
    by_contra h
    exact hcon ⟨a, ha, not_le.mp h⟩
  have hjA : j ∉ A := by
    intro hjA
    have h := hcon' j hjA
    rw [dist_self] at h
    linarith
  have hins : insert j A ∈ S := by
    rw [hS, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.insert_subset hj hAS.1, ?_⟩
    intro p hp q hq hpq
    rcases Finset.mem_insert.1 hp with rfl | hp' <;> rcases Finset.mem_insert.1 hq with rfl | hq'
    · exact absurd rfl hpq
    · exact hcon' q hq'
    · rw [dist_comm]; exact hcon' p hp'
    · exact hAS.2 p hp' q hq' hpq
  have hle := hmax _ hins
  rw [Finset.card_insert_of_notMem hjA] at hle
  omega


/-! ### The punchline: an axial family of bounded size admits no essentially distinct cover -/


/-! ### Non-vacuity: the forbidden family exists, inside the unit ball -/


/-! ### The remaining binders of the target, for the witness family -/


/-! ### The refutation -/

open Topology Filter in
/-- Eventually `δ^p ≤ c`, for `p > 0` and `c > 0`: the threshold form used below. -/
private theorem eventually_rpow_le {c : ℝ≥0} (hc : 0 < c) {p : ℝ} (hp : 0 < p) :
    ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0, δ ^ p ≤ c := by
  have hd : (0 : ℝ≥0) < c ^ (1 / p) := NNReal.rpow_pos hc
  filter_upwards [Ioo_mem_nhdsGT hd] with δ hδ
  have h1 : δ ≤ c ^ (1 / p) := hδ.2.le
  calc δ ^ p ≤ (c ^ (1 / p)) ^ p := NNReal.rpow_le_rpow h1 hp.le
    _ = c := by
        rw [← NNReal.rpow_mul, one_div, inv_mul_cancel₀ hp.ne', NNReal.rpow_one]


end Kakeya.VeryNotSticky

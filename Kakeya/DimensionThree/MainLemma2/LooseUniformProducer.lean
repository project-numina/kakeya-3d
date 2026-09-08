/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.LooseUniform

/-!
# R18: what the exact→loose producer question is, and exactly what is compiled here

`MainLemma2/LooseUniform.lean` introduces the three loose
structures of the R18 route and says in its own module docstring that they have **no producer**. This file measures the gap between the exact and the loose bundle, and compiles one family on
which the loose bundle fails. Its results are conditional on the geometric hypotheses specified below.

## What is in scope at conjunct 6's call site

Conjunct 6 of `Kakeya.VeryNotSticky.SideDataObligations`
(`MainLemma2/SetupSideData.lean`) binds exactly `cfg : Kakeya.VeryNotSticky`,
`bd : Kakeya.VeryNotSticky.BallData cfg`, the six parameter equations, and the grid level `k`
with its two `Tube.gridScale` bounds.  The **only** uniformity datum `cfg` carries is the field
`Kakeya.VeryNotSticky.uniform`, namely
`Nonempty (ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)` — the
*exact* GWZ Definition 2.2 bundle on the *whole* family `cfg.s`.  So a producer of
`Kakeya.LooseUniform.LooseShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) 4 cfg.C₀`
must come from that exact bundle (possibly rebuilding the cover directly out of `cfg.s`
and `cfg.T`).

## Part 1 — the conditional producer: the gap is exactly TWO fields

`Kakeya.LooseUniform.Producer.looseShadedOfExact` builds the loose Definition-2.2 bundle from
the exact one, at the same `s`, `T`, `N` and `C`, given **exactly two** residual data:

* `hdir` — the loose `dir_close_tube_assign` bracket, and
* `hbo` — the loose `boundedOverlapDil` bracket.

Every other field is *derived*: `assign_mem`, `nested`, `tube_injOn`, `card_class_le`,
`le_card_class` and all six shade brackets transfer **verbatim** (they are literally the same
statements), and `le_dilate_tube_assign` follows from the exact `le_tube_assign` through
`Tube.subset_dilate`.  That is the honest measurement of the gap, compiler-established, and
 confirms it.

## Part 2 — `hdir` is not implied by exact containment at the coarse level

`Kakeya.LooseUniform.Producer.exists_le_tube_not_dir_close`: at the coarse grid level `k = 0`,
where `Tube.gridScale δ N 0 = 1`, a `δ`-tube through the origin **transverse** to the node's
axis is *exactly contained* in the node, while its direction is at distance `√2` from the
node's — vastly more than the `1/4` the loose bracket demands.  So exact containment carries
no direction information at all at the coarse level, at every `N`.

Note what `dir_close_tube_assign` is: GWZ's Definition 2.1 (GWZ) has **no**
direction clause at any scale, and `Kakeya.LooseUniform.LooseGridCoverSystem`
(`MainLemma2/LooseUniform.lean`) adds this one.  At `k = 0` it demands every member's direction
lie within `1/4` of its node's, at a level where GWZ's Definition 2.1 says nothing at all
(`T_1 = {B₁}`).

## Part 3 — one family on which the loose bundle fails

`Kakeya.LooseUniform.Producer.not_nonempty_looseUniformTubeSet_bush`: on the family of `m`
distinct unit `δ`-tubes through the origin in the direction `e₁` (axial offsets
`i / (4(m+1))`) **plus one** transverse member in the direction `e₂`, there is **no**
`Kakeya.LooseUniform.LooseUniformTubeSet` at **any** dilation factor `K ≥ 0` and any constant
`C` with `C³ < m + 1`, for **every** grid length `N`.  The mechanism:

* the loose direction bracket at `ρ₀ = 1` forces the transverse member into a node of its own,
  so its class is a **singleton**, whence `branchingN 0 ≤ C`;
* `boundedOverlapDil` against the coarse node containing the whole family caps the number of
  nodes in use by `C`;
* the two class brackets then force `m + 1 ≤ C · (C · 1) · C = C³`.

`Kakeya.LooseUniform.Producer.not_nonempty_looseShaded_ssfGridLen` states the same failure at
the Section-9 grid length `N = Tube.ssfGridLen δ` and the Section-9 dilation factor `K = 4`.
`Kakeya.LooseUniform.Producer.exact_datum_does_not_produce_loose` puts an exact bundle and the
failure on **one** family — but at grid length `0` on both sides (see below).

## What this does and does not establish [narrowed by ]

* It does **not** establish that a producer cannot exist. Three mathematical
  observations explain the distinction:

  1. *(§3.5(a), measured)* `exact_datum_does_not_produce_loose` is stated at grid length **`0`**
     on both sides — `ShadedTube.ShadedUniformTubeSet … (bV δ m) 0 1` and
     `LooseShadedUniformTubeSet … (bV δ m) 0 K C`.  The exact bundle
     `Kakeya.LooseUniform.Producer.exactShaded` is built on
     `Kakeya.LooseUniform.Producer.gridScale_zero_len : Tube.gridScale δ 0 k = 1`, the
     degenerate one-node grid.  `not_nonempty_looseShaded_ssfGridLen` *is* at the Section-9
     grid length, but it carries **no exact-datum companion**: no family is exhibited here that
     holds the exact Definition-2.2 datum at `N = Tube.ssfGridLen δ` and fails the loose one.
  2. *(§3.5(b), compiled probe)* On that same family the **other** residual bracket, `hbo`
     (`boundedOverlapDil`), is **true** at `K = 4`, `C = 1` — the level's index set is `{0}`, so
     every filter of it has card `≤ 1`.  The sole refuted bracket is therefore
     `Kakeya.LooseUniform.LooseGridCoverSystem.dir_close_tube_assign`, the clause Part 2 records
     as this development's own addition to GWZ's Definition 2.1.
  3. *(§3.5(c)/(e), measured)* Every step of the impossibility lives at `k = 0`, where
     `Tube.gridScale δ N 0 = 1`.  Conjunct 6's level is pinned near
     `gridScale ≈ cfg.rho2Star bd.C₀`, and `Kakeya.LooseUniform.angularCone_card_le_of_loose`
     reads the brackets only at that same `k`.  So the clause that kills this family is imposed
     at a level GWZ's Definition 2.1 leaves empty and **no consumer reads**.

* The loose type is **not** empty, at any `N`.  `Kakeya.LooseUniform.NonVacuity` inhabits it on
  a genuinely two-membered family (`exists_looseShadedUniformTubeSet_card_two`, at `N = 1`,
  `K = 4`, `C = 2`, with loaded brackets), and 's compiled probe inhabits it at
  **every** `N` at `K = 4`, `C = 1`.  Nothing here is an emptiness result.

* What survives as an argument against the loose datum *as existing* is a reading of the source,
  not a consequence of Part 3: GWZ's  only ever produces uniformity on a
  **refinement**, whereas the loose datum as existing is stated on the full `cfg.s`, which is
  fixed by the configuration and cannot be refined by a producer.   confirms
  that half and rests its §1 verdict on it.

* It does **not** establish that conjunct 6 is false, and nothing here may be cited to that
  effect.  It also does not establish that the bush-plus-transverse
  family satisfies the other 50 fields of `Kakeya.VeryNotSticky`; that question is untouched
  and remains uncompiled.  Finally,
  `Kakeya.VeryNotSticky.eventually_conjunct6_of_looseUniform` (`MainLemma2/LooseUniform.lean`)
  is **not** conjunct 6: it reads the fibres off a bound `LooseShadedUniformTubeSet`, whereas
  conjunct 6 names `cfg.activeTubeNodes cfg.splitHierarchy` / `cfg.tubeFibre cfg.splitHierarchy`
  — the `Classical.choice`-selected exact hierarchy.  Even a producer of the loose datum would
  not discharge conjunct 6 as existing.

## Duplicate short names, recorded not merged

`norm_e₂`, `inner_e₁_e₂` and `inner_e₂_e₁` below duplicate declarations of the same short names
in `Kakeya.DimensionThree.MainLemma1.Factoring`.  The full names differ (this file's live in
`Kakeya.LooseUniform.Producer`), and they are kept separate **deliberately**: importing
`MainLemma1/Factoring.lean` into `MainLemma2` would create a cross-area import for three
two-line orthonormality facts.  Recorded here so the duplication is not rediscovered as a defect.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Metric Set

namespace Kakeya.LooseUniform.Producer

open Kakeya.LooseUniform Kakeya.LooseUniform.NonVacuity
open scoped NNReal

/-! ## Part 1 — the conditional producer -/

section Conditional
variable {ι : Type*}


end Conditional

/-! ## Elementary geometry of bush tubes through the origin -/

/-- The second coordinate direction of `E3`. -/
noncomputable def e₂ : E3 := EuclideanSpace.single 1 1

lemma norm_e₂ : ‖e₂‖ = 1 := by simp [e₂]


/-! ## Part 2 — exact containment does not give the loose direction bracket -/


/-! ## Part 3 — the bush-plus-transverse family, and the impossibility -/

/-- The axial offsets of the `m` parallel members. -/
noncomputable def bOff (m : ℕ) (i : Fin (m + 1)) : ℝ := (i : ℝ) / (4 * (m + 1))

lemma bOff_nonneg (m : ℕ) (i : Fin (m + 1)) : 0 ≤ bOff m i := by
  unfold bOff; positivity

lemma bOff_abs_le (m : ℕ) (i : Fin (m + 1)) : |bOff m i| ≤ 1 / 4 := by
  have h0 : 0 ≤ bOff m i := bOff_nonneg m i
  rw [abs_of_nonneg h0]
  have him : (i : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp i.isLt
  have hpos : (0 : ℝ) < 4 * (m + 1) := by positivity
  rw [bOff, div_le_iff₀ hpos]
  nlinarith


/-- **The family**: `m` distinct unit `δ`-tubes through the origin in the direction `e₁`, at
axial offsets `i / (4(m+1))`, plus **one** transverse member in the direction `e₂`.  This is a
bush — exactly the configuration `Kakeya.LooseUniform.bush_obstruction` is about — with one
member turned sideways. -/
noncomputable def bT (δ : ℝ≥0) (m : ℕ) (i : Fin (m + 1)) : Tube δ E3 :=
  if (i : ℕ) < m then bushTube δ 0 e₁ norm_e₁ (bOff m i) else bushTube δ 0 e₂ norm_e₂ 0


/-! ### The same family carries the EXACT Definition-2.2 datum -/


lemma mem_segment_bT {δ : ℝ≥0} (m : ℕ) (i : Fin (m + 1)) :
    (0 : E3) ∈ segment ℝ (bT δ m i).x (bT δ m i).y := by
  rw [bT]
  split
  · exact mem_segment_bushTube δ 0 e₁ norm_e₁ (by
      have := bOff_abs_le m i; linarith)
  · exact mem_segment_bushTube δ 0 e₂ norm_e₂ (by norm_num)

/-- The shaded family: the same tubes, each shaded by the ball about their common point, which
has positive volume for `δ > 0`. -/
noncomputable def bV (δ : ℝ≥0) (m : ℕ) (i : Fin (m + 1)) : ShadedTube δ E3 where
  toTube := bT δ m i
  shade := Metric.closedBall 0 (δ : ℝ)
  measurableSet_shade := measurableSet_closedBall
  shade_subset := (bT δ m i).closedBall_subset_carrier_of_mem_segment (mem_segment_bT m i)

@[simp] lemma bV_toTube (δ : ℝ≥0) (m : ℕ) (i : Fin (m + 1)) :
    (bV δ m i).toTube = bT δ m i := rfl

@[simp] lemma bV_shade (δ : ℝ≥0) (m : ℕ) (i : Fin (m + 1)) :
    (bV δ m i).shade = Metric.closedBall 0 (δ : ℝ) := rfl


end Kakeya.LooseUniform.Producer

end

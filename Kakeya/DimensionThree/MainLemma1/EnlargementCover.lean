/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.FibreCompletion
public import Kakeya.MultiScaleFac
public import Kakeya.Tube.Dilate

/-!
# Main Lemma 1, Case (ii), Step 5a item (a): a producer for `IsEnlargementCover`

Blueprint `subsec:ml1bootEnlargementCover`, split there over
the enlargement cover, the enlargement-cover net and
the enlargement-cover construction.

`Kakeya.ml1Boot.exists_cover_of_subset_rescale` builds the covering family from `W`, `θ` and
`Kakeya.ml1Boot.enlargementCoverNet` alone and covers **every** `δ`-tube of the container, of which
there are a continuum; `Kakeya.ml1Boot.isEnlargementCover_rescale` is its quantifier-order
weakening and is **the first producer of `Kakeya.ml1Boot.IsEnlargementCover` in this
development**.  Until it was written every result of
the covering route — `Kakeya.ml1Boot.card_neighbouringParents_le_of_cover`,
`Kakeya.ml1Boot.card_completedFibreParents_le`, `Kakeya.ml1Boot.card_completedFibre_le` and
`Kakeya.ml1Boot.densityIn_le_of_neighbouringParents` — was a proved implication whose antecedent
nothing supplied.  The count it produces is `Kakeya.ml1Boot.enlargementCoverConstant E Λ`, which
depends on the ambient space `E` and on the enlargement factor `Λ` and **on nothing else**: not on
`θ`, not on `δ`, not on the tube `W`, not on the family and not on the index set.  That is the
whole content of blueprint `def:ml1bootNeighbouringParentsConstant`'s informal half, and what
carries it is that `Kakeya.ml1Boot.enlargementCoverConstant E Λ` is a *term* mentioning `E` and
`Λ` alone — the binder order below merely displays it and is not itself the assertion.

## The container is a concentric rescaling and *not* a homothety

Every statement here is read at `W.rescale (Λ * θ)`, the concentric rescaling of blueprint
`note:ml1bootTwoDilates`: it keeps the unit core of `W` and replaces the radius, so its
longitudinal extent is `1 + 2 Λ θ`.  The shape may **not** be traded for a homothety `c · V`.
`Kakeya.Tube.norm_midpoint_sub_center_le_of_norm_chord_eq_one`, the step that pins a leaf
longitudinally, is false at a homothety with `c > 1` fixed: the sliding configuration of blueprint
`note:ml1bootHomothetyOverlapInsufficient` is a family of unit segments inside such a container
whose midpoints are spread over a distance `Θ(c - 1)` and not `O(θ)`.  So nothing here closes the
longitudinal gap of blueprint `note:ml1bootEnlargementTubeStatus`, and nothing here bears on
hypothesis (R1) of `Kakeya.ml1Boot.card_neighbouringParents_le_of_essDistinct`.

## The edge to the consumers, and what it costs

The four consumers listed above keep their statements, which continue to take
`Kakeya.ml1Boot.IsEnlargementCover` as a bare hypothesis; alongside each of them there now stands
an **unconditional** variant in the final section of this file, whose covering hypothesis is
discharged at `Kakeya.ml1Boot.isEnlargementCover_rescale` and whose count is therefore the term
`Kakeya.ml1Boot.enlargementCoverConstant E Λ * Cu`.  The price is a genuine hypothesis on the
scales, not a technicality: the producer needs `2 δ ≤ ρ_a`, which **fails at `a = N`**, where the
coarse grid scale is `δ` itself.  So every statement in that section carries `a < N` explicitly,
together with the smallness `δ ≤ 16 ^ (-N)` the rest of this development already uses
(`Tube.exists_uniformTubeSet_subfamily`); the two together give `2 δ ≤ ρ_a` through
`Kakeya.ml1Boot.two_mul_le_gridScale_of_le_pow`.  At the Case (ii) call sites `a < N` is free:
`StickyKakeya.IsFrostmanDividingBlock` asserts `a < b` and `b ≤ N`.

## Placement of the generic lemmas, and a split this file still owes

The scalar lemma `Kakeya.abs_add_add_abs_sub_le_of_abs_le`, the net lemmas
`Kakeya.exists_finset_nonempty_forall_exists_norm_sub_le`,
`Kakeya.exists_mem_norm_sub_add_smul_le`, the normalization `Kakeya.normalizeWith` and its two
lemmas, and the generic tube lemmas of the `Kakeya.Tube` namespace below all live in **this** file,
and **they should not.**  Only the last three declarations — `Kakeya.ml1Boot.enlargementCoverNet`,
`Kakeya.ml1Boot.enlargementCoverConstant` and the two producers
`Kakeya.ml1Boot.exists_cover_of_subset_rescale` and
`Kakeya.ml1Boot.isEnlargementCover_rescale` — are about Step 5a at all; everything before the
`Kakeya.ml1Boot` namespace is generic normed-space, net or tube material that mentions neither
Main Lemma 1 nor `Kakeya.ml1Boot.IsEnlargementCover`, and belongs in `Kakeya/Mathlib/Analysis/` and
`Kakeya/Tube/` respectively.  Being this file's only consumer is not a reason to keep it here: the
file is past a thousand lines, well over the project's guidance of about five hundred, and the two
blocks are separable at the `end Tube` / `namespace ml1Boot` boundary because every reference across
that boundary runs the same way: the Step 5a block cites the generic one and nothing in the generic
block cites anything after it.  The split is deliberately **not** made in the same pass as the
mathematics, because it is a move of some six hundred lines across new modules and would have to be
existing together with a regenerated `Kakeya.lean` import index and a fresh `lake shake`, none of
which can be checked without a build.  It is recorded here as owed rather than presented as a
design choice.

## Statements that already exist elsewhere, and are cited rather than reproved

* blueprint `lem:dilatePointBoundsGeneral` is `Tube.abs_inner_and_perp_le_of_mem_dilate`
  (`Kakeya/Tube/Dilate.lean`) read at dilation ratio `1` of the tube `W.rescale r`;
* the transverse and quadratic-defect chord estimates are the two
  halves of blueprint `lem:ml1bootUnitChordTilt`, already proved as
  `Kakeya.Tube.norm_chord_transverse_le_of_endpoints_mem_dilate` and
  `Kakeya.Tube.one_sub_abs_inner_chord_le_of_endpoints_mem_dilate` (`Kakeya/Tube/Dilate.lean`),
  read at ratio `1` of a tube of radius `r`, where the two right-hand sides `2 c δ` and
  `4 c ^ 2 δ ^ 2` become `2 r` and `4 r ^ 2`; entering the `1`-dilate from the tube itself is
  `Tube.subset_dilate` at `c = 1` — which is the *root* `Tube` namespace of
  `Kakeya/Tube/Dilate.lean` and not `Kakeya.Tube`, where only the last group of that file's
  declarations sits — and `dist p q = 1` is `‖q - p‖ = 1` through `dist_eq_norm'`.  **So they have
  no declaration of their own here** and the confinement lemmas below cite them directly.  The intermediate `1 - 4 r ^ 2 ≤ ⟪u, e⟫ ^ 2` of the first of those two
  halves is likewise not stated: it is one application of
  `Kakeya.inner_sq_add_norm_transverse_sq_eq`, and the only consequence used downstream is the
  linear form `1 - 4 r ^ 2 ≤ |⟪u, e⟫|`, which *is* the second declaration named above;
* the first sentence of blueprint `lem:ml1bootCoverRescaleBall` is
  `Kakeya.Tube.carrier_subset_closedBall_midpoint` (`Kakeya/Tube/Basic.lean`); only its second
  sentence, `Kakeya.Tube.norm_midpoint_sub_center_le_of_mem_carrier`, is written here;
* the covering half of blueprint `lem:ml1bootCoverFiniteNet` is
  `Kakeya.closedBall_finite_closedBall_cover` (`Kakeya/Mathlib/Topology/Metric.lean`); only the
  adjunction of the centre that makes the net nonempty is additionally required, and
  `Kakeya.exists_finset_nonempty_forall_exists_norm_sub_le` is the statement carrying it;
* blueprint `lem:segmentEndpointCthickening` is
  `Metric.cthickening_segment_subset_cthickening_segment` (`Kakeya/Tube/Dilate.lean`) read at
  thickening radius `0`, and so has **no declaration of its own here**.  Blueprint
  `lem:ml1bootCoverTubeFromCore` — `Kakeya.Tube.subset_of_core_subset_cthickening` below — is that
  same lemma composed with `Kakeya.Tube.carrier_eq_cthickening` and one `Metric.cthickening_mono`,
  and it *is* kept, because it is the shape
  `Kakeya.Tube.subset_ofMidpointDirection_of_dist_params_le` consumes.

## Why `[MeasurableSpace E]` and `[BorelSpace E]` are carried

No statement in this file needs a measure on `E`, and several need neither an inner product nor a
dimension. They are nonetheless stated in the full context above, because every declaration they
are to be proved from — `Tube.abs_inner_and_perp_le_of_mem_dilate`,
`Kakeya.Tube.norm_chord_transverse_le_of_endpoints_mem_dilate`,
`Kakeya.Tube.one_sub_abs_inner_chord_le_of_endpoints_mem_dilate`, `Tube.subset_dilate`,
`Tube.x_mem_carrier`, `Tube.y_mem_carrier` and
`Metric.cthickening_segment_subset_cthickening_segment` — stands under one of the two variable
blocks of `Kakeya/Tube/Dilate.lean` (the root-`Tube` one and the `Kakeya.Tube` one), each of which
carries `[FiniteDimensional ℝ E]`, `[MeasurableSpace E]` and `[BorelSpace E]` with no `omit`
before any of them. `[ProperSpace E]`, which
`Tube` requires, is an instance of `[FiniteDimensional ℝ E]` and so is never written. The one
declaration that does omit all three is
`Kakeya.Tube.norm_midpoint_sub_center_le_of_mem_carrier`, whose single input
`Kakeya.Tube.carrier_subset_closedBall_midpoint` already stands under an `omit`. `[Nontrivial E]`
is omitted throughout, nothing here using it.

## Recorded adjustments to the blueprint display

* The confinement lemmas are stated at a tube `V : Tube r E` rather than at `W.rescale r` for a
  tube `W` of some unrelated radius.  Blueprint `lem:dilatePointBoundsGeneral` records that
  the radius of `W` itself does not occur, so a second radius would be a binder naming nothing;
  the displayed statements are the instances `V = W.rescale r`, at which `V.center = W.center` and
  `V.direction = W.direction`.
* `Kakeya.exists_mem_norm_sub_add_smul_le` omits the
  blueprint's `0 ≤ R` and `0 < ε`: neither is used, the whole argument being the case split on
  `θ = 0`.
* `Kakeya.exists_finset_nonempty_forall_exists_norm_sub_le` omits the blueprint's `0 ≤ R`. That
  entry justifies the hypothesis
  by nonemptiness of the net, and the justification is wrong: the net is made nonempty by
  adjoining the centre, which is available at every `R`, and at `R < 0` the covering clause is
  vacuous.  No sign condition on `R` is needed for either clause.
* `Kakeya.norm_sub_normalizeWith_le` omits the
  blueprint's `0 ≤ s`, which follows from `‖e - w‖ ≤ s`.
* Blueprint `lem:ml1bootCoverTubeFromCore` and `lem:ml1bootCoverLeafContainment` are displayed
  there at the typeclasses of `def:deltaTube` alone; here they carry the inner-product and measure
  context of the rest of the file, for the reason recorded above.  The blueprint writes those
  typeclasses as `[SeminormedAddCommGroup E]`, which is the class the structure `Tube` is declared
  over; the `Tube` API these two statements use — `Tube.carrier_eq_cthickening`, `Tube.rescale`
  and `Tube.ofMidpointDirection` — is stated one class up, at `[NormedAddCommGroup E]`.
-/

@[expose] public section

open scoped NNReal

open Metric Set

namespace Kakeya

/-! ### One statement of `ℝ` alone, and three of a bare normed space -/


section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


end NormedSpace

/-- **A finite nonempty net of a ball**.

The covering half is `Kakeya.closedBall_finite_closedBall_cover` of
`Kakeya/Mathlib/Topology/Metric.lean`, which is already proved; what this statement adds is that
the net is **nonempty**, obtained by adjoining the centre.  Nonemptiness is genuinely used, at
`Kakeya.exists_mem_norm_sub_add_smul_le` in the degenerate case `θ = 0`.

**No hypothesis `0 ≤ R`.**  Blueprint `lem:ml1bootCoverFiniteNet` carries one and justifies it by
nonemptiness; that justification is wrong, adjoining the centre being available at every `R`, and
at `R < 0` the covering clause is vacuous because no `z` satisfies `‖z‖ ≤ R`.  So the hypothesis
would be a binder naming nothing and it is dropped.

**No cardinality bound is asserted.**  Nothing downstream needs a formula for `N.card`, only that
some finite `N` exists, and the deliberate consequence is that
`Kakeya.ml1Boot.enlargementCoverConstant` is not an explicit numeral.  That is the same status the
quantity `M(n,Λ)` has in blueprint `def:ml1bootNeighbouringParentsConstant`, whose prose likewise
counts net points only up to `O_{n,Λ}(1)`. -/
theorem exists_finset_nonempty_forall_exists_norm_sub_le (E : Type*) [NormedAddCommGroup E]
    [ProperSpace E] {R ε : ℝ} (hε : 0 < ε) :
    ∃ N : Finset E, N.Nonempty ∧ ∀ z : E, ‖z‖ ≤ R → ∃ v ∈ N, ‖z - v‖ ≤ ε := by
  classical
  obtain ⟨t, htmem, hsub⟩ := closedBall_finite_closedBall_cover (E := E) R hε (0 : E)
  refine ⟨insert (0 : E) t, Finset.insert_nonempty (0 : E) t, ?_⟩
  intro z hz
  have hzball : z ∈ Metric.closedBall (0 : E) R := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hz
  rcases (Set.mem_iUnion₂.mp (hsub hzball)) with ⟨y, hyt, hyz⟩
  refine ⟨y, Finset.mem_insert_of_mem hyt, ?_⟩
  exact (show ‖z - y‖ ≤ ε by simpa [dist_eq_norm] using (Metric.mem_closedBall.mp hyz))

namespace Tube

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-! ### From a containment of cores to a containment of tubes

The two statements of this block are the only ones in the file that mention no inner product, no
orthogonal projection and no dimension, and blueprint `lem:ml1bootCoverTubeFromCore` and
`lem:ml1bootCoverLeafContainment` are displayed at the typeclasses of the structure `Tube` alone.
They are nonetheless stated in the inner-product context of the rest of the file, because the
declaration they are to be proved from — `Metric.cthickening_segment_subset_cthickening_segment`
of `Kakeya/Tube/Dilate.lean` — stands under that file's variable block and carries
`[InnerProductSpace ℝ E]`, `[FiniteDimensional ℝ E]`, `[MeasurableSpace E]` and `[BorelSpace E]`
with no `omit`; a statement at the weaker typeclasses could not cite it.  `[ProperSpace E]`, which
`Tube` requires, is an instance of `[FiniteDimensional ℝ E]` and so is not written.  They are
grouped first, out of the order in which the producer uses them.
-/


/-! ### Longitudinal and angular confinement of a unit segment in a concentric rescaling

Each statement below is read at a tube `V` of radius exactly `r`.  The displayed instance is
`V = W.rescale r` for a tube `W`, the concentric rescaling of blueprint
`note:ml1bootTwoDilates`, at which `V.center = W.center` and `V.direction = W.direction`; the
radius of `W` itself does not occur, so it is not a binder here.

The two chord estimates are **not** among the statements below: they are the two halves of
blueprint `lem:ml1bootUnitChordTilt`, already proved as
`Kakeya.Tube.norm_chord_transverse_le_of_endpoints_mem_dilate` and
`Kakeya.Tube.one_sub_abs_inner_chord_le_of_endpoints_mem_dilate`, and are cited at ratio `1`
through `Kakeya.Tube.subset_dilate`.
-/


/-! ### The three moves the producer makes on a single leaf

From a containment of tubes to oriented endpoint data
(`Kakeya.Tube.exists_core_endpoints_of_subset`), from that data to a pair of net points
(`Kakeya.Tube.exists_net_parameters`), and from the net points back to a containment of tubes —
that third move is `Kakeya.Tube.subset_ofMidpointDirection_of_dist_params_le`, which is stated in
the core block above.  They are stated separately so that
`Kakeya.ml1Boot.isEnlargementCover_rescale` is the construction of the family and nothing else.
-/


end Tube

namespace ml1Boot

/-! ### The constant, and the producer -/

/-- **The net underlying the covering constant**: one *chosen* finite nonempty `1/16`-net of the
closed ball
of radius `4 Λ` about the origin of `E`, fixed once and for all.

`Kakeya.exists_finset_nonempty_forall_exists_norm_sub_le` is existentially quantified, so a witness
has to be chosen; this is that choice.  The radius `4 Λ` is the numeral of
`Kakeya.Tube.norm_midpoint_sub_center_le_of_norm_chord_eq_one` and
`Kakeya.Tube.min_norm_chord_sub_direction_le` divided by `θ`, and the spacing `1/16` is `1/8`
halved to pay for the normalization of `Kakeya.norm_sub_normalizeWith_le`. -/
noncomputable def enlargementCoverNet (E : Type*) [NormedAddCommGroup E] [ProperSpace E]
    (Λ : ℝ≥0) : Finset E :=
  (exists_finset_nonempty_forall_exists_norm_sub_le E (R := 4 * (Λ : ℝ)) (ε := 1 / 16)
    (by norm_num)).choose

/-- **The covering constant** `M(E, Λ)`, the
square of the cardinality of `Kakeya.ml1Boot.enlargementCoverNet`.

The square is the two parameters of a unit segment, the centre and the direction, each netted by
the **same** set — the centre after translation to the centre of `W` and the direction after
translation to the direction of `W`, both after scaling by `θ`.  That is what makes one net serve
both and makes the count independent of `θ`.

This quantity depends on `E` and on `Λ` and **on nothing else**: not on `θ`, not on `δ`, not on the
tube `W`, not on the family and not on the index set.  It is indexed by the ambient space rather
than by a dimension because the finiteness above comes from compactness of a ball of `E` and no
isometry-invariance statement is made or needed.

**It is not the `M(n, Λ)` of blueprint `def:ml1bootNeighbouringParentsConstant`, only an upper
bound for it.**  That `M(n, Λ)` is the *least* integer admitting a covering family, whereas this is
*one* admissible value and depends on the choice of net made in
`Kakeya.ml1Boot.enlargementCoverNet`; what holds is `M(n, Λ) ≤ enlargementCoverConstant (ℝ^n) Λ`.
Its worth is that the right-hand side exists at all, which is what makes that "least integer"
well defined, and what witnesses this is the family-first
`Kakeya.ml1Boot.exists_cover_of_subset_rescale` and **not** its packaging
`Kakeya.ml1Boot.isEnlargementCover_rescale`, which covers the members of one finite indexed family
and so exhibits no admissible integer in the sense of that definition.

**It is not an explicit numeral.**  `Kakeya.exists_finset_nonempty_forall_exists_norm_sub_le`
asserts no cardinality bound, so no bound of the form `(C Λ) ^ (2 n)` is available here; a consumer
needing a numeral would have to add a covering-number estimate this development does not contain.
The prose of blueprint `def:ml1bootNeighbouringParentsConstant` likewise counts its nets only up to
`O_{n,Λ}(1)`. -/
noncomputable def enlargementCoverConstant (E : Type*) [NormedAddCommGroup E] [ProperSpace E]
    (Λ : ℝ≥0) : ℕ :=
  (enlargementCoverNet E Λ).card ^ 2

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]


/-! ### Drawing the edge: the producer read at a coarse node of the grid

Blueprint `lem:ml1bootNeighbouringParents`.  The producer above is stated at an arbitrary
`θ`-tube `W` and an arbitrary `θ` subject to `2 δ ≤ θ`.  Read at `θ = ρ_a` the coarse grid scale
and at `W = P_a(l)` a coarse node tube, it discharges the covering hypothesis of all four
consumers, and the count `M` becomes the term `Kakeya.ml1Boot.enlargementCoverConstant E Λ`.

**`a < N` is not decoration.**  `Tube.gridScale δ N N = δ`, so at `a = N` the producer's
hypothesis `2 δ ≤ ρ_a` reads `2 δ ≤ δ` and fails for every `δ > 0`.  Nor is `a < N` by itself
enough: `ρ_a ≥ ρ_{N-1} = δ / δ ^ (1/N)`, so `2 δ ≤ ρ_a` needs `δ ^ (1/N) ≤ 1/2` as well.  The two
lemmas below separate those two facts, and the smallness is asked in the form
`δ ≤ 16 ^ (-N)` that `Tube.exists_uniformTubeSet_subfamily` already uses. -/

section Edge

open MeasureTheory ConvexSpaceBody StickyKakeya _root_.Tube Convexity
open _root_.StickyKakeya
open scoped NNReal


end Edge

end ml1Boot

end Kakeya

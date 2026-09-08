/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Rescaling.Pigeonhole

/-!
# Main Lemma 1, Case (ii): The Frostman constant of the fibre over a `b`-tube

Split out of `Kakeya/DimensionThree/MainLemma1/Rescaling.lean`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya

namespace ml1Boot

/-! ### The Frostman constant of the fibre over a `b`-tube -/

/-- **The constant `C_{lem:ml1bootPlankInTubeRepaired}`**: the volume-comparison constant of the
*repaired* plank-in-tube
lemma `Kakeya.ml1Boot.exists_plank_tube_of_thickness_le_one`.

For a plank `W` whose thicknesses are only comparable to `1, b, a` with constant `C_𝕎`, and the
`2`-dilate of the tube of scale `C_𝕎 b` attached to it, the ratio `|2 · T_b| / (b/a · |W|)` can
be as large as `320 C_𝕎 ^ 6 / c₃`, where `c₃ = Metric.lt_volume_convexHull.c 3` and
`Metric.volume_comparison.C 3 = 4 ^ 3 / c₃`; the reverse ratio needs `2 C_𝕎 / c₃`.  Both are
dominated by the value below, which is a deliberately generous explicit choice:
`320 C_𝕎 ^ 6 / c₃ = 5 C_𝕎 ^ 6 * Metric.volume_comparison.C 3
≤ 256 C_𝕎 ^ 6 * Metric.volume_comparison.C 3` (`Kakeya.ml1Boot.plankInTube_constant_bounds`).

The value is kept as an expression in `plankPigeonhole.C` and `Metric.volume_comparison.C 3`
and never collapsed to a numeral, so that a missing power of `C_𝕎` shows up here rather than
at a use site.  It depends only on the ambient dimension `3` and on `plankPigeonhole.C`; in
particular not on `δ̃`, `a`, `b`, `ρ`, `γ`, `j`, or the family. -/
noncomputable abbrev plankInTube.C : ℝ≥0 :=
  256 * plankPigeonhole.C ^ 6 * Metric.volume_comparison.C 3

/-- **The constant `C_{lem:ml1bootDensityTransfer}`**: the constant comparing a plank of dimensions
`a × b × 1` with the `2`-dilate of the `b`-tube that contains it.

Both the containment and the volume comparison it refers to are statements about
`Kakeya.Tube.dilate T_b 2` and not about `T_b`: that is what
`Kakeya.ml1Boot.exists_plank_tube_of_thickness_le_one` supplies, containment of a plank in a
tube of *any* scale `O(b)` being false.  The value
is therefore taken to be `Kakeya.ml1Boot.plankInTube.C` itself, which is exactly the constant
that lemma produces for the dilate and which already contains the factor `2 ^ 3` of
`Kakeya.Tube.tubeDilateVolume`.  The alternative value
`plankPigeonhole.C ^ 3 * Metric.volume_comparison.C 3 ^ 2` was too small by many orders of
magnitude; see blueprint `note:ml1bootDensityTransferConstantTooSmall`.

It depends only on the ambient dimension `3` and on `Kakeya.ml1Boot.plankPigeonhole.C`; in
particular not on `δ̃`, on `a`, on `b`, on `ρ`, on `γ`, on `j`, or on the family. -/
noncomputable abbrev densityTransfer.C : ℝ≥0 := plankInTube.C

/-- **The constant `C_{lem:ml1bootPlankTubeInParentDilate}`**: the dilation factor `32 C_𝕎` by which
a parent
`ρ`-tube has to be enlarged before it contains the tube attached to a plank inside it.

The value has been raised twice, and the reasons are worth keeping.  The original `3 C_𝕎` was
unjustified even for the undilated containment `W ⊆ Tb`: since
`Metric.ethickness ℝ W.carrier 0 ≥ 2⁻¹` gives only `diam W ≥ 2⁻¹`, an arbitrary tube `Tb` of
scale `C_𝕎 b` containing `W` is pinned to the parent axis only up to a chord angle, and the
transverse protrusion is bounded only by `5 ρ + 6 C_𝕎 ρ ≤ 11 C_𝕎 ρ`; blueprint
`note:auditPlankTubeInParentDilate` exhibits admissible data on which the `3 C_𝕎`-dilate is
genuinely left, so that form was false not a consequence of the hypotheses.  That recomputation then had to
be redone against the hypothesis the development can actually supply:
`Kakeya.ml1Boot.exists_plankTube_family` delivers only the *dilated* containment
`W ≤ Tube.dilate Tb 2`, the undilated one being unsatisfiable for these planks, which roughly
doubles every transverse quantity and gives
`ρ + 21 C_𝕎 ρ ≤ 22 C_𝕎 ρ`.  Longitudinally `Tb`'s core midpoint is offset by `O(1)`, not
`O(ρ)`, so `Tb` reaches `|⟪x, e⟫| ≤ 2 + ρ + 3 C_𝕎 ρ`, dominated by `c'/2 = 16 C_𝕎`; at
`c' = 1` the containment fails, so neither direction is free.  Both enlargements are free
downstream: every consumer uses nothing about `c'` beyond `1 ≤ ·`.

It depends only on the ambient dimension `3` and on `Kakeya.ml1Boot.plankPigeonhole.C`; in
particular not on `δ̃`, `a`, `b`, `ρ`, `γ`, `j`, or the family.  As elsewhere the value is
kept as an expression in `C_𝕎` and never collapsed to a closed numeral. -/
noncomputable abbrev plankTubeInParent.C : ℝ≥0 := 32 * plankPigeonhole.C

section DensityTransfer

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The anchor placement of a block**.

Write `C_T = Kakeya.ml1Boot.densityTransfer.C`.  For a family `𝕍 = (T̃_k)_{k ∈ s'}` of
`δ̃`-tubes, a convex body `K` — the **anchor** — and widths `ã, b̃ > 0`, a finite index set `t`
is an *anchor placement* for `(𝕍, K, ã, b̃)` if, with `W = conv (⋃_{k ∈ t} T̃_k)` the plank of
the block `t`, it satisfies `t ⊆ s'`, `t` is nonempty, `W ≤ K`, and `|K| ≤ C_T (b̃/ã) |W|`.

*This is a bundle and not a new hypothesis.*  The four fields are, verbatim, the standing
conditions on `t` and the second and third displays of the denominator hypothesis of
`Kakeya.ml1Boot.frostmanConstIn_anchor_le`.  Nothing is added, nothing is strengthened, and no
constant is introduced: `C_T` is the one of `Kakeya.ml1Boot.densityTransfer.C`, already carried
by every statement that displays this group.

The ambient index set is the *parameter* `s'` rather than being fixed to the family's own
index type, because the group is read at two different ambients: at `t ⊆ u''` by
`Kakeya.ml1Boot.frostmanConstIn_anchor_le`, whose numerator is asserted at `u''`, and at
`t ⊆ s'` with a separate `s' ⊆ u''` by
`Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_factorization` and its callers.

*The capture `𝕍|_t[W] = t` is deliberately not a field.*  It is derivable — every `T̃_k` with
`k ∈ t` lies in the convex hull `W` of their union, so all of `t` is caught — and putting it here
would carry a step of a proof in the data.  That derivation is
`Kakeya.ml1Boot.familyIn_convexHull_biUnion_self`, and it is what every consumer of this bundle
now uses in place of the former `hcapture` binder.

`block_nonempty` is carried but unused, in the idiom of
`Kakeya.ml1Boot.density_dilate_ge`, which binds it as the unused `_htne`.  It is what makes `t`
a *block*, and every site holds it.

*The widths are unconstrained here, and `volume_le` is vacuous at `ap = 0`.*  In `ℝ≥0∞` the
ratio `bp/ap` is `⊤` when `ap = 0 < bp`, so `volume_le` then says only `|K| ≤ ⊤`.  The pair
`0 < ap ≤ bp` is therefore **not** a field: it is not what makes this bundle a placement, it is
what the *arithmetic* of the consumers needs — `Kakeya.ml1Boot.frostmanConstIn_anchor_le` spends
it on cancelling `C_T (bp/ap)` against `C_T⁻¹ (ap/bp)` — and every consumer carries it as its own
`hap0`, `hab`.  Bundling it here would put a hypothesis of the conclusion into the hypothesis of
the placement, and would make this predicate false in the degenerate case rather than vacuous,
which is a strengthening. -/
structure IsAnchorPlacement {ι : Type*} {δt : ℝ≥0} (T : ι → Tube δt E)
    (K : ConvexSpaceBody E) (ap bp : ℝ≥0) (s' t : Finset ι) : Prop where
  /-- The block lies in the ambient index set. -/
  block_subset : t ⊆ s'
  /-- The block is nonempty; this is what makes `t` a block. -/
  block_nonempty : t.Nonempty
  /-- The plank of the block lies inside the anchor. -/
  plank_le : (t.convexHull_biUnion fun k => (T k).toConvexSpaceBody) ≤ K
  /-- The anchor has volume at most `C_T (b̃/ã)` times that of the plank of the block. -/
  volume_le : volume K.carrier ≤ (densityTransfer.C : ℝ≥0∞)
    * ((bp : ℝ≥0∞) / (ap : ℝ≥0∞))
    * volume (t.convexHull_biUnion fun k => (T k).toConvexSpaceBody).carrier

/-- **The anchor denominator at a block**.

In the situation of `Kakeya.ml1Boot.IsAnchorPlacement`, and with
`W = conv (⋃_{k ∈ t} T̃_k)` the plank of `t` as there, a pair `(t, L)` with `L : ℝ≥0∞` is an
*anchor denominator* for `(𝕍, K, ã, b̃)` if `t` is an anchor placement for `(𝕍, K, ã, b̃)`,
`0 < L`, and `L ≤ Δ(𝕍|_t, W)`.

*This is the denominator hypothesis of `Kakeya.ml1Boot.frostmanConstIn_anchor_le` and nothing
else.*  The placement is one field of it and the two displays above are the other two.

*`L ≠ ⊤` is deliberately not a field.*  What the proof of that lemma needs of the denominator is
`0 < L < ∞`, the identity `(U/L) * L = U` failing at `L = ⊤` in `ℝ≥0∞`; but finiteness follows
from `denom_le` alone, by
`L ≤ Δ(𝕍|_t, W) ≤ Δ_max(𝕍|_t) ≤ |t| < ∞`, that is `Kakeya.le_maxDensity` followed by
`Kakeya.maxDensity_le_card`, the block `t` being finite.  That derivation is
`Kakeya.ml1Boot.IsAnchorDenominator.denom_ne_top`, and it is what the consumers now use in place
of the former `hLtop` binder.  Dropping that binder does not change what
`Kakeya.ml1Boot.frostmanConstIn_anchor_le` proves: its former form is the instance of the present
one at a caller who happens to hold `L ≠ ⊤`.

Six of the eight sites that display the anchor group hold this bundle entire; the two that
manufacture their own denominator out of a count —
`Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_factorization` and
`Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_count` — hold
`Kakeya.ml1Boot.IsAnchorPlacement` only.  That is the reason for two bundles rather than
one. -/
structure IsAnchorDenominator {ι : Type*} {δt : ℝ≥0} (T : ι → Tube δt E)
    (K : ConvexSpaceBody E) (ap bp : ℝ≥0) (s' t : Finset ι) (L : ℝ≥0∞) : Prop
    extends IsAnchorPlacement T K ap bp s' t where
  /-- The denominator is positive. -/
  denom_pos : 0 < L
  /-- The denominator is a lower bound for the density of the block at its own plank. -/
  denom_le : L ≤ densityIn t (fun k => (T k).toConvexSpaceBody)
    (t.convexHull_biUnion fun k => (T k).toConvexSpaceBody)

/-! #### The seam between the produced and the consumed fibre Frostman bound

`Kakeya.ml1Boot.frostmanConstIn_fibre_le_rpow` produces its bound at the index set
`𝕋̃''[2 · T_b]` and the body `2 · T_b`, whereas hypothesis (a) of
`Kakeya.ml1Boot.normalized_le_of_coarse` reads it at the index set `fibre u p_b l` and the body
`T_{b,l}`.  The four declarations below close that seam, and record exactly what it costs.

Both differences are handled, and only one of them costs anything:

* the **body** is free.  Shrinking the ambient body from `2 · T_b` back to `T_b` *lowers* the
  Frostman constant whenever the index set's members all lie in `T_b`, which is what the
  undilated `Kakeya.ml1Boot.IsParentFamily` of `Kakeya.ml1Boot.normalized_le_of_coarse` supplies;
  this is `Kakeya.ml1Boot.frostmanConstIn_le_of_le_ambient`, with no loss at all.  The `2`-dilate
  is therefore needed only on the *producer* side, where the plank lies in `2 · T_b` and in no
  tube of scale `O(b)`, and does not have to be
  propagated into the consumer.
* the **index set** is not free.  `Kakeya.frostmanConstIn` is not monotone in the index set, so
  the free inclusion `fibre u p_b l ⊆ 𝕋̃''[2 · T_b]` — the containment clause of the parent
  family followed by `Kakeya.Tube.subset_dilate` — transports nothing.  What is needed is that
  the two index sets *agree*, i.e. the reverse inclusion `𝕋̃''[2 · T_b] ⊆ fibre u p_b l`: no
  `δ̃`-tube of the family lies in `2 · T_b` except those assigned to `T_b` itself.  That is a
  hypothesis of exactly the kind blueprint `note:ml1bootFibreInclusionNotAutomatic` refutes as
  automatic, read at the *plank* scale rather than at the parent scale `ρ`.

The two are one seam and not two: `Kakeya.ml1Boot.familyIn_subset_of_familyIn_subset_of_le` shows
that the `∀ K ≤ 2 · T_b` in the `hfibre` of `Kakeya.ml1Boot.frostmanConstIn_fibre_le` is
redundant — the single instance at `K = 2 · T_b` implies all of it, because `𝕋̃''[K]` is monotone
in `K` — so the plank-scale inclusion needed for the index sets to agree *implies* `hfibre`
whenever `p_b` refines `p_ρ`.

Where that inclusion cannot come from, and what replaces it:

* **not from the parent map.**  Hypothesis (a) of `Kakeya.ml1Boot.normalized_le_of_coarse` reads
  the bound at *every* `l ∈ t_b`, so the seam needs the inclusion at every `l` at once; by
  `Kakeya.ml1Boot.disjoint_familyIn_of_familyIn_subset_fibre` that is equivalent to a separation
  property of the `b`-tubes — no `δ̃`-tube of `u''` lies in two of the `2`-dilates — and once
  that fails no reassignment of `p_b` repairs it, a single `δ̃`-tube having to go to two indices.
  So it is not a fact that the *construction* of the parent map can be made to deliver.
* **not from essential distinctness, hence not from the merge.**  Pairwise
  `Kakeya.IsEssentiallyDistinct` is the only geometric information about `t_b` that
  `Kakeya.ml1Boot.exists_plankTube_parentFamily_essDistinct` and the merge
  `Kakeya.ml1Boot.exists_merged_parentFamily` behind it export, and it is strictly weaker than
  that separation: two `σ`-tubes with parallel cores at distance `3 σ` are disjoint, hence
  essentially distinct, while both `2`-dilates contain the `δ̃`-tube whose core is the parallel
  unit segment midway between them.  Raising the merge ratio does not help: the ratio is spent
  transporting the plank clause of a *discarded* tube, never on emptying a *retained* tube's
  dilate.  The docstring of `Kakeya.ml1Boot.disjoint_familyIn_of_familyIn_subset_fibre` carries
  the computation.
* **what does transport is mass.**  `Kakeya.ml1Boot.frostmanConstIn_fibre_le_of_mass` and its
  tube-shaped form `Kakeya.ml1Boot.frostmanConstIn_fibre_undilated_le_of_mass` replace the
  inclusion by the share `∑_{𝕋̃''[2 · T_b]} |T_i| ≤ C ∑_{fibre} |T_i|`, at the price `C` in the
  constant.  Unlike the inclusion, the share can hold at every `l` at once.  It is the weaker
  ask that blueprint `note:ml1bootReduceToTbFrostmanIndexSet` identifies as where to attack the
  seam next, and the route through `ConvexSpaceBody.IsFrostmanIn.of_le_of_subset` taken here
  carries none of the four side conditions of `ConvexSpaceBody.frostmanConstIn_subfamily_le`
  that the note routes it through — no nonemptiness, no equality of member volumes — so it is
  available at *every* `l` and not only at the index
  `Kakeya.ml1Boot.exists_surviving_parent_index` singles out.  Whether the share itself is
  derivable from the Case (ii) data is not settled here. -/

end DensityTransfer

end ml1Boot

end Kakeya

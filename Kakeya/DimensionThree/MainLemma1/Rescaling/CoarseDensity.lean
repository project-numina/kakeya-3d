/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.OneSidedUniform
public import Kakeya.DimensionThree.MainLemma1.Rescaling.FineDilate
public import Kakeya.Thickness.Diam
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Main Lemma 1, Case (ii): The maximal density of the `b`-tubes

Split out of `Kakeya/DimensionThree/MainLemma1/Rescaling.lean`.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya

namespace ml1Boot

/-! ### The maximal density of the `b`-tubes -/

/-- **The constant `C_{lem:ml1bootDilateTestBody}(3)`**:

`C(n) = 3 ^ n · C_{lem:outerPrismVolumeComparison}(n)`, so in particular
`C(3) = 3 ^ 3 · Metric.volume_outerPrism_le_volume_self.C 3 ≥ 1`,

the factor by which a convex test body has to be enlarged before it absorbs the `2`-dilates of
all the tubes it contains (`Kakeya.ml1Boot.exists_dilate_testBody`).

The two factors are the two steps of that lemma, whose witness is
`K* = 3 · outerPrism K` (`Kakeya.ml1Boot.dilateTestBody`).  The factor
`Metric.volume_outerPrism_le_volume_self.C 3` pays for replacing `K` by the outer prism
`P = outerPrism K` around it, and the factor `3 ^ 3` is the volume of a homothety of ratio `3`
in `ℝ³`, which pays for the enlargement of `P` to `3 · P` that absorbs the dilates.  Both
factors are `≥ 1`, hence so is the product.  It depends only on the ambient dimension; in
particular not on `δ̃`, `ap`, `bp`, `ρ`, `γ`, `j`, the family, or the test body.

It is emphatically *not* `Kakeya.Tube.tubeDilateVolume.C' 3 2 = 2³`: that constant compares
`|2 · T|` with `|T|` for a single tube, whereas the quantity bounded here is `|K*| / |K|` for
a test body `K`, and a tube is in general far from centrally placed inside a `K` containing
it.

The alternative value was `2 ^ 3 * (6 choose 3)`, whose second factor was the Rogers–Shephard
constant of the now retired blueprint `prop:ml1bootDifferenceBodyVolume` and whose first was
the volume of a ratio-`2` homothety.  Nothing downstream uses the numerical value: it enters
`Kakeya.ml1Boot.coarsePlank.C` symbolically and is carried symbolically from there. -/
noncomputable abbrev dilateTestBody.C : ℝ≥0 :=
  3 ^ 3 * Metric.volume_outerPrism_le_volume_self.C 3

/-- **The constant `C_{lem:ml1bootCoarsePlankDensity}`**:
`C_{lem:ml1bootDilateTestBody} · 2 · C_{lem:ml1bootPlankInTubeRepaired} · C_{lem:ml1bootCardBound}`.

The middle factor compares a `b`-tube with the plank it contains, the first pays for the
passage to a test body absorbing the `2`-dilates, and the last counts the essentially
distinct `ρ`-tubes of `𝕋̃_ρ` in `B₁ ⊆ ℝ³`.  It depends only on the ambient dimension `3`,
and on nothing else.

The plank-to-tube factor is `Kakeya.ml1Boot.plankInTube.C`; see the docstring of
`Kakeya.ml1Boot.volume_plankTube_le` for why the alternative candidate
`Kakeya.ml1Boot.densityTransfer.C * Kakeya.ml1Boot.plankPigeonhole.C`, computed with the
retired value of `densityTransfer.C`, was too small by a factor
`1280 · Metric.volume_comparison.C 3`. -/
noncomputable abbrev coarsePlank.C : ℝ≥0 :=
  dilateTestBody.C * 2 * plankInTube.C * cardBound.C

/-- **The constant `C_{lem:ml1bootPlankTubeParents}(n)`**:

`C(n) = 6 · C_{lem:tubeOverlapCoreClose}(n) ²`, with
`C_{lem:tubeOverlapCoreClose}(n) = 9 + 2 · 4 ^ n / c_{le_volume}(n)`
(`Kakeya.Tube.tubeOverlapCoreClose.C`), so that in `ℝ³`
`C(3) = 6 · (9 + 128 / c_{le_volume}(3)) ²`.

This is the dilation ratio of the parent family that
`Kakeya.ml1Boot.exists_plankTube_parentFamily_essDistinct` produces: it replaces the ratio `2`
that the plank-to-tube step alone would give, and the enlargement pays for making the `b`-tubes
pairwise essentially distinct *without* discarding any fine tube.  It depends only on the
ambient dimension `n`; in particular not on `δ̃`, `ap`, `bp`, `ρ`, the family, or the index
sets.

**The enlargement is not needed, because the distinctness it pays for is not needed, and this
constant now has no live consumer.**  The `b`-tubes' pairwise essential distinctness was asked
for only by `Kakeya.ml1Boot.multiplicity_coarse_le`, and that hypothesis was inert: it was used
only to build the corresponding hypothesis of `Kakeya.ml1Boot.bracket_mem_Icc`, which never
referenced it, and neither did `Kakeya.ml1Boot.multiplicity_coarse_raw`, while
`Kakeya.KatzTaoEstimate.multiplicity_bound` has no such hypothesis at all.  What excludes
degenerate repetition at the bottom of that chain is the fullness hypothesis.  All three
hypotheses have been deleted, and `Kakeya.ml1Boot.exists_plankTube_parentFamily` now delivers
the parent family at the plank's own ratio `2`, obtaining the `injOn` field of
`Kakeya.ml1Boot.IsParentFamilyDilate` from `Kakeya.ml1Boot.exists_dedupe_dilate` instead — which
identifies only blocks whose `b`-tubes have *equal bodies*, and so costs nothing in the ratio.

This constant is therefore reached only through
`Kakeya.ml1Boot.exists_plankTube_parentFamily_essDistinct`, which is itself retained but
uncalled, against a future consumer that does need distinctness.  It is kept rather than
deleted for the same reason.  See blueprint `note:ml1bootCoarseEDInert`.

Three constraints fix it, all read at `C_ov = Kakeya.Tube.tubeOverlapCoreClose.C n`:

* the plank clause `T_k ⊆ 2 · T_{b,l}` must survive at the new ratio, so `2 ≤ C(n)`;
* `Kakeya.Tube.subset_dilate_rescale_of_subset_dilate`, which transports a containment from a
  discarded `b`-tube to a retained one, asks `2 · C_ov ≤ C(n)`;
* and, at equal scales `δ = ρ = C_𝕎 bp`, its numeric hypothesis
  `6 · C_ov ² · δ ≤ C(n) · ρ` asks `6 · C_ov ² ≤ C(n)`.

The third is the binding one, `C_ov > 9` making it dominate the other two, so `C(n) = 6 C_ov ²`
is exactly the least value the route allows.  The figure `3` (hence `6 = 2 · 3`) that blueprint
`note:auditPlankTubeParents`(b) guessed for the discarded-to-retained containment is *not*
what the available geometry gives: `Kakeya.Tube.tubeOverlapCoreClose` produces `C_ov`, whose
value is dictated by the near-parallelism bound `2 · 4 ^ n / c_n` of
`Kakeya.Tube.overlapTransversal` together with the axial overhang. -/
noncomputable abbrev plankTubeParents.C (n : ℕ) : ℝ :=
  6 * Tube.tubeOverlapCoreClose.C n ^ 2

/-- **`Kakeya.ml1Boot.plankTubeParents.C` as an `NNReal`.**

The dilation ratio of the `b`-tube parent family is `ℝ`-valued because
`Kakeya.Tube.tubeOverlapCoreClose.C` is, but every consumer that carries it as a *scale* — the
`c` of `Kakeya.ml1Boot.IsParentFamilyDilate` and of
`Kakeya.ml1Boot.normalized_le_of_coarse_dilate` — needs an `NNReal`.  This is that `NNReal`,
together with the two facts a caller reads off it: its coercion is the `ℝ`-valued constant
(`Kakeya.ml1Boot.plankTubeParents.coe_CNN`) and it is at least `1`
(`Kakeya.ml1Boot.plankTubeParents.one_le_CNN`).

Recorded in the ledger of `Kakeya.ml1Boot.multTildeT_of_planksClose` as "naming an `NNReal` whose
coercion is the `ℝ`-valued `Kakeya.ml1Boot.plankTubeParents.C 3`"; this discharges it.  Positivity
comes from `Kakeya.Tube.tubeOverlapCoreClose.one_lt_C`, so no numeral is evaluated. -/
noncomputable def plankTubeParents.CNN (n : ℕ) : ℝ≥0 :=
  Real.toNNReal (plankTubeParents.C n)

/-- The `ℝ`-valued dilation ratio is at least `1`, from
`Kakeya.Tube.tubeOverlapCoreClose.one_lt_C`; no numeral is evaluated. -/
theorem plankTubeParents.one_le_C (n : ℕ) : (1 : ℝ) ≤ plankTubeParents.C n := by
  have h := Tube.tubeOverlapCoreClose.one_lt_C n
  have h0 : (0 : ℝ) ≤ Tube.tubeOverlapCoreClose.C n :=
    le_of_lt (lt_trans zero_lt_one h)
  simp only [plankTubeParents.C]
  nlinarith

@[simp]
theorem plankTubeParents.coe_CNN (n : ℕ) :
    ((plankTubeParents.CNN n : ℝ≥0) : ℝ) = plankTubeParents.C n :=
  Real.coe_toNNReal _ (le_trans zero_le_one (plankTubeParents.one_le_C n))

section CoarseDensity

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### The pinning chain against a *dilated* parent

The six declarations below are the `Kakeya/Tube/Dilate.lean` pinning chain
(`Tube.norm_perp_direction_le_of_chord` … `Tube.subset_dilate_of_norm_perp_direction_le`) with
the parent membership of the pinning point `p` weakened from `p ∈ T_ρ` to
`p ∈ c · T_ρ` for a ratio `c ≥ 1`.  They are what the merge-before-pigeonhole route needs:
once the `ρ`-parents are merged by `Kakeya.ml1Boot.exists_merged_rhoParentFamily`, every plank
containment is only a `c`-dilate containment, and the original chain — which reads `hpρ` at the
undilated carrier in three places — is unavailable.

They are *parked* here rather than placed beside the lemmas they generalize, exactly as
`Kakeya.ml1Boot.dilate_le_dilate_of_le` is: `Kakeya/Tube/Dilate.lean` is closed, and the
signed chord-angle step it uses is `private` there, so the copy
`Kakeya.ml1Boot.perp_direction_le_of_aux` is unavoidable.

Every `ρ`-term of the original picks up one factor of `c` and the axial `1/2` becomes `c/2`,
because `Tube.abs_inner_and_perp_le_of_mem_dilate` is already stated at a free ratio and reads
`c / 2 + c δ` and `c δ` there.  With `c ≤ K` and `c ρ ≤ 1` the two branch constants `59/2 K ρ`
and the longitudinal `16 K` are unchanged, so the final ratio is `32 K` exactly as before; at
`c = 1` each statement is the original one, `Tube.subset_dilate` turning `p ∈ T_ρ` into
`p ∈ 1 · T_ρ`. -/

end CoarseDensity

end ml1Boot

end Kakeya

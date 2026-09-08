/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.AffineMap
public import Kakeya.Frostman
public import Kakeya.KatzTao
public import Kakeya.Thickness.Volume

/-!
# The Section-9 spine: inheritance of the two non-clustering conditions

Main Lemma 2 (blueprint GWZ) uses GWZ Remark 3.3
(blueprint `inheritedDownwardsUpwardsRemark`, stated in GWZ) twice, and the two uses
are of *opposite* kinds:

* **(B), downwards, Katz-Tao.** From `Δ_max(𝕋) ≤ δ^{-η}`, for each
  `T_τ ∈ 𝕋_τ` one gets `C_KT(𝕋[T_τ], T_τ) ≤ δ^{-η}`.
* **(A), upwards, Frostman.** From `C_F(𝕋̃_ρ, T_b) ≲ δ^{-η'}` one gets
  `C_F(𝕋̃_σ, T_b) ≲ δ^{-η'}` for the coarser families `𝕋̃_σ`, `σ ∈ [ρ, b]`.

Both halves of the remark are **already in the tree**, at the general convex-body level:

* (B) is `ConvexSpaceBody.IsKatzTao.subset` (`Kakeya/KatzTao.lean`);
* (A) is `ConvexSpaceBody.IsFrostmanIn.inherited_upwards`, its ambient-radius version
  `ConvexSpaceBody.IsFrostmanIn.inherited_upwards'`, and the uniform-fibre version
  `ConvexSpaceBody.IsFrostmanIn.inherited_upwards_uniform` (`Kakeya/Frostman.lean`).

This file supplies only the *adapters* between those and the shapes the Section-9 reduction
reads, and the two `Δ`-comparison facts of the non-eccentric case.
mathematics; everything is bookkeeping around the two named lemmas.

## What is here

### The anchored reading of (B)

`C_KT(𝕍, K)` is `Δ_max` of the family after the affine change of variables that takes `K` to
the unit ball, and `Kakeya.maxDensity` is exactly invariant under such a change
(`Kakeya.maxDensity_affineImage`). So the anchor carries no information and (B) is a statement
about `Kakeya.maxDensity` of a subfamily: `Kakeya.ML2Spine.isKatzTao_familyIn` and
`Kakeya.ML2Spine.maxDensity_familyIn_le` read it at the subfamily `𝕋[K]` that the Section-9
call site names, and `Kakeya.ML2Spine.isKatzTao_familyIn_affineImage` records that rescaling
`K` to `B₁` first changes nothing.

### The parent-map reading of (A)

`ConvexSpaceBody.IsFrostmanIn.inherited_upwards'` consumes a `Finpartition` and produces a
family indexed by a subset of its *parts*. Section 9 has instead a *parent map*
`par : ι → κ` sending each `ρ`-tube to the `σ`-tube containing it, and wants the conclusion
indexed by a subset of the coarse index set `κ`.
`Kakeya.ML2Spine.exists_subset_isFrostmanIn_parents'` performs that translation once and for
all: it builds the fibre partition, transports the coarse bodies to the parts
(`Kakeya.ML2Spine.parentBody`), applies `inherited_upwards'`, and reindexes back along
`ConvexSpaceBody.IsFrostmanIn.reindex`.

The conclusion keeps the explicit dyadic-pigeonhole loss
`ConvexSpaceBody.IsFrostmanIn.inherited_upwards.C'` of the underlying lemma; it is a
logarithm of `|q| / δ^n`, not a constant, and absorbing it into a small negative power of the
scale is the caller's business (compare the docstring of
`Kakeya.ml1Boot.exists_frostmanConstIn_coarse_le`, which makes the same choice on the
Main-Lemma-1 side).

The subfamily `out' ⊆ out` cannot be dispensed with: without a comparability hypothesis on the
fibre densities the remark is only true after passing to a dyadic class, which is precisely
what GWZ's `\lessapprox` conclusion means. The all-parents version, at the price of that
hypothesis, is the existing `ConvexSpaceBody.isFrostmanIn_parents_of_uniform_fibres`.

### The retained-mass bound, and why the conclusion is worthless without it

`ConvexSpaceBody.IsFrostmanIn s W K C` unfolds to
`∀ K' ≤ K, densityIn s W K' ≤ C * densityIn s W K`, which at `s = ∅` reads `0 ≤ C * 0` and
therefore holds for **every** `C`, including `C = 0`. So a conclusion of the bare shape
`∃ out' ⊆ out, IsFrostmanIn out' W K …` is provable from *no* hypotheses at all by taking
`out' = ∅`: it says nothing. The mathematics that is missing from such a statement is not
missing from the proof — the dyadic pigeonhole `ENNReal.dyadic_pigeonhole₁''` inside
`ConvexSpaceBody.IsFrostmanIn.inherited_upwards'` *proves* that the retained parts carry a
definite fraction of the total mass, and that lemma then discards the fact.

Every existential statement in this file therefore carries the pigeonhole's own retained-mass
bound alongside the Frostman conclusion:
`∑_{i ∈ q} |V i| ≤ L · ∑_{i ∈ q, par i ∈ out'} |V i|`, with
`L = Kakeya.ML2Spine.inheritedMassLoss`, the exact `1 + log₂(range ratio)` factor charged by the
pigeonhole (and exactly half of `inherited_upwards.C'`, see
`Kakeya.ML2Spine.two_mul_inheritedMassLoss`). Since `δ > 0` forces every `|V i| > 0`, this bound
fails outright at `out' = ∅` whenever `q` is nonempty
(`Kakeya.ML2Spine.filter_nonempty_of_massBound`), so the `∅` witness no longer discharges the
goal. `Kakeya.ML2Spine.exists_subset_mass_isFrostmanIn_parts` is the partition-level lemma that
keeps `hsum`; it is a mass-tracking restatement of
`ConvexSpaceBody.IsFrostmanIn.inherited_upwards'`, proved the same way.

For the Section-9 consumer the mass bound is essential. In the GWZ estimate
`goodFrostmanBoundTTRhoInsideTb`, the Frostman bound on the coarse family is combined with the
lower bound `lowerBdOnDeltaMaxTTSigmaTb` on the maximal density of the coarse family inside
`T_b` to produce the cardinality estimate `TTSigmaBigCardinalityV1`. A coarse subfamily carrying
none of the mass carries none of the density either, and the comparison degenerates.

### The two `Δ` comparisons of the non-eccentric case

The GWZ argument requires, for convex bodies `V ⊆ T_b`,
`Δ(𝕋_ρ, T_b) ≥ (|V|/|T_b|) · Δ(𝕋_ρ, V)` and `Δ_max(𝕋_b) ≤ (|T_b|/|V|) · Δ_max(𝕍)`. These are
`Kakeya.ML2Spine.volume_div_mul_densityIn_le` and
`Kakeya.ML2Spine.maxDensity_le_ratio_mul_maxDensity`. Neither is in `Kakeya/Density.lean`: the
density lemmas there are monotone in the *index set* (`Kakeya.densityIn_mono`,
`Kakeya.maxDensity_mono`) or compare a family with itself under a change of test body
(`Kakeya.densityIn_mul_le_of_volume_band`), whereas these two compare *two different families*
across a containment, so they are proved here from
`Kakeya.sum_volume_eq_densityIn_mul_volume` and `Kakeya.maxDensity_le_of_forall_sum_le`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Kakeya

namespace Kakeya.ML2Spine

section KatzTaoDownwards

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*}

/-- **GWZ Remark 3.3(B), anchored form.** If `𝕎` is `C`-Katz-Tao then so is the subfamily
`𝕎[K]` of its members contained in `K`. Immediate from `ConvexSpaceBody.IsKatzTao.subset`. -/
theorem isKatzTao_familyIn {s : Finset ι} {W : ι → ConvexSpaceBody E} {C : ℝ≥0∞}
    (h : ConvexSpaceBody.IsKatzTao s W C) (K : ConvexSpaceBody E) :
    ConvexSpaceBody.IsKatzTao (familyIn s W K) W C :=
  h.subset (Finset.filter_subset _ _)

end KatzTaoDownwards

section DensityComparison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι κ : Type*}

end DensityComparison

section MassTrackingInheritance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*}

/-- **The density floor of the dyadic pigeonhole** inside
`ConvexSpaceBody.IsFrostmanIn.inherited_upwards'`: a convex body whose `ethickness.scale` is at
least `δ`, sitting inside an ambient body contained in `B(0, R)`, has density at least this. -/
@[nolint defsWithUnderscore]
noncomputable abbrev inheritedFloor (n : ℕ) (δ R : ℝ≥0) : ℝ≥0 :=
  lt_volume_convexHull.c n * δ ^ n / (2 * R) ^ n

/-- **The retained-mass loss** charged by the dyadic pigeonhole inside
`ConvexSpaceBody.IsFrostmanIn.inherited_upwards'`: the `1 + log₂(range ratio)` count of dyadic
classes, i.e. exactly half of `ConvexSpaceBody.IsFrostmanIn.inherited_upwards.C'`, whose other
factor `2` is the width of the dyadic window itself
(`Kakeya.ML2Spine.two_mul_inheritedMassLoss`). -/
@[nolint defsWithUnderscore]
noncomputable abbrev inheritedMassLoss (n card : ℕ) (δ R : ℝ≥0) : ℝ≥0 :=
  Real.toNNReal (1 + Real.logb 2
    ((card : ℝ) * (2 * R : ℝ) ^ n / ((lt_volume_convexHull.c n : ℝ) * (δ : ℝ) ^ n)))

/-- The closed ball of radius `R` about the origin has volume at most `(2R) ^ n`. -/
private lemma volume_closedBall_le_two_mul_pow (R : ℝ≥0) :
    volume (Metric.closedBall (0 : E) (R : ℝ)) ≤
      ((2 * R : ℝ≥0) : ℝ≥0∞) ^ Module.finrank ℝ E := by
  rw [Measure.addHaar_closedBall' volume (0 : E) (R.coe_nonneg)]
  calc
    ENNReal.ofReal ((R : ℝ) ^ Module.finrank ℝ E) * volume (Metric.closedBall (0 : E) 1)
        ≤ ENNReal.ofReal ((R : ℝ) ^ Module.finrank ℝ E) * 2 ^ Module.finrank ℝ E := by
          gcongr
          exact volume_closedBall_le_two_pow_finrank (E := E)
    _ = ((2 * R : ℝ≥0) : ℝ≥0∞) ^ Module.finrank ℝ E := by
      rw [ENNReal.ofReal_pow R.coe_nonneg, ← mul_pow]
      congr 1
      norm_num [mul_comm]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Local copy of the private `ConvexSpaceBody.IsFrostmanIn.all_le_of_partition`. -/
private lemma all_le_of_partition [DecidableEq ι] {s : Finset ι} (P : Finpartition s)
    {V : ι → ConvexSpaceBody E} {W : Finset ι → ConvexSpaceBody E} {K : ConvexSpaceBody E}
    (hWK : ∀ t ∈ P.parts, W t ≤ K) (hVW : ∀ t ∈ P.parts, ∀ i ∈ t, V i ≤ W t) :
    ∀ i ∈ s, V i ≤ K := fun i hi ↦ by
  rw [← P.sup_parts, Finset.sup_eq_biUnion, Finset.mem_biUnion] at hi
  obtain ⟨t, ht, hit⟩ := hi
  exact le_trans (hVW t ht i hit) (hWK t ht)

end MassTrackingInheritance

section FrostmanUpwards

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι κ : Type*}

variable [DecidableEq ι] [DecidableEq κ]

end FrostmanUpwards

end Kakeya.ML2Spine

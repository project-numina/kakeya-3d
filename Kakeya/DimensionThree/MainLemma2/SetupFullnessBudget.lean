/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.SetupAbsorption
public import Kakeya.DimensionThree.MainLemma2.ThinEstimates
public import Kakeya.DimensionThree.MainLemma2.BallJoint
public import Kakeya.ShadedUniform

/-!
# The fullness budget of the setup statement

`Kakeya.VeryNotSticky.fullness_ge` asserts the aggregate fullness of the *produced*
configuration at exactly `δ^η`, the same exponent, with no comparison constant, at which the
binder `hfull` of `Kakeya.VeryNotSticky.exists_setup_caseSideData` asserts it for the *given*
family.  This file measures what that costs, in one direction and the other.

* `Kakeya.VeryNotSticky.rpow_add_le_fullness_of_isCRefinement` and
  `Kakeya.VeryNotSticky.fullness_two_eta_of_isCRefinement`: at the exponent `2η` the field is
  **free** — it follows from the two conjuncts the target already carries, `hfull` and
  `δ^η ≤ c`, by `ShadedBody.IsCRefinement.mul_fullness_le`.  Nothing else is needed: no
  property of the construction, no geometry.
* `Kakeya.VeryNotSticky.lt_rpow_of_fullness_loss` and
  `Kakeya.VeryNotSticky.rpow_two_eta_le_of_fullness_loss`: the budget the field grants for a
  refinement's fullness loss is **exactly `1` at the exponent `η`** — any loss factor below
  `1` is fatal — and `δ^η` at the exponent `2η`.
* `Kakeya.VeryNotSticky.rpow_mul_fullness_le_of_fullness'_le`: the loss of the tree's only
  producer of the field `Kakeya.VeryNotSticky.uniform`,
  `ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf`, in the form the budget above reads.
  That lemma's fullness clause is a `δ^{-α'}` comparison with `0 < α'` a *hypothesis of the
  lemma*, so the loss is a positive power of `δ` and cannot be zero.
* `Kakeya.VeryNotSticky.exists_uniform_refinement_fullness_two_eta`: the composition — the
  Markov step of the density-band pigeonhole followed by the shaded uniformization — delivering
  `uniform` at the dimension-only constant `ShadedTube.ssfUniformConst` **together with**
  aggregate fullness `δ^{2η}`, from the aggregate binder alone.  So the pair (`uniform`,
  `fullness_ge`) is jointly satisfiable at the repaired exponent, and (by the two budget lemmas
  above) not at the exponent as written.
* `Kakeya.VeryNotSticky.caseSideData_localDensity`: the demand side, unconditional — the side
  data forces the produced shading to be `δ^{3η}`-dense at scale `r₁` around *every* one of its
  own points, which is what a construction has to arrange by deleting the shading that is not.

Read together: the construction's mandatory steps all lose a positive power of `δ` of the
fullness, the field as written grants none, and at `δ^{2η}` it grants more than they spend.

**Not settled here, and recorded so that it is not mistaken for settled.**  The composition
above stops short of the two-sided density bracket
`Kakeya.VeryNotSticky.shading_lb`/`Kakeya.VeryNotSticky.shading_ub`.  Those come from the dyadic
band (`Kakeya.VeryNotSticky.eventually_exists_shadingBand_eta`, which already delivers them
together with the target's own conjunct `δ^η ≤ c`), and the band is a *selection of an index
subset*, under which `ShadedTube.ShadedUniformTubeSet` is not hereditary: its two lower brackets
`le_card_shadeClass` and `le_branchingN` are lower bounds on shade-class cardinalities.  Running
the band after the uniformization therefore breaks `uniform`, and running it before means the
uniformization's per-tube shade deletion — controlled only in the aggregate — breaks
`shading_lb`.  The exact missing input is a *class-dense* density pigeonhole, in the sense of
the criterion Section 8 records for the same obstruction at
`Kakeya.ml1Boot.exists_uniformFactorCore`.  This file makes no claim about it.
-/

@[expose] public section

open scoped NNReal ENNReal

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set Topology Filter ShadedBody
open scoped NNReal ENNReal

universe u

/-! ### The budget at `2η`: free from the target's own conjuncts -/


/-! ### The budget at `η`: exactly zero -/


/-! ### The loss of the two mandatory steps, and the composition -/

/-- **Pointwise density gives aggregate fullness.**

The converse direction of the Markov step: a family every member of which is individually
`θ`-full is `θ`-full in the aggregate.  This is what makes the shaded uniformization's
*relative* fullness clause usable — that clause compares the new shading with the old one on
the **same** subfamily, and says nothing about how full the subfamily was to begin with. -/
theorem le_fullness_of_pointwise {ι : Type*} {s : Finset ι}
    {V : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} {θ : ℝ≥0}
    (hne : ∑ i ∈ s, volume (V i).carrier ≠ 0)
    (h : ∀ i ∈ s, (θ : ℝ≥0∞) * volume (V i).carrier ≤ volume (V i).shade) :
    θ ≤ ShadedBody.fullness s V := by
  have htop : ∑ i ∈ s, volume (V i).carrier ≠ ⊤ :=
    (ENNReal.sum_lt_top.2 fun i _ ↦ (V i).isCompact.measure_lt_top).ne
  rw [← ENNReal.coe_le_coe, ShadedBody.coe_fullness]
  refine (ENNReal.le_div_iff_mul_le (Or.inl hne) (Or.inl htop)).2 ?_
  calc (θ : ℝ≥0∞) * ∑ i ∈ s, volume (V i).carrier
      = ∑ i ∈ s, (θ : ℝ≥0∞) * volume (V i).carrier := by rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ s, volume (V i).shade := Finset.sum_le_sum h


/-! ### The demand side: what the produced shading must satisfy at every one of its points -/


end Kakeya.VeryNotSticky

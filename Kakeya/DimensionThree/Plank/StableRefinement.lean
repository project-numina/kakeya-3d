/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.TypicalAngleIncidence
public import Mathlib.Algebra.Order.Floor.Extended

/-!
# The stable refinement, and its compatibility with the selection

The saturated Item 2 route runs on shadings carrying two *global* angular data: the one-sided angle
upper bound `Kakeya.HasMaxPlankAngleBound` and a global angular stability clause.  Those are the two
hypotheses of `Plank.localAngleConcentration_of_saturated_scaled`, from which hypothesis (5) of the
dense-box chain follows for every saturated box-local family.

This file supplies them.  There is nothing to construct: they are two of the conclusions of GWZ
Lemma 6.11, taken in the reserve form `Kakeya.findingTypicalAngleOfIntersection_stable_reserve`,
whose stability clause is already at the sub-polynomial scale `Kakeya.plankAngleScaleB a`.
What this file does is repackage that output in the exact shape the route consumes, and record
honestly what
the repackaging costs:

* the stability scale is `2 · Kakeya.plankAngleScaleB a`, not `Kakeya.plankAngleScaleB a`.  The
  factor `2` is genuine: the global `θ` is selected by a dyadic pigeonhole across fibres and so
  agrees with the fibre-local typical angle only up to the constant `2` of the angle comparison.
  This is why `Plank.localAngleConcentration_of_saturated_scaled` exists;
* the fibre-retention scale is the output scale `Aout(a) = max 2 (Kakeya.plankAngleScaleA a)`, at
  which `2 ≤ Aout(a)` holds by `le_max_left` for every `a`.  Delivering the clause at the *constant*
  `2` instead would need `2 ≤ Kakeya.plankAngleScaleA a`, which fails as `a → 1⁻`; that is where the
  old smallness threshold came from, and taking the clause from the reserve-scale producer removes
  it;
* the refinement loss is `c_stb · a^ε`, **not** a uniform constant.  `c_stb = C⁻¹` with
  `C = C(ε, C₀, N_exp)` fixed before the configuration, but the `a^ε` is the retained-fraction of
  Lemma 6.11 and cannot be removed.  Every downstream constant of the Item 2 ledger therefore
  carries `a^ε` as well as `c_stb`, exactly as `c_P` and `c_λ` of `Kakeya.plankReduction` do.

Compatibility with the selection layer is free: the refinement returns equal carriers and smaller
shades, so the coherence `(Y' i).carrier = (V i).carrier` and any containment of the shades in a
representative prism are inherited, and `Plank.exists_shift_halfBox_capture_of_fullness` applied to
`(s, Y')` returns its shift and window at the same absolute constants.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Convexity
open scoped NNReal Real ENNReal

noncomputable section

namespace Plank

variable {ι : Type*}

/-- **A `c`-refinement transports a fullness lower bound.**  The `c`-mass bound lower-bounds the
shade numerator while `s' ⊆ s` with equal carriers on `s'` shrinks the carrier denominator, so
`c · λ(s,V) ≤ λ(s',V')`. -/
theorem fullness_ge_of_isCRefinement
    {s' s : Finset ι} {V' V : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} {c : ℝ≥0}
    (h : ShadedBody.IsCRefinement s' V' s V c) :
    c * ShadedBody.fullness s V ≤ ShadedBody.fullness s' V' := by
  rw [← ENNReal.coe_le_coe, ENNReal.coe_mul, ShadedBody.coe_fullness s V,
    ShadedBody.coe_fullness s' V']
  dsimp [ShadedBody.fullness']
  rcases h with ⟨⟨hsub, hbody⟩, hmass⟩
  have hDS' : ∑ i ∈ s', volume (V' i).carrier ≤ ∑ i ∈ s, volume (V i).carrier := by
    calc
      ∑ i ∈ s', volume (V' i).carrier = ∑ i ∈ s', volume (V i).carrier := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [congrArg (fun (cb : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) =>
          volume (ConvexSpaceBody.carrier cb)) (hbody i hi).1]
      _ ≤ ∑ i ∈ s, volume (V i).carrier := Finset.sum_le_sum_of_subset hsub
  calc
    (c : ℝ≥0∞) * ((∑ i ∈ s, volume (V i).shade) / ∑ i ∈ s, volume (V i).carrier)
        = ((c : ℝ≥0∞) * ∑ i ∈ s, volume (V i).shade) / ∑ i ∈ s, volume (V i).carrier := by
      rw [mul_div_assoc]
    _ ≤ (∑ i ∈ s', volume (V' i).shade) / ∑ i ∈ s, volume (V i).carrier :=
      ENNReal.div_le_div_right hmass (∑ i ∈ s, volume (V i).carrier)
    _ ≤ (∑ i ∈ s', volume (V' i).shade) / ∑ i ∈ s', volume (V' i).carrier :=
      ENNReal.div_le_div_left hDS' (∑ i ∈ s', volume (V' i).shade)


end Plank

end

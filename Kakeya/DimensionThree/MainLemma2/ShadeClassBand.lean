/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.AliveBand
public import Kakeya.DimensionThree.MainLemma1.OneSidedUniform

/-!
# The hereditary shade band, and the node count Definition 2.2 already brackets
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Real Metric
open Tube

namespace ShadedTube

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasureSpace E] [BorelSpace E] [ProperSpace E]
  {ι : Type*}

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- A member of the fibre of `x` lies in its own shade class. -/
theorem mem_shadeClass_self {δ : ℝ≥0} {s : Finset ι} {V : ι → ShadedTube δ E}
    (assign : ι → ι) {i : ι} (hi : i ∈ s) {x : E} (hxi : x ∈ (V i).shade) :
    i ∈ shadeClass s V assign (assign i) x := by
  classical
  simp only [shadeClass, coverClass, Finset.mem_filter]
  exact ⟨⟨hi, trivial⟩, hxi⟩

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- The shade class of a member of the fibre is nonempty. -/
theorem one_le_card_shadeClass_self {δ : ℝ≥0} {s : Finset ι} {V : ι → ShadedTube δ E}
    (assign : ι → ι) {i : ι} (hi : i ∈ s) {x : E} (hxi : x ∈ (V i).shade) :
    (1 : ℝ≥0) ≤ ((shadeClass s V assign (assign i) x).card : ℝ≥0) := by
  have : 1 ≤ (shadeClass s V assign (assign i) x).card :=
    Finset.card_pos.mpr ⟨i, mem_shadeClass_self assign hi hxi⟩
  exact_mod_cast this

/-! ### The node count Definition 2.2 already brackets -/

open scoped Classical in
omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- The fibre of `x` is the disjoint union, over the scale-`k` nodes it meets, of its shade
classes.  Restated as a cardinality identity. -/
theorem card_fibre_eq_sum_card_shadeClass [DecidableEq ι] {δ : ℝ≥0} {s : Finset ι}
    {V : ι → ShadedTube δ E} (assign : ι → ι) (x : E) :
    (s.filter (fun i => x ∈ (V i).shade)).card
      = ∑ j ∈ (s.filter (fun i => x ∈ (V i).shade)).image assign,
          (shadeClass s V assign j x).card := by
  classical
  rw [Finset.card_eq_sum_card_image assign (s.filter (fun i => x ∈ (V i).shade))]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  ext i
  simp only [shadeClass, coverClass, Finset.mem_filter]
  tauto

/-! ### What the `B ≡ 1` route costs: it is priced at the multiplicity -/

open scoped Classical in
omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- A shade class is contained in the fibre, so its cardinality is at most the pointwise
multiplicity.  This is the step by which a pointwise-multiplicity cut discharges the band
hypothesis of `nonempty_shadedUniformTubeSet_of_shadeClass_card_le`. -/
theorem card_shadeClass_le_pointwiseMultiplicity {δ : ℝ≥0} (s : Finset ι)
    (V : ι → ShadedTube δ E) (assign : ι → ι) (j : ι) (x : E) :
    (shadeClass s V assign j x).card
      ≤ ShadedBody.pointwiseMultiplicity s (fun i => (V i).toShadedBody) x := by
  classical
  refine Finset.card_le_card ?_
  intro i hi
  simp only [shadeClass, coverClass, Finset.mem_filter] at hi
  simpa [ShadedBody.pointwiseMultiplicity, Finset.mem_filter] using ⟨hi.1.1, hi.2⟩

/-! ### The class-density obligation is empty at every scale with small branching -/

/-! ### The alive band, in the shape clause (f) asks for -/

/-! ### (A) settled: the alive band cannot be rescued by a better cut -/

end ShadedTube

namespace ShadedBody

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

/-! ### …and the price is the theorem itself -/

end ShadedBody

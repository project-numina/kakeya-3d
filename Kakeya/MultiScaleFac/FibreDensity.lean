/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.FibreCommon
public import Kakeya.Frostman

/-!
# Counts, densities and Frostman constants of a single fibre

Every remaining geometric step of GWZ Lemma 7.7(A)
(`Kakeya.StickyKakeya.dividingScalesFrostman`) has the same three-layer shape:

1. a comparison of two *fibre counts*, supplied by uniformity
   (`Kakeya.MultiScaleFac.comparableFibreCounts_of_isUniformAtScale`,
   `Kakeya.MultiScaleFac.anchorGraded_of_isUniformAtScale`);
2. the passage from counts to *densities*, which is pure tube-volume bookkeeping;
3. the passage from densities to *Frostman constants*, which is division by the anchor density.

Layers 2 and 3 are identical in every one of those steps, so they are isolated here once and for
all.  The pivotal statement is `frostmanConstant_fibre_le_of_card_le`: a comparison of the two
fibre counts at anchors `ρ ≤ ρ'` immediately yields the comparison of the two Frostman constants,
with a loss depending only on the ambient dimension.  Both interpolation lemmas of
`Kakeya.MultiScaleFac.Interp` and both halves of a cut in `Kakeya.MultiScaleFac.Stopping` are
instances of it.

Every constant depends only on `Module.finrank ℝ E`; none depends on `δ`, so the blueprint's `⪅`
never appears.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Real Metric

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya
open scoped NNReal ENNReal

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ : ℝ≥0} {s : Finset ι} {T : ι → Tube δ E}

/-! ### The fibre as a family inside its own anchor -/

/-! ### Counts and densities -/


/-! ### Densities and Frostman constants -/


/-- Cross-multiplied comparison of two `ENNReal` quotients with nonzero finite denominators. -/
private theorem div_le_div_of_mul_le_mul {M N d e : ℝ≥0∞} (hd : d ≠ 0) (hd' : d ≠ ⊤)
    (he : e ≠ 0) (he' : e ≠ ⊤) (h : M * e ≤ N * d) : M / d ≤ N / e := by
  --
  rwa [ENNReal.le_div_iff_mul_le (Or.inl he) (Or.inl he'), div_eq_mul_inv, mul_right_comm,
    ← div_eq_mul_inv, ENNReal.div_le_iff hd hd']


/-! ### Thickening the members -/


/-! ### The sharp form, keeping the anchor-volume gain -/


/-! ### Two unconditional bounds on a fibre Frostman constant -/


end MultiScaleFac

end Kakeya

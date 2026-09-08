/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Shading
public import Kakeya.Mathlib.ENNReal

/-!
# Main Lemma 1, Case (ii): fullness thresholds

The three fullness lemmas of the reduction to the `b`-tubes, split out of
`Kakeya/DimensionThree/MainLemma1/Rescaling.lean` (blueprint
the Main Lemma 1 endgame, the subsection "Fullness thresholds"):

* `Kakeya.ml1Boot.le_fullness_of_termwise`;
* `Kakeya.ml1Boot.coarse_fullness_threshold`;
* `Kakeya.ml1Boot.fine_fullness_threshold`.

Nothing here is geometric: the statements are about `ShadedBody.fullness` and `ENNReal`
arithmetic only, and the shaded families enter through their carriers' volumes. That is why
they live in their own module — they are reusable at any scale and are the arithmetic
backbone of `Kakeya.ml1Boot.normalized_le_of_coarse`.

The two threshold lemmas carry their constant as a **free parameter** `≥ 1` rather than as
`Kakeya.ml1Boot.factorOneScale.C` / `Kakeya.ml1Boot.fineFactor.C`, because the dilate chain
needs them at the larger constants `Kakeya.ml1Boot.factorOneScaleUniformDilate.C` and
`Kakeya.ml1Boot.fineNormalizeDilate.C c`, and neither instance follows from the one at the
smaller constant. Carrying the constant free is also what lets the dilation ratio `c` stay free
in the fine chain: these lemmas never see it. See blueprint `note:ml1bootArithFreeConstant`.
-/

@[expose] public section

open scoped ENNReal

open MeasureTheory ShadedBody

namespace Kakeya

namespace ml1Boot

section Thresholds

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **A termwise density bound passes to every subfamily**.

If every member of a shaded family satisfies `λ₀ |V i| ≤ |Z i|` and the carriers have positive
finite volume, then *every* nonempty subfamily has fullness at least `λ₀`.

The hypothesis is termwise and that is the whole content: a lower bound on `λ(𝕍, Z)` alone
would not pass to a subfamily, fullness being a ratio of two sums.  This is why
`Kakeya.ml1Boot.exists_factorOneScaleUniform`(a) and (b) are stated with two-sided densities
rather than with a fullness bound.  It is the sibling of
`ShadedBody.le_fullness_of_volume_le`. -/
theorem le_fullness_of_termwise {ι : Type*} {s : Finset ι} (V : ι → ShadedBody E)
    {lam₀ : ℝ≥0∞}
    (hpos : ∀ i ∈ s, 0 < volume (V i).carrier)
    (hfin : ∀ i ∈ s, volume (V i).carrier ≠ ⊤)
    (hterm : ∀ i ∈ s, lam₀ * volume (V i).carrier ≤ volume (V i).shade)
    {S : Finset ι} (hSs : S ⊆ s) (hS : S.Nonempty) :
    lam₀ ≤ (ShadedBody.fullness S V : ℝ≥0∞) := by
  have hposOnS : ∀ i ∈ S, 0 < volume (V i).carrier := fun i hi => hpos i (hSs hi)
  have hfinOnS : ∀ i ∈ S, volume (V i).carrier ≠ ⊤ := fun i hi => hfin i (hSs hi)
  have hsum : lam₀ * (∑ i ∈ S, volume (V i).carrier) ≤ ∑ i ∈ S, volume (V i).shade := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i hi => hterm i (hSs hi))
  have hDne0 : (∑ i ∈ S, volume (V i).carrier) ≠ 0 := by
    intro hzero
    rcases hS with ⟨i, hi⟩
    exact (ne_of_gt (hposOnS i hi)) ((Finset.sum_eq_zero_iff.mp hzero) i hi)
  have hDneTop : (∑ i ∈ S, volume (V i).carrier) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr hfinOnS
  rw [ShadedBody.fullness_def]
  exact (ENNReal.le_div_iff_mul_le (Or.inl hDne0) (Or.inl hDneTop)).2 hsum

end Thresholds

end ml1Boot

end Kakeya

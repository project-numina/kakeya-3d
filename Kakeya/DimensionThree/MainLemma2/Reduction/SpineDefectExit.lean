/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.FibreCommon
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineDefectConstantLedger

/-!
# `P6` — the `(D)` exit: a destroyed lower concentration is a potential drop

GWZ, , verbatim:

```
 If a required lower concentration fails after the restrictions, then for one m ∈ W the old value
 is larger than ½Θ_m^τ, while the new value is smaller than ½Θ_m^{τ/2}.  Hence
   d_{a,m}(S') − d_{a,m}(S*) ≥ τε²/4 ≥ 2h.
 Every other D_{k,l} is monotone under restriction, so the corresponding ceiling drops by at
 least one and no other ceiling increases.  This is (D).
```

together with `log Θ_m / log(1/δ) ≥ ε²/2` and `h = η₁ε²/8`.

## The alignment `D-R1`, and why it works — the first item, as a named lemma

 names the risk: the source's two concentration bounds are on
`Δ_max(𝕊_m⟨S⟩)`, the **assignment fibre**, whereas `Kakeya.ML2Core.pairProfile` is on
**footprints**.  The upper bound transfers downwards for free; the lower bound is the direction
that needs work.

The resolution is `Kakeya.ML2Core.pairProfile_ambient`: **on the ambient family the two objects are
literally equal.**  Every node of the hierarchy is occupied — that is
`Kakeya.MultiScaleFac.coverClass_nonempty_of_mem_parent`, which is exactly where Definition
2.1(iii)'s lower half earns its keep — so `footprint 𝒰 u l = 𝒰.cover.indexSet l` and the level-`l`
footprint under a level-`a` node **is** `Tube.UniformTubeSet.nodesUnder`.  Hence
`Kakeya.ML2Core.le_mul_pairProfile_of_level_clause`: the window's own level clause, which is stated
on `nodesUnder` (`ML2Reduction.IsKatzTaoDividingWindowLevels.le_level_maxDensity`, the containment
form `W1`), gives the *before* bound on `pairProfile` directly.  That is the source's reading — the
lower concentration is tested **before** the restrictions — and it is why the order of 
is essential.

## The arithmetic, and a measurement the source's sketch leaves implicit

Writing `L = log(1/δ)`, `A = ½Θ^{τ/2}` and `B = ½Θ^τ`,

```
 log A / L + 2h ≤ log B / L    ⟺    2h ≤ (τ/2)·(log Θ / L),
```

because **`log 2` occurs on both sides and cancels**.  So the trigger costs *no* `δ`-threshold at
all: with `log Θ / L ≥ ε²/2` the requirement is `2h ≤ τε²/4`, which is the source's own inequality
and is exactly `h = η₁ε²/8` together with `τ = η_{J+1} ≥ η₁`.  The factor `½` — which one would
expect to have to absorb — is free.

## Contents

* the alignment: `footprint_ambient`, `pairProfile_ambient`, `le_mul_pairProfile_of_level_clause`;
* the arithmetic: `profileExp_drop_of_bounds`;
* the descent step: `potential_drop_of_profileExp_drop`;
* **the exit: `profileDrop_of_concentration_destroyed`.**
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric ConvexSpaceBody

namespace Kakeya.ML2Core

/-! ## `D-R1`: the footprint profile at the ambient family is the source's `D_{k,l}` -/

section Alignment

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ Cu : ℝ≥0} {u : Finset ι} {T : ι → Tube δ E}

end Alignment

/-! ## The arithmetic of the trigger -/

section Arithmetic

variable {δ : ℝ≥0}

/-- **The normalized profile drops by `2h`.**

`x` is the profile before the restrictions, bounded below by `B`; `y` is the profile after, bounded
above by `A`; `hgap` is the source's `d(S') − d(S*) ≥ 2h` written on the two bounds.  Both `A` and
`B` are asked to be at least `1` because `d` is `log max{1, ·}`. -/
theorem profileExp_drop_of_bounds (hδ0 : 0 < δ) (hδ1 : δ < 1) {x y : ℝ≥0∞}
    (hx : x ≠ ⊤) (hy : y ≠ ⊤) {A B h : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hbefore : ENNReal.ofReal B ≤ x) (hafter : y ≤ ENNReal.ofReal A)
    (hgap : Real.log A / Real.log (1 / (δ : ℝ)) + 2 * h
      ≤ Real.log B / Real.log (1 / (δ : ℝ))) :
    profileExp δ y + 2 * h ≤ profileExp δ x := by
  have hL : 0 < Real.log (1 / (δ : ℝ)) := log_one_div_pos hδ0 hδ1
  -- the after bound
  have hyA : Real.log (max 1 y.toReal) ≤ Real.log A := by
    have hyR : y.toReal ≤ A := ENNReal.toReal_le_of_le_ofReal (le_trans zero_le_one hA) hafter
    exact Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (max_le hA hyR)
  -- the before bound
  have hxB : Real.log B ≤ Real.log (max 1 x.toReal) := by
    have hxR : B ≤ x.toReal := (ENNReal.ofReal_le_iff_le_toReal hx).mp hbefore
    exact Real.log_le_log (lt_of_lt_of_le zero_lt_one hB) (le_trans hxR (le_max_right _ _))
  rw [profileExp_of_ne_top hx, profileExp_of_ne_top hy]
  have h1 : Real.log (max 1 y.toReal) / Real.log (1 / (δ : ℝ))
      ≤ Real.log A / Real.log (1 / (δ : ℝ)) := div_le_div_of_nonneg_right hyA hL.le
  have h2 : Real.log B / Real.log (1 / (δ : ℝ))
      ≤ Real.log (max 1 x.toReal) / Real.log (1 / (δ : ℝ)) := div_le_div_of_nonneg_right hxB hL.le
  linarith

end Arithmetic

/-! ## The descent step -/

section Step

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ Cu : ℝ≥0} {u : Finset ι} {T : ι → Tube δ E}

end Step

/-! ## The `(D)` exit -/

section Exit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ Cu : ℝ≥0} {u : Finset ι} {T : ι → Tube δ E}

end Exit

/-! ## Non-vacuity of the trigger -/

section NonVacuity

end NonVacuity

end Kakeya.ML2Core

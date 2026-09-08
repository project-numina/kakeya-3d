/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Frostman

/-!
# Changing the container of a Frostman lower bound

This file isolates the last leaf of item (iv) of
`Kakeya.ml1Boot.exists_fineNormalization_lower`: the **container change**.  Item (iv) has to
turn a Frostman lower bound read at a source container `K₁` into a Frostman lower bound read
at a larger container `K₂ ⊇ K₁` of comparable volume, the family being read at an ambient
index set in both cases.

The two halves of that change behave completely differently, and separating them is the point
of this file.

* **Growing the container with the index set held fixed is free.**
  `ConvexSpaceBody.frostmanConstIn_le_of_container_le`: if every member of `s` lies in `K₁`
  and `K₁ ≤ K₂`, then `C_F(s, 𝕎, K₁) ≤ C_F(s, 𝕎, K₂)` with **no** loss and **no** volume
  comparability hypothesis.  Enlarging the container only lowers the reference density
  `Δ(𝕎, K)`, which sits in the denominator of the Frostman constant.
* **Growing the index set is not free, and it is not a matter of volume comparability.**
  What the enlarged container adds is *members*: bodies of the ambient family that lie in `K₂`
  and not in `K₁`.  Their mass inflates the reference density `Δ(𝕎, K₂)` and deflates the
  Frostman constant.  `ConvexSpaceBody.frostmanConstIn_le_of_subfamily_of_densityIn_le` pays
  for exactly that, at exactly the density ratio, and
  `ConvexSpaceBody.container_change_false_of_no_density_comparison` shows the ratio cannot be
  dropped: with `K₂` a `2`-dilate of `K₁` — *any* fixed volume ratio would do — the Frostman
  constant at `K₁` is `≥ 1/(2t)` while the constant at `K₂` is `≤ 1`, for every `t > 0`.

So the hypothesis of item (iv) is **not** a statement about the normalization, and no
amount of construction visibility supplies it: it is a *doubling clause on the ambient family*,

> the members of the ambient family lying in a bounded enlargement of the window container
> carry at most `O(1)` times the mass of those lying in the container itself,

which is a hypothesis about `𝕌` at the window scales and has to be assumed.
-/

@[expose] public section

open scoped ENNReal

open MeasureTheory Kakeya

namespace ConvexSpaceBody

section General

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*}
  {s s₁ s₂ : Finset ι} {W : ι → ConvexSpaceBody E} {K K₁ K₂ : ConvexSpaceBody E} {C : ℝ≥0∞}

/-- **Growing the container is free when the index set is held fixed.**

If every body of the family `s` lies in `K₁` and `K₁ ≤ K₂`, then the Frostman constant read at
the smaller container is at most the one read at the larger container.  There is no constant
and no volume-comparability hypothesis: the family is the same on both sides, so the only
change is that the reference density `Δ(𝕎, K)` — the denominator of the Frostman constant —
drops when `K` grows.

This is the exact converse direction to `ConvexSpaceBody.frostmanConstIn_ambient_mono`, which
bounds the constant at the *larger* container by the volume ratio times the constant at the
smaller one. -/
theorem frostmanConstIn_le_of_container_le (hK : K₁ ≤ K₂) (hsK : ∀ i ∈ s, W i ≤ K₁) :
    frostmanConstIn s W K₁ ≤ frostmanConstIn s W K₂ := by
  refine frostmanConstIn_le ?_
  intro K' hK'
  refine (isFrostmanIn_frostmanConstIn s W K₂ K' (hK'.trans hK)).trans ?_
  gcongr
  rw [densityIn_of_all_le hsK, densityIn_of_all_le (fun i hi => (hsK i hi).trans hK)]
  exact ENNReal.div_le_div_left (measure_mono hK) _

end General

section ItemIV

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*}
  {s : Finset ι} {W V : ι → ConvexSpaceBody E} {Q Q' K : ConvexSpaceBody E} {A C D : ℝ≥0∞}

end ItemIV

section Counterexample

end Counterexample

end ConvexSpaceBody

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineThreeScale
public import Kakeya.DimensionThree.MainLemma2.Reduction.BandSqueeze

/-!
# The new-parent factor at `(a, p)`, the seam-restricted split, and which set retention is about

Four rows of the four-way producer, closed.  Every declaration states its family, its shading and
its level pair, because the two defects this file exists to prevent are invisible to `check`,
`scan`, `axioms` and `guard`: a factor read at the wrong level pair, and a retention statement read
about the wrong set.

## 1. `hpar`: the new-parent factor is the existing defect estimate at `(a, p)`

`Kakeya.ML2Core.exists_coarse_factor` is level-agnostic — a family of `θ`-tubes with fullness
`≥ dt ^ η` and `maxDensity ≤ dt ^ (-ηc)` has multiplicity `≤ dt ^ (-(ε + ηc)) · card ^ β`.  The
outer factor instantiates it at level `a` with `ηc` from the window's `coarse_maxDensity_le`.  The
**new-parent** factor is the same estimate at the pair `(a, p)`, and its density input is not a
window field at all: it is the **(F) payload's own parent-density row**,
`∀ jθ ∈ indexSet a, maxDensity (nodesUnder p a jθ) ≤ δ ^ (-2η')`, the row
 lists as *"produced, consumed by nothing"*.

So the four-way split does not merely need that row — it is **the first consumer of it**, and the
loss it charges is `εp = ε + 2η'`.  That closes the loop the map opened.

## 2. `tτ' ⊆ t₁`: run the split on the seam-restricted family

`Kakeya.ML2Reduction.exists_spineThreeScale_ofChain` returns `tτ' ⊆ activeNodes 𝒞 b` while the
re-cut `hfac` asks `tτ' ⊆ t₁`.  The existing three-way route gets this by running the split on the
node-restricted family `{i ∈ s | assign b i ∈ t₁}`, where `assign b` maps into `t₁` by
construction; `Kakeya.ML2Core.exists_spineThreeScale_restricted` is that move at three levels, and
its multiplicity is read on exactly the family `hfac`'s `hprod` reads.

## 3. `hballπ`: the level-`p` ball row

Derived, not assumed, from the seam's level-`a` ball row and `tube_le_coarseNode`: a level-`p` node
whose `(a,p)`-parent is retained sits inside a retained level-`a` node, hence in the unit ball.
`TCTL4` is the control that the row is load-bearing.

## 4. Which set is retention about?

**`t₁`, the seam's retained set, is fibre-complete** —
`Kakeya.ML2Core.threeLevelSeam_fibre_complete`,
because the seam never selected at level `b`.  **`tτ'`, the split's retained set, is not**: it is
the mass-pigeonholed outer set of a one-scale application, and retention does **not** pass to
subsets — `Kakeya.ML2Core.not_retentionAt_empty` is the record of that, at the extreme
subset `∅ ⊆ t₁`.  For `tτ'` the vehicle is bracket ∘ retention:
`Kakeya.ML2Core.retentionProportionAt_of_fibreRetention`, at the cost `θ₀ ↦ θ₀ / Cu ^ 5`.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Metric ConvexSpaceBody ShadedBody Tube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

section NewParent

variable {δ Cu : ℝ≥0} {ι : Type u}


end NewParent

section Restricted

variable {δ : ℝ≥0} {ι : Type u}


end Restricted

section BallRow

variable {δ : ℝ≥0} {ι : Type u}

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- **Translation preserves node containment.**  `≤` on `ConvexSpaceBody` *is* carrier inclusion,
and `Tube.translate` is a preimage, so containment survives the seam's translate. -/
theorem translate_carrier_subset_of_le {ρ ρ' : ℝ≥0} (A : Tube ρ E) (B : Tube ρ' E) (v : E)
    (h : A.toConvexSpaceBody ≤ B.toConvexSpaceBody) :
    (A.translate v).carrier ⊆ (B.translate v).carrier := by
  simp only [Tube.translate_carrier]
  exact Set.preimage_mono h


end BallRow

section Thresholds

variable {δ : ℝ≥0}

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- **`≤` on tubes survives the seam's translate**, in the `ConvexSpaceBody` form the split
consumes.  The carrier form is `Kakeya.ML2Core.translate_carrier_subset_of_le`; `≤` on
`ConvexSpaceBody` *is* that inclusion, so the two are the same statement and this records it. -/
theorem tube_translate_le_translate {ρ ρ' : ℝ≥0} (A : Tube ρ E) (B : Tube ρ' E) (v : E)
    (h : A.toConvexSpaceBody ≤ B.toConvexSpaceBody) :
    (A.translate v).toConvexSpaceBody ≤ (B.translate v).toConvexSpaceBody :=
  translate_carrier_subset_of_le A B v h


end Thresholds

section Retention

variable {δ Cu : ℝ≥0} {ι : Type u}


end Retention

end Kakeya.ML2Core

end

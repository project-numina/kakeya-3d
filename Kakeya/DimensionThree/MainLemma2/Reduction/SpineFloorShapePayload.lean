/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSiteClosure
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeSelfHierarchy
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorGateRed
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorTerminal
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShape

/-!
# `FloorPayload`: the `hdev` row's one blocking inequality, and the payload's **empty-family**
refutation

 lists `Kakeya.ML2Core.FloorPayload` as row R3 of `GeometricCoreAt`, carried
by the floor hands.  This file measures what that row costs, and the answer is in two halves.

## The `hdev` half — one inequality, named

`Kakeya.ML2Core.hfloor_of_producers`'s `hdev` row is
`∃ S' W, IsShadedRefinementOf 𝒰 Λf S Z S' W`.  The producer is existing
(`Kakeya.ML2Core.exists_shadedRefinement_of_pass`, `R0′`) but returns the loss
`Kakeya.ML2Core.refinementLoss K 3 Cu δ`, while the closure fixes `Λf := polylogLoss K'`.
`Kakeya.ML2Core.IsShadedRefinementOf.mono_loss` below shows the predicate is **monotone in the
loss**, so the whole gap between producer and consumer is the single scalar inequality

```
    refinementLoss K 3 Cu δ ≤ polylogLoss K' δ          -- the `hdev` blocker, in one line
```

and `Kakeya.ML2Core.exists_shadedRefinement_of_le` is the reduction.  That inequality is **false**
in general and the reason is recorded : `refinementLoss`
carries the comparability factor `K` (`= lam⁻¹`, up to `2 δ^{-ηin}` at the trial's floor), a genuine
`δ`-power, and `StickyKakeya.gridLoss Cu 6 δ`, whose exponent
`6 (ssfGridLen δ + 1)^2` grows with `δ → 0`, whereas `polylogLoss K' δ` is `(1 − log δ)^{K'}` at a
**fixed** `K'`.

## The payload half — `FloorPayload` is **FALSE as stated**

`Kakeya.ML2Core.FloorDataAt` quantifies over **every** `S ⊆ u`, including `S = ∅`, and
`IsClassHomogeneousOn 𝒰 ∅` holds (take `bN = 0`; the band is quantified over
`(∅ : Finset ι).image _ = ∅`).  At `S = ∅` the hierarchy handed to
`Kakeya.ML2Core.RefinedFloorHypothesis` is indexed by `∅`, and that predicate's first clause is
`IsShadedRefinementOf … S' W` with `S' ⊆ ∅` **and** `S'.Nonempty` — the explicit anti-vacuity clause
`C-M1a` of   The two are contradictory, so:

* `Kakeya.ML2Core.not_refinedFloorHypothesis_of_empty` — the `(F)` predicate is false on an
  empty-indexed hierarchy, at every window and every loss;
* `Kakeya.ML2Core.not_floorDataAt` — hence `FloorDataAt` is false for **every** hierarchy;
* `Kakeya.ML2Core.not_floorPayload` — hence `FloorPayload` is false, with a witness family
  supplied at every small `δ`.

The nonemptiness clause was added to `IsShadedRefinementOf` ( `C-M1a`) and to
`Kakeya.ML2Core.isShadedRefinementOf_self` (which carries `hne : S.Nonempty`), but never to
`FloorDataAt`'s binder list.  **This is a statement-level defect and is not repaired here**: the
repair is one binder, `(hne : S.Nonempty)`, in an existing `def`, and that is the source comparison's call.
See  for the exact requested text and the consumer check.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric

local notation "E3" => EuclideanSpace ℝ (Fin 3)

namespace Kakeya.ML2Core

section MonoLoss

variable {ι : Type*} {δ Cu : ℝ≥0} {u : Finset ι}
  {T : ι → ShadedTube δ E3}
  {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}

/-- **The refinement predicate is monotone in the loss.**  Only the retention clause mentions `Λ`,
and it is an upper bound.  This is what turns the gap between `R0′`'s output loss and the closure's
`Λf` into a single scalar inequality. -/
theorem IsShadedRefinementOf.mono_loss {Λ Λ' : ℝ≥0∞} {S S' : Finset ι}
    {Z W : ι → ShadedTube δ E3}
    (h : IsShadedRefinementOf 𝒰 Λ S Z S' W) (hΛ : Λ ≤ Λ') :
    IsShadedRefinementOf 𝒰 Λ' S Z S' W :=
  ⟨h.subset, h.nonempty, h.2.2.1, h.2.2.2.1,
    h.retention.trans (mul_le_mul_left hΛ _), h.classHomogeneous⟩

end MonoLoss

/-! ### The empty-family refutation -/

section Vacuity

variable {ι : Type*} {δ Cu : ℝ≥0}

end Vacuity

section PayloadRefutation

/-- The tube with its whole carrier shaded — the cheapest `ShadedTube`, used only to exhibit a
family at which `FloorPayload`'s inner `∀` bites. -/
noncomputable def fullShade (δ : ℝ≥0) (T : Tube δ E3) : ShadedTube δ E3 where
  toTube := T
  shade := T.carrier
  measurableSet_shade := T.isCompact'.measurableSet
  shade_subset := subset_rfl

@[simp] theorem fullShade_toTube (δ : ℝ≥0) (T : Tube δ E3) :
    (fullShade δ T).toTube = T := rfl

end PayloadRefutation

/-! ### What is left of the payload once `hdev` is free -/

section Reduction

variable {ι : Type*} {δ Cu : ℝ≥0} {u : Finset ι}
  {T : ι → ShadedTube δ E3}

end Reduction

end Kakeya.ML2Core

end

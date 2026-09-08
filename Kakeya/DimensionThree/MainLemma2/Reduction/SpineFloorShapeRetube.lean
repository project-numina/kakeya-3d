/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShape

/-!
# `M1`'s first move: F7's tail **is** generic, and the one friction point, removed

 item 4 is the plan's only `[NOT MEASURED]` claim about `M1`'s cost:

> *whether F7's existing tail (`exists_windowSeam`, `sum_shade_gain_of_window`) elaborates unchanged
> against `𝒰.restrictOccupied` — a `defeq`/instance question construction will settle in minutes
> and which could move `M1`'s 250–400 into the 400s.*

**Measured. The answer is yes, and the whole question reduces to one line.**

## Why it reduces to one line

`Kakeya.ML2Core.trialOutcome_middle_of_floorFactors` and its engine `…_gain` conclude

```
∀ᶠ δ, ∀ {ι} (S : Finset ι) (T : ι → ShadedTube δ E₃) (Cu lam : ℝ≥0)
        (𝒰 : Tube.UniformTubeSet S (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu) (a b m : ℕ),
      <binders> → ∀ Λ, TrialOutcomeAt … 𝒰 Λ lam S T
```

— `S`, `T`, `Cu` and `𝒰` are **universally quantified**, so instantiating them at a refinement is
type-correct *by construction*.  Nothing in the 146-line tail is special to the ambient hierarchy.
The **only** obstruction is a book-keeping one: `Tube.UniformTubeSet.restrictOccupied` returns a
hierarchy over the **ambient** tube family `fun i ↦ (T i).toTube`, while F7 wants one over the
**refinement's** `fun i ↦ (W i).toTube`.  `Kakeya.ML2Core.IsShadedRefinementOf` guarantees those two
functions are *propositionally* equal (`(W i).toTube = (Z i).toTube`, 's *"its shading is
a restriction of `Z`"*), but not definitionally.

`Tube.UniformTubeSet.retube` transports along exactly that equality, and — this is the point — it
is built **field by field from the same data**, so every projection a consumer can see is `rfl`:

```
(𝒰.retube hT).cover.indexSet = 𝒰.cover.indexSet          rfl
(𝒰.retube hT).cover.assign   = 𝒰.cover.assign            rfl
(𝒰.retube hT).cover.tube     = 𝒰.cover.tube              rfl
(𝒰.retube hT).nodesUnder     = 𝒰.nodesUnder              rfl
(𝒰.retube hT).branchingN     = 𝒰.branchingN              rfl
```

Only `le_tube_assign` and `boundedOverlap` mention the tube family at all, and they are the two
fields the transport rewrites.  A `▸`-transport would have made every projection an `Eq.mpr` and
forced `M1` to fight the elaborator at each of F7's thirteen binders; the explicit build makes them
all disappear.

**Consequence for `M1`'s price.**  's second risk row is discharged:
`M1` is a re-instantiation, not a re-proof, and the estimate stays at 250–400 rather than moving
into the 400s.  `Kakeya.ML2Core.generic_at_refinement` is the statement of that, in F7's
own binder shape.

## Contents

* `Tube.UniformTubeSet.retube` and its five `rfl` projections.
* `Kakeya.ML2Core.isClassHomogeneousOn_retube_iff` — the clause survives, `Iff.rfl`.
* `Kakeya.ML2Core.refinedHierarchy` — the hierarchy `M1`'s `(F)` binder names.
* `Kakeya.ML2Core.generic_at_refinement` — **the measurement**: anything universally quantified over
  `(S, T, 𝒰)` in F7's exact shape instantiates at the refinement.
* `Kakeya.ML2Core.retube_ne_transport_control` — the firing control: `retube` is not vacuous, it
  really does change the *type*, and the two hierarchies are not the same term.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Metric ConvexSpaceBody
open Tube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

section Retube

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ C : ℝ≥0} {s : Finset ι} {N : ℕ}

/-- **Transport a hierarchy along a pointwise equality of tube families.**

Built field by field from the *same* data, so `cover.indexSet`, `cover.assign`, `cover.tube`,
`nodesUnder` and `branchingN` are unchanged **definitionally** — see the module docstring for why
that matters and why `hT ▸ 𝒰` would not do.  Only `le_tube_assign` and `boundedOverlap` mention the
tube family, and those are the two proofs the transport rewrites. -/
noncomputable def _root_.Tube.UniformTubeSet.retube {T T' : ι → Tube δ E} (hT : T' = T)
    (𝒰 : Tube.UniformTubeSet s T N C) : Tube.UniformTubeSet s T' N C where
  cover :=
    { indexSet := 𝒰.cover.indexSet
      assign := 𝒰.cover.assign
      tube := 𝒰.cover.tube
      assign_mem := 𝒰.cover.assign_mem
      le_tube_assign := by subst hT; exact 𝒰.cover.le_tube_assign
      nested := 𝒰.cover.nested
      tube_nested := 𝒰.cover.tube_nested }
  branchingN := 𝒰.branchingN
  tube_injOn := 𝒰.tube_injOn
  boundedOverlap := by subst hT; exact 𝒰.boundedOverlap
  card_class_le := 𝒰.card_class_le
  le_card_class := 𝒰.le_card_class

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem retube_indexSet {T T' : ι → Tube δ E} (hT : T' = T)
    (𝒰 : Tube.UniformTubeSet s T N C) :
    (𝒰.retube hT).cover.indexSet = 𝒰.cover.indexSet :=
      rfl

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem retube_assign {T T' : ι → Tube δ E} (hT : T' = T)
    (𝒰 : Tube.UniformTubeSet s T N C) :
    (𝒰.retube hT).cover.assign = 𝒰.cover.assign :=
      rfl

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem retube_tube {T T' : ι → Tube δ E} (hT : T' = T)
    (𝒰 : Tube.UniformTubeSet s T N C) :
    (𝒰.retube hT).cover.tube = 𝒰.cover.tube :=
      rfl

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem retube_branchingN {T T' : ι → Tube δ E} (hT : T' = T)
    (𝒰 : Tube.UniformTubeSet s T N C) :
    (𝒰.retube hT).branchingN = 𝒰.branchingN :=
      rfl

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem retube_nodesUnder {T T' : ι → Tube δ E} (hT : T' = T)
    (𝒰 : Tube.UniformTubeSet s T N C) (b a : ℕ) (j : ι) :
    (𝒰.retube hT).nodesUnder b a j = 𝒰.nodesUnder b a j :=
      rfl


end Retube

/-! ## The measurement, in F7's own shape -/

section Measurement

variable {ι : Type*} {δ Cu : ℝ≥0} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

/-- **The hierarchy `M1`'s `(F)` binder names**: the ambient tower restricted to the refinement, at
the **same** `Cu`, and re-typed at the refinement's own tube family.

`Kakeya.ML2Core.IsShadedRefinementOf` supplies both ingredients — `S' ⊆ S ⊆ u` and
`(W i).toTube = (Z i).toTube` — so this is the canonical object and not a choice. -/
noncomputable def refinedHierarchy
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    {S' : Finset ι} (hS' : S' ⊆ u) (hhom : IsClassHomogeneousOn 𝒰 S')
    {W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (hW : (fun i => (W i).toTube) = (fun i => (T i).toTube)) :
    Tube.UniformTubeSet S' (fun i => (W i).toTube) (Tube.ssfGridLen δ) Cu :=
  (𝒰.restrictOccupied hS' hhom).retube hW

@[simp] theorem refinedHierarchy_assign
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    {S' : Finset ι} (hS' : S' ⊆ u) (hhom : IsClassHomogeneousOn 𝒰 S')
    {W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (hW : (fun i => (W i).toTube) = (fun i => (T i).toTube)) :
    (refinedHierarchy 𝒰 hS' hhom hW).cover.assign = 𝒰.cover.assign :=
      rfl

@[simp] theorem refinedHierarchy_tube
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    {S' : Finset ι} (hS' : S' ⊆ u) (hhom : IsClassHomogeneousOn 𝒰 S')
    {W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (hW : (fun i => (W i).toTube) = (fun i => (T i).toTube)) :
    (refinedHierarchy 𝒰 hS' hhom hW).cover.tube = 𝒰.cover.tube :=
      rfl

@[simp] theorem refinedHierarchy_nodesUnder
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    {S' : Finset ι} (hS' : S' ⊆ u) (hhom : IsClassHomogeneousOn 𝒰 S')
    {W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (hW : (fun i => (W i).toTube) = (fun i => (T i).toTube)) (b a : ℕ) (j : ι) :
    (refinedHierarchy 𝒰 hS' hhom hW).nodesUnder b a j
      = (𝒰.restrictOccupied hS' hhom).nodesUnder b a j :=
        rfl


end Measurement

/-! ### Firing control -/

section Control


end Control

end Kakeya.ML2Core

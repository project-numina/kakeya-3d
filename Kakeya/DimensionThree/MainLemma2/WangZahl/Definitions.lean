/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

/-
Source-faithful definitions for Wang--Zahl, Definition 1.5.

Source: Wang--Zahl, Definition 1.5 (`defnCDE`).
-/

public import Kakeya.PartialEstimates
public import Kakeya.Mathlib.Analysis.AffineSubspace

/-!
# Wang--Zahl Definition 1.5: source-faithful definitions

The ambient `Kakeya.WangZahl.Space3`, the test sets `ConvexTestSet`, `Hyperplane3` and
`SlabTestSet`, the model tube `modelTube` and its volume `tubeVolume`, and the canonical
Wolff constants `katzTaoConvexWolffConstant` and `frostmanSlabWolffConstant` as infima over
admissible `C`. `IsTubeShadingFamily` and `IsDense` encode the source's `(T,Y)_delta` and
`lambda`-density conventions, and `AssertionD`, `AssertionE` state Assertions `D(sigma, omega)`
and `E(sigma, omega)` quantified over every positive scale. Everything in `WangZahl/` builds on
these.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory

namespace Kakeya.WangZahl

noncomputable section

universe u

/-- The ambient space in Wang--Zahl Definition 1.5. -/
abbrev Space3 := EuclideanSpace ℝ (Fin 3)

/-- A convex test set in `R^3`.

Unlike `ConvexSpaceBody`, the source does not require the test set to be
nonempty, compact, or bounded. -/
structure ConvexTestSet where
  carrier : Set Space3
  convex_carrier : Convex ℝ carrier

/-- A hyperplane in `R^3`, represented as an affine subspace of affine
dimension two. -/
structure Hyperplane3 where
  carrier : AffineSubspace ℝ Space3
  nonempty_carrier : (carrier : Set Space3).Nonempty
  finrank_direction : Module.finrank ℝ carrier.direction = 2

/-- A slab in the sense immediately preceding Wang--Zahl Definition 1.5:
the intersection of the unit ball with a closed thickened neighbourhood of a
hyperplane. -/
structure SlabTestSet where
  plane : Hyperplane3
  thickness : ℝ≥0

/-- The underlying subset of a Wang--Zahl slab. -/
def SlabTestSet.carrier (W : SlabTestSet) : Set Space3 :=
  Metric.closedBall 0 1 ∩ Metric.cthickening (W.thickness : ℝ) W.plane.carrier

/-- A fixed model `delta`-tube, used only to give literal meaning to the
common tube volume `|T|` in Definition 1.5. -/
def modelTube (δ : ℝ≥0) : Tube δ Space3 :=
  Tube.mk' δ (x := 0) (y := EuclideanSpace.single 0 (1 : ℝ)) (by
    rw [dist_zero_left, PiLp.norm_single, norm_one])

/-- The common volume `|T|` of a `delta`-tube in `R^3`. -/
def tubeVolume (δ : ℝ≥0) : ℝ≥0∞ := volume (modelTube δ).carrier

/-- The canonical Katz--Tao convex Wolff constant from the definition
immediately preceding Wang--Zahl Definition 1.5.

It is the infimum over positive `C` for which the stated counting estimate
holds for every convex subset of `R^3`. -/
noncomputable def katzTaoConvexWolffConstant {δ : ℝ≥0} {ι : Type u}
    (s : Finset ι) (T : ι → ShadedTube δ Space3) : ℝ≥0∞ :=
  @sInf ℝ≥0∞ _
    {C : ℝ≥0∞ | 0 < C ∧ ∀ W : ConvexTestSet,
      ((@Finset.filter ι (fun i => (T i).carrier ⊆ W.carrier)
        (Classical.decPred _) s).card : ℝ≥0∞) ≤
        C * volume W.carrier * (tubeVolume δ)⁻¹}

/-- The canonical Frostman slab Wolff constant from the definition
immediately preceding Wang--Zahl Definition 1.5.

It is the infimum over positive `C` for which the stated counting estimate
holds for every slab. -/
noncomputable def frostmanSlabWolffConstant {δ : ℝ≥0} {ι : Type u}
    (s : Finset ι) (T : ι → ShadedTube δ Space3) : ℝ≥0∞ :=
  @sInf ℝ≥0∞ _
    {C : ℝ≥0∞ | 0 < C ∧ ∀ W : SlabTestSet,
      ((@Finset.filter ι (fun i => (T i).carrier ⊆ W.carrier)
        (Classical.decPred _) s).card : ℝ≥0∞) ≤
        C * volume W.carrier * (s.card : ℝ≥0∞)}

/-- The source convention `(T,Y)_delta`: a finite family of essentially
distinct shaded `delta`-tubes, all contained in the unit ball. Measurability of
each shading and the inclusion `Y(T) subset T` are bundled in `ShadedTube`. -/
def IsTubeShadingFamily {δ : ℝ≥0} {ι : Type u}
    (s : Finset ι) (T : ι → ShadedTube δ Space3) : Prop :=
  (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) ∧
    (s : Set ι).Pairwise fun i j =>
      IsEssentiallyDistinct (T i).carrier (T j).carrier

/-- The source's `lambda`-density condition for `(T,Y)_delta`. -/
def IsDense {δ : ℝ≥0} {ι : Type u}
    (s : Finset ι) (T : ι → ShadedTube δ Space3) (density : ℝ≥0) : Prop :=
  (density : ℝ≥0∞) * ∑ i ∈ s, volume (T i).carrier ≤
    ∑ i ∈ s, volume (T i).shade

end

end Kakeya.WangZahl

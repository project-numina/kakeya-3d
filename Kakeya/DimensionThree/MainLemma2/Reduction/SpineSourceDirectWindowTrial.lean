/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceDirectWindowData

/-!
# The direct paid trial law on a fixed tower

Defines the good exit and the paid step used by the direct fixed-`Q` trials.
`Kakeya.ML2Core.SourceDirectGoodMass` is the mass-form analytic estimate shared with the
dichotomy; `SourceDirectPaidStep` is the literal paid D step (subset, subshade, weighted mass
and a unit potential drop on the original `Q`); and `SourceDirectPaidTrialLaw` says every
sufficiently full `SourcePaidState` is terminal or admits such a step.
`source_direct_paidStep_of_coordinate_step` shows the existing coordinate-certified
`SourcePaidStep` already yields a `SourceDirectPaidStep`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

open ML2Assembly

universe u

/-- The good exit is the same mass-form analytic estimate used by Dichotomy. -/
def SourceDirectGoodMass {iota : Type u} {delta : ℝ≥0} (S : Finset iota)
    (Z : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3)))
    (beta gain : ℝ) : Prop :=
  (∑ i ∈ S, volume (Z i).shade) <= (delta : ℝ≥0∞) ^ gain *
    (S.card : ℝ≥0∞) ^ beta * volume (⋃ i ∈ S, (Z i).shade)

section Paid

variable {iota : Type u} {delta : ℝ≥0} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace ℝ (Fin 3))} {M C : Nat}
  {Y : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3))}

/-- The literal paid D step. The original fixed Q supplies the potential;
actual subsets and shade/mass payments are retained, without a false
inference from integer descent to a two-h coordinate descent. -/
structure SourceDirectPaidStep (Q : SourceThreadedTower S T M C)
    (h : ℝ) (loss : ℝ≥0∞) (x y : SourcePaidState S T Y) : Prop where
  subset : y.family <= x.family
  shade_subset : forall i, i ∈ y.family -> (y.shaded i).shade <= (x.shaded i).shade
  weighted_mass : x.mass <= loss * y.mass
  potential_drop : Q.assignedPotential h y.family + 1 <= Q.assignedPotential h x.family

/-- A trial may run on any actual retained state of this fixed tower once
its fullness permits it. The real preparation and dividing-scales choices
are constructed in the supplier theorem, not part of this input state. -/
def SourceDirectPaidTrialLaw
    (Y : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3)))
    (Q : SourceThreadedTower S T M C)
    (h eta0 alpha gamma beta : ℝ) (loss : ℝ≥0∞) : Prop :=
  forall x : SourcePaidState S T Y, (delta : ℝ≥0∞) ^ (2 * eta0) <= x.fullness ->
    SourcePaidTerminal loss alpha gamma beta x \/
      exists y : SourcePaidState S T Y, SourceDirectPaidStep Q h loss x y

end Paid

end Kakeya.ML2Core

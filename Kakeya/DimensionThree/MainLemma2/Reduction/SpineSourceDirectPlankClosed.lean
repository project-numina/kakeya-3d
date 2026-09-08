/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceDirectWindowData
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceEccentricNormalization
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceEccentricFactorTransport
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceDirectSelectorAdapters

/-!
# The direct plank (P) alternative, closed

`Kakeya.ML2Core.SourceEccentricAssignedConstruction` collects the analytic inputs on one paid
same-`Q` terminal subfamily.  `source_exists_direct_plank_construction` builds the full assigned
Part-B datum from one ordinary factorization level and the upper window, via the
`GeometryV2` normalization and eccentric factor transport.  `source_exists_direct_plank_exit`
is the closed P estimate: with `nuPlank ≤ etaParent·β/4` and a density budget on `κ`, for small
`δ` every `SourceDirectPlankFactors` in an upper window gives
`multiplicity S ≤ sourceFixedPreparationLoss K δ · δ ^ nuPlank · |S| ^ β`, with the
comparison `D` fixed and the ordinary coefficient bounded by `δ ^ (-etaPlank)`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

open ML2Assembly

universe u

section

variable {iota : Type u} {delta : ℝ≥0} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace ℝ (Fin 3))} {M C : Nat}

/-- All actual analytic inputs on one paid same-Q terminal subfamily. The
displayed mass, fullness and density rows are outputs of the construction. -/
structure SourceEccentricAssignedConstruction (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3)))
    {a m : Nat} {etaParent bias : ℝ} {D aw bw cw : ℝ≥0}
    (E : SourceZeroEccentricFactors Q Z a m etaParent bias D aw bw cw)
    (Rnorm : ℝ) (Cgeom cParent A : ℝ≥0) (p K : Nat) (etaPlank zeta : ℝ) where
  outer : SourceEccentricOuterSplit Q Z a (sourceEccentricLogLoss K delta)
  outer_normalization : SourceEccentricOuterNormalization Q outer Cgeom
  normalization : SourceEccentricCellNormalization Q outer m Rnorm Cgeom cParent
  selection : SourceEccentricAssignedSelection Q outer normalization E
    (sourceEccentricSelectionCost A p K delta etaPlank zeta)
    (A * delta ^ (-(p : ℝ) * zeta))
  factor_transport : SourceEccentricFactorTransport Q selection
    (sourceEccentricTransportCost A
      (sourceEccentricSelectionCost A p K delta etaPlank zeta) p delta bias)
  assigned : SourceEccentricAssignedDatum Q factor_transport
  normalized_scale_positive : 0 < sourceEccentricFineScale delta M a
  normalized_scale_lower : 10 * delta <= sourceEccentricFineScale delta M a
  fine_ball : forall i, i ∈ selection.leaves -> (selection.shading i).carrier <= Metric.closedBall 0 1
  fine_density : Kakeya.maxDensity selection.leaves (fun i => (selection.shading i).toConvexSpaceBody) <=
    (A : ℝ≥0∞) * (delta : ℝ≥0∞) ^ (-etaPlank)
  fine_fullness : delta ^ etaPlank /
    (A * sourceEccentricLogLoss K delta * sourceEccentricSelectionCost A p K delta etaPlank zeta) <=
    ShadedBody.fullness selection.leaves (fun i => (selection.shading i).toShadedBody)
  outer_fullness : delta ^ etaPlank / sourceEccentricLogLoss K delta <=
    ShadedBody.fullness outer.outer (fun i => (outer.outerShade i).toShadedBody)
  card_product : (outer.outer.card : ℝ≥0∞) * (selection.leaves.card : ℝ≥0∞) <=
    2 * (S.card : ℝ≥0∞)
  multiplicity : ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <=
    (sourceEccentricLogLoss K delta : ℝ≥0∞) *
      (sourceEccentricSelectionCost A p K delta etaPlank zeta : ℝ≥0∞) *
      ShadedBody.multiplicity outer.outer (fun i => (outer.outerShade i).toShadedBody) *
      ShadedBody.multiplicity selection.leaves (fun i => (selection.shading i).toShadedBody)

end

end Kakeya.ML2Core

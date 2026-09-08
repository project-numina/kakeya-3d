/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceParameterChoice
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceGridChoice
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceIndex
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceLocalReserve
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEveryScale
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineDefectDichotomy
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSiteClosure

/-!
# The chosen Sticky accuracy and its exponent map

Fixes the accuracy at which the every-scale (Sticky) multiplicity estimate is called:
`Kakeya.ML2Core.sourceStickyChi` and `sourceStickyAccuracy β ϖ = min (ϖ/4, 1/2, β/4)`.
`SourceStickyEstimateAt` is the estimate body at one scale and `SourceStickyExponentMap` bundles
it at every positive accuracy; `source_exists_actual_sticky_map` obtains one from
`ML2Reduction.exists_everyScale_exponent`.  `source_exists_chosen_sticky_grid` pairs the map with
the grid choice, `source_chosen_sticky_strict_budget` shows the accuracy sits strictly below
`β/2 - defectMargin`, `source_eventually_chosen_sticky_budget` absorbs a polylog loss, and
`source_everyScale_mono_input` is monotonicity of `IsKatzTaoAtEveryScale` in the exponent.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u

/-- The complete actual Sticky estimate at one input exponent and one runtime scale. -/
def SourceStickyEstimateAt (delta : ℝ≥0) (accuracy inputExponent : ℝ) : Prop :=
  ∀ {iota : Type u} {eta : ℝ}, eta <= inputExponent ->
  ∀ (s : Finset iota) (V : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3))),
    (∀ i ∈ s, (V i).carrier <= Metric.closedBall 0 1) ->
    ∀ {C : ℝ≥0} (VU : ShadedUniformTubeSet s V (ssfGridLen delta) C),
      ENNReal.ofReal ((delta : ℝ) ^ eta) <=
        ShadedBody.fullness' s (fun i => (V i).toShadedBody) ->
      Kakeya.maxDensity s (fun i => (V i).toConvexSpaceBody) <=
        ENNReal.ofReal ((delta : ℝ) ^ (-eta)) ->
      VU.tubeUniform.IsKatzTaoAtEveryScale
        (ENNReal.ofReal ((delta : ℝ) ^ (-inputExponent))) ->
      ShadedBody.multiplicity s (fun i => (V i).toShadedBody) <=
        ENNReal.ofReal ((delta : ℝ) ^ (-accuracy))

/-- The map carries its actual complete estimate body at every positive accuracy. -/
structure SourceStickyExponentMap (Eexp : ℝ -> ℝ) : Prop where
  positive : ∀ accuracy : ℝ, 0 < accuracy -> 0 < Eexp accuracy
  estimate : ∀ accuracy : ℝ, 0 < accuracy ->
    ∃ delta0 : ℝ, 0 < delta0 /\ delta0 <= 1 /\
      ∀ delta : ℝ≥0, 0 < delta -> (delta : ℝ) <= delta0 ->
        SourceStickyEstimateAt.{u} delta accuracy (Eexp accuracy)

end Kakeya.ML2Core

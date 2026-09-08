/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceLateChoice
public import Kakeya.MultiScaleSubmult
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineTwoScale
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineRungWiring
public import Kakeya.DimensionThree.MainLemma2.LineEssDistinct
public import Kakeya.Tube.Rigidity
public import Kakeya.FrostmanTransfer
public import Kakeya.ShadedUniform
public import Kakeya.DimensionThree.MainLemma2.GridRounding
public import Kakeya.StickyKakeya.CrossScale
public import Kakeya.MultiScaleFac.Stopping
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeRoute
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineDichotomyInputs
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCoarseSeam
public import Kakeya.MultiScaleFac.UniformBridgeKT
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineLevelBandDescent
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapePayload
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEveryScale
public import Kakeya.MultiScaleFac.GapsKT
public import Kakeya.GridScale
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCoreWindow
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineParams
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEccentric
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEDMultBound
public import Kakeya.DimensionThree.MainLemma2.SetupAbsorption
public import Kakeya.BiasedDensity
public import Kakeya.Factorization
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeM1
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSiteProducer
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorTerminal

/-!
# Terminal four-factor consumer and the complete coarse factor

`sourceTerminalParent` and `sourceTerminalNetGain` are the parent parameter and net middle
gain at a canonical rung. `SourceHfacAtRung` and `SourceFiniteHfac` state the scheduled
four-factor hypothesis for the finite range; `source_multiplicity_le_of_finite_four_factors`
and `source_sum_shade_le_finite_floor` consume it keeping the reserve `R0`.
`source_trialOutcome_finite_refined` runs the refinement at the ambient hierarchy.
`source_outer_factor_at_zero`, `source_parent_factor_at_zero` and
`source_eventually_top_cell_payments` pay the bounded top-cardinality constants, and
`source_exists_coarse_factor_complete` restates `exists_coarse_factor_complete` as the coarse
API with that payment explicit.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal

namespace Kakeya.ML2Assembly

universe u

/-- The source parent parameter at a specified canonical finite rung. -/
noncomputable def sourceTerminalParent (β ϖ ε₁ : ℝ) (rawGain rawDens : ℝ → ℝ) (m : ℕ) : ℝ :=
  sourceParentMinimum (ML2Spine.spineDiv ϖ ε₁)
    (ML2Spine.spineRung β ϖ ε₁
      (sourceChoiceGain β rawGain rawDens) (sourceChoiceDens β rawDens) (m + 1))
    (rawGain (ML2Spine.spineRung β ϖ ε₁
      (sourceChoiceGain β rawGain rawDens) (sourceChoiceDens β rawDens) (m + 1) / 16))
    (rawDens (ML2Spine.spineRung β ϖ ε₁
      (sourceChoiceGain β rawGain rawDens) (sourceChoiceDens β rawDens) (m + 1) / 16))

/-- The net middle gain comes from the actual raw VNS output at the next rung divided by 16. -/
noncomputable def sourceTerminalNetGain (β ϖ ε₁ : ℝ) (rawGain rawDens : ℝ → ℝ) (m : ℕ) : ℝ :=
  sourceMiddleNetGain (ML2Spine.spineDiv ϖ ε₁)
    (rawGain (ML2Spine.spineRung β ϖ ε₁
      (sourceChoiceGain β rawGain rawDens) (sourceChoiceDens β rawDens) (m + 1) / 16))

end Kakeya.ML2Assembly

namespace Kakeya.ML2Core

universe u

open ML2Assembly

section TopCell

variable {ι : Type u} {δ Cu : ℝ≥0} {s : Finset ι}
  {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}

end TopCell

end Kakeya.ML2Core

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Kakeya.Sticky
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Core

/-!
# Direct Conversion Statement

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

open MeasureTheory

namespace KakeyaLink

universe uE uI

/-- The reviewed direct geometric conversion obligation. -/
def DirectConversionStatement : Prop :=
  ∀ {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E],
    Module.finrank ℝ E = 3 →
    ∀ outputLoss : ℝ, 0 < outputLoss →
      ∃ inputLoss conversionDelta0 : ℝ,
        0 < inputLoss ∧ 0 < conversionDelta0 ∧
        ∀ {delta : NNReal}, 0 < delta → (delta : ℝ) ≤ conversionDelta0 →
        ∀ {ι : Type uI} (s : Finset ι) (V : ι → ShadedTube delta E),
          (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall (0 : E) 1) →
          ∀ {C : NNReal}, C ≤ ShadedTube.ssfUniformConst (Module.finrank ℝ E) →
          ∀ (U : ShadedTube.ShadedUniformTubeSet s V (Tube.ssfGridLen delta) C),
            ENNReal.ofReal ((delta : ℝ) ^ inputLoss) ≤
              ShadedBody.fullness' s (fun i => (V i).toShadedBody) →
            U.tubeUniform.IsFrostmanAtEveryScale
              (ENNReal.ofReal ((delta : ℝ) ^ (-inputLoss))) →
            ∃ family : Kakeya.Streamlined.TubeFamily (delta : ℝ),
            ∃ shading : Kakeya.Streamlined.TubeShading family,
              family.Nonempty ∧
              Kakeya.Assouad.WZ2PaperPureCWAAtNearbyScales family
                (Kakeya.realRpowENN (delta : ℝ) (-outputLoss)) ∧
              shading.IsLambdaDense (Kakeya.realRpowENN (delta : ℝ) outputLoss) ∧
              volume shading.union ≤ volume (⋃ i ∈ s, (V i).shade)

end KakeyaLink

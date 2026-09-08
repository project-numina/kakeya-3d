/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.CoarseBallUpstreamW50
public import Kakeya.DimensionThree.MainLemma1.Rescaling.KatzTao

/-!
# No-ED Katz--Tao consumer for a coarse family

`HonestCoarseAnalyticInput coarse Zcoarse eps apKT etaCoarse` is a producer-independent record of
the four analytic inputs at the coarse scale: nonemptiness, containment in `B_R`, a fullness lower
bound `δ^((1-5ε) etaCoarse)`, a maximal-density bound `CΔ δ^(-30ε - apKT)`, and a Frostman bound
`CΔ δ^(-apKT)` relative to `closedBall 0 R`.  No essential distinctness is required.
`eventually_multiplicity_of_honestCoarseAnalyticInput_w52` is the consumer: from a
`KatzTaoEstimate` of exponent `β` and the numeric conditions on `ε, apKT` and
`γ - betaPrime β γ`, it yields the coarse multiplicity bound with exponent `10 apKT` for
`δ ≤ b ≤ δ^(1-5ε)`, via `Kakeya.ml1Boot.multiplicity_coarse_le_of_const_ball` from
`Rescaling.KatzTao`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Convexity ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya.ml1Boot.W52NoEDHonestCoarseConsumer

noncomputable section

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

/- The input is intentionally independent of any producer.  A producer may fill
  these four fields on its literal coarse family, after which the theorem below
  is the ordinary no-ED Katz--Tao consumer. -/
structure HonestCoarseAnalyticInput
    {b deltaT R CDelta : ℝ≥0} {kappa : Type v}
    (coarse : Finset kappa) (Zcoarse : kappa -> ShadedTube b E)
    (eps apKT etaCoarse : ℝ) : Prop where
  nonempty : coarse.Nonempty
  ball : forall l, l ∈ coarse ->
    (Zcoarse l).carrier ⊆ Metric.closedBall 0 (R : ℝ)
  fullness : (deltaT : ℝ≥0∞) ^ ((1 - 5 * eps) * etaCoarse) <=
    ShadedBody.fullness coarse (fun l => (Zcoarse l).toShadedBody)
  maxDensity : Kakeya.maxDensity coarse
      (fun l => (Zcoarse l).toConvexSpaceBody) <=
    (CDelta : ℝ≥0∞) * (deltaT : ℝ≥0∞) ^ (-30 * eps - apKT)
  frostman : frostmanConstIn coarse
      (fun l => (Zcoarse l).toConvexSpaceBody)
      (ConvexSpaceBody.closedBall (0 : E) (R : ℝ) R.coe_nonneg) <=
    (CDelta : ℝ≥0∞) * (deltaT : ℝ≥0∞) ^ (-apKT)

end

end Kakeya.ml1Boot.W52NoEDHonestCoarseConsumer

end

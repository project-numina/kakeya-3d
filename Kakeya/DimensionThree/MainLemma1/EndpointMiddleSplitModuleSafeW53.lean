/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Setup
public import Kakeya.DimensionThree.MainLemma1.Rescaling.Numerics
public import Kakeya.DimensionThree.MainLemma1.W44NoEDNormalization
public import Kakeya.DimensionThree.MainLemma1.Cases
public import Kakeya.DimensionThree.MainLemma1.ThreePass
public import Kakeya.DimensionThree.MainLemma1.W44NormalizationCardPort
public import Kakeya.DimensionThree.MainLemma1.Rescaling.BallRadius

/-!
# Module-safe pointwise middle split from a raw Wang--Zahl certificate

An upstream-safe copy of the middle-scale split, importing only the balanced-middle algebra so it
can be used by `CaseTwo` without the legacy WZ packet files.  `RawWZCertificate β' ζ eM` records
an eventual multiplicity bound `δ^(-eM) · maxDensity^(1-β') · #t^β'` for shaded `q`-tubes with
`δ ≤ q ≤ δ^(ζ/5)`.  `middle_raw_pointwise_split` applies such a bound at the fine scale
`fineScale τ ρ`, together with a maximal-density bound and a two-sided normalised-`Q` band, to a
family whose `τ`-multiplicity equals its fine multiplicity, and returns the Katz--Tao-shaped
multiplicity bound with explicit exponent
`-eM - (1-β') zD - zQ + 2ζ(γ-β')/5` and constants `CΔ^(1-β') · CQ`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology Tube

namespace Kakeya.ml1Boot.W48EndpointMiddleSplitModuleSafeW53

noncomputable section
set_option maxHeartbeats 12000000

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/- A split-universe raw certificate.  This copy is kept upstream-safe: its
  proof only uses the module-safe balanced middle algebra, so it can be
  imported by CaseTwo without the legacy WZ packet files. -/
structure RawWZCertificate (betaPrimeValue zeta eM : ℝ) where
  etaM : ℝ
  etaM_pos : 0 < etaM
  bound :
    ∀ᶠ delta : ℝ≥0 in nhdsWithin 0 (Set.Ioi 0),
      ∀ q : ℝ≥0, delta <= q -> q <= delta ^ (zeta / 5) ->
        ∀ {iota : Type u} {t : Finset iota}
          (Tq : iota -> ShadedTube q E),
          t.Nonempty -> (∀ l ∈ t, (Tq l).carrier ⊆ Metric.closedBall 0 1) ->
          (delta : ℝ≥0∞) ^ etaM <=
            (ShadedBody.fullness t (fun l => (Tq l).toShadedBody) : ℝ≥0∞) ->
          ShadedBody.multiplicity t (fun l => (Tq l).toShadedBody) <=
            (delta : ℝ≥0∞) ^ (-eM) *
              maxDensity t (fun l => (Tq l).toConvexSpaceBody) ^
                (1 - betaPrimeValue) * (t.card : ℝ≥0∞) ^ betaPrimeValue

end
end Kakeya.ml1Boot.W48EndpointMiddleSplitModuleSafeW53

end

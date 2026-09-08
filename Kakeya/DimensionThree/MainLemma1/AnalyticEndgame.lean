/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Factoring
public import Kakeya.DimensionThree.MainLemma1.Rescaling.MiddleAverage
public import Kakeya.DimensionThree.MainLemma1.ScalarFactorization

/-!
# The analytic/numeric endgame for the scalar B3 interface

This file separates the only genuinely analytic input still needed after an
`IsTwoScaleFactors` producer from the completely deterministic exponent ledger.  The three
factor estimates are bundled together.  All remaining choices in the exact Case-II leaf are
made here: `etaVol = 2`, `c3 = 1`, `av = eta m`, and
`av' = eta m + 2 eps'`.

The factor constant is allowed to be a fixed NNReal multiple of
`factorTwoScales.C`.  The fixed multiplier covers, in particular, the `4 * M` loss of the
fixed-ball product factorization.  Its product with the hierarchy cardinality constant is absorbed
uniformly once the two relevant cardinalities obey the standard dimension-three
`delta ^ (-7)` bound.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya.ml1Boot.AnalyticEndgameW27

universe u v q w

variable {E : Type w}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The three analytic inequalities consumed by the scalar B3 collapse.  Geometry, Frostman
input, and threshold management belong in the producer of this certificate; the exponent and
capacity ledger below does not inspect how the bounds were obtained. -/
structure IsTwoScaleAnalyticBounds
    {ι : Type u} {κ : Type v} {lc : Type q}
    [DecidableEq κ] [DecidableEq lc]
    {δ τ θ : ℝ≥0} (γ a a' : ℝ)
    (s : Finset ι) (pτ : ι → κ) (kF : κ) (Yf : ι → ShadedTube δ E)
    (tτ : Finset κ) (pθ : κ → lc) (lM : lc) (Ym : κ → ShadedTube τ E)
    (tθ : Finset lc) (Yc : lc → ShadedTube θ E) : Prop where
  fine :
    ShadedBody.multiplicity (fibre s pτ kF) (fun i => (Yf i).toShadedBody)
      ≤ (δ : ℝ≥0∞) ^ (-4 * a') * ((δ / τ : ℝ≥0) : ℝ≥0∞) ^ (-2 * γ)
        * (((fibre s pτ kF).card : ℝ≥0∞)
            * ((δ / τ : ℝ≥0) : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2)
  middle :
    ShadedBody.multiplicity (fibre tτ pθ lM) (fun k => (Ym k).toShadedBody)
      ≤ (δ : ℝ≥0∞) ^ (10 * a) * ((τ / θ : ℝ≥0) : ℝ≥0∞) ^ (-2 * γ)
        * (((fibre tτ pθ lM).card : ℝ≥0∞)
            * ((τ / θ : ℝ≥0) : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2)
  coarse :
    ShadedBody.multiplicity tθ (fun l => (Yc l).toShadedBody)
      ≤ (δ : ℝ≥0∞) ^ (-4 * a') * (θ : ℝ≥0∞) ^ (-2 * γ)
        * ((tθ.card : ℝ≥0∞) * (θ : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2)

end Kakeya.ml1Boot.AnalyticEndgameW27

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Factoring
public import Kakeya.MultiScaleFac
public import Kakeya.Asymptotics
public import Kakeya.DimensionThree.MainLemma1.ThreePass
public import Kakeya.Factoring.RhoTubes
public import Kakeya.Tube.Dilate
public import Kakeya.Factoring.RhoTubesUndilated
public import Kakeya.Factoring.WeightedFullness
public import Kakeya.DimensionThree.MainLemma1.Rescaling.BallRadius

/-! ## A counted deduplication -/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya.ml1Boot.W50Upstream

noncomputable section
set_option maxHeartbeats 12000000

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The product-only certificate, duplicated upstream of `CaseTwo` so that the raw producer
does not import any Case-Two consumer or the `MainLemma1` umbrella. -/
structure IsCaseTwoDirectFactorsUpstreamW50
    {delta tau theta : ℝ≥0} {iota kappa : Type u} [DecidableEq kappa]
    (s : Finset iota) (T : iota -> ShadedTube delta E)
    (tTau : Finset kappa) (TTau : kappa -> Tube tau E) (pTau : iota -> kappa)
    (tTheta : Finset kappa) (TTheta : kappa -> Tube theta E) (pTheta : kappa -> kappa)
    (M : Nat) (tm : Finset kappa) (sf : Finset iota)
    (ZTau : kappa -> ShadedTube tau E) (Zf : iota -> ShadedTube delta E)
    (uCell : Finset kappa) (v0 : E) (tc sm : Finset kappa)
    (Zc : kappa -> ShadedTube theta E) (Zm : kappa -> ShadedTube tau E)
    (kF lM : kappa) : Prop where
  fine_nonempty : (fibre sf pTau kF).Nonempty
  middle_nonempty : (fibre sm pTheta lM).Nonempty
  coarse_nonempty : tc.Nonempty
  mid_subset : tm ⊆ tTau
  fine_subset : sf ⊆ s
  cell_subset : uCell ⊆ tm
  middle_subset : sm ⊆ uCell
  coarse_subset : tc ⊆ tTheta
  fine_mem : kF ∈ tm
  middle_mem : lM ∈ tc
  fine_maps : ∀ i ∈ sf, pTau i ∈ tm
  fine_card_band : ∀ k ∈ tm, ∀ k' ∈ tm,
    ((fibre sf pTau k).card : ℝ≥0∞) <=
      2 * ((fibre sf pTau k').card : ℝ≥0∞)
  middle_maps : ∀ k ∈ sm, pTheta k ∈ tc
  middle_card_band : ∀ l ∈ tc, ∀ l' ∈ tc,
    ((fibre sm pTheta l).card : ℝ≥0∞) <=
      2 * ((fibre sm pTheta l').card : ℝ≥0∞)
  fine_tube : ∀ i, (Zf i).toTube = (T i).toTube
  outer_tube : ∀ k, (ZTau k).toTube = TTau k
  coarse_tube : ∀ l, (Zc l).toTube = TTheta l
  middle_tube : ∀ k, (Zm k).toTube = (TTau k).translate v0
  middle_ball : ∀ k ∈ uCell, (Zm k).carrier ⊆ Metric.closedBall 0 1
  cell_fullness : ((1 / 2 : ℝ≥0) : ℝ≥0∞) *
      ShadedBody.fullness tm (fun k => (ZTau k).toShadedBody) <=
    ShadedBody.fullness uCell (fun k => ((ZTau k).translate v0).toShadedBody)
  cell_mass : (∑ k ∈ tm, volume (ZTau k).shade) <=
    4 * (M : ℝ≥0∞) * ∑ k ∈ uCell, volume ((ZTau k).translate v0).shade
  outer_fullness : (factorOneScale.C s.card delta)⁻¹ *
      ShadedBody.fullness s (fun i => (T i).toShadedBody) <=
    ShadedBody.fullness tm (fun k => (ZTau k).toShadedBody)
  fine_refinement : ShadedBody.IsCRefinement sf
    (fun i => (Zf i).toShadedBody) s (fun i => (T i).toShadedBody)
    (factorOneScale.C s.card delta)⁻¹
  coarse_fullness : (factorOneScale.C uCell.card tau)⁻¹ *
      (((1 / 2 : ℝ≥0) : ℝ≥0∞) *
        ShadedBody.fullness tm (fun k => (ZTau k).toShadedBody)) <=
    ShadedBody.fullness tc (fun l => (Zc l).toShadedBody)
  middle_refinement : ShadedBody.IsCRefinement sm
    (fun k => (Zm k).toShadedBody) uCell
    (fun k => ((ZTau k).translate v0).toShadedBody)
    (factorOneScale.C uCell.card tau)⁻¹
  fine_fullness : ShadedBody.fullness sf (fun i => (Zf i).toShadedBody) <=
    ShadedBody.fullness (fibre sf pTau kF) (fun i => (Zf i).toShadedBody)
  middle_fullness : ShadedBody.fullness sm (fun k => (Zm k).toShadedBody) <=
    ShadedBody.fullness (fibre sm pTheta lM) (fun k => (Zm k).toShadedBody)
  card_product : ((fibre sf pTau kF).card : ℝ≥0∞) *
      ((fibre sm pTheta lM).card : ℝ≥0∞) * (tc.card : ℝ≥0∞) <=
    4 * (s.card : ℝ≥0∞)
  product : ShadedBody.multiplicity s (fun i => (T i).toShadedBody) <=
    (4 * (M : ℝ≥0∞)) *
      (factorTwoScales.C s.card delta uCell.card tau : ℝ≥0∞) *
      ShadedBody.multiplicity tc (fun j => (Zc j).toShadedBody) *
      ShadedBody.multiplicity (fibre sm pTheta lM)
        (fun j => (Zm j).toShadedBody) *
      ShadedBody.multiplicity (fibre sf pTau kF)
        (fun i => (Zf i).toShadedBody)

/-! ## The B3 count on a deduplicated fixed skeleton -/

end
end Kakeya.ml1Boot.W50Upstream

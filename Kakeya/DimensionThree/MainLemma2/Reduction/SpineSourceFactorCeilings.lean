/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceBudget
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFactors
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineNewParentFactor

/-!
# Actual factor ceilings and their complete analytic applications

The returned input exponents and tube-scale thresholds are fixed before
the common input exponent, the source rung, and all runtime families.
-/

@[expose] public section

open scoped NNReal ENNReal

open Filter
open scoped Topology NNReal ENNReal

namespace Kakeya.ML2Assembly

universe u v

variable (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- The full eventual fine-factor estimate at its own scale. -/
def SourceFineFactorBody (beta charge input : ℝ) : Prop :=
  ∀ᶠ (delta : ℝ≥0) in 𝓝[>] 0,
    forall {iota : Type u} (f : Finset iota) (Y : iota -> ShadedTube delta E),
      (forall i, i ∈ f -> (Y i).carrier ⊆ Metric.closedBall (0 : E) 1) ->
      Kakeya.maxDensity f (fun i => (Y i).toConvexSpaceBody) <=
        (delta : ℝ≥0∞) ^ (-input) ->
      delta ^ input <= ShadedBody.fullness f (fun i => (Y i).toShadedBody) ->
      ShadedBody.multiplicity f (fun i => (Y i).toShadedBody) <=
        (delta : ℝ≥0∞) ^ (-charge) * (f.card : ℝ≥0∞) ^ beta

open Classical in
/-- The full actual translated new-parent fibre body at a fixed parent parameter. -/
def SourceParentFactorAtBody (beta charge input : ℝ) (thetaParent : ℝ≥0)
    (etaPrime : ℝ) : Prop :=
  forall {delta Cu : ℝ≥0} {iota : Type u} {family : Finset iota}
    {T : iota -> Tube delta E} {L a p : Nat}
    {U : Tube.UniformTubeSet family T L Cu} {tp : Finset iota}
    {Yp : iota -> ShadedTube (Tube.gridScale delta L p) E} {shift : E} {j : iota},
    0 < delta -> delta <= 1 -> a <= p -> p <= L ->
    Tube.gridScale delta L p <= thetaParent ->
    tp ⊆ ML2Reduction.activeNodes U.cover.toChain p ->
    (forall k, (Yp k).toTube = (U.cover.tube p k).translate shift) ->
    (forall k, k ∈ ({k ∈ tp | ML2Reduction.coarseNode U.cover.toChain a p k = j} :
        Finset iota) -> (Yp k).carrier ⊆ Metric.closedBall (0 : E) 1) ->
    delta ^ input <= ShadedBody.fullness
      ({k ∈ tp | ML2Reduction.coarseNode U.cover.toChain a p k = j} : Finset iota)
      (fun k => (Yp k).toShadedBody) ->
    Kakeya.maxDensity (U.nodesUnder p a j)
      (fun k => (U.cover.tube p k).toConvexSpaceBody) <=
        (delta : ℝ≥0∞) ^ (-(2 * etaPrime)) ->
    ShadedBody.multiplicity
      ({k ∈ tp | ML2Reduction.coarseNode U.cover.toChain a p k = j} : Finset iota)
      (fun k => (Yp k).toShadedBody) <=
        (delta : ℝ≥0∞) ^ (-charge) *
          ((({k ∈ tp | ML2Reduction.coarseNode U.cover.toChain a p k = j} :
            Finset iota).card : ℝ≥0∞)) ^ beta

/-- The complete outer estimate with ambient fullness and density scales decoupled. -/
def SourceOuterFactorAtBody (beta charge input : ℝ) (thetaOuter : ℝ≥0)
    (densityExponent : ℝ) : Prop :=
  forall {theta : ℝ≥0}, 0 < theta -> theta <= thetaOuter ->
    forall dt : ℝ≥0, 0 < dt -> dt <= theta ->
    forall {iota : Type u} (t : Finset iota) (Y : iota -> ShadedTube theta E),
      (forall k, k ∈ t -> (Y k).carrier ⊆ Metric.closedBall (0 : E) 1) ->
      dt ^ input <= ShadedBody.fullness t (fun k => (Y k).toShadedBody) ->
      Kakeya.maxDensity t (fun k => (Y k).toConvexSpaceBody) <=
        (dt : ℝ≥0∞) ^ (-densityExponent) ->
      ShadedBody.multiplicity t (fun k => (Y k).toShadedBody) <=
        (dt : ℝ≥0∞) ^ (-charge) * (t.card : ℝ≥0∞) ^ beta

/-- Actual estimator outputs: three exponents and two distinct tube-scale thresholds. -/
structure SourceFactorCeilingData where
  fineInput : ℝ
  parentInput : ℝ
  outerInput : ℝ
  parentThreshold : ℝ≥0
  outerThreshold : ℝ≥0

open Classical in
/-- Only returned ambient exponent ceilings enter the later finite minimum. -/
noncomputable def sourceFactorCeilingSet (x : SourceFactorCeilingData) : Finset ℝ :=
  {x.fineInput, x.parentInput, x.outerInput}

/-- All returned signs, thresholds, and complete bodies before any input or rung choice. -/
structure SourceFactorCores (beta epsFine epsParent epsOuter : ℝ)
    (x : SourceFactorCeilingData) : Prop where
  fine_input_pos : 0 < x.fineInput
  parent_input_pos : 0 < x.parentInput
  outer_input_pos : 0 < x.outerInput
  parent_threshold_pos : 0 < x.parentThreshold
  parent_threshold_le_one : x.parentThreshold <= 1
  outer_threshold_pos : 0 < x.outerThreshold
  outer_threshold_le_one : x.outerThreshold <= 1
  ceilings_pos : forall h : ℝ, h ∈ sourceFactorCeilingSet x -> 0 < h
  fine : SourceFineFactorBody.{u} E beta epsFine x.fineInput
  parent : forall etaPrime : ℝ, 0 <= etaPrime ->
    SourceParentFactorAtBody.{u} E beta (epsParent + 2 * etaPrime)
      x.parentInput x.parentThreshold etaPrime
  outer : forall k : ℝ, 0 <= k ->
    SourceOuterFactorAtBody.{u} E beta (epsOuter + k) x.outerInput x.outerThreshold k

/-- A1: the fine ceiling and full body come from the actual Katz-Tao estimate. -/
theorem source_exists_fine_factor {beta epsFine : ℝ}
    (hbeta : 0 <= beta) (hKT : KatzTaoEstimate.{u} E beta) (heps : 0 < epsFine) :
    exists Hf : ℝ, 0 < Hf /\ SourceFineFactorBody.{u} E beta epsFine Hf := by
  exact ML2Core.exists_fine_factor (E := E) hbeta hKT heps


/-- A3: the actual outer call precedes every nonnegative density exponent. -/
theorem source_exists_outer_factor {beta epsOuter : ℝ}
    (hbeta0 : 0 <= beta) (hbeta1 : beta <= 1)
    (hKT : KatzTaoEstimate.{u} E beta) (heps : 0 < epsOuter) :
    exists Hc : ℝ, 0 < Hc /\ exists thetaOuter : ℝ≥0,
      0 < thetaOuter /\ thetaOuter <= 1 /\
      forall k : ℝ, 0 <= k ->
        SourceOuterFactorAtBody.{u} E beta (epsOuter + k) Hc thetaOuter k := by
  obtain ⟨H, hH, theta0, htheta0, htheta1, hcore⟩ :=
    ML2Core.exists_coarse_factor (E := E) hbeta0 hbeta1 hKT heps
  refine ⟨H, hH, theta0, htheta0, htheta1, ?_⟩
  intro k hk theta htheta hscale dt hdt0 hdttheta iota t Y hball hfull hdens
  exact hcore htheta hscale dt hdt0 hdttheta hk t Y hball hfull hdens


/-- Actual scheduled charges and density parameters, uniformly over every source rung. -/
structure SourceScheduledFactorBodies (beta varpi eps1 : ℝ)
    (rawGain rawDens : ℝ -> ℝ) (a : SourceLocalAccuracyData)
    (etaL : ℝ) (x : SourceFactorCeilingData) : Prop where
  parent_parameter_nonneg : forall m : Nat, m < ML2Spine.spineCount varpi eps1 ->
    0 <= sourceParentMinimum (ML2Spine.spineDiv varpi eps1)
      (ML2Spine.spineRung beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1))
      (rawGain (ML2Spine.spineRung beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1) / 16))
      (rawDens (ML2Spine.spineRung beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1) / 16))
  outer_density_nonneg : forall m : Nat, m < ML2Spine.spineCount varpi eps1 ->
    0 <= a.kappaC + ML2Spine.spineRung beta varpi eps1
      (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) m
  fine : ∀ᶠ (delta : ℝ≥0) in 𝓝[>] 0,
    forall m : Nat, m < ML2Spine.spineCount varpi eps1 ->
      forall {iota : Type u} (f : Finset iota) (Y : iota -> ShadedTube delta E),
        (forall i, i ∈ f -> (Y i).carrier ⊆ Metric.closedBall (0 : E) 1) ->
        Kakeya.maxDensity f (fun i => (Y i).toConvexSpaceBody) <=
          (delta : ℝ≥0∞) ^ (-etaL) ->
        delta ^ etaL <= ShadedBody.fullness f (fun i => (Y i).toShadedBody) ->
        ShadedBody.multiplicity f (fun i => (Y i).toShadedBody) <=
          (delta : ℝ≥0∞) ^ (-(a.epsf m)) * (f.card : ℝ≥0∞) ^ beta
  parent : forall m : Nat, m < ML2Spine.spineCount varpi eps1 ->
    SourceParentFactorAtBody.{u} E beta (a.epsp m) etaL x.parentThreshold
      (sourceParentMinimum (ML2Spine.spineDiv varpi eps1)
        (ML2Spine.spineRung beta varpi eps1
          (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1))
        (rawGain (ML2Spine.spineRung beta varpi eps1
          (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1) / 16))
        (rawDens (ML2Spine.spineRung beta varpi eps1
          (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1) / 16)))
  outer : forall m : Nat, m < ML2Spine.spineCount varpi eps1 ->
    SourceOuterFactorAtBody.{u} E beta
      (a.epsc m + ML2Spine.spineRung beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) m)
      etaL x.outerThreshold
      (a.kappaC + ML2Spine.spineRung beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) m)


end Kakeya.ML2Assembly

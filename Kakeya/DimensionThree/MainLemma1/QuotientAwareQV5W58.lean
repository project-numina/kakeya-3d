/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.QuotientAwareQV5SupportW58

/-!
# Quotient-aware second factor at the two-source stop (V5, W58)

Assembles the second factor of the two-scale product at the moment the two-source stopping
rule fires.  `FinalSecondFactorAtStopV5W58` packages a translated ball cell of the stopped
active family, its paid mass and multiplicity comparisons, the raw and translated parent
structures, and the `IsOneScaleSelected` second factor.  The eventual constructors
`eventually_exists_preSecondFactor_levelB_v5_w58`,
`eventually_exists_finalSecondFactor_of_stopped_v5_w58` and
`eventually_exists_twoSourceStop_then_finalSecondFactor_v5_w58` produce the pre-packet, the
stop and the final factor from a `StickyKakeya.IsFrostmanDividingBlock` on a uniform tube set.
`rawMiddle_le_target_mul_quotientResidual_v5_w58` is the scalar estimate that converts a raw
middle multiplicity bound into the target form with the retained share and normalized `Q`
residual from `QuotientAwareQV5SupportW58`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology Tube

namespace Kakeya.ml1Boot.W58QuotientAwareQV5

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option linter.unusedVariables false

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

structure FinalSecondFactorAtStopV5W58
    {delta Cd : ℝ≥0} {iota : Type u} [DecidableEq iota]
    {sPrime : Finset iota} {V : iota -> ShadedTube delta E}
    {N a b : Nat}
    (p : Params) (m M : Nat)
    (U : Tube.UniformTubeSet sPrime (fun i => (V i).toTube) N Cd)
    (pre : PreSecondFactorLevelBPacketV5W58 (b := b) p U)
    (stop : StoppedTwoSourceV5W58 (a := a) (b := b) p m U pre) where
  cell : Finset iota
  v0 : E
  middleActive : Finset iota
  ZTauFinal : iota -> ShadedTube (Tube.gridScale delta N b) E
  coarseActive : Finset iota
  ZThetaFinal : iota -> ShadedTube (Tube.gridScale delta N stop.j) E
  lM : iota
  lamM : ℝ≥0
  cell_subset : cell ⊆ stop.active
  cell_nonempty : cell.Nonempty
  cell_ball : forall k, k ∈ cell ->
    ((pre.ZTau k).translate v0).carrier ⊆ Metric.closedBall 0 1
  cell_mass_paid :
    (∑ k ∈ stop.active, volume (pre.ZTau k).shade) <=
      4 * (M : ℝ≥0∞) *
        ∑ k ∈ cell, volume ((pre.ZTau k).translate v0).shade
  cell_multiplicity_paid :
    ShadedBody.multiplicity stop.active
        (fun k => (pre.ZTau k).toShadedBody) <=
      4 * (M : ℝ≥0∞) * ShadedBody.multiplicity cell
        (fun k => ((pre.ZTau k).translate v0).toShadedBody)
  raw_parent : IsParentFamily stop.active (U.cover.tube b)
    ({stop.pJ} : Finset iota) (U.cover.tube stop.j)
    (U.nodeAncestor b stop.j)
  translated_parent : IsParentFamily stop.active
    (fun k => (U.cover.tube b k).translate v0)
    ({stop.pJ} : Finset iota)
    (fun _ => (U.cover.tube stop.j stop.pJ).translate v0)
    (U.nodeAncestor b stop.j)
  second_factor : IsOneScaleSelected
    ((((factorOneScale.C cell.card (Tube.gridScale delta N b))⁻¹ : ℝ≥0) :
      ℝ≥0∞))
    ((factorOneScale.C cell.card (Tube.gridScale delta N b) : ℝ≥0) : ℝ≥0∞)
    stop.active cell
    (zeroExtend cell (fun k => (U.cover.tube b k).translate v0)
      (fun k => (pre.ZTau k).translate v0))
    ({stop.pJ} : Finset iota)
    (fun _ => (U.cover.tube stop.j stop.pJ).translate v0)
    (U.nodeAncestor b stop.j)
    middleActive ZTauFinal coarseActive ZThetaFinal lM
    ((2 * factorOneScale.C cell.card
      (Tube.gridScale delta N b))⁻¹ * pre.mu0) lamM
  selected_parent_eq : lM = stop.pJ
  literal_active_source :
    fibre stop.active (U.nodeAncestor b stop.j) lM = stop.active
  selected_fullness_paid :
    ((((factorOneScale.C cell.card
        (Tube.gridScale delta N b))⁻¹ : ℝ≥0) : ℝ≥0∞)) *
        (((4 : ℝ≥0∞) * (M : ℝ≥0∞))⁻¹ *
          (ShadedBody.fullness stop.active
            (fun k => (pre.ZTau k).toShadedBody) : ℝ≥0∞)) <=
      (lamM : ℝ≥0∞)
  frostman_final_active_levelA :
    frostmanConstIn
        (fibre stop.active (U.nodeAncestor b stop.j) lM)
        (fun k =>
          (selectedShade middleActive
            (zeroExtend cell (fun r => (U.cover.tube b r).translate v0)
              (fun r => (pre.ZTau r).translate v0))
            ZTauFinal k).toConvexSpaceBody)
        ((U.cover.tube a stop.q).translate v0).toConvexSpaceBody <=
      stop.kappa⁻¹ * completeLevelAFrostmanBudgetV5W58 delta N a b m p
  q_on_literal_active_source :
    (stop.j = 0 /\ Tube.gridScale delta N stop.j = 1 /\
      stop.kappa * (delta : ℝ≥0∞) ^ (3 * p.η m) <=
        normalizedQV5W58
          (Tube.gridScale delta N b / Tube.gridScale delta N stop.j)
          (fibre stop.active (U.nodeAncestor b stop.j) lM)) \/
    (0 < stop.j /\ QuotientScaledActiveQBandV5W58 delta
      (Tube.gridScale delta N b / Tube.gridScale delta N stop.j)
      (fibre stop.active (U.nodeAncestor b stop.j) lM)
      stop.kappa 1 (3 * p.η m))

end

end Kakeya.ml1Boot.W58QuotientAwareQV5

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.UpstreamCountedRawProducerW50Module
public import Kakeya.DimensionThree.MainLemma1.CoarseFibre
public import Kakeya.DimensionThree.MainLemma1.Factoring
public import Kakeya.Factoring.RhoTubes
public import Kakeya.Tube.Dilate
public import Kakeya.Factoring.RhoTubesUndilated
public import Kakeya.Factoring.WeightedFullness
public import Kakeya.DimensionThree.MainLemma1.W44NoEDNormalization
public import Kakeya.DimensionThree.MainLemma1.Rescaling.Numerics
public import Kakeya.DimensionThree.MainLemma1.Cases
public import Kakeya.DimensionThree.MainLemma1.ThreePass
public import Kakeya.DimensionThree.MainLemma1.W44NormalizationCardPort
public import Kakeya.DimensionThree.MainLemma1.Setup
public import Kakeya.DimensionThree.MainLemma1.Rescaling.BallRadius
public import Kakeya.DimensionThree.MainLemma1.Rescaling.KatzTao
public import Kakeya.MultiScaleFac
public import Kakeya.Asymptotics
public import Kakeya.DimensionThree.MainLemma1.ScalarFactorization
public import Kakeya.DimensionThree.MainLemma1.Rescaling.MiddleAverage
public import Kakeya.DimensionThree.MainLemma1.WZGlobalCrossing
public import Kakeya.DimensionThree.MainLemma1.WZCanonicalQBand
public import Kakeya.DimensionThree.MainLemma1.CapacityLedger
public import Kakeya.DimensionThree.MainLemma1.EnlargementCover
public import Kakeya.ConvexBody.ContainerChange
public import Mathlib.Order.Filter.Finite

/-!
# Quotient-aware stopped two-source packet (V5)

Support library and producer for the second (middle-to-coarse) factor at a protected stopping
level, tracking the active class and its complete hierarchy fibre separately with the exact
retained share `kappa = #active / #complete`.  The file collects several earlier layers:
ancestor and `tauAncestorClass` lemmas in `Kakeya.WangZahl`; the maximal-multiplicity class
selection `exists_positive_maxMultiplicity_tauAncestorClass_w48`; the first-crossing and
symmetric `Q`-band results of `W48ReverseQBand`; tube-capacity Frostman lower bounds in
`W47EndpointLowCard`; and the weak coarse-parent core `WeakCoarseFibreCore` with
`eventually_exists_completeOldFibreFreshCore_at_active_weak_w48`.
The namespace `W58QuotientAwareQV5` defines `normalizedQV5W58`, the active/complete classes, the
`Q`-band predicates, the input record `PreSecondFactorLevelBPacketV5W58` and the output record
`StoppedTwoSourceV5W58`, and proves the producer
`eventually_exists_stoppedTwoSource_of_preSecond_v5_w58` from a Frostman dividing block.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology Tube

namespace Kakeya.WangZahl

noncomputable section

universe u

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

end

end Kakeya.WangZahl

namespace Kakeya.ml1Boot

noncomputable section

universe u

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

end

end Kakeya.ml1Boot

namespace Kakeya.ml1Boot.W48ReverseQBand

noncomputable section

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

end

end Kakeya.ml1Boot.W48ReverseQBand

namespace Kakeya.ml1Boot.W47EndpointLowCard

end Kakeya.ml1Boot.W47EndpointLowCard

namespace Kakeya.ml1Boot.W48OldFibreProtectedStop

noncomputable section

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

end

end Kakeya.ml1Boot.W48OldFibreProtectedStop

namespace Kakeya.ml1Boot.WeakCoarseFibreCore

noncomputable section
set_option maxHeartbeats 12000000

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

structure WeakCoarseNodeParents {iota : Type*} {delta : ℝ≥0}
    {s' : Finset iota} {T : iota -> Tube delta E} {N : Nat} {C : ℝ≥0}
    (U : Tube.UniformTubeSet s' T N C) (a b : Nat) (pTheta : iota -> iota) : Prop where
  le_index : a <= b
  le_gridLen : b <= N
  nodes_carry_leaf : ∀ k ∈ U.cover.indexSet b,
    ∃ i ∈ s', U.cover.assign b i = k
  assign_comp : ∀ i ∈ s',
    pTheta (U.cover.assign b i) = U.cover.assign a i
  mapsTo : ∀ k ∈ U.cover.indexSet b, pTheta k ∈ U.cover.indexSet a
  le_parent : ∀ k ∈ U.cover.indexSet b,
    (U.cover.tube b k).toConvexSpaceBody <=
      (U.cover.tube a (pTheta k)).toConvexSpaceBody

end

end Kakeya.ml1Boot.WeakCoarseFibreCore

namespace Kakeya.ml1Boot.W48SelectedFreshStopProducer

noncomputable section
set_option maxHeartbeats 8000000

universe u v w

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

end

end Kakeya.ml1Boot.W48SelectedFreshStopProducer

namespace Kakeya.ml1Boot.W58QuotientAwareQV5

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

structure WeakCoarseNodeParentsV5W58
    {iota : Type u} {delta : ℝ≥0}
    {sPrime : Finset iota} {T : iota -> Tube delta E}
    {N : Nat} {Cd : ℝ≥0}
    (U : Tube.UniformTubeSet sPrime T N Cd)
    (a b : Nat) (pTheta : iota -> iota) : Prop where
  le_index : a <= b
  le_gridLen : b <= N
  nodes_carry_leaf : forall k, k ∈ U.cover.indexSet b ->
    exists i, i ∈ sPrime /\ U.cover.assign b i = k
  assign_comp : forall i, i ∈ sPrime ->
    pTheta (U.cover.assign b i) = U.cover.assign a i
  mapsTo : forall k, k ∈ U.cover.indexSet b ->
    pTheta k ∈ U.cover.indexSet a
  le_parent : forall k, k ∈ U.cover.indexSet b ->
    (U.cover.tube b k).toConvexSpaceBody <=
      (U.cover.tube a (pTheta k)).toConvexSpaceBody

def normalizedQV5W58 {iota : Type u}
    (q : ℝ≥0) (source : Finset iota) : ℝ≥0∞ :=
  (q : ℝ≥0∞) ^ (2 : Nat) * (source.card : ℝ≥0∞)

def activeClassV5W58
    {delta Cd : ℝ≥0} {iota : Type u} [DecidableEq iota]
    {sPrime : Finset iota} {V : iota -> ShadedTube delta E}
    {N : Nat}
    (U : Tube.UniformTubeSet sPrime (fun i => (V i).toTube) N Cd)
    (b a : Nat) (mid : Finset iota) (q : iota) : Finset iota :=
  Kakeya.WangZahl.tauAncestorClass U b a mid q

def completeClassV5W58
    {delta Cd : ℝ≥0} {iota : Type u} [DecidableEq iota]
    {sPrime : Finset iota} {V : iota -> ShadedTube delta E}
    {N : Nat}
    (U : Tube.UniformTubeSet sPrime (fun i => (V i).toTube) N Cd)
    (b a : Nat) (q : iota) : Finset iota :=
  Kakeya.WangZahl.tauAncestorClass U b a (U.cover.indexSet b) q

def retainedShareV5W58 {iota : Type u}
    (active complete : Finset iota) : ℝ≥0∞ :=
  (active.card : ℝ≥0∞) / (complete.card : ℝ≥0∞)

def SymmetricCompleteQBandV5W58 {iota : Type u}
    (delta q : ℝ≥0) (complete : Finset iota)
    (CQ : ℝ≥0) (zQ : ℝ) : Prop :=
  (CQ : ℝ≥0∞) ^ (-1 : ℝ) * (delta : ℝ≥0∞) ^ zQ <=
      normalizedQV5W58 q complete /\
    normalizedQV5W58 q complete <=
      (CQ : ℝ≥0∞) * (delta : ℝ≥0∞) ^ (-zQ)

def QuotientScaledActiveQBandV5W58 {iota : Type u}
    (delta q : ℝ≥0) (active : Finset iota)
    (kappa : ℝ≥0∞) (CQ : ℝ≥0) (zQ : ℝ) : Prop :=
  kappa * ((CQ : ℝ≥0∞) ^ (-1 : ℝ) * (delta : ℝ≥0∞) ^ zQ) <=
      normalizedQV5W58 q active /\
    normalizedQV5W58 q active <=
      kappa * ((CQ : ℝ≥0∞) * (delta : ℝ≥0∞) ^ (-zQ))

def completeLevelAFrostmanBudgetV5W58
    (delta : ℝ≥0) (N a b m : Nat) (p : Params) : ℝ≥0∞ :=
  (delta : ℝ≥0∞) ^ (-p.ε) *
    ((Tube.gridScale delta N a / Tube.gridScale delta N b : ℝ≥0) : ℝ≥0∞) ^ p.η m

structure PreSecondFactorLevelBPacketV5W58
    {delta Cd : ℝ≥0} {iota : Type u} [DecidableEq iota]
    {sPrime : Finset iota} {V : iota -> ShadedTube delta E}
    {N b : Nat}
    (p : Params)
    (U : Tube.UniformTubeSet sPrime (fun i => (V i).toTube) N Cd) where
  tTau : Finset iota
  pTau : iota -> iota
  repTau : iota -> iota
  fineActive : Finset iota
  Zf : iota -> ShadedTube delta E
  tAct : Finset iota
  ZTau : iota -> ShadedTube (Tube.gridScale delta N b) E
  kF : iota
  lamP : ℝ≥0
  lamF : ℝ≥0
  regularizationExponent : ℝ
  mid : Finset iota
  mu0 : ℝ≥0
  tau_subset : tTau ⊆ U.cover.indexSet b
  tau_map_mem : forall i, pTau i ∈ tTau
  tau_map_is_representative : forall i, i ∈ sPrime ->
    pTau i = repTau (U.cover.assign b i)
  tau_represents_every_body : forall k, k ∈ U.cover.indexSet b ->
    repTau k ∈ tTau /\
      (U.cover.tube b (repTau k)).toConvexSpaceBody =
        (U.cover.tube b k).toConvexSpaceBody
  tau_representative_onto : forall k, k ∈ tTau ->
    exists k0, k0 ∈ U.cover.indexSet b /\ repTau k0 = k
  tau_selected_body : forall i, i ∈ sPrime ->
    (U.cover.tube b (pTau i)).toConvexSpaceBody =
      (U.cover.tube b (U.cover.assign b i)).toConvexSpaceBody
  fine_parent : IsParentFamily sPrime (fun i => (V i).toTube)
    tTau (U.cover.tube b) pTau
  lamP_exact : lamP =
    ((1 * factorOneScale.C sPrime.card delta)⁻¹ * delta ^ p.η 0)
  first_factor : IsOneScaleSelected
    ((((factorOneScale.C sPrime.card delta)⁻¹ : ℝ≥0) : ℝ≥0∞))
    ((factorOneScale.C sPrime.card delta : ℝ≥0) : ℝ≥0∞)
    sPrime sPrime V tTau (U.cover.tube b) pTau
    fineActive Zf tAct ZTau kF lamP lamF
  lamP_funded :
    (delta : ℝ≥0∞) ^ regularizationExponent <= (lamP : ℝ≥0∞)
  mid_subset : mid ⊆ tAct
  mid_nonempty : mid.Nonempty
  mu0_pos : 0 < mu0
  middle_tube : forall k, k ∈ mid ->
    (ZTau k).toTube = U.cover.tube b k
  density_band : forall k, k ∈ mid ->
    ((2 : ℝ≥0) : ℝ≥0∞)⁻¹ * (mu0 : ℝ≥0∞) * volume (ZTau k).carrier <=
        volume (ZTau k).shade /\
      volume (ZTau k).shade <=
        ((2 : ℝ≥0) : ℝ≥0∞) * (mu0 : ℝ≥0∞) * volume (ZTau k).carrier
  regularization_multiplicity :
    ShadedBody.multiplicity tAct (fun k => (ZTau k).toShadedBody) <=
      16 * (delta : ℝ≥0∞) ^ (-regularizationExponent) *
        ShadedBody.multiplicity mid (fun k => (ZTau k).toShadedBody)
  regularization_fullness :
    (delta : ℝ≥0∞) ^ (2 * regularizationExponent) / 16 <=
      (ShadedBody.fullness mid (fun k => (ZTau k).toShadedBody) : ℝ≥0∞)
  regularization_card :
    ((delta : ℝ≥0∞) ^ (2 * regularizationExponent) / 16) *
        (tAct.card : ℝ≥0∞) <= (mid.card : ℝ≥0∞)

structure StoppedTwoSourceV5W58
    {delta Cd : ℝ≥0} {iota : Type u} [DecidableEq iota]
    {sPrime : Finset iota} {V : iota -> ShadedTube delta E}
    {N a b : Nat}
    (p : Params) (m : Nat)
    (U : Tube.UniformTubeSet sPrime (fun i => (V i).toTube) N Cd)
    (pre : PreSecondFactorLevelBPacketV5W58 (b := b) p U) where
  pTheta : iota -> iota
  parents : WeakCoarseNodeParentsV5W58 U a b pTheta
  q : iota
  active : Finset iota
  complete : Finset iota
  j : Nat
  pJ : iota
  q_active : q ∈ Kakeya.WangZahl.activeRhoParents U b a pre.mid
  active_eq : active = activeClassV5W58 U b a pre.mid q
  complete_eq : complete = completeClassV5W58 U b a q
  complete_fibre_eq : complete = fibre (U.cover.indexSet b) pTheta q
  active_nonempty : active.Nonempty
  complete_nonempty : complete.Nonempty
  active_subset_complete : active ⊆ complete
  active_subset_mid : active ⊆ pre.mid
  complete_subset_levelB : complete ⊆ U.cover.indexSet b
  active_mass_pos : 0 < ∑ k ∈ active, volume (pre.ZTau k).shade
  max_multiplicity_paid :
    ShadedBody.multiplicity pre.mid (fun k => (pre.ZTau k).toShadedBody) <=
      ((Kakeya.WangZahl.activeRhoParents U b a pre.mid).card : ℝ≥0∞) *
        ShadedBody.multiplicity active (fun k => (pre.ZTau k).toShadedBody)
  kappa : ℝ≥0∞
  kappa_eq : kappa = retainedShareV5W58 active complete
  kappa_ne_zero : kappa ≠ 0
  kappa_ne_top : kappa ≠ ⊤
  kappa_le_one : kappa <= 1
  card_share_exact :
    kappa * (complete.card : ℝ≥0∞) = (active.card : ℝ≥0∞)
  level_le : j <= a
  stopped_parent_eq : pJ = U.nodeAncestor a j q
  stopped_parent_mem : pJ ∈ U.cover.indexSet j
  complete_constant_at_stop : forall k, k ∈ complete ->
    U.nodeAncestor b j k = pJ
  active_constant_at_stop : forall k, k ∈ active ->
    U.nodeAncestor b j k = pJ
  complete_eq_stopped_class :
    Kakeya.WangZahl.tauAncestorClass U b j complete pJ = complete
  active_eq_stopped_class :
    Kakeya.WangZahl.tauAncestorClass U b j active pJ = active
  first_crossing_complete :
    Kakeya.WangZahl.hierarchyGlobalCrossing U b complete
      ((delta : ℝ≥0∞) ^ (3 * p.η m)).toNNReal j
  frostman_complete_levelA :
    frostmanConstIn complete
        (fun k => (U.cover.tube b k).toConvexSpaceBody)
        (U.cover.tube a q).toConvexSpaceBody <=
      completeLevelAFrostmanBudgetV5W58 delta N a b m p
  frostman_active_levelA :
    frostmanConstIn active
        (fun k => (U.cover.tube b k).toConvexSpaceBody)
        (U.cover.tube a q).toConvexSpaceBody <=
      kappa⁻¹ * completeLevelAFrostmanBudgetV5W58 delta N a b m p
  complete_Q_lower_at_a :
    (delta : ℝ≥0∞) ^ (3 * p.η m) <=
      normalizedQV5W58
        (Tube.gridScale delta N b / Tube.gridScale delta N a) complete
  active_Q_lower_at_a_scaled :
    kappa * (delta : ℝ≥0∞) ^ (3 * p.η m) <=
      normalizedQV5W58
        (Tube.gridScale delta N b / Tube.gridScale delta N a) active
  Q_identity_at_a :
    normalizedQV5W58
        (Tube.gridScale delta N b / Tube.gridScale delta N a) active =
      kappa * normalizedQV5W58
        (Tube.gridScale delta N b / Tube.gridScale delta N a) complete
  Q_identity_at_stop :
    normalizedQV5W58
        (Tube.gridScale delta N b / Tube.gridScale delta N j) active =
      kappa * normalizedQV5W58
        (Tube.gridScale delta N b / Tube.gridScale delta N j) complete
  endpoint_or_nonTop_complete :
    (j = 0 /\ Tube.gridScale delta N j = 1 /\
      (delta : ℝ≥0∞) ^ (3 * p.η m) <=
        normalizedQV5W58
          (Tube.gridScale delta N b / Tube.gridScale delta N j) complete) \/
    (0 < j /\ SymmetricCompleteQBandV5W58 delta
      (Tube.gridScale delta N b / Tube.gridScale delta N j)
      complete 1 (3 * p.η m))
  endpoint_or_nonTop_active_scaled :
    (j = 0 /\ Tube.gridScale delta N j = 1 /\
      kappa * (delta : ℝ≥0∞) ^ (3 * p.η m) <=
        normalizedQV5W58
          (Tube.gridScale delta N b / Tube.gridScale delta N j) active) \/
    (0 < j /\ QuotientScaledActiveQBandV5W58 delta
      (Tube.gridScale delta N b / Tube.gridScale delta N j)
      active kappa 1 (3 * p.η m))

end
end Kakeya.ml1Boot.W58QuotientAwareQV5

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.PersistentTrialStateW94
public import Kakeya.DimensionThree.MainLemma1.ScalarFactorization

/-!
# Source construction definitions

Definitions shared by the revised source construction. Fibre notions
`actualDescendantsW95`, `actualRelativeFrostmanW95`, `actualBandParentsW95`; the regularized
tower record `SourceRegularizedWorkingTowerW95` (surjective assignments, count and Frostman
bands); the numerical parameter record `SourcePassNumericsW95` relating `p`, `beta`,
`gammaZero`, `xi`, `xiMin` and `M`; the every-scale Frostman predicate `actualEveryScaleW95`;
the dividing block `ActualSourceDividingBlockW95`; the same-mass selection record
`ActualSameMassSelectionsW95`; the terminal alternative `actualSourceTerminalW95`; and the paid
drop record `SourcePaidDropW95`, together with the cost helpers `sourceFlatDropW95`,
`sourceRestartFuelW95`, `uniformPaidPassCostW95` and `towerPreparationRetainedW95`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ConvexSpaceBody ShadedBody

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

universe uE uI

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

open RevisedLiteralProfileInterfaceFormalizerW87

def actualDescendantsW95 {iota : Type uI} [DecidableEq iota]
    (F : Finset iota) (assign : Nat -> iota -> iota) (k l : Nat) (R : iota) :
    Finset iota :=
  (completeFibreW94 F (assign k) R).image (assign l)

def actualRelativeFrostmanW95 {iota : Type uI} [DecidableEq iota]
    (F : Finset iota) (assign : Nat -> iota -> iota) {rho : Nat -> ℝ≥0}
    (tube : (l : Nat) -> iota -> Tube (rho l) E) (k l : Nat) (R : iota) : ℝ≥0∞ :=
  frostmanConstIn (actualDescendantsW95 F assign k l R)
    (fun S => (tube l S).toConvexSpaceBody) (tube k R).toConvexSpaceBody

def dyadicRangeLengthW95 (H : ℝ≥0∞) : Nat :=
  Nat.floor (Real.log H.toReal / Real.log 2) + 1

def actualBandParentsW95 {iota : Type uI} [DecidableEq iota]
    (F : Finset iota) (assign : Nat -> iota -> iota) {rho : Nat -> ℝ≥0}
    (tube : (l : Nat) -> iota -> Tube (rho l) E)
    (k l a b : Nat) : Finset iota :=
  (F.image (assign k)).filter (fun R =>
    (2 : ℝ≥0∞) ^ a <= (actualDescendantsW95 F assign k l R).card ∧
    ((actualDescendantsW95 F assign k l R).card : ℝ≥0∞) < (2 : ℝ≥0∞) ^ (a + 1) ∧
    (2 : ℝ≥0∞) ^ b <= actualRelativeFrostmanW95 F assign tube k l R ∧
    actualRelativeFrostmanW95 F assign tube k l R < (2 : ℝ≥0∞) ^ (b + 1))

structure SourceRegularizedWorkingTowerW95
    {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}
    {A : Finset iota} {Y : iota -> ShadedTube delta E} {M : Nat} {Ccan : ℝ≥0}
    (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
    (Ctw Ccell : ℝ≥0) where
  surjective : ∀ k, k <= M -> A.image (U.cover.assign k) = U.cover.indexSet k
  bottom_index : U.cover.indexSet M = A
  bottom_assign : ∀ i ∈ A, U.cover.assign M i = i
  bottom_tube : ∀ i ∈ A,
    (U.cover.tube M i).toConvexSpaceBody = (Y i).toConvexSpaceBody
  nice : U.Nice
  parent_ball : ∀ k, k <= M -> ∀ R ∈ U.cover.indexSet k,
    (U.cover.tube k R).carrier ⊆ Metric.closedBall 0 2
  parent_line_ed : ∀ k, k <= M ->
    lineEssentiallyDistinctW94 (U.cover.indexSet k) (U.cover.tube k) Ctw
  geometric_count : ∀ k, k <= M -> ∀ R ∈ U.cover.indexSet k,
    ((exactTubeCellW87 A (fun i => (Y i).toTube) (U.cover.tube k R)).card : ℝ≥0) <=
      Ccell * ((completeFibreW94 A (U.cover.assign k) R).card : ℝ≥0)
  countBand : Nat -> Nat -> ℝ≥0
  countBand_pos : ∀ k l, k < l -> l <= M -> 0 < countBand k l
  count_lower : ∀ k l, k < l -> l <= M -> ∀ R ∈ U.cover.indexSet k,
    countBand k l <= ((actualDescendantsW95 A U.cover.assign k l R).card : ℝ≥0)
  count_upper : ∀ k l, k < l -> l <= M -> ∀ R ∈ U.cover.indexSet k,
    ((actualDescendantsW95 A U.cover.assign k l R).card : ℝ≥0) < 2 * countBand k l
  frostmanBand : Nat -> Nat -> ℝ≥0∞
  frostmanBand_pos : ∀ k l, k < l -> l <= M -> 0 < frostmanBand k l
  frostmanBand_finite : ∀ k l, k < l -> l <= M -> frostmanBand k l < ⊤
  frostman_lower : ∀ k l, k < l -> l <= M -> ∀ R ∈ U.cover.indexSet k,
    frostmanBand k l <= actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k l R
  frostman_upper : ∀ k l, k < l -> l <= M -> ∀ R ∈ U.cover.indexSet k,
    actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k l R < 2 * frostmanBand k l

def towerPreparationRetainedW95 (delta : ℝ≥0) (C : ℝ≥0) (K : Nat) : ℝ≥0∞ :=
  ((C : ℝ≥0∞) * ENNReal.ofReal
    ((2 + Real.log (1 / (delta : ℝ)) / Real.log 2) ^ K))⁻¹

structure SourcePassNumericsW95 (p : Params) (beta gammaZero : ℝ)
    (xi : Fin (p.N + 1) -> ℝ) (xiMin : ℝ) (M : Nat) : Prop where
  beta_pos : 0 < beta
  gammaZero_gt : beta < gammaZero
  gammaZero_le : gammaZero <= 1
  N_large : 5 <= p.N
  epsilon_eq : p.ε = (p.N : ℝ) ^ (-(1 / 2 : ℝ))
  epsilon_pos : 0 < p.ε
  epsilon_small : p.ε < 1 / 3
  gap : 3 * p.ε / 2 <= (gammaZero - beta) / 1000
  zeta_pos : ∀ m, m <= p.N -> 0 < p.η m
  zeta_mono : ∀ k l, k <= l -> l <= p.N -> p.η k <= p.η l
  zeta_top : p.η p.N <= p.ε / 5
  xi_pos : ∀ m : Fin (p.N + 1), m.val < p.N -> 0 < xi m
  xi_beta : ∀ m : Fin (p.N + 1), m.val < p.N ->
    xi m <= 4 * p.ε ^ 3 * beta / 25000
  xi_next : ∀ m : Fin (p.N + 1), m.val < p.N ->
    xi m <= p.ε ^ 2 * beta * p.η (m.val + 1) / 8000
  rung_next : ∀ m, m < p.N -> p.η m <= p.ε * p.η (m + 1) / 100
  rung_xi : ∀ m : Fin (p.N + 1), m.val < p.N -> p.η m.val <= xi m / 200
  xiMin_pos : 0 < xiMin
  xiMin_lower : ∀ m : Fin (p.N + 1), m.val < p.N -> xiMin <= xi m
  xiMin_attained : ∃ m : Fin (p.N + 1), m.val < p.N ∧ xi m = xiMin
  M_pos : 1 <= M
  M_zeta : (1 : ℝ) / M <= p.ε * p.η 0 / 100
  M_xi : (1 : ℝ) / M <= p.ε * xiMin / 200
  M_profile : (1 : ℝ) / M <= p.ε ^ 2 * p.η 0 / 192
  M_next : ∀ m, m < p.N -> (1 : ℝ) / M <= p.ε * p.η (m + 1) / 160000

def actualEveryScaleW95 {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}
    {A : Finset iota} {Y : iota -> ShadedTube delta E} {M : Nat} {Ccan : ℝ≥0}
    (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
    (epsilon : ℝ) (N : Nat) (BF : ℝ≥0) : Prop :=
  ∀ k, k <= M -> ∀ R ∈ U.cover.indexSet k,
    frostmanConstIn (completeFibreW94 A (U.cover.assign k) R)
      (fun i => (Y i).toConvexSpaceBody) (U.cover.tube k R).toConvexSpaceBody <=
        (BF : ℝ≥0∞) ^ (N + 1) * (delta : ℝ≥0∞) ^ (-3 * epsilon)

structure ActualSourceDividingBlockW95
    {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}
    {A : Finset iota} {Y : iota -> ShadedTube delta E} {M : Nat} {Ccan : ℝ≥0}
    (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
    (p : Params) (BF : ℝ≥0) where
  a : Fin (M + 1)
  b : Fin (M + 1)
  a_lt_b : a.val < b.val
  label : Fin (p.N + 1)
  label_active : label.val < p.N
  block_long : Tube.gridScale delta M b.val / Tube.gridScale delta M a.val <=
    delta ^ p.ε
  middle_upper : ∀ R ∈ U.cover.indexSet a.val,
    actualRelativeFrostmanW95 A U.cover.assign U.cover.tube a.val b.val R <=
      ((Tube.gridScale delta M a.val : ℝ≥0∞) /
        (Tube.gridScale delta M b.val : ℝ≥0∞)) ^ p.η label.val
  tail_upper : b.val < M -> ∀ R ∈ U.cover.indexSet b.val,
    frostmanConstIn (completeFibreW94 A (U.cover.assign b.val) R)
      (fun i => (Y i).toConvexSpaceBody) (U.cover.tube b.val R).toConvexSpaceBody <=
        (BF : ℝ≥0∞) ^ p.N *
          ((Tube.gridScale delta M b.val : ℝ≥0∞) / (delta : ℝ≥0∞)) ^ p.η label.val
  intermediate_lower : ∀ l, a.val < l -> l < b.val ->
    ((Tube.gridScale delta M b.val : ℝ≥0∞) /
      (Tube.gridScale delta M a.val : ℝ≥0∞)) ^ (1 - p.ε) <=
        (Tube.gridScale delta M b.val : ℝ≥0∞) / (Tube.gridScale delta M l : ℝ≥0∞) ->
    (Tube.gridScale delta M b.val : ℝ≥0∞) / (Tube.gridScale delta M l : ℝ≥0∞) <=
      ((Tube.gridScale delta M b.val : ℝ≥0∞) /
        (Tube.gridScale delta M a.val : ℝ≥0∞)) ^ p.ε ->
    ∀ R ∈ U.cover.indexSet l,
      (1 / 2 : ℝ≥0∞) *
        ((Tube.gridScale delta M l : ℝ≥0∞) /
          (Tube.gridScale delta M b.val : ℝ≥0∞)) ^ p.η (label.val + 1) <
        actualRelativeFrostmanW95 A U.cover.assign U.cover.tube l b.val R

def sourceFlatDropW95 (p : Params) : ℝ := p.ε ^ 2 * p.η 0 / 32

def sourceRestartFuelW95 (p : Params) (M : Nat) : Nat :=
  Nat.ceil (7 * ((M + 1 : Nat) : ℝ) ^ 2 / sourceFlatDropW95 p)

def uniformPaidPassCostW95 (delta : ℝ≥0) (M CM Ktr : Nat)
    (Cpass : ℝ≥0) : ℝ≥0∞ :=
  actualPaidPassCostW94 delta delta M CM Ktr Cpass

structure ActualSameMassSelectionsW95
    {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}
    {A : Finset iota} {Y : iota -> ShadedTube delta E} {M : Nat} {Ccan : ℝ≥0}
    {U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan}
    {p : Params} {BF : ℝ≥0} (block : ActualSourceDividingBlockW95 U p BF)
    (loss : ℝ≥0) where
  loss_one : 1 <= loss
  firstFamily : Finset iota
  firstShading : iota -> ShadedTube delta E
  firstParents : Finset iota
  firstParentShading : iota -> ShadedTube (Tube.gridScale delta M block.b.val) E
  fineLabel : iota
  firstParentFullness : ℝ≥0
  fineFullness : ℝ≥0
  first : IsOneScaleSelected ((loss : ℝ≥0∞)⁻¹) (loss : ℝ≥0∞)
    A A Y (U.cover.indexSet block.b.val) (U.cover.tube block.b.val)
    (U.cover.assign block.b.val) firstFamily firstShading firstParents
    firstParentShading fineLabel firstParentFullness fineFullness
  middle : Finset iota
  middleShading : iota -> ShadedTube (Tube.gridScale delta M block.b.val) E
  middle_nonempty : middle.Nonempty
  middle_subset : middle ⊆ firstParents
  middle_tube : ∀ Q ∈ middle,
    (middleShading Q).toTube = U.cover.tube block.b.val Q
  normalization : IsCRefinement middle (fun Q => (middleShading Q).toShadedBody)
    firstParents (fun Q => (firstParentShading Q).toShadedBody) loss⁻¹
  commonMass : ℝ≥0
  commonMass_pos : 0 < commonMass
  induced_mass : ∀ Q ∈ middle, volume (middleShading Q).shade =
    (commonMass : ℝ≥0∞) *
      ∑ i ∈ completeFibreW94 firstFamily (U.cover.assign block.b.val) Q,
        volume (firstShading i).shade
  coarseAssign : iota -> iota
  parent_compatibility : ∀ i ∈ A,
    coarseAssign (U.cover.assign block.b.val i) = U.cover.assign block.a.val i
  secondFamily : Finset iota
  secondShading : iota -> ShadedTube (Tube.gridScale delta M block.b.val) E
  coarseFamily : Finset iota
  coarseShading : iota -> ShadedTube (Tube.gridScale delta M block.a.val) E
  middleLabel : iota
  coarseFullness : ℝ≥0
  middleFullness : ℝ≥0
  second : IsOneScaleSelected ((loss : ℝ≥0∞)⁻¹) (loss : ℝ≥0∞)
    (U.cover.indexSet block.b.val) middle
    (zeroExtend middle (U.cover.tube block.b.val) middleShading)
    (U.cover.indexSet block.a.val) (U.cover.tube block.a.val) coarseAssign
    secondFamily secondShading coarseFamily coarseShading
    middleLabel coarseFullness middleFullness
  fineFamily : Finset iota
  fineShading : iota -> ShadedTube delta E
  fine_nonempty : fineFamily.Nonempty
  fine_subset : fineFamily ⊆ firstFamily
  fine_image : fineFamily.image (U.cover.assign block.b.val) = secondFamily
  fine_same_tube : ∀ i ∈ fineFamily, (fineShading i).toTube = (Y i).toTube
  fine_subshade : ∀ i ∈ fineFamily, (fineShading i).shade ⊆ (firstShading i).shade
  weighted_cut : ∀ Q ∈ secondFamily,
    (∑ i ∈ completeFibreW94 fineFamily (U.cover.assign block.b.val) Q,
      volume (fineShading i).shade) =
        (commonMass : ℝ≥0∞)⁻¹ * volume (secondShading Q).shade
  selected_fine_refinement : IsCRefinement
    (completeFibreW94 A (U.cover.assign block.b.val) fineLabel)
    (fun i => ((selectedShade fineFamily Y fineShading) i).toShadedBody)
    (completeFibreW94 A (U.cover.assign block.b.val) fineLabel)
    (fun i => ((selectedShade firstFamily Y firstShading) i).toShadedBody) loss⁻¹
  fine_retention : ((loss : ℝ≥0∞) ^ (3 : Nat))⁻¹ *
    (∑ i ∈ A, volume (Y i).shade) <= ∑ i ∈ fineFamily, volume (fineShading i).shade

def actualSourceTerminalW95
    {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}
    (A : Finset iota) (Y : iota -> ShadedTube delta E)
    (p : Params) (gamma xiMin : ℝ) (M : Nat)
    (Cwork Ctw Ccell BF Cgood : ℝ≥0) : Prop :=
  (ShadedBody.multiplicity A (fun i => (Y i).toShadedBody) <=
    (Cgood : ℝ≥0∞) * (delta : ℝ≥0∞) ^ (18 * xiMin) *
      (delta : ℝ≥0∞) ^ (-2 * gamma) *
      ((delta : ℝ≥0∞) ^ (2 : Nat) * (A.card : ℝ≥0∞)) ^ (1 - gamma / 2)) ∨
  ∃ U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Cwork,
    Nonempty (SourceRegularizedWorkingTowerW95 U Ctw Ccell) ∧
      actualEveryScaleW95 U p.ε p.N BF

structure SourcePaidDropW95
    {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}
    {B : Finset iota} {V : iota -> ShadedTube delta E}
    {M : Nat} {Ccan : ℝ≥0}
    (U0 : CanonicalProfileNetW87 B (fun i => (V i).toTube) M Ccan)
    (current next : RetainedStateW94 B V) (p : Params)
    (CM Kmax : Nat) (Cpass Cwork Ctw Ccell BF : ℝ≥0) where
  step : PaidDropTransitionW94 U0 current next CM Cpass (sourceFlatDropW95 p)
  trial_exponent_bound : step.Ktr <= Kmax
  workingFamily : Finset iota
  working_subset : workingFamily ⊆ current.active
  working_nonempty : workingFamily.Nonempty
  workingNet : CanonicalProfileNetW87 workingFamily
    (fun i => (current.shading i).toTube) M Cwork
  regular : SourceRegularizedWorkingTowerW95 workingNet Ctw Ccell
  block : ActualSourceDividingBlockW95 workingNet p BF
  selectionLoss : ℝ≥0
  selections : ActualSameMassSelectionsW95 block selectionLoss
  trial_scale_eq : step.trialScale =
    Tube.gridScale delta M block.b.val / Tube.gridScale delta M block.a.val
  dagger_same_component : step.daggerFamily ⊆ workingFamily
  dagger_from_cut : step.daggerFamily ⊆ selections.fineFamily
  dagger_cut_subshade : ∀ i ∈ step.daggerFamily,
    (step.Ydagger i).shade ⊆ (selections.fineShading i).shade
  uniform_paid : current.retained /
    uniformPaidPassCostW95 delta M CM Kmax Cpass <= next.retained

end

end Kakeya.ml1Boot.TrialRestartW94

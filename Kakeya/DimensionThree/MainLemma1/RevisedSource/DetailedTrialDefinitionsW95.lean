/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.TrialEntryLemmasW94
public import Kakeya.ChainUniform
public import Kakeya.PartialEstimates
public import Kakeya.DimensionThree.MainLemma1.LiteralProfileHelpersW93

/-!
# Definitions for the detailed Inner Trial

The vocabulary of the revised-source Inner Trial, all in
`Kakeya.ml1Boot.TrialRestartW94`.  `liesInFiveDeltaLineTubeW94` and
`lineEssentiallyDistinctW94` express control of entire affine lines (a cardinality bound `C` on
tubes inside the `5 d`-neighbourhood of any line); `centredTubeW94` says the centre is
perpendicular to the direction.  `DetailedTrialCellsW94` packages a scale ladder `rho`, parent
tubes, assignments and the two-sided cell counts `D`; `DetailedTrialInputW94` records the
analytic hypotheses (fullness, Frostman constant, complete-cell lower bound);
`detailedInnerGoodW94` is the Good alternative with constant one; `DetailedTrialDropW94` is the
Drop witness with mass retention `trialRetainedFractionW94 d Ktr` and both per-cell and
all-exact `Ns` drops.  `detailedTrialAtThresholdW94` is the Good-or-Drop output specification,
and `LabelledDetailedTrialThresholdsW94` is its finite labelled schedule over `Params`.
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

/-- The complete affine-line neighbourhood used in the definition. -/
def liesInFiveDeltaLineTubeW94 {d : ℝ≥0} (T : Tube d E) (o v : E) : Prop :=
  ∀ x ∈ T.carrier, ∃ t : ℝ, dist x (o + t • v) <= 5 * (d : ℝ)

/-- The source controls entire affine lines, including axial translates. -/
def lineEssentiallyDistinctW94 {iota : Type uI} {d : ℝ≥0}
    (F : Finset iota) (T : iota -> Tube d E) (C : ℝ≥0) : Prop :=
  ∀ o v, ‖v‖ = 1 ->
    ((F.filter (fun i => liesInFiveDeltaLineTubeW94 (T i) o v)).card : ℝ≥0) <= C

def centredTubeW94 {d : ℝ≥0} (T : Tube d E) : Prop :=
  inner ℝ T.center T.direction = 0

/-- Actual listed parents and complete assigned cells in the detailed
Inner Trial. Nested maps are not an extra hypothesis of that source lemma. -/
structure DetailedTrialCellsW94 {iota : Type uI} [DecidableEq iota] {d : ℝ≥0}
    (F : Finset iota) (Y : iota -> ShadedTube d E) (L : Nat)
    (rho : Nat -> ℝ≥0) (Ctw Ccell : ℝ≥0) where
  rho_zero : rho 0 = 1
  rho_bottom : rho L = d
  rho_pos : ∀ l, l <= L -> 0 < rho l
  rho_nonincreasing : ∀ l, l < L -> rho (l + 1) <= rho l
  rho_step : ∀ l, l < L ->
    (rho l : ℝ≥0∞) / (rho (l + 1) : ℝ≥0∞) <=
      (d : ℝ≥0∞) ^ (-(2 : ℝ) / (L : ℝ))
  parentSet : Nat -> Finset iota
  parentTube : (l : Nat) -> iota -> Tube (rho l) E
  assign : Nat -> iota -> iota
  assign_image : ∀ l, l <= L -> F.image (assign l) = parentSet l
  assigned_containment : ∀ l, l <= L -> ∀ i ∈ F,
    (Y i).toConvexSpaceBody <= (parentTube l (assign l i)).toConvexSpaceBody
  parent_ball : ∀ l, l <= L -> ∀ R ∈ parentSet l,
    (parentTube l R).carrier ⊆ Metric.closedBall 0 2
  parent_line_ed : ∀ l, l <= L ->
    lineEssentiallyDistinctW94 (parentSet l) (parentTube l) Ctw
  D : Nat -> ℝ≥0
  D_pos : ∀ l, l <= L -> 0 < D l
  geometric_lower : ∀ l, l <= L -> ∀ R ∈ parentSet l,
    D l <= ((exactTubeCellW87 F (fun i => (Y i).toTube) (parentTube l R)).card : ℝ≥0)
  geometric_upper : ∀ l, l <= L -> ∀ R ∈ parentSet l,
    ((exactTubeCellW87 F (fun i => (Y i).toTube) (parentTube l R)).card : ℝ≥0) <
      2 * Ccell * D l
  assigned_lower : ∀ l, l <= L -> ∀ R ∈ parentSet l,
    D l <= ((completeFibreW94 F (assign l) R).card : ℝ≥0)

/-- The actual analytic inputs, with the lower bound on old complete cells. -/
structure DetailedTrialInputW94 {iota : Type uI} [DecidableEq iota] {d : ℝ≥0}
    {F : Finset iota} {Y : iota -> ShadedTube d E} {L : Nat}
    {rho : Nat -> ℝ≥0} {Ctw Ccell : ℝ≥0}
    (cells : DetailedTrialCellsW94 F Y L rho Ctw Ccell)
    (epsilon xi zetaPlus etaLambda : ℝ) : Prop where
  nonempty : F.Nonempty
  ball : ∀ i ∈ F, (Y i).carrier ⊆ Metric.closedBall 0 1
  centred : ∀ i ∈ F, centredTubeW94 (Y i).toTube
  line_ed : lineEssentiallyDistinctW94 F (fun i => (Y i).toTube) Ctw
  fullness : (d : ℝ≥0∞) ^ etaLambda <= fullness' F (fun i => (Y i).toShadedBody)
  frostman : frostmanConstIn F (fun i => (Y i).toConvexSpaceBody)
    ConvexSpaceBody.closedUnitBall <= (d : ℝ≥0∞) ^ (-xi / 160)
  complete_cell_lower : ∀ l, l <= L ->
    (d : ℝ≥0∞) ^ (1 - 3 * epsilon / 2) <= (rho l : ℝ≥0∞) ->
    (rho l : ℝ≥0∞) <= (d : ℝ≥0∞) ^ (3 * epsilon / 2) ->
    ∀ R ∈ cells.parentSet l,
      (1 / 2 : ℝ≥0∞) * ((rho l : ℝ≥0∞) / (d : ℝ≥0∞)) ^ zetaPlus <
        frostmanConstIn (completeFibreW94 F (cells.assign l) R)
          (fun i => (Y i).toConvexSpaceBody) (cells.parentTube l R).toConvexSpaceBody

/-- The detailed source has constant one in this literal Good alternative. -/
def detailedInnerGoodW94 {iota : Type uI} {d : ℝ≥0}
    (F : Finset iota) (Y : iota -> ShadedTube d E)
    (gamma epsilon xi : ℝ) : Prop :=
  ShadedBody.multiplicity F (fun i => (Y i).toShadedBody) <=
    (d : ℝ≥0∞) ^ (20 * xi / epsilon) * (d : ℝ≥0∞) ^ (-2 * gamma) *
      ((d : ℝ≥0∞) ^ (2 : Nat) * (F.card : ℝ≥0∞)) ^ (1 - gamma / 2)

def trialRetainedFractionW94 (d : ℝ≥0) (Ktr : Nat) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 + Real.log (1 / (d : ℝ))) ^ (-(Ktr : ℝ)))

/-- The same actual refinement witnesses both the per-cell and all-exact
Ns bounds. The new partition is not silently identified with an old cell. -/
structure DetailedTrialDropW94 {iota : Type uI} [DecidableEq iota] {d : ℝ≥0}
    {F : Finset iota} {Y : iota -> ShadedTube d E} {L : Nat}
    {rho : Nat -> ℝ≥0} {Ctw Ccell : ℝ≥0}
    (cells : DetailedTrialCellsW94 F Y L rho Ctw Ccell)
    (epsilon zetaPlus : ℝ) (Ktr : Nat) where
  level : Fin (L + 1)
  Fplus : Finset iota
  Yplus : iota -> ShadedTube d E
  Fplus_nonempty : Fplus.Nonempty
  Fplus_subset : Fplus ⊆ F
  same_tube : ∀ i ∈ Fplus, (Yplus i).toTube = (Y i).toTube
  subshade : ∀ i ∈ Fplus, (Yplus i).shade ⊆ (Y i).shade
  nodes : Finset iota
  nodes_nonempty : nodes.Nonempty
  nodes_subset : nodes ⊆ cells.parentSet level.val
  assignPlus : iota -> iota
  assignPlus_image : Fplus.image assignPlus = nodes
  assigned_cover : Fplus = nodes.biUnion (completeFibreW94 Fplus assignPlus)
  assigned_disjoint : (nodes : Set iota).Pairwise (fun P Q =>
    Disjoint (completeFibreW94 Fplus assignPlus P) (completeFibreW94 Fplus assignPlus Q))
  assigned_containment : ∀ P ∈ nodes,
    completeFibreW94 Fplus assignPlus P ⊆
      exactTubeCellW87 F (fun i => (Y i).toTube) (cells.parentTube level.val P)
  card_le : Fplus.card <= F.card
  mass_retention : trialRetainedFractionW94 d Ktr * (∑ i ∈ F, volume (Y i).shade) <=
    ∑ i ∈ Fplus, volume (Yplus i).shade
  per_cell_density_drop : ∀ P ∈ nodes,
    Kakeya.maxDensity (completeFibreW94 Fplus assignPlus P)
        (fun i => (Yplus i).toConvexSpaceBody) <=
      (d : ℝ≥0∞) ^ (epsilon * zetaPlus / 4) *
        allExactTubeNsW87 F (fun i => (Y i).toTube) (rho level.val)
  exact_Ns_drop : allExactTubeNsW87 Fplus (fun i => (Yplus i).toTube) (rho level.val) <=
    (d : ℝ≥0∞) ^ (epsilon * zetaPlus / 8) *
      allExactTubeNsW87 F (fun i => (Y i).toTube) (rho level.val)

/-- This is an output specification of the actual threshold construction.
No producer theorem below takes it as an analytic callback. -/
def detailedTrialAtThresholdW94
    (gamma epsilon xi zetaPlus : ℝ) (Ctw Ccell : ℝ≥0) (L : Nat)
    (etaLambda : ℝ) (d0 : ℝ≥0) (Ktr : Nat) : Prop :=
  ∀ {d : ℝ≥0}, 0 < d -> d < d0 ->
    ∀ {iota : Type uI} [DecidableEq iota]
      (F : Finset iota) (Y : iota -> ShadedTube d E) (rho : Nat -> ℝ≥0)
      (cells : DetailedTrialCellsW94 F Y L rho Ctw Ccell),
      DetailedTrialInputW94 cells epsilon xi zetaPlus etaLambda ->
      detailedInnerGoodW94 F Y gamma epsilon xi ∨
        Nonempty (DetailedTrialDropW94 cells epsilon zetaPlus Ktr)

/-- A label uses zeta_(m+1), with its own returned threshold and loss.
This schedule is construction output, never an input to the trial theorem. -/
structure LabelledDetailedTrialThresholdsW94 (p : Params)
    (xi : Fin (p.N + 1) -> ℝ) (gamma : ℝ) (Ctw Ccell : ℝ≥0) (L : Nat) where
  inner : Fin (p.N + 1) -> ℝ
  cutoff : Fin (p.N + 1) -> ℝ≥0
  Ktr : Fin (p.N + 1) -> Nat
  inner_pos : ∀ m, 0 < inner m
  cutoff_pos : ∀ m, 0 < cutoff m
  cutoff_lt_one : ∀ m, cutoff m < 1
  Ktr_pos : ∀ m, 1 <= Ktr m
  actual_trial : ∀ m, m.val < p.N ->
    detailedTrialAtThresholdW94.{uE, uI} (E := E) gamma p.ε (xi m) (p.η (m.val + 1))
      Ctw Ccell L (inner m) (cutoff m) (Ktr m)

end

end Kakeya.ml1Boot.TrialRestartW94

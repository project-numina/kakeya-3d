/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceAssignedNormalizationW97

/-!
# Eligible trial calls

Defines the second ambient family `actualSecondAmbientW97` (zero-extended second selection at
level `b`), the eligible theta-parents `actualEligibleThetaParentsW97` (level-`a` parents whose
descendant second shades carry at least `delta^etaLambda`-fullness relative to `Cext`), and the
record `ActualEligibleTrialCallsW97`, which bundles for every eligible parent an
`ActualAssignedUnitNormalizationW97`, the `DetailedTrialInputW94` hypotheses, the mass retention
`1/2` bound, and the Good-or-Drop outcome. Consumed by the window trial, transport and Good files.
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
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

open RevisedLiteralProfileInterfaceFormalizerW87

def actualSecondAmbientW97
    {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}
    {A : Finset iota} {Y : iota -> ShadedTube delta E} {M : Nat} {Ccan : ℝ≥0}
    {U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan}
    {p : Params} {BF loss : ℝ≥0} {block : ActualSourceDividingBlockW95 U p BF}
    (selections : ActualSameMassSelectionsW95 block loss) :
    iota -> ShadedTube (Tube.gridScale delta M block.b.val) E :=
  zeroExtend selections.secondFamily (U.cover.tube block.b.val) selections.secondShading

def actualEligibleThetaParentsW97
    {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}
    {A : Finset iota} {Y : iota -> ShadedTube delta E} {M : Nat} {Ccan : ℝ≥0}
    {U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan}
    {p : Params} {BF loss : ℝ≥0} {block : ActualSourceDividingBlockW95 U p BF}
    (selections : ActualSameMassSelectionsW95 block loss) (Cext : ℝ≥0) (etaLambda : ℝ) : Finset iota :=
  (U.cover.indexSet block.a.val).filter (fun R =>
    (Cext : ℝ≥0∞) *
      ((Tube.gridScale delta M block.b.val / Tube.gridScale delta M block.a.val : ℝ≥0) : ℝ≥0∞) ^ etaLambda *
        (∑ Q ∈ actualDescendantsW95 A U.cover.assign block.a.val block.b.val R,
          volume (U.cover.tube block.b.val Q).carrier) <=
      ∑ Q ∈ actualDescendantsW95 A U.cover.assign block.a.val block.b.val R,
        volume (actualSecondAmbientW97 selections Q).shade)

/-- Genuine per-fibre input and output on the SAME full ambient labels. -/
structure ActualEligibleTrialCallsW97
    {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}
    {A : Finset iota} {Y : iota -> ShadedTube delta E} {M : Nat} {Ccan : ℝ≥0}
    {U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan}
    (Uext : CanonicalProfileNetW87 A (fun i => (Y i).toTube) (M * M) Ccan)
    {p : Params} {BF loss : ℝ≥0} (block : ActualSourceDividingBlockW95 U p BF)
    (selections : ActualSameMassSelectionsW95 block loss)
    (xi : Fin (p.N + 1) -> ℝ) (gamma : ℝ)
    (Rnorm Cext Cnorm CtwNorm CcellNorm : ℝ≥0)
    (aux : AuxiliaryHalfEtaThresholdsW97.{uE, uI} (E := E) p xi gamma CtwNorm CcellNorm M) where
  eligible_nonempty : (actualEligibleThetaParentsW97 selections Cext (aux.inner block.label)).Nonempty
  mass_retention : (1 / 2 : ℝ≥0∞) *
      (∑ Q ∈ U.cover.indexSet block.b.val, volume (actualSecondAmbientW97 selections Q).shade) <=
    ∑ R ∈ actualEligibleThetaParentsW97 selections Cext (aux.inner block.label),
      ∑ Q ∈ actualDescendantsW95 A U.cover.assign block.a.val block.b.val R,
        volume (actualSecondAmbientW97 selections Q).shade
  normalization : ∀ R ∈ actualEligibleThetaParentsW97 selections Cext (aux.inner block.label),
    ActualAssignedUnitNormalizationW97 U Uext block.a.val block.b.val R
      (actualSecondAmbientW97 selections) Rnorm Cext Cnorm CtwNorm CcellNorm
  input : ∀ R (hR : R ∈ actualEligibleThetaParentsW97 selections Cext (aux.inner block.label)),
    DetailedTrialInputW94 (normalization R hR).cells p.ε (xi block.label)
      (p.η (block.label.val + 1) / 2) (aux.inner block.label)
  outcome : ∀ R (hR : R ∈ actualEligibleThetaParentsW97 selections Cext (aux.inner block.label)),
    detailedInnerGoodW94 (actualDescendantsW95 A U.cover.assign block.a.val block.b.val R)
      (normalization R hR).normalized gamma p.ε (xi block.label) ∨
    Nonempty (DetailedTrialDropW94 (normalization R hR).cells p.ε
      (p.η (block.label.val + 1) / 2) (aux.Ktr block.label))

end

end Kakeya.ml1Boot.TrialRestartW94

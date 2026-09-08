/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceQuotientGridW97
public import Kakeya.Tube.Rescale

/-!
# Assigned unit normalization record (C4 output)

Defines the structure `Kakeya.ml1Boot.TrialRestartW94.ActualAssignedUnitNormalizationW97`, the
output of the C4 normalization on one full old theta-fibre of a canonical profile net `U` and its
`M*M` extension `Uext`. It packages the normalized shaded tubes, the `DetailedTrialCellsW94` on
the quotient grid, the identities tying the cells' assignments and parent sets to `Uext`, the
affine rescaling map (direction, centre, image of carrier and shade, Jacobian), volume
comparisons, Frostman-constant comparisons with `actualRelativeFrostmanW95`, and preservation of
fullness and multiplicity. No theorems; this is the interface consumed by the eligible-calls and
window-trial files.
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

/-- C4 output on one FULL old theta-fibre. The affine map, every old label,
every quotient assignment, and the complete-cell denominator remain visible. -/
structure ActualAssignedUnitNormalizationW97
    {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}
    {A : Finset iota} {Y : iota -> ShadedTube delta E} {M : Nat} {Ccan : ℝ≥0}
    (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
    (Uext : CanonicalProfileNetW87 A (fun i => (Y i).toTube) (M * M) Ccan)
    (a b : Nat) (R : iota) (Z : iota -> ShadedTube (Tube.gridScale delta M b) E)
    (Rnorm Cext Cnorm CtwNorm CcellNorm : ℝ≥0) where
  normalized : iota -> ShadedTube (Tube.gridScale delta M b / Tube.gridScale delta M a) E
  cells : DetailedTrialCellsW94 (actualDescendantsW95 A U.cover.assign a b R)
    normalized M (Tube.gridScale (Tube.gridScale delta M b / Tube.gridScale delta M a) M)
    CtwNorm CcellNorm
  assign_eq : ∀ l, l <= M -> cells.assign l =
    Kakeya.ML2Reduction.coarseNode Uext.cover.toChain (quotientGridIndexW97 M a b l) (b * M)
  parents_eq : ∀ l, l <= M -> cells.parentSet l =
    actualDescendantsW95 A Uext.cover.assign (a * M) (quotientGridIndexW97 M a b l) R
  assigned_eq : ∀ l, l <= M -> ∀ S ∈ cells.parentSet l,
    completeFibreW94 (actualDescendantsW95 A U.cover.assign a b R) (cells.assign l) S =
      actualDescendantsW95 A Uext.cover.assign (quotientGridIndexW97 M a b l) (b * M) S
  ball : ∀ Q ∈ actualDescendantsW95 A U.cover.assign a b R,
    (normalized Q).carrier ⊆ Metric.closedBall 0 1
  centred : ∀ Q ∈ actualDescendantsW95 A U.cover.assign a b R, centredTubeW94 (normalized Q).toTube
  line_ed : lineEssentiallyDistinctW94 (actualDescendantsW95 A U.cover.assign a b R)
    (fun Q => (normalized Q).toTube) CtwNorm
  fine_direction : ∀ Q ∈ actualDescendantsW95 A U.cover.assign a b R,
    let v := ((U.cover.tube a R).rescaleMap (Rnorm : ℝ)).linear (U.cover.tube b Q).direction
    (normalized Q).toTube.direction = ‖v‖⁻¹ • v
  fine_centre : ∀ Q ∈ actualDescendantsW95 A U.cover.assign a b R,
    let x := (U.cover.tube a R).rescaleMap (Rnorm : ℝ) (U.cover.tube b Q).center
    (normalized Q).toTube.center = x - inner ℝ x (normalized Q).toTube.direction •
      (normalized Q).toTube.direction
  image_carrier : ∀ Q ∈ actualDescendantsW95 A U.cover.assign a b R,
    (U.cover.tube a R).rescaleMap (Rnorm : ℝ) '' (U.cover.tube b Q).carrier ⊆
      (normalized Q).carrier
  image_shade : ∀ Q ∈ actualDescendantsW95 A U.cover.assign a b R,
    (normalized Q).shade = (U.cover.tube a R).rescaleMap (Rnorm : ℝ) '' (Z Q).shade
  jacobian : ℝ≥0
  jacobian_pos : 0 < jacobian
  jacobian_eq : (jacobian : ℝ≥0∞) =
    (4 * (Rnorm : ℝ≥0∞)) ^ (-3 : ℝ) * (Tube.gridScale delta M a : ℝ≥0∞) ^ (-2 : ℝ)
  volume_image : ∀ S : Set E, MeasurableSet S ->
    volume ((U.cover.tube a R).rescaleMap (Rnorm : ℝ) '' S) = (jacobian : ℝ≥0∞) * volume S
  carrier_volume : ∀ Q ∈ actualDescendantsW95 A U.cover.assign a b R,
    (jacobian : ℝ≥0∞) * volume (U.cover.tube b Q).carrier <= volume (normalized Q).carrier ∧
    volume (normalized Q).carrier <= (Cext : ℝ≥0∞) * (jacobian : ℝ≥0∞) *
      volume (U.cover.tube b Q).carrier
  parent_image : ∀ l, l <= M -> ∀ S ∈ cells.parentSet l,
    (U.cover.tube a R).rescaleMap (Rnorm : ℝ) ''
      (Uext.cover.tube (quotientGridIndexW97 M a b l) S).carrier ⊆ (cells.parentTube l S).carrier
  parent_volume : ∀ l, l <= M -> ∀ S ∈ cells.parentSet l,
    (jacobian : ℝ≥0∞) * volume (Uext.cover.tube (quotientGridIndexW97 M a b l) S).carrier <=
      volume (cells.parentTube l S).carrier ∧
    volume (cells.parentTube l S).carrier <= (Cext : ℝ≥0∞) * (jacobian : ℝ≥0∞) *
      volume (Uext.cover.tube (quotientGridIndexW97 M a b l) S).carrier
  forward_test : ∀ K : ConvexSpaceBody E, ∃ D : ConvexSpaceBody E,
    volume D.carrier <= (Cext : ℝ≥0∞) * (jacobian : ℝ≥0∞) * volume K.carrier ∧
    (∀ Q ∈ actualDescendantsW95 A U.cover.assign a b R,
      (U.cover.tube b Q).toConvexSpaceBody <= K -> (normalized Q).toConvexSpaceBody <= D)
  backward_test : ∀ K : ConvexSpaceBody E, ∃ D : ConvexSpaceBody E,
    volume D.carrier <= (Cext : ℝ≥0∞) * (jacobian : ℝ≥0∞)⁻¹ * volume K.carrier ∧
    (∀ Q ∈ actualDescendantsW95 A U.cover.assign a b R,
      (normalized Q).toConvexSpaceBody <= K -> (U.cover.tube b Q).toConvexSpaceBody <= D)
  whole_cf :
    (Cnorm : ℝ≥0∞)⁻¹ * actualRelativeFrostmanW95 A U.cover.assign U.cover.tube a b R <=
      frostmanConstIn (actualDescendantsW95 A U.cover.assign a b R)
        (fun Q => (normalized Q).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall ∧
    frostmanConstIn (actualDescendantsW95 A U.cover.assign a b R)
      (fun Q => (normalized Q).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall <=
      (Cnorm : ℝ≥0∞) * actualRelativeFrostmanW95 A U.cover.assign U.cover.tube a b R
  assigned_cf : ∀ l, l <= M -> ∀ S ∈ cells.parentSet l,
    (Cnorm : ℝ≥0∞)⁻¹ * actualRelativeFrostmanW95 A Uext.cover.assign Uext.cover.tube
      (quotientGridIndexW97 M a b l) (b * M) S <=
      frostmanConstIn (completeFibreW94 (actualDescendantsW95 A U.cover.assign a b R) (cells.assign l) S)
        (fun Q => (normalized Q).toConvexSpaceBody) (cells.parentTube l S).toConvexSpaceBody ∧
    frostmanConstIn (completeFibreW94 (actualDescendantsW95 A U.cover.assign a b R) (cells.assign l) S)
      (fun Q => (normalized Q).toConvexSpaceBody) (cells.parentTube l S).toConvexSpaceBody <=
      (Cnorm : ℝ≥0∞) * actualRelativeFrostmanW95 A Uext.cover.assign Uext.cover.tube
        (quotientGridIndexW97 M a b l) (b * M) S
  nearby : Nat -> iota -> Finset iota
  nearby_subset : ∀ l, l <= M -> ∀ S ∈ cells.parentSet l, nearby l S ⊆ cells.parentSet l
  nearby_card : ∀ l, l <= M -> ∀ S ∈ cells.parentSet l, ((nearby l S).card : ℝ≥0) <= Cnorm
  complete_cell_cover : ∀ l, l <= M -> ∀ S ∈ cells.parentSet l,
    exactTubeCellW87 (actualDescendantsW95 A U.cover.assign a b R)
      (fun Q => (normalized Q).toTube) (cells.parentTube l S) ⊆
      (nearby l S).biUnion (completeFibreW94 (actualDescendantsW95 A U.cover.assign a b R) (cells.assign l))
  enlarged_denominator : ∀ l, l <= M -> ∀ S ∈ cells.parentSet l,
    ∀ D : ConvexSpaceBody E, (cells.parentTube l S).toConvexSpaceBody <= D ->
      volume D.carrier <= (Cext : ℝ≥0∞) * volume (cells.parentTube l S).carrier ->
      ((familyIn (actualDescendantsW95 A U.cover.assign a b R)
          (fun Q => (normalized Q).toConvexSpaceBody) D).card : ℝ≥0) <=
        Cnorm * ((completeFibreW94 (actualDescendantsW95 A U.cover.assign a b R) (cells.assign l) S).card : ℝ≥0)
  fullness : (Cext : ℝ≥0∞)⁻¹ * fullness' (actualDescendantsW95 A U.cover.assign a b R)
      (fun Q => (Z Q).toShadedBody) <=
    fullness' (actualDescendantsW95 A U.cover.assign a b R) (fun Q => (normalized Q).toShadedBody)
  multiplicity : ShadedBody.multiplicity (actualDescendantsW95 A U.cover.assign a b R)
      (fun Q => (normalized Q).toShadedBody) =
    ShadedBody.multiplicity (actualDescendantsW95 A U.cover.assign a b R) (fun Q => (Z Q).toShadedBody)

end

end Kakeya.ml1Boot.TrialRestartW94

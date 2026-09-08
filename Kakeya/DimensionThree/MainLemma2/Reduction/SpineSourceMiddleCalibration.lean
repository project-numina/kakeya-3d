/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceLateChoice
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceFactorCeilings
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineHfacProducer

/-!
# Scalar calibration of the middle rung

Fixes the middle-rung scalar choices before any runtime state:
`Kakeya.ML2Assembly.sourceMiddleCardBudget`, `sourceMiddleSmallLoss`, `sourceMiddleCardPower`,
`sourceMiddleDensityExponent` and `sourceMiddleNextZeta`, the caps record
`SourceMiddleSourceCaps` and the finite ceiling record `SourceMiddleFiniteChoices`.
`sourceMiddle_exists_fixed_integer` and `sourceMiddle_exists_finite_choices` make these
choices from `Lemma91ParamsAt` and the factor ceilings of `SpineSourceFactorCeilings`. The
calibration lemmas `sourceMiddle_fullness_calibration`,
`sourceMiddle_site_fullness_calibration` and `sourceMiddle_density_calibration` pay the
fullness and density rows, and `sourceMiddle_exists_uniform_threshold` fixes one `delta0`
below which all loss bounds hold uniformly.
-/

@[expose] public section

open Filter Kakeya.ML2Reduction
open scoped NNReal ENNReal Topology

namespace Kakeya.ML2Assembly

universe u

noncomputable def sourceMiddleCardBudget (varpi zeta : ℝ) : ℝ := varpi * zeta / 16

noncomputable def sourceMiddleSmallLoss (varpi zeta v d : ℝ) : ℝ :=
  min (sourceMiddleCardBudget varpi zeta) (sourceMiddleCenter v d) / 8

noncomputable def sourceMiddleCardPower (e : ℝ) : Nat := Nat.ceil (8 / e) + 1

/-- The earlier source choices in the finite minimum labelled ml2-nonc-input. -/
structure SourceMiddleSourceCaps (N : Nat) where
  nuC : ℝ
  epsSc : ℝ
  etaOne : ℝ
  hOne : ℝ
  hTwo : ℝ
  etaFine : Nat -> ℝ
  etaParent : Nat -> ℝ
  nuC_pos : 0 < nuC
  epsSc_pos : 0 < epsSc
  etaOne_pos : 0 < etaOne
  hOne_pos : 0 < hOne
  hTwo_pos : 0 < hTwo
  etaFine_pos : forall m, m < N -> 0 < etaFine m
  etaParent_pos : forall m, m < N -> 0 < etaParent m

/-- Each finite source ceiling and all three strict R4 gaps on its actual rung. -/
structure SourceMiddleFiniteChoices (N : Nat) (e varpi : ℝ)
    (zeta v d : Nat -> ℝ) (caps : SourceMiddleSourceCaps N) (etaC : ℝ) : Prop where
  input_ceiling_pos : 0 < etaC
  nonsticky_gain : etaC <= caps.nuC / 100
  scale_accuracy : etaC <= e * caps.epsSc * caps.etaOne / 224
  auxiliary_one : etaC <= caps.hOne / 100
  auxiliary_two : etaC <= caps.hTwo / 100
  first_rung : etaC <= caps.etaOne / 2
  raw_density : forall m, m < N -> etaC <= e * d m / 28
  fine_input : forall m, m < N -> etaC <= caps.etaFine m
  parent_input : forall m, m < N -> etaC <= caps.etaParent m / 4
  middle_fullness : forall m, m < N ->
    etaC <= e * sourceMiddleSmallLoss varpi (zeta m) (v m) (d m) / 24
  middle_retention : forall m, m < N -> etaC <= e * varpi * zeta m / 100
  card_budget_pos : forall m, m < N -> 0 < sourceMiddleCardBudget varpi (zeta m)
  center_pos : forall m, m < N -> 0 < sourceMiddleCenter (v m) (d m)
  small_loss_pos : forall m, m < N ->
    0 < sourceMiddleSmallLoss varpi (zeta m) (v m) (d m)
  small_loss_le_center : forall m, m < N ->
    sourceMiddleSmallLoss varpi (zeta m) (v m) (d m) <= sourceMiddleCenter (v m) (d m)
  card_gap : forall m, m < N ->
    2 * sourceMiddleSmallLoss varpi (zeta m) (v m) (d m) <
      sourceMiddleCardBudget varpi (zeta m)
  mass_gap : forall m, m < N ->
    3 * sourceMiddleSmallLoss varpi (zeta m) (v m) (d m) <
      3 * sourceMiddleCenter (v m) (d m)
  card_power_pos : 0 < sourceMiddleCardPower e
  card_power_bound : 4 <= e * (sourceMiddleCardPower e : ℝ) / 2

end Kakeya.ML2Assembly

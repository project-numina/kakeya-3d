/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceEccentricNormalizationData
public import Kakeya.Tube.EssentiallyDistinctShadeSelection

/-!
# ED and assigned-count selection inside the normalized fine cell

`Kakeya.ML2Core.SourceEccentricAssignedSelection` records one essentially-distinct refinement
of the chosen fine cell of a `SourceEccentricCellNormalization`: the ED leaves and their mass
price, the retained `leaves` with subshading, `C`-refinement, fullness and multiplicity at loss
`Lsel`, the occupied `parents` under `Q.place m`, and per-old-part retention in the kept factor
parts. The main theorem `source_exists_eccentric_ED_assigned_refinement` produces it for the
fixed constants `sourceThreadConstant`, `sourceBottomED`, `sourceLevelED`, eventually in
`delta`, uniformly in the later `bias`, at cost `sourceEccentricSelectionCost`. It uses
`Kakeya.Tube.EssentiallyDistinctShadeSelection` and feeds the factor transport.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

universe u

variable {iota : Type u} {delta : ℝ≥0} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace ℝ (Fin 3))} {M C : Nat}

/-- One actual fine ED/count selection, with its genuine occupied parents and
the retained fractions in every kept old factor. These are private terminal
restrictions; no inherited Q statistics are claimed for the selected leaves. -/
structure SourceEccentricAssignedSelection (Q : SourceThreadedTower S T M C)
    {Z : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3))}
    {a m : Nat} {Lout : ℝ≥0} (O : SourceEccentricOuterSplit Q Z a Lout)
    {Rnorm : ℝ} {Cgeom cParent : ℝ≥0}
    (Nrm : SourceEccentricCellNormalization Q O m Rnorm Cgeom cParent)
    {etaParent bias : ℝ} {D aw bw cw : ℝ≥0}
    (E : SourceZeroEccentricFactors Q Z a m etaParent bias D aw bw cw)
    (Lsel Ccount : ℝ≥0) where
  edLeaves : Finset iota
  ed_subset : edLeaves <= Q.cell a O.chosen
  ed_pairwise : (edLeaves : Set iota).Pairwise
    (fun i j => _root_.IsEssentiallyDistinct (Nrm.fine i).carrier (Nrm.fine j).carrier)
  ed_mass_price : (∑ i ∈ Q.cell a O.chosen, volume (Nrm.fine i).shade) <=
    (1 + Tube.refineToEssDistinctLeaves.C 3 *
      Kakeya.maxDensity (Q.cell a O.chosen) (fun i => (Nrm.fine i).toConvexSpaceBody)) *
      ∑ i ∈ edLeaves, volume (Nrm.fine i).shade
  leaves : Finset iota
  leaves_subset_ed : leaves <= edLeaves
  leaves_subset : leaves <= Q.cell a O.chosen
  leaves_nonempty : leaves.Nonempty
  shading : iota -> ShadedTube (sourceEccentricFineScale delta M a) (EuclideanSpace ℝ (Fin 3))
  same_tubes : forall i, (shading i).toTube = (Nrm.fine i).toTube
  subshade : forall i, (shading i).shade <= (Nrm.fine i).shade
  essentially_distinct : (leaves : Set iota).Pairwise
    (fun i j => _root_.IsEssentiallyDistinct (shading i).carrier (shading j).carrier)
  refinement : ShadedBody.IsCRefinement leaves (fun i => (shading i).toShadedBody)
    (Q.cell a O.chosen) (fun i => (Nrm.fine i).toShadedBody) Lsel⁻¹
  mass : (∑ i ∈ Q.cell a O.chosen, volume (Nrm.fine i).shade) <=
    (Lsel : ℝ≥0∞) * ∑ i ∈ leaves, volume (shading i).shade
  union_subset : (⋃ i ∈ leaves, (shading i).shade) <=
    ⋃ i ∈ Q.cell a O.chosen, (Nrm.fine i).shade
  fullness : ShadedBody.fullness (Q.cell a O.chosen) (fun i => (Nrm.fine i).toShadedBody) / Lsel <=
    ShadedBody.fullness leaves (fun i => (shading i).toShadedBody)
  multiplicity : ShadedBody.multiplicity (Q.cell a O.chosen) (fun i => (Nrm.fine i).toShadedBody) <=
    (Lsel : ℝ≥0∞) * ShadedBody.multiplicity leaves (fun i => (shading i).toShadedBody)
  parents : Finset iota
  parents_eq : parents = leaves.image (Q.place m)
  parents_subset : parents <= Q.fibre a m O.chosen
  parents_nonempty : parents.Nonempty
  parent_ball : forall k, k ∈ parents -> (Nrm.parent k).carrier <= Metric.closedBall 0 1
  n : ℝ≥0
  Cfib : ℝ≥0
  n_positive : 0 < n
  Cfib_one : 1 <= Cfib
  Cfib_bound : Cfib <= Ccount
  fibre_nonempty : forall k, k ∈ parents ->
    (leaves.filter (fun i => Q.place m i = k)).Nonempty
  fibre_lower : forall k, k ∈ parents ->
    n / Cfib <= ((leaves.filter (fun i => Q.place m i = k)).card : ℝ≥0)
  fibre_upper : forall k, k ∈ parents ->
    ((leaves.filter (fun i => Q.place m i = k)).card : ℝ≥0) <= Cfib * n
  keptParts : Finset (Finset iota)
  kept_parts_subset : keptParts <= (E.factor O.chosen (O.outer_subset O.chosen_mem)).parts
  kept_parts_nonempty : keptParts.Nonempty
  kept_intersection_nonempty : forall part, part ∈ keptParts -> (part ∩ parents).Nonempty
  kept_cover : keptParts.biUnion (fun part => part ∩ parents) = parents
  partRetention : ℝ≥0
  part_retention_one : 1 <= partRetention
  part_retention_bound : partRetention <= Lsel
  part_card_retention : forall part, part ∈ keptParts ->
    (part.card : ℝ≥0) <= partRetention * ((part ∩ parents).card : ℝ≥0)
  part_volume_retention : forall part, part ∈ keptParts ->
    (∑ k ∈ part, volume (Q.tube m k).carrier) <=
      (partRetention : ℝ≥0∞) * ∑ k ∈ part ∩ parents, volume (Q.tube m k).carrier
  part_mass_retention : forall part, part ∈ keptParts ->
    (∑ i ∈ (Q.cell a O.chosen).filter (fun i => Q.place m i ∈ part),
      volume (Nrm.fine i).shade) <=
      (Lsel : ℝ≥0∞) * ∑ i ∈ leaves.filter (fun i => Q.place m i ∈ part), volume (shading i).shade

end Kakeya.ML2Core

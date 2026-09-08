/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Unconditional.SharedChildGeometry

/-!
# Shared Child Packing

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

namespace Kakeya.Assouad

open Kakeya.Streamlined.GeometricLemmas

def sharedChildParentDegreeBound (factor : ℝ) : ℕ :=
  (2 * Nat.ceil (200 * (4 * factor ^ 2 + 2 * factor)) + 1) ^ 2 *
    (2 * Nat.ceil ((400 * max (8 * factor) 16) * (3 * factor)) + 1) *
    (2 * Nat.ceil (200 * (8 * factor)) + 1) ^ 2

theorem shared_child_parent_neighbor_card_le
    {delta rho factor : ℝ}
    (deltaPos : 0 < delta) (rhoPos : 0 < rho) (factorOne : 1 ≤ factor)
    (scaleSmall : rho ≤ 1 / (200 * factor))
    (childScale : delta ≤ factor * rho)
    {parents : Kakeya.Streamlined.TubeFamily rho}
    (parentsDistinct : parents.IsEssentiallyDistinct)
    (reference : Fin parents.card)
    (neighbors : Finset (Fin parents.card))
    (sharedChild : ∀ j ∈ neighbors,
      ∃ child : Kakeya.DeltaTube delta,
        child.carrier ⊆ wz2PaperCenteredDilatedCarrier factor (parents.tube reference) ∧
        child.carrier ⊆ wz2PaperCenteredDilatedCarrier factor (parents.tube j)) :
    neighbors.card ≤ sharedChildParentDegreeBound factor := by
  let referenceDirection := (parents.tube reference).direction
  let oriented : Fin parents.card → Kakeya.DeltaTube rho :=
    fun i => pureWZ2OrientedParent referenceDirection (parents.tube i)
  let center := wz2PaperTubeMidpoint (parents.tube reference)
  have factorPos : 0 < factor := by linarith
  have rhoOne : rho ≤ 1 := by
    have scaled := (le_div_iff₀ (by positivity : 0 < 200 * factor)).mp scaleSmall
    nlinarith
  have geometry : ∀ j ∈ neighbors,
      ‖(parents.tube j).direction -
        inner ℝ (parents.tube j).direction referenceDirection • referenceDirection‖ ≤
          8 * factor * rho ∧
      ‖(wz2PaperTubeMidpoint (parents.tube j) - center) -
        inner ℝ (wz2PaperTubeMidpoint (parents.tube j) - center)
          referenceDirection • referenceDirection‖ ≤ (4 * factor ^ 2 + 2 * factor) * rho ∧
      |inner ℝ (wz2PaperTubeMidpoint (parents.tube j) - center) referenceDirection| ≤
          3 * factor ∧
      1 / 2 ≤ |inner ℝ (parents.tube j).direction referenceDirection| := by
    intro j jMem
    obtain ⟨child, childReference, childNeighbor⟩ := sharedChild j jMem
    exact shared_child_parent_parameter_bounds deltaPos rhoPos factorOne scaleSmall
      childScale child (parents.tube reference) (parents.tube j) childReference childNeighbor
  have midpointTransverse : ∀ j ∈ neighbors,
      ‖(wz2PaperTubeMidpoint (oriented j) - center) -
        inner ℝ (wz2PaperTubeMidpoint (oriented j) - center)
          referenceDirection • referenceDirection‖ ≤ (4 * factor ^ 2 + 2 * factor) * rho := by
    intro j jMem
    simpa only [oriented, pureWZ2OrientedParent_midpoint] using (geometry j jMem).2.1
  have midpointLongitudinal : ∀ j ∈ neighbors,
      |inner ℝ (wz2PaperTubeMidpoint (oriented j) - center) referenceDirection| ≤
        3 * factor := by
    intro j jMem
    simpa only [oriented, pureWZ2OrientedParent_midpoint] using (geometry j jMem).2.2.1
  have directionTransverse : ∀ j ∈ neighbors,
      ‖(oriented j).direction -
        inner ℝ (oriented j).direction referenceDirection • referenceDirection‖ ≤
          (8 * factor) * rho := by
    intro j jMem
    simpa only [oriented, pureWZ2OrientedParent_transverse] using (geometry j jMem).1
  have directionLongitudinal : ∀ j ∈ neighbors,
      1 / 2 ≤ inner ℝ (oriented j).direction referenceDirection := by
    intro j jMem
    simpa only [oriented, pureWZ2OrientedParent_inner_eq_abs] using (geometry j jMem).2.2.2
  have orientedDistinct : ∀ i j, i ∈ neighbors → j ∈ neighbors → i ≠ j →
      (oriented i).EssentiallyDistinct (oriented j) := by
    intro i j _ _ ijNe
    exact pureWZ2OrientedParent_distinct (parentsDistinct i j ijNe)
  have packing := large_scale_packing_bound rhoPos rhoOne
    (by positivity : 0 ≤ (4 * factor ^ 2 + 2 * factor) * rho)
    (by positivity : 0 ≤ 3 * factor)
    (by positivity : 0 ≤ 8 * factor)
    neighbors center referenceDirection (parents.tube reference).direction_unit
    midpointTransverse midpointLongitudinal directionTransverse directionLongitudinal
    orientedDistinct capsule_lower_bound_instantiation capsule_upper_bound_instantiation
  have radiusCancel :
      200 * ((4 * factor ^ 2 + 2 * factor) * rho) / rho =
        200 * (4 * factor ^ 2 + 2 * factor) := by
    field_simp
  simpa only [radiusCancel, sharedChildParentDegreeBound] using packing

end Kakeya.Assouad

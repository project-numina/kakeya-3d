/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.FrostmanConvexWolff

/-!
# Body C W A To John

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

theorem tubeFamily_mass_eq_card_mul_volume
    {delta : ℝ} (family : Kakeya.Streamlined.TubeFamily delta) :
    family.toBodyFamily.mass = family.toBodyFamily.enncard * Kakeya.deltaTubeVolume delta := by
  have allVolume : ∀ i, (family.toBodyFamily.body i).volume = Kakeya.deltaTubeVolume delta := by
    intro i
    exact Kakeya.Streamlined.tube_volume_eq (family.tube i)
      { base := 0, direction := EuclideanSpace.single (0 : Fin 3) 1,
        direction_unit := by simp }
  simp only [Kakeya.Streamlined.BodyFamily.mass, allVolume,
    Kakeya.Streamlined.BodyFamily.enncard]
  simp [mul_comm]

theorem tubeFamily_containedMass_eq_count_mul_volume
    {delta : ℝ} (family : Kakeya.Streamlined.TubeFamily delta) (set : Set Point3) :
    family.toBodyFamily.containedMass set =
      family.toBodyFamily.containedCount set * Kakeya.deltaTubeVolume delta := by
  have allVolume : ∀ i, (family.toBodyFamily.body i).volume = Kakeya.deltaTubeVolume delta := by
    intro i
    exact Kakeya.Streamlined.tube_volume_eq (family.tube i)
      { base := 0, direction := EuclideanSpace.single (0 : Fin 3) 1,
        direction_unit := by simp }
  simp only [Kakeya.Streamlined.BodyFamily.containedMass, allVolume,
    Kakeya.Streamlined.BodyFamily.containedCount]
  simp [mul_comm]

theorem bodyCWA_to_john_rescaled
    {delta rho : ℝ} (deltaPos : 0 < delta) (rhoPos : 0 < rho)
    {family : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (parent : Fin coarse.card)
    (contained : ∀ i, (family.tube i).carrier ⊆ (coarse.tube parent).carrier)
    (normalization : WZ2PaperAssouadUnitRescalingData (coarse.tube parent))
    {constant : ENNReal}
    (ordinaryCWA : WZ2PaperBodyConvexWolffBound family.toBodyFamily constant) :
    WZ2PaperBodyConvexWolffBound
      { card := family.card
        body := fun i => ⟨normalization.map '' (family.tube i).carrier⟩ }
      (27 * (constant * volume (coarse.tube parent).carrier)) := by
  let identity : Kakeya.Streamlined.TubeSubfamily family :=
    { family := family, embedding := Function.Embedding.refl _, tube_eq := fun _ => rfl }
  have dilationOne : wz2PaperCenteredDilatedCarrier 1 (coarse.tube parent) =
      (coarse.tube parent).carrier := by simp [wz2PaperCenteredDilatedCarrier]
  apply gwz_frostman_to_john_rescaled_convex_wolff deltaPos rhoPos
    (A := 1) (by norm_num) parent identity
    (fun i => by simpa only [dilationOne] using contained i) normalization
  intro set convexSet _
  change family.toBodyFamily.containedMass set *
    volume (wz2PaperCenteredDilatedCarrier 1 (coarse.tube parent)) ≤ _
  rw [dilationOne, tubeFamily_containedMass_eq_count_mul_volume,
    show identity.family = family from rfl, tubeFamily_mass_eq_card_mul_volume]
  calc
    _ ≤ (constant * volume set * family.toBodyFamily.enncard *
          Kakeya.deltaTubeVolume delta) * volume (coarse.tube parent).carrier := by
      gcongr
      exact ordinaryCWA set convexSet
    _ = _ := by ring

end Kakeya.Assouad

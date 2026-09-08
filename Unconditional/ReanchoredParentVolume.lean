/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Unconditional.ReanchoredParentEnclosure
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeVolume

/-!
# Reanchored Parent Volume

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

theorem reanchored_parent_volume_le
    {rho factor : ℝ} (rhoNonneg : 0 ≤ rho) (factorOne : 1 ≤ factor)
    (center : Point3) (parent : Kakeya.DeltaTube rho) :
    volume (pureWZ2ReanchoredParentTube (A := factor) center parent).carrier ≤
      512 * volume (wz2PaperCenteredDilatedCarrier factor parent) := by
  let reanchored := pureWZ2ReanchoredParentTube (A := factor) center parent
  let thin : Kakeya.DeltaTube rho :=
    { base := reanchored.base
      direction := reanchored.direction
      direction_unit := reanchored.direction_unit }
  have contain : reanchored.carrier ⊆ wz2PaperCenteredDilatedCarrier (8 * factor) thin := by
    have h := coaxial_dilated_carrier_subset
      (by positivity : 0 ≤ 8 * factor * rho)
      (by norm_num : (0 : ℝ) < 1) (by positivity : 0 < 8 * factor)
      reanchored thin rfl (shift := 0) (by simp [thin])
      (by ring_nf; exact le_rfl) (by simp; linarith)
    simpa [wz2PaperCenteredDilatedCarrier] using h
  have volumeEq : volume thin.carrier = volume parent.carrier :=
    Kakeya.Streamlined.tube_volume_eq thin parent
  calc
    _ ≤ volume (wz2PaperCenteredDilatedCarrier (8 * factor) thin) := measure_mono contain
    _ = ENNReal.ofReal ((8 * factor) ^ 3) * volume parent.carrier := by
      rw [wz2_paper_centeredDilatedCarrier_volume, abs_of_nonneg (by positivity), volumeEq]
    _ = 512 * volume (wz2PaperCenteredDilatedCarrier factor parent) := by
      rw [wz2_paper_centeredDilatedCarrier_volume, abs_of_nonneg (by positivity), mul_pow,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8 ^ 3)]
      norm_num
      exact mul_assoc _ _ _

end Kakeya.Assouad

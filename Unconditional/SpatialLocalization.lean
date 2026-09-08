/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZBridge

/-!
# Spatial Localization

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace KakeyaLink.JointSelection

open Kakeya.Streamlined Kakeya.Assouad

theorem exists_fixed_ball_mass_localization (R : ℝ) (hR : 1 ≤ R) :
    ∃ loss : ℕ, 0 < loss ∧
      ∀ {delta : ℝ} {source : TubeFamily delta},
        PureWZ2FixedBallSupport source R →
        ∀ sourceShading : TubeShading source,
          ∃ center : Kakeya.Point3,
            sourceShading.mass ≤ (loss : ENNReal) *
              ∑ index : Fin source.card,
                volume (sourceShading.carrier index ∩ Metric.closedBall center (1 / 4)) := by
  classical
  obtain ⟨centers, hcover⟩ :=
    (isCompact_closedBall (0 : Kakeya.Point3) R).elim_finite_subcover
      (fun center : Kakeya.Point3 => Metric.ball center (1 / 4))
      (fun _ => Metric.isOpen_ball) (by
        intro point _
        exact Set.mem_iUnion.mpr ⟨point, by simp⟩)
  have hcenters : centers.Nonempty := by
    have hzero : (0 : Kakeya.Point3) ∈ Metric.closedBall 0 R := by
      simp only [Metric.mem_closedBall, dist_self]
      linarith
    obtain ⟨center, hcenter, _⟩ := Set.mem_iUnion₂.mp (hcover hzero)
    exact ⟨center, hcenter⟩
  refine ⟨centers.card, Finset.card_pos.mpr hcenters, ?_⟩
  intro delta source hsupport sourceShading
  let weight : Kakeya.Point3 → ENNReal := fun center =>
    ∑ index : Fin source.card,
      volume (sourceShading.carrier index ∩ Metric.closedBall center (1 / 4))
  obtain ⟨center, hcenter, hmax⟩ := centers.exists_max_image weight hcenters
  refine ⟨center, ?_⟩
  have hmass : sourceShading.mass ≤ ∑ c ∈ centers, weight c := by
    change (∑ index : Fin source.card, volume (sourceShading.carrier index)) ≤ _
    simp only [weight]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro index _
    calc
      volume (sourceShading.carrier index) ≤
          volume (⋃ c ∈ centers,
            sourceShading.carrier index ∩ Metric.closedBall c (1 / 4)) := by
        apply measure_mono
        intro point hpoint
        obtain ⟨c, hc, hball⟩ := Set.mem_iUnion₂.mp
          (hcover (hsupport index (sourceShading.subset_body index hpoint)))
        exact Set.mem_iUnion₂.mpr ⟨c, hc, hpoint, Metric.ball_subset_closedBall hball⟩
      _ ≤ ∑ c ∈ centers,
          volume (sourceShading.carrier index ∩ Metric.closedBall c (1 / 4)) :=
        measure_biUnion_finset_le _ _
  calc
    sourceShading.mass ≤ ∑ c ∈ centers, weight c := hmass
    _ ≤ ∑ _c ∈ centers, weight center := Finset.sum_le_sum fun c hc => hmax c hc
    _ = (centers.card : ENNReal) * weight center := by simp

end KakeyaLink.JointSelection

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Kakeya.DimensionThree.MainLemma1.RevisedSource.AxisFootNormalizationCountingW103
import Kakeya.Tube.CoverCountComparable
import Unconditional.CentringCommonChord

/-!
# Centered Coarse Incidence

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

open MeasureTheory
open scoped Classical

namespace KakeyaLink.DirectCenteredRoute

open Kakeya Kakeya.ml1Boot.TrialRestartW94

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

omit [Nontrivial E] in
theorem dilate_carrier_subset_axis_neighborhood
    {rho : NNReal} (T : _root_.Tube rho E) {K : Real} (hK : 0 < K) :
    (Kakeya.Tube.dilate T K).carrier ⊆
      VeryNotSticky.lineNbhd T.center T.direction (K * (rho : Real)) := by
  intro x hx
  apply VeryNotSticky.mem_lineNbhd_of_dist_le (inner Real T.direction (x - T.center))
  have heq : x - (T.center + inner Real T.direction (x - T.center) • T.direction) =
      x - T.center - inner Real T.direction (x - T.center) • T.direction := by abel
  rw [dist_eq_norm, heq]
  exact (_root_.Tube.abs_inner_and_perp_le_of_mem_dilate T hK hx).2

theorem coarse_dilate_neighbors_card_le
    {J : Type v} {rho : NNReal} (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (F neighbors : Finset J) (T : J -> _root_.Tube rho E) (C : NNReal)
    (hline : lineEssentiallyDistinctW94 F T C)
    (B K : Real) (hB : 0 ≤ B) (hK : 1 ≤ K)
    (hcenter : ∀ j ∈ F, ‖(T j).center‖ ≤ B)
    (reference : _root_.Tube rho E) (hsub : neighbors ⊆ F)
    (hcontain : ∀ j ∈ neighbors,
      (T j).carrier ⊆ (Kakeya.Tube.dilate reference K).carrier) :
    (neighbors.card : NNReal) ≤
      (lineAmplificationBoundW95 (Module.finrank Real E) B K : NNReal) * C := by
  have hnear : neighbors ⊆ nearLineFamilyW95 F T reference.center reference.direction K := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨hsub hj,
      (hcontain j hj).trans (dilate_carrier_subset_axis_neighborhood reference
        (lt_of_lt_of_le zero_lt_one hK))⟩
  calc
    (neighbors.card : NNReal) ≤
        ((nearLineFamilyW95 F T reference.center reference.direction K).card : NNReal) := by
      exact_mod_cast Finset.card_le_card hnear
    _ ≤ _ := line_aperture_card_w103 hrho hrho1 F T C hline B K hB hK
      hcenter reference.center reference.direction reference.norm_direction


@[irreducible]
def centeredCoarseIncidenceBound : Nat :=
  Nat.ceil ((lineAmplificationBoundW95 3 (3 / 4) 128 : NNReal) * (2 * (223 : NNReal) ^ 6))


theorem homothetic_coarse_parent_image_card_le
    {I : Type v} {J : Type w} [DecidableEq J]
    {originalDelta fineDelta rho : NNReal} (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hscale : fineDelta ≤ rho)
    (S : Finset I) (original : I -> _root_.Tube originalDelta E)
    (F : Finset J) (T : J -> _root_.Tube rho E) (parent : I -> J)
    (C : NNReal) (hline : lineEssentiallyDistinctW94 F T C)
    (B : Real) (hB : 0 ≤ B) (hcenter : ∀ j ∈ F, ‖(T j).center‖ ≤ B)
    (fine : _root_.Tube fineDelta E)
    (hparent : ∀ i ∈ S, parent i ∈ F)
    (hfine : ∀ i ∈ S,
      (fun x : E => (1 / 8 : Real) • x) '' (original i).carrier ⊆ fine.carrier)
    (hcoarse : ∀ i ∈ S,
      (fun x : E => (1 / 8 : Real) • x) '' (original i).carrier ⊆
        (T (parent i)).carrier) :
    ((S.image parent).card : NNReal) ≤
      (lineAmplificationBoundW95 (Module.finrank Real E) B 128 : NNReal) * C := by
  apply coarse_dilate_neighbors_card_le hrho hrho1 F (S.image parent) T C hline B
    128 hB (by norm_num) hcenter (fine.rescale rho)
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact hparent i hi
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact homothetic_common_leaf_subset_dilate (show (rho : Real) ≤ 1 from hrho1)
      hscale (original i) fine (T (parent i)) (hfine i hi) (hcoarse i hi)


end KakeyaLink.DirectCenteredRoute

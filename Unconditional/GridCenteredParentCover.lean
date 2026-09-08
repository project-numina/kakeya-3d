/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Unconditional.BallThreeCenteredCover
import Unconditional.CenteredUnitParent
import Unconditional.CoarseParentSupport

/-!
# Grid Centered Parent Cover

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

open MeasureTheory

namespace KakeyaLink.DirectCenteredRoute

open Kakeya.ml1Boot.TrialRestartW94

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

theorem exists_grid_centered_parent_cover
    (hdim : Module.finrank Real E = 3)
    {delta : NNReal} (hdelta : 0 < delta)
    {I : Type v} [DecidableEq I] (s : Finset I) (T : I -> Tube delta E)
    (hs : s.Nonempty) (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1)
    {N : Nat} (U : Tube.GridCoverSystem s T N) (k : Nat) (hk : k ≤ N)
    (hsmall : Tube.gridScale delta N k ≤ 1 / 200) :
    ∃ (G : Finset I) (q : I -> I)
      (W : I -> Tube (Tube.gridScale delta N k / 2) E),
      G.Nonempty ∧ G ⊆ s.image (U.assign k) ∧
      (s.image (U.assign k)).image q = G ∧
      s.image (fun i => q (U.assign k i)) = G ∧
      (∀ j ∈ G, (W j).IsCentred) ∧
      (∀ j ∈ G, ‖(W j).midpoint‖ ≤ (5 / 12 : Real)) ∧
      (∀ j ∈ G, (W j).carrier ⊆ Metric.closedBall 0 1) ∧
      lineEssentiallyDistinctW94 G W (2 * (223 : NNReal) ^ 6) ∧
      (∀ j ∈ s.image (U.assign k),
        (fun x : E => (1 / 8 : Real) • x) '' (U.tube k j).carrier ⊆ (W (q j)).carrier) ∧
      (∀ i ∈ s, (fun x : E => (1 / 8 : Real) • x) '' (T i).carrier ⊆
        (W (q (U.assign k i))).carrier) := by
  classical
  have hactive : (s.image (U.assign k)).Nonempty := hs.image (U.assign k)
  have hparentBall : ∀ j ∈ s.image (U.assign k),
      (U.tube k j).carrier ⊆ Metric.closedBall 0 3 := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    apply coarse_parent_carrier_subset_ball_three (T i) (U.tube k (U.assign k i))
      (le_trans (show (Tube.gridScale delta N k : Real) ≤ 1 / 200 from hsmall) (by norm_num))
      (hball i hi)
    exact U.le_tube_assign k hk i hi
  obtain ⟨G, q, W, hG, hGsub, himage, _, hcenter, hmid, hballW, hline, hcover⟩ :=
    exists_ball_three_centred_representatives hdim (Tube.gridScale_pos hdelta N k)
      hsmall (s.image (U.assign k)) (U.tube k) hactive hparentBall
  refine ⟨G, q, W, hG, hGsub, himage, ?_, hcenter, hmid, hballW, hline, hcover, ?_⟩
  · simpa only [Finset.image_image, Function.comp_def] using himage
  · intro i hi
    exact (Set.image_mono (show (T i).carrier ⊆ (U.tube k (U.assign k i)).carrier from
      U.le_tube_assign k hk i hi)).trans
        (hcover (U.assign k i) (Finset.mem_image_of_mem (U.assign k) hi))


end KakeyaLink.DirectCenteredRoute

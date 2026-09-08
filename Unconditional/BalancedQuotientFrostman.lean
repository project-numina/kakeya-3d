/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Kakeya.Homothety

/-!
# Balanced Quotient Frostman

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace KakeyaLink.DirectCenteredRoute

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]
  {iota : Type v} {kappa : Type w}

theorem frostman_balanced_quotient
    (source : Finset iota) (W : iota -> ConvexSpaceBody E)
    (oldParent newParent : ConvexSpaceBody E) (A Q : ENNReal)
    (hFrostman : ConvexSpaceBody.IsFrostmanIn source W oldParent A)
    (hinside : forall i, i ∈ source -> W i ≤ oldParent)
    (hparentPositive : volume oldParent.carrier ≠ 0)
    (hpositive : forall i, i ∈ source -> 0 < volume (W i).carrier)
    (quotient : Finset kappa) (parent : iota -> kappa)
    (V : kappa -> ConvexSpaceBody E)
    (hmap : forall i, i ∈ source -> parent i ∈ quotient)
    (hcover : forall i, i ∈ source -> W i ≤ V (parent i))
    (hnewInside : forall j, j ∈ quotient -> V j ≤ newParent)
    (hsurj : forall j, j ∈ quotient -> (source.filter fun i => parent i = j).Nonempty)
    (oldVolume newVolume : ENNReal)
    (holdVolume : forall i, i ∈ source -> volume (W i).carrier = oldVolume)
    (hnewVolume : forall j, j ∈ quotient -> volume (V j).carrier = newVolume)
    (hbalanced : forall j, j ∈ quotient -> forall j', j' ∈ quotient ->
      ((source.filter fun i => parent i = j).card : ENNReal) ≤
        Q * ((source.filter fun i => parent i = j').card : ENNReal)) :
    ConvexSpaceBody.IsFrostmanIn quotient V newParent
      (Q * (A * (volume newParent.carrier / volume oldParent.carrier))) := by
  classical
  by_cases hnewZero : volume newParent.carrier = 0
  · exact ConvexSpaceBody.IsFrostmanIn.of_volume_eq_zero hnewZero
  have hallNew : forall i, i ∈ source -> W i ≤ newParent := by
    intro i hi
    exact (hcover i hi).trans (hnewInside _ (hmap i hi))
  have hsource := hFrostman.change_ambient hinside hallNew hparentPositive hnewZero
  apply ConvexSpaceBody.isFrostmanIn_parents_of_uniform_fibres hsource hpositive
    hmap hcover hnewInside (fun _ => rfl) hsurj
  intro j hj j' hj'
  have hdensity (j : kappa) (hj : j ∈ quotient) :
      Kakeya.densityIn (source.filter fun i => parent i = j) W (V j) =
        ((source.filter fun i => parent i = j).card : ENNReal) * oldVolume / newVolume := by
    rw [Kakeya.densityIn_of_all_le]
    · rw [hnewVolume j hj]
      congr 1
      calc
        (∑ i ∈ source.filter (fun i => parent i = j), volume (W i).carrier) =
            ∑ i ∈ source.filter (fun i => parent i = j), oldVolume := by
          apply Finset.sum_congr rfl
          intro i hi
          exact holdVolume i (Finset.mem_filter.mp hi).1
        _ = _ := by simp
    · intro i hi
      obtain ⟨hi, hij⟩ := Finset.mem_filter.mp hi
      exact hij ▸ hcover i hi
  rw [hdensity j hj, hdensity j' hj']
  calc
    ((source.filter fun i => parent i = j).card : ENNReal) * oldVolume / newVolume ≤
        (Q * ((source.filter fun i => parent i = j').card : ENNReal)) *
          oldVolume / newVolume := by
      gcongr
      exact hbalanced j hj j' hj'
    _ = Q * (((source.filter fun i => parent i = j').card : ENNReal) *
        oldVolume / newVolume) := by
      simp only [div_eq_mul_inv]
      ring

end KakeyaLink.DirectCenteredRoute

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Kakeya.Frostman

/-!
# Atom Mass Frostman

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace KakeyaLink.DirectCenteredRoute

universe u v w z

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]

theorem volume_mass_le_of_real_card_floor
    {I : Type v} (source selected : Finset I) (body : I -> ConvexSpaceBody E)
    (commonVolume : ENNReal)
    (hsourceVolume : forall i, i ∈ source -> volume (body i).carrier = commonVolume)
    (hselectedVolume : forall i, i ∈ selected -> volume (body i).carrier = commonVolume)
    (alpha : Real) (halpha : 0 < alpha)
    (hretained : alpha * (source.card : Real) ≤ (selected.card : Real)) :
    (∑ i ∈ source, volume (body i).carrier) ≤
      ENNReal.ofReal alpha⁻¹ * (∑ i ∈ selected, volume (body i).carrier) := by
  have hreal := mul_le_mul_of_nonneg_left hretained (inv_nonneg.mpr halpha.le)
  rw [← mul_assoc, inv_mul_cancel₀ halpha.ne', one_mul] at hreal
  have henn : (source.card : ENNReal) ≤
      ENNReal.ofReal alpha⁻¹ * (selected.card : ENNReal) := by
    simpa only [ENNReal.ofReal_mul (inv_nonneg.mpr halpha.le), ENNReal.ofReal_natCast]
      using ENNReal.ofReal_le_ofReal hreal
  have hsourceSum : (∑ i ∈ source, volume (body i).carrier) =
      (source.card : ENNReal) * commonVolume := by
    rw [Finset.sum_congr rfl hsourceVolume]
    simp
  have hselectedSum : (∑ i ∈ selected, volume (body i).carrier) =
      (selected.card : ENNReal) * commonVolume := by
    rw [Finset.sum_congr rfl hselectedVolume]
    simp
  rw [hsourceSum, hselectedSum]
  calc
    (source.card : ENNReal) * commonVolume ≤
        (ENNReal.ofReal alpha⁻¹ * (selected.card : ENNReal)) * commonVolume := by
      gcongr
    _ = _ := mul_assoc _ _ _

theorem frostman_pullback_of_relative_card_core
    {I : Type v} {A : Type w} {J : Type z}
    (source : Finset I) (selected : Finset A) (code : I -> A) (parent : A -> J)
    (body : I -> ConvexSpaceBody E) (anchor : J -> ConvexSpaceBody E)
    (commonVolume constant : ENNReal)
    (hvolume : forall i, i ∈ source -> volume (body i).carrier = commonVolume)
    (hcontained : forall i, i ∈ source -> body i ≤ anchor (parent (code i)))
    (hFrostman : forall j, j ∈ selected.image parent ->
      ConvexSpaceBody.IsFrostmanIn
        (source.filter (fun i => parent (code i) = j)) body (anchor j) constant)
    (alpha : Real) (halpha : 0 < alpha)
    (hcore : forall j, j ∈ selected.image parent ->
      alpha * ((source.filter (fun i => parent (code i) = j)).card : Real) ≤
        (((source.filter (fun i => code i ∈ selected)).filter
          (fun i => parent (code i) = j)).card : Real)) :
    forall j, j ∈ selected.image parent ->
      ConvexSpaceBody.IsFrostmanIn
        ((source.filter (fun i => code i ∈ selected)).filter
          (fun i => parent (code i) = j)) body (anchor j)
          (constant * ENNReal.ofReal alpha⁻¹) := by
  classical
  intro j hj
  apply (hFrostman j hj).of_le_of_subset
  · intro i hi
    obtain ⟨hi, hparent⟩ := Finset.mem_filter.mp hi
    simpa only [hparent] using hcontained i hi
  · intro i hi
    obtain ⟨hi, hparent⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1, hparent⟩
  · exact volume_mass_le_of_real_card_floor _ _ body commonVolume
      (fun i hi => hvolume i (Finset.mem_filter.mp hi).1)
      (fun i hi => hvolume i (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1)
      alpha halpha (hcore j hj)

end KakeyaLink.DirectCenteredRoute

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Kakeya.Pigeonhole

/-!
# Balanced Quotient Selection

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

open scoped BigOperators Classical

namespace KakeyaLink.DirectCenteredRoute

universe u v

theorem exists_comparable_weights_log_card
    {iota : Type u} (s : Finset iota) (weight : iota -> Real)
    (hweight : forall i, i ∈ s -> 0 ≤ weight i)
    (hpositive : 0 < ∑ i ∈ s, weight i) :
    exists selected : Finset iota,
      selected ⊆ s ∧ selected.Nonempty ∧
      (∑ i ∈ s, weight i) ≤
        (2 * (1 + Real.logb 2 (2 * (s.card : Real)))) *
          (∑ i ∈ selected, weight i) ∧
      (forall i, i ∈ selected -> 0 < weight i) ∧
      (forall i, i ∈ selected -> forall j, j ∈ selected -> weight i ≤ 2 * weight j) := by
  classical
  let total := ∑ i ∈ s, weight i
  have hs : s.Nonempty := by
    by_contra hempty
    have hs0 := Finset.not_nonempty_iff_eq_empty.mp hempty
    simp [hs0] at hpositive
  have hcard : 0 < (s.card : Real) := by
    exact_mod_cast hs.card_pos
  have hcardOne : 1 ≤ (s.card : Real) := by
    exact_mod_cast hs.card_pos
  let threshold : Real := total / (2 * (s.card : Real))
  have hthreshold : 0 < threshold := by
    dsimp [threshold, total]
    positivity
  have hthresholdTotal : threshold ≤ total := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (s.card : Real))).mpr
    nlinarith [hpositive]
  let heavy := s.filter fun i => threshold ≤ weight i
  have hsplit :
      (∑ i ∈ heavy, weight i) +
        (∑ i ∈ s.filter (fun i => ¬ threshold ≤ weight i), weight i) = total := by
    exact Finset.sum_filter_add_sum_filter_not s (fun i => threshold ≤ weight i) weight
  have hlight :
      (∑ i ∈ s.filter (fun i => ¬ threshold ≤ weight i), weight i) ≤ total / 2 := by
    calc
      _ ≤ ∑ i ∈ s.filter (fun i => ¬ threshold ≤ weight i), threshold := by
        apply Finset.sum_le_sum
        intro i hi
        exact (lt_of_not_ge (Finset.mem_filter.mp hi).2).le
      _ = ((s.filter (fun i => ¬ threshold ≤ weight i)).card : Real) * threshold := by simp
      _ ≤ (s.card : Real) * threshold := by
        gcongr
        exact Finset.filter_subset _ _
      _ = total / 2 := by
        dsimp [threshold]
        field_simp
  have hheavy : total ≤ 2 * ∑ i ∈ heavy, weight i := by linarith
  have hrange : forall i, i ∈ heavy -> weight i ∈ Set.Icc threshold total := by
    intro i hi
    obtain ⟨hi, hithreshold⟩ := Finset.mem_filter.mp hi
    refine ⟨hithreshold, ?_⟩
    exact Finset.single_le_sum hweight hi
  obtain ⟨selected, hsub, hretained, hcompare⟩ :=
    Real.dyadic_pigeonhole₁ heavy weight weight hthreshold hthresholdTotal hrange
  have hratio : total / threshold = 2 * (s.card : Real) := by
    have htotalZero : total ≠ 0 := hpositive.ne'
    dsimp [threshold]
    field_simp
  rw [hratio] at hretained
  have hmain : total ≤
      (2 * (1 + Real.logb 2 (2 * (s.card : Real)))) *
        (∑ i ∈ selected, weight i) := by
    nlinarith
  refine ⟨selected, hsub.trans (Finset.filter_subset _ _), ?_, hmain, ?_, hcompare⟩
  · by_contra hempty
    have hzero := Finset.not_nonempty_iff_eq_empty.mp hempty
    simp only [hzero, Finset.sum_empty, mul_zero] at hmain
    exact (not_le_of_gt hpositive) hmain
  · intro i hi
    exact hthreshold.trans_le (Finset.mem_filter.mp (hsub hi)).2


end KakeyaLink.DirectCenteredRoute

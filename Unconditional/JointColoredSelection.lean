/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.FiniteColoredDegreeSelection

/-!
Direct consumer interface for the existing simultaneous colored selector.
No geometry, conflict-degree bound, or full-fiber identity is asserted here.
-/

noncomputable section

open scoped BigOperators

namespace KakeyaLink.JointSelection

attribute [local instance] Classical.propDecidable

/-- One common color vector, one simultaneous regularization, and one total loss. -/
theorem exists_joint_colored_degree_selection
    {I : Type*} [Fintype I] [DecidableEq I] [LinearOrder I]
    (coordinateCount : ℕ) (hcoordinateCount : 0 < coordinateCount)
    (Color Vertex : Fin coordinateCount → Type)
    [∀ coordinate, Fintype (Color coordinate)]
    [∀ coordinate, DecidableEq (Color coordinate)]
    [∀ coordinate, Nonempty (Color coordinate)]
    [∀ coordinate, Fintype (Vertex coordinate)]
    [∀ coordinate, DecidableEq (Vertex coordinate)]
    (color : ∀ coordinate, I → Color coordinate)
    (parent : ∀ coordinate, I → Vertex coordinate)
    (weight : I → ENNReal) (hweight : 0 < ∑ i : I, weight i) :
    ∃ selected : Finset I, ∃ colorVector : ∀ coordinate, Color coordinate,
      selected.Nonempty ∧
      (∀ i ∈ selected, ∀ coordinate, color coordinate i = colorVector coordinate) ∧
      (∀ i ∈ selected, 0 < weight i) ∧
      (∑ i : I, weight i) ≤
        (Fintype.card (∀ coordinate, Color coordinate) : ENNReal) *
          (8 : ENNReal) *
          (Nat.log 2 (2 * Fintype.card I) + 1 : ENNReal) ^ (coordinateCount + 1) *
          (∑ i ∈ selected, weight i) ∧
      (∀ coordinate, ∀ first second : Vertex coordinate,
        0 < (selected.filter fun i => parent coordinate i = first).card →
        0 < (selected.filter fun i => parent coordinate i = second).card →
        ((selected.filter fun i => parent coordinate i = first).card : ENNReal) ≤
          (16 * (coordinateCount : ENNReal) *
            (Nat.log 2 (2 * Fintype.card I) + 1 : ENNReal) ^ coordinateCount) *
            ((selected.filter fun i => parent coordinate i = second).card : ENNReal)) ∧
      (∃ weightLevel : ENNReal, 0 < weightLevel ∧
        ∀ i ∈ selected, weightLevel ≤ weight i ∧ weight i ≤ 2 * weightLevel) := by
  classical
  obtain ⟨data⟩ := Kakeya.Assouad.wz2_finite_colored_degree_selection
    coordinateCount Color Vertex color parent weight hcoordinateCount
  have hclassSum :
      (∑ i : I, if i ∈ data.colorClass then weight i else 0) =
        ∑ i ∈ data.colorClass, weight i := by
    simp only [← Finset.sum_filter]
    simp
  have hselectedSum :
      (∑ i ∈ data.regularized.selected,
        if i ∈ data.colorClass then weight i else 0) =
        ∑ i ∈ data.regularized.selected, weight i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [if_pos (data.selected_subset_colorClass hi)]
  have hretained : (∑ i : I, weight i) ≤
      (Fintype.card (∀ coordinate, Color coordinate) : ENNReal) *
        (8 : ENNReal) *
        (Nat.log 2 (2 * Fintype.card I) + 1 : ENNReal) ^ (coordinateCount + 1) *
        (∑ i ∈ data.regularized.selected, weight i) := by
    have h := data.regularized.retained_weight
    rw [hclassSum, hselectedSum] at h
    calc
      _ ≤ (Fintype.card (∀ coordinate, Color coordinate) : ENNReal) *
          (∑ i ∈ data.colorClass, weight i) := data.color_retained
      _ ≤ (Fintype.card (∀ coordinate, Color coordinate) : ENNReal) *
          ((8 : ENNReal) *
            (Nat.log 2 (2 * Fintype.card I) + 1 : ENNReal) ^ (coordinateCount + 1) *
            (∑ i ∈ data.regularized.selected, weight i)) := mul_le_mul_left' h _
      _ = _ := by simp only [mul_assoc]
  refine ⟨data.regularized.selected, data.colorVector, ?_, ?_, ?_,
    hretained, data.regularized.degree_uniform, ?_⟩
  · apply Finset.nonempty_iff_ne_empty.mpr
    intro hempty
    simp only [hempty, Finset.sum_empty, mul_zero] at hretained
    exact (not_le_of_gt hweight) hretained
  · intro i hi coordinate
    exact data.monochromatic i (data.selected_subset_colorClass hi) coordinate
  · intro i hi
    simpa only [if_pos (data.selected_subset_colorClass hi)] using
      data.regularized.selected_weight_pos i hi
  · refine ⟨data.regularized.weightLevel, data.regularized.weightLevel_pos, ?_⟩
    intro i hi
    simpa only [if_pos (data.selected_subset_colorClass hi)] using
      data.regularized.weight_band i hi

end KakeyaLink.JointSelection

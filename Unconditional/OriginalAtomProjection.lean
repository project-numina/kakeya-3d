/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Unconditional.OriginalAtomCoding

/-!
# Original Atom Projection

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

open scoped Classical

namespace KakeyaLink.DirectCenteredRoute

universe u v w

theorem exists_original_fine_projection
    {I : Type u} {Q : Type v} {m : Nat} {J : Fin m -> Type w}
    (source dense : Finset I) (fine : I -> Q) (coarse : forall k, I -> J k)
    (initial : Finset (Option Q × (forall k, J k)))
    (hinitial : initial ⊆ source.image (denseJointCode dense fine coarse))
    (hnonempty : initial.Nonempty)
    (hinjective : Set.InjOn (fun a : Option Q × (forall k, J k) => a.1) initial)
    (hdense : (source.filter (fun i => denseJointCode dense fine coarse i ∈ initial)) ⊆ dense) :
    exists projection : (Option Q × (forall k, J k)) -> Q,
      Set.InjOn projection initial ∧
      (forall i, i ∈ source -> denseJointCode dense fine coarse i ∈ initial ->
        projection (denseJointCode dense fine coarse i) = fine i) ∧
      initial.image projection ⊆ dense.image fine := by
  classical
  have hsource : source.Nonempty := by
    obtain ⟨a, ha⟩ := hnonempty
    obtain ⟨i, hi, _⟩ := Finset.mem_image.mp (hinitial ha)
    exact ⟨i, hi⟩
  let projection := fun a : Option Q × (forall k, J k) => a.1.getD (fine hsource.choose)
  have hmem : forall i, i ∈ source -> denseJointCode dense fine coarse i ∈ initial ->
      i ∈ dense := fun i hi ha => hdense (Finset.mem_filter.mpr ⟨hi, ha⟩)
  have hproj : forall i, i ∈ source -> denseJointCode dense fine coarse i ∈ initial ->
      projection (denseJointCode dense fine coarse i) = fine i := by
    intro i hi ha
    simp only [projection, denseJointCode, if_pos (hmem i hi ha), Option.getD_some]
  refine ⟨projection, ?_, hproj, ?_⟩
  · intro a ha b hb heq
    obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp (hinitial ha)
    obtain ⟨j, hj, hjb⟩ := Finset.mem_image.mp (hinitial hb)
    have hai := hia ▸ ha
    have hbj := hjb ▸ hb
    have hfine : fine i = fine j := by
      rw [← hproj i hi hai, ← hproj j hj hbj, hia, hjb]
      exact heq
    apply hinjective ha hb
    rw [← hia, ← hjb]
    simp only [denseJointCode, if_pos (hmem i hi hai), if_pos (hmem j hj hbj), hfine]
  · intro q hq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp (hinitial ha)
    have hai := hia ▸ ha
    exact Finset.mem_image.mpr ⟨i, hmem i hi hai, by rw [← hia, hproj i hi hai]⟩

end KakeyaLink.DirectCenteredRoute

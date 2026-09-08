/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Mathlib

/-!
# Atom Weight Level

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

open scoped Classical

namespace KakeyaLink.DirectCenteredRoute

universe u v

theorem exists_atom_weight_level
    {I : Type u} {A : Type v} [DecidableEq A]
    (source : Finset I) (code : I -> A) (atoms : Finset A)
    (hatoms : atoms ⊆ source.image code) (hnonempty : atoms.Nonempty)
    (hbalanced : forall a, a ∈ atoms -> forall b, b ∈ atoms ->
      ((source.filter (fun i => code i = a)).card : ENNReal) ≤
        2 * ((source.filter (fun i => code i = b)).card : ENNReal)) :
    exists level : Real, 0 < level ∧
      forall a, a ∈ atoms -> level ≤ ((source.filter (fun i => code i = a)).card : Real) ∧
        ((source.filter (fun i => code i = a)).card : Real) ≤ 2 * level := by
  classical
  let weight := fun a => ((source.filter (fun i => code i = a)).card : Real)
  obtain ⟨a, ha, hmin⟩ := atoms.exists_min_image weight hnonempty
  have hfiber : (source.filter (fun i => code i = a)).Nonempty := by
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp (hatoms ha)
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, heq⟩⟩
  refine ⟨weight a, by dsimp [weight]; exact_mod_cast hfiber.card_pos, ?_⟩
  intro b hb
  refine ⟨hmin b hb, ?_⟩
  have hnat : (source.filter (fun i => code i = b)).card ≤
      2 * (source.filter (fun i => code i = a)).card := by exact_mod_cast hbalanced b hb a ha
  dsimp [weight]
  exact_mod_cast hnat

end KakeyaLink.DirectCenteredRoute

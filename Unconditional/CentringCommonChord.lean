/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Kakeya.Tube.CoverCountComparable

/-!
# Centring Common Chord

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

open MeasureTheory

namespace KakeyaLink.DirectCenteredRoute

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

theorem homothetic_common_leaf_subset_dilate
    {originalDelta fineDelta rho : NNReal}
    (hrho : (rho : Real) ≤ 1) (hscale : fineDelta ≤ rho)
    (original : Tube originalDelta E) (fine : Tube fineDelta E)
    (coarse : Tube rho E)
    (hfine : (fun x : E => (1 / 8 : Real) • x) '' original.carrier ⊆ fine.carrier)
    (hcoarse : (fun x : E => (1 / 8 : Real) • x) '' original.carrier ⊆ coarse.carrier) :
    coarse.carrier ⊆ (Kakeya.Tube.dilate (fine.rescale rho) 128).carrier := by
  let p : E := (1 / 8 : Real) • original.x
  let q : E := (1 / 8 : Real) • original.y
  have hx : p ∈ (fun x : E => (1 / 8 : Real) • x) '' original.carrier :=
    ⟨original.x, Tube.x_mem_carrier original, rfl⟩
  have hy : q ∈ (fun x : E => (1 / 8 : Real) • x) '' original.carrier :=
    ⟨original.y, Tube.y_mem_carrier original, rfl⟩
  have hpq : dist p q = (1 / 8 : Real) := by
    dsimp [p, q]
    rw [dist_smul₀, Real.norm_of_nonneg (by norm_num), original.dist_eq_one, mul_one]
  have hrescale : fine.carrier ⊆ (fine.rescale rho).carrier := fine.le_rescale hscale
  have h := Tube.subset_dilate_of_common_chord_at hrho (K := 4) (by norm_num)
    coarse (fine.rescale rho) (hcoarse hx) (hcoarse hy)
    (hrescale (hfine hx)) (hrescale (hfine hy)) (by rw [hpq]; norm_num)
  simpa only [show (32 : Real) * 4 = 128 by norm_num] using h

end KakeyaLink.DirectCenteredRoute

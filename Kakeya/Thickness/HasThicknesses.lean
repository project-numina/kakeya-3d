/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Thickness.Basic

/-!
# Prescribed affine thicknesses

Throughout the development the blueprint records the shape of a convex body by a chain of
comparisons `τ₀(K) ∼ t 0`, `τ₁(K) ∼ t 1`, … of its affine thicknesses with a prescribed
sequence of scales, with an implicit constant. `Kakeya.HasThicknesses` is that statement
with the implicit constant made explicit.

The predicate is indexed by an arbitrary `Fin n`, so that it can be used in dimension-generic
statements; in a space of dimension `d` one takes `n = d` (equivalently, a vector
`![t₀, …, t_{d-1}]`), which is the only case appearing in the blueprint.
-/

@[expose] public section
open scoped NNReal

namespace Kakeya

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A set `K` has affine thicknesses comparable, with constant `C`, to the prescribed
sequence `t : Fin n → ℝ`: this is the meaning of the blueprint's `τ_k(K) ∼ t k`, with the
implicit constant made explicit.

The length `n` of the sequence is arbitrary; the statements of the development instantiate
it at the dimension of the ambient space, so that a three-dimensional body is described by
`HasThicknesses K C ![t₀, t₁, t₂]`. -/
def HasThicknesses {n : ℕ} (K : Set E) (C : ℝ≥0) (t : Fin n → ℝ) : Prop :=
  ∀ k : Fin n, (C : ℝ)⁻¹ * t k ≤ Metric.thickness ℝ K (k : ℕ) ∧
    Metric.thickness ℝ K (k : ℕ) ≤ C * t k


end Kakeya

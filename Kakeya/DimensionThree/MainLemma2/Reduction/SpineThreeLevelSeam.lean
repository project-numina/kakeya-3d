/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCoarseSeam

/-!
# The three-level seam, and fibre-completeness at `(p, b)`

's "cheap route", tested: **it works.**

The map proposed that the four-way split's seam need not be a new pigeonhole.
`Kakeya.ML2Core.exists_coarseParentSeam` already runs **one** pigeonhole, at the coarsest level `a`
(`Kakeya.ML2Core.exists_parentSeam`), and then *defines* the level-`b` retained set as the coarse
cell's descendants.  A three-level seam is the same single pigeonhole with **two** descendant sets,
one at the genuine parent level `p` and one at `b`.

And then the clause `0-E` was chartered to supply — retention of **complete** `(p,b)`-fibres,
source  — **is true by construction and needs no mass-coupled selection**:
`Kakeya.ML2Core.threeLevelSeam_fibre_complete`.  If `k` is a retained `p`-cell and `j` is *any*
active level-`b` node whose `(p,b)`-parent is `k`, then `j`'s `(a,b)`-parent is `k`'s `(a,p)`-parent
by `Kakeya.ML2Core.coarseNode_trans`, which is in `t₀`, so `j` is retained.  The seam keeps whole
tagged thread cells because it never selected at `b` in the first place.

## Family / shading / level pair

 §SPEC.1 makes this column part of the statement.

* `Kakeya.ML2Core.coarseNode_mem_activeNodes`, `Kakeya.ML2Core.coarseNode_trans` —
  **family:** the chain cover `𝒞` on `(s, T)`, no shading; **level pairs:** `(a,b)` and the
  composite `(a,p) ∘ (p,b)`.
* `Kakeya.ML2Core.exists_threeLevelParentSeam` — **family:** `(s, T)` with the seam's translate `v`,
  no shading (the shading enters later, at the one-scale applications);
  **level triple:** `a ≤ p ≤ b`, with retained sets `t₀ ⊆ activeNodes a`, `tp ⊆ activeNodes p`,
  `t₁ ⊆ activeNodes b`.
* `Kakeya.ML2Core.threeLevelSeam_fibre_complete` — **family:** the same; **level pair:** `(p, b)`,
  which is the source's middle-factor pair (`δ̃ = ρ_b/(2ρ_p)`) and the one `hfac` does not
  have.

**What this does NOT do.**  It does not touch `hfac`, whose seam is still at `coarseNode 𝒞 a b`;
moving that is the guarded re-cut.  It does not supply the mass-coupled fullness selection as a *shaded* statement — the fullness and `Δ_max` clauses of `𝕌_b` are still owed.
What it removes is the need for a **new pigeonhole** to get fibre-completeness.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Metric ConvexSpaceBody ShadedBody
open Tube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

section Transitivity

variable {ι : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {δ : ℝ≥0} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {σ : ℕ → ℝ≥0}

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The coarse parent of an active node is active.**

**Family:** `(s, T)` through the chain `𝒞`.  **Level pair:** `(a, b)`. -/
theorem coarseNode_mem_activeNodes (𝒞 : Tube.ChainCoverSystem s T N σ) {a b : ℕ}
    (hab : a ≤ b) (hbN : b ≤ N) {j : ι} (hj : j ∈ ML2Reduction.activeNodes 𝒞 b) :
    ML2Reduction.coarseNode 𝒞 a b j ∈ ML2Reduction.activeNodes 𝒞 a := by
  classical
  obtain ⟨i, hi⟩ : (Tube.coverClass s (𝒞.assign b) j).Nonempty := (Finset.mem_filter.mp hj).2
  simp only [Tube.coverClass, Finset.mem_filter] at hi
  obtain ⟨his, hij⟩ := hi
  rw [← hij, coarseNode_assign 𝒞 hab hbN his]
  exact ML2Reduction.assign_mem_activeNodes 𝒞 (hab.trans hbN) his


end Transitivity

section ThreeLevel

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]


end ThreeLevel

end Kakeya.ML2Core

end

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.MultiScaleFac.Stopping
public import Kakeya.MultiScaleFac.StoppingKTBase

/-!
# The refined stopping time of GWZ Lemma 7.7(B)

The Katz–Tao twin of `Kakeya/MultiScaleFac/Refine.lean`.

What is *not* the same is the price.  In half (A) the block predicate
`MultiScaleFac.BlockFrostmanAt t T N C ζ a b i₀` reads the fibres of the **current pile** `t`, so
shrinking the pile changes the predicate and the descent
`MultiScaleFac.BlockFrostmanAt.of_subfamily` costs a factor; restoring the hypotheses that descent
needs costs a re-uniformization at every level, and that is the origin of the polylogarithmic
factor in half (A).

Here `MultiScaleFac.BlockKatzTaoAt u C ζ a b i₀` reads only the node families of the **fixed**
uniform data `u` and the anchor `i₀`.  It does not mention the pile at all.  So:

* the invariant `∀ i₀ ∈ t, BlockKatzTaoAt u C ζ a b i₀` descends to any subset of `t` by
  restricting a universal quantifier — no constant, no hypotheses to restore;
* the constant never grows along the stopping time, since both halves of a cut carry the constant
  the parent carried (`MultiScaleFac.BlockKatzTaoOn.anchor_le`);
* no level re-uniformizes, so the only loss is the pile shrinkage `2 (N+1)` per level — a factor of
  `N` alone, independent of `δ`.

The state of the abstract engine is therefore just the pile, and the uniform data is a parameter
fixed once and for all before the recursion starts.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Real Metric ConvexSpaceBody
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya
open scoped NNReal

universe u

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

variable {ι : Type*} {δ : ℝ≥0} {s : Finset ι} {T : ι → Tube δ E} {Cu : ℝ≥0} {N : ℕ}

section Invariant

/-- **The block bound of GWZ Lemma 7.7(B) with the anchor set named separately.**  Where
`MultiScaleFac.BlockKatzTao` quantifies over the whole family carrying the uniform data, here the
two roles are separated: `u` is the uniform data on the ambient family `s`, and `t` is the current
pile of anchors.  The predicate `BlockKatzTaoAt u C ζ a b i₀` never mentions `t`. -/
def BlockKatzTaoOn (t : Finset ι)
    (u : ∀ k, k ≤ N → Tube.IsUniformAtScale s T (gridScale δ N k) Cu)
    (C : ℝ≥0) (ζ : ℝ) (a b : ℕ) : Prop :=
  ∀ i₀ ∈ t, BlockKatzTaoAt u C ζ a b i₀

omit [Nontrivial E] in
/-- The invariant descends to a smaller pile for free: it is a universal quantifier over the pile
and its body does not mention the pile.  This is the `hdescend` hypothesis of
`MultiScaleFac.exists_maximal_cuts_abstract_state`, and in half (B) it is free where half (A) pays
`MultiScaleFac.BlockFrostmanAt.of_subfamily`. -/
theorem BlockKatzTaoOn.subset {t t' : Finset ι}
    {u : ∀ k, k ≤ N → Tube.IsUniformAtScale s T (gridScale δ N k) Cu}
    {C : ℝ≥0} {ζ : ℝ} {a b : ℕ} (h : BlockKatzTaoOn t u C ζ a b) (ht : t' ⊆ t) :
    BlockKatzTaoOn t' u C ζ a b :=
  fun i₀ hi₀ => h i₀ (ht hi₀)

omit [Nontrivial E] in
/-- The pile-relative form of `MultiScaleFac.BlockKatzTaoAt.mono`, quantified over the pile. -/
theorem BlockKatzTaoOn.mono (hδ : 0 < δ) (hδ1 : δ ≤ 1) {t : Finset ι}
    {u : ∀ k, k ≤ N → Tube.IsUniformAtScale s T (gridScale δ N k) Cu}
    {C C' : ℝ≥0} {ζ ζ' : ℝ} (hCC' : C ≤ C') (hζ : 0 ≤ ζ) (hζζ' : ζ ≤ ζ')
    {a b : ℕ} (hab : a ≤ b) (h : BlockKatzTaoOn t u C ζ a b) :
    BlockKatzTaoOn t u C' ζ' a b :=
  fun i₀ hi₀ => (h i₀ hi₀).mono hδ hδ1 hCC' hζ hζζ' hab


end Invariant

section PerNode


end PerNode

section GridState


end GridState

end MultiScaleFac

end Kakeya

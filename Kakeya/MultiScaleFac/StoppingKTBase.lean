/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.FibreCommon
public import Kakeya.Thickness.ConvexSpaceBody
public import Kakeya.ChainUniform
public import Kakeya.Sticky
public import Kakeya.Uniform
public import Mathlib.Tactic.Linarith.NNRealPreprocessor
public import Kakeya.Density
public import Kakeya.Tube.Basic

/-!
# The stopping time of GWZ Lemma 7.7(B)

The Katz–Tao half of the dividing-scales dichotomy.  This file is the `Δ_max` twin of the
Frostman stopping time in `Kakeya/MultiScaleFac/Stopping.lean`, and it reuses that file's
combinatorial skeleton `MultiScaleFac.exists_maximal_cuts_abstract` verbatim; only the tracked
quantity changes.

## The node convention

`Δ_max` is tracked on the **node** families of the uniform structure — the essentially distinct
`ρ`-tubes `𝕋_ρ` of GWZ Definition 2.1 — and never on the thickened family `𝕋^{(ρ)}` with its
leaf multiplicities.  This is forced, not a matter of taste:

* `StickyKakeya.card_mul_le_of_isKatzTaoAtEveryScale` below shows that the multiplicity-carrying
  reading — `Δ_max(𝕋^{(ρ)}) ≤ C` on the full index set `s`, already at `ρ = 1` — implies
  `#s ≲_n C`.  With `C = δ^{-o(1)}` that
  caps the family at `δ^{-o(1)}` tubes, whereas the families GWZ Lemma 7.7(B) is applied to have
  `≈ δ^{-(n-1)}` tubes.  So the multiplicity reading is unsatisfiable in the intended regime.
* The Wang–Zahl source states the definition for a *set* of `ρ`-tubes: "there exists `ρ` and a
  set of `ρ`-tubes `𝕋_ρ`" with "`𝕋_ρ` is a `K`-balanced partitioning cover of `𝕋`" and
  "`C_KT(𝕋_ρ) ≤ K`" (Wang-Zahl).

On the node families the quantity behaves as it should: for a Kakeya family the `ρ`-nodes number
`≈ ρ^{-(n-1)}` and each has volume `≈ ρ^{n-1}`, so `Δ_max ≈ 1` at every scale.

## The duality with Lemma 7.7(A)

The two stopping times are mirror images, and the mirror is the direction in which the tracked
quantity is inherited (GWZ, the two inheritance principles):

* `C_F` passes to *coarse* families, so in (A) the coarse half of a cut is free — it is
  `MultiScaleFac.BlockRestrictStep` — and the stopping test must supply the **fine** half.
* `Δ_max` passes to *subfamilies*, so in (B) the fine half of a cut is free — it is
  `ConvexSpaceBody.IsKatzTao.subset` applied to the node index set, which shrinks with the
  anchor — and the stopping test must supply the **coarse** half.

Consequently (B) needs no analogue of `MultiScaleFac.BlockRestrictStep`, and no geometric constant
accumulates along the stopping time: where (A) carries `C' ^ N`, (B) carries the single constant
it starts with.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Real Metric ConvexSpaceBody
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya
open scoped NNReal ENNReal

universe u

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

section Multiplicity

variable {ι : Type*} {δ : ℝ≥0} {s : Finset ι} {T : ι → Tube δ E}

end Multiplicity

section Blocks

variable {ι : Type*} {δ : ℝ≥0} {s : Finset ι} {T : ι → Tube δ E} {Cu : ℝ≥0} {N : ℕ}

/-- **The per-anchor block bound of GWZ Lemma 7.7(B).**  `BlockKatzTaoAt u C ζ a b i₀` says that the
`σ_b`-nodes contained in the anchor `T_{i₀}^{(σ_a)}` are `C (σ_a/σ_b)^ζ`-Katz–Tao, where
`σ_k = gridScale δ N k`.  The uniformity witnesses are carried as a function `u`, supplied only on
the grid range `k ≤ N` since off it the requirement would be unsatisfiable; accordingly the bound is
stated as `∀ hb : b ≤ N, …`. -/
def BlockKatzTaoAt (u : ∀ k, k ≤ N → Tube.IsUniformAtScale s T (gridScale δ N k) Cu)
    (C : ℝ≥0) (ζ : ℝ) (a b : ℕ) (i₀ : ι) : Prop :=
  ∀ hb : b ≤ N,
    ConvexSpaceBody.IsKatzTao (gapNodeIndexAtScale (u b hb) i₀ (5 * gridScale δ N a))
      (fun j => ((u b hb).parentTube j).toConvexSpaceBody)
      ((C : ℝ≥0∞) * ENNReal.ofReal
        (((gridScale δ N a : ℝ) / (gridScale δ N b : ℝ)) ^ ζ))


omit [Nontrivial E] in
/-- **The block bound weakens as the constant and the exponent grow.**  The ratio `σ_a/σ_b` is at
least `1` for `a ≤ b`, so raising the exponent enlarges the right-hand side.  This is the `hmono`
hypothesis of `MultiScaleFac.exists_maximal_cuts_abstract`. -/
theorem BlockKatzTaoAt.mono (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {u : ∀ k, k ≤ N → Tube.IsUniformAtScale s T (gridScale δ N k) Cu}
    {C C' : ℝ≥0} {ζ ζ' : ℝ} (hCC' : C ≤ C') (_hζ : 0 ≤ ζ) (hζζ' : ζ ≤ ζ')
    {a b : ℕ} (hab : a ≤ b) {i₀ : ι} (h : BlockKatzTaoAt u C ζ a b i₀) :
    BlockKatzTaoAt u C' ζ' a b i₀ := by
  intro hb
  have hb_pos : 0 < (gridScale δ N b : ℝ) := by exact_mod_cast gridScale_pos hδ N b
  have hr1 : (1 : ℝ) ≤ (gridScale δ N a : ℝ) / (gridScale δ N b : ℝ) :=
    (one_le_div hb_pos).mpr (by exact_mod_cast gridScale_antitone hδ hδ1 N hab)
  exact (h hb).mono (mul_le_mul' (ENNReal.coe_le_coe.mpr hCC')
    (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hr1 hζζ')))


end Blocks

end MultiScaleFac

end Kakeya

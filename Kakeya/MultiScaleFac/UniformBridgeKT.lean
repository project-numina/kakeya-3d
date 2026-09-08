/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.MultiScaleFac.RefineKT
public import Kakeya.ChainUniform
public import Kakeya.MultiScaleFac.FibreDensity
public import Kakeya.FibreCommon
public import Kakeya.Thickness.ConvexSpaceBody
public import Kakeya.Sticky
public import Kakeya.Uniform
public import Mathlib.Tactic.Linarith.NNRealPreprocessor
public import Kakeya.MultiScaleFac.Stopping
public import Kakeya.Uniform.ParentBodyDensity

/-!
# Translating the Katz–Tao stopping time into the node language

The Katz–Tao counterpart of the node translations of `Kakeya/MultiScaleFac/Bridge.lean`, and vastly
cheaper than them.

`Kakeya.maxDensity` is a supremum of densities over *all* test bodies, so it carries no anchor of
its own: a container enters only by selecting an index set, and `Δ_max` is monotone in that set.
Consequently both directions of the node translation in half (B) are plain set inclusions —
upper bounds by shrinking the index set, the lower bound by enlarging it — with no volume
comparison and no constant.  Half (A) needed a whole bridge layer for the same two steps, because
`C_F` is a *ratio* anchored at a test body and moving the anchor costs volume comparisons.

The two inclusions are:

* `nodesUnder b a j ⊆ gapNodeIndex (u b) i₀ (5 σ_a)` for any member `i₀` of the class of `j`.  The
  factor `5` in the container convention of `MultiScaleFac.BlockKatzTaoAt` was chosen for exactly
  this: `T i₀ ≤ tube a j` gives `tube a j ≤ (T i₀)^{(4σ_a)}` by `Tube.rescale_le_of_le`, and
  `4 ≤ 5`.
* `gapNodeIndex (u c) i₀ (5 σ_a) ⊆ nodesIn c ((tube a j)^{(8σ_a)})`, which is why the lower bound of
  alternative (ii) is stated on a dilate of the anchor node: the stopping time delivers its bound on
  the `5σ_a`-thickening of a *leaf*, a container five times thicker than `tube a j`, so the
  inclusion runs the wrong way for a lower bound until the anchor is dilated.  Chasing
  `T i₀ ≤ tube a j` gives `(T i₀)^{(5σ_a)} ⊆ (tube a j)^{(6σ_a)}`; `8` is taken to match half (A)
  and for room.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Real Metric ConvexSpaceBody
open Tube

namespace Kakeya

open StickyKakeya


universe u

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

variable {ι : Type*} {δ : ℝ≥0} {t : Finset ι} {T : ι → Tube δ E} {N : ℕ} {Cv : ℝ≥0}

namespace MultiScaleFac

open _root_.StickyKakeya


end MultiScaleFac

section  -- Declarations lie in the root `Tube` namespace.
open MultiScaleFac


omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem _root_.Tube.GridUniform.toUniformTubeSet_cover (𝒢 : GridUniform t T N Cv) :
    𝒢.toUniformTubeSet.cover = 𝒢.cover := rfl


end

namespace MultiScaleFac

open _root_.StickyKakeya

section TopScaleCount


omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Every node of the system lies in a fixed ball.**  A node contains a member, the members lie in
`B_1`, and a node tube has radius at most `1` and a unit-length core, so
`Tube.subset_ball_of_carrier_subset_ball` puts the node in `B_4`.  This is the containment
hypothesis of GWZ Lemma 7.4 for the node chain, at every level at once. -/
theorem node_carrier_subset_ball {s : Finset ι} {C : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (𝒰 : UniformTubeSet s T N C) (hs : s.Nonempty)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
    {k : ℕ} (hk : k ≤ N) {j : ι} (hj : j ∈ 𝒰.cover.indexSet k) :
    (𝒰.cover.tube k j).carrier ⊆ Metric.closedBall (0 : E) 4 := by
  classical
  obtain ⟨i, hi⟩ := coverClass_nonempty_of_mem_parent 𝒰 hk hs hj
  simp only [coverClass, Finset.mem_filter] at hi
  obtain ⟨his, hij⟩ := hi
  have hcov : (T i).carrier ⊆ (𝒰.cover.tube k j).carrier := by
    have h := 𝒰.cover.le_tube_assign k hk i his
    rw [hij] at h
    exact SetLike.coe_subset_coe.mpr h
  have hmain := Tube.subset_ball_of_carrier_subset_ball hδ (gridScale_pos hδ N k)
    (T i) (𝒰.cover.tube k j) (hball i his) hcov
  refine subset_trans hmain (Metric.closedBall_subset_closedBall ?_)
  have hle : (gridScale δ N k : ℝ) ≤ 1 := by exact_mod_cast gridScale_le_one hδ1 N k
  linarith

end TopScaleCount

end MultiScaleFac

section  -- Declarations lie in the root `Tube` namespace.
open MultiScaleFac


/-- **The ancestor of a node at a coarser grid index.**  `GridCoverSystem` records the assignment of
*members* to nodes, not of nodes to nodes; the node map is recovered by following any member of the
node's class up to the coarser index.  Well-definedness is not needed — the choice is made once by
`Classical.choose` — only the two properties below, and both hold for any member. -/
noncomputable def _root_.Tube.UniformTubeSet.nodeAncestor {s : Finset ι} {C : ℝ≥0}
    (𝒰 : UniformTubeSet s T N C) (b a : ℕ) (w : ι) : ι :=
  open scoped Classical in
  if h : (coverClass s (𝒰.cover.assign b) w).Nonempty then 𝒰.cover.assign a h.choose else w


end

namespace MultiScaleFac

open _root_.StickyKakeya

section TopScaleCount

end TopScaleCount

section Telescope


end Telescope

section ShortGap

end ShortGap

end MultiScaleFac

section  -- Declarations lie in the root `Tube` namespace.
open MultiScaleFac


end

namespace MultiScaleFac

open _root_.StickyKakeya
open scoped NNReal

section ShortGap


end ShortGap


section CoarseChain


end CoarseChain

section CrudeGap


end CrudeGap

section AlternativeOne


end AlternativeOne

section AlternativeOneGeneral


end AlternativeOneGeneral

section Window

end Window

section AlternativeOneFinal

end AlternativeOneFinal

section AlternativeTwoKT

end AlternativeTwoKT

section EmptyFamily

/-- **The nodeless uniform structure on an empty family.**  Alternative (i) of half (B) bounds
`Δ_max` of the *node* family, so it is not automatic when the family is empty: the parents of an
arbitrary system need not be empty.  Every clause of `GridCoverSystem` quantifies over members and
so holds vacuously; the uniformity clauses quantify over nodes, of which there are none. -/
noncomputable def emptyUniformTubeSet {s : Finset ι} (hs : s = ∅) (T : ι → Tube δ E) (N : ℕ)
    (C : ℝ≥0) (tb : (k : ℕ) → ι → Tube (gridScale δ N k) E) :
    UniformTubeSet s T N C where
  cover :=
    { indexSet := fun _ => ∅
      assign := fun _ i => i
      tube := tb
      assign_mem := by
        intro k _ i hi; rw [hs] at hi; exact absurd hi (Finset.notMem_empty i)
      le_tube_assign := by
        intro k _ i hi; rw [hs] at hi; exact absurd hi (Finset.notMem_empty i)
      nested := by
        intro k _ i hi; rw [hs] at hi; exact absurd hi (Finset.notMem_empty i)
      tube_nested := by
        intro k _ i hi; rw [hs] at hi; exact absurd hi (Finset.notMem_empty i) }
  branchingN := fun _ => 1
  tube_injOn := by intro k _; simp
  boundedOverlap := by intro k _ V; simp
  card_class_le := by intro k _ j hj; exact absurd hj (Finset.notMem_empty j)
  le_card_class := by intro k _ j hj; exact absurd hj (Finset.notMem_empty j)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem emptyUniformTubeSet_parent {s : Finset ι} (hs : s = ∅) (T : ι → Tube δ E) (N : ℕ)
    (C : ℝ≥0) (tb : (k : ℕ) → ι → Tube (gridScale δ N k) E) (k : ℕ) :
    (emptyUniformTubeSet hs T N C tb).cover.indexSet k = ∅ := rfl


end EmptyFamily

end MultiScaleFac

end Kakeya

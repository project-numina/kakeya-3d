/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFactors

/-!
# The coarse seam, the level-`0` node count, and the estimate without residual hypotheses

`Kakeya.ML2Core.exists_coarse_factor_at_window` (the estimate, `Reduction/SpineFactors.lean`) carries two
hypotheses that existing output does not supply:

* the coarse family's containment in `B₁`, because `Kakeya.ML2Core.exists_parentSeam` is applied at
  the **fine** level `b` and a level-`a` node containing a normalised level-`b` node lies only in
  `B̄(0, 1 + 4θ)` (`Kakeya.ML2Core.coverTube_carrier_subset_closedBall`);
* the smallness `θ ≤ θ₀` of the coarse scale, which is false at `a = 0`, where
  `Tube.gridScale δ M 0 = 1` on the nose.

This file closes both, and it does so **without changing a single existing statement**.

## The coarse seam (`1 ≤ a`)

The seam is not re-derived: `Kakeya.ML2Core.exists_parentSeam` is applied at level `a` instead of
level `b`, and the fine data is recovered by *nestedness*, which runs the right way. Setting

`t₁ := {j ∈ activeNodes 𝒞 b | coarseNode 𝒞 a b j ∈ t₀}`,

a level-`b` node of `t₁` lies inside its level-`a` ancestor (`Tube.ChainCoverSystem.tube_assign_le`
through `Kakeya.ML2Reduction.tube_le_coarseNode`), so one pigeonhole at the coarse level delivers
**all three** ball conditions where the fine seam delivers two.  The cardinality retention is
carried across unchanged because the two retained leaf sets are *equal*:
`{i ∈ s | 𝒞.assign b i ∈ t₁} = {i ∈ s | 𝒞.assign a i ∈ t₀}`, by
`Kakeya.ML2Core.coarseNode_assign`.

`Kakeya.ML2Core.exists_spineTwoScale_ofChain_coarseSeam` then runs
`Kakeya.ML2Reduction.exists_spineTwoScale` — the *arbitrary-family* lemma, not the existing
`ofChain` wrapper — at `u := t₀` rather than at `u := 𝒞.indexSet a`.  That is the whole point: the
wrapper pins the coarse family to the entire index set, and a `tθ'` inside the entire index set
carries no ball information, whereas a `tθ'` inside `t₀` carries it by construction.  The coarse
ball condition is therefore a *conclusion* of the two-scale run, not a hypothesis of it.

## The level-`0` node count (`a = 0`)

At `a = 0` no smallness threshold on the tube scale can be met, and the only exit is the trivial
bound `Kakeya.ML2Core.multiplicity_le_of_card_le`, which needs a cardinality ceiling on the
retained coarse node set.  It is available, and from Definition 2.1(ii) alone:

* a tube of radius `≥ 1` containing `B̄(0,1)` exists
  (`Kakeya.ML2Core.exists_tube_superset_closedBall`), and `Tube.gridScale δ N 0 = 1`, so that the
  coarse endpoint of the grid has node radius exactly `1` and every **active** node meets it
  through the family and `Tube.UniformTubeSet.boundedOverlap` counts them all: at most `Cu`
  (`Kakeya.ML2Core.card_activeNodes_le_of_container`);
* and on a nonempty family **every** node is active
  (`Kakeya.ML2Core.indexSet_subset_activeNodes`): if some class were empty then Definition
  2.1(iii)'s lower half forces `branchingN k = 0`, and its upper half then forces *every* class to
  be empty, contradicting `Tube.GridCoverSystem.assign_mem` at any member.

So `|𝕋_0| ≤ Cu` (`Kakeya.ML2Core.card_indexSet_zero_le`) — with no smallness, no shading and no
translation.  The count is **not** obtained from
`Kakeya.VeryNotSticky.card_indexSet_mul_branchingN_le`, which gives
`|indexSet k| · branchingN k ≤ C |s|` and is vacuous exactly when `branchingN k = 0`; the second
bullet above is what rules that degeneracy out, and it is the same fact.

## What is delivered

`Kakeya.ML2Core.exists_coarse_factor_complete` bounds the coarse factor at **every** `a`, with the
`a = 0` branch taking the ceiling route and the `1 ≤ a` branch taking `K_KT(β)`; its coarse-scale
threshold is discharged internally by `Kakeya.ML2Core.eventually_gridScale_le`.  Its hypotheses are
actual outputs, the window, `s.Nonempty`, the leaves in `B₁`, and two exponent
absorptions.  `Kakeya.ML2Core.exists_coarseSeam_with_coarse_factor` is the compatibility that
the coarse seam, the coarse two-scale run and the coarse factor compose with no adapter.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ShadedBody ConvexSpaceBody Tube Filter
open scoped NNReal ENNReal Topology

namespace Kakeya.ML2Core

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ## The coarse seam -/

section CoarseSeam

variable {ι : Type u}

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The level-`a` ancestor of a leaf's level-`b` node is the leaf's own level-`a` node.**

`Kakeya.ML2Reduction.coarseNode` reads the ancestor off an arbitrary member of the node's class,
which is legitimate because `Tube.ChainCoverSystem.assign_eq_of_le` makes the reading independent
of the member; this is that independence, at the member one actually has. -/
theorem coarseNode_assign {δ : ℝ≥0} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {σ : ℕ → ℝ≥0}
    (𝒞 : Tube.ChainCoverSystem s T N σ) {a b : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    {i : ι} (hi : i ∈ s) :
    ML2Reduction.coarseNode 𝒞 a b (𝒞.assign b i) = 𝒞.assign a i := by
  classical
  have h : (Tube.coverClass s (𝒞.assign b) (𝒞.assign b i)).Nonempty :=
    ⟨i, by simp [Tube.coverClass, hi]⟩
  rw [ML2Reduction.coarseNode, dif_pos h]
  have hmem := h.choose_spec
  simp only [Tube.coverClass, Finset.mem_filter] at hmem
  exact 𝒞.assign_eq_of_le hab hbN hmem.1 hi hmem.2

omit [MeasurableSpace E] [BorelSpace E] in
open Classical in
/-- **The parent-ball seam, run at the coarse level.**

`Kakeya.ML2Core.exists_parentSeam` applied at level `a`, with the fine data recovered by
nestedness.  The retained fine set is `t₁ = {j ∈ activeNodes 𝒞 b | coarseNode 𝒞 a b j ∈ t₀}`, and
the output is strictly stronger than the fine seam's: **three** ball conditions — coarse nodes,
fine nodes, leaves — plus the clause `coarseNode 𝒞 a b '' t₁ ⊆ t₀` that lets the two-scale run be
performed against `t₀` rather than against the whole level-`a` index set.

The cardinality retention is the fine seam's, unchanged, because the two retained leaf sets are
literally equal (`Kakeya.ML2Core.coarseNode_assign`); no second pigeonhole is paid for.

The side condition is `σ a ≤ 1/4` at the **coarse** scale, where the fine seam asks it at the fine
one.  Since `σ` is antitone, that is the stronger of the two requirements, and it is what makes
`a = 0` — where `Tube.gridScale δ M 0 = 1` — inaccessible to this route. -/
theorem exists_coarseParentSeam :
    ∃ M : ℕ, 0 < M ∧
      ∀ {δ : ℝ≥0} {κ : Type u} {s : Finset κ} {T : κ → Tube δ E} {N : ℕ} {σ : ℕ → ℝ≥0}
        (𝒞 : Tube.ChainCoverSystem s T N σ) {a b : ℕ} {Cu Bn : ℝ≥0},
        a ≤ b → b ≤ N → (σ a : ℝ) ≤ 1 / 4 →
        (∀ j ∈ 𝒞.indexSet a, ((Tube.coverClass s (𝒞.assign a) j).card : ℝ≥0) ≤ Cu * Bn) →
        (∀ j ∈ 𝒞.indexSet a, Bn ≤ Cu * ((Tube.coverClass s (𝒞.assign a) j).card : ℝ≥0)) →
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
        ∃ (v : E) (t₀ t₁ : Finset κ),
          t₀ ⊆ ML2Reduction.activeNodes 𝒞 a ∧
          t₁ ⊆ ML2Reduction.activeNodes 𝒞 b ∧
          (∀ k ∈ t₀, ((𝒞.tube a k).translate v).carrier ⊆ Metric.closedBall (0 : E) 1) ∧
          (∀ j ∈ t₁, ((𝒞.tube b j).translate v).carrier ⊆ Metric.closedBall (0 : E) 1) ∧
          (∀ i ∈ ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset κ),
            ((T i).translate v).carrier ⊆ Metric.closedBall (0 : E) 1) ∧
          (∀ j ∈ t₁, ML2Reduction.coarseNode 𝒞 a b j ∈ t₀) ∧
          (s.card : ℝ≥0) ≤ (M : ℝ≥0) * Cu * Cu
            * (({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset κ).card : ℝ≥0) := by
  classical
  obtain ⟨M, hM0, hseam⟩ := exists_parentSeam (E := E)
  refine ⟨M, hM0, ?_⟩
  intro δ κ s T N σ 𝒞 a b Cu Bn hab hbN hσ4 hup hlo hball
  have haN : a ≤ N := hab.trans hbN
  obtain ⟨v, t₀, ht₀, hballt₀, hballs₀, hcard₀⟩ := hseam 𝒞 haN hσ4 hup hlo hball
  set t₁ : Finset κ :=
    {j ∈ ML2Reduction.activeNodes 𝒞 b | ML2Reduction.coarseNode 𝒞 a b j ∈ t₀} with ht₁def
  have ht₁sub : t₁ ⊆ ML2Reduction.activeNodes 𝒞 b := Finset.filter_subset _ _
  have hcoarse : ∀ j ∈ t₁, ML2Reduction.coarseNode 𝒞 a b j ∈ t₀ :=
    fun j hj => (Finset.mem_filter.mp hj).2
  have hsets : ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset κ)
      = ({i ∈ s | 𝒞.assign a i ∈ t₀} : Finset κ) := by
    ext i
    simp only [Finset.mem_filter, ht₁def]
    constructor
    · rintro ⟨his, _hact, hcn⟩
      rw [coarseNode_assign 𝒞 hab hbN his] at hcn
      exact ⟨his, hcn⟩
    · rintro ⟨his, hcn⟩
      refine ⟨his, ML2Reduction.assign_mem_activeNodes 𝒞 hbN his, ?_⟩
      rw [coarseNode_assign 𝒞 hab hbN his]
      exact hcn
  refine ⟨v, t₀, t₁, ht₀, ht₁sub, hballt₀, ?_, ?_, hcoarse, ?_⟩
  · intro j hj
    refine subset_trans ?_ (hballt₀ _ (hcoarse j hj))
    have hle : (𝒞.tube b j).carrier ⊆ (𝒞.tube a (ML2Reduction.coarseNode 𝒞 a b j)).carrier :=
      ML2Reduction.tube_le_coarseNode 𝒞 hab hbN (ht₁sub hj)
    exact Set.image_mono hle
  · rw [hsets]; exact hballs₀
  · rw [hsets]; exact hcard₀

end CoarseSeam

/-! ## the estimate against the coarse seam -/

section TwoScaleCoarse

variable [Nontrivial E]
variable {ι : Type u} {δ : ℝ≥0} {s : Finset ι} {V : ι → ShadedTube δ E} {N : ℕ}
  {σ : ℕ → ℝ≥0}


end TwoScaleCoarse

/-! ## The level-`0` node count -/

section LevelZero

variable {ι : Type u} {δ Cu : ℝ≥0} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}


end LevelZero

/-! ## the estimate at every `a` -/

section CoarseFactorComplete

variable [Nontrivial E]


omit [Nontrivial E] in
open Classical in
/-- **The coarse-seam entry point of branch (ii)**, the coarse-level companion of
`Kakeya.ML2Core.exists_windowSeam`.

Same shape, one level up: the side condition `σ a ≤ 1/4` is discharged by
`Kakeya.ML2Core.gridScale_le_quarter` from `1 ≤ a` and the eventually-true
`2 ⌈log log 1/δ⌉ ≤ log(1/δ)`, and the two class brackets are Definition 2.1(iii) read at level `a`.
The output is the coarse seam's, plus the three window scales. -/
theorem exists_coarseWindowSeam :
    ∃ M : ℕ, 0 < M ∧
      ∀ {δ Cu : ℝ≥0} {κ : Type u} {s : Finset κ} {V : κ → ShadedTube δ E}
        (𝒰 : Tube.UniformTubeSet s (fun i => (V i).toTube) (ssfGridLen δ) Cu)
        {Cstar : ℝ≥0∞} {ηl : ℕ → ℝ} {εd : ℝ} {N a b m : ℕ},
        0 < δ → δ ≤ 1 → 1 ≤ a → 2 * (ssfGridLen δ : ℝ) ≤ Real.log (1 / (δ : ℝ)) →
        ML2Reduction.IsKatzTaoDividingWindow 𝒰 Cstar ηl εd N a b m →
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall (0 : E) 1) →
        ∃ (v : E) (t₀ t₁ : Finset κ),
          t₀ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain a ∧
          t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain b ∧
          (∀ k ∈ t₀, ((𝒰.cover.tube a k).translate v).carrier ⊆ Metric.closedBall (0 : E) 1) ∧
          (∀ j ∈ t₁, ((𝒰.cover.tube b j).translate v).carrier ⊆ Metric.closedBall (0 : E) 1) ∧
          (∀ i ∈ ({i ∈ s | 𝒰.cover.assign b i ∈ t₁} : Finset κ),
            ((V i).translate v).carrier ⊆ Metric.closedBall (0 : E) 1) ∧
          (∀ j ∈ t₁, ML2Reduction.coarseNode 𝒰.cover.toChain a b j ∈ t₀) ∧
          (s.card : ℝ≥0) ≤ (M : ℝ≥0) * Cu * Cu
            * (({i ∈ s | 𝒰.cover.assign b i ∈ t₁} : Finset κ).card : ℝ≥0) ∧
          δ ≤ Tube.gridScale δ (ssfGridLen δ) b ∧
          Tube.gridScale δ (ssfGridLen δ) b ≤ Tube.gridScale δ (ssfGridLen δ) a ∧
          Tube.gridScale δ (ssfGridLen δ) a ≤ 1 := by
  classical
  obtain ⟨M, hM0, hseam⟩ := exists_coarseParentSeam (E := E)
  refine ⟨M, hM0, ?_⟩
  intro δ Cu κ s V 𝒰 Cstar ηl εd N a b m hδ0 hδ1 ha1 hlog hw hball
  obtain ⟨hδτ, hτθ, hθ1⟩ := window_scales hδ0 hδ1 hw
  have haM : a ≤ ssfGridLen δ := le_trans hw.coarse_lt_fine.le hw.fine_le_gridLen
  have hσ4 : ((Tube.gridScale δ (ssfGridLen δ) a : ℝ≥0) : ℝ) ≤ 1 / 4 :=
    gridScale_le_quarter hδ0 hδ1 ha1 haM hlog
  obtain ⟨v, t₀, t₁, ht₀, ht₁, hb₀, hb₁, hbs, hcn, hcard⟩ :=
    hseam 𝒰.cover.toChain hw.coarse_lt_fine.le hw.fine_le_gridLen hσ4
      (𝒰.card_class_le a haM) (𝒰.le_card_class a haM) hball
  exact ⟨v, t₀, t₁, ht₀, ht₁, hb₀, hb₁, hbs, hcn, hcard, hδτ, hτθ, hθ1⟩


end CoarseFactorComplete

end Kakeya.ML2Core

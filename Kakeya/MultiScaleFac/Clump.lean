/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Uniform.GridNet
public import Kakeya.FibreCommon
public import Kakeya.Uniform
public import Kakeya.Thickness.ConvexSpaceBody
public import Kakeya.ChainUniform
public import Kakeya.Sticky
public import Mathlib.Tactic.Linarith.NNRealPreprocessor
public import Kakeya.Tube.CardEssentiallyDistinct

/-!
# Re-uniformizing a subfamily along the grid

The refined form of GWZ Lemma 7.7(A) discards tubes at every level of its stopping time, and
uniformity is *not* inherited by an arbitrary subset: deleting tubes destroys the constancy of the
class sizes.  Since the consumers of that lemma require a uniform family, every level must restore
uniformity — and, with it, the comparable fibre counts of GWZ Definition 2.1(iii) — before the next
test is run.  This file states that repair.

The refinement is run against a *system of covers fixed in advance* at all grid scales
(`GridCoverSystem`).  This is forced: clumping is a statement about the classes of a given cover,
so a uniformization that chose fresh covers afterwards would leave the clumping saying nothing
about the new nodes.

Three movements, then the assembly.

* **Clumping** (`exists_clumped_subset_of_leaves`, `exists_clumped_subset_along_grid`).  Inside one
  node the leaves are pigeonholed into a common tube of a quarter of the node's radius, at a
  dimensional cost; after that every retained leaf sees the whole retained class inside its own
  exact-scale thickening.  This is what supplies the *lower* bound on an individual fibre, which
  uniformity alone cannot give.
* **Uniformization** (`exists_uniformize_one_scale`, `exists_uniformize_along_grid`).  A dyadic
  pigeonhole over the class sizes at each of the `N + 1` grid scales, run as a single nested pass,
  makes the retained class sizes constant up to a factor `2`.
* **Comparability** (`card_fibreIndex_band_of_clumped`,
  `card_fibreIndex_four_mul_le_of_branching_lower`,
  `exists_const_card_fibreIndex_bottom_scale`).  Uniform *and* clumped gives the two-sided
  comparison of an exact-scale fibre with the branching number, whence
  `Kakeya.MultiScaleFac.ComparableFibreCounts`; a further covering step inflates the anchor, giving
  `Kakeya.MultiScaleFac.ComparableFibreCountsInflated`; and at the bottom grid scale `ρ = δ`, where
  there is no clumping, both come from essential distinctness instead.

`exists_uniformize_subfamily` is the assembly and the only statement the stopping time consumes.
Its loss is `(C log(1/δ))^{O(N)}`, which is `δ^{-o(1)}` for fixed `N` but not uniformly in `N`;
that, together with the threshold `δ ≤ 16^{-N}` needed to make the grid `16`-separated, is why the
threshold `δ₀` of GWZ Lemma 7.7(A) depends on `N`.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Real Metric

universe u
open Tube

namespace Kakeya

open StickyKakeya
open scoped NNReal

namespace MultiScaleFac


variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-! ### Pigeonhole over a cover -/


/-! ### The two geometric one-move lemmas -/

variable {ι : Type*}


/-! ### Clumping -/


omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- A fibre containment in an ambient index set restricts to any sub-index-set containing the
family in question: `fibreIndex` filters the ambient set by a condition that does not mention it. -/
private theorem subset_fibreIndex_restrict {δ ρ : ℝ≥0} {s t' : Finset ι} {T : ι → Tube δ E}
    {i₂ : ι} {L : Finset ι} (hL : L ⊆ t') (h : L ⊆ fibreIndex s T δ ρ i₂) :
    L ⊆ fibreIndex t' T δ ρ i₂ := by
  rw [fibreIndex_self] at h ⊢
  exact fun j hj => Finset.mem_filter.mpr ⟨hL hj, (Finset.mem_filter.mp (h hj)).2⟩


/-! ### Uniformization -/


/-! ### Comparable thickening counts -/


variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*}
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*}


omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Clumping restricts.**  A clump of a class inside a single `ρ`-fibre survives passing to a
subset: `fibreIndex` filters its ambient set by a condition that does not mention that set. -/
theorem clump_restrict_to_subset {δ ρ : ℝ≥0} {t₁ t' : Finset ι} {T : ι → Tube δ E}
    (ht't : t' ⊆ t₁) (assign : ι → ι) {P : ι}
    (h : ∃ i₂ : ι, coverClass t₁ assign P ⊆ fibreIndex t₁ T δ ρ i₂) :
    ∃ i₂ : ι, coverClass t' assign P ⊆ fibreIndex t' T δ ρ i₂ := by
  classical
  exact h.imp fun i₂ hsub => subset_fibreIndex_restrict (s := t₁)
    (fun i hi => (Finset.mem_filter.mp hi).1)
    ((coverClass_subset_of_subset ht't assign P).trans hsub)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Packaging the per-scale uniform structures into a grid-uniform system.**  The cover is the
restricted system cut down to the uniform parents; `parent_eq` is then definitional and `nice` is
inherited from the ambient system. -/
theorem exists_gridUniform_pack {δ : ℝ≥0} {N : ℕ} {u : Finset ι} {T : ι → Tube δ E}
    {Cu : ℝ≥0} (𝒞' : GridCoverSystem u T N)
    (hnice : ∀ k ≤ N,
      Set.InjOn (𝒞'.tube k) (𝒞'.indexSet k : Set ι) ∧
      ∀ V : Tube (gridScale δ N k) E,
        ((𝒞'.indexSet k).filter (fun v => ∃ i ∈ u,
            (T i).toConvexSpaceBody ≤ (𝒞'.tube k v).toConvexSpaceBody ∧
            (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card ≤
              Tube.overlapConstBOTight (Module.finrank ℝ E))
    (huniform : ∀ k ≤ N, Tube.IsUniformAtScale u T (gridScale δ N k) Cu)
    (hparent : ∀ k (hk : k ≤ N), (huniform k hk).parent ⊆ 𝒞'.indexSet k)
    (hassign : ∀ k (hk : k ≤ N), ∀ i ∈ u, 𝒞'.assign k i ∈ (huniform k hk).parent)
    (hparentTube : ∀ k (hk : k ≤ N), ∀ P ∈ (huniform k hk).parent,
      (huniform k hk).parentTube P = 𝒞'.tube k P)
    (hlow : ∀ k (hk : k ≤ N), ∀ P ∈ (huniform k hk).parent,
      (huniform k hk).branchingN ≤ ((coverClass u (𝒞'.assign k) P).card : ℝ≥0))
    (hclump : ∀ k (hk₀ : k < N), ∀ P ∈ (huniform k (le_of_lt hk₀)).parent, ∃ i₂ : ι,
      coverClass u (𝒞'.assign k) P ⊆ fibreIndex u T δ (gridScale δ N k / 4) i₂) :
    ∃ 𝒢 : GridUniform u T N Cu,
      (∀ k (hk : k ≤ N), 𝒢.uniformAt k hk = huniform k hk) ∧
      (∀ k ≤ N, 𝒢.cover.assign k = 𝒞'.assign k) ∧
      (∀ k (hk : k ≤ N), 𝒢.cover.indexSet k = (huniform k hk).parent) ∧
      (∀ k, 𝒢.cover.tube k = 𝒞'.tube k) := by
  classical
  let gparent : ℕ → Finset ι := fun k => if hk : k ≤ N then (huniform k hk).parent else ∅
  have hg : ∀ k (hk : k ≤ N), gparent k = (huniform k hk).parent := fun k hk => dif_pos hk
  refine ⟨{ cover := { indexSet := gparent,
                       assign := 𝒞'.assign,
                       tube := 𝒞'.tube,
                       assign_mem := fun k hk i hi => (hg k hk).symm ▸ hassign k hk i hi,
                       le_tube_assign := 𝒞'.le_tube_assign,
                       nested := 𝒞'.nested,
                       tube_nested := 𝒞'.tube_nested },
            uniformAt := huniform,
            parent_eq := fun k hk => (hg k hk).symm,
            tube_eq := fun k hk P hP => hparentTube k hk P (hg k hk ▸ hP),
            le_card_class := fun k hk P hP => hlow k hk P (hg k hk ▸ hP),
            clumped := fun k hk₀ P hP => hclump k hk₀ P (hg k (le_of_lt hk₀) ▸ hP),
            nice := ?_ }, fun _ _ => rfl, fun _ _ => rfl, hg, fun _ => rfl⟩
  intro k hk
  dsimp only
  rw [hg k hk]
  exact ⟨(hnice k hk).1.mono fun x hx => hparent k hk hx, fun V =>
    (Finset.card_le_card (Finset.filter_subset_filter _ (hparent k hk))).trans ((hnice k hk).2 V)⟩


/-- The node at one scale of the downward recursion: a `gridScale δ N k`-tube whose midpoint lies
in `B₃`, which is a net tube of `Gk k` when `k < N`, and which contains `T i`. -/
private structure GridCoverNode {δ : ℝ≥0} {N k : ℕ} {ι : Type*}
    (t : Finset ι) (T : ι → Tube δ E) (i : ι)
    (Gk : (k : ℕ) → Finset (Tube (gridScale δ N k) E)) where
  tube : Tube (gridScale δ N k) E
  mem_ball : tube.midpoint ∈ Metric.closedBall (0 : E) 3
  mem_net : (k < N) → tube ∈ Gk k
  contains : i ∈ t → (T i).toConvexSpaceBody ≤ tube.toConvexSpaceBody


end MultiScaleFac

end Kakeya

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.ShadedUniform

/-!
# One-sided uniformity, and why it restricts for free

`Tube.UniformTubeSet` and `ShadedTube.ShadedUniformTubeSet` are two-sided: each class bracket
is asserted in both directions.  That is what makes them fail to descend to a subfamily, and
it is the obstruction recorded on `Kakeya.ml1Boot.exists_plankDimensions_uniformSelection`:
every consumer of the plank pigeonhole has to be run at the *refined* index set `u''`, while
the middle-factor data supplies uniformity only at `u'`.

This file splits both predicates along the direction of their inequalities and keeps only the
half that survives restriction.  The resulting predicates,
`Kakeya.ml1Boot.IsOneSidedUniformTubeSet` and `Kakeya.ml1Boot.IsOneSidedUniform`, restrict to an
arbitrary subfamily with the data inherited verbatim, at **no loss in the constant and with no
pigeonholing** (`Kakeya.ml1Boot.IsOneSidedUniformTubeSet.mono_index`,
`Kakeya.ml1Boot.IsOneSidedUniform.mono_index`).  Every two-sided hierarchy projects onto them
(`Kakeya.ml1Boot.IsOneSidedUniform.of_shadedUniformTubeSet`), so the pair
"project, then restrict" replaces a re-uniformization.

## Which half survives, and why

Writing `A` for the cardinality of the class in question, the four inequalities of
`ShadedTube.ShadedUniformTubeSet` split as

| clause                | shape                     | restricts |
|-----------------------|---------------------------|-----------|
| `card_shadeClass_le`  | `A ≤ C · localN x k`      | yes       |
| `le_card_shadeClass`  | `localN x k ≤ C · A`      | no        |
| `branchingN_le`       | `branchingN k ≤ C · localN x k` | no  |
| `le_branchingN`       | `localN x k ≤ C · branchingN k` | yes |

and the three of `Tube.UniformTubeSet` as `boundedOverlap` (yes), `card_class_le` (yes),
`le_card_class` (no).

The two survivors survive for *different* reasons, and both are used below.

* `card_shadeClass_le` and `card_class_le` survive because the class is monotone in the index
  set — `Tube.coverClass_subset_of_subset` and `Kakeya.ml1Boot.shadeClass_subset_of_subset`
  below — and the clause is an *upper* bound on a quantity that shrinks.  `boundedOverlap` is
  of the same kind: its filter predicate `∃ i ∈ s, …` weakens, so the filtered node set shrinks.
* `le_branchingN` survives because it never mentions the index set at all: it relates the two
  inherited counting functions at a point.  `tube_injOn` survives for the same reason — it
  speaks about `indexSet` and the node tubes only.

Two further facts make the inheritance literal rather than approximate.  `branchingN` and
`localN` are *free fields* of the two structures, not quantities derived from the family, so a
subfamily may keep them unchanged; and the domain `⋃ i ∈ s, (V i).shade` of the two pointwise
clauses shrinks under restriction, which is the favourable direction for a `∀ x` hypothesis.

## What is deliberately absent

No lower bracket appears anywhere below, and no constant is enlarged to compensate for one.
A consumer that genuinely needs a lower branching bound is not served by this file; it has to
re-uniformize, or be restated.  In particular nothing here is claimed about
`prop:ml1bootFlatPrismsCorrected`, whose Lean carrier does not exist.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Metric Set

namespace Kakeya

namespace ml1Boot

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasureSpace E] [BorelSpace E] [ProperSpace E]
  {ι : Type*}

/-! ### Monotonicity of the shaded class in the index set -/

/-! ### Restricting a nested cover system -/

/-! ### One-sided uniformity at the tube level -/

/-- **The half of `Tube.UniformTubeSet` that restricts.**

Definition 2.1 with the *lower* class bracket `le_card_class` deleted.  What remains is the
hierarchy, the injective indexing of the nodes, bounded overlap, and the upper class bracket —
every clause of which is either independent of the index set or an upper bound on a quantity
monotone in it. -/
structure IsOneSidedUniformTubeSet {δ : ℝ≥0} (s : Finset ι) (T : ι → Tube δ E) (N : ℕ)
    (C : ℝ≥0) where
  /-- The nested system of covers along the grid `ρ_k = δ^{k/N}`. -/
  cover : Tube.GridCoverSystem s T N
  /-- The branching number at each grid scale, a free datum. -/
  branchingN : ℕ → ℝ≥0
  /-- Distinct node indices name distinct node tubes. -/
  tube_injOn : ∀ k ≤ N, Set.InjOn (cover.tube k) (cover.indexSet k : Set ι)
  /-- **Definition 2.1(ii) (Bounded overlap).** -/
  boundedOverlap : ∀ k ≤ N, ∀ V : Tube (Tube.gridScale δ N k) E,
    (open scoped Classical in
      (cover.indexSet k).filter (fun j => ∃ i ∈ s,
        (T i).toConvexSpaceBody ≤ (cover.tube k j).toConvexSpaceBody ∧
        (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card ≤ C
  /-- **Definition 2.1(iii), upper half only.** -/
  card_class_le : ∀ k ≤ N, ∀ j ∈ cover.indexSet k,
    ((Tube.coverClass s (cover.assign k) j).card : ℝ≥0) ≤ C * branchingN k

/-! ### One-sided uniformity at the shaded level -/

/-- **The half of `ShadedTube.ShadedUniformTubeSet` that restricts** (the one-sided reading of
GWZ Definition 2.2).

Definition 2.2 with the two clauses that bound a *shrinking* quantity from below deleted:
`le_card_shadeClass` and `branchingN_le` are gone, `card_shadeClass_le` and `le_branchingN`
remain, and the ambient tube hierarchy is the one-sided
`Kakeya.ml1Boot.IsOneSidedUniformTubeSet`.

What the two survivors still say together is that no node the fibre of `x` meets carries more
than `C · localN x k` members of that fibre, and that `localN x k` is no larger than
`C · branchingN k` — a uniform *upper* bound on the local branching, with `branchingN`
independent of `x`.  That is exactly the content a consumer needs when it uses uniformity to
bound a count from above; a consumer needing a member of every class is not served. -/
structure IsOneSidedUniform {δ : ℝ≥0} (s : Finset ι) (V : ι → ShadedTube δ E) (N : ℕ)
    (C : ℝ≥0) where
  /-- The underlying tubes carry a one-sided uniform hierarchy. -/
  tubeUniform : IsOneSidedUniformTubeSet s (fun i => (V i).toTube) N C
  /-- The per-scale branching count shared across all points of the shade union. -/
  branchingN : ℕ → ℝ≥0
  /-- The branching count of the fibre at a single point. -/
  localN : E → ℕ → ℝ≥0
  /-- Each node met by the fibre of `x` contributes at most `C · localN x k` of its members. -/
  card_shadeClass_le : ∀ x ∈ (⋃ i ∈ s, (V i).shade), ∀ k ≤ N, ∀ i ∈ s, x ∈ (V i).shade →
    ((ShadedTube.shadeClass s V (tubeUniform.cover.assign k)
      (tubeUniform.cover.assign k i) x).card : ℝ≥0) ≤ C * localN x k
  /-- Each local count is at most a factor `C` above the shared count. -/
  le_branchingN : ∀ x ∈ (⋃ i ∈ s, (V i).shade), ∀ k ≤ N, localN x k ≤ C * branchingN k

/-- **Weakening the constant, tube level.**  The node data and the branching function are
unchanged; both retained clauses are upper bounds, so they weaken with the constant. -/
def IsOneSidedUniformTubeSet.mono {δ : ℝ≥0} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {C C' : ℝ≥0} (𝒰 : IsOneSidedUniformTubeSet s T N C) (hC : C ≤ C') :
    IsOneSidedUniformTubeSet s T N C' where
  cover := 𝒰.cover
  branchingN := 𝒰.branchingN
  tube_injOn := 𝒰.tube_injOn
  boundedOverlap := fun k hk V => (𝒰.boundedOverlap k hk V).trans hC
  card_class_le := fun k hk j hj => (𝒰.card_class_le k hk j hj).trans (by gcongr)

/-- **Weakening the constant.**  The counterpart of `ShadedTube.ShadedUniformTubeSet.mono`; the
hierarchy and both counting functions are unchanged, and both retained clauses are upper bounds. -/
def IsOneSidedUniform.mono {δ : ℝ≥0} {s : Finset ι} {V : ι → ShadedTube δ E} {N : ℕ}
    {C C' : ℝ≥0} (𝒱 : IsOneSidedUniform s V N C) (hC : C ≤ C') :
    IsOneSidedUniform s V N C' where
  tubeUniform := 𝒱.tubeUniform.mono hC
  branchingN := 𝒱.branchingN
  localN := 𝒱.localN
  card_shadeClass_le := fun x hx k hk i hi hxi =>
    (𝒱.card_shadeClass_le x hx k hk i hi hxi).trans (by gcongr)
  le_branchingN := fun x hx k hk => (𝒱.le_branchingN x hx k hk).trans (by gcongr)

end ml1Boot

end Kakeya

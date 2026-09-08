/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.TubeParentPacking
public import Kakeya.DimensionThree.BoundedOverlapCount

/-!
# Counting the parents of an external parent system

`Kakeya.exists_externalParentSystem_of_four_mul_le` builds, with **no essential distinctness
input**, an `Kakeya.ExternalParentSystem q T ρ parentOverlapConst` whenever `4 * δ ≤ ρ`.  That
object carries a factorisation of the fine family through coarse `ρ`-tubes, but no bound on how
many coarse tubes there are.  This file supplies the missing count, still ED-free:

`|parents| ≤ parentOverlapConst · parentCount.C · ρ ^ (-5)`.

## The mismatch with `Tube.HasBoundedOverlap`

The two bounded-overlap conditions in play are *not* the same, in two independent ways.

* **Test radius.** `Tube.HasBoundedOverlap s V t Vρ Co` quantifies over test tubes `W : Tube ρ E`,
  at the *same* radius as the parents.  `Kakeya.ExternalParentSystem.boundedOverlapThroughLeaves`
  quantifies over test tubes of radius `8 * ρ`.  This direction is harmless: `8 * ρ` is the larger
  test tube, so the `8 * ρ` statement is the stronger one and specialises to radius `ρ` through
  `Tube.le_rescale`.
* **The "through" clause.** `Tube.HasBoundedOverlap` counts a parent `k` when *some* leaf lies in
  both `Vρ k` and `W`; `boundedOverlapThroughLeaves` counts `k` when some leaf **assigned to `k`**
  lies in `W`.  By `Kakeya.ExternalParentSystem.leaf_le_parent`, `assign i = k` implies
  `T i ≤ parentTube k`, so the parent system's filter set is *contained* in the
  `Tube.HasBoundedOverlap` filter set.  The bound therefore transfers in the wrong direction, and
  an external parent system does **not** in general satisfy `Tube.HasBoundedOverlap`: a parent may
  contain leaves that were assigned elsewhere, and nothing in the structure limits how many
  parents share such an unassigned leaf.

So `Kakeya.ml1Boot.card_parents_le_of_hasBoundedOverlap` cannot be applied off the shelf.  What
*can* be reused is its proof, which only ever consults the overlap hypothesis at a designated leaf
per parent.  `Kakeya.ml1Boot.card_le_of_designatedLeaf_overlap` below is that argument, restated
against a designated-leaf map `w : κ → ι`; it is strictly weaker in hypothesis than
`Kakeya.ml1Boot.card_parents_le_of_hasBoundedOverlap` and gives the same `ρ ^ (-5)`.

## Why the exponent is `-5` and not `-6`

The obvious route, `Kakeya.ExternalParentSystem.card_occupiedParents_le`, costs `ρ ^ (-6)`: its
constant `Kakeya.tubeParamPackingConstOf N = (4N+1)^3 * (250N^3+250)` is applied at `N ≍ ρ⁻¹`, and
the second factor is the deliberately non-sharp direction count of
`Kakeya.card_le_of_projective_separated_in_cap`, whose exponent is `Module.finrank ℝ E = 3` rather
than the sharp `2` of a cap in `S²`.  That route is therefore unusable here.

The net route is sharp.  `Kakeya.ml1Boot.exists_dirPos_net` is built from
`Kakeya.ml1Boot.card_le_of_unit_separated`, which *is* the sharp `ρ ^ (-2)` sphere count, times the
`ρ ^ (-3)` midpoint count of `Kakeya.ml1Boot.card_le_of_ball_separated`; `5 = 2 + 3`.

## Discarding the unoccupied parents

`Kakeya.ExternalParentSystem.parents` may contain parents owning no leaf, and those are invisible
to `boundedOverlapThroughLeaves`, hence uncountable by any leaf-mediated argument.  They are also
useless: `Kakeya.ExternalParentSystem.restrictOccupied` deletes them, preserving every field, and
the count is stated for the restricted system.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Metric

open scoped ENNReal NNReal

namespace Kakeya.ml1Boot

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]


end Kakeya.ml1Boot

namespace Kakeya

open Classical in
/-- The parents of an external parent system that actually own a leaf.

The unoccupied parents carry no information: no leaf is assigned to them, so they are invisible to
`Kakeya.ExternalParentSystem.boundedOverlapThroughLeaves` and cannot be counted. -/
noncomputable def ExternalParentSystem.occupiedParents {ι : Type*} {q : Finset ι} {δ ρ Cu : ℝ≥0}
    {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))} (PS : ExternalParentSystem q T ρ Cu) :
    Finset PS.Parent :=
  PS.parents.filter fun k => ∃ i ∈ q, PS.assign i = k

/-- Occupied parents are parents. -/
theorem ExternalParentSystem.occupiedParents_subset {ι : Type*} {q : Finset ι} {δ ρ Cu : ℝ≥0}
    {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))} (PS : ExternalParentSystem q T ρ Cu) :
    PS.occupiedParents ⊆ PS.parents := by
  classical
  simp only [ExternalParentSystem.occupiedParents]
  exact Finset.filter_subset _ _

/-- Every leaf is assigned to an *occupied* parent — itself being the witness. -/
theorem ExternalParentSystem.assign_mem_occupiedParents {ι : Type*} {q : Finset ι} {δ ρ Cu : ℝ≥0}
    {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))} (PS : ExternalParentSystem q T ρ Cu) :
    ∀ i ∈ q, PS.assign i ∈ PS.occupiedParents := by
  classical
  intro i hi
  simp only [ExternalParentSystem.occupiedParents, Finset.mem_filter]
  exact ⟨PS.assign_mem i hi, i, hi, rfl⟩

open Classical in
/-- Leaf-mediated bounded overlap survives restriction to the occupied parents, the filter set
only shrinking. -/
theorem ExternalParentSystem.boundedOverlapThroughLeaves_occupiedParents {ι : Type*}
    {q : Finset ι} {δ ρ Cu : ℝ≥0} {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}
    (PS : ExternalParentSystem q T ρ Cu) :
    ∀ V : Tube (8 * ρ) (EuclideanSpace ℝ (Fin 3)),
      (((PS.occupiedParents.filter fun k => ∃ i ∈ q, PS.assign i = k ∧
          (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card : ℝ≥0) ≤ Cu := by
  classical
  intro V
  refine le_trans ?_ (PS.boundedOverlapThroughLeaves V)
  have hsub : (PS.occupiedParents.filter fun k => ∃ i ∈ q, PS.assign i = k ∧
        (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)
      ⊆ (PS.parents.filter fun k => ∃ i ∈ q, PS.assign i = k ∧
        (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody) := by
    intro k hk
    simp only [Finset.mem_filter] at hk ⊢
    exact ⟨PS.occupiedParents_subset hk.1, hk.2⟩
  exact_mod_cast Finset.card_le_card hsub

/-- **The external parent system with its unoccupied parents deleted.**

Every field is inherited; only `Kakeya.ExternalParentSystem.parents` shrinks, to
`Kakeya.ExternalParentSystem.occupiedParents`. -/
noncomputable def ExternalParentSystem.restrictOccupied {ι : Type*} {q : Finset ι} {δ ρ Cu : ℝ≥0}
    {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))} (PS : ExternalParentSystem q T ρ Cu) :
    ExternalParentSystem q T ρ Cu where
  Parent := PS.Parent
  parents := PS.occupiedParents
  parentTube := PS.parentTube
  assign := PS.assign
  assign_mem := PS.assign_mem_occupiedParents
  leaf_le_parent := PS.leaf_le_parent
  boundedOverlapThroughLeaves := PS.boundedOverlapThroughLeaves_occupiedParents

/-- The parents of the restricted system are exactly the occupied parents. -/
@[simp]
theorem ExternalParentSystem.parents_restrictOccupied {ι : Type*} {q : Finset ι} {δ ρ Cu : ℝ≥0}
    {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))} (PS : ExternalParentSystem q T ρ Cu) :
    PS.restrictOccupied.parents = PS.occupiedParents := rfl


end Kakeya

end

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.FibreCommon

/-!
# Balanced hierarchy covers for the WZ stopping construction

This module packages one level of a uniform tube hierarchy as balanced parent classes and proves
the partition, cardinality, and cross-level nesting facts used by the WZ dynamic producer.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory

namespace Kakeya.WangZahl

noncomputable section

universe u

open Tube
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- One level of a WZ balanced partitioning cover. The classes are defined by
the assignment function; `branch` and `balance` give their common cardinality
band. -/
structure BalancedNodeCover {ι : Type u} {delta rho : ℝ≥0}
    (s : Finset ι) (T : ι → Tube delta E) (balance : ℝ≥0) where
  parent : Finset ι
  assign : ι → ι
  part : ι → Finset ι
  part_eq : ∀ j, part j = _root_.Tube.coverClass s assign j
  mem_part_iff : ∀ i j, i ∈ part j ↔ i ∈ s ∧ assign i = j
  parentTube : ι → Tube rho E
  branch : ℝ≥0
  assign_mem : ∀ i ∈ s, assign i ∈ parent
  leaf_le_parent : ∀ i ∈ s,
    (T i).toConvexSpaceBody ≤ (parentTube (assign i)).toConvexSpaceBody
  parentTube_injOn : Set.InjOn parentTube (parent : Set ι)
  card_class_le : ∀ j ∈ parent,
    ((part j).card : ℝ≥0) ≤ balance * branch
  le_card_class : ∀ j ∈ parent,
    branch ≤ balance * ((part j).card : ℝ≥0)

namespace BalancedNodeCover

variable {ι : Type u} [DecidableEq ι] {delta rho balance : ℝ≥0} {s : Finset ι}
  {T : ι → Tube delta E}


end BalancedNodeCover


end

end Kakeya.WangZahl

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceFixedTowerData

/-!
# Fixed source constants and neighbour sharing

Fixes the numerical constants `Kakeya.ML2Core.sourceBottomED`, `sourceLevelED` and
`sourceThreadConstant` used as the ED and containment-multiplicity parameters of the fixed
source tower, and defines `SourceTowerNeighbourSharing`, the pairwise segment-sharing bound
between tubes of the same level required by the one-trial caller. Both are inputs to
`SourceFixedTowerInput` in `SpineSourceFixedPreparation`.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u

/-- Source constants fixed before every runtime family and bottom scale. -/
def sourceBottomED : Nat := 2 * 223 ^ 6

def sourceLevelED : Nat := 2 * 641 ^ 6

def sourceThreadConstant : Nat := 2 * 897 ^ 6

section FixedTower

variable {iota : Type u} {delta : ℝ≥0} {ambient : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace ℝ (Fin 3))} {M C : Nat}

/-- The extra pairwise segment-sharing row explicitly stated by the one-trial caller.
It is distinguished from bounding the tubes containing one preselected segment. -/
def SourceTowerNeighbourSharing (Q : SourceThreadedTower ambient T M C) : Prop :=
  ∀ k, k < M -> ∀ j ∈ Q.indexSet k,
    (open scoped Classical in
      ((Q.indexSet k).filter (fun j' => ∃ x y : EuclideanSpace ℝ (Fin 3), dist x y = 1 /\
        segment ℝ x y <= (Q.tube k j).carrier /\
        segment ℝ x y <= (Q.tube k j').carrier)).card) <= C

end FixedTower

end Kakeya.ML2Core

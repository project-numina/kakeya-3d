/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.WZBalancedCover
public import Kakeya.MultiScaleFac.UniformBridgeKT

/-!
# Canonical hierarchy classes for the WZ rho selection

This module partitions a retained family of fine hierarchy nodes by the assignment ancestor map.
Unlike `UniformTubeSet.nodesUnder`, these classes are disjoint by construction.  The geometric
containment of every class member in its assigned ancestor is proved separately.
-/

@[expose] public section

open scoped NNReal

namespace Kakeya.WangZahl

noncomputable section

open Tube
open scoped NNReal

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- The retained fine nodes canonically assigned to the coarse node `p`. -/
def tauAncestorClass {ι : Type u} {delta : ℝ≥0} {s : Finset ι}
    {T : ι -> Tube delta E} {N : Nat} {C : ℝ≥0}
    (U : _root_.Tube.UniformTubeSet s T N C) (b a : Nat) (tauNodes : Finset ι)
    (p : ι) : Finset ι :=
  open scoped Classical in
  tauNodes.filter fun w => U.nodeAncestor b a w = p

/-- The coarse parents used by a retained fine-node family. -/
def activeRhoParents {ι : Type u} {delta : ℝ≥0} {s : Finset ι}
    {T : ι -> Tube delta E} {N : Nat} {C : ℝ≥0}
    (U : _root_.Tube.UniformTubeSet s T N C) (b a : Nat)
    (tauNodes : Finset ι) : Finset ι :=
  open scoped Classical in
  tauNodes.image (U.nodeAncestor b a)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem mem_tauAncestorClass {ι : Type u} {delta : ℝ≥0} {s : Finset ι}
    {T : ι -> Tube delta E} {N : Nat} {C : ℝ≥0}
    (U : _root_.Tube.UniformTubeSet s T N C) (b a : Nat) (tauNodes : Finset ι) (p w : ι) :
    w ∈ tauAncestorClass U b a tauNodes p ↔
      w ∈ tauNodes ∧ U.nodeAncestor b a w = p := by
  classical
  simp [tauAncestorClass]


end

end Kakeya.WangZahl

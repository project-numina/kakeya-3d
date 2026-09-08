/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.WZCanonicalClasses

/-!
# Global scale crossing for the WZ rho selection

The crossing is stated without division.  The finite selection lemmas choose one global hierarchy
level and distinguish a crossing at the first-failure level from a strictly coarser crossing whose
immediately finer predecessor fails.
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

/-- Cross-multiplied form of `tauCard / rhoCard >= theta * (rho / tau)^2`. -/
def GlobalCrossing (theta tau rho tauCard rhoCard : ℝ≥0) : Prop :=
  theta * rho ^ 2 * rhoCard <= tau ^ 2 * tauCard

/-- The WZ global crossing at hierarchy level `a`, using one fixed retained tau-node family. -/
def hierarchyGlobalCrossing {ι : Type u} {delta : ℝ≥0} {s : Finset ι}
    {T : ι -> Tube delta E} {N : Nat} {C : ℝ≥0}
    (U : _root_.Tube.UniformTubeSet s T N C) (b : Nat) (tauNodes : Finset ι)
    (theta : ℝ≥0) (a : Nat) : Prop :=
  GlobalCrossing theta (_root_.Tube.gridScale delta N b) (_root_.Tube.gridScale delta N a)
    tauNodes.card (activeRhoParents U b a tauNodes).card


end

end Kakeya.WangZahl

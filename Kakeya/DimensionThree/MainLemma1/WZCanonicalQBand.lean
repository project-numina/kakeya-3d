/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.WZGlobalCrossing

/-!
# Transporting the global WZ ratio to canonical rho fibres

This module combines a two-sided global cardinality ratio with retained canonical-class balance.
All conclusions are cross-multiplied, so no scale division is needed.
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

/-- Cross-multiplied upper bound for a global tau-to-rho cardinality ratio. -/
def GlobalRatioUpperBound (Xi tau rho tauCard rhoCard : ℝ≥0) : Prop :=
  tau ^ 2 * tauCard <= Xi * rho ^ 2 * rhoCard


/-- Enlarge the coefficient in a global upper-ratio bound. -/
theorem GlobalRatioUpperBound.mono {Xi Xi' tau rho tauCard rhoCard : ℝ≥0}
    (hXi : Xi <= Xi') (h : GlobalRatioUpperBound Xi tau rho tauCard rhoCard) :
    GlobalRatioUpperBound Xi' tau rho tauCard rhoCard := by
  calc
    tau ^ 2 * tauCard <= Xi * rho ^ 2 * rhoCard := h
    _ <= Xi' * rho ^ 2 * rhoCard := by gcongr


end

end Kakeya.WangZahl

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceCurrentParentData

/-!
# Current-parent outcome and terminal geometry

`Kakeya.ML2Core.SourceCurrentParentOutcome` is the outcome of the parent-selection stage stated
with the current factor histories of `SpineSourceCurrentParentData` (a potential drop, or joint
window factors with retained concentration and an eccentric or actual parent).
`SourceParentTerminalGeometry` is the same alternative with the history witnesses erased, the
common input for analytic consumers.  `source_current_historical_pieces` derives the
intersection diagram of a restriction against historical parts, and
`source_current_history_payment` telescopes the stage mass payments on the original shading.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

universe u

variable {iota : Type u} {delta : ℝ≥0} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace ℝ (Fin 3))} {M C : Nat}

/-- The source-facing actual outcome uses current factors and paid histories.
All original-Q profile, final-Q statistics and F/P geometry are retained. -/
structure SourceCurrentParentOutcome (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3)))
    (R : Finset iota) (Q' : SourceThreadedTower R T M C)
    (N J A0 A1 : Nat) (e : ℝ) (eta : Nat -> ℝ)
    (etaParent bias etaF : ℝ) (K : Nat) (cap : ℝ≥0) (a b : Nat) : Prop where
  retained : SourceParentRetainedState Q Z R Q' Z (sourceFixedPreparationLoss K delta)
  input : SourceFixedTowerInput Q' A0 A1 etaF
  upper : SourceParentUpperWindow Q' A0 A1 N eta e a b J
  alternative :
    (exists k, SourceTowerWindow delta M e a b k /\
      SourceParentFailedConcentration Q R a k e (eta (J + 1)) /\
      Q.assignedPotential (eta 1 * e ^ 2 / 8) R + 1 <=
        Q.assignedPotential (eta 1 * e ^ 2 / 8) S) \/
    (exists B : SourceJointWindowFactors Q' e a b bias,
      Nonempty (SourceCurrentWindowHistory Q Z Q' B K) /\
      SourceParentRetainedConcentration Q' e (eta (J + 1)) a b /\
      (Nonempty (SourceParentEccentric Q' B etaParent) \/
        (exists P : SourceActualParent Q' B etaParent (eta (J + 1)) cap,
          Nonempty (SourceCurrentParentHistory Q Z Q' B P K))))

/-- This common terminal input exposes every current F/P field, with the paid
retained ledger, but does not ask an analytic consumer to reconstruct history. -/
structure SourceParentTerminalGeometry (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3)))
    (R : Finset iota) (Q' : SourceThreadedTower R T M C)
    (N J A0 A1 : Nat) (e : ℝ) (eta : Nat -> ℝ)
    (etaParent bias etaF : ℝ) (K : Nat) (cap : ℝ≥0) (a b : Nat) : Prop where
  retained : SourceParentRetainedState Q Z R Q' Z (sourceFixedPreparationLoss K delta)
  input : SourceFixedTowerInput Q' A0 A1 etaF
  upper : SourceParentUpperWindow Q' A0 A1 N eta e a b J
  alternative :
    (exists k, SourceTowerWindow delta M e a b k /\
      SourceParentFailedConcentration Q R a k e (eta (J + 1)) /\
      Q.assignedPotential (eta 1 * e ^ 2 / 8) R + 1 <=
        Q.assignedPotential (eta 1 * e ^ 2 / 8) S) \/
    (exists B : SourceJointWindowFactors Q' e a b bias,
      SourceParentRetainedConcentration Q' e (eta (J + 1)) a b /\
      (Nonempty (SourceParentEccentric Q' B etaParent) \/
        Nonempty (SourceActualParent Q' B etaParent (eta (J + 1)) cap)))

end Kakeya.ML2Core

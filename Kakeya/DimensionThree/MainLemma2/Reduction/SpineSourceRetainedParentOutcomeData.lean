/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceRetainedAnalyticData
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceZeroDefectData

/-!
# The retained parent outcome

A single `Prop`-valued structure, `SourceRetainedParentOutcome`, bundling one actual-parent
output: the `SourceParentRetainedState` from `Q` to `Q'`, the fixed tower input and upper
window of `Q'`, and an alternative that is either a measured `SourceParentFailedConcentration`
with a strict assigned-potential drop on the original `Q`, or joint window factors on `Q'`
with compatible whole factors and retained concentration, splitting further into the
eccentric case or an actual parent with complete history.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

open ML2Assembly

universe u

variable {iota : Type u} {delta : ℝ≥0} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace ℝ (Fin 3))} {M C : Nat}

/-- Exactly one actual-parent output, including its original-Q failure and its
retained-Q' alternative. The full original lower window is not a Q' field. -/
structure SourceRetainedParentOutcome (Q : SourceThreadedTower S T M C)
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
      Nonempty (SourceCompatibleWholeFactors Q Z Q' B K) /\
      SourceParentRetainedConcentration Q' e (eta (J + 1)) a b /\
      (Nonempty (SourceParentEccentric Q' B etaParent) \/
        (exists P : SourceActualParent Q' B etaParent (eta (J + 1)) cap,
          Nonempty (SourceParentCompleteHistory Q Z Q' B P K))))

end Kakeya.ML2Core

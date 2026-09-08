/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceBudget

/-!
# Input exponents after the returned ambient ceilings

The actual finite preparation, estimator accuracies, and reserve precede
every finite collection of positive ambient input ceilings.
-/

@[expose] public section

namespace Kakeya.ML2Assembly

universe u

/-- All parent and raw middle preparation on the same chosen finite spine. -/
structure SourceLocalPreparation (beta varpi eps1 : ℝ)
    (rawGain rawDens : ℝ -> ℝ) : Prop where
  parent : forall m : Nat, m < ML2Spine.spineCount varpi eps1 ->
    SourceParentMinBounds beta
      (ML2Spine.spineNu beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens))
      (ML2Spine.spineDiv varpi eps1)
      (ML2Spine.spineRung beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) m)
      (ML2Spine.spineRung beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1))
      (rawGain ((ML2Spine.spineRung beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1)) / 16))
      (rawDens ((ML2Spine.spineRung beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1)) / 16))
  middle : forall m : Nat, m < ML2Spine.spineCount varpi eps1 ->
    SourceMiddlePreparation.{u} beta varpi (ML2Spine.spineDiv varpi eps1)
      (ML2Spine.spineRung beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1))
      (rawGain ((ML2Spine.spineRung beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1)) / 16))
      (rawDens ((ML2Spine.spineRung beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1)) / 16))

/-- Late input choices preserve every earlier factor accuracy and the reserve. -/
structure SourceLateInputBounds (beta varpi eps1 : ℝ)
    (rawGain rawDens : ℝ -> ℝ) (s : ℝ) (a : SourceLocalAccuracyData)
    (H : Finset ℝ) (etaL etaIn eta aL : ℝ) : Prop where
  input_pos : 0 < etaIn
  input_lt_loss : etaIn < etaL
  loss_le_accuracy : etaL <= s
  loss_le_ceilings : forall h : ℝ, h ∈ H -> etaL <= h
  shading_pos : 0 < eta
  shading_le_one : eta <= 1
  absorption_pos : 0 < aL
  site_ladder : eta + aL <= etaIn
  site_budget : eta + aL < ML2Spine.spineNu beta varpi eps1
    (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens)
  residual : forall m : Nat, m < ML2Spine.spineCount varpi eps1 ->
    a.kappaC + ML2Spine.spineRung beta varpi eps1
      (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) m <=
      2 * sourceParentMinimum (ML2Spine.spineDiv varpi eps1)
        (ML2Spine.spineRung beta varpi eps1
          (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1))
        (rawGain ((ML2Spine.spineRung beta varpi eps1
          (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1)) / 16))
        (rawDens ((ML2Spine.spineRung beta varpi eps1
          (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1)) / 16))
  reserve_pos : 0 < a.reserve
  budget : forall m : Nat, m < ML2Spine.spineCount varpi eps1 ->
    6 * ML2Spine.spineNu beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) +
      a.theta2 + etaIn + a.epsf m + a.epsp m +
      (a.epsc m + ML2Spine.spineRung beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) m) +
      a.kappaPrime + a.reserve <=
      sourceMiddleNetGain (ML2Spine.spineDiv varpi eps1)
        (rawGain ((ML2Spine.spineRung beta varpi eps1
          (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1)) / 16))


end Kakeya.ML2Assembly

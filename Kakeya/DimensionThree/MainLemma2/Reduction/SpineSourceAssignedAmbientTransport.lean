/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceChosenTowerRealization

/-!
# Transporting the assigned source profile to the ambient hierarchy

Interfaces comparing a source tower `SourceThreadedTower` (radii `sourceTowerRadius`, profile
`assignedProfileExp`) with the ambient `UniformTubeSet` hierarchy through the lift
`Kakeya.ML2Core.sourceNormalizedLift`.  `SourceAssignedAmbientComparison` states the radius and
profile error bounds along a level sample; `SourceAssignedAmbientDropReflection` is the extra
hypothesis under which a source drop of `2 hSrc` lowers the ambient `potential`
(`source_potential_drop_of_assigned_reflection`).  `SourceActualTrialState`,
`SourceUniversalRuntimeBridgeGoal`, `SourceFixedKTArrayGood` and
`SourceAssignedStickyRealizationGoal` name the remaining bridge obligations as `Prop`s; nothing
here proves them.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube

namespace Kakeya.ML2Core

universe u

open scoped Classical in
/-- Pull back one named normalized retained family through the actual canonical surjection. -/
noncomputable def sourceNormalizedLift {iota : Type u}
    (S : Finset iota) (pi : iota -> iota) (R : Finset iota) : Finset iota :=
  S.filter (fun i => pi i ∈ R)

section Comparison

variable {iota : Type u} {delta d Cu : ℝ≥0} {ambient sourceFamily : Finset iota}
  {T : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3))}
  {Y : iota -> Tube d (EuclideanSpace ℝ (Fin 3))} {M C : Nat}

/-- A required comparison for an actual finite level embedding and its paid errors.
Source logarithms use d, ambient logarithms use delta; neither denominator is replaced. -/
structure SourceAssignedAmbientComparison
    (U : UniformTubeSet ambient (fun i => (T i).toTube) (ssfGridLen delta) Cu)
    (Q : SourceThreadedTower sourceFamily Y M C) (S support : Finset iota) (pi : iota -> iota)
    (sample : Fin (M + 1) ↪o Fin (ssfGridLen delta + 1))
    (radiusError profileError : ℝ) : Prop where
  original_subset : S <= ambient
  source_subset : support <= sourceFamily
  radius_error_nonneg : 0 <= radiusError
  profile_error_nonneg : 0 <= profileError
  bottom_level : sample (Fin.last M) = Fin.last (ssfGridLen delta)
  radius_lower : ∀ k : Fin (M + 1),
    delta ^ radiusError * gridScale delta (ssfGridLen delta) (sample k) <= sourceTowerRadius d M k
  radius_upper : ∀ k : Fin (M + 1),
    sourceTowerRadius d M k <= delta ^ (-radiusError) * gridScale delta (ssfGridLen delta) (sample k)
  profile_lower : ∀ R : Finset iota, R <= support -> ∀ a b : Fin (M + 1), a < b ->
    profileExp delta (pairProfile U (sourceNormalizedLift S pi R) (sample a) (sample b)) <=
      Q.assignedProfileExp R a b + profileError
  profile_upper : ∀ R : Finset iota, R <= support -> ∀ a b : Fin (M + 1), a < b ->
    Q.assignedProfileExp R a b <=
      profileExp delta (pairProfile U (sourceNormalizedLift S pi R) (sample a) (sample b)) + profileError

end Comparison

/-- Full actual TrialSupplier/IsTrialAtGain input, without added source centring or ED. -/
structure SourceActualTrialState {iota : Type u} {delta Cu : ℝ≥0}
    {ambient : Finset iota} {T : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3))}
    (Cu0 : ℝ≥0) (etaIn : ℝ)
    (U : UniformTubeSet ambient (fun i => (T i).toTube) (ssfGridLen delta) Cu)
    (S : Finset iota) (Z : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3)))
    (lam : ℝ≥0) : Prop where
  uniform_constant : Cu <= Cu0
  subset : S <= ambient
  nonempty : S.Nonempty
  tubes : ∀ i, (Z i).toTube = (T i).toTube
  shades : ∀ i, (Z i).shade <= (T i).shade
  homogeneous : IsClassHomogeneousOn U S
  ball : ∀ i ∈ S, (Z i).carrier <= Metric.closedBall 0 1
  max_density : Kakeya.maxDensity S (fun i => (Z i).toConvexSpaceBody) <= (delta : ℝ≥0∞) ^ (-etaIn)
  dense : ML2Shaded.HasDenseShading lam S (fun i => (Z i).toShadedBody)
  comparable : ML2Shaded.HasComparableDensities lam⁻¹ S (fun i => (Z i).toShadedBody)
  lambda_floor : delta ^ etaIn / 2 <= lam
  ambient_card : (ambient.card : ℝ≥0) <= delta ^ (-(4 : ℝ))

/-- The exact finite source Katz--Tao array good alternative, S:2688-2692. -/
def SourceFixedKTArrayGood {iota : Type u} {d : ℝ≥0} {R : Finset iota}
    {Y : iota -> Tube d (EuclideanSpace ℝ (Fin 3))} {M C : Nat}
    (Q : SourceThreadedTower R Y M C) (B : ℝ≥0) (N : Nat) (e : ℝ) : Prop :=
  ∀ l : Nat, 1 <= l -> l <= M ->
    Q.assignedProfile R 0 l <= (B : ℝ≥0∞) ^ (N + 1) * (d : ℝ≥0∞) ^ (-(5 * e))

end Kakeya.ML2Core

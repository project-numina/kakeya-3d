/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.LiteralDetailedTrialW94

/-!
# Persistent retained states and paid drop transitions

Definitions, in `Kakeya.ml1Boot.TrialRestartW94`, for the restart layer of the revised source.
`FixedBaseReserveW94` fixes the base family `B`, `V` once (common carrier volume, unit ball,
fullness `lambda0`, Frostman bound `F0`).  `RetainedStateW94` is a current active subfamily with
subshadings and a cumulative `retained` coefficient.  `persistentProfileW94` evaluates the
literal profile coordinate of a state against the fixed base net `U0`; `actualPaidPassCostW94`
is the exact pass cost `Cpass * fullPassDenominatorW87 / trialRetainedFractionW94`.
`PaidDropTransitionW94` is the P4-P5 witness of one step (dagger family, prior trial retention,
selector retention, paid coefficient and a profile drop by `cFlat`), and `ActualDropTraceW94`
records a finite sequence of such steps.  Imports `LiteralDetailedTrialW94`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ConvexSpaceBody ShadedBody

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false

universe uE uI

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

open RevisedLiteralProfileInterfaceFormalizerW87

/-- The base is fixed once after the independently paid initial normalization. -/
structure FixedBaseReserveW94 {iota : Type uI} {delta : ℝ≥0}
    (B : Finset iota) (V : iota -> ShadedTube delta E) where
  nonempty : B.Nonempty
  delta_pos : 0 < delta
  delta_lt_one : delta < 1
  carrierVolume : ℝ≥0∞
  carrierVolume_pos : 0 < carrierVolume
  carrierVolume_finite : carrierVolume < ⊤
  common_volume : ∀ i ∈ B, volume (V i).carrier = carrierVolume
  ball : ∀ i ∈ B, (V i).carrier ⊆ Metric.closedBall 0 1
  lambda0 : ℝ≥0∞
  lambda0_pos : 0 < lambda0
  lambda0_finite : lambda0 < ⊤
  fullness : lambda0 <= fullness' B (fun i => (V i).toShadedBody)
  F0 : ℝ≥0∞
  F0_finite : F0 < ⊤
  frostman : frostmanConstIn B (fun i => (V i).toConvexSpaceBody)
    ConvexSpaceBody.closedUnitBall <= F0

/-- A real current family and its cumulative retained mass. There is no
fresh canonical net, arbitrary profile, or reset fullness exponent here. -/
structure RetainedStateW94 {iota : Type uI} {delta : ℝ≥0}
    (B : Finset iota) (V : iota -> ShadedTube delta E) where
  active : Finset iota
  shading : iota -> ShadedTube delta E
  active_nonempty : active.Nonempty
  active_subset : active ⊆ B
  same_tube : ∀ i ∈ active, (shading i).toTube = (V i).toTube
  subshade : ∀ i ∈ active, (shading i).shade ⊆ (V i).shade
  retained : ℝ≥0∞
  retained_pos : 0 < retained
  retained_finite : retained < ⊤
  mass_retention : retained * (∑ i ∈ B, volume (V i).shade) <=
    ∑ i ∈ active, volume (shading i).shade

/-- All states are evaluated against this same externally fixed base net. -/
def persistentProfileW94 {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}
    {B : Finset iota} {V : iota -> ShadedTube delta E} {M : Nat} {Ccan : ℝ≥0}
    (U0 : CanonicalProfileNetW87 B (fun i => (V i).toTube) M Ccan)
    (state : RetainedStateW94 B V) (q ell : Fin (M + 1)) : ℝ :=
  literalProfileCoordW87 U0 state.active q ell

/-- The exact integer-ceil selection cost is kept, and prior trial loss is
paid separately. Thus neither the factor-eight comparison nor Ydagger loss
is hidden in a real-valued three-Lambda denominator. -/
def actualPaidPassCostW94 (delta d : ℝ≥0) (M CM Ktr : Nat)
    (Cpass : ℝ≥0) : ℝ≥0∞ :=
  (Cpass : ℝ≥0∞) * fullPassDenominatorW87 delta M CM /
    trialRetainedFractionW94 d Ktr

/-- Output witness for P4-P5. Every payment is on the actual intermediate
fine family, and the decreasing coordinate uses the persistent base net. -/
structure PaidDropTransitionW94 {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}
    {B : Finset iota} {V : iota -> ShadedTube delta E} {M : Nat} {Ccan : ℝ≥0}
    (U0 : CanonicalProfileNetW87 B (fun i => (V i).toTube) M Ccan)
    (current next : RetainedStateW94 B V) (CM : Nat) (Cpass : ℝ≥0)
    (cFlat : ℝ) where
  trialScale : ℝ≥0
  trialScale_lower : delta <= trialScale
  trialScale_lt_one : trialScale < 1
  Ktr : Nat
  Ktr_pos : 1 <= Ktr
  daggerFamily : Finset iota
  Ydagger : iota -> ShadedTube delta E
  dagger_subset : daggerFamily ⊆ current.active
  dagger_same_tube : ∀ i ∈ daggerFamily, (Ydagger i).toTube = (current.shading i).toTube
  dagger_subshade : ∀ i ∈ daggerFamily, (Ydagger i).shade ⊆ (current.shading i).shade
  prior_trial_retention : trialRetainedFractionW94 trialScale Ktr *
    (∑ i ∈ current.active, volume (current.shading i).shade) <=
      ∑ i ∈ daggerFamily, volume (Ydagger i).shade
  next_subset : next.active ⊆ daggerFamily
  next_subshade : ∀ i ∈ next.active, (next.shading i).shade ⊆ (Ydagger i).shade
  selector_retention : ((Cpass : ℝ≥0∞) * fullPassDenominatorW87 delta M CM)⁻¹ *
    (∑ i ∈ daggerFamily, volume (Ydagger i).shade) <=
      ∑ i ∈ next.active, volume (next.shading i).shade
  coefficient_paid : current.retained /
    actualPaidPassCostW94 delta trialScale M CM Ktr Cpass <= next.retained
  drop_q : Fin (M + 1)
  drop_ell : Fin (M + 1)
  profile_drop : persistentProfileW94 U0 next drop_q drop_ell + cFlat <=
    persistentProfileW94 U0 current drop_q drop_ell

/-- A constructed trace may record these witnesses. No existence theorem
takes a supplied trace or universal pass callback as an outer input. -/
structure ActualDropTraceW94 {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}
    {B : Finset iota} {V : iota -> ShadedTube delta E} {M : Nat} {Ccan : ℝ≥0}
    (U0 : CanonicalProfileNetW87 B (fun i => (V i).toTube) M Ccan)
    (initial : RetainedStateW94 B V) (CM : Nat) (Cpass : ℝ≥0) (cFlat : ℝ) where
  length : Nat
  state : Fin (length + 1) -> RetainedStateW94 B V
  head : state 0 = initial
  step : ∀ n : Fin length,
    PaidDropTransitionW94 U0 (state (Fin.castSucc n)) (state (Fin.succ n)) CM Cpass cFlat

end

end Kakeya.ml1Boot.TrialRestartW94

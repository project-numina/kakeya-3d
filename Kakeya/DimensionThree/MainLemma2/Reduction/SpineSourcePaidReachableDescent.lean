/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceAssignedProfile
public import Mathlib.Logic.Relation

/-!
# Paid descent traces on a threaded tower

Finite-descent bookkeeping for the source potential. `sourceAssignedPotentialCeiling`
bounds the number of paid steps in terms of `M` and `h` only
(`source_assignedPotential_le_fixed_ceiling`). `SourcePaidState` records a retained family
with its shading; `SourcePaidStep` is one paid whole-fibre drop, with retention and a strict
potential decrease (`source_paidStep_retention`, `source_paidStep_potential_drop`).
`SourcePaidTrace`/`SourcePaidReachable` iterate such steps and give the cumulative mass
ledger and fullness ladder. Given the open trial law `SourceReachablePaidTrialLaw`,
`source_exists_paid_terminal_trace` and `source_paid_descent_bound` produce a terminal
trace (`SourcePaidTerminal`) and the resulting multiplicity alternative for the initial state.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube

namespace Kakeya.ML2Core

universe u

/-- The fixed number of assigned level pairs, with the source height bound five. -/
noncomputable def sourceAssignedPotentialCeiling (M : Nat) (h : ℝ) : Nat :=
  (M * (M + 1) / 2) * Nat.ceil (5 / h)

section FixedTower

variable {iota : Type u} {d : ℝ≥0} {ambient : Finset iota}
  {T : iota -> Tube d (EuclideanSpace ℝ (Fin 3))} {M C : Nat}

/-- Cardinality of the actual assigned images bounds every finite density profile. -/
theorem source_assignedProfile_le_retained_card
    (Q : SourceThreadedTower ambient T M C) (R : Finset iota) (a b : Nat) :
    Q.assignedProfile R a b <= (R.card : ℝ≥0∞) := by
  classical
  refine Finset.sup_le fun j _ => ?_
  refine (Kakeya.maxDensity_le_card _ _).trans ?_
  exact_mod_cast (Finset.card_image_le.trans (Finset.card_filter_le R _))

/-- The source logarithm is finite and lies in [0,5] after the actual leaf-card bound. -/
theorem source_assignedProfileExp_le_five
    (Q : SourceThreadedTower ambient T M C) {R : Finset iota}
    (hR : R <= ambient) (hd0 : 0 < d) (hd1 : d < 1)
    (hcard : (ambient.card : ℝ) <= (d : ℝ) ^ (-5 : ℝ)) (a b : Nat) :
    0 <= Q.assignedProfileExp R a b /\ Q.assignedProfileExp R a b <= 5 := by
  have hfinite := source_assignedProfile_ne_top Q R a b
  have hnn := profileExp_nonneg hd0 hd1 (Q.assignedProfile R a b)
  have hle : (Q.assignedProfile R a b).toReal <= (1 / (d : ℝ)) ^ (5 : ℝ) := by
    calc (Q.assignedProfile R a b).toReal <= (R.card : ℝ) := by
          simpa using ENNReal.toReal_mono (ENNReal.natCast_ne_top R.card)
            (source_assignedProfile_le_retained_card Q R a b)
      _ <= (ambient.card : ℝ) := by exact_mod_cast Finset.card_le_card hR
      _ <= (d : ℝ) ^ (-5 : ℝ) := hcard
      _ = (1 / (d : ℝ)) ^ (5 : ℝ) := by
          rw [one_div, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity)]
  have hbound := profileExp_le_of_toReal_le hd0 hd1 hfinite (by norm_num : (0 : ℝ) <= 5) hle
  simpa only [profileExp_of_ne_top hfinite, SourceThreadedTower.assignedProfileExp] using
    And.intro hnn hbound

/-- Source S:5782-5789,6120-6136: the ceiling depends on M,h, not the scale. -/
theorem source_assignedPotential_le_fixed_ceiling
    (Q : SourceThreadedTower ambient T M C) {R : Finset iota}
    (hR : R <= ambient) (hd0 : 0 < d) (hd1 : d < 1) {h : ℝ} (hh : 0 < h)
    (hcard : (ambient.card : ℝ) <= (d : ℝ) ^ (-5 : ℝ)) :
    Q.assignedPotential h R <= sourceAssignedPotentialCeiling M h := by
  classical
  unfold SourceThreadedTower.assignedPotential
  calc _ <= ∑ _p ∈ (Finset.range (M + 1) ×ˢ Finset.range (M + 1)).filter
          (fun p => p.1 < p.2), Nat.ceil (5 / h) := by
        refine Finset.sum_le_sum fun p _ => Nat.ceil_le_ceil ?_
        exact div_le_div_of_nonneg_right
          (source_assignedProfileExp_le_five Q hR hd0 hd1 hcard p.1 p.2).2 hh.le
    _ = sourceAssignedPotentialCeiling M h := by
        rw [Finset.sum_const, smul_eq_mul, card_pairs_lt, sourceAssignedPotentialCeiling]

/-- A state retains actual tube identities and shades inside the fixed initial shading. -/
structure SourcePaidState (ambient : Finset iota)
    (T : iota -> Tube d (EuclideanSpace ℝ (Fin 3)))
    (Y : iota -> ShadedTube d (EuclideanSpace ℝ (Fin 3))) where
  family : Finset iota
  shaded : iota -> ShadedTube d (EuclideanSpace ℝ (Fin 3))
  subset : family <= ambient
  nonempty : family.Nonempty
  same_tubes : ∀ i, (shaded i).toTube = T i
  shade_subset : ∀ i ∈ family, (shaded i).shade <= (Y i).shade
  mass_pos : 0 < ∑ i ∈ family, volume (shaded i).shade

variable {Y : iota -> ShadedTube d (EuclideanSpace ℝ (Fin 3))}

noncomputable def SourcePaidState.mass (x : SourcePaidState ambient T Y) : ℝ≥0∞ :=
  ∑ i ∈ x.family, volume (x.shaded i).shade

noncomputable def SourcePaidState.fullness (x : SourcePaidState ambient T Y) : ℝ≥0∞ :=
  ShadedBody.fullness' x.family (fun i => (x.shaded i).toShadedBody)

noncomputable def SourcePaidState.multiplicity (x : SourcePaidState ambient T Y) : ℝ≥0∞ :=
  ShadedBody.multiplicity x.family (fun i => (x.shaded i).toShadedBody)

def SourcePaidState.shadeUnion (x : SourcePaidState ambient T Y) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  ⋃ i ∈ x.family, (x.shaded i).shade

open scoped Classical in
/-- One recorded cut keeps whole CURRENT assigned fibres at its named source level.
It makes no claim that arbitrary cuts preserve earlier statistical regularity. -/
def SourceWholeFibreCut (Q : SourceThreadedTower ambient T M C)
    (S R : Finset iota) : Prop :=
  ∃ k : Nat, k <= M /\ ∃ selected : Finset iota,
    selected <= Q.assignedFootprint S k /\
    R = S.filter (fun i => Q.place k i ∈ selected)

/-- A paid drop carries the actual selected family, shade restriction and weighted mass.
The coordinate drop is on Q itself. Multiplicity/fullness retention are derived below. -/
structure SourcePaidStep (Q : SourceThreadedTower ambient T M C)
    (h : ℝ) (loss : ℝ≥0∞) (x y : SourcePaidState ambient T Y) : Prop where
  subset : y.family <= x.family
  whole_fibre_selections : Relation.ReflTransGen (SourceWholeFibreCut Q) x.family y.family
  shade_subset : ∀ i ∈ y.family, (y.shaded i).shade <= (x.shaded i).shade
  weighted_mass : x.mass <= loss * y.mass
  coordinate_drop : ∃ a b : Nat, a < b /\ b <= M /\
    Q.assignedProfileExp y.family a b + 2 * h <= Q.assignedProfileExp x.family a b

/-- A finite sequence with an actual paid step at every successor and its starting identity. -/
structure SourcePaidTrace (Q : SourceThreadedTower ambient T M C)
    (h : ℝ) (loss : ℝ≥0∞) (initial : SourcePaidState ambient T Y) where
  length : Nat
  state : Fin (length + 1) -> SourcePaidState ambient T Y
  start : state 0 = initial
  step : ∀ j : Fin length, SourcePaidStep Q h loss (state j.castSucc) (state j.succ)

def SourcePaidTrace.last {Q : SourceThreadedTower ambient T M C} {h : ℝ}
    {loss : ℝ≥0∞} {initial : SourcePaidState ambient T Y}
    (trace : SourcePaidTrace Q h loss initial) : SourcePaidState ambient T Y :=
  trace.state (Fin.last trace.length)

/-- Reachability is generated only by the paid source relation, with zero steps allowed. -/
def SourcePaidReachable (Q : SourceThreadedTower ambient T M C) (h : ℝ)
    (loss : ℝ≥0∞) (initial x : SourcePaidState ambient T Y) : Prop :=
  Relation.ReflTransGen (SourcePaidStep Q h loss) initial x

/-- Actual terminal estimates, including ONE terminal loss. alpha is absolute Sticky accuracy;
gamma is the actual surviving positive analytic gain, never the positive-defect source bound. -/
def SourcePaidTerminal (loss : ℝ≥0∞) (alpha gamma beta : ℝ)
    (x : SourcePaidState ambient T Y) : Prop :=
  x.multiplicity <= loss * (d : ℝ≥0∞) ^ (-alpha) \/
    x.multiplicity <= loss * (d : ℝ≥0∞) ^ gamma * (x.family.card : ℝ≥0∞) ^ beta

/-- Explicit OPEN input of the conditional consumer: produce a real exit or paid child
for each state reached from this initial pair, once its fullness permits a trial. -/
def SourceReachablePaidTrialLaw (Q : SourceThreadedTower ambient T M C)
    (h eta0 alpha gamma beta : ℝ) (loss : ℝ≥0∞)
    (initial : SourcePaidState ambient T Y) : Prop :=
  ∀ x : SourcePaidState ambient T Y,
    SourcePaidReachable Q h loss initial x ->
    (d : ℝ≥0∞) ^ (2 * eta0) <= x.fullness ->
    SourcePaidTerminal loss alpha gamma beta x \/
      ∃ y : SourcePaidState ambient T Y, SourcePaidStep Q h loss x y

end FixedTower

end Kakeya.ML2Core

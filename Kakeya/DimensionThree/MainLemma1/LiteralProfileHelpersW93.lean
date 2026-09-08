/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib
public import Kakeya.Uniform
public import Kakeya.ShadedUniform
public import Kakeya.DimensionThree.MainLemma1.Setup
public import Kakeya.DimensionThree.Plank.PlankFactorizationEstimate
public import Kakeya.FibreCommon
public import Kakeya.MultiScaleFac
public import Kakeya.DimensionThree.Plank.InnerEDAssembly

/-! ## Exact full-pass weighted mass and same-witness output -/

@[expose] public section

open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.RevisedInnerTrialRestartW74

def profilePotential (M : Nat) (p : Fin (M + 1) → Fin (M + 1) → ℝ) : ℝ :=
  ∑ a : Fin (M + 1), ∑ b : Fin (M + 1), p a b

structure ProfileStateW74 (M : Nat) where
  coord : Fin (M + 1) → Fin (M + 1) → ℝ
  coord_nonneg : ∀ a b, 0 ≤ coord a b
  coord_upper : ∀ a b, coord a b ≤ 7
  /-- The finite profile budget, recorded at construction time. -/
  potential_bound : profilePotential M coord ≤
    (7 : ℝ) * (((M + 1 : Nat) : ℝ) ^ 2)

end Kakeya.ml1Boot.RevisedInnerTrialRestartW74

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology Set
open scoped NNReal ENNReal BigOperators

namespace Kakeya.ml1Boot.RevisedLiteralProfileInterfaceFormalizerW87

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000

universe uE uI uP

variable {E : Type uE}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [ProperSpace E]
  [MeasurableSpace E] [BorelSpace E]

open Kakeya.ml1Boot.RevisedInnerTrialRestartW74

abbrev CanonicalProfileNetW87
    {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}
    (base : Finset iota) (T : iota -> Tube delta E)
    (M : Nat) (C : ℝ≥0) :=
  Tube.UniformTubeSet base T M C

noncomputable def canonicalAncestorFamilyW87
    {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}
    {base : Finset iota} {T : iota -> Tube delta E}
    {M : Nat} {C : ℝ≥0} (U : CanonicalProfileNetW87 base T M C)
    (F : Finset iota) (q : Fin (M + 1)) : Finset iota :=
  F.image (U.cover.assign q.val)

/-- A level-`q` canonical node, distinguished in the type from a fine leaf. -/
abbrev CanonicalQNodeW87
    {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}
    {base : Finset iota} {T : iota -> Tube delta E}
    {M : Nat} {C : ℝ≥0} (U : CanonicalProfileNetW87 base T M C)
    (current : Finset iota) (q : Fin (M + 1)) :=
  {w : iota // w ∈ canonicalAncestorFamilyW87 U current q}

/-- The complete finite type of canonical `q`-nodes realized by `current`. -/
noncomputable def canonicalQNodeFinsetW87
    {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}
    {base : Finset iota} {T : iota -> Tube delta E}
    {M : Nat} {C : ℝ≥0} (U : CanonicalProfileNetW87 base T M C)
    (current : Finset iota) (q : Fin (M + 1)) :
    Finset (CanonicalQNodeW87 U current q) :=
  (canonicalAncestorFamilyW87 U current q).attach

/-- Forget the node subtype only at the legal bridge back to hierarchy labels. -/
noncomputable def canonicalQNodeValuesW87
    {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}
    {base current : Finset iota} {T : iota -> Tube delta E}
    {M : Nat} {C : ℝ≥0} {U : CanonicalProfileNetW87 base T M C}
    {q : Fin (M + 1)}
    (nodes : Finset (CanonicalQNodeW87 U current q)) : Finset iota :=
  nodes.image Subtype.val

noncomputable def saturatedFineLiftW87
    {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}
    {base : Finset iota} {T : iota -> Tube delta E}
    {M : Nat} {C : ℝ≥0} (U : CanonicalProfileNetW87 base T M C)
    (current : Finset iota) (q : Fin (M + 1))
    (keptNodes : Finset iota) : Finset iota :=
  current.filter fun i => U.cover.assign q.val i ∈ keptNodes

theorem exists_heaviestFiber_ennreal_w87
    {alpha nu : Type*} [Fintype nu] [DecidableEq nu] [Nonempty nu]
    (A : Finset alpha) (weight : alpha -> ℝ≥0∞)
    (label : alpha -> nu) (_hpos : 0 < ∑ a ∈ A, weight a) :
    exists v : nu,
      (∑ a ∈ A, weight a) <=
        (Fintype.card nu : ℝ≥0∞) *
          (∑ a ∈ A.filter (fun a => label a = v), weight a) := by
  classical
  obtain ⟨v, _, hv⟩ := Finset.exists_max_image Finset.univ
    (fun v : nu => ∑ a ∈ A.filter (fun a => label a = v), weight a)
    Finset.univ_nonempty
  refine ⟨v, ?_⟩
  calc
    (∑ a ∈ A, weight a) =
        ∑ v : nu, ∑ a ∈ A.filter (fun a => label a = v), weight a :=
      (Finset.sum_fiberwise A label weight).symm
    _ <= ∑ _v : nu, ∑ a ∈ A.filter (fun a => label a = v), weight a := by
      exact Finset.sum_le_sum hv
    _ = _ := by simp [nsmul_eq_mul]

noncomputable def sourceLambdaMNatW87 (delta : ℝ≥0) (CM : Nat) : Nat :=
  Nat.ceil ((2 + Real.log (1 / (delta : ℝ)) / Real.log 2) ^ CM)

noncomputable def sourceLambdaINatW87 (delta : ℝ≥0) (CM : Nat) : Nat :=
  Nat.ceil ((2 + Real.log (1 / (delta : ℝ)) / Real.log 2) ^ CM)

noncomputable def sourceLambdaBalNatW87 (delta : ℝ≥0) (CM : Nat) : Nat :=
  Nat.ceil ((2 + Real.log (1 / (delta : ℝ)) / Real.log 2) ^ CM)

noncomputable def fullPassDenominatorW87
    (delta : ℝ≥0) (M CM : Nat) : ℝ≥0∞ :=
  4 * ((M + 1 : Nat) : ℝ≥0∞) * (sourceLambdaMNatW87 delta CM : ℝ≥0∞) *
    (sourceLambdaINatW87 delta CM : ℝ≥0∞) *
      (sourceLambdaBalNatW87 delta CM : ℝ≥0∞)

structure FullPassSelectionInputW87
    {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}
    {base : Finset iota} {T : iota -> ShadedTube delta E}
    {M CM : Nat} {C : ℝ≥0} (current : Finset iota)
    (U : CanonicalProfileNetW87 base
      (fun i => (T i).toTube) M C)
    (q : Fin (M + 1)) where
  current_subset : current <= base
  current_nonempty : current.Nonempty
  Ydagger : iota -> ShadedTube delta E
  same_tube : ∀ i ∈ current,
    (Ydagger i).toTube = (T i).toTube
  subshading : ∀ i ∈ current, (Ydagger i).shade <= (T i).shade
  current_mass_pos : 0 < ∑ i ∈ current, volume (Ydagger i).shade
  branchBucket : CanonicalQNodeW87 U current q -> Fin 4
  scaleBucket : CanonicalQNodeW87 U current q -> Fin (M + 1)
  towerBucket : CanonicalQNodeW87 U current q ->
    Fin (sourceLambdaMNatW87 delta CM)
  innerBucket : CanonicalQNodeW87 U current q ->
    Fin (sourceLambdaINatW87 delta CM)
  balancedBucket : CanonicalQNodeW87 U current q ->
    Fin (sourceLambdaBalNatW87 delta CM)
  Ktr : Nat
  Ktr_pos : 0 < Ktr
  Ktr_le_CM : Ktr <= CM

noncomputable def exactTubeCellW87
    {iota : Type uI} [DecidableEq iota] {r s : ℝ≥0}
    (F : Finset iota) (W : iota -> Tube r E) (R : Tube s E) : Finset iota := by
  classical
  exact F.filter fun i =>
    (W i).toConvexSpaceBody <= R.toConvexSpaceBody

/--
The finite quotient of all nonempty exact `s`-tube cells.  The existential
still ranges over every `Tube s E`; `F.powerset` only deduplicates exact tubes
which realize the same finite cell.
-/
noncomputable def realizedExactTubeCellsW87
    {iota : Type uI} [DecidableEq iota] {r : ℝ≥0}
    (F : Finset iota) (W : iota -> Tube r E) (s : ℝ≥0) :
    Finset (Finset iota) := by
  classical
  exact F.powerset.filter fun A =>
    A.Nonempty /\ exists R : Tube s E, A = exactTubeCellW87 F W R

/--
The source quantity `N_s(F)`: the maximum `Delta_max` over all nonempty cells
realized by exact `s`-tubes.  It is a finite supremum because a finite family
has only finitely many distinct cells.
-/
noncomputable def allExactTubeNsW87
    {iota : Type uI} [DecidableEq iota] {r : ℝ≥0}
    (F : Finset iota) (W : iota -> Tube r E) (s : ℝ≥0) : ℝ≥0∞ :=
  (realizedExactTubeCellsW87 F W s).sup fun A =>
    Kakeya.maxDensity A (fun i => (W i).toConvexSpaceBody)

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem exactTubeCell_subset_w87
    {iota : Type uI} [DecidableEq iota] {r s : ℝ≥0}
    (F : Finset iota) (W : iota -> Tube r E) (R : Tube s E) :
    exactTubeCellW87 F W R <= F := by
  intro i hi
  exact (Finset.mem_filter.mp hi).1

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem exactTubeCell_mono_family_w87
    {iota : Type uI} [DecidableEq iota] {r s : ℝ≥0}
    {F F' : Finset iota} (hsub : F' <= F)
    (W : iota -> Tube r E) (R : Tube s E) :
    exactTubeCellW87 F' W R <= exactTubeCellW87 F W R := by
  intro i hi
  exact Finset.mem_filter.mpr
    ⟨hsub (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩

theorem mem_realizedExactTubeCells_w87
    {iota : Type uI} [DecidableEq iota] {r : ℝ≥0}
    {F : Finset iota} {W : iota -> Tube r E} {s : ℝ≥0}
    {A : Finset iota} :
    A ∈ realizedExactTubeCellsW87 F W s <->
      A.Nonempty /\ exists R : Tube s E, A = exactTubeCellW87 F W R := by
  classical
  constructor
  · intro hA
    exact (Finset.mem_filter.mp hA).2
  · intro hA
    refine Finset.mem_filter.mpr ⟨?_, hA⟩
    rcases hA.2 with ⟨R, rfl⟩
    exact Finset.mem_powerset.mpr (exactTubeCell_subset_w87 F W R)

theorem realized_cell_of_exact_w87
    {iota : Type uI} [DecidableEq iota] {r s : ℝ≥0}
    {F : Finset iota} {W : iota -> Tube r E} (R : Tube s E)
    (hne : (exactTubeCellW87 F W R).Nonempty) :
    exactTubeCellW87 F W R ∈ realizedExactTubeCellsW87 F W s := by
  exact mem_realizedExactTubeCells_w87.mpr ⟨hne, R, rfl⟩

theorem maxDensity_exactTubeCell_le_allExactTubeNs_w87
    {iota : Type uI} [DecidableEq iota] {r s : ℝ≥0}
    {F : Finset iota} {W : iota -> Tube r E} (R : Tube s E)
    (hne : (exactTubeCellW87 F W R).Nonempty) :
    Kakeya.maxDensity (exactTubeCellW87 F W R)
        (fun i => (W i).toConvexSpaceBody) <=
      allExactTubeNsW87 F W s := by
  unfold allExactTubeNsW87
  exact Finset.le_sup
    (f := fun A : Finset iota =>
      Kakeya.maxDensity A (fun i => (W i).toConvexSpaceBody))
    (realized_cell_of_exact_w87 R hne)

theorem allExactTubeNs_le_w87
    {iota : Type uI} [DecidableEq iota] {r s : ℝ≥0}
    {F : Finset iota} {W : iota -> Tube r E} {A : ℝ≥0∞}
    (hbound : forall R : Tube s E,
      (exactTubeCellW87 F W R).Nonempty ->
      Kakeya.maxDensity (exactTubeCellW87 F W R)
          (fun i => (W i).toConvexSpaceBody) <= A) :
    allExactTubeNsW87 F W s <= A := by
  apply Finset.sup_le
  intro cell hcell
  rcases mem_realizedExactTubeCells_w87.mp hcell with ⟨hne, R, rfl⟩
  exact hbound R hne

theorem allExactTubeNs_ne_top_w87
    {iota : Type uI} [DecidableEq iota] {r : ℝ≥0}
    (F : Finset iota) (W : iota -> Tube r E) (s : ℝ≥0) :
    allExactTubeNsW87 F W s ≠ ⊤ := by
  apply ne_top_of_le_ne_top
    (Kakeya.maxDensity_ne_top F (fun i => (W i).toConvexSpaceBody))
  apply allExactTubeNs_le_w87
  intro R _hne
  exact Kakeya.maxDensity_mono _ (exactTubeCell_subset_w87 F W R)

theorem allExactTubeNs_mono_w87
    {iota : Type uI} [DecidableEq iota] {r s : ℝ≥0}
    {F F' : Finset iota} (hsub : F' <= F) (W : iota -> Tube r E) :
    allExactTubeNsW87 F' W s <= allExactTubeNsW87 F W s := by
  apply allExactTubeNs_le_w87
  intro R hne
  have hcell : exactTubeCellW87 F' W R <= exactTubeCellW87 F W R :=
    exactTubeCell_mono_family_w87 hsub W R
  have hne' : (exactTubeCellW87 F W R).Nonempty := hne.mono hcell
  exact (Kakeya.maxDensity_mono _ hcell).trans
    (maxDensity_exactTubeCell_le_allExactTubeNs_w87 R hne')

theorem one_le_allExactTubeNs_of_nonempty_w87
    {iota : Type uI} [DecidableEq iota] {r s : ℝ≥0}
    {F : Finset iota} (W : iota -> Tube r E)
    (hF : F.Nonempty) (hr : 0 < r) (hr1 : r <= 1) (hrs : r <= s) :
    1 <= allExactTubeNsW87 F W s := by
  rcases hF with ⟨i, hi⟩
  let R : Tube s E := (W i).rescale s
  have hiCell : i ∈ exactTubeCellW87 F W R := by
    exact Finset.mem_filter.mpr ⟨hi, Tube.le_rescale (W i) hrs⟩
  have hcell : (exactTubeCellW87 F W R).Nonempty := ⟨i, hiCell⟩
  have hvol : 0 < volume (W i).toConvexSpaceBody.carrier :=
    (Tube.volume_pos_and_lt_top hr hr1 (W i)).1
  exact (Kakeya.one_le_maxDensity ⟨i, hiCell, hvol⟩).trans
    (maxDensity_exactTubeCell_le_allExactTubeNs_w87 R hcell)

theorem max_one_toReal_allExactTubeNs_eq_w87
    {iota : Type uI} [DecidableEq iota] {r s : ℝ≥0}
    {F : Finset iota} {W : iota -> Tube r E}
    (h1 : 1 <= allExactTubeNsW87 F W s) :
    max 1 (allExactTubeNsW87 F W s).toReal =
      (allExactTubeNsW87 F W s).toReal := by
  apply max_eq_right
  simpa only [ENNReal.toReal_one] using
    ENNReal.toReal_mono (allExactTubeNs_ne_top_w87 F W s) h1

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem canonicalAncestorFamily_mono_w87
    {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}
    {base F F' : Finset iota} {T : iota -> Tube delta E}
    {M : Nat} {C : ℝ≥0} (U : CanonicalProfileNetW87 base T M C)
    (hsub : F' <= F) (q : Fin (M + 1)) :
    canonicalAncestorFamilyW87 U F' q <=
      canonicalAncestorFamilyW87 U F q := by
  exact Finset.image_subset_image hsub

noncomputable def literalCanonicalDW87
    {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}
    {base : Finset iota} {T : iota -> Tube delta E}
    {M : Nat} {C : ℝ≥0} (U : CanonicalProfileNetW87 base T M C)
    (F : Finset iota) (q ell : Fin (M + 1)) : ℝ≥0∞ :=
  allExactTubeNsW87 (canonicalAncestorFamilyW87 U F q)
    (fun w => U.cover.tube q.val w) (Tube.gridScale delta M ell.val)

noncomputable def literalProfileCoordW87
    {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}
    {base : Finset iota} {T : iota -> Tube delta E}
    {M : Nat} {C : ℝ≥0} (U : CanonicalProfileNetW87 base T M C)
    (F : Finset iota) (q ell : Fin (M + 1)) : ℝ :=
  Real.log (max 1 (literalCanonicalDW87 U F q ell).toReal) /
    Real.log ((delta : ℝ) ^ (-1 : ℝ))

theorem literalCanonicalD_mono_w87
    {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}
    {base F F' : Finset iota} {T : iota -> Tube delta E}
    {M : Nat} {C : ℝ≥0} (U : CanonicalProfileNetW87 base T M C)
    (hsub : F' <= F) (q ell : Fin (M + 1)) :
    literalCanonicalDW87 U F' q ell <= literalCanonicalDW87 U F q ell := by
  exact allExactTubeNs_mono_w87 (canonicalAncestorFamily_mono_w87 U hsub q) _

theorem literalProfileCoord_mono_w87
    {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}
    {base F F' : Finset iota} {T : iota -> Tube delta E}
    {M : Nat} {C : ℝ≥0} (U : CanonicalProfileNetW87 base T M C)
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (hsub : F' <= F) (q ell : Fin (M + 1)) :
    literalProfileCoordW87 U F' q ell <=
      literalProfileCoordW87 U F q ell := by
  unfold literalProfileCoordW87
  apply div_le_div_of_nonneg_right _ (by
    apply Real.log_nonneg
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hdelta hdelta1.le (by norm_num))
  apply Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  apply max_le_max_left
  exact ENNReal.toReal_mono (allExactTubeNs_ne_top_w87 _ _ _)
    (literalCanonicalD_mono_w87 U hsub q ell)

omit [Nontrivial E] in
theorem literalProfileCoord_nonneg_w87
    {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}
    {base F : Finset iota} {T : iota -> Tube delta E}
    {M : Nat} {C : ℝ≥0} (U : CanonicalProfileNetW87 base T M C)
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (q ell : Fin (M + 1)) :
    0 <= literalProfileCoordW87 U F q ell := by
  unfold literalProfileCoordW87
  apply div_nonneg (Real.log_nonneg (le_max_left _ _))
  apply Real.log_nonneg
  exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hdelta hdelta1.le (by norm_num)

theorem literalProfileCoord_le_seven_w87
    {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}
    {base F : Finset iota} {T : iota -> Tube delta E}
    {M : Nat} {C : ℝ≥0} (U : CanonicalProfileNetW87 base T M C)
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (hF : F <= base)
    (hcard7 : (base.card : ℝ) <= (delta : ℝ) ^ (-7 : ℝ))
    (q ell : Fin (M + 1)) :
    literalProfileCoordW87 U F q ell <= 7 := by
  have hdeltaR : 0 < (delta : ℝ) := hdelta
  have hdeltaR1 : (delta : ℝ) < 1 := hdelta1
  have hDcard : literalCanonicalDW87 U F q ell <= (base.card : ℝ≥0∞) := by
    apply allExactTubeNs_le_w87
    intro R _
    calc
      _ <= ((exactTubeCellW87 (canonicalAncestorFamilyW87 U F q)
        (fun w => U.cover.tube q.val w) R).card : ℝ≥0∞) :=
          Kakeya.maxDensity_le_card _ _
      _ <= ((canonicalAncestorFamilyW87 U F q).card : ℝ≥0∞) := by
        exact_mod_cast Finset.card_le_card (exactTubeCell_subset_w87 _ _ R)
      _ <= (F.card : ℝ≥0∞) := by
        exact_mod_cast Finset.card_image_le
      _ <= (base.card : ℝ≥0∞) := by
        exact_mod_cast Finset.card_le_card hF
  have hreal : (literalCanonicalDW87 U F q ell).toReal <= (base.card : ℝ) := by
    simpa only [ENNReal.toReal_natCast] using
      ENNReal.toReal_mono (ENNReal.natCast_ne_top _) hDcard
  have hmax : max 1 (literalCanonicalDW87 U F q ell).toReal <=
      (delta : ℝ) ^ (-7 : ℝ) :=
    max_le (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hdeltaR hdeltaR1.le
      (by norm_num)) (hreal.trans hcard7)
  have hlog : 0 < Real.log ((delta : ℝ) ^ (-1 : ℝ)) :=
    Real.log_pos (Real.one_lt_rpow_of_pos_of_lt_one_of_neg hdeltaR hdeltaR1
      (by norm_num))
  unfold literalProfileCoordW87
  apply (div_le_iff₀ hlog).mpr
  calc
    _ <= Real.log ((delta : ℝ) ^ (-7 : ℝ)) :=
      Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hmax
    _ = _ := by rw [Real.log_rpow hdeltaR, Real.log_rpow hdeltaR]; ring

/-- A profile state whose coordinates are exactly the literal source profile. -/
structure LiteralProfileStateWitnessW87
    {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}
    {base : Finset iota} {T : iota -> Tube delta E}
    {M : Nat} {C : ℝ≥0} (U : CanonicalProfileNetW87 base T M C)
    (F : Finset iota) where
  state : ProfileStateW74 M
  coord_eq : forall q ell,
    state.coord q ell = literalProfileCoordW87 U F q ell

/-- Parameters selected before the running scale and tied to `Params`. -/
structure RevisedProfileParametersW87 (p : Params) where
  M : Nat
  CM : Nat
  canonicalC : ℝ≥0
  M_pos : 0 < M
  CM_pos : 0 < CM
  canonicalC_one : 1 <= canonicalC
  epsilon_pos : 0 < p.ε
  zeta0_pos : 0 < p.η 0
  zeta_mono : Monotone p.η
  reciprocal_M_small :
    (1 : ℝ) / (M : ℝ) <= p.ε ^ 2 * p.η 0 / 192

/-- The exact fixed comparison constant: G7 times the canonical overlap. -/
noncomputable def sourceCgeomW87
    {p : Params} (P : RevisedProfileParametersW87 p) : ℝ :=
  2 * 25 ^ (6 : Nat) * 4 ^ (6 : Nat) * (P.canonicalC : ℝ)

noncomputable def sourceCFlatW87 (p : Params) : ℝ :=
  p.ε ^ 2 * p.η 0 / 32

noncomputable def canonicalComparisonFactorW87
    {p : Params} (P : RevisedProfileParametersW87 p)
    (delta d : ℝ≥0) (zetaJ : ℝ) : ℝ :=
  sourceCgeomW87 P * (delta : ℝ) ^ (-6 / (P.M : ℝ)) *
    (d : ℝ) ^ (p.ε * zetaJ / 8)

theorem exists_deltaProfileAbsorb_w87
    {p : Params} (P : RevisedProfileParametersW87 p) :
    exists delta0 : ℝ≥0, 0 < delta0 /\ delta0 < 1 /\
      forall delta : ℝ≥0, 0 < delta -> delta <= delta0 ->
      forall d : ℝ≥0, forall zetaJ : ℝ,
        0 < d -> d <= 1 ->
        (d : ℝ) <= (delta : ℝ) ^ p.ε ->
        p.η 0 <= zetaJ ->
        canonicalComparisonFactorW87 P delta d zetaJ <=
          (delta : ℝ) ^ sourceCFlatW87 p := by
  have hflat : 0 < sourceCFlatW87 p := by
    unfold sourceCFlatW87
    exact div_pos (mul_pos (sq_pos_of_pos P.epsilon_pos) P.zeta0_pos) (by norm_num)
  have hgeom : 1 <= sourceCgeomW87 P := by
    have hC : (1 : ℝ) <= P.canonicalC := P.canonicalC_one
    unfold sourceCgeomW87
    nlinarith
  let K : ℝ≥0 := ⟨sourceCgeomW87 P, le_trans zero_le_one hgeom⟩
  obtain ⟨delta1, hdelta1pos, hconstant⟩ :=
    Kakeya.exists_threshold_le_rpow_neg K hgeom hflat
  refine ⟨min delta1 (1 / 2), lt_min hdelta1pos (by norm_num),
    lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
  intro delta hdelta hsmall d zetaJ hd hd1 hdscale hzeta
  have hdeltaR : 0 < (delta : ℝ) := hdelta
  have hdeltaR1 : (delta : ℝ) <= 1 := by
    have hhalf : delta <= 1 / 2 := hsmall.trans (min_le_right _ _)
    exact_mod_cast le_trans hhalf (by norm_num : (1 / 2 : ℝ≥0) <= 1)
  have hconstantR : sourceCgeomW87 P <=
      (delta : ℝ) ^ (-sourceCFlatW87 p) := by
    exact_mod_cast hconstant delta hdelta (hsmall.trans (min_le_left _ _))
  have he0 : 0 <= p.ε * p.η 0 / 8 :=
    div_nonneg (mul_nonneg P.epsilon_pos.le P.zeta0_pos.le) (by norm_num)
  have he : p.ε * p.η 0 / 8 <= p.ε * zetaJ / 8 := by
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hzeta
      P.epsilon_pos.le) (by norm_num)
  have hdpow : (d : ℝ) ^ (p.ε * zetaJ / 8) <=
      (delta : ℝ) ^ (p.ε ^ 2 * p.η 0 / 8) := by
    calc
      _ <= (d : ℝ) ^ (p.ε * p.η 0 / 8) :=
        Real.rpow_le_rpow_of_exponent_ge hd hd1 he
      _ <= ((delta : ℝ) ^ p.ε) ^ (p.ε * p.η 0 / 8) :=
        Real.rpow_le_rpow hd.le hdscale he0
      _ = _ := by rw [← Real.rpow_mul delta.coe_nonneg]; congr 1; ring
  have hloss : 6 / (P.M : ℝ) <= sourceCFlatW87 p := by
    have hM := P.reciprocal_M_small
    unfold sourceCFlatW87
    calc
      6 / (P.M : ℝ) = 6 * (1 / (P.M : ℝ)) := by ring
      _ <= 6 * (p.ε ^ 2 * p.η 0 / 192) := mul_le_mul_of_nonneg_left hM (by norm_num)
      _ = _ := by ring
  unfold canonicalComparisonFactorW87
  calc
    _ <= (delta : ℝ) ^ (-sourceCFlatW87 p) *
        (delta : ℝ) ^ (-6 / (P.M : ℝ)) *
          (delta : ℝ) ^ (p.ε ^ 2 * p.η 0 / 8) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right hconstantR (Real.rpow_nonneg delta.coe_nonneg _)
      · exact hdpow
      · exact Real.rpow_nonneg d.coe_nonneg _
      · positivity
    _ = (delta : ℝ) ^
        (-sourceCFlatW87 p + (-6 / (P.M : ℝ)) + p.ε ^ 2 * p.η 0 / 8) := by
      rw [← Real.rpow_add hdeltaR, ← Real.rpow_add hdeltaR]
    _ <= _ := by
      apply Real.rpow_le_rpow_of_exponent_ge hdeltaR hdeltaR1
      dsimp [sourceCFlatW87] at hloss hflat ⊢
      rw [neg_div]
      linarith

theorem max_one_literalCanonicalD_drop_w87
    {iota : Type uI} [DecidableEq iota]
    {delta : ℝ≥0} {base current next : Finset iota}
    {T : iota -> Tube delta E} {M : Nat} {C : ℝ≥0}
    (U : CanonicalProfileNetW87 base T M C)
    (q ell : Fin (M + 1)) (cFlat : ℝ)
    (hbefore1 : 1 <= literalCanonicalDW87 U current q ell)
    (hafter1 : 1 <= literalCanonicalDW87 U next q ell)
    (hraw : literalCanonicalDW87 U next q ell <=
      ENNReal.ofReal ((delta : ℝ) ^ cFlat) *
        literalCanonicalDW87 U current q ell) :
    max 1 (literalCanonicalDW87 U next q ell).toReal <=
      (delta : ℝ) ^ cFlat *
        max 1 (literalCanonicalDW87 U current q ell).toReal := by
  unfold literalCanonicalDW87 at hbefore1 hafter1 hraw ⊢
  rw [max_one_toReal_allExactTubeNs_eq_w87 hbefore1,
    max_one_toReal_allExactTubeNs_eq_w87 hafter1]
  have hfinite : ENNReal.ofReal ((delta : ℝ) ^ cFlat) *
      literalCanonicalDW87 U current q ell ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (allExactTubeNs_ne_top_w87 _ _ _)
  have hreal := ENNReal.toReal_mono hfinite hraw
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg delta.coe_nonneg _),
    literalCanonicalDW87]
    using hreal

theorem allExactTubeNs_coarse_le_fine_w87
    {iota : Type uI} [DecidableEq iota]
    {r sFine sCoarse : ℝ≥0} (F : Finset iota)
    (W : iota -> Tube r E)
    (hdim : Module.finrank ℝ E = 3)
    (hr : 0 < r) (hmember : 2 * r <= sFine)
    (hsc : sFine <= sCoarse) :
    allExactTubeNsW87 F W sCoarse <=
      ENNReal.ofReal
        (2 * 25 ^ (6 : Nat) *
          (4 * (sCoarse : ℝ) / (sFine : ℝ)) ^ (6 : Nat)) *
        allExactTubeNsW87 F W sFine := by
  classical
  have hrf : r <= sFine := (by nlinarith : r <= 2 * r).trans hmember
  have hf : 0 < sFine := hr.trans_le hrf
  apply allExactTubeNs_le_w87
  intro R hne
  obtain ⟨i0, hi0⟩ := hne
  have hR : R.toConvexSpaceBody <=
      ((W i0).rescale (4 * sCoarse)).toConvexSpaceBody :=
    Tube.rescale_le_of_le (W i0) R (Finset.mem_filter.mp hi0).2
  obtain ⟨A, hAF, hcard, hcover⟩ :=
    Kakeya.MultiScaleFac.exists_gapFibre_cover_of_ratio
      (s := F) (T := W) (δ := r) (σ := r)
      (ρ := sFine) (ρ' := 4 * sCoarse) hf le_rfl hmember
      (hsc.trans (by nlinarith)) i0
  have hsub : exactTubeCellW87 F W R <=
      A.biUnion (fun a => exactTubeCellW87 F W ((W a).rescale sFine)) := by
    intro i hi
    have hi' := Finset.mem_filter.mp hi
    have hiFibre : i ∈ Kakeya.StickyKakeya.fibreIndex F W r (4 * sCoarse) i0 := by
      rw [Kakeya.StickyKakeya.fibreIndex_self]
      exact Finset.mem_filter.mpr ⟨hi'.1, hi'.2.trans hR⟩
    obtain ⟨a, ha, hia⟩ := hcover i hiFibre
    apply Finset.mem_biUnion.mpr
    refine ⟨a, ha, ?_⟩
    simpa only [Kakeya.StickyKakeya.fibreIndex_self, exactTubeCellW87] using hia
  have hterm : ∀ a ∈ A,
      Kakeya.maxDensity (exactTubeCellW87 F W ((W a).rescale sFine))
        (fun i => (W i).toConvexSpaceBody) <= allExactTubeNsW87 F W sFine := by
    intro a ha
    apply maxDensity_exactTubeCell_le_allExactTubeNs_w87
    exact ⟨a, Finset.mem_filter.mpr ⟨hAF ha, Tube.le_rescale (W a) hrf⟩⟩
  have hcardE : (A.card : ℝ≥0∞) <=
      ENNReal.ofReal (2 * 25 ^ (6 : Nat) *
        (4 * (sCoarse : ℝ) / (sFine : ℝ)) ^ (6 : Nat)) := by
    have hcardR : (A.card : ℝ) <= 2 * 25 ^ (6 : Nat) *
        (4 * (sCoarse : ℝ) / (sFine : ℝ)) ^ (6 : Nat) := by
      simpa only [hdim, NNReal.coe_mul, NNReal.coe_ofNat] using hcard
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hcardR
  calc
    Kakeya.maxDensity (exactTubeCellW87 F W R) (fun i => (W i).toConvexSpaceBody)
        <= ∑ a ∈ A, Kakeya.maxDensity (exactTubeCellW87 F W ((W a).rescale sFine))
          (fun i => (W i).toConvexSpaceBody) :=
      Kakeya.maxDensity_le_sum_of_subset_biUnion _ hsub
    _ <= ∑ _a ∈ A, allExactTubeNsW87 F W sFine := Finset.sum_le_sum hterm
    _ = (A.card : ℝ≥0∞) * allExactTubeNsW87 F W sFine := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ <= _ := mul_le_mul_left hcardE _

noncomputable def blockThetaW87
    {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}
    {sPrime : Finset iota} {T : iota -> ShadedTube delta E}
    {Cds : ℝ≥0} (_U : Tube.UniformTubeSet sPrime
      (fun i => (T i).toTube) (Tube.ssfGridLen delta) Cds)
    (a : Nat) : ℝ≥0 :=
  Tube.gridScale delta (Tube.ssfGridLen delta) a

noncomputable def blockTauW87
    {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}
    {sPrime : Finset iota} {T : iota -> ShadedTube delta E}
    {Cds : ℝ≥0} (_U : Tube.UniformTubeSet sPrime
      (fun i => (T i).toTube) (Tube.ssfGridLen delta) Cds)
    (b : Nat) : ℝ≥0 :=
  Tube.gridScale delta (Tube.ssfGridLen delta) b

noncomputable def blockRatioW87
    {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}
    {sPrime : Finset iota} {T : iota -> ShadedTube delta E}
    {Cds : ℝ≥0} (U : Tube.UniformTubeSet sPrime
      (fun i => (T i).toTube) (Tube.ssfGridLen delta) Cds)
    (a b : Nat) : ℝ≥0 :=
  blockTauW87 U b / blockThetaW87 U a

structure CanonicalDropCoordinateW87
    {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}
    {sPrime : Finset iota} {T : iota -> ShadedTube delta E}
    {Cds : ℝ≥0} (U : Tube.UniformTubeSet sPrime
      (fun i => (T i).toTube) (Tube.ssfGridLen delta) Cds)
    {p : Params} (P : RevisedProfileParametersW87 p)
    (a b m : Nat) (working : ℝ≥0) where
  q : Fin (P.M + 1)
  ell : Fin (P.M + 1)
  ell_pos : 0 < ell.val
  ellPred : Fin (P.M + 1)
  ellPred_eq : ellPred.val = ell.val - 1
  ell_le_q : ell <= q
  label : Fin p.N
  label_eq_block : label.val = m
  theta_eq : blockThetaW87 U a =
    Tube.gridScale delta (Tube.ssfGridLen delta) a
  tau_eq : blockTauW87 U b =
    Tube.gridScale delta (Tube.ssfGridLen delta) b
  ratio_eq : blockRatioW87 U a b = blockTauW87 U b / blockThetaW87 U a
  ratio_pos : 0 < blockRatioW87 U a b
  ratio_le_one : blockRatioW87 U a b <= 1
  ratio_le_delta_epsilon :
    (blockRatioW87 U a b : ℝ) <= (delta : ℝ) ^ p.ε
  q_round : Tube.gridScale delta P.M q.val <= blockTauW87 U b
  q_round_pred : q.val = 0 \/
    blockTauW87 U b < Tube.gridScale delta P.M (q.val - 1)
  ell_round : Tube.gridScale delta P.M ell.val <= working
  ell_round_pred : working < Tube.gridScale delta P.M ellPred.val

theorem allExactTubeNs_le_of_assignedCover_w87
    {iota : Type uI} [DecidableEq iota] {pi : Type uP}
    [DecidableEq pi] {r s : ℝ≥0}
    {before after : Finset iota} {W : iota -> Tube r E}
    (parents : Finset pi) (part : pi -> Finset iota)
    (kappa CoverC : ℝ≥0∞)
    (hcover : after <= parents.biUnion part)
    (hlocal : ∀ P ∈ parents,
      Kakeya.maxDensity (part P) (fun i => (W i).toConvexSpaceBody) <=
        kappa * allExactTubeNsW87 before W s)
    (hmeeting : forall R : Tube s E,
      (((parents.filter fun P =>
        (part P ∩ exactTubeCellW87 after W R).Nonempty).card : Nat) : ℝ≥0∞) <=
        CoverC) :
    allExactTubeNsW87 after W s <=
      CoverC * kappa * allExactTubeNsW87 before W s := by
  classical
  apply allExactTubeNs_le_w87
  intro R _hcellNe
  let meeting : Finset pi := parents.filter fun P =>
    (part P ∩ exactTubeCellW87 after W R).Nonempty
  have hcoverR : exactTubeCellW87 after W R <= meeting.biUnion part := by
    intro i hi
    rcases Finset.mem_biUnion.mp (hcover (exactTubeCell_subset_w87 after W R hi)) with
      ⟨P, hP, hiP⟩
    refine Finset.mem_biUnion.mpr ⟨P, ?_, hiP⟩
    exact Finset.mem_filter.mpr ⟨hP, ⟨i, Finset.mem_inter.mpr ⟨hiP, hi⟩⟩⟩
  have hmax := Kakeya.maxDensity_le_sum_of_subset_biUnion
    (W := fun i => (W i).toConvexSpaceBody) hcoverR
  calc
    Kakeya.maxDensity (exactTubeCellW87 after W R)
        (fun i => (W i).toConvexSpaceBody)
        <= ∑ P ∈ meeting,
          Kakeya.maxDensity (part P) (fun i => (W i).toConvexSpaceBody) := hmax
    _ <= ∑ _P ∈ meeting, kappa * allExactTubeNsW87 before W s := by
      apply Finset.sum_le_sum
      intro P hP
      exact hlocal P (Finset.mem_filter.mp hP).1
    _ = (meeting.card : ℝ≥0∞) *
        (kappa * allExactTubeNsW87 before W s) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ <= CoverC * (kappa * allExactTubeNsW87 before W s) := by
      exact mul_le_mul_left (by simpa [meeting] using hmeeting R) _
    _ = CoverC * kappa * allExactTubeNsW87 before W s := by
      rw [mul_assoc]

/-! ## Literal canonical D_(q,ell) and profile -/

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem image_saturatedFineLift_eq_w87
    {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}
    {base current : Finset iota} {T : iota -> Tube delta E}
    {M : Nat} {C : ℝ≥0} (U : CanonicalProfileNetW87 base T M C)
    (q : Fin (M + 1))
    (keptNodes : Finset (CanonicalQNodeW87 U current q)) :
    canonicalAncestorFamilyW87 U
      (saturatedFineLiftW87 U current q
        (canonicalQNodeValuesW87 keptNodes)) q =
      canonicalQNodeValuesW87 keptNodes := by
  classical
  apply Finset.Subset.antisymm
  · intro w hw
    rcases Finset.mem_image.mp hw with ⟨i, hi, rfl⟩
    exact (Finset.mem_filter.mp hi).2
  · intro w hw
    rcases Finset.mem_image.mp hw with ⟨wnode, hwnode, rfl⟩
    rcases Finset.mem_image.mp wnode.property with ⟨i, hiCurrent, hiAssign⟩
    refine Finset.mem_image.mpr ⟨i, ?_, hiAssign⟩
    exact Finset.mem_filter.mpr
      ⟨hiCurrent, Finset.mem_image.mpr ⟨wnode, hwnode, hiAssign.symm⟩⟩

structure LiteralInnerDropOutputW87
    {iota : Type uI} [DecidableEq iota] {delta working : ℝ≥0}
    {base current : Finset iota} {T : iota -> Tube delta E}
    {M : Nat} {C : ℝ≥0} (U : CanonicalProfileNetW87 base T M C)
    (q : Fin (M + 1))
    (Y : CanonicalQNodeW87 U current q ->
      ShadedTube (Tube.gridScale delta M q.val) E)
    (nodeFamily : Finset iota) (nodeTube : iota -> Tube working E)
    (part : iota -> Finset (CanonicalQNodeW87 U current q))
    (d : ℝ≥0) (epsilon zetaJ : ℝ) (Ktr : Nat) where
  FPlus : Finset (CanonicalQNodeW87 U current q)
  YPlus : CanonicalQNodeW87 U current q ->
    ShadedTube (Tube.gridScale delta M q.val) E
  FPlus_nonempty : FPlus.Nonempty
  FPlus_subset : FPlus <= canonicalQNodeFinsetW87 U current q
  middle_same_tube : forall w, (Y w).toTube = U.cover.tube q.val w.val
  subshading : ∀ w ∈ FPlus,
    (YPlus w).toTube = (Y w).toTube /\ (YPlus w).shade <= (Y w).shade
  assigned_cover : FPlus = nodeFamily.biUnion part
  assigned_disjoint : Set.Pairwise (nodeFamily : Set iota) fun P Q =>
    Disjoint (part P) (part Q)
  part_subset : ∀ P ∈ nodeFamily, part P <= FPlus
  part_parent_containment : ∀ P ∈ nodeFamily, ∀ w ∈ part P,
    (YPlus w).toConvexSpaceBody <= (nodeTube P).toConvexSpaceBody
  parent_boundedOverlap : Tube.HasBoundedOverlap
    (canonicalQNodeFinsetW87 U current q) (fun w => (Y w).toTube)
      nodeFamily nodeTube C
  member_twice_le_working : 2 * Tube.gridScale delta M q.val <= working
  per_cell_density_drop : ∀ P ∈ nodeFamily,
    Kakeya.maxDensity (part P)
        (fun w => (YPlus w).toConvexSpaceBody) <=
      (d : ℝ≥0∞) ^ (epsilon * zetaJ / 4) *
        allExactTubeNsW87 (canonicalQNodeFinsetW87 U current q)
          (fun w => (Y w).toTube) working
  Ktr_pos : 0 < Ktr
  mass_retention :
    ENNReal.ofReal
        ((1 + Real.log (1 / (d : ℝ))) ^ (-(Ktr : ℝ))) *
      (∑ w ∈ canonicalQNodeFinsetW87 U current q, volume (Y w).shade) <=
        ∑ w ∈ FPlus, volume (YPlus w).shade

private theorem allExactTubeNs_map_w90
    {alpha beta : Type*} [DecidableEq alpha] [DecidableEq beta]
    {r s : ℝ≥0} (A : Finset alpha) (e : alpha ↪ beta)
    (W : beta -> Tube r E) :
    allExactTubeNsW87 (A.map e) W s =
      allExactTubeNsW87 A (fun a => W (e a)) s := by
  classical
  have hcell (R : Tube s E) :
      exactTubeCellW87 (A.map e) W R =
        (exactTubeCellW87 A (fun a => W (e a)) R).map e := by
    ext b
    simp only [exactTubeCellW87, Finset.mem_filter, Finset.mem_map]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hbody⟩
      exact ⟨a, ⟨ha, hbody⟩, rfl⟩
    · rintro ⟨a, ⟨ha, hbody⟩, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, hbody⟩
  apply le_antisymm
  · apply allExactTubeNs_le_w87
    intro R hne
    rw [hcell R, Kakeya.maxDensity_map]
    apply maxDensity_exactTubeCell_le_allExactTubeNs_w87 R
    simpa [hcell R] using hne
  · apply allExactTubeNs_le_w87
    intro R hne
    rw [← Kakeya.maxDensity_map
      (exactTubeCellW87 A (fun a => W (e a)) R) e
        (fun b => (W b).toConvexSpaceBody), ← hcell R]
    apply maxDensity_exactTubeCell_le_allExactTubeNs_w87 R
    rw [hcell R]
    exact Finset.map_nonempty.mpr hne

theorem inner_literal_Ns_drop_w87
    {iota : Type uI} [DecidableEq iota] {delta working d : ℝ≥0}
    {base current : Finset iota} {T : iota -> Tube delta E}
    {M Ktr : Nat} {C : ℝ≥0}
    (U : CanonicalProfileNetW87 base T M C) (q : Fin (M + 1))
    {Y : CanonicalQNodeW87 U current q ->
      ShadedTube (Tube.gridScale delta M q.val) E}
    {nodeFamily : Finset iota} {nodeTube : iota -> Tube working E}
    {part : iota -> Finset (CanonicalQNodeW87 U current q)}
    {epsilon zetaJ : ℝ}
    (inner : LiteralInnerDropOutputW87 U q Y nodeFamily nodeTube part
      d epsilon zetaJ Ktr)
    (_hd : 0 < d) (hd1 : d <= 1) (hexp : 0 <= epsilon * zetaJ) :
    allExactTubeNsW87 (canonicalQNodeValuesW87 inner.FPlus)
        (fun w => U.cover.tube q.val w) working <=
      (C : ℝ≥0∞) * (d : ℝ≥0∞) ^ (epsilon * zetaJ / 8) *
        allExactTubeNsW87 (canonicalAncestorFamilyW87 U current q)
          (fun w => U.cover.tube q.val w) working := by
  classical
  let rawPart : iota -> Finset iota := fun P => canonicalQNodeValuesW87 (part P)
  let valEmbedding : CanonicalQNodeW87 U current q ↪ iota :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hcover : canonicalQNodeValuesW87 inner.FPlus <=
      nodeFamily.biUnion rawPart := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨wnode, hwPlus, rfl⟩
    rw [inner.assigned_cover] at hwPlus
    rcases Finset.mem_biUnion.mp hwPlus with ⟨P, hP, hwPart⟩
    exact Finset.mem_biUnion.mpr
      ⟨P, hP, Finset.mem_image.mpr ⟨wnode, hwPart, rfl⟩⟩
  have hlocal : ∀ P ∈ nodeFamily,
      Kakeya.maxDensity (rawPart P)
          (fun w => (U.cover.tube q.val w).toConvexSpaceBody) <=
        (d : ℝ≥0∞) ^ (epsilon * zetaJ / 4) *
          allExactTubeNsW87 (canonicalAncestorFamilyW87 U current q)
            (fun w => U.cover.tube q.val w) working := by
    intro P hP
    calc
      Kakeya.maxDensity (rawPart P)
          (fun w => (U.cover.tube q.val w).toConvexSpaceBody)
          = Kakeya.maxDensity (part P)
              (fun w => (U.cover.tube q.val w.val).toConvexSpaceBody) := by
            have hmap :=
              Kakeya.maxDensity_map (part P) valEmbedding
                (fun w => (U.cover.tube q.val w).toConvexSpaceBody)
            rw [Finset.map_eq_image] at hmap
            convert hmap using 1 <;> simp [rawPart, valEmbedding,
              canonicalQNodeValuesW87]
      _ = Kakeya.maxDensity (part P)
            (fun w => (inner.YPlus w).toConvexSpaceBody) := by
          apply Kakeya.maxDensity_congr
          intro w hw
          have hwPlus := inner.part_subset P hP hw
          rw [(inner.subshading w hwPlus).1, inner.middle_same_tube w]
      _ <= (d : ℝ≥0∞) ^ (epsilon * zetaJ / 4) *
          allExactTubeNsW87 (canonicalQNodeFinsetW87 U current q)
            (fun w => (Y w).toTube) working := inner.per_cell_density_drop P hP
      _ = (d : ℝ≥0∞) ^ (epsilon * zetaJ / 4) *
          allExactTubeNsW87 (canonicalAncestorFamilyW87 U current q)
            (fun w => U.cover.tube q.val w) working := by
          congr 1
          have hY : (fun w => (Y w).toTube) =
              (fun w => U.cover.tube q.val w.val) := by
            funext w
            exact inner.middle_same_tube w
          rw [hY]
          have hvalues : canonicalQNodeValuesW87
              (canonicalQNodeFinsetW87 U current q) =
              canonicalAncestorFamilyW87 U current q := by
            ext w
            simp [canonicalQNodeValuesW87, canonicalQNodeFinsetW87]
          calc
            allExactTubeNsW87 (canonicalQNodeFinsetW87 U current q)
                (fun w => U.cover.tube q.val w.val) working =
              allExactTubeNsW87 (canonicalQNodeValuesW87
                  (canonicalQNodeFinsetW87 U current q))
                (fun w => U.cover.tube q.val w) working := by
                  have hmap :=
                    (allExactTubeNs_map_w90 (s := working)
                      (canonicalQNodeFinsetW87 U current q)
                      valEmbedding
                      (fun w => U.cover.tube q.val w)).symm
                  rw [Finset.map_eq_image] at hmap
                  convert hmap using 1 <;> simp [valEmbedding,
                    canonicalQNodeValuesW87]
            _ = allExactTubeNsW87 (canonicalAncestorFamilyW87 U current q)
                (fun w => U.cover.tube q.val w) working := by rw [hvalues]
  have hmeeting : forall R : Tube working E,
      (((nodeFamily.filter fun P =>
        (rawPart P ∩ exactTubeCellW87 (canonicalQNodeValuesW87 inner.FPlus)
          (fun w => U.cover.tube q.val w) R).Nonempty).card : Nat) : ℝ≥0∞) <= C := by
    intro R
    have hfilter :
        nodeFamily.filter (fun P =>
          (rawPart P ∩ exactTubeCellW87 (canonicalQNodeValuesW87 inner.FPlus)
            (fun w => U.cover.tube q.val w) R).Nonempty) <=
        nodeFamily.filter (fun P => ∃ w ∈ canonicalQNodeFinsetW87 U current q,
          (Y w).toConvexSpaceBody <= (nodeTube P).toConvexSpaceBody /\
          (Y w).toConvexSpaceBody <= R.toConvexSpaceBody) := by
      intro P hP
      have hP' := Finset.mem_filter.mp hP
      rcases hP'.2 with ⟨w, hw⟩
      have hwPart' := Finset.mem_inter.mp hw
      rcases Finset.mem_image.mp hwPart'.1 with ⟨wnode, hwnodePart, rfl⟩
      have hwPlus := inner.part_subset P hP'.1 hwnodePart
      have hwAll := inner.FPlus_subset hwPlus
      have hparent := inner.part_parent_containment P hP'.1 wnode hwnodePart
      have hsub := (inner.subshading wnode hwPlus).1
      have hmiddle := inner.middle_same_tube wnode
      refine Finset.mem_filter.mpr ⟨hP'.1, wnode, hwAll, ?_, ?_⟩
      · simpa [hsub] using hparent
      · have hcellBody := (Finset.mem_filter.mp hwPart'.2).2
        simpa [hmiddle] using hcellBody
    have hcard :
        (((nodeFamily.filter fun P =>
          (rawPart P ∩ exactTubeCellW87 (canonicalQNodeValuesW87 inner.FPlus)
            (fun w => U.cover.tube q.val w) R).Nonempty).card : Nat) : ℝ≥0∞) <=
        (((nodeFamily.filter fun P => ∃ w ∈ canonicalQNodeFinsetW87 U current q,
          (Y w).toConvexSpaceBody <= (nodeTube P).toConvexSpaceBody /\
          (Y w).toConvexSpaceBody <= R.toConvexSpaceBody).card : Nat) : ℝ≥0∞) := by
      exact_mod_cast Finset.card_le_card hfilter
    exact hcard.trans (by
      simpa [Tube.HasBoundedOverlap] using inner.parent_boundedOverlap R)
  have hdrop := allExactTubeNs_le_of_assignedCover_w87
    nodeFamily rawPart ((d : ℝ≥0∞) ^ (epsilon * zetaJ / 4)) (C : ℝ≥0∞)
    hcover hlocal hmeeting
  refine hdrop.trans ?_
  have hpow : (d : ℝ≥0∞) ^ (epsilon * zetaJ / 4) <=
      (d : ℝ≥0∞) ^ (epsilon * zetaJ / 8) := by
    apply ENNReal.rpow_le_rpow_of_exponent_ge
    · exact_mod_cast hd1
    · linarith
  exact mul_le_mul_left (mul_le_mul_right hpow (C : ℝ≥0∞)) _

theorem inner_before_le_canonical_before_w87
    {iota : Type uI} [DecidableEq iota]
    {delta : ℝ≥0} {base current : Finset iota}
    {T : iota -> Tube delta E} {M : Nat} {C : ℝ≥0}
    (U : CanonicalProfileNetW87 base T M C)
    (q ellPred : Fin (M + 1))
    (working : ℝ≥0)
    (hscale : working <= Tube.gridScale delta M ellPred.val) :
    allExactTubeNsW87 (canonicalAncestorFamilyW87 U current q)
        (fun w => U.cover.tube q.val w) working <=
      literalCanonicalDW87 U current q ellPred := by
  unfold literalCanonicalDW87
  apply allExactTubeNs_le_w87
  intro R hne
  let R' : Tube (Tube.gridScale delta M ellPred.val) E :=
    R.rescale (Tube.gridScale delta M ellPred.val)
  have hcell : exactTubeCellW87 (canonicalAncestorFamilyW87 U current q)
      (fun w => U.cover.tube q.val w) R <=
      exactTubeCellW87 (canonicalAncestorFamilyW87 U current q)
        (fun w => U.cover.tube q.val w) R' := by
    intro i hi
    have hi' := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr
      ⟨hi'.1, hi'.2.trans (Tube.le_rescale R hscale)⟩
  have hne' : (exactTubeCellW87 (canonicalAncestorFamilyW87 U current q)
      (fun w => U.cover.tube q.val w) R').Nonempty := hne.mono hcell
  exact (Kakeya.maxDensity_mono _ hcell).trans
    (maxDensity_exactTubeCell_le_allExactTubeNs_w87 R' hne')

theorem canonical_after_le_inner_after_w87
    {iota : Type uI} [DecidableEq iota]
    {delta : ℝ≥0} {base current : Finset iota}
    {T : iota -> Tube delta E} {C : ℝ≥0} {p : Params}
    (P : RevisedProfileParametersW87 p)
    (U : CanonicalProfileNetW87 base T P.M C)
    (hdim : Module.finrank ℝ E = 3)
    (hdelta : 0 < delta)
    (_hcurrent : current <= base)
    (q ellPred : Fin (P.M + 1)) (working : ℝ≥0)
    (keptNodes : Finset (CanonicalQNodeW87 U current q))
    (hworking : 0 < working)
    (hmember : 2 * Tube.gridScale delta P.M q.val <= working)
    (hround_lower : Tube.gridScale delta P.M (ellPred.val + 1) <= working)
    (hround : working < Tube.gridScale delta P.M ellPred.val) :
    literalCanonicalDW87 U
        (saturatedFineLiftW87 U current q
          (canonicalQNodeValuesW87 keptNodes)) q ellPred <=
      ENNReal.ofReal
          (2 * 25 ^ (6 : Nat) * 4 ^ (6 : Nat) *
            (delta : ℝ) ^ (-6 / (P.M : ℝ))) *
        allExactTubeNsW87 (canonicalQNodeValuesW87 keptNodes)
          (fun w => U.cover.tube q.val w) working := by
  have hratio : (Tube.gridScale delta P.M ellPred.val : ℝ) / (working : ℝ) <=
      (delta : ℝ) ^ (-1 / (P.M : ℝ)) := by
    calc
      (Tube.gridScale delta P.M ellPred.val : ℝ) / (working : ℝ) <=
          (Tube.gridScale delta P.M ellPred.val : ℝ) /
            (Tube.gridScale delta P.M (ellPred.val + 1) : ℝ) :=
        div_le_div_of_nonneg_left (NNReal.coe_nonneg _)
          (by exact_mod_cast Tube.gridScale_pos hdelta P.M (ellPred.val + 1))
          (by exact_mod_cast hround_lower)
      _ = (delta : ℝ) ^ (-1 / (P.M : ℝ)) := by
        rw [← NNReal.coe_div, Tube.gridScale_div_gridScale hdelta, NNReal.coe_rpow]
        congr 1
        push_cast
        ring
  have hconstant :
      2 * 25 ^ (6 : Nat) *
          (4 * (Tube.gridScale delta P.M ellPred.val : ℝ) / (working : ℝ)) ^ (6 : Nat) <=
        2 * 25 ^ (6 : Nat) * 4 ^ (6 : Nat) *
          (delta : ℝ) ^ (-6 / (P.M : ℝ)) := by
    calc
      2 * 25 ^ (6 : Nat) *
          (4 * (Tube.gridScale delta P.M ellPred.val : ℝ) / (working : ℝ)) ^ (6 : Nat) =
          (2 * 25 ^ (6 : Nat) * 4 ^ (6 : Nat)) *
            ((Tube.gridScale delta P.M ellPred.val : ℝ) / (working : ℝ)) ^ (6 : Nat) := by
        ring
      _ <= (2 * 25 ^ (6 : Nat) * 4 ^ (6 : Nat)) *
          ((delta : ℝ) ^ (-1 / (P.M : ℝ))) ^ (6 : Nat) := by
        gcongr
      _ = _ := by
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_mul (NNReal.coe_nonneg delta)]
        congr 1
        ring
  unfold literalCanonicalDW87
  rw [image_saturatedFineLift_eq_w87]
  exact (allExactTubeNs_coarse_le_fine_w87
    (canonicalQNodeValuesW87 keptNodes) (fun w => U.cover.tube q.val w)
    hdim (Tube.gridScale_pos hdelta P.M q.val) hmember hround.le).trans
      (mul_le_mul_left (ENNReal.ofReal_le_ofReal hconstant) _)

theorem raw_literalCanonicalD_drop_w87
    {iota : Type uI} [DecidableEq iota]
    {delta working d : ℝ≥0} {base current next : Finset iota}
    {T : iota -> Tube delta E} {p : Params}
    (P : RevisedProfileParametersW87 p)
    (U : CanonicalProfileNetW87 base T P.M P.canonicalC)
    (q ellPred : Fin (P.M + 1)) (zetaJ : ℝ)
    {Y : CanonicalQNodeW87 U current q ->
      ShadedTube (Tube.gridScale delta P.M q.val) E}
    {nodeFamily : Finset iota} {nodeTube : iota -> Tube working E}
    {part : iota -> Finset (CanonicalQNodeW87 U current q)} {Ktr : Nat}
    (inner : LiteralInnerDropOutputW87 U q Y nodeFamily nodeTube part
      d p.ε zetaJ Ktr)
    (hdim : Module.finrank ℝ E = 3)
    (hdelta : 0 < delta) (_hdelta1 : delta < 1)
    (hd : 0 < d) (hd1 : d <= 1) (hexp : 0 <= p.ε * zetaJ)
    (hcurrent : current <= base)
    (hnext : next = saturatedFineLiftW87 U current q
      (canonicalQNodeValuesW87 inner.FPlus))
    (hround_lower : Tube.gridScale delta P.M (ellPred.val + 1) <= working)
    (hround : working < Tube.gridScale delta P.M ellPred.val) :
    literalCanonicalDW87 U next q ellPred <=
      ENNReal.ofReal (canonicalComparisonFactorW87 P delta d zetaJ) *
        literalCanonicalDW87 U current q ellPred := by
  let A : ℝ := 2 * 25 ^ (6 : Nat) * 4 ^ (6 : Nat) *
    (delta : ℝ) ^ (-6 / (P.M : ℝ))
  have hworking : 0 < working :=
    (mul_pos (by norm_num) (Tube.gridScale_pos hdelta P.M q.val)).trans_le
      inner.member_twice_le_working
  have hcanonical := canonical_after_le_inner_after_w87 P U hdim hdelta hcurrent
    q ellPred working inner.FPlus hworking inner.member_twice_le_working hround_lower hround
  have hinner := inner_literal_Ns_drop_w87 U q inner hd hd1 hexp
  have hbefore := inner_before_le_canonical_before_w87
    (current := current) U q ellPred working hround.le
  have hcoefficient : ENNReal.ofReal A * (P.canonicalC : ℝ≥0∞) *
      (d : ℝ≥0∞) ^ (p.ε * zetaJ / 8) =
        ENNReal.ofReal (canonicalComparisonFactorW87 P delta d zetaJ) := by
    have hA : 0 <= A := by dsimp [A]; positivity
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have hfactor : canonicalComparisonFactorW87 P delta d zetaJ =
        A * (P.canonicalC : ℝ) * (d : ℝ) ^ (p.ε * zetaJ / 8) := by
      dsimp [canonicalComparisonFactorW87, sourceCgeomW87, A]
      ring
    rw [hfactor, ENNReal.ofReal_mul (mul_nonneg hA (NNReal.coe_nonneg _)),
      ENNReal.ofReal_mul hA, ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_rpow_of_pos hdR, ENNReal.ofReal_coe_nnreal]
  rw [hnext]
  calc
    literalCanonicalDW87 U
        (saturatedFineLiftW87 U current q (canonicalQNodeValuesW87 inner.FPlus)) q ellPred <=
        ENNReal.ofReal A * allExactTubeNsW87 (canonicalQNodeValuesW87 inner.FPlus)
          (fun w => U.cover.tube q.val w) working := hcanonical
    _ <= ENNReal.ofReal A * ((P.canonicalC : ℝ≥0∞) *
        (d : ℝ≥0∞) ^ (p.ε * zetaJ / 8) *
          allExactTubeNsW87 (canonicalAncestorFamilyW87 U current q)
            (fun w => U.cover.tube q.val w) working) := mul_le_mul_right hinner _
    _ = (ENNReal.ofReal A * (P.canonicalC : ℝ≥0∞) *
        (d : ℝ≥0∞) ^ (p.ε * zetaJ / 8)) *
          allExactTubeNsW87 (canonicalAncestorFamilyW87 U current q)
            (fun w => U.cover.tube q.val w) working := by ring
    _ <= (ENNReal.ofReal A * (P.canonicalC : ℝ≥0∞) *
        (d : ℝ≥0∞) ^ (p.ε * zetaJ / 8)) *
          literalCanonicalDW87 U current q ellPred := mul_le_mul_right hbefore _
    _ = _ := by rw [hcoefficient]

end

end Kakeya.ml1Boot.RevisedLiteralProfileInterfaceFormalizerW87

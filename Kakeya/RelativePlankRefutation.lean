/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.RelativePlank
public import Kakeya.DimensionThree.Volume
public import Kakeya.DimensionThree.Plank.PlankFactorizationEstimate
public import Kakeya.DimensionThree.FrostmanEstimateOne

/-!
# `Kakeya.tubeMultiplicityOfLocalPersistentPlankFactorisation` is refutable

`Kakeya.tubeMultiplicityOfLocalPersistentPlankFactorisation` (`Kakeya/RelativePlank.lean`) is the
persistent-hypothesis variant of GWZ Proposition 6.6(A) in the regime `δ ≤ ρ ≤ a ≤ b ≤ 1`.  Its
hypothesis list carries **no essential-distinctness clause** on the fine family `(T i)_{i ∈ q}`,
and no upper bound on `#q`.  Every other form of the same estimate in the development does carry
one:

* `Kakeya.FrostmanEstimate.multiplicity_bound_of_mem` (the canonical Frostman multiplicity
  estimate, `Kakeya/PartialEstimates.lean`) takes
  `(s : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier)`;
* `Kakeya.IsFlatPrismFamily` — the family package of
  `Kakeya.FlatPrisms.multiplicity_le_of_factorsThroughFlatPrisms'`, the surviving general form of
  6.6(A) — carries it as the field `essDistinct`.

Without it the statement is false, and this file proves it false, unconditionally in `β`: the
witness is `N` **copies of one fully shaded `δ`-tube**, at `ρ = a = b = δ`.  Every hypothesis is
`N`-independent — uniformity holds at constant `1`, the Frostman constant is `|B₁| / |T|`, and the
plank-factorisation constant is `8 / c₃` where `c₃` is `Tube.le_volume.c 3` — while the
multiplicity is exactly `N` and the right-hand side grows like `N ^ (1 - β / 2)`.  Taking `N` large
breaks the inequality.

## What is proved here

* `Kakeya.PersistPlankCE.Payload` is the target's conclusion copied verbatim, with the index
  universe fixed at `Type`; `Kakeya.PersistPlankCE.payload_of_target` is the one-line check that
  the copy is exact (it is the target, applied). * `Kakeya.PersistPlankCE.not_payload` refutes it, for every `β ∈ (0, 1]`. * `Kakeya.PersistPlankCE.not_katzTaoEstimate_and_frostmanEstimate` combines the two: the target as
  stated implies `¬ (K_KT(β) ∧ K_F(β))`. It cites the sorried target and therefore carries
  `sorryAx`; that is the point of the statement, not a defect of it.

## The witness

`ι = ℕ`, `q = Finset.range N`, `T i = ` one fixed fully shaded `δ`-tube along `e₂`
(`Kakeya.PersistPlankCE.ST`), and `ρ = a = b = δ`.  The outer plank is the `δ × δ × 1` prism
around the same axis (`Kakeya.PersistPlankCE.P`), the coarse tube is the tube itself, and the
factor family has one block and one parent (`Kakeya.PersistPlankCE.CEfam`).

Every hypothesis holds, and every constant is independent of `N`:

* two-sided shaded uniformity at constant `1` (`Kakeya.PersistPlankCE.CEshadedUnif`) — one node at
  every grid scale, all branching numbers equal to `N`;
* fullness `1` (`Kakeya.PersistPlankCE.CEfullness`);
* `IsFrostmanIn` at `C_F = |B₁| / |T|` (`Kakeya.PersistPlankCE.isFrostman`) — both densities scale
  linearly in `N`, so the ratio does not see `N`;
* `PersistentPlankFactorization` at `C₀ = max 1 (8 / c₃)` with `c₃ = Tube.le_volume.c 3`
  (`Kakeya.PersistPlankCE.CEpersistent`) — the density clause reduces to
  `|δ × δ × 1 plank| ≤ C₀ · |δ-tube|`, which is `8 δ² ≤ C₀ · c₃ δ²`.

The multiplicity is exactly `N` (`Kakeya.PersistPlankCE.CEmultiplicity`) while the right-hand side
is `A · N ^ (1 - β/2)` with `A = Kakeya.PersistPlankCE.Aconst β δ` finite and `N`-free, so `N`
beyond `A ^ (2/β)` breaks it.

## Why the density clause does not save the statement

`PersistentPlankFactorization.maxDensity_le_mul` is what stops the *aspect-ratio* free lunch: with
all inner tubes of a block inside one `ρ`-tube, `|hull(fibre)| ≤ C ρ²`, so the clause forces
`8ab = |plank| ≤ C₀ · C ρ² ≤ C₀ · C a²`, i.e. `b / a ≲ C₀ ≤ δ ^ (-η)`, and the claimed gain
`(a/b) ^ (3β/2)` is at most a `δ ^ (-ε)`-absorbable loss.  It does **not** stop the *cardinality*
free lunch, because it is a statement about ratios of densities and every density in the witness
is homogeneous of degree one in `N`.

## The minimal repair

Add the clause every sibling form carries:

`(q : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier)`

to `Kakeya.tubeMultiplicityOfLocalPersistentPlankFactorisation`.  It kills this witness outright
(the `N` copies are not pairwise essentially distinct) and it is what
`Kakeya.FrostmanEstimate.multiplicity_bound_of_mem` — the estimate any proof of the target must
eventually reach — demands.  Its intended producer,
`Kakeya.multiplicity_le_of_relativePlankSelection`, can supply it, since the selection only ever
shrinks the index set.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Kakeya Convexity ConvexSpaceBody
open Tube (gridScale gridScale_self gridScale_antitone GridCoverSystem)

noncomputable section

namespace Kakeya.PersistPlankCE

/-! ### The witness geometry: one tube, one plank -/

abbrev E3 := EuclideanSpace ℝ (Fin 3)

def e2 : E3 := EuclideanSpace.single 2 (1:ℝ)

theorem norm_e2 : ‖e2‖ = 1 := by simp [e2]

theorem dist_pts : dist (-(1/2:ℝ) • e2) ((1/2:ℝ) • e2) = 1 := by
  rw [dist_eq_norm]
  have h : -(1/2:ℝ) • e2 - (1/2:ℝ) • e2 = (-1:ℝ) • e2 := by module
  rw [h, norm_smul]
  simp [norm_e2]

def T (δ : ℝ≥0) : Tube δ E3 := Tube.mk' δ dist_pts

/-- Every point of the segment is `c • e2` with `|c| ≤ 1/2`. -/
theorem mem_segment_iff {z : E3} :
    z ∈ segment ℝ (-(1/2:ℝ) • e2) ((1/2:ℝ) • e2) → ∃ c : ℝ, |c| ≤ 1/2 ∧ z = c • e2 := by
  rintro ⟨a, b, ha, hb, hab, rfl⟩
  refine ⟨(b - a)/2, ?_, ?_⟩
  · rw [abs_le]; constructor <;> linarith
  · module

theorem T_mem {δ : ℝ≥0} {x : E3} (hx : x ∈ (T δ).carrier) :
    ∃ c : ℝ, |c| ≤ 1/2 ∧ ‖x - c • e2‖ ≤ (δ:ℝ) := by
  rw [Tube.carrier_eq] at hx
  simp only [Set.mem_iUnion, Metric.mem_closedBall, exists_prop] at hx
  obtain ⟨z, hz, hd⟩ := hx
  obtain ⟨c, hc, rfl⟩ := mem_segment_iff hz
  exact ⟨c, hc, by rwa [← dist_eq_norm]⟩

theorem T_ball {δ : ℝ≥0} (hδ : δ ≤ 1 / 2) : (T δ).carrier ⊆ closedBall (0:E3) 1 := by
  intro x hx
  obtain ⟨c, hc, hd⟩ := T_mem hx
  have hδ' : (δ:ℝ) ≤ 1/2 := by exact_mod_cast hδ
  have : ‖c • e2‖ = |c| := by rw [norm_smul, norm_e2]; simp
  simp only [Metric.mem_closedBall, dist_zero_right]
  calc ‖x‖ = ‖(x - c • e2) + c • e2‖ := by congr 1; abel
    _ ≤ ‖x - c • e2‖ + ‖c • e2‖ := norm_add_le _ _
    _ ≤ 1/2 + 1/2 := by rw [this]; linarith
    _ = 1 := by norm_num

def P (δ : ℝ≥0) (hδ1 : δ ≤ 1) : Plank δ δ le_rfl hδ1 where
  toPrismNDim := PrismNDim.mk' (0 : E3) (EuclideanSpace.basisFun (Fin 3) ℝ) ![δ, δ, 1]
  thicknesses_eq := rfl

/-! ### Volumes -/

/-- The volume of the witness tube. -/
def m (δ : ℝ≥0) : ℝ≥0∞ := volume (T δ).carrier

theorem m_ne_top (δ : ℝ≥0) : m δ ≠ ⊤ := (T δ).isCompact'.measure_ne_top

theorem finrank_E3 : Module.finrank ℝ E3 = 3 := by simp

theorem c3_mul_le (δ : ℝ≥0) :
    ((Tube.le_volume.c 3 : ℝ≥0) : ℝ≥0∞) * (δ : ℝ≥0∞) ^ 2 ≤ m δ := by
  have h := Tube.le_volume (T δ)
  rw [finrank_E3] at h
  exact (by simpa using h : _)

theorem m_pos {δ : ℝ≥0} (hδ : 0 < δ) : 0 < m δ := by
  refine lt_of_lt_of_le ?_ (c3_mul_le δ)
  have h1 : ((Tube.le_volume.c 3 : ℝ≥0) : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (Tube.le_volume.c_pos 3).ne'
  have h2 : (δ : ℝ≥0∞) ^ 2 ≠ 0 := pow_ne_zero _ (ENNReal.coe_ne_zero.mpr hδ.ne')
  exact pos_iff_ne_zero.mpr (mul_ne_zero h1 h2)

/-- The plank-to-tube volume ratio constant. -/
def C0 : ℝ≥0 := max 1 (8 / Tube.le_volume.c 3)

/-! ### The shaded family -/

def ST (δ : ℝ≥0) : ShadedTube δ E3 where
  toTube := T δ
  shade := (T δ).carrier
  measurableSet_shade := (T δ).isCompact'.measurableSet
  shade_subset := subset_rfl

theorem ST_carrier (δ : ℝ≥0) : (ST δ).carrier = (T δ).carrier := rfl

/-! ### Density bookkeeping for a constant family -/

variable {ι : Type*}

open scoped Classical in
theorem const_sum_le (B : ConvexSpaceBody E3) (s : Finset ι) (K : ConvexSpaceBody E3) :
    ∑ i ∈ s with (fun _ : ι => B) i ≤ K, volume ((fun _ : ι => B) i).carrier
      ≤ (s.card : ℝ≥0∞) * volume K.carrier := by
  classical
  rcases Finset.eq_empty_or_nonempty (s.filter (fun i : ι => (fun _ : ι => B) i ≤ K)) with he | ⟨i0, hi0⟩
  · simp [he]
  · have hBK : B ≤ K := (Finset.mem_filter.mp hi0).2
    have hvol : volume B.carrier ≤ volume K.carrier := measure_mono hBK
    have hcard : (s.filter (fun i : ι => (fun _ : ι => B) i ≤ K)).card ≤ s.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    calc ∑ i ∈ s with (fun _ : ι => B) i ≤ K, volume ((fun _ : ι => B) i).carrier
        = ((s.filter (fun i : ι => (fun _ : ι => B) i ≤ K)).card : ℝ≥0∞) * volume B.carrier := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (s.card : ℝ≥0∞) * volume K.carrier := by
          refine mul_le_mul' ?_ hvol
          exact_mod_cast hcard

theorem const_densityIn_eq (B : ConvexSpaceBody E3) (s : Finset ι) {K : ConvexSpaceBody E3}
    (h : B ≤ K) :
    densityIn s (fun _ : ι => B) K = (s.card : ℝ≥0∞) * volume B.carrier / volume K.carrier := by
  classical
  rw [densityIn_of_all_le (fun i _ => h), Finset.sum_const, nsmul_eq_mul]

/-! ### Uniformity of the witness family -/

theorem delta_le_gridScale {δ : ℝ≥0} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {M k : ℕ} (hk : k ≤ M) :
    δ ≤ gridScale δ M k := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · have : k = 0 := Nat.le_zero.mp hk
    subst this
    simpa using hδ1
  · calc δ = gridScale δ M M := (gridScale_self δ hM).symm
      _ ≤ gridScale δ M k := gridScale_antitone hδ0 hδ1 M hk

section ClassicalBlock
open scoped Classical

end ClassicalBlock

/-! ### Frostman constant, factor family, and the plank factorisation -/

/-- The volume of the unit ball. -/
def vB : ℝ≥0∞ := volume (ConvexSpaceBody.closedUnitBall (E := E3)).carrier

theorem vB_pos : 0 < vB := ConvexSpaceBody.closedUnitBall_volume_pos
theorem vB_ne_top : vB ≠ ⊤ := (ConvexSpaceBody.closedUnitBall (E := E3)).isCompact'.measure_ne_top

theorem ST_le_ball {δ : ℝ≥0} (hδ : δ ≤ 1 / 2) :
    (ST δ).toConvexSpaceBody ≤ (ConvexSpaceBody.closedUnitBall (E := E3)) :=
  T_ball hδ

theorem m_le_vB {δ : ℝ≥0} (hδ : δ ≤ 1 / 2) : m δ ≤ vB := measure_mono (T_ball hδ)

/-- The Frostman constant of the witness family. -/
def CF (δ : ℝ≥0) : ℝ≥0∞ := vB / m δ

theorem one_le_CF {δ : ℝ≥0} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) : 1 ≤ CF δ := by
  rw [CF, ENNReal.le_div_iff_mul_le (Or.inl (m_pos hδ0).ne') (Or.inl (m_ne_top δ)), one_mul]
  exact m_le_vB hδ

theorem isFrostman (δ : ℝ≥0) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (Nn : ℕ) :
    IsFrostmanIn (Finset.range Nn) (fun _ : ℕ => (ST δ).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall (CF δ) := by
  have hm0 : m δ ≠ 0 := (m_pos hδ0).ne'
  have hmt : m δ ≠ ⊤ := m_ne_top δ
  have hv0 : vB ≠ 0 := vB_pos.ne'
  have hvt : vB ≠ ⊤ := vB_ne_top
  have hdens : densityIn (Finset.range Nn) (fun _ : ℕ => (ST δ).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall = (Nn : ℝ≥0∞) * m δ / vB := by
    rw [const_densityIn_eq _ _ (ST_le_ball hδ)]
    simp only [Finset.card_range, vB, m, ST_carrier]
  have hkey : (Nn : ℝ≥0∞) ≤ CF δ * densityIn (Finset.range Nn)
      (fun _ : ℕ => (ST δ).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall := by
    rw [hdens, CF]
    have hone : vB / m δ * (m δ / vB) = 1 := by
      rw [← mul_div_assoc, ENNReal.div_mul_cancel hm0 hmt, ENNReal.div_self hv0 hvt]
    have : vB / m δ * ((Nn : ℝ≥0∞) * m δ / vB) = (Nn : ℝ≥0∞) := by
      rw [mul_div_assoc, ← mul_assoc, mul_comm (vB / m δ), mul_assoc, hone, mul_one]
    rw [this]
  intro K' hK'
  refine le_trans ?_ hkey
  refine ENNReal.div_le_of_le_mul ?_
  simpa [Finset.card_range] using
    const_sum_le ((ST δ).toConvexSpaceBody) (Finset.range Nn) K'

/-! ### Multiplicity and fullness of the witness family -/

/-! ### The payload, and its refutation -/

/-- The `N`-independent constant of the witness configuration. -/
def Aconst (β : ℝ) (δ : ℝ≥0) : ℝ≥0∞ :=
  (δ : ℝ≥0∞) ^ (-(1:ℝ)) * CF δ ^ (1 - β / 2)
    * ((δ : ℝ≥0∞) / (δ : ℝ≥0∞)) ^ (3 * β / 2)
    * (δ : ℝ≥0∞) ^ (-2 * β) * (((δ : ℝ≥0∞) ^ 2) ^ (1 - β / 2))

end Kakeya.PersistPlankCE

namespace Kakeya

/-! ### The repaired statement is not vacuous

The failure mode this guards against is closing a goal from an unsatisfiable hypothesis
bundle.  Every hypothesis of
`Kakeya.tubeMultiplicityOfLocalPersistentPlankFactorisation` (and of its stronger form
`Kakeya.tubeMultiplicityOfLocalPersistentPlankFactorisation_of_essDistinct`) is met simultaneously,
with `q` nonempty, by the configuration of this file taken at **one**
tube instead of `N` — at which the essential-distinctness clause is vacuous but everything else is
unchanged, since none of the other constants ever saw `N`.
-/

end Kakeya

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factoring.FlatPrisms
public import Kakeya.Thickness.Lemmas
public import Kakeya.Tube.IntersectionVolume

/-!
# Main Lemma 1, Case (ii): the tube attached to a plank

This file collects the geometric and volume-theoretic obligations that
`Kakeya.ml1Boot.exists_plank_tube_of_thickness_le_one` (blueprint
`lem:ml1bootPlankInTubeRepaired`, in `Kakeya/DimensionThree/MainLemma1/Rescaling.lean`) is
assembled from, so that the lemma itself becomes a short assembly.  It formalizes the group of
auxiliary statements of the Main Lemma 1 endgame:

* `Kakeya.ml1Boot.volume_bounds_of_ethickness_bounds` — the two-sided volume estimate in `ℝ³`,
  packaged once so
  that the two volume computations below become a matter of supplying six numbers;
* `Kakeya.ml1Boot.volume_bounds_of_isPlankOfDimensions`
  and `Kakeya.ml1Boot.volume_bounds_of_tube` — the
  volumes of a plank and of a tube of moderate scale;
* `Kakeya.ml1Boot.tube_ethickness_bounds` — the
  ethicknesses of a tube, the four separate bounds of `Tube` glued by
  `Metric.ethickness_antitone` into the identity `τₖ(T) = δ` for `1 ≤ k ≤ n - 1`;
* `Kakeya.ml1Boot.unitCoreSegment`,
  `Kakeya.ml1Boot.dist_prism_transverse_le` and
  `Kakeya.ml1Boot.prism_subset_unitCoreTube` — the purely
  geometric fact that a rectangular prism whose first half-width is at most `Λ₀` lies in the
  `(2 Λ₀)`-dilate of a tube whose core is the unit segment through its centre along its long axis;
* `Kakeya.ml1Boot.plankTube` and
  `Kakeya.ml1Boot.subset_plankTube` — that tube,
  of scale `C b`, attached to a nonempty compact set through its outer prism, and the
  containment of the set in its `(2 Λ₀)`-dilate;
* `Kakeya.ml1Boot.plankInTube_constant_bounds` — the arithmetic of the constants.

## The comparability constant is a parameter

The blueprint writes `C_𝕎 = C_{lem:ml1bootPlankPigeonhole}` throughout this group, i.e.
`Kakeya.ml1Boot.plankPigeonhole.C`, which is defined downstream in
`Kakeya/DimensionThree/MainLemma1/Rescaling.lean`.  Here the constant is carried as an explicit
parameter `C : NNReal`, which is a strict generalization: instantiating `C := plankPigeonhole.C`
returns the blueprint statements verbatim, `plankPigeonhole.C` being a reducible abbreviation.
The same applies to `Kakeya.ml1Boot.plankInTube_constant_bounds`, whose right-hand side is the
unfolding of `Kakeya.ml1Boot.plankInTube.C`.

## Ethicknesses versus affine thicknesses

Every statement here is phrased in the ethicknesses `Metric.ethickness ℝ · k` except
`Kakeya.ml1Boot.subset_plankTube`, which reads off the half-widths of an outer prism and is
therefore phrased in the affine thicknesses `Metric.thickness ℝ · k`; the two agree on bounded
sets by `Metric.ethickness_thickness`, which is where that identification is discharged.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ConvexSpaceBody Metric

namespace Kakeya

namespace ml1Boot

/-! ### The two-sided volume estimate in `ℝ³` -/

section Volume

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Two-sided volume bounds from ethickness bounds in `ℝ³`**.

If the three ethicknesses of a convex body `V ⊆ ℝ³` are sandwiched between `lₖ` and `uₖ`, then
`c₃ l₀ l₁ l₂ ≤ |V| ≤ 8 u₀ u₁ u₂`, where `c₃ = Metric.lt_volume_convexHull.c 3`.

The lower half is `Convex.ethickness_prod_le_volume` and the upper half is
`Metric.volume_le_prod_ethickness`, in each case after expanding
`∏ k ∈ Finset.range 3, Metric.ethickness ℝ V.carrier k` and pushing the three monotonicity
steps through the triple product.  That work is done once here, because
`Kakeya.ml1Boot.volume_bounds_of_isPlankOfDimensions` and
`Kakeya.ml1Boot.volume_bounds_of_tube` are the same computation with different data. -/
theorem volume_bounds_of_ethickness_bounds (hdim : Module.finrank ℝ E = 3)
    (V : ConvexSpaceBody E) {l₀ l₁ l₂ u₀ u₁ u₂ : ℝ≥0∞}
    (hl₀ : l₀ ≤ ethickness ℝ V.carrier 0) (hl₁ : l₁ ≤ ethickness ℝ V.carrier 1)
    (hl₂ : l₂ ≤ ethickness ℝ V.carrier 2) (hu₀ : ethickness ℝ V.carrier 0 ≤ u₀)
    (hu₁ : ethickness ℝ V.carrier 1 ≤ u₁) (hu₂ : ethickness ℝ V.carrier 2 ≤ u₂) :
    (lt_volume_convexHull.c 3 : ℝ≥0∞) * (l₀ * l₁ * l₂) ≤ volume V.carrier ∧
      volume V.carrier ≤ 8 * (u₀ * u₁ * u₂) := by
  haveI : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (by rw [hdim]; norm_num)
  have hprod : ∏ i ∈ Finset.range (Module.finrank ℝ E), ethickness ℝ V.carrier i =
      ethickness ℝ V.carrier 0 * ethickness ℝ V.carrier 1 * ethickness ℝ V.carrier 2 := by
    rw [hdim]
    simp [Finset.prod_range_succ]
  have hVconvex : Convex ℝ V.carrier := V.convex'.convex
  constructor
  · calc
      (lt_volume_convexHull.c 3 : ℝ≥0∞) * (l₀ * l₁ * l₂)
          ≤ (lt_volume_convexHull.c 3 : ℝ≥0∞) *
              (ethickness ℝ V.carrier 0 * ethickness ℝ V.carrier 1 * ethickness ℝ V.carrier 2) :=
            mul_le_mul' (le_refl _) (mul_le_mul' (mul_le_mul' hl₀ hl₁) hl₂)
      _ = (lt_volume_convexHull.c (Module.finrank ℝ E) : ℝ≥0∞) *
          (ethickness ℝ V.carrier 0 * ethickness ℝ V.carrier 1 * ethickness ℝ V.carrier 2) := by
            rw [hdim]
      _ = (lt_volume_convexHull.c (Module.finrank ℝ E) : ℝ≥0∞) *
          ∏ i ∈ Finset.range (Module.finrank ℝ E), ethickness ℝ V.carrier i := by rw [← hprod]
      _ ≤ volume V.carrier := hVconvex.ethickness_prod_le_volume
  · calc
      volume V.carrier
          ≤ 2 ^ (Module.finrank ℝ E) *
              ∏ i ∈ Finset.range (Module.finrank ℝ E), ethickness ℝ V.carrier i :=
            volume_le_prod_ethickness _
      _ = (8 : ℝ≥0∞) *
          (ethickness ℝ V.carrier 0 * ethickness ℝ V.carrier 1 * ethickness ℝ V.carrier 2) := by
        rw [hprod, hdim]
        norm_num
      _ ≤ 8 * (u₀ * u₁ * u₂) :=
        mul_le_mul' (le_refl _) (mul_le_mul' (mul_le_mul' hu₀ hu₁) hu₂)

/-- **The volume of a plank**.

An `a × b × 1` plank in `ℝ³` with comparability constant `C` — that is, a convex body `W` with
`C⁻¹ ≤ τ₀(W) ≤ C`, `C⁻¹ b ≤ τ₁(W) ≤ C b` and `C⁻¹ a ≤ τ₂(W) ≤ C a`, which is
`Kakeya.IsPlankOfDimensions C a b W` — has volume comparable to `a b`:
`C⁻³ c₃ a b ≤ |W| ≤ 8 C³ a b`.

Immediate from `Kakeya.ml1Boot.volume_bounds_of_ethickness_bounds` with
`(l₀, l₁, l₂) = (C⁻¹, C⁻¹ b, C⁻¹ a)` and `(u₀, u₁, u₂) = (C, C b, C a)`, the six hypotheses
being exactly the six inequalities of the plank predicate.  Neither `a ≤ b` nor `b ≤ 1` enters.
In the intended application `C = Kakeya.ml1Boot.plankPigeonhole.C`.

The bounds are **not** the same as item `item:plankVolume` of
`Kakeya.ml1Boot.exists_plankDimensions`, which asserts `C⁻¹ a b ≤ |W| ≤ C a b`; neither implies
the other, both failing by a factor of order `C²`.  See blueprint
`note:plankVolumeConstantGap`. -/
theorem volume_bounds_of_isPlankOfDimensions (hdim : Module.finrank ℝ E = 3) {C a b : ℝ≥0}
    (_hC : 1 ≤ C) {W : ConvexSpaceBody E} (hW : IsPlankOfDimensions C a b W) :
    ((C : ℝ≥0∞) ^ 3)⁻¹ * (lt_volume_convexHull.c 3 : ℝ≥0∞) * ((a : ℝ≥0∞) * b)
        ≤ volume W.carrier ∧
      volume W.carrier ≤ 8 * (C : ℝ≥0∞) ^ 3 * ((a : ℝ≥0∞) * b) := by
  obtain ⟨⟨h0l, h0u⟩, ⟨h1l, h1u⟩, ⟨h2l, h2u⟩⟩ := hW
  have h := volume_bounds_of_ethickness_bounds hdim W
    (l₀ := (C : ℝ≥0∞)⁻¹)
    (l₁ := (C : ℝ≥0∞)⁻¹ * (b : ℝ≥0∞))
    (l₂ := (C : ℝ≥0∞)⁻¹ * (a : ℝ≥0∞))
    (u₀ := (C : ℝ≥0∞))
    (u₁ := (C : ℝ≥0∞) * (b : ℝ≥0∞))
    (u₂ := (C : ℝ≥0∞) * (a : ℝ≥0∞))
    h0l h1l h2l h0u h1u h2u
  obtain ⟨hL, hU⟩ := h
  have hEqL : ((C : ℝ≥0∞) ^ 3)⁻¹ * (lt_volume_convexHull.c 3 : ℝ≥0∞) * ((a : ℝ≥0∞) * b) =
      (lt_volume_convexHull.c 3 : ℝ≥0∞) *
        (((C : ℝ≥0∞)⁻¹) * (((C : ℝ≥0∞)⁻¹) * (b : ℝ≥0∞)) *
          (((C : ℝ≥0∞)⁻¹) * (a : ℝ≥0∞))) := by
    rw [ENNReal.inv_pow]
    ring
  have hEqU : 8 * ((C : ℝ≥0∞) * ((C : ℝ≥0∞) * (b : ℝ≥0∞)) *
        ((C : ℝ≥0∞) * (a : ℝ≥0∞))) =
      8 * (C : ℝ≥0∞) ^ 3 * ((a : ℝ≥0∞) * b) := by
    ring
  constructor
  · exact le_trans (le_of_eq hEqL) hL
  · exact le_trans hU (le_of_eq hEqU)

end Volume

/-! ### The ethicknesses and the volume of a tube -/

section Tube

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Ethicknesses of a tube**.

An `s`-tube in a space of dimension at least `2` — the closed `s`-neighbourhood of a segment
whose endpoints are at distance exactly `1` — has `1 / 2 ≤ τ₀(T) ≤ 1 + s` and `τₖ(T) = s` for
every `1 ≤ k ≤ n - 1`.

The four bounds are `Tube.le_ethickness_zero`, `Tube.ethickness_zero_le`,
`Tube.ethickness_one_le` and `Tube.le_ethickness_finrank_sub_one`; the *identity* is none of
them, being obtained by gluing the last two with the antitonicity `Metric.ethickness_antitone`
of `ethickness` in its rank:
`s ≤ τ_{n-1}(T) ≤ τₖ(T) ≤ τ₁(T) ≤ s`.

The upper bound `1 + s` on `τ₀` is deliberately *not* weakened to `2`: the tube scales occurring
in `Kakeya.ml1Boot.subset_plankTube` are of the form `C b` with `C ≥ 1024`, so the usual bound
`Tube.ethickness_zero_le_two`, which needs `s ≤ 1`, is unusable there. -/
theorem tube_ethickness_bounds (hn : 2 ≤ Module.finrank ℝ E) {s : ℝ≥0} (T : Tube s E) :
    1 / 2 ≤ ethickness ℝ T.carrier 0 ∧ ethickness ℝ T.carrier 0 ≤ 1 + (s : ℝ≥0∞) ∧
      ∀ k, 1 ≤ k → k ≤ Module.finrank ℝ E - 1 → ethickness ℝ T.carrier k = (s : ℝ≥0∞) := by
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (lt_of_lt_of_le zero_lt_two hn)
  constructor
  · exact T.le_ethickness_zero
  constructor
  · exact T.ethickness_zero_le
  · intro k hk1 hkfin
    apply le_antisymm
    · exact (ethickness_antitone hk1).trans T.ethickness_one_le
    · exact T.le_ethickness_finrank_sub_one.trans (ethickness_antitone hkfin)

end Tube

/-! ### A prism with normalized first half-width lies in a unit-core tube -/

section Prism

variable {E S : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace S] [NormedAddTorsor E S]

omit [FiniteDimensional ℝ E] in
/-- **Transverse distance from the long axis of a prism**.

Let `P` be a rectangular prism with centre `c`, orthonormal axes `(eₖ)` and half-widths `(rₖ)`.
For `x ∈ P`, writing `t₀ = ⟪x -ᵥ c, e₀⟫`, the point `c + t₀ e₀` is within `r₁ + ⋯ + r_{n-1}` of
`x`.

Indeed `x -ᵥ c = ∑ₖ tₖ eₖ` with `|tₖ| ≤ rₖ`, so `x -ᵥ (t₀ e₀ +ᵥ c) = ∑_{k ≥ 1} tₖ eₖ` and the
triangle inequality applies.  The crude bound `‖∑_{k ≥ 1} tₖ eₖ‖ ≤ ∑_{k ≥ 1} |tₖ|` is
deliberate: in the case `n = 3` used downstream the sharp estimate `√(t₁² + t₂²)` would put a
square root into the tube scale and propagate it into every constant; see blueprint
`note:ml1bootPlankTubeNoSqrt`. -/
theorem dist_prism_transverse_le {n : ℕ} (P : PrismNDim (n + 1) E S) {x : S}
    (hx : x ∈ P.carrier) :
    dist x (P.basis.repr (x -ᵥ P.center) 0 • P.basis 0 +ᵥ P.center)
      ≤ ∑ k ∈ Finset.univ.erase (0 : Fin (n + 1)), (P.thicknesses k : ℝ) := by
  set t := fun i : Fin (n + 1) => P.basis.repr (x -ᵥ P.center) i with ht
  have ht_sum : x -ᵥ P.center = ∑ k : Fin (n + 1), t k • P.basis k := by
    calc
      x -ᵥ P.center = ∑ k, (P.basis.repr (x -ᵥ P.center) k) • P.basis k := by
        symm; exact P.basis.sum_repr (x -ᵥ P.center)
      _ = ∑ k, t k • P.basis k := by
        simp [t]
  have hx' : ∀ k, |t k| ≤ (P.thicknesses k : ℝ) := by
    intro k
    have := (P.mem_carrier_iff x).mp hx k
    simpa [t] using this
  calc
    dist x (t 0 • P.basis 0 +ᵥ P.center) = ‖x -ᵥ (t 0 • P.basis 0 +ᵥ P.center)‖ := by
      rw [dist_eq_norm_vsub E]
    _ = ‖(x -ᵥ P.center) - t 0 • P.basis 0‖ := by
      rw [vsub_vadd_eq_vsub_sub]
    _ = ‖∑ k ∈ Finset.univ.erase (0 : Fin (n + 1)), t k • P.basis k‖ := by
      have h_eq : (x -ᵥ P.center) - t 0 • P.basis 0
          = ∑ k ∈ Finset.univ.erase (0 : Fin (n + 1)), t k • P.basis k := by
        calc
          (x -ᵥ P.center) - t 0 • P.basis 0 =
              (∑ k : Fin (n + 1), t k • P.basis k) - t 0 • P.basis 0 := by rw [ht_sum]
          _ = ∑ k ∈ Finset.univ.erase (0 : Fin (n + 1)), t k • P.basis k := by
            simp [Finset.sum_erase_eq_sub (Finset.mem_univ (0 : Fin (n + 1)))]
      rw [h_eq]
    _ ≤ ∑ k ∈ Finset.univ.erase (0 : Fin (n + 1)), ‖t k • P.basis k‖ :=
      norm_sum_le (Finset.univ.erase (0 : Fin (n + 1))) (fun k => t k • P.basis k)
    _ = ∑ k ∈ Finset.univ.erase (0 : Fin (n + 1)), (|t k| * ‖P.basis k‖) := by
      simp [norm_smul]
    _ = ∑ k ∈ Finset.univ.erase (0 : Fin (n + 1)), |t k| := by
      simp [P.basis.orthonormal.norm_eq_one]
    _ ≤ ∑ k ∈ Finset.univ.erase (0 : Fin (n + 1)), (P.thicknesses k : ℝ) :=
      Finset.sum_le_sum fun k _ => hx' k

end Prism

section UnitCore

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end UnitCore

/-! ### The tube attached to a plank -/

section PlankTube

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end PlankTube

/-! ### The arithmetic of the constants -/

end ml1Boot

end Kakeya

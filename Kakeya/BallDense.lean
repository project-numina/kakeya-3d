/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionN.Volume
public import Kakeya.Mathlib.Topology.CoveringNumber
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Ball density at a scale

GWZ compress the geometric input of Lemma 5.8 into the single clause
`|A(W)| ≲ |Y_𝒲(W)|` "because `|W ∩ B| ≳ |B|` for every ball `B` of radius `w₁` with centre in
`W`".  This file isolates the shape hypothesis that clause presupposes, `Metric.IsBallDense`,
verifies it for rectangular prisms, and proves the covering/packing comparison that uses it:
for a `β`-ball dense compact set `W` at scale `r` and a measurable `A ⊆ W`,
`|N_{λ r}(A)| ≤ C(n, λ, β) · |W ∩ N_r(A)|`.

Ball density is *not* automatic for a convex body (a thin triangle in the plane fails it at
its own apex at the scale of its smallest affine thickness), which is why it has to be carried
as a hypothesis; see the blueprint note `note:ballDenseNotAutomatic`.
-/

@[expose] public section

open scoped NNReal ENNReal

open Metric MeasureTheory

/-! ### Boxes in an orthonormal frame -/

section Box

variable {n : ℕ} {E S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [PseudoMetricSpace S] [NormedAddTorsor E S]

end Box

section BoxVolume

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end BoxVolume

/-! ### Ball density -/

namespace Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]

/-- Blueprint `def:ballDense`: `W` is **`β`-ball dense at scale `r`** if
`|W ∩ B̄(x, s)| ≥ β · sⁿ` for every `x ∈ W` and every `0 < s ≤ r`, where `n` is the dimension
of the ambient Euclidean space.

This is the precise content of GWZ's parenthetical "`W` has dimensions roughly
`w₁ × ⋯ × wₙ`": the body is not allowed to taper away at any of its own points on scales
below `r`.  The density constant is written `β`, not `κ`, because in GWZ Section 5 the letter
`κ` already denotes the dimensional volume-comparison constant between a convex body and its
outer prism. -/
def IsBallDense (W : Set E) (r : ℝ) (β : ℝ≥0) : Prop :=
  ∀ ⦃x⦄, x ∈ W → ∀ ⦃s : ℝ⦄, 0 < s → s ≤ r →
    (β : ℝ≥0∞) * ENNReal.ofReal (s ^ Module.finrank ℝ E) ≤ volume (W ∩ Metric.closedBall x s)

/-- Ball density at a scale implies ball density, with the same constant, at every smaller
positive scale. -/
theorem IsBallDense.mono_scale {W : Set E} {r r' : ℝ} {β : ℝ≥0} (h : IsBallDense W r β)
    (hr : r' ≤ r) : IsBallDense W r' β :=
  fun _ hx _ hs hsr => h hx hs (hsr.trans hr)

end Metric

/-! ### Rectangular prisms are ball dense -/

namespace PrismNDim

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Blueprint `def:prismBallDenseConstant`: the ball-density constant of a rectangular prism,
`c(n) = n ^ (-n / 2)`.  It is positive and depends only on the ambient dimension `n`. -/
noncomputable abbrev isBallDense_carrier.c (n : ℕ) : ℝ≥0 :=
  ⟨(Real.sqrt n)⁻¹ ^ n, by positivity⟩

theorem isBallDense_carrier.c_pos (n : ℕ) : 0 < isBallDense_carrier.c n := by
  rw [← NNReal.coe_lt_coe]
  change (0 : ℝ) < (Real.sqrt n)⁻¹ ^ n
  rcases n with _ | m
  · simp
  · positivity

end PrismNDim

/-! ### Separated subsets, coverings, and the volume comparison -/

namespace Metric

/-- Blueprint `lem:maximalSeparatedSubset`: a nonempty bounded set in a proper metric space
admits a finite nonempty `r`-separated subset which is also an `r`-cover of it.

This is `Metric.maximalSeparatedSet` packaged as a `Finset`; finiteness comes from finiteness
of the packing number of a bounded set. -/
theorem exists_finset_separated_cover {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    {A : Set X} (hAne : A.Nonempty) (hA : Bornology.IsBounded A) {r : ℝ} (hr : 0 < r) :
    ∃ T : Finset X, (T : Set X) ⊆ A ∧ T.Nonempty ∧
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y → r < dist x y) ∧
      A ⊆ ⋃ x ∈ T, Metric.closedBall x r := by
  let ε : ℝ≥0 := r.toNNReal
  have hεr : (ε : ℝ) = r := by
    dsimp [ε]
    exact Real.coe_toNNReal r (le_of_lt hr)
  have hε0 : (0 : ℝ≥0) < ε := by
    dsimp [ε]
    exact Real.toNNReal_pos.mpr hr
  -- Step 1: the packing number is finite.
  have hpack : Metric.packingNumber ε A ≠ ⊤ := by
    have h2e : (2 : ℝ≥0) * (ε / 2) = ε := by
      have h2ne : (2 : ℝ≥0) ≠ 0 := by norm_num
      calc
        (2 : ℝ≥0) * (ε / 2) = (2 : ℝ≥0) * (ε * (2 : ℝ≥0)⁻¹) := by rw [div_eq_mul_inv]
        _ = ε * ((2 : ℝ≥0) * (2 : ℝ≥0)⁻¹) := by ring
        _ = ε := by rw [mul_inv_cancel₀ h2ne, mul_one]
    have h1 : Metric.packingNumber ε A ≤ Metric.externalCoveringNumber (ε / 2) A := by
      have hstep := Metric.packingNumber_two_mul_le_externalCoveringNumber (ε / 2) A
      rwa [h2e] at hstep
    have h2 : Metric.externalCoveringNumber (ε / 2) A ≤ Metric.coveringNumber (ε / 2) A :=
      Metric.externalCoveringNumber_le_coveringNumber (ε / 2) A
    have hle : Metric.packingNumber ε A ≤ Metric.coveringNumber (ε / 2) A := h1.trans h2
    have hεhalf : (0 : ℝ≥0) < ε / 2 := by
      rw [← NNReal.coe_lt_coe]
      rw [NNReal.coe_div]
      rw [show ((2 : ℝ≥0) : ℝ) = 2 by norm_num]
      exact half_pos (by simpa [hεr] using hr)
    have h3 : Metric.coveringNumber (ε / 2) A ≠ ⊤ := hA.coveringNumber_ne_top hεhalf
    exact ne_of_lt (lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr h3))
  -- Steps 2-3: the maximal separated set is finite.
  have hfin : (Metric.maximalSeparatedSet ε A).Finite := by
    rw [← Set.encard_ne_top_iff]
    rw [Metric.encard_maximalSeparatedSet hpack]
    exact hpack
  lift Metric.maximalSeparatedSet ε A to Finset X using hfin with T hT
  -- Step 6: `T` is nonempty, since it covers the nonempty set `A`.
  have hcovM : A ⊆ ⋃ y ∈ Metric.maximalSeparatedSet ε A, Metric.closedBall y (ε : ℝ) := by
    exact (Metric.isCover_iff_subset_iUnion_closedBall).mp
      (Metric.isCover_maximalSeparatedSet hpack)
  have hneM : (Metric.maximalSeparatedSet ε A).Nonempty := by
    rcases hAne with ⟨a, ha⟩
    rcases Set.mem_iUnion.mp (hcovM ha) with ⟨y, hy⟩
    rcases Set.mem_iUnion.mp hy with ⟨hyM, _⟩
    exact ⟨y, hyM⟩
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  · rw [hT]
    exact Metric.maximalSeparatedSet_subset
  · change (T : Set X).Nonempty
    simpa [← hT] using hneM
  · intro x hx y hy hxy
    have hsepT : Metric.IsSeparated (ε : ℝ≥0∞) (T : Set X) := by
      simpa [hT] using
        (Metric.isSeparated_maximalSeparatedSet : Metric.IsSeparated (ε : ℝ≥0∞)
          (Metric.maximalSeparatedSet ε A))
    have he : (ε : ℝ≥0∞) < edist x y := hsepT hx hy hxy
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal (p := ε)] at he
    have hre : (ε : ℝ) < dist x y :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ε.prop).mp he
    simpa [hεr] using hre
  · simpa [← hT, hεr] using hcovM

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]

/-- Blueprint `def:thickeningBallDenseComparisonConstant`: the constant in
`Metric.volume_cthickening_le_of_isBallDense`,
`C(n, λ, β) = β⁻¹ · ωₙ · 3ⁿ · (λ + 1)ⁿ`, where `ωₙ = √π ^ n / Γ(n / 2 + 1)` is the volume of
the closed unit ball of an `n`-dimensional Euclidean space.  It depends only on the ambient
dimension `n`, on the dilation factor `λ`, and on the ball-density constant `β`. -/
noncomputable abbrev volume_cthickening_le_of_isBallDense.C (n : ℕ) (lam β : ℝ≥0) : ℝ≥0 :=
  β⁻¹ * ⟨Real.sqrt Real.pi ^ n / Real.Gamma (n / 2 + 1), by positivity⟩ * 3 ^ n * (lam + 1) ^ n

end Metric

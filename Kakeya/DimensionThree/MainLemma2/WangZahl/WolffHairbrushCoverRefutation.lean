/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.WangZahl.WolffHairbrushGuardrails

/-!
# The `θ`-tube cover leaf cannot manufacture broad classes

`Kakeya.WangZahl.CappedBalancedBroadCover` (Leaf 1b of the Wang--Zahl
Proposition 1.10 decomposition) asks: given a `δ^η`-dense, Katz--Tao bounded
family that is cap-concentrated and `ν`-broad at a scale `θ ∈ [δ, 1]`, produce a
balanced cover of the family by `θ`-tubes together with per-class shadings so
that *each class is again `ν`-broad at scale `θ`*.

This file records the obstruction, and it is a *fourth* instance of the defect
class that already produced `not_balancedBroadCover` and the two repairs of
`WolffHairbrushBroad`: **the transcription kept one half of a source clause and
dropped the other.**

## The source

Wang--Zahl state

> Furthermore, there exists a balanced partitioning cover `𝕋_θ` of `𝕋`, so that
> `|⋃_{T ∈ 𝕋} Y(T)| = ∑_{T_θ ∈ 𝕋_θ} |⋃_{T ∈ 𝕋[T_θ]} Y(T)|`.  (broadAtScaleTheta)
> After a further refinement, we may suppose that each set `𝕋^{T_θ}` is
> `δ^{3η}`-dense.  Note that `𝕋^{T_θ}` [...] satisfies the broadness condition
> [...].

and Wang--Zahl define a *partitioning cover*: a cover in which each
`U ∈ 𝒰` lies in exactly one `𝒰[W]`.  So `broadAtScaleTheta` carries **two**
statements: the cover partitions the *tubes*, and — this is the content of the
displayed equality, not of the word "cover" — each *point* of `⋃ Y(T)` is
counted once, i.e. the tubes through a typical point are captured by a single
`θ`-tube of the cover.  The Lean transcription rendered the display as the
output inequality

`∑_j |⋃_{i ∈ part j} Y_j(i)| ≤ |⋃_{i ∈ s} Y(i)|`,

which is satisfiable by *shrinking* the shadings and therefore no longer says
that a point's tubes lie in one class.  With that clause gone, the leaf demands
per-class broadness while granting nothing that ties a point's tubes to a
single class — and it is then false.

## The obstruction

Broadness at scale `θ > δ` is a pointwise multiplicity lower bound
(`rpow_le_multiplicity_of_isBroadAtScale`): every point of every shading of a
`ν`-broad family must lie in at least `(θ/δ)^ν > 1` tubes *of its own class*.
A class of the cover, however, is a set of `δ`-tubes contained in one *unit
length* `θ`-tube (`parent j : Tube θ Space3`), so two tubes of a class have
carriers inside a common set of diameter `1 + 2θ`.  Nothing in the hypotheses
of Leaf 1b prevents the tubes through a point from having pairwise *axial*
offsets `≫ θ`: cap concentration constrains only their **directions**.  A family
in which no two tubes share a `θ`-tube therefore has only singleton classes,
and a singleton class is never broad at a scale `θ > δ`.

`not_cappedBalancedBroadCover_of_axiallySpread` is that argument.  It reduces
the refutation of Leaf 1b to the construction of one witness family, which is
`Kakeya.WangZahl.axialFamily` below.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Metric

namespace Kakeya.WangZahl

noncomputable section

universe u

/-! ### A class holding at most one tube is never broad above `δ` -/

/-! ### Two tubes in a common `θ`-tube are close

A `Tube θ` has diameter at most `1 + 2θ`: its carrier is the `θ`-thickening of a
segment of length one. -/

/-! ### The reduction: an axially spread family refutes Leaf 1b -/

/-! ### Four directions on the boundary of a `θ`-cap -/

/-- The axial component of the four witness directions. -/
def capA (θ : ℝ≥0) : ℝ := 1 - (θ : ℝ) ^ 2 / 2

/-- The transverse component of the four witness directions. -/
def capB (θ : ℝ≥0) : ℝ := (θ : ℝ) * Real.sqrt (1 - (θ : ℝ) ^ 2 / 4)

/-- First transverse coefficient of the `k`-th witness direction. -/
def capC : Fin 4 → ℝ := ![1, -1, 0, 0]

/-- Second transverse coefficient of the `k`-th witness direction. -/
def capS : Fin 4 → ℝ := ![0, 0, 1, -1]

/-- The four unit vectors at chordal distance exactly `θ` from `capAxis`, forming
a square inscribed in the boundary circle of the `θ`-cap. -/
def capDir (θ : ℝ≥0) (k : Fin 4) : Space3 :=
  !₂[capA θ, capB θ * capC k, capB θ * capS k]

theorem norm_coord (x y z : ℝ) : ‖(!₂[x, y, z] : Space3)‖ = Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_three, sq_abs]

theorem capCS_sq (k : Fin 4) : capC k ^ 2 + capS k ^ 2 = 1 := by
  fin_cases k <;> norm_num [capC, capS]

variable {θ : ℝ≥0}

theorem capB_sq (hθ : (θ : ℝ) ≤ 2) : capB θ ^ 2 = (θ : ℝ) ^ 2 * (1 - (θ : ℝ) ^ 2 / 4) := by
  have hnn : (0 : ℝ) ≤ 1 - (θ : ℝ) ^ 2 / 4 := by nlinarith [θ.coe_nonneg]
  rw [capB, mul_pow, Real.sq_sqrt hnn]

theorem capA_sq_add_capB_sq (hθ : (θ : ℝ) ≤ 2) : capA θ ^ 2 + capB θ ^ 2 = 1 := by
  rw [capB_sq hθ, capA]; ring

theorem norm_capDir (hθ : (θ : ℝ) ≤ 2) (k : Fin 4) : ‖capDir θ k‖ = 1 := by
  rw [capDir, norm_coord]
  have h : capA θ ^ 2 + (capB θ * capC k) ^ 2 + (capB θ * capS k) ^ 2 = 1 := by
    have h1 := capCS_sq k
    have h2 := capA_sq_add_capB_sq (θ := θ) hθ
    nlinarith [h1, h2]
  rw [h, Real.sqrt_one]

/-! ### The direction count of the witness family

`capDirCount θ w r` is the number of witness directions within chordal distance
`r` of `± w`.  The two lemmas below are the only geometric input to the
broadness verification. -/

/-! ### The witness family: four `δ`-tubes with `θ = 100 δ` -/

/-- The scale of the witness: `θ = 200 δ`, truncated at `1` so that the
directions are unconditionally unit vectors. -/
def capTheta (δ : ℝ≥0) : ℝ≥0 := min (200 * δ) 1

theorem capTheta_le_one (δ : ℝ≥0) : (capTheta δ : ℝ) ≤ 1 := by
  rw [capTheta]
  exact_mod_cast min_le_right (200 * δ) 1

/-- The `k`-th direction of the witness family. -/
def axialDir (δ : ℝ≥0) (k : Fin 4) : Space3 := capDir (capTheta δ) k

theorem norm_axialDir (δ : ℝ≥0) (k : Fin 4) : ‖axialDir δ k‖ = 1 :=
  norm_capDir (le_trans (capTheta_le_one δ) (by norm_num)) k

/-- The axial offsets: the origin sits at parameter `capLam k` along the `k`-th
axis, and the four offsets are `1/5` apart. -/
def capLam : Fin 4 → ℝ := ![1/10, 3/10, 5/10, 7/10]

/-- The `k`-th tube of the witness family: the `δ`-tube whose axis is the unit
segment through the origin in direction `axialDir δ k`, with the origin at
parameter `capLam k`. -/
def axialTube (δ : ℝ≥0) (k : Fin 4) : Tube δ Space3 :=
  Tube.mk' δ (x := -(capLam k) • axialDir δ k) (y := (1 - capLam k) • axialDir δ k)
    (by
      rw [dist_eq_norm,
        show -(capLam k) • axialDir δ k - (1 - capLam k) • axialDir δ k
          = -axialDir δ k by module, norm_neg]
      exact norm_axialDir δ k)

theorem axialTube_x (δ : ℝ≥0) (k : Fin 4) :
    (axialTube δ k).x = -(capLam k) • axialDir δ k := rfl

theorem axialTube_y (δ : ℝ≥0) (k : Fin 4) :
    (axialTube δ k).y = (1 - capLam k) • axialDir δ k := rfl

/-! ### The shading: one box inside all four tubes -/

/-! ### The witness family as a shaded family -/

/-! ### Cap concentration holds with equality -/

/-! ### No `θ`-tube holds two tubes of the family -/

theorem x_mem_carrier {δ : ℝ≥0} (hδ : 0 < δ) (T : Tube δ Space3) : T.x ∈ T.carrier := by
  rw [T.carrier_eq]
  exact Set.mem_iUnion₂.mpr ⟨T.x, left_mem_segment ℝ T.x T.y,
    Metric.mem_closedBall_self (NNReal.coe_pos.mpr hδ).le⟩

theorem y_mem_carrier {δ : ℝ≥0} (hδ : 0 < δ) (T : Tube δ Space3) : T.y ∈ T.carrier := by
  rw [T.carrier_eq]
  exact Set.mem_iUnion₂.mpr ⟨T.y, right_mem_segment ℝ T.x T.y,
    Metric.mem_closedBall_self (NNReal.coe_pos.mpr hδ).le⟩

/-! ### Broadness of the witness family at quality `1/4` -/

variable {θ : ℝ≥0}

/-! ### The `ENNReal` arithmetic of the count -/

/-! ### Essential distinctness of the four tubes -/

/-- Every point of the `k`-th axis is `t • axialDir δ k` for `t ∈ [-λ_k, 1-λ_k]`. -/
theorem exists_param_of_mem_segment {δ : ℝ≥0} {k : Fin 4} {z : Space3}
    (hz : z ∈ segment ℝ (axialTube δ k).x (axialTube δ k).y) :
    ∃ t : ℝ, -capLam k ≤ t ∧ t ≤ 1 - capLam k ∧ z = t • axialDir δ k := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hsum, hz⟩ := hz
  refine ⟨c₂ - capLam k, by linarith, by linarith, ?_⟩
  rw [← hz, axialTube_x, axialTube_y, show c₁ = 1 - c₂ by linarith]
  module

/-! ### Axis-aligned coordinate boxes -/

/-! ### A wide box inside a `δ`-tube: `tubeVolume δ ≥ 1.96 δ²` -/

/-! ### The intersection of two tubes of the family is thin -/

/-! ### The remaining hypotheses of Leaf 1b -/

/-! ### The witness exists at every input quality, and Leaf 1b is false -/

end

end Kakeya.WangZahl

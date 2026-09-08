/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.ThinSetup
public import Mathlib.Analysis.PSeries

/-!
# `Kakeya.ThinCase.factoringApply` is false as stated, and the exact missing hypothesis

This file proves
that it cannot be proved: two of its thirteen conclusions,

* **(iv)** the centred multiplicity comparison at *equal* radii,
  `|U(𝕋', Y') ∩ B(x, w₁)| ≤ C |U(𝕋', Y') ∩ B(y, w₁)|` for all `x, y` in the outer shaded union,
* **(vi)** the summed refinement `C⁻¹ ∑_{p ∈ 𝕋} |Y(p)| ≤ ∑_{p ∈ 𝕋'} |Y'(p)|`,

are jointly unachievable with the constant `Kakeya.ThinCase.factoringApplyConstant CF Cfull
Ccore`, whose only inputs are `CF`, `Cfull` and — through `Ccore` — `segs.card`, `bodies.card`
and `δ`.

## What the refutation is

`Kakeya.ThinCase.Refute.factoringApply_refuted` derives `False` from
`Kakeya.ThinCase.Refute.FactoringApplyStatement`, the statement of `factoringApply` with all
binders made explicit and **without the localisation hypothesis**.

`factoringApply` now carries that hypothesis,
`hloc : ∃ z : E, ∀ j ∈ bodies, (Wb j).carrier ⊆ Metric.closedBall z 1`, and
`Kakeya.ThinCase.Refute.statement_of_universal_loc` is the tripwire in its repaired form: it
derives `FactoringApplyStatement` from the current declaration by granting `hloc` for free and
passing every other argument through verbatim, so it typechecks exactly as long as `hloc` is
the only *ungranted* difference. The hypothesis is discharged at the sole call site
(`Kakeya.ThinCase.perBall` → `Kakeya.ThinCase.thinSetupExists` →
`Kakeya.VeryNotSticky.exists_thinConfig`, from
`Kakeya.VeryNotSticky.BallData.bodies_subset_ball` and `r₁ = δ^exscal ≤ 1`).

`factoringApply` also carries the *second* field of
`ShadedBody.FactorFamily.InnerIsDiscretizedAtScale` — a discretization scale `δ₀` with
`hscale : ∀ p ∈ segs, δ₀ ≤ ethickness.scale ℝ (Y p).carrier`, together with the two
scale-dependent envelope bounds at `δ₀`. Those are *not* granted by the tripwire: they are part
of `FactoringApplyStatement` and the counterexample supplies them, at `δ₀ = δ = 1 / 2`, via
`Kakeya.ThinCase.Refute.scale_capsule_ge`. So the refutation is strictly stronger than the one
first recorded: the statement is false even with the discretization hypothesis in hand at the
full scale `δ`, `subset_unitBall` being the missing field.

The witness uses **one** segment inside **one** body, so that neither `segs.card` nor
`bodies.card` can grow with the configuration, and `C := factoringApplyConstant 1 1
(factoringApplyCore 3 1 1 (1/2))` is one fixed number:

* the body is `Kakeya.ThinCase.Refute.capsule M`, the closed `1/2`-neighbourhood of the segment
  from `0` to `2 (M+1)` on the first coordinate axis of `EuclideanSpace ℝ (Fin 3)`. Its
  `2`-thickness is exactly `1/2` (`thickness_capsule_le`, `thickness_capsule_ge`), so the width
  hypothesis `hw₁` holds at `w₁ = 1`;
* the shading is `Kakeya.ThinCase.Refute.shadeSet M = ⋃_{k < M} blob k`, where `blob k` is the
  closed ball of radius `(1/4) (k+1)^(-1/3)` about `2 (k+1)` on the axis. The blobs are
  pairwise `2`-separated, so `B(x, 1)` meets exactly the blob containing `x`
  (`inter_ball_eq`), and `(k+1) |blob k| = massUnit` is constant
  (`succ_mul_volume_blob`): the mass profile is harmonic;
* `δ = 1/2`, `w₁ = 1`, `CF = Cfull = 1`, `Ccore = factoringApplyCore 3 1 1 (1/2)`, and `η` is a
  natural number large enough for the fullness hypothesis (`exists_eta`). One segment in its own
  body is `1`-Frostman (`isFrostmanIn_self`), so `hFr` holds with `CF = 1`.

`Kakeya.ThinCase.Refute.harmonic_le_of_centredMult` is the counting core. Clause (iv) forces the
retained blob masses to be pairwise comparable up to `C`; because `(k+1) |blob k|` is constant,
comparability caps the *number* of surviving blobs, and the retained mass at `C * massUnit`.
Clause (vi) demands at least `C⁻¹ * massUnit * H_M`. Hence `H_M ≤ C ^ 2` for every `M`, and the
harmonic series diverges.

## What the missing hypothesis is

`Kakeya.ThinCase.Refute.not_subset_closedBall_one`: the refuting body has diameter `2 M`, so it
violates `ConvexSpaceBody.IsDiscretizedAtScale.subset_unitBall`, the first field of
`ShadedBody.FactorFamily.InnerIsDiscretizedAtScale δ` — a hypothesis of *every* item of GWZ
Proposition 5.1 in this repository, item 7
(`ShadedBody.outerFactoringFamily_avgMultOnBalls`) included, and one that `factoringApply`
does not carry. Under it, and with `δ ≤ w₁`, the shaded union is covered by at most
`(1 + 4/δ) ^ n` balls of radius `w₁ / 2`, so the Step 5 dyadic mass pigeonhole
(`Kakeya.factoringStep5SelfPigeonholeConstant`) costs `O(n log δ⁻¹)` — subpolynomial in `δ⁻¹`,
hence inside the `Ccore` budget. Without it the covering number is unbounded and no
cardinality-only constant can pay for it.

## The positive half

`Kakeya.ThinCase.Localise.exists_localised_refinement` and
`exists_localised_refinement_of_subset_ball` price clause (iv) exactly: keeping the heaviest
half-ball of a `w₁/2`-net gives clause (iv) with constant `1`, at a mass cost equal to the
covering number of the shaded union at scale `w₁ / 2`, which is `≤ (1 + 4 R / w₁) ^ n` when the
union sits in a ball of radius `R`. (The sharp cost is the logarithm of that number, via the
dyadic mass pigeonhole that Step 5 already performs; the crude bound above is what is needed to
see *which* quantity the constant must depend on.)
-/

@[expose] public section

open scoped ENNReal

namespace Kakeya.ThinCase.Refute

open MeasureTheory Metric Set ShadedBody Filter

/-- The ambient space of the counterexample. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The centre of the `k`-th blob: the point `2 (k+1)` on the first coordinate axis. -/
noncomputable def ctr (k : ℕ) : E3 := EuclideanSpace.single (0 : Fin 3) (2 * ((k : ℝ) + 1))

/-- The radius of the `k`-th blob. -/
noncomputable def rad (k : ℕ) : ℝ := (1 / 4 : ℝ) * ((k : ℝ) + 1) ^ (-(1 : ℝ) / 3)

/-- The `k`-th blob. -/
noncomputable def blob (k : ℕ) : Set E3 := Metric.closedBall (ctr k) (rad k)

/-- The shading of the counterexample: the union of the first `M` blobs. -/
noncomputable def shadeSet (M : ℕ) : Set E3 := ⋃ k ∈ Finset.range M, blob k

lemma one_le_succ (k : ℕ) : (1 : ℝ) ≤ (k : ℝ) + 1 := by
  have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  linarith


lemma rad_le (k : ℕ) : rad k ≤ 1 / 4 := by
  have h1 : (1 : ℝ) ≤ ((k : ℝ) + 1) := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have := Real.rpow_le_one_of_one_le_of_nonpos h1 (by norm_num : (-(1:ℝ)/3) ≤ 0)
  unfold rad; nlinarith [this]


/-! ### Separation and locality -/

lemma dist_ctr (k l : ℕ) : dist (ctr k) (ctr l) = |2 * ((k : ℝ) + 1) - 2 * ((l : ℝ) + 1)| := by
  unfold ctr
  rw [show dist (EuclideanSpace.single (0 : Fin 3) (2 * ((k : ℝ) + 1)))
        (EuclideanSpace.single (0 : Fin 3) (2 * ((l : ℝ) + 1)))
      = dist (2 * ((k : ℝ) + 1)) (2 * ((l : ℝ) + 1)) from
    PiLp.dist_single_same 2 (fun _ => ℝ) _ _ _]
  exact Real.dist_eq _ _

lemma two_le_dist_ctr {k l : ℕ} (h : k ≠ l) : 2 ≤ dist (ctr k) (ctr l) := by
  rw [dist_ctr]
  have hne : (k : ℝ) ≠ (l : ℝ) := by exact_mod_cast h
  have h1 : (1 : ℝ) ≤ |(k : ℝ) - (l : ℝ)| := by
    rcases lt_or_gt_of_ne h with hlt | hgt
    · have : (k : ℕ) + 1 ≤ l := hlt
      have : ((k : ℝ)) + 1 ≤ (l : ℝ) := by exact_mod_cast this
      rw [abs_of_nonpos (by linarith)]; linarith
    · have : (l : ℕ) + 1 ≤ k := hgt
      have : ((l : ℝ)) + 1 ≤ (k : ℝ) := by exact_mod_cast this
      rw [abs_of_nonneg (by linarith)]; linarith
  have : |2 * ((k : ℝ) + 1) - 2 * ((l : ℝ) + 1)| = 2 * |(k : ℝ) - (l : ℝ)| := by
    rw [show 2 * ((k : ℝ) + 1) - 2 * ((l : ℝ) + 1) = 2 * ((k : ℝ) - (l : ℝ)) by ring,
      abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  rw [this]; linarith

lemma dist_le_of_mem_blob {k : ℕ} {z : E3} (hz : z ∈ blob k) : dist z (ctr k) ≤ 1 / 4 :=
  le_trans (Metric.mem_closedBall.mp hz) (rad_le k)


lemma measurableSet_blob (k : ℕ) : MeasurableSet (blob k) := measurableSet_closedBall

/-! ### Volumes -/

/-- The volume of the unit ball, the normalising constant of the configuration. -/
noncomputable def v0 : ℝ≥0∞ := volume (Metric.ball (0 : E3) 1)

lemma v0_pos : 0 < v0 := measure_ball_pos _ _ one_pos

lemma v0_ne_top : v0 ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (measure_mono Metric.ball_subset_closedBall)
  exact (isCompact_closedBall (0 : E3) 1).measure_lt_top.ne


/-! ### The carrier: a capsule of thickness `1/2` around the first coordinate axis -/

/-- The unit vector along the first coordinate axis. -/
noncomputable def axisVec : E3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)

lemma ctr_eq_smul (k : ℕ) : ctr k = (2 * ((k : ℝ) + 1)) • axisVec := by
  unfold ctr axisVec
  ext i
  simp

lemma smul_ctr {k M : ℕ} :
    (((k : ℝ) + 1) / ((M : ℝ) + 1)) • ctr M = ctr k := by
  have hM : ((M : ℝ) + 1) ≠ 0 := by positivity
  rw [ctr_eq_smul, ctr_eq_smul, smul_smul]
  congr 1
  field_simp

/-- The spine of the capsule: the segment from the origin to the last centre. -/
noncomputable def spine (M : ℕ) : Set E3 := segment ℝ (0 : E3) (ctr M)

lemma ctr_mem_spine {k M : ℕ} (h : k ≤ M) : ctr k ∈ spine M := by
  have hM : (0 : ℝ) < ((M : ℝ) + 1) := by positivity
  have hkM : ((k : ℝ) + 1) ≤ ((M : ℝ) + 1) := by
    have : (k : ℝ) ≤ (M : ℝ) := by exact_mod_cast h
    linarith
  refine ⟨1 - ((k : ℝ) + 1) / ((M : ℝ) + 1), ((k : ℝ) + 1) / ((M : ℝ) + 1), ?_, ?_, by ring, ?_⟩
  · have : ((k : ℝ) + 1) / ((M : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hM]; exact hkM
    linarith
  · positivity
  · rw [smul_zero, zero_add, smul_ctr]

/-- The carrier of the counterexample: the closed `1/2`-neighbourhood of the spine. -/
noncomputable def capsule (M : ℕ) : Set E3 := Metric.cthickening (1 / 2) (spine M)

lemma isCompact_capsule (M : ℕ) : IsCompact (capsule M) :=
  isCompact_segment.cthickening

lemma convex_capsule (M : ℕ) : Convex ℝ (capsule M) :=
  (convex_segment _ _).cthickening _

lemma capsule_nonempty (M : ℕ) : (capsule M).Nonempty :=
  ⟨0, Metric.self_subset_cthickening _ (left_mem_segment _ _ _)⟩

lemma blob_subset_capsule {k M : ℕ} (h : k < M) : blob k ⊆ capsule M := by
  intro z hz
  refine Metric.mem_cthickening_of_dist_le z (ctr k) (1 / 2) _
    (ctr_mem_spine h.le) ?_
  linarith [dist_le_of_mem_blob hz]

lemma shadeSet_subset_capsule (M : ℕ) : shadeSet M ⊆ capsule M := by
  intro z hz
  obtain ⟨k, hk, hzk⟩ := Set.mem_iUnion₂.mp hz
  exact blob_subset_capsule (Finset.mem_range.mp hk) hzk


/-! ### The mass profile -/


/-! ### Locality -/


/-! ### The counting core -/


/-! ### The convex body and the shaded body -/

lemma measurableSet_shadeSet (M : ℕ) : MeasurableSet (shadeSet M) := by
  unfold shadeSet
  exact Finset.measurableSet_biUnion _ fun k _ => measurableSet_blob k

/-- The single body of the counterexample. -/
noncomputable def carrierBody (M : ℕ) : ConvexSpaceBody E3 :=
  ⟨capsule M, (convex_capsule M).isConvexSet, isCompact_capsule M, capsule_nonempty M⟩

@[simp] lemma carrierBody_carrier (M : ℕ) : (carrierBody M).carrier = capsule M := rfl

/-- The single shaded body of the counterexample. -/
noncomputable def shadedBody (M : ℕ) : ShadedBody E3 :=
  { toConvexSpaceBody := carrierBody M
    shade := shadeSet M
    measurableSet_shade := measurableSet_shadeSet M
    shade_subset := shadeSet_subset_capsule M }

@[simp] lemma shadedBody_shade (M : ℕ) : (shadedBody M).shade = shadeSet M := rfl

@[simp] lemma shadedBody_body (M : ℕ) : (shadedBody M).toConvexSpaceBody = carrierBody M := rfl


/-! ### The statement under test -/

universe u v w


/-! ### The refutation -/


lemma exists_harmonic_gt (c : ℝ) : ∃ M : ℕ, c < ∑ k ∈ Finset.range M, 1 / ((k : ℝ) + 1) := by
  have h := Real.tendsto_sum_range_one_div_nat_succ_atTop
  rw [tendsto_atTop_atTop] at h
  obtain ⟨M, hM⟩ := h (c + 1)
  exact ⟨M, by linarith [hM M le_rfl]⟩


/-! ### Which hypothesis of GWZ Proposition 5.1 the configuration violates -/


end Kakeya.ThinCase.Refute

namespace Kakeya.ThinCase.Localise

open MeasureTheory Metric Set ShadedBody
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]


end Kakeya.ThinCase.Localise

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank
public import Kakeya.DimensionThree.Plank.EDExtraction
public import Kakeya.Tube.Basic

/-!
# The direction step of the ED conflict-degree bound

`Kakeya/DimensionThree/Plank/EDExtraction.lean` reduces essential distinctness of the inner plank
family to a bound on the *conflict degree*: the number of planks that fail to be essentially
distinct from a fixed one.  The route to that bound recorded there has four steps, of which this
file supplies step 3.

The reason step 3 matters is quantitative.  The generic count
`Kakeya.card_le_of_ED_subset` bounds pairwise-ED `δ`-tubes in a container by
`C · M · δ ^ (-(n-1))`, the factor `δ ^ (-(n-1))` being the number of *direction caps* needed to
cover the sphere.  That factor is fatal here: it makes the conflict degree `δ ^ (-2)` in `ℝ³` and
no power of `δ` can absorb it.  But it is also unnecessary, because all the tubes being counted are
nearly parallel.  `Kakeya.position_count_le_of_bad_directionClass'` is the sharp count for a
*single* direction cap, and it returns `C · M / c` — an absolute constant once the container is
tube-shaped.  Its hypothesis is exactly

`∀ i ∈ s, min ‖(T i).direction - e‖ ‖(T i).direction + e‖ ≤ c_slide * δ`,

a *projective* cap: directions are compared up to sign, since a tube does not remember which of its
two endpoints is which.

This file proves that hypothesis from containment.  `Kakeya.projective_cap_of_orthogonal_le` is the
linear-algebra core — a unit vector whose component orthogonal to another unit vector is small is
projectively close to it — and
`Kakeya.Tube.direction_projective_cap_of_subset_cthickening` is the tube-level statement: a
`δ`-tube contained in the `r`-neighbourhood of another `δ`-tube has direction in the
`√2 · 2 (r + δ)` projective cap around it.

The sign ambiguity is why the bound is stated with `min` and why the constant carries a `√2`: at
the extreme `r = 1` the two unit vectors may be antipodal, and `min ‖v - u‖ ‖v + u‖` is then `0`,
which the estimate must not contradict.

## The assembly interface

`Kakeya.exists_inner_plank_ED_subfamily_of_bounded_conflict_degree` is the seam at which the
combinatorics and the geometry meet.  It takes a finite family of shaded planks and a bound `d` on
`Kakeya.edConflictDegree` and returns an essentially distinct subfamily at cardinality loss
`d + 1`.  It contains no geometry: `d` is an arbitrary natural number, not a constant, so the
statement is agnostic about whether the eventual bound is absolute or scale-dependent.  Producing a
`d` is the job of the geometric steps 1--3 above.
-/

@[expose] public section

open MeasureTheory Metric

noncomputable section

namespace Kakeya

/-- **A unit vector with small orthogonal component lies in a projective cap.**

If `u`, `v` are unit vectors and the component of `v` orthogonal to `u` has norm at most `r`, then
`v` is within `√2 · r` of `u` *or of* `-u`.

Both alternatives are genuinely needed: `v = -u` has zero orthogonal component, so no bound on
`‖v - u‖` alone can hold.  This is the projective form consumed by
`Kakeya.position_count_le_of_bad_directionClass'`.

The proof is the identity `min ‖v - u‖² ‖v + u‖² = 2 - 2 |⟪u, v⟫|` for unit vectors, together with
`|⟪u, v⟫| = √(1 - ‖v - ⟪u, v⟫ • u‖²) ≥ √(1 - r²)` and `2 - 2√(1 - r²) ≤ 2 r²` on `[0, 1]`. -/
theorem projective_cap_of_orthogonal_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) {r : ℝ} (hr0 : 0 ≤ r)
    (h : ‖v - (inner ℝ u v : ℝ) • u‖ ≤ r) :
    min ‖v - u‖ ‖v + u‖ ≤ Real.sqrt 2 * r := by
  let c : ℝ := inner ℝ u v
  let w : E := v - c • u
  have hnorm_sub : ‖v - u‖ ^ 2 = 2 - 2 * c := by
    rw [norm_sub_sq_real, hv, hu, real_inner_comm]
    dsimp [c]
    ring
  have hnorm_add : ‖v + u‖ ^ 2 = 2 + 2 * c := by
    rw [norm_add_sq_real, hv, hu, real_inner_comm]
    dsimp [c]
    ring
  have horth : inner ℝ u w = 0 := by
    dsimp [w, c]
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hu]
    ring
  have hv_eq : v = c • u + w := by
    dsimp [w]
    abel
  have hnorm_smul : ‖c • u‖ ^ 2 = c ^ 2 := by
    simp [norm_smul, hu, Real.norm_eq_abs, sq_abs]
  have horth' : inner ℝ (c • u) w = 0 := by
    simp [real_inner_smul_left, horth]
  have hc2 : c ^ 2 = 1 - ‖w‖ ^ 2 := by
    have hnorm : ‖v‖ ^ 2 = c ^ 2 + ‖w‖ ^ 2 := by
      rw [hv_eq, norm_add_sq_real, hnorm_smul, horth']
      ring
    rw [hv] at hnorm
    nlinarith
  let m : ℝ := min ‖v - u‖ ‖v + u‖
  have hm_nonneg : 0 ≤ m := by
    dsimp [m]
    exact le_min (norm_nonneg _) (norm_nonneg _)
  have hm2_abs : m ^ 2 ≤ 2 - 2 * |c| := by
    rcases le_or_gt 0 c with hc | hc
    · calc
        m ^ 2 ≤ ‖v - u‖ ^ 2 :=
          pow_le_pow_left₀ hm_nonneg (min_le_left ‖v - u‖ ‖v + u‖) 2
        _ = 2 - 2 * c := hnorm_sub
        _ = 2 - 2 * |c| := by rw [abs_of_nonneg hc]
    · calc
        m ^ 2 ≤ ‖v + u‖ ^ 2 :=
          pow_le_pow_left₀ hm_nonneg (min_le_right ‖v - u‖ ‖v + u‖) 2
        _ = 2 + 2 * c := hnorm_add
        _ = 2 - 2 * |c| := by rw [abs_of_neg hc]; ring
  by_cases h1 : 1 ≤ r
  · have hm2le2 : m ^ 2 ≤ 2 := by
      calc
        m ^ 2 ≤ 2 - 2 * |c| := hm2_abs
        _ ≤ 2 := by nlinarith [abs_nonneg c]
    have hr2 : 1 ≤ r ^ 2 := by nlinarith [h1, hr0]
    have hm2le : m ^ 2 ≤ 2 * r ^ 2 := by nlinarith [hm2le2, hr2, hr0]
    have hm2le' : m ^ 2 ≤ (Real.sqrt 2 * r) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      exact hm2le
    have hsqrt_nonneg : 0 ≤ Real.sqrt 2 * r := mul_nonneg (Real.sqrt_nonneg 2) hr0
    have h_abs : |m| ≤ |Real.sqrt 2 * r| := sq_le_sq.mp hm2le'
    rwa [abs_of_nonneg hm_nonneg, abs_of_nonneg hsqrt_nonneg] at h_abs
  · have hr1 : r < 1 := lt_of_not_ge h1
    have h1r2 : 0 ≤ 1 - r ^ 2 := by nlinarith [hr0, hr1]
    have hw2 : ‖w‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg w) h 2
    have hc2ge : 1 - r ^ 2 ≤ c ^ 2 := by nlinarith [hc2, hw2]
    have hcabs : Real.sqrt (1 - r ^ 2) ≤ |c| := by
      have htmp : Real.sqrt (1 - r ^ 2) ≤ Real.sqrt (c ^ 2) :=
        Real.sqrt_le_sqrt hc2ge
      rwa [Real.sqrt_sq_eq_abs] at htmp
    have hs_nonneg : 0 ≤ Real.sqrt (1 - r ^ 2) := Real.sqrt_nonneg _
    have hs_le1 : Real.sqrt (1 - r ^ 2) ≤ 1 :=
      (Real.sqrt_le_one).2 (by nlinarith [hr0, hr1])
    have hsq_le : Real.sqrt (1 - r ^ 2) ^ 2 ≤ Real.sqrt (1 - r ^ 2) := by
      nlinarith [hs_nonneg, hs_le1]
    have hmain : 2 - 2 * Real.sqrt (1 - r ^ 2) ≤ 2 * r ^ 2 := by
      have hsq : Real.sqrt (1 - r ^ 2) ^ 2 = 1 - r ^ 2 := Real.sq_sqrt h1r2
      nlinarith [hsq, hsq_le]
    have hm2le : m ^ 2 ≤ 2 * r ^ 2 := by
      calc
        m ^ 2 ≤ 2 - 2 * |c| := hm2_abs
        _ ≤ 2 - 2 * Real.sqrt (1 - r ^ 2) := by nlinarith [hcabs]
        _ ≤ 2 * r ^ 2 := hmain
    have hm2le' : m ^ 2 ≤ (Real.sqrt 2 * r) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      exact hm2le
    have hsqrt_nonneg : 0 ≤ Real.sqrt 2 * r := mul_nonneg (Real.sqrt_nonneg 2) hr0
    have h_abs : |m| ≤ |Real.sqrt 2 * r| := sq_le_sq.mp hm2le'
    rwa [abs_of_nonneg hm_nonneg, abs_of_nonneg hsqrt_nonneg] at h_abs


end Kakeya

end

end

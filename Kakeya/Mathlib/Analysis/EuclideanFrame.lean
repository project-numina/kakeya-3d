/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# General Euclidean / inner-product-space helpers

Dimension-free, project-type-free lemmas about Euclidean spaces and inner product
spaces: a sup-norm bound on the Euclidean norm, an inner-product width bound for a
set contained in the closed thickening of an affine subspace, and a Gram-Schmidt
style construction of an orthonormal frame orthogonal to a descending family of
subspaces.
-/

@[expose] public section

open scoped InnerProductSpace


section InnerProductUnit

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


/-- Perpendicular-component frame-shift: if `u, u'` are two unit vectors and `w` is any vector,
the perpendicular projections of `w` onto the hyperplanes orthogonal to `u` and `u'` differ by
at most `2 ‖w‖ ‖u - u'‖`. -/
lemma perp_component_frame_shift (w u u' : E)
    (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1) :
    ‖(w - (inner ℝ w u') • u') - (w - (inner ℝ w u) • u)‖
      ≤ 2 * ‖w‖ * ‖u - u'‖ := by
  -- Simplify the LHS: (w - α'•u') - (w - α•u) = α•u - α'•u'
  have hsimp : (w - (inner ℝ w u') • u') - (w - (inner ℝ w u) • u)
      = (inner ℝ w u) • u - (inner ℝ w u') • u' := by
    abel
  rw [hsimp]
  -- Decompose: α•u - α'•u' = α•(u - u') + (α - α')•u'
  have hdec : (inner ℝ w u) • u - (inner ℝ w u') • u'
      = (inner ℝ w u) • (u - u') + ((inner ℝ w u) - (inner ℝ w u')) • u' := by
    rw [smul_sub, sub_smul]
    abel
  rw [hdec]
  -- Triangle inequality
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hu']
  -- Bound |⟨w,u⟩| ≤ ‖w‖
  have h1 : |inner ℝ w u| ≤ ‖w‖ := by
    have := abs_real_inner_le_norm w u
    rw [hu, mul_one] at this
    exact this
  -- Bound |⟨w,u⟩ - ⟨w,u'⟩| ≤ ‖w‖ * ‖u - u'‖
  have h2 : |inner ℝ w u - inner ℝ w u'| ≤ ‖w‖ * ‖u - u'‖ := by
    have heq : inner ℝ w u - inner ℝ w u' = inner ℝ w (u - u') := by
      rw [inner_sub_right]
    rw [heq]
    exact abs_real_inner_le_norm w (u - u')
  have hnonneg : 0 ≤ ‖u - u'‖ := norm_nonneg _
  have hwnn : 0 ≤ ‖w‖ := norm_nonneg _
  have hT1 : |inner ℝ w u| * ‖u - u'‖ ≤ ‖w‖ * ‖u - u'‖ :=
    mul_le_mul_of_nonneg_right h1 hnonneg
  have hT2 : |inner ℝ w u - inner ℝ w u'| * 1 ≤ ‖w‖ * ‖u - u'‖ * 1 :=
    mul_le_mul_of_nonneg_right h2 zero_le_one
  linarith

/-- Parallel-component frame-shift: if `u, u'` are two unit vectors and `w` is any vector,
the parallel components `⟪w, u⟫` and `⟪w, u'⟫` differ by at most `‖w‖ ‖u - u'‖`. -/
lemma par_component_frame_shift (w u u' : E)
    (_hu : ‖u‖ = 1) (_hu' : ‖u'‖ = 1) :
    |inner ℝ w u' - inner ℝ w u| ≤ ‖w‖ * ‖u - u'‖ := by
  have heq : inner ℝ w u' - inner ℝ w u = inner ℝ w (u' - u) := by
    rw [inner_sub_right]
  rw [heq]
  have hbd : |inner ℝ w (u' - u)| ≤ ‖w‖ * ‖u' - u‖ :=
    abs_real_inner_le_norm w (u' - u)
  rwa [norm_sub_rev] at hbd

/-- The component of `v` orthogonal to a unit vector `u` has norm at most `2 * ‖v‖`. -/
lemma norm_perp_le_two_mul_norm {u : E} (hu : ‖u‖ = 1) (v : E) :
    ‖v - (inner ℝ v u) • u‖ ≤ 2 * ‖v‖ := by
  calc
    ‖v - (inner ℝ v u) • u‖ ≤ ‖v‖ + ‖(inner ℝ v u) • u‖ := norm_sub_le _ _
    _ = ‖v‖ + (‖inner ℝ v u‖ * ‖u‖) := by rw [norm_smul]
    _ = ‖v‖ + (|inner ℝ v u| * ‖u‖) := by rw [Real.norm_eq_abs]
    _ = ‖v‖ + |inner ℝ v u| := by rw [hu, mul_one]
    _ ≤ ‖v‖ + (‖v‖ * ‖u‖) := by
      gcongr
      exact abs_real_inner_le_norm v u
    _ = ‖v‖ + ‖v‖ := by rw [hu, mul_one]
    _ = 2 * ‖v‖ := by ring

/-- If `m = t • d + c • u + z` with `u` a unit vector, `|t| ≤ 1 / 2`, `‖d - u‖ ≤ r` and
`‖z‖ ≤ ρ`, then the component of `m` orthogonal to `u` has norm at most `r + 2 * ρ`: the
`c • u` term is annihilated, `t • d` contributes `|t| * 2 * r` and `z` contributes
`2 * ρ`. -/
lemma norm_perp_le_of_decomp {u : E} (hu : ‖u‖ = 1) {m d z : E} {t c r ρ : ℝ}
    (hm : m = t • d + c • u + z) (ht : |t| ≤ 1 / 2)
    (hd : ‖d - u‖ ≤ r) (hz : ‖z‖ ≤ ρ) :
    ‖m - (inner ℝ m u) • u‖ ≤ r + 2 * ρ := by
  have hinner_uu : inner ℝ u u = 1 := by
    calc
      inner ℝ u u = ‖u‖ ^ 2 := real_inner_self_eq_norm_sq _
      _ = 1 ^ 2 := by rw [hu]
      _ = 1 := by norm_num
  have hinner_du_minus_one : inner ℝ (d - u) u = inner ℝ d u - 1 := by
    calc
      inner ℝ (d - u) u = inner ℝ d u - inner ℝ u u := by rw [inner_sub_left]
      _ = inner ℝ d u - 1 := by rw [hinner_uu]
  have h_eq : d - (inner ℝ d u) • u = (d - u) - (inner ℝ (d - u) u) • u := by
    calc
      d - (inner ℝ d u) • u = (d - u) - ((inner ℝ d u) • u - u) := by
        abel
      _ = (d - u) - ((inner ℝ d u - 1) • u) := by simp [sub_smul, one_smul]
      _ = (d - u) - (inner ℝ (d - u) u) • u := by rw [hinner_du_minus_one]
  have hinner_mu : inner ℝ m u = t * inner ℝ d u + c + inner ℝ z u := by
    calc
      inner ℝ m u = inner ℝ (t • d + c • u + z) u := by rw [hm]
      _ = inner ℝ (t • d) u + inner ℝ (c • u) u + inner ℝ z u := by simp [inner_add_left]
      _ = t * inner ℝ d u + c * inner ℝ u u + inner ℝ z u := by simp [inner_smul_left]
      _ = t * inner ℝ d u + c * 1 + inner ℝ z u := by rw [hinner_uu]
      _ = t * inner ℝ d u + c + inner ℝ z u := by ring
  have key : m - (inner ℝ m u) • u =
      t • ((d - u) - (inner ℝ (d - u) u) • u) + (z - (inner ℝ z u) • u) := by
    calc
      m - (inner ℝ m u) • u = (t • d + c • u + z) - (inner ℝ m u) • u := by rw [hm]
      _ = (t • d + c • u + z) - ((t * inner ℝ d u + c + inner ℝ z u) • u) := by rw [hinner_mu]
      _ = (t • d + c • u + z) - ((t * inner ℝ d u) • u + c • u + (inner ℝ z u) • u) := by
        simp [add_smul]
      _ = t • d - (t * inner ℝ d u) • u + z - (inner ℝ z u) • u := by
        abel
      _ = t • (d - (inner ℝ d u) • u) + (z - (inner ℝ z u) • u) := by
        simp [smul_smul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      _ = t • ((d - u) - (inner ℝ (d - u) u) • u) + (z - (inner ℝ z u) • u) := by rw [h_eq]
  rw [key]
  have hnormA : ‖t • ((d - u) - (inner ℝ (d - u) u) • u)‖ ≤ r := by
    calc
      ‖t • ((d - u) - (inner ℝ (d - u) u) • u)‖ = |t| * ‖(d - u) - (inner ℝ (d - u) u) • u‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ ≤ |t| * (2 * ‖d - u‖) := by
        refine mul_le_mul_of_nonneg_left (norm_perp_le_two_mul_norm hu (d - u)) (abs_nonneg _)
      _ = (|t| * 2) * ‖d - u‖ := by ring
      _ ≤ (1 : ℝ) * ‖d - u‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        calc
          |t| * 2 = 2 * |t| := by ring
          _ ≤ 2 * (1 / 2) := mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ 2)
          _ = 1 := by ring
      _ = ‖d - u‖ := by simp
      _ ≤ r := hd
  have hnormB : ‖z - (inner ℝ z u) • u‖ ≤ 2 * ρ := by
    calc
      ‖z - (inner ℝ z u) • u‖ ≤ 2 * ‖z‖ := norm_perp_le_two_mul_norm hu z
      _ ≤ 2 * ρ := mul_le_mul_of_nonneg_left hz (by norm_num : (0 : ℝ) ≤ 2)
  calc
    ‖t • ((d - u) - (inner ℝ (d - u) u) • u) + (z - (inner ℝ z u) • u)‖
        ≤ ‖t • ((d - u) - (inner ℝ (d - u) u) • u)‖ + ‖z - (inner ℝ z u) • u‖ := norm_add_le _ _
    _ ≤ r + 2 * ρ := add_le_add hnormA hnormB

end InnerProductUnit

section DirectionBasis

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]

/-- Given a unit vector `d : E` in a finite-dimensional inner product space,
there exists an orthonormal basis of `E` (indexed by `Fin (Module.finrank ℝ E)`)
whose zeroth element equals `d`. -/
lemma exists_orthonormalBasis_zero_eq {d : E} (hd : ‖d‖ = 1) :
    ∃ b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E, b 0 = d := by
  have h_orth : Orthonormal ℝ
      (({0} : Set (Fin (Module.finrank ℝ E))).restrict (fun _ => d)) := by
    refine ⟨?_, ?_⟩
    · intro _; simpa using hd
    · intro i j hij
      exact absurd (Subsingleton.elim i j) hij
  obtain ⟨b, hb⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (ι := Fin (Module.finrank ℝ E))
      (s := ({0} : Set (Fin (Module.finrank ℝ E))))
      (v := fun _ => d)
      (Fintype.card_fin _).symm h_orth
  exact ⟨b, hb 0 (Set.mem_singleton 0)⟩

/-- An orthonormal basis of `E` whose zeroth vector is a given unit vector `d`. -/
noncomputable def directionBasis {d : E} (hd : ‖d‖ = 1) :
    OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E :=
  (exists_orthonormalBasis_zero_eq hd).choose

@[simp]
lemma directionBasis_zero {d : E} (hd : ‖d‖ = 1) :
    directionBasis hd 0 = d :=
  (exists_orthonormalBasis_zero_eq hd).choose_spec

/-- The orthonormal-basis isometry `E ≃ₗᵢ EuclideanSpace ℝ (Fin (finrank ℝ E))`
arising from `directionBasis hd`. Maps the chosen unit direction `d` to the
zeroth standard basis vector. -/
noncomputable def cylinderEquiv {d : E} (hd : ‖d‖ = 1) :
    E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
  (directionBasis hd).repr

@[simp]
lemma cylinderEquiv_apply_direction {d : E} (hd : ‖d‖ = 1) :
    cylinderEquiv hd d = EuclideanSpace.single 0 1 := by
  have h := (directionBasis hd).repr_self 0
  rw [directionBasis_zero hd] at h
  exact h

@[simp]
lemma cylinderEquiv_symm_single_zero {d : E} (hd : ‖d‖ = 1) :
    (cylinderEquiv hd).symm (EuclideanSpace.single 0 1) = d := by
  rw [← cylinderEquiv_apply_direction hd, LinearIsometryEquiv.symm_apply_apply]

end DirectionBasis

section Fin3Frame

/-- Expansion of an inner product over an orthonormal frame of `EuclideanSpace ℝ (Fin 3)`. -/
theorem inner_eq_sum_frame
    (basis : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)))
    (u w : EuclideanSpace ℝ (Fin 3)) :
    (inner ℝ u w : ℝ) = ∑ j : Fin 3, inner ℝ (basis j) w * inner ℝ u (basis j) :=
  (basis.sum_inner_mul_inner u w).symm.trans (Finset.sum_congr rfl fun _ _ => mul_comm _ _)

/-- Term-by-term bound for the frame expansion of `inner_eq_sum_frame`: the size of an inner
product is at most the sum over the frame of `|frame coordinate| * |cross-frame coefficient|`. -/
theorem abs_inner_le_sum_frame
    (basis : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)))
    (u w : EuclideanSpace ℝ (Fin 3)) :
    |(inner ℝ u w : ℝ)| ≤ |inner ℝ (basis 0) w| * |inner ℝ u (basis 0)|
      + |inner ℝ (basis 1) w| * |inner ℝ u (basis 1)|
      + |inner ℝ (basis 2) w| * |inner ℝ u (basis 2)| := by
  rw [inner_eq_sum_frame basis u w, Fin.sum_univ_three, ← abs_mul, ← abs_mul, ← abs_mul]
  exact abs_add_three _ _ _

/-- Frame expansion with per-term bounds: a bound `dⱼ` on each frame coordinate of `w` together
with a bound `cⱼ` on each cross-frame coefficient of `u` bounds `⟪u, w⟫` by `∑ dⱼ cⱼ`. -/
theorem abs_inner_le_of_frame_bounds
    (basis : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)))
    (u w : EuclideanSpace ℝ (Fin 3)) {d₀ d₁ d₂ c₀ c₁ c₂ : ℝ}
    (h₀ : |(inner ℝ (basis 0) w : ℝ)| ≤ d₀) (h₁ : |(inner ℝ (basis 1) w : ℝ)| ≤ d₁)
    (h₂ : |(inner ℝ (basis 2) w : ℝ)| ≤ d₂)
    (k₀ : |(inner ℝ u (basis 0) : ℝ)| ≤ c₀) (k₁ : |(inner ℝ u (basis 1) : ℝ)| ≤ c₁)
    (k₂ : |(inner ℝ u (basis 2) : ℝ)| ≤ c₂) (hd₀ : 0 ≤ d₀) (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂) :
    |(inner ℝ u w : ℝ)| ≤ d₀ * c₀ + d₁ * c₁ + d₂ * c₂ :=
  (abs_inner_le_sum_frame basis u w).trans <|
    add_le_add (add_le_add (mul_le_mul h₀ k₀ (abs_nonneg _) hd₀)
      (mul_le_mul h₁ k₁ (abs_nonneg _) hd₁)) (mul_le_mul h₂ k₂ (abs_nonneg _) hd₂)

/-- Cauchy–Schwarz between two orthonormal frames: every cross-frame coefficient is at most `1`
in absolute value. -/
theorem abs_inner_basis_le_one
    (basis basis' : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))) (i j : Fin 3) :
    |(inner ℝ (basis i) (basis' j) : ℝ)| ≤ 1 :=
  (abs_real_inner_le_norm _ _).trans_eq (by rw [basis.norm_eq_one, basis'.norm_eq_one, mul_one])

/-- Triangle-inequality split of a coordinate of `x -ᵥ c` through an auxiliary point `p` and an
auxiliary centre `c'`. -/
theorem abs_inner_vsub_le_split (u x p c c' : EuclideanSpace ℝ (Fin 3)) :
    |(inner ℝ u (x -ᵥ c) : ℝ)|
      ≤ |inner ℝ u (x -ᵥ c')| + |inner ℝ u (p -ᵥ c')| + |inner ℝ u (p -ᵥ c)| := by
  rw [show x -ᵥ c = (x -ᵥ c') - (p -ᵥ c') + (p -ᵥ c) by
        rw [vsub_sub_vsub_cancel_right, vsub_add_vsub_cancel],
    inner_add_right, inner_sub_right]
  exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)

end Fin3Frame

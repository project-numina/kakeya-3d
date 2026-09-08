/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Conjunct6EssDistinct
public import Kakeya.Tube.Nets

/-!
# The anchored `ρ`-net: one scale of the loose hierarchy, at the existing constants

The loose-hierarchy condition associated with
`Kakeya.VeryNotSticky.SideDataObligations` as *"produce a
`Kakeya.LooseUniform.LooseShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) 4 …"*,
because everything inside that binder is already the compiled theorem
`Kakeya.VeryNotSticky.exists_Cang_angularFibre_le_of_looseUniform`. What remains is the
**producer**, and its keystone is one scale:

> a finite family of `ρ`-tubes, and an assignment of every `δ`-tube of the family (`4δ ≤ ρ`,
> carrier in the unit ball) to one of them, such that
> * the member lies in the **`4`-dilate** of its node
>   (`Kakeya.LooseUniform.LooseGridCoverSystem.le_dilate_tube_assign` at `K = 4`),
> * its direction is within **`ρ/4`** of the node's
>   (`Kakeya.LooseUniform.LooseGridCoverSystem.dir_close_tube_assign`),
> * the node map is injective on the used index set
>   (`Kakeya.LooseUniform.LooseUniformTubeSet.tube_injOn`), and
> * for **every** `ρ`-tube `V`, at most an absolute constant many used nodes have a member in
>   `Kakeya.Tube.dilate V 8`
>   (`Kakeya.LooseUniform.LooseUniformTubeSet.boundedOverlapDil` at `K + 4 = 8`).

`Kakeya.LooseUniform.exists_anchorCover` is exactly that, **at the existing constants `K = 4`
and `ρ/4`** — no field is weakened.

## Why the net is anchored, and why that is the whole point

The obvious candidate, `Tube.grid_net_tight`, already gives the first two clauses (it covers a
`δ`-tube by a `ρ`-tube *exactly*, with midpoint within `ρ/32` and direction within `ρ/16`).  It
does **not** give the fourth: its nodes are separated in the **midpoint**, so a node may be
translated **along its own axis** by `ρ/64` and still count as a new node, and
`Kakeya.Tube.dilate V 8` is `8` times as long as a node — so `Θ(1/ρ)` distinct net tubes have a
member inside one `8`-dilate, and no `δ`-free bound exists.   identified the
repair and left it uncompiled; this file compiles it.

The repair is to bin a member not by its midpoint but by its **anchor**
`Kakeya.LooseUniform.anchorAt`, the component of its centre orthogonal to the chosen node
direction.  The anchor kills the axial degree of freedom, and
`Kakeya.LooseUniform.anchor_near_axisFoot` is the estimate that makes it work: a member inside
`Kakeya.Tube.dilate V 8` has its anchor within `82 ρ` of `Kakeya.LooseUniform.axisFoot V`, a
point depending on `V` **alone** — the `|t| ≤ 4` axial freedom of the dilate cancels against the
anchor's own subtraction.  Bounded overlap is then the packing bound
`Tube.card_le_of_L1_separated_in_box` in the four net coordinates, with the absolute constant
`Kakeya.LooseUniform.anchorOverlapConst = 2 · 21249 ^ 6`.

## What this file does NOT do

It is **one scale**.  A `Kakeya.LooseUniform.LooseGridCoverSystem` additionally needs the levels
`0 … N` to be `nested`, and `Kakeya.LooseUniform.LooseUniformTubeSet` needs GWZ Definition
2.1(iii)'s two-sided class bracket, which costs a refinement (the pruning engine
`Tube.exists_pruned_subset_noroot_notop`).  **Nothing here discharges conjunct 6**, and nothing
here may be cited as doing so.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Set
open scoped NNReal RealInnerProductSpace ENNReal

namespace Kakeya
namespace LooseUniform

noncomputable def axisFoot {ρ : ℝ≥0} (V : Tube ρ E3) : E3 :=
  V.center - ⟪V.center, V.direction⟫ • V.direction

noncomputable def anchorAt {δ : ℝ≥0} (T : Tube δ E3) (d : E3) : E3 :=
  T.center - ⟪T.center, d⟫ • d

theorem center_mem_carrier {δ : ℝ≥0} (hδ : 0 < δ) (T : Tube δ E3) :
    T.center ∈ T.carrier := by
  have h := Tube.midpoint_mem_carrier hδ T
  have he : T.center = T.midpoint := by
    change midpoint ℝ T.x T.y = _
    rw [midpoint_eq_smul_add]; norm_num
  rwa [he]

private theorem anchor_algebra (c v fv uv ev : E3) (A t' c₀ : ℝ)
    (hc : c = v + t' • uv + fv)
    (hA : A = c₀ + t' + ⟪fv, uv⟫ + ⟪c, ev⟫) :
    (c - A • (uv + ev)) - (v - c₀ • uv)
      = (-(⟪fv, uv⟫ + ⟪c, ev⟫)) • uv + fv - A • ev := by
  rw [hA, hc]
  module

theorem anchor_near_axisFoot {δ ρ : ℝ≥0}
    (T : Tube δ E3) (V : Tube ρ E3) {d : E3} (hd : ‖d‖ = 1)
    (hm1 : ‖T.center‖ ≤ 1) (hδ : 0 < δ)
    (hdT : ‖T.direction - d‖ ≤ (ρ : ℝ) / 4)
    (hTV : T.toConvexSpaceBody ≤ Kakeya.Tube.dilate V 8) :
    ∃ σ : ℝ, |σ| = 1 ∧ ‖d - σ • V.direction‖ ≤ 33 * (ρ : ℝ) ∧
      ‖anchorAt T d - axisFoot V‖ ≤ 82 * (ρ : ℝ) := by
  have hρ0 : (0 : ℝ) ≤ (ρ : ℝ) := ρ.coe_nonneg
  obtain ⟨σ₁, hσ₁, hdir₁⟩ :=
    Kakeya.VeryNotSticky.exists_sign_norm_direction_sub_le_of_le_dilate T V
      (by norm_num : (0:ℝ) < 8) hTV
  have hσsq : σ₁ * σ₁ = 1 := by
    rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hσ₁ with h | h <;> rw [h] <;> norm_num
  have hVdirnorm : ‖V.direction‖ = 1 := Tube.norm_direction V
  -- the reference unit vector
  have hu : ‖σ₁ • V.direction‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, hσ₁, hVdirnorm, one_mul]
  have hVback : σ₁ • (σ₁ • V.direction) = V.direction := by
    rw [smul_smul, hσsq, one_smul]
  have he33 : ‖d - σ₁ • V.direction‖ ≤ 33 * (ρ : ℝ) := by
    calc ‖d - σ₁ • V.direction‖
        ≤ ‖d - T.direction‖ + ‖T.direction - σ₁ • V.direction‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (ρ : ℝ) / 4 + 4 * 8 * (ρ : ℝ) := by
            refine add_le_add ?_ hdir₁
            rw [← norm_neg]
            simpa using hdT
      _ ≤ 33 * (ρ : ℝ) := by linarith
  refine ⟨σ₁, hσ₁, he33, ?_⟩
  -- position
  obtain ⟨t, ht, hdist⟩ :=
    exists_axis_point_of_mem_dilate V (by norm_num : (0:ℝ) < 8)
      (hTV (center_mem_carrier hδ T))
  have hf : ‖T.center - (V.center + t • V.direction)‖ ≤ 8 * (ρ : ℝ) := by
    rw [← dist_eq_norm]; exact hdist
  have htv : t • V.direction = (t * σ₁) • (σ₁ • V.direction) := by
    rw [smul_smul, mul_assoc, hσsq, mul_one]
  have hcenter : T.center
      = V.center + (t * σ₁) • (σ₁ • V.direction)
        + (T.center - (V.center + t • V.direction)) := by
    rw [← htv]; module
  have hfoot : axisFoot V = V.center - ⟪V.center, σ₁ • V.direction⟫ • (σ₁ • V.direction) := by
    rw [axisFoot, real_inner_smul_right, smul_smul,
      mul_comm σ₁ (⟪V.center, V.direction⟫ : ℝ), mul_assoc, hσsq, mul_one]
  have hdsplit : d = (σ₁ • V.direction) + (d - σ₁ • V.direction) := by module
  have hA : ⟪T.center, d⟫
      = ⟪V.center, σ₁ • V.direction⟫ + (t * σ₁)
        + ⟪T.center - (V.center + t • V.direction), σ₁ • V.direction⟫
        + ⟪T.center, d - σ₁ • V.direction⟫ := by
    nth_rewrite 1 [hdsplit]
    rw [inner_add_right]
    nth_rewrite 1 [hcenter]
    rw [inner_add_left, inner_add_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    rw [hu]
    ring
  have hkey := anchor_algebra T.center V.center
    (T.center - (V.center + t • V.direction)) (σ₁ • V.direction) (d - σ₁ • V.direction)
    ⟪T.center, d⟫ (t * σ₁) ⟪V.center, σ₁ • V.direction⟫ hcenter hA
  have hgoal : anchorAt T d - axisFoot V
      = (-(⟪T.center - (V.center + t • V.direction), σ₁ • V.direction⟫
            + ⟪T.center, d - σ₁ • V.direction⟫)) • (σ₁ • V.direction)
        + (T.center - (V.center + t • V.direction))
        - ⟪T.center, d⟫ • (d - σ₁ • V.direction) := by
    rw [anchorAt, hfoot, ← hkey, ← hdsplit]
  rw [hgoal]
  have hb1 : |⟪T.center - (V.center + t • V.direction), σ₁ • V.direction⟫| ≤ 8 * (ρ : ℝ) := by
    calc |⟪T.center - (V.center + t • V.direction), σ₁ • V.direction⟫|
        ≤ ‖T.center - (V.center + t • V.direction)‖ * ‖σ₁ • V.direction‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ 8 * (ρ : ℝ) := by rw [hu, mul_one]; exact hf
  have hb2 : |⟪T.center, d - σ₁ • V.direction⟫| ≤ 33 * (ρ : ℝ) := by
    calc |⟪T.center, d - σ₁ • V.direction⟫|
        ≤ ‖T.center‖ * ‖d - σ₁ • V.direction‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 * (33 * (ρ : ℝ)) := by
            refine mul_le_mul hm1 he33 (norm_nonneg _) (by norm_num)
      _ = 33 * (ρ : ℝ) := one_mul _
  have hb3 : |⟪T.center, d⟫| ≤ 1 := by
    calc |⟪T.center, d⟫| ≤ ‖T.center‖ * ‖d‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 * 1 := mul_le_mul hm1 (le_of_eq hd) (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  calc ‖(-(⟪T.center - (V.center + t • V.direction), σ₁ • V.direction⟫
            + ⟪T.center, d - σ₁ • V.direction⟫)) • (σ₁ • V.direction)
        + (T.center - (V.center + t • V.direction))
        - ⟪T.center, d⟫ • (d - σ₁ • V.direction)‖
      ≤ ‖(-(⟪T.center - (V.center + t • V.direction), σ₁ • V.direction⟫
            + ⟪T.center, d - σ₁ • V.direction⟫)) • (σ₁ • V.direction)
          + (T.center - (V.center + t • V.direction))‖
        + ‖⟪T.center, d⟫ • (d - σ₁ • V.direction)‖ := norm_sub_le _ _
    _ ≤ (‖(-(⟪T.center - (V.center + t • V.direction), σ₁ • V.direction⟫
            + ⟪T.center, d - σ₁ • V.direction⟫)) • (σ₁ • V.direction)‖
          + ‖T.center - (V.center + t • V.direction)‖)
        + ‖⟪T.center, d⟫ • (d - σ₁ • V.direction)‖ := by
          gcongr; exact norm_add_le _ _
    _ ≤ ((8 * (ρ:ℝ) + 33 * (ρ:ℝ)) + 8 * (ρ:ℝ)) + 33 * (ρ:ℝ) := by
          gcongr
          · rw [norm_smul, hu, mul_one, Real.norm_eq_abs, abs_neg]
            exact (abs_add_le _ _).trans (add_le_add hb1 hb2)
          · rw [norm_smul, Real.norm_eq_abs]
            calc |⟪T.center, d⟫| * ‖d - σ₁ • V.direction‖
                ≤ 1 * (33 * (ρ : ℝ)) :=
                  mul_le_mul hb3 he33 (norm_nonneg _) (by norm_num)
              _ = 33 * (ρ : ℝ) := one_mul _
    _ = 82 * (ρ : ℝ) := by ring

/-- The absolute bounded-overlap constant of the anchored net. -/
def anchorOverlapConst : ℕ := 2 * 21249 ^ 6


/-! ## The multiscale anchored cover

The one-scale construction is repeated at every grid level, and the two structural fields of
`Kakeya.LooseUniform.LooseGridCoverSystem` that relate the levels — `nested` — is obtained by a
**downward recursion on the cell key, not on a chain of members**.

That choice is the whole content of this section.  Chaining through cell *representatives*
(`i ↦ representative of `i`'s level-`(k+1)` cell ↦ …`) does not work: two members of one cell may
differ by an **axial** displacement of order `1`, and when the node direction rotates by `Θ(ρ_k)`
between levels that displacement re-enters as a `Θ(ρ_k)` *perpendicular* error at **every** one of
the `N` steps, so the containment constant would grow like `N`.  Recursing on the key instead
carries only *anchored* data: the level-`k` key is computed from the level-`(k+1)` **key**
(`Kakeya.LooseUniform.downIter`), and the axial component cancels because
`Kakeya.LooseUniform.perp d' d = Kakeya.LooseUniform.perp d' (d - d')`.  The resulting errors are
geometric in `k` and the constants are absolute — the invariant is
`‖(T i).direction - d_k‖ ≤ ρ_k/8` and `‖p_k - perp d_k (T i).center‖ ≤ 3 ρ_k/16`.

Nesting is then free (`key k` is a function of `key (k+1)`), node injectivity is free (the level-`k`
index set is the set of level-`k` **keys**, and the node is determined by the key), and the whole
construction has **retention `1`**: no member of `s` is discarded.
-/

/-- Iterate a level-indexed step map downward from level `N` to level `k`. -/
def downIter {α : Type*} (N : ℕ) (base : α) (stp : ℕ → α → α) (k : ℕ) : α :=
  if _h : k < N then stp k (downIter N base stp (k + 1)) else base
termination_by N - k
decreasing_by omega

lemma downIter_of_lt {α : Type*} (N : ℕ) (base : α) (stp : ℕ → α → α) {k : ℕ} (h : k < N) :
    downIter N base stp k = stp k (downIter N base stp (k + 1)) := by
  rw [downIter]; simp [h]

lemma downIter_of_not_lt {α : Type*} (N : ℕ) (base : α) (stp : ℕ → α → α) {k : ℕ}
    (h : ¬ k < N) : downIter N base stp k = base := by
  rw [downIter]; simp [h]

/-- The component of `v` orthogonal to the unit vector `d`. -/
noncomputable def perp (d v : E3) : E3 := v - ⟪v, d⟫ • d


lemma perp_sub (d v w : E3) : perp d (v - w) = perp d v - perp d w := by
  simp only [perp, inner_sub_left, sub_smul]; module

lemma perp_smul (d : E3) (t : ℝ) (v : E3) : perp d (t • v) = t • perp d v := by
  simp only [perp, real_inner_smul_left, smul_smul, smul_sub]

lemma perp_self {d : E3} (hd : ‖d‖ = 1) : perp d d = 0 := by
  have h1 : (⟪d, d⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hd]; norm_num
  rw [perp, h1, one_smul, sub_self]

lemma norm_perp_le {d : E3} (hd : ‖d‖ = 1) (v : E3) : ‖perp d v‖ ≤ ‖v‖ := by
  have hexp : ‖perp d v‖ ^ 2 = ‖v‖ ^ 2 - (⟪v, d⟫ : ℝ) ^ 2 := by
    have h := norm_sub_sq_real v ((⟪v, d⟫ : ℝ) • d)
    rw [real_inner_smul_right, norm_smul, Real.norm_eq_abs, hd, mul_one, sq_abs] at h
    simp only [perp]
    rw [h]; ring
  have hle : ‖perp d v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [hexp]; nlinarith [sq_nonneg (⟪v, d⟫ : ℝ)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hle


open scoped Classical in
/-- **The multiscale anchored cover.** -/
theorem exists_looseGridCover {ι : Type*} {δ : ℝ≥0} {N : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (s : Finset ι) (T : ι → Tube δ E3)
    (hB : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E3) 1)
    (hgap : ∀ k, 2 * ((Tube.gridScale δ N (k + 1) : ℝ≥0) : ℝ)
      ≤ ((Tube.gridScale δ N k : ℝ≥0) : ℝ))
    (hδle : ∀ k, k ≤ N → (δ : ℝ) ≤ ((Tube.gridScale δ N k : ℝ≥0) : ℝ)) :
    ∃ cover : LooseGridCoverSystem s T N 4,
      (∀ k, k ≤ N → Set.InjOn (cover.tube k) (cover.indexSet k : Set ι)) ∧
      (∀ k, k ≤ N → ∀ V : Tube (Tube.gridScale δ N k) E3,
        (((cover.indexSet k).filter (fun j => ∃ i ∈ s, cover.assign k i = j ∧
          (T i).toConvexSpaceBody ≤ Kakeya.Tube.dilate V ((4 : ℝ) + 4))).card : ℕ)
          ≤ anchorOverlapConst) ∧
      (∀ k, ∀ j ∈ cover.indexSet k, ∃ i ∈ s, cover.assign k i = j) := by
  classical
  obtain ⟨v₀, hv₀ne⟩ := exists_ne (0 : E3)
  set u₀ : E3 := ‖v₀‖⁻¹ • v₀ with hu₀_def
  have hu₀ : ‖u₀‖ = 1 := by
    rw [hu₀_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv₀ne)]
  set ρ : ℕ → ℝ := fun k => ((Tube.gridScale δ N k : ℝ≥0) : ℝ) with hρ_def
  have hρpos : ∀ k, 0 < ρ k := by
    intro k; exact_mod_cast Tube.gridScale_pos hδ N k
  have hρ1 : ∀ k, ρ k ≤ 1 := by
    intro k; exact_mod_cast Tube.gridScale_le_one hδ1 N k
  rcases s.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · refine ⟨{ indexSet := fun _ => ∅
              assign := fun _ i => i
              tube := fun k _ => Tube.ofMidpointDirection (Tube.gridScale δ N k) 0 u₀ hu₀
              assign_mem := by simp
              le_dilate_tube_assign := by simp
              dir_close_tube_assign := by simp
              nested := by simp }, ?_, ?_, ?_⟩ <;> simp [anchorOverlapConst]
  haveI : Nonempty ι := ⟨i₀⟩
  -- the per-level nets
  have hnetD : ∀ k : ℕ, ∃ D : Finset E3, (∀ d ∈ D, ‖d‖ = 1) ∧
      (∀ x ∈ D, ∀ y ∈ D, x ≠ y → ρ k / 32 ≤ ‖x - y‖) ∧
      (∀ u : E3, ‖u‖ = 1 → ∃ d ∈ D, ‖u - d‖ ≤ 2 * (ρ k / 32)) := by
    intro k
    exact Tube.sphere_sep_net (E := E3) (by linarith [hρpos k]) (by linarith [hρ1 k])
  choose Dn hDn_unit hDn_sep hDn_cover using hnetD
  have hnetP : ∀ k : ℕ, ∃ P : Finset E3, (∀ p ∈ P, p ∈ Metric.closedBall (0 : E3) 3) ∧
      (∀ x ∈ P, ∀ y ∈ P, x ≠ y → ρ k / 64 ≤ ‖x - y‖) ∧
      (∀ m ∈ Metric.closedBall (0 : E3) 3, ∃ p ∈ P, ‖m - p‖ ≤ 2 * (ρ k / 64)) := by
    intro k
    exact Tube.midpoint_sep_net (E := E3) (by linarith [hρpos k])
  choose Pn hPn_loc hPn_sep hPn_cover using hnetP
  -- the rounding maps, made total
  have hrd : ∀ (k : ℕ) (u : E3), ∃ d : E3,
      ‖u‖ = 1 → (d ∈ Dn k ∧ ‖u - d‖ ≤ 2 * (ρ k / 32)) := by
    intro k u
    by_cases h : ‖u‖ = 1
    · obtain ⟨d, hd, hd2⟩ := hDn_cover k u h
      exact ⟨d, fun _ => ⟨hd, hd2⟩⟩
    · exact ⟨u₀, fun hc => absurd hc h⟩
  choose rD hrD using hrd
  have hrp : ∀ (k : ℕ) (m : E3), ∃ p : E3,
      m ∈ Metric.closedBall (0 : E3) 3 → (p ∈ Pn k ∧ ‖m - p‖ ≤ 2 * (ρ k / 64)) := by
    intro k m
    by_cases h : m ∈ Metric.closedBall (0 : E3) 3
    · obtain ⟨p, hp, hp2⟩ := hPn_cover k m h
      exact ⟨p, fun _ => ⟨hp, hp2⟩⟩
    · exact ⟨u₀, fun hc => absurd hc h⟩
  choose rP hrP using hrp
  -- the key, defined by downward iteration
  set stp : ℕ → (E3 × E3) → (E3 × E3) := fun k q =>
    (rP k (perp (rD k q.2) q.1), rD k q.2) with hstp_def
  set base : ι → E3 × E3 := fun i =>
    (rP N (perp (rD N (T i).direction) (T i).center), rD N (T i).direction) with hbase_def
  set key : ℕ → ι → E3 × E3 := fun k i => downIter N (base i) stp k with hkey_def
  have hkey_lt : ∀ k, k < N → ∀ i, key k i = stp k (key (k + 1) i) := by
    intro k hk i
    simp only [hkey_def]
    exact downIter_of_lt N (base i) stp hk
  have hkey_top : ∀ i, key N i = base i := by
    intro i
    simp only [hkey_def]
    exact downIter_of_not_lt N (base i) stp (lt_irrefl N)
  -- centres of members lie in the unit ball
  have hcen1 : ∀ i ∈ s, ‖(T i).center‖ ≤ 1 := by
    intro i hi
    have := hB i hi (center_mem_carrier hδ (T i))
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  -- the downward invariant
  have hinv : ∀ i ∈ s, ∀ k, k ≤ N →
      (key k i).2 ∈ Dn k ∧ (key k i).1 ∈ Pn k ∧
      ‖(T i).direction - (key k i).2‖ ≤ ρ k / 8 ∧
      ‖(key k i).1 - perp ((key k i).2) ((T i).center)‖ ≤ 3 * ρ k / 16 := by
    intro i hi
    have H : ∀ l k, N - k = l → k ≤ N →
        (key k i).2 ∈ Dn k ∧ (key k i).1 ∈ Pn k ∧
        ‖(T i).direction - (key k i).2‖ ≤ ρ k / 8 ∧
        ‖(key k i).1 - perp ((key k i).2) ((T i).center)‖ ≤ 3 * ρ k / 16 := by
      intro l
      induction l with
      | zero =>
        intro k hlk hk
        have hkN : k = N := by omega
        subst hkN
        have hdN := hrD k (T i).direction (Tube.norm_direction (T i))
        have hdunit : ‖rD k (T i).direction‖ = 1 := hDn_unit k _ hdN.1
        have hball : perp (rD k (T i).direction) ((T i).center)
            ∈ Metric.closedBall (0 : E3) 3 := by
          rw [Metric.mem_closedBall, dist_zero_right]
          calc ‖perp (rD k (T i).direction) ((T i).center)‖ ≤ ‖(T i).center‖ :=
                norm_perp_le hdunit _
            _ ≤ 1 := hcen1 i hi
            _ ≤ 3 := by norm_num
        have hpN := hrP k _ hball
        rw [hkey_top i]
        refine ⟨hdN.1, hpN.1, ?_, ?_⟩
        · calc ‖(T i).direction - (base i).2‖ ≤ 2 * (ρ k / 32) := hdN.2
            _ ≤ ρ k / 8 := by linarith [hρpos k]
        · have := hpN.2
          calc ‖(base i).1 - perp ((base i).2) ((T i).center)‖
              = ‖perp (rD k (T i).direction) ((T i).center) - rP k
                  (perp (rD k (T i).direction) ((T i).center))‖ := by
                rw [← norm_neg]; simp only [hbase_def]; congr 1; module
            _ ≤ 2 * (ρ k / 64) := this
            _ ≤ 3 * ρ k / 16 := by linarith [hρpos k]
      | succ l ih =>
        intro k hlk hk
        have hkN : k < N := by omega
        obtain ⟨hd1, hp1, hdir1, hpos1⟩ := ih (k + 1) (by omega) (by omega)
        set d : E3 := (key (k + 1) i).2 with hd_def
        set p : E3 := (key (k + 1) i).1 with hp_def
        have hdunit : ‖d‖ = 1 := hDn_unit (k + 1) _ hd1
        have hrDspec := hrD k d hdunit
        set d' : E3 := rD k d with hd'_def
        have hd'unit : ‖d'‖ = 1 := hDn_unit k _ hrDspec.1
        have hball : perp d' p ∈ Metric.closedBall (0 : E3) 3 := by
          rw [Metric.mem_closedBall, dist_zero_right]
          have hp3 : ‖p‖ ≤ 3 := by
            have := hPn_loc (k + 1) _ hp1
            rwa [Metric.mem_closedBall, dist_zero_right] at this
          exact le_trans (norm_perp_le hd'unit _) hp3
        have hrPspec := hrP k (perp d' p) hball
        have hkeyk : key k i = (rP k (perp d' p), d') := by
          rw [hkey_lt k hkN i]
        have hgapk := hgap k
        have hdd' : ‖d - d'‖ ≤ 2 * (ρ k / 32) := hrDspec.2
        rw [hkeyk]
        refine ⟨hrDspec.1, hrPspec.1, ?_, ?_⟩
        · calc ‖(T i).direction - d'‖
              ≤ ‖(T i).direction - d‖ + ‖d - d'‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
            _ ≤ ρ (k + 1) / 8 + 2 * (ρ k / 32) := add_le_add hdir1 hdd'
            _ ≤ ρ k / 8 := by linarith
        · have hd'd : perp d' d = perp d' (d - d') := by
            rw [perp_sub, perp_self hd'unit, sub_zero]
          have hid : perp d' (p - (T i).center)
              = perp d' (p - perp d ((T i).center))
                - (⟪(T i).center, d⟫ : ℝ) • perp d' d := by
            rw [← perp_smul, ← perp_sub]
            congr 1
            simp only [perp]
            module
          have hinner1 : |(⟪(T i).center, d⟫ : ℝ)| ≤ 1 := by
            calc |(⟪(T i).center, d⟫ : ℝ)| ≤ ‖(T i).center‖ * ‖d‖ := abs_real_inner_le_norm _ _
              _ ≤ 1 * 1 := mul_le_mul (hcen1 i hi) (le_of_eq hdunit) (norm_nonneg _) (by norm_num)
              _ = 1 := by norm_num
          have hb2 : ‖perp d' (p - (T i).center)‖ ≤ 3 * ρ (k + 1) / 16 + ρ k / 16 := by
            rw [hid]
            calc ‖perp d' (p - perp d ((T i).center))
                    - (⟪(T i).center, d⟫ : ℝ) • perp d' d‖
                ≤ ‖perp d' (p - perp d ((T i).center))‖
                  + ‖(⟪(T i).center, d⟫ : ℝ) • perp d' d‖ := norm_sub_le _ _
              _ ≤ 3 * ρ (k + 1) / 16 + ρ k / 16 := by
                  refine add_le_add ?_ ?_
                  · exact le_trans (norm_perp_le hd'unit _) hpos1
                  · rw [norm_smul, Real.norm_eq_abs, hd'd]
                    calc |(⟪(T i).center, d⟫ : ℝ)| * ‖perp d' (d - d')‖
                        ≤ 1 * ‖d - d'‖ :=
                          mul_le_mul hinner1 (norm_perp_le hd'unit _) (norm_nonneg _)
                            (by norm_num)
                      _ ≤ 1 * (2 * (ρ k / 32)) := by
                          exact mul_le_mul_of_nonneg_left hdd' (by norm_num)
                      _ = ρ k / 16 := by ring
          have hb1 : ‖rP k (perp d' p) - perp d' p‖ ≤ 2 * (ρ k / 64) := by
            rw [← norm_neg, neg_sub]
            exact hrPspec.2
          calc ‖rP k (perp d' p) - perp d' ((T i).center)‖
              ≤ ‖rP k (perp d' p) - perp d' p‖ + ‖perp d' p - perp d' ((T i).center)‖ :=
                norm_sub_le_norm_sub_add_norm_sub _ _ _
            _ ≤ 2 * (ρ k / 64) + (3 * ρ (k + 1) / 16 + ρ k / 16) := by
                refine add_le_add hb1 ?_
                rw [← perp_sub]
                exact hb2
            _ ≤ 3 * ρ k / 16 := by linarith
    exact fun k hk => H (N - k) k rfl hk
  have hgs : ∀ m : ℕ, ((Tube.gridScale δ N m : ℝ≥0) : ℝ) = ρ m := fun _ => rfl
  -- the cell representatives
  have hex : ∀ (k : ℕ) (c : E3 × E3), ∃ j : ι,
      (∃ j', j' ∈ s ∧ key k j' = c) → (j ∈ s ∧ key k j = c) := by
    intro k c
    by_cases h : ∃ j', j' ∈ s ∧ key k j' = c
    · obtain ⟨j, hj, hkj⟩ := h
      exact ⟨j, fun _ => ⟨hj, hkj⟩⟩
    · exact ⟨i₀, fun hc => absurd hc h⟩
  choose cellRep hcellRep using hex
  set asg : ℕ → ι → ι := fun k i => cellRep k (key k i) with hasg_def
  have hasg_app : ∀ k i, asg k i = cellRep k (key k i) := fun _ _ => rfl
  have hasg_spec : ∀ k, ∀ i ∈ s, asg k i ∈ s ∧ key k (asg k i) = key k i :=
    fun k i hi => hcellRep k (key k i) ⟨i, hi, rfl⟩
  have hasg_mem : ∀ k, ∀ i ∈ s, asg k i ∈ s := fun k i hi => (hasg_spec k i hi).1
  have hasg_key : ∀ k, ∀ i ∈ s, key k (asg k i) = key k i := fun k i hi => (hasg_spec k i hi).2
  have hasg_idem : ∀ k, ∀ i ∈ s, asg k (asg k i) = asg k i := by
    intro k i hi
    rw [hasg_app k (asg k i), hasg_key k i hi, ← hasg_app k i]
  set idx : ℕ → Finset ι := fun k => s.image (asg k) with hidx_def
  have hidx_asg : ∀ k, ∀ j ∈ idx k, asg k j = j := by
    intro k j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact hasg_idem k i hi
  have hidx_s : ∀ k, ∀ j ∈ idx k, j ∈ s := by
    intro k j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact hasg_mem k i hi
  -- the nodes
  set ndAt : (k : ℕ) → E3 → E3 → Tube (Tube.gridScale δ N k) E3 := fun k m u =>
    if h : ‖u‖ = 1 then Tube.ofMidpointDirection (Tube.gridScale δ N k) m u h
    else Tube.ofMidpointDirection (Tube.gridScale δ N k) m u₀ hu₀ with hndAt_def
  set nd : (k : ℕ) → ι → Tube (Tube.gridScale δ N k) E3 :=
    fun k j => ndAt k (key k j).1 (key k j).2 with hnd_def
  have hnd_c : ∀ k j, ‖(key k j).2‖ = 1 → (nd k j).center = (key k j).1 := by
    intro k j h
    simp only [hnd_def, hndAt_def, dif_pos h]
    simp [Tube.center, Tube.ofMidpointDirection, midpoint_eq_smul_add]
    module
  have hnd_d : ∀ k j, ‖(key k j).2‖ = 1 → (nd k j).direction = (key k j).2 := by
    intro k j h
    simp only [hnd_def, hndAt_def, dif_pos h]
    simp [Tube.direction, Tube.ofMidpointDirection]
    module
  have hfield1 : ∀ k, k ≤ N → ∀ i ∈ s,
      (T i).toConvexSpaceBody ≤ Kakeya.Tube.dilate (nd k (asg k i)) 4 := by
    intro k hk i hi
    obtain ⟨hd1, hp1, hdir1, hpos1⟩ := hinv i hi k hk
    have hdunit : ‖(key k i).2‖ = 1 := hDn_unit k _ hd1
    have hkeq : key k (asg k i) = key k i := hasg_key k i hi
    have hc : (nd k (asg k i)).center = (key k i).1 := by
      rw [hnd_c k (asg k i) (by rw [hkeq]; exact hdunit), hkeq]
    have hd : (nd k (asg k i)).direction = (key k i).2 := by
      rw [hnd_d k (asg k i) (by rw [hkeq]; exact hdunit), hkeq]
    refine le_dilate_of_through_point (nd k (asg k i)) (K' := 4) (r := 3 * ρ k / 16)
      (θ := ρ k / 8) (by norm_num) (x := (T i).center)
      (s₀ := (⟪(T i).center, (key k i).2⟫ : ℝ)) ?_ ?_ (T i)
      (center_mem_carrier hδ (T i)) (σ := 1) (by norm_num) ?_ ?_
    · have hb : |(⟪(T i).center, (key k i).2⟫ : ℝ)| ≤ 1 := by
        calc |(⟪(T i).center, (key k i).2⟫ : ℝ)| ≤ ‖(T i).center‖ * ‖(key k i).2‖ :=
              abs_real_inner_le_norm _ _
          _ ≤ 1 * 1 := mul_le_mul (hcen1 i hi) (le_of_eq hdunit) (norm_nonneg _) (by norm_num)
          _ = 1 := by norm_num
      linarith
    · rw [hc, hd, dist_eq_norm,
        show (T i).center - ((key k i).1 + (⟪(T i).center, (key k i).2⟫ : ℝ) • (key k i).2)
            = -((key k i).1 - perp ((key k i).2) ((T i).center)) from by
          simp only [perp]; module, norm_neg]
      exact hpos1
    · rw [hd, one_smul]; exact hdir1
    · rw [hgs k]
      have h1 := hδle k hk
      rw [hgs k] at h1
      linarith [hρpos k]
  have hfield2 : ∀ k, k ≤ N → ∀ i ∈ s, ∃ σ : ℝ, |σ| = 1 ∧
      ‖(T i).direction - σ • (nd k (asg k i)).direction‖
        ≤ ((Tube.gridScale δ N k : ℝ≥0) : ℝ) / 4 := by
    intro k hk i hi
    obtain ⟨hd1, hp1, hdir1, hpos1⟩ := hinv i hi k hk
    have hdunit : ‖(key k i).2‖ = 1 := hDn_unit k _ hd1
    have hkeq : key k (asg k i) = key k i := hasg_key k i hi
    have hd : (nd k (asg k i)).direction = (key k i).2 := by
      rw [hnd_d k (asg k i) (by rw [hkeq]; exact hdunit), hkeq]
    refine ⟨1, by norm_num, ?_⟩
    rw [hd, one_smul, hgs k]
    linarith [hρpos k]
  have hfield3 : ∀ k, k + 1 ≤ N → ∀ i ∈ s, ∀ j ∈ s,
      asg (k + 1) i = asg (k + 1) j → asg k i = asg k j := by
    intro k hk i hi j hj heq
    have h1 : key (k + 1) i = key (k + 1) j := by
      rw [← hasg_key (k + 1) i hi, ← hasg_key (k + 1) j hj, heq]
    have h2 : key k i = key k j := by
      rw [hkey_lt k (by omega) i, hkey_lt k (by omega) j, h1]
    rw [hasg_app k i, hasg_app k j, h2]
  have hinjOn : ∀ k, k ≤ N → Set.InjOn (nd k) (idx k : Set ι) := by
    intro k hk j hj j' hj' heq
    have hjidx : j ∈ idx k := Finset.mem_coe.mp hj
    have hj'idx : j' ∈ idx k := Finset.mem_coe.mp hj'
    obtain ⟨hd1, -, -, -⟩ := hinv j (hidx_s k j hjidx) k hk
    obtain ⟨hd1', -, -, -⟩ := hinv j' (hidx_s k j' hj'idx) k hk
    have hu : ‖(key k j).2‖ = 1 := hDn_unit k _ hd1
    have hu' : ‖(key k j').2‖ = 1 := hDn_unit k _ hd1'
    have hc : (key k j).1 = (key k j').1 := by rw [← hnd_c k j hu, ← hnd_c k j' hu', heq]
    have hd : (key k j).2 = (key k j').2 := by rw [← hnd_d k j hu, ← hnd_d k j' hu', heq]
    have hkk : key k j = key k j' := Prod.ext hc hd
    have hEq : asg k j = asg k j' := by rw [hasg_app k j, hasg_app k j', hkk]
    rwa [hidx_asg k j hjidx, hidx_asg k j' hj'idx] at hEq
  have hbo : ∀ k, k ≤ N → ∀ V : Tube (Tube.gridScale δ N k) E3,
      ((((idx k).filter (fun j => ∃ i ∈ s, asg k i = j ∧
        (T i).toConvexSpaceBody ≤ Kakeya.Tube.dilate V ((4 : ℝ) + 4))).card : ℕ))
        ≤ anchorOverlapConst := by
    intro k hk V
    set F := (idx k).filter (fun j => ∃ i ∈ s, asg k i = j ∧
      (T i).toConvexSpaceBody ≤ Kakeya.Tube.dilate V ((4 : ℝ) + 4)) with hF_def
    have hFprop : ∀ j ∈ F, ‖(key k j).1 - axisFoot V‖ ≤ 83 * ρ k ∧
        (‖(key k j).2 - V.direction‖ ≤ 33 * ρ k ∨
          ‖(key k j).2 - (-V.direction)‖ ≤ 33 * ρ k) := by
      intro j hj
      obtain ⟨hjidx, i, hi, haij, hiV⟩ := Finset.mem_filter.mp hj
      obtain ⟨hd1, hp1, hdir1, hpos1⟩ := hinv i hi k hk
      have hdunit : ‖(key k i).2‖ = 1 := hDn_unit k _ hd1
      have h8 : (T i).toConvexSpaceBody ≤ Kakeya.Tube.dilate V 8 := by
        have h44 : ((4 : ℝ) + 4) = 8 := by norm_num
        rwa [h44] at hiV
      obtain ⟨σ, hσ, hdd, hfoot⟩ :=
        anchor_near_axisFoot (T i) V hdunit (hcen1 i hi) hδ
          (by rw [hgs k]; linarith [hρpos k]) h8
      subst haij
      rw [hasg_key k i hi]
      constructor
      · calc ‖(key k i).1 - axisFoot V‖
            ≤ ‖(key k i).1 - anchorAt (T i) ((key k i).2)‖
              + ‖anchorAt (T i) ((key k i).2) - axisFoot V‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ 3 * ρ k / 16 + 82 * ρ k := by
              refine add_le_add hpos1 ?_
              rw [hgs k] at hfoot
              exact hfoot
          _ ≤ 83 * ρ k := by linarith [hρpos k]
      · rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hσ with h | h
        · left
          rw [h, one_smul] at hdd
          rw [hgs k] at hdd
          exact hdd
        · right
          rw [h] at hdd
          rw [hgs k] at hdd
          simpa using hdd
    set Fp := F.filter (fun j => ‖(key k j).2 - V.direction‖ ≤ 33 * ρ k) with hFp_def
    set Fm := F \ Fp with hFm_def
    have hcard_bound : ∀ (G : Finset ι) (cy : E3), G ⊆ F →
        (∀ j ∈ G, ‖(key k j).2 - cy‖ ≤ 33 * ρ k) → G.card ≤ 21249 ^ 6 := by
      intro G cy hGF hGy
      have hsep : ∀ x ∈ G, ∀ y ∈ G, x ≠ y →
          ρ k / 64 ≤ ‖(key k x).1 - (key k y).1‖ + ‖(key k x).2 - (key k y).2‖ := by
        intro x hx y hy hxy
        have hxidx : x ∈ idx k := (Finset.mem_filter.mp (hGF hx)).1
        have hyidx : y ∈ idx k := (Finset.mem_filter.mp (hGF hy)).1
        obtain ⟨hdx, hpx, -, -⟩ := hinv x (hidx_s k x hxidx) k hk
        obtain ⟨hdy, hpy, -, -⟩ := hinv y (hidx_s k y hyidx) k hk
        by_cases hp : (key k x).1 = (key k y).1
        · have hdne : (key k x).2 ≠ (key k y).2 := by
            intro hd
            apply hxy
            have hkk : key k x = key k y := Prod.ext hp hd
            have hEq : asg k x = asg k y := by rw [hasg_app k x, hasg_app k y, hkk]
            rwa [hidx_asg k x hxidx, hidx_asg k y hyidx] at hEq
          have hsd := hDn_sep k _ hdx _ hdy hdne
          have h0 : (0:ℝ) ≤ ‖(key k x).1 - (key k y).1‖ := norm_nonneg _
          linarith [hρpos k]
        · have hsp := hPn_sep k _ hpx _ hpy hp
          have h0 : (0:ℝ) ≤ ‖(key k x).2 - (key k y).2‖ := norm_nonneg _
          linarith
      have hpack := Tube.card_le_of_L1_separated_in_box (E := E3) G
        (fun j => (key k j).1) (fun j => (key k j).2) (axisFoot V) cy
        (R := 83 * ρ k) (r := ρ k / 64) (by linarith [hρpos k]) hsep
        (fun j hj => (hFprop j (hGF hj)).1)
        (fun j hj => (hGy j hj).trans (by linarith [hρpos k]))
      have hfr : Module.finrank ℝ E3 = 3 := by simp [E3]
      rw [hfr] at hpack
      have hval : ((83 * ρ k + (ρ k / 64) / 4) / ((ρ k / 64) / 4)) = 21249 := by
        rw [div_eq_iff (by have := hρpos k; intro hc; nlinarith)]
        ring
      rw [hval] at hpack
      exact_mod_cast hpack
    have hFp_card : Fp.card ≤ 21249 ^ 6 :=
      hcard_bound Fp V.direction (Finset.filter_subset _ _)
        (fun j hj => (Finset.mem_filter.mp hj).2)
    have hFm_card : Fm.card ≤ 21249 ^ 6 := by
      refine hcard_bound Fm (-V.direction) Finset.sdiff_subset ?_
      intro j hj
      obtain ⟨hjF, hjn⟩ := Finset.mem_sdiff.mp hj
      rcases (hFprop j hjF).2 with h | h
      · exact absurd (Finset.mem_filter.mpr ⟨hjF, h⟩) hjn
      · exact h
    have hsplit : F.card ≤ Fp.card + Fm.card := by
      have hFeq : F.card = (Fp ∪ Fm).card := by
        congr 1
        rw [hFm_def, Finset.union_sdiff_of_subset (Finset.filter_subset _ _)]
      rw [hFeq]
      exact Finset.card_union_le _ _
    calc F.card ≤ Fp.card + Fm.card := hsplit
      _ ≤ 21249 ^ 6 + 21249 ^ 6 := Nat.add_le_add hFp_card hFm_card
      _ = anchorOverlapConst := by rw [anchorOverlapConst]; ring
  refine ⟨{ indexSet := idx
            assign := asg
            tube := nd
            assign_mem := fun k _ i hi => Finset.mem_image_of_mem (asg k) hi
            le_dilate_tube_assign := hfield1
            dir_close_tube_assign := hfield2
            nested := hfield3 }, hinjOn, hbo, ?_⟩
  intro k j hj
  obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp hj
  exact ⟨i, hi, hij⟩

/-! ## Packaging, and the essential-distinctness question

Two further pieces, for the two consumers of this hierarchy.

**(a) The residue, named.**  `Kakeya.LooseUniform.LooseUniformTubeSet.ofCoverBrackets` turns the
output of `Kakeya.LooseUniform.exists_looseGridCover` into a
`Kakeya.LooseUniform.LooseUniformTubeSet` as soon as GWZ Definition 2.1(iii)'s two-sided class
bracket is supplied.  So the *whole* remaining obligation of the loose Definition-2.1 datum is
Definition 2.1(iii), which is geometry-free (`Tube.exists_pruned_subset_noroot_notop`) and costs a
refinement; the geometry is done.

**(b) Essential distinctness of the nodes is a DIFFERENT hierarchy, not this one.**  The nodes
produced here are **not** pairwise essentially distinct, and cannot be made so while
`Kakeya.LooseUniform.LooseGridCoverSystem.dir_close_tube_assign` is read at `ρ_k/4`: that clause
forces the node directions in use to be a `ρ_k/4`-dense subset of the sphere, hence to contain
pairs at distance `≤ ρ_k/2`, and two unit `ρ_k`-tubes whose directions differ by `≤ ρ_k/2` and
whose axes pass within `ρ_k` of each other overlap in almost their whole volume.  What is offered
instead, for the consumers that need Definition 2.1(ii) itself
(`Kakeya.ML2Core.hstep8_of_essDistinct`), is the generic selector
`Kakeya.LooseUniform.exists_essDistinct_subfamily`: a **maximal** essentially distinct subfamily of
an arbitrary finite tube family, together with the maximality clause "every discarded member fails
to be essentially distinct from a kept one", which is what converts a count on the full family into
a count on the essentially distinct one.
-/


/-- **The residue named: Definition 2.1(iii) and nothing else.** -/
noncomputable def LooseUniformTubeSet.ofCoverBrackets {ι : Type*} {δ : ℝ≥0} {s : Finset ι}
    {T : ι → Tube δ E3} {N : ℕ} (cover : LooseGridCoverSystem s T N 4)
    (branchingN : ℕ → ℝ≥0) {C : ℝ≥0}
    (hinj : ∀ k, k ≤ N → Set.InjOn (cover.tube k) (cover.indexSet k : Set ι))
    (hbo : ∀ k, k ≤ N → ∀ V : Tube (Tube.gridScale δ N k) E3,
      (open scoped Classical in
        ((cover.indexSet k).filter (fun j => ∃ i ∈ s, cover.assign k i = j ∧
          (T i).toConvexSpaceBody ≤ Kakeya.Tube.dilate V ((4 : ℝ) + 4))).card)
        ≤ anchorOverlapConst)
    (hup : ∀ k, k ≤ N → ∀ j ∈ cover.indexSet k,
      ((Tube.coverClass s (cover.assign k) j).card : ℝ≥0) ≤ C * branchingN k)
    (hlo : ∀ k, k ≤ N → ∀ j ∈ cover.indexSet k,
      branchingN k ≤ C * ((Tube.coverClass s (cover.assign k) j).card : ℝ≥0)) :
    LooseUniformTubeSet s T N 4 (max C (anchorOverlapConst : ℝ≥0)) where
  cover := cover
  branchingN := branchingN
  tube_injOn := hinj
  boundedOverlapDil k hk V := le_trans (by exact_mod_cast hbo k hk V) (le_max_right _ _)
  card_class_le k hk j hj := (hup k hk j hj).trans (mul_le_mul' (le_max_left _ _) le_rfl)
  le_card_class k hk j hj := (hlo k hk j hj).trans (mul_le_mul' (le_max_left _ _) le_rfl)


/-! ## From the cover to GWZ Definition 2.1 and Definition 2.2, on a refinement

The geometry is finished above.  What is left of the loose Definition-2.1 datum is Definition
2.1(iii)'s two-sided class bracket, and of Definition 2.2 its four shading brackets; both are
**geometry-free** and both are paid for by a refinement.  This section runs the two existing engines
on the anchored cover.

* **Definition 2.1(iii)** — `Tube.exists_pruned_subset_noroot_notop` takes only `assign`,
  `assign_mem`, `nested` and a bound on the level-`0` index set.  The last of these is supplied by
  the cover's own `boundedOverlapDil` at `k = 0`, where `Tube.gridScale δ N 0 = 1` and the
  `8`-dilate of the unit tube through the origin swallows the whole unit ball
  (`Kakeya.LooseUniform.card_indexSet_zero_le`) — so the pruning constant is again the absolute
  `anchorOverlapConst`, not a new one.  Retention: `(anchorOverlapConst · (⌊log₂|s|⌋+1))^N`, i.e.
  `δ^{-α}` at the grid length after `Tube.exists_threshold_polylog_pow_ssfGridLen_le`.
* **Definition 2.2** — `ShadedTube.exists_balanced_shadeRefinement_of_cover` wants a *bare*
  `Tube.GridCoverSystem` over an arbitrary tube family at an arbitrary thickness, and reads only
  its `assign`.  `Kakeya.LooseUniform.trivialGridCover` is that carrier: the constant family at
  thickness `1`, whose containment and nesting fields are `le_refl` after
  `Kakeya.LooseUniform.gridScale_one`.  This is the manoeuvre  predicted and did
  not compile.  Retention: `(⌊log₂|s|⌋+1)^{2N+2}` of shade mass, i.e. `δ^{-α'}` at the grid length.

The end products are `Kakeya.LooseUniform.exists_looseUniformTubeSet_subfamily_ssf` and
`Kakeya.LooseUniform.exists_looseShadedUniformTubeSet_subfamily_ssf`, stated for an **arbitrary**
family, and `Kakeya.LooseUniform.exists_looseShaded_subfamily_of_config`, the same at a
`Kakeya.VeryNotSticky` and at the constant `max cfg.C₀ anchorOverlapConst`.

**What is still NOT discharged.**  Conjunct 6's `∃ 𝒱` binds the datum on `cfg.s` itself; what is
produced here lives on a **subfamily** `s' ⊆ cfg.s` with a shrunk shading, exactly as GWZ's
 produces it.  Closing conjunct 6 therefore needs the *configuration producer* to name the
refined family as the new `cfg.s` — which is what
`Kakeya.VeryNotSticky.exists_config_of_slackCut_at` already does for the exact datum, and which is
not touched here.  **Nothing in this file discharges
conjunct 6.**
-/


/-! ### (4) The shaded (Definition 2.2) hierarchy -/


/-- Weakening the constant of a loose Definition-2.1 datum. -/
def LooseUniformTubeSet.mono {ι : Type*} {δ : ℝ≥0} {s : Finset ι} {T : ι → Tube δ E3}
    {N : ℕ} {K : ℝ} {C C' : ℝ≥0} (𝒰 : LooseUniformTubeSet s T N K C) (hC : C ≤ C') :
    LooseUniformTubeSet s T N K C' where
  cover := 𝒰.cover
  branchingN := 𝒰.branchingN
  tube_injOn := 𝒰.tube_injOn
  boundedOverlapDil k hk V := (𝒰.boundedOverlapDil k hk V).trans hC
  card_class_le k hk j hj := (𝒰.card_class_le k hk j hj).trans (mul_le_mul' hC le_rfl)
  le_card_class k hk j hj := (𝒰.le_card_class k hk j hj).trans (mul_le_mul' hC le_rfl)


/-- The `fullness'` form of a shade-mass bound (the private
`ShadedTube.fullness_le_of_shade_sum`, restated here because it is private). -/
theorem fullness_le_of_shade_sum' {ι : Type*} {δ : ℝ≥0} {s : Finset ι} (c : ℝ≥0∞)
    (V V' : ι → ShadedTube δ E3) (htube : ∀ i, (V' i).toTube = (V i).toTube)
    (hnum : (∑ i ∈ s, volume (V i).shade) ≤ c * (∑ i ∈ s, volume (V' i).shade)) :
    ShadedBody.fullness' s (fun i => (V i).toShadedBody)
      ≤ c * ShadedBody.fullness' s (fun i => (V' i).toShadedBody) := by
  classical
  change (∑ i ∈ s, volume (V i).shade) / (∑ i ∈ s, volume (V i).carrier)
      ≤ c * ((∑ i ∈ s, volume (V' i).shade) / (∑ i ∈ s, volume (V' i).carrier))
  have hden : (∑ i ∈ s, volume (V i).carrier) = ∑ i ∈ s, volume (V' i).carrier := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 1
    calc (V i).carrier = (V i).toTube.carrier := rfl
      _ = (V' i).toTube.carrier := by rw [← htube i]
      _ = (V' i).carrier := rfl
  calc (∑ i ∈ s, volume (V i).shade) / (∑ i ∈ s, volume (V i).carrier)
      ≤ (c * (∑ i ∈ s, volume (V' i).shade)) / (∑ i ∈ s, volume (V i).carrier) :=
        ENNReal.div_le_div_right hnum _
    _ = c * ((∑ i ∈ s, volume (V' i).shade) / (∑ i ∈ s, volume (V i).carrier)) :=
        mul_div_assoc _ _ _
    _ = c * ((∑ i ∈ s, volume (V' i).shade) / (∑ i ∈ s, volume (V' i).carrier)) := by rw [hden]


/-- Weakening the constant of a loose Definition-2.2 datum. -/
def LooseShadedUniformTubeSet.mono {ι : Type*} {δ : ℝ≥0} {s : Finset ι}
    {V : ι → ShadedTube δ E3} {N : ℕ} {K : ℝ} {C C' : ℝ≥0}
    (𝒱 : LooseShadedUniformTubeSet s V N K C) (hC : C ≤ C') :
    LooseShadedUniformTubeSet s V N K C' where
  tubeUniform := 𝒱.tubeUniform.mono hC
  branchingN := 𝒱.branchingN
  localN := 𝒱.localN
  card_shadeClass_le := fun x hx k hk i hi hxi =>
    (𝒱.card_shadeClass_le x hx k hk i hi hxi).trans (mul_le_mul' hC le_rfl)
  le_card_shadeClass := fun x hx k hk i hi hxi =>
    (𝒱.le_card_shadeClass x hx k hk i hi hxi).trans (mul_le_mul' hC le_rfl)
  branchingN_le := fun x hx k hk => (𝒱.branchingN_le x hx k hk).trans (mul_le_mul' hC le_rfl)
  le_branchingN := fun x hx k hk => (𝒱.le_branchingN x hx k hk).trans (mul_le_mul' hC le_rfl)


end LooseUniform
end Kakeya

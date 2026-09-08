/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.TangentialSlabFamily
public import Kakeya.DimensionThree.MainLemma2.SlabMultKTGeneral

/-!
# The aligned anisotropic transport: clause (A2) at a `δ`-free constant

**What this file settles.** GWZ's tangential case charges the factor `δ^{-O(τ')}` of (105)
(GWZ) to the **multiplicity**: it is the number of slabs
`𝕎''_S` that one fibre `𝕎''_{Y}(x)` can meet, which (103) bounds by `δ^{-O(τ')}` because the
fibre spans the typical angle `θ ≤ δ^{-τ'} a/b` while each slab spans only the slab's own
angular width `a/b`. Inside one slab GWZ pay nothing: the linear change of variables
"converts `S` to `B₁` and converts `𝕎''_S` to a set `𝕋̃` of `ρ₂`-tubes in `B₁`" with
`λ(𝕋̃, Y_𝕋̃) = λ(𝕎''_S, Y_{𝕎''_S})` — *equality*, no fullness loss.

The tree already charges the fibre count where GWZ do: the `δ^{-2τ'}` is written out in the
statement of `Kakeya.VeryNotSticky.tangentialSlabDecomp` and budgeted at the quarter
`C_sep·τ'/4` (see `Kakeya.VeryNotSticky.slabDecompFibreConstant`'s docstring). What this file
supplies is the *other* half of GWZ's accounting: that the transport inside one slab really
is `δ`-free — i.e. that clause (A2) of `Kakeya.VeryNotSticky.IsAnisotropicSlabRescale` holds
at a comparison constant that is a polynomial in `bd.C₀` and carries **no power of `δ`** —
**provided the body's normal is aligned with the slab's to within a `δ`-free multiple of the
slab's own angular width `a/b`**.

That proviso is the whole content. `Kakeya.VeryNotSticky.aniLin_rank_two_gap` and the
docstring of `Kakeya.VeryNotSticky.ethickness_aniLin_image_ge` record that the transport's
unconditional rank-`2` lower bound misses (A2) by the factor `a/b`, and
`Kakeya.VeryNotSticky.norm_aniLin_le_of_inner_le`'s docstring records that the missing input is
a tilt bound `≲ a/b`. `Kakeya.VeryNotSticky.IsDenseSlab.angle` supplies only `2θ`, and in the
tangential case `θ` may be as large as `δ^{-τ'} a/b`; the gap between the two is exactly one
factor of `δ^{-τ'}`, and it is that factor which, charged to the enclosure constant
`Kakeya.VeryNotSticky.ktRho2EnclosureConstant`, becomes the loss-to-fullness ratio of


**Why a `δ`-free constant costs nothing.** The comparison constant of
`Kakeya.VeryNotSticky.KTRho2ScaleData` enters its producer
`Kakeya.VeryNotSticky.eventually_ktRho2ScaleData_nonslab` only through the four thresholds
`hT1`-`hT4`, each of the form `∀ᶠ δ, δ^{positive exponent} ≤ (a constant)⁻¹`. A larger
`δ`-free constant moves the threshold and nothing else. A factor `δ^{-cτ'}`, by contrast,
turns `hT3`/`hT4` into `c·τ' ≤ η` and `c·τ' ≤ ϱ/2`, which
`Kakeya.VeryNotSticky.enclosure_tau'_charge_refuted` below refutes outright from
`Kakeya.VeryNotSticky.CaseParams`. That asymmetry is the reason the cost must be re-sited.

## Contents

* `Kakeya.VeryNotSticky.abs_inner_middle_le_of_lineAngle_le` — the alignment estimate moved
  from the body's normal (`bodyNormal`, the rank-`2` frame vector) to the *middle* frame
  vector, which is the one the transport stretches;
* `Kakeya.VeryNotSticky.thickness_one_aniRescale_image_le_of_aligned` — the rank-`1` upper
  bound of (A2), the first of the two inequalities
  `Kakeya.VeryNotSticky.hasThicknesses_slabRescale_image_of_two` leaves open;
* `Kakeya.VeryNotSticky.thickness_two_slabRescale_image_ge` — the rank-`2` lower bound, the
  second one, by a volume comparison: the transport multiplies every volume by the same
  factor, and it takes the slab it normalises *onto* the unit ball
  (`Kakeya.VeryNotSticky.slabRescale_image_generalSlab`), so the factor can be eliminated
  without ever computing a determinant;
* `Kakeya.VeryNotSticky.hasThicknesses_slabRescale_image_of_aligned` — **clause (A2) in full,
  at the `δ`-free constant `Kakeya.VeryNotSticky.alignedRescaleConstant bd.C₀ κ`**;
* `Kakeya.VeryNotSticky.ktRho2_L_le_five_thirds` — the fullness clause stays where the existing
  tree puts it: `L = max 1 (10η/wη) ≤ 5/3` from `hηKT` alone, with no relation between `we`
  and `wη`;
* `Kakeya.VeryNotSticky.enclosure_tau'_charge_refuted` — and the alternative, charging the
  `δ^{-τ'}` to the enclosure constant, is refuted by `CaseParams` at every `k ≥ 1`;
* `Kakeya.VeryNotSticky.axisAngle_le_two_theta_of_le_ratio` — the tightened alignment clause
  *implies* the existing `2θ` clause, so no consumer of
  `Kakeya.VeryNotSticky.IsSlabFamily.S3` or `Kakeya.VeryNotSticky.IsDenseSlab.angle` changes
  direction under the re-cut.

Every declaration in this file is new.
-/

@[expose] public section

open scoped NNReal ENNReal

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set Topology Filter
open scoped NNReal ENNReal RealInnerProductSpace

universe u

/-- Shorthand for the ambient space of the tangential case. -/
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

noncomputable section

/-! ### The alignment estimate on the middle frame vector -/

/-- **The alignment estimate, moved to the middle frame vector.**

`Kakeya.VeryNotSticky.bodyNormal` is the rank-`2` vector `e₂` of the body's outer-prism frame;
the vector the anisotropic transport actually stretches out of shape is the *middle* one, `e₁`.
Since `e₁ ⊥ e₂`, Bessel's identity in the orthonormal frame gives
`⟪n, e₁⟫² ≤ 1 - ⟪n, e₂⟫² = sin²∠(e₂, n)`, and `sin x ≤ x` on `[0, π/2]`, where
`Kakeya.NonSlab.lineAngle` lives. So a bound on the *normal* angle is a bound on the middle
vector's component along `n`, at no loss. -/
theorem abs_inner_middle_le_of_lineAngle_le (W : ConvexSpaceBody E₃) (n : E₃) (hn : ‖n‖ = 1) {κ : ℝ}
    (h : NonSlab.lineAngle (bodyNormal W) n ≤ κ) :
    |⟪n, outerPrism.basis (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3))
      W.isCompact' W.nonempty' 1⟫| ≤ κ := by
  set hfr : Module.finrank ℝ E₃ = 3 := finrank_euclideanSpace_fin with hfr_def
  set e := outerPrism.basis hfr W.isCompact' W.nonempty' with he_def
  have he2 : e 2 = bodyNormal W := by
    rw [he_def, bodyNormal, NonSlab.bodyNormal_eq]
  have hsum : ∑ i, (⟪n, e i⟫ : ℝ) * ⟪e i, n⟫ = ⟪n, n⟫ := e.sum_inner_mul_inner n n
  rw [Fin.sum_univ_three] at hsum
  have hnn : (⟪n, n⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  have hsym : ∀ i, (⟪n, e i⟫ : ℝ) = ⟪e i, n⟫ := fun i => real_inner_comm _ _
  rw [hsym 0, hsym 1, hsym 2, hnn] at hsum
  -- `⟪e 1, n⟫² ≤ 1 - ⟪e 2, n⟫²`
  have hbess : (⟪e 1, n⟫ : ℝ) ^ 2 ≤ 1 - (⟪e 2, n⟫ : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (⟪e 0, n⟫ : ℝ)]
  have hne2 : ‖e 2‖ = 1 := e.norm_eq_one 2
  have hang : NonSlab.lineAngle (e 2) n = Real.arccos |(⟪e 2, n⟫ : ℝ)| :=
    NonSlab.lineAngle_eq_arccos_abs_inner hne2 hn
  have hsin : Real.sin (NonSlab.lineAngle (e 2) n) = Real.sqrt (1 - (⟪e 2, n⟫ : ℝ) ^ 2) := by
    rw [hang, Real.sin_arccos, sq_abs]
  have hle : Real.sin (NonSlab.lineAngle (e 2) n) ≤ κ := by
    refine le_trans (Real.sin_le (NonSlab.lineAngle_nonneg _ _)) ?_
    rw [he2]; exact h
  rw [hsin] at hle
  calc |(⟪n, e 1⟫ : ℝ)| = Real.sqrt ((⟪e 1, n⟫ : ℝ) ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, hsym 1]
    _ ≤ Real.sqrt (1 - (⟪e 2, n⟫ : ℝ) ^ 2) := Real.sqrt_le_sqrt hbess
    _ ≤ κ := hle

/-! ### The rank-`1` upper bound of (A2), from the alignment -/

/-- **The rank-`1` upper bound of clause (A2), from the alignment** — the first of the two
inequalities that `Kakeya.VeryNotSticky.hasThicknesses_slabRescale_image_of_two` leaves as
hypotheses.

The body is contained in the box of its own outer prism, of half-widths `τ₀, τ₁, τ₂`; the
image of that box under `Kakeya.VeryNotSticky.aniRescale` lies within
`τ₁‖L e₁‖ + τ₂‖L e₂‖` of the line through `L(centre)` in the direction `L e₀`, because the
`e₀`-component of every displacement is absorbed by moving along that line. The two norms are
`Kakeya.VeryNotSticky.norm_aniLin_le_of_inner_le` at `s` and
`Kakeya.VeryNotSticky.norm_aniLin_le_max`. **`s` is where `δ` would enter**: the `β s` term is
the tilt's price, and at `α = 1/r₁`, `β = b/(a r₁)` it is `s · b/(a r₁)`, which is `∼ 1/r₁`
exactly when `s ≲ a/b`. -/
theorem thickness_one_aniRescale_image_le_of_aligned (cc : E₃) (n : E₃) (hn : ‖n‖ = 1)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    {X : Set E₃} (hXc : IsCompact X) (hXne : X.Nonempty) {t₁ t₂ s : ℝ}
    (h1 : Metric.thickness ℝ X 1 ≤ t₁) (h2 : Metric.thickness ℝ X 2 ≤ t₂)
    (hs : 0 ≤ s)
    (halign : |⟪n, outerPrism.basis (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3)) hXc hXne 1⟫|
      ≤ s) :
    Metric.thickness ℝ (aniRescale cc n hn hα.ne' hβ.ne' '' X) 1
      ≤ t₁ * (α + β * s) + t₂ * (α + β) := by
  have hα' : (0:ℝ) ≤ α := hα.le
  have hβ' : (0:ℝ) ≤ β := hβ.le
  set hfr : Module.finrank ℝ E₃ = 3 := finrank_euclideanSpace_fin with hfr_def
  set e := outerPrism.basis hfr hXc hXne with he_def
  set c₀ := outerPrism.center hfr hXc hXne with hc_def
  have ht1 : (0:ℝ) ≤ t₁ := le_trans (Metric.thickness_nonneg X 1) h1
  have ht2 : (0:ℝ) ≤ t₂ := le_trans (Metric.thickness_nonneg X 2) h2
  have hR : (0:ℝ) ≤ t₁ * (α + β * s) + t₂ * (α + β) := by positivity
  set A : AffineSubspace ℝ E₃ :=
    AffineSubspace.mk' (aniRescale cc n hn hα.ne' hβ.ne' c₀) (ℝ ∙ (aniLin n α β (e 0)))
    with hA_def
  have hrank : Module.rank ℝ A.direction ≤ (1 : ℕ) := by
    rw [hA_def, AffineSubspace.direction_mk']
    simpa using rank_span_le ({aniLin n α β (e 0)} : Set E₃)
  refine Metric.thickness_le_of_cthickening hR hrank ?_
  rintro _ ⟨x, hx, rfl⟩
  set v : E₃ := x - c₀ with hv_def
  set v0 : ℝ := ⟪e 0, v⟫ with hv0
  set v1 : ℝ := ⟪e 1, v⟫ with hv1
  set v2 : ℝ := ⟪e 2, v⟫ with hv2
  have hdecomp : v = v0 • e 0 + v1 • e 1 + v2 • e 2 := by
    have := e.sum_repr v
    rw [Fin.sum_univ_three] at this
    simp only [OrthonormalBasis.repr_apply_apply] at this
    rw [← this, hv0, hv1, hv2]
  have hmemA : v0 • aniLin n α β (e 0) + aniRescale cc n hn hα.ne' hβ.ne' c₀ ∈ A := by
    rw [hA_def, AffineSubspace.mem_mk']
    have hvs : (v0 • aniLin n α β (e 0) + aniRescale cc n hn hα.ne' hβ.ne' c₀)
        -ᵥ aniRescale cc n hn hα.ne' hβ.ne' c₀ = v0 • aniLin n α β (e 0) := by simp
    rw [hvs]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  refine Metric.mem_cthickening_of_dist_le _ _ _ _ hmemA ?_
  have hkey : aniRescale cc n hn hα.ne' hβ.ne' x
      - (v0 • aniLin n α β (e 0) + aniRescale cc n hn hα.ne' hβ.ne' c₀)
      = v1 • aniLin n α β (e 1) + v2 • aniLin n α β (e 2) := by
    rw [aniRescale_apply, aniRescale_apply]
    have hxx : x - cc - (c₀ - cc) = v := by rw [hv_def]; abel
    have : aniLin n α β (x - cc) - aniLin n α β (c₀ - cc) = aniLin n α β v := by
      rw [← map_sub, hxx]
    rw [show aniLin n α β (x - cc) - (v0 • aniLin n α β (e 0) + aniLin n α β (c₀ - cc))
        = (aniLin n α β (x - cc) - aniLin n α β (c₀ - cc)) - v0 • aniLin n α β (e 0) by abel,
      this, hdecomp]
    simp only [map_add, map_smul]
    abel
  rw [dist_eq_norm, hkey]
  have hb1 : |v1| ≤ Metric.thickness ℝ X 1 := by
    have := outerPrism.basis_repr_le hfr hXc hXne hx 1
    simpa [hv1, hv_def, OrthonormalBasis.repr_apply_apply, inner_sub_right] using this
  have hb2 : |v2| ≤ Metric.thickness ℝ X 2 := by
    have := outerPrism.basis_repr_le hfr hXc hXne hx 2
    simpa [hv2, hv_def, OrthonormalBasis.repr_apply_apply, inner_sub_right] using this
  have hne1 : ‖e 1‖ = 1 := e.norm_eq_one 1
  have hne2 : ‖e 2‖ = 1 := e.norm_eq_one 2
  have ha1 : ‖aniLin n α β (e 1)‖ ≤ α + β * s := by
    have := norm_aniLin_le_of_inner_le n hn hα' hβ' (e 1) halign
    rwa [hne1, mul_one] at this
  have ha2 : ‖aniLin n α β (e 2)‖ ≤ α + β := by
    have := norm_aniLin_le_max n hn hα' hβ' (e 2)
    rw [hne2, mul_one] at this
    exact this.trans (by cases max_choice α β with
      | inl h => rw [h]; linarith
      | inr h => rw [h]; linarith)
  calc ‖v1 • aniLin n α β (e 1) + v2 • aniLin n α β (e 2)‖
      ≤ ‖v1 • aniLin n α β (e 1)‖ + ‖v2 • aniLin n α β (e 2)‖ := norm_add_le _ _
    _ = |v1| * ‖aniLin n α β (e 1)‖ + |v2| * ‖aniLin n α β (e 2)‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ t₁ * (α + β * s) + t₂ * (α + β) := by
        have hp1 : (0:ℝ) ≤ α + β * s := by positivity
        have hp2 : (0:ℝ) ≤ α + β := by positivity
        gcongr
        · exact hb1.trans h1
        · exact hb2.trans h2

/-! ### The rank-`2` lower bound of (A2), by a volume comparison -/

/-- **Volume floor from a three-term thickness profile**, the general-profile companion of
`Kakeya.VeryNotSticky.volume_ge_of_tubeProfile`: `6` is `3!`, the reciprocal of the
inscribed-simplex constant of `Convex.prod_thickness_le_volumeReal`, and `C₀³` is one factor
of `C₀` per axis. -/
theorem volumeReal_ge_of_threeProfile {K : Set E₃} (hconv : Convex ℝ K)
    (hbdd : Bornology.IsBounded K)
    {C₀ : ℝ≥0} (hC₀ : 1 ≤ C₀) {t0 t1 t2 : ℝ} (h0 : 0 ≤ t0) (h1 : 0 ≤ t1) (h2 : 0 ≤ t2)
    (hprof : Kakeya.HasThicknesses K C₀ ![t0, t1, t2]) :
    (t0 * t1 * t2) / (6 * (C₀ : ℝ) ^ 3) ≤ MeasureTheory.volume.real K := by
  have hC0ne : (C₀ : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast (lt_of_lt_of_le zero_lt_one hC₀))
  have e0 : (C₀ : ℝ)⁻¹ * t0 ≤ Metric.thickness ℝ K 0 := by simpa using (hprof 0).1
  have e1 : (C₀ : ℝ)⁻¹ * t1 ≤ Metric.thickness ℝ K 1 := by simpa using (hprof 1).1
  have e2 : (C₀ : ℝ)⁻¹ * t2 ≤ Metric.thickness ℝ K 2 := by simpa using (hprof 2).1
  have ha0 : 0 ≤ (C₀ : ℝ)⁻¹ * t0 := by positivity
  have ha1 : 0 ≤ (C₀ : ℝ)⁻¹ * t1 := by positivity
  have ha2 : 0 ≤ (C₀ : ℝ)⁻¹ * t2 := by positivity
  have ht0 : 0 ≤ Metric.thickness ℝ K 0 := Metric.thickness_nonneg K 0
  have ht1 : 0 ≤ Metric.thickness ℝ K 1 := Metric.thickness_nonneg K 1
  have h01 : ((C₀ : ℝ)⁻¹ * t0) * ((C₀ : ℝ)⁻¹ * t1)
      ≤ Metric.thickness ℝ K 0 * Metric.thickness ℝ K 1 := mul_le_mul e0 e1 ha1 ht0
  have hprod_lower :
      (((C₀ : ℝ)⁻¹ * t0) * ((C₀ : ℝ)⁻¹ * t1)) * ((C₀ : ℝ)⁻¹ * t2)
        ≤ Metric.thickness ℝ K 0 * Metric.thickness ℝ K 1 * Metric.thickness ℝ K 2 :=
    mul_le_mul h01 e2 ha2 (mul_nonneg ht0 ht1)
  have hvol : (6 : ℝ)⁻¹ *
      (Metric.thickness ℝ K 0 * Metric.thickness ℝ K 1 * Metric.thickness ℝ K 2) ≤
      MeasureTheory.volume.real K := by
    have hv0 := Convex.prod_thickness_le_volumeReal (E := E₃) hconv hbdd
    rw [finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3)] at hv0
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ] at hv0
    norm_num [Metric.lt_volume_convexHull.c] at hv0
    simpa using hv0
  have hLHS : (t0 * t1 * t2) / (6 * (C₀ : ℝ) ^ 3) =
      (6 : ℝ)⁻¹ * (((C₀ : ℝ)⁻¹ * t0) * ((C₀ : ℝ)⁻¹ * t1)) * ((C₀ : ℝ)⁻¹ * t2) := by
    field_simp [hC0ne]
  rw [hLHS]
  nlinarith [hprod_lower, hvol, ha0, ha1, ha2, ht0, ht1,
    show 0 ≤ (6 : ℝ)⁻¹ by positivity]

/-- **The volume ratio identity — the determinant eliminated.**

An affine automorphism multiplies every volume by `|det|` (`Kakeya.volume_affineImage`), and
`Kakeya.VeryNotSticky.slabRescale` carries the slab it normalises *onto* the unit ball
(`Kakeya.VeryNotSticky.slabRescale_image_generalSlab`, an equality). Multiplying the two
identities crosswise cancels `|det|`, so the volume of the image of an arbitrary set is pinned
by the volume of the unit ball and the volume of the slab, and no determinant of
`Kakeya.VeryNotSticky.aniLin` ever has to be computed. -/
theorem volume_slabRescale_image_mul_volume_generalSlab (c n : E₃) (hn : ‖n‖ = 1)
    {r₁ ratio : ℝ} (hr₁ : 0 < r₁)
    (hratio : 0 < ratio) (X : Set E₃) :
    volume (slabRescale c n hn hr₁ hratio '' X) *
        volume (generalSlab c n hn hr₁ hratio).carrier
      = volume (Metric.closedBall (0 : E₃) 1) * volume X := by
  set L := slabRescale c n hn hr₁ hratio with hL
  set D : ℝ≥0∞ := ENNReal.ofReal |LinearMap.det (L.linear : E₃ →ₗ[ℝ] E₃)| with hD
  have hX : volume (L '' X) = D * volume X := Kakeya.volume_affineImage L X
  have hS : volume (L '' (generalSlab c n hn hr₁ hratio).carrier)
      = D * volume (generalSlab c n hn hr₁ hratio).carrier :=
    Kakeya.volume_affineImage L _
  rw [slabRescale_image_generalSlab c n hn hr₁ hratio] at hS
  rw [hX, hS]
  ring

/-- The unit ball of `ℝ³` has volume at least `1/6`, from the inscribed simplex alone: its
three affine thicknesses are all `1`. Only a positive lower bound is needed below, so the
sharp value `4π/3` is not required. -/
theorem ofReal_six_inv_le_volume_unitBall :
    ENNReal.ofReal ((1 : ℝ) / 6) ≤ volume (Metric.closedBall (0 : E₃) 1) := by
  have hprof : Kakeya.HasThicknesses (Metric.closedBall (0 : E₃) 1) 1 ![(1:ℝ), 1, 1] := by
    intro k
    have hk : (k : ℕ) < Module.finrank ℝ E₃ := by
      rw [finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3)]; exact k.2
    have hle := Metric.thickness_closedBall_le (𝕜 := ℝ) (x := (0 : E₃))
      (r := (1:ℝ)) zero_le_one (k : ℕ)
    have hge := Metric.thickness_closedBall_ge (x := (0 : E₃)) (r := (1:ℝ)) zero_le_one hk
    fin_cases k <;> simp_all
  have hfl := volumeReal_ge_of_threeProfile (K := Metric.closedBall (0 : E₃) 1)
    (convex_closedBall _ _) Metric.isBounded_closedBall (le_refl (1 : ℝ≥0))
    zero_le_one zero_le_one zero_le_one hprof
  norm_num at hfl
  rw [MeasureTheory.Measure.real] at hfl
  have hne : volume (Metric.closedBall (0 : E₃) 1) ≠ ⊤ :=
    (Metric.isBounded_closedBall (x := (0:E₃)) (r := 1)).measure_lt_top.ne
  exact (ENNReal.ofReal_le_iff_le_toReal hne).mpr (by linarith)

/-- `volume s ≤ 2³ · τ₀ τ₁ τ₂`, in the form the comparison below consumes: upper bounds for
the three thicknesses give an upper bound for the volume. -/
theorem volume_le_of_thickness_bounds {s : Set E₃} (hs : Bornology.IsBounded s) {u0 u1 u2 : ℝ}
    (h0 : Metric.thickness ℝ s 0 ≤ u0) (h1 : Metric.thickness ℝ s 1 ≤ u1)
    (h2 : Metric.thickness ℝ s 2 ≤ u2) :
    volume s ≤ ENNReal.ofReal (8 * (u0 * u1 * u2)) := by
  have hv := volume_le_prod_thickness (E := E₃) hs
  rw [finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3)] at hv
  rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
    Finset.prod_range_zero, one_mul] at hv
  refine hv.trans ?_
  have hu0 : (0:ℝ) ≤ u0 := le_trans (Metric.thickness_nonneg s 0) h0
  have hu1 : (0:ℝ) ≤ u1 := le_trans (Metric.thickness_nonneg s 1) h1
  have hu2 : (0:ℝ) ≤ u2 := le_trans (Metric.thickness_nonneg s 2) h2
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul hu0]
  gcongr
  rw [show ((8:ℝ)) = ((8:ℕ):ℝ) by norm_num, ENNReal.ofReal_natCast]; norm_num

/-- **The rank-`2` lower bound of clause (A2)** — the second inequality
`Kakeya.VeryNotSticky.hasThicknesses_slabRescale_image_of_two` leaves open, and the one that
`Kakeya.VeryNotSticky.aniLin_rank_two_gap` shows the transport cannot supply unconditionally.

The route is a volume comparison rather than a direct thickness transport, which is what makes
it work: the image `Y` has a volume floor (the body's own floor, transported by the ratio
identity), and `volume Y ≤ 2³ τ₀(Y) τ₁(Y) τ₂(Y)` with `τ₀(Y) ≤ 1` and `τ₁(Y) ≤ T₁` then bounds
`τ₂(Y)` from below by `ρ₂²/(2304 C₀³ T₁)`. With the aligned `T₁ ∼ C₀ ρ₂` of
`Kakeya.VeryNotSticky.thickness_one_aniRescale_image_le_of_aligned` that is `∼ ρ₂`, which is
(A2); with the unaligned `T₁ ∼ δ^{-τ'} C₀ ρ₂` it is `δ^{τ'} ρ₂`, which is not. -/
theorem thickness_two_slabRescale_image_ge (c n : E₃) (hn : ‖n‖ = 1)
    {r₁ ratio a b T₁ : ℝ} {C₀ : ℝ≥0}
    (hr₁ : 0 < r₁) (hratio : 0 < ratio) (hratio1 : ratio ≤ 1) (ha : 0 < a) (hb : 0 < b)
    (hrb : ratio * b = a) (hC₀ : 1 ≤ C₀) (W : ConvexSpaceBody E₃)
    (hX : Kakeya.HasThicknesses W.carrier C₀ ![r₁, b, a])
    (hsub : W.carrier ⊆ (generalSlab c n hn hr₁ hratio).carrier)
    (hT₁ : Metric.thickness ℝ (slabRescale c n hn hr₁ hratio '' W.carrier) 1 ≤ T₁)
    (hT₁0 : 0 < T₁) :
    (b / r₁) ^ 2 / (2304 * (C₀ : ℝ) ^ 3 * T₁)
      ≤ Metric.thickness ℝ (slabRescale c n hn hr₁ hratio '' W.carrier) 2 := by
  have hC₀' : (1 : ℝ) ≤ (C₀ : ℝ) := by exact_mod_cast hC₀
  have hC₀0 : (0 : ℝ) < (C₀ : ℝ) := lt_of_lt_of_le one_pos hC₀'
  set Y := slabRescale c n hn hr₁ hratio '' W.carrier with hY_def
  set t2 : ℝ := Metric.thickness ℝ Y 2 with ht2_def
  have ht20 : (0:ℝ) ≤ t2 := Metric.thickness_nonneg Y 2
  -- `Y ⊆ B₁`
  have hYball : Y ⊆ Metric.closedBall (0 : E₃) 1 :=
    slabRescale_image_subset_closedBall c n hn hr₁ hratio hsub
  have hYbdd : Bornology.IsBounded Y :=
    Metric.isBounded_closedBall.subset hYball
  have hY0 : Metric.thickness ℝ Y 0 ≤ 1 :=
    Metric.thickness_le_of_subset_closedBall hYball zero_le_one 0
  have hvolY : volume Y ≤ ENNReal.ofReal (8 * (1 * T₁ * t2)) :=
    volume_le_of_thickness_bounds hYbdd hY0 hT₁ le_rfl
  -- the slab's own volume
  have hgSprof := hasThicknesses_generalSlab c n hn hr₁ hratio hratio1 (le_refl (1 : ℝ≥0))
  have hgS0 : Metric.thickness ℝ (generalSlab c n hn hr₁ hratio).carrier 0 ≤ r₁ := by
    simpa using (hgSprof 0).2
  have hgS1 : Metric.thickness ℝ (generalSlab c n hn hr₁ hratio).carrier 1 ≤ r₁ := by
    simpa using (hgSprof 1).2
  have hgS2 : Metric.thickness ℝ (generalSlab c n hn hr₁ hratio).carrier 2 ≤ ratio * r₁ := by
    simpa using (hgSprof 2).2
  have hvolgS : volume (generalSlab c n hn hr₁ hratio).carrier
      ≤ ENNReal.ofReal (8 * (r₁ * r₁ * (ratio * r₁))) :=
    volume_le_of_thickness_bounds
      (generalSlab c n hn hr₁ hratio).isCompact'.isBounded hgS0 hgS1 hgS2
  -- the body's volume floor
  have hvolW : ENNReal.ofReal ((r₁ * b * a) / (6 * (C₀ : ℝ) ^ 3)) ≤ volume W.carrier := by
    have h := volumeReal_ge_of_threeProfile W.convex W.isCompact'.isBounded hC₀
      hr₁.le hb.le ha.le hX
    rw [MeasureTheory.Measure.real] at h
    exact (ENNReal.ofReal_le_iff_le_toReal W.isCompact'.measure_ne_top).mpr h
  -- combine
  have hkey := volume_slabRescale_image_mul_volume_generalSlab c n hn hr₁ hratio W.carrier
  have hlow : ENNReal.ofReal ((1:ℝ)/6) * ENNReal.ofReal ((r₁ * b * a) / (6 * (C₀ : ℝ) ^ 3))
      ≤ ENNReal.ofReal (8 * (1 * T₁ * t2)) * ENNReal.ofReal (8 * (r₁ * r₁ * (ratio * r₁))) := by
    calc ENNReal.ofReal ((1:ℝ)/6) * ENNReal.ofReal ((r₁ * b * a) / (6 * (C₀ : ℝ) ^ 3))
        ≤ volume (Metric.closedBall (0 : E₃) 1) * volume W.carrier := by
          gcongr
          · exact ofReal_six_inv_le_volume_unitBall
      _ = volume Y * volume (generalSlab c n hn hr₁ hratio).carrier := hkey.symm
      _ ≤ _ := by gcongr
  rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)] at hlow
  have hlow' : ((1:ℝ)/6) * ((r₁ * b * a) / (6 * (C₀ : ℝ) ^ 3))
      ≤ (8 * (1 * T₁ * t2)) * (8 * (r₁ * r₁ * (ratio * r₁))) := by
    have hpos : (0:ℝ) ≤ (8 * (1 * T₁ * t2)) * (8 * (r₁ * r₁ * (ratio * r₁))) := by positivity
    exact (ENNReal.ofReal_le_ofReal_iff hpos).mp hlow
  have hratio_eq : ratio = a / b := by field_simp [hb.ne'] at hrb ⊢; linarith [hrb]
  rw [hratio_eq] at hlow'
  rw [div_le_iff₀ (by positivity)]
  have hb' : b ≠ 0 := hb.ne'
  have hr' : r₁ ≠ 0 := hr₁.ne'
  have ha' : a ≠ 0 := ha.ne'
  field_simp at hlow' ⊢
  nlinarith [hlow', sq_nonneg (b*r₁), mul_pos hr₁ hb, mul_pos ha hb, hC₀0, hT₁0, ht20]

/-! ### Clause (A2) in full, at a `δ`-free constant -/

/-! `Kakeya.VeryNotSticky.alignedRescaleConstant` — a polynomial in the body's own comparison
constant `C₀` and in the alignment factor `κ` of the slab-membership clause, and — this is the
point — **free of `δ`** — is now declared in
`Kakeya.DimensionThree.MainLemma2.TangentialCase`, because clauses (A2)/(A2′) of
`Kakeya.VeryNotSticky.IsAnisotropicSlabRescale` are stated at it (re-cuts R3/R4). It is the
constant at which `Kakeya.VeryNotSticky.hasThicknesses_slabRescale_image_of_aligned` delivers
clause (A2). Being `δ`-free it is discharged by the four `∀ᶠ δ` thresholds of
`Kakeya.VeryNotSticky.eventually_ktRho2ScaleDataAt_nonslab` and costs no exponent; contrast
`Kakeya.VeryNotSticky.enclosure_tau'_charge_refuted`. -/

set_option maxHeartbeats 1000000 in
-- The six inequalities of (A2) are assembled here from four sources at once (the two
-- unconditional transport brackets, the aligned rank-`1` bound and the volume comparison),
-- and the `field_simp`/`nlinarith` normalisation of the constant `2304 (3 + κ) C₀⁴` against
-- three different profiles exceeds the default budget; the proof is linear, not a search.
/-- **Clause (A2) of `Kakeya.VeryNotSticky.IsAnisotropicSlabRescale`, produced at a `δ`-free
constant from the alignment `∠(n(W), n(S)) ≤ κ · (a/b)`.**

All six inequalities: the four that
`Kakeya.VeryNotSticky.hasThicknesses_slabRescale_image_of_two` already had unconditionally,
weakened to the larger constant, plus the rank-`1` upper bound
(`Kakeya.VeryNotSticky.thickness_one_aniRescale_image_le_of_aligned`, which needs the
alignment) and the rank-`2` lower bound
(`Kakeya.VeryNotSticky.thickness_two_slabRescale_image_ge`, which needs the rank-`1` one).

**This is GWZ's transport, with GWZ's own accounting**: within one slab the change of variables
is free, and the `δ^{-O(τ')}` of (105) is charged where GWZ charge it, to the number of slabs a
fibre meets — the `δ^{-2τ'}` already written into
`Kakeya.VeryNotSticky.tangentialSlabDecomp` and paid from
`Kakeya.VeryNotSticky.CaseParams.tangential`'s `2²⁰(ϱ + τ')`. -/
theorem hasThicknesses_slabRescale_image_of_aligned (c n : E₃) (hn : ‖n‖ = 1)
    {r₁ ratio a b : ℝ} {C₀ κ : ℝ≥0}
    (hr₁ : 0 < r₁) (hratio : 0 < ratio) (hratio1 : ratio ≤ 1) (ha : 0 < a) (hb : 0 < b)
    (hab : a ≤ b) (hrb : ratio * b = a) (hC₀ : 1 ≤ C₀) (hκ : 1 ≤ κ) (W : ConvexSpaceBody E₃)
    (hX : Kakeya.HasThicknesses W.carrier C₀ ![r₁, b, a])
    (hsub : W.carrier ⊆ (generalSlab c n hn hr₁ hratio).carrier)
    (halign : NonSlab.lineAngle (bodyNormal W) n ≤ (κ : ℝ) * ratio) :
    Kakeya.HasThicknesses (slabRescale c n hn hr₁ hratio '' W.carrier)
      (alignedRescaleConstant C₀ κ) ![1, b / r₁, b / r₁] := by
  have hC₀' : (1 : ℝ) ≤ (C₀ : ℝ) := by exact_mod_cast hC₀
  have hC₀0 : (0 : ℝ) < (C₀ : ℝ) := lt_of_lt_of_le one_pos hC₀'
  have hκ' : (1 : ℝ) ≤ (κ : ℝ) := by exact_mod_cast hκ
  set M : ℝ := 2304 * (3 + (κ : ℝ)) * (C₀ : ℝ) ^ 4 with hM_def
  have hCc : ((alignedRescaleConstant C₀ κ : ℝ≥0) : ℝ) = M := by
    simp [alignedRescaleConstant, hM_def]
  have hMpos : (0 : ℝ) < M := by rw [hM_def]; positivity
  have hcube : (1 : ℝ) ≤ (C₀ : ℝ) ^ 3 := one_le_pow₀ hC₀'
  have hC4 : (C₀ : ℝ) ≤ (C₀ : ℝ) ^ 4 := by nlinarith
  have hκ0 : (0 : ℝ) ≤ (κ : ℝ) := κ.coe_nonneg
  have hpow4 : (1 : ℝ) ≤ (C₀ : ℝ) ^ 4 := one_le_pow₀ hC₀'
  have hkey : ∀ x : ℝ, 0 ≤ x → x * (C₀ : ℝ) ≤ 2304 * x * (C₀ : ℝ) ^ 4 := by
    intro x hx
    calc x * (C₀ : ℝ) ≤ x * (2304 * (C₀ : ℝ) ^ 4) := by
          refine mul_le_mul_of_nonneg_left ?_ hx
          nlinarith
      _ = 2304 * x * (C₀ : ℝ) ^ 4 := by ring
  have hCle : (C₀ : ℝ) ≤ M := by
    rw [hM_def]
    have := hkey (3 + (κ : ℝ)) (by linarith)
    nlinarith
  have hCinv : M⁻¹ ≤ ((C₀ : ℝ))⁻¹ := inv_anti₀ hC₀0 hCle
  set Y := slabRescale c n hn hr₁ hratio '' W.carrier with hY_def
  have hpos : (0 : ℝ) < ratio * r₁ := mul_pos hratio hr₁
  have hαpos : (0 : ℝ) < r₁⁻¹ := inv_pos.mpr hr₁
  have hαβ : r₁⁻¹ ≤ (ratio * r₁)⁻¹ := (inv_le_inv₀ hr₁ hpos).2 (by nlinarith)
  have hbr : (ratio * r₁)⁻¹ * a = b / r₁ := by rw [← hrb]; field_simp
  have hXbdd : Bornology.IsBounded W.carrier := W.isCompact'.isBounded
  have hX0 := (hX 0).1
  have hX1 := (hX 1).1
  have hX2 := (hX 2).2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at hX0 hX1 hX2
  have hρ0 : (0:ℝ) ≤ b / r₁ := by positivity
  have hYball : Y ⊆ Metric.closedBall (0 : E₃) 1 :=
    slabRescale_image_subset_closedBall c n hn hr₁ hratio hsub
  have h0u : Metric.thickness ℝ Y 0 ≤ 1 :=
    Metric.thickness_le_of_subset_closedBall hYball zero_le_one 0
  have h0l : M⁻¹ * 1 ≤ Metric.thickness ℝ Y 0 := by
    have hlow := (thickness_aniRescale_image_mem c n hn hαpos hαβ hXbdd 0).1
    calc M⁻¹ * 1 ≤ r₁⁻¹ * (((C₀ : ℝ))⁻¹ * r₁) := by
          rw [mul_one]
          have he : r₁⁻¹ * (((C₀ : ℝ))⁻¹ * r₁) = ((C₀ : ℝ))⁻¹ := by field_simp
          rw [he]
          exact hCinv
      _ ≤ r₁⁻¹ * Metric.thickness ℝ W.carrier 0 := mul_le_mul_of_nonneg_left hX0 hαpos.le
      _ ≤ _ := hlow
  have h1l : M⁻¹ * (b / r₁) ≤ Metric.thickness ℝ Y 1 := by
    have hlow := (thickness_aniRescale_image_mem c n hn hαpos hαβ hXbdd 1).1
    calc M⁻¹ * (b / r₁) ≤ r₁⁻¹ * (((C₀ : ℝ))⁻¹ * b) := by
          have he : r₁⁻¹ * (((C₀ : ℝ))⁻¹ * b) = ((C₀ : ℝ))⁻¹ * (b / r₁) := by
            field_simp
          rw [he]
          exact mul_le_mul_of_nonneg_right hCinv hρ0
      _ ≤ r₁⁻¹ * Metric.thickness ℝ W.carrier 1 := mul_le_mul_of_nonneg_left hX1 hαpos.le
      _ ≤ _ := hlow
  have h2u : Metric.thickness ℝ Y 2 ≤ M * (b / r₁) := by
    have hup := (thickness_aniRescale_image_mem c n hn hαpos hαβ hXbdd 2).2
    calc Metric.thickness ℝ Y 2 ≤ (ratio * r₁)⁻¹ * Metric.thickness ℝ W.carrier 2 := hup
      _ ≤ (ratio * r₁)⁻¹ * ((C₀ : ℝ) * a) := mul_le_mul_of_nonneg_left hX2 (inv_pos.mpr hpos).le
      _ = (C₀ : ℝ) * ((ratio * r₁)⁻¹ * a) := by ring
      _ = (C₀ : ℝ) * (b / r₁) := by rw [hbr]
      _ ≤ M * (b / r₁) := mul_le_mul_of_nonneg_right hCle hρ0
  -- the aligned rank-`1` upper bound
  have halign' : |⟪n, outerPrism.basis (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3))
      W.isCompact' W.nonempty' 1⟫| ≤ (κ : ℝ) * ratio :=
    abs_inner_middle_le_of_lineAngle_le W n hn halign
  have hXt1 : Metric.thickness ℝ W.carrier 1 ≤ (C₀ : ℝ) * b := by simpa using (hX 1).2
  have hXt2 : Metric.thickness ℝ W.carrier 2 ≤ (C₀ : ℝ) * a := hX2
  have hβpos : (0:ℝ) < (ratio * r₁)⁻¹ := inv_pos.mpr hpos
  have hsnn : (0:ℝ) ≤ (κ : ℝ) * ratio := by positivity
  have h1u' : Metric.thickness ℝ Y 1
      ≤ ((C₀ : ℝ) * b) * (r₁⁻¹ + (ratio * r₁)⁻¹ * ((κ : ℝ) * ratio))
        + ((C₀ : ℝ) * a) * (r₁⁻¹ + (ratio * r₁)⁻¹) :=
    thickness_one_aniRescale_image_le_of_aligned c n hn hαpos hβpos
      W.isCompact' W.nonempty' hXt1 hXt2 hsnn halign'
  have h1u : Metric.thickness ℝ Y 1 ≤ (3 + (κ : ℝ)) * (C₀ : ℝ) * (b / r₁) := by
    refine h1u'.trans ?_
    have e1 : (ratio * r₁)⁻¹ * ((κ : ℝ) * ratio) = (κ : ℝ) * r₁⁻¹ := by field_simp
    have e2 : ((C₀ : ℝ) * a) * (ratio * r₁)⁻¹ = (C₀ : ℝ) * (b / r₁) := by
      rw [mul_assoc, mul_comm a ((ratio * r₁)⁻¹), hbr]
    have hexp : ((C₀ : ℝ) * b) * (r₁⁻¹ + (κ : ℝ) * r₁⁻¹)
          + ((C₀ : ℝ) * a) * (r₁⁻¹ + (ratio * r₁)⁻¹)
        = (2 + (κ : ℝ)) * (C₀ : ℝ) * (b / r₁) + (C₀ : ℝ) * (a / r₁) := by
      have hsplit : ((C₀ : ℝ) * a) * (r₁⁻¹ + (ratio * r₁)⁻¹)
          = ((C₀ : ℝ) * a) * r₁⁻¹ + ((C₀ : ℝ) * a) * (ratio * r₁)⁻¹ := by ring
      rw [hsplit, e2]
      field_simp
      ring
    rw [e1, hexp]
    have hmono : (C₀ : ℝ) * (a / r₁) ≤ (C₀ : ℝ) * (b / r₁) := by gcongr
    nlinarith
  have hT₁0 : (0:ℝ) < (3 + (κ : ℝ)) * (C₀ : ℝ) * (b / r₁) := by positivity
  have h2l' := thickness_two_slabRescale_image_ge c n hn hr₁ hratio hratio1 ha hb hrb hC₀ W
    hX hsub h1u hT₁0
  have h2l : M⁻¹ * (b / r₁) ≤ Metric.thickness ℝ Y 2 := by
    refine le_trans (le_of_eq ?_) h2l'
    rw [hM_def]
    field_simp
  have h1uC : Metric.thickness ℝ Y 1 ≤ M * (b / r₁) := by
    refine h1u.trans (mul_le_mul_of_nonneg_right ?_ hρ0)
    rw [hM_def]
    exact hkey (3 + (κ : ℝ)) (by linarith)
  have h0uC : Metric.thickness ℝ Y 0 ≤ M * 1 := by
    rw [mul_one]
    refine h0u.trans ?_
    rw [hM_def]
    nlinarith
  intro k
  rw [hCc]
  fin_cases k
  · exact ⟨h0l, h0uC⟩
  · exact ⟨h1l, h1uC⟩
  · exact ⟨h2l, h2u⟩

/-! ### Where the `δ^{-τ'}` may and may not be charged -/


/-! ### The tightened alignment clause against the existing one -/


/-! ### The packaged (A2), in the binder shape of `exists_slabPackage_general` -/

/-- The aspect ratio `a/b` of the configuration, as a positive real. -/
theorem cfg_ratio_pos (cfg : VeryNotSticky.{u}) :
    (0 : ℝ) < ((cfg.a / cfg.b : ℝ≥0) : ℝ) := by
  have hb0 : (0 : ℝ≥0) < cfg.b := lt_of_lt_of_le cfg.hδ (cfg.hdims.1.trans cfg.hdims.2.1)
  have ha0 : (0 : ℝ≥0) < cfg.a := lt_of_lt_of_le cfg.hδ cfg.hdims.1
  have : (0 : ℝ≥0) < cfg.a / cfg.b := div_pos ha0 hb0
  exact_mod_cast this

/-- The aspect ratio is at most one, since `a ≤ b`. -/
theorem cfg_ratio_le_one (cfg : VeryNotSticky.{u}) :
    ((cfg.a / cfg.b : ℝ≥0) : ℝ) ≤ 1 := by
  have hb0 : (0 : ℝ≥0) < cfg.b := lt_of_lt_of_le cfg.hδ (cfg.hdims.1.trans cfg.hdims.2.1)
  have : cfg.a / cfg.b ≤ 1 := div_le_one_of_le₀ cfg.hdims.2.1 (le_of_lt hb0)
  exact_mod_cast this

/-- `(a/b) · b = a`. -/
theorem cfg_ratio_mul_b (cfg : VeryNotSticky.{u}) :
    ((cfg.a / cfg.b : ℝ≥0) : ℝ) * (cfg.b : ℝ) = (cfg.a : ℝ) := by
  have hb0 : (0 : ℝ≥0) < cfg.b := lt_of_lt_of_le cfg.hδ (cfg.hdims.1.trans cfg.hdims.2.1)
  have hb' : (cfg.b : ℝ) ≠ 0 := by exact_mod_cast hb0.ne'
  push_cast
  field_simp

/-- `ρ₂ = b / r₁` in the reals. -/
theorem cfg_rho2_coe (cfg : VeryNotSticky.{u}) :
    ((cfg.rho2 : ℝ≥0) : ℝ) = (cfg.b : ℝ) / (cfg.r₁ : ℝ) := by
  rw [VeryNotSticky.rho2, NNReal.coe_div]


/-! ### Does the existing containment already force the alignment?  No, and by exactly `1/ρ₂` -/


/-! ### R3–R6: the whole Katz–Tao chain at a general `δ`-free constant

`Kakeya.VeryNotSticky.KTRho2ScaleData` hard-codes the comparison constant `2 * bd.C₀`, so
"a larger `δ`-free constant is absorbed at zero exponent cost" cannot be checked by
instantiating the existing producer — the constant is not a parameter of it. It is checked here
by **re-running the chain**: the enclosure, the estimate and its `∀ᶠ δ` form are re-proved at
an arbitrary `δ`-free `Cmp ≥ 1`, and the exponents `(4ϱ, 9η, 3ϱ)` come out **identical**.

`Kakeya.VeryNotSticky.ktRho2ScaleDataAt_at_C₀` is the tripwire: at `Cmp = bd.C₀` the
generalised predicate is the existing one, definitionally.

The three proofs below are the existing ones with `bd.C₀` replaced by `Cmp` and `bd.hC₀` by
`hCmp` throughout; `bd` is otherwise used only for its index type `bd.ω`, which is why the
generalisation is mechanical. **That is the measurement**: nothing about `bd.C₀` beyond
`1 ≤ bd.C₀` is used anywhere in the chain, so every occurrence of the comparison constant is a
`δ`-free threshold and none of them is an exponent.

`Kakeya.VeryNotSticky.KTRho2ScaleDataAt` itself is declared in
`Kakeya.DimensionThree.MainLemma2.TangentialCase`, since
`Kakeya.VeryNotSticky.SlabMultKT.estimate` reads it, and the chain that produces it at a
general `Cmp` — `ktRho2ScaleDataAt_at_C₀`, `exists_enclosing_shadedTubes_of_ktRho2_at`,
`ktRho2ScaleData_of_ckt_nonslab_at`, `eventually_ktRho2ScaleDataAt_nonslab`,
`eventually_ktRho2ScaleDataAt_aligned` — now lives in
`Kakeya.DimensionThree.MainLemma2.SlabMultKTProduce`/`SlabMultKTGeneral`, upstream of the
degenerate boundary that has to read it (conjunct 4 of
`Kakeya.VeryNotSticky.SideDataObligations`). The declarations are unchanged, byte for byte.
-/


/-! ### R6: the `δ`-free constant in `slabCard`'s absorption, at a general `Cmp` -/


/-! ### The angular sub-classing, and why its count is free -/


/-! ### Building `hfam`: the positional obstruction, located exactly -/

/-- The normalising ellipsoid reaches distance `r₁` from its own centre, in **every** direction
orthogonal to its normal: `c ± r₁ u ∈ generalSlab c n` for any unit `u ⊥ n`. This is the sense
in which clause (S2)'s profile `(r₁, r₁, (a/b) r₁)` is *exact* for it
(`Kakeya.VeryNotSticky.hasThicknesses_generalSlab`). -/
theorem mem_generalSlab_of_orthogonal (c n : E₃) (hn : ‖n‖ = 1) {r₁ ratio : ℝ} (hr₁ : 0 < r₁)
    (hratio : 0 < ratio) {u : E₃} (hu : ‖u‖ = 1) (hun : ⟪n, u⟫ = (0 : ℝ)) {t : ℝ}
    (ht : |t| ≤ r₁) : c + t • u ∈ (generalSlab c n hn hr₁ hratio).carrier := by
  rw [mem_generalSlab_iff]
  have hsub : c + t • u - c = t • u := by abel
  rw [hsub]
  have hinner : (⟪n, t • u⟫ : ℝ) = 0 := by rw [real_inner_smul_right, hun, mul_zero]
  have hnorm : ‖aniLin n r₁⁻¹ (ratio * r₁)⁻¹ (t • u)‖ ^ 2 = (r₁⁻¹) ^ 2 * ‖t • u‖ ^ 2 := by
    rw [norm_sq_aniLin n hn, hinner]
    ring
  have htu : ‖t • u‖ = |t| := by rw [norm_smul, hu, mul_one, Real.norm_eq_abs]
  have hle : ‖aniLin n r₁⁻¹ (ratio * r₁)⁻¹ (t • u)‖ ^ 2 ≤ 1 ^ 2 := by
    rw [hnorm, htu, one_pow]
    have h1 : |t| ^ 2 ≤ r₁ ^ 2 := by nlinarith [abs_nonneg t]
    have h2 : (r₁⁻¹) ^ 2 * r₁ ^ 2 = 1 := by field_simp
    nlinarith [sq_nonneg (r₁⁻¹), inv_pos.mpr hr₁]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) zero_le_one two_ne_zero).mp hle


/-! ### Determinacy of `bodyNormal` on the normalising ellipsoid -/

/-- **`bodyNormal` is determined, to within the aspect ratio, on the normalising ellipsoid.**

`Kakeya.NonSlab.bodyNormal` is `outerPrism.basis … 2`, a `Classical.choose`, and the tree has
no determinacy lemma for it — which is what  recorded as the reason a
counterexample body could not be compiled, and what blocks *any* construction of a slab family
from proving clause (S4′) or the alignment clause R1, both of which are stated through
`Kakeya.VeryNotSticky.axisAngle`.

For the ellipsoid of semi-axes `(R, R, ratio · R)` the frame **is** determined up to `ratio`:
the outer prism's rank-`2` half-width is exactly `ratio · R`
(`Kakeya.VeryNotSticky.hasThicknesses_generalSlab` at comparison constant `1`), while the
ellipsoid reaches `± R` in every direction orthogonal to `n`
(`Kakeya.VeryNotSticky.mem_generalSlab_of_orthogonal`), so the component of `bodyNormal` along
any unit `u ⊥ n` is at most `ratio`. Taking `u` in the direction of `bodyNormal`'s own
orthogonal part gives `‖(n(S))_{⊥n}‖ ≤ ratio` — i.e. `sin ∠(n(S), n) ≤ ratio`. -/
theorem norm_bodyNormal_orthogonal_le (c n : E₃) (hn : ‖n‖ = 1) {R ratio : ℝ} (hR : 0 < R)
    (hratio : 0 < ratio) (hratio1 : ratio ≤ 1) :
    ‖bodyNormal (generalSlab c n hn hR hratio)
        - (⟪n, bodyNormal (generalSlab c n hn hR hratio)⟫ : ℝ) • n‖ ≤ ratio := by
  set S := generalSlab c n hn hR hratio with hS
  set e : E₃ := bodyNormal S with he
  set w : E₃ := e - (⟪n, e⟫ : ℝ) • n with hw
  rcases eq_or_ne w 0 with h0 | h0
  · rw [h0, norm_zero]; exact hratio.le
  -- the unit vector in the direction of `w`, orthogonal to `n`
  set u : E₃ := ‖w‖⁻¹ • w with hu
  have hwpos : (0:ℝ) < ‖w‖ := norm_pos_iff.mpr h0
  have hunorm : ‖u‖ = 1 := by
    rw [hu, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hwpos), inv_mul_cancel₀ hwpos.ne']
  have hnn : (⟪n, n⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  have hwn : (⟪n, w⟫ : ℝ) = 0 := by
    rw [hw, inner_sub_right, real_inner_smul_right, hnn, mul_one, sub_self]
  have hun : (⟪n, u⟫ : ℝ) = 0 := by rw [hu, real_inner_smul_right, hwn, mul_zero]
  -- the two extreme points of the ellipsoid along `u`
  have hp : c + R • u ∈ S.carrier :=
    mem_generalSlab_of_orthogonal c n hn hR hratio hunorm hun (by rw [abs_of_pos hR])
  have hm : c + (-R) • u ∈ S.carrier :=
    mem_generalSlab_of_orthogonal c n hn hR hratio hunorm hun
      (by rw [abs_of_neg (neg_neg_iff_pos.mpr hR)]; linarith)
  -- the rank-`2` half-width of the outer prism is exactly `ratio · R`
  have hprof := hasThicknesses_generalSlab c n hn hR hratio hratio1 (le_refl (1 : ℝ≥0))
  have hτ2 : Metric.thickness ℝ S.carrier 2 ≤ ratio * R := by
    have := (hprof 2).2
    simpa using this
  set hfr : Module.finrank ℝ E₃ = 3 := finrank_euclideanSpace_fin with hfr_def
  have he2 : e = outerPrism.basis hfr S.isCompact' S.nonempty' 2 := by
    rw [he, bodyNormal, NonSlab.bodyNormal_eq]
  have hbp := outerPrism.basis_repr_le hfr S.isCompact' S.nonempty' hp 2
  have hbm := outerPrism.basis_repr_le hfr S.isCompact' S.nonempty' hm 2
  simp only [OrthonormalBasis.repr_apply_apply, ← he2] at hbp hbm
  -- subtract: `|⟪e, 2R u⟫| ≤ 2 ratio R`
  have hdiff : |(⟪e, (2 * R) • u⟫ : ℝ)| ≤ 2 * (ratio * R) := by
    have hex : ((2 * R) • u : E₃)
        = (c + R • u - outerPrism.center hfr S.isCompact' S.nonempty')
          - (c + (-R) • u - outerPrism.center hfr S.isCompact' S.nonempty') := by
      rw [neg_smul]
      match_scalars <;> ring
    rw [hex, inner_sub_right]
    calc |(⟪e, c + R • u - outerPrism.center hfr S.isCompact' S.nonempty'⟫ : ℝ)
            - ⟪e, c + (-R) • u - outerPrism.center hfr S.isCompact' S.nonempty'⟫|
        ≤ |(⟪e, c + R • u - outerPrism.center hfr S.isCompact' S.nonempty'⟫ : ℝ)|
          + |(⟪e, c + (-R) • u - outerPrism.center hfr S.isCompact' S.nonempty'⟫ : ℝ)| :=
          abs_sub _ _
      _ ≤ Metric.thickness ℝ S.carrier 2 + Metric.thickness ℝ S.carrier 2 := add_le_add hbp hbm
      _ ≤ 2 * (ratio * R) := by linarith
  -- `⟪e, u⟫ = ‖w‖`
  have heu : (⟪e, u⟫ : ℝ) = ‖w‖ := by
    have hee : (⟪e, e⟫ : ℝ) = 1 := by
      rw [real_inner_self_eq_norm_sq, he, norm_bodyNormal]; norm_num
    have hen : (⟪e, n⟫ : ℝ) = ⟪n, e⟫ := (real_inner_comm e n).symm
    have hkey : (⟪e, w⟫ : ℝ) = 1 - (⟪n, e⟫ : ℝ) ^ 2 := by
      rw [hw]
      simp only [inner_sub_right, real_inner_smul_right, hee, hen]
      ring
    have hnorm2 : ‖w‖ ^ 2 = 1 - (⟪n, e⟫ : ℝ) ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, hw]
      simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
        hee, hnn, hen]
      ring
    have hew : (⟪e, w⟫ : ℝ) = ‖w‖ ^ 2 := by rw [hkey, hnorm2]
    rw [hu, real_inner_smul_right, hew]
    field_simp
  rw [real_inner_smul_right, heu, abs_mul, abs_of_pos (by linarith : (0:ℝ) < 2 * R),
    abs_of_pos hwpos] at hdiff
  nlinarith

/-- The orthogonal part of one unit vector against another has norm `sin` of the line angle. -/
theorem norm_orthogonal_eq_sin_lineAngle {u v : E₃} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖u - (⟪v, u⟫ : ℝ) • v‖ = Real.sin (NonSlab.lineAngle u v) := by
  have hvv : (⟪v, v⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have huu : (⟪u, u⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have huv : (⟪u, v⟫ : ℝ) = ⟪v, u⟫ := (real_inner_comm u v).symm
  have hsq : ‖u - (⟪v, u⟫ : ℝ) • v‖ ^ 2 = 1 - (⟪u, v⟫ : ℝ) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      huu, hvv, huv]
    ring
  have hle : (⟪u, v⟫ : ℝ) ^ 2 ≤ 1 := by
    have := abs_real_inner_le_norm u v
    rw [hu, hv, mul_one] at this
    nlinarith [abs_nonneg (⟪u, v⟫ : ℝ), sq_abs (⟪u, v⟫ : ℝ)]
  rw [NonSlab.lineAngle_eq_arccos_abs_inner hu hv, Real.sin_arccos, sq_abs]
  rw [← hsq, Real.sqrt_sq (norm_nonneg _)]

/-- **Determinacy in the form the angle clauses read it**: the slab's `bodyNormal` is within
`2 · ratio` of the slab's defining normal `n`, in `Kakeya.NonSlab.lineAngle`. With
`ratio = a/b` this is exactly the resolution at which clause R1 (`S3_ratio`) and clause (S4′)
are stated, so a family of normalising ellipsoids can prove **both by construction**.

Jordan's inequality `2/π · θ ≤ sin θ` on `[0, π/2]` turns
`Kakeya.VeryNotSticky.norm_bodyNormal_orthogonal_le`'s `sin ∠ ≤ ratio` into `∠ ≤ (π/2) ratio`,
and `π/2 ≤ 2`. -/
theorem lineAngle_bodyNormal_generalSlab_le (c n : E₃) (hn : ‖n‖ = 1) {R ratio : ℝ}
    (hR : 0 < R) (hratio : 0 < ratio) (hratio1 : ratio ≤ 1) :
    NonSlab.lineAngle (bodyNormal (generalSlab c n hn hR hratio)) n ≤ 2 * ratio := by
  set e : E₃ := bodyNormal (generalSlab c n hn hR hratio) with he
  have hene : ‖e‖ = 1 := norm_bodyNormal _
  have hsin : Real.sin (NonSlab.lineAngle e n) ≤ ratio := by
    rw [← norm_orthogonal_eq_sin_lineAngle hene hn]
    exact norm_bodyNormal_orthogonal_le c n hn hR hratio hratio1
  have h0 : 0 ≤ NonSlab.lineAngle e n := NonSlab.lineAngle_nonneg _ _
  have h2 : NonSlab.lineAngle e n ≤ Real.pi / 2 := by
    rw [NonSlab.lineAngle_eq_arccos_abs_inner hene hn]
    exact Real.arccos_le_pi_div_two.mpr (abs_nonneg _)
  have hj := Real.mul_le_sin h0 h2
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hpipos : (0:ℝ) < Real.pi := Real.pi_pos
  have : 2 / Real.pi * NonSlab.lineAngle e n ≤ ratio := le_trans hj hsin
  rw [div_mul_eq_mul_div, div_le_iff₀ hpipos] at this
  nlinarith

/-! ### Two transverse slabs pinch to a line — the input clause (S1) needs -/


/-! ### The second obstruction to `hfam`: (S1) and (S3) trade off against each other -/


/-! ### The trade-off is proportional to the essential-distinctness threshold -/


end

end Kakeya.VeryNotSticky

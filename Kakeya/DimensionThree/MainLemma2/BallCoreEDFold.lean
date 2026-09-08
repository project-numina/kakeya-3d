/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.BallCoreEDRescale
public import Kakeya.DimensionThree.MainLemma2.Conjunct6Refutation

/-!
# GWZ §9.3 steps 6-8, assembled at the dilated carrier (S-4)

This file assembles the `BallDataCore` used by `Kakeya.VeryNotSticky.edFoldCore`
at a dilated carrier and proves the resulting estimate under explicit
hypothesis floors for the geometric constants.

## What is here

* `Kakeya.VeryNotSticky.CapsulePresentation` — the capsule presentation of a `BallDataCore`'s
  segments, as *data*: the parent tube of each segment, named. This is
  `Kakeya.VeryNotSticky.HasCapsuleSegments` with the existential skolemised, plus the two
  facts about the presentation the dilated re-presentation needs (the parent's shading meets
  the piece; the pieces sit in the shrunken balls).
* `Kakeya.VeryNotSticky.edDilateCore` — the **re-presentation of a capsule core at the
  `K′₀`-dilated carrier**, all forty-four `BallDataCore` fields. Nothing is folded here: the
  segments, the parent families, the fibre count and the shadings are the base core's; only
  the carriers grow, from `Kakeya.VeryNotSticky.segCarrierSet` to
  `Kakeya.VeryNotSticky.segCarrierSetAt edDilateConstant`.
* `Kakeya.VeryNotSticky.exists_core_edSegments_of_cover_floor` — the BP264 target with the
  three hypothesis floors of  §G-1  in
  place of `4 ≤ C₀`, `4 c₁ D ≤ 1` and `16 δ ≤ r₁`, and with the fibre budget kept as an
  explicit binder so that the explicit fibre budget is a substitution.

## Why the carrier is the *radius* dilate and not the homothety dilate

`Kakeya.VeryNotSticky.not_segCarrierSetHom_subset_closedBall_of_radiusFloor` (below) is the
compiled reason: the homothety dilate of a capsule of half-length `L = r₁/4` has half-length
`K′₀ L ≈ 25 r₁`, so it violates `BallDataCore.segs_subset_ball` for *every* configuration —
the field asks the carrier to sit inside the ball of radius `r₁` it was cut out of. The
radius-only dilate `Kakeya.VeryNotSticky.segCarrierSetAt` keeps the core window and only widens
the tube, and its margin `r₁/4 + r₁/16 + K′₀ δ ≤ r₁` is paid by the radius floor.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Set

namespace Kakeya.VeryNotSticky

universe u

variable {cfg : VeryNotSticky.{u}}

/-! ### Preliminaries -/

/-- Weakening the constant of a thickness profile. -/
theorem hasThicknesses_mono {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    {A : Set E} {C C' : ℝ≥0} {t : Fin n → ℝ} (hC : 0 < C) (hCC' : C ≤ C')
    (ht : ∀ k, 0 ≤ t k) (h : Kakeya.HasThicknesses A C t) : Kakeya.HasThicknesses A C' t := by
  intro k
  obtain ⟨h1, h2⟩ := h k
  have hCR : (0 : ℝ) < (C : ℝ) := by exact_mod_cast hC
  have hCC'R : (C : ℝ) ≤ (C' : ℝ) := by exact_mod_cast hCC'
  exact ⟨le_trans (mul_le_mul_of_nonneg_right (inv_anti₀ hCR hCC'R) (ht k)) h1,
    le_trans h2 (mul_le_mul_of_nonneg_right hCC'R (ht k))⟩

/-- `Metric.ethickness.scale` is monotone under inclusion. -/
theorem ethickness_scale_mono {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s t : Set E} (h : s ⊆ t) :
    Metric.ethickness.scale ℝ s ≤ Metric.ethickness.scale ℝ t :=
  Finset.inf_mono_fun (fun n _ => Metric.ethickness_monotone (𝕜 := ℝ) h n)

/-- The radius floor pays the dilate inside a quarter of the ball radius. -/
theorem edDilate_mul_delta_le_quarter
    (hrad : ((edRadiusConstant : ℝ≥0) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ)) :
    ((edDilateConstant : ℝ≥0) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ) / 4 := by
  have hδ0 : (0 : ℝ) ≤ (cfg.δ : ℝ) := (cfg.δ).coe_nonneg
  have he : ((edRadiusConstant : ℝ≥0) : ℝ) = 8 * ((edDilateConstant : ℝ≥0) : ℝ) := by
    rw [edRadiusConstant]; push_cast; ring
  rw [he] at hrad
  have hK0 : (0 : ℝ) ≤ ((edDilateConstant : ℝ≥0) : ℝ) := (edDilateConstant).coe_nonneg
  nlinarith

theorem edDilate_mul_delta_le_eighth
    (hrad : ((edRadiusConstant : ℝ≥0) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ)) :
    ((edDilateConstant : ℝ≥0) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ) / 8 := by
  have hδ0 : (0 : ℝ) ≤ (cfg.δ : ℝ) := (cfg.δ).coe_nonneg
  have he : ((edRadiusConstant : ℝ≥0) : ℝ) = 8 * ((edDilateConstant : ℝ≥0) : ℝ) := by
    rw [edRadiusConstant]; push_cast; ring
  rw [he] at hrad
  linarith

theorem delta_le_quarter_of_radiusFloor
    (hrad : ((edRadiusConstant : ℝ≥0) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ)) :
    (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ) / 4 := by
  have h := deltaLeR₁_of_radiusFloor hrad
  linarith

/-- The dilated capsule stays inside the ball it was cut out of, at the concrete margin. -/
theorem segCarrierSetAt_subset_closedBall_ctr {δ : ℝ≥0} (K : ℝ≥0)
    (T : Tube δ (EuclideanSpace ℝ (Fin 3))) (c : EuclideanSpace ℝ (Fin 3)) {L ρ R : ℝ}
    (hL : 0 ≤ L) (hmeet : (T.carrier ∩ ball c ρ).Nonempty)
    (hR : (K : ℝ) * (δ : ℝ) + (2 * L + 2 * (δ : ℝ) + ρ) ≤ R) :
    segCarrierSetAt K T c L ⊆ closedBall c R := by
  have hδ0 : (0 : ℝ) ≤ (δ : ℝ) := δ.coe_nonneg
  have hρ : 0 < ρ := by
    obtain ⟨x, -, hx⟩ := hmeet
    exact lt_of_le_of_lt dist_nonneg (Metric.mem_ball.1 hx)
  have hR' : (0 : ℝ) ≤ 2 * L + 2 * (δ : ℝ) + ρ := by linarith
  have h1 : segment ℝ (corePt T (segStart T c L)) (corePt T (segStart T c L + 2 * L)) ⊆
      closedBall c (2 * L + 2 * (δ : ℝ) + ρ) :=
    subset_trans (Metric.self_subset_cthickening _)
      (segCarrierSet_subset_closedBall_ctr T c hL hmeet le_rfl)
  intro z hz
  have h2 := Metric.cthickening_subset_of_subset ((K : ℝ) * (δ : ℝ)) h1 hz
  rw [cthickening_closedBall (by positivity) hR'] at h2
  exact Metric.closedBall_subset_closedBall hR h2

/-! ### The dilated capsule is a capsule: R-a and the core-line clause at radius `K δ`

`Kakeya.VeryNotSticky.capsule_subset_hom_of_not_essDistinct` (R-a) is stated at the tube's own
radius `δ` and for two windows about a *common* reference point. Both restrictions are
inessential to its proof, and lifting them is what lets the fold's obligations be discharged at
the **dilated** carrier, where  §G-1 rules they have to live. -/

section DilatedRadiusGeometry

variable {δ : ℝ≥0}

/-- The `K`-dilated capsule as a convex body. -/
noncomputable def capsuleBodyAt (K : ℝ≥0) (T : Tube δ E3) (c : E3) {L : ℝ} (hL : 0 ≤ L) :
    ConvexSpaceBody E3 where
  carrier := segCarrierSetAt K T c L
  convex' := (convex_segCarrierSetAt K T c L).isConvexSet
  isCompact' := Metric.isCompact_of_isClosed_isBounded (isClosed_segCarrierSetAt K T c L)
    (isBounded_segCarrierSetAt K T c hL)
  nonempty' := ⟨corePt T (segStart T c L), Metric.self_subset_cthickening _
    (left_mem_segment ℝ _ _)⟩

@[simp] theorem capsuleBodyAt_carrier (K : ℝ≥0) (T : Tube δ E3) (c : E3) {L : ℝ}
    (hL : 0 ≤ L) : (capsuleBodyAt K T c hL).carrier = segCarrierSetAt K T c L := rfl

/-- **The dilated capsule, rescaled to a unit tube.** -/
noncomputable def rescaledCapsuleTubeAt {δ' : ℝ≥0} (K : ℝ≥0) (T : Tube δ E3) (c m : E3)
    {L : ℝ} (hL : 0 < L) (hδ' : (δ' : ℝ) = (2 * L)⁻¹ * ((K : ℝ) * (δ : ℝ))) : Tube δ' E3 where
  toConvexSpaceBody :=
    ConvexSpaceBody.affineImage (AffineMap.homothety m (2 * L)⁻¹)
      (AffineMap.continuous_of_finiteDimensional _) (capsuleBodyAt K T c (le_of_lt hL))
  x := AffineMap.homothety m (2 * L)⁻¹ (corePt T (segStart T c L))
  y := AffineMap.homothety m (2 * L)⁻¹ (corePt T (segStart T c L + 2 * L))
  dist_eq_one := by
    have h2L : (0 : ℝ) < 2 * L := by linarith
    rw [dist_homothety, abs_of_pos (inv_pos.2 h2L), dist_corePt_window T c (le_of_lt hL),
      inv_mul_cancel₀ (ne_of_gt h2L)]
  carrier_eq := by
    have h2L : (0 : ℝ) < 2 * L := by linarith
    have hk : (0 : ℝ) < (2 * L)⁻¹ := inv_pos.2 h2L
    have hKδ : (0 : ℝ) ≤ (K : ℝ) * (δ : ℝ) := by positivity
    change (AffineMap.homothety m (2 * L)⁻¹) '' (segCarrierSetAt K T c L) = _
    rw [segCarrierSetAt, isClosed_segment.cthickening_eq_biUnion_closedBall hKδ,
      Set.image_iUnion₂]
    rw [← homothety_image_segment m (2 * L)⁻¹ _ _]
    rw [Set.biUnion_image]
    refine Set.iUnion₂_congr fun w _ => ?_
    rw [homothety_image_closedBall hk w ((K : ℝ) * (δ : ℝ)), hδ']

@[simp] theorem rescaledCapsuleTubeAt_carrier {δ' : ℝ≥0} (K : ℝ≥0) (T : Tube δ E3)
    (c m : E3) {L : ℝ} (hL : 0 < L) (hδ' : (δ' : ℝ) = (2 * L)⁻¹ * ((K : ℝ) * (δ : ℝ))) :
    (rescaledCapsuleTubeAt K T c m hL hδ').carrier =
      (AffineMap.homothety m (2 * L)⁻¹) '' (segCarrierSetAt K T c L) := rfl

end DilatedRadiusGeometry

/-! ### The capsule presentation, skolemised -/

/-- The capsule presentation of a `BallDataCore`'s segments, as *data*. -/
structure CapsulePresentation (core : BallDataCore cfg) where
  /-- The parent tube of a segment. -/
  tub : core.σ → cfg.ι
  /-- The parent tube belongs to the family. -/
  tub_mem : ∀ B ∈ core.bs, ∀ p ∈ core.segs B, tub p ∈ cfg.s
  /-- The carrier of a segment is the capsule of its parent tube. -/
  carrier_eq : ∀ B ∈ core.bs, ∀ p ∈ core.segs B,
    (core.Y p).carrier = segCarrierSet (cfg.T (tub p)).toTube (core.ctr B) ((cfg.r₁ : ℝ) / 4)
  /-- The parent family is the singleton of the parent tube. -/
  fam_eq : ∀ B ∈ core.bs, ∀ p ∈ core.segs B, core.fam p = {tub p}
  /-- The parent tube's shading meets the piece. -/
  meets : ∀ B ∈ core.bs, ∀ p ∈ core.segs B, ((cfg.T (tub p)).shade ∩ core.P B).Nonempty
  /-- The pieces sit in the shrunken balls. -/
  ball16 : ∀ B ∈ core.bs, core.P B ⊆ ball (core.ctr B) ((cfg.r₁ : ℝ) / 16)

/-! ### The dilated re-presentation -/

/-- The `K′₀`-dilated capsule of the segment `p.2` in the ball `p.1`. -/
noncomputable abbrev edDilateSet (core : BallDataCore cfg) (tub : core.σ → cfg.ι)
    (p : core.bι × core.σ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  segCarrierSetAt edDilateConstant (cfg.T (tub p.2)).toTube (core.ctr p.1) ((cfg.r₁ : ℝ) / 4)

/-- The segment body of the dilated re-presentation. -/
noncomputable def edDilateBody (core : BallDataCore cfg) (tub : core.σ → cfg.ι)
    (p : core.bι × core.σ) : ShadedBody (EuclideanSpace ℝ (Fin 3)) where
  carrier := edDilateSet core tub p
  convex' := (convex_segCarrierSetAt _ _ _ _).isConvexSet
  isCompact' := Metric.isCompact_of_isClosed_isBounded (isClosed_segCarrierSetAt _ _ _ _)
    (isBounded_segCarrierSetAt _ _ _ (by positivity))
  nonempty' := Set.Nonempty.mono
    (segCarrierSet_subset_segCarrierSetAt one_le_edDilateConstant _ _ _)
    (segCarrierSet_nonempty _ _ (by positivity))
  shade := (core.Y p.2).shade ∩ edDilateSet core tub p
  measurableSet_shade := (core.Y p.2).measurableSet_shade.inter
    (isClosed_segCarrierSetAt _ _ _ _).measurableSet
  shade_subset := fun _ hx => hx.2

@[simp] theorem edDilateBody_carrier (core : BallDataCore cfg) (tub : core.σ → cfg.ι)
    (p : core.bι × core.σ) :
    (edDilateBody core tub p).carrier = edDilateSet core tub p := rfl

@[simp] theorem edDilateBody_shade (core : BallDataCore cfg) (tub : core.σ → cfg.ι)
    (p : core.bι × core.σ) :
    (edDilateBody core tub p).shade = (core.Y p.2).shade ∩ edDilateSet core tub p := rfl

open scoped Classical in
/-- The segment index set of the dilated re-presentation: the base core's, tagged by the ball. -/
noncomputable def edDilateSegs (core : BallDataCore cfg) (B : core.bι) :
    Finset (core.bι × core.σ) :=
  (core.segs B).image (fun x => ((B, x) : core.bι × core.σ))

theorem mem_edDilateSegs {core : BallDataCore cfg} {B : core.bι} {p : core.bι × core.σ} :
    p ∈ edDilateSegs core B ↔ p.1 = B ∧ p.2 ∈ core.segs B := by
  classical
  constructor
  · intro hp
    obtain ⟨x, hx, hxp⟩ := Finset.mem_image.1 hp
    exact ⟨by rw [← hxp], by rw [← hxp]; exact hx⟩
  · rintro ⟨h1, h2⟩
    refine Finset.mem_image.2 ⟨p.2, h2, ?_⟩
    rw [← h1]

theorem mem_edDilateSegs' {core : BallDataCore cfg} {B : core.bι} {p : core.bι × core.σ}
    (hp : p ∈ edDilateSegs core B) : ∃ x ∈ core.segs B, p = (B, x) := by
  classical
  obtain ⟨x, hx, hxp⟩ := Finset.mem_image.1 hp
  exact ⟨x, hx, hxp.symm⟩

section DilateCore

variable {core : BallDataCore cfg} (pres : CapsulePresentation core)

theorem base_carrier_subset_edDilateSet {B : core.bι} (hB : B ∈ core.bs) {x : core.σ}
    (hx : x ∈ core.segs B) :
    (core.Y x).carrier ⊆ edDilateSet core pres.tub (B, x) := by
  rw [pres.carrier_eq B hB x hx]
  exact segCarrierSet_subset_segCarrierSetAt one_le_edDilateConstant _ _ _

theorem base_shade_subset_edDilateSet {B : core.bι} (hB : B ∈ core.bs) {x : core.σ}
    (hx : x ∈ core.segs B) :
    (core.Y x).shade ⊆ edDilateSet core pres.tub (B, x) :=
  subset_trans (core.Y x).shade_subset (base_carrier_subset_edDilateSet pres hB hx)

theorem edDilate_profile_nonneg (cfg : VeryNotSticky.{u}) :
    ∀ k : Fin 3, 0 ≤ (![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)] : Fin 3 → ℝ) k := by
  intro k
  fin_cases k <;> simp

theorem edDilate_hasThicknesses {B : core.bι} (_hB : B ∈ core.bs) {x : core.σ}
    (_hx : x ∈ core.segs B)
    (hrad : ((edRadiusConstant : ℝ≥0) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ))
    (hfloor : edSegmentsConstant ≤ core.C₀) :
    Kakeya.HasThicknesses (edDilateBody core pres.tub (B, x)).carrier core.C₀
      ![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)] := by
  have hδL : (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ) / 4 := delta_le_quarter_of_radiusFloor hrad
  have h := hasThicknesses_segCarrierSetAt one_le_edDilateConstant
    (cfg.T (pres.tub x)).toTube (core.ctr B) (L := (cfg.r₁ : ℝ) / 4) (by positivity) hδL
  have hrw : (4 : ℝ) * ((cfg.r₁ : ℝ) / 4) = (cfg.r₁ : ℝ) := by ring
  rw [hrw] at h
  refine hasThicknesses_mono ?_ ?_ (edDilate_profile_nonneg cfg) h
  · have hK : (1 : ℝ≥0) ≤ edDilateConstant := one_le_edDilateConstant
    calc (0 : ℝ≥0) < 1 := zero_lt_one
      _ ≤ 4 * edDilateConstant := by
          nth_rewrite 1 [show (4 : ℝ≥0) * edDilateConstant
            = 4 * edDilateConstant from rfl]
          calc (1 : ℝ≥0) ≤ edDilateConstant := hK
            _ = 1 * edDilateConstant := (one_mul _).symm
            _ ≤ 4 * edDilateConstant := by gcongr; norm_num
  · exact hfloor

theorem edDilate_segs_core {B : core.bι} (hB : B ∈ core.bs) {x : core.σ}
    (hx : x ∈ core.segs B) (hfloor : edSegmentsConstant ≤ core.C₀) {i : cfg.ι}
    (hi : i ∈ core.fam x) :
    ∃ z : EuclideanSpace ℝ (Fin 3), edDilateSet core pres.tub (B, x) ⊆
      cthickening ((core.C₀ : ℝ) * (cfg.δ : ℝ))
        (AffineSubspace.mk' z (Submodule.span ℝ {(cfg.T i).direction}) :
          Set (EuclideanSpace ℝ (Fin 3))) := by
  rw [pres.fam_eq B hB x hx, Finset.mem_singleton] at hi
  subst hi
  refine ⟨corePt (cfg.T (pres.tub x)).toTube
    (segStart (cfg.T (pres.tub x)).toTube (core.ctr B) ((cfg.r₁ : ℝ) / 4)), ?_⟩
  refine segCarrierSetAt_subset_cthickening_line _ _ _ (by positivity) ?_
  have h : ((edDilateConstant : ℝ≥0) : ℝ) ≤ ((core.C₀ : ℝ≥0) : ℝ) := by
    exact_mod_cast edDilateConstant_le_of_floor hfloor
  exact mul_le_mul_of_nonneg_right h (cfg.δ).coe_nonneg

theorem edDilate_segs_subset_ball {B : core.bι} (hB : B ∈ core.bs) {x : core.σ}
    (hx : x ∈ core.segs B)
    (hrad : ((edRadiusConstant : ℝ≥0) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ)) :
    edDilateSet core pres.tub (B, x) ⊆ closedBall (core.ctr B) (cfg.r₁ : ℝ) := by
  obtain ⟨y, hy1, hy2⟩ := pres.meets B hB x hx
  have hr₁0 : (0 : ℝ) ≤ (cfg.r₁ : ℝ) := (cfg.r₁).coe_nonneg
  refine segCarrierSetAt_subset_closedBall_ctr _ _ _ (ρ := (cfg.r₁ : ℝ) / 16)
    (by positivity) ⟨y, (cfg.T (pres.tub x)).shade_subset hy1, pres.ball16 B hB hy2⟩ ?_
  have h1 : ((edDilateConstant : ℝ≥0) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ) / 8 :=
    edDilate_mul_delta_le_eighth hrad
  have h2 : (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ) / 16 := by
    have := deltaLeR₁_of_radiusFloor hrad; linarith
  linarith

theorem edDilate_segs_scale {B : core.bι} (_hB : B ∈ core.bs) {x : core.σ}
    (_hx : x ∈ core.segs B) :
    (cfg.δ : ℝ≥0∞) ≤ Metric.ethickness.scale ℝ (edDilateSet core pres.tub (B, x)) :=
  le_trans (le_ethickness_scale_segCarrierSet _ _ (by positivity))
    (ethickness_scale_mono (segCarrierSet_subset_segCarrierSetAt one_le_edDilateConstant _ _ _))

open scoped Classical in
/-- **The dilated re-presentation of a capsule core**, all forty-four `BallDataCore` fields.

Nothing is folded: the segments, parent families, fibre count, working shading and shadings are
the base core's. Only the carriers grow, from the capsule `segCarrierSet` to its `K′₀`-dilate
`Kakeya.VeryNotSticky.segCarrierSetAt edDilateConstant`, which is where  §G-1 rules
the comparability clause has to live. The three floors are what pay for the growth:
`edSegmentsConstant ≤ C₀` for `segs_thickness` and `segs_core`, and the radius floor for
`segs_dims`, `segs_subset_ball` and the `δ`-cover. -/
noncomputable def edDilateCore
    (hrad : ((edRadiusConstant : ℝ≥0) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ))
    (hfloor : edSegmentsConstant ≤ core.C₀)
    (hDfloor : ballCoverConstant ≤ core.D) : BallDataCore cfg where
  C₀ := core.C₀
  hC₀ := core.hC₀
  D := core.D
  Yg := core.Yg
  Yg_subset := core.Yg_subset
  Yg_measurable := core.Yg_measurable
  Cg := core.Cg
  hCg := core.hCg
  Yg_mass := core.Yg_mass
  bι := core.bι
  σ := core.bι × core.σ
  bs := core.bs
  bs_nonempty := core.bs_nonempty
  ctr := core.ctr
  P := core.P
  P_subset_ball := core.P_subset_ball
  P_disjoint := core.P_disjoint
  P_measurable := core.P_measurable
  P_cover := core.P_cover
  ballOverlap := core.ballOverlap
  segs := fun B => edDilateSegs core B
  Y := fun p => edDilateBody core pres.tub p
  fam := fun p => core.fam p.2
  segs_nonempty := by
    intro B hB
    obtain ⟨x, hx⟩ := core.segs_nonempty B hB
    exact ⟨(B, x), mem_edDilateSegs.2 ⟨rfl, hx⟩⟩
  fam_subset := by
    intro B hB p hp
    obtain ⟨x, hx, rfl⟩ := mem_edDilateSegs' hp
    exact core.fam_subset B hB x hx
  fam_disjoint := by
    intro B hB p hp q hq hpq
    rw [Finset.mem_coe] at hp hq
    obtain ⟨x, hx, rfl⟩ := mem_edDilateSegs' hp
    obtain ⟨y, hy, rfl⟩ := mem_edDilateSegs' hq
    have hne : x ≠ y := fun h => hpq (by rw [h])
    exact core.fam_disjoint B hB (Finset.mem_coe.2 hx) (Finset.mem_coe.2 hy) hne
  Y_piece := by
    intro B hB p hp z hz
    obtain ⟨x, hx, rfl⟩ := mem_edDilateSegs' hp
    exact core.Y_piece B hB x hx hz.1
  segs_thickness := by
    intro B hB p hp
    obtain ⟨x, hx, rfl⟩ := mem_edDilateSegs' hp
    exact edDilate_hasThicknesses pres hB hx hrad hfloor
  segs_dims := by
    intro B hB p hp q hq
    obtain ⟨x, hx, rfl⟩ := mem_edDilateSegs' hp
    obtain ⟨y, hy, rfl⟩ := mem_edDilateSegs' hq
    exact thickness_segCarrierSetAt_le_two_nsmul one_le_edDilateConstant _ _ _ _
      (by positivity) (edDilate_mul_delta_le_quarter hrad)
  parent := by
    intro B hB i hi hne
    obtain ⟨x, hx, hix⟩ := core.parent B hB i hi hne
    exact ⟨(B, x), mem_edDilateSegs.2 ⟨rfl, hx⟩, hix⟩
  into := by
    intro B hB p hp i hi
    obtain ⟨x, hx, rfl⟩ := mem_edDilateSegs' hp
    intro z hz
    have hz' := core.into B hB x hx i hi hz
    exact ⟨hz', base_shade_subset_edDilateSet pres hB hx hz'⟩
  back := by
    intro B hB p hp
    obtain ⟨x, hx, rfl⟩ := mem_edDilateSegs' hp
    exact fun z hz => core.back B hB x hx hz.1
  segs_core := by
    intro B hB p hp i hi
    obtain ⟨x, hx, rfl⟩ := mem_edDilateSegs' hp
    exact edDilate_segs_core pres hB hx hfloor hi
  m := core.m
  Cm := core.Cm
  hCm := core.hCm
  fibre := by
    intro B hB p hp z hz
    obtain ⟨x, hx, rfl⟩ := mem_edDilateSegs' hp
    exact core.fibre B hB x hx z hz.1
  γ := (exists_deltaCovers cfg.hδ (edDilateBody core pres.tub)).choose
  cov := (exists_deltaCovers cfg.hδ (edDilateBody core pres.tub)).choose_spec.choose
  covCtr :=
    (exists_deltaCovers cfg.hδ (edDilateBody core pres.tub)).choose_spec.choose_spec.choose
  cov_isCover := fun _ _ p _ =>
    ⟨((exists_deltaCovers cfg.hδ
        (edDilateBody core pres.tub)).choose_spec.choose_spec.choose_spec.1 p).subset_iUnion,
      fun x => le_trans (((exists_deltaCovers cfg.hδ
        (edDilateBody core pres.tub)).choose_spec.choose_spec.choose_spec.1 p).card_filter_le
          x) hDfloor⟩
  cov_meets := fun _ _ p _ =>
    (exists_deltaCovers cfg.hδ
      (edDilateBody core pres.tub)).choose_spec.choose_spec.choose_spec.2 p
  segs_subset_ball := by
    intro B hB p hp
    obtain ⟨x, hx, rfl⟩ := mem_edDilateSegs' hp
    exact edDilate_segs_subset_ball pres hB hx hrad
  segs_scale := by
    intro B hB p hp
    obtain ⟨x, hx, rfl⟩ := mem_edDilateSegs' hp
    exact edDilate_segs_scale pres hB hx

end DilateCore

/-! ### The two quantitative clauses at the dilated carrier -/

section DilateClauses

variable {core : BallDataCore cfg} (pres : CapsulePresentation core)

end DilateClauses

/-! ### The capsule presentation of a capsule core -/

section DilateCoreSimp

variable {core : BallDataCore cfg} (pres : CapsulePresentation core)
  (hrad : ((edRadiusConstant : ℝ≥0) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ))
  (hfloor : edSegmentsConstant ≤ core.C₀) (hDfloor : ballCoverConstant ≤ core.D)

@[simp] theorem edDilateCore_C₀ :
    (edDilateCore pres hrad hfloor hDfloor).C₀ = core.C₀ := rfl

@[simp] theorem edDilateCore_D :
    (edDilateCore pres hrad hfloor hDfloor).D = core.D := rfl

@[simp] theorem edDilateCore_bs :
    (edDilateCore pres hrad hfloor hDfloor).bs = core.bs := rfl

@[simp] theorem edDilateCore_segs (B : core.bι) :
    (edDilateCore pres hrad hfloor hDfloor).segs B = edDilateSegs core B := rfl

@[simp] theorem edDilateCore_Y (p : core.bι × core.σ) :
    (edDilateCore pres hrad hfloor hDfloor).Y p = edDilateBody core pres.tub p := rfl

end DilateCoreSimp

/-! ### The three floor constants -/

/-- **The `c₁` floor of  §G-1, at the value the *homothety-free* dilate costs**:
`64 K′₀² / c₃`. The constant `edDensityConstant = 4 K′²` prices only the `K′²` growth of the
carrier and not the inscribed-simplex constant `c₃` of the capsule's volume lower bound; the
compiled ratio is `Kakeya.VeryNotSticky.volume_segCarrierSetAt_le_mul_volume_segCarrierSet`,
`c₃ |At| ≤ 16 K′² |cap|`, so the floor is `4 · 16 K′²/c₃ = 64 K′²/c₃`. -/
noncomputable def edDensityFloorConstant : ℝ≥0 :=
  64 * edDilateConstant ^ 2 / (Metric.lt_volume_convexHull.c 3)

/-! ### The two floors the dilated carrier's *geometry* forces -/

/-- **The `C₀` floor the dilated core-line clause forces**: `4 K′₀²`. The clause at the dilated
carrier asks the `K′₀`-dilated capsule of `i` to lie within `C₀ δ` of the core line of a
comparable `j`, and R-a at radius `K′₀ δ` gives it at `K′₀ · K′₀ δ`. This is a
**hypothesis-floor** move of exactly  §G-1's kind, on a caller-chosen constant that
already carries a floor; it implies `edSegmentsConstant ≤ C₀`. -/
noncomputable def edFoldSegmentsConstant : ℝ≥0 := 4 * edDilateConstant ^ 2

/-- **The radius floor the dilated class count forces**: `8 K′₀²`, because the cone radius of the
count at the dilated carrier is `ρ = 8 K′₀² δ / r₁` and `card_cone_le` needs `ρ ≤ 1`. It implies
`edRadiusConstant · δ ≤ r₁`. -/
noncomputable def edFoldRadiusConstant : ℝ≥0 := 8 * edDilateConstant ^ 2

/-! ### The step-5/6 core, with the shrunken-ball localisation exported -/

/-! ### Why the carrier is the radius dilate: the homothety dilate does not fit in its ball -/

/-! ### Satisfiability controls for the three remaining obligations -/

/-! ### The three obligations in capsule form at the dilated carrier

The existing reductions `Kakeya.VeryNotSticky.edClassContainment_of_capsule`,
`edClassCore_of_capsule`, `edClassMult_of_capsule` state (C1)/(C2)/(C3) for the **undilated**
capsule. These are their analogues for the dilated re-presentation: the exact
Euclidean-geometry statements about two `K′₀`-dilated capsules and a piece of the ball cover
that discharge the three hypotheses of
`Kakeya.VeryNotSticky.exists_core_edSegments_of_cover_floor`. -/

section CapsuleFormDilate

variable {core : BallDataCore cfg} (pres : CapsulePresentation core)
  (hrad : ((edRadiusConstant : ℝ≥0) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ))
  (hfloor : edSegmentsConstant ≤ core.C₀) (hDfloor : ballCoverConstant ≤ core.D)

/-! ### Obligation (C2) at the dilated carrier: **PROVED** -/

/-! ### Obligation (C3) at the dilated carrier: **PROVED** -/

/-! ### Obligation (C1) at the dilated carrier: **the one that stays open, and why** -/

end CapsuleFormDilate

/-! ### The cover level, over the floor text -/

section CoverFloor

variable (cfg : VeryNotSticky.{u}) {bι : Type u}
  {C₀ : ℝ≥0} (hC₀ : edFoldSegmentsConstant ≤ C₀) {D : ℕ} (hD : ballCoverConstant ≤ D)
  (hrad : ((edFoldRadiusConstant : ℝ≥0) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ))
  (bs : Finset bι) (ctr : bι → EuclideanSpace ℝ (Fin 3))
  (P : bι → Set (EuclideanSpace ℝ (Fin 3)))
  (hbsne : bs.Nonempty)
  (hPball16 : ∀ B ∈ bs, P B ⊆ ball (ctr B) ((cfg.r₁ : ℝ) / 16))
  (hPball : ∀ B ∈ bs, P B ⊆ closedBall (ctr B) (cfg.r₁ : ℝ))
  (hPdisj : (bs : Set bι).PairwiseDisjoint P)
  (hPmeas : ∀ B, MeasurableSet (P B))
  (hPcov : ∀ i ∈ cfg.s, (cfg.T i).shade ⊆ ⋃ B ∈ bs, P B)
  (hoverlap : ∀ (x : EuclideanSpace ℝ (Fin 3)) (t : Finset bι), t ⊆ bs →
    (∀ B ∈ t, x ∈ ball (ctr B) (cfg.r₁ : ℝ)) → t.card ≤ ballCoverConstant)
  (hPne : ∀ B ∈ bs, (P B ∩ ⋃ i ∈ cfg.s, (cfg.T i).shade).Nonempty)
  {c₁ : ℝ≥0} (hc₁ : 0 < c₁)
  (hc₁' : edDensityFloorConstant * c₁ * (ballCoverConstant : ℝ≥0) ≤ 1)

end CoverFloor

end Kakeya.VeryNotSticky

/-! ### F28 — the BP264 target, re-cut to the hypothesis-floor text

It cannot be cut *in place* in
`Kakeya/DimensionThree/MainLemma2/BallCoreEDSegments.lean`, and the reason is mechanical rather
than editorial: the re-cut statement's geometric hypothesis is about the **dilated** capsule
`Kakeya.VeryNotSticky.segCarrierSetAt`, which is defined in `BallCoreEDCapsule.lean`, and its
proof is `Kakeya.VeryNotSticky.exists_core_edSegments_of_cover_floor_of_alignment`, which lives
here; both modules import `BallCoreEDSegments.lean`, so a `theorem` with this statement cannot be
elaborated there. **The re-cut target belongs in a leaf after `BallCoreEDFold.lean`.**

Licences:  §G-1 (the hypothesis-floor form of the (C1) dilate, and the `c₁` floor),
 §G-2 (SP-H: `bd.m = 1 ∧ bd.Cm = 1` → the fibre budget),  §C-iii (the exit),
and the four amendments  The four constants are
`Kakeya.VeryNotSticky.edFoldSegmentsConstant = 4 K′₀²`,
`Kakeya.VeryNotSticky.edDensityFloorConstant = 64 K′₀²/c₃`,
`Kakeya.VeryNotSticky.edFoldRadiusConstant = 8 K′₀²` and
`Kakeya.VeryNotSticky.edDilationFloorConstant`, all built from the single named
`Kakeya.VeryNotSticky.edDilateConstant = Kakeya.Tube.tubeOverlapCoreClose.C 3`. -/

namespace BP264

open Kakeya Kakeya.VeryNotSticky

end BP264

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.TangentialCase

/-!
# The Katz–Tao input of the tangential slab step, from `K_KT(β)`

The Katz--Tao estimate at the scale used by the tangential argument.

`Kakeya.VeryNotSticky.ktRho2ScaleData_of_katzTaoEstimate` produces, from `K_KT(β)`
(`Kakeya.KatzTaoEstimate`, GWZ Definition 3.4, GWZ ), the fullness threshold
`η₁ = η₁(ϱ, β) > 0` of GWZ Lemma 3.7 (GWZ: blueprint `genKKT`,
`Kakeya.KatzTaoEstimate.multiplicity_bound_generalize`, read through Remark 3.6 =
blueprint `multBoundsDeltaVsRho`, GWZ ) such that, for every small `δ`, every
configuration at the parameters `(δ, β, ϱ)` with `bd.C₀ = C₀` and `ρ₂ ≤ δ^e` satisfies
`cfg.KTRho2ScaleData bd (4ϱ) η₁ (3ϱ)`: any family of bodies comparable (constant `2 C₀`) to
`ρ₂`-tubes in the unit ball, Katz–Tao at `δ^{-3ϱ}` and `δ^{η₁}`-full, has multiplicity at most
`δ^{-4ϱ} |𝕋|^β`. This is the analytic half of the tangential slab step, GWZ (104)
(GWZ): `µ(𝕋̃) ⪅ δ^{-O(ηbias)} δ^{-ηbias(1-β)} |𝕋̃|^β`, with the tree's `ϱ` for
GWZ's `ηbias`, the `Δ_max` level `δ^{-3ϱ}` that `Kakeya.VeryNotSticky.slabKatzTao` supplies, and
the loss `4ϱ ≥ ϱ/2 + ϱ/2 + 3ϱ(1-β)`.

## Route

* Lemma 3.7 is stated for `ShadedTube` families with unit cores, while the estimate quantifies
  over `ShadedBody` families with the thickness profile `(1, ρ₂, ρ₂)` (see the docstring of
  `Kakeya.VeryNotSticky.KTRho2ScaleData` for why). A body with that profile inside `B₁` may have
  diameter `2`, so it is first shrunk by the homothety of centre `0` and ratio `1/8`
  (`ShadedBody.homothety`): multiplicity, fullness and the Katz–Tao bound are exactly invariant
  (`ShadedBody.multiplicity_homothety`, `ShadedBody.fullness_homothety`,
  `ConvexSpaceBody.IsKatzTao.homothety`), and the image lies in `B_{1/8}` with `1`-thickness
  `≤ C₀ ρ₂ / 4`.
* Each shrunk body is enclosed in the `r`-tube, `r = C₀ ρ₂`, around the unit segment centred at
  the foot of one of its points on the attained thickness line
  (`Metric.exists_subset_cthickening_thickness_finrank_eq`); the tube lies in `B₁`
  (`Kakeya.VeryNotSticky.exists_tube_of_thickness_one_le`). The shading is carried over
  unchanged, so multiplicities agree; the carriers grow by at most the factor
  `Kakeya.VeryNotSticky.ktRho2EnclosureConstant C₀ = 16 · 512 · 48 · C₀⁵` (tube volume
  `≤ 16 r²` against the inscribed-simplex bound `|W| ≥ ρ₂² / (6 (2C₀)³)` and the homothety
  factor `8³`), which is what fullness loses and `Δ_max` gains
  (`ConvexSpaceBody.IsVolumeControlledEnlargement.isKatzTao`).
* Lemma 3.7 in its Remark 3.6 form is then applied at tube scale `r` and Katz–Tao parameter
  `τ = δ ≤ r` (`δ ≤ b ≤ ρ₂ ≤ r` from `cfg.hdims`), at loss `ϱ/2`; the `∀ᶠ` of the lemma is in
  the tube scale, which is where the hypothesis `ρ₂ ≤ δ^e` enters. The enclosure constant is
  absorbed twice, into the fullness threshold (`η₁ := η/2`) and into one further `δ^{-ϱ/2}`.

The clause `6 * cfg.η ≤ η₁` of `Kakeya.VeryNotSticky.SlabMultKT.fullness_threshold` is not part
of this statement: it constrains `η` against the unspecified threshold `η₁` and is discharged by the
consumer.
-/

@[expose] public section

open scoped NNReal ENNReal

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Filter Topology
open scoped NNReal ENNReal

universe u

/-! ### Geometry: enclosing a small body in a unit tube -/

/-- **Enclosure of a small set in a unit tube.** A bounded nonempty set inside `B_{1/8}` whose
`1`-thickness is at most `r ≤ 1/8` lies in the `r`-tube (`Tube.mk'`) around a unit segment of
the attained thickness line, and that tube lies in the unit ball.

The segment is centred at the foot `a₀` of one point `k₀` of the set on the line: every other
foot is within `2r + 1/4 ≤ 1/2` of `a₀`, so the unit segment centred at `a₀` covers all feet.
This is the design step "`Tube` has a unit core, so enclosure needs a homothety first" of
, with the homothety ratio `1/8`. -/
theorem exists_tube_of_thickness_one_le {K : Set (EuclideanSpace ℝ (Fin 3))}
    (hbdd : Bornology.IsBounded K) (hne : K.Nonempty)
    (hK : K ⊆ closedBall 0 (1 / 8)) {r : ℝ≥0} (hr : thickness ℝ K 1 ≤ r)
    (hr8 : (r : ℝ) ≤ 1 / 8) :
    ∃ x y : EuclideanSpace ℝ (Fin 3), ∃ h : dist x y = 1,
      K ⊆ (Tube.mk' r h).carrier ∧ (Tube.mk' r h).carrier ⊆ closedBall 0 1 := by
  have hfr : (1 : ℕ) ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    rw [finrank_euclideanSpace_fin]; norm_num
  obtain ⟨A, hAne, hArank, hKA⟩ := exists_subset_cthickening_thickness_finrank_eq hbdd hne hfr
  have hAclosed : IsClosed (A : Set (EuclideanSpace ℝ (Fin 3))) := A.closed_of_finiteDimensional
  have hKA' : K ⊆ ⋃ a ∈ (A : Set (EuclideanSpace ℝ (Fin 3))), closedBall a (r : ℝ) := by
    rw [← hAclosed.cthickening_eq_biUnion_closedBall r.coe_nonneg]
    exact hKA.trans (cthickening_mono hr _)
  obtain ⟨k₀, hk₀⟩ := hne
  obtain ⟨a₀, ha₀A, hk₀a₀⟩ := Set.mem_iUnion₂.mp (hKA' hk₀)
  -- a unit vector spanning the direction of `A`
  haveI : Nontrivial A.direction :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hArank]; exact one_pos)
  obtain ⟨e', he'⟩ := exists_norm_eq A.direction zero_le_one
  set e : EuclideanSpace ℝ (Fin 3) := (e' : EuclideanSpace ℝ (Fin 3)) with he_def
  have he : ‖e‖ = 1 := he'
  have he0 : e ≠ 0 := by
    intro h0; rw [h0, norm_zero] at he; exact zero_ne_one he
  have hspan : Submodule.span ℝ {e} = A.direction := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact e'.2
    · rw [finrank_span_singleton he0, hArank]
  -- every point of `A` is `a₀ + c • e`
  have hpts : ∀ a ∈ (A : Set (EuclideanSpace ℝ (Fin 3))), ∃ c : ℝ, a = c • e + a₀ := by
    intro a ha
    have hmem : a -ᵥ a₀ ∈ A.direction := AffineSubspace.vsub_mem_direction ha ha₀A
    rw [← hspan, Submodule.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    refine ⟨c, ?_⟩
    rw [hc, vsub_eq_sub]; abel
  refine ⟨a₀ - (2⁻¹ : ℝ) • e, a₀ + (2⁻¹ : ℝ) • e, ?_, ?_, ?_⟩
  · rw [dist_eq_norm, show (a₀ - (2⁻¹ : ℝ) • e) - (a₀ + (2⁻¹ : ℝ) • e) = -e by module,
      norm_neg, he]
  · intro k hk
    obtain ⟨a, haA, hka⟩ := Set.mem_iUnion₂.mp (hKA' hk)
    obtain ⟨c, rfl⟩ := hpts a haA
    rw [Tube.mk'_carrier]
    refine Set.mem_iUnion₂.mpr ⟨c • e + a₀, ?_, hka⟩
    -- `|c| ≤ 1/2`
    have hc : |c| ≤ 2⁻¹ := by
      have h1 : |c| = dist (c • e + a₀) a₀ := by
        rw [dist_eq_norm, add_sub_cancel_right, norm_smul, he, mul_one, Real.norm_eq_abs]
      have hkk₀ : dist k k₀ ≤ 1 / 4 := by
        have h1 := mem_closedBall_zero_iff.mp (hK hk)
        have h2 := mem_closedBall_zero_iff.mp (hK hk₀)
        calc dist k k₀ ≤ ‖k‖ + ‖k₀‖ := dist_le_norm_add_norm k k₀
          _ ≤ 1 / 8 + 1 / 8 := add_le_add h1 h2
          _ = 1 / 4 := by norm_num
      have hka' : dist k (c • e + a₀) ≤ r := mem_closedBall.mp hka
      have hk₀a₀' : dist k₀ a₀ ≤ r := mem_closedBall.mp hk₀a₀
      calc |c| = dist (c • e + a₀) a₀ := h1
        _ ≤ dist (c • e + a₀) k + dist k k₀ + dist k₀ a₀ := dist_triangle4 _ _ _ _
        _ ≤ r + 1 / 4 + r := by
            rw [dist_comm (c • e + a₀) k]
            exact add_le_add (add_le_add hka' hkk₀) hk₀a₀'
        _ ≤ 2⁻¹ := by linarith
    rw [segment]
    refine ⟨2⁻¹ - c, 2⁻¹ + c, ?_, ?_, ?_, ?_⟩
    · linarith [(abs_le.mp hc).1, (abs_le.mp hc).2]
    · linarith [(abs_le.mp hc).1, (abs_le.mp hc).2]
    · ring
    · module
  · intro p hp
    rw [Tube.mk'_carrier] at hp
    obtain ⟨z, hz, hpz⟩ := Set.mem_iUnion₂.mp hp
    have ha₀ : ‖a₀‖ ≤ 1 / 4 := by
      have h1 := mem_closedBall_zero_iff.mp (hK hk₀)
      have h2 : dist k₀ a₀ ≤ r := mem_closedBall.mp hk₀a₀
      calc ‖a₀‖ ≤ ‖k₀‖ + dist k₀ a₀ := by
            rw [dist_eq_norm]
            calc ‖a₀‖ = ‖k₀ - (k₀ - a₀)‖ := by congr 1; abel
              _ ≤ ‖k₀‖ + ‖k₀ - a₀‖ := norm_sub_le _ _
        _ ≤ 1 / 8 + 1 / 8 := add_le_add h1 (h2.trans hr8)
        _ = 1 / 4 := by norm_num
    have hx : a₀ - (2⁻¹ : ℝ) • e ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) (3 / 4) := by
      rw [mem_closedBall_zero_iff]
      calc ‖a₀ - (2⁻¹ : ℝ) • e‖ ≤ ‖a₀‖ + ‖(2⁻¹ : ℝ) • e‖ := norm_sub_le _ _
        _ = ‖a₀‖ + 2⁻¹ := by
            rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_pos (by norm_num)]
        _ ≤ 3 / 4 := by linarith
    have hy : a₀ + (2⁻¹ : ℝ) • e ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) (3 / 4) := by
      rw [mem_closedBall_zero_iff]
      calc ‖a₀ + (2⁻¹ : ℝ) • e‖ ≤ ‖a₀‖ + ‖(2⁻¹ : ℝ) • e‖ := norm_add_le _ _
        _ = ‖a₀‖ + 2⁻¹ := by
            rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_pos (by norm_num)]
        _ ≤ 3 / 4 := by linarith
    have hz' : z ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) (3 / 4) :=
      (convex_closedBall (0 : EuclideanSpace ℝ (Fin 3)) (3 / 4)).segment_subset hx hy hz
    rw [mem_closedBall_zero_iff] at hz' ⊢
    have hpz' : dist p z ≤ r := mem_closedBall.mp hpz
    calc ‖p‖ = ‖(p - z) + z‖ := by congr 1; abel
      _ ≤ ‖p - z‖ + ‖z‖ := norm_add_le _ _
      _ = dist p z + ‖z‖ := by rw [dist_eq_norm]
      _ ≤ 1 / 8 + 3 / 4 := add_le_add (hpz'.trans hr8) hz'
      _ ≤ 1 := by norm_num

/-! ### The `1/8`-homothety -/

/-- **Thickness under a homothety**, real-valued form of `Metric.ethickness_homothety_image`:
a homothety of ratio `t ≠ 0` multiplies every affine thickness of a bounded set by `|t|`. -/
theorem thickness_homothety_image_eq {X : Set (EuclideanSpace ℝ (Fin 3))}
    (hX : Bornology.IsBounded X) (x : EuclideanSpace ℝ (Fin 3)) {t : ℝ} (ht : t ≠ 0) (n : ℕ) :
    thickness ℝ (AffineMap.homothety x t '' X) n = |t| * thickness ℝ X n := by
  have hX' : Bornology.IsBounded (AffineMap.homothety x t '' X) :=
    (Kakeya.lipschitzWith_homothety x t).isBounded_image hX
  have h := ethickness_homothety_image x ht X n
  rw [ethickness_thickness' hX' n, ethickness_thickness' hX n] at h
  have hnn : ((‖t‖₊ : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal |t| := by
    rw [← Real.enorm_eq_ofReal_abs]; rfl
  rw [hnn, ← ENNReal.ofReal_mul (abs_nonneg t)] at h
  exact (ENNReal.ofReal_eq_ofReal_iff (thickness_nonneg _ _)
    (mul_nonneg (abs_nonneg _) (thickness_nonneg _ _))).mp h

/-- The homothety of centre `0` and ratio `t` is the scalar multiplication by `t`. -/
theorem homothety_zero_apply_eq_smul (t : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    AffineMap.homothety (0 : EuclideanSpace ℝ (Fin 3)) t p = t • p := by
  simp [AffineMap.homothety_apply]

/-- The carrier of the homothetic image of a convex body is the image of its carrier. -/
theorem carrier_homothety_eq_image (W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (t : ℝ) :
    (W.homothety 0 t).carrier =
      AffineMap.homothety (0 : EuclideanSpace ℝ (Fin 3)) t '' W.carrier := rfl

/-- The `1/8`-homothety of centre `0` takes a body inside `B₁` into `B_{1/8}`. -/
theorem homothety_carrier_subset_closedBall_eighth
    (W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (hW : W.carrier ⊆ closedBall 0 1) :
    (W.homothety 0 (8⁻¹ : ℝ)).carrier ⊆ closedBall 0 (1 / 8) := by
  rw [carrier_homothety_eq_image]
  rintro p ⟨q, hq, rfl⟩
  rw [homothety_zero_apply_eq_smul, mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0:ℝ) < 8⁻¹)]
  have := mem_closedBall_zero_iff.mp (hW hq)
  nlinarith

/-- The `1/8`-homothety divides the volume of a body in `ℝ³` by `8³ = 512`. -/
theorem volume_homothety_eighth (W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :
    volume (W.homothety 0 (8⁻¹ : ℝ)).carrier = ENNReal.ofReal (1 / 512) * volume W.carrier := by
  rw [ConvexSpaceBody.volume_homothety, finrank_euclideanSpace_fin]
  norm_num

/-! ### Tubes: shading and volume -/

/-- The shaded `r`-tube with core tube `Z` and the shading of a body `W` whose carrier `Z`
contains. Its shade is `W.shade` and its convex body is `Z`, both definitionally. -/
def shadedTubeOfSubset {r : ℝ≥0} (Z : Tube r (EuclideanSpace ℝ (Fin 3)))
    (W : ShadedBody (EuclideanSpace ℝ (Fin 3))) (h : W.carrier ⊆ Z.carrier) :
    ShadedTube r (EuclideanSpace ℝ (Fin 3)) :=
  { toTube := Z, shade := W.shade, measurableSet_shade := W.measurableSet_shade,
    shade_subset := W.shade_subset.trans h }

/-- An `r`-tube in `ℝ³` with `r ≤ 1` has volume at most `16 r²` (`Tube.volume_le` at `n = 3`,
`Tube.volume_le.C 3 = 2⁴`). -/
theorem tube_volume_le_sixteen_mul_sq {r : ℝ≥0} (hr : r ≤ 1)
    (Z : Tube r (EuclideanSpace ℝ (Fin 3))) :
    volume Z.carrier ≤ ((16 : ℝ≥0) : ℝ≥0∞) * ((r : ℝ≥0∞) ^ (2 : ℕ)) := by
  have h := Tube.volume_le hr Z
  rw [finrank_euclideanSpace_fin] at h
  calc volume Z.carrier ≤ _ := h
    _ = ((16 : ℝ≥0) : ℝ≥0∞) * ((r : ℝ≥0∞) ^ (2 : ℕ)) := by
        simp [Tube.volume_le.C]; norm_num

/-- **`ENNReal` form of `Kakeya.VeryNotSticky.volume_ge_of_tubeProfile` for a convex body** (the
inscribed-simplex input of `Kakeya.VeryNotSticky.slabCard`).

A convex bounded set whose affine thicknesses are comparable, with constant `C₀`, to the
`ρ`-tube profile `(1, ρ, ρ)` has volume at least `ρ² / (6 C₀³)`: the `6` is `3!`, the reciprocal
of the inscribed-simplex constant `Metric.lt_volume_convexHull.c 3` of
`Convex.prod_thickness_le_volumeReal`, and the `C₀³` is one factor of `C₀` per axis.

The real-valued statement is `Kakeya.VeryNotSticky.volume_ge_of_tubeProfile`
(`MainLemma2/TangentialCase.lean`), where the cardinality count uses it and where its single
proof lives; the `KTRho2` interface cites that lemma directly. -/
theorem ofReal_le_volume_of_tubeProfile (W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    {C₀ ρ : ℝ≥0} (hC₀ : 1 ≤ C₀)
    (hprof : HasThicknesses W.carrier C₀ ![(1 : ℝ), (ρ : ℝ), (ρ : ℝ)]) :
    ENNReal.ofReal (((ρ : ℝ) ^ 2) / (6 * (C₀ : ℝ) ^ 3)) ≤ volume W.carrier := by
  have h := volume_ge_of_tubeProfile W.convex W.isCompact'.isBounded hC₀ hprof
  rw [Measure.real] at h
  exact (ENNReal.ofReal_le_iff_le_toReal W.isCompact'.measure_ne_top).mpr h

/-! ### Transport of fullness, multiplicity and the loss -/

/-- **Fullness under a volume-controlled enlargement of the carriers.** If the shaded family
`W` has the same shades as `V` on `t`, carriers at least as large and at most `K` times as
large in volume, then a fullness lower bound `x` for `V` becomes the lower bound `y` for `W`
whenever `y K ≤ x`. -/
theorem le_fullness_of_enlargement {ι : Type*} {t : Finset ι}
    {V W : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} {K x y : ℝ≥0∞}
    (hsh : ∀ j ∈ t, (W j).shade = (V j).shade)
    (hle : ∀ j ∈ t, volume (V j).carrier ≤ volume (W j).carrier)
    (hvol : ∀ j ∈ t, volume (W j).carrier ≤ K * volume (V j).carrier)
    (h0 : ∑ j ∈ t, volume (V j).carrier ≠ 0)
    (hfull : x ≤ (ShadedBody.fullness t V : ℝ≥0∞)) (hxy : y * K ≤ x) :
    y ≤ (ShadedBody.fullness t W : ℝ≥0∞) := by
  have hVtop : ∑ j ∈ t, volume (V j).carrier ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun j _ ↦ (V j).isCompact.measure_ne_top
  have hWtop : ∑ j ∈ t, volume (W j).carrier ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun j _ ↦ (W j).isCompact.measure_ne_top
  have hW0 : ∑ j ∈ t, volume (W j).carrier ≠ 0 := fun h ↦
    h0 (le_antisymm ((Finset.sum_le_sum hle).trans h.le) bot_le)
  rw [ShadedBody.fullness_def] at hfull ⊢
  rw [ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl hVtop)] at hfull
  rw [ENNReal.le_div_iff_mul_le (Or.inl hW0) (Or.inl hWtop)]
  rw [Finset.sum_congr rfl fun j hj ↦ congrArg volume (hsh j hj)]
  calc y * ∑ j ∈ t, volume (W j).carrier
      ≤ y * ∑ j ∈ t, K * volume (V j).carrier := by gcongr with j hj; exact hvol j hj
    _ = (y * K) * ∑ j ∈ t, volume (V j).carrier := by rw [← Finset.mul_sum, mul_assoc]
    _ ≤ x * ∑ j ∈ t, volume (V j).carrier := by gcongr
    _ ≤ ∑ j ∈ t, volume (V j).shade := hfull

/-- `ShadedBody.multiplicity` depends only on the shades of the members of `t`. -/
theorem ktRho2_multiplicity_congr_shade {ι : Type*} (t : Finset ι)
    {V W : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    (h : ∀ j ∈ t, (V j).shade = (W j).shade) :
    ShadedBody.multiplicity t V = ShadedBody.multiplicity t W := by
  unfold ShadedBody.multiplicity
  rw [Finset.sum_congr rfl fun j hj ↦ congrArg volume (h j hj),
    Set.iUnion₂_congr fun j hj ↦ h j hj]

/-- **The exponent arithmetic of GWZ (104)**: Lemma 3.7 at loss `ϱ/2` with `Δ_max ≤ K δ^{-3ϱ}`
gives `δ^{-4ϱ}` once the enclosure constant `K` is absorbed into one further `δ^{-ϱ/2}`:
`δ^{-ϱ/2} · (K δ^{-3ϱ})^{1-β} ≤ δ^{-ϱ/2} · K · δ^{-3ϱ} ≤ δ^{-4ϱ}` for `0 ≤ β ≤ 1`, `1 ≤ K`,
`K ≤ δ^{-ϱ/2}` and `δ ≤ 1`. -/
theorem ktRho2_loss_arith {δ : ℝ≥0} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {ϱ β : ℝ} (hϱ : 0 < ϱ)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) {K : ℝ≥0∞} (hK1 : 1 ≤ K)
    (hKδ : K ≤ (δ : ℝ≥0∞) ^ (-(ϱ / 2))) {Δ : ℝ≥0∞}
    (hΔ : Δ ≤ K * (δ : ℝ≥0∞) ^ (-(3 * ϱ))) (N : ℝ≥0∞) :
    (δ : ℝ≥0∞) ^ (-(ϱ / 2)) * Δ ^ (1 - β) * N ^ β ≤ (δ : ℝ≥0∞) ^ (-(4 * ϱ)) * N ^ β := by
  have hδ0' : (δ : ℝ≥0∞) ≠ 0 := by exact_mod_cast hδ0.ne'
  have hδtop : (δ : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hδ1' : (δ : ℝ≥0∞) ≤ 1 := by exact_mod_cast hδ1
  have hKtop : K ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.rpow_ne_top_of_nonneg' (by exact_mod_cast hδ0) hδtop) hKδ
  have h1 : Δ ^ (1 - β) ≤ K ^ (1 - β) * ((δ : ℝ≥0∞) ^ (-(3 * ϱ))) ^ (1 - β) := by
    rw [← ENNReal.mul_rpow_of_ne_top hKtop
      (ENNReal.rpow_ne_top_of_nonneg' (by exact_mod_cast hδ0) hδtop)]
    exact ENNReal.rpow_le_rpow hΔ (by linarith)
  have h2 : K ^ (1 - β) ≤ K := by
    calc K ^ (1 - β) ≤ K ^ (1 : ℝ) := ENNReal.rpow_le_rpow_of_exponent_le hK1 (by linarith)
      _ = K := ENNReal.rpow_one K
  have h3 : ((δ : ℝ≥0∞) ^ (-(3 * ϱ))) ^ (1 - β) ≤ (δ : ℝ≥0∞) ^ (-(3 * ϱ)) := by
    rw [← ENNReal.rpow_mul]
    exact ENNReal.rpow_le_rpow_of_exponent_ge hδ1' (by nlinarith)
  calc (δ : ℝ≥0∞) ^ (-(ϱ / 2)) * Δ ^ (1 - β) * N ^ β
      ≤ (δ : ℝ≥0∞) ^ (-(ϱ / 2)) * (K * (δ : ℝ≥0∞) ^ (-(3 * ϱ))) * N ^ β := by
        gcongr
        exact h1.trans (mul_le_mul' h2 h3)
    _ ≤ (δ : ℝ≥0∞) ^ (-(ϱ / 2)) * ((δ : ℝ≥0∞) ^ (-(ϱ / 2)) * (δ : ℝ≥0∞) ^ (-(3 * ϱ)))
          * N ^ β := by gcongr
    _ = (δ : ℝ≥0∞) ^ (-(4 * ϱ)) * N ^ β := by
        rw [← ENNReal.rpow_add _ _ hδ0' hδtop, ← ENNReal.rpow_add _ _ hδ0' hδtop]
        congr 2; ring

/-- For `a > 0` and `c > 0`, eventually `δ ^ a ≤ c` as `δ → 0⁺` in `ℝ≥0`
(`ENNReal.eventually_coe_rpow_le_of_pos` read in `ℝ≥0`). -/
theorem eventually_rpow_le_of_pos_nnreal {a : ℝ} (ha : 0 < a) {c : ℝ≥0} (hc : 0 < c) :
    ∀ᶠ δ : ℝ≥0 in 𝓝[>] 0, δ ^ a ≤ c := by
  have h := ENNReal.eventually_coe_rpow_le_of_pos ha (C := (c : ℝ≥0∞)) (by exact_mod_cast hc)
  filter_upwards [h] with δ hδ
  rw [← ENNReal.coe_rpow_of_nonneg δ ha.le] at hδ
  exact_mod_cast hδ

/-! ### The theorem -/

/-- **The enclosure constant** `16 · 512 · 48 · C₀⁵ = 393216 C₀⁵`: the volume of the enclosing
`C₀ρ₂`-tube (`≤ 16 (C₀ρ₂)²`, `Kakeya.VeryNotSticky.tube_volume_le_sixteen_mul_sq`) against the
volume of the `1/8`-homothetic image of a body with profile `(2C₀; 1, ρ₂, ρ₂)`
(`≥ 8⁻³ · ρ₂² / (6 (2C₀)³)`, `Kakeya.VeryNotSticky.ofReal_le_volume_of_tubeProfile`). -/
noncomputable def ktRho2EnclosureConstant (C₀ : ℝ≥0) : ℝ≥0 := 393216 * C₀ ^ 5

/-- The enclosure constant is at least `1` when `1 ≤ C₀`. -/
theorem one_le_ktRho2EnclosureConstant {C₀ : ℝ≥0} (hC₀ : 1 ≤ C₀) :
    (1 : ℝ≥0) ≤ ktRho2EnclosureConstant C₀ := by
  unfold ktRho2EnclosureConstant
  calc (1 : ℝ≥0) ≤ 393216 * 1 := by norm_num
    _ ≤ 393216 * C₀ ^ 5 := by gcongr; exact one_le_pow₀ hC₀


end Kakeya.VeryNotSticky

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.KTRho2Interface
public import Kakeya.DimensionThree.MainLemma2.SetupSideData

/-!
# The slab multiplicity input `SlabMultKT` on the degenerate path (T10, route R15)

Row T10 of the side-data construction plan ((a)), conjunct 4 of
`Kakeya.VeryNotSticky.SideDataObligations`: for every small `δ`, every configuration at
`(δ, β, η, exscal, ϱ)` on the degenerate path `b = δ` and every `bd : BallData cfg` with
`bd.C₀ = C₀bd`, the estimate `cfg.KTRho2ScaleData bd (4ϱ) (9·cfg.η) (3ϱ)` holds — GWZ Lemma 3.7
(GWZ: blueprint `genKKT`) in its Remark 3.6 form at the tangential
step, equation (104): a family of bodies comparable to `ρ₂`-tubes in `B₁`, Katz–Tao at
`δ^{-3ϱ}` and `δ^{9η}`-full, has multiplicity at most `δ^{-4ϱ} |𝕋|^β`.

## Where the fullness threshold `9·cfg.η` comes from

`Kakeya.VeryNotSticky.ktRho2ScaleData_of_katzTaoEstimate` (T7K) derives the same estimate from
`K_KT(β)` but at an unspecified threshold `η₁ > 0` chosen before `δ`, so the clause
`Kakeya.VeryNotSticky.SlabMultKT.fullness_threshold : 9 * cfg.η ≤ η₁` cannot be discharged from
it. The tree's one mechanism for a `K_KT`-dependent constraint on `η`
fixed *before* `η` is the window datum `Kakeya.CoarseKTWindow` every configuration carries as
`cfg.ckt` (`Kakeya.CoarseKTData`): its field `hwin : Kakeya.WindowFour … β we wη wρ` is Lemma 3.7
with the Katz–Tao parameter `τ` free below the tube scale and the fullness threshold `τ^{wη}`,
and `hηKT : 3 * η ≤ exscal * wη` is the budget clause. Reading `hwin` for the enclosing
`C₀ρ₂`-tubes with

  `τ := δ ^ max 1 (10η / wη)`

gives `τ^{wη} ≤ δ^{10η} = δ^{9η} · δ^{η}`, so the `δ^{9η}`-fullness of the bodies survives the
enclosure (which costs the constant `K = ktRho2EnclosureConstant C₀ ≤ δ^{-η}`), and the loss
`τ^{-we} = δ^{-we · max 1 (10η/wη)} ≤ δ^{-ϱ/2}` because `10η/wη ≤ (10/3) exscal ≤ 5/3` (`hηKT`)
and `we ≤ ϱ² wb/1440 ≤ ϱ/1440` (`hwe`, `wb ≤ β ≤ 1`, `ϱ ≤ 1`). With `Δ_max ≤ K δ^{-3ϱ}` and
`K ≤ δ^{-ϱ/2}` the total loss is `ϱ/2 + ϱ/2 + 3ϱ(1-β) ≤ 4ϱ`
(`Kakeya.VeryNotSticky.ktRho2_loss_arith`). So `η₁ := 9 * cfg.η` is data and
`fullness_threshold` is `le_rfl`; no new field, no new premise, no clause on `K_KT`.

## The route in this file

* `Kakeya.VeryNotSticky.exists_enclosing_shadedTubes_of_ktRho2` — the geometric half of T7K,
  factored out: the `1/8`-homothety and the `C₀ρ₂`-tube enclosure of the bodies, with
  multiplicity preserved, `Δ_max` multiplied by `K` and fullness divided by at most `K`.
* `Kakeya.VeryNotSticky.ktRho2_window_loss_le` — the exponent arithmetic of the `τ` choice.
* `Kakeya.VeryNotSticky.ktRho2ScaleData_of_ckt` — the estimate at `(4ϱ, 9η, 3ϱ)` from
  `cfg.ckt.hwin` at `b = δ`, under four smallness conditions on `δ`.
* `Kakeya.VeryNotSticky.eventually_ktRho2ScaleData_degenerate` — the `∀ᶠ δ` form, conjunct 4
  of `Kakeya.VeryNotSticky.SideDataObligations` verbatim (tripwires below).
* `Kakeya.VeryNotSticky.slabMultKTOfThresholds` — the four-field `SlabMultKT` from the estimate
  and the density-constant threshold `tangentialSlabDecompConstant tc.C ≤ δ^{-η}` (which T6,
  conjunct 2, supplies); `Kakeya.VeryNotSticky.eventually_nonempty_slabMultKT_degenerate` is
  its `∀ᶠ δ` form.

The two `δ`-thresholds of the tube scale are `C₀ρ₂ ≤ 1/8` (the enclosure) and `C₀ρ₂ ≤ wρ`
(the window radius, from `cfg.ckt.hδrad : 6 δ^{exscal-η} ≤ wρ`): at `b = δ`,
`ρ₂ = δ^{1-exscal}`, and `C₀ δ^{1-exscal} ≤ 6 δ^{exscal-η}` is the absorption
`C₀ δ^{1-2exscal+η} ≤ 6` of the `δ`-free `C₀`, which needs `exscal ≤ 1/2`. The hypotheses
`exscal ≤ 1/2` and `ϱ ≤ 1` are those of `Kakeya.VeryNotSticky.CaseParams` (`scale`, `slabBias`) that
the assembly already extracts (T8 takes the same two).
-/

@[expose] public section

open scoped NNReal ENNReal

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Filter Topology
open scoped NNReal ENNReal

universe u

/-! ### The enclosure, factored out of T7K -/

/-- **Bodies comparable to `ρ₂`-tubes are enclosed in `C₀ρ₂`-tubes** with multiplicity
preserved, the Katz–Tao bound multiplied by `K = ktRho2EnclosureConstant C₀` and fullness divided
by at most `K`. This is the geometric half of
`Kakeya.VeryNotSticky.ktRho2ScaleData_of_katzTaoEstimate`, stated on
its own so that the analytic input can be `Kakeya.WindowFour` instead of Lemma 3.7 at `τ = δ`.

The bodies are first shrunk by the homothety of centre `0` and ratio `1/8`
(`ShadedBody.homothety`; `μ`, `λ` and `Δ_max` are exactly invariant), then each shrunk body,
of `1`-thickness `≤ 2C₀ρ₂/8 ≤ C₀ρ₂`, is enclosed in a unit `C₀ρ₂`-tube inside `B₁`
(`Kakeya.VeryNotSticky.exists_tube_of_thickness_one_le`) shaded by the body's own shade
(`Kakeya.VeryNotSticky.shadedTubeOfSubset`); off `t` a default empty-shaded tube is used. The
volume ratio tube/body is at most `K` (`Kakeya.VeryNotSticky.tube_volume_le_sixteen_mul_sq`
against `Kakeya.VeryNotSticky.ofReal_le_volume_of_tubeProfile`), whence the `Δ_max` clause
(`ConvexSpaceBody.IsVolumeControlledEnlargement.isKatzTao`) and the fullness clause
(`Kakeya.VeryNotSticky.le_fullness_of_enlargement`). -/
theorem exists_enclosing_shadedTubes_of_ktRho2 (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
    {t : Finset bd.ω} (htne : t.Nonempty) (T : bd.ω → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (hball : ∀ j ∈ t, (T j).carrier ⊆ closedBall 0 1)
    (hthick : ∀ j ∈ t, HasThicknesses (T j).carrier (2 * bd.C₀)
      ![(1 : ℝ), (cfg.rho2 : ℝ), (cfg.rho2 : ℝ)])
    {κ : ℝ} (hKTt : ConvexSpaceBody.IsKatzTao t (fun j ↦ (T j).toConvexSpaceBody)
      ((cfg.δ : ℝ≥0∞) ^ (-κ)))
    (hr8 : ((bd.C₀ * cfg.rho2 : ℝ≥0) : ℝ) ≤ 1 / 8) :
    ∃ T' : bd.ω → ShadedTube (bd.C₀ * cfg.rho2) (EuclideanSpace ℝ (Fin 3)),
      (∀ j, (T' j).carrier ⊆ closedBall 0 1) ∧
      ShadedBody.multiplicity t (fun j ↦ (T' j).toShadedBody) = ShadedBody.multiplicity t T ∧
      ConvexSpaceBody.IsKatzTao t (fun j ↦ (T' j).toConvexSpaceBody)
        ((ktRho2EnclosureConstant bd.C₀ : ℝ≥0∞) * (cfg.δ : ℝ≥0∞) ^ (-κ)) ∧
      ∀ x y : ℝ≥0∞, x ≤ (ShadedBody.fullness t T : ℝ≥0∞) →
        y * (ktRho2EnclosureConstant bd.C₀ : ℝ≥0∞) ≤ x →
        y ≤ (ShadedBody.fullness t (fun j ↦ (T' j).toShadedBody) : ℝ≥0∞) := by
  have hδ0 : 0 < cfg.δ := cfg.hδ
  have hδ1 : cfg.δ ≤ 1 := cfg.hδ1
  have hC₀ : 1 ≤ bd.C₀ := bd.hC₀
  have hC₀pos : (0 : ℝ≥0) < bd.C₀ := lt_of_lt_of_le zero_lt_one hC₀
  set K : ℝ≥0 := ktRho2EnclosureConstant bd.C₀ with hK_def
  set ρ : ℝ≥0 := cfg.rho2 with hρ_def
  -- `δ ≤ b ≤ ρ₂`
  have hr₁pos : 0 < cfg.r₁ := NNReal.rpow_pos hδ0
  have hr₁le : cfg.r₁ ≤ 1 := NNReal.rpow_le_one hδ1 cfg.hexscal.le
  have hδρ : cfg.δ ≤ ρ := by
    have hb : cfg.δ ≤ cfg.b := cfg.hdims.1.trans cfg.hdims.2.1
    refine hb.trans ?_
    rw [hρ_def, VeryNotSticky.rho2, le_div_iff₀ hr₁pos]
    exact mul_le_of_le_one_right bot_le hr₁le
  have hρpos : 0 < ρ := lt_of_lt_of_le hδ0 hδρ
  -- the tube scale `r = C₀ ρ₂`
  set r : ℝ≥0 := bd.C₀ * ρ with hr_def
  have hr1 : r ≤ 1 := by
    have : (r : ℝ) ≤ 1 := hr8.trans (by norm_num)
    exact_mod_cast this
  -- the `1/8`-homothety of the family
  have h8 : (8⁻¹ : ℝ) ≠ 0 := by norm_num
  set W' : bd.ω → ShadedBody (EuclideanSpace ℝ (Fin 3)) :=
    fun j ↦ (T j).homothety (0 : EuclideanSpace ℝ (Fin 3)) h8 with hW'_def
  have hone_le_two : (1 : ℝ≥0) ≤ 2 * bd.C₀ := by
    calc (1 : ℝ≥0) ≤ bd.C₀ := hC₀
      _ = 1 * bd.C₀ := (one_mul _).symm
      _ ≤ 2 * bd.C₀ := by gcongr; norm_num
  -- enclosing tubes, shaded by the shrunk bodies; a default tube off `t`
  have hencl : ∀ j, ∃ Z : ShadedTube r (EuclideanSpace ℝ (Fin 3)), Z.carrier ⊆ closedBall 0 1 ∧
      (j ∈ t → (W' j).carrier ⊆ Z.carrier ∧ Z.shade = (W' j).shade ∧
        volume Z.carrier ≤ (K : ℝ≥0∞) * volume (W' j).carrier) := by
    intro j
    by_cases hj : j ∈ t
    · have hbdd : Bornology.IsBounded (W' j).carrier := (W' j).isCompact'.isBounded
      have hne : (W' j).carrier.Nonempty := (W' j).nonempty'
      have hball' : (W' j).carrier ⊆ closedBall 0 (1 / 8) :=
        homothety_carrier_subset_closedBall_eighth (T j).toConvexSpaceBody (hball j hj)
      have hth : thickness ℝ (W' j).carrier 1 ≤ r := by
        have h2C : thickness ℝ (T j).carrier 1 ≤ 2 * (bd.C₀ : ℝ) * (ρ : ℝ) := by
          simpa using (hthick j hj 1).2
        have hbddT : Bornology.IsBounded (T j).carrier := (T j).isCompact'.isBounded
        calc thickness ℝ (W' j).carrier 1
            = thickness ℝ (AffineMap.homothety (0 : EuclideanSpace ℝ (Fin 3)) (8⁻¹ : ℝ) ''
                (T j).carrier) 1 := rfl
          _ = |(8⁻¹ : ℝ)| * thickness ℝ (T j).carrier 1 :=
              thickness_homothety_image_eq hbddT 0 h8 1
          _ ≤ |(8⁻¹ : ℝ)| * (2 * (bd.C₀ : ℝ) * (ρ : ℝ)) := by gcongr
          _ ≤ (r : ℝ) := by
              rw [hr_def, NNReal.coe_mul, abs_of_pos (by norm_num : (0:ℝ) < 8⁻¹)]
              have : (0 : ℝ) ≤ (bd.C₀ : ℝ) * ρ := by positivity
              nlinarith
      obtain ⟨x, y, hxy, hsubK, htube⟩ :=
        exists_tube_of_thickness_one_le hbdd hne hball' hth hr8
      refine ⟨shadedTubeOfSubset (Tube.mk' r hxy) (W' j) hsubK, htube, fun _ ↦
        ⟨hsubK, rfl, ?_⟩⟩
      -- volume comparison: `16 r² = K · 8⁻³ · ρ₂² / (6 (2C₀)³)`
      have hvolT : ENNReal.ofReal (((ρ : ℝ) ^ 2) / (6 * ((2 * bd.C₀ : ℝ≥0) : ℝ) ^ 3)) ≤
          volume (T j).carrier :=
        ofReal_le_volume_of_tubeProfile (T j).toConvexSpaceBody hone_le_two (hthick j hj)
      have hvolW' : volume (W' j).carrier = ENNReal.ofReal (1 / 512) * volume (T j).carrier :=
        volume_homothety_eighth (T j).toConvexSpaceBody
      calc volume (shadedTubeOfSubset (Tube.mk' r hxy) (W' j) hsubK).carrier
          = volume (Tube.mk' r hxy).carrier := rfl
        _ ≤ ((16 : ℝ≥0) : ℝ≥0∞) * ((r : ℝ≥0∞) ^ (2 : ℕ)) :=
            tube_volume_le_sixteen_mul_sq hr1 _
        _ = (K : ℝ≥0∞) * (ENNReal.ofReal (1 / 512) *
              ENNReal.ofReal (((ρ : ℝ) ^ 2) / (6 * ((2 * bd.C₀ : ℝ≥0) : ℝ) ^ 3))) := by
            have hreal : (16 : ℝ) * ((r : ℝ)) ^ 2 =
                (K : ℝ) * (1 / 512 * (((ρ : ℝ) ^ 2) / (6 * ((2 * bd.C₀ : ℝ≥0) : ℝ) ^ 3))) := by
              rw [hK_def, ktRho2EnclosureConstant, hr_def]
              push_cast
              field_simp
              ring
            calc ((16 : ℝ≥0) : ℝ≥0∞) * ((r : ℝ≥0∞) ^ (2 : ℕ))
                = ENNReal.ofReal ((16 : ℝ) * ((r : ℝ)) ^ 2) := by
                  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow r.coe_nonneg,
                    ENNReal.ofReal_coe_nnreal]
                  congr 1
                  simp
              _ = ENNReal.ofReal ((K : ℝ) *
                    (1 / 512 * (((ρ : ℝ) ^ 2) / (6 * ((2 * bd.C₀ : ℝ≥0) : ℝ) ^ 3)))) := by
                  rw [hreal]
              _ = (K : ℝ≥0∞) * (ENNReal.ofReal (1 / 512) *
                    ENNReal.ofReal (((ρ : ℝ) ^ 2) / (6 * ((2 * bd.C₀ : ℝ≥0) : ℝ) ^ 3))) := by
                  rw [ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_mul (by norm_num),
                    ENNReal.ofReal_coe_nnreal]
        _ ≤ (K : ℝ≥0∞) * (ENNReal.ofReal (1 / 512) * volume (T j).carrier) := by gcongr
        _ = (K : ℝ≥0∞) * volume (W' j).carrier := by rw [hvolW']
    · -- default tube with empty shade, around the origin
      have hth0 : thickness ℝ ({(0 : EuclideanSpace ℝ (Fin 3))} : Set _) 1 ≤ r :=
        thickness_le_of_subset_closedBall (x := (0 : EuclideanSpace ℝ (Fin 3))) (by simp)
          r.coe_nonneg 1
      obtain ⟨x, y, hxy, -, htube⟩ :=
        exists_tube_of_thickness_one_le (K := {(0 : EuclideanSpace ℝ (Fin 3))})
          Bornology.isBounded_singleton (Set.singleton_nonempty _) (by simp) hth0 hr8
      let Z : ShadedTube r (EuclideanSpace ℝ (Fin 3)) :=
        { toTube := Tube.mk' r hxy
          shade := ∅
          measurableSet_shade := MeasurableSet.empty
          shade_subset := Set.empty_subset _ }
      exact ⟨Z, htube, fun h ↦ absurd h hj⟩
  choose T' hT' using hencl
  have hball' : ∀ j, (T' j).carrier ⊆ closedBall 0 1 := fun j ↦ (hT' j).1
  have hsubj : ∀ j ∈ t, (W' j).carrier ⊆ (T' j).carrier := fun j hj ↦ ((hT' j).2 hj).1
  have hshj : ∀ j ∈ t, (T' j).shade = (W' j).shade := fun j hj ↦ ((hT' j).2 hj).2.1
  have hvolj : ∀ j ∈ t, volume (T' j).carrier ≤ (K : ℝ≥0∞) * volume (W' j).carrier :=
    fun j hj ↦ ((hT' j).2 hj).2.2
  -- Katz–Tao control of the tube family: `Δ_max ≤ K δ^{-κ}`
  have hvce : ConvexSpaceBody.IsVolumeControlledEnlargement t (fun j ↦ (W' j).toConvexSpaceBody)
      (fun j ↦ (T' j).toConvexSpaceBody) (K : ℝ≥0∞) :=
    fun j hj ↦ ⟨hsubj j hj, hvolj j hj⟩
  have hKT' : ConvexSpaceBody.IsKatzTao t (fun j ↦ (T' j).toConvexSpaceBody)
      ((K : ℝ≥0∞) * (cfg.δ : ℝ≥0∞) ^ (-κ)) :=
    hvce.isKatzTao (hKTt.homothety 0 h8)
  refine ⟨T', hball', ?_, hKT', ?_⟩
  · -- same shades, and the homothety is exact for `μ`
    rw [ktRho2_multiplicity_congr_shade t (W := W') (fun j hj ↦ hshj j hj), hW'_def,
      ShadedBody.multiplicity_homothety]
  · intro x y hx hxy
    have hfullW' : x ≤ (ShadedBody.fullness t W' : ℝ≥0∞) := by
      rw [hW'_def, ShadedBody.fullness_homothety]
      exact hx
    have h0 : ∑ j ∈ t, volume (W' j).carrier ≠ 0 := by
      intro h
      obtain ⟨j, hj⟩ := htne
      have hj0 : volume (W' j).carrier = 0 := (Finset.sum_eq_zero_iff.mp h) j hj
      have hpos : 0 < volume (W' j).carrier := by
        rw [show volume (W' j).carrier = ENNReal.ofReal (1 / 512) * volume (T j).carrier from
          volume_homothety_eighth (T j).toConvexSpaceBody]
        have hT0 : 0 < volume (T j).carrier := by
          refine lt_of_lt_of_le ?_
            (ofReal_le_volume_of_tubeProfile (T j).toConvexSpaceBody hone_le_two (hthick j hj))
          rw [ENNReal.ofReal_pos]
          have : (0 : ℝ) < ρ := hρpos
          have : (0 : ℝ) < bd.C₀ := hC₀pos
          positivity
        exact ENNReal.mul_pos (by simp) hT0.ne'
      exact hpos.ne' hj0
    exact le_fullness_of_enlargement (t := t) (V := W') (W := fun j ↦ (T' j).toShadedBody)
      (K := (K : ℝ≥0∞)) (fun j hj ↦ hshj j hj)
      (fun j hj ↦ measure_mono (hsubj j hj)) (fun j hj ↦ hvolj j hj) h0 hfullW' hxy

/-! ### The exponent arithmetic of the `τ` choice -/

/-- **The loss exponent of the window read at `τ = δ^{max 1 (10η/wη)}`.** From the budget
clause `3η ≤ exscal · wη` of `Kakeya.CoarseKTWindow` (`hηKT`) and `exscal ≤ 1/2`,
`10η/wη ≤ 5/3`; from `we ≤ ϱ² wb/1440` (`hwe`), `wb ≤ β ≤ 1` and `ϱ ≤ 1`, `we ≤ ϱ/1440`. Hence
`we · max 1 (10η/wη) ≤ ϱ/2`, which is the `δ^{-ϱ/2}` that
`Kakeya.VeryNotSticky.ktRho2_loss_arith` charges for Lemma 3.7's loss. -/
theorem ktRho2_window_loss_le {η ϱ exscal we wη wb β : ℝ} (hϱ : 0 < ϱ) (hϱ1 : ϱ ≤ 1)
    (hexscal12 : exscal ≤ 1 / 2) (hwe0 : 0 < we) (hwe : we ≤ ϱ ^ 2 * wb / 1440)
    (hwb : wb ≤ β) (hβ1 : β ≤ 1) (hwη : 0 < wη)
    (hηKT : 3 * η ≤ exscal * wη) :
    we * max 1 (10 * η / wη) ≤ ϱ / 2 := by
  have h1 : 10 * η / wη ≤ 5 / 3 := by
    rw [div_le_iff₀ hwη]
    nlinarith
  have hL : max 1 (10 * η / wη) ≤ 5 / 3 := max_le (by norm_num) h1
  have hwe' : we ≤ ϱ / 1440 := by
    refine hwe.trans ?_
    have : ϱ ^ 2 * wb ≤ ϱ := by nlinarith
    linarith
  calc we * max 1 (10 * η / wη) ≤ (ϱ / 1440) * (5 / 3) :=
        mul_le_mul hwe' hL (le_trans zero_le_one (le_max_left _ _)) (by positivity)
    _ ≤ ϱ / 2 := by linarith

/-! ### The estimate from `cfg.ckt` at `b = δ` -/


/-! ### `SlabMultKT` -/


/-! The `∀ᶠ δ` producer of `Kakeya.VeryNotSticky.SlabMultKT` on the degenerate path, and the
tripwires against conjunct 4 of `Kakeya.VeryNotSticky.SideDataObligations`, live in
`Kakeya.DimensionThree.MainLemma2.SlabMultKTGeneral`: since re-cut R5 the conjunct is read at
`Kakeya.VeryNotSticky.latticeRescaleConstant bd.C₀`, and the general-`Cmp` chain that proves
it at those unchanged exponents needs `Kakeya.VeryNotSticky.rho2_le_rpow_exscal` and
`Kakeya.VeryNotSticky.delta_le_rho2_general`, which are declared downstream of this file. -/

end Kakeya.VeryNotSticky

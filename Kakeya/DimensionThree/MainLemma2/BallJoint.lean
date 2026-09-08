/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.BallConstruction

/-!
# The (C4) factoring of Configuration `hyp:ml2setup` at ball-level granularity

`Kakeya.VeryNotSticky.BallDataCore` (in `Kakeya.DimensionThree.MainLemma2.BallConstruction`)
supplies forty-two of the sixty-seven fields of `Kakeya.VeryNotSticky.BallData`, uniformly in
the configuration.  This file closes twenty-two of the remaining twenty-five, leaving only
`Kakeya.VeryNotSticky.BallData.segs_dilation` together with its comparison constant `Cdil`, which every lemma below takes as a parameter.

The point is a structural one about the *statement* of `BallData`, and it is worth stating
plainly because it decides where the mathematical content of blueprint `lem:ml2setupSideData`
actually lives:

* the four constants `CF`, `Cbias`, `c₁` and `C₀` are **free fields** of `BallData`, bounded
  only by `1 ≤ CF`, `1 ≤ Cbias`, `0 < c₁`, `1 ≤ C₀`.  Nothing in `BallData` bounds any of them
  from above;
* every clause of (C4) — `frostman`, `biasedDensity`, `bodies_antiClustering` — and the (C5)
  clause `segs_density` are *monotone* in those constants;
* the families of `BallData` are `Finset`s, so a constant may be chosen as a maximum over the
  data already constructed.

Consequently (C4) can be realized by the degenerate factoring **one body per ball, the body
being the ball itself**, at a `CF` and a `Cbias` read off the constructed segments.  The
resulting `BallData` is of course useless to the case split, whose bundle
`Kakeya.VeryNotSticky.CaseSideData` bounds each of those constants from above in terms of
`cfg.δ` (`Kakeya.VeryNotSticky.thickDensityThresholds_canonical` takes
`CP^{1+ηF} δ^{τ ηF - η} ≤ bd.c₁` and `Cbias (48 C₀^6)^3 ≤ δ^{-τϱ}`).  That is exactly the
finding: **the difficulty of `Kakeya.VeryNotSticky.exists_setup_caseSideData` is not in
`BallData` at all** — barring `segs_dilation`, whose constant `Cdil` is bounded only
downstream, in `Kakeya.VeryNotSticky.SlabScale.final` — but in the
quantitative side conditions of `CaseSideData`.

## What is proved

* `Kakeya.VeryNotSticky.BallDataCore.nonempty_ballData_of_dilation` — from a `BallDataCore`
  whose segments have shading of positive measure, from the single scale condition
  `r₁ ≤ C₀ a`, and from `segs_dilation` at any constant `Cdil ≥ 1`, a full
  `Kakeya.VeryNotSticky.BallData`.
* `Kakeya.VeryNotSticky.exists_shade_delete_positive` — the *null* refinement that supplies
  the positivity hypothesis: deleting one global null set from every shading leaves all
  shading volumes unchanged and makes every non-empty intersection of a shading with a piece
  of the cover have positive measure.

The positivity hypothesis is not cosmetic.  It is the exact form of the emptiness phenomenon
recorded : a configuration one of whose shadings meets a piece in a
**non-empty null set** admits no `BallData` at all, since `parent` then forces a segment whose
shade is null while `segs_thickness` forces its carrier to have positive volume, so
`segs_density` forces `c₁ = 0`.  The obstruction is measure-theoretic, not quantitative: a
crumb of small but *positive* measure is harmless, because `c₁` may be taken smaller.
-/

@[expose] public section

open scoped NNReal ENNReal

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set ShadedBody
open scoped NNReal ENNReal

universe u

section Positivity

variable {cfg : VeryNotSticky.{u}}


end Positivity


section Arithmetic


end Arithmetic

section Joint

variable {cfg : VeryNotSticky.{u}}


end Joint

section MonoC

variable {cfg : VeryNotSticky.{u}}

/-- A thickness profile with a larger comparison constant. -/
private lemma hasThicknesses_mono {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin 3))} {C C' : ℝ≥0}
    {t : Fin n → ℝ} (h : Kakeya.HasThicknesses K C t) (hC : 0 < C) (hCC' : C ≤ C')
    (ht : ∀ k, 0 ≤ t k) : Kakeya.HasThicknesses K C' t := by
  intro k
  obtain ⟨h1, h2⟩ := h k
  have hCR : (0 : ℝ) < (C : ℝ) := by exact_mod_cast hC
  have hle : (C : ℝ) ≤ (C' : ℝ) := by exact_mod_cast hCC'
  have hinv : ((C' : ℝ))⁻¹ ≤ ((C : ℝ))⁻¹ := by
    apply inv_anti₀ hCR hle
  refine ⟨le_trans ?_ h1, le_trans h2 ?_⟩
  · exact mul_le_mul_of_nonneg_right hinv (ht k)
  · exact mul_le_mul_of_nonneg_right hle (ht k)


end MonoC

section NullRefinement

variable {cfg : VeryNotSticky.{u}}


end NullRefinement

section DeleteShade

/-- Deleting a measurable set from the shading of a shaded `δ`-tube, leaving the tube itself
untouched. -/
def deleteShadeTube {δ : ℝ≥0} (T : ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (S : Set (EuclideanSpace ℝ (Fin 3))) (hS : MeasurableSet S) :
    ShadedTube δ (EuclideanSpace ℝ (Fin 3)) where
  toTube := T.toTube
  shade := T.shade \ S
  measurableSet_shade := T.measurableSet_shade.diff hS
  shade_subset := Set.Subset.trans Set.sdiff_subset T.shade_subset

@[simp] lemma deleteShadeTube_shade {δ : ℝ≥0} (T : ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (S : Set (EuclideanSpace ℝ (Fin 3))) (hS : MeasurableSet S) :
    (deleteShadeTube T S hS).shade = T.shade \ S := rfl

@[simp] lemma deleteShadeTube_toTube {δ : ℝ≥0} (T : ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (S : Set (EuclideanSpace ℝ (Fin 3))) (hS : MeasurableSet S) :
    (deleteShadeTube T S hS).toTube = T.toTube := rfl

/-- **A global deletion does not change any shade class at a surviving point.**  This is why
the deletion of the null crumbs is invisible to `ShadedTube.ShadedUniformTubeSet`: the four
clauses of that bundle are quantified over points of the shaded union, and at a point outside
the deleted set no member of the family has lost the point. -/
lemma shadeClass_deleteShadeTube {δ : ℝ≥0} {ι : Type*} (s : Finset ι)
    (V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (S : Set (EuclideanSpace ℝ (Fin 3))) (hS : MeasurableSet S)
    (assign : ι → ι) (j : ι) {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∉ S) :
    ShadedTube.shadeClass s (fun i ↦ deleteShadeTube (V i) S hS) assign j x
      = ShadedTube.shadeClass s V assign j x := by
  classical
  simp only [ShadedTube.shadeClass]
  refine Finset.filter_congr fun i _ ↦ ?_
  simp [hx]

/-- **The uniform hierarchy survives a global deletion.** -/
def shadedUniform_deleteShadeTube {δ : ℝ≥0} {ι : Type*} {s : Finset ι}
    {V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {N : ℕ} {C : ℝ≥0}
    (𝒱 : ShadedTube.ShadedUniformTubeSet s V N C)
    (S : Set (EuclideanSpace ℝ (Fin 3))) (hS : MeasurableSet S) :
    ShadedTube.ShadedUniformTubeSet s (fun i ↦ deleteShadeTube (V i) S hS) N C where
  tubeUniform := 𝒱.tubeUniform
  branchingN := 𝒱.branchingN
  localN := 𝒱.localN
  card_shadeClass_le := by
    intro x hx k hk i hi hxi
    have hxS : x ∉ S := hxi.2
    rw [shadeClass_deleteShadeTube s V S hS _ _ hxS]
    refine 𝒱.card_shadeClass_le x ?_ k hk i hi hxi.1
    exact Set.mem_biUnion hi hxi.1
  le_card_shadeClass := by
    intro x hx k hk i hi hxi
    have hxS : x ∉ S := hxi.2
    rw [shadeClass_deleteShadeTube s V S hS _ _ hxS]
    refine 𝒱.le_card_shadeClass x ?_ k hk i hi hxi.1
    exact Set.mem_biUnion hi hxi.1
  branchingN_le := by
    intro x hx k hk
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 hx
    exact 𝒱.branchingN_le x (Set.mem_biUnion hi hxi.1) k hk
  le_branchingN := by
    intro x hx k hk
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 hx
    exact 𝒱.le_branchingN x (Set.mem_biUnion hi hxi.1) k hk

/-- **A configuration with its null crumbs deleted.**

Every field of `Kakeya.VeryNotSticky` survives the deletion of a *null* set from every
shading: the carriers are untouched, so the tube-level fields are unchanged; the shading
volumes are untouched, so `fullness_ge`, `shading_lb` and `shading_ub` are unchanged; and the
deleted set is one and the same for every tube, so `uniform` is unchanged
(`Kakeya.VeryNotSticky.shadedUniform_deleteShadeTube`).

This is the refinement that a joint construction of `cfg` and `bd` may perform for free.  Its
refinement constant is `1`, so it costs nothing against the target's conjunct `δ^η ≤ c`. -/
noncomputable def deleteShade (cfg : VeryNotSticky.{u})
    (S : Set (EuclideanSpace ℝ (Fin 3))) (hS : MeasurableSet S) (hnull : volume S = 0) :
    VeryNotSticky.{u} :=
  { cfg with
    T := fun i ↦ deleteShadeTube (cfg.T i) S hS
    uniform := cfg.uniform.elim fun 𝒰 ↦ ⟨shadedUniform_deleteShadeTube 𝒰 S hS⟩
    fullness_ge := by
      have hnum : ∑ i ∈ cfg.s, volume (deleteShadeTube (cfg.T i) S hS).shade
          = ∑ i ∈ cfg.s, volume (cfg.T i).shade :=
        Finset.sum_congr rfl fun i _ ↦ measure_sdiff_null (s := (cfg.T i).shade) hnull
      have heq : ShadedBody.fullness cfg.s
            (fun i ↦ (deleteShadeTube (cfg.T i) S hS).toShadedBody)
          = ShadedBody.fullness cfg.s (fun i ↦ (cfg.T i).toShadedBody) := by
        rw [← ENNReal.coe_inj, ShadedBody.fullness_def, ShadedBody.fullness_def]
        exact congrArg (fun z ↦ z / ∑ i ∈ cfg.s, volume (cfg.T i).carrier) hnum
      rw [ge_iff_le, heq]
      exact cfg.fullness_ge
    shading_lb := by
      intro i hi
      have h : volume ((cfg.T i).shade \ S) = volume (cfg.T i).shade :=
        measure_sdiff_null (s := (cfg.T i).shade) hnull
      simpa [h] using cfg.shading_lb i hi
    shading_ub := by
      intro i hi
      have h : volume ((cfg.T i).shade \ S) = volume (cfg.T i).shade :=
        measure_sdiff_null (s := (cfg.T i).shade) hnull
      simpa [h] using cfg.shading_ub i hi
    coarseLocalMass := by
      -- deleting a null set from every shade leaves the datum standing: the coarse
      -- neighbourhood and the ball intersection only shrink, while the total mass is unchanged.
      intro k hk x
      have hUeq : (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody.shade \ S))
          = (⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade) \ S := by
        ext y
        simp only [Set.mem_iUnion, Set.mem_sdiff, exists_prop]
        tauto
      have hvol : volume ((⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade) \ S)
          = volume (⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade) :=
        measure_sdiff_null (s := ⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade) hnull
      have hsub : (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody.shade \ S))
          ⊆ ⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade :=
        Set.iUnion₂_mono fun i _ => Set.sdiff_subset
      have hmass := cfg.coarseLocalMass k hk x
      show (cfg.δ : ℝ≥0∞) ^ cfg.η *
          (volume (Metric.cthickening
                (2 * (Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : ℝ))
                (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody.shade \ S))) *
            (volume ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody.shade \ S)) ∩
                  Metric.ball x (Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : ℝ)) /
              volume (Metric.ball x (Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : ℝ)))) ≤
        volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody.shade \ S))
      rw [hUeq, hvol]
      have hd : ((⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade) \ S)
          ⊆ ⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade := Set.sdiff_subset
      exact le_trans (mul_le_mul' le_rfl (mul_le_mul'
        (measure_mono (Metric.cthickening_subset_of_subset _ hd))
        (ENNReal.div_le_div_right (measure_mono (Set.inter_subset_inter_left _ hd)) _))) hmass }

@[simp] lemma deleteShade_shade (cfg : VeryNotSticky.{u})
    (S : Set (EuclideanSpace ℝ (Fin 3))) (hS : MeasurableSet S) (hnull : volume S = 0)
    (i : cfg.ι) : ((cfg.deleteShade S hS hnull).T i).shade = (cfg.T i).shade \ S := rfl

end DeleteShade

section CoreTransport

variable {cfg : VeryNotSticky.{u}}

/-- **The per-ball core survives the deletion of the null crumbs.**

The same global null set is removed from every tube shading, from the working shading `Y_g`
and from every segment shading, so `into`, `back` and `fibre` — the three clauses that read the
shadings pointwise — transport verbatim: at a surviving point no tube has lost the point, so the
fibre count is unchanged. The working shading becomes `Y_g(T) \ S`, at the same loss `Cg`,
since deleting a null set changes no volume. -/
noncomputable def BallDataCore.deleteShade (core : BallDataCore cfg)
    (S : Set (EuclideanSpace ℝ (Fin 3))) (hS : MeasurableSet S) (hnull : volume S = 0) :
    BallDataCore (cfg.deleteShade S hS hnull) where
  C₀ := core.C₀
  hC₀ := core.hC₀
  D := core.D
  Yg := fun i ↦ core.Yg i \ S
  Yg_subset := fun i hi ↦ Set.sdiff_subset_sdiff_left (core.Yg_subset i hi)
  Yg_measurable := fun i hi ↦ (core.Yg_measurable i hi).diff hS
  Cg := core.Cg
  hCg := core.hCg
  Yg_mass := by
    have h1 : ∀ i, volume ((cfg.T i).shade \ S) = volume (cfg.T i).shade :=
      fun i ↦ measure_sdiff_null (s := (cfg.T i).shade) hnull
    have h2 : ∀ i, volume (core.Yg i \ S) = volume (core.Yg i) :=
      fun i ↦ measure_sdiff_null (s := core.Yg i) hnull
    simp only [deleteShade_shade, h1, h2]
    exact core.Yg_mass
  bι := core.bι
  σ := core.σ
  bs := core.bs
  bs_nonempty := core.bs_nonempty
  ctr := core.ctr
  P := core.P
  P_subset_ball := core.P_subset_ball
  P_disjoint := core.P_disjoint
  P_measurable := core.P_measurable
  P_cover := fun i hi ↦ Set.Subset.trans Set.sdiff_subset (core.P_cover i hi)
  ballOverlap := core.ballOverlap
  segs := core.segs
  Y := fun p ↦ (core.Y p).restrictShade Sᶜ hS.compl
  fam := core.fam
  segs_nonempty := core.segs_nonempty
  fam_subset := core.fam_subset
  fam_disjoint := core.fam_disjoint
  Y_piece := fun B hB p hp ↦
    Set.Subset.trans Set.inter_subset_left (core.Y_piece B hB p hp)
  segs_thickness := core.segs_thickness
  segs_dims := core.segs_dims
  parent := by
    intro B hB i hi hne
    refine core.parent B hB i hi ?_
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, hx.1.1, hx.2⟩
  into := by
    intro B hB p hp i hi x hx
    exact ⟨core.into B hB p hp i hi ⟨hx.1.1, hx.2⟩, hx.1.2⟩
  back := by
    intro B hB p hp x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (core.back B hB p hp hx.1)
    exact Set.mem_biUnion hi ⟨hxi, hx.2⟩
  segs_core := core.segs_core
  m := core.m
  Cm := core.Cm
  hCm := core.hCm
  fibre := by
    classical
    intro B hB p hp x hx
    have hxS : x ∉ S := hx.2
    simp only [Set.mem_sdiff, hxS, not_false_eq_true, and_true]
    exact core.fibre B hB p hp x hx.1
  γ := core.γ
  cov := core.cov
  covCtr := core.covCtr
  cov_isCover := core.cov_isCover
  cov_meets := core.cov_meets
  segs_subset_ball := core.segs_subset_ball
  segs_scale := core.segs_scale


end CoreTransport

section Capstone


end Capstone

section Dilation

variable {cfg : VeryNotSticky.{u}}


end Dilation

section Rigidity


end Rigidity

section Coarse


end Coarse

end Kakeya.VeryNotSticky

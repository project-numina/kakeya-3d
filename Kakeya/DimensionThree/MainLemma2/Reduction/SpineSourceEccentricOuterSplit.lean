/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceEccentricScaleLedger
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineTwoScale

/-!
# The one-scale outer split and its normalization

`Kakeya.ML2Core.SourceEccentricOuterSplit` records the weighted one-scale split of a fixed
tower at level `a`: the outer family, its outer shading, the inner subshading, the selected
full cell `chosen`, and the refinement, fullness, multiplicity and cardinality rows at loss
`L`. `SourceEccentricOuterNormalization` is the fixed homothety by `1/8` with unit-core
replacement. `source_exists_eccentric_outer_split` constructs both eventually in `delta` at
loss `sourceEccentricLogLoss K delta`, and `source_exists_eccentric_outer_estimate` derives
the outer multiplicity bound from a `KatzTaoEstimate`, treating `a = 0` by the root cardinal
bound. Builds on `SpineTwoScale` and the scale ledger.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

universe u

variable {iota : Type u} {delta : ℝ≥0} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace ℝ (Fin 3))} {M C : Nat}

/-- The actual one-scale weighted split and its selected full assigned cell.
The coarse shading need not be contained in the original fine shade union. -/
structure SourceEccentricOuterSplit (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3))) (a : Nat) (L : ℝ≥0) where
  outer : Finset iota
  outer_subset : outer <= Q.indexSet a
  outer_nonempty : outer.Nonempty
  outerShade : iota -> ShadedTube (sourceTowerRadius delta M a) (EuclideanSpace ℝ (Fin 3))
  outer_tubes : forall i, (outerShade i).toTube = Q.tube a i
  innerShade : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3))
  inner_tubes : forall i, (innerShade i).toTube = T i
  inner_subshade : forall i, (innerShade i).shade <= (Z i).shade
  chosen : iota
  chosen_mem : chosen ∈ outer
  chosen_cell_nonempty : (Q.cell a chosen).Nonempty
  refinedFine : Finset iota
  refined_fine_eq : refinedFine = S.filter (fun i => Q.place a i ∈ outer)
  fine_refinement : ShadedBody.IsCRefinement refinedFine (fun i => (innerShade i).toShadedBody)
    S (fun i => (Z i).toShadedBody) L⁻¹
  refined_mass : (∑ i ∈ S, volume (Z i).shade) <=
    (L : ℝ≥0∞) * ∑ i ∈ refinedFine, volume (innerShade i).shade
  fine_under_outer : forall i, i ∈ refinedFine ->
    (innerShade i).shade <= (outerShade (Q.place a i)).shade
  outer_fullness : ShadedBody.fullness S (fun i => (Z i).toShadedBody) / L <=
    ShadedBody.fullness outer (fun i => (outerShade i).toShadedBody)
  inner_fullness : ShadedBody.fullness S (fun i => (Z i).toShadedBody) / L <=
    ShadedBody.fullness (Q.cell a chosen) (fun i => (innerShade i).toShadedBody)
  inner_mass_pos : 0 < ∑ i ∈ Q.cell a chosen, volume (innerShade i).shade
  split_multiplicity : ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <=
    (L : ℝ≥0∞) * ShadedBody.multiplicity outer (fun i => (outerShade i).toShadedBody) *
      ShadedBody.multiplicity (Q.cell a chosen) (fun i => (innerShade i).toShadedBody)
  card_product : (outer.card : ℝ≥0∞) * ((Q.cell a chosen).card : ℝ≥0∞) <=
    2 * (S.card : ℝ≥0∞)
  outer_density : Kakeya.maxDensity outer (fun i => (Q.tube a i).toConvexSpaceBody) <=
    Kakeya.maxDensity (Q.indexSet a) (fun i => (Q.tube a i).toConvexSpaceBody)

/-- A single fixed homothety and genuine unit-core replacement resolve the B3
outer window. The two mass identities name the very same outer shade witness. -/
structure SourceEccentricOuterNormalization (Q : SourceThreadedTower S T M C)
    {Z : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3))} {a : Nat} {L : ℝ≥0}
    (O : SourceEccentricOuterSplit Q Z a L) (Cgeom : ℝ≥0) where
  affine : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)
  affine_eq : forall x, affine x = (1 / 8 : ℝ) • x
  tubes : iota -> ShadedTube (sourceTowerRadius delta M a / 8) (EuclideanSpace ℝ (Fin 3))
  shade_image : forall i, i ∈ O.outer -> (tubes i).shade = affine '' (O.outerShade i).shade
  carrier_image : forall i, i ∈ O.outer -> affine '' (Q.tube a i).carrier <= (tubes i).carrier
  volume_comparison : forall i, i ∈ O.outer -> volume (tubes i).carrier <=
    (Cgeom : ℝ≥0∞) * volume (affine '' (Q.tube a i).carrier)
  ball : forall i, i ∈ O.outer -> (tubes i).carrier <= Metric.closedBall 0 1
  jacobian_pos : 0 < affineJacobian affine
  jacobian_finite : affineJacobian affine < (⊤ : ℝ≥0∞)
  mass_image : (∑ i ∈ O.outer, volume (tubes i).shade) =
    affineJacobian affine * ∑ i ∈ O.outer, volume (O.outerShade i).shade
  union_image : volume (⋃ i ∈ O.outer, (tubes i).shade) =
    affineJacobian affine * volume (⋃ i ∈ O.outer, (O.outerShade i).shade)
  multiplicity : ShadedBody.multiplicity O.outer (fun i => (tubes i).toShadedBody) =
    ShadedBody.multiplicity O.outer (fun i => (O.outerShade i).toShadedBody)
  fullness : ShadedBody.fullness O.outer (fun i => (O.outerShade i).toShadedBody) / Cgeom <=
    ShadedBody.fullness O.outer (fun i => (tubes i).toShadedBody)
  maximal_density : Kakeya.maxDensity O.outer (fun i => (tubes i).toConvexSpaceBody) <=
    (Cgeom : ℝ≥0∞) * Kakeya.maxDensity (Q.indexSet a)
      (fun i => (Q.tube a i).toConvexSpaceBody)

/-- This actual outer estimate treats a=0 by the fixed root cardinal bound.
For a>0 the genuine normalized outer family enters the generalized KT estimate. -/
theorem source_exists_eccentric_outer_estimate {beta : ℝ}
    (hbeta : 0 < beta) (hbeta1 : beta <= 1)
    (hKT : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) beta)
    (M : Nat) (hM : 2 <= M) (Cgeom : ℝ≥0) (hC : 1 <= Cgeom)
    (eps : ℝ) (heps : 0 < eps) :
    exists etaOuter : ℝ, 0 < etaOuter /\
      ∀ᶠ delta : ℝ≥0 in 𝓝[>] 0,
        forall {iota : Type u} (S : Finset iota)
          (T : iota -> Tube delta (EuclideanSpace ℝ (Fin 3)))
          (Q : SourceThreadedTower S T M sourceThreadConstant)
          (Z : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3))),
        SourceTowerGeometry Q sourceBottomED sourceLevelED ->
        forall (a : Nat) (L : ℝ≥0), a < M ->
        forall O : SourceEccentricOuterSplit Q Z a L,
        SourceEccentricOuterNormalization Q O Cgeom ->
        delta ^ etaOuter <= ShadedBody.fullness O.outer (fun i => (O.outerShade i).toShadedBody) ->
        ShadedBody.multiplicity O.outer (fun i => (O.outerShade i).toShadedBody) <=
          (delta : ℝ≥0∞) ^ (-eps) *
            Kakeya.maxDensity (Q.indexSet a) (fun i => (Q.tube a i).toConvexSpaceBody) ^
              (1 - beta) * (O.outer.card : ℝ≥0∞) ^ beta := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hC0 : 0 < Cgeom := zero_lt_one.trans_le hC
  obtain ⟨eta, heta, rho0, hrho0, hbound⟩ :=
    KatzTaoEstimate.exists_threshold_multiplicity_bound_univ hbeta.le hKT
      (eps / 4) (by positivity)
  let etaOuter := eta / (2 * (M : ℝ))
  have hetaOuter : 0 < etaOuter := by dsimp [etaOuter]; positivity
  have hcut : (0 : ℝ≥0) < rho0 ^ (M : ℝ) := by positivity
  refine ⟨etaOuter, hetaOuter, ?_⟩
  filter_upwards [source_eventually_fixed_tower_radius_conditions M hM (by norm_num : (0 : ℝ) < 1),
    Ioo_mem_nhdsGT (show (0 : ℝ≥0) < 1 / 2 by norm_num), Ioo_mem_nhdsGT hcut,
    Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg
      (K := (Cgeom : ℝ≥0∞)) ENNReal.coe_ne_top hetaOuter,
    Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg
      (K := (Cgeom : ℝ≥0∞) ^ (1 - beta)) (by finiteness) (by positivity : 0 < eps / 2),
    Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg
      (K := ((1280 : ℝ≥0∞) ^ 6) ^ (1 - beta)) (by finiteness) heps]
    with delta hd hdhalf hdcut hCfull hCcost hrootcost
  have hd0 := hd.2.2.1
  have hd1 : delta <= 1 := hdhalf.2.le.trans (by norm_num)
  have hd0E : (delta : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hd0.ne'
  have hCfull' : Cgeom <= delta ^ (-etaOuter) := by
    rw [← ENNReal.coe_rpow_of_ne_zero hd0.ne'] at hCfull
    exact ENNReal.coe_le_coe.mp hCfull
  have hsmall : delta ^ (1 / (M : ℝ)) <= rho0 := by
    have h := NNReal.rpow_le_rpow hdcut.2.le (by positivity : 0 <= 1 / (M : ℝ))
    rwa [← NNReal.rpow_mul, mul_one_div_cancel hMr.ne', NNReal.rpow_one] at h
  intro iota S T Q Z hgeom a L ha O Nrm hfull
  have hr0 : 0 < sourceTowerRadius delta M a := by
    have h := hd.2.2.2.2.1 a ha
    exact lt_of_lt_of_le (by positivity) h
  have hD1 : 1 <= Kakeya.maxDensity (Q.indexSet a)
      (fun i => (Q.tube a i).toConvexSpaceBody) := by
    refine Kakeya.one_le_maxDensity ⟨O.chosen, O.outer_subset O.chosen_mem, ?_⟩
    apply lt_of_lt_of_le _ (Tube.le_volume (Q.tube a O.chosen))
    have h := Tube.le_volume.c_pos (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
    positivity
  by_cases ha0 : a = 0
  · subst a
    have hroot : sourceTowerRadius delta M 0 = (1 / 40 : ℝ≥0) := by
      simp [sourceTowerRadius, show 0 < M by omega]
    have hcardReal : ((Q.indexSet 0).card : ℝ) <= (1280 : ℝ) ^ 6 := by
      have h := hgeom.coarse_card 0 ha
      norm_num [hroot] at h ⊢
      exact h
    have hcard : (O.outer.card : ℝ≥0∞) <= (1280 : ℝ≥0∞) ^ 6 := by
      have h := (show (O.outer.card : ℝ) <= (Q.indexSet 0).card by
        exact_mod_cast Finset.card_le_card O.outer_subset).trans hcardReal
      exact_mod_cast h
    calc ShadedBody.multiplicity O.outer (fun i => (O.outerShade i).toShadedBody) <=
          ((1280 : ℝ≥0∞) ^ 6) ^ (1 - beta) * (O.outer.card : ℝ≥0∞) ^ beta :=
            multiplicity_le_of_card_le hbeta1 hcard
      _ <= (delta : ℝ≥0∞) ^ (-eps) * (O.outer.card : ℝ≥0∞) ^ beta := by gcongr
      _ <= (delta : ℝ≥0∞) ^ (-eps) *
          Kakeya.maxDensity (Q.indexSet 0) (fun i => (Q.tube 0 i).toConvexSpaceBody) ^
            (1 - beta) * (O.outer.card : ℝ≥0∞) ^ beta := by
          have hpow : 1 <= Kakeya.maxDensity (Q.indexSet 0)
              (fun i => (Q.tube 0 i).toConvexSpaceBody) ^ (1 - beta) :=
            by simpa only [ENNReal.one_rpow] using
              ENNReal.rpow_le_rpow hD1 (sub_nonneg.mpr hbeta1)
          simpa only [mul_one] using mul_le_mul'
            (mul_le_mul' (le_refl ((delta : ℝ≥0∞) ^ (-eps))) hpow)
            (le_refl ((O.outer.card : ℝ≥0∞) ^ beta))
  · let rho := sourceTowerRadius delta M a / 8
    have hrho : 0 < rho := div_pos hr0 (by norm_num)
    have hrhou : rho <= delta ^ (1 / (M : ℝ)) := by
      have hpow : delta ^ ((a : ℝ) / (M : ℝ)) <= delta ^ (1 / (M : ℝ)) :=
        NNReal.rpow_le_rpow_of_exponent_ge hd0 hd1
          (div_le_div_of_nonneg_right (by exact_mod_cast (show 1 <= a by omega)) hMr.le)
      calc rho = ((1 / 40 : ℝ≥0) * delta ^ ((a : ℝ) / (M : ℝ))) / 8 := by
            simp [rho, sourceTowerRadius, ha]
        _ <= delta ^ ((a : ℝ) / (M : ℝ)) := by
            rw [div_le_iff₀ (show (0 : ℝ≥0) < 8 by norm_num)]
            nlinarith only [show (0 : ℝ≥0) <= delta ^ ((a : ℝ) / (M : ℝ)) from bot_le]
        _ <= delta ^ (1 / (M : ℝ)) := hpow
    have hrhol : delta ^ (2 : Nat) <= rho := by
      change delta ^ (2 : Nat) <= sourceTowerRadius delta M a / 8
      rw [le_div_iff₀ (show (0 : ℝ≥0) < 8 by norm_num)]
      have h := hd.2.2.2.2.1 a ha
      have hh := mul_le_mul_of_nonneg_left hdhalf.2.le delta.2
      nlinarith only [h, hh]
    have hfullN : rho ^ eta <= ShadedBody.fullness O.outer (fun i => (Nrm.tubes i).toShadedBody) := by
      apply le_trans _ Nrm.fullness
      rw [le_div_iff₀ hC0]
      calc rho ^ eta * Cgeom <= (delta ^ (1 / (M : ℝ))) ^ eta * delta ^ (-etaOuter) := by gcongr
        _ = delta ^ etaOuter := by
            rw [← NNReal.rpow_mul, ← NNReal.rpow_add hd0.ne']
            dsimp [etaOuter]
            congr 1; field_simp; ring
        _ <= ShadedBody.fullness O.outer (fun i => (O.outerShade i).toShadedBody) := hfull
    have hKTbound := hbound rho hrho (hrhou.trans hsmall) O.outer Nrm.tubes Nrm.ball hfullN
    have hrhocost : (rho : ℝ≥0∞) ^ (-(eps / 4)) <= (delta : ℝ≥0∞) ^ (-(eps / 2)) := by
      calc (rho : ℝ≥0∞) ^ (-(eps / 4)) <= ((delta : ℝ≥0∞) ^ (2 : Nat)) ^ (-(eps / 4)) :=
            by simpa only [ENNReal.coe_pow] using
              rpow_neg_le_rpow_neg_of_le hrhol (by linarith only [heps] : 0 <= eps / 4)
        _ = (delta : ℝ≥0∞) ^ (-(eps / 2)) := by
            rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
            congr 1; norm_num; ring
    rw [Nrm.multiplicity] at hKTbound
    calc ShadedBody.multiplicity O.outer (fun i => (O.outerShade i).toShadedBody) <=
          (rho : ℝ≥0∞) ^ (-(eps / 4)) *
            Kakeya.maxDensity O.outer (fun i => (Nrm.tubes i).toConvexSpaceBody) ^ (1 - beta) *
              (O.outer.card : ℝ≥0∞) ^ beta := hKTbound
      _ <= (delta : ℝ≥0∞) ^ (-(eps / 2)) *
          ((Cgeom : ℝ≥0∞) * Kakeya.maxDensity (Q.indexSet a)
            (fun i => (Q.tube a i).toConvexSpaceBody)) ^ (1 - beta) * (O.outer.card : ℝ≥0∞) ^ beta := by
          gcongr
          exact Nrm.maximal_density
      _ = ((delta : ℝ≥0∞) ^ (-(eps / 2)) * (Cgeom : ℝ≥0∞) ^ (1 - beta)) *
          Kakeya.maxDensity (Q.indexSet a) (fun i => (Q.tube a i).toConvexSpaceBody) ^ (1 - beta) *
            (O.outer.card : ℝ≥0∞) ^ beta := by rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith only [hbeta1])]; ac_rfl
      _ <= ((delta : ℝ≥0∞) ^ (-(eps / 2)) * (delta : ℝ≥0∞) ^ (-(eps / 2))) *
          Kakeya.maxDensity (Q.indexSet a) (fun i => (Q.tube a i).toConvexSpaceBody) ^ (1 - beta) *
            (O.outer.card : ℝ≥0∞) ^ beta := by gcongr
      _ = (delta : ℝ≥0∞) ^ (-eps) *
          Kakeya.maxDensity (Q.indexSet a) (fun i => (Q.tube a i).toConvexSpaceBody) ^ (1 - beta) *
            (O.outer.card : ℝ≥0∞) ^ beta := by
          rw [← ENNReal.rpow_add _ _ hd0E ENNReal.coe_ne_top]
          congr 3; ring

end Kakeya.ML2Core

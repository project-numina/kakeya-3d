/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceRetainedTerminalBridges
public import Kakeya.DimensionThree.Plank.Prop66BClose

/-!
# Retained four-factor data and the plank application

`SourceRetainedFourFactors` records the corrected four factors with the actual
factor-shading construction; `source_retained_fourFactor_ledger` multiplies them into the
multiplicity bound `loss * 16^beta * delta^(g - f - pCharge - c) * card^beta`.
`SourceRetainedMiddleAnalysis` bundles a same-seam VNS construction (all-radius input, R4 output,
downstairs count, Lemma91At). `SourceRetainedPlankApplication` and
`SourceRetainedPlankNormalization` collect the non-analytic premises of the proved GWZ 6.6(B),
and `source_exists_retained_plank_application_accuracy` applies
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` to them.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

open ML2Assembly ML2Reduction VeryNotSticky

universe u

variable {iota : Type u} {delta : ℝ≥0} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace ℝ (Fin 3))} {M C : Nat}

/-- The corrected four factors retain the actual factor-shading construction.
The old protected SourceZeroFourFactors is a different conditional object. -/
structure SourceRetainedFourFactors (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3)))
    (a p b : Nat) (beta fineCharge parentCharge outerCharge middleGain : ℝ)
    (loss : ℝ≥0∞) where
  lambda : ℝ≥0
  seam : SourceQMiddleSeam Q Z a p b lambda loss
  three : SourceQThreeFactorBounds Q seam beta fineCharge parentCharge outerCharge
  middle : ShadedBody.multiplicity seam.middle (fun i => (seam.middleShade i).toShadedBody) <=
    (delta : ℝ≥0∞) ^ middleGain * (seam.middle.card : ℝ≥0∞) ^ beta

/-- A same-seam VNS construction includes the real all-radius input, R4 output,
downstairs count and literal Lemma91At. These are produced together. -/
structure SourceRetainedMiddleAnalysis (Q : SourceThreadedTower S T M C)
    {Z : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3))}
    {a p b : Nat} {lambda : ℝ≥0} {loss : ℝ≥0∞}
    (X : SourceQMiddleSeam Q Z a p b lambda loss)
    (beta varpi zeta v etaD nuMid e : ℝ) where
  rho : ℝ≥0
  R : ℝ
  etaC : ℝ
  q : ℝ
  gamma : ℝ
  R_pos : 0 < R
  rho_pos : 0 < rho
  rho_le_one : rho <= 1
  q_pos : 0 < q
  gamma_pos : 0 < gamma
  gamma_le_q : gamma <= q
  density_budget : 3 * q <= etaD
  gain_budget : nuMid + 3 * q <= v
  scale_gain : (rho : ℝ) <= (delta : ℝ) ^ (e / 2)
  cover_parameters : SourceQCoverParameters M sourceBottomED sourceLevelED C e varpi zeta etaC R
  cover_input : SourceQCoverInput Q a p b X.jp X.middle X.middleShade rho e zeta etaC
  situation : Tube.IsRescalingSituation (sourceTowerRadius delta M p)
    (sourceTowerRadius delta M b) rho R 3
  normalized : SourceQNormalizedRows situation R_pos (Q.tube p X.jp) X.middle X.middleShade
  D : Finset iota
  E : Finset iota
  U0 : iota -> ShadedTube rho (EuclideanSpace ℝ (Fin 3))
  U1 : iota -> ShadedTube rho (EuclideanSpace ℝ (Fin 3))
  retention : SourceMiddleActualRetention situation R_pos (Q.tube p X.jp)
    (varpi * zeta / 16) q gamma gamma gamma etaD varpi zeta X.middle D E X.middleShade U0 U1
  downstairs : SourceMiddleDownstairsCount situation R_pos (Q.tube p X.jp) varpi zeta E X.middleShade
  raw_vns : Lemma91At.{u} beta varpi zeta v etaD rho
  uniformity_budget : ((ShadedTube.ssfUniformConst 3 : ℝ≥0) : ℝ≥0∞) <=
    (rho : ℝ≥0∞) ^ (-etaD)

/-- Every non-analytic premise of the proved GWZ 6.6(B), on actual finite
normalized tubes. The branching floor and volumetric ED are not source-line ED. -/
structure SourceRetainedPlankApplication (n : Nat) (sigma : ℝ≥0) (eta eps2 : ℝ) where
  family : Finset (Fin n)
  tubes : Fin n -> ShadedTube sigma (EuclideanSpace ℝ (Fin 3))
  sigma_pos : 0 < sigma
  family_nonempty : family.Nonempty
  centred : forall i, i ∈ family -> (tubes i).carrier <= Metric.closedBall 0 1
  essentially_distinct : (family : Set (Fin n)).Pairwise
    (fun i j => _root_.IsEssentiallyDistinct (tubes i).carrier (tubes j).carrier)
  Cu : ℝ≥0
  uniformity : ShadedTube.ShadedUniformTubeSet family tubes (Tube.ssfGridLen sigma) Cu
  Cu_budget : Cu <= sigma ^ (-eta)
  fullness : sigma ^ eta <= ShadedBody.fullness family (fun i => (tubes i).toShadedBody)
  rho : ℝ≥0
  short : ℝ≥0
  middle : ℝ≥0
  Cw : ℝ≥0
  Cpar : ℝ≥0
  Czero : ℝ≥0
  short_le_middle : short <= middle
  middle_le_one : middle <= 1
  width_budget : Cw <= sigma ^ (-eta)
  parent_budget : Cpar <= sigma ^ (-eta)
  factor_budget : Czero <= sigma ^ (-eta)
  coarse_lower : sigma ^ (1 - eps2) <= rho
  rho_le_short : rho <= short
  parents : Tube.IsUniformAtScale family (fun i => (tubes i).toTube) rho Cpar
  branching_floor : (max 1 Cpar) ^ 2 <= parents.branchingN
  parent_centred : forall j, j ∈ parents.parent ->
    (parents.parentTube j).carrier <= Metric.closedBall 0 1
  factors : Kakeya.GlobalPlankFactorization Cw short middle short_le_middle middle_le_one
    parents.parent (fun j => (parents.parentTube j).toConvexSpaceBody) Czero

/-- A conditional good-branch normalization records original tags, affine shade
images and the complete leaves before paid ED/SSF extraction. The dimensions are
compared through an explicit constant; equality with a John axis is absent. -/
structure SourceRetainedPlankNormalization (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3)))
    {a m : Nat} {etaParent bias : ℝ} {D aw bw cw : ℝ≥0}
    (E : SourceZeroEccentricFactors Q Z a m etaParent bias D aw bw cw)
    (eta eps2 : ℝ) (sigma0 : ℝ≥0) (comparison : ℝ≥0) where
  coarse : iota
  coarse_mem : coarse ∈ Q.indexSet a
  selectedNodes : Finset iota
  selectedParts : Finset (Finset iota)
  parts_subset : selectedParts <= (E.factor coarse coarse_mem).parts
  nodes_eq : selectedNodes = selectedParts.sup id
  completeLeaves : Finset iota
  complete_leaves_eq : completeLeaves = S.filter (fun i => Q.place m i ∈ selectedNodes)
  leaves : Finset iota
  leaves_subset : leaves <= completeLeaves
  leaves_nonempty : leaves.Nonempty
  leaves_in_cell : leaves <= Q.cell a coarse
  n : Nat
  enumerate : Fin n ≃ {i // i ∈ leaves}
  sigma : ℝ≥0
  application : SourceRetainedPlankApplication n sigma eta eps2
  sigma_small : sigma <= sigma0
  all_fine : application.family = Finset.univ
  affine : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)
  fineShade : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3))
  fine_tubes : forall i, (fineShade i).toTube = T i
  fine_subshade : forall i, (fineShade i).shade <= (Z i).shade
  extractionLoss : ℝ≥0
  extraction_loss_one : 1 <= extractionLoss
  fine_refinement : ShadedBody.IsCRefinement leaves (fun i => (fineShade i).toShadedBody)
    completeLeaves (fun i => (Z i).toShadedBody) extractionLoss⁻¹
  shade_images : forall j, (application.tubes j).shade = affine '' (fineShade (enumerate j)).shade
  carrier_images : forall j, affine '' (T (enumerate j)).carrier <= (application.tubes j).carrier
  jacobian_positive : 0 < affineJacobian affine
  jacobian_finite : affineJacobian affine < (⊤ : ℝ≥0∞)
  mass_image : (∑ j ∈ application.family, volume (application.tubes j).shade) =
    affineJacobian affine * ∑ i ∈ leaves, volume (fineShade i).shade
  union_image : volume (⋃ j ∈ application.family, (application.tubes j).shade) =
    affineJacobian affine * volume (⋃ i ∈ leaves, (fineShade i).shade)
  parent_origin : Fin n -> iota
  parent_origin_mem : forall j, j ∈ application.parents.parent -> parent_origin j ∈ selectedNodes
  parent_factor_origin : forall part, part ∈ application.factors.parts ->
    exists originalPart, originalPart ∈ selectedParts /\
      forall j, j ∈ part -> parent_origin j ∈ originalPart
  source_parent_containment : forall j, j ∈ application.parents.parent ->
    affine '' (Q.tube m (parent_origin j)).carrier <= (application.parents.parentTube j).carrier
  comparison_one : 1 <= comparison
  scale_lower : delta / (comparison * sourceTowerRadius delta M a) <= sigma
  scale_upper : sigma <= comparison * delta / sourceTowerRadius delta M a
  aspect_comparison : application.short / application.middle <= comparison * (aw / bw)

theorem source_retained_fourFactor_ledger (Q : SourceThreadedTower S T M C)
    {Z : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3))}
    {a p b : Nat} {beta f pCharge c g : ℝ} {loss : ℝ≥0∞}
    (hdelta : 0 < delta) (hbeta : 0 <= beta)
    (F : SourceRetainedFourFactors Q Z a p b beta f pCharge c g loss) :
    ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <=
      loss * (16 : ℝ≥0∞) ^ beta * (delta : ℝ≥0∞) ^ (g - f - pCharge - c) *
        (S.card : ℝ≥0∞) ^ beta := by
  have hd0 : (delta : ℝ≥0∞) ≠ 0 := by exact_mod_cast hdelta.ne'
  have hdt : (delta : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  calc
    ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <=
        loss * ShadedBody.multiplicity (Q.cell b F.seam.jb)
          (fun i => (F.seam.fineShade i).toShadedBody) *
          ShadedBody.multiplicity F.seam.middle (fun i => (F.seam.middleShade i).toShadedBody) *
          ShadedBody.multiplicity F.seam.parents (fun i => (F.seam.parentShade i).toShadedBody) *
          ShadedBody.multiplicity F.seam.coarse (fun i => (F.seam.outerShade i).toShadedBody) :=
      F.seam.split
    _ <= loss * ((delta : ℝ≥0∞) ^ (-f) * ((Q.cell b F.seam.jb).card : ℝ≥0∞) ^ beta) *
          ((delta : ℝ≥0∞) ^ g * (F.seam.middle.card : ℝ≥0∞) ^ beta) *
          ((delta : ℝ≥0∞) ^ (-pCharge) * (F.seam.parents.card : ℝ≥0∞) ^ beta) *
          ((delta : ℝ≥0∞) ^ (-c) * (F.seam.coarse.card : ℝ≥0∞) ^ beta) :=
      mul_le_mul' (mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl F.three.fine)
        F.middle) F.three.parent) F.three.outer
    _ = loss * (delta : ℝ≥0∞) ^ (g - f - pCharge - c) *
          (((Q.cell b F.seam.jb).card : ℝ≥0∞) * F.seam.middle.card *
            F.seam.parents.card * F.seam.coarse.card) ^ beta := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hbeta, ENNReal.mul_rpow_of_nonneg _ _ hbeta,
        ENNReal.mul_rpow_of_nonneg _ _ hbeta]
      rw [show g - f - pCharge - c = ((-f + g) + -pCharge) + -c by ring]
      rw [ENNReal.rpow_add _ _ hd0 hdt, ENNReal.rpow_add _ _ hd0 hdt,
        ENNReal.rpow_add _ _ hd0 hdt]
      ring
    _ <= loss * (delta : ℝ≥0∞) ^ (g - f - pCharge - c) *
          (16 * (S.card : ℝ≥0∞)) ^ beta :=
      mul_le_mul' le_rfl (ENNReal.rpow_le_rpow F.seam.card_product hbeta)
    _ = loss * (16 : ℝ≥0∞) ^ beta * (delta : ℝ≥0∞) ^ (g - f - pCharge - c) *
          (S.card : ℝ≥0∞) ^ beta := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hbeta]
      ring

end Kakeya.ML2Core

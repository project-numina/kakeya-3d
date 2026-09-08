/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFourFactorRowsSite
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceMiddleCalibration
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceNormalizedRetention
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineMiddleProducer

/-!
# Calling the middle producer on the mediant-chosen fibre

Runs the R4 middle producer on the level-`p` node `jp` supplied by the mediant seam.
`Kakeya.ML2Assembly.sourceMiddleLeaf`, `sourceMiddleFibre` and `sourceMiddleFullness` name
the retained leaves, the `(p, b)` fibre and the two-fold-loss fullness on a `UniformTubeSet`.
`SourceMiddleOriginalInput` collects the C0 mediant and the C2 scalar rows, and
`sourceMiddle_original_rows` derives the `SourceMiddleOriginalRows` antecedents (ancestor,
fibre, count and normalized density/fullness). `SourceMiddleActualRetention` records all
retention projections, and `sourceMiddle_exists_actual_retention` obtains it by one
application of the R4 producer `exists_normalizedRetention` from
`SpineSourceNormalizedRetention` to the chosen `jp`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Kakeya.ML2Core Kakeya.ML2Reduction Kakeya.VeryNotSticky

namespace Kakeya.ML2Assembly

universe u

section Runtime

variable {iota : Type u} {delta Cu : ℝ≥0} {u : Finset iota}
  {T : iota -> ShadedTube delta (EuclideanSpace ℝ (Fin 3))}
  (U : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen delta) Cu)

open Classical in
noncomputable def sourceMiddleLeaf (t1 : Finset iota) (b : Nat) : Finset iota :=
  {i ∈ u | U.cover.assign b i ∈ t1}

open Classical in
noncomputable def sourceMiddleFibre (t1 tTau : Finset iota) (p b : Nat) (jp : iota) :
    Finset iota := {j ∈ tTau | coarseNode (retainedLeafChain U t1 b) p b j = jp}

noncomputable def sourceMiddleFullness (t1 tTau : Finset iota) (b : Nat)
    (shift : EuclideanSpace ℝ (Fin 3)) : ℝ≥0 :=
  (spineScaleLoss 3 (sourceMiddleLeaf U t1 b).card delta *
      spineScaleLoss 3 tTau.card (Tube.gridScale delta (Tube.ssfGridLen delta) b))⁻¹ *
    ShadedBody.fullness (sourceMiddleLeaf U t1 b) (fun i => ((T i).translate shift).toShadedBody)

/-- C0 supplies this jp; C2 supplies only its scalar rows. No normalized row is assumed. -/
structure SourceMiddleOriginalInput (t1 tTau : Finset iota) (a p b m N : Nat)
    (shift : EuclideanSpace ℝ (Fin 3))
    (Z : iota -> ShadedTube (Tube.gridScale delta (Tube.ssfGridLen delta) b)
      (EuclideanSpace ℝ (Fin 3))) (jp : iota)
    {rho : ℝ≥0} {R : ℝ}
    (hsit : Tube.IsRescalingSituation (Tube.gridScale delta (Tube.ssfGridLen delta) p)
      (Tube.gridScale delta (Tube.ssfGridLen delta) b) rho R 3) (hR : 0 < R)
    (e q gamma etaD : ℝ) (K0 : Nat) (Cstar : ℝ≥0∞) (rung : Nat -> ℝ) : Prop where
  delta_pos : 0 < delta
  delta_le_one : delta <= 1
  ancestor_le_parent : a <= p
  parent_le_middle : p <= b
  middle_le_grid : b <= Tube.ssfGridLen delta
  middle_subset : tTau ⊆ activeNodes (retainedLeafChain U t1 b) b
  parent_active : jp ∈ activeNodes (retainedLeafChain U t1 b) p
  original_tubes : forall j,
    (Z j).toTube = ((retainedLeafChain U t1 b).tube b j).translate shift
  window : IsKatzTaoDividingWindow U Cstar rung e N a b m
  mediant_positive : 0 < sourceMiddleFullness U t1 tTau b shift
  mediant : sourceMiddleFullness U t1 tTau b shift <=
    ShadedBody.fullness (sourceMiddleFibre U t1 tTau p b jp) (fun i => (Z i).toShadedBody)
  rho_eq : rho = midScale delta (Tube.ssfGridLen delta) p b
  rho_pos : 0 < rho
  rho_le_one : rho <= 1
  div_pos : 0 < e
  scale_lower : 20 * delta <= rho
  scale_upper : (rho : ℝ) <= (delta : ℝ) ^ (e / 2) / 2
  card_power : 4 <= e * (K0 : ℝ) / 2
  ambient_card : (u.card : ℝ) <= (delta : ℝ) ^ (-(4 : ℝ))
  radius_ge_one : 1 <= R
  scale_ratio : (Tube.gridScale delta (Tube.ssfGridLen delta) b : ℝ) /
      (Tube.gridScale delta (Tube.ssfGridLen delta) p : ℝ) <= 4 * (rho : ℝ)
  fullness_scalar : rho ^ gamma <=
    (outerLoss R)⁻¹ * sourceMiddleFullness U t1 tTau b shift
  normalized_density_scalar : (outerLoss R : ℝ≥0∞) *
      (Cstar * ENNReal.ofReal
        (((Tube.gridScale delta (Tube.ssfGridLen delta) a : ℝ) /
          (Tube.gridScale delta (Tube.ssfGridLen delta) b : ℝ)) ^ rung m)) <=
    (rho : ℝ≥0∞) ^ (-q)
  original_density_scalar : Cstar * ENNReal.ofReal
      (((Tube.gridScale delta (Tube.ssfGridLen delta) a : ℝ) /
        (Tube.gridScale delta (Tube.ssfGridLen delta) b : ℝ)) ^ rung m) <=
    (rho : ℝ≥0∞) ^ (-(etaD - q))

/-- Actual ancestor, fibre and indexed normalization identities, all on the chosen jp. -/
structure SourceMiddleOriginalRows (t1 tTau : Finset iota) (a p b : Nat)
    (shift : EuclideanSpace ℝ (Fin 3))
    (Z : iota -> ShadedTube (Tube.gridScale delta (Tube.ssfGridLen delta) b)
      (EuclideanSpace ℝ (Fin 3))) (jp : iota)
    {rho : ℝ≥0} {R : ℝ}
    (hsit : Tube.IsRescalingSituation (Tube.gridScale delta (Tube.ssfGridLen delta) p)
      (Tube.gridScale delta (Tube.ssfGridLen delta) b) rho R 3) (hR : 0 < R)
    (q gamma etaD : ℝ) (K0 : Nat) : Prop where
  ancestor_mem : coarseNode (retainedLeafChain U t1 b) a p jp ∈ U.cover.indexSet a
  ancestor_contains : (U.cover.tube p jp).toConvexSpaceBody <=
    (U.cover.tube a (coarseNode (retainedLeafChain U t1 b) a p jp)).toConvexSpaceBody
  fibre_under_ancestor : sourceMiddleFibre U t1 tTau p b jp ⊆
    U.nodesUnder b a (coarseNode (retainedLeafChain U t1 b) a p jp)
  nonempty : (sourceMiddleFibre U t1 tTau p b jp).Nonempty
  contained : forall i, i ∈ sourceMiddleFibre U t1 tTau p b jp ->
    (Z i).carrier ⊆ (((retainedLeafChain U t1 b).tube p jp).translate shift).carrier
  card_leaf : (sourceMiddleFibre U t1 tTau p b jp).card <= (sourceMiddleLeaf U t1 b).card
  leaf_card : (sourceMiddleLeaf U t1 b).card <= u.card
  card_power : ((sourceMiddleFibre U t1 tTau p b jp).card : ℝ) <=
    (rho : ℝ) ^ (-(K0 : ℝ))
  original_density : Kakeya.maxDensity (sourceMiddleFibre U t1 tTau p b jp)
      (fun i => (Z i).toConvexSpaceBody) <= (rho : ℝ≥0∞) ^ (-(etaD - q))
  normalized_density : Kakeya.maxDensity (sourceMiddleFibre U t1 tTau p b jp)
      (fun i => (outerFamily hsit.pos_ambient
        (((retainedLeafChain U t1 b).tube p jp).translate shift) hR rho Z i).toConvexSpaceBody) <=
    (rho : ℝ≥0∞) ^ (-q)
  normalized_fullness : (rho : ℝ≥0∞) ^ gamma <=
    ShadedBody.fullness (sourceMiddleFibre U t1 tTau p b jp)
      (fun i => (outerFamily hsit.pos_ambient
        (((retainedLeafChain U t1 b).tube p jp).translate shift) hR rho Z i).toShadedBody)
  normalized_shade : forall i, i ∈ sourceMiddleFibre U t1 tTau p b jp ->
    (outerFamily hsit.pos_ambient (((retainedLeafChain U t1 b).tube p jp).translate shift)
      hR rho Z i).shade =
      spineRescaleUnit hsit.pos_ambient (((retainedLeafChain U t1 b).tube p jp).translate shift)
        hR '' (Z i).shade
  normalized_multiplicity : ShadedBody.multiplicity (sourceMiddleFibre U t1 tTau p b jp)
      (fun i => (outerFamily hsit.pos_ambient
        (((retainedLeafChain U t1 b).tube p jp).translate shift) hR rho Z i).toShadedBody) =
    ShadedBody.multiplicity (sourceMiddleFibre U t1 tTau p b jp) (fun i => (Z i).toShadedBody)
  normalized_map :
    (spineRescaleUnit hsit.pos_ambient
      (((retainedLeafChain U t1 b).tube p jp).translate shift) hR).toAffineMap =
      (((retainedLeafChain U t1 b).tube p jp).translate shift).rescaleMap R
  jacobian_value : Kakeya.affineJacobian (spineRescaleUnit hsit.pos_ambient
      (((retainedLeafChain U t1 b).tube p jp).translate shift) hR) =
    ENNReal.ofReal ((4 * R)⁻¹ ^ (3 : Nat)) *
      (Tube.gridScale delta (Tube.ssfGridLen delta) p : ℝ≥0∞)⁻¹ ^ (2 : Nat)
  jacobian_pos : 0 < Kakeya.affineJacobian (spineRescaleUnit hsit.pos_ambient
    (((retainedLeafChain U t1 b).tube p jp).translate shift) hR)
  jacobian_finite : Kakeya.affineJacobian (spineRescaleUnit hsit.pos_ambient
    (((retainedLeafChain U t1 b).tube p jp).translate shift) hR) < (⊤ : ℝ≥0∞)
  normalized_mass : forall I : Finset iota, I ⊆ sourceMiddleFibre U t1 tTau p b jp ->
    (∑ i ∈ I, volume (outerFamily hsit.pos_ambient
      (((retainedLeafChain U t1 b).tube p jp).translate shift) hR rho Z i).shade) =
      Kakeya.affineJacobian (spineRescaleUnit hsit.pos_ambient
        (((retainedLeafChain U t1 b).tube p jp).translate shift) hR) *
        ∑ i ∈ I, volume (Z i).shade
  normalized_union : forall I : Finset iota, I ⊆ sourceMiddleFibre U t1 tTau p b jp ->
    volume (⋃ i ∈ I, (outerFamily hsit.pos_ambient
      (((retainedLeafChain U t1 b).tube p jp).translate shift) hR rho Z i).shade) =
      Kakeya.affineJacobian (spineRescaleUnit hsit.pos_ambient
        (((retainedLeafChain U t1 b).tube p jp).translate shift) hR) *
        volume (⋃ i ∈ I, (Z i).shade)

end Runtime

/-- All retention projections on the one E/U1 returned by the verified R4 producer. -/
structure SourceMiddleActualRetention {b deltaTube rho : ℝ≥0} {R : ℝ}
    (hsit : Tube.IsRescalingSituation b deltaTube rho R 3) (hR : 0 < R)
    (T0 : Tube b (EuclideanSpace ℝ (Fin 3))) (A q gamma alpha alphaPrime etaD varpi zeta : ℝ)
    {iota : Type u} (F D E : Finset iota)
    (Z : iota -> ShadedTube deltaTube (EuclideanSpace ℝ (Fin 3)))
    (U0 U1 : iota -> ShadedTube rho (EuclideanSpace ℝ (Fin 3))) : Prop where
  paid : SourcePaidRetentionData hsit hR T0 A q gamma alpha alphaPrime F D E Z U0 U1
  count : CountTransport hsit hR T0 0 varpi zeta E Z U1
  subset : E ⊆ F
  nonempty : E.Nonempty
  cardinality_retained : (rho : ℝ) ^ A * (F.card : ℝ) <= (E.card : ℝ)
  cardinality_upper : E.card <= F.card
  mass_retained : (∑ i ∈ F, volume (outerFamily hsit.pos_ambient T0 hR rho Z i).shade) / 512 <=
    (rho : ℝ≥0∞) ^ (-(3 * q)) * ∑ i ∈ E, volume (U1 i).shade
  original_fullness : (rho : ℝ≥0∞) ^ gamma <=
    ShadedBody.fullness F (fun i => (outerFamily hsit.pos_ambient T0 hR rho Z i).toShadedBody)
  original_density : Kakeya.maxDensity F (fun i => (Z i).toConvexSpaceBody) <=
    (rho : ℝ≥0∞) ^ (-(etaD - q))
  retained_fullness : (rho : ℝ≥0∞) ^ (3 * q) <=
    ShadedBody.fullness E (fun i => (U1 i).toShadedBody)
  vns_fullness : (rho : ℝ≥0∞) ^ etaD <= ShadedBody.fullness E (fun i => (U1 i).toShadedBody)
  retained_density : Kakeya.maxDensity E (fun i => (U1 i).toConvexSpaceBody) <=
    (rho : ℝ≥0∞) ^ (-(2 * q))
  uniform : Nonempty (ShadedTube.ShadedUniformTubeSet E U1 (Tube.ssfGridLen rho)
    (ShadedTube.ssfUniformConst 3))
  normalized_multiplicity :
    ShadedBody.multiplicity F (fun i => (outerFamily hsit.pos_ambient T0 hR rho Z i).toShadedBody) =
      ShadedBody.multiplicity F (fun i => (Z i).toShadedBody)
  multiplicity_retained : ShadedBody.multiplicity F (fun i => (Z i).toShadedBody) <=
    (rho : ℝ≥0∞) ^ (-(3 * q)) * ShadedBody.multiplicity E (fun i => (U1 i).toShadedBody)

end Kakeya.ML2Assembly

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Setup
public import Kakeya.DimensionThree.MainLemma1.ScalarFactorization
public import Kakeya.DimensionThree.MainLemma1.WZCanonicalClasses
public import Kakeya.Factoring.DilatedTubePresentation
public import Kakeya.Factoring.WeightedFullness
public import Kakeya.DimensionThree.MainLemma1.Factoring

/-!
  The packet boundary used by the endpoint WZ consumers.  It deliberately has
  no dependency on the legacy `WeakCoarseFibre` file: a downstream producer
  can fill these fields from its hierarchy witness, while an upstream module
  can import this declaration without importing `CaseTwo`.

  `source` is the one fibre on which the WZ estimate is run.  `ambient` is the
  complete parent-family carrier.  `parent_constant` records that the chosen
  parent map is constant on the ambient carrier, which is the exact condition
  needed to turn hierarchy containment into the single-parent tube input of
  the no-ED middle consumer.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology Tube

namespace Kakeya.ml1Boot.W48EndpointModuleSafe

noncomputable section
set_option maxHeartbeats 12000000

universe u v w

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

structure EndpointHierarchySelectedPacket
    {iota : Type u} [DecidableEq iota]
    {kappa : Type w} [DecidableEq kappa]
    {delta tau rho : ℝ≥0}
    (source ambient : Finset iota)
    (Ttau : iota -> ShadedTube tau E)
    (parentSet : Finset kappa)
    (Trho : kappa -> Tube rho E)
    (pMap : iota -> kappa) (parent : kappa)
    (zFr zQ etaIn : ℝ) (CFr CQ : ℝ≥0) where
  source_nonempty : source.Nonempty
  source_subset : source ⊆ ambient
  parent_mem : parent ∈ parentSet
  parent_family :
    IsParentFamily source (fun i => (Ttau i).toTube)
      parentSet Trho pMap
  parent_constant : ∀ i ∈ ambient, pMap i = parent
  ambient_containment : ∀ i ∈ ambient,
    (Ttau i).carrier ⊆ (Trho parent).carrier
  source_eq_fibre : source = fibre ambient pMap parent
  fullness_pos :
    0 < fullness source (fun i => (Ttau i).toShadedBody)
  fullness_lower :
    (delta : ℝ≥0∞) ^ etaIn <=
      (fullness source (fun i => (Ttau i).toShadedBody) : ℝ≥0∞)
  source_frostman :
    frostmanConstIn source
        (fun i => (Ttau i).toConvexSpaceBody)
        (Trho parent).toConvexSpaceBody <=
      (CFr : ℝ≥0∞) * (delta : ℝ≥0∞) ^ (-zFr)
  q_lower :
    (CQ : ℝ≥0∞)⁻¹ * (delta : ℝ≥0∞) ^ zQ <=
      (((tau / rho : ℝ≥0) : ℝ≥0∞) ^ (2 : Nat)) *
        (source.card : ℝ≥0∞)
  q_upper :
    (((tau / rho : ℝ≥0) : ℝ≥0∞) ^ (2 : Nat)) *
        (source.card : ℝ≥0∞) <=
      (CQ : ℝ≥0∞) * (delta : ℝ≥0∞) ^ (-zQ)

/- The parent family and the explicit ambient containment are both retained:
   the former is used by coarse assembly, the latter by the WZ middle call. -/
theorem EndpointHierarchySelectedPacket.parent_containment
    {iota : Type u} [DecidableEq iota]
    {kappa : Type w} [DecidableEq kappa]
    {delta tau rho : ℝ≥0}
    {source ambient : Finset iota}
    {Ttau : iota -> ShadedTube tau E}
    {parentSet : Finset kappa} {Trho : kappa -> Tube rho E}
    {pMap : iota -> kappa} {parent : kappa}
    {zFr zQ etaIn : ℝ} {CFr CQ : ℝ≥0}
    (P : EndpointHierarchySelectedPacket (delta := delta) source ambient Ttau parentSet Trho
      pMap parent zFr zQ etaIn CFr CQ) :
    ∀ i ∈ source,
      (Ttau i).toConvexSpaceBody <= (Trho (pMap i)).toConvexSpaceBody := by
  intro i hi
  apply (SetLike.coe_subset_coe (A := ConvexSpaceBody E)
    (S := (Ttau i).toConvexSpaceBody)
    (T := (Trho (pMap i)).toConvexSpaceBody)).mpr
  have hparent := P.parent_constant i (P.source_subset hi)
  rw [hparent]
  change (Ttau i).carrier ⊆ (Trho parent).carrier
  exact P.ambient_containment i (P.source_subset hi)

/- This is the exact tuple consumed by the split-universe WZ interface.  It
   exposes every source/Frostman/Q field, rather than hiding one in an
   existential callback. -/

/- A constructor-facing producer interface.  The producer is an eventual
   packet witness, not a hidden analytic premise; all quantitative fields are
   visible in the returned packet. -/

end
end Kakeya.ml1Boot.W48EndpointModuleSafe

end

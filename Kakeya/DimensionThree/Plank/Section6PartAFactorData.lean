/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Section6FactorInterface
public import Kakeya.DimensionThree.Plank.ComparableBodyFactorization
public import Kakeya.DimensionThree.Plank.TubeParentPacking

/-!
# Proposition 6.6(A): inputs for the corrected Proposition 5.1

The local factorisation has one `ComparableBodyFactorization` for each occupied coarse parent.
This file forms their dependent sum and records, explicitly, the representative-plank geometry
which is not a conclusion of Proposition 5.1.  In particular, the common-scale hypothesis is not
manufactured: only a common upper scale is required, and Proposition 5.1 selects a dyadic scale.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Convexity ConvexSpaceBody
open scoped ENNReal NNReal Classical

noncomputable section

namespace Kakeya

universe u_section6PartA

/-- A parent together with the proof that it is used by the external parent system. -/
abbrev Section6PartAParent {ι : Type*} {q : Finset ι} {δ ρ : ℝ≥0}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {Cpar : ℝ≥0}
    (PS : ExternalParentSystem q (fun i ↦ (T i).toTube) ρ Cpar) :=
  {k : PS.Parent // k ∈ PS.parents}

/-- A parentwise factorization reindexed by the subtype of occupied parents. -/
abbrev Section6PartAFactorization {ι : Type*} {q : Finset ι} {δ ρ b : ℝ≥0}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {Cpar C₀ : ℝ≥0}
    (PS : ExternalParentSystem q (fun i ↦ (T i).toTube) ρ Cpar)
    (Fz : ∀ k ∈ PS.parents, ComparableBodyFactorization b
      {i ∈ q | PS.assign i = k} (fun i ↦ (T i).toConvexSpaceBody) C₀)
    (k : Section6PartAParent PS) := Fz k.1 k.2

/-- The dependent sum of the cells supplied over the occupied coarse parents. -/
abbrev Section6PartACell {ι : Type*} {q : Finset ι} {δ ρ b : ℝ≥0}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {Cpar C₀ : ℝ≥0}
    (PS : ExternalParentSystem q (fun i ↦ (T i).toTube) ρ Cpar)
    (Fz : ∀ k ∈ PS.parents, ComparableBodyFactorization b
      {i ∈ q | PS.assign i = k} (fun i ↦ (T i).toConvexSpaceBody) C₀) :=
  Σ k : Section6PartAParent PS, (Section6PartAFactorization PS Fz k).Cell

section DependentSum

variable {ι : Type u_section6PartA} {q : Finset ι} {δ ρ b : ℝ≥0}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {Cpar C₀ : ℝ≥0}
  (PS : ExternalParentSystem q (fun i ↦ (T i).toTube) ρ Cpar)
  (Fz : ∀ k ∈ PS.parents, ComparableBodyFactorization b
    {i ∈ q | PS.assign i = k} (fun i ↦ (T i).toConvexSpaceBody) C₀)
  (hq : q.Nonempty)

/-- Total parent assignment used by the dependent-sum construction.  Outside `q` it uses the
parent of one fixed member; all factor-family obligations concern indices in `q`. -/
noncomputable def section6PartAParentOf (i : ι) : Section6PartAParent PS :=
  if hi : i ∈ q then ⟨PS.assign i, PS.assign_mem i hi⟩
  else ⟨PS.assign hq.choose, PS.assign_mem hq.choose hq.choose_spec⟩

/-- Cell assignment into the dependent sum of the parentwise factorizations. -/
noncomputable def section6PartACellOf (i : ι) : Section6PartACell PS Fz :=
  let k := section6PartAParentOf PS hq i
  ⟨k, (Section6PartAFactorization PS Fz k).cellOf i⟩

/-- Finite set of all cells in all used parentwise factorizations. -/
noncomputable def section6PartACells : Finset (Section6PartACell PS Fz) :=
  PS.parents.attach.sigma fun k ↦ (Section6PartAFactorization PS Fz k).cells

/-- Actual body of a dependent-sum cell. -/
noncomputable def section6PartABody (x : Section6PartACell PS Fz) :
    ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
  (Section6PartAFactorization PS Fz x.1).body x.2


theorem section6PartACellOf_mem (i : ι) (hi : i ∈ q) :
    section6PartACellOf PS Fz hq i ∈ section6PartACells PS Fz := by
  let k : Section6PartAParent PS := ⟨PS.assign i, PS.assign_mem i hi⟩
  have hk : section6PartAParentOf PS hq i = k := by
    apply Subtype.ext
    simp [section6PartAParentOf, hi, k]
  have hcell : section6PartACellOf PS Fz hq i =
      ⟨k, (Section6PartAFactorization PS Fz k).cellOf i⟩ := by
    simp only [section6PartACellOf]
    rw [hk]
  rw [hcell]
  simp only [section6PartACells, Finset.mem_sigma, Finset.mem_attach, true_and]
  exact (Section6PartAFactorization PS Fz k).cellOf_mem i
    (Finset.mem_filter.mpr ⟨hi, by simp [k]⟩)

theorem section6PartALe_body (i : ι) (hi : i ∈ q) :
    (T i).toConvexSpaceBody ≤
      section6PartABody PS Fz (section6PartACellOf PS Fz hq i) := by
  let k : Section6PartAParent PS := ⟨PS.assign i, PS.assign_mem i hi⟩
  have hk : section6PartAParentOf PS hq i = k := by
    apply Subtype.ext
    simp [section6PartAParentOf, hi, k]
  have hcell : section6PartACellOf PS Fz hq i =
      ⟨k, (Section6PartAFactorization PS Fz k).cellOf i⟩ := by
    simp only [section6PartACellOf]
    rw [hk]
  rw [hcell]
  exact (Section6PartAFactorization PS Fz k).le_body i
    (Finset.mem_filter.mpr ⟨hi, by simp [k]⟩)

/-- The factor family obtained by aggregating all parentwise comparable-body factorizations. -/
noncomputable def section6PartAFactorFamily :
    ShadedBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) ι (Section6PartACell PS Fz) where
  innerSet := q
  innerBody := fun i ↦ (T i).toShadedBody
  outerSet := section6PartACells PS Fz
  outerBody := section6PartABody PS Fz
  parent := section6PartACellOf PS Fz hq
  parent_mem := section6PartACellOf_mem PS Fz hq
  inner_le_parent := section6PartALe_body PS Fz hq

/-- Fibre of a dependent-sum cell, with the structural `DecidableEq` instance fixed once. -/
noncomputable def section6PartAFiber (x : Section6PartACell PS Fz) : Finset ι :=
  @Finset.filter ι (fun i ↦ section6PartACellOf PS Fz hq i = x)
    (fun i ↦ (inferInstance : DecidableEq (Section6PartACell PS Fz))
      (section6PartACellOf PS Fz hq i) x) q

end DependentSum

/-- The explicit Section-6 data surrounding the Proposition 5.1 call in Part (A).

The fields through `input` are the hypotheses of Proposition 5.1.  The remaining fields are
Section-6 geometry: parent labels, occupancy, a common window, essential distinctness and
parentwise Katz--Tao for the representative planks. -/
structure Section6PartAFactorData
    (a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1)
    {ι : Type u_section6PartA} (q : Finset ι) {δ ρ : ℝ≥0}
    (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    {Cpar : ℝ≥0} (PS : ExternalParentSystem q (fun i ↦ (T i).toTube) ρ Cpar)
    (CFib : ℝ≥0∞) (C₀ Cmass Cdim B : ℝ≥0) where
  /-- The actual bodies and their representative planks. -/
  core : Section6CoreFactorData a b hab hb1 q T CFib C₀ Cmass Cdim
  /-- The original coarse parent of a local factor cell. -/
  parent : core.Cell → PS.Parent
  /-- Every retained local cell belongs to an occupied coarse parent. -/
  parent_mem : ∀ x ∈ core.cells, parent x ∈ PS.parents
  /-- Every local cell contains a fine tube assigned to its own coarse parent. -/
  occupancy : ∀ x ∈ core.cells, ∃ i ∈ q,
    PS.assign i = parent x ∧ (T i).toConvexSpaceBody ≤ core.body x
  /-- Representative planks lie in the common Section-6 window. -/
  repr_window : ∀ x ∈ core.cells, (core.repr x).toConvexSpaceBody ≤ plankWindow
  /-- Representatives from all parents are pairwise essentially distinct. -/
  repr_pairwise : (core.cells : Set core.Cell).Pairwise
    (fun x y ↦ _root_.IsEssentiallyDistinct (core.repr x).carrier (core.repr y).carrier)
  /-- Katz--Tao is retained separately on each original coarse-parent fibre. -/
  repr_katzTao : ∀ k ∈ PS.parents,
    IsKatzTao (core.cells.filter fun x ↦ parent x = k)
      (fun x ↦ (core.repr x).toConvexSpaceBody) (C₀ : ℝ≥0∞)
  /-- Scale/discretisation data for the scale-selecting Proposition 5.1 interface. -/
  input : @ShadedBody.Section6FactoringSelectScaleInput _ _ _ _ _ _ _ _ core.decEqCell
    core.toFactorFamily δ B

/-- The Section-6 geometric data used to build the actual Proposition-5.1 input from the
parentwise `ComparableBodyFactorization`s.

Unlike `Section6PartAFactorData`, this structure fixes the cell type to the dependent sum of the
given `Fz`.  Its conversion below is therefore the provenance certificate that the core call is
really applied to the factorization occurring in Proposition 6.6(A). -/
structure Section6PartAConstructionData
    (a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1)
    {ι : Type u_section6PartA} (q : Finset ι) {δ ρ : ℝ≥0}
    (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    {Cpar : ℝ≥0} (PS : ExternalParentSystem q (fun i ↦ (T i).toTube) ρ Cpar)
    (CFib : ℝ≥0∞) (C₀ Cmass Cdim B : ℝ≥0)
    (Fz : ∀ k ∈ PS.parents, ComparableBodyFactorization b
      {i ∈ q | PS.assign i = k} (fun i ↦ (T i).toConvexSpaceBody) C₀)
    where
  /-- The fine family is nonempty. -/
  q_nonempty : q.Nonempty
  /-- Representative plank attached to every dependent-sum cell. -/
  repr : Section6PartACell PS Fz → Plank a b hab hb1
  /-- The scale collar of every actual factor body lies in its representative plank. -/
  cthickening_le_repr : ∀ x ∈ section6PartACells PS Fz,
    (section6PartABody PS Fz x).cthickening (section6PartABody PS Fz x).scale ≤
      (repr x).toConvexSpaceBody
  /-- Representative volume is controlled by actual-body volume. -/
  volume_repr_le : ∀ x ∈ section6PartACells PS Fz,
    volume ((repr x).carrier : Set (EuclideanSpace ℝ (Fin 3))) ≤
      (Cdim : ℝ≥0∞) * volume (section6PartABody PS Fz x).carrier
  /-- Every dependent-sum cell has a nonempty fine fibre. -/
  fibre_nonempty : ∀ x ∈ section6PartACells PS Fz,
    (section6PartAFiber PS Fz q_nonempty x).Nonempty
  /-- The representative version of the fibre Frostman hypothesis. -/
  fibre_frostman : ∀ x ∈ section6PartACells PS Fz,
    IsFrostmanIn (section6PartAFiber PS Fz q_nonempty x)
      (fun i ↦ (T i).toConvexSpaceBody) (repr x).toConvexSpaceBody CFib
  /-- Actual-body fibre densities are mutually comparable. -/
  fibre_mass_comparable : ∀ x ∈ section6PartACells PS Fz,
    ∀ y ∈ section6PartACells PS Fz,
      densityIn (section6PartAFiber PS Fz q_nonempty x)
          (fun i ↦ (T i).toConvexSpaceBody) (section6PartABody PS Fz x) ≤
        (Cmass : ℝ≥0∞) * densityIn (section6PartAFiber PS Fz q_nonempty y)
          (fun i ↦ (T i).toConvexSpaceBody) (section6PartABody PS Fz y)
  /-- All representative planks lie in the Section-6 window. -/
  repr_window : ∀ x ∈ section6PartACells PS Fz,
    (repr x).toConvexSpaceBody ≤ plankWindow
  /-- The representative planks are pairwise essentially distinct. -/
  repr_pairwise : (section6PartACells PS Fz : Set (Section6PartACell PS Fz)).Pairwise
    (fun x y ↦ _root_.IsEssentiallyDistinct (repr x).carrier (repr y).carrier)
  /-- Representative planks are Katz--Tao separately in every original parent. -/
  repr_katzTao : ∀ k ∈ PS.parents,
    IsKatzTao ((section6PartACells PS Fz).filter fun x ↦ x.1.1 = k)
      (fun x ↦ (repr x).toConvexSpaceBody) (C₀ : ℝ≥0∞)
  /-- Positivity of the fine scale. -/
  delta_pos : 0 < δ
  /-- Discretization of the complete dependent-sum family. -/
  inner_discretized : (section6PartAFactorFamily PS Fz q_nonempty).InnerIsDiscretizedAtScale δ
  /-- Explicit outer/inner volume-ratio exponent. -/
  volumeRatio : ShadedBody.OuterInnerVolumeRatio
    (section6PartAFactorFamily PS Fz q_nonempty)
  /-- The fine scale is below the common outer-scale upper bound. -/
  delta_le_upper : δ ≤ B
  /-- Every actual outer body has scale at most `B`. -/
  outer_scale_le : ∀ x ∈ section6PartACells PS Fz, (section6PartABody PS Fz x).scale ≤ B
  /-- Positive input shading mass. -/
  shading_mass_pos : 0 < ∑ i ∈ (section6PartAFactorFamily PS Fz q_nonempty).innerSet,
    volume ((section6PartAFactorFamily PS Fz q_nonempty).innerBody i).shade
  /-- The scale bound used for the similar-shape input. -/
  delta_le_half : (δ : ℝ) ≤ 1 / 2

namespace Section6PartAFactorData

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
  {ι : Type u_section6PartA} {q : Finset ι} {δ ρ : ℝ≥0}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
  {Cpar : ℝ≥0} {PS : ExternalParentSystem q (fun i ↦ (T i).toTube) ρ Cpar}
  {CFib : ℝ≥0∞} {C₀ Cmass Cdim B : ℝ≥0}
  (D : Section6PartAFactorData a b hab hb1 q T PS CFib C₀ Cmass Cdim B)


/-- Invoke the corrected Proposition 5.1 after selecting a common outer scale. -/
theorem prop51CoreSelectScale :
    @ShadedBody.FactoringAndMultPropCoreSelectScaleResult _ _ _ _ _ _ _ _ _
      D.core.decEqCell D.core.toFactorFamily CFib δ B
      (@ShadedBody.Section6FactoringSelectScaleInput.hδ _ _ _ _ _ _ _ _
        D.core.decEqCell D.core.toFactorFamily δ B D.input)
      (@ShadedBody.Section6FactoringSelectScaleInput.hdisc _ _ _ _ _ _ _ _
        D.core.decEqCell D.core.toFactorFamily δ B D.input)
      (@ShadedBody.Section6FactoringSelectScaleInput.volumeRatio _ _ _ _ _ _ _ _
        D.core.decEqCell D.core.toFactorFamily δ B D.input)
      (@ShadedBody.Section6FactoringSelectScaleInput.hδB _ _ _ _ _ _ _ _
        D.core.decEqCell D.core.toFactorFamily δ B D.input)
      (@ShadedBody.Section6FactoringSelectScaleInput.hupper _ _ _ _ _ _ _ _
        D.core.decEqCell D.core.toFactorFamily δ B D.input)
      (@ShadedBody.Section6FactoringSelectScaleInput.hmass _ _ _ _ _ _ _ _
        D.core.decEqCell D.core.toFactorFamily δ B D.input) :=
  D.core.prop51CoreSelectScale D.input


end Section6PartAFactorData

namespace Section6PartAConstructionData

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
  {ι : Type u_section6PartA} {q : Finset ι} {δ ρ : ℝ≥0}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
  {Cpar : ℝ≥0} {PS : ExternalParentSystem q (fun i ↦ (T i).toTube) ρ Cpar}
  {CFib : ℝ≥0∞} {C₀ Cmass Cdim B : ℝ≥0}
  {Fz : ∀ k ∈ PS.parents, ComparableBodyFactorization b
    {i ∈ q | PS.assign i = k} (fun i ↦ (T i).toConvexSpaceBody) C₀}


end Section6PartAConstructionData

end Kakeya

end

end

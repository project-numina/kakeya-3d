/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Uniform.PerScale
public import Kakeya.DimensionThree.Plank.PlankFactorizationEstimate
public import Kakeya.DimensionThree.Plank.InnerConflictDegree
public import Kakeya.DimensionThree.Plank.InnerMultiplicityTransport
public import Kakeya.DimensionThree.Plank.InnerEDAssembly
public import Kakeya.DimensionThree.Plank.Section6PartBCoarseParent
public import Kakeya.DimensionThree.Plank.Section6PartBProp51
public import Kakeya.DimensionThree.Plank.FibreFullnessSelection

/-!
# GWZ Proposition 6.6(B): global plank factorisation

This module contains the global half of GWZ Proposition 6.6. The local Part (A), shared
real-power bookkeeping, and master-scale interfaces live in `PlankFactorizationEstimate.lean`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Convexity ConvexSpaceBody
open scoped NNReal Real ENNReal Classical

noncomputable section

namespace Kakeya

/-- The outer family and the raw Proposition 5.1 data used by the global factorisation assembly. -/
structure Section6PartBData.OuterPackage
    {ι : Type*} {q : Finset ι} {δ : ℝ≥0}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    {a b ρ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {κ : Type*} {r : Finset κ} {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}
    {m Cfib CF C₀ : ℝ≥0} (D : Section6PartBData a b hab hb1 q T r R m Cfib CF C₀)
    (Cprop : ℝ≥0) (ηₒ : ℝ) : Prop where
  outerSet_nonempty : D.fineOutput.outerSet.Nonempty
  outerSet_subset : D.fineOutput.outerSet ⊆ D.factor.cells
  outerPlanks_eq_repr : ∀ x, (D.outerPlanks x).toPrism3D = D.factor.repr x
  outerPlanks_window : ∀ j ∈ D.fineOutput.outerSet,
    ((D.outerPlanks j).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      Metric.closedBall 0 (plankWindowRadius : ℝ)
  outer_fullness : δ ^ ηₒ ≤ ShadedBody.fullness D.fineOutput.outerSet
    (fun j => (D.outerPlanks j).toShadedBody)
  outer_katzTao : IsKatzTao D.fineOutput.outerSet
    (fun j => (D.outerPlanks j).toConvexSpaceBody) ((δ : ℝ≥0∞) ^ (-ηₒ))
  innerSet_eq : D.fineOutput.innerSet =
    ({i ∈ q | D.cellOfFine i ∈ D.fineOutput.outerSet} : Finset ι)
  innerBody_carrier : ∀ i ∈ q,
    (D.fineOutput.innerBody i).toConvexSpaceBody = (T i).toConvexSpaceBody
  refinement : ShadedBody.IsCRefinement D.fineOutput.innerSet D.fineOutput.innerBody q
    (fun i => (T i).toShadedBody) Cprop⁻¹
  multiplicity_split : ∀ x ∈ D.fineOutput.outerSet,
    ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ≤
      (Cprop : ℝ≥0∞) *
        ShadedBody.multiplicity D.fineOutput.outerSet
          (fun y => (D.outerPlanks y).toShadedBody) *
        ShadedBody.multiplicity (D.fineOutput.fiber x) D.fineOutput.innerBody
  fiber_card_comparable : ∀ x ∈ D.fineOutput.outerSet, ∀ y ∈ D.fineOutput.outerSet,
    ((D.fineOutput.fiber x).card : ℝ≥0) ≤
      Cprop * ((D.fineOutput.fiber y).card : ℝ≥0)
  shade_subset : ∀ i ∈ D.fineOutput.innerSet,
    (D.fineOutput.innerBody i).shade ⊆ (D.outerPlanks (D.cellOfFine i)).shade


/-! ### The outer clauses of Proposition 6.6(B) -/


/-! ### The inner block of Proposition 6.6(B) -/

/-- **The essentially distinct inner plank family of Proposition 6.6(B).**

The whole inner pipeline in one step: normalise the fine tubes inside the outer plank
(`Kakeya.exists_inner_family_of_partB`, whose coarse container is already discharged), bound the
conflict degree of the normalised planks (`Kakeya.exists_inner_plank_conflict_degree_bound`), extract
a pairwise essentially distinct subfamily at the weighted loss `d + 1`
(`Kakeya.exists_inner_ED_factorisation_package`), and transport the multiplicity exactly
(`Kakeya.inner_multiplicity_transport`, constant `1`, because the shade is the exact affine image).

The losses are kept explicit and un-absorbed: `Cnorm` on the carrier-sensitive quantities (fullness,
maximal density) and `d + 1` on the extraction-sensitive ones (fullness, cardinality, slab count,
multiplicity).  Absorbing them into `δ`-powers is the caller's job, through
`Kakeya.exists_partB_smallness_threshold`.

**Quantifier order, and the un-absorbed slab constant.**  The dependency chain is
`kap → Cnorm, Cvol, d, δ₀ → configuration`.  `Cnorm` depends on `kap` alone
(`Kakeya.innerShadedPlankFamily`), `Cvol` on `kap` and `cfac`
(`Kakeya.exists_coarse_container_of_guards`), and the conflict degree `d` and threshold `δ₀` on
`kap` alone (`Kakeya.exists_inner_plank_conflict_degree_bound`).  Nothing here depends on `Cfib`,
`CF`, or any exponent, so Proposition 6.6(B) can fix `Csplit = C · (d + 1)` and `Cinner = Cnorm`
before `ηₒ`, `ηᵢ`, `b₀ₒ`, `b₀ᵢ`.

The slab count is reported with its raw constant `(d + 1) · Cfib² · innerCoarseTubeVolumeRatio ·
CF · Cvol`.  It is deliberately *not* absorbed into a power of `a'` here: the absorption threshold
would depend on `Cfib` and `CF`, which the caller does not have when it must fix `s₀`.  The caller
absorbs it into `δ ^ (-ηᵢ)` instead, using `Cfib, CF ≤ δ ^ (-η)` with `η` small compared to `ηᵢ`. -/
theorem exists_inner_ED_family_of_partB {kap : ℝ} (hkap : 0 < kap)
    (cfac : ℝ≥0) (hcfac : 0 < cfac) :
    ∃ (Cnorm Cvol : ℝ≥0) (d : ℕ) (δ₀ : ℝ),
      1 ≤ Cnorm ∧ 1 ≤ Cvol ∧ 0 < d ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {ι : Type*} [DecidableEq ι] {ιr : Type*} [DecidableEq ιr]
        {a b δ ρ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
        (_ha : 0 < a) (_hδ0 : 0 < δ) (_hδa : δ ≤ a) (_hρ0 : 0 < ρ) (_hρ1 : ρ ≤ 1) (_hρa : ρ ≤ a)
        (_hδconf : (δ : ℝ) ≤ δ₀)
        (a₀ b₀ᵢ : ℝ≥0) (_hsmalla : δ ≤ a₀ * b) (_hsmallb : δ ≤ b₀ᵢ * a)
        (W : Plank a b hab hb1) (q : Finset ι) (r : Finset ιr)
        (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (R : ιr → Tube ρ (EuclideanSpace ℝ (Fin 3))) (m Cfib CF : ℝ≥0)
        (f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)) (J : ℝ≥0)
        (g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))),
        0 < J →
        Plank.IsPlankNormalisation W f kap g →
        (∀ E : Set (EuclideanSpace ℝ (Fin 3)), volume (f '' E) = (J : ℝ≥0∞) * volume E) →
        f '' (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ Metric.closedBall 0 1 →
        (∀ x ∈ (W.carrier : Set (EuclideanSpace ℝ (Fin 3))), ‖f x - f W.center‖ ≤ 1) →
        cfac ≤ J * (a * b) →
        (∀ i ∈ q, ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
          ⊆ (W.carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        (q : Set ι).Pairwise
          (fun i j => _root_.IsEssentiallyDistinct
            ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
            ((T j).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        ∀ (_data : CoarseParentSystem q r T R W Cfib CF m),
          ∃ (a' b' : ℝ≥0) (ha'b' : a' ≤ b') (hb'1 : b' ≤ 1) (ιj : Type)
            (qj : Finset ιj) (P : ιj → ShadedPlank a' b' ha'b' hb'1),
            0 < a' ∧ δ ≤ a' ∧ b' ≤ b₀ᵢ ∧
            a' / b' = a / b ∧
            ((a' : ℝ≥0∞) / (b' : ℝ≥0∞) = (a : ℝ≥0∞) / (b : ℝ≥0∞)) ∧
            (∀ i ∈ qj, ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
              ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ)) ∧
            (qj : Set ιj).Pairwise
              (fun i j => _root_.IsEssentiallyDistinct
                ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
                ((P j).carrier : Set (EuclideanSpace ℝ (Fin 3)))) ∧
            q.card ≤ (d + 1) * qj.card ∧ qj.card ≤ q.card ∧
            ShadedBody.fullness q (fun i => (T i).toShadedBody)
              ≤ Cnorm * ((d : ℝ≥0) + 1)
                * ShadedBody.fullness qj (fun i => (P i).toShadedBody) ∧
            maxDensity qj (fun i => (P i).toConvexSpaceBody)
              ≤ (Cnorm : ℝ≥0∞) * maxDensity q (fun i => (T i).toConvexSpaceBody) ∧
            (∀ (φ : ℝ≥0) (hφR : φ ≤ Rslab), a' / b' ≤ φ →
                ∀ (S : Prism3D φ Rslab Rslab hφR le_rfl),
                ((Plank.inWideSlabFamily qj (fun i => (P i).toPrism3D) S).card : ℝ≥0)
                  ≤ ((d : ℝ≥0) + 1) * (Cfib ^ 2 * (innerCoarseTubeVolumeRatio * CF * Cvol))
                      * φ ^ (1 : ℝ) * (qj.card : ℝ≥0)) ∧
            ShadedBody.multiplicity q (fun i => (T i).toShadedBody)
              ≤ ((d : ℝ≥0∞) + 1)
                * ShadedBody.multiplicity qj (fun i => (P i).toShadedBody) := by
  classical
  obtain ⟨Cnorm, Cvol, hCnorm, hCvol, hinner⟩ := exists_inner_family_of_partB kap hkap cfac hcfac
  obtain ⟨d, hdpos, δ₀, hδ₀pos, hδ₀le, hdeg⟩ :=
    exists_inner_plank_conflict_degree_bound hkap
  refine ⟨Cnorm, Cvol, d, δ₀, hCnorm, hCvol, hdpos, hδ₀pos, hδ₀le, ?_⟩
  intro ι _ ιr _ a b δ ρ hab hb1 ha hδ0 hδa hρ0 hρ1 hρa hδconf a₀ b₀ᵢ hsmalla hsmallb
    W q r T R m Cfib CF f J g hJ hnorm hvolf himg hWimg hJab hcarrier hED data
  obtain ⟨a', b', ha'b', hb'1, Pj, ha'def, hb'def, ha'pos, hδa', ha'a₀, hb'b₀, hratioNN,
      hratioENN, hwindow, hfull, hmaxd, hslab, hshade, hcarrimg, halign, hortho⟩ :=
    hinner ha hδ0 hδa hρ0 hρ1 hρa a₀ b₀ᵢ hsmalla hsmallb W q r T R m Cfib CF f J g hJ hnorm hvolf
      himg hWimg hJab hcarrier data
  obtain ⟨F, hF⟩ := Plank.exists_affineEquiv_of_isPlankNormalisation ha W hkap hnorm
  have hJab_deg : J * (a * b) = Real.toNNReal kap ^ 3 :=
    Plank.jacobian_eq ha W hkap hnorm hvolf
  have hvolfF : ∀ E : Set (EuclideanSpace ℝ (Fin 3)),
      volume ((F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) '' E) =
        (J : ℝ≥0∞) * volume E := by
    intro E
    have himg : (F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) '' E =
        (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) '' E :=
      congrArg (fun m : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) => m '' E)
        (funext hF)
    rw [himg]
    exact hvolf E
  have halignlin : ∀ i ∈ q, (Pj i).basis 2 =
      (‖f.linear (T i).direction‖)⁻¹ • (f.linear (T i).direction) := by
    intro i hi
    exact align_linear_of_align_sub (T i).toTube (Pj i).toPrism3D (halign i hi)
  have hdeg' : ∀ i ∈ q, edConflictDegree q (fun j => (Pj j).carrier) i ≤ d := by
    intro i hi
    exact hdeg ha hδ0 hδconf (a' := a') (b' := b') (ha'b' := ha'b') (hb'1 := hb'1)
      ha'def hb'def W q (fun i => (T i).toTube) (fun i => (Pj i).toPrism3D)
      f F J g hF hJ hnorm hJab_deg hvolfF hcarrier hcarrimg halignlin hortho hED i hi
  let hpack := exists_inner_ED_factorisation_package q T Pj Cnorm
    (Cfib ^ 2 * (innerCoarseTubeVolumeRatio * CF * Cvol)) hCnorm hwindow hfull hmaxd hslab hdeg'
  let ιj := hpack.choose
  let hpack₁ := hpack.choose_spec
  let qj := hpack₁.choose
  let hpack₂ := hpack₁.choose_spec
  let P := hpack₂.choose
  let hpack₃ := hpack₂.choose_spec
  let _source := hpack₃.choose
  let hrest := hpack₃.choose_spec
  have hwin := hrest.2.2.1
  have hEDpair := hrest.2.2.2.1
  have hcard1 := hrest.2.2.2.2.1
  have hcard2 := hrest.2.2.2.2.2.1
  have hfull' := hrest.2.2.2.2.2.2.2.1
  have hmaxd' := hrest.2.2.2.2.2.2.2.2.1
  have hslab' := hrest.2.2.2.2.2.2.2.2.2.1
  have hmult := hrest.2.2.2.2.2.2.2.2.2.2
  have hmt : ShadedBody.multiplicity q (fun i => (Pj i).toShadedBody)
      = ShadedBody.multiplicity q (fun i => (T i).toShadedBody) :=
    inner_multiplicity_transport ha hkap W hnorm q T Pj hshade
  refine ⟨a', b', ha'b', hb'1, ιj, qj, P, ha'pos, hδa', hb'b₀, hratioNN, hratioENN, hwin,
    hEDpair, hcard1, hcard2, hfull', hmaxd', hslab', ?_⟩
  calc
    ShadedBody.multiplicity q (fun i ↦ (T i).toShadedBody) =
        ShadedBody.multiplicity q (fun i ↦ (Pj i).toShadedBody) := hmt.symm
    _ ≤ ((d : ℝ≥0∞) + 1) *
        ShadedBody.multiplicity qj (fun i ↦ (P i).toShadedBody) := hmult

namespace Section6PartBData

/-- The selected, normalised inner plank family and all raw bounds used by the Part (B) assembly. -/
structure SelectedInnerPackage
    {ι : Type*} {q : Finset ι} {δ : ℝ≥0}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    {a b ρ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {κ : Type*} {r : Finset κ} {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}
    {m Cfib CF C₀ : ℝ≥0} (D : Section6PartBData a b hab hb1 q T r R m Cfib CF C₀)
    (x₀ : D.factor.Cell) (b₀ᵢ Cnorm Cvol : ℝ≥0) (d : ℕ)
    (innerA innerB : ℝ≥0) (innerA_le_innerB : innerA ≤ innerB)
    (innerB_le_one : innerB ≤ 1) (ιj : Type) (qj : Finset ιj)
    (P : ιj → ShadedPlank innerA innerB innerA_le_innerB innerB_le_one) where
  innerA_pos : 0 < innerA
  delta_le_innerA : δ ≤ innerA
  innerB_le : innerB ≤ b₀ᵢ
  ratio_ennreal : (innerA : ℝ≥0∞) / (innerB : ℝ≥0∞) =
    (a : ℝ≥0∞) / (b : ℝ≥0∞)
  ratio_nnreal : innerA / innerB = a / b
  window : ∀ i ∈ qj,
    ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      Metric.closedBall 0 (plankWindowRadius : ℝ)
  pairwise : (qj : Set ιj).Pairwise
    (fun i j => _root_.IsEssentiallyDistinct ((P i).carrier) ((P j).carrier))
  card_le : qj.card ≤ (D.fineOutput.fiber x₀).card
  fullness : ShadedBody.fullness (D.fineOutput.fiber x₀) D.fineOutput.innerBody ≤
    Cnorm * ((d : ℝ≥0) + 1) * ShadedBody.fullness qj (fun i => (P i).toShadedBody)
  maxDensity_le : maxDensity qj (fun i => (P i).toConvexSpaceBody) ≤
    (Cnorm : ℝ≥0∞) * maxDensity q (fun i => (T i).toConvexSpaceBody)
  slab : ∀ (φ : ℝ≥0) (hφR : φ ≤ Rslab), innerA / innerB ≤ φ →
    ∀ (S : Prism3D φ Rslab Rslab hφR le_rfl),
      ((Plank.inWideSlabFamily qj (fun i => (P i).toPrism3D) S).card : ℝ≥0) ≤
        ((d : ℝ≥0) + 1) * (Cfib ^ 2 * (innerCoarseTubeVolumeRatio * CF * Cvol)) *
          φ ^ (1 : ℝ) * (qj.card : ℝ≥0)
  multiplicity : ShadedBody.multiplicity (D.fineOutput.fiber x₀) D.fineOutput.innerBody ≤
    ((d : ℝ≥0∞) + 1) * ShadedBody.multiplicity qj (fun i => (P i).toShadedBody)

end Section6PartBData

set_option maxHeartbeats 1000000 in
/-- **The selected inner essentially-distinct package of 6.6(B).**

Helper 2 of the assembly.  It chooses the cell `x₀` once, by mediant fibre selection
(`Kakeya.exists_fibre_fullness_le`), so that the *same* fibre serves the inner fullness and the
inner multiplicity, and runs the whole inner pipeline on it: the affine normalisation
(`Plank.factorNormalisingAffineEquiv`), the cellwise coarse-parent system
(`Kakeya.Section6PartBData.coarseParentSystem`, re-shaded by
`Kakeya.CoarseParentSystem.ofTubeEq`), and `Kakeya.exists_inner_ED_family_of_partB`.

The fine tubes are re-shaded with the *refined* Proposition-5.1 shades,
`T' i = ⟨(T i).toTube, (D.fineOutput.innerBody i).shade⟩`; the coarse-parent data sees only
carriers, so it transports unchanged.

**All losses are returned raw.**  `Cfib`, `CF`, `Cvol` and `d + 1` are not absorbed into powers of
`δ` here; that is the finalising helper's job, and it is the only place where the sub-polynomial
bounds on `Cfib` and `CF` are used.  This helper never mentions `Remark53Prop51`: it consumes only
the raw refinement data that the outer package already extracted. -/
theorem exists_partB_selected_inner_ED_package :
    ∃ (Cnorm Cvol : ℝ≥0) (d : ℕ) (δconf : ℝ),
      1 ≤ Cnorm ∧ 1 ≤ Cvol ∧ 0 < d ∧ 0 < δconf ∧ δconf ≤ 1 ∧
      ∀ {ι : Type*} [DecidableEq ι] {q : Finset ι} {δ : ℝ≥0} (_hδ0 : 0 < δ)
        {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
        (_hδconf : (δ : ℝ) ≤ δconf)
        (_hEDq : (q : Set ι).Pairwise
          (fun i j => _root_.IsEssentiallyDistinct
            ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
            ((T j).carrier : Set (EuclideanSpace ℝ (Fin 3)))))
        {a b ρ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
        (_ha : 0 < a) (_hδa : δ ≤ a) (_hρ0 : 0 < ρ) (_hρ1 : ρ ≤ 1) (_hρa : ρ ≤ a)
        (a₀ b₀ᵢ : ℝ≥0) (_hsmalla : δ ≤ a₀ * b) (_hsmallb : δ ≤ b₀ᵢ * a)
        {κ : Type*} {r : Finset κ} {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}
        {m Cfib CF C₀ : ℝ≥0}
        (D : Section6PartBData a b hab hb1 q T r R m Cfib CF C₀)
        (_hne : D.fineOutput.outerSet.Nonempty)
        (_hinnerSet : D.fineOutput.innerSet
          = ({i ∈ q | D.cellOfFine i ∈ D.fineOutput.outerSet} : Finset ι))
        (_hbody : ∀ i ∈ q, (D.fineOutput.innerBody i).toConvexSpaceBody = (T i).toConvexSpaceBody)
        (_hcfibne : ∀ x ∈ D.fineOutput.outerSet, (D.factor.coarseFibre x).Nonempty)
        (_hsub : D.fineOutput.outerSet ⊆ D.factor.cells)
        (_hB0 : (∑ i ∈ D.fineOutput.innerSet,
          volume (D.fineOutput.innerBody i).carrier) ≠ 0)
        (_hBtop : (∑ i ∈ D.fineOutput.innerSet,
          volume (D.fineOutput.innerBody i).carrier) ≠ ⊤),
        ∃ x₀ : D.factor.Cell, x₀ ∈ D.fineOutput.outerSet ∧
          ShadedBody.fullness D.fineOutput.innerSet D.fineOutput.innerBody
            ≤ ShadedBody.fullness (D.fineOutput.fiber x₀) D.fineOutput.innerBody ∧
          ∃ (a' b' : ℝ≥0) (ha'b' : a' ≤ b') (hb'1 : b' ≤ 1)
            (ιj : Type) (qj : Finset ιj)
            (P : ιj → ShadedPlank a' b' ha'b' hb'1),
            D.SelectedInnerPackage x₀ b₀ᵢ Cnorm Cvol d a' b' ha'b' hb'1 ιj qj P := by
  classical
  obtain ⟨kap, cfac, Cfac, hkap, hcfac, hCfac, hnormfam⟩ := Plank.factorNormalisingAffineEquiv
  obtain ⟨Cnorm, Cvol, d, δconf, hCnorm, hCvol, hdpos, hδconfpos, hδconfle, hED⟩ :=
    exists_inner_ED_family_of_partB hkap cfac hcfac
  refine ⟨Cnorm, Cvol, d, δconf, hCnorm, hCvol, hdpos, hδconfpos, hδconfle, ?_⟩
  intro ι _ q δ hδ0 T hδconf hEDq a b ρ hab hb1 ha hδa hρ0 hρ1 hρa a₀ b₀ᵢ hsmalla hsmallb
    κ r R m Cfib CF C₀ D hne hinnerSet hbody hcfibne hsub hB0 hBtop
  -- make the decidability instances used by `Section6PartBData.coarseParentSystem` (which is
  -- `open Classical in`) agree with the ones expected by `CoarseParentSystem.ofTubeEq` and `hED`
  letI : DecidableEq ι := Classical.decEq ι
  -- STEP 1: mediant fibre selection
  obtain ⟨x₀, hx₀, hfull₀⟩ :=
    exists_fibre_fullness_le D.fineOutput.innerSet D.fineOutput.innerBody
      D.fineOutput.outerSet D.fineOutput.parent D.fineOutput.parent_mem hne hB0 hBtop
  -- STEP 2: the fibre is the datum's fine fibre
  have hfib : D.fineOutput.fiber x₀ = D.fineFibre x₀ :=
    D.fineOutput_fiber_eq_fineFibre hinnerSet hx₀
  -- the fibre lies in q
  have hfibq : D.fineOutput.fiber x₀ ⊆ q := by
    intro i hi
    have hi' : i ∈ D.fineOutput.innerSet := by
      simpa [ShadedBody.ShadedFactorFamily.fiber] using (Finset.mem_filter.mp hi).1
    rw [hinnerSet] at hi'
    exact (Finset.mem_filter.mp hi').1
  -- STEP 3: re-shaded fine family
  let T' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)) := fun i =>
    if hiq : i ∈ q then
      { toTube := (T i).toTube
        shade := (D.fineOutput.innerBody i).shade
        measurableSet_shade := (D.fineOutput.innerBody i).measurableSet_shade
        shade_subset := by
          intro x hx
          have hcar : (D.fineOutput.innerBody i).carrier = (T i).carrier := by
            simpa using congrArg (fun B : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) => B.carrier)
              (hbody i hiq)
          simpa [hcar] using (D.fineOutput.innerBody i).shade_subset hx }
    else
      T i
  have hT' : ∀ i, (T' i).toConvexSpaceBody = (T i).toConvexSpaceBody := by
    intro i
    by_cases hiq : i ∈ q
    · simp [T', hiq]
    · simp [T', hiq]
  have hshade' : ∀ i ∈ q, (T' i).shade = (D.fineOutput.innerBody i).shade := by
    intro i hiq
    simp [T', hiq]
  -- STEP 4: coarse-parent system, re-shaded
  have hx₀cells : x₀ ∈ D.factor.cells := hsub hx₀
  have hcne : (D.factor.coarseFibre x₀).Nonempty := hcfibne x₀ hx₀
  let data0 := D.coarseParentSystem x₀ hx₀cells hcne
  let data := data0.ofTubeEq hT'
  -- STEP 5: normalisation
  obtain ⟨f, J, g, hJ, hnorm, hvolf, himg, hWimg, hJab, hJabU⟩ := hnormfam ha (D.factor.repr x₀)
  -- side conditions for hED
  have hcarrierT' : ∀ i ∈ D.fineFibre x₀,
      ((T' i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ ((D.factor.repr x₀).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    intro i hi
    have hiq : i ∈ q := D.fineFibre_subset x₀ hi
    simpa [T', hiq] using D.carrier_subset_repr hi
  have hEDfib : (D.fineFibre x₀ : Set ι).Pairwise
      (fun i j => _root_.IsEssentiallyDistinct
        ((T' i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ((T' j).carrier : Set (EuclideanSpace ℝ (Fin 3)))) := by
    intro i hi j hj hne
    have hED : _root_.IsEssentiallyDistinct
        ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ((T j).carrier : Set (EuclideanSpace ℝ (Fin 3))) :=
      hEDq (D.fineFibre_subset x₀ hi) (D.fineFibre_subset x₀ hj) hne
    have hiq : i ∈ q := D.fineFibre_subset x₀ hi
    have hjq : j ∈ q := D.fineFibre_subset x₀ hj
    simpa [T', hiq, hjq] using hED
  -- STEP 6: run the inner pipeline
  obtain ⟨a', b', ha'b', hb'1, ιj, qj, P, ha'pos, hδa', hb'b₀, hratioNN, hratioENN,
      hwindow, hpair, hcard1, hcard2, hfull, hmaxd, hslab, hmult⟩ :=
    hED ha hδ0 hδa hρ0 hρ1 hρa hδconf a₀ b₀ᵢ hsmalla hsmallb
      (D.factor.repr x₀) (D.fineFibre x₀) (D.factor.coarseFibre x₀) T' R m Cfib CF
      f J g hJ hnorm hvolf himg hWimg hJab hcarrierT' hEDfib data
  -- STEP 7: package
  have hcardfib : qj.card ≤ (D.fineOutput.fiber x₀).card := by
    simpa [hfib] using hcard2
  have hsum_shade : (∑ i ∈ D.fineOutput.fiber x₀, volume (D.fineOutput.innerBody i).shade)
      = (∑ i ∈ D.fineOutput.fiber x₀, volume ((T' i).toShadedBody).shade) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    congr 1
    exact (hshade' i (hfibq hi)).symm
  have hsum_car : (∑ i ∈ D.fineOutput.fiber x₀, volume (D.fineOutput.innerBody i).carrier)
      = (∑ i ∈ D.fineOutput.fiber x₀, volume ((T' i).toShadedBody).carrier) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    congr 1
    have hiq : i ∈ q := hfibq hi
    have hcar : (D.fineOutput.innerBody i).carrier = (T i).carrier := by
      simpa using congrArg (fun B : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) => B.carrier)
        (hbody i hiq)
    simp [T', hiq, hcar]
  have hfull_eq : ShadedBody.fullness (D.fineOutput.fiber x₀) D.fineOutput.innerBody
      = ShadedBody.fullness (D.fineOutput.fiber x₀) (fun i => (T' i).toShadedBody) := by
    rw [← ENNReal.coe_inj, ShadedBody.fullness_def, ShadedBody.fullness_def]
    rw [hsum_shade, hsum_car]
  have hfullgoal : ShadedBody.fullness (D.fineOutput.fiber x₀) D.fineOutput.innerBody
      ≤ Cnorm * ((d : ℝ≥0) + 1)
        * ShadedBody.fullness qj (fun i => (P i).toShadedBody) := by
    calc
      ShadedBody.fullness (D.fineOutput.fiber x₀) D.fineOutput.innerBody
          = ShadedBody.fullness (D.fineOutput.fiber x₀) (fun i => (T' i).toShadedBody) := hfull_eq
      _ = ShadedBody.fullness (D.fineFibre x₀) (fun i => (T' i).toShadedBody) := by
            rw [hfib]
      _ ≤ Cnorm * ((d : ℝ≥0) + 1)
            * ShadedBody.fullness qj (fun i => (P i).toShadedBody) := hfull
  have hmaxdgoal : maxDensity qj (fun i => (P i).toConvexSpaceBody)
      ≤ (Cnorm : ℝ≥0∞) * maxDensity q (fun i => (T i).toConvexSpaceBody) := by
    calc
      maxDensity qj (fun i => (P i).toConvexSpaceBody)
          ≤ (Cnorm : ℝ≥0∞) * maxDensity (D.fineFibre x₀)
              (fun i => (T' i).toConvexSpaceBody) := hmaxd
      _ ≤ (Cnorm : ℝ≥0∞) * maxDensity q (fun i => (T i).toConvexSpaceBody) := by
            gcongr
            calc
              maxDensity (D.fineFibre x₀) (fun i => (T' i).toConvexSpaceBody)
                  = maxDensity (D.fineFibre x₀) (fun i => (T i).toConvexSpaceBody) := by
                    simp [hT']
              _ ≤ maxDensity q (fun i => (T i).toConvexSpaceBody) := by
                    exact maxDensity_mono (fun i => (T i).toConvexSpaceBody)
                      (D.fineFibre_subset x₀)
  have hmultgoal : ShadedBody.multiplicity (D.fineOutput.fiber x₀) D.fineOutput.innerBody
      ≤ ((d : ℝ≥0∞) + 1)
        * ShadedBody.multiplicity qj (fun i => (P i).toShadedBody) := by
    calc
      ShadedBody.multiplicity (D.fineOutput.fiber x₀) D.fineOutput.innerBody
          = ShadedBody.multiplicity (D.fineOutput.fiber x₀) (fun i => (T' i).toShadedBody) := by
            exact multiplicity_eq_of_shade_eqOn (D.fineOutput.fiber x₀) D.fineOutput.innerBody
              (fun i => (T' i).toShadedBody) (by intro i hi; exact (hshade' i (hfibq hi)).symm)
      _ = ShadedBody.multiplicity (D.fineFibre x₀) (fun i => (T' i).toShadedBody) := by
            rw [hfib]
      _ ≤ ((d : ℝ≥0∞) + 1)
            * ShadedBody.multiplicity qj (fun i => (P i).toShadedBody) := hmult
  refine ⟨x₀, hx₀, ?_, a', b', ha'b', hb'1, ιj, qj, P, {
    innerA_pos := ha'pos
    delta_le_innerA := hδa'
    innerB_le := hb'b₀
    ratio_ennreal := hratioENN
    ratio_nnreal := hratioNN
    window := hwindow
    pairwise := hpair
    card_le := hcardfib
    fullness := hfullgoal
    maxDensity_le := hmaxdgoal
    slab := hslab
    multiplicity := hmultgoal }⟩
  simpa [ShadedBody.ShadedFactorFamily.fiber] using hfull₀

/-- **Finalising the raw inner bounds of 6.6(B) into the public `δ`-power form.**

Helper 3 of the assembly, and the only place where the sub-polynomial bounds `Cfib, CF ≤ δ ^ (-η)`
are used.  It is purely scalar: it converts the two raw losses produced by the inner package into
the two `δ`-power clauses `Kakeya.factoringAndMultPropGlobal` exports.

* **Slab.**  The raw coefficient is `(d + 1) · Cfib² · innerCoarseTubeVolumeRatio · CF · Cvol`.
  Two factors of `Cfib` and one of `CF` cost `δ ^ (-3η)`; the remaining absolute constant
  `(d + 1) · innerCoarseTubeVolumeRatio · Cvol` is absorbed by `habsSlab` at the fixed threshold.
  With `8 · η ≤ ηᵢ` the two exponents fit inside `ηᵢ`, since `ηᵢ / 2 + 3η ≤ ηᵢ`.
* **Fullness.**  The raw loss is `Cnorm · (d + 1)`, with no `Cfib` or `CF` in it at all; it is
  absorbed across the exponent gap `ηᵢ - η` by `habsFull`.  It is stated as a transfer between two
  abstract fullness values, so that it applies to the selected fibre without carrying the whole
  configuration.

Neither `Csplit`, `Ccard` nor `Cinner` appears here: those are fixed before any of this, and the
maximal-density clause needs no finalising at all (`Cinner = Cnorm`, verbatim). -/
theorem partB_finalize_selected_inner_bounds
    {ηᵢ η : ℝ} (hη : 0 < η) (hηᵢ : 0 < ηᵢ) (h8η : 8 * η ≤ ηᵢ)
    {δ : ℝ≥0} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {Cprop Cfib CF Cvol Cnorm : ℝ≥0} (hCprop : 1 ≤ Cprop) {d : ℕ}
    (hCfib : Cfib ≤ δ ^ (-η)) (hCF : CF ≤ δ ^ (-η))
    (habsSlab : ((d : ℝ≥0) + 1) * (innerCoarseTubeVolumeRatio * Cvol) ≤ δ ^ (-(ηᵢ / 2)))
    (habsFull : Cprop * (Cnorm * ((d : ℝ≥0) + 1)) ≤ δ ^ (-(ηᵢ - η))) :
    ((d : ℝ≥0) + 1) * (Cfib ^ 2 * (innerCoarseTubeVolumeRatio * CF * Cvol)) ≤ δ ^ (-ηᵢ) ∧
    (∀ F G : ℝ≥0, Cprop⁻¹ * δ ^ η ≤ F →
      F ≤ Cnorm * ((d : ℝ≥0) + 1) * G → δ ^ ηᵢ ≤ G) := by
  have hδne : δ ≠ 0 := ne_of_gt hδ0
  have hCfib2 : Cfib ^ 2 ≤ (δ ^ (-η)) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) hCfib 2
  have hCfibCF : Cfib ^ 2 * CF ≤ (δ ^ (-η)) ^ 2 * δ ^ (-η) := by
    exact mul_le_mul hCfib2 hCF (by positivity) (by positivity)
  have hpow2 : (δ ^ (-η)) ^ 2 * δ ^ (-η) = δ ^ (-(3 * η)) := by
    rw [pow_two]
    rw [← NNReal.rpow_add hδne]
    rw [← NNReal.rpow_add hδne]
    congr
    ring
  have hmain1 : ((d : ℝ≥0) + 1) * (Cfib ^ 2 * (innerCoarseTubeVolumeRatio * CF * Cvol))
      ≤ δ ^ (-(ηᵢ / 2)) * δ ^ (-(3 * η)) := by
    calc
      ((d : ℝ≥0) + 1) * (Cfib ^ 2 * (innerCoarseTubeVolumeRatio * CF * Cvol))
          = (((d : ℝ≥0) + 1) * (innerCoarseTubeVolumeRatio * Cvol)) * (Cfib ^ 2 * CF) := by
        ring
      _ ≤ δ ^ (-(ηᵢ / 2)) * (Cfib ^ 2 * CF) := by
        exact mul_le_mul_of_nonneg_right habsSlab (by positivity)
      _ ≤ δ ^ (-(ηᵢ / 2)) * ((δ ^ (-η)) ^ 2 * δ ^ (-η)) := by
        exact mul_le_mul_of_nonneg_left hCfibCF (by positivity)
      _ = δ ^ (-(ηᵢ / 2)) * δ ^ (-(3 * η)) := by
        rw [hpow2]
  have hle : -ηᵢ ≤ -(ηᵢ / 2) - 3 * η := by
    have hηᵢ_nonneg : 0 ≤ ηᵢ := le_of_lt hηᵢ
    linarith
  have hmono : δ ^ (-(ηᵢ / 2) - 3 * η) ≤ δ ^ (-ηᵢ) := by
    exact NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hle
  have hfinal1 : ((d : ℝ≥0) + 1) * (Cfib ^ 2 * (innerCoarseTubeVolumeRatio * CF * Cvol))
      ≤ δ ^ (-ηᵢ) := by
    calc
      ((d : ℝ≥0) + 1) * (Cfib ^ 2 * (innerCoarseTubeVolumeRatio * CF * Cvol))
          ≤ δ ^ (-(ηᵢ / 2)) * δ ^ (-(3 * η)) := hmain1
      _ = δ ^ (-(ηᵢ / 2) + -(3 * η)) := by
        rw [← NNReal.rpow_add hδne]
      _ = δ ^ (-(ηᵢ / 2) - 3 * η) := by rfl
      _ ≤ δ ^ (-ηᵢ) := hmono
  constructor
  · exact hfinal1
  · intro F G hF hFG
    have hCne : Cprop ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hCprop)
    have hpow_le : δ ^ η ≤ Cprop * F := by
      calc
        δ ^ η = Cprop * (Cprop⁻¹ * δ ^ η) := by
          rw [← mul_assoc, mul_inv_cancel₀ hCne, one_mul]
        _ ≤ Cprop * F := mul_le_mul_of_nonneg_left hF (by positivity)
    have hFG' : Cprop * F ≤ (Cprop * (Cnorm * ((d : ℝ≥0) + 1))) * G := by
      calc
        Cprop * F ≤ Cprop * (Cnorm * ((d : ℝ≥0) + 1) * G) :=
          mul_le_mul_of_nonneg_left hFG (by positivity)
        _ = (Cprop * (Cnorm * ((d : ℝ≥0) + 1))) * G := by ring
    exact rpow_le_of_le_mul_of_loss_le hδ0 habsFull hpow_le hFG'


/-- `Kakeya.gammaZeroSlabBound` at the master scale: the `γ = 0` slab hypothesis of the master-scale
reading of GWZ Lemma 6.1 (`Kakeya.PlankEstimateAtMasterScale`) is vacuous for the same reason, and
for any scale `δ ∈ (0, 1]` in place of the plank scale `a`. -/
theorem gammaZeroSlabBoundAtMasterScale {a b δ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}
    {η : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : 0 ≤ η) (s : Finset ι) (P : ι → Plank a b hab hb1)
    (φ : ℝ≥0) (hφR : φ ≤ Rslab) (S : Prism3D φ Rslab Rslab hφR le_rfl) :
    ((Plank.inWideSlabFamily s P S).card : ℝ≥0) ≤ δ ^ (-η) * φ ^ (0 : ℝ) * (s.card : ℝ≥0) := by
  have hcard : ((Plank.inWideSlabFamily s P S).card : ℝ≥0) ≤ (s.card : ℝ≥0) := by
    exact_mod_cast Finset.card_le_card (Plank.inWideSlabFamily_subset (s := s) (V := P) (Sφ := S))
  have h_one : (1 : ℝ≥0) ≤ δ ^ (-η) :=
    NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by
      linarith)
  calc
    ((Plank.inWideSlabFamily s P S).card : ℝ≥0) ≤ (s.card : ℝ≥0) := hcard
    _ = (1 : ℝ≥0) * (s.card : ℝ≥0) := by simp
    _ = (1 : ℝ≥0) * (1 : ℝ≥0) * (s.card : ℝ≥0) := by simp
    _ ≤ δ ^ (-η) * (1 : ℝ≥0) * (s.card : ℝ≥0) := by
      gcongr
    _ = δ ^ (-η) * φ ^ (0 : ℝ) * (s.card : ℝ≥0) := by simp


/-- **The 6.6(B) combination, with the inner density loss of GWZ Proposition 5.1.**

`Kakeya.combineGlobalFactor` with the max-density transfer of the Proposition 5.1 leaf weakened from
`Δ_max(inner) ≤ Δ_max(𝒯)` to `Δ_max(inner) ≤ Cinner · Δ_max(𝒯)`, which is all the affine
normalisation of an `a × b × 1` plank can give (see `Kakeya.factoringAndMultPropGlobal`).  The extra
constant is paid for out of the sub-polynomial budget: the two applications of Lemma 6.1 are run at
`ε/6` rather than `ε/3`, and the reserved factor `δ ^ (-ε/2)` absorbs `Cinner` through the threshold
hypothesis `hthrI`, exactly as `hthr` absorbs `Csplit · Ccard ^ β`. -/
theorem combineGlobalFactorWithInnerLoss {β ε : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1)
    {δ a b : ℝ≥0} (hδ0 : 0 < δ) (_hδ1 : δ ≤ 1) {Csplit Ccard Cinner : ℝ≥0}
    (_hCs1 : 1 ≤ Csplit) (_hCc1 : 1 ≤ Ccard) (hCi1 : 1 ≤ Cinner)
    {Δ : ℝ≥0∞} {nq nts nj : ℕ} {μqT μW μTj : ℝ≥0∞}
    (hW : μW ≤ (δ : ℝ≥0∞) ^ (-(ε / 6)) * (nts : ℝ≥0∞) ^ β)
    (hTj : μTj ≤ (δ : ℝ≥0∞) ^ (-(ε / 6)) * ((Cinner : ℝ≥0∞) * Δ) ^ (1 - β)
        * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ β * (nj : ℝ≥0∞) ^ β)
    (hsplit : μqT ≤ (Csplit : ℝ≥0∞) * μW * μTj)
    (hcard : (nts : ℝ≥0∞) * (nj : ℝ≥0∞) ≤ (Ccard : ℝ≥0∞) * (nq : ℝ≥0∞))
    (hthr : (Csplit : ℝ≥0∞) * (Ccard : ℝ≥0∞) ^ β ≤ (δ : ℝ≥0∞) ^ (-(ε / 6)))
    (hthrI : (Cinner : ℝ≥0∞) ≤ (δ : ℝ≥0∞) ^ (-(ε / 2))) :
    μqT ≤ (δ : ℝ≥0∞) ^ (-ε) * Δ ^ (1 - β)
      * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ β * (nq : ℝ≥0∞) ^ β := by
  -- Step 1: combine hsplit with hW and hTj
  have hβ_nonneg : 0 ≤ β := by linarith
  have hstep : μqT ≤ (Csplit : ℝ≥0∞)
      * ((δ : ℝ≥0∞) ^ (-(ε / 6)) * (nts : ℝ≥0∞) ^ β)
      * ((δ : ℝ≥0∞) ^ (-(ε / 6)) * ((Cinner : ℝ≥0∞) * Δ) ^ (1 - β)
        * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ β * (nj : ℝ≥0∞) ^ β) := by
    calc
      μqT ≤ (Csplit : ℝ≥0∞) * μW * μTj := hsplit
      _ ≤ (Csplit : ℝ≥0∞) * ((δ : ℝ≥0∞) ^ (-(ε / 6)) * (nts : ℝ≥0∞) ^ β) * μTj := by
        gcongr
      _ ≤ (Csplit : ℝ≥0∞) * ((δ : ℝ≥0∞) ^ (-(ε / 6)) * (nts : ℝ≥0∞) ^ β)
          * ((δ : ℝ≥0∞) ^ (-(ε / 6)) * ((Cinner : ℝ≥0∞) * Δ) ^ (1 - β)
            * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ β * (nj : ℝ≥0∞) ^ β) := by
        gcongr
  -- Step 2: cardinality bound hprod: (nts)^β * (nj)^β ≤ (Ccard)^β * (nq)^β
  have hprod : (nts : ℝ≥0∞) ^ β * (nj : ℝ≥0∞) ^ β ≤
      (Ccard : ℝ≥0∞) ^ β * (nq : ℝ≥0∞) ^ β := by
    calc
      (nts : ℝ≥0∞) ^ β * (nj : ℝ≥0∞) ^ β = ((nts : ℝ≥0∞) * (nj : ℝ≥0∞)) ^ β := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hβ_nonneg]
      _ ≤ ((Ccard : ℝ≥0∞) * (nq : ℝ≥0∞)) ^ β :=
        ENNReal.rpow_le_rpow hcard hβ_nonneg
      _ = (Ccard : ℝ≥0∞) ^ β * (nq : ℝ≥0∞) ^ β := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hβ_nonneg]
  -- Step 3: the inner-density constant is absorbed through `Cinner ^ (1 - β) ≤ Cinner`
  have h_nonneg_1mβ : 0 ≤ 1 - β := by linarith
  have hCinner_rpow : (Cinner : ℝ≥0∞) ^ (1 - β) ≤ (Cinner : ℝ≥0∞) := by
    calc
      (Cinner : ℝ≥0∞) ^ (1 - β) ≤ (Cinner : ℝ≥0∞) ^ (1 : ℝ) :=
        ENNReal.rpow_le_rpow_of_exponent_le (by exact_mod_cast hCi1) (by linarith : 1 - β ≤ 1)
      _ = (Cinner : ℝ≥0∞) := ENNReal.rpow_one _
  have hCinner_mul_eq : ((Cinner : ℝ≥0∞) * Δ) ^ (1 - β)
      = (Cinner : ℝ≥0∞) ^ (1 - β) * Δ ^ (1 - β) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ h_nonneg_1mβ]
  -- Step 4: δ-power split: δ^(-ε) = δ^(-(ε/6))^3 * δ^(-(ε/2))
  have hδ_nonzero : (δ : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ0.ne'
  have hδ_not_top : (δ : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hsplitδ : (δ : ℝ≥0∞) ^ (-ε)
      = (δ : ℝ≥0∞) ^ (-(ε / 6)) * (δ : ℝ≥0∞) ^ (-(ε / 6)) * (δ : ℝ≥0∞) ^ (-(ε / 6))
        * (δ : ℝ≥0∞) ^ (-(ε / 2)) := by
    calc
      (δ : ℝ≥0∞) ^ (-ε) =
          (δ : ℝ≥0∞) ^ (-(ε / 6) + (-(ε / 6)) + (-(ε / 6)) + (-(ε / 2))) := by
        rw [show -ε = -(ε / 6) + -(ε / 6) + -(ε / 6) + -(ε / 2) by ring]
      _ = ((δ : ℝ≥0∞) ^ (-(ε / 6) + (-(ε / 6)) + (-(ε / 6)))) * (δ : ℝ≥0∞) ^ (-(ε / 2)) := by
        rw [ENNReal.rpow_add (-(ε / 6) + (-(ε / 6)) + (-(ε / 6))) (-(ε / 2)) hδ_nonzero
          hδ_not_top]
      _ = (((δ : ℝ≥0∞) ^ (-(ε / 6) + (-(ε / 6)))) * (δ : ℝ≥0∞) ^ (-(ε / 6)))
          * (δ : ℝ≥0∞) ^ (-(ε / 2)) := by
        rw [ENNReal.rpow_add (-(ε / 6) + (-(ε / 6))) (-(ε / 6)) hδ_nonzero hδ_not_top]
      _ = (((δ : ℝ≥0∞) ^ (-(ε / 6)) * (δ : ℝ≥0∞) ^ (-(ε / 6))) * (δ : ℝ≥0∞) ^ (-(ε / 6)))
          * (δ : ℝ≥0∞) ^ (-(ε / 2)) := by
        rw [ENNReal.rpow_add (-(ε / 6)) (-(ε / 6)) hδ_nonzero hδ_not_top]
      _ = (δ : ℝ≥0∞) ^ (-(ε / 6)) * (δ : ℝ≥0∞) ^ (-(ε / 6)) * (δ : ℝ≥0∞) ^ (-(ε / 6))
          * (δ : ℝ≥0∞) ^ (-(ε / 2)) := by ring
  -- Step 5: final calc
  calc
    μqT ≤ (Csplit : ℝ≥0∞)
        * ((δ : ℝ≥0∞) ^ (-(ε / 6)) * (nts : ℝ≥0∞) ^ β)
        * ((δ : ℝ≥0∞) ^ (-(ε / 6)) * ((Cinner : ℝ≥0∞) * Δ) ^ (1 - β)
          * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ β * (nj : ℝ≥0∞) ^ β) :=
      hstep
    _ = (Csplit : ℝ≥0∞) * (δ : ℝ≥0∞) ^ (-(ε / 6)) * (δ : ℝ≥0∞) ^ (-(ε / 6))
        * ((nts : ℝ≥0∞) ^ β * (nj : ℝ≥0∞) ^ β) * ((Cinner : ℝ≥0∞) * Δ) ^ (1 - β)
        * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ β := by
      ring
    _ ≤ (Csplit : ℝ≥0∞) * (δ : ℝ≥0∞) ^ (-(ε / 6)) * (δ : ℝ≥0∞) ^ (-(ε / 6))
        * ((Ccard : ℝ≥0∞) ^ β * (nq : ℝ≥0∞) ^ β) * ((Cinner : ℝ≥0∞) * Δ) ^ (1 - β)
        * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ β := by
      gcongr
    _ = (Csplit : ℝ≥0∞) * (δ : ℝ≥0∞) ^ (-(ε / 6)) * (δ : ℝ≥0∞) ^ (-(ε / 6))
        * ((Ccard : ℝ≥0∞) ^ β * (nq : ℝ≥0∞) ^ β) * (Cinner : ℝ≥0∞) ^ (1 - β)
        * Δ ^ (1 - β) * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ β := by
      rw [hCinner_mul_eq]
      ring
    _ ≤ (Csplit : ℝ≥0∞) * (δ : ℝ≥0∞) ^ (-(ε / 6)) * (δ : ℝ≥0∞) ^ (-(ε / 6))
        * ((Ccard : ℝ≥0∞) ^ β * (nq : ℝ≥0∞) ^ β) * (Cinner : ℝ≥0∞)
        * Δ ^ (1 - β) * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ β := by
      gcongr
    _ = (Csplit : ℝ≥0∞) * (Ccard : ℝ≥0∞) ^ β * (δ : ℝ≥0∞) ^ (-(ε / 6))
        * (δ : ℝ≥0∞) ^ (-(ε / 6)) * (nq : ℝ≥0∞) ^ β * (Cinner : ℝ≥0∞)
        * Δ ^ (1 - β) * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ β := by
      ring
    _ ≤ (δ : ℝ≥0∞) ^ (-(ε / 6)) * (δ : ℝ≥0∞) ^ (-(ε / 6)) * (δ : ℝ≥0∞) ^ (-(ε / 6))
        * (nq : ℝ≥0∞) ^ β * (Cinner : ℝ≥0∞) * Δ ^ (1 - β) * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ β := by
      gcongr
    _ ≤ (δ : ℝ≥0∞) ^ (-(ε / 6)) * (δ : ℝ≥0∞) ^ (-(ε / 6)) * (δ : ℝ≥0∞) ^ (-(ε / 6))
        * (nq : ℝ≥0∞) ^ β * (δ : ℝ≥0∞) ^ (-(ε / 2)) * Δ ^ (1 - β)
        * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ β := by
      gcongr
    _ = (δ : ℝ≥0∞) ^ (-(ε / 6)) * (δ : ℝ≥0∞) ^ (-(ε / 6)) * (δ : ℝ≥0∞) ^ (-(ε / 6))
        * (δ : ℝ≥0∞) ^ (-(ε / 2)) * (nq : ℝ≥0∞) ^ β * Δ ^ (1 - β)
        * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ β := by
      ring
    _ = (δ : ℝ≥0∞) ^ (-ε) * (nq : ℝ≥0∞) ^ β * Δ ^ (1 - β)
        * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ β := by
      rw [hsplitδ]
    _ = (δ : ℝ≥0∞) ^ (-ε) * Δ ^ (1 - β) * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ β * (nq : ℝ≥0∞) ^ β := by
      ring

/-- **The `γ = 0` outer plank bound at the master scale, packaged for GWZ Proposition 6.6(B).**

The master-scale reading of GWZ Lemma 6.1 (`Kakeya.PlankEstimateAtMasterScale`) applied with
`γ = 0`, whose slab hypothesis is vacuous (`Kakeya.gammaZeroSlabBoundAtMasterScale`, GWZ Remark 6.2)
and whose eccentricity factor is therefore `1`.  This is the exact shape in which Proposition 6.6(B)
consumes the outer family produced by GWZ Proposition 5.1: fullness and Katz--Tao data at the master
scale `δ`, loss `δ ^ (-ε')`, no `(a/b)` factor. -/
theorem exists_outerMultiplicityBoundAtMasterScale.{u} {β : ℝ}
    (h61δ : PlankEstimateAtMasterScale.{u} β)
    {ε' : ℝ} (hε' : 0 < ε') :
    ∃ η > (0 : ℝ), ∃ b₀ > (0 : ℝ≥0),
      ∀ {κ' : Type u} (ts : Finset κ') {δ a b : ℝ≥0} (hab : a ≤ b) (hb1 : b ≤ 1)
        (W : κ' → ShadedPlank a b hab hb1),
        0 < δ → δ ≤ a → b ≤ b₀ →
        (∀ j ∈ ts, (W j).carrier ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ)) →
        (ts : Set κ').Pairwise
          (fun i j => _root_.IsEssentiallyDistinct (W i).carrier (W j).carrier) →
        δ ^ η ≤ ShadedBody.fullness ts (fun j => (W j).toShadedBody) →
        IsKatzTao ts (fun j => (W j).toConvexSpaceBody) (δ ^ (-η)) →
        ShadedBody.multiplicity ts (fun j => (W j).toShadedBody) ≤
          (δ : ℝ≥0∞) ^ (-ε') * (ts.card : ℝ≥0∞) ^ β := by
  rcases h61δ ε' hε' with ⟨η, hη, b₀, hb₀, hinstance⟩
  refine ⟨η, hη, b₀, hb₀, ?_⟩
  intro κ' ts δ a b hab hb1 W hδ hδa hbb₀ hWball hWed hWfull hWKT
  have hδ1 : δ ≤ 1 := le_trans hδa (le_trans hab hb1)
  have hslab : ∀ (φ : ℝ≥0) (hφR : φ ≤ Rslab), a / b ≤ φ →
      ∀ (S : Prism3D φ Rslab Rslab hφR le_rfl),
      ((Plank.inWideSlabFamily ts (fun j => (W j).toPrism3D) S).card : ℝ≥0)
        ≤ δ ^ (-η) * φ ^ (0 : ℝ) * (ts.card : ℝ≥0) :=
    fun φ hφR _ S =>
      gammaZeroSlabBoundAtMasterScale hδ hδ1 hη.le ts (fun j => (W j).toPrism3D) φ hφR S
  have hmain : ShadedBody.multiplicity ts (fun j => (W j).toShadedBody) ≤
      (δ : ℝ≥0∞) ^ (-ε') * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ ((0 : ℝ) * β)
        * (ts.card : ℝ≥0∞) ^ β :=
    hinstance ts hab hb1 W
      hδ hδa hbb₀ hWball hWed hWfull hWKT 0 le_rfl zero_le_one hslab
  have hz : ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ ((0 : ℝ) * β) = 1 := by
    rw [zero_mul, ENNReal.rpow_zero]
  rw [hz] at hmain
  rwa [mul_one] at hmain

/-- **Transfer of the inner `γ = 1` plank estimate to the outer scales.**

The rpow bookkeeping that turns the conclusion of GWZ Lemma 6.1 for the *normalised inner* family
(`Kakeya.PlankEstimateAtMasterScaleWithDensity` at `γ = 1`, stated with the inner maximal density)
into the shape the 6.6(B) combination lemmas consume: the ambient density `Δ₀` carrying the
Proposition 5.1 normalisation loss `Cinner`, and the eccentricity factor rewritten by the preserved
ratio `a'/b' = a/b`. -/
theorem innerBoundTransfer {β ε' : ℝ} (hβle : β ≤ 1)
    {δ a b a' b' Cinner : ℝ≥0} {Δ₀ Δj μTj : ℝ≥0∞} {nj : ℕ}
    (hratio : (a' : ℝ≥0∞) / (b' : ℝ≥0∞) = (a : ℝ≥0∞) / (b : ℝ≥0∞))
    (hmaxd : Δj ≤ (Cinner : ℝ≥0∞) * Δ₀)
    (hinner : μTj ≤ (δ : ℝ≥0∞) ^ (-ε') * Δj ^ (1 - β)
      * ((a' : ℝ≥0∞) / (b' : ℝ≥0∞)) ^ ((1 : ℝ) * β) * (nj : ℝ≥0∞) ^ β) :
    μTj ≤ (δ : ℝ≥0∞) ^ (-ε') * ((Cinner : ℝ≥0∞) * Δ₀) ^ (1 - β)
      * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ β * (nj : ℝ≥0∞) ^ β := by
  have hinner_simp : μTj ≤ (δ : ℝ≥0∞) ^ (-ε') * Δj ^ (1 - β)
      * ((a' : ℝ≥0∞) / (b' : ℝ≥0∞)) ^ β * (nj : ℝ≥0∞) ^ β := by
    simpa [one_mul] using hinner
  have hΔ : Δj ^ (1 - β) ≤ ((Cinner : ℝ≥0∞) * Δ₀) ^ (1 - β) := by
    have h_nonneg : (0 : ℝ) ≤ 1 - β := by linarith
    exact ENNReal.rpow_le_rpow hmaxd h_nonneg
  have hratio_enn : ((a' : ℝ≥0∞) / (b' : ℝ≥0∞)) ^ β =
      ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ β := by
    rw [hratio]
  calc
    μTj ≤ (δ : ℝ≥0∞) ^ (-ε') * Δj ^ (1 - β) * ((a' : ℝ≥0∞) / (b' : ℝ≥0∞)) ^ β
        * (nj : ℝ≥0∞) ^ β := hinner_simp
    _ ≤ (δ : ℝ≥0∞) ^ (-ε') * ((Cinner : ℝ≥0∞) * Δ₀) ^ (1 - β)
        * ((a' : ℝ≥0∞) / (b' : ℝ≥0∞)) ^ β * (nj : ℝ≥0∞) ^ β := by
      gcongr
    _ = (δ : ℝ≥0∞) ^ (-ε') * ((Cinner : ℝ≥0∞) * Δ₀) ^ (1 - β)
        * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ β * (nj : ℝ≥0∞) ^ β := by
      rw [hratio_enn]

/-! ### Additional estimates

The next declaration is **not** a proof of GWZ Proposition 6.6(B).  Two of its hypotheses,
`h61δ : PlankEstimateAtMasterScale β` and `h61δΔ : PlankEstimateAtMasterScaleWithDensity β`, are
`Prop`-valued readings of **GWZ Lemma 6.1 itself**.  Neither is established anywhere, on the source
branch or here; they are assumed.  So what is proved is the implication
"Lemma 6.1 at the master scale (both readings) ⟹ Proposition 6.6(B)", not Proposition 6.6(B).

Note also that the statement below is over
`Kakeya.Section6PartBData`, a different — and hypothesis-richer — datum than ship's
`Kakeya.GlobalPlankFactorization`. -/


end Kakeya

end

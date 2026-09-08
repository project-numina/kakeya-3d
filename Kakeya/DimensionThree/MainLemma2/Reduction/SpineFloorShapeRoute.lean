/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapePayload
public import Kakeya.MultiScaleSubmult
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineTwoScale
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineRungWiring
public import Kakeya.DimensionThree.MainLemma2.LineEssDistinct
public import Kakeya.Tube.Rigidity
public import Kakeya.FrostmanTransfer
public import Kakeya.ShadedUniform
public import Kakeya.DimensionThree.MainLemma2.GridRounding
public import Kakeya.StickyKakeya.CrossScale
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEveryScale
public import Kakeya.MultiScaleFac.GapsKT
public import Kakeya.GridScale
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCoreWindow
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineParams
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEccentric
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEDMultBound
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineDefectExit
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShape
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeFullness

/-!
# The floor and defect alternatives on a refined family

GWZ's `lem:ml2-window-refinement` gives alternative outputs;
an unconditional floor conclusion would select one disjunct without justification.
`DefectBranchAt` states the defect alternative and obtains fullness retention
from `IsShadedRefinementOf.fullness'_le`. `FloorDataAtTrichotomy` combines the
floor and defect alternatives after choosing the window indices `a`, `b`, `m`.
The consumers split on these alternatives.

The identity refinement cannot destroy concentration, as
`lt_pairProfile_of_identity` shows. In the surviving branch, a supplied gain
already yields the conclusion through `trialOutcomeAtGain_of_gain_of_absorb`.
Thus choosing the identity refinement does not produce the required gain;
that gain must be obtained from the floor construction.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Tube Topology Filter

namespace Kakeya.ML2Core

/-! ### Route (a): the identity refinement cannot destroy the concentration -/

section RouteA

variable {ι : Type*} {δ Cu : ℝ≥0} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
  {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}

end RouteA

/-! ### Route (b), at source shape: a **named** `(D)` branch -/

section RouteB

variable {ι : Type*} {δ Cu : ℝ≥0} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

/-- **The source's `(D)` output, named.**

`lem:ml2-window-refinement`, item `(D)`:

> *there are a nonempty `𝕊* ⊂ 𝕊'` and a subshading `Z*` for which `Φ_h(𝕊*) ≤ Φ_h(𝕊') − 1`*

together with the clause shared by all three outputs: the `Λf⁻¹` mass retention, the
inherited tower, and *"its shading is a restriction of `Z`"*.  Conjuncts 1 and 2 below are exactly
that: `Kakeya.ML2Core.IsShadedRefinementOf` already packages nonemptiness, the sub-shading, the same
tubes, the `Λf` mass retention and the inherited tower
(`Kakeya.ML2Core.IsClassHomogeneousOn`), and `potential h 𝒰 S' + 1 ≤ potential h 𝒰 S` is
`Φ_h(𝕊*) ≤ Φ_h(𝕊') − 1`.

Conjunct 3 is **not** in the source's `(D)`; it is the dense-shading transfer that the tree's existing
`Kakeya.ML2Core.TrialOutcomeAtGain` carries in its third disjunct.  It is included so that the
branch is consumable with **no new obligation at the consumer**, and
`Kakeya.ML2Core.DefectBranchAt.sourceForm` projects back onto the source's own two conjuncts so the
excess stays auditable.

The `fullness'` retention that the tree's third disjunct also carries is **not** a conjunct here:
`SRC-A`'s `Kakeya.ML2Core.IsShadedRefinementOf.fullness'_le` derives it from clause 5 of the
refinement, so asking for it would have been a fourth excess over the source. -/
def DefectBranchAt (h : ℝ) (Λf : ℝ≥0∞) (lam : ℝ≥0)
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    (S : Finset ι) (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∃ (S' : Finset ι) (W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
    IsShadedRefinementOf 𝒰 Λf S Z S' W ∧
    potential h 𝒰 S' + 1 ≤ potential h 𝒰 S ∧
    ∃ lam' : ℝ≥0, 0 < lam' ∧ lam ≤ Λf * lam' ∧
      ML2Shaded.HasDenseShading lam' S' (fun i => (W i).toShadedBody)

/-- **The `(D)` branch is consumable with no new obligation**: it *is* the third disjunct of the
existing `Kakeya.ML2Core.TrialOutcomeAtGain`. -/
theorem trialOutcomeAtGain_of_defectBranch {h ε₀ g β : ℝ} {Λf : ℝ≥0∞} {lam : ℝ≥0}
    {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}
    {S : Finset ι} {Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (hD : DefectBranchAt h Λf lam 𝒰 S Z) :
    TrialOutcomeAtGain h ε₀ g β 𝒰 Λf lam S Z := by
  obtain ⟨S', W, href, hdrop, lam', hlam'0, hlam', hdense⟩ := hD
  exact Or.inr (Or.inr ⟨S', href.subset, W, href.nonempty, href.2.2.1, href.2.2.2.1,
    href.retention, href.fullness'_le, hdrop, href.classHomogeneous, lam', hlam'0, hlam',
    hdense⟩)

/-- The floor-or-defect alternative for a nonempty shaded family.
The eccentric alternative `(P)` has the separate supplier
`Kakeya.ML2Core.htrial_of_eccentricData`. The parameter `h` is the potential
exponent used by the defect branch, and `lam` is the shading density.
The condition `S.Nonempty` ensures that a retained floor family can exist. -/
def FloorDataAtTrichotomy (β ϖ ε₁ η' h : ℝ) (gain dens : ℝ → ℝ)
    {C : ℝ≥0} {Kl cl : ℕ} (Λf : ℝ≥0∞)
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu) : Prop :=
  ∀ (S : Finset ι) (hS : S ⊆ u), S.Nonempty →
    ∀ (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
      (ht : ∀ i, (Z i).toTube = (T i).toTube) (hh : IsClassHomogeneousOn 𝒰 S) (lam : ℝ≥0),
      ∃ a b m : ℕ,
        RefinedFloorHypothesis (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ gain dens
            η' Λf ((𝒰.restrictOccupied hS hh).retube (funext ht)) a b m
        ∨ DefectBranchAt h Λf lam 𝒰 S Z

/-- Route (b) over the whole filter. -/
def FloorPayloadTrichotomy.{w} (β ϖ ε₁ η' h : ℝ) (gain dens : ℝ → ℝ)
    {C : ℝ≥0} {Kl cl : ℕ} (Λf : ℝ≥0 → ℝ≥0∞) : Prop :=
  ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0,
    ∀ {ι : Type w} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (Cu : ℝ≥0)
      (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu),
      FloorDataAtTrichotomy (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' h gain dens (Λf δ) 𝒰

end RouteB
/-! ### Consumers of the floor-or-defect alternative

`Kakeya.ML2Core.htrial_of_floorData` and
`Kakeya.ML2Core.trialSupplier_of_floorRoute` each split the disjunction.
The floor case uses `hF7`; the defect case uses
`trialOutcomeAtGain_of_defectBranch`. The latter consumer performs the same
argument under `filter_upwards`. -/

section RouteBConsumers

variable {ι : Type*} {δ Cu : ℝ≥0} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

open scoped Classical in
/-- **Route (b), consumer 2** — `Kakeya.ML2Core.trialSupplier_of_floorRoute` at the trichotomy
payload.  This is the endpoint the descent composes into the closure's third row. -/
theorem trialSupplier_of_floorRouteTrichotomy.{w} {β ϖ ε₁ ηin η' h : ℝ} {gain dens : ℝ → ℝ}
    {C : ℝ≥0} {Kl cl : ℕ} {Cu₀ : ℝ≥0} {Λf : ℝ≥0 → ℝ≥0∞}
    (hF7 : ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0,
      ∀ {ι : Type w} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (Cu : ℝ≥0) (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
        (a b m : ℕ) (S : Finset ι) (hS : S ⊆ u)
        (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (lam : ℝ≥0),
        S.Nonempty →
        ∀ (ht : ∀ i, (Z i).toTube = (T i).toTube),
        (∀ i, (Z i).shade ⊆ (T i).shade) →
        ∀ (hh : IsClassHomogeneousOn 𝒰 S),
        (∀ i ∈ S, (Z i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
        Kakeya.maxDensity S (fun i => (Z i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-ηin) →
        ML2Shaded.HasDenseShading lam S (fun i => (Z i).toShadedBody) →
        ML2Shaded.HasComparableDensities lam⁻¹ S (fun i => (Z i).toShadedBody) →
        (δ : ℝ≥0) ^ ηin / 2 ≤ lam →
        (u.card : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ)) →
        Cu ≤ Cu₀ →
        Λf δ * (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens
              + 2 * defectMargin β ϖ ε₁ gain dens)
            ≤ (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens
              + defectMargin β ϖ ε₁ gain dens) →
        RefinedFloorHypothesis (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ gain dens
          η' (Λf δ) ((𝒰.restrictOccupied hS hh).retube (funext ht)) a b m →
        ∀ Λ : ℝ≥0∞, TrialOutcomeAtGain h (β / 2 - defectMargin β ϖ ε₁ gain dens)
          (4 * ML2Spine.spineNu β ϖ ε₁ gain dens + defectMargin β ϖ ε₁ gain dens) β 𝒰 Λ lam S Z)
    (hΛf : ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0,
      Λf δ * (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens
            + 2 * defectMargin β ϖ ε₁ gain dens)
          ≤ (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens
            + defectMargin β ϖ ε₁ gain dens))
    (hfloor : FloorPayloadTrichotomy.{w} (C := C) (Kl := Kl) (cl := cl)
      β ϖ ε₁ η' h gain dens Λf) :
    TrialSupplier.{w} β ϖ ε₁ ηin h gain dens Cu₀ Λf := by
  filter_upwards [hF7, hΛf, hfloor] with δ hδ hΛ hfl
  intro ι u T Cu 𝒰 hCu hcard S hS Z lam hne ht hs hh hb hmx hd hc hl hcard'
  obtain ⟨a, b, m, hbr⟩ := hfl u T Cu 𝒰 S hS hne Z ht hh lam
  rcases hbr with hf | hD
  · exact hδ u T Cu 𝒰 a b m S hS Z lam hne ht hs hh hb hmx hd hc hl hcard' hCu hΛ hf (Λf δ)
  · exact trialOutcomeAtGain_of_defectBranch hD

end RouteBConsumers

/-! ### the first horn, upgraded from argument to proof -/

section RefinementLoss

/-- **The two dimensional tube-volume constants are ordered.**  A unit-radius tube in `E₃` has
`c₃ ≤ |T| ≤ C₃`, so `c₃ ≤ C₃`.  Taken at `δ = 1` so the `δ^{n-1}` factor is `1` and no cancellation
is needed. -/
theorem le_volume_c_le_volume_le_C :
    Tube.le_volume.c 3 ≤ Tube.volume_le.C 3 := by
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have h1 := Tube.le_volume (redTube (1 : ℝ≥0))
  have h2 := Tube.volume_le (E := EuclideanSpace ℝ (Fin 3)) (le_refl (1 : ℝ≥0))
    (redTube (1 : ℝ≥0))
  rw [hfr] at h1 h2
  simp only [ENNReal.coe_one, one_pow, mul_one] at h1 h2
  exact_mod_cast h1.trans h2

end RefinementLoss

end Kakeya.ML2Core

end

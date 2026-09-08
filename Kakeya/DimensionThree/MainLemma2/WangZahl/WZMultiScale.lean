/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.WangZahl.SigmaCalculus
public import Kakeya.DimensionThree.MainLemma2.WangZahl.WZBalancedCover
public import Kakeya.DimensionThree.MainLemma2.WangZahl.EToD
public import Kakeya.Density
public import Kakeya.Frostman
public import Kakeya.GridScale
public import Kakeya.Sticky
public import Kakeya.Tube.Basic
public import Kakeya.Uniform
public import Kakeya.MultiScaleFac.Bridge
public import Kakeya.MultiScaleLoss
public import Kakeya.DimensionThree.Plank.TubeParentPacking
public import Kakeya.StickyKakeya
public import Kakeya.StickyKakeya.Reindex
public import Kakeya.Multiplicity
public import Kakeya.Shading

/-!
The multi-scale analysis behind Wang--Zahl Proposition 1.7 (`improvingProp`).

Source: Wang--Zahl.

  * Proposition `improvingProp`                   (statement)
  * Section "Multi-scale analysis"                (proof)
  * Lemma `bigVolumeOrFineDivisions`             
  * Lemma `bigVolumeOrKatzTaoAllScales`          
  * Theorem `katzTaoEveryScaleStickyKakeyaThm`   
  * Proposition `refinedInductionOnScaleProp`    
  * Proposition `grainsDecomposition`            
  * Moves #1, #2, #3                             

This file carries out the *bookkeeping* half of the source's proof of
Proposition 1.7 and isolates the geometry into named leaves.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory

namespace Kakeya.WangZahl

noncomputable section

universe u

/-! ### `delta^t` as a density / error parameter -/

/-- `delta^t` as a nonnegative real; the density and error parameters of the
source are always of this shape.  It is *definitionally* the anonymous
constructor `⟨(delta:R)^t, _⟩` used in `Kakeya.WangZahl.AssertionD`. -/
def rpowNN (δ : ℝ≥0) (t : ℝ) : ℝ≥0 := δ ^ t

/-- `delta^t` is antitone in `t` for `delta <= 1`. -/
theorem rpowNN_le_rpowNN {δ : ℝ≥0} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {t t' : ℝ}
    (h : t' ≤ t) : rpowNN δ t ≤ rpowNN δ t' :=
  NNReal.coe_le_coe.mp (Real.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hδ0)
    (by exact_mod_cast hδ1) h)

/-- Density is monotone: a smaller density parameter is a weaker hypothesis. -/
theorem IsDense.mono {δ : ℝ≥0} {ι : Type u} {s : Finset ι}
    {T : ι → ShadedTube δ Space3} {lam lam' : ℝ≥0} (h : lam' ≤ lam)
    (hd : IsDense s T lam) : IsDense s T lam' :=
  le_trans (by gcongr) hd

/-! ### The hypothesis bundle shared by the source's multi-scale lemmas -/

/-- The hypotheses carried by every family appearing in Assertion `D` and in
the source's multi-scale lemmas: the pair
`(T, Y)_delta` is a tube-shading family, is `delta^eta` dense, and obeys the
Katz--Tao Convex Wolff and Frostman Slab Wolff Axioms with error at most
`delta^{-eta}`. -/
def WZAdmissible {δ : ℝ≥0} {ι : Type u} (s : Finset ι)
    (T : ι → ShadedTube δ Space3) (η : ℝ) : Prop :=
  IsTubeShadingFamily s T ∧
    IsDense s T (rpowNN δ η) ∧
      katzTaoConvexWolffConstant s T ≤ (δ : ℝ≥0∞) ^ (-η) ∧
        frostmanSlabWolffConstant s T ≤ (δ : ℝ≥0∞) ^ (-η)

/-- Admissibility is *antitone* in `eta`: a smaller `eta` is a stronger
hypothesis (denser shading, smaller Wolff errors), so it implies admissibility
at every larger `eta`.  This is the mechanism by which the source is free to
"choose `eta` sufficiently small". -/
theorem WZAdmissible.mono {δ : ℝ≥0} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {ι : Type u}
    {s : Finset ι} {T : ι → ShadedTube δ Space3} {η η' : ℝ} (hle : η' ≤ η)
    (h : WZAdmissible.{u} s T η') : WZAdmissible.{u} s T η := by
  obtain ⟨hfam, hdense, hm, hell⟩ := h
  have hδ0' : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hδ1' : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  have hdens := ENNReal.coe_le_coe.mpr (rpowNN_le_rpowNN hδ0 hδ1 hle)
  have hpow : (δ : ℝ≥0∞) ^ (-η') ≤ (δ : ℝ≥0∞) ^ (-η) :=
    ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hδ1) (by linarith)
  refine ⟨hfam, ?_, hm.trans hpow, hell.trans hpow⟩
  exact le_trans (by gcongr) hdense

/-! ### The two volume bounds appearing in the source's dichotomies -/

/-- Conclusion (A) of the source's multi-scale lemmas: the "large volume"
alternative, with a *gain* `alpha` over the exponent `omega` of Assertion `D`.
See Wang--Zahl, Proposition `grainsDecomposition` and Proposition
`refinedInductionOnScaleProp`, for the multiscale gain estimates. -/
def WZGainBound (σ ω α : ℝ) (κ : ℝ≥0) {δ : ℝ≥0} {ι : Type u}
    (s : Finset ι) (T : ι → ShadedTube δ Space3) : Prop :=
  (κ : ℝ≥0∞) * (δ : ℝ≥0∞) ^ (ω - α) * (s.card : ℝ≥0∞) * tubeVolume δ *
      (wzCurrency δ s.card) ^ (-σ) ≤
    volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody)

/-- The conclusion of Theorem `katzTaoEveryScaleStickyKakeyaThm` : the
union of the shadings has essentially full volume `(#T)|T|`, with only a
`delta^beta` loss.  This is the output of the sticky-Kakeya branch. -/
def WZFullBound (β : ℝ) (κ : ℝ≥0) {δ : ℝ≥0} {ι : Type u}
    (s : Finset ι) (T : ι → ShadedTube δ Space3) : Prop :=
  (κ : ℝ≥0∞) * (δ : ℝ≥0∞) ^ β * (s.card : ℝ≥0∞) * tubeVolume δ ≤
    volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody)

/-- The dichotomy actually used in the source's proof of Proposition 1.7
: every admissible family either satisfies the improved bound
of Conclusion (A) of Lemma `bigVolumeOrKatzTaoAllScales` , or --- via
Conclusion (B) of that lemma  fed into Theorem
`katzTaoEveryScaleStickyKakeyaThm`  applied with `eps = omega/2` ---
satisfies the near-full volume bound. -/
def WZDichotomy (σ ω α : ℝ) (κ : ℝ≥0) (η : ℝ) : Prop :=
  ∀ (δ : ℝ≥0), 0 < δ → δ ≤ 1 →
    ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3),
      WZAdmissible.{u} s T η →
      WZGainBound σ ω α κ s T ∨ WZFullBound (ω / 2) κ s T

/-- The dichotomy is monotone in `eta` in the same (antitone) sense as
`WZAdmissible`. -/
theorem WZDichotomy.mono {σ ω α : ℝ} {κ : ℝ≥0} {η η' : ℝ} (hle : η' ≤ η)
    (h : WZDichotomy.{u} σ ω α κ η) : WZDichotomy.{u} σ ω α κ η' := by
  intro δ hδ0 hδ1 ι s T hadm
  exact h δ hδ0 hδ1 s T (hadm.mono hδ0 hδ1 hle)

/-! ### Refinements, and the Katz--Tao Convex Wolff Axioms at every scale -/

/-- The total carrier mass of a tube family. -/
theorem sum_volume_carrier {δ : ℝ≥0} {ι : Type u} (s : Finset ι)
    (T : ι → ShadedTube δ Space3) :
    ∑ i ∈ s, volume (T i).carrier = (s.card : ℝ≥0∞) * tubeVolume δ := by
  simp [volume_carrier_eq_tubeVolume, Finset.sum_const, nsmul_eq_mul]

/-- The source's notion of a `t`-refinement : a sub-family, with shrunk
shadings, retaining a `t` fraction of the total shading mass. -/
def IsWZRefinement {δ : ℝ≥0} {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3)
    (s' : Finset ι) (T' : ι → ShadedTube δ Space3) (t : ℝ≥0) : Prop :=
  s' ⊆ s ∧ (∀ i ∈ s', (T' i).carrier = (T i).carrier) ∧
    (∀ i ∈ s', (T' i).shade ⊆ (T i).shade) ∧
      (t : ℝ≥0∞) * ∑ i ∈ s, volume (T i).shade ≤ ∑ i ∈ s', volume (T' i).shade

namespace IsWZRefinement

variable {δ : ℝ≥0} {ι : Type u} {s s' : Finset ι} {T T' : ι → ShadedTube δ Space3}
  {t lam : ℝ≥0}

/-- The source's refinement identity: a `t`-refinement of a `lam`-dense family is
`t * lam`-dense. -/
theorem isDense (href : IsWZRefinement s T s' T' t) (hdense : IsDense s T lam) :
    IsDense s' T' (t * lam) := by
  obtain ⟨hsub, _, _, hmass⟩ := href
  have hcard : (s'.card : ℝ≥0∞) ≤ (s.card : ℝ≥0∞) := by
    exact_mod_cast Finset.card_le_card hsub
  calc ((t * lam : ℝ≥0) : ℝ≥0∞) * ∑ i ∈ s', volume (T' i).carrier
      = (t : ℝ≥0∞) * ((lam : ℝ≥0∞) * ((s'.card : ℝ≥0∞) * tubeVolume δ)) := by
        rw [sum_volume_carrier]; push_cast; ring
    _ ≤ (t : ℝ≥0∞) * ((lam : ℝ≥0∞) * ((s.card : ℝ≥0∞) * tubeVolume δ)) := by gcongr
    _ = (t : ℝ≥0∞) * ((lam : ℝ≥0∞) * ∑ i ∈ s, volume (T i).carrier) := by
        rw [sum_volume_carrier]
    _ ≤ (t : ℝ≥0∞) * ∑ i ∈ s, volume (T i).shade := by gcongr; exact hdense
    _ ≤ ∑ i ∈ s', volume (T' i).shade := hmass

end IsWZRefinement

/-- Weakening the balance constant of a balanced partitioning cover. -/
def BalancedNodeCover.monoBalance {ι : Type u} {δ ρ : ℝ≥0} {s : Finset ι}
    {T : ι → Tube δ Space3} {K K' : ℝ≥0} (h : K ≤ K')
    (B : BalancedNodeCover (rho := ρ) s T K) : BalancedNodeCover (rho := ρ) s T K' :=
  { B with
    card_class_le := fun j hj => (B.card_class_le j hj).trans (by gcongr)
    le_card_class := fun j hj => (B.le_card_class j hj).trans (by gcongr) }

/-- Wang--Zahl every-scale Katz--Tao definition: the family `T` satisfies the *Katz--Tao Convex
Wolff Axioms at every scale with error `K`* if for every `rho_0` in `[delta,1]`
there is a scale `rho` in `[rho_0, K rho_0)` and a `K`-balanced partitioning
cover of `T` by `rho`-tubes whose own Katz--Tao constant is at most `K`.

The auxiliary shading `P` carries no information (`katzTaoConvexWolffConstant`
depends only on the carriers); it is present because the project's Katz--Tao
constant is defined for *shaded* tube families. -/
def KatzTaoEveryScale {δ : ℝ≥0} {ι : Type u} (s : Finset ι)
    (T : ι → ShadedTube δ Space3) (K : ℝ≥0) : Prop :=
  ∀ ρ₀ : ℝ≥0, δ ≤ ρ₀ → ρ₀ ≤ 1 →
    ∃ ρ : ℝ≥0, ρ₀ ≤ ρ ∧ ρ < K * ρ₀ ∧
      ∃ (P : ι → ShadedTube ρ Space3)
        (B : BalancedNodeCover (rho := ρ) s (fun i => (T i).toTube) K),
        (∀ j, B.parentTube j = (P j).toTube) ∧
          katzTaoConvexWolffConstant B.parent P ≤ (K : ℝ≥0∞)

theorem KatzTaoEveryScale.mono {δ : ℝ≥0} {ι : Type u} {s : Finset ι}
    {T : ι → ShadedTube δ Space3} {K K' : ℝ≥0} (hK : K ≤ K')
    (h : KatzTaoEveryScale.{u} s T K) : KatzTaoEveryScale.{u} s T K' := by
  intro ρ₀ hρδ hρ1
  obtain ⟨ρ, hρ0, hρK, P, B, hPB, hCKT⟩ := h ρ₀ hρδ hρ1
  refine ⟨ρ, hρ0, lt_of_lt_of_le hρK (by gcongr), P, B.monoBalance hK, hPB, ?_⟩
  exact hCKT.trans (by exact_mod_cast hK)

/-! ### From the source's every-scale hypothesis to the project's node reading -/

/-! ### The two geometric leaves -/

/-! ### The packing cap supplied by the in-tube count -/

/-! ### A defect in the source's final display -/

/-! ### The gain bookkeeping: from the dichotomy to Assertion `D` -/

/-! ### Assembling the dichotomy from the two leaves -/

end

end Kakeya.WangZahl

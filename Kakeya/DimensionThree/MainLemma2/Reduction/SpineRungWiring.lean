/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineMiddleProducer

/-!
# The rung-level re-cut of the branch-(ii) wiring

`Kakeya.ML2Core.geometricCoreAt_of_middleFactor` reduces the geometric core to a middle-factor
hypothesis whose binder block is satisfiable by a single fully shaded tube
(`Kakeya.ML2Core.not_middleFactor_hypothesis`), so the theorem is unusable.  Two things in that
block are responsible, and both are repaired here.

* **The window's rung function was abstract.**  The block quantified over an arbitrary
  `ηl : ℕ → ℝ` with only `0 ≤ ηl m ≤ ε₁/25`, so the refuting model could take `ηl ≡ 0`, at which
  the window's density lower bound `IsKatzTaoDividingWindow.le_window_maxDensity` — GWZ's
  `tildeDeltaLargeDeltamax`, the source of the count clause — says nothing.  The block below pins
  the window to the **constructed** spine `Kakeya.ML2Spine.spineRung`, whose rungs are positive
  (`Kakeya.ML2Core.two_le_card_nodesUnder_of_spineWindow` is the consequence: no coarse
  node of such a window has a one-node middle family).
* **The exponents were fixed before the window.**  `Kakeya.ML2Core.dichotomy_of_windowFactors`
  takes `εf, gm, εc` as reals, so the coarse cost `ε + κ + η_m` had to be flattened to `ε₁/25`
  while the middle gain was asked for uniformly; `Kakeya.ML2Core.spineRung_middle_gain_lt_demand`
  shows the two never meet.  `Kakeya.ML2Core.dichotomy_of_rungFactors` reads both at the window's
  own rung `X = η_m`, where `Kakeya.ML2Core.rung_budget_closes_of_overhead_le_four` closes.

The third change is the one that makes the arithmetic *satisfiable*: the input density exponent
of the dichotomy is decoupled from the spine's bottom rung.  The two Katz--Tao factors are read at
an accuracy `ε = ν/20`, and their density exponents `η_f, η_c` are then whatever `K_KT(β)`
returns — possibly far below `ν`.  The fullness floor the window branch hands them is
`λ ≥ δ^{η_in}/2` where `η_in` is the *input* density exponent, so choosing
`η_in ≤ min η_f η_c / 2` is a choice about the statement's density slot (which
`Kakeya.ML2Assembly.GeometricCoreAt` leaves free), not about the spine.  The existing wiring made
`ν` small instead, by shrinking `ε₁`, which shrinks the middle gain with it.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody
open Tube ShadedTube

namespace Kakeya.ML2Core

universe u

/-! ## The window package with the constructed spine pinned

`Kakeya.ML2Inputs.exists_shaded_dividingScales_of_dichotomyHypotheses` builds its ladder from
`Kakeya.ML2Inputs.exists_dividingScalesLadder`, which *is* the constructed spine, but its statement
hides that behind `∃ η`.  The consumers below need the rungs by name, so the same proof is run with
the spine written out. -/

section SpinePackage

end SpinePackage

/-! ## Branch (i) at every small Katz--Tao exponent, on the spine, at input density `η_in` -/

section DichotomySpine

end DichotomySpine

/-! ## The window branch, re-cut at the rung -/

section RungPackage

open Classical in
/-- **The window branch, wired at the rung, with the window read as
`IsKatzTaoDividingWindowLevels`.**
The level twin of `Kakeya.ML2Core.dichotomy_of_rungFactors` (§2.8): the package `hpkg` hands
the twin window and the factor hypothesis `hfac` is asked only at twin windows, so a producer that
needs the source's level clause can discharge it.  Statement and proof are otherwise the existing
ones, verbatim; the seam and gain lemmas read the parent through `toIsKatzTaoDividingWindow`.

The existing docstring follows.

`Kakeya.ML2Core.dichotomy_of_windowFactors` with the three changes the module docstring lists.

* The package `hpkg` is on the constructed spine and at the input density exponent `η_in ≤ ν`
  (`Kakeya.ML2Core.exists_dichotomyLeft_or_window_spine`), so the dense-shading floor it hands the
  factors is `δ^{η_in}/2`.
* The factor exponents are read **at the window's rung** `X = η_m`: the middle gain is `gm X`, a
  function of the rung, and the coarse cost is `εc + X` — the `+ ηl m` of
  `Kakeya.ML2Reduction.exists_coarse_factor_complete`'s own binder — instead of the flattened
  `ε₁/25`.  The budget `hexp` is then a statement about every rung `X ≥ ν`, and it is checked
  *inside* the window's scope.
* The pushback overhead is `2ν + 2η_in + θ₁ + θ₂` instead of `6ν`: the two movable terms —
  `StickyKakeya.totalLoss` and the seam constants — sit at free thresholds `θ₁, θ₂`, and the two
  `λ⁻¹`'s are read at the input density `η_in`.  Only the package's cardinality loss `δ^{-2ν}`
  stays at `ν`, being a clause of the package.  So the internal gain `g` the split has to
  produce is `g = 6ν + θ₁ + θ₂ + 2η_in`, against the target `4ν`.

The middle factor's exponent is a *function* `gm` of the rung so that a producer may hand in
`47 X/5` (`Kakeya.ML2Core.middle_factor_of_edNodes_sharp` transported at the window's own
separation exponent, `Kakeya.ML2Core.ambient_sharp_gain_ge`) or anything else that meets `hexp`. -/
theorem dichotomy_of_rungFactors_levels
    {β ϖ : ℝ} {gain dens : ℝ → ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    {ε₁ : ℝ} (hε₁ : 0 < ε₁)
    {ηin : ℝ} (hηinν : ηin ≤ ML2Spine.spineNu β ϖ ε₁ gain dens)
    {C : ℝ≥0} {Kl cl : ℕ} (hC : 1 ≤ C)
    (hpkg : ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0,
      0 < δ ∧ δ ≤ 1 ∧
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ℝ≥0∞) ^ (-ηin)) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ ηin →
        (δ : ℝ)⁻¹ ≤ (s.card : ℝ) →
        s.Nonempty ∧
        (ML2Shading.DichotomyLeft (β / 2) s T
          ∨ ∃ u' ⊆ s, ∃ W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)), ∃ lam : ℝ≥0,
              δ ^ ηin / 2 ≤ lam ∧ 0 < lam ∧ u'.Nonempty ∧
              (∀ i, (W i).toTube = (T i).toTube) ∧
              (∀ i, (W i).shade ⊆ (T i).shade) ∧
              ML2Shaded.HasDenseShading lam u' (fun i ↦ (T i).toShadedBody) ∧
              ML2Shaded.HasComparableDensities lam⁻¹ u'
                  (fun i ↦ (T i).toShadedBody) ∧
              (lam : ℝ≥0∞)
                    * (Tube.le_volume.c
                        (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞)
                    * (∑ i ∈ s, volume (T i).shade)
                  ≤ 2 * (ENNReal.ofReal ((δ : ℝ) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens
                          + ML2Spine.spineNu β ϖ ε₁ gain dens)))
                      * StickyKakeya.totalLoss C Kl cl δ)
                    * (Tube.volume_le.C
                        (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞)
                    * ∑ i ∈ u', volume (T i).shade ∧
              (∑ i ∈ u', volume (T i).shade)
                  ≤ ((Nat.log 2 s.card + 1 : ℕ) : ℝ≥0∞) ^ (2 * ssfGridLen δ + 2)
                    * ∑ i ∈ u', volume (W i).shade ∧
              volume (⋃ i ∈ u', (W i).shade) ≤ volume (⋃ i ∈ s, (T i).shade) ∧
              (lam : ℝ≥0∞)
                  ≤ ((Nat.log 2 s.card + 1 : ℕ) : ℝ≥0∞) ^ (2 * ssfGridLen δ + 2)
                    * ShadedBody.fullness' u' (fun i ↦ (W i).toShadedBody) ∧
              ∃ 𝒲 : ShadedUniformTubeSet u' W (ssfGridLen δ) (max C 4),
                ∃ a b m : ℕ, ML2Reduction.IsKatzTaoDividingWindowLevels 𝒲.tubeUniform
                    ((C : ℝ≥0∞) * StickyKakeya.totalLoss C Kl cl δ)
                    (ML2Spine.spineRung β ϖ ε₁ gain dens) (ML2Spine.spineDiv ϖ ε₁)
                    (ML2Spine.spineCount ϖ ε₁) a b m))
    {gm : ℝ → ℝ} {εf εc κc κ' θ₁ θ₂ : ℝ}
    (hκc : 0 < κc) (hκ' : 0 < κ') (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂)
    (hexp : ∀ X : ℝ, ML2Spine.spineNu β ϖ ε₁ gain dens ≤ X →
      6 * ML2Spine.spineNu β ϖ ε₁ gain dens + θ₁ + θ₂ + 2 * ηin
        ≤ gm X - εf - (εc + X) - κ')
    (hfac : ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0,
      ∀ {ι : Type u} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (Cu lam :
          ℝ≥0)
        (𝒰 : Tube.UniformTubeSet u (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu)
        (Cstar : ℝ≥0∞) (a b m : ℕ),
        ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰 Cstar (ML2Spine.spineRung β ϖ ε₁ gain dens)
          (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m →
      ∀ (v : (EuclideanSpace ℝ (Fin 3))) (t₀ t₁ : Finset ι),
        t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain b →
        (∀ j ∈ t₁, ((𝒰.cover.tube b j).translate v).carrier ⊆ Metric.closedBall (0 :
            (EuclideanSpace ℝ (Fin 3))) 1) →
        (∀ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), ((T i).translate v).carrier ⊆
            Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 1) →
        (a ≠ 0 → t₀ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain a) →
        (a ≠ 0 → ∀ j ∈ t₁, ML2Reduction.coarseNode 𝒰.cover.toChain a b j ∈ t₀) →
        (a ≠ 0 → ∀ k ∈ t₀,
          ((𝒰.cover.tube a k).translate v).carrier ⊆ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin
              3))) 1) →
        (∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 1) →
        u.Nonempty →
        Kakeya.maxDensity u (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-ηin) →
        ML2Shaded.HasDenseShading lam u (fun i ↦ (T i).toShadedBody) →
        ML2Shaded.HasComparableDensities lam⁻¹ u (fun i ↦ (T i).toShadedBody) →
        (δ : ℝ≥0) ^ ηin / 2 ≤ lam →
        (u.card : ℝ≥0) ≤ δ ^ (-(4 : ℝ)) →
        Cstar ≤ (δ : ℝ≥0∞) ^ (-κc) →
        Cu ≤ max C 4 →
        0 < ∑ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), volume (T i).shade →
        δ ≤ Tube.gridScale δ (Tube.ssfGridLen δ) b →
        Tube.gridScale δ (Tube.ssfGridLen δ) b ≤ Tube.gridScale δ (Tube.ssfGridLen δ) a →
        Tube.gridScale δ (Tube.ssfGridLen δ) a ≤ 1 →
        ∃ (tτ' tθ' : Finset ι)
        (Yτ' : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b) (EuclideanSpace ℝ (Fin 3)))
        (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a) (EuclideanSpace ℝ (Fin 3)))
        (Y' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (jτ jθ : ι),
        tτ' ⊆ t₁ ∧ tθ' ⊆ 𝒰.cover.indexSet a ∧ jτ ∈ t₁ ∧ jθ ∈ tθ' ∧ tτ'.Nonempty ∧
        ShadedBody.multiplicity ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) (fun i ↦ (T
            i).toShadedBody)
            ≤ ((ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) ({i ∈ u
                | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ *
                  ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) tτ'.card
                    (Tube.gridScale δ (Tube.ssfGridLen δ) b) : ℝ≥0) : ℝ≥0∞)
              * ShadedBody.multiplicity ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
                  𝒰.cover.assign b i = jτ} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
              * ShadedBody.multiplicity ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j
                  = jθ} : Finset ι) (fun j ↦ (Yτ' j).toShadedBody)
              * ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody) ∧
        ShadedBody.multiplicity ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
            𝒰.cover.assign b i = jτ} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
            ≤ (δ : ℝ≥0∞) ^ (-(εf)) * ((({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
                𝒰.cover.assign b i = jτ} : Finset ι)).card : ℝ≥0∞) ^ β ∧
        ShadedBody.multiplicity ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} :
            Finset ι) (fun j ↦ (Yτ' j).toShadedBody)
            ≤ (δ : ℝ≥0∞) ^ (gm (ML2Spine.spineRung β ϖ ε₁ gain dens m))
              * ((({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} : Finset
                  ι)).card : ℝ≥0∞) ^ β ∧
        ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody)
            ≤ (δ : ℝ≥0∞) ^ (-(εc + ML2Spine.spineRung β ϖ ε₁ gain dens m))
              * ((tθ'.card : ℕ) : ℝ≥0∞) ^ β) :
    ML2Assembly.Dichotomy.{u} β (β / 2) (4 * ML2Spine.spineNu β ϖ ε₁ gain dens) ηin := by
  classical
  have hsp := ML2Spine.spineRung_isSpine hβ0 hβ1 hϖ hε₁ hgain hdens
  have hν0 : 0 < ML2Spine.spineNu β ϖ ε₁ gain dens :=
    ML2Spine.spineNu_pos hβ0 hϖ hε₁ hgain hdens
  have hν1 : ML2Spine.spineNu β ϖ ε₁ gain dens ≤ 1 := by
    have := ML2Inputs.spineNu_le_div_48000 hβ0 hβ1 hϖ hε₁ hgain hdens
    linarith
  have hηin1 : ηin ≤ 1 := hηinν.trans hν1
  refine dichotomy_of_dichotomyLeft_or_gain ?_
  -- the two seams, and the thresholds, all chosen before the scale
  obtain ⟨M₁, hM₁0, hseam₁⟩ := exists_windowSeam.{u} (E := EuclideanSpace ℝ (Fin 3))
  obtain ⟨M₂, hM₂0, hseam₂⟩ := exists_coarseWindowSeam.{u} (E := EuclideanSpace ℝ (Fin 3))
  set Mseam : ℕ := max M₁ M₂ with hMseam
  have hcc0 : 0 < Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) :=
    Tube.le_volume.c_pos _
  have hCuu1 : (1 : ℝ≥0) ≤ max C 4 := le_trans hC (le_max_left _ _)
  obtain ⟨d1, hd10, hd1⟩ :=
    ML2Reduction.exists_threshold_coe_const_le_rpow_neg
      (C := max 1 (8 * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) ^ 2 *
        ((Mseam : ℝ≥0) * max C 4 * max C 4) /
        (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) ^ 2))
      (le_max_left _ _) (κ := θ₂) hθ₂
  obtain ⟨Cε, hCε⟩ :=
    ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C_leApprox
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) (κ' / 20) (by positivity)
  obtain ⟨d2, hd20, hd2⟩ :=
    ML2Reduction.exists_threshold_const_le_rpow_neg
      (C := max 1 (Cε ^ 2 * (max C 4) ^ 5)) (le_max_left _ _)
      (κ := κ' / 2) (by positivity)
  obtain ⟨dT, hdT0, hdT1, hdT⟩ :=
    StickyKakeya.exists_threshold_totalLoss_le C hC Kl cl θ₁ hθ₁
  obtain ⟨dL, hdL0, hdL1, hdL⟩ := exists_threshold_two_mul_ssfGridLen_le_log
  obtain ⟨d3, hd30, hd3⟩ :=
    ML2Reduction.exists_threshold_coe_const_le_rpow_neg (C := C) hC (κ := κc / 2)
      (by positivity)
  obtain ⟨dT', hdT'0, hdT'1, hdT'⟩ :=
    StickyKakeya.exists_threshold_totalLoss_le C hC Kl cl (κc / 2) (by positivity)
  filter_upwards [hpkg, hfac, ML2Assembly.eventually_card_thresholds,
    Ioc_mem_nhdsGT hd10, Ioc_mem_nhdsGT hd20, Ioc_mem_nhdsGT hdT0, Ioc_mem_nhdsGT hdL0,
    Ioc_mem_nhdsGT hd30, Ioc_mem_nhdsGT hdT'0]
    with δ hpkgδ hfacδ hthr hm1 hm2 hmT hmL hm3 hmT'
  obtain ⟨hδ0, hδ1, hbody⟩ := hpkgδ
  obtain ⟨-, -, hδC⟩ := hthr
  intro ι s T hball hKTs hfull hcard
  rcases (hbody s T hball hKTs hfull hcard).2 with hleft | hwindow
  · exact Or.inl hleft
  refine Or.inr ?_
  obtain ⟨u', hu's, W, lam, hlamlow, hlam0, hu'ne, htube, hshade, hdenseu, hcompu,
    hmassloss, hpoly, hunion, hfullpoly, 𝒲, aa, bb, mm, hwinW⟩ := hwindow
  -- the hierarchy, read on the family whose masses the dichotomy states
  obtain ⟨𝒰, hwin⟩ : ∃ 𝒰 : Tube.UniformTubeSet u' (fun i ↦ (T i).toTube)
      (Tube.ssfGridLen δ) (max C 4),
      ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰
        ((C : ℝ≥0∞) * StickyKakeya.totalLoss C Kl cl δ)
        (ML2Spine.spineRung β ϖ ε₁ gain dens) (ML2Spine.spineDiv ϖ ε₁)
        (ML2Spine.spineCount ϖ ε₁) aa bb mm := by
    have hfun : (fun i ↦ (W i).toTube) = (fun i ↦ (T i).toTube) := funext htube
    exact hfun ▸ ⟨𝒲.tubeUniform, hwinW⟩
  have hwinP := hwin.toIsKatzTaoDividingWindow
  -- the crude cardinality ceiling
  have hcard4 : (s.card : ℝ) ≤ (δ : ℝ) ^ (-4 : ℝ) :=
    ML2Assembly.card_le_rpow_neg_four hδ0 hδ1 hδC s T hball hηin1 hKTs
  have hcardu : (u'.card : ℝ≥0) ≤ δ ^ (-(4 : ℝ)) := by
    have h1 : ((u'.card : ℕ) : ℝ) ≤ (δ : ℝ) ^ (-4 : ℝ) := by
      refine le_trans ?_ hcard4
      exact_mod_cast Nat.cast_le.mpr (Finset.card_le_card hu's)
    have h2 : (((δ ^ (-(4 : ℝ)) : ℝ≥0)) : ℝ) = (δ : ℝ) ^ (-4 : ℝ) := by
      rw [NNReal.coe_rpow]
    rw [← NNReal.coe_le_coe, h2]
    exact_mod_cast h1
  -- the seam
  have hballu' : ∀ i ∈ u', (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    fun i hi ↦ hball i (hu's hi)
  obtain ⟨v, t₀, t₁, ht₀, ht₁, hballt₀, hballt, hballs, hcn, hcardseam, hδτ, hτθ, hθ1⟩ :
      ∃ (v : EuclideanSpace ℝ (Fin 3)) (t₀ t₁ : Finset ι),
        (aa ≠ 0 → t₀ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain aa) ∧
        t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain bb ∧
        (aa ≠ 0 → ∀ k ∈ t₀, ((𝒰.cover.tube aa k).translate v).carrier
          ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) ∧
        (∀ j ∈ t₁, ((𝒰.cover.tube bb j).translate v).carrier
          ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) ∧
        (∀ i ∈ ({i ∈ u' | 𝒰.cover.assign bb i ∈ t₁} : Finset ι),
          ((T i).translate v).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) ∧
        (aa ≠ 0 → ∀ j ∈ t₁, ML2Reduction.coarseNode 𝒰.cover.toChain aa bb j ∈ t₀) ∧
        (u'.card : ℝ≥0) ≤ (Mseam : ℝ≥0) * max C 4 * max C 4
          * ((({i ∈ u' | 𝒰.cover.assign bb i ∈ t₁} : Finset ι)).card : ℝ≥0) ∧
        δ ≤ Tube.gridScale δ (Tube.ssfGridLen δ) bb ∧
        Tube.gridScale δ (Tube.ssfGridLen δ) bb ≤ Tube.gridScale δ (Tube.ssfGridLen δ) aa ∧
        Tube.gridScale δ (Tube.ssfGridLen δ) aa ≤ 1 := by
    have hMcast : ∀ n : ℕ, n ≤ Mseam → ((n : ℝ≥0) ≤ (Mseam : ℝ≥0)) := by
      intro n hn; exact_mod_cast Nat.cast_le.mpr hn
    rcases eq_or_ne aa 0 with ha0 | ha0
    · obtain ⟨v, t₁, ht₁, hballt, hballs, hcardseam, hδτ, hτθ, hθ1⟩ :=
        hseam₁ 𝒰 hδ0 hδ1 (hdL δ hδ0 hmL.2) hwinP hballu'
      refine ⟨v, ∅, t₁, fun h ↦ absurd ha0 h, ht₁, fun h ↦ absurd ha0 h, hballt, hballs,
        fun h ↦ absurd ha0 h, ?_, hδτ, hτθ, hθ1⟩
      refine hcardseam.trans (mul_le_mul' (mul_le_mul' (mul_le_mul'
        (hMcast M₁ (le_max_left _ _)) le_rfl) le_rfl) le_rfl)
    · obtain ⟨v, t₀, t₁, ht₀, ht₁, hballt₀, hballt, hballs, hcn, hcardseam, hδτ, hτθ, hθ1⟩ :=
        hseam₂ 𝒰 hδ0 hδ1 (Nat.one_le_iff_ne_zero.mpr ha0) (hdL δ hδ0 hmL.2) hwinP hballu'
      refine ⟨v, t₀, t₁, fun _ ↦ ht₀, ht₁, fun _ ↦ hballt₀, hballt, hballs, fun _ ↦ hcn,
        ?_, hδτ, hτθ, hθ1⟩
      refine hcardseam.trans (mul_le_mul' (mul_le_mul' (mul_le_mul'
        (hMcast M₂ (le_max_right _ _)) le_rfl) le_rfl) le_rfl)
  -- mass positivity, transported across both discards
  have hmass0 : 0 < ∑ i ∈ s, volume (T i).shade := by
    rw [pos_iff_ne_zero]
    intro h
    have hf : ((ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) : ℝ≥0) : ℝ≥0∞) = 0 := by
      rw [ShadedBody.fullness_def, h, ENNReal.zero_div]
    have hf0 : ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) = 0 := by exact_mod_cast hf
    have hpow : (0 : ℝ≥0) < δ ^ ηin := NNReal.rpow_pos hδ0
    rw [ge_iff_le, hf0] at hfull
    exact absurd hfull (not_le.mpr hpow)
  have hcc0E : ((Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0)
      : ℝ≥0∞) ≠ 0 := by
    simpa using (Tube.le_volume.c_pos (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))).ne'
  have hlam0E : ((lam : ℝ≥0) : ℝ≥0∞) ≠ 0 := by simpa using hlam0.ne'
  have hmassu' : 0 < ∑ i ∈ u', volume (T i).shade := by
    rw [pos_iff_ne_zero]
    intro h
    rw [h, mul_zero] at hmassloss
    have h0 : (lam : ℝ≥0∞)
        * ((Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0) : ℝ≥0∞)
        * (∑ i ∈ s, volume (T i).shade) = 0 := le_antisymm hmassloss (by simp)
    rcases mul_eq_zero.mp h0 with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact hlam0E h2
      · exact hcc0E h2
    · exact hmass0.ne' h1
  have hmasspos : 0 < ∑ i ∈ ({i ∈ u' | 𝒰.cover.assign bb i ∈ t₁} : Finset ι),
      volume (T i).shade := by
    have hret := sum_shade_le_of_node_subfamily (E := EuclideanSpace ℝ (Fin 3)) hδ1
      (Finset.filter_subset (fun i ↦ 𝒰.cover.assign bb i ∈ t₁) u') hdenseu hcardseam
    rw [pos_iff_ne_zero]
    intro h
    rw [h, mul_zero] at hret
    have h0 : (lam : ℝ≥0∞)
        * ((Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0) : ℝ≥0∞)
        * (∑ i ∈ u', volume (T i).shade) = 0 := le_antisymm hret (by simp)
    rcases mul_eq_zero.mp h0 with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact hlam0E h2
      · exact hcc0E h2
    · exact hmassu'.ne' h1
  -- the two-scale loss, absorbed at `κ'`
  have hσb1 : Tube.gridScale δ (Tube.ssfGridLen δ) bb ≤ 1 := le_trans hτθ hθ1
  have hCuu5one : (1 : ℝ≥0) ≤ (max C 4 : ℝ≥0) ^ 5 := one_le_pow₀ hCuu1
  have hCuu5ne : ((max C 4 : ℝ≥0) ^ 5) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hCuu5one)
  have hLfinal : ∀ n₁ n₂ : ℕ, 0 < n₁ → 0 < n₂ →
      (n₁ : ℝ≥0) ≤ δ ^ (-(4 : ℝ)) → (n₂ : ℝ≥0) ≤ δ ^ (-(4 : ℝ)) →
      ((ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) n₁ δ *
          ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) n₂
            (Tube.gridScale δ (Tube.ssfGridLen δ) bb) : ℝ≥0) : ℝ≥0∞)
        * ((((max C 4 : ℝ≥0) ^ 5 : ℝ≥0) : ℝ≥0∞)) ^ β ≤ (δ : ℝ≥0∞) ^ (-κ') := by
    intro n₁ n₂ hn1p hn2p hn1 hn2
    have hprod := spineScaleLoss_prod_le hδ0 hδ1 hδτ hσb1 hn1p hn2p hn1 hn2
      (ε := κ' / 20) (by positivity) hCε
    have hβpow : ((max C 4 : ℝ≥0) ^ 5) ^ β ≤ (max C 4 : ℝ≥0) ^ 5 := by
      calc ((max C 4 : ℝ≥0) ^ 5) ^ β ≤ ((max C 4 : ℝ≥0) ^ 5) ^ (1 : ℝ) :=
            NNReal.rpow_le_rpow_of_exponent_le hCuu5one hβ1
        _ = (max C 4 : ℝ≥0) ^ 5 := by rw [NNReal.rpow_one]
    rw [← ENNReal.coe_rpow_of_ne_zero hCuu5ne, ← ENNReal.coe_mul,
      ← ENNReal.coe_rpow_of_ne_zero hδ0.ne', ENNReal.coe_le_coe]
    calc (ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) n₁ δ *
            ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) n₂
              (Tube.gridScale δ (Tube.ssfGridLen δ) bb))
          * (((max C 4 : ℝ≥0) ^ 5) ^ β)
        ≤ (Cε ^ 2 * δ ^ (-(10 * (κ' / 20)))) * ((max C 4 : ℝ≥0) ^ 5) :=
          mul_le_mul' hprod hβpow
      _ = (Cε ^ 2 * (max C 4 : ℝ≥0) ^ 5) * δ ^ (-(κ' / 2)) := by
          rw [show (10 : ℝ) * (κ' / 20) = κ' / 2 by ring]; ring
      _ ≤ δ ^ (-(κ' / 2)) * δ ^ (-(κ' / 2)) := by
          gcongr
          exact le_trans (le_max_right _ _) (hd2 δ hδ0 hm2.2)
      _ = δ ^ (-κ') := by
          rw [← NNReal.rpow_add hδ0.ne']
          congr 1
          ring
  -- the pushback ledger, absorbed: `g = 6ν + θ₁ + θ₂ + 2η_in` against the target `4ν`
  have hlamE : (δ : ℝ≥0∞) ^ ηin ≤ 2 * (lam : ℝ≥0∞) := by
    have hnn : (δ : ℝ≥0) ^ ηin ≤ 2 * lam := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ≥0) < 2)] at hlamlow
      calc (δ : ℝ≥0) ^ ηin ≤ lam * 2 := hlamlow
        _ = 2 * lam := by ring
    calc (δ : ℝ≥0∞) ^ ηin = (((δ : ℝ≥0) ^ ηin : ℝ≥0) : ℝ≥0∞) :=
          (ENNReal.coe_rpow_of_ne_zero hδ0.ne' _).symm
      _ ≤ ((2 * lam : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_le_coe.mpr hnn
      _ = 2 * (lam : ℝ≥0∞) := by push_cast; ring
  have habs : (2 * (ENNReal.ofReal ((δ : ℝ) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens
            + ML2Spine.spineNu β ϖ ε₁ gain dens)))
          * StickyKakeya.totalLoss C Kl cl δ)
        * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞))
        * ((((Mseam : ℝ≥0) * max C 4 * max C 4 : ℝ≥0) : ℝ≥0∞)
          * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞))
        * (δ : ℝ≥0∞) ^ (6 * ML2Spine.spineNu β ϖ ε₁ gain dens + θ₁ + θ₂ + 2 * ηin)
      ≤ ((lam : ℝ≥0∞)
          * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞))
        * ((lam : ℝ≥0∞)
          * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞))
        * (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens) := by
    have hδEne : (δ : ℝ≥0∞) ≠ 0 := by simpa using hδ0.ne'
    have hδEtop : (δ : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := ENNReal.coe_ne_top
    have hA : ENNReal.ofReal ((δ : ℝ) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens
          + ML2Spine.spineNu β ϖ ε₁ gain dens)))
        = (δ : ℝ≥0∞) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens
          + ML2Spine.spineNu β ϖ ε₁ gain dens)) :=
      ofReal_rpow_coe hδ0 _
    have hT : StickyKakeya.totalLoss C Kl cl δ ≤ (δ : ℝ≥0∞) ^ (-θ₁) := by
      rw [← ofReal_rpow_coe hδ0]
      exact hdT hδ0 hmT.2
    have hcc2ne : (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) ^ 2 ≠ 0 :=
      pow_ne_zero _ hcc0.ne'
    have hconstNN : (8 : ℝ≥0)
          * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) ^ 2
          * ((Mseam : ℝ≥0) * max C 4 * max C 4)
        ≤ (max 1 (8 * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) ^ 2 *
            ((Mseam : ℝ≥0) * max C 4 * max C 4) /
            (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) ^ 2))
          * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) ^ 2 := by
      refine le_trans (le_of_eq ?_) (mul_le_mul' (le_max_right _ _) le_rfl)
      rw [div_mul_cancel₀ _ hcc2ne]
    have hconst : (8 : ℝ≥0∞)
          * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞) ^ 2
          * (((Mseam : ℝ≥0) * max C 4 * max C 4 : ℝ≥0) : ℝ≥0∞)
        ≤ (δ : ℝ≥0∞) ^ (-θ₂)
          * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞) ^ 2 := by
      have h1 : ((8 * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) ^ 2
            * ((Mseam : ℝ≥0) * max C 4 * max C 4) : ℝ≥0) : ℝ≥0∞)
          ≤ (((max 1 (8 * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) ^ 2 *
              ((Mseam : ℝ≥0) * max C 4 * max C 4) /
              (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) ^ 2))
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) ^ 2
              : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_le_coe.mpr hconstNN
      have h2 := hd1 δ hδ0 hm1.2
      push_cast at h1 ⊢
      exact h1.trans (mul_le_mul' h2 le_rfl)
    have e1 : (δ : ℝ≥0∞) ^ (-θ₂) * ((δ : ℝ≥0∞) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens
            + ML2Spine.spineNu β ϖ ε₁ gain dens))
          * (δ : ℝ≥0∞) ^ (-θ₁)
          * (δ : ℝ≥0∞) ^ (6 * ML2Spine.spineNu β ϖ ε₁ gain dens + θ₁ + θ₂ + 2 * ηin))
        = (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens + 2 * ηin) := by
      rw [← ENNReal.rpow_add _ _ hδEne hδEtop, ← ENNReal.rpow_add _ _ hδEne hδEtop,
        ← ENNReal.rpow_add _ _ hδEne hδEtop]
      congr 1
      ring
    have e2 : (δ : ℝ≥0∞) ^ ηin * (δ : ℝ≥0∞) ^ ηin
          * (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens)
        = (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens + 2 * ηin) := by
      rw [← ENNReal.rpow_add _ _ hδEne hδEtop, ← ENNReal.rpow_add _ _ hδEne hδEtop]
      congr 1
      ring
    refine (ENNReal.mul_le_mul_iff_left (by norm_num : (4 : ℝ≥0∞) ≠ 0)
      (by norm_num : (4 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞))).mp ?_
    calc ((2 * (ENNReal.ofReal ((δ : ℝ) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens
                + ML2Spine.spineNu β ϖ ε₁ gain dens)))
              * StickyKakeya.totalLoss C Kl cl δ)
            * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞))
            * ((((Mseam : ℝ≥0) * max C 4 * max C 4 : ℝ≥0) : ℝ≥0∞)
              * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞))
            * (δ : ℝ≥0∞) ^ (6 * ML2Spine.spineNu β ϖ ε₁ gain dens + θ₁ + θ₂ + 2 * ηin)) * 4
        ≤ ((2 * ((δ : ℝ≥0∞) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens
                + ML2Spine.spineNu β ϖ ε₁ gain dens)) * (δ : ℝ≥0∞) ^ (-θ₁))
            * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞))
            * ((((Mseam : ℝ≥0) * max C 4 * max C 4 : ℝ≥0) : ℝ≥0∞)
              * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞))
            * (δ : ℝ≥0∞) ^ (6 * ML2Spine.spineNu β ϖ ε₁ gain dens + θ₁ + θ₂ + 2 * ηin)) * 4 := by
          rw [hA]; gcongr
      _ = ((8 : ℝ≥0∞)
            * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞) ^ 2
            * (((Mseam : ℝ≥0) * max C 4 * max C 4 : ℝ≥0) : ℝ≥0∞))
          * ((δ : ℝ≥0∞) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens
                + ML2Spine.spineNu β ϖ ε₁ gain dens)) * (δ : ℝ≥0∞) ^ (-θ₁)
              * (δ : ℝ≥0∞) ^ (6 * ML2Spine.spineNu β ϖ ε₁ gain dens + θ₁ + θ₂ + 2 * ηin)) := by
          ring
      _ ≤ ((δ : ℝ≥0∞) ^ (-θ₂)
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞) ^ 2)
          * ((δ : ℝ≥0∞) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens
                + ML2Spine.spineNu β ϖ ε₁ gain dens)) * (δ : ℝ≥0∞) ^ (-θ₁)
              * (δ : ℝ≥0∞) ^ (6 * ML2Spine.spineNu β ϖ ε₁ gain dens + θ₁ + θ₂ + 2 * ηin)) := by
          gcongr
      _ = (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞) ^ 2
          * ((δ : ℝ≥0∞) ^ (-θ₂) * ((δ : ℝ≥0∞) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens
                + ML2Spine.spineNu β ϖ ε₁ gain dens))
              * (δ : ℝ≥0∞) ^ (-θ₁)
              * (δ : ℝ≥0∞) ^ (6 * ML2Spine.spineNu β ϖ ε₁ gain dens + θ₁ + θ₂ + 2 * ηin))) := by
          ring
      _ = (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞) ^ 2
          * (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens + 2 * ηin) := by rw [e1]
      _ = (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞) ^ 2
          * ((δ : ℝ≥0∞) ^ ηin * (δ : ℝ≥0∞) ^ ηin)
          * (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens) := by
          rw [← e2]; ring
      _ ≤ (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞) ^ 2
          * ((2 * (lam : ℝ≥0∞)) * (2 * (lam : ℝ≥0∞)))
          * (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens) := by
          gcongr
      _ = (((lam : ℝ≥0∞)
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞))
          * ((lam : ℝ≥0∞)
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞))
          * (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens)) * 4 := by ring
  -- the numeric inputs of the factor interface
  have hδEne : (δ : ℝ≥0∞) ≠ 0 := by simpa using hδ0.ne'
  have hδEtop : (δ : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := ENNReal.coe_ne_top
  have hCstarB : (C : ℝ≥0∞) * StickyKakeya.totalLoss C Kl cl δ
      ≤ (δ : ℝ≥0∞) ^ (-κc) := by
    have hT : StickyKakeya.totalLoss C Kl cl δ ≤ (δ : ℝ≥0∞) ^ (-(κc / 2)) := by
      rw [← ofReal_rpow_coe hδ0]
      exact hdT' hδ0 hmT'.2
    calc (C : ℝ≥0∞) * StickyKakeya.totalLoss C Kl cl δ
        ≤ (δ : ℝ≥0∞) ^ (-(κc / 2)) * (δ : ℝ≥0∞) ^ (-(κc / 2)) :=
          mul_le_mul' (hd3 δ hδ0 hm3.2) hT
      _ = (δ : ℝ≥0∞) ^ (-κc) := by
          rw [← ENNReal.rpow_add _ _ hδEne hδEtop]
          congr 1
          ring
  have hmaxu' : Kakeya.maxDensity u' (fun i ↦ (T i).toConvexSpaceBody)
      ≤ (δ : ℝ≥0∞) ^ (-ηin) := (Kakeya.maxDensity_mono _ hu's).trans hKTs
  have hs₁ne' : ({i ∈ u' | 𝒰.cover.assign bb i ∈ t₁} : Finset ι).Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    rw [hcon] at hmasspos
    simp at hmasspos
  have hune : u'.Nonempty := hs₁ne'.mono (Finset.filter_subset _ _)
  have hfacw := hfacδ u' T (max C 4) lam 𝒰
    ((C : ℝ≥0∞) * StickyKakeya.totalLoss C Kl cl δ) aa bb mm hwin
    v t₀ t₁ ht₁ hballt hballs ht₀ hcn hballt₀ hballu' hune hmaxu' hdenseu hcompu hlamlow hcardu
    hCstarB le_rfl hmasspos hδτ hτθ hθ1
  have hX : ML2Spine.spineNu β ϖ ε₁ gain dens ≤ ML2Spine.spineRung β ϖ ε₁ gain dens mm :=
    hsp.rung_mono (Nat.zero_le mm)
  refine sum_shade_gain_of_window (β := β) hβ0.le hδ0 hδ1 hlam0 hu's hdenseu 𝒰 hwinP ht₁
    hcardseam hmasspos
    (εf := εf) (gm := gm (ML2Spine.spineRung β ϖ ε₁ gain dens mm))
    (εc := εc + ML2Spine.spineRung β ϖ ε₁ gain dens mm) (κ := κ')
    (g := 6 * ML2Spine.spineNu β ϖ ε₁ gain dens + θ₁ + θ₂ + 2 * ηin)
    (gt := 4 * ML2Spine.spineNu β ϖ ε₁ gain dens)
    hcardu hfacw hLfinal (hexp _ hX) hmassloss habs

end RungPackage

/-! ## `GeometricCoreAt` from the middle factor at the rung -/

section TopLevel

end TopLevel

/-! ## The non-vacuity control: the pinned block excludes the refuting configuration -/

section Control

end Control

end Kakeya.ML2Core

end

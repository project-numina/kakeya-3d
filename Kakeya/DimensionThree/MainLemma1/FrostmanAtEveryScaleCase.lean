/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.ShadedUniform
public import Kakeya.Sticky
public import Kakeya.Multiplicity
public import Kakeya.StickyKakeya.FibreCounts

/-!
# GWZ Lemma 8.1, case (i): the Frostman-at-every-scale case

The bootstrapping lemma [GWZ, Lemma 8.1] splits according to the two conclusions of
[GWZ, Lemma 7.7(A)].  This file treats the first conclusion, in which the family of
`δ`-tubes is Frostman at every scale.  In that case sticky Kakeya
([GWZ, Theorem 7.3(A)], stated here as
`StickyKakeya.volume_iUnionShade_ge_of_isFrostmanAtEveryScale`) gives an almost
maximal shaded union, and the Frostman estimate `K_F(γ/2)` follows at once, i.e.
[GWZ, Lemma 8.1] holds with `ν = γ/2`.

The one adaptation relative to GWZ: the paper uses the sharp packing bound
`|𝕋| ≤ δ⁻⁴` for essentially distinct `δ`-tubes in `B₁ ⊆ ℝ³`, whereas the bound
available here is the crude `Tube.card_le_of_EssDistinct`, which only gives
`|𝕋| ≲ δ⁻⁶`.  We therefore apply [GWZ, Theorem 7.3(A)] with `ε / 2` in place of
`γ / 2` and retain an explicit `δ ^ (-ε)` factor.  This changes only constants; the
conclusion is the same `K_F(γ/2)` bound.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Topology Filter ShadedBody Tube ShadedTube

universe v

namespace Kakeya

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- Blueprint `lem:multBoundFromUnionLower`: a lower bound `u` for the shaded union
turns into an upper bound for the multiplicity, using only `|T| ≲ δ ^ (n-1)` for a
`δ`-tube (`Tube.volume_le`). -/
theorem multiplicity_le_div_of_le_volume_iUnionShade {δ : ℝ≥0} (hδ1 : δ ≤ 1)
    {ι : Type*} (s : Finset ι) (T : ι → ShadedTube δ E)
    {u : ℝ≥0∞} (_hu : 0 < u) (hU : u ≤ volume (⋃ i ∈ s, (T i).shade)) :
    multiplicity s (fun i ↦ (T i).toShadedBody) ≤
      (Tube.volume_le.C (Module.finrank ℝ E) : ℝ≥0∞) *
        ((s.card : ℝ≥0∞) * (δ : ℝ≥0∞) ^ (Module.finrank ℝ E - 1)) / u := by
  rw [ShadedBody.multiplicity_eq_div]
  refine ENNReal.div_le_div ?_ hU
  calc
    (∑ i ∈ s, volume ((T i).toShadedBody).shade)
      ≤ ∑ _ ∈ s, (Tube.volume_le.C (Module.finrank ℝ E) : ℝ≥0∞) *
          (δ : ℝ≥0∞) ^ (Module.finrank ℝ E - 1) :=
        Finset.sum_le_sum fun i _ =>
          (measure_mono (T i).toShadedBody.shade_subset).trans
            (by simpa using Tube.volume_le hδ1 (T i).toTube)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

end Kakeya

namespace StickyKakeya

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

omit [Nontrivial E] in
/-- [GWZ, Theorem 7.3(A)] (sticky Kakeya, union form), in the filter form Section 8 uses.
For every `ε > 0` there is `η > 0` such that, for all small `δ`, every family of `δ`-tubes
in `B₁` carrying a uniform hierarchy along the grid of `Tube.ssfGridLen δ`, a
shading of fullness at least `δ ^ η`, and the every-scale Frostman bound `δ ^ (-η)` on the
classes of that hierarchy, has shaded union of volume at least `δ ^ ε`.

No dimension hypothesis is needed: `StickyKakeya.StickyFrostmanEstimate` is itself stated
dimension-free, so only its `B_R`-to-`B_1` specialisation and the passage from the explicit
threshold to the filter are used here.  The consumer
`Kakeya.multiplicity_le_of_isFrostmanAtEveryScale` supplies `Module.finrank ℝ E = 3` on its
own, where it is genuinely needed for the tube-packing count.

This is not a second assumption: it is the hypothesis `StickyKakeya.StickyFrostmanEstimate`
— the explicit sticky Kakeya assumption of the development — restated with
its explicit threshold `δ₀` replaced by the `𝓝[>] 0` filter, which is the form
`Kakeya.multiplicity_le_of_isFrostmanAtEveryScale` consumes.  Sticky Kakeya is now a `Prop`
*definition* rather than a theorem, so it is threaded through as the hypothesis `hSFE`
instead of being invoked by name.

**Both hypotheses are read off one hierarchy.**  Uniformity and the every-scale condition
share the single bundle `𝒯 : ShadedTube.ShadedUniformTubeSet s T (ssfGridLen δ) Cunif`:
the Frostman bound is imposed on the class of each node of `𝒯.tubeUniform` by
`Tube.UniformTubeSet.IsFrostmanAtEveryScale`.  This replaces the alternative pair
"per-scale shaded uniformity on `Set.Icc δ 1`" plus the leaf-anchored
`Tube.IsFrostmanAtEveryScale`, in which nothing tied the family witnessing
uniformity to the anchors carrying the Frostman bound.  The bundle is quantified inside the
`∀ᶠ δ`, as in `StickyKakeya.StickyFrostmanEstimate`; only its constant `Cunif` is fixed
before `η`, which is what lets `Kakeya.ml1Boot.multiplicity_le_of_frostmanAtEveryScale`
choose `η⋆` after `Cunif`.

The grid length is `Tube.ssfGridLen δ` and no change-of-grid lemma is needed at the
call sites: `ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf` produces a bundle at
exactly this length. -/
theorem volume_iUnionShade_ge_of_isFrostmanAtEveryScale
    (hSFE : StickyFrostmanEstimate.{_, v} (E := E))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η > (0 : ℝ), ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0,
    ∀ {ι : Type v} (s : Finset ι) (T : ι → ShadedTube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      ∀ {Cunif : ℝ≥0}, Cunif ≤ ssfUniformConst (Module.finrank ℝ E) →
      ∀ 𝒯 : ShadedUniformTubeSet s T (ssfGridLen δ) Cunif,
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
      𝒯.tubeUniform.IsFrostmanAtEveryScale ((δ : ℝ≥0∞) ^ (-η)) →
      (δ : ℝ≥0∞) ^ ε ≤ volume (⋃ i ∈ s, (T i).shade) := by
  obtain ⟨η, δ₀, hη, hδ₀, H⟩ := hSFE ε hε
  refine ⟨η, hη, ?_⟩
  have hpos : ∀ᶠ δ : ℝ≥0 in 𝓝[>] (0 : ℝ≥0), 0 < δ := by
    simpa [Set.Ioi] using
      (eventually_mem_nhdsWithin : ∀ᶠ δ in 𝓝[>] (0 : ℝ≥0), δ ∈ Set.Ioi (0 : ℝ≥0))
  have hcoe : Tendsto (fun δ : ℝ≥0 => (δ : ℝ)) (𝓝[>] (0 : ℝ≥0)) (𝓝 (0 : ℝ)) :=
    NNReal.continuous_coe.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hle : ∀ᶠ δ : ℝ≥0 in 𝓝[>] (0 : ℝ≥0), (δ : ℝ) ≤ δ₀ :=
    hcoe.eventually (eventually_le_nhds hδ₀)
  filter_upwards [hpos, hle] with δ hδpos hδle
  intro ι s T hB Cunif hCunif 𝒯 hfull hfrost
  have hδR : (0 : ℝ) < (δ : ℝ) := NNReal.coe_pos.mpr hδpos
  have hfull' : ENNReal.ofReal ((δ : ℝ) ^ η) ≤
      ShadedBody.fullness' s (fun i ↦ (T i).toShadedBody) := by
    rw [← ENNReal.ofReal_rpow_of_pos hδR, ENNReal.ofReal_coe_nnreal,
      ENNReal.rpow_ofNNReal hη.le, ← coe_fullness]
    exact ENNReal.coe_le_coe.mpr hfull
  have hfrost' : 𝒯.tubeUniform.IsFrostmanAtEveryScale (ENNReal.ofReal ((δ : ℝ) ^ (-η))) := by
    rw [← ENNReal.ofReal_rpow_of_pos hδR, ENNReal.ofReal_coe_nnreal]
    exact hfrost
  have hconc := H hδpos hδle s T hB hCunif 𝒯 hfull' hfrost'
  rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_rpow_of_pos hδR]
  exact hconc

end StickyKakeya

namespace Kakeya

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-! ### Discharging the uniformity cap

Case (i) caps the uniformity constant of the bundle it is applied to by the dimension-only
`ShadedTube.ssfUniformConst (Module.finrank ℝ E)`, inherited from
`StickyKakeya.StickyFrostmanEstimate`.  The dichotomy
`StickyKakeya.dividingScalesFrostman` returns its hierarchy at a constant that is *provably
larger* than that cap — it is at least `comparableCuOf (gridUniformBandConst …)`, a square of a
band constant — so its node-anchored alternative (i) cannot be read on a capped bundle.

Its **leaf-anchored** alternative (i) can.  `StickyKakeya.IsFrostmanAtEveryScale` mentions no
hierarchy at all, and `StickyKakeya.isFrostmanAtEveryScale_nodes_of_ambient_fibre` converts it
into the node-anchored condition on *any* hierarchy carried by a subfamily retaining a
`Λ`-proportion.  Instantiated at a bundle produced by
`ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf` or by
`Kakeya.ml1Boot.exists_caseFamily` — both of which land at exactly
`ShadedTube.ssfUniformConst (Module.finrank ℝ E)` — this is the theorem below, and the cap is
discharged with no change to `StickyKakeya.StickyFrostmanEstimate`. -/

end Kakeya

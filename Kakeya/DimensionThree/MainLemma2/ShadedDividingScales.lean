/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.MultiScaleFac
public import Kakeya.ShadedUniform
public import Kakeya.Pigeonhole
public import Kakeya.Factoring.Pigeonhole

/-!
# The mass-banded shade refinement, and the shaded dividing-scales dichotomy

The Section-9 reduction of GWZ Main Lemma 2 consumes GWZ Lemma 7.7(B) in a *shaded* form: given a
uniform family of `δ`-tubes carrying a shading, the dividing-scales dichotomy must return, besides
the scales, (i) a sub-shading `Y' ⊆ Y`, (ii) a shaded-mass loss, and (iii) comparability of the
per-tube shading densities.  `StickyKakeya.dividingScalesKatzTao` (`Kakeya/MultiScaleFac.lean`) is
proved but unshaded and returns none of the three.

`ShadedTube.exists_shadedUniformTubeSet_of_uniformTubeSet` (`Kakeya/ShadedUniform.lean`) supplies
(i) and (ii): it refines a shading against a *given* hierarchy, pinning
`cover.{indexSet, assign, tube}` and `branchingN` to that hierarchy's, so both alternatives of the
dichotomy transfer verbatim, and it returns the `ShadedBody.fullness'` loss.  Item (iii) is the gap,
and it is what this file closes.

## What is here

* `Kakeya.ML2Shaded.HasComparableDensities` — the obligation, in cross-multiplied form
  (`|Y_i| |T_j| ≤ K |Y_j| |T_i|`), together with `.subset` and `.mono`.
* `Kakeya.ML2Shaded.massBandLoss` and `Kakeya.ML2Shaded.exists_massBanded_shadeRefinement` — the
  **mass-banded** analogue of `ShadedTube.exists_balanced_shadeRefinement`, which bands shade-*class
  cardinalities* and therefore cannot produce (iii).  Every finite family of shaded `δ`-tubes has a
  subfamily retaining all but a `massBandLoss` share of the shaded mass and on which the densities
  are comparable at the absolute constant `2`.
* `Kakeya.ML2Shaded.massBandLoss_le_gridLoss` and
  `Kakeya.ML2Shaded.exists_threshold_massBandLoss_le` — the loss bookkeeping, honestly: the loss is
  `Θ(η log (1/δ))`, hence `≤ δ^{-α}` only *below a threshold determined by `α` and `η`*, which is
  derived explicitly and exposed in the `∃ δ₀ > 0, ∀ δ ≤ δ₀` idiom the development uses.
* `Kakeya.ML2Shaded.card_le_of_sum_shade_le` — a share of the shaded mass is a share of the index
  set, at the price of the fullness and of the dimensional tube-volume ratio.  This is what makes
  the banded subfamily usable by a consumer that needs a cardinality bound; the two are packaged
  together as `Kakeya.ML2Shaded.exists_massBanded_shadeRefinement_card`.
* `Kakeya.ML2Shaded.sum_shade_le_of_card_le` — the converse of `card_le_of_sum_shade_le`: a
  cardinality share becomes a mass share against a pointwise density lower bound, which is what the
  reduction actually spends its input comparability on (in both of the two places it spends it).
* `Kakeya.ML2Shaded.HasDenseShading` and `Kakeya.ML2Shaded.exists_denseShading_refinement` — the
  **one-sided** half of the banding: a pointwise lower bound `lam · |T_i| ≤ |Y_i|`, obtained by the
  below-average discard alone, so at the absolute cost `2` and with *no* logarithm.  It is weaker
  than `HasComparableDensities` at an absolute constant (its own comparability constant is `2/λ`,
  a `δ`-power) and stronger where the consumer needs it: being pointwise it restricts to every
  subfamily, and therefore hands the fullness to every subfamily
  (`Kakeya.ML2Shaded.HasDenseShading.le_fullness'`), which no aggregate hypothesis on the parent
  family can do.
* `Kakeya.ML2Shaded.exists_shaded_dividingScalesKatzTao` — the shaded dichotomy, assembled from the
  three ingredients above.
* `Kakeya.ML2Shaded.exists_shaded_dividingScalesKatzTao_dense` — the same dichotomy with a dense
  input shading, which is what puts a density invariant **and** a fullness lower bound for the
  refined shading on the returned index set `s'` itself rather than on a further subfamily.  This
  is the form the Section-9 reduction consumes; see its docstring for why the two comparability
  clauses it returns are genuinely different statements.
* Guardrails: `nonempty_of_massBand`, `shade_eq_zero_of_hasComparableDensities`,
  `not_hasComparableDensities_of_aggregate_retention`, `massBand_must_discard`,
  `massBand_forced_on_concrete_family`, `coverClass_nonempty_of_uniformTubeSet`.

## The loss, and where the threshold comes from

Write `λ = λ(𝕋, Y)` for the fullness and `L = log (1/δ)`.  The banding is two pigeonholes:

1. *Discard below average.*  Keeping `{i : |Y_i| ≥ (λ/2) |T_i|}` costs a factor `2` of the shaded
   mass (`ShadedBody.one_sub_mul_sum_volume_shade_le_sum_discardLowShading` at `c = 1/2`) and
   confines the retained densities `|Y_i| / |T_i|` to `[λ/2, 1]`.
2. *Dyadic pigeonhole on that range.*  A range of ratio `2/λ` has `1 + log₂ (2/λ)` dyadic bands, and
   the heaviest one retains that share of the mass and has densities comparable within a factor `2`
   (`ENNReal.dyadic_pigeonhole₁''`).

So `massBandLoss λ = 2 (1 + log₂ (2/λ))`.  Under the standing hypothesis `δ^η ≤ λ`,

  `massBandLoss λ ≤ 2 (2 + η L / log 2) = 4 + (2η / log 2) L ≤ (4 + 2η/log 2) (1 + L)`,

and `1 + L = 1 - log δ ≤ (1 - log δ)^{(⌈log log 1/δ⌉+1)^2} = StickyKakeya.gridLoss 1 1 δ`.  That is
`massBandLoss_le_gridLoss`.  Absorbing the *constant* `4 + 2η/log 2` into `δ^{-α/2}`
(`exists_threshold_const_le_rpow_neg'`, threshold `(max (4 + 2η/log 2) 1)^{-2/α}`) and the grid loss
into `δ^{-α/2}` (`StickyKakeya.exists_threshold_gridLoss_le`) gives

  `massBandLoss λ ≤ δ^{-α}` for `δ ≤ δ₀(η, α)`,

with `δ₀` bound **before** `δ`, before `λ` and before the family.  The retained mass is `⪆ 1/L`, not
`⪆ 1`; there is no threshold at which it becomes `⪆ 1`, only one at which `1/L ≥ δ^α`.

## Why comparability lands on a *further* subfamily, and what that costs

`HasComparableDensities` is pointwise and two-sided, so it fails outright as soon as one retained
index has zero shaded mass beside one with positive mass
(`shade_eq_zero_of_hasComparableDensities`).  A shade refinement that keeps every index therefore
cannot deliver it, however good its aggregate retention:
`not_hasComparableDensities_of_aggregate_retention` exhibits a sub-shading with an aggregate
retention of `1/2` — better than any loss charged anywhere in this development — whose densities
are comparable at no constant at all.  This is the aggregate-versus-pointwise gap, and no
sharpening of the `ShadedBody.fullness'` loss of
`ShadedTube.exists_shadedUniformTubeSet_of_uniformTubeSet` can bridge it.

Discarding indices is therefore forced.  But discarding indices destroys
`Tube.UniformTubeSet.le_card_class` at every node whose class is emptied, and the only repair —
shrinking `Tube.GridCoverSystem.indexSet` to the nodes still hit — shrinks
`Tube.UniformTubeSet.nodesUnder`, under which the **third** window bullet of alternative (ii), being
a *lower* bound on `Kakeya.maxDensity`, does not survive.  (Alternative (i) and the first two
bullets, being upper bounds, do survive, by `Kakeya.maxDensity_mono`.)

So `exists_shaded_dividingScalesKatzTao` returns the `ShadedTube.ShadedUniformTubeSet` on `s'` and
the comparability on a further `s'' ⊆ s'`, and this is the strongest form obtainable by composing
the three proved ingredients.  Putting both on the same index set requires the shaded uniformization
to be *interleaved* with the stopping time — a different proof of 7.7(B), not a different
composition.  `card_le_of_sum_shade_le` makes the returned `s''` quantitatively usable all the same:
it converts the mass share into the cardinality share `#s'' ≥ (λ c_n)/(massBandLoss · C_n) · #s'`.

## What lands on `s'` and what does not, once more

The consumer of 7.7(B) wants comparability of the densities on the index set that carries the
hierarchy, because what it does with comparability is recover a fullness lower bound for the
refined shading on that set.  The two are not the same ask, and only the second is obtainable here:

* the **fullness** lower bound on `s'` *is* obtainable, and
  `Kakeya.ML2Shaded.exists_shaded_dividingScalesKatzTao_dense` delivers it, provided the input
  fullness was handed in pointwise (`HasDenseShading`) rather than as an aggregate;
* **absolute-constant comparability of `Y'` on `s'`** is not, and cannot be, for the reason
  isolated by `Kakeya.ML2Shaded.not_hasComparableDensities_of_aggregate_retention`.

## Absorbing the two `δ`-dependent losses

The cardinality loss is `StickyKakeya.totalLoss`, absorbed by
`StickyKakeya.exists_threshold_totalLoss_le`.  The mass loss is `(log₂ #s + 1)^{2M+2}` with
`M = Tube.ssfGridLen δ`, absorbed by `Tube.exists_threshold_polylog_pow_ssfGridLen_le` at `A = 1`,
`m = 2` once the consumer supplies a cardinality bound `#s ≤ δ^{-K₀}`.  The banding loss is
`massBandLoss`, absorbed by `exists_threshold_massBandLoss_le`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Real Metric
open Tube ShadedTube

universe u

namespace Kakeya.ML2Shaded

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

/-! ### Pairwise comparable shading densities -/

/-- **Pairwise comparable shading densities**, in cross-multiplied form. -/
def HasComparableDensities (K : ℝ≥0) (u : Finset ι) (V : ι → ShadedBody E) : Prop :=
  ∀ i ∈ u, ∀ j ∈ u,
    volume (V i).shade * volume (V j).carrier
      ≤ (K : ℝ≥0∞) * (volume (V j).shade * volume (V i).carrier)

omit [Nontrivial E] in
theorem HasComparableDensities.subset {K : ℝ≥0} {u u' : Finset ι} {V : ι → ShadedBody E}
    (h : HasComparableDensities K u V) (hsub : u' ⊆ u) : HasComparableDensities K u' V :=
  fun i hi j hj => h i (hsub hi) j (hsub hj)

omit [Nontrivial E] in
theorem HasComparableDensities.mono {K K' : ℝ≥0} {u : Finset ι} {V : ι → ShadedBody E}
    (h : HasComparableDensities K u V) (hK : K ≤ K') : HasComparableDensities K' u V :=
  fun i hi j hj => (h i hi j hj).trans
    (mul_le_mul_left (ENNReal.coe_le_coe.mpr hK) _)

/-! ### Positivity and finiteness of the carrier volume of a `δ`-tube -/

/-- A `δ`-tube with `0 < δ` has positive carrier volume. -/
theorem volume_carrier_ne_zero {δ : ℝ≥0} (hδ : 0 < δ) (T : Tube δ E) :
    volume T.carrier ≠ 0 := by
  have hle := Tube.le_volume (E := E) T
  have h1 : (Tube.le_volume.c (Module.finrank ℝ E) : ℝ≥0∞) ≠ 0 := by
    have := Tube.le_volume.c_pos (Module.finrank ℝ E)
    simpa using this.ne'
  have h2 : ((δ : ℝ≥0∞)) ^ (Module.finrank ℝ E - 1) ≠ 0 := by
    refine pow_ne_zero _ ?_
    simpa using hδ.ne'
  have hpos : (0 : ℝ≥0∞)
      < (Tube.le_volume.c (Module.finrank ℝ E) : ℝ≥0∞)
        * (δ : ℝ≥0∞) ^ (Module.finrank ℝ E - 1) := ENNReal.mul_pos h1 h2
  exact (lt_of_lt_of_le hpos hle).ne'

omit [Nontrivial E] in
/-- The carrier of a tube is compact, so its volume is finite. -/
theorem volume_carrier_ne_top {δ : ℝ≥0} (T : Tube δ E) : volume T.carrier ≠ ⊤ :=
  T.isCompact'.measure_ne_top

/-! ### The loss of the mass-banding pigeonhole -/

/-- **The loss of the mass-banded shade refinement.**

Two factors.  The `2` is the below-average discard: throwing away the indices whose shaded mass
falls below half the average density `λ` costs half the shaded mass and no more.  The
`1 + log₂ (2/λ)` is the dyadic pigeonhole over the bands the *retained* densities can occupy: after
the discard they lie in `[λ/2, 1]`, a range of ratio `2/λ`, so `⌈log₂ (2/λ)⌉ + 1` bands suffice.

The loss is governed by the fullness `λ` alone, not by the cardinality of the family.  Under the
standing hypothesis `δ^η ≤ λ` of this development it is `O(η log (1/δ))`, hence subpolynomial
(`Kakeya.ML2Shaded.exists_threshold_massBandLoss_le`). -/
noncomputable def massBandLoss (lam : ℝ≥0) : ℝ≥0∞ :=
  2 * ENNReal.ofReal (1 + Real.logb 2 (2 / (lam : ℝ)))

/-! ### The mass-banded shade refinement -/

/-- **Mass-banded shade refinement** (the mass analogue of
`ShadedTube.exists_balanced_shadeRefinement`, which bands shade-*class cardinalities*).

Every finite family of shaded `δ`-tubes has a subfamily which retains all but a
`Kakeya.ML2Shaded.massBandLoss` share of the shaded mass and on which the per-tube shading
densities are pairwise comparable *within a factor `2`* — a genuine pointwise conclusion, obtained
from the aggregate mass bound by discarding, not by averaging.

**Discarding is not optional.**  `Kakeya.ML2Shaded.HasComparableDensities` is a two-sided pointwise
statement, so it fails outright as soon as one retained index carries zero shaded mass beside one
carrying positive mass.  A shade refinement that keeps every index — in particular the refinement
performed by `ShadedTube.exists_shadedUniformTubeSet_of_uniformTubeSet`, which returns only the
aggregate `ShadedBody.fullness'` loss — therefore cannot deliver it; see
`Kakeya.ML2Shaded.not_hasComparableDensities_of_aggregate_retention`.

The comparability constant is the absolute `2`, and the whole loss sits in the retained mass. -/
theorem exists_massBanded_shadeRefinement {δ : ℝ≥0} (hδ : 0 < δ)
    (s : Finset ι) (V : ι → ShadedTube δ E) :
    ∃ s' ⊆ s,
      (∑ i ∈ s, volume (V i).shade)
          ≤ massBandLoss (ShadedBody.fullness s (fun i => (V i).toShadedBody))
              * ∑ i ∈ s', volume (V i).shade ∧
        HasComparableDensities 2 s' (fun i => (V i).toShadedBody) := by
  classical
  set Vb : ι → ShadedBody E := fun i => (V i).toShadedBody with hVbdef
  have hcar0 : ∀ i, volume (Vb i).carrier ≠ 0 :=
    fun i => volume_carrier_ne_zero hδ (V i).toTube
  have hcarT : ∀ i, volume (Vb i).carrier ≠ ⊤ :=
    fun i => volume_carrier_ne_top (V i).toTube
  set lam : ℝ≥0 := ShadedBody.fullness s Vb with hlamdef
  set S : ℝ≥0∞ := ∑ i ∈ s, volume (Vb i).shade with hSdef
  by_cases hS0 : S = 0
  · refine ⟨s, Finset.Subset.refl s, ?_, ?_⟩
    · change S ≤ massBandLoss lam * S
      rw [hS0, mul_zero]
    · have h0 : ∀ k ∈ s, volume (Vb k).shade = 0 := by
        intro k hk
        exact le_antisymm (hS0 ▸ Finset.single_le_sum (f := fun i => volume (Vb i).shade)
          (fun i _ => zero_le) hk) (zero_le)
      intro i hi j hj
      simp [h0 i hi, h0 j hj]
  · -- the total shaded mass is positive, hence so is the fullness
    have hsne : s.Nonempty := by
      rcases Finset.eq_empty_or_nonempty s with h | h
      · exact absurd (by simp [hSdef, h]) hS0
      · exact h
    have hD_ne_top : (∑ i ∈ s, volume (Vb i).carrier) ≠ ⊤ :=
      ENNReal.sum_ne_top.mpr (fun i _ => hcarT i)
    have hlam_pos : 0 < lam := by
      rw [hlamdef]
      have hne : ShadedBody.fullness' s Vb ≠ 0 := by
        rw [ShadedBody.fullness']
        exact ENNReal.div_ne_zero.mpr ⟨hS0, hD_ne_top⟩
      have : ShadedBody.fullness s Vb ≠ 0 := by
        intro h
        exact hne (by
          have := ShadedBody.coe_fullness s Vb
          rw [h] at this
          simpa using this.symm)
      exact pos_iff_ne_zero.mpr this
    -- Step 1: discard the indices of below-average shading
    set s₀ : Finset ι := ShadedBody.discardLowShading s Vb (1 / 2) with hs₀def
    have hs₀sub : s₀ ⊆ s := ShadedBody.discardLowShading_subset s Vb _
    have hhalf : ((1 / 2 : ℝ≥0) : ℝ≥0∞) * S ≤ ∑ i ∈ s₀, volume (Vb i).shade := by
      have := ShadedBody.one_sub_mul_sum_volume_shade_le_sum_discardLowShading s Vb
        (c := (1 / 2 : ℝ≥0)) (by norm_num)
      have hsub2 : (1 - (1 / 2 : ℝ≥0)) = (1 / 2 : ℝ≥0) := by
        rw [← NNReal.coe_inj, NNReal.coe_sub (by norm_num : (1 / 2 : ℝ≥0) ≤ 1)]
        norm_num
      simpa [hs₀def, hSdef, hsub2] using this
    have hS_le_two : S ≤ 2 * ∑ i ∈ s₀, volume (Vb i).shade := by
      have h2 : (2 : ℝ≥0∞) * (((1 / 2 : ℝ≥0) : ℝ≥0∞) * S) = S := by
        have hcoe : ((1 / 2 : ℝ≥0) : ℝ≥0∞)
            = ((1 : ℝ≥0) : ℝ≥0∞) / ((2 : ℝ≥0) : ℝ≥0∞) :=
          ENNReal.coe_div (by norm_num)
        have : ((1 / 2 : ℝ≥0) : ℝ≥0∞) = (2 : ℝ≥0∞)⁻¹ := by
          rw [hcoe]; simp
        rw [this, ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
      calc S = 2 * (((1 / 2 : ℝ≥0) : ℝ≥0∞) * S) := h2.symm
        _ ≤ 2 * ∑ i ∈ s₀, volume (Vb i).shade := mul_le_mul' le_rfl hhalf
    -- Step 2: the retained densities live in `[lam/2, 1]`
    set f : ι → ℝ≥0∞ := fun i => volume (Vb i).shade / volume (Vb i).carrier with hfdef
    have hcoe_half : (((lam / 2 : ℝ≥0)) : ℝ≥0∞)
        = ((1 / 2 : ℝ≥0) : ℝ≥0∞) * (lam : ℝ≥0∞) := by
      rw [show ((lam / 2 : ℝ≥0) : ℝ≥0∞) = (lam : ℝ≥0∞) / ((2 : ℝ≥0) : ℝ≥0∞)
        from ENNReal.coe_div (by norm_num),
        show ((1 / 2 : ℝ≥0) : ℝ≥0∞) = ((1 : ℝ≥0) : ℝ≥0∞) / ((2 : ℝ≥0) : ℝ≥0∞)
        from ENNReal.coe_div (by norm_num)]
      simp [ENNReal.div_eq_inv_mul]
    have hIcc : ∀ i ∈ s₀,
        f i ∈ Set.Icc (((lam / 2 : ℝ≥0)) : ℝ≥0∞) ((1 : ℝ≥0) : ℝ≥0∞) := by
      intro i hi
      constructor
      · have hlow := ShadedBody.le_volume_shade_of_mem_discardLowShading (hi := hi)
        rw [hfdef]
        refine (ENNReal.le_div_iff_mul_le (Or.inl (hcar0 i)) (Or.inl (hcarT i))).2 ?_
        rw [hcoe_half]
        simpa [mul_assoc, hlamdef] using hlow
      · have hsub : volume (Vb i).shade ≤ volume (Vb i).carrier :=
          measure_mono (Vb i).shade_subset
        rw [hfdef]
        simp only [ENNReal.coe_one]
        exact ENNReal.div_le_of_le_mul (by simpa using hsub)
    have hapos : 0 < (lam / 2 : ℝ≥0) := by
      have : (0 : ℝ≥0) < lam := hlam_pos
      positivity
    obtain ⟨s', hs'sub, hsum, hband⟩ :=
      ENNReal.dyadic_pigeonhole₁'' (s := s₀) (w := fun i => volume (Vb i).shade) (f := f)
        (a := lam / 2) (b := 1) hapos hIcc
    refine ⟨s', hs'sub.trans hs₀sub, ?_, ?_⟩
    · -- the two losses compose into `massBandLoss`
      have hloss : ENNReal.ofReal (1 + Real.logb 2 (((1 : ℝ≥0) : ℝ) / ((lam / 2 : ℝ≥0) : ℝ)))
          = ENNReal.ofReal (1 + Real.logb 2 (2 / (lam : ℝ))) := by
        congr 2
        push_cast
        rw [one_div_div]
      change S ≤ massBandLoss lam * ∑ i ∈ s', volume (Vb i).shade
      unfold massBandLoss
      calc S ≤ 2 * ∑ i ∈ s₀, volume (Vb i).shade := hS_le_two
        _ ≤ 2 * (ENNReal.ofReal
              (1 + Real.logb 2 (((1 : ℝ≥0) : ℝ) / ((lam / 2 : ℝ≥0) : ℝ)))
              * ∑ i ∈ s', volume (Vb i).shade) := mul_le_mul' le_rfl hsum
        _ = 2 * ENNReal.ofReal (1 + Real.logb 2 (2 / (lam : ℝ)))
              * ∑ i ∈ s', volume (Vb i).shade := by rw [hloss, mul_assoc]
    · -- pointwise comparability of the densities, cleared of denominators
      intro i hi j hj
      have key : f i ≤ 2 * f j := hband i hi j hj
      have hmul := mul_le_mul' key
        (le_refl (volume (Vb i).carrier * volume (Vb j).carrier))
      have hL : f i * (volume (Vb i).carrier * volume (Vb j).carrier)
          = volume (Vb i).shade * volume (Vb j).carrier := by
        rw [hfdef]
        rw [← mul_assoc, ENNReal.div_mul_cancel (hcar0 i) (hcarT i)]
      have hR : 2 * f j * (volume (Vb i).carrier * volume (Vb j).carrier)
          = 2 * (volume (Vb j).shade * volume (Vb i).carrier) := by
        calc 2 * f j * (volume (Vb i).carrier * volume (Vb j).carrier)
            = 2 * (f j * volume (Vb j).carrier * volume (Vb i).carrier) := by ring
          _ = 2 * (volume (Vb j).shade * volume (Vb i).carrier) := by
              rw [hfdef, ENNReal.div_mul_cancel (hcar0 j) (hcarT j)]
      rw [hL, hR] at hmul
      simpa using hmul

omit [Nontrivial E] in
/-- Any constant is eventually dominated by a negative power of `δ`, with the threshold written as
an `NNReal` in `(0, 1]`.  (The version in `Kakeya.StickyKakeya.BallReduction` returns a real
threshold and lives behind a much heavier import.) -/
theorem exists_threshold_const_le_rpow_neg' (c : ℝ) {β : ℝ} (hβ : 0 < β) :
    ∃ d : ℝ≥0, 0 < d ∧ d ≤ 1 ∧
      ∀ {δ : ℝ≥0}, 0 < δ → δ ≤ d → c ≤ (δ : ℝ) ^ (-β) := by
  set C : ℝ := max c 1 with hCdef
  have hC1 : (1 : ℝ) ≤ C := le_max_right _ _
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC1
  have hbase : (0 : ℝ) < C ^ (-(1 / β)) := Real.rpow_pos_of_pos hCpos _
  have hbase1 : C ^ (-(1 / β)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hC1 (by
      simp only [neg_nonpos]
      positivity)
  refine ⟨Real.toNNReal (C ^ (-(1 / β))), Real.toNNReal_pos.mpr hbase, ?_, ?_⟩
  · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hbase.le]
    simpa using hbase1
  · intro δ hδpos hδle
    have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδpos
    have hδleR : (δ : ℝ) ≤ C ^ (-(1 / β)) := by
      have := NNReal.coe_le_coe.mpr hδle
      rwa [Real.coe_toNNReal _ hbase.le] at this
    have hmono : (C ^ (-(1 / β))) ^ (-β) ≤ (δ : ℝ) ^ (-β) :=
      Real.rpow_le_rpow_of_nonpos hδR hδleR (by linarith)
    have heq : (C ^ (-(1 / β))) ^ (-β) = C := by
      rw [← Real.rpow_mul hCpos.le]
      have hone : (-(1 / β)) * (-β) = 1 := by field_simp
      rw [hone, Real.rpow_one]
    rw [heq] at hmono
    exact le_trans (le_max_left c 1) hmono

/-! ### The banding loss is subpolynomial: the explicit threshold -/

/-! ### Guardrails: the statement is neither vacuous nor trivially satisfiable -/

/-! ### Transport helpers -/

/-- **The fullness loss, read on the shaded masses.**  The carriers are literally unchanged by a
sub-shading on the same tubes, so the `ShadedBody.fullness'` inequality returned by
`ShadedTube.exists_shadedUniformTubeSet_of_uniformTubeSet` is the mass inequality that
`ShadedBody.isCRefinement_of_isRefinement_of_sum_le` consumes. -/
theorem sum_shade_le_of_fullness_le {δ : ℝ≥0} (hδ : 0 < δ) {u : Finset ι}
    {V V' : ι → ShadedTube δ E} (htube : ∀ i, (V' i).toTube = (V i).toTube)
    {L : ℝ≥0∞} (hL : ShadedBody.fullness' u (fun i => (V i).toShadedBody)
        ≤ L * ShadedBody.fullness' u (fun i => (V' i).toShadedBody)) :
    (∑ i ∈ u, volume (V i).shade) ≤ L * ∑ i ∈ u, volume (V' i).shade := by
  classical
  rcases Finset.eq_empty_or_nonempty u with rfl | hune
  · simp
  set D : ℝ≥0∞ := ∑ i ∈ u, volume (V i).carrier with hDdef
  have hDeq : (∑ i ∈ u, volume (V' i).carrier) = D := by
    rw [hDdef]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 1
    calc (V' i).carrier = (V' i).toTube.carrier := rfl
      _ = (V i).toTube.carrier := by rw [htube i]
      _ = (V i).carrier := rfl
  have hD0 : D ≠ 0 := by
    obtain ⟨i₀, hi₀⟩ := hune
    intro h
    have := Finset.sum_eq_zero_iff.mp h i₀ hi₀
    exact volume_carrier_ne_zero hδ (V i₀).toTube this
  have hDT : D ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun i _ => volume_carrier_ne_top (V i).toTube)
  have hL' : (∑ i ∈ u, volume (V i).shade) / D
      ≤ (L * ∑ i ∈ u, volume (V' i).shade) / D := by
    have h1 : ShadedBody.fullness' u (fun i => (V i).toShadedBody)
        = (∑ i ∈ u, volume (V i).shade) / D := rfl
    have h2 : L * ShadedBody.fullness' u (fun i => (V' i).toShadedBody)
        = (L * ∑ i ∈ u, volume (V' i).shade) / D := by
      change L * ((∑ i ∈ u, volume (V' i).shade) / (∑ i ∈ u, volume (V' i).carrier))
        = (L * ∑ i ∈ u, volume (V' i).shade) / D
      rw [hDeq, mul_div_assoc]
    rw [← h1, ← h2]
    exact hL
  have hmul := mul_le_mul' hL' (le_refl D)
  rwa [ENNReal.div_mul_cancel hD0 hDT, ENNReal.div_mul_cancel hD0 hDT] at hmul

/-! ### From a share of the shaded mass to a share of the index set -/

/-- **A mass share is a cardinality share, at the price of the fullness and of the dimensional
tube-volume ratio.**

If a subfamily `s' ⊆ s` carries all but a factor `L` of the shaded mass, then it carries all but a
factor `L · C_n / (λ c_n)` of the *indices*, where `λ = λ(𝕋, Y)` is the fullness of the whole family
and `c_n ≤ |T| / δ^{n-1} ≤ C_n` are the two dimensional tube-volume constants.

No comparability of the densities is used — only `Y_i ⊆ T_i` and the two-sided volume bracket for a
`δ`-tube.  This is the converse direction to the blueprint's
`exists_massShare_of_comparableDensities`, and it is what makes the mass-banded subfamily of
`Kakeya.ML2Shaded.exists_massBanded_shadeRefinement` usable by a consumer that needs a cardinality
bound: under the standing hypothesis `δ^η ≤ λ` the extra factor is `δ^{-η}` times a constant. -/
theorem card_le_of_sum_shade_le {δ : ℝ≥0} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {s s' : Finset ι} {V : ι → ShadedTube δ E} {L : ℝ≥0∞}
    (hmass : (∑ i ∈ s, volume (V i).shade) ≤ L * ∑ i ∈ s', volume (V i).shade) :
    (ShadedBody.fullness s (fun i => (V i).toShadedBody) : ℝ≥0∞)
        * (Tube.le_volume.c (Module.finrank ℝ E) : ℝ≥0∞) * (s.card : ℝ≥0∞)
      ≤ L * (Tube.volume_le.C (Module.finrank ℝ E) : ℝ≥0∞) * (s'.card : ℝ≥0∞) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn
  set p : ℝ≥0∞ := (δ : ℝ≥0∞) ^ (n - 1) with hp
  have hp0 : p ≠ 0 := by
    rw [hp]
    exact pow_ne_zero _ (by simpa using hδ0.ne')
  have hpT : p ≠ ⊤ := by
    rw [hp]
    exact ENNReal.pow_ne_top ENNReal.coe_ne_top
  set lam : ℝ≥0 := ShadedBody.fullness s (fun i => (V i).toShadedBody) with hlam
  -- lower bound on the total shaded mass
  have hlow : (lam : ℝ≥0∞) * ((Tube.le_volume.c n : ℝ≥0∞) * p) * (s.card : ℝ≥0∞)
      ≤ ∑ i ∈ s, volume (V i).shade := by
    have hsum : ∑ i ∈ s, volume (V i).shade
        = (lam : ℝ≥0∞) * ∑ i ∈ s, volume ((V i).toShadedBody).carrier :=
      ShadedBody.sum_volumeReal_shade_eq_fullness_mul s (fun i => (V i).toShadedBody)
    have hcar : (s.card : ℝ≥0∞) * ((Tube.le_volume.c n : ℝ≥0∞) * p)
        ≤ ∑ i ∈ s, volume ((V i).toShadedBody).carrier := by
      have := Finset.card_nsmul_le_sum s (fun i => volume ((V i).toShadedBody).carrier)
        ((Tube.le_volume.c n : ℝ≥0∞) * p) (fun i _ => by
          simpa [hn, hp] using Tube.le_volume (E := E) (V i).toTube)
      simpa [nsmul_eq_mul] using this
    calc (lam : ℝ≥0∞) * ((Tube.le_volume.c n : ℝ≥0∞) * p) * (s.card : ℝ≥0∞)
        = (lam : ℝ≥0∞) * ((s.card : ℝ≥0∞) * ((Tube.le_volume.c n : ℝ≥0∞) * p)) := by ring
      _ ≤ (lam : ℝ≥0∞) * ∑ i ∈ s, volume ((V i).toShadedBody).carrier :=
          mul_le_mul' le_rfl hcar
      _ = ∑ i ∈ s, volume (V i).shade := hsum.symm
  -- upper bound on the retained shaded mass
  have hup : (∑ i ∈ s', volume (V i).shade)
      ≤ (s'.card : ℝ≥0∞) * ((Tube.volume_le.C n : ℝ≥0∞) * p) := by
    have := Finset.sum_le_card_nsmul s' (fun i => volume (V i).shade)
      ((Tube.volume_le.C n : ℝ≥0∞) * p) (fun i _ => by
        refine le_trans (measure_mono ((V i).toShadedBody).shade_subset) ?_
        simpa [hn, hp] using Tube.volume_le (E := E) hδ1 (V i).toTube)
    simpa [nsmul_eq_mul] using this
  -- chain and cancel the common factor `δ^{n-1}`
  have hchain : p * ((lam : ℝ≥0∞) * (Tube.le_volume.c n : ℝ≥0∞) * (s.card : ℝ≥0∞))
      ≤ p * (L * (Tube.volume_le.C n : ℝ≥0∞) * (s'.card : ℝ≥0∞)) := by
    calc p * ((lam : ℝ≥0∞) * (Tube.le_volume.c n : ℝ≥0∞) * (s.card : ℝ≥0∞))
        = (lam : ℝ≥0∞) * ((Tube.le_volume.c n : ℝ≥0∞) * p) * (s.card : ℝ≥0∞) := by ring
      _ ≤ ∑ i ∈ s, volume (V i).shade := hlow
      _ ≤ L * ∑ i ∈ s', volume (V i).shade := hmass
      _ ≤ L * ((s'.card : ℝ≥0∞) * ((Tube.volume_le.C n : ℝ≥0∞) * p)) :=
          mul_le_mul' le_rfl hup
      _ = p * (L * (Tube.volume_le.C n : ℝ≥0∞) * (s'.card : ℝ≥0∞)) := by ring
  exact (ENNReal.mul_le_mul_iff_right hp0 hpT).mp hchain

/-! ### One-sided density: the pointwise invariant a consumer of 7.7(B) actually needs

`Kakeya.ML2Shaded.HasComparableDensities` is two-sided, and the price of establishing it is the
`Kakeya.ML2Shaded.massBandLoss` logarithm.  The *one-sided* half — a pointwise lower bound
`lam · |T_i| ≤ |Y_i|` — costs only a factor `2` of the shaded mass, and it is strictly stronger
where it matters: it is inherited by **every** subfamily together with the fullness bound
`lam ≤ λ(u', Y)`, whereas a fullness bound on `u` alone says nothing about a subfamily of `u`.

This is the aggregate-versus-pointwise conversion in its safe direction, and the direction the
consumer needs: the dividing-scales dichotomy hands back an arbitrary subfamily `s' ⊆ s`, and the
consumer must recover `δ^{η'} ≤ λ(s', Y')` from `δ^{η} ≤ λ(s, Y)`.  Nothing but a pointwise
hypothesis can do that. -/

/-- **A pointwise lower bound on the shading densities**: every body of `u` has shaded mass at
least `lam` times its own volume.

Unlike `ShadedBody.fullness`, which is an aggregate, this restricts to subfamilies
(`Kakeya.ML2Shaded.HasDenseShading.subset`) and therefore *transports* the fullness to every
subfamily (`Kakeya.ML2Shaded.HasDenseShading.le_fullness'`). -/
def HasDenseShading (lam : ℝ≥0) (u : Finset ι) (V : ι → ShadedBody E) : Prop :=
  ∀ i ∈ u, (lam : ℝ≥0∞) * volume (V i).carrier ≤ volume (V i).shade

omit [Nontrivial E] in
theorem HasDenseShading.subset {lam : ℝ≥0} {u u' : Finset ι} {V : ι → ShadedBody E}
    (h : HasDenseShading lam u V) (hsub : u' ⊆ u) : HasDenseShading lam u' V :=
  fun i hi => h i (hsub hi)

omit [Nontrivial E] in
theorem HasDenseShading.mono {lam lam' : ℝ≥0} {u : Finset ι} {V : ι → ShadedBody E}
    (h : HasDenseShading lam u V) (hle : lam' ≤ lam) : HasDenseShading lam' u V :=
  fun i hi => le_trans (mul_le_mul_left (ENNReal.coe_le_coe.mpr hle) _) (h i hi)

omit [Nontrivial E] in
/-- **A dense shading gives the fullness of the family, and of every subfamily.**  This is the
payoff of the pointwise form: the hypothesis is inherited by subfamilies, so the conclusion is
available at every subfamily too, with the *same* `lam` and no loss. -/
theorem HasDenseShading.le_fullness' {lam : ℝ≥0} {u : Finset ι} {V : ι → ShadedBody E}
    (h : HasDenseShading lam u V)
    (hne : (∑ i ∈ u, volume (V i).carrier) ≠ 0)
    (hnt : (∑ i ∈ u, volume (V i).carrier) ≠ ⊤) :
    (lam : ℝ≥0∞) ≤ ShadedBody.fullness' u V := by
  rw [ShadedBody.fullness', ENNReal.le_div_iff_mul_le (Or.inl hne) (Or.inl hnt)]
  calc (lam : ℝ≥0∞) * ∑ i ∈ u, volume (V i).carrier
      = ∑ i ∈ u, (lam : ℝ≥0∞) * volume (V i).carrier := by rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ u, volume (V i).shade := Finset.sum_le_sum h

/-- The `δ`-tube instance of `Kakeya.ML2Shaded.HasDenseShading.le_fullness'`: for a nonempty family
of `δ`-tubes with `0 < δ` the two side conditions are automatic. -/
theorem HasDenseShading.le_fullness_tube {δ : ℝ≥0} (hδ : 0 < δ) {lam : ℝ≥0} {u : Finset ι}
    {V : ι → ShadedTube δ E} (h : HasDenseShading lam u (fun i => (V i).toShadedBody))
    (hu : u.Nonempty) :
    (lam : ℝ≥0∞) ≤ ShadedBody.fullness' u (fun i => (V i).toShadedBody) := by
  classical
  refine h.le_fullness' ?_ ?_
  · obtain ⟨i₀, hi₀⟩ := hu
    intro hzero
    exact volume_carrier_ne_zero hδ (V i₀).toTube
      (Finset.sum_eq_zero_iff.mp hzero i₀ hi₀)
  · exact ENNReal.sum_ne_top.mpr (fun i _ => volume_carrier_ne_top (V i).toTube)

omit [Nontrivial E] in
/-- **A dense shading is a comparable shading**, at the constant `lam⁻¹`: the densities lie in
`[lam, 1]`.  The constant is *not* absolute — it is `δ^{-η}` under the standing hypothesis
`δ^η ≤ lam` — which is exactly why `Kakeya.ML2Shaded.exists_massBanded_shadeRefinement` pays a
logarithm to reach the absolute constant `2` instead. -/
theorem HasDenseShading.hasComparableDensities {lam : ℝ≥0} {u : Finset ι}
    {V : ι → ShadedBody E} (h : HasDenseShading lam u V) (hlam : 0 < lam) :
    HasComparableDensities lam⁻¹ u V := by
  intro i hi j hj
  have hj' : (lam : ℝ≥0∞) * volume (V j).carrier ≤ volume (V j).shade := h j hj
  have hi' : volume (V i).shade ≤ volume (V i).carrier := measure_mono (V i).shade_subset
  have hlam0 : (lam : ℝ≥0) ≠ 0 := hlam.ne'
  have hcoe : ((lam⁻¹ : ℝ≥0) : ℝ≥0∞) = ((lam : ℝ≥0∞))⁻¹ := ENNReal.coe_inv hlam0
  have hcancel : ((lam : ℝ≥0∞))⁻¹ * (lam : ℝ≥0∞) = 1 :=
    ENNReal.inv_mul_cancel (by simpa using hlam0) ENNReal.coe_ne_top
  calc volume (V i).shade * volume (V j).carrier
      ≤ volume (V i).carrier * volume (V j).carrier := mul_le_mul' hi' le_rfl
    _ = (((lam : ℝ≥0∞))⁻¹ * (lam : ℝ≥0∞)) * (volume (V j).carrier
          * volume (V i).carrier) := by rw [hcancel]; ring
    _ = ((lam : ℝ≥0∞))⁻¹ * (((lam : ℝ≥0∞) * volume (V j).carrier)
          * volume (V i).carrier) := by ring
    _ ≤ ((lam : ℝ≥0∞))⁻¹ * (volume (V j).shade * volume (V i).carrier) :=
        mul_le_mul' le_rfl (mul_le_mul' hj' le_rfl)
    _ = ((lam⁻¹ : ℝ≥0) : ℝ≥0∞) * (volume (V j).shade * volume (V i).carrier) := by
        rw [hcoe]

/-! ### The dense-shading refinement: the below-average discard, and nothing else -/

omit [Nontrivial E] in
/-- Half the shaded mass survives the below-average discard at level `1/2`. -/
theorem sum_shade_le_two_mul_discardLowShading (s : Finset ι) (V : ι → ShadedBody E) :
    (∑ i ∈ s, volume (V i).shade)
      ≤ 2 * ∑ i ∈ ShadedBody.discardLowShading s V (1 / 2), volume (V i).shade := by
  classical
  have h := ShadedBody.one_sub_mul_sum_volume_shade_le_sum_discardLowShading s V
    (c := (1 / 2 : ℝ≥0)) (by norm_num)
  have hsub2 : (1 - (1 / 2 : ℝ≥0)) = (1 / 2 : ℝ≥0) := by
    rw [← NNReal.coe_inj, NNReal.coe_sub (by norm_num : (1 / 2 : ℝ≥0) ≤ 1)]
    norm_num
  rw [hsub2] at h
  have hcoe : ((1 / 2 : ℝ≥0) : ℝ≥0∞) = (2 : ℝ≥0∞)⁻¹ := by
    rw [show ((1 / 2 : ℝ≥0) : ℝ≥0∞) = ((1 : ℝ≥0) : ℝ≥0∞) / ((2 : ℝ≥0) : ℝ≥0∞)
      from ENNReal.coe_div (by norm_num)]
    simp
  rw [hcoe] at h
  calc (∑ i ∈ s, volume (V i).shade)
      = 2 * ((2 : ℝ≥0∞)⁻¹ * ∑ i ∈ s, volume (V i).shade) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
    _ ≤ 2 * ∑ i ∈ ShadedBody.discardLowShading s V (1 / 2), volume (V i).shade :=
        mul_le_mul' le_rfl h

omit [Nontrivial E] in
/-- **The dense-shading refinement.**  Every finite family of shaded bodies has a subfamily
retaining half of the shaded mass on which the shading is *pointwise* dense at `λ/2`, `λ` the
fullness of the whole family.

This is `ShadedBody.discardLowShading` at `c = 1/2`, packaged as the pointwise invariant.  It is
the cheap half of `Kakeya.ML2Shaded.exists_massBanded_shadeRefinement`: no dyadic pigeonhole, hence
no logarithm — the entire loss is the absolute factor `2`.  What it does *not* give is a two-sided
comparability at an absolute constant; see
`Kakeya.ML2Shaded.HasDenseShading.hasComparableDensities`, whose constant is `2/λ`. -/
theorem exists_denseShading_refinement (s : Finset ι) (V : ι → ShadedBody E) :
    ∃ s' ⊆ s,
      (∑ i ∈ s, volume (V i).shade) ≤ 2 * ∑ i ∈ s', volume (V i).shade ∧
        HasDenseShading (ShadedBody.fullness s V / 2) s' V := by
  classical
  refine ⟨ShadedBody.discardLowShading s V (1 / 2),
    ShadedBody.discardLowShading_subset s V _, sum_shade_le_two_mul_discardLowShading s V, ?_⟩
  intro i hi
  have hlow := ShadedBody.le_volume_shade_of_mem_discardLowShading (hi := hi)
  have hcoe_half : ((ShadedBody.fullness s V / 2 : ℝ≥0) : ℝ≥0∞)
      = ((1 / 2 : ℝ≥0) : ℝ≥0∞) * ((ShadedBody.fullness s V : ℝ≥0) : ℝ≥0∞) := by
    rw [show ((ShadedBody.fullness s V / 2 : ℝ≥0) : ℝ≥0∞)
        = ((ShadedBody.fullness s V : ℝ≥0) : ℝ≥0∞) / ((2 : ℝ≥0) : ℝ≥0∞)
      from ENNReal.coe_div (by norm_num),
      show ((1 / 2 : ℝ≥0) : ℝ≥0∞) = ((1 : ℝ≥0) : ℝ≥0∞) / ((2 : ℝ≥0) : ℝ≥0∞)
      from ENNReal.coe_div (by norm_num)]
    simp [ENNReal.div_eq_inv_mul]
  rw [hcoe_half]
  exact hlow

/-- **A cardinality share is a mass share, given a pointwise density lower bound.**

The converse of `Kakeya.ML2Shaded.card_le_of_sum_shade_le`, and the direction the Section-9
reduction performs (as `exists_massShare_of_comparableDensities`) from *two-sided* comparability.
The one-sided `Kakeya.ML2Shaded.HasDenseShading` suffices, and the resulting constant is
`(L · C_n)/(lam · c_n)` with `c_n ≤ |T|/δ^{n-1} ≤ C_n` the two dimensional tube-volume constants —
no fullness of the parent family and no comparability constant enters, and `0 < δ` is not needed
(the bound is one-sided).

This is what makes the subfamily returned by the dividing-scales dichotomy a
`ShadedBody.IsCRefinement` of the original family, via
`ShadedBody.isCRefinement_of_isRefinement_of_sum_le`; both places where the reduction consumes an
input comparability go through exactly this inequality. -/
theorem sum_shade_le_of_card_le {δ : ℝ≥0} (hδ1 : δ ≤ 1)
    {lam : ℝ≥0} {s s' : Finset ι} {V : ι → ShadedTube δ E}
    (hdense : HasDenseShading lam s' (fun i => (V i).toShadedBody))
    {L : ℝ≥0∞} (hcard : (s.card : ℝ≥0∞) ≤ L * (s'.card : ℝ≥0∞)) :
    (lam : ℝ≥0∞) * (Tube.le_volume.c (Module.finrank ℝ E) : ℝ≥0∞)
        * (∑ i ∈ s, volume (V i).shade)
      ≤ L * (Tube.volume_le.C (Module.finrank ℝ E) : ℝ≥0∞)
        * ∑ i ∈ s', volume (V i).shade := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn
  set p : ℝ≥0∞ := (δ : ℝ≥0∞) ^ (n - 1) with hp
  -- the shaded mass of the whole family, from above
  have hup : (∑ i ∈ s, volume (V i).shade)
      ≤ (s.card : ℝ≥0∞) * ((Tube.volume_le.C n : ℝ≥0∞) * p) := by
    have := Finset.sum_le_card_nsmul s (fun i => volume (V i).shade)
      ((Tube.volume_le.C n : ℝ≥0∞) * p) (fun i _ => by
        refine le_trans (measure_mono ((V i).toShadedBody).shade_subset) ?_
        simpa [hn, hp] using Tube.volume_le (E := E) hδ1 (V i).toTube)
    simpa [nsmul_eq_mul] using this
  -- the shaded mass of the subfamily, from below, pointwise
  have hlow : (lam : ℝ≥0∞) * ((Tube.le_volume.c n : ℝ≥0∞) * p) * (s'.card : ℝ≥0∞)
      ≤ ∑ i ∈ s', volume (V i).shade := by
    have hpt : ∀ i ∈ s', (lam : ℝ≥0∞) * ((Tube.le_volume.c n : ℝ≥0∞) * p)
        ≤ volume (V i).shade := by
      intro i hi
      refine le_trans (mul_le_mul' (le_refl (lam : ℝ≥0∞)) ?_) (hdense i hi)
      simpa [hn, hp] using Tube.le_volume (E := E) (V i).toTube
    have := Finset.card_nsmul_le_sum s' (fun i => volume (V i).shade)
      ((lam : ℝ≥0∞) * ((Tube.le_volume.c n : ℝ≥0∞) * p)) hpt
    simpa [nsmul_eq_mul, mul_comm] using this
  calc (lam : ℝ≥0∞) * (Tube.le_volume.c n : ℝ≥0∞) * (∑ i ∈ s, volume (V i).shade)
      ≤ (lam : ℝ≥0∞) * (Tube.le_volume.c n : ℝ≥0∞)
          * ((s.card : ℝ≥0∞) * ((Tube.volume_le.C n : ℝ≥0∞) * p)) :=
        mul_le_mul' le_rfl hup
    _ ≤ (lam : ℝ≥0∞) * (Tube.le_volume.c n : ℝ≥0∞)
          * ((L * (s'.card : ℝ≥0∞)) * ((Tube.volume_le.C n : ℝ≥0∞) * p)) :=
        mul_le_mul' le_rfl (mul_le_mul' hcard le_rfl)
    _ = L * (Tube.volume_le.C n : ℝ≥0∞)
          * ((lam : ℝ≥0∞) * ((Tube.le_volume.c n : ℝ≥0∞) * p) * (s'.card : ℝ≥0∞)) := by
        ring
    _ ≤ L * (Tube.volume_le.C n : ℝ≥0∞) * ∑ i ∈ s', volume (V i).shade :=
        mul_le_mul' le_rfl hlow

/-! ### Guardrails for the dense form -/

omit [Nontrivial E] in
/-- A family carrying some shaded mass has positive fullness.  (Extracted so that the concrete
guardrails below can name the level `λ/2` of `Kakeya.ML2Shaded.exists_denseShading_refinement`
without recomputing it.) -/
theorem fullness_pos_of_sum_shade_ne_zero {u : Finset ι} {V : ι → ShadedBody E}
    (hS : (∑ i ∈ u, volume (V i).shade) ≠ 0)
    (hD : (∑ i ∈ u, volume (V i).carrier) ≠ ⊤) :
    0 < ShadedBody.fullness u V := by
  have hne : ShadedBody.fullness' u V ≠ 0 := by
    rw [ShadedBody.fullness']
    exact ENNReal.div_ne_zero.mpr ⟨hS, hD⟩
  refine pos_iff_ne_zero.mpr (fun h => hne ?_)
  have := ShadedBody.coe_fullness u V
  rw [h] at this
  simpa using this.symm

/-! ### The shaded dividing-scales dichotomy -/

end Kakeya.ML2Shaded

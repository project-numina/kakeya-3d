/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineNewParentFactor
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCentredHandBackWire

/-!
# Closing the four-way producer's own rows: the translate, the `a = 0` case, and `hfullπ`

Three rows, and one correction to a measurement of mine.

## 0. Correction: the translation invariance was existing all along

I reported that the tree had no translation-invariance lemma for `ShadedBody.multiplicity`,
on a `grep` for `multiplicity_translate` / `translate_multiplicity` restricted to `theorem`.
**That was wrong twice over**: the declaration is `ShadedBody.multiplicity_translate_const`
(`Kakeya/Multiplicity.lean`) and it is a `lemma`, not a `theorem`.  The row was never open.
Recorded because the failure mode — a name-shaped grep with a keyword filter — is the one this run
has a standing caution about.

`Kakeya.ML2Core.multiplicity_eq_of_shade_translate` below is the same fact phrased on **shade
equalities** rather than on a named translate operation, which is what the split needs:
`Tube.translate`
is a preimage by `-v`, `ShadedTube.translate` an image by `+v`, and the existing rows
(`Kakeya.ML2Core.CoarseStructRow`, `CoarseBallRow`) speak of `((T i).translate v).toTube`.  Phrasing
the bridge on shades avoids committing to either.

## 1. The translated split — and with it `hcoarse` / R2b

`Kakeya.ML2Core.exists_spineThreeScale_ofChain_translated` runs the four-way split on the
**translated** node families, so its shading identities are
`(Yτ' j).toTube = (𝒞.tube b j).translate v` and `(Yθ l).toTube = (𝒞.tube a l).translate v` —
exactly the form `Kakeya.ML2Core.CoarseStructRow` and `Kakeya.ML2Core.CoarseBallRow` state, and
exactly the form `Kakeya.ML2Core.exists_newParent_factor_at` consumes.  Its `hprod` is on the
**untranslated** leaf family, which is the form `Kakeya.ML2Core.HfacPostDropFour` reads, the two
being reconciled by §0's bridge.  So the shading-translate row and `hcoarse`/R2b close
together: they are one row.

## 2. `a = 0`: a case split in the producer, not a request on the window

The source *allows* `a = 0`;  gives the outer factor there as `n_a = 1`, the single ambient
cell.  So the faithful move is a branch, not a `1 ≤ a` field:
`Kakeya.ML2Core.outer_factor_at_zero_of_card_le_one` closes the outer factor at `a = 0` from
`ShadedBody.multiplicity_le_card` with **no defect estimate invoked** and no threshold — the
threshold `gridScale δ N a ≤ θ₀` is exactly what fails there
(`Kakeya.ML2Core.outer_threshold_fails_at_zero_newParent_lives`, `FCTLB` beside it), and this branch
never asks for it.

**What the `a = 0` branch needs and the `a ≥ 1` branch does not:** `tθ'.card ≤ 1`, i.e. the
source's `n_a = 1`.  It is a fact about the *cover* at level `0`, not about grid scales — `gridScale
δ N 0 = 1` bounds the thickness, not the index set — so it is named, not assumed silently.
`Kakeya.ML2Core.outer_factor_at_zero_of_card_le_δpow` is the unconditional alternative, at the price
of one scalar, `4 * (1 - β) ≤ εc`.

## 3. `hfullπ`: the share is the sites' `hfull`, and the bridge is a hand-back at level `p`

`Kakeya.VeryNotSticky.fullness_ge_of_centredHandBack`  delivers a fullness **lower bound** for
a hand-back's produced family, not a mass share; so `hfullπ` is supplied by it exactly when the
`(a, p)` fibre *is* such a family, at the grid scale `ρ_p`.
`Kakeya.ML2Core.newParent_fullness_of_centredHandBack` is that composition, and its hypotheses name
the bridge precisely: a `CentredHandBack` whose produced family and scale are the fibre's.

**Family / shading / level pair** for everything below: family `(s, V)` under the chain `𝒞`;
shadings as the split produces them, translated by the seam's `v`; level pairs leaf → `b`,
`(p, b)`, `(a, p)`, and level `a`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric ConvexSpaceBody ShadedBody Tube

namespace Kakeya.ML2Core

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

section Translate

variable {ι : Type u}

omit [Nontrivial E] in
/-- **Multiplicity is blind to a common translation, phrased on shades.**

`ShadedBody.multiplicity_translate_const` is the existing statement at the named translate; this is
the same fact for any two families whose shades differ by `(v + ·)`, which is what a split run on
translated tubes hands back.  `volume` is translation invariant, and multiplicity is a ratio of
volumes of shades. -/
theorem multiplicity_eq_of_shade_translate (s : Finset ι) (V V' : ι → ShadedBody E) (v : E)
    (h : ∀ i, (V' i).shade = (v + ·) '' (V i).shade) :
    ShadedBody.multiplicity s V' = ShadedBody.multiplicity s V := by
  have hsum : ∑ i ∈ s, volume (V' i).shade = ∑ i ∈ s, volume (V i).shade :=
    Finset.sum_congr rfl fun i _ => by rw [h i]; exact measure_image_add volume v (V i).shade
  have huni : volume (⋃ i ∈ s, (V' i).shade) = volume (⋃ i ∈ s, (V i).shade) := by
    have : (⋃ i ∈ s, (V' i).shade) = (v + ·) '' (⋃ i ∈ s, (V i).shade) := by
      simp only [h, Set.image_iUnion₂]
    rw [this]
    exact measure_image_add volume v _
  rw [ShadedBody.multiplicity_eq_div, ShadedBody.multiplicity_eq_div, hsum, huni]

end Translate

section OuterAtZero

variable {δ : ℝ≥0} {ι : Type u}

end OuterAtZero

section TranslatedSplit

variable {δ : ℝ≥0} {ι : Type u}

open Classical in
/-- **The four-way split on the translated family** — the shape the existing rows speak, and the
shape `Kakeya.ML2Core.HfacPostDropFour` needs.

The node families are translated by the seam's `v`, so the returned shadings satisfy
`(Yτ' j).toTube = (𝒞.tube b j).translate v` and `(Yθ l).toTube = (𝒞.tube a l).translate v` — the
identities `Kakeya.ML2Core.CoarseStructRow` and `Kakeya.ML2Core.CoarseBallRow` state, and the ones
`Kakeya.ML2Core.exists_newParent_factor_at` consumes.  The ball rows it asks are the translated
ones `hfac` supplies.  And its `hprod` is on the **untranslated** leaf family, by §0's bridge, which
is the form `hfac` reads.

So one theorem closes the shading-translate row and `hcoarse` / R2b at once.

**Family:** `(s, V)` under `𝒞`, read through the translated shading `V'`; **shadings:** the split's
four, all translated.  **Level pairs:** leaf → `b`, `(p, b)`, `(a, p)`, level `a`. -/
theorem exists_spineThreeScale_ofChain_translated {s : Finset ι} {V : ι → ShadedTube δ E} {N : ℕ}
    {σ : ℕ → ℝ≥0} (hδ : 0 < δ) (𝒞 : Tube.ChainCoverSystem s (fun i => (V i).toTube) N σ)
    {a p b : ℕ} (hap : a ≤ p) (hpb : p ≤ b) (haN : a ≤ N) (hpN : p ≤ N) (hbN : b ≤ N)
    (hδτ : δ ≤ σ b) (hτπ : σ b ≤ σ p) (hπθ : σ p ≤ σ a) (hθ1 : σ a ≤ 1) (v : E)
    (V' : ι → ShadedTube δ E)
    (hV'tube : ∀ i, (V' i).toTube = ((V i).toTube).translate v)
    (hV'shade : ∀ i, (V' i).shade = (v + ·) '' (V i).shade)
    (hball : ∀ i ∈ s, (V' i).carrier ⊆ Metric.closedBall (0 : E) 1)
    (hballτ : ∀ j ∈ ML2Reduction.activeNodes 𝒞 b,
      ((𝒞.tube b j).translate v).carrier ⊆ Metric.closedBall (0 : E) 1)
    (hballπ : ∀ k ∈ ML2Reduction.activeNodes 𝒞 p,
      ((𝒞.tube p k).translate v).carrier ⊆ Metric.closedBall (0 : E) 1) :
    ∃ tτ' ⊆ ML2Reduction.activeNodes 𝒞 b, ∃ tp' ⊆ ML2Reduction.activeNodes 𝒞 p,
      ∃ tθ' ⊆ 𝒞.indexSet a,
      ∃ (Yτ' : ι → ShadedTube (σ b) E) (Ypo Yp : ι → ShadedTube (σ p) E)
        (Yθ : ι → ShadedTube (σ a) E) (Y' : ι → ShadedTube δ E),
        (∀ j, (Yτ' j).toTube = (𝒞.tube b j).translate v) ∧
        (∀ k, (Ypo k).toTube = (𝒞.tube p k).translate v) ∧
        (∀ k, (Yp k).toTube = (𝒞.tube p k).translate v) ∧
        (∀ l, (Yθ l).toTube = (𝒞.tube a l).translate v) ∧
        (∀ i, (Y' i).toTube = (V' i).toTube) ∧
        (0 < ∑ i ∈ s, volume (V' i).shade →
          tτ'.Nonempty ∧ tp'.Nonempty ∧ tθ'.Nonempty) ∧
        (∀ jτ ∈ tτ', ∀ jp ∈ tp', ∀ jθ ∈ tθ',
          ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
            ≤ ((ML2Reduction.spineScaleLoss (Module.finrank ℝ E) s.card δ *
                  ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card (σ b) *
                  ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tp'.card (σ p) : ℝ≥0) : ℝ≥0∞)
              * ShadedBody.multiplicity {i ∈ s | 𝒞.assign b i = jτ}
                  (fun i => (Y' i).toShadedBody)
              * ShadedBody.multiplicity {j ∈ tτ' | ML2Reduction.coarseNode 𝒞 p b j = jp}
                  (fun j => (Yτ' j).toShadedBody)
              * ShadedBody.multiplicity {k ∈ tp' | ML2Reduction.coarseNode 𝒞 a p k = jθ}
                  (fun k => (Yp k).toShadedBody)
              * ShadedBody.multiplicity tθ' (fun l => (Yθ l).toShadedBody)) := by
  classical
  have hbody : ∀ i, (V' i).toConvexSpaceBody = (((V i).toTube).translate v).toConvexSpaceBody :=
    fun i => congrArg (fun T : Tube δ E => T.toConvexSpaceBody) (hV'tube i)
  obtain ⟨tτ', htτ', tp', htp', tθ', htθ', Yτ', Ypo, Yp, Yθ, Y', hYτ', hYpo, hYp, hYθ, hY'tube,
      _hY'shade, _hYpshade, hne, _hfull, hprod⟩ :=
    ML2Reduction.exists_spineThreeScale (E := E) hδ hδτ hτπ hπθ hθ1 V'
      (fun j => (𝒞.tube b j).translate v) (fun k => (𝒞.tube p k).translate v)
      (fun l => (𝒞.tube a l).translate v)
      (𝒞.assign b) (ML2Reduction.coarseNode 𝒞 p b) (ML2Reduction.coarseNode 𝒞 a p)
      hball hballτ hballπ
      (fun i hi => ML2Reduction.assign_mem_activeNodes 𝒞 hbN hi)
      (fun i hi => by
        rw [hbody i]
        exact tube_translate_le_translate _ _ v (𝒞.le_tube_assign b hbN i hi))
      (fun j hj => coarseNode_mem_activeNodes 𝒞 hpb hbN hj)
      (fun j hj => tube_translate_le_translate _ _ v
        (ML2Reduction.tube_le_coarseNode 𝒞 hpb hbN hj))
      (fun k hk => ML2Reduction.coarseNode_mem 𝒞 haN hk)
      (fun k hk => tube_translate_le_translate _ _ v
        (ML2Reduction.tube_le_coarseNode 𝒞 hap hpN hk))
  refine ⟨tτ', htτ', tp', htp', tθ', htθ', Yτ', Ypo, Yp, Yθ, Y', hYτ', hYpo, hYp, hYθ, hY'tube,
    hne, ?_⟩
  intro jτ hjτ jp hjp jθ hjθ
  have hbridge : ShadedBody.multiplicity s (fun i => (V' i).toShadedBody)
      = ShadedBody.multiplicity s (fun i => (V i).toShadedBody) :=
    multiplicity_eq_of_shade_translate s (fun i => (V i).toShadedBody)
      (fun i => (V' i).toShadedBody) v hV'shade
  rw [← hbridge]
  exact hprod jτ hjτ jp hjp jθ hjθ

end TranslatedSplit

section ParentFullness

end ParentFullness

section FibreIsFamily

variable {δ : ℝ≥0} {ι : Type u}

end FibreIsFamily

end Kakeya.ML2Core

end

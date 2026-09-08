/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineRungWiring
public import Kakeya.DimensionThree.MainLemma2.LineEssDistinct
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineMiddleProducer
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEDExtraction
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEDMultBound
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCountClause
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCanonicalCover

/-!
# GC-1 — the line-based ED twin of the GeometricCore middle factor, and the covering bridge

This follows GWZ using `Reduction/SpineRefinedFloor.lean` for the
`hfloor`/`hmid` decomposition and `MainLemma2/LineEssDistinct.lean` for
line-based essential distinctness, the degree bound, and the conversion between notions.

## What the refined text asks for, and what is done with it

The GWZ proof runs every level of its towers at **line-based `A`-essential distinctness**: `#{T ∈ 𝕋 : T ⊂ N_{5δ}(L)} ≤ A` for every complete line `L`, with the absolute
constants `A₀ = 2·223⁶` (the canonical cover) and `A₁ = 2·641⁶` (the centred canonical
cover).  The tree's Section-9 interfaces — above all the count clause of the
protected Lemma 9.1 — consume the *pairwise* volume notion `IsEssentiallyDistinct`.  The bridge
between them is E0's

`IsLineEssDistinctAt C_n A 𝕋  ⇒  edDegree ≤ A − 1  ⇒  a pairwise-ED subfamily of ≥ 1/A of the count`

(`Kakeya.VeryNotSticky.edDegree_le_of_isLineEssDistinctAt`,
`Kakeya.VeryNotSticky.exists_pairwise_of_isLineEssDistinctAt`), a **theorem**, never an axiom.
Its radius is the tree's two-tube overlap constant `C_n = Kakeya.Tube.tubeOverlapCoreClose.C 3`
(`≈ 101`), not the refined `5`: that is the one gap E0 measured and did not paper over, and every
statement below therefore reads `IsLineEssDistinctAt (Tube.tubeOverlapCoreClose.C 3)`, a
**stronger** hypothesis than the refined `IsLineEssDistinct` (`IsLineEssDistinctAt.mono_radius`
runs the other way).  `Kakeya.VeryNotSticky.LineEDLevelsAt` is
the level datum at that radius, with `Kakeya.VeryNotSticky.LineEDLevels` its refined `K = 5`
instance.

## What this buys: `SpineEDExtraction`'s `M` price becomes an absolute constant

`Kakeya.ML2Reduction.canonicalCoverAt_of_upstairs_edMult` prices the canonical cover by the
family's own ED-multiplicity `M`, and the only existing producer of `M`
(`Kakeya.ML2Reduction.edMultNat_le_of_upstairs_essDistinct`) needs the upstairs family to be
**pairwise** essentially distinct.  `canonicalCoverAt_of_upstairs_lineED` below replaces that
hypothesis by line-based `A`-ED and the price by the product of two absolutes,
`A · ⌈C₃(R)⌉` — so the budget clause is a *threshold on the scale*, not a competition between
`δ`-powers (`exists_threshold_lineED_budget`).  This is the refined covering bridge's charge
"line-based ED charges at most `A₁` surviving `m`-cells to one `W`" in the tree's
vocabulary.

## Main declarations

* `Kakeya.ML2Core.lineEDLevelConstant` — `A₁ = 2·641⁶`, a named absolute.
* E0's `Kakeya.VeryNotSticky.LineEDLevelsAt`, `lineEDLevels_iff_at` (repointed here) — the level
  datum at a
  general neighbourhood radius, and the refined `K = 5` reading.
* `Kakeya.ML2Reduction.canonicalCoverAt_of_upstairs_lineED`,
  `Kakeya.ML2Reduction.canonicalCover_of_upstairs_lineED` — **the covering bridge**: the
  canonical-cover datum from line-ED upstairs, at the absolute price.
* `Kakeya.ML2Core.canonicalCover_of_lineEDNodes` — the additive twin of
  `Kakeya.ML2Core.canonicalCover_of_edNodes`.
* `Kakeya.ML2Core.middle_factor_of_canonicalCover_sharp` — the sharp middle factor with the
  canonical-cover datum factored out of `Kakeya.ML2Core.middle_factor_of_edNodes_sharp` (which is
  **not** re-cut;  forbids that, and it is re-derived below as
  `middle_factor_of_edNodes_sharp'` as a control that the factorisation is faithful).
* `Kakeya.ML2Core.middle_factor_of_lineEDNodes_sharp` — **the additive twin**: the same
  conclusion, the same exponent `47 η_k/5`, with the line-based ED clause and the `A₁`-loaded
  budget.
* `Kakeya.ML2Core.geometricCoreAt_of_lineEDLevels` — the wiring: `GeometricCoreAt` from the
  refined count floor, a middle factor that may read the line-ED levels, and a producer of those
  levels (U1's output at the wiring level).
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Set Topology Filter ConvexSpaceBody ShadedBody

namespace Kakeya.ML2Core

universe u

/-! ## The refined absolute constant `A₁`, and the level datum at a general radius -/

section Constants

end Constants

section LevelsAt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*}

/-! ### Spelling bridge for the line's neighbourhood

E0's existing `Kakeya.VeryNotSticky.IsLineEssDistinctAt` reads the line's neighbourhood as
`lineNbhd p d r = Metric.cthickening r (lineSet p d)` with `lineSet p d = {y | ∃ t : ℝ,
y = p + t • d}` (the C6-a spelling).  The other rendering in circulation is the inline
`Metric.cthickening r (Set.range fun t ↦ p + t • d)`.  The two sets are equal but **not**
definitionally so — `Set.range f = {y | ∃ t, f t = y}` and `lineSet` is `{y | ∃ t, y = f t}`, the
defining equation the other way round — so a `rfl` between the two readings of the predicate does
not typecheck.  `range_line_eq_setOf` is the rewrite, E0's own form of it is
`Kakeya.VeryNotSticky.lineNbhd_eq_cthickening_range`, and `isLineEssDistinctAt_iff_range` states
the predicate in the inline spelling so that either reading can be consumed here.

Nothing else in this file touches either spelling: every declaration below consumes
`IsLineEssDistinct` / `IsLineEssDistinctAt` abstractly — no `cthickening`, no `Set.range` and
no `lineNbhd` occurs outside this block — so the choice costs this leaf nothing. -/

end LevelsAt

end Kakeya.ML2Core

namespace Kakeya.ML2Reduction

universe u

variable {θ τ : ℝ≥0}

/-! ## The covering bridge: the canonical-cover datum from line-ED upstairs -/

section CoveringBridge

/-- **The push-up price** `⌈C₃(R)⌉` of
`Kakeya.ML2Reduction.edMultNat_le_of_upstairs_essDistinct`, named once so the budget clauses
below read as a product of two absolutes. -/
noncomputable def lineEDPushConstant (R : ℝ) : ℕ :=
  ⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
      (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : ℝ≥0) : ℝ)⌉₊

/-- **`canonicalCoverAt_of_upstairs_lineED` at a named count constant**
Identical to its sibling above except that the count is read
at `Kc` rather than at `Kakeya.ML2Reduction.spineOuterCountLoss R`; the count is a free parameter
of `Kakeya.ML2Reduction.canonicalCoverAt_of_used_of_edMult`, so nothing about the extraction
changes.  The centring transport needs the `Kakeya.VeryNotSticky.centringCountLossConstant R` form. -/
theorem canonicalCoverAt_of_upstairs_lineED_const {σ : ℝ≥0} {R ζ ζ' Kc : ℝ}
    (hKc0 : 0 ≤ Kc)
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R)
    (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {s : Finset α} (𝕋 : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    {ρ : ℝ≥0} (hρ0 : 0 < ρ) (hρ4 : (ρ : ℝ) ≤ 1 / 4)
    {κ₀ : Type u} (t : Finset κ₀) (W : κ₀ → Tube (ρ * θ) (EuclideanSpace ℝ (Fin 3)))
    (hsubW : ∀ k ∈ t, (W k).carrier ⊆ T₀.carrier)
    (hused : ∀ k ∈ t, ∃ i ∈ s, (𝕋 i).carrier ⊆ (W k).carrier)
    {A : ℕ} (hA0 : 0 < A)
    (hline : Kakeya.VeryNotSticky.IsLineEssDistinctAt (Tube.tubeOverlapCoreClose.C 3) A t W)
    (hslack : (A : ℝ) * (lineEDPushConstant R : ℝ) * Kc
      ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    (hcard : (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ)) :
    ∃ (κ₁ : Type u) (u : Finset κ₁) (V : κ₁ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
      ((u : Set κ₁).Pairwise
        fun j k ↦ _root_.IsEssentiallyDistinct (V j).carrier (V k).carrier) ∧
      (∀ j ∈ u, ∃ i ∈ s,
        (spineFamily (spineRescaleUnit hsit.pos_ambient T₀ hR) 𝕋 i).toConvexSpaceBody
          ≤ (V j).toConvexSpaceBody) ∧
      Kc * (ρ : ℝ) ^ (-2 - ζ) ≤ (u.card : ℝ) := by
  classical
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hρθ0 : 0 < ρ * θ := mul_pos hρ0 hsit.pos_ambient
  have hρ1 : ρ ≤ 1 := by
    have : (ρ : ℝ) ≤ 1 := by linarith
    exact_mod_cast this
  have hρθ1 : ρ * θ ≤ 1 := by
    calc ρ * θ ≤ 1 * 1 := by gcongr; exact hsit.ambient_le_one
      _ = 1 := one_mul 1
  have hline' : Kakeya.VeryNotSticky.IsLineEssDistinctAt
      (Tube.tubeOverlapCoreClose.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) A t W := by
    rwa [hfr]
  obtain ⟨t', ht's, hpair, -, hret⟩ :=
    Kakeya.VeryNotSticky.exists_pairwise_of_isLineEssDistinctAt hρθ0 hρθ1 hline' (fun _ ↦ 0)
  have hAeq : A - 1 + 1 = A := Nat.succ_pred_eq_of_pos hA0
  rw [hAeq] at hret
  have hsubW' : ∀ k ∈ t', (W k).carrier ⊆ T₀.carrier := fun k hk ↦ hsubW k (ht's hk)
  have hused'0 : ∀ k ∈ t', ∃ i ∈ s, (𝕋 i).carrier ⊆ (W k).carrier := fun k hk ↦ hused k (ht's hk)
  have hM : ∀ i ∈ t', (t'.filter (fun j ↦
      ¬ _root_.IsEssentiallyDistinct
          (outerTube hsit.pos_ambient T₀ hR ρ (W j)).carrier
          (outerTube hsit.pos_ambient T₀ hR ρ (W i)).carrier)).card
      ≤ lineEDPushConstant R :=
    fun i hi ↦ edMultNat_le_of_upstairs_essDistinct hsit hR hfr T₀ hρ0 hρ4 W hsubW' hpair hi
  have hsit2 := isRescalingSituation_scaledUp hsit hρ0 hρ4
  have hused' := outerTube_used_of_used hfr hsit2 hR (ratio_scaledUp hsit.pos_ambient ρ)
    T₀ 𝕋 (t := t') W hsubW' hused'0
  have hρR : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ0
  have hAR : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA0
  have hne' : t'.Nonempty := by
    rw [← Finset.card_pos]
    have hpos : (0 : ℝ) < (ρ : ℝ) ^ (-2 - ζ') := Real.rpow_pos_of_pos hρR _
    have h1 : (0 : ℝ) < (t.card : ℝ) := lt_of_lt_of_le hpos hcard
    have h2 : 0 < t.card := by exact_mod_cast h1
    have h3 : t.card ≤ A * t'.card := hret
    rcases Nat.eq_zero_or_pos t'.card with hz | hp
    · rw [hz, Nat.mul_zero] at h3; omega
    · exact hp
  have hM0 : 0 < lineEDPushConstant R :=
    lt_of_lt_of_le zero_lt_one
      (one_le_edMult hρ0 (fun k ↦ outerTube hsit.pos_ambient T₀ hR ρ (W k)) hne' hM)
  refine canonicalCoverAt_of_used_of_edMult hsit.pos_ambient T₀ (hR := hR) 𝕋 hρ0 t'
    (fun k ↦ outerTube hsit.pos_ambient T₀ hR ρ (W k)) hM0 hM hused' ?_
  have hLam : (0 : ℝ) ≤ Kc := hKc0
  have hsplit : (ρ : ℝ) ^ (-(ζ' - ζ)) * (ρ : ℝ) ^ (-2 - ζ) = (ρ : ℝ) ^ (-2 - ζ') := by
    rw [← Real.rpow_add hρR]; ring_nf
  have hstep : (A : ℝ) * ((lineEDPushConstant R : ℝ)
      * (Kc * (ρ : ℝ) ^ (-2 - ζ))) ≤ (A : ℝ) * (t'.card : ℝ) := by
    calc (A : ℝ) * ((lineEDPushConstant R : ℝ)
            * (Kc * (ρ : ℝ) ^ (-2 - ζ)))
        = ((A : ℝ) * (lineEDPushConstant R : ℝ) * Kc)
            * (ρ : ℝ) ^ (-2 - ζ) := by ring
      _ ≤ (ρ : ℝ) ^ (-(ζ' - ζ)) * (ρ : ℝ) ^ (-2 - ζ) :=
          mul_le_mul_of_nonneg_right hslack (Real.rpow_nonneg hρR.le _)
      _ = (ρ : ℝ) ^ (-2 - ζ') := hsplit
      _ ≤ (t.card : ℝ) := hcard
      _ ≤ (A : ℝ) * (t'.card : ℝ) := by exact_mod_cast hret
  exact le_of_mul_le_mul_left hstep hAR

end CoveringBridge

end Kakeya.ML2Reduction

namespace Kakeya.ML2Core

universe u

/-! ## The middle factor with the canonical-cover datum factored out -/

section Factored

open Classical in
/-- **The sharp middle factor, with the canonical-cover datum as a binder.**

`Kakeya.ML2Core.middle_factor_of_edNodes_sharp` (existing, unchanged, and **not** re-cut — see
) reaches step 10 through one intermediate object, the canonical-cover
datum `hcanon` of `Kakeya.ML2Reduction.fine_factor_of_lemma91At_of_canonicalCover`.  Everything
between the ED-node clause and `hcanon` is the producer's business; everything after it is the
same for every producer.  This theorem is that theorem with `hED`, `hbudget` and `hwin4` replaced
by `hcanon` itself; the existing theorem is re-derived from it below
(`middle_factor_of_edNodes_sharp'`) as a control that the factorisation is faithful, and the
line-based twin is derived from it through the covering bridge. -/
theorem middle_factor_of_canonicalCover_sharp
    {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ} {k : ℕ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hk : k < ML2Spine.spineCount ϖ ε₁)
    -- the ambient window and the transport 
    {δ θ τ δt : ℝ≥0} {Rout : ℝ} {w : ℝ}
    (hsitOut : Tube.IsRescalingSituation θ τ δt Rout 3) (hRout : 0 < Rout)
    (hτθ : (τ : ℝ) / (θ : ℝ) ≤ 4 * (δt : ℝ))
    (Tθ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {fib : Finset α}
    (Y : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    (hsubOut : ∀ j ∈ fib, (Y j).carrier ⊆ Tθ.carrier)
    (hw : 0 ≤ w) (hsep : δt ≤ δ ^ w)
    -- the rescaled world 
    {b δ' : ℝ≥0} {R : ℝ}
    (hδ0 : 0 < δt) (hδ1 : δt ≤ 1) (hδ'0 : 0 < δ') (hb1 : b ≤ 1) (hδtb : δt ≤ b)
    (hbw : δt ^ ML2Spine.spineEps₂ ϖ ε₁ ≤ b) (hprod : δ' * b = δt)
    {κc : Type u} {t' : Finset κc} {Zρ : κc → ShadedTube b (EuclideanSpace ℝ (Fin 3))} {ηc : ℝ}
    (hcoarse : ∀ (dt : ℝ≥0), dt ≠ 0 → dt ≤ b → b ≤ 1 →
      ∀ {ι : Type u} (t : Finset ι) (T : ι → ShadedTube b (EuclideanSpace ℝ (Fin 3))),
        (∀ i, (T i).carrier ⊆ closedBall 0 1) →
        (ShadedBody.fullness t (fun i ↦ (T i).toShadedBody) : ℝ) ≥ (b : ℝ) ^ ηc →
        Kakeya.maxDensity t (fun i ↦ (T i).toConvexSpaceBody)
          ≤ (dt : ℝ≥0∞) ^ (-(12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
              / (ML2Spine.spineDiv ϖ ε₁ * β))) →
        ShadedBody.multiplicity t (fun i ↦ (T i).toShadedBody)
          ≤ (dt : ℝ≥0∞) ^ (-(2 * (12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
              / (ML2Spine.spineDiv ϖ ε₁ * β)))) * (t.card : ℝ≥0∞) ^ β)
    (hballb : ∀ j, (Zρ j).carrier ⊆ closedBall 0 1)
    (hfullb : (ShadedBody.fullness t' (fun j ↦ (Zρ j).toShadedBody) : ℝ) ≥ (b : ℝ) ^ ηc)
    (hDb : Kakeya.maxDensity t' (fun j ↦ (Zρ j).toConvexSpaceBody)
      ≤ (δt : ℝ≥0∞) ^ (-(12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
          / (ML2Spine.spineDiv ϖ ε₁ * β))))
    {s' : Finset α} (hs' : s' ⊆ fib)
    {U' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))}
    (hsit : Tube.IsRescalingSituation b δt δ' R 3) (hR : 0 < R) (hR1 : 1 ≤ R)
    (hτσ : (δt : ℝ) / (b : ℝ) ≤ 4 * (δ' : ℝ))
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3)))
    (hsubfib : ∀ i ∈ fib,
      (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).carrier ⊆ T₀.carrier)
    {cst ζ ηd : ℝ}
    (mm : EuclideanSpace ℝ (Fin 3)) {qc : ℝ} (hqc0 : 0 < qc) (h3qc : 3 * qc ≤ ηd)
    (hcb : Kakeya.VeryNotSticky.CentredHandBack hsit hR T₀ mm qc fib s'
      (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U')
    (hL91 : ML2Reduction.Lemma91At.{u} β ϖ ζ
      (gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) + 3 * qc) ηd δ')
    -- the exact negation of the vacuity condition
    -- `Kakeya.VeryNotSticky.lemma91Binders_vacuous_of_exponents` (cited by name only — this is a
    -- hypothesis, not a consumed term, so the witness leaf is NOT imported): Lemma 9.1's binder
    -- list is jointly unsatisfiable whenever `2 + ηd < (1 - ϖ) * (2 + ζ)`, and `hζ` is exactly
    -- its negation, so it is what keeps `hL91` above from being vacuously true.  Corroborated
    -- caller-side by the source's own `ζ ≤ (4/5) ζ_*`.
    (hζ : ζ * (1 - ϖ) ≤ ηd + 2 * ϖ)
    (hloss : ML2Reduction.outerLoss R ≤ δ' ^ (-cst))
    (_hmax : Kakeya.maxDensity fib (fun i ↦
        (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).toConvexSpaceBody)
      ≤ (δ' : ℝ≥0∞) ^ (-(ηd - cst)))
    (hfull : ShadedBody.fullness s' (fun i ↦ (U' i).toShadedBody) ≥ δ' ^ ηd)
    (huni : ∃ C : ℝ≥0, 1 ≤ C ∧ (C : ℝ≥0∞) ≤ (δ' : ℝ≥0∞) ^ (-ηd) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s' U' (Tube.ssfGridLen δ') C))
    -- step 10's datum, factored out: the count clause at the CENTRED representatives, which is
    -- `Kakeya.ML2Reduction.Lemma91At`'s clause verbatim.  A caller holding the canonical cover on
    -- the *rescaled bodies* reaches this through `Kakeya.VeryNotSticky.CountTransport`.
    (hcnt : ∀ ρ : ℝ≥0, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      ∃ (κ₁ : Type u) (tρ : Finset κ₁) (Tρ : κ₁ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
        (tρ : Set κ₁).Pairwise
          (fun j l ↦ _root_.IsEssentiallyDistinct (Tρ j).carrier (Tρ l).carrier) ∧
        (∀ j ∈ tρ, ∃ i ∈ s', (U' i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
        (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ))
    -- step 9, the cardinality multiplicativity and the loss ledger
    {Cf L Cu : ℝ≥0∞} {Nm : ℕ} {κ : ℝ}
    (hCf1 : (1 : ℝ≥0∞) ≤ Cf)
    (hsplit : ShadedBody.multiplicity fib (fun i ↦
        (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).toShadedBody)
      ≤ L * (ShadedBody.multiplicity t' (fun j ↦ (Zρ j).toShadedBody)
        * ShadedBody.multiplicity fib (fun i ↦
            (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).toShadedBody)))
    (hcard : (t'.card : ℝ≥0∞) * (fib.card : ℝ≥0∞) ≤ Cu * (Nm : ℝ≥0∞))
    (hLoss : L * Cf * Cu ^ β ≤ (δt : ℝ≥0∞) ^ (-κ))
    (hκ : κ ≤ ML2Spine.spineRung β ϖ ε₁ gain dens k / (20 * ML2Spine.spineDiv ϖ ε₁)) :
    ShadedBody.multiplicity fib (fun j ↦ (Y j).toShadedBody)
      ≤ (δ : ℝ≥0∞) ^ (w * (47 * ML2Spine.spineRung β ϖ ε₁ gain dens k
          / (5 * ML2Spine.spineDiv ϖ ε₁))) * (Nm : ℝ≥0∞) ^ β := by
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hsp := ML2Spine.spineRung_isSpine (β := β) (ϖ := ϖ) (ε₁ := ε₁) (gain := gain)
    (dens := dens) hβ0 hβ1 hϖ hε₁ hgain hdens
  have hgm : 0 ≤ 47 * ML2Spine.spineRung β ϖ ε₁ gain dens k / (5 * ML2Spine.spineDiv ϖ ε₁) := by
    have h1 := hsp.rung_pos k
    have h2 := hsp.div_pos
    positivity
  refine middle_factor_of_rescaled hsitOut hRout hτθ Tθ Y hsubOut hgm hw hsep ?_
  set Z' : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3)) :=
    ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y with hZ'
  have hb4 := hcoarse δt (ne_of_gt hδ0) hδtb hb1 t' Zρ hballb hfullb hDb
  -- Step 10 on the REPRESENTED family.  The hand-back's transport is *inside* the eliminator, so
  -- the `3 qc` is charged exactly once — in `hL91`'s gain (V-3).  `hU`, `hUshade`, `hret` and
  -- `hretm` are gone: the centred representative is the `normalise` image of the rescaled body,
  -- not the rescaled body, so `hU`/`hUshade` are false and `Cf` needs only `1 ≤ Cf`.
  have h10 := ML2Reduction.fine_factor_of_lemma91At_of_canonicalCover
    (ν := gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2))
    hL91 hζ hsit hR hR1 hτσ hδ'0 hϖ.le hβ0.le hqc0 le_rfl h3qc T₀ mm hs' Z' U' hcb hsubfib hloss
    huni hcnt
  have h10' : ShadedBody.multiplicity fib (fun i ↦ (Z' i).toShadedBody)
      ≤ (δ' : ℝ≥0∞) ^ (gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2))
        * (fib.card : ℝ≥0∞) ^ β := by
    rw [← ML2Reduction.outerFamily_multiplicity hn hsit hR hτσ hsubfib]
    exact h10
  have hsplit2 : ShadedBody.multiplicity fib (fun i ↦ (Z' i).toShadedBody)
      ≤ (L * Cf) * (ShadedBody.multiplicity t' (fun j ↦ (Zρ j).toShadedBody)
        * ShadedBody.multiplicity fib (fun i ↦ (Z' i).toShadedBody)) := by
    refine hsplit.trans (mul_le_mul' ?_ le_rfl)
    calc L = L * 1 := (mul_one L).symm
      _ ≤ L * Cf := by gcongr
  exact spine_multiplicity_le_two_factors_sharp hβ0 hβ1 hϖ hε₁ hgain hdens hk hδ0 hδ1 hbw hprod
    hsplit2 hb4 h10' hcard hLoss hκ

end Factored

/-! ## Control: the existing theorem, re-derived from the factored one -/

section FactorisationControl

open Classical in
/-- **`Kakeya.ML2Core.middle_factor_of_edNodes_sharp`, re-derived.**  Binder for binder the existing
theorem, proved as `middle_factor_of_canonicalCover_sharp ∘ canonicalCover_of_edNodes`.  It is a
**control**, not a replacement: the existing theorem is untouched (
forbids re-cutting it), and this re-derivation is what certifies that the factorisation above
lost nothing — the only thing the factored theorem asks for that the existing one did not is the
canonical-cover datum the existing one built. -/
theorem middle_factor_of_edNodes_sharp'
    {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ} {k : ℕ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hk : k < ML2Spine.spineCount ϖ ε₁)
    -- the ambient window and the transport 
    {δ θ τ δt : ℝ≥0} {Rout : ℝ} {w : ℝ}
    (hsitOut : Tube.IsRescalingSituation θ τ δt Rout 3) (hRout : 0 < Rout)
    (hτθ : (τ : ℝ) / (θ : ℝ) ≤ 4 * (δt : ℝ))
    (Tθ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {fib : Finset α}
    (Y : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    (hsubOut : ∀ j ∈ fib, (Y j).carrier ⊆ Tθ.carrier)
    (hw : 0 ≤ w) (hsep : δt ≤ δ ^ w)
    -- the rescaled world 
    {b δ' : ℝ≥0} {R : ℝ}
    (hδ0 : 0 < δt) (hδ1 : δt ≤ 1) (hδ'0 : 0 < δ') (hb1 : b ≤ 1) (hδtb : δt ≤ b)
    (hbw : δt ^ ML2Spine.spineEps₂ ϖ ε₁ ≤ b) (hprod : δ' * b = δt)
    {κc : Type u} {t' : Finset κc} {Zρ : κc → ShadedTube b (EuclideanSpace ℝ (Fin 3))} {ηc : ℝ}
    (hcoarse : ∀ (dt : ℝ≥0), dt ≠ 0 → dt ≤ b → b ≤ 1 →
      ∀ {ι : Type u} (t : Finset ι) (T : ι → ShadedTube b (EuclideanSpace ℝ (Fin 3))),
        (∀ i, (T i).carrier ⊆ closedBall 0 1) →
        (ShadedBody.fullness t (fun i ↦ (T i).toShadedBody) : ℝ) ≥ (b : ℝ) ^ ηc →
        Kakeya.maxDensity t (fun i ↦ (T i).toConvexSpaceBody)
          ≤ (dt : ℝ≥0∞) ^ (-(12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
              / (ML2Spine.spineDiv ϖ ε₁ * β))) →
        ShadedBody.multiplicity t (fun i ↦ (T i).toShadedBody)
          ≤ (dt : ℝ≥0∞) ^ (-(2 * (12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
              / (ML2Spine.spineDiv ϖ ε₁ * β)))) * (t.card : ℝ≥0∞) ^ β)
    (hballb : ∀ j, (Zρ j).carrier ⊆ closedBall 0 1)
    (hfullb : (ShadedBody.fullness t' (fun j ↦ (Zρ j).toShadedBody) : ℝ) ≥ (b : ℝ) ^ ηc)
    (hDb : Kakeya.maxDensity t' (fun j ↦ (Zρ j).toConvexSpaceBody)
      ≤ (δt : ℝ≥0∞) ^ (-(12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
          / (ML2Spine.spineDiv ϖ ε₁ * β))))
    {s' : Finset α} (hs' : s' ⊆ fib)
    {U' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))}
    (hsit : Tube.IsRescalingSituation b δt δ' R 3) (hR : 0 < R) (hR1 : 1 ≤ R)
    (hτσ : (δt : ℝ) / (b : ℝ) ≤ 4 * (δ' : ℝ))
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3)))
    (hsubfib : ∀ i ∈ fib,
      (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).carrier ⊆ T₀.carrier)
    {cst ζ ζ' ηd : ℝ}
    (mm : EuclideanSpace ℝ (Fin 3)) {qc : ℝ} (hqc0 : 0 < qc) (h3qc : 3 * qc ≤ ηd)
    (hcb : Kakeya.VeryNotSticky.CentredHandBack hsit hR T₀ mm qc fib s'
      (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U')
    (hct : Kakeya.VeryNotSticky.CountTransport hsit hR T₀ mm ϖ ζ s'
      (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U')
    (hL91 : ML2Reduction.Lemma91At.{u} β ϖ ζ
      (gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) + 3 * qc) ηd δ')
    -- the exact negation of the vacuity condition
    -- `Kakeya.VeryNotSticky.lemma91Binders_vacuous_of_exponents` (cited by name only — this is a
    -- hypothesis, not a consumed term, so the witness leaf is NOT imported): Lemma 9.1's binder
    -- list is jointly unsatisfiable whenever `2 + ηd < (1 - ϖ) * (2 + ζ)`, and `hζ` is exactly
    -- its negation, so it is what keeps `hL91` above from being vacuously true.  Corroborated
    -- caller-side by the source's own `ζ ≤ (4/5) ζ_*`.
    (hζ : ζ * (1 - ϖ) ≤ ηd + 2 * ϖ)
    (hloss : ML2Reduction.outerLoss R ≤ δ' ^ (-cst))
    (hmax : Kakeya.maxDensity fib (fun i ↦
        (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).toConvexSpaceBody)
      ≤ (δ' : ℝ≥0∞) ^ (-(ηd - cst)))
    (hfull : ShadedBody.fullness s' (fun i ↦ (U' i).toShadedBody) ≥ δ' ^ ηd)
    -- AA/AB: tightened to the constant the producer actually returns
    -- (`ShadedTube.ssfUniformConst 3`, `Kakeya/ShadedUniform.lean`), with the threshold the
    -- loose bracket used to quantify away carried explicitly.  Discharged at wiring time by
    -- `exists_outerShadedUniformTubeSet_ssf` + `exists_threshold_coe_const_le_rpow_neg`.
    -- this binder is ALSO where the line-ED levels row is sourced.  The witness carries
    -- a uniform hierarchy, and `Kakeya.VeryNotSticky.lineEDLevelsAt_C3_of_huni` turns it (with
    -- `hcb`'s `centred`/`contained`/`small` rows and the uniformiser's own grid threshold) into
    -- `LineEDLevelsAt C₃ lineEDLevelsConstant _` at the NAMED constant (
    -- ): the datum is DERIVED here, never an ambient field.
    (huni : ((ShadedTube.ssfUniformConst 3 : ℝ≥0) : ℝ≥0∞) ≤ (δ' : ℝ≥0∞) ^ (-ηd) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s' U' (Tube.ssfGridLen δ')
        (ShadedTube.ssfUniformConst 3)))
    -- the ONE open input
    (hwin4 : ((δ' ^ ϖ : ℝ≥0) : ℝ) ≤ 1 / 4)
    -- CONTRACTED-bottom window `[δ'^{1-ϖ}/C, δ'^{ϖ}]` — the hand-back reads the cover
    -- at `ρ/C`.  A producer must supply this clause on the wide
    -- window.  `hbudget` below did NOT move: `Kakeya.ML2Reduction.budget_descends` carries
    -- it from `ρ` down to `ρ/C`, at the cost of the reading gap `hgap`.
    (hED : ∀ ρ : ℝ≥0, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))),
        ((t : Set κ₀).Pairwise
          fun j l ↦ _root_.IsEssentiallyDistinct (W j).carrier (W l).carrier) ∧
        (∀ l ∈ t, (W l).carrier ⊆ T₀.carrier) ∧
        (∀ l ∈ t, ∃ i ∈ s',
          (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).carrier
            ⊆ (W l).carrier) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ))
    (_hbudget : ∀ ρ : ℝ≥0, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
            (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : ℝ≥0) : ℝ)⌉₊ : ℝ)
          * (ML2Reduction.spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    -- this is `hbudget` with `centringCountLossConstant R ·` at the head of the left-hand
    -- side, so it IMPLIES `hbudget`; `hbudget` is retained only because keeps its text
    -- tree-wide.  Discharged by `exists_threshold_hup_budget`'s argument at the
    -- new constant, never assumed; `ζ < ζ'` (`hgap`) is its side condition.
    (hcntbudget : ∀ ρ : ℝ≥0, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ)
        * (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
              (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : ℝ≥0) : ℝ)⌉₊ : ℝ)
          * (ML2Reduction.spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    (hgap : ζ ≤ ζ')
    -- step 9, the cardinality multiplicativity and the loss ledger
    {Cf L Cu : ℝ≥0∞} {Nm : ℕ} {κ : ℝ}
    (hCf1 : (1 : ℝ≥0∞) ≤ Cf)
    (hsplit : ShadedBody.multiplicity fib (fun i ↦
        (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).toShadedBody)
      ≤ L * (ShadedBody.multiplicity t' (fun j ↦ (Zρ j).toShadedBody)
        * ShadedBody.multiplicity fib (fun i ↦
            (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).toShadedBody)))
    (hcard : (t'.card : ℝ≥0∞) * (fib.card : ℝ≥0∞) ≤ Cu * (Nm : ℝ≥0∞))
    (hLoss : L * Cf * Cu ^ β ≤ (δt : ℝ≥0∞) ^ (-κ))
    (hκ : κ ≤ ML2Spine.spineRung β ϖ ε₁ gain dens k / (20 * ML2Spine.spineDiv ϖ ε₁)) :
    ShadedBody.multiplicity fib (fun j ↦ (Y j).toShadedBody)
      ≤ (δ : ℝ≥0∞) ^ (w * (47 * ML2Spine.spineRung β ϖ ε₁ gain dens k
          / (5 * ML2Spine.spineDiv ϖ ε₁))) * (Nm : ℝ≥0∞) ^ β :=
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hsp := ML2Spine.spineRung_isSpine (β := β) (ϖ := ϖ) (ε₁ := ε₁) (gain := gain)
    (dens := dens) hβ0 hβ1 hϖ hε₁ hgain hdens
  middle_factor_of_canonicalCover_sharp hβ0 hβ1 hϖ hε₁ hgain hdens hk hsitOut hRout hτθ Tθ Y
    hsubOut hw hsep hδ0 hδ1 hδ'0 hb1 hδtb hbw hprod hcoarse hballb hfullb hDb hs' hsit hR hR1
    hτσ T₀ hsubfib mm hqc0 h3qc hcb hL91 hζ hloss hmax hfull
    (Kakeya.VeryNotSticky.huni_loose_of_tight huni)
    (fun ρ hρ ↦ hct ρ hρ
      (by
        -- the cover is read at the CONTRACTED radius; `hED` moved, `hbudget` did NOT —
        -- `Kakeya.ML2Reduction.budget_descends` carries it from `ρ` down to `ρ/C` 
        have hmem := Kakeya.VeryNotSticky.mem_widened_window_of_mem hρ
        have hc0 : 0 < ρ / Kakeya.VeryNotSticky.centringCoverRadiusConstant :=
          lt_of_lt_of_le (div_pos (NNReal.rpow_pos hδ'0)
            Kakeya.VeryNotSticky.edWindowContractionConstant_pos) hmem.1
        obtain ⟨κ₀, t, W, hEDt, hsubW, hused, hcard⟩ := hED _ hmem
        obtain ⟨κ₁, t₈, W', M, hsubW', hused', hM', hMρ', hcard'⟩ :=
          hstep8_of_essDistinct t W hEDt hsubW hused hcard
        exact ML2Reduction.canonicalCoverAt_of_step8_const (m := 0) (ζ' := ζ')
          (Kc := (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ))
          hsit hR T₀ _ hc0
          (le_trans (by exact_mod_cast hmem.2) hwin4) t₈ W' hsubW' hused' hM' hMρ' hcard'
          (ML2Reduction.budget_descends
            (h := ML2Reduction.hbud_of_hcntbudget (NNReal.coe_nonneg _)
              (by simpa using hcntbudget ρ hρ))
            (hρ'0 := by exact_mod_cast hc0)
            (hle := by exact_mod_cast Kakeya.VeryNotSticky.div_centringCoverRadiusConstant_le ρ)
            (he := by linarith))))
    hCf1 hsplit hcard hLoss hκ

end FactorisationControl

/-! ## The additive twin: the ED-node clause, line-based -/

section LineEDTwin

open Classical in
/-- **The additive twin of `Kakeya.ML2Core.middle_factor_of_edNodes_sharp`**
Binder for binder the existing theorem, **which is not touched**, with two changes:

* `hED`'s pairwise `IsEssentiallyDistinct` clause becomes line-based `A`-ED at the tree's two-tube
  radius `Kakeya.Tube.tubeOverlapCoreClose.C 3` — the line-based notion at the radius
  E0's bridge is proved for rather than the refined `5` (E0 §1.3: the tree's only route from
  `¬ IsEssentiallyDistinct` to a line neighbourhood has constant `≈ 101`, and the hypothesis at
  the larger radius is the *stronger* one);
* `hbudget`'s left factor gains `A` — the bridge's retention `1/A`, paid out of the reading gap
  `ζ' − ζ` exactly as `SpineCanonicalCover`'s docstring prices `Ced·Λ` today.

**The conclusion is unchanged**, so every downstream budget statement applies verbatim: the
ambient gain is still `47 η_k/5` (`Kakeya.ML2Core.ambient_sharp_gain_ge`) and the rung ledger
still closes (`Kakeya.ML2Core.rung_budget_closes_of_overhead_le_four`, composed below as
`lineED_twin_rung_budget_closes`).  The twin costs the budget exactly the constant `A`, and a
constant is a threshold on the scale, not an exponent
(`Kakeya.ML2Reduction.exists_threshold_lineED_budget`). -/
theorem middle_factor_of_lineEDNodes_sharp
    {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ} {k : ℕ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hk : k < ML2Spine.spineCount ϖ ε₁)
    -- the ambient window and the transport 
    {δ θ τ δt : ℝ≥0} {Rout : ℝ} {w : ℝ}
    (hsitOut : Tube.IsRescalingSituation θ τ δt Rout 3) (hRout : 0 < Rout)
    (hτθ : (τ : ℝ) / (θ : ℝ) ≤ 4 * (δt : ℝ))
    (Tθ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {fib : Finset α}
    (Y : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    (hsubOut : ∀ j ∈ fib, (Y j).carrier ⊆ Tθ.carrier)
    (hw : 0 ≤ w) (hsep : δt ≤ δ ^ w)
    -- the rescaled world 
    {b δ' : ℝ≥0} {R : ℝ}
    (hδ0 : 0 < δt) (hδ1 : δt ≤ 1) (hδ'0 : 0 < δ') (hb1 : b ≤ 1) (hδtb : δt ≤ b)
    (hbw : δt ^ ML2Spine.spineEps₂ ϖ ε₁ ≤ b) (hprod : δ' * b = δt)
    {κc : Type u} {t' : Finset κc} {Zρ : κc → ShadedTube b (EuclideanSpace ℝ (Fin 3))} {ηc : ℝ}
    (hcoarse : ∀ (dt : ℝ≥0), dt ≠ 0 → dt ≤ b → b ≤ 1 →
      ∀ {ι : Type u} (t : Finset ι) (T : ι → ShadedTube b (EuclideanSpace ℝ (Fin 3))),
        (∀ i, (T i).carrier ⊆ closedBall 0 1) →
        (ShadedBody.fullness t (fun i ↦ (T i).toShadedBody) : ℝ) ≥ (b : ℝ) ^ ηc →
        Kakeya.maxDensity t (fun i ↦ (T i).toConvexSpaceBody)
          ≤ (dt : ℝ≥0∞) ^ (-(12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
              / (ML2Spine.spineDiv ϖ ε₁ * β))) →
        ShadedBody.multiplicity t (fun i ↦ (T i).toShadedBody)
          ≤ (dt : ℝ≥0∞) ^ (-(2 * (12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
              / (ML2Spine.spineDiv ϖ ε₁ * β)))) * (t.card : ℝ≥0∞) ^ β)
    (hballb : ∀ j, (Zρ j).carrier ⊆ closedBall 0 1)
    (hfullb : (ShadedBody.fullness t' (fun j ↦ (Zρ j).toShadedBody) : ℝ) ≥ (b : ℝ) ^ ηc)
    (hDb : Kakeya.maxDensity t' (fun j ↦ (Zρ j).toConvexSpaceBody)
      ≤ (δt : ℝ≥0∞) ^ (-(12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
          / (ML2Spine.spineDiv ϖ ε₁ * β))))
    {s' : Finset α} (hs' : s' ⊆ fib)
    {U' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))}
    (hsit : Tube.IsRescalingSituation b δt δ' R 3) (hR : 0 < R) (hR1 : 1 ≤ R)
    (hτσ : (δt : ℝ) / (b : ℝ) ≤ 4 * (δ' : ℝ))
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3)))
    (hsubfib : ∀ i ∈ fib,
      (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).carrier ⊆ T₀.carrier)
    {cst ζ ζ' ηd : ℝ}
    (mm : EuclideanSpace ℝ (Fin 3)) {qc : ℝ} (hqc0 : 0 < qc) (h3qc : 3 * qc ≤ ηd)
    (hcb : Kakeya.VeryNotSticky.CentredHandBack hsit hR T₀ mm qc fib s'
      (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U')
    (hct : Kakeya.VeryNotSticky.CountTransport hsit hR T₀ mm ϖ ζ s'
      (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U')
    (hL91 : ML2Reduction.Lemma91At.{u} β ϖ ζ
      (gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) + 3 * qc) ηd δ')
    -- the exact negation of the vacuity condition
    -- `Kakeya.VeryNotSticky.lemma91Binders_vacuous_of_exponents` (cited by name only — this is a
    -- hypothesis, not a consumed term, so the witness leaf is NOT imported): Lemma 9.1's binder
    -- list is jointly unsatisfiable whenever `2 + ηd < (1 - ϖ) * (2 + ζ)`, and `hζ` is exactly
    -- its negation, so it is what keeps `hL91` above from being vacuously true.  Corroborated
    -- caller-side by the source's own `ζ ≤ (4/5) ζ_*`.
    (hζ : ζ * (1 - ϖ) ≤ ηd + 2 * ϖ)
    (hloss : ML2Reduction.outerLoss R ≤ δ' ^ (-cst))
    (hmax : Kakeya.maxDensity fib (fun i ↦
        (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).toConvexSpaceBody)
      ≤ (δ' : ℝ≥0∞) ^ (-(ηd - cst)))
    (hfull : ShadedBody.fullness s' (fun i ↦ (U' i).toShadedBody) ≥ δ' ^ ηd)
    -- AA/AB: tightened to the constant the producer actually returns
    -- (`ShadedTube.ssfUniformConst 3`, `Kakeya/ShadedUniform.lean`), with the threshold the
    -- loose bracket used to quantify away carried explicitly.  Discharged at wiring time by
    -- `exists_outerShadedUniformTubeSet_ssf` + `exists_threshold_coe_const_le_rpow_neg`.
    -- this binder is ALSO where the line-ED levels row is sourced.  The witness carries
    -- a uniform hierarchy, and `Kakeya.VeryNotSticky.lineEDLevelsAt_C3_of_huni` turns it (with
    -- `hcb`'s `centred`/`contained`/`small` rows and the uniformiser's own grid threshold) into
    -- `LineEDLevelsAt C₃ lineEDLevelsConstant _` at the NAMED constant (
    -- ): the datum is DERIVED here, never an ambient field.
    (huni : ((ShadedTube.ssfUniformConst 3 : ℝ≥0) : ℝ≥0∞) ≤ (δ' : ℝ≥0∞) ^ (-ηd) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s' U' (Tube.ssfGridLen δ')
        (ShadedTube.ssfUniformConst 3)))
    -- the ONE open input, line-based
    (hwin4 : ((δ' ^ ϖ : ℝ≥0) : ℝ) ≤ 1 / 4)
    {A : ℕ} (hA0 : 0 < A)
    -- CONTRACTED-bottom window `[δ'^{1-ϖ}/C, δ'^{ϖ}]` — the hand-back reads the cover
    -- at `ρ/C`.  A producer must supply this clause on the wide
    -- window.  `hbudget` below did NOT move: `Kakeya.ML2Reduction.budget_descends` carries
    -- it from `ρ` down to `ρ/C`, at the cost of the reading gap `hgap`.
    (hEDline : ∀ ρ : ℝ≥0, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))),
        Kakeya.VeryNotSticky.IsLineEssDistinctAt (Tube.tubeOverlapCoreClose.C 3) A t W ∧
        (∀ l ∈ t, (W l).carrier ⊆ T₀.carrier) ∧
        (∀ l ∈ t, ∃ i ∈ s',
          (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).carrier
            ⊆ (W l).carrier) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ))
    (_hbudget : ∀ ρ : ℝ≥0, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (A : ℝ) * (ML2Reduction.lineEDPushConstant R : ℝ)
          * (ML2Reduction.spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    -- this is `hbudget` with `centringCountLossConstant R ·` at the head of the left-hand
    -- side, so it IMPLIES `hbudget`; `hbudget` is retained only because keeps its text
    -- tree-wide.  Discharged by `exists_threshold_hup_budget`'s argument at the
    -- new constant, never assumed; `ζ < ζ'` (`hgap`) is its side condition.  The `A` here is
    -- `hEDline`'s carried line-ED constant — the same `A` that `hbudget` above already prices,
    -- not a fresh variable: the twin's whole price is that constant (`A₁ = 2·641⁶` at the
    -- refined reading), and it is a threshold on the scale, not an exponent.  This is the one
    -- site whose left-hand side is `A · lineEDPushConstant R · spineOuterCountLoss R` rather
    -- than the `⌈…⌉₊` form, so it is the first threshold to check.
    (hcntbudget : ∀ ρ : ℝ≥0, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ)
        * (A : ℝ) * (ML2Reduction.lineEDPushConstant R : ℝ)
          * (ML2Reduction.spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    (hgap : ζ ≤ ζ')
    -- step 9, the cardinality multiplicativity and the loss ledger
    {Cf L Cu : ℝ≥0∞} {Nm : ℕ} {κ : ℝ}
    (hCf1 : (1 : ℝ≥0∞) ≤ Cf)
    (hsplit : ShadedBody.multiplicity fib (fun i ↦
        (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).toShadedBody)
      ≤ L * (ShadedBody.multiplicity t' (fun j ↦ (Zρ j).toShadedBody)
        * ShadedBody.multiplicity fib (fun i ↦
            (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).toShadedBody)))
    (hcard : (t'.card : ℝ≥0∞) * (fib.card : ℝ≥0∞) ≤ Cu * (Nm : ℝ≥0∞))
    (hLoss : L * Cf * Cu ^ β ≤ (δt : ℝ≥0∞) ^ (-κ))
    (hκ : κ ≤ ML2Spine.spineRung β ϖ ε₁ gain dens k / (20 * ML2Spine.spineDiv ϖ ε₁)) :
    ShadedBody.multiplicity fib (fun j ↦ (Y j).toShadedBody)
      ≤ (δ : ℝ≥0∞) ^ (w * (47 * ML2Spine.spineRung β ϖ ε₁ gain dens k
          / (5 * ML2Spine.spineDiv ϖ ε₁))) * (Nm : ℝ≥0∞) ^ β :=
  middle_factor_of_canonicalCover_sharp hβ0 hβ1 hϖ hε₁ hgain hdens hk hsitOut hRout hτθ Tθ Y
    hsubOut hw hsep hδ0 hδ1 hδ'0 hb1 hδtb hbw hprod hcoarse hballb hfullb hDb hs' hsit hR hR1
    hτσ T₀ hsubfib mm hqc0 h3qc hcb hL91 hζ hloss hmax hfull
    (Kakeya.VeryNotSticky.huni_loose_of_tight huni)
    (fun ρ hρ ↦ hct ρ hρ
      (by
        -- as above, through the LINE-based pointwise cover
        have hmem := Kakeya.VeryNotSticky.mem_widened_window_of_mem hρ
        have hc0 : 0 < ρ / Kakeya.VeryNotSticky.centringCoverRadiusConstant :=
          lt_of_lt_of_le (div_pos (NNReal.rpow_pos hδ'0)
            Kakeya.VeryNotSticky.edWindowContractionConstant_pos) hmem.1
        obtain ⟨κ₀, t, W, hline, hsubW, hused, hcard⟩ := hEDline _ hmem
        exact ML2Reduction.canonicalCoverAt_of_upstairs_lineED_const (ζ' := ζ')
          (Kc := (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ))
          (NNReal.coe_nonneg _) hsit hR T₀ _ hc0
          (le_trans (by exact_mod_cast hmem.2) hwin4) t W hsubW hused hA0 hline
          (ML2Reduction.budget_descends
            (h := by
              have h1 := ML2Reduction.le_of_mul_spineOuterCountLoss (R := R)
                (x := (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ) * (A : ℝ)
                  * (ML2Reduction.lineEDPushConstant R : ℝ)) (by positivity)
                (hcntbudget ρ hρ)
              have hEq : (A : ℝ) * (ML2Reduction.lineEDPushConstant R : ℝ)
                    * (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ)
                  = (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ) * (A : ℝ)
                    * (ML2Reduction.lineEDPushConstant R : ℝ) := by ring
              rw [hEq]; exact h1)
            (hρ'0 := by exact_mod_cast hc0)
            (hle := by exact_mod_cast Kakeya.VeryNotSticky.div_centringCoverRadiusConstant_le ρ)
            (he := by linarith)) hcard))
    hCf1 hsplit hcard hLoss hκ

end LineEDTwin

/-! ## The budget: what the twin costs, measured -/

section Budget

end Budget

/-! ## The wiring: `GeometricCoreAt` with the line-ED levels as a named producer obligation -/

section Wiring

end Wiring

end Kakeya.ML2Core

end

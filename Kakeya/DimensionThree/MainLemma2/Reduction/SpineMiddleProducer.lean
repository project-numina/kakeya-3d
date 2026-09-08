/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCoreWiring
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCanonicalCoverAt

/-!
# the estimate: the middle-factor producer, and the exponent it can reach

`Kakeya.ML2Core.geometricCoreAt_of_middleFactor` reduces GWZ Main Lemma 2's geometric core to a
single hypothesis, the **middle factor** at the two-scale split of a Katz--Tao dividing window,
asked at the gain `2 ε + 14 ε₁/25` for **every** Katz--Tao exponent `ε₁ > 0`.

This file measures that demand against what the existing chain delivers, and the measurement is
negative on both sides:

* **a ceiling on the demand itself** — any witness of the middle factor's own conclusion, at any
  input satisfying the wiring's binders, forces `gm ≤ 4 β`
  (`Kakeya.ML2Core.middle_gain_le_of_split`).  So the demand `2 ε + 14 ε₁/25` is met by nothing at
  all once `ε₁ > 25 (4 β - 2 ε)/14`;
* **a ceiling on the supply** — the transported exponent of the estimate
  (`Kakeya.ML2Reduction.spine_multiplicity_le_nonEccentric_of_canonicalCover`, read at the ambient
  scale through `Kakeya.ML2Core.middle_factor_of_rescaled`) is at most `e³ β/24`, while the demand
  is at least `14 e` (`Kakeya.ML2Core.spine_middle_gain_lt_demand`).

The positive content is the composition itself: `Kakeya.ML2Core.middle_factor_of_edNodes_window`
produces the middle factor at the ambient scale from the **ED-node clause** alone among the
open inputs, at the exponent the chain actually reaches.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody
open Tube ShadedTube

namespace Kakeya.ML2Core

universe u

/-! ## A multiplicity that is not zero is at least one -/

section OneLe

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*}

end OneLe

/-! ## The ceiling on the demand -/

section Ceiling

end Ceiling

/-! ## The ceiling on the supply -/

section Supply

end Supply

/-! ## The ED-node clause, into step-10 binder -/

section EdNodes

end EdNodes

/-! ## the component estimates (non-eccentric), composed, with the ED-node clause as the only open input -/

section Composition

open Classical in
/-- **The middle factor at the ambient scale, from the ED-node clause.**

This is the component estimates : `Kakeya.ML2Reduction.spine_multiplicity_le_nonEccentric_of_canonicalCover`
at the rescaled thickness `δ̃`, with its step-10 binder discharged by the **ED-node clause**
(`Kakeya.ML2Core.canonicalCover_of_edNodes`), transported to the ambient scale by
`Kakeya.ML2Core.middle_factor_of_rescaled`.

Read as an obligation list, every binder below is either an existing producer's output or a datum the
window hands over, **except** `hED`, which is GWZ Definition 2.1(ii) on the nodes at the scales the
count is read.  That is the one clause this composition carries.

**The exponent it reaches is `w · (10 η_k/ε₂)`,** where `w` is the window's own scale-separation
exponent (`Kakeya.ML2Reduction.IsKatzTaoDividingWindow.scale_sep`, which is `e` on the spine).
`Kakeya.ML2Core.spineRung_middle_gain_lt_demand` measures that against what
`Kakeya.ML2Core.geometricCoreAt_of_middleFactor` asks for, and they do not meet. -/
theorem middle_factor_of_edNodes
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
    -- stated on the CONTRACTED-bottom window `[δ'^{1-ϖ}/C, δ'^{ϖ}]`, because the
    -- centring hand-back reads the cover at `ρ/C`.  A producer of
    -- this clause must supply it on the wide window, not merely on Lemma 9.1's.
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
    (hκ : κ ≤ 20 * ML2Spine.spineRung β ϖ ε₁ gain dens k / ML2Spine.spineEps₂ ϖ ε₁) :
    ShadedBody.multiplicity fib (fun j ↦ (Y j).toShadedBody)
      ≤ (δ : ℝ≥0∞) ^ (w * (10 * ML2Spine.spineRung β ϖ ε₁ gain dens k
          / ML2Spine.spineEps₂ ϖ ε₁)) * (Nm : ℝ≥0∞) ^ β := by
  have hsp := ML2Spine.spineRung_isSpine (β := β) (ϖ := ϖ) (ε₁ := ε₁) (gain := gain)
    (dens := dens) hβ0 hβ1 hϖ hε₁ hgain hdens
  have hgm : 0 ≤ 10 * ML2Spine.spineRung β ϖ ε₁ gain dens k / ML2Spine.spineEps₂ ϖ ε₁ := by
    have h1 := hsp.rung_pos k
    have h2 := hsp.eps₂_pos
    positivity
  refine middle_factor_of_rescaled hsitOut hRout hτθ Tθ Y hsubOut hgm hw hsep ?_
  exact ML2Reduction.spine_multiplicity_le_nonEccentric_of_canonicalCover hβ0 hβ1 hϖ hε₁ hgain
    hdens hk hδ0 hδ1 hδ'0 hb1 hδtb hbw hprod hcoarse hballb hfullb hDb hs' hsit hR hR1 hτσ T₀ mm
    hsubfib hqc0 h3qc hcb hL91 hζ hloss hmax hfull
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

end Composition

/-! ## The singleton refutation: the existing `hmid` is FALSE, not merely capped -/

section Singleton

end Singleton

/-! ## The sharp rung exponent: `47 η_k/(5 e)` at `δ̃`, i.e. `9.4 η_k` at the ambient scale -/

section SharpBudget

/-- **The gain budget at the sharp exponent `47 X/(5 e)`.**

`Kakeya.ML2Reduction.gainBudget_of_step_le` reads the middle factor at `10 X/ε₂`, which — since
`ε₂ ≥ 5 e` — is at most `2 X/e`.  That reading is what
`Kakeya.ML2Core.spineRung_middle_gain_lt_demand` shows is hopeless against the wiring's demand,
and it is **not** the sharpest the construction supports: `Kakeya.ML2Spine.spineStep`'s second
entry gives `ν ≥ 34 X/(e β)`, and after the `(1-ε₂)` rescaling loss and the eccentricity charge
`2 · 12 X/(e β)` what is left is `(10 - 34 ε₂) X/(e β) - κ`, i.e. **essentially `10 X/e` and not
`2 X/e`**, because `β ≤ 1`.

This lemma takes `47 X/(5 e) = 9.4 X/e` of it and leaves `X/(20 e)` for the multiscale loss.  The
arithmetic that has to close is `9.45 β + 34 ε₂ ≤ 10`, and on the constructed spine
`β ≤ 1` and `ε₂ ≤ 1/64` give `9.45 + 0.53125 = 9.98125 ≤ 10`.

**Inert hypothesis found and not carried:** `0 ≤ ε₂` is *not* needed — a negative `ε₂` only makes
the right-hand side larger — so this lemma is stated without it.

**The margin is `0.019`, and the cap `ε₂ ≤ 1/64` is load-bearing**: the abstract
`Kakeya.ML2Spine.IsSpine` only caps `ε₂ < 1/12`, at which `9.45 β + 34/12 > 10` for
`β` near `1`.  So this lemma is stated for the *construction*, not for an abstract spine — the
same distinction `Kakeya.ML2Reduction.rescaleLoss_not_free_of_isSpine_fields` draws one exponent
down. -/
theorem gainBudget_of_step_sharp {β ε₂ e X ν κ : ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (he : 0 < e) (hε₂ : ε₂ ≤ 1 / 64)
    (hX : 0 < X) (hstep : X ≤ e * β * ν / 34) (hκ : κ ≤ X / (20 * e)) :
    47 * X / (5 * e) + 2 * (12 * X / (e * β)) + κ ≤ (1 - ε₂) * ν := by
  have heb : 0 < e * β := mul_pos he hβ
  have hB0 : 0 < X / (e * β) := div_pos hX heb
  have hBν : 34 * (X / (e * β)) ≤ ν := by
    rw [mul_div_assoc', div_le_iff₀ heb]
    nlinarith [hstep, heb]
  have hA : 47 * X / (5 * e) = 47 * β * (X / (e * β)) / 5 := by
    field_simp
  have hC : 2 * (12 * X / (e * β)) = 24 * (X / (e * β)) := by ring
  have hD : X / (20 * e) = β * (X / (e * β)) / 20 := by
    field_simp
  rw [hA, hC]
  rw [hD] at hκ
  nlinarith [hBν, hB0, hκ, hβ1, hε₂]

/-- **The sharp gain budget on the constructed spine.**

`Kakeya.ML2Spine.spineRung_eq_step`'s second minimum entry is
`e β · gain(η_{k+1}/2)/34`, which is exactly the `hstep` of
`Kakeya.ML2Core.gainBudget_of_step_sharp`; `Kakeya.ML2Spine.spineEps₂_le_inv64` supplies the cap
that lemma needs. -/
theorem spineRung_gainBudget_sharp {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    {k : ℕ} (hk : k < ML2Spine.spineCount ϖ ε₁) {κ : ℝ}
    (hκ : κ ≤ ML2Spine.spineRung β ϖ ε₁ gain dens k / (20 * ML2Spine.spineDiv ϖ ε₁)) :
    47 * ML2Spine.spineRung β ϖ ε₁ gain dens k / (5 * ML2Spine.spineDiv ϖ ε₁)
        + 2 * (12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
            / (ML2Spine.spineDiv ϖ ε₁ * β)) + κ
      ≤ (1 - ML2Spine.spineEps₂ ϖ ε₁)
          * gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) := by
  have hsp := ML2Spine.spineRung_isSpine hβ hβ1 hϖ hε₁ hgain hdens
  have hst := ML2Spine.spineRung_eq_step (β := β) (ϖ := ϖ) (ε₁ := ε₁)
    (gain := gain) (dens := dens) hk
  have hstep : ML2Spine.spineRung β ϖ ε₁ gain dens k
      ≤ ML2Spine.spineDiv ϖ ε₁ * β
          * gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) / 34 := by
    rw [hst]
    exact (min_le_left _ _).trans (min_le_right _ _)
  exact gainBudget_of_step_sharp hβ hβ1 hsp.div_pos
    ML2Spine.spineEps₂_le_inv64 (hsp.rung_pos k) hstep hκ

/-- **Step 11 at the sharp exponent.**

`Kakeya.ML2Reduction.spine_multiplicity_le_two_factors` with
`Kakeya.ML2Core.spineRung_gainBudget_sharp` in place of
`Kakeya.ML2Reduction.spineRung_gainBudget_of_rescaleLoss`: the conclusion's exponent is
`47 η_k/(5 e)` instead of `10 η_k/ε₂`, at the price of the tighter multiscale budget
`κ ≤ η_k/(20 e)` instead of `κ ≤ 20 η_k/ε₂`.

**Why the trade is the right one.** Both budgets are spent on subpolynomial constants and can be
met by thresholds on `δ`; the exponent cannot. Transported to the ambient scale by
`Kakeya.ML2Core.middle_factor_of_rescaled` at the window's own separation exponent `e`, this reads
`δ^{47 η_k/5} = δ^{9.4 η_k}`, against `δ^{2 η_k}` for the `ε₂`-reading. -/
theorem spine_multiplicity_le_two_factors_sharp
    {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ} {k : ℕ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hk : k < ML2Spine.spineCount ϖ ε₁)
    {δt b δ' : ℝ≥0} {mu mub muf L Cu : ℝ≥0∞} {Nb Nf N : ℕ} {κ : ℝ}
    (hδ0 : 0 < δt) (hδ1 : δt ≤ 1)
    (hbw : δt ^ ML2Spine.spineEps₂ ϖ ε₁ ≤ b) (hprod : δ' * b = δt)
    (hsplit : mu ≤ L * (mub * muf))
    (hb : mub ≤ (δt : ℝ≥0∞) ^
          (-(2 * (12 * ML2Spine.spineRung β ϖ ε₁ gain dens k / (ML2Spine.spineDiv ϖ ε₁ * β))))
        * (Nb : ℝ≥0∞) ^ β)
    (hf : muf ≤ (δ' : ℝ≥0∞) ^ (gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2))
        * (Nf : ℝ≥0∞) ^ β)
    (hcard : (Nb : ℝ≥0∞) * (Nf : ℝ≥0∞) ≤ Cu * (N : ℝ≥0∞))
    (hL : L * Cu ^ β ≤ (δt : ℝ≥0∞) ^ (-κ))
    (hκ : κ ≤ ML2Spine.spineRung β ϖ ε₁ gain dens k / (20 * ML2Spine.spineDiv ϖ ε₁)) :
    mu ≤ (δt : ℝ≥0∞) ^
          (47 * ML2Spine.spineRung β ϖ ε₁ gain dens k / (5 * ML2Spine.spineDiv ϖ ε₁))
        * (N : ℝ≥0∞) ^ β := by
  have hsp := ML2Spine.spineRung_isSpine (β := β) (ϖ := ϖ) (ε₁ := ε₁) (gain := gain)
    (dens := dens) hβ0 hβ1 hϖ hε₁ hgain hdens
  have hpos : (0 : ℝ) < ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2 := by
    have := hsp.rung_pos (k + 1)
    linarith
  have hν : 0 ≤ gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) := (hgain _ hpos).le
  have hbud := spineRung_gainBudget_sharp hβ0 hβ1 hϖ hε₁ hgain hdens hk hκ
  refine ML2Reduction.multiplicity_le_of_two_factors_rescaled (by simpa using hδ0.ne')
    (by exact_mod_cast hδ1) hβ0.le hν (hsp.eps₂_le_half.trans (by norm_num))
    (ML2Reduction.rescaledScale_le hδ0 hbw hprod) hsplit hb hf hcard hL ?_
  linarith

end SharpBudget

/-! ## The sharp composition -/

section SharpComposition

open Classical in
/-- **The middle factor at the ambient scale, from the ED-node clause, at the SHARP exponent.**

Identical to `Kakeya.ML2Core.middle_factor_of_edNodes` except that step 11 is run through
`Kakeya.ML2Core.spine_multiplicity_le_two_factors_sharp`, so the rescaled exponent is
`47 η_k/(5 e)` rather than `10 η_k/ε₂` and the multiscale budget tightens from `20 η_k/ε₂` to
`η_k/(20 e)`.  Transported at the window's own separation exponent `w = e`
(`ML2Reduction.IsKatzTaoDividingWindow.scale_sep`) the ambient gain is

```
e · 47 η_k/(5 e)  =  47 η_k/5  =  9.4 η_k  ≥  9.4 ν
```

against `2 η_k` for the `ε₂`-reading — the factor of `4.7` that
`Kakeya.ML2Core.rung_budget_closes_of_overhead_le_four` needs and
`Kakeya.ML2Core.spineRung_middle_gain_lt_demand` shows the `ε₂`-reading does not have.

The body is `Kakeya.ML2Reduction.spine_multiplicity_le_nonEccentric_of_canonicalCover`'s, inlined
because that theorem hard-codes its own exponent; every step of it is unchanged except the last. -/
theorem middle_factor_of_edNodes_sharp
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
    (_hmax : Kakeya.maxDensity fib (fun i ↦
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
    -- stated on the CONTRACTED-bottom window `[δ'^{1-ϖ}/C, δ'^{ϖ}]`, because the
    -- centring hand-back reads the cover at `ρ/C`.  A producer of
    -- this clause must supply it on the wide window, not merely on Lemma 9.1's.
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
  -- Step 10 on the REPRESENTED family (the UNPRIMED eliminator): the hand-back's `3 qc`
  -- transport is inside it, so the `3 qc` is charged exactly once, on `hL91`'s gain (V-3).
  -- `Cf` keeps its text in `hLoss` and needs only `1 ≤ Cf`.
  have h10 := ML2Reduction.fine_factor_of_lemma91At_of_canonicalCover
    (ν := gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2))
    hL91 hζ hsit hR hR1 hτσ hδ'0 hϖ.le hβ0.le hqc0 le_rfl h3qc T₀ mm hs'
    (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U' hcb hsubfib hloss
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

end SharpComposition

/-! ## The rung-level ledger: what the window branch must pay, and whether the sharp gain pays it -/

section Ledger

end Ledger

/-! ## The model: the existing `hmid` is false, not vacuous -/

section Model

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end Model

end Kakeya.ML2Core

end

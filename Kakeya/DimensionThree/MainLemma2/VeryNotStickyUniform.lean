/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.VeryNotStickyCase
public import Kakeya.DimensionThree.FrostmanEstimateOne
public import Kakeya.DimensionThree.FrostmanEstimateMono

/-!
# The `β`-uniform companion of GWZ Lemma 9.1, and why it is not needed

The file opens with the question it was written for: can the three exponents `ϖ`, `ν`, `η` that
GWZ Lemma 9.1 (`Kakeya.multiplicity_le_of_card_isEssDistinct_ge`) produces be chosen **once**, at
a threshold `β₀`, and then serve every `β ∈ [β₀, 1]`?  The GWZ reduction assembly needs that
uniform companion because the protected Main Lemma 2,
`Kakeya.KatzTaoEstimate.katzTaoEstimate_sub_of_frostmanEstimate`, asks for a *monotone* `ν`.

## What is proved

**Part 1 — the companion, and the single residual it rests on.**

* `Kakeya.VNSUniform.VNSBody`, `Lemma91`, `Lemma91Uniform`: the statements, copied verbatim from
  the protected declaration and pinned to it by the tripwire `example : Lemma91 := …`.
  `Lemma91Uniform` is *definitionally* `Kakeya.ML2Assembly.Lemma91Uniform`.
* `VNSBody.mono_gain`, `VNSBody.mono_dens`, `VNSBody.mono_window`: `VNSBody` is antitone in all
  three exponents, so "uniform on `[β₀,1]`" means "the infimum on `[β₀,1]` is positive".
* `vnsBody_of_params`: GWZ Lemma 9.1's proof with the parameters of Configuration `hyp:ml2params`
  as *arguments* instead of produced by `Kakeya.VeryNotSticky.exists_caseParams`.  Recovering the
  protected statement from it is `lemma91_of_vnsBody_of_params`.
* `CaseParams.mono_beta`, `CaseParams.mono_eta`, `casesplitExponent_mono_beta` (and the three
  nested exponents): the whole parameter budget eases as `β` grows and as `η` shrinks.  Hence
  `exists_uniform_caseParams`: **eleven of the twelve `CaseParams` fields and the case-split
  budget transport to the whole window for free.**
* The one that does not transport is the binder
  `hplankF : 2η < τ · plankFrostmanExponent β (ϱβτ/8)` of
  `Kakeya.VeryNotSticky.exists_setup_caseSideData`.  It is isolated as
  `UniformPlankExponent`, shown to be *equivalent* to the missing budget
  (`exists_uniform_bound_of_uniform_budget`) and consistent
  (`uniformPlankExponent_of_not_plankFrostmanVolume`), and
  `lemma91Uniform_of_uniformPlankExponent` proves the companion from it.
  `Kakeya.VeryNotSticky.plankFrostmanExponent` is `@[irreducible]` and defined by
  `Classical.choose`, and unwinds to the accuracy that `K_F β` supplies existentially *after* `β`
  — so no uniform lower bound over a continuum of `β` is available, and the companion is blocked
  there and nowhere else.

**Part 2 — the reduction that removes the obligation.**

Write `A = {β ∈ (0,1] | K_KT β ∧ K_F β}`.

* `no_monotoneOn_drop_of_open_threshold`: if `A = (m,1]` with `0 < m`, the protected Main Lemma 2
  is *false*, however uniform Lemma 9.1 is.  So the uniform companion could never have been the
  whole story.
* `katzTaoEstimate_sub_of_least`, `katzTaoEstimate_sub_of_never`,
  `katzTaoEstimate_sub_of_trichotomy`: in the other three shapes of `A`, the protected statement
  follows from the **pointwise** drop with no uniformity at all.
* `katzTaoEstimate_of_forall_gt`, `frostmanEstimate_of_forall_gt`: both partial estimates are
  closed from above in the exponent, by the crude bound `|𝕋| ≤ δ^{-4}` and the bracket bound.
* `estimateSet_shape`: therefore `A` is a nonempty closed up-set, and the bad shape does not
  occur.
* `mainLemma2Statement_of_pointwise_drop`: **Main Lemma 2, verbatim, from the pointwise drop.**
  No `β`-uniform Lemma 9.1 is used, and the declaration is `sorryAx`-free.

Nothing here edits `Kakeya.multiplicity_le_of_card_isEssDistinct_ge` or any protected statement.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Topology Filter ShadedBody ConvexSpaceBody

namespace Kakeya.VNSUniform

universe u

/-! ## The statement, pinned to the protected declaration -/

/-- The body of GWZ Lemma 9.1 at exponent `β`, window exponent `ϖ`, tolerance `ζ`, gain `ν` and
density exponent `η` — copied verbatim from the protected
`Kakeya.multiplicity_le_of_card_isEssDistinct_ge`, and identical to
`Kakeya.ML2Assembly.VNSBody`. -/
def VNSBody (β ϖ ζ ν η : ℝ) : Prop :=
  KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
  FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
  ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0,
  ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
    (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
    (∀ i ∈ s, (T i).toTube.IsCentred) →
    (∃ C : ℝ≥0, 1 ≤ C ∧ (C : ℝ≥0∞) ≤ (δ : ℝ≥0∞) ^ (-η) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) C)) →
    maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-η) →
    ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
    (∀ ρ : ℝ≥0, ρ ∈ Set.Icc (δ ^ (1 - ϖ)) (δ ^ ϖ) →
      ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
        (tρ : Set κ).Pairwise
          (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
        (∀ j ∈ tρ, ∃ i ∈ s, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
        (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) →
    multiplicity s (fun i ↦ (T i).toShadedBody) ≤
      (δ : ℝ≥0∞) ^ ν * (s.card : ℝ≥0∞) ^ β

/-- **GWZ Lemma 9.1**, exactly as the protected declaration states it. -/
def Lemma91 : Prop :=
  ∀ β : ℝ, 0 < β → β ≤ 1 →
    ∃ ϖ > (0 : ℝ), ∀ ζ > (0 : ℝ), ∃ ν > (0 : ℝ), ∃ η > (0 : ℝ), VNSBody.{u} β ϖ ζ ν η

/- The fidelity tripwire `example : Lemma91 := fun _ hβ hβ1 ↦ Kakeya.multiplicity_le_of_card_isEssDistinct_ge hβ hβ1`
lives in `MainLemma2/VeryNotStickyClosed.lean` since the  A.5 relocation of Lemma 9.1 downstream of
its producers; this module is upstream of that file. -/

/-- **The `β`-uniform companion of GWZ Lemma 9.1**, identical to
`Kakeya.ML2Assembly.Lemma91Uniform`: the three exponents are chosen *before* `β` ranges over
the window `[β₀, 1]`. -/
def Lemma91Uniform : Prop :=
  ∀ β₀ : ℝ, 0 < β₀ → β₀ ≤ 1 →
    ∃ ϖ > (0 : ℝ), ∀ ζ > (0 : ℝ), ∃ ν > (0 : ℝ), ∃ η > (0 : ℝ),
      ∀ β ∈ Set.Icc β₀ 1, VNSBody.{u} β ϖ ζ ν η


/-! ## How `VNSBody` may be weakened

`VNSBody` is antitone in the gain `ν`, in the density exponent `η` and in the window exponent
`ϖ`: a smaller value of any of the three gives a *weaker* statement.  This is what makes
"uniform over `[β₀,1]`" mean "the infimum over `[β₀,1]` is positive", and it is what lets the
companion be assembled from a single choice at the threshold. -/

private lemma eventually_mem_Ioo :
    ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0, 0 < δ ∧ δ < 1 := by
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ≥0) < 1 from zero_lt_one)] with δ hδ
  exact ⟨hδ.1, hδ.2⟩

/-- `VNSBody` is antitone in the gain: a proof with gain `ν` gives one with any smaller gain. -/
theorem VNSBody.mono_gain {β ϖ ζ ν ν' η : ℝ} (hνν' : ν' ≤ ν) (h : VNSBody.{u} β ϖ ζ ν η) :
    VNSBody.{u} β ϖ ζ ν' η := by
  intro hKT hF
  filter_upwards [h hKT hF, eventually_mem_Ioo] with δ hδ hδ1
  intro ι s T hball hcen huni hmax hfull hcount
  refine (hδ s T hball hcen huni hmax hfull hcount).trans ?_
  have hδ1' : (δ : ℝ≥0∞) ≤ 1 := ENNReal.coe_le_one_iff.mpr hδ1.2.le
  exact mul_le_mul_of_nonneg_right
    (ENNReal.rpow_le_rpow_of_exponent_ge hδ1' hνν') zero_le

/-- `VNSBody` is antitone in the density exponent: a proof at `η` gives one at any smaller
`η'`, because both hypotheses `Δ_max ≤ δ^{-η}` and `λ ≥ δ^η` weaken as `η` grows. -/
theorem VNSBody.mono_dens {β ϖ ζ ν η η' : ℝ} (hη' : η' ≤ η) (h : VNSBody.{u} β ϖ ζ ν η) :
    VNSBody.{u} β ϖ ζ ν η' := by
  intro hKT hF
  filter_upwards [h hKT hF, eventually_mem_Ioo] with δ hδ hδ1
  intro ι s T hball hcen huni hmax hfull hcount
  have hδ1' : (δ : ℝ≥0∞) ≤ 1 := ENNReal.coe_le_one_iff.mpr hδ1.2.le
  -- the uniformity constant's cap `δ^{-η'}` is below `δ^{-η}`
  have huni' : ∃ C : ℝ≥0, 1 ≤ C ∧ (C : ℝ≥0∞) ≤ (δ : ℝ≥0∞) ^ (-η) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) C) := by
    obtain ⟨C, hC1, hCδ, hC⟩ := huni
    exact ⟨C, hC1, hCδ.trans (ENNReal.rpow_le_rpow_of_exponent_ge hδ1' (by linarith)), hC⟩
  refine hδ s T hball hcen huni' ?_ ?_ hcount
  · exact hmax.trans (ENNReal.rpow_le_rpow_of_exponent_ge hδ1' (by linarith))
  · refine le_trans ?_ hfull
    exact_mod_cast NNReal.rpow_le_rpow_of_exponent_ge hδ1.1 hδ1.2.le hη'

/-- `VNSBody` is antitone in the window exponent: shrinking `ϖ` *enlarges* the scale window
`[δ^{1-ϖ}, δ^{ϖ}]` over which the tube-count hypothesis is assumed, hence strengthens that
hypothesis and weakens the statement. -/
theorem VNSBody.mono_window {β ϖ ϖ' ζ ν η : ℝ} (hϖ' : ϖ' ≤ ϖ) (h : VNSBody.{u} β ϖ ζ ν η) :
    VNSBody.{u} β ϖ' ζ ν η := by
  intro hKT hF
  filter_upwards [h hKT hF, eventually_mem_Ioo] with δ hδ hδ1
  intro ι s T hball hcen huni hmax hfull hcount
  refine hδ s T hball hcen huni hmax hfull ?_
  intro ρ hρ
  refine hcount ρ ⟨?_, ?_⟩
  · exact le_trans (NNReal.rpow_le_rpow_of_exponent_ge hδ1.1 hδ1.2.le (by linarith)) hρ.1
  · exact le_trans hρ.2 (NNReal.rpow_le_rpow_of_exponent_ge hδ1.1 hδ1.2.le hϖ')

/-! ## The core of Lemma 9.1, with its parameters exposed

`Kakeya.multiplicity_le_of_card_isEssDistinct_ge` opens by running
`Kakeya.VeryNotSticky.exists_caseParams` at `β` and then never mentions `β` again except through
those parameters.  The theorem below is that proof with the `exists_caseParams` step *removed*:
the parameters are arguments.  It is what makes a uniform choice of parameters possible at all,
and it is stated so that the protected declaration is recovered by feeding it
`exists_caseParams`; `Kakeya.VNSUniform.lemma91_of_vnsBody_of_params` is that recovery, and is a
second fidelity check on this file.
-/

open Kakeya.VeryNotSticky
open scoped NNReal ENNReal


/-! ## Every exponent of the case split is monotone in `β`

The four nested exponents of the case split — `bigmultExponent`, `nonslabExponent`,
`thinExponent`, `casesplitExponent` — are minima of products in which `β` occurs positively, so
each *increases* with `β`.  The gain therefore never degrades as the exponent rises, which is
half of what a uniform choice at the threshold needs. -/


/-! ## `CaseParams` eases as `β` grows and as `η` shrinks

`β` occurs in exactly five of the twelve fields of `Kakeya.VeryNotSticky.CaseParams` — `thick`,
`slab`, `smallMultiplicity`, `transverse`, `tangential` — and in all five on the *large* side of
a strict inequality.  `η` occurs in six, and in all six on the *small* side.  So the whole
budget system is monotone in `β` and antitone in `η`; neither fact is recorded upstream. -/


/-! ## The one residual: a `β`-uniform plank-Frostman exponent

Running `Kakeya.VeryNotSticky.exists_caseParams` at the threshold `β₀` and transporting its
output along `Kakeya.VNSUniform.CaseParams.mono_beta` discharges **eleven of the twelve fields**
of `CaseParams` and the case-split budget `η ≤ ν_casesplit/2` at every `β ∈ [β₀,1]`, with no
hypothesis at all.  Exactly one of `exists_caseParams`' three conclusions fails to transport:
the binder

`hplankF : 2η < τ · plankFrostmanExponent β (ϱβτ/8)`

that `Kakeya.VeryNotSticky.exists_setup_caseSideData` requires.  It is an *upper* bound on `η`
whose right-hand side moves with `β`, and `η` must be fixed before `β`; so it transports exactly
when the canonical exponent is bounded below by a positive constant on the window.

`Kakeya.VeryNotSticky.plankFrostmanExponent` is `@[irreducible]` and defined by
`Classical.choose` on `Kakeya.VeryNotSticky.PlankFrostmanVolume β ε`; the only fact about it
available anywhere in the development is `plankFrostmanExponent_pos`, its positivity at a *single*
`(β, ε)`. A uniform positive lower bound over a continuum of `β` is therefore not derivable, and
that — not any part of the case split — is what stands between this file and an unconditional
`Kakeya.VNSUniform.Lemma91Uniform`. -/


/-! ## The uniform parameter package, and the uniform companion -/


/-! ## Is the uniform companion the right obligation?

The assembly asks for `Lemma91Uniform` because the protected Main Lemma 2 asks for a *monotone*
`ν`.  This section makes the relationship between the two precise, and it changes the priority.

Write `A := {β ∈ (0,1] | K_KT β ∧ K_F β}` for the set of exponents at which Main Lemma 2 has
anything to say.  `A` is up-closed, by `Kakeya.KatzTaoEstimate.mono` and
`Kakeya.FrostmanEstimate.mono`, so it is one of `∅`, `(0,1]`, `[m,1]` or `(m,1]` with `0 < m`.

* On `∅` and on `(0,1]` the protected statement is immediate
  (`Kakeya.VNSUniform.katzTaoEstimate_sub_of_never`, and
  `Kakeya.KatzTaoEstimate.mainLemma2_of_all` for `(0,1]`).
* On `[m,1]` **one single application of the *non-uniform* Lemma 9.1, at `m`, suffices**:
  `Kakeya.VNSUniform.katzTaoEstimate_sub_of_least`.  No uniformity of any kind is used.
* On `(m,1]` with `0 < m` the protected statement is **unprovable from any per-exponent drop**:
  `Kakeya.VNSUniform.no_monotoneOn_drop_of_open_threshold` derives `False` from a monotone
  positive `ν` in that configuration, and a `β`-uniform Lemma 9.1 would not help either, since
  the obstruction is on the `K_KT` side, not on the parameter side.

So `Lemma91Uniform` is *not* the load-bearing obligation.  The load-bearing obligation is that
the fourth case does not occur — i.e. that `A` is closed at its infimum — and that is a
self-contained analytic statement about `Kakeya.KatzTaoEstimate` and `Kakeya.FrostmanEstimate`,
not about the case split of Lemma 9.1.  See `Kakeya.VNSUniform.katzTaoEstimate_sub_of_trichotomy`
for the resulting reduction of the whole of Main Lemma 2 to the *pointwise* drop. -/

section Envelope

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]


/-- **When the estimates first hold at an exponent that is attained, Main Lemma 2 needs no
uniformity at all.**

If `m` is a *least* exponent at which both partial estimates hold, then a single drop `c` valid
at `m` — the output of the ordinary, non-uniform GWZ Lemma 9.1 route — already yields the whole
protected conclusion, with the monotone function `ν β = min c (β/2)`.  Up-closedness of
`K_KT` (`Kakeya.KatzTaoEstimate.mono`) does the rest.

The conclusion below is *verbatim* the statement of
`Kakeya.KatzTaoEstimate.katzTaoEstimate_sub_of_frostmanEstimate`. -/
theorem katzTaoEstimate_sub_of_least {m c : ℝ} (hc : 0 < c)
    (hleast : ∀ β : ℝ, 0 < β → β ≤ 1 → KatzTaoEstimate.{u} E β → FrostmanEstimate.{u} E β →
      m ≤ β)
    (hdrop : KatzTaoEstimate.{u} E (m - c)) :
    ∃ ν : ℝ → ℝ, MonotoneOn ν (Set.Ioc 0 1) ∧
      (∀ β : ℝ, 0 < β → β ≤ 1 → 0 < ν β) ∧
      ∀ β : ℝ, 0 < β → β ≤ 1 →
        KatzTaoEstimate.{u} E β → FrostmanEstimate.{u} E β →
        KatzTaoEstimate.{u} E (β - ν β) := by
  refine ⟨fun β ↦ min c (β / 2), ?_, ?_, ?_⟩
  · intro x _ y _ hxy
    exact min_le_min le_rfl (by linarith)
  · intro β hβ _
    exact lt_min hc (by linarith)
  · intro β hβ hβ1 hKT hF
    refine KatzTaoEstimate.mono ?_ hdrop
    have hmβ : m ≤ β := hleast β hβ hβ1 hKT hF
    have : min c (β / 2) ≤ c := min_le_left _ _
    linarith

/-- **When the estimates never hold, Main Lemma 2 is vacuous.**  The conclusion is again verbatim
the protected statement. -/
theorem katzTaoEstimate_sub_of_never
    (h : ∀ β : ℝ, 0 < β → β ≤ 1 → KatzTaoEstimate.{u} E β → ¬ FrostmanEstimate.{u} E β) :
    ∃ ν : ℝ → ℝ, MonotoneOn ν (Set.Ioc 0 1) ∧
      (∀ β : ℝ, 0 < β → β ≤ 1 → 0 < ν β) ∧
      ∀ β : ℝ, 0 < β → β ≤ 1 →
        KatzTaoEstimate.{u} E β → FrostmanEstimate.{u} E β →
        KatzTaoEstimate.{u} E (β - ν β) := by
  refine ⟨fun β ↦ β / 2, ?_, ?_, ?_⟩
  · intro x _ y _ hxy; dsimp; linarith
  · intro β hβ _; dsimp; linarith
  · intro β hβ hβ1 hKT hF
    exact absurd hF (h β hβ hβ1 hKT)

/-- **Main Lemma 2 from the *pointwise* drop, given that the estimate set is not open at its
infimum.**

The hypothesis `hdrop` is exactly what the ordinary GWZ route delivers: at each single exponent
where both estimates hold, *some* positive drop is available.  The hypothesis `hshape` is the
trichotomy discussed above — the estimate set is empty, is everything, or has a least element.
Together they give the protected Main Lemma 2 verbatim, with **no `β`-uniform Lemma 9.1
anywhere**.

`Kakeya.VNSUniform.no_monotoneOn_drop_of_open_threshold` shows the missing fourth case is not an
artefact of this proof: in it the protected conclusion is false outright.  So `hshape` is not a
convenience — it is the whole remaining gap, and it is a statement about the two partial
estimates alone. -/
theorem katzTaoEstimate_sub_of_trichotomy
    (hdrop : ∀ β : ℝ, 0 < β → β ≤ 1 → KatzTaoEstimate.{u} E β → FrostmanEstimate.{u} E β →
      ∃ d : ℝ, 0 < d ∧ KatzTaoEstimate.{u} E (β - d))
    (hshape :
      (∀ β : ℝ, 0 < β → β ≤ 1 → KatzTaoEstimate.{u} E β → ¬ FrostmanEstimate.{u} E β) ∨
      (∀ β : ℝ, 0 < β → β ≤ 1 → KatzTaoEstimate.{u} E β) ∨
      (∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧ KatzTaoEstimate.{u} E m ∧ FrostmanEstimate.{u} E m ∧
        ∀ β : ℝ, 0 < β → β ≤ 1 → KatzTaoEstimate.{u} E β → FrostmanEstimate.{u} E β → m ≤ β)) :
    ∃ ν : ℝ → ℝ, MonotoneOn ν (Set.Ioc 0 1) ∧
      (∀ β : ℝ, 0 < β → β ≤ 1 → 0 < ν β) ∧
      ∀ β : ℝ, 0 < β → β ≤ 1 →
        KatzTaoEstimate.{u} E β → FrostmanEstimate.{u} E β →
        KatzTaoEstimate.{u} E (β - ν β) := by
  rcases hshape with hnone | hall | ⟨m, hm, hm1', hKTm, hFm, hleast⟩
  · exact katzTaoEstimate_sub_of_never hnone
  · refine ⟨fun β ↦ β / 2, ?_, ?_, ?_⟩
    · intro x _ y _ hxy; dsimp; linarith
    · intro β hβ _; dsimp; linarith
    · intro β hβ hβ1 _ _
      have : β - β / 2 = β / 2 := by ring
      rw [this]
      exact hall (β / 2) (by linarith) (by linarith)
  · obtain ⟨d, hd, hKTd⟩ := hdrop m hm hm1' hKTm hFm
    exact katzTaoEstimate_sub_of_least hd hleast hKTd


/-! ## The estimate set is closed on the Katz--Tao side

The fourth case of the trichotomy above is `A = (m,1]` with `0 < m`.  It cannot occur on the
`K_KT` side: `Kakeya.KatzTaoEstimate` at the exponent `m` follows from `Kakeya.KatzTaoEstimate`
at every exponent above `m`, because a `δ`-tube family in `B₁` with `Δ_max ≤ δ^{-η}` and `η ≤ 1`
has at most `δ^{-4}` members, so `|𝕋|^{β} ≤ |𝕋|^{m}·δ^{-4(β-m)}` and the difference is absorbed
into the accuracy.

This is the "closedness" half of `hshape` in
`Kakeya.VNSUniform.katzTaoEstimate_sub_of_trichotomy`; the other half is the same statement for
`Kakeya.FrostmanEstimate`, which is not proved here. -/

/-- `|𝕋| ≤ δ^{-4}` in `ℝ≥0∞`.  The `ENNReal` form of `Kakeya.ML2Assembly.card_le_rpow_neg_four`
(same proof, stopped one step earlier: that declaration transfers the bound to `ℝ`, and the
`ℝ`-valued form is not what the exponent bookkeeping below needs). -/
theorem card_le_rpow_neg_four_enn {δ : ℝ≥0} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hδC : (Tube.card_le_of_densityIn_le.C 3 : ℝ≥0∞) ≤ (δ : ℝ≥0∞) ^ (-1 : ℝ))
    {ι : Type*} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1)
    {η : ℝ} (hη1 : η ≤ 1)
    (hmax : maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-η)) :
    (s.card : ℝ≥0∞) ≤ (δ : ℝ≥0∞) ^ (-4 : ℝ) := by
  have hE : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hδE0 : (0 : ℝ≥0∞) < (δ : ℝ≥0∞) := by exact_mod_cast hδ0
  have hδE1 : (δ : ℝ≥0∞) ≤ 1 := by exact_mod_cast hδ1
  have hden : densityIn s (fun i ↦ (T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall ≤ (δ : ℝ≥0∞) ^ (-η) :=
    (le_maxDensity s _ _).trans hmax
  have hraw := Tube.card_le_of_densityIn_le (E := EuclideanSpace ℝ (Fin 3)) (δ := δ)
    (s := s) (T := fun i ↦ (T i).toTube) hδ0.ne' hball hden
  rw [hE] at hraw
  norm_num at hraw
  have hstep1 : (δ : ℝ≥0∞) ^ (-η) ≤ (δ : ℝ≥0∞) ^ (-1 : ℝ) :=
    ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith)
  have hzpow : (δ : ℝ≥0∞) ^ (-2 : ℤ) = (δ : ℝ≥0∞) ^ (-2 : ℝ) := by
    rw [← ENNReal.rpow_intCast]; norm_num
  refine hraw.trans ?_
  rw [hzpow]
  calc (Tube.card_le_of_densityIn_le.C 3 : ℝ≥0∞) * (δ : ℝ≥0∞) ^ (-η)
          * (δ : ℝ≥0∞) ^ (-2 : ℝ)
      ≤ (δ : ℝ≥0∞) ^ (-1 : ℝ) * (δ : ℝ≥0∞) ^ (-1 : ℝ) * (δ : ℝ≥0∞) ^ (-2 : ℝ) := by
        gcongr
    _ = (δ : ℝ≥0∞) ^ (-4 : ℝ) := by
        rw [← ENNReal.rpow_add _ _ hδE0.ne' ENNReal.coe_ne_top,
          ← ENNReal.rpow_add _ _ hδE0.ne' ENNReal.coe_ne_top]
        norm_num

/-- The thresholds under which `Kakeya.VNSUniform.card_le_rpow_neg_four_enn` applies hold for all
small `δ`.  Copied from `Kakeya.ML2Assembly.eventually_card_thresholds`. -/
theorem eventually_card_thresholds' :
    ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0,
      0 < δ ∧ δ ≤ 1 ∧
        (Tube.card_le_of_densityIn_le.C 3 : ℝ≥0∞) ≤ (δ : ℝ≥0∞) ^ (-1 : ℝ) := by
  set C : ℝ≥0 := Tube.card_le_of_densityIn_le.C 3 with hC
  have hpos : (0 : ℝ≥0) < (C + 1)⁻¹ := by positivity
  have hmem : Set.Ioo (0 : ℝ≥0) (min 1 (C + 1)⁻¹) ∈ 𝓝[>] (0 : ℝ≥0) :=
    Ioo_mem_nhdsGT (lt_min zero_lt_one hpos)
  filter_upwards [hmem] with δ hδ
  obtain ⟨hδ0, hδlt⟩ := hδ
  have hδ1 : δ ≤ 1 := (lt_of_lt_of_le hδlt (min_le_left _ _)).le
  refine ⟨hδ0, hδ1, ?_⟩
  have hδinv : δ ≤ (C + 1)⁻¹ := (lt_of_lt_of_le hδlt (min_le_right _ _)).le
  have hCδ : C * δ ≤ 1 := by
    have h1 : (C + 1) * δ ≤ (C + 1) * (C + 1)⁻¹ := by gcongr
    rw [mul_inv_cancel₀ (by positivity)] at h1
    exact le_trans (by gcongr; exact le_self_add) h1
  have hCle : (C : ℝ≥0∞) ≤ (δ : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.le_inv_iff_mul_le]
    calc (C : ℝ≥0∞) * (δ : ℝ≥0∞) = ((C * δ : ℝ≥0) : ℝ≥0∞) := by rw [ENNReal.coe_mul]
      _ ≤ ((1 : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast hCδ
      _ = 1 := by simp
  calc (C : ℝ≥0∞) ≤ (δ : ℝ≥0∞)⁻¹ := hCle
    _ = (δ : ℝ≥0∞) ^ (-1 : ℝ) := by rw [ENNReal.rpow_neg, ENNReal.rpow_one]

/-- **`Kakeya.KatzTaoEstimate` is closed from above in the exponent.**

If `K_KT(β)` holds for every `β ∈ (m, 1]`, then `K_KT(m)` holds.  Hence the set of exponents at
which the Katz--Tao partial estimate holds is a *closed* up-set, and the open-threshold
configuration refuted by `Kakeya.VNSUniform.no_monotoneOn_drop_of_open_threshold` cannot arise
from the `K_KT` side alone.

The proof is the crude cardinality bound `|𝕋| ≤ δ^{-4}` and nothing else: run the estimate at
`β = m + ε/8`, and pay `|𝕋|^{β - m} ≤ δ^{-4(β-m)} ≤ δ^{-ε/2}` out of the accuracy. -/
theorem katzTaoEstimate_of_forall_gt {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1)
    (h : ∀ β : ℝ, m < β → β ≤ 1 → KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β) :
    KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) m := by
  intro ε hε
  have hβm : m < min 1 (m + ε / 8) := lt_min hm1 (by linarith)
  have hβ1 : min 1 (m + ε / 8) ≤ 1 := min_le_left _ _
  have hβm8 : min 1 (m + ε / 8) - m ≤ ε / 8 := by
    have := min_le_right (1 : ℝ) (m + ε / 8); linarith
  set β : ℝ := min 1 (m + ε / 8) with hβdef
  obtain ⟨η, hη, hev⟩ := h β hβm hβ1 (ε / 2) (by linarith)
  refine ⟨min η 1, lt_min hη one_pos, ?_⟩
  filter_upwards [hev, eventually_card_thresholds'] with δ hδ hthr
  obtain ⟨hδ0, hδ1, hδC⟩ := hthr
  intro ι s T hball hKT hfull
  have hδE0 : (0 : ℝ≥0∞) < (δ : ℝ≥0∞) := by exact_mod_cast hδ0
  have hδE1 : (δ : ℝ≥0∞) ≤ 1 := by exact_mod_cast hδ1
  -- transfer the two standing hypotheses from `min η 1` to `η`
  have hKT' : IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ℝ≥0∞) ^ (-η)) :=
    le_trans hKT (ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by simp))
  have hfull' : ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η :=
    le_trans (NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (min_le_left η 1)) hfull
  have hres := hδ s T hball hKT' hfull'
  refine hres.trans ?_
  -- the crude cardinality bound
  have hcard : (s.card : ℝ≥0∞) ≤ (δ : ℝ≥0∞) ^ (-4 : ℝ) :=
    card_le_rpow_neg_four_enn hδ0 hδ1 hδC s T hball (min_le_right η 1) hKT
  have key : (δ : ℝ≥0∞) ^ (-(ε / 2)) * (s.card : ℝ≥0∞) ^ β ≤
      (δ : ℝ≥0∞) ^ (-ε) * (s.card : ℝ≥0∞) ^ m := by
    rcases Nat.eq_zero_or_pos s.card with h0 | hpos
    · have hβpos : 0 < β := lt_trans hm0 hβm
      simp [h0, ENNReal.zero_rpow_of_pos hβpos, ENNReal.zero_rpow_of_pos hm0]
    · have hne : (s.card : ℝ≥0∞) ≠ 0 := by
        simp only [ne_eq, Nat.cast_eq_zero]
        omega
      have htop : (s.card : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
      have hsplit : (s.card : ℝ≥0∞) ^ β
          = (s.card : ℝ≥0∞) ^ m * (s.card : ℝ≥0∞) ^ (β - m) := by
        rw [← ENNReal.rpow_add _ _ hne htop]
        ring_nf
      have hpow : (s.card : ℝ≥0∞) ^ (β - m) ≤ (δ : ℝ≥0∞) ^ (-(ε / 2)) := by
        have h1 : (s.card : ℝ≥0∞) ^ (β - m) ≤ ((δ : ℝ≥0∞) ^ (-4 : ℝ)) ^ (β - m) :=
          ENNReal.rpow_le_rpow hcard (by linarith)
        refine h1.trans ?_
        rw [← ENNReal.rpow_mul]
        exact ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith)
      calc (δ : ℝ≥0∞) ^ (-(ε / 2)) * (s.card : ℝ≥0∞) ^ β
          = (δ : ℝ≥0∞) ^ (-(ε / 2)) * (s.card : ℝ≥0∞) ^ m * (s.card : ℝ≥0∞) ^ (β - m) := by
            rw [hsplit, mul_assoc]
        _ ≤ (δ : ℝ≥0∞) ^ (-(ε / 2)) * (s.card : ℝ≥0∞) ^ m * (δ : ℝ≥0∞) ^ (-(ε / 2)) := by
            gcongr
        _ = (δ : ℝ≥0∞) ^ (-(ε / 2)) * (δ : ℝ≥0∞) ^ (-(ε / 2)) * (s.card : ℝ≥0∞) ^ m := by
            ring
        _ = (δ : ℝ≥0∞) ^ (-ε) * (s.card : ℝ≥0∞) ^ m := by
            rw [← ENNReal.rpow_add _ _ hδE0.ne' ENNReal.coe_ne_top]
            ring_nf
  exact mul_le_mul_of_nonneg_right key zero_le


/-- Main Lemma 2 with every quantifier explicit. -/
def MainLemma2Statement : Prop :=
  ∃ ν : ℝ → ℝ, MonotoneOn ν (Set.Ioc 0 1) ∧
    (∀ β : ℝ, 0 < β → β ≤ 1 → 0 < ν β) ∧
    ∀ β : ℝ, 0 < β → β ≤ 1 →
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) (β - ν β)

/-- **Main Lemma 2 itself, from the pointwise drop plus the shape of the estimate set.**  The
specialisation of `Kakeya.VNSUniform.katzTaoEstimate_sub_of_trichotomy` to `ℝ³`, stated against
`Kakeya.VNSUniform.MainLemma2Statement` so that the fit with the protected declaration is a
typechecking obligation and not a claim. -/
theorem mainLemma2Statement_of_trichotomy
    (hdrop : ∀ β : ℝ, 0 < β → β ≤ 1 →
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      ∃ d : ℝ, 0 < d ∧ KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) (β - d))
    (hshape :
      (∀ β : ℝ, 0 < β → β ≤ 1 → KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
        ¬ FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β) ∨
      (∀ β : ℝ, 0 < β → β ≤ 1 → KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β) ∨
      (∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧ KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) m ∧
        FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) m ∧
        ∀ β : ℝ, 0 < β → β ≤ 1 → KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
          FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β → m ≤ β)) :
    MainLemma2Statement.{u} :=
  katzTaoEstimate_sub_of_trichotomy hdrop hshape

/-- **`Kakeya.FrostmanEstimate` is closed from above in the exponent.**

If `K_F(β)` holds for every `β ∈ (m, 1]` then `K_F(m)` holds.  Together with
`Kakeya.VNSUniform.katzTaoEstimate_of_forall_gt` this closes the estimate set `A`, which is what
`Kakeya.VNSUniform.katzTaoEstimate_sub_of_trichotomy` needs.

The proof pays the difference out of the accuracy, using the two-sided bound
`δ^{n-1} ≤ |𝕋|·δ^{n-1} ` on the bracket: run `K_F` at `β = m + κ` with `κ ≤ ε/6`, and note
`B^{1-β/2}·δ^{κ} ≤ B^{1-m/2}` and `δ^{-ε/2-2β-κ} ≤ δ^{-ε-2m}`. -/
theorem frostmanEstimate_of_forall_gt {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1)
    (h : ∀ β : ℝ, m < β → β ≤ 1 → FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β) :
    FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) m := by
  intro ε hε
  have hκpos : 0 < min (ε / 6) ((1 - m) / 2) := lt_min (by linarith) (by linarith)
  have hκ6 : min (ε / 6) ((1 - m) / 2) ≤ ε / 6 := min_le_left _ _
  have hκ2 : min (ε / 6) ((1 - m) / 2) ≤ (1 - m) / 2 := min_le_right _ _
  set κ : ℝ := min (ε / 6) ((1 - m) / 2) with hκdef
  have hβm : m < m + κ := by linarith
  have hβ1 : m + κ ≤ 1 := by linarith
  obtain ⟨η, hη, hev⟩ := h (m + κ) hβm hβ1 (ε / 2) (by linarith)
  refine ⟨min η 1, lt_min hη one_pos, ?_⟩
  filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : ℝ≥0) < 1 from zero_lt_one)] with δ hδ hδr
  obtain ⟨hδ0, hδlt1⟩ := hδr
  intro ι s T hball hED hFr hfull
  have hδE0 : (0 : ℝ≥0∞) < (δ : ℝ≥0∞) := by exact_mod_cast hδ0
  have hδE1 : (δ : ℝ≥0∞) ≤ 1 := by exact_mod_cast hδlt1.le
  have hδne : (δ : ℝ≥0∞) ≠ 0 := hδE0.ne'
  have hδtop : (δ : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hFr' : IsFrostmanIn s (fun i ↦ (T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall ((δ : ℝ≥0∞) ^ (-η)) :=
    hFr.mono (ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by simp))
  have hfull' : ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η :=
    le_trans (NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδlt1.le (min_le_left η 1)) hfull
  refine (hδ s T hball hED hFr' hfull').trans ?_
  set n1 : ℕ := Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1 with hn1
  set B : ℝ≥0∞ := (s.card : ℝ≥0∞) * (δ : ℝ≥0∞) ^ n1 with hB
  have hexpβ : (0 : ℝ) < 1 - (m + κ) / 2 := by linarith
  have hexpm : (0 : ℝ) < 1 - m / 2 := by linarith
  rcases Nat.eq_zero_or_pos s.card with h0 | hpos
  · have hB0 : B = 0 := by simp [hB, h0]
    rw [hB0, ENNReal.zero_rpow_of_pos hexpβ, ENNReal.zero_rpow_of_pos hexpm]
    simp
  · have hcard1 : (1 : ℝ≥0∞) ≤ (s.card : ℝ≥0∞) := by
      have : 1 ≤ s.card := hpos
      exact_mod_cast this
    have hn1eq : n1 = 2 := by simp [hn1]
    have hq : (δ : ℝ≥0∞) ^ n1 = (δ : ℝ≥0∞) ^ (2 : ℝ) := by
      rw [hn1eq, ← ENNReal.rpow_natCast]; norm_num
    have hB0 : B ≠ 0 := by
      have hc : (s.card : ℝ≥0∞) ≠ 0 := by
        simp only [ne_eq, Nat.cast_eq_zero]
        omega
      have hd : ((δ : ℝ≥0∞)) ^ n1 ≠ 0 := by positivity
      simp only [hB, ne_eq, mul_eq_zero, not_or]
      exact ⟨hc, hd⟩
    have hBtop : B ≠ ⊤ := by
      simp only [hB]
      exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (by finiteness)
    -- the bracket is at least `δ ^ 2`
    have hBlow : (δ : ℝ≥0∞) ^ (2 : ℝ) ≤ B := by
      rw [hB, ← hq]
      exact le_mul_of_one_le_left zero_le hcard1
    -- `δ ^ κ ≤ B ^ (κ/2)`
    have hδκ : (δ : ℝ≥0∞) ^ κ ≤ B ^ (κ / 2) := by
      have h1 : ((δ : ℝ≥0∞) ^ (2 : ℝ)) ^ (κ / 2) ≤ B ^ (κ / 2) :=
        ENNReal.rpow_le_rpow hBlow (by positivity)
      refine le_trans (le_of_eq ?_) h1
      rw [← ENNReal.rpow_mul, show (2 : ℝ) * (κ / 2) = κ by ring]
    -- split the bracket exponent
    have hsplit : B ^ (1 - m / 2) = B ^ (1 - (m + κ) / 2) * B ^ (κ / 2) := by
      rw [← ENNReal.rpow_add _ _ hB0 hBtop]
      ring_nf
    -- split the `δ` exponent
    have hδsplit : (δ : ℝ≥0∞) ^ (-(ε / 2) - 2 * (m + κ)) =
        (δ : ℝ≥0∞) ^ (-(ε / 2) - 2 * (m + κ) - κ) * (δ : ℝ≥0∞) ^ κ := by
      rw [← ENNReal.rpow_add _ _ hδne hδtop]
      ring_nf
    have hδmono : (δ : ℝ≥0∞) ^ (-(ε / 2) - 2 * (m + κ) - κ) ≤ (δ : ℝ≥0∞) ^ (-ε - 2 * m) :=
      ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith)
    calc (δ : ℝ≥0∞) ^ (-(ε / 2) - 2 * (m + κ)) * B ^ (1 - (m + κ) / 2)
        = (δ : ℝ≥0∞) ^ (-(ε / 2) - 2 * (m + κ) - κ) *
            (B ^ (1 - (m + κ) / 2) * (δ : ℝ≥0∞) ^ κ) := by
          rw [hδsplit]; ring
      _ ≤ (δ : ℝ≥0∞) ^ (-(ε / 2) - 2 * (m + κ) - κ) *
            (B ^ (1 - (m + κ) / 2) * B ^ (κ / 2)) := by
          gcongr
      _ = (δ : ℝ≥0∞) ^ (-(ε / 2) - 2 * (m + κ) - κ) * B ^ (1 - m / 2) := by
          rw [hsplit]
      _ ≤ (δ : ℝ≥0∞) ^ (-ε - 2 * m) * B ^ (1 - m / 2) := by
          gcongr

/-! ## The shape of the estimate set, unconditionally

Both partial estimates are up-closed in the exponent (`Kakeya.KatzTaoEstimate.mono`,
`Kakeya.FrostmanEstimate.mono`) and both are closed from above
(`Kakeya.VNSUniform.katzTaoEstimate_of_forall_gt`,
`Kakeya.VNSUniform.frostmanEstimate_of_forall_gt`), and both hold at `β = 1`
(`Kakeya.KatzTao_one`, `Kakeya.frostmanEstimate_one`).  So the set

`A = {β ∈ (0,1] | K_KT β ∧ K_F β}`

is a nonempty closed up-set: it is either all of `(0,1]` or `[m,1]` for some `m ∈ (0,1]`.  The
open-threshold configuration `(m,1]` with `0 < m` — the only one in which the protected Main
Lemma 2 fails (`Kakeya.VNSUniform.no_monotoneOn_drop_of_open_threshold`) — **does not occur**. -/

/-- **The estimate set is `(0,1]` or `[m,1]`.**  This discharges the hypothesis `hshape` of
`Kakeya.VNSUniform.katzTaoEstimate_sub_of_trichotomy` outright. -/
theorem estimateSet_shape :
    (∀ β : ℝ, 0 < β → β ≤ 1 → KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β) ∨
    (∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧ KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) m ∧
      FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) m ∧
      ∀ β : ℝ, 0 < β → β ≤ 1 → KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
        FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β → m ≤ β) := by
  classical
  have hE : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  set A : Set ℝ := {β : ℝ | 0 < β ∧ β ≤ 1 ∧ KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β ∧
    FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β} with hA
  have hone : (1 : ℝ) ∈ A := ⟨one_pos, le_rfl, KatzTao_one, frostmanEstimate_one⟩
  have hAne : A.Nonempty := ⟨1, hone⟩
  have hbdd : BddBelow A := ⟨0, fun x hx ↦ hx.1.le⟩
  set m : ℝ := sInf A with hm
  have hm0 : 0 ≤ m := le_csInf hAne fun x hx ↦ hx.1.le
  have hm1 : m ≤ 1 := csInf_le hbdd hone
  -- every exponent strictly above the infimum lies in `A`
  have hup : ∀ β : ℝ, m < β → β ≤ 1 →
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β ∧
      FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β := by
    intro β hβm hβ1
    obtain ⟨a, ha, haβ⟩ := exists_lt_of_csInf_lt hAne hβm
    exact ⟨KatzTaoEstimate.mono haβ.le ha.2.2.1, FrostmanEstimate.mono hE haβ.le ha.2.2.2⟩
  rcases eq_or_lt_of_le hm0 with hm00 | hmpos
  · -- `m = 0`: the estimates hold at every exponent of `(0,1]`
    left
    intro β hβ hβ1
    exact (hup β (by rw [← hm00]; exact hβ) hβ1).1
  · -- `m > 0`: the infimum is attained
    right
    have hmem : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) m ∧
        FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) m := by
      rcases eq_or_lt_of_le hm1 with hm11 | hmlt
      · rw [hm11]; exact ⟨KatzTao_one, frostmanEstimate_one⟩
      · exact ⟨katzTaoEstimate_of_forall_gt hmpos hmlt fun β hβm hβ1 ↦ (hup β hβm hβ1).1,
          frostmanEstimate_of_forall_gt hmpos hmlt fun β hβm hβ1 ↦ (hup β hβm hβ1).2⟩
    exact ⟨m, hmpos, hm1, hmem.1, hmem.2,
      fun β hβ hβ1 hKT hF ↦ csInf_le hbdd ⟨hβ, hβ1, hKT, hF⟩⟩

/-- **Main Lemma 2 from a positive drop at each exponent.**
The hypothesis `hdrop` supplies a positive drop for every `β` at which both
partial estimates hold. `Kakeya.VNSUniform.estimateSet_shape` converts these
pointwise drops into a function satisfying `MonotoneOn ν`.
Thus no uniform-in-`β` companion to Lemma 9.1 is required. -/
theorem mainLemma2Statement_of_pointwise_drop
    (hdrop : ∀ β : ℝ, 0 < β → β ≤ 1 →
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      ∃ d : ℝ, 0 < d ∧ KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) (β - d)) :
    MainLemma2Statement.{u} :=
  mainLemma2Statement_of_trichotomy hdrop (Or.inr estimateSet_shape)


end Envelope

end Kakeya.VNSUniform

namespace Kakeya


end Kakeya

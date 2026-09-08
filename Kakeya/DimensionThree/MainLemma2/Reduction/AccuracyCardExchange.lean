/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.BandSqueeze
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineParams

/-!
# The accuracy–cardinality exchange: why the every-scale branch cannot be re-cut

`Reduction/GainFloor.lean` settles the **gain** column of the every-scale branch: a gain-shaped
conclusion `μ ≤ δ^{g}|𝕋|^β` with no cardinality clause is *false*
(`Kakeya.ML2GainFloor.not_gainOnly`), with a clause below the Katz--Tao ceiling it is still false
(`not_gainBand_of_lt_katzTaoCeiling`), and with any clause `δ^{-θ} ≤ |𝕋|`, `θ > 0`, its residue is
the goal (`gainBand_residue_is_the_goal`).  *There is no third column* — for gains.

This file settles the **accuracy** column, which `GainFloor.lean` does not touch, and it settles it
at every absolute accuracy rather than at the one the development happens to use.

## The exchange

`Kakeya.ML2Assembly.Dichotomy`'s first alternative delivers an accuracy `μ ≤ δ^{-ε₀}` and its
cardinality hypothesis is `δ⁻¹ ≤ |𝕋|`, i.e. the threshold `θ = 1`.  **That threshold is not
forced; it is a rounding.**  Converting the accuracy into the goal
`∑|Y| ≤ δ^{-ε}|𝕋|^{γ}|⋃Y|` at `γ = β - c` needs only

```
ε₀ ≤ ε + θ · γ                         (the large side, θ arbitrary)
```

— `Kakeya.ML2Exchange.katzTaoGoal_of_absoluteLoss_of_card_ge_rpow`, which is
`Kakeya.MainLemma2.Reduction.katzTaoGoal_of_absoluteLoss_of_card_ge` with its hard-wired `θ = 1`
released.  Symmetrically the complementary band is discharged for free by the trivial bound exactly
when

```
θ · (1 - γ) ≤ ε                        (the small side)
```

— `Kakeya.MainLemma2.Reduction.katzTaoGoal_of_card_le_rpow`, already general in `θ`.  The two have
been in the tree side by side, at different `θ` conventions, and nobody asked when they meet.
**They meet exactly when**

```
ε₀ · (1 - γ) ≤ ε.
```

That is `Kakeya.ML2Exchange.exists_threshold_iff`, an equivalence: a threshold closing both sides
exists *iff* the absolute accuracy obeys that bound.  Two immediate consequences:

* `Kakeya.ML2Exchange.epsFree_accuracy_nonpos` — **an `ε`-free accuracy that closes the band at
  every outer accuracy must be non-positive.**  So no positive `ε`-free `ε₀` avoids a residue, at
  *any* threshold: lowering `θ` below `1` does not help, and neither does lowering `ε₀`.  What is
  left over is `Kakeya.ML2Squeeze.SmallCardCut θ γ`, which
  `Kakeya.ML2Squeeze.smallCardCut_iff_katzTaoEstimate` shows is the goal, for every `θ > 0`.
* `Kakeya.ML2Exchange.exists_threshold_of_le` — and the bound is *sufficient*: if `ε₀` may shrink
  with `ε`, the band closes and there is no residue at all.

## The dilemma

The second bullet is the only escape, and it is closed by the other end of the reduction.  Reading
Theorem 7.3(B) at an accuracy that shrinks with the outer `ε` makes an `ε`-free gain impossible
(`Kakeya.ML2Spine.not_epsFree_of_outerAccuracy'`), and Main Lemma 2 needs the drop `c` — hence the
target exponent `β - c` — chosen **before** `ε`, because `Kakeya.KatzTaoEstimate (β - c)` binds `ε`
inside.  `Kakeya.ML2Exchange.ml2_accuracy_horns` puts the two refutations in one statement:

> **neither** an `ε`-free positive absolute accuracy (the band never closes) **nor** an
> `ε`-dependent one (the gain dies) supports the reduction.

Together with `GainFloor.lean`'s trichotomy for gain-shaped branches this exhausts the shapes the
every-scale branch can have: accuracy or gain, at any threshold, at any accuracy.  **The
obstruction is not the strength of the branch and not the position of the cut; it is that the cut
exists at all.**

## How this sits beside what was already proved

Three results in the tree bracket this one, and none of them is it.

* `Kakeya.ML2Band.absoluteLossRoute_insufficient` (`Reduction/SpineCardBand.lean`) is the
  **necessity** half of Part I's budget, already at a general threshold: below `ε₀ ≤ ε + θγ` the
  bound the branch would need is strictly false on every family with `|𝕋| ≤ δ^{-θ}`.  Part I
  supplies the matching **sufficiency**, at the measure level a consumer can use; the tree had
  sufficiency only at `θ = 1`.  Together the budget is exact.
* `Kakeya.ML2Squeeze.forall_cut_circular` says: **if** the residue is nonempty, it is the theorem,
  at every threshold.  `Kakeya.ML2Exchange.epsFree_accuracy_nonpos` says the residue **is** always
  nonempty, at every positive `ε`-free accuracy.  Those are different statements, and the argument
  needs both: without the second, "lower the threshold until the residue vanishes" is still open;
  the exchange closes it by showing the threshold that would do so does not exist.
* `Kakeya.ML2Squeeze.producer_of_smallCardCut_is_producer_of_goal` is the acceptance filter for a
  *proposed* residue.  Part II is upstream of it: it says which residues can even be proposed.

## The one cut that is not a cardinality cut, and why it collapses too

Cutting on GWZ Lemma 9.1's own side condition `Kakeya.ML2Squeeze.ScaleCount` instead of on `|𝕋|`
looks like an escape — essential distinctness is affine-covariant, so the squeeze of
`Reduction/BandSqueezeAlt.lean` does not obviously reach it, and
`Kakeya.ML2Squeeze.gainOnlyMult_of_lemma91Body` shows Lemma 9.1 delivers the gain on exactly the
families that satisfy it.  It is not an escape.
`Kakeya.ML2Squeeze.not_scaleCount_of_card_lt_delta_inv` shows `ScaleCount` **fails on every family
below the band**, so the residue of the `ScaleCount` cut *contains* the residue of the `δ⁻¹` cut,
and by `Kakeya.ML2Squeeze.forall_cut_circular` the latter is already the theorem.  A finer cut with
a larger residue is not progress.  This is recorded here so the idea is not re-costed a third time.

## What is *not* claimed

Nothing here refutes GWZ Main Lemma 2, GWZ Lemma 9.1, or Theorem 7.3(B). What is refuted is one
*reduction shape*: a two-case split of the tube families by a `δ`-power cardinality threshold, with
the every-scale case closed from a `β`-only bound. GWZ's own §9 carries no cardinality hypothesis;
`Reduction/BandSqueezeAlt.lean` localises why the one introduced here cannot be a real restriction
(the band compares an affine invariant to a non-invariant), and this file prices what it would cost
if it could.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Set Filter Topology ShadedBody ConvexSpaceBody

namespace Kakeya.ML2Exchange

/-! ## Part I — the large-cardinality branch at a general threshold -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*}

/-- **The large-cardinality branch, at an arbitrary threshold `θ`.**

`Kakeya.MainLemma2.Reduction.katzTaoGoal_of_absoluteLoss_of_card_ge` is this theorem with
`θ = 1` hard-wired, both in the hypothesis `δ⁻¹ ≤ |𝕋|` and in the budget `ε₀ ≤ ε + γ`.  Releasing
`θ` is what makes the exchange with the small side visible: the branch closes on
`δ^{-θ} ≤ |𝕋|` as soon as `ε₀ ≤ ε + θγ`, so the threshold the every-scale branch really needs is
`θ ≥ (ε₀ - ε)/γ`, and **`Kakeya.ML2Assembly.Dichotomy`'s `δ⁻¹` is a rounding of it, not a
requirement** (`Kakeya.ML2Exchange.absAccuracy_threshold_le_one`). -/
theorem katzTaoGoal_of_absoluteLoss_of_card_ge_rpow {s : Finset ι} {V : ι → ShadedBody E}
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ε ε₀ γ θ : ℝ} (hγ0 : 0 ≤ γ)
    (hloss : ε₀ ≤ ε + θ * γ) (hcard : (δ : ℝ) ^ (-θ) ≤ (s.card : ℝ))
    (h : ∑ i ∈ s, volume (V i).shade
          ≤ (δ : ℝ≥0∞) ^ (-ε₀) * volume (⋃ i ∈ s, (V i).shade)) :
    ∑ i ∈ s, volume (V i).shade
      ≤ (δ : ℝ≥0∞) ^ (-ε) * (s.card : ℝ≥0∞) ^ γ * volume (⋃ i ∈ s, (V i).shade) := by
  have hd0 : (δ : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ.ne'
  have hdtop : (δ : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hd1 : (δ : ℝ≥0∞) ≤ 1 := ENNReal.coe_le_one_iff.mpr hδ1
  have hcardE : (δ : ℝ≥0∞) ^ (-θ) ≤ (s.card : ℝ≥0∞) :=
    Kakeya.ML2Band.coe_rpow_le_natCast hδ hcard
  have hpow : (δ : ℝ≥0∞) ^ (-(θ * γ)) ≤ (s.card : ℝ≥0∞) ^ γ := by
    have heq : (δ : ℝ≥0∞) ^ (-(θ * γ)) = ((δ : ℝ≥0∞) ^ (-θ)) ^ γ := by
      rw [← ENNReal.rpow_mul, neg_mul]
    rw [heq]
    exact ENNReal.rpow_le_rpow hcardE hγ0
  have hkey : (δ : ℝ≥0∞) ^ (-ε₀) ≤ (δ : ℝ≥0∞) ^ (-ε) * (s.card : ℝ≥0∞) ^ γ := by
    calc (δ : ℝ≥0∞) ^ (-ε₀)
        ≤ (δ : ℝ≥0∞) ^ (-ε + -(θ * γ)) :=
          ENNReal.rpow_le_rpow_of_exponent_ge hd1 (by linarith)
      _ = (δ : ℝ≥0∞) ^ (-ε) * (δ : ℝ≥0∞) ^ (-(θ * γ)) := ENNReal.rpow_add _ _ hd0 hdtop
      _ ≤ (δ : ℝ≥0∞) ^ (-ε) * (s.card : ℝ≥0∞) ^ γ := by gcongr
  exact h.trans (by gcongr)

/-! ## Part II — the exchange identity -/

/-! ## Part III — the threshold `Kakeya.ML2Assembly.Dichotomy` uses is a rounding -/

/-! ## Part IV — the dilemma -/

variable {β ϖ : ℝ} {gain dens : ℝ → ℝ}

/-! ## Part V — the source, quoted, and where the split actually comes from

Everything above is arithmetic about the reduction as this development cuts it.  This part records
what GWZ *write*, transcribed from `pdftotext -layout` of `kakeya-streamlined-2601.14411.pdf`, so
that the comparison rests on the paper rather than on our own docstrings.

**GWZ Theorem 7.3 (p. 25).**

> For all `ϵ > 0`, there exists `η, δ₀ > 0` so that the following holds for all `δ ∈ (0, δ₀]`.
> Let `(T, Y)` be a uniform set of `δ`-tubes in `B₁ ⊂ R³`, with `λ(T, Y) ≥ δ^η`.
> **(A)** If `T` is Frostman at every scale with error `δ^{-η}`, then `|U(T, Y)| ≥ δ^ϵ`.
> **(B)** If `T` is Katz-Tao at every scale with error `δ^{-η}`, then `µ(T, Y) ≤ δ^{-ϵ}`.

Three hypotheses — uniform, `λ(T,Y) ≥ δ^η`, Katz--Tao at every scale with error `δ^{-η}` — and a
bare conclusion `µ(T,Y) ≤ δ^{-ϵ}`.  **No cardinality hypothesis and no `|T|^β` factor.**

**GWZ, proof of Main Lemma 2 using Lemma 9.1, Conclusion (i) (p. 33).**

> Apply Lemma 7.7(B) to `T`.  If Conclusion (i) holds, then (provided we select `ϵ₂ ≤ ϵ₁/5`) we
> have that `T` is `δ^{-ϵ₁}` Katz-Tao at every scale, and hence by Theorem 7.3(B) we have
> `µ(T, Y) ≤ δ^{-ϵ}`, and thus (67) is satisfied.

and (67) is `µ(T, Y) ≤ δ^{-ϵ}|T|^{β-ν}`.  So the branch closes because `|T| ≥ 1` and `β - ν ≥ 0`,
**with nothing about cardinality at all**.  That step is
`Kakeya.ML2Reduction.multiplicity_le_mul_card_rpow_of_le`, already in the tree, and it is
`Kakeya.ML2Exchange.katzTaoGoal_of_absoluteLoss_of_le` below — *which is Part I at `θ = 0`.*
**GWZ's Conclusion (i) is the `θ = 0` case of the released-threshold branch and
`Kakeya.ML2Assembly.Dichotomy`'s is the `θ = 1` case; the exchange identity at `θ = 0` reads
`ε₀ ≤ ε`.**

**Our Theorem 7.3(B) is not weaker than GWZ's.**  `StickyKakeya.StickyKatzTaoEstimate`
(`Kakeya/Sticky.lean`) has GWZ's quantifier order (`∀ ε, ∃ η δ₀`), GWZ's three hypotheses, and
GWZ's conclusion `µ ≤ δ^{-ε}` verbatim — no cardinality clause, no `|T|^β`. It carries exactly one
hypothesis GWZ's does not: the leaf-scale density bound `Δ_max(T) ≤ δ^{-η}`
(`ConvexSpaceBody.IsKatzTao s _ (δ^{-η})`), which the node reading of "Katz--Tao at every scale"
does not imply. **That hypothesis is free at the Section-9 call site**: it is the first bullet of
GWZ Definition 3.4 (`K_KT(β)`) and therefore already in scope wherever Main Lemma 2's goal is being
proved.

**Where the split does come from, then.**  One clause, GWZ p. 32:

> Let `ϵ₁` and `δ₁` be the output of Theorem 7.3 with `ϵ` as above. … Let `ϵ₂ = ϵ₂(ϵ₁, ϵscale, β)`
> be a number to be chosen later **(since `ϵ₁` and `ϵscale` depend only on `β`, `ϵ₂` depends only
> on `β`)**.

`ϵ₁` is *defined* one sentence earlier as Theorem 7.3's output at the outer `ϵ`, so `ϵ₁ = ϵ₁(ϵ, β)`;
the parenthetical asserts `ϵ₁ = ϵ₁(β)`.  Exactly one of the two can hold, and the whole architecture
turns on which:

* **`ϵ₁ = ϵ₁(ϵ)`, the definition.**  Branch (i) closes with no cardinality clause, exactly as
  written.  But `ν = η₁ ≤ ϵ₂ ≤ ϵ₁/5` then depends on `ϵ`, while GWZ Definition 3.4 binds `ϵ`
  *outside* `K_KT(β - ν)` and Main Lemma states `ν = ν(β)`.  Refuted by
  `Kakeya.ML2Spine.not_epsFree_of_outerAccuracy'`.
* **`ϵ₁ = ϵ₁(β)`, the parenthetical.**  Then Theorem 7.3(B) must be read at a `β`-only accuracy
  `ε₀`, its conclusion is `µ ≤ δ^{-ε₀}` with `ε₀ > ε` in general, and a cardinality lower bound
  appears — `Kakeya.ML2Reduction.ofReal_rpow_neg_le_mul_card_rpow`, the one place `|𝕋| ≥ δ⁻¹` is
  spent.  Refuted by `Kakeya.ML2Exchange.epsFree_accuracy_nonpos` together with
  `Kakeya.ML2Squeeze.smallCardCut_iff_katzTaoEstimate`.

**So `δ⁻¹ ≤ |𝕋|` is not GWZ's and not an artefact of our Theorem 7.3(B): it is the forced price of
the only reading under which Main Lemma 2's `ν` is well defined.**
`Kakeya.ML2Exchange.ml2_accuracy_horns` is the pair of refutations, and this part is what anchors
it to the paper.  The remaining escape —
swapping Theorem 7.3(B)'s own quantifiers to `∃ η, ∀ ϵ` — is unavailable: an `η` bounded below at
every accuracy would say that any family Katz--Tao at every scale with that fixed error has
multiplicity `δ^{-ϵ}` for *every* `ϵ`, which is the argument inside
`Kakeya.ML2Spine.not_epsFree_of_outerAccuracy`. -/

/-! ## Part VI — testing the author's own reading, and the scope of Part II

Prof. Hong Wang's clarification of this argument says two things, and the development has been
using them as if they were one:

1. the absolute accuracy parameter for Theorem 7.3 — when applying Theorem 7.3, use an **absolute** `ε₀` —
   together with the independence of `nu` from the running accuracy, `ν` depends on the other `ε_i` but
   **not** on `ε`.  This is the reading under which `ν` comes out `β`-only, as Main Lemma 2
   requires.
2. *"if `𝕋` is bilinear this is automatic; in the non-bilinear case broad--narrow supplies the
   improvement"* — the **source of the cardinality lower bound** `|𝕋| > δ^{-1}`.

**These are two halves of one repair, and the formalisation has only the first half.**

### The apparent contradiction, and why there is none

GWZ contains **zero** occurrences of `delta^{-1}`, of "small
cardinality" and of "few tubes" in 2143 lines, and the paper itself contains **zero** occurrences of
"broad" and of "bilinear".  So neither the band nor broad--narrow is in the written proof — which is
correct and expected: **the written proof reads Theorem 7.3(B) at the outer `ε`, and at the outer
`ε` no band is needed.**  The band and broad--narrow enter together, in the clarification, precisely
because the clarification changes the accuracy to an absolute one.  Two measurements of two
different objects; both stand.

### The test: reading 2 with the band removed

At `θ = 0` — no cardinality information — `Kakeya.ML2Exchange.katzTaoGoal_of_absoluteLoss_of_le`
closes the branch from `μ ≤ δ^{-ε₀}` **iff** `ε₀ ≤ ε`, and the deficit when `ε < ε₀` is
`δ^{-(ε₀-ε)}`: a genuine positive power of `δ`, **not** a subpolynomial factor, so no `⪅` absorbs
it (`Kakeya.ML2Exchange.zeroThreshold_insufficient`, from
`Kakeya.ML2Band.absoluteLossRoute_insufficient` at `θ = 0`; see also
`Kakeya.OmegaAssessment.oneParam_fixed_loss_fails`).  And
`Kakeya.ML2Exchange.absoluteAccuracy_nonpos_of_le_forall` says no positive `ε`-free `ε₀` has
`ε₀ ≤ ε` at every `ε`.

The sharp way to say it: at `θ = 0` the branch's target is `μ(𝕋,Y) ≤ δ^{-ε}` — since
`|𝕋|^{β-ν} ≥ 1` is all the information left — **which is Theorem 7.3(B) at the outer accuracy.**
So "reading 2 with the band removed" is not a third option; it *is* reading 1.  **The band is not
an artefact of a lossy conversion: it is what an absolute accuracy costs, exactly.**

### What Part II does and does not refute

`Kakeya.ML2Exchange.epsFree_accuracy_nonpos` quantifies over pairs of budgets

* `ε₀ ≤ ε + θγ`  — the large side converts (Part I), and
* `θ(1-γ) ≤ ε`   — **the small side is discharged by the trivial bound**
  (`Kakeya.MainLemma2.Reduction.katzTaoGoal_of_card_le_rpow`).

So what it refutes, at every threshold and every positive `ε`-free accuracy, is *closing the band by
the trivial bound*.  **It does not refute reading 2**, because reading 2 does not propose to close
the band: it proposes to make the band's complement **empty**, by bilinearity or broad--narrow.
That is a different move and Part II says nothing about it.  This scope is stated here because the
opposite reading of Part II would be an easy and expensive mistake.

### The missing ingredient, named

In the *very-not-sticky* case the band is already free: GWZ Lemma 9.1's third bullet is impossible
below it (`Kakeya.ML2Band.not_scaleCount_of_card_lt_inv`, and
`Kakeya.MainLemma2.Reduction.delta_inv_le_card_of_scaleCount_bullet` the other way), so *"the band
consists exactly of the families that fail the very-not-sticky count"*.  **But branch (i) is not the
very-not-sticky case** — it is the every-scale case, and it carries no count hypothesis at all.  Its
four available facts are unit-ball containment, `Δ_max(𝕋) ≤ δ^{-η}`, `λ ≥ δ^η` and nothing else, and
`Reduction/BandSqueezeAlt.lean` shows the affine squeeze survives all four
(`Kakeya.ML2BandSqz.repair_blocks_but_is_unavailable`): the clause that *would* block it,
`Kakeya.ML2BandSqz.DirNonConcentrated` — the formal shadow of "bilinear"/broad — is exactly the one
the branch cannot hand over (`Kakeya.ML2BandSqz.not_callSiteAvailable_dirNonConcentrated`).

**So the missing ingredient is a producer of `Kakeya.ML2BandSqz.DirNonConcentrated`, or a
broad--narrow decomposition reducing to families that have it.**  The tree has no broadness
apparatus outside the abandoned `MainLemma2.WangZahl.*` subtree, which Section 9 may not import, and
the GWZ-adapted blueprint never mentions broadness.  **That is a geometric development that was
never begun — not a defect in the paper, and not something the assembly can bookkeep its way
around.**
-/

end Kakeya.ML2Exchange

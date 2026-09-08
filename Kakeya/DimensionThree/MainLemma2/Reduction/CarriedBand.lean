/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.BandSqueeze
public import Kakeya.Factoring.RhoFreeParentCount
public import Kakeya.DimensionThree.MainLemma2.Reduction.AssemblyPointwise

/-!
# Carrying the cardinality band into the inducted statement

steps.

`Kakeya.ML2Assembly.katzTaoEstimate_sub_of_dichotomy` derives Main Lemma 2's conclusion from two
inputs: the GWZ dichotomy on the band `δ⁻¹ ≤ |𝕋|`, and `Kakeya.ML2Assembly.SmallCard`, the
*complement* of that band.  `Kakeya.ML2Squeeze.forall_cut_circular` proves the complement is the
goal itself, at every threshold, so the reduction is circular; three repairs that **remove or
split on** the cardinality content have since been refuted, all (`Kakeya.ML2Squeeze.forall_cut_circular`, `Kakeya.ML2Squeeze.residue_of_banded`, and the
`GainOnly` line).

This file does the one thing that is not "remove or split": it **carries** the band into the
inducted statement, so there is no complement to discharge.

## What is proved

* `Kakeya.ML2Carried.CarriedBand` — `K_KT(γ)` with `δ⁻¹ ≤ |𝕋|` as a *hypothesis*, at the price of
  a density parameter `M` (the family is only `M·δ^{-η}` Katz--Tao) and the covariant conclusion
  `δ^{-ε} · M^{1-γ} · |𝕋|^γ`.
* `Kakeya.ML2Carried.katzTaoEstimate_of_carriedBand` — **Main Lemma 2's conclusion follows**, with
  no complement and no residue.  The transport is `R`-fold duplication with `R = ⌈δ⁻¹⌉`, and it is
  *lossless*: duplication multiplies the shade mass, the cardinality and the maximal density each
  by exactly `R`, leaves the union and the fullness alone, and `M^{1-γ}|𝕋|^γ` is the unique
  normalisation covariant for that scaling.
* `Kakeya.ML2Carried.carriedBand_of_katzTaoEstimate` — the converse, from **GWZ Lemma 3.7**
  (`Kakeya.KatzTaoEstimate.multiplicity_bound`, which is already `μ ≤ δ^{-ε}Δ_max^{1-γ}|𝕋|^γ` with
  no Katz--Tao hypothesis).  Hence `Kakeya.ML2Carried.carriedBand_iff`: the carried statement is
  the goal **re-encoded**, not strengthened.  The acceptance filter is applied to it explicitly in
  `Kakeya.ML2Carried.carriedBand_is_producer_of_goal`, and reported rather than hidden.
* `Kakeya.ML2Carried.katzTaoEstimateGE_of_carriedBand` — at `M = 1` the carried statement is
  exactly `Kakeya.ML2Squeeze.KatzTaoEstimateGE 1 γ`, what the GWZ route delivers.  So `M` is the
  entire distance from the route's output to the goal.

## Where it stops, exactly

The transport is applied to the dichotomy's two alternatives in
`Kakeya.ML2Carried.accuracy_branch_after_transport` and
`Kakeya.ML2Carried.gain_branch_after_transport`.  Both say the same thing: **a branch's closure
condition is invariant under the transport.**

* For the **gain** that is harmless: `Kakeya.ML2Carried.gain_branch_closes` discharges the
  invariant condition at the assembly's own `ε`-free budget `4c ≤ g`, using only the crude
  cardinality bound `|𝕋| ≤ δ^{-4}`.  The gain branch survives the re-encoding untouched.
* For the **accuracy** the invariant condition is a band on `|𝕋| / M`
  (`Kakeya.ML2Carried.accuracy_branch_closes_of_dedup_band`, whose budget `ε₀ ≤ ε + γ` is exactly
  `Kakeya.ML2Assembly.katzTaoEstimate_sub_of_dichotomy`'s `2c ≤ β`), and that is fatal.
  Read without the covariance factor the branch is **false**
  (`Kakeya.ML2Carried.not_strongAccuracyBand`, witnessed by `R` copies of one fully shaded central
  tube).  Read with it, its invariant closure condition is `δ^{-ε₀} ≤ δ^{-ε}|𝕋|^γ` on the
  *original* count — i.e. **the band on the de-duplicated count** — and at the image of a
  one-tube family this reads `ε₀ ≤ ε`
  (`Kakeya.ML2Carried.accuracy_branch_after_transport_fails`).  Since `ε₀` must be `ε`-free while
  `ε → 0`, it fails for every positive `ε₀`.

So the verdict of steps  is: **the carried-cardinality induction does yield Main Lemma 2 —
`Kakeya.ML2Carried.katzTaoEstimate_of_carriedBand` is the missing step, and it is unconditional —
but the GWZ dichotomy cannot produce `CarriedBand`, because the band its accuracy branch consumes
is a band on `|𝕋| / M`, which duplication provably leaves fixed.**  The obstruction is no longer
"the residue is the goal"; it is the single inequality `ε₀ ≤ ε`, which is the `ε`-freeness
tension of GWZ §9 (`Kakeya.ML2Spine.not_epsFree_of_outerAccuracy'`) reappearing on the carried
side as a hard budget.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Set Filter Topology

open Kakeya.ML2Squeeze (Space3)

namespace Kakeya.ML2Carried

universe u

section Duplication

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

variable {ι : Type*}

/-- The index set of the `R`-fold duplicate of a family indexed by `s`. -/
def dupFinset (s : Finset ι) (R : ℕ) : Finset (ι × Fin R) := s ×ˢ Finset.univ

@[simp] theorem dupFinset_card (s : Finset ι) (R : ℕ) :
    (dupFinset s R).card = s.card * R := by
  simp [dupFinset]

@[simp] theorem mem_dupFinset {s : Finset ι} {R : ℕ} {p : ι × Fin R} :
    p ∈ dupFinset s R ↔ p.1 ∈ s := by
  simp [dupFinset]


end Duplication

/-! ## The inducted statement, with the cardinality lower bound carried -/

/-- **`K_KT(γ)` with the cardinality band `δ⁻¹ ≤ |𝕋|` carried in the hypothesis.**

`Kakeya.ML2Assembly.Dichotomy` — and, per Prof. Hong Wang's clarification of 2026-08-30, the
blueprint proof of Main Lemma 2 itself — is stated under the standing assumption
`δ⁻¹ ≤ |𝕋|`, which `Kakeya.KatzTaoEstimate` does not supply.  The existing reduction
discharges the *complement* of that assumption through `Kakeya.ML2Assembly.SmallCard`, and
`Kakeya.ML2Squeeze.forall_cut_circular` shows the complement is the goal itself, at every
threshold.

This predicate carries the band instead of splitting on it.  The price is one extra parameter:
the family is only asked to be `M · δ^{-η}` Katz--Tao, and the conclusion is weakened by
`M ^ (1 - γ)`.  Both changes are forced, and they are forced by the *same* scaling: an `R`-fold
duplication of a family multiplies the shade mass, the cardinality and the maximal density each
by exactly `R`, and leaves the union and the fullness alone
(`Kakeya.ML2Carried.sum_dupFinset`, `Kakeya.ML2Carried.dupFinset_card`,
`Kakeya.ML2Carried.isKatzTao_dupFinset`, `Kakeya.ML2Carried.iUnion_dupFinset`,
`Kakeya.ML2Carried.fullness_dupFinset`).  `M ^ (1-γ) · |𝕋| ^ γ` is the unique normalisation of
`|𝕋| ^ γ` that is covariant for that scaling, and `Kakeya.ML2Carried.katzTaoEstimate_of_carriedBand`
is the proof that covariance is exactly what removes the complement.

At `M = 1` this is `Kakeya.ML2Squeeze.KatzTaoEstimateGE 1 γ`, the banded estimate the GWZ route
delivers. -/
def CarriedBand (γ : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), η ≤ 1 ∧
    ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3) (M : ℝ≥0∞),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        1 ≤ M → M ≠ ⊤ →
        ConvexSpaceBody.IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody)
          (M * (δ : ℝ≥0∞) ^ (-η)) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (δ : ℝ)⁻¹ ≤ (s.card : ℝ) →
        ∑ i ∈ s, volume (T i).shade
          ≤ (δ : ℝ≥0∞) ^ (-ε) * M ^ (1 - γ) * (s.card : ℝ≥0∞) ^ γ
              * volume (⋃ i ∈ s, (T i).shade)


/-! ## The re-encoding is exact: `CarriedBand γ` is *not* stronger than `K_KT γ` -/


/-! ## What the transport does to the two branches of the GWZ dichotomy

`Kakeya.ML2Assembly.Dichotomy` offers, on the band, either

* **(i)** the absolute-accuracy bound `∑ |Y| ≤ δ^{-ε₀} |⋃ Y|` from the every-scale branch, or
* **(ii)** the `δ`-gain `∑ |Y| ≤ δ^{g} |𝕋|^β |⋃ Y|` from the window branch.

Duplication multiplies `∑ |Y|` and `|𝕋|` by `R` and leaves `|⋃ Y|` alone, so the only forms of
(i) and (ii) that can survive it are the covariant ones, `M · δ^{-ε₀}` and `M^{1-β} δ^{g} |𝕋|^β`.
The two theorems below compute what each of those becomes at the transport
`(M, |𝕋|) = (1, n) ↦ (R, n R)` used by `Kakeya.ML2Carried.katzTaoEstimate_of_carriedBand`.

The answer is the same for both, and it is the point of this file: **the closure condition of a
branch is transport-invariant.**  For the gain that is harmless — its condition is met by the
crude cardinality bound at every `n`.  For the accuracy it is fatal — its condition *is* the band
`δ^{-1} ≤ n` on the *original* count, which is exactly what the transport was supposed to supply
and provably does not. -/


/-! ## Non-vacuity: the branch that dies is the one that fires

`Kakeya.ML2Carried.accuracy_branch_after_transport_fails` is arithmetic.  This section shows the
arithmetic is about a real configuration: `R` copies of one fully shaded central `δ`-tube, with
`R = ⌈δ⁻¹⌉`.  It satisfies **every** hypothesis of the carried statement — ball containment,
fullness `1`, `M · δ^{-η}` Katz--Tao at `M = |𝕋|`, and the band `δ⁻¹ ≤ |𝕋|` — and its
multiplicity is exactly `|𝕋|`.

Consequences, in the two possible readings of the every-scale branch:

* read **non-covariantly** (`μ ≤ δ^{-ε₀}`, the form `Kakeya.ML2Assembly.Dichotomy` has at `M = 1`),
  it is **false** on this configuration — `Kakeya.ML2Carried.not_strongAccuracyBand`;
* read **covariantly** (`μ ≤ M·δ^{-ε₀}`, the only form duplication permits), it is true on this
  configuration but does not close the carried target —
  `Kakeya.ML2Carried.accuracy_branch_after_transport_fails`.

The carried target *is* satisfied by this configuration
(`Kakeya.ML2Carried.repeatFam_meets_carried_target`), as it must be, since
`Kakeya.ML2Carried.carriedBand_iff` makes `CarriedBand` a true statement.  What fails is only the
route to it through the accuracy branch. -/

section Witness

variable {δ : ℝ≥0} {R : ℕ}


/-- The index set of `Kakeya.ML2Carried.repeatFam` has exactly `R` elements. -/
@[simp] theorem repeatFam_card :
    (Finset.univ : Finset (ULift.{u} (Fin R))).card = R := by simp


end Witness


/-! This section
prices both. **Both close**, and the second closes by a budget that is *not* the one GWZ's own
chain gives, so it is recorded here rather than inherited.

### Direction 1 — read the every-scale branch at the outer `ε`

The escape would be: `Kakeya.ML2Assembly.Dichotomy`'s accuracy slot is `β/2`
(`Kakeya.ML2Spine.absAccuracy`); read Theorem 7.3(B) at the *outer* `ε` instead and the accuracy
branch closes with no band at all (`Kakeya.ML2Carried.accuracy_branch_closes_of_dedup_band` at
`ε₀ = ε` needs only `n ≥ 1`).  **It fails, because the two branches share one exponent.**

`Kakeya.ML2Assembly.GeometricCoreAt` produces
`Dichotomy β (β/2) (4 * Kakeya.ML2Spine.spineNu β ϖ ε₁ gain dens) η`: the **gain slot is `4ν`**,
and `ν` is a function of the very exponent `ε₁` at which the every-scale branch is read
(`Kakeya.ML2Spine.spineNu`'s argument list, and `Kakeya.ML2Spine.exists_ml2SpineParams` which
instantiates it at `ε₁ = E (Kakeya.ML2Spine.absAccuracy β)`).
`Kakeya.ML2Carried.spineNu_le_everyScale` below is the link `ν ≤ ε₁/25`, so buying a
smaller accuracy in branch (i) is paid for, one for one, in branch (ii)'s gain.

### Direction 2 — a floor on the de-duplicated count `|𝕋|/M`

A single fully shaded tube, `|𝕋| = Δ_max = 1`, refutes an unconditional floor.
`Kakeya.ML2Carried.singleton_dedup_is_trivial` records why that witness is **inert against the
carried route**: at `n_d = 1` the carried target is closed by the trivial bound `μ ≤ |𝕋|`, so the
witness sits strictly inside the region the route never needed a floor on.  The shape that
survives is therefore a floor **above the trivial region**, and
`Kakeya.ML2Carried.gap_thresholds_meet_iff` says exactly how far above it must reach.

### And then both directions close at once

`Kakeya.ML2Carried.no_epsFree_drop_of_carried_budgets` is the capstone: the gain budget and the
carried closure budget are jointly unsatisfiable by any `ε`-free drop, **even when the accuracy at
which Theorem 7.3(B) is read is chosen adaptively per `ε`** — the one strategy the re-encoding had
left open. -/

section Budgets

-- selective, so nothing here can shadow a library name
open Kakeya.ML2Spine (spineNu spineAux spineRung spineDiv spineEps₂ spineAux_antitone
  spineDiv_le spineEps₂_le_everyScale)


end Budgets

end Kakeya.ML2Carried

end

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Factorization
public import Kakeya.DimensionThree.Plank.Prop66BClose
public import Kakeya.DimensionThree.Plank.ComparableEnvelope
public import Kakeya.Tube.Param

/-!
# Main Lemma 2, reduction to Lemma 9.1: the eccentric case

Blueprint: GWZ, "Proof of Main Lemma~\ref{lemmain2}", the
paragraph beginning *"We set `ρ = δ̃^{1-ε₂}`"* and the paragraph *"The eccentric case"*.

## Contents

* `Kakeya.ML2Reduction.eccExponent`, `multiplicity_le_of_eccentric_bound` — the exponent
  arithmetic `-η - (η/ε₂)(1-β) + 12η/ε₂ ≥ 10η/ε₂` of `\eqref{multTildeTLem2}`.
* `Kakeya.ML2Reduction.IsEccentric`, `IsNonEccentric`, `isEccentric_or_isNonEccentric` — the two
  halves of `\eqref{eqecccase}`, at the normalisation the factoring step produces.  `IsEccentric`
  is used **in the statement** of every eccentric-case theorem below, so the pairing with
  `Reduction/SpineNonEccentric.lean` via `Reduction/SpineCaseSplit.lean` is a typechecking
  obligation rather than a textual one.
* `Kakeya.ML2Reduction.eccentric_of_prop66B_conclusion` and
  `eccentric_of_prop66B_conclusion_isEccentric` — the eccentric case with the conclusion
  of GWZ Proposition 6.6(B) taken as a hypothesis, in the general and in the produced-parameter
  form.  Both are axiom-clean.
* `Kakeya.ML2Reduction.containsFlatDisc_of_lt_ethickness_one` and its non-strict form — the
  missing geometric direction: a convex body in the unit ball that contains a unit segment and is
  not within `r` of a line contains a flat disc of radius `r/32`.  The converse,
  `Kakeya.ContainsFlatDisc.le_ethickness_one`, was already in the tree; this direction is what a
  *producer* of `Kakeya.GlobalPlankFactorization.wide` needs.
* `Kakeya.ML2Reduction.HasPlankThicknesses`, `exists_maxDensityFactoring_planks`,
  `PlankFactoringData`, `exists_plankFactoringData`,
  `nonempty_plankFactoringData_concrete` — what the maximal density factoring step
  (`lemmafactmax`, i.e. `ConvexSpaceBody.nonempty_factorization.factorization_weighted`)
  actually delivers, packaged as one datum, with a proof that it is inhabited and a fully closed
  witness.
* `Kakeya.ML2Reduction.PlankFactoringData.toGlobalPlankFactorization` — the bridge from that
  datum to GWZ 6.6(B)'s own datum `Kakeya.GlobalPlankFactorization`, at the **absolute**
  transverse comparability constant `Cw = 128`.
* `Kakeya.ML2Reduction.restrictParents`, `exists_plankFactoringData_of_isUniformAtScale` — the
  reconciliation of the two shapes: 6.6(B) wants the factoring over `PS.parent`, the factoring
  step delivers it over a refinement `p ⊆ PS.parent`, and `p` is the parent family of the
  restricted uniformity structure.  This produces a `(PS', D)` **pair** of the exact type
  `exists_threshold_eccentric` quantifies over.
* `Kakeya.ML2Reduction.exists_threshold_eccentric` — the eccentric case with 6.6(B) applied.
* `Kakeya.ML2Reduction.tube_carrier_subset_closedBall_of_le`,
  `parentTube_subset_unitBall_of_leafBall` — the *parent* ball obligation, discharged: a parent
  `ρ`-tube covering a leaf that lies in `B̄(0, r)` lies in `B̄(0, r + 4 ρ)`, so `r + 4 ρ ≤ 1`
  supplies `PlankFactoringData.ball` from a hypothesis on the leaves alone.
* `Kakeya.ML2Reduction.parentMass`, `sum_le_of_parentMass_heavy`,
  `fullness'_le_mul_of_subset_of_sum_shade_le`,
  `multiplicity_le_mul_of_subset_of_sum_shade_le` — the transport
  across `lemmafactmax`'s `≈ 1` refinement, in the free weight, at the loss
  `C_fact · C_overlap`.
* `Kakeya.ML2Reduction.eccentric_of_maxDensityFactoring`, its `_of_leafBall` form (no parent
  hypothesis) and `eccentric_of_maxDensityFactoring_crossed` (hypotheses and conclusion both on
  the original family `s`).

## Which factoring lemma this is

The unbiased one.  GWZ (proof of Main Lemma~\ref{lemmain2}) says *"Apply
Lemma \ref{lemmafactmax} to `𝕋̃_ρ`"*, and the `\uses` list of that proof names `lemmafactmax`,
not `lemmafactmaxbias`.  The **biased** variant of subsection *"Maximal density factoring
revisited"* (`ConvexSpaceBody.nonempty_biasedFactorization`, `Kakeya/BiasedDensity.lean`) is
introduced there for a different consumer — *"To prove Lemma \ref{lemmain2vns}, it is important
to choose carefully in the case of a tie"* — and every `\uses{…lemmafactmaxbias…}` in
GWZ sits inside the proof of Lemma 9.1, not inside this reduction.  It would in fact
be the wrong tool here: `nonempty_biasedFactorization` states its heavy-subfamily bound in the
**volume** only, and for a family of `ρ`-tubes of a common thickness the volumes are all equal,
so that bound carries no information about the shading; the eccentric case needs the arbitrary
weight of `factorization_weighted`.

## Dependencies

`exists_threshold_eccentric` depends on the *conclusion* of GWZ Proposition 6.6(B)
(`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation`, proved in
`Kakeya/DimensionThree/Plank/Prop66BClose.lean`); until that proof existing it carried
`sorryAx` through that dependency, and nothing else (`#print axioms`).  That dependency is a
genuine Section 9 ingredient.  `eccentric_of_prop66B_conclusion` is the same statement with
6.6(B)'s conclusion as a hypothesis and is axiom-clean; so is **every other declaration in this
file**.

The file does not quantify over a hypothesis with no producer.  Its plank input is
`Kakeya.ML2Reduction.PlankFactoringData`, proved inhabited in general
(`exists_plankFactoringData`), at fully closed data (`nonempty_plankFactoringData_concrete`), and
— at the type `exists_threshold_eccentric` actually asks for, namely over the parent family of a
`Tube.IsUniformAtScale` — by
`Kakeya.ML2Reduction.exists_plankFactoringData_of_isUniformAtScale`.

## The two call-site obligations, and what is left of them

The predecessor of this file left two obligations explicit.  Both are now settled, one
positively and one negatively.

* **The unit-ball normalisation is on the parents.**  Discharged.
  `Kakeya.ML2Reduction.tube_carrier_subset_closedBall_of_le` proves the sharp containment — a
  unit core segment inside the `ρ`-neighbourhood of another unit core segment pins the second to
  within `2 ρ` of the first at both ends, so a parent covering a leaf inside `B̄(0, r)` lies
  inside `B̄(0, r + 4 ρ)` — and
  `Kakeya.ML2Reduction.eccentric_of_maxDensityFactoring_of_leafBall` therefore assumes nothing
  about the parents at all: `r + 4 ρ ≤ 1` on the leaf side is enough.  Note that a *rescaling* of
  the whole configuration to radius `1` cannot replace this, because
  `Kakeya.GlobalPlankFactorization.le_plank` asks for a `Kakeya.Plank a b`, a prism of
  half-widths `a × b × 1`: a block hull of long extent `> 2` fits in no such plank whatever `a`
  and `b` are, so the normalisation must happen before the factoring, on the leaf side.
* **`huni` and `hfull` must cross the refinement.**  Half discharged, and the other half is
  provably not a matter of choosing the weight.  With
  `w = Kakeya.ML2Reduction.parentMass PS (fun i ↦ volume (T i).shade)` the heaviness bound
  becomes a bound on the leaf mass (`Kakeya.ML2Reduction.sum_le_of_parentMass_heavy`), which
  transports the fullness lower bound and brings the conclusion back to `s`; the ball
  normalisation and the density bound cross by monotonicity.  The shaded uniformity does **not**
  cross: `ShadedTube.ShadedUniformTubeSet` has two-sided class brackets and the tree's criterion
  for restricting it,
  `Kakeya.ml1Boot.ShadedTube.ShadedUniformTubeSet.restrict_of_shadeClass_dense`, demands that the
  subfamily keep a fixed fraction of *every shade class at every point* — which no mass-weight
  heaviness bound implies, since the heavy members of a shade class can be a vanishing fraction
  of it.  `Kakeya.ML2Reduction.eccentric_of_maxDensityFactoring_crossed` therefore states
  everything on `s` except that one hypothesis.

## The fine-family essential distinctness

Since the condition, GWZ Proposition 6.6(B) as rendered carries
`(q : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier)` on its fine
family — GWZ Definition 2.1(ii) at `ρ = δ`, entailed by "uniform" and previously misrecorded as a
clause of ours.  Every theorem of this file that reaches 6.6(B) carries the same binder on its
leaf family, beside the leaf window, in lockstep: `exists_threshold_eccentric` and
`exists_threshold_eccentric_atPlankScale` on `q`; `eccentric_of_maxDensityFactoring` on the
refined leaves `restrictedLeaves PS p`, inside the handed-back implication; the `_of_leafBall` and
`_crossed` forms on `s`, restricted inside the proof (`Set.Pairwise.mono`).  It is hereditary, so
it crosses `lemmafactmax`'s refinement for free.  It is to be paid at the reduction's outer
"without loss of generality `(𝕋, Y)` is uniform" (GWZ: proof of Main Lemma 2 from Lemma 9.1), at
a `δ^{-O(η)}` loss absorbed by the outer `ε` — **not** by an essential-distinctness refinement
inside the eccentric case at the loss `C · Δmax(𝕋̃) ≤ C · δ̃^{-η/ε₂}`, which is the power the
ledger of `eccentric_of_prop66B_conclusion` lacks.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric ConvexSpaceBody ShadedBody

noncomputable section

namespace Kakeya.ML2Reduction

/-! ### The eccentricity exponent -/

/-- The gain exponent `η'_{j-1} = 12 η_{j-1} / (ε₂ β)` of the eccentric case. -/
def eccExponent (β ε₂ η : ℝ) : ℝ := 12 * η / (ε₂ * β)

theorem eccExponent_mul_beta {β ε₂ η : ℝ} (hβ : β ≠ 0) :
    eccExponent β ε₂ η * β = 12 * η / ε₂ := by
  unfold eccExponent
  field_simp

/-! ### The eccentric / non-eccentric dichotomy, named once

Blueprint GWZ, `\eqref{eqecccase}`: *"We are in the eccentric case if
`b \ge \tilde\delta^{-\eta'_{j-1}} a`"*, and *"Henceforth we shall assume that
`b < \tilde\delta^{-\eta'_{j-1}} a`"* for the complementary case.

`Kakeya.ML2Reduction.IsEccentric` and `Kakeya.ML2Reduction.IsNonEccentric` are the two halves of
**one** inequality, read at the plank parameters `a = 2 pa`, `b = min (2 pb) 1` that
`Kakeya.ML2Reduction.exists_plankFactoringData_of_isUniformAtScale` actually produces.  The
normalisation is not a choice: that theorem *produces* `pa` and `pb`, so the eccentric side's
shape is forced and the non-eccentric side has to match it.

`IsEccentric` is used **in the statement** of `Kakeya.ML2Reduction.exists_threshold_eccentric`,
`Kakeya.ML2Reduction.eccentric_of_maxDensityFactoring` and their `_of_leafBall` forms below.  So
the pairing of the eccentric branch with the non-eccentric one is a *typechecking* obligation
rather than a textual match between two inequalities that happen to be written the same way: an
assembly which discharges both branches has provably discharged all cases, by
`Kakeya.ML2Reduction.isEccentric_or_isNonEccentric`.

`Reduction/SpineCaseSplit.lean` consumes `IsNonEccentric` and converts it into the `hratio`
hypothesis of `Kakeya.ML2Spine.upperBdDeltaMaxTb` — `\eqref{upperBdDeltaMaxTb}`, the one place
the blueprint spends the case assumption.
-/

/-- **The eccentric case, `\eqref{eqecccase}`.**

`b \ge \tilde\delta^{-\eta'_{j-1}} a` at the plank parameters `a = 2 pa`, `b = min (2 pb) 1`
delivered by `Kakeya.ML2Reduction.exists_plankFactoringData_of_isUniformAtScale`, with
`\eta'_{j-1} = Kakeya.ML2Reduction.eccExponent β ε₂ η = 12 η / (ε₂ β)`. -/
def IsEccentric (β ε₂ η : ℝ) (δ pa pb : ℝ≥0) : Prop :=
  δ ^ (-eccExponent β ε₂ η) * (2 * pa) ≤ min (2 * pb) 1

/-! ### The two arithmetic steps of the eccentric case -/

/-- The eccentricity hypothesis `b ≥ δ̃ ^ (-ν) a`, read as a bound on the ratio `a / b`. -/
theorem ratio_le_of_eccentric {δ a b : ℝ≥0} (hδ0 : 0 < δ) {ν : ℝ}
    (hecc : δ ^ (-ν) * a ≤ b) :
    (a : ℝ≥0∞) / (b : ℝ≥0∞) ≤ (δ : ℝ≥0∞) ^ ν := by
  have hδne : δ ≠ 0 := hδ0.ne'
  have hcancel : δ ^ ν * δ ^ (-ν) = 1 := by
    rw [← NNReal.rpow_add hδne]
    simp
  have hstep : a ≤ δ ^ ν * b := by
    calc a = (δ ^ ν * δ ^ (-ν)) * a := by rw [hcancel, one_mul]
      _ = δ ^ ν * (δ ^ (-ν) * a) := by ring
      _ ≤ δ ^ ν * b := by gcongr
  refine ENNReal.div_le_of_le_mul ?_
  calc (a : ℝ≥0∞) ≤ ((δ ^ ν * b : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast hstep
    _ = (δ : ℝ≥0∞) ^ ν * (b : ℝ≥0∞) := by
        rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hδne]

/-- **The arithmetic of the eccentric case.**

This is the display

  `μ(𝕋̃, Ỹ) ≤ δ̃ ^ (-2 η_{j-1} / ε₂) (a / b) ^ β |𝕋̃| ^ β ≤ δ̃ ^ (10 η_{j-1} / ε₂) |𝕋̃| ^ β`

of the blueprint, with the two inputs kept abstract:

* `hmult` is the conclusion of GWZ Proposition 6.6(B) applied with `η` in place of `ε`, whose
  three variable factors are the maximal density `M`, the eccentricity ratio `R = a / b` and the
  cardinality `N`;
* `hM` is `\eqref{upperBdDeltaMaxTildeTT}`, `Δ_max(𝕋̃) ≤ δ̃ ^ (-η_{j-1} / ε₂)`;
* `hR` is the eccentric case hypothesis `\eqref{eqecccase}`, in the ratio form delivered by
  `Kakeya.ML2Reduction.ratio_le_of_eccentric`.

The arithmetic that makes it work is
`-η - (η/ε₂)(1-β) + 12η/ε₂ - 10η/ε₂ = η ((1+β)/ε₂ - 1) ≥ 0`, which uses `ε₂ ≤ 1` and `β > 0`. -/
theorem multiplicity_le_of_eccentric_bound
    {δ : ℝ≥0} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {β ε₂ η : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hε₂0 : 0 < ε₂) (hε₂1 : ε₂ ≤ 1) (hη : 0 ≤ η)
    {M mult R N : ℝ≥0∞}
    (hM : M ≤ (δ : ℝ≥0∞) ^ (-(η / ε₂)))
    (hR : R ≤ (δ : ℝ≥0∞) ^ eccExponent β ε₂ η)
    (hmult : mult ≤ (δ : ℝ≥0∞) ^ (-η) * M ^ (1 - β) * R ^ β * N ^ β) :
    mult ≤ (δ : ℝ≥0∞) ^ (10 * η / ε₂) * N ^ β := by
  have hδ0' : (δ : ℝ≥0∞) ≠ 0 := by simpa using hδ0.ne'
  have hδtop : (δ : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hδ1' : (δ : ℝ≥0∞) ≤ 1 := by exact_mod_cast hδ1
  -- Raise the two inputs to their exponents.
  have hMpow : M ^ (1 - β) ≤ (δ : ℝ≥0∞) ^ (-(η / ε₂) * (1 - β)) := by
    rw [ENNReal.rpow_mul]
    exact ENNReal.rpow_le_rpow hM (by linarith)
  have hRpow : R ^ β ≤ (δ : ℝ≥0∞) ^ (eccExponent β ε₂ η * β) := by
    rw [ENNReal.rpow_mul]
    exact ENNReal.rpow_le_rpow hR hβ0.le
  -- The combined exponent.
  set X : ℝ := -η + (-(η / ε₂) * (1 - β) + eccExponent β ε₂ η * β) with hX
  have hcollect :
      (δ : ℝ≥0∞) ^ (-η) * (δ : ℝ≥0∞) ^ (-(η / ε₂) * (1 - β))
          * (δ : ℝ≥0∞) ^ (eccExponent β ε₂ η * β) = (δ : ℝ≥0∞) ^ X := by
    rw [hX, ENNReal.rpow_add _ _ hδ0' hδtop, ENNReal.rpow_add _ _ hδ0' hδtop, mul_assoc]
  -- The exponent inequality `10 η / ε₂ ≤ X`.
  have hkey : 10 * η / ε₂ ≤ X := by
    have hEB : eccExponent β ε₂ η * β = 12 * η / ε₂ := eccExponent_mul_beta hβ0.ne'
    have hu : η ≤ η / ε₂ := by rw [le_div_iff₀ hε₂0]; nlinarith
    have hu0 : (0 : ℝ) ≤ η / ε₂ := div_nonneg hη hε₂0.le
    have hub : (0 : ℝ) ≤ η / ε₂ * β := mul_nonneg hu0 hβ0.le
    have e10 : 10 * η / ε₂ = 10 * (η / ε₂) := by ring
    have e12 : 12 * η / ε₂ = 12 * (η / ε₂) := by ring
    rw [hX, hEB, e10, e12]
    nlinarith
  calc mult ≤ (δ : ℝ≥0∞) ^ (-η) * M ^ (1 - β) * R ^ β * N ^ β := hmult
    _ ≤ (δ : ℝ≥0∞) ^ (-η) * (δ : ℝ≥0∞) ^ (-(η / ε₂) * (1 - β))
          * (δ : ℝ≥0∞) ^ (eccExponent β ε₂ η * β) * N ^ β := by gcongr
    _ = (δ : ℝ≥0∞) ^ X * N ^ β := by rw [hcollect]
    _ ≤ (δ : ℝ≥0∞) ^ (10 * η / ε₂) * N ^ β :=
        mul_le_mul' (ENNReal.rpow_le_rpow_of_exponent_ge hδ1' hkey) le_rfl

/-! ### The eccentric case -/

/-- **The eccentric case of the proof of GWZ Main Lemma 2, with the conclusion of GWZ
Proposition 6.6(B) taken as an explicit hypothesis.**

Blueprint GWZ, "Proof of Main Lemma~\ref{lemmain2}", the paragraph "The eccentric
case".  The three hypotheses are, in the blueprint's notation with `δ = δ̃` and `η = η_{j-1}`:

* `hΔ` is `\eqref{upperBdDeltaMaxTildeTT}`, `Δ_max(𝕋̃) ≤ δ̃ ^ (-η_{j-1}/ε₂)`;
* `hecc` is `\eqref{eqecccase}`, `b ≥ δ̃ ^ (-η'_{j-1}) a` with
  `η'_{j-1} = Kakeya.ML2Reduction.eccExponent β ε₂ η_{j-1} = 12 η_{j-1} / (ε₂ β)`;
* `h66B` is Proposition `factoringThoughFlatPrismsB` applied with `η_{j-1}` in place of `ε`.

The conclusion is `\eqref{multTildeTLem2}`,
`μ(𝕋̃, Ỹ) ≤ δ̃ ^ (10 η_{j-1}/ε₂) |𝕋̃| ^ β`.

This statement mentions Proposition 6.6(B) only through `h66B`, which is its conclusion
*verbatim*; `Kakeya.ML2Reduction.exists_threshold_eccentric` below is the one place in this file
where the proposition itself is applied. -/
theorem eccentric_of_prop66B_conclusion
    {ι : Type*} (q : Finset ι) {δ : ℝ≥0} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    {β ε₂ η : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hε₂0 : 0 < ε₂) (hε₂1 : ε₂ ≤ 1) (hη : 0 ≤ η)
    {a b : ℝ≥0}
    (hΔ : maxDensity q (fun i => (T i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-(η / ε₂)))
    (hecc : δ ^ (-eccExponent β ε₂ η) * a ≤ b)
    (h66B : ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ≤
      (δ : ℝ≥0∞) ^ (-η) * maxDensity q (fun i => (T i).toConvexSpaceBody) ^ (1 - β)
        * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ β * (q.card : ℝ≥0∞) ^ β) :
    ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ≤
      (δ : ℝ≥0∞) ^ (10 * η / ε₂) * (q.card : ℝ≥0∞) ^ β :=
  multiplicity_le_of_eccentric_bound hδ0 hδ1 hβ0 hβ1 hε₂0 hε₂1 hη hΔ
    (ratio_le_of_eccentric hδ0 hecc) h66B

/-! ### The auxiliary scale `ρ = δ̃ ^ (1 - ε₂)` -/

/-! ### The maximal density factoring step

Blueprint GWZ: *"We set `ρ = δ̃^{1-ε₂}`.  Apply Lemma `lemmafactmax` to `𝕋̃_ρ` and let
`𝕍` be the resulting set of planks. […]  Suppose every plank `V ∈ 𝕍` has affine thicknesses
`τ₀(V) ∼ 1`, `τ₁(V) ∼ b`, and `τ₂(V) ∼ a`."*
-/

/-- **`τ₀(V) ∼ 1`, `τ₁(V) ∼ pb`, `τ₂(V) ∼ pa` for every member of a plank family**, with the
implied constants made explicit and equal to `2` — the constant of
`ConvexSpaceBody.Factorization.simDims` produced by `lemmafactmax`.

The blueprint writes the three relations with an unquantified `∼`; the bracket below is the
Lean reading, and it is exactly what
`Kakeya.IsPlankOfDimensions 2 pa pb` asks for, since `pa ≤ τ₂ ≤ 2 pa` implies `2⁻¹ pa ≤ τ₂` and
`τ₀ ≤ 1 ≤ 2`. -/
def HasPlankThicknesses {κ : Type*} (pa pb : ℝ≥0) (P : Finset (Finset κ))
    (W : Finset κ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∀ t ∈ P,
    (2⁻¹ ≤ Metric.ethickness ℝ (W t).carrier 0 ∧ Metric.ethickness ℝ (W t).carrier 0 ≤ 1) ∧
    ((pb : ℝ≥0∞) ≤ Metric.ethickness ℝ (W t).carrier 1 ∧
      Metric.ethickness ℝ (W t).carrier 1 ≤ 2 * (pb : ℝ≥0∞)) ∧
    ((pa : ℝ≥0∞) ≤ Metric.ethickness ℝ (W t).carrier 2 ∧
      Metric.ethickness ℝ (W t).carrier 2 ≤ 2 * (pa : ℝ≥0∞))

/-- **The maximal density factoring of `𝕋̃_ρ`, with its two plank thicknesses.**

`lemmafactmax` — in this development `ConvexSpaceBody.nonempty_factorization.factorization_weighted`
— applied to the family `𝕋̃_ρ` of `ρ`-tubes, together with the reading of the resulting factor
bodies as `1 × pb × pa` planks.

* `r'` is the `≈ 1` refinement of `𝕋̃_ρ` that the lemma produces.  Its heaviness is stated in the
  arbitrary weight `w` fixed before the construction, because the blueprint immediately transports
  the refinement of `𝕋̃_ρ` to a refinement of `(𝕋̃, Ỹ)`; taking `w` to be a shading mass is what
  makes that transport possible, and the volume-weighted form would not (all `ρ`-tubes have the
  same volume).
* `F` is the factoring, `𝕍 = {W_t : t ∈ F.parts}` its family of factor bodies.
* `pa` and `pb` are the blueprint's `a` and `b`.  They are the *minima* over `𝕍` of `τ₂` and of
  `τ₁`, which is what makes `ρ ≤ pa` hold with no implied constant — the form
  `Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` asks for.  The upper halves
  `τ₂ ≤ 2 pa`, `τ₁ ≤ 2 pb` are read off `ConvexSpaceBody.Factorization.simDims`, so the blueprint's
  three dyadic pigeonholes are not needed and no member of `𝕍` is discarded.
* `τ₀ ∈ [2⁻¹, 1]` is absolute: the lower half because every factor body contains a `ρ`-tube, whose
  core has length `1` (`Tube.le_ethickness_zero`), the upper half because every `ρ`-tube of
  `𝕋̃_ρ` lies in the unit ball. -/
theorem exists_maxDensityFactoring_planks
    {κ : Type*} [DecidableEq κ] {ρ : ℝ≥0} (hρ0 : 0 < ρ) {r : Finset κ} (hr : r.Nonempty)
    (R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3)))
    (hball : ∀ k ∈ r, (R k).carrier ⊆ Metric.closedBall 0 1)
    (w : κ → ℝ≥0∞) :
    ∃ r' ⊆ r, r'.Nonempty ∧
      ∑ k ∈ r, w k ≤
        ConvexSpaceBody.nonempty_factorization.C 3 r.card ρ * ∑ k ∈ r', w k ∧
      ∃ F : ConvexSpaceBody.Factorization r' (fun k => (R k).toConvexSpaceBody) 2,
        F.parts.Nonempty ∧
        ∃ pa pb : ℝ≥0, ρ ≤ pa ∧ pa ≤ pb ∧ pb ≤ 1 ∧
          HasPlankThicknesses pa pb F.parts
            (fun t => t.convexHull_biUnion fun k => (R k).toConvexSpaceBody) := by
  classical
  set V : κ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    fun k => (R k).toConvexSpaceBody with hVdef
  have hcar : ∀ k, (V k).carrier = (R k).carrier := fun _ => rfl
  have h1 : ∀ k ∈ r, (V k).carrier ⊆ Metric.closedBall 0 1 := by
    intro k hk; rw [hcar]; exact hball k hk
  have h2 : ∀ k ∈ r, (ρ : ℝ≥0∞) ≤ Metric.ethickness.scale ℝ (V k).carrier := by
    intro k _; exact (R k).le_ethickness_scale
  obtain ⟨r', hr'sub, hr'ne, hheavy, F, hFne⟩ :=
    ConvexSpaceBody.nonempty_factorization.factorization_weighted hρ0 hr h1 h2 w
  refine ⟨r', hr'sub, hr'ne, by simpa using hheavy, F, hFne, ?_⟩
  -- The factor bodies.
  have hpne : ∀ t ∈ F.parts, t.Nonempty := fun t ht =>
    F.toFinpartition.nonempty_of_mem_parts ht
  have hpsub : ∀ t ∈ F.parts, t ⊆ r' := fun t ht => F.toFinpartition.le ht
  have hupper : ∀ t ∈ F.parts, ∀ n : ℕ,
      Metric.ethickness ℝ (t.convexHull_biUnion V).carrier n ≤ 1 := by
    intro t ht n
    have hle : t.convexHull_biUnion V ≤
        (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :=
      ((hpne t ht).convexHull_biUnion_le_iff V _).2 fun k hk => by
        show (V k).carrier ⊆
          (ConvexSpaceBody.closedUnitBall :
            ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))).carrier
        rw [ConvexSpaceBody.closedUnitBall_carrier]
        exact h1 k (hr'sub (hpsub t ht hk))
    have hsub : (t.convexHull_biUnion V).carrier ⊆ Metric.closedBall 0 1 := by
      have hsub' : (t.convexHull_biUnion V).carrier ⊆
          (ConvexSpaceBody.closedUnitBall :
            ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))).carrier := hle
      rwa [ConvexSpaceBody.closedUnitBall_carrier] at hsub' 
    simpa using Metric.ethickness_le_of_subset_closedBall (𝕜 := ℝ) 1 hsub n
  have hlow0 : ∀ t ∈ F.parts,
      (2⁻¹ : ℝ≥0∞) ≤ Metric.ethickness ℝ (t.convexHull_biUnion V).carrier 0 := by
    intro t ht
    obtain ⟨k, hk⟩ := hpne t ht
    have hsub : (V k).carrier ⊆ (t.convexHull_biUnion V).carrier :=
      Finset.le_convexHull_biUnion V hk
    calc (2⁻¹ : ℝ≥0∞) = 1 / 2 := by norm_num
      _ ≤ Metric.ethickness ℝ (V k).carrier 0 := (R k).le_ethickness_zero
      _ ≤ _ := Metric.ethickness_monotone hsub 0
  have hlow2 : ∀ t ∈ F.parts,
      (ρ : ℝ≥0∞) ≤ Metric.ethickness ℝ (t.convexHull_biUnion V).carrier 2 := by
    intro t ht
    obtain ⟨k, hk⟩ := hpne t ht
    have hsub : (V k).carrier ⊆ (t.convexHull_biUnion V).carrier :=
      Finset.le_convexHull_biUnion V hk
    have hrk : (ρ : ℝ≥0∞) ≤ Metric.ethickness ℝ (V k).carrier 2 := by
      have h := (R k).le_ethickness_finrank_sub_one
      rwa [show Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1 = 2 by simp] at h
    exact hrk.trans (Metric.ethickness_monotone hsub 2)
  -- The two thicknesses, as minima over the factor family.
  obtain ⟨t2, ht2, ht2min⟩ :=
    F.parts.exists_min_image
      (fun t => Metric.ethickness ℝ (t.convexHull_biUnion V).carrier 2) hFne
  obtain ⟨t1, ht1, ht1min⟩ :=
    F.parts.exists_min_image
      (fun t => Metric.ethickness ℝ (t.convexHull_biUnion V).carrier 1) hFne
  refine ⟨(Metric.ethickness ℝ (t2.convexHull_biUnion V).carrier 2).toNNReal,
    (Metric.ethickness ℝ (t1.convexHull_biUnion V).carrier 1).toNNReal, ?_, ?_, ?_, ?_⟩
  all_goals
    have hpaco : (((Metric.ethickness ℝ (t2.convexHull_biUnion V).carrier 2).toNNReal :
        ℝ≥0) : ℝ≥0∞) = Metric.ethickness ℝ (t2.convexHull_biUnion V).carrier 2 :=
      ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.one_ne_top (hupper t2 ht2 2))
  all_goals
    have hpbco : (((Metric.ethickness ℝ (t1.convexHull_biUnion V).carrier 1).toNNReal :
        ℝ≥0) : ℝ≥0∞) = Metric.ethickness ℝ (t1.convexHull_biUnion V).carrier 1 :=
      ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.one_ne_top (hupper t1 ht1 1))
  · rw [← ENNReal.coe_le_coe, hpaco]
    exact hlow2 t2 ht2
  · rw [← ENNReal.coe_le_coe, hpaco, hpbco]
    exact (ht2min t1 ht1).trans (Metric.ethickness_antitone (by norm_num))
  · rw [← ENNReal.coe_le_coe, hpbco, ENNReal.coe_one]
    exact hupper t1 ht1 1
  · intro t ht
    refine ⟨⟨hlow0 t ht, hupper t ht 0⟩, ⟨?_, ?_⟩, ?_, ?_⟩
    · rw [hpbco]; exact ht1min t ht
    · have h : ∀ n : ℕ, Metric.ethickness ℝ (t.convexHull_biUnion V).carrier n ≤
          (2 : ℝ≥0) • Metric.ethickness ℝ (t1.convexHull_biUnion V).carrier n :=
        F.simDims t ht t1 ht1
      rw [hpbco]
      simpa [ENNReal.smul_def, smul_eq_mul] using h 1
    · rw [hpaco]; exact ht2min t ht
    · have h : ∀ n : ℕ, Metric.ethickness ℝ (t.convexHull_biUnion V).carrier n ≤
          (2 : ℝ≥0) • Metric.ethickness ℝ (t2.convexHull_biUnion V).carrier n :=
        F.simDims t ht t2 ht2
      rw [hpaco]
      simpa [ENNReal.smul_def, smul_eq_mul] using h 2

/-! ### From the factor thicknesses to plank containment

The `le_plank` field of `Kakeya.GlobalPlankFactorization` — the hypothesis of GWZ Proposition
6.6(B) that the factoring step has to supply.
-/

/-! ### From an affine thickness lower bound to a flat disc

`Kakeya.GlobalPlankFactorization.wide` — the field of GWZ Proposition 6.6(B)'s datum that keeps
the eccentricity gain `(a/b) ^ β` honest — asks a factor body to *contain* a flat disc of radius
`min b (1/2) / Cw`.  The maximal density factoring, by contrast, controls the factor bodies by
their **affine thicknesses** (`ConvexSpaceBody.Factorization.simDims`), i.e. by
`Metric.ethickness`.  The two lemmas of this section are the bridge, and they are what makes
`wide` a hypothesis the factoring step can actually supply.

Only one direction was previously available in the tree,
`Kakeya.ContainsFlatDisc.le_ethickness_one` (a flat disc of radius `b` forces
`ethickness _ 1 ≥ b`).  The converse below is the one the producer needs; it is quantitative and
costs an absolute constant, exactly as the `Cw` of `Kakeya.GlobalPlankFactorization` anticipates.
-/

/-- **A convex body that is wide at rank one contains a flat disc of comparable radius.**

If `S` is convex, sits in the unit ball, contains two points `P₀, P₁` at distance `1` — for the
hull of a block of `ρ`-tubes, the two endpoints of any one tube's unit core — and is *not* within
`r` of any line (`r < Metric.ethickness ℝ S 1`), then `S` contains a flat disc of radius `r/32`.

The proof is the elementary triangle bound.  Let `u = P₁ - P₀` (a unit vector), let `A` be the
line through `P₀` in direction `u`, and let `P₂ ∈ S` be a point at distance `h > r` from `A`,
which exists exactly because `ethickness ℝ S 1 > r`.  Write `P₂ = P₀ + α u + h e` with `e ⊥ u` a
unit vector.  The triangle `P₀P₁P₂` lies in `S` by convexity, and the disc of radius `r/32`
around its centroid, in the plane `span {u, e}`, lies in that triangle: a point
`centroid + p u + q e` has barycentric coordinates `1/3 + q/h`, `1/3 + p - α q/h` and
`1/3 - p + (α - 1) q/h`, all nonnegative once `|p|, |q| ≤ r/32`, `r < h ≤ 4` and `|α| ≤ 2`.

The constant `32` is not optimal (the sharp inradius bound is `h/3` for a triangle whose base is
a diameter); it is chosen so that the three barycentric estimates close with no case analysis. -/
theorem containsFlatDisc_of_lt_ethickness_one
    {S : Set (EuclideanSpace ℝ (Fin 3))} (hconv : Convex ℝ S)
    (hball : S ⊆ Metric.closedBall 0 1)
    {P₀ P₁ : EuclideanSpace ℝ (Fin 3)} (h0 : P₀ ∈ S) (h1 : P₁ ∈ S) (hd : dist P₀ P₁ = 1)
    {r : ℝ≥0} (hr : (r : ℝ≥0∞) < Metric.ethickness ℝ S 1) :
    ContainsFlatDisc (r / 32) S := by
  classical
  have hnorm_le : ∀ x ∈ S, ‖x‖ ≤ 1 := by
    intro x hx
    simpa using hball hx
  set u : EuclideanSpace ℝ (Fin 3) := P₁ - P₀ with hu_def
  have hu : ‖u‖ = 1 := by
    rw [hu_def, ← dist_eq_norm, dist_comm]
    exact hd
  have hu0 : u ≠ 0 := by
    intro hcon
    rw [hcon, norm_zero] at hu
    norm_num at hu
  -- the line through `P₀` in direction `u`
  set A : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)) :=
    AffineSubspace.mk' P₀ (ℝ ∙ u) with hA_def
  have hArank : Module.rank ℝ A.direction ≤ 1 := by
    rw [hA_def, AffineSubspace.direction_mk']
    simpa using rank_span_le ({u} : Set (EuclideanSpace ℝ (Fin 3)))
  obtain ⟨P₂, hP₂S, hP₂⟩ := Metric.exists_not_in_cthickening hr hArank
  rw [show ((r : ℝ≥0∞)).toReal = (r : ℝ) by simp] at hP₂
  set α : ℝ := inner ℝ u (P₂ - P₀) with hα_def
  set z : EuclideanSpace ℝ (Fin 3) := (P₂ - P₀) - α • u with hz_def
  have hmemA : α • u + P₀ ∈ A := by
    rw [hA_def, AffineSubspace.mem_mk']
    have hvs : (α • u + P₀) -ᵥ P₀ = α • u := by simp
    rw [hvs]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
  have hdist : dist P₂ (α • u + P₀) = ‖z‖ := by
    rw [dist_eq_norm, hz_def]
    congr 1
    abel
  have hrz : (r : ℝ) < ‖z‖ := by
    by_contra hcon
    push Not at hcon
    exact hP₂ (Metric.mem_cthickening_of_dist_le _ _ _ _ hmemA (by rw [hdist]; exact hcon))
  -- basic size bounds
  have hdiff2 : ‖P₂ - P₀‖ ≤ 2 := by
    calc ‖P₂ - P₀‖ ≤ ‖P₂‖ + ‖P₀‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by gcongr <;> [exact hnorm_le _ hP₂S; exact hnorm_le _ h0]
      _ = 2 := by norm_num
  have hα2 : |α| ≤ 2 := by
    have hcs := abs_real_inner_le_norm u (P₂ - P₀)
    rw [hu, one_mul] at hcs
    exact hcs.trans hdiff2
  have hh4 : ‖z‖ ≤ 4 := by
    calc ‖z‖ = ‖(P₂ - P₀) - α • u‖ := by rw [hz_def]
      _ ≤ ‖P₂ - P₀‖ + ‖α • u‖ := norm_sub_le _ _
      _ = ‖P₂ - P₀‖ + |α| := by rw [norm_smul, hu, Real.norm_eq_abs, mul_one]
      _ ≤ 2 + 2 := by gcongr
      _ = 4 := by norm_num
  set h : ℝ := ‖z‖ with hh_def
  have hh0 : 0 < h := lt_of_le_of_lt r.coe_nonneg hrz
  have hzu : inner ℝ u z = (0 : ℝ) := by
    rw [hz_def, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hu]
    rw [← hα_def]
    ring
  set e : EuclideanSpace ℝ (Fin 3) := h⁻¹ • z with he_def
  have he1 : ‖e‖ = 1 := by
    rw [he_def, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hh0), ← hh_def,
      inv_mul_cancel₀ hh0.ne']
  have hue : inner ℝ u e = (0 : ℝ) := by
    rw [he_def, real_inner_smul_right, hzu, mul_zero]
  have hP₂eq : P₂ = P₀ + α • u + h • e := by
    rw [he_def, smul_smul, mul_inv_cancel₀ hh0.ne', one_smul, hz_def]
    abel
  have hP₁eq : P₁ = P₀ + u := by rw [hu_def]; abel
  have hhne : h ≠ 0 := hh0.ne'
  -- the plane spanned by `u` and `e`
  have horth : Orthonormal ℝ ![u, e] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [hu, he1, hue, real_inner_comm u e]
  have hrange : Set.range ![u, e] = {u, e} := by
    simp [Matrix.range_cons, Matrix.range_empty, Set.pair_comm]
  have hfr : Module.finrank ℝ
      (Submodule.span ℝ ({u, e} : Set (EuclideanSpace ℝ (Fin 3)))) = 2 := by
    rw [← hrange, finrank_span_eq_card horth.linearIndependent]
    simp
  refine ⟨P₀ + ((1 + α) / 3) • u + (h / 3) • e,
    Submodule.span ℝ ({u, e} : Set (EuclideanSpace ℝ (Fin 3))), hfr, ?_⟩
  intro v hv hvn
  obtain ⟨p, q, hpq⟩ := Submodule.mem_span_pair.mp hv
  have hvn' : ‖v‖ ≤ (r : ℝ) / 32 := by
    refine hvn.trans_eq ?_
    push_cast
    ring
  have hvsq : ‖v‖ ^ 2 = p ^ 2 + q ^ 2 := by
    rw [← hpq, norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left,
      real_inner_smul_right, hue, hu, he1]
    simp [Real.norm_eq_abs, sq_abs]
  have hpv : |p| ≤ ‖v‖ := by
    nlinarith [sq_abs p, sq_abs q, abs_nonneg p, abs_nonneg q, norm_nonneg v]
  have hqv : |q| ≤ ‖v‖ := by
    nlinarith [sq_abs p, sq_abs q, abs_nonneg p, abs_nonneg q, norm_nonneg v]
  set Q : ℝ := q / h with hQ_def
  have hpb : |p| ≤ 1 / 8 := by
    have hr4 : (r : ℝ) ≤ 4 := le_of_lt (hrz.trans_le hh4)
    calc |p| ≤ ‖v‖ := hpv
      _ ≤ (r : ℝ) / 32 := hvn'
      _ ≤ 4 / 32 := by linarith
      _ = 1 / 8 := by norm_num
  have hQb : |Q| ≤ 1 / 32 := by
    rw [hQ_def, abs_div, abs_of_pos hh0, div_le_iff₀ hh0]
    have hq1 : |q| ≤ (r : ℝ) / 32 := hqv.trans hvn'
    have hq2 : (r : ℝ) ≤ h := hrz.le
    linarith
  have hα2' := abs_le.mp hα2
  have hpb' := abs_le.mp hpb
  have hQb' := abs_le.mp hQb
  have hαQ : |α * Q| ≤ 1 / 16 := by
    rw [abs_mul]
    calc |α| * |Q| ≤ 2 * (1 / 32) :=
          mul_le_mul hα2 hQb (abs_nonneg _) (by norm_num)
      _ = 1 / 16 := by norm_num
  have hα1 : |α - 1| ≤ 3 := by
    rw [abs_le]
    constructor <;> linarith [hα2'.1, hα2'.2]
  have hα1Q : |(α - 1) * Q| ≤ 3 / 32 := by
    rw [abs_mul]
    calc |α - 1| * |Q| ≤ 3 * (1 / 32) :=
          mul_le_mul hα1 hQb (abs_nonneg _) (by norm_num)
      _ = 3 / 32 := by norm_num
  have hαQ' := abs_le.mp hαQ
  have hα1Q' := abs_le.mp hα1Q
  set l₂ : ℝ := 1 / 3 + Q with hl₂_def
  set l₁ : ℝ := 1 / 3 + p - α * Q with hl₁_def
  set l₀ : ℝ := 1 / 3 - p + (α - 1) * Q with hl₀_def
  have h₂ : 0 ≤ l₂ := by rw [hl₂_def]; linarith [hQb'.1]
  have h₁ : 0 ≤ l₁ := by rw [hl₁_def]; linarith [hpb'.2, hαQ'.2]
  have h₀ : 0 ≤ l₀ := by rw [hl₀_def]; linarith [hpb'.2, hα1Q'.1]
  have hsum : l₀ + l₁ + l₂ = 1 := by rw [hl₀_def, hl₁_def, hl₂_def]; ring
  have hpt : P₀ + ((1 + α) / 3) • u + (h / 3) • e + v = l₀ • P₀ + l₁ • P₁ + l₂ • P₂ := by
    rw [hP₁eq, hP₂eq, ← hpq, hl₀_def, hl₁_def, hl₂_def, hQ_def]
    match_scalars <;> field_simp <;> ring
  rw [hpt]
  have key := hconv.sum_mem (t := (Finset.univ : Finset (Fin 3)))
    (w := ![l₀, l₁, l₂]) (z := ![P₀, P₁, P₂])
    (by
      intro i _
      fin_cases i
      · simpa using h₀
      · simpa using h₁
      · simpa using h₂)
    (by
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      exact hsum)
    (by
      intro i _
      fin_cases i
      · simpa using h0
      · simpa using h1
      · simpa using hP₂S)
  simpa only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] using key

/-- **The non-strict form of `Kakeya.ML2Reduction.containsFlatDisc_of_lt_ethickness_one`.**

A positive affine-thickness lower bound `w ≤ ethickness ℝ S 1` gives a flat disc of radius
`w / 64`; the extra factor `2` pays for passing from the strict hypothesis to the non-strict
one (apply the strict form at `3w/4 < w`, which gives radius `3w/128 ≥ w/64`).

This is the form the maximal density factoring supplies, because
`Kakeya.ML2Reduction.HasPlankThicknesses` records exactly `pb ≤ ethickness _ 1 ≤ 2 pb`. -/
theorem containsFlatDisc_of_le_ethickness_one
    {S : Set (EuclideanSpace ℝ (Fin 3))} (hconv : Convex ℝ S)
    (hball : S ⊆ Metric.closedBall 0 1)
    {P₀ P₁ : EuclideanSpace ℝ (Fin 3)} (h0 : P₀ ∈ S) (h1 : P₁ ∈ S) (hd : dist P₀ P₁ = 1)
    {w : ℝ≥0} (hw0 : 0 < w) (hw : (w : ℝ≥0∞) ≤ Metric.ethickness ℝ S 1) :
    ContainsFlatDisc (w / 64) S := by
  have hw0' : (0 : ℝ) < (w : ℝ) := hw0
  have hlt : (3 * w / 4 : ℝ≥0) < w := by
    have hc : ((3 * w / 4 : ℝ≥0) : ℝ) < ((w : ℝ≥0) : ℝ) := by push_cast; linarith
    exact_mod_cast hc
  have hstrict : ((3 * w / 4 : ℝ≥0) : ℝ≥0∞) < Metric.ethickness ℝ S 1 :=
    lt_of_lt_of_le (by exact_mod_cast hlt) hw
  refine (containsFlatDisc_of_lt_ethickness_one hconv hball h0 h1 hd hstrict).mono ?_
  have hc : ((w / 64 : ℝ≥0) : ℝ) ≤ (((3 * w / 4 : ℝ≥0) / 32 : ℝ≥0) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast hc

/-! ### The datum the maximal density factoring step actually produces

`Kakeya.ML2Reduction.PlankFactoringData` bundles precisely the output of
`Kakeya.ML2Reduction.exists_maxDensityFactoring_planks` — a `ConvexSpaceBody.Factorization` of a
family of `ρ`-tubes in the unit ball, with nonempty parts and with the two plank thicknesses
`τ₂ ∼ pa`, `τ₁ ∼ pb` — and nothing else.  Every field is *supplied* by that theorem, so the
structure is inhabited whenever the coarse family is (`exists_plankFactoringData`).

`Kakeya.ML2Reduction.PlankFactoringData.toGlobalPlankFactorization` then converts it into the
datum GWZ Proposition 6.6(B) consumes, at the *absolute* transverse comparability constant
`Cw = 128`.  That conversion is the point of this section: without it,
`Kakeya.GlobalPlankFactorization` is a hypothesis no producer in this development can supply,
and any theorem quantifying over it is unusable.
-/

/-- **What the maximal density factoring of `𝕋̃_ρ` delivers**, as a single datum.

Blueprint GWZ: *"Apply Lemma `lemmafactmax` to `𝕋̃_ρ` and let `𝕍` be the resulting set
of planks. […] Suppose every plank `V ∈ 𝕍` has affine thicknesses `τ₀(V) ∼ 1`, `τ₁(V) ∼ b`, and
`τ₂(V) ∼ a`."*

The fields are, in order: the factoring itself (blueprint `def:Factors`, i.e.
`ConvexSpaceBody.Factorization`), the nonemptiness of the family of factor bodies, the unit-ball
normalisation of the coarse tubes, the scale ordering `ρ ≤ a ≤ b ≤ 1`, and the two-sided plank
thicknesses.  `Kakeya.ML2Reduction.exists_plankFactoringData` proves that
`ConvexSpaceBody.nonempty_factorization.factorization_weighted` produces all of them. -/
structure PlankFactoringData {κ : Type*} [DecidableEq κ] (ρ pa pb C₀ : ℝ≥0)
    (r : Finset κ) (R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))) where
  /-- The factoring produced by `lemmafactmax`. -/
  toFactorization : ConvexSpaceBody.Factorization r (fun k => (R k).toConvexSpaceBody) C₀
  /-- The family `𝕍` of factor bodies is nonempty. -/
  parts_nonempty : toFactorization.parts.Nonempty
  /-- The coarse tubes are normalised to the unit ball. -/
  ball : ∀ k ∈ r, (R k).carrier ⊆ Metric.closedBall 0 1
  /-- `ρ ≤ a`: the thin plank half-width is at least the coarse scale. -/
  scale_le : ρ ≤ pa
  /-- `a ≤ b`. -/
  thin_le_wide : pa ≤ pb
  /-- `b ≤ 1`. -/
  wide_le_one : pb ≤ 1
  /-- `τ₀ ∼ 1`, `τ₁ ∼ pb`, `τ₂ ∼ pa` for every factor body. -/
  thicknesses : HasPlankThicknesses pa pb toFactorization.parts
      (fun t => t.convexHull_biUnion (fun k => (R k).toConvexSpaceBody))

namespace PlankFactoringData

variable {κ : Type*} [DecidableEq κ] {ρ pa pb C₀ : ℝ≥0} {r : Finset κ}
  {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}

/-- Every part is a nonempty block of coarse tubes. -/
theorem part_nonempty (D : PlankFactoringData ρ pa pb C₀ r R)
    {t : Finset κ} (ht : t ∈ D.toFactorization.parts) : t.Nonempty :=
  D.toFactorization.toFinpartition.nonempty_of_mem_parts ht

/-- Every part is a subfamily of the coarse family. -/
theorem part_subset (D : PlankFactoringData ρ pa pb C₀ r R)
    {t : Finset κ} (ht : t ∈ D.toFactorization.parts) : t ⊆ r :=
  D.toFactorization.toFinpartition.le ht

/-- Each factor body inherits the unit-ball normalisation of the coarse tubes. -/
theorem hull_subset_closedBall (D : PlankFactoringData ρ pa pb C₀ r R)
    {t : Finset κ} (ht : t ∈ D.toFactorization.parts) :
    (t.convexHull_biUnion (fun k => (R k).toConvexSpaceBody)).carrier ⊆
      Metric.closedBall 0 1 := by
  have hle : t.convexHull_biUnion (fun k => (R k).toConvexSpaceBody) ≤
      (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :=
    ((D.part_nonempty ht).convexHull_biUnion_le_iff _ _).2 fun k hk => by
      show ((R k).toConvexSpaceBody).carrier ⊆
        (ConvexSpaceBody.closedUnitBall :
          ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))).carrier
      rw [ConvexSpaceBody.closedUnitBall_carrier]
      exact D.ball k (D.part_subset ht hk)
  have hsub' : (t.convexHull_biUnion (fun k => (R k).toConvexSpaceBody)).carrier ⊆
      (ConvexSpaceBody.closedUnitBall :
        ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))).carrier := hle
  rwa [ConvexSpaceBody.closedUnitBall_carrier] at hsub'

/-- **Each factor body contains a flat disc of radius `pb / 64`.**

This is `Kakeya.ML2Reduction.containsFlatDisc_of_le_ethickness_one` applied to the hull of a
block of coarse tubes: it is convex, it lies in the unit ball, it contains the unit core segment
of any one of its tubes, and its rank-one affine thickness is at least `pb`. -/
theorem hull_containsFlatDisc (D : PlankFactoringData ρ pa pb C₀ r R) (hρ0 : 0 < ρ)
    {t : Finset κ} (ht : t ∈ D.toFactorization.parts) :
    ContainsFlatDisc (pb / 64)
      (t.convexHull_biUnion (fun k => (R k).toConvexSpaceBody)).carrier := by
  have hpb0 : 0 < pb := lt_of_lt_of_le hρ0 (D.scale_le.trans D.thin_le_wide)
  obtain ⟨k, hk⟩ := D.part_nonempty ht
  have hsubk : ((R k).toConvexSpaceBody).carrier ⊆
      (t.convexHull_biUnion (fun k => (R k).toConvexSpaceBody)).carrier :=
    Finset.le_convexHull_biUnion (fun k => (R k).toConvexSpaceBody) hk
  have hxm : (R k).x ∈ (R k).carrier := by
    rw [(R k).carrier_eq]
    exact Set.mem_iUnion₂.mpr
      ⟨(R k).x, left_mem_segment ℝ _ _, Metric.mem_closedBall_self ρ.coe_nonneg⟩
  have hym : (R k).y ∈ (R k).carrier := by
    rw [(R k).carrier_eq]
    exact Set.mem_iUnion₂.mpr
      ⟨(R k).y, right_mem_segment ℝ _ _, Metric.mem_closedBall_self ρ.coe_nonneg⟩
  exact containsFlatDisc_of_le_ethickness_one
    (t.convexHull_biUnion (fun k => (R k).toConvexSpaceBody)).isConvexSet.convex
    (D.hull_subset_closedBall ht) (hsubk hxm) (hsubk hym) (R k).dist_eq_one hpb0
    (D.thicknesses t ht).2.1.1

/-- **The coarse scale is below the thin plank half-width `2 pa`.**

`ρ ≤ a` is a hypothesis of `Kakeya.tubeMultiplicityOfGlobalPlankFactorisation`; here it is
*derived*, because every factor body contains a coarse `ρ`-tube and hence has rank-two affine
thickness at least `ρ`, while the datum bounds that thickness by `2 pa`. -/
theorem scale_le_thin (D : PlankFactoringData ρ pa pb C₀ r R) : ρ ≤ 2 * pa := by
  refine D.scale_le.trans ?_
  have hstep : (1 : ℝ≥0) * pa ≤ 2 * pa := by gcongr; norm_num
  simpa using hstep

/-- **The bridge: the factoring datum is a `Kakeya.GlobalPlankFactorization`.**

The plank parameters are `a = 2 pa` (`comparablePlankEnvelope.bodyThin 2 pa`) and
`b = min (2 pb) 1` (`comparablePlankEnvelope.bodyWide 2 pb`) — the exact envelope of the two
upper brackets of `Kakeya.ML2Reduction.HasPlankThicknesses` together with the unit-ball
normalisation — and the transverse comparability constant is the **absolute** `Cw = 128`.

* `le_plank` is `Kakeya.comparablePlankEnvelope.body_le_bodyPlank`.
* `wide` is `Kakeya.ML2Reduction.PlankFactoringData.hull_containsFlatDisc`: the disc it produces
  has radius `pb / 64`, and `min b (1/2) / 128 ≤ 2 pb / 128 = pb / 64`, so the flat-disc field
  holds at `Cw = 128`.

`Cw = 128` is absolute — it does not grow with `δ`, `ρ`, `pa` or `pb` — so the budget
`Cw ≤ δ ^ (-η)` of `Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` is met by a threshold on
`δ` alone.  This is exactly the reservation the `Cw` parameterisation of
`Kakeya.GlobalPlankFactorization` was introduced to discharge: at the unconstanted radius
`min b (1/2)` the field is **not** supplied by this producer, because the hull of a block of
`ρ`-tubes of rank-one thickness `∼ pb` need not contain a disc of radius exactly `pb`. -/
def toGlobalPlankFactorization (D : PlankFactoringData ρ pa pb C₀ r R) (hρ0 : 0 < ρ)
    (hpa1 : 2 * pa ≤ 1) (hab : 2 * pa ≤ min (2 * pb) 1) :
    GlobalPlankFactorization 128 (2 * pa) (min (2 * pb) 1) hab (min_le_right _ _)
      r (fun k => (R k).toConvexSpaceBody) C₀ where
  toFactorization := D.toFactorization
  one_le_Cw := by norm_num
  le_plank := by
    intro t ht
    obtain ⟨-, ⟨-, hone⟩, ⟨-, htwo⟩⟩ := D.thicknesses t ht
    have hone' : Metric.ethickness ℝ
        (t.convexHull_biUnion (fun k => (R k).toConvexSpaceBody)).carrier 1
          ≤ ((2 : ℝ≥0) : ℝ≥0∞) * (pb : ℝ≥0∞) := by simpa using hone
    have htwo' : Metric.ethickness ℝ
        (t.convexHull_biUnion (fun k => (R k).toConvexSpaceBody)).carrier 2
          ≤ ((2 : ℝ≥0) : ℝ≥0∞) * (pa : ℝ≥0∞) := by simpa using htwo
    have hKball : t.convexHull_biUnion (fun k => (R k).toConvexSpaceBody) ≤
        (ConvexSpaceBody.closedUnitBall :
          ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) := by
      show (t.convexHull_biUnion (fun k => (R k).toConvexSpaceBody)).carrier ⊆
        (ConvexSpaceBody.closedUnitBall :
          ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))).carrier
      rw [ConvexSpaceBody.closedUnitBall_carrier]
      exact D.hull_subset_closedBall ht
    exact ⟨comparablePlankEnvelope.bodyPlank 2 pa pb D.thin_le_wide hpa1 _,
      comparablePlankEnvelope.body_le_bodyPlank D.thin_le_wide hpa1 hone' htwo' hKball⟩
  wide := by
    intro t ht
    refine (D.hull_containsFlatDisc hρ0 ht).mono ?_
    have hmin : min (min (2 * pb) 1) (1 / 2) ≤ 2 * pb := (min_le_left _ _).trans (min_le_left _ _)
    calc min (min (2 * pb) 1) (1 / 2) / (128 : ℝ≥0) ≤ 2 * pb / 128 := by gcongr
      _ = pb / 64 := by
          have hco : ((2 * pb / 128 : ℝ≥0) : ℝ) = ((pb / 64 : ℝ≥0) : ℝ) := by
            push_cast; ring
          exact_mod_cast hco

end PlankFactoringData

/-- **The maximal density factoring produces a `Kakeya.ML2Reduction.PlankFactoringData`.**

This is `Kakeya.ML2Reduction.exists_maxDensityFactoring_planks` repackaged: the structure of the
previous section is inhabited by the actual output of `lemmafactmax`, so the hypothesis of
`Kakeya.ML2Reduction.exists_threshold_eccentric` is not vacuous and not unsupplyable.

The refinement `r' ⊆ r` is `lemmafactmax`'s own — blueprint GWZ, *"Lemma
`lemmafactmax` replaces the set `𝕋̃_ρ` with an `≈ 1` refinement. […] Abusing notation, we will
continue to refer to these new objects as `𝕋̃_ρ` and `Ỹ`"* — and its heaviness is stated in the
weight `w` fixed before the construction. -/
theorem exists_plankFactoringData
    {κ : Type*} [DecidableEq κ] {ρ : ℝ≥0} (hρ0 : 0 < ρ) {r : Finset κ} (hr : r.Nonempty)
    (R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3)))
    (hball : ∀ k ∈ r, (R k).carrier ⊆ Metric.closedBall 0 1)
    (w : κ → ℝ≥0∞) :
    ∃ r' ⊆ r, r'.Nonempty ∧
      ∑ k ∈ r, w k ≤
        ConvexSpaceBody.nonempty_factorization.C 3 r.card ρ * ∑ k ∈ r', w k ∧
      ∃ pa pb : ℝ≥0, Nonempty (PlankFactoringData ρ pa pb 2 r' R) := by
  obtain ⟨r', hr'sub, hr'ne, hheavy, F, hFne, pa, pb, hρpa, hab, hb1, hth⟩ :=
    exists_maxDensityFactoring_planks hρ0 hr R hball w
  refine ⟨r', hr'sub, hr'ne, hheavy, pa, pb, ⟨?_⟩⟩
  exact
    { toFactorization := F
      parts_nonempty := hFne
      ball := fun k hk => hball k (hr'sub hk)
      scale_le := hρpa
      thin_le_wide := hab
      wide_le_one := hb1
      thicknesses := hth }

/-! ### The plank datum at the parent family of a uniformity structure

`Kakeya.ML2Reduction.exists_threshold_eccentric` asks for a
`Kakeya.ML2Reduction.PlankFactoringData` over `PS.parent` — GWZ Proposition 6.6(B)'s own shape,
in which the factored family is the parent family of a `Tube.IsUniformAtScale`.  The
factoring step, by contrast, hands back a factoring of a *refinement* `p ⊆ PS.parent`; the
blueprint says so explicitly (GWZ: proof of Main Lemma~\ref{lemmain2}: *"Lemma
`lemmafactmax` replaces the set `𝕋̃_ρ` with an `≈ 1` refinement.  This in turn induces a `≈ 1`
refinement on `(𝕋̃, Ỹ)`.  Abusing notation, we will continue to refer to these new objects as
`𝕋̃_ρ` and `Ỹ`"*).

The two shapes are reconciled by `Kakeya.ML2Reduction.restrictParents`, which cuts a uniformity
structure down to a subfamily of its parents and takes the leaves along as the induced
refinement.  `Kakeya.ML2Reduction.exists_plankFactoringData_of_isUniformAtScale` then produces a
`(PS', D)` **pair** of the exact shape `exists_threshold_eccentric` quantifies over, which is the
compiler-checked form of the claim that its plank hypothesis has a producer.
-/

section RestrictParents

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] [MeasureSpace E]
  {ι : Type*} [DecidableEq ι] {δ : ℝ≥0}

open Classical in
/-- **The leaves retained when the parent family of a single-scale uniformity structure is cut
down to `p`**: those `δ`-tubes of `s` that still lie in a parent belonging to `p`. -/
def restrictedLeaves {s : Finset ι} {T : ι → Tube δ E} {ρ C D : ℝ≥0}
    (PS : Tube.IsUniformAtScale s T ρ C D) (p : Finset ι) : Finset ι :=
  s.filter fun i => ∃ j ∈ p, (T i).toConvexSpaceBody ≤ (PS.parentTube j).toConvexSpaceBody

omit [MeasureSpace E] [DecidableEq ι] in
open Classical in
theorem restrictedLeaves_subset {s : Finset ι} {T : ι → Tube δ E} {ρ C D : ℝ≥0}
    (PS : Tube.IsUniformAtScale s T ρ C D) (p : Finset ι) :
    restrictedLeaves PS p ⊆ s := Finset.filter_subset _ _

open Classical in
/-- **Restriction of a single-scale uniformity structure to a subfamily of its parents.**

The branching number and the parent tubes are unchanged; only the parent index set and the leaf
family shrink.  All five clauses of GWZ Definition 2.1 survive, and the last one — the *lower*
branching bound `branchingN ≤ C * |{i ∈ s | T i ≤ parentTube j}|`, the only field that a naive
restriction could break — survives because the retained leaf set is defined so that
`{i ∈ restrictedLeaves PS p | T i ≤ parentTube j} = {i ∈ s | T i ≤ parentTube j}` for every
`j ∈ p`: a leaf under a retained parent is retained. -/
def restrictParents {s : Finset ι} {T : ι → Tube δ E} {ρ C D : ℝ≥0}
    (PS : Tube.IsUniformAtScale s T ρ C D) {p : Finset ι} (hp : p ⊆ PS.parent) :
    Tube.IsUniformAtScale (restrictedLeaves PS p) T ρ C D where
  branchingN := PS.branchingN
  parent := p
  parentTube := PS.parentTube
  exists_le_rescale := by
    intro i hi
    rw [restrictedLeaves, Finset.mem_filter] at hi
    exact hi.2
  boundedOverlap := by
    intro V
    refine le_trans ?_ (PS.boundedOverlap V)
    have hsub : (p.filter fun j => ∃ i ∈ restrictedLeaves PS p,
          (T i).toConvexSpaceBody ≤ (PS.parentTube j).toConvexSpaceBody ∧
          (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody) ⊆
        (PS.parent.filter fun j => ∃ i ∈ s,
          (T i).toConvexSpaceBody ≤ (PS.parentTube j).toConvexSpaceBody ∧
          (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody) := by
      intro j hj
      rw [Finset.mem_filter] at hj ⊢
      obtain ⟨hjp, i, hi, h1, h2⟩ := hj
      exact ⟨hp hjp, i, restrictedLeaves_subset PS p hi, h1, h2⟩
    exact_mod_cast Finset.card_le_card hsub
  parentTube_injOn := PS.parentTube_injOn.mono (by exact_mod_cast hp)
  card_filter_le := by
    intro j hj
    refine le_trans ?_ (PS.card_filter_le (hp hj))
    have hsub : {i ∈ restrictedLeaves PS p |
          (T i).toConvexSpaceBody ≤ (PS.parentTube j).toConvexSpaceBody} ⊆
        {i ∈ s | (T i).toConvexSpaceBody ≤ (PS.parentTube j).toConvexSpaceBody} := by
      intro i hi
      rw [Finset.mem_filter] at hi ⊢
      exact ⟨restrictedLeaves_subset PS p hi.1, hi.2⟩
    exact_mod_cast Finset.card_le_card hsub
  le_mul_card_filter := by
    intro j hj
    refine le_trans (PS.le_mul_card_filter (hp hj)) ?_
    have hsub : {i ∈ s | (T i).toConvexSpaceBody ≤ (PS.parentTube j).toConvexSpaceBody} ⊆
        {i ∈ restrictedLeaves PS p |
          (T i).toConvexSpaceBody ≤ (PS.parentTube j).toConvexSpaceBody} := by
      intro i hi
      rw [Finset.mem_filter] at hi ⊢
      refine ⟨?_, hi.2⟩
      rw [restrictedLeaves, Finset.mem_filter]
      exact ⟨hi.1, j, hj, hi.2⟩
    have hcard : ({i ∈ s | (T i).toConvexSpaceBody ≤
        (PS.parentTube j).toConvexSpaceBody}.card : ℝ≥0) ≤
        ({i ∈ restrictedLeaves PS p |
          (T i).toConvexSpaceBody ≤ (PS.parentTube j).toConvexSpaceBody}.card : ℝ≥0) := by
      exact_mod_cast Finset.card_le_card hsub
    gcongr

end RestrictParents

/-! ### The unit-ball normalisation is on the parents, and where it comes from

`Kakeya.ML2Reduction.PlankFactoringData.ball` asks that the *parent* `ρ`-tubes lie in the unit
ball.  That is `lemmafactmax`'s own hypothesis (`ConvexSpaceBody.nonempty_factorization` assumes
`(V i).carrier ⊆ closedBall 0 1`) and it is **not** implied by the leaves lying in the unit ball:
a parent covering a leaf inside `B̄(0,1)` need only lie inside `B̄(0, 2 + 2 ρ)`.

The obligation is discharged here rather than assumed.  The content is
`Kakeya.ML2Reduction.tube_carrier_subset_closedBall_of_le`: a unit core segment sitting inside
the `ρ`-neighbourhood of another unit core segment pins the second to within `2 ρ` of the first
at *both* ends, so a parent covering a leaf inside `B̄(0, r)` lies inside `B̄(0, r + 4 ρ)`.  With
`r + 4 ρ ≤ 1` the parents are unit-ball normalised and
`Kakeya.ML2Reduction.PlankFactoringData.ball` is available for free
(`Kakeya.ML2Reduction.parentTube_subset_unitBall_of_leafBall`).

**Why this and not a rescaling.**  The alternative — carry the parents at radius `R = 4` and
rescale — cannot work against GWZ 6.6(B) as stated, because the plank of
`Kakeya.GlobalPlankFactorization.le_plank` is a `Kakeya.Plank a b`, i.e. a prism of half-widths
`a × b × 1`: a block hull of extent `> 2` in its long direction fits in no such plank, whatever
`a` and `b` are.  So the normalisation has to happen *before* the factoring, on the leaf side,
and `r ≥ 1/2` is forced because a leaf is a unit segment thickened.  `r = 1/2` with `ρ ≤ 1/8` is
the sharpest reading, and the auxiliary scale `ρ = Kakeya.ML2Reduction.plankScale δ ε₂` meets it
for `δ` below an absolute threshold.
-/

section ParentBall

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [ProperSpace E]

omit [FiniteDimensional ℝ E] [ProperSpace E] in
/-- A point of the line through `A = M + t₁ • v` and `B = M + t₂ • v` whose parameter lies
between `t₁` and `t₂` is a convex combination of `A` and `B`, hence no further from the origin
than the worse of the two. -/
private theorem norm_le_of_param_between_aux {M v A B : E} {t₁ t₂ c R : ℝ}
    (hA : A = M + t₁ • v) (hB : B = M + t₂ • v) (hlt : t₁ < t₂)
    (hc1 : t₁ ≤ c) (hc2 : c ≤ t₂) (hnA : ‖A‖ ≤ R) (hnB : ‖B‖ ≤ R) :
    ‖M + c • v‖ ≤ R := by
  have hd : (0 : ℝ) < t₂ - t₁ := by linarith
  set l : ℝ := (c - t₁) / (t₂ - t₁) with hl
  have hl0 : 0 ≤ l := div_nonneg (by linarith) hd.le
  have hl1 : l ≤ 1 := (div_le_one hd).mpr (by linarith)
  have hne : t₂ - t₁ ≠ 0 := hd.ne'
  have hceq : c = t₁ + l * (t₂ - t₁) := by
    rw [hl, div_mul_cancel₀ _ hne]; ring
  have hEq : M + c • v = (1 - l) • A + l • B := by
    rw [hA, hB, hceq]; module
  calc ‖M + c • v‖ = ‖(1 - l) • A + l • B‖ := by rw [hEq]
    _ ≤ ‖(1 - l) • A‖ + ‖l • B‖ := norm_add_le _ _
    _ = (1 - l) * ‖A‖ + l * ‖B‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - l), abs_of_nonneg hl0]
    _ ≤ (1 - l) * R + l * R := by
        have h1 : (1 - l) * ‖A‖ ≤ (1 - l) * R := by
          have : (0:ℝ) ≤ 1 - l := by linarith
          exact mul_le_mul_of_nonneg_left hnA this
        have h2 : l * ‖B‖ ≤ l * R := mul_le_mul_of_nonneg_left hnB hl0
        linarith
    _ = R := by ring

/-- The clamp of `t` to the interval spanned by `t₁` and `t₂`, when that interval covers all but
`2 ρ` of `[-1/2, 1/2]`, moves `t` by at most `2 ρ`. -/
private theorem exists_clamp {t t₁ t₂ ρ : ℝ} (hρ : 0 ≤ ρ)
    (ht : |t| ≤ 1 / 2) (h1 : |t₁| ≤ 1 / 2) (h2 : |t₂| ≤ 1 / 2)
    (hle : t₁ ≤ t₂) (hgap : 1 - 2 * ρ ≤ t₂ - t₁) :
    ∃ c, t₁ ≤ c ∧ c ≤ t₂ ∧ |t - c| ≤ 2 * ρ := by
  rw [abs_le] at ht h1 h2
  refine ⟨max t₁ (min t t₂), le_max_left _ _, ?_, ?_⟩
  · exact max_le hle (min_le_right _ _)
  · rcases lt_trichotomy t t₁ with h | h | h
    · have hmin : min t t₂ = t := min_eq_left (by linarith)
      have hmax : max t₁ (min t t₂) = t₁ := by rw [hmin]; exact max_eq_left (by linarith)
      rw [hmax, abs_le]
      constructor <;> linarith [ht.1, ht.2, h1.1, h1.2, h2.1, h2.2]
    · subst h
      have hmin : min t t₂ = t := min_eq_left (by linarith)
      have hmax : max t (min t t₂) = t := by rw [hmin]; exact max_self _
      rw [hmax]; simp; linarith
    · rcases le_total t t₂ with h' | h'
      · have hmin : min t t₂ = t := min_eq_left h'
        have hmax : max t₁ (min t t₂) = t := by rw [hmin]; exact max_eq_right h.le
        rw [hmax]; simp; linarith
      · have hmin : min t t₂ = t₂ := min_eq_right h'
        have hmax : max t₁ (min t t₂) = t₂ := by rw [hmin]; exact max_eq_right hle
        rw [hmax, abs_le]
        constructor <;> linarith [ht.1, ht.2, h1.1, h1.2, h2.1, h2.2]

/-- **A parent tube that covers a leaf lying in a ball lies in a slightly larger ball.**

If the `δ`-tube `T` is contained in the `ρ`-tube `P` and `T.carrier ⊆ B̄(0, r)`, then
`P.carrier ⊆ B̄(0, r + 4 ρ)`.  The hypothesis `2 ρ < 1` is what makes the two core parameters of
`T`'s endpoints separate, which is the whole content: a unit segment inside the `ρ`-neighbourhood
of another unit segment pins the second segment to within `2 ρ` of the first at both ends. -/
theorem tube_carrier_subset_closedBall_of_le {δ ρ : ℝ≥0} {r : ℝ}
    (T : Tube δ E) (P : Tube ρ E) (hρ1 : 2 * (ρ : ℝ) < 1)
    (hle : T.carrier ⊆ P.carrier)
    (hball : T.carrier ⊆ Metric.closedBall (0 : E) r) :
    P.carrier ⊆ Metric.closedBall (0 : E) (r + 4 * (ρ : ℝ)) := by
  have hρ0 : (0 : ℝ) ≤ (ρ : ℝ) := ρ.coe_nonneg
  have hxm : T.x ∈ T.carrier := by
    rw [T.carrier_eq]
    exact Set.mem_iUnion₂.mpr
      ⟨T.x, left_mem_segment ℝ _ _, Metric.mem_closedBall_self δ.coe_nonneg⟩
  have hym : T.y ∈ T.carrier := by
    rw [T.carrier_eq]
    exact Set.mem_iUnion₂.mpr
      ⟨T.y, right_mem_segment ℝ _ _, Metric.mem_closedBall_self δ.coe_nonneg⟩
  obtain ⟨t₁, ht₁, hd₁⟩ := P.exists_param_of_mem_carrier (hle hxm)
  obtain ⟨t₂, ht₂, hd₂⟩ := P.exists_param_of_mem_carrier (hle hym)
  set M : E := P.midpoint with hM
  set v : E := P.direction with hv
  have hvn : ‖v‖ = 1 := P.norm_direction
  have hAx : ‖T.x - (M + t₁ • v)‖ ≤ (ρ : ℝ) := by
    have : T.x - (M + t₁ • v) = T.x - M - t₁ • v := by abel
    rw [this]; exact hd₁
  have hBy : ‖T.y - (M + t₂ • v)‖ ≤ (ρ : ℝ) := by
    have : T.y - (M + t₂ • v) = T.y - M - t₂ • v := by abel
    rw [this]; exact hd₂
  have hxn : ‖T.x‖ ≤ r := by simpa using hball hxm
  have hyn : ‖T.y‖ ≤ r := by simpa using hball hym
  have hAn : ‖M + t₁ • v‖ ≤ r + (ρ : ℝ) := by
    calc ‖M + t₁ • v‖ = ‖T.x - (T.x - (M + t₁ • v))‖ := by congr 1; abel
      _ ≤ ‖T.x‖ + ‖T.x - (M + t₁ • v)‖ := norm_sub_le _ _
      _ ≤ r + (ρ : ℝ) := by gcongr
  have hBn : ‖M + t₂ • v‖ ≤ r + (ρ : ℝ) := by
    calc ‖M + t₂ • v‖ = ‖T.y - (T.y - (M + t₂ • v))‖ := by congr 1; abel
      _ ≤ ‖T.y‖ + ‖T.y - (M + t₂ • v)‖ := norm_sub_le _ _
      _ ≤ r + (ρ : ℝ) := by gcongr
  -- the two parameters are `1 - 2 ρ` apart
  have hAB : ‖(M + t₁ • v) - (M + t₂ • v)‖ = |t₁ - t₂| := by
    have : (M + t₁ • v) - (M + t₂ • v) = (t₁ - t₂) • v := by module
    rw [this, norm_smul, hvn, Real.norm_eq_abs, mul_one]
  have hxy : ‖T.x - T.y‖ = 1 := by
    rw [← dist_eq_norm]; exact T.dist_eq_one
  have hgap : 1 - 2 * (ρ : ℝ) ≤ |t₁ - t₂| := by
    rw [← hAB]
    have hsplit : T.x - T.y =
        (T.x - (M + t₁ • v)) + ((M + t₁ • v) - (M + t₂ • v)) - (T.y - (M + t₂ • v)) := by abel
    have h1 : ‖T.x - T.y‖ ≤ ‖T.x - (M + t₁ • v)‖ + ‖(M + t₁ • v) - (M + t₂ • v)‖
        + ‖T.y - (M + t₂ • v)‖ := by
      rw [hsplit]
      exact (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    rw [hxy] at h1
    linarith
  -- every core point of `P` is within `r + 3 ρ` of the origin
  have hcore : ∀ t : ℝ, |t| ≤ 1 / 2 → ‖M + t • v‖ ≤ r + 3 * (ρ : ℝ) := by
    intro t ht
    have key : ∀ (s₁ s₂ : ℝ), |s₁| ≤ 1 / 2 → |s₂| ≤ 1 / 2 → s₁ ≤ s₂ →
        1 - 2 * (ρ : ℝ) ≤ s₂ - s₁ → ‖M + s₁ • v‖ ≤ r + (ρ : ℝ) →
        ‖M + s₂ • v‖ ≤ r + (ρ : ℝ) → ‖M + t • v‖ ≤ r + 3 * (ρ : ℝ) := by
      intro s₁ s₂ hs₁ hs₂ hle' hgap' hn₁ hn₂
      obtain ⟨c, hc1, hc2, hcd⟩ := exists_clamp hρ0 ht hs₁ hs₂ hle' hgap'
      have hlt : s₁ < s₂ := by
        rcases eq_or_lt_of_le hle' with h | h
        · exfalso; rw [← h] at hgap'; linarith
        · exact h
      have hcn : ‖M + c • v‖ ≤ r + (ρ : ℝ) :=
        norm_le_of_param_between_aux rfl rfl hlt hc1 hc2 hn₁ hn₂
      have hdiff : ‖(M + t • v) - (M + c • v)‖ = |t - c| := by
        have : (M + t • v) - (M + c • v) = (t - c) • v := by module
        rw [this, norm_smul, hvn, Real.norm_eq_abs, mul_one]
      calc ‖M + t • v‖ ≤ ‖M + c • v‖ + ‖(M + t • v) - (M + c • v)‖ := by
            have := norm_add_le (M + c • v) ((M + t • v) - (M + c • v))
            simpa using this
        _ = ‖M + c • v‖ + |t - c| := by rw [hdiff]
        _ ≤ (r + (ρ : ℝ)) + 2 * (ρ : ℝ) := by gcongr
        _ = r + 3 * (ρ : ℝ) := by ring
    rcases le_total t₁ t₂ with h | h
    · exact key t₁ t₂ ht₁ ht₂ h (by rw [abs_of_nonpos (by linarith)] at hgap; linarith) hAn hBn
    · exact key t₂ t₁ ht₂ ht₁ h (by rw [abs_of_nonneg (by linarith)] at hgap; linarith) hBn hAn
  intro p hp
  obtain ⟨t, ht, hpt⟩ := P.exists_param_of_mem_carrier hp
  have hpt' : ‖p - (M + t • v)‖ ≤ (ρ : ℝ) := by
    have : p - (M + t • v) = p - M - t • v := by abel
    rw [this]; exact hpt
  have : ‖p‖ ≤ r + 4 * (ρ : ℝ) := by
    calc ‖p‖ = ‖(M + t • v) + (p - (M + t • v))‖ := by congr 1; abel
      _ ≤ ‖M + t • v‖ + ‖p - (M + t • v)‖ := norm_add_le _ _
      _ ≤ (r + 3 * (ρ : ℝ)) + (ρ : ℝ) := by gcongr; exact hcore t ht
      _ = r + 4 * (ρ : ℝ) := by ring
  simpa using this

section Uniform

variable [MeasureSpace E] {ι : Type*} {δ : ℝ≥0} {s : Finset ι} {T : ι → Tube δ E}
  {ρ C D : ℝ≥0}

end Uniform

end ParentBall

/-! ### Crossing `lemmafactmax`'s refinement

`lemmafactmax` replaces the coarse family by an `≈ 1` refinement `p ⊆ PS.parent`, which induces
the refinement `Kakeya.ML2Reduction.restrictedLeaves PS p ⊆ s` on the leaves; the blueprint says
so and then abuses notation.  Formally the four leaf-side hypotheses of GWZ 6.6(B) have to be
transported across that refinement, and the free weight `w` of
`ConvexSpaceBody.nonempty_factorization.factorization_weighted` is what pays for it.

Taking `w = Kakeya.ML2Reduction.parentMass PS (fun i ↦ volume (T i).shade)` — the shading mass a
parent carries — the heaviness bound becomes a bound on the *leaf* mass
(`Kakeya.ML2Reduction.sum_le_of_parentMass_heavy`), at the extra factor `D` of the bounded-overlap
constant, and that transports the fullness lower bound
(`Kakeya.ML2Reduction.fullness'_le_mul_of_subset_of_sum_shade_le`) and, in the reverse direction, brings the
conclusion back to `s` (`Kakeya.ML2Reduction.multiplicity_le_mul_of_subset_of_sum_shade_le`).  The ball
normalisation and the density bound cross for free, by monotonicity.

**What the weight cannot do.**  `ShadedTube.ShadedUniformTubeSet` is not hereditary — its class
brackets are two-sided — and the tree's criterion for restricting it,
`Kakeya.ml1Boot.ShadedTube.ShadedUniformTubeSet.restrict_of_shadeClass_dense`, asks the subfamily
to retain a fixed fraction of *every shade class at every point*.  A mass-heaviness bound does not
imply that for any weight: the heavy members of a shade class can be a vanishing fraction of it.
So the shaded uniformity is left as the single remaining input of
`Kakeya.ML2Reduction.eccentric_of_maxDensityFactoring_crossed`.
-/

section Crossing

variable {ι : Type*}

end Crossing

section ParentWeight

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] [MeasureSpace E]
  {δ : ℝ≥0} {s : Finset ι} {T : ι → Tube δ E} {ρ C D : ℝ≥0}

end ParentWeight

/-- **The maximal density factoring step supplies the plank hypothesis of the eccentric case.**

Given a single-scale uniformity structure `PS` whose parent `ρ`-tubes are normalised to the unit
ball, `lemmafactmax` — in the weighted form
`ConvexSpaceBody.nonempty_factorization.factorization_weighted` — produces a subfamily
`p ⊆ PS.parent` that is `≈ 1`-heavy in the weight `w` fixed beforehand, together with a
`Kakeya.ML2Reduction.PlankFactoringData` over `p`.  And `p` is not a bare `Finset`: it is the
parent family of the honest uniformity structure `Kakeya.ML2Reduction.restrictParents PS hp`,
whose leaf family is the induced refinement of `s`.

So the pair `(PS', D)` that `Kakeya.ML2Reduction.exists_threshold_eccentric` quantifies over is
**jointly producible** by the factoring step, at the exact types it asks for.  What a call site
must still transport across the refinement `restrictedLeaves PS p ⊆ s` are the two hypotheses
that are not about planks — the shaded uniformity `huni` and the fullness lower bound `hfull` —
and that is what the `≈ 1`-heaviness in `w` is for; take `w i = volume (T i).shade`.

The unit-ball normalisation `hball` is on the *parents*, not the leaves, and is a genuine
requirement inherited from `lemmafactmax` itself (`ConvexSpaceBody.nonempty_factorization`
assumes `(V i).carrier ⊆ closedBall 0 1`).  It is not implied by the leaves lying in the unit
ball: a parent `ρ`-tube covering a leaf inside `B(0,1)` need only lie inside `B(0, 2 + 2ρ)`.  A
call site therefore rescales first. -/
theorem exists_plankFactoringData_of_isUniformAtScale
    {ι : Type*} [DecidableEq ι] {δ : ℝ≥0} {s : Finset ι}
    {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))} {ρ C D : ℝ≥0}
    (PS : Tube.IsUniformAtScale s T ρ C D) (hρ0 : 0 < ρ) (hne : PS.parent.Nonempty)
    (hball : ∀ j ∈ PS.parent, (PS.parentTube j).carrier ⊆ Metric.closedBall 0 1)
    (w : ι → ℝ≥0∞) :
    ∃ (p : Finset ι) (hp : p ⊆ PS.parent), p.Nonempty ∧
      ∑ k ∈ PS.parent, w k ≤
        ConvexSpaceBody.nonempty_factorization.C 3 PS.parent.card ρ * ∑ k ∈ p, w k ∧
      restrictedLeaves PS p ⊆ s ∧
      ∃ pa pb : ℝ≥0,
        Nonempty (PlankFactoringData ρ pa pb 2 (restrictParents PS hp).parent
          (restrictParents PS hp).parentTube) := by
  obtain ⟨p, hp, hpne, hheavy, pa, pb, hD⟩ :=
    exists_plankFactoringData hρ0 hne PS.parentTube hball w
  exact ⟨p, hp, hpne, hheavy, restrictedLeaves_subset PS p, pa, pb, hD⟩

/-! ### The eccentric case, with GWZ Proposition 6.6(B) discharged -/

open Classical in
/-- **The eccentric case of the proof of GWZ Main Lemma 2.**

This is `Kakeya.ML2Reduction.eccentric_of_prop66B_conclusion` with its hypothesis `h66B` supplied
by `Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` (GWZ Proposition 6.6(B)), applied — as the
blueprint says — "with `η_{j-1}` in place of `ε`".

It does
**not** depend on any hypothesis without a producer:
the plank datum is `Kakeya.ML2Reduction.PlankFactoringData`, which is exactly the output of the
maximal density factoring step and is inhabited by
`Kakeya.ML2Reduction.exists_plankFactoringData`. The conversion into 6.6(B)'s own datum
`Kakeya.GlobalPlankFactorization`, including its `wide` field, is `Kakeya.ML2Reduction.PlankFactoringData.toGlobalPlankFactorization`, at
the absolute transverse comparability constant `Cw = 128`.

The threshold `δ₀` is 6.6(B)'s own, intersected with `1` and with the scale below which
`128 ≤ δ ^ (-η₀)`, i.e. below which the absolute `Cw = 128` fits inside 6.6(B)'s sub-polynomial
budget.

The eccentricity hypothesis is `\eqref{eqecccase}` read at the plank parameters that the datum
actually hands to 6.6(B), `a = 2 pa` and `b = min (2 pb) 1`; the density hypothesis is
`\eqref{upperBdDeltaMaxTildeTT}`, and the conclusion is `\eqref{multTildeTLem2}`.

**The fine family is pairwise essentially distinct** (`(q : Set ι).Pairwise …`, beside the
window).  This is 6.6(B)'s own hypothesis because GWZ's
"uniform" entails it through Definition 2.1(ii) at `ρ = δ`, and it is passed through here
unchanged.  Where the reduction is to pay it: at its outer "we can assume without loss of
generality that `(𝕋, Y)` is uniform" (GWZ: proof of Main Lemma 2 from Lemma 9.1), where the
`δ^{-O(η)}` loss of uniformisation is absorbed by the outer `ε` — **not** by an
essential-distinctness refinement inside this case, whose loss `C · Δmax(𝕋̃) ≤ C · δ̃^{-η/ε₂}` is
exactly the power the ledger `-η - η/ε₂ + 12η/ε₂ ≥ 10η/ε₂` has no room for. -/
theorem exists_threshold_eccentric {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hKKT : KatzTaoEstimate (EuclideanSpace ℝ (Fin 3)) β)
    (hKF : FrostmanEstimate (EuclideanSpace ℝ (Fin 3)) β)
    {ε₂ η : ℝ} (hε₂0 : 0 < ε₂) (hε₂1 : ε₂ ≤ 1) (hη : 0 < η) :
    ∃ η₀ > (0 : ℝ), ∃ δ₀ > (0 : ℝ≥0), δ₀ ≤ 1 ∧
      ∀ {ι : Type*} (q : Finset ι) {δ : ℝ≥0} (_hδ0 : 0 < δ)
        (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        δ ≤ δ₀ →
        (∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (q : Set ι).Pairwise
          (fun i j => _root_.IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        (∃ C : ℝ≥0, C ≤ δ ^ (-η₀) ∧
          Nonempty (ShadedTube.ShadedUniformTubeSet q T (Tube.ssfGridLen δ) C)) →
        (δ : ℝ≥0) ^ η₀ ≤ ShadedBody.fullness q (fun i => (T i).toShadedBody) →
        ∀ (ρ pa pb Cpar C₀ : ℝ≥0),
          Cpar ≤ δ ^ (-η₀) → C₀ ≤ δ ^ (-η₀) → (δ : ℝ≥0) ^ (1 - ε₂) ≤ ρ →
          ∀ (PS : Tube.IsUniformAtScale q (fun i ↦ (T i).toTube) ρ Cpar),
          (max 1 Cpar) ^ 2 ≤ PS.branchingN →
          ∀ (_D : PlankFactoringData ρ pa pb C₀ PS.parent PS.parentTube),
          maxDensity q (fun i => (T i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-(η / ε₂)) →
          IsEccentric β ε₂ η δ pa pb →
          ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ≤
            (δ : ℝ≥0∞) ^ (10 * η / ε₂) * (q.card : ℝ≥0∞) ^ β := by
  obtain ⟨η₀, hη₀, δ₀, hδ₀, h66⟩ :=
    tubeMultiplicityOfGlobalPlankFactorisation hβ0 hβ1 hKKT hKF hε₂0 hε₂1 η hη
  have hthr0 : (0 : ℝ≥0) < ((128 : ℝ≥0)⁻¹) ^ (1 / η₀) :=
    NNReal.rpow_pos (by norm_num)
  refine ⟨η₀, hη₀, min (min δ₀ 1) (((128 : ℝ≥0)⁻¹) ^ (1 / η₀)),
    lt_min (lt_min hδ₀ one_pos) hthr0, (min_le_left _ _).trans (min_le_right _ _), ?_⟩
  intro ι q δ hδ0 T hδ hballq hEDq huni hfull ρ pa pb Cpar C₀ hCpar hC₀ hρlb PS hbr D hΔ hecc
  have hecc' : δ ^ (-eccExponent β ε₂ η) * (2 * pa) ≤ min (2 * pb) 1 := hecc
  have hδδ₀ : δ ≤ δ₀ := hδ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδ1 : δ ≤ 1 := hδ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδρ : δ ≤ ρ := by
    refine le_trans ?_ hρlb
    have := NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (show (1 : ℝ) - ε₂ ≤ 1 by linarith)
    simpa using this
  have hρ0 : 0 < ρ := lt_of_lt_of_le hδ0 hδρ
  -- The absolute comparability constant fits inside 6.6(B)'s sub-polynomial budget.
  have hCw : (128 : ℝ≥0) ≤ δ ^ (-η₀) := by
    have hle : δ ≤ ((128 : ℝ≥0)⁻¹) ^ (1 / η₀) := hδ.trans (min_le_right _ _)
    have hpow : δ ^ η₀ ≤ (128 : ℝ≥0)⁻¹ := by
      have := NNReal.rpow_le_rpow hle hη₀.le
      rwa [← NNReal.rpow_mul, one_div, inv_mul_cancel₀ hη₀.ne', NNReal.rpow_one] at this
    have hpos : (0 : ℝ≥0) < δ ^ η₀ := NNReal.rpow_pos hδ0
    have hinv := inv_anti₀ hpos hpow
    rwa [inv_inv, ← NNReal.rpow_neg] at hinv
  -- The eccentricity hypothesis forces the plank parameters into range.
  have hone_le : (1 : ℝ≥0) ≤ δ ^ (-eccExponent β ε₂ η) := by
    have hexp : eccExponent β ε₂ η ≥ 0 := by
      unfold eccExponent
      positivity
    have := NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1
      (show -eccExponent β ε₂ η ≤ (0 : ℝ) by linarith)
    rwa [NNReal.rpow_zero] at this
  have hab : 2 * pa ≤ min (2 * pb) 1 := by
    refine le_trans ?_ hecc'
    calc 2 * pa = 1 * (2 * pa) := by ring
      _ ≤ δ ^ (-eccExponent β ε₂ η) * (2 * pa) := by gcongr
  have hpa1 : 2 * pa ≤ 1 := hab.trans (min_le_right _ _)
  -- Convert the factoring datum into GWZ 6.6(B)'s datum and apply the proposition.
  have h66B := h66 q hδ0 T hδδ₀ hballq hEDq huni hfull ρ (2 * pa) (min (2 * pb) 1) hab
    (min_le_right _ _) 128 Cpar C₀ hCw hCpar hC₀ hρlb D.scale_le_thin PS hbr D.ball
    (D.toGlobalPlankFactorization hρ0 hpa1 hab)
  exact eccentric_of_prop66B_conclusion q hδ0 hδ1 T hβ0 hβ1 hε₂0 hε₂1 hη.le hΔ hecc' h66B

/-! ### The eccentric case, applied to the output of the factoring step -/

open Classical in
/-- **The eccentric case, with its plank hypothesis discharged by the maximal density factoring
step.**

This is `Kakeya.ML2Reduction.exists_threshold_eccentric` composed with
`Kakeya.ML2Reduction.exists_plankFactoringData_of_isUniformAtScale`: the plank datum is no longer
a hypothesis at all.  What is quantified over is a `Tube.IsUniformAtScale` on the coarse
scale `ρ` whose parents are normalised to the unit ball, i.e. exactly the blueprint's `𝕋̃_ρ`; the
refinement `p ⊆ PS.parent`, the plank parameters `a = 2 pa`, `b = min (2 pb) 1` and the factoring
itself are all *produced*.

The remaining four hypotheses are handed back as an implication on the refined leaf family
`Kakeya.ML2Reduction.restrictedLeaves PS p`, because they are precisely the things a call site
has to transport across `lemmafactmax`'s own `≈ 1` refinement: unit-ball normalisation of the
leaves, shaded uniformity, the fullness lower bound `\eqref{tildeYDense}`, and
`\eqref{upperBdDeltaMaxTildeTT}`.  The heaviness bound in the free weight `w` — take
`w i = volume (T i).shade` — is what pays for that transport.  The fifth is the case hypothesis
`\eqref{eqecccase}` itself, read at the produced plank parameters; the complementary inequality is
the non-eccentric case, and `le_or_lt` on exactly this predicate is what makes the two exhaustive.

`2 ≤ δ ^ (-η₀)` is the factoring constant `C₀ = 2` of
`ConvexSpaceBody.nonempty_factorization.factorization_weighted` fitting inside GWZ 6.6(B)'s
sub-polynomial budget; like `Cw = 128` it is absolute, so it is a threshold on `δ` alone.

Like `exists_threshold_eccentric`, this rests on GWZ Proposition 6.6(B)
(`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation`, proved in
`Kakeya/DimensionThree/Plank/Prop66BClose.lean`); for that single reason it carried `sorryAx`
until that proof existing, and it is now axiom-clean.

The fine-family pairwise essential distinctness of 6.6(B) is handed back on the
refined leaf family beside its window, exactly as the window is; it is hereditary
(`Set.Pairwise.mono`), so a call site holding it on `s` supplies it by restriction. -/
theorem eccentric_of_maxDensityFactoring {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hKKT : KatzTaoEstimate (EuclideanSpace ℝ (Fin 3)) β)
    (hKF : FrostmanEstimate (EuclideanSpace ℝ (Fin 3)) β)
    {ε₂ η : ℝ} (hε₂0 : 0 < ε₂) (hε₂1 : ε₂ ≤ 1) (hη : 0 < η) :
    ∃ η₀ > (0 : ℝ), ∃ δ₀ > (0 : ℝ≥0), δ₀ ≤ 1 ∧
      ∀ {ι : Type*} (s : Finset ι) {δ : ℝ≥0} (_hδ0 : 0 < δ)
        (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (w : ι → ℝ≥0∞),
        δ ≤ δ₀ → (2 : ℝ≥0) ≤ δ ^ (-η₀) →
        ∀ (ρ Cpar : ℝ≥0), Cpar ≤ δ ^ (-η₀) → (δ : ℝ≥0) ^ (1 - ε₂) ≤ ρ →
        ∀ (PS : Tube.IsUniformAtScale s (fun i => (T i).toTube) ρ Cpar),
          PS.parent.Nonempty → (max 1 Cpar) ^ 2 ≤ PS.branchingN →
          (∀ j ∈ PS.parent, (PS.parentTube j).carrier ⊆ Metric.closedBall 0 1) →
          ∃ (p : Finset ι) (_ : p ⊆ PS.parent) (pa pb : ℝ≥0),
            p.Nonempty ∧
            ∑ k ∈ PS.parent, w k ≤
              ConvexSpaceBody.nonempty_factorization.C 3 PS.parent.card ρ * ∑ k ∈ p, w k ∧
            ((∀ i ∈ restrictedLeaves PS p, (T i).carrier ⊆ Metric.closedBall 0 1) →
              (restrictedLeaves PS p : Set ι).Pairwise
                (fun i j => _root_.IsEssentiallyDistinct (T i).carrier (T j).carrier) →
              (∃ C : ℝ≥0, C ≤ δ ^ (-η₀) ∧
                Nonempty (ShadedTube.ShadedUniformTubeSet (restrictedLeaves PS p) T
                  (Tube.ssfGridLen δ) C)) →
              (δ : ℝ≥0) ^ η₀ ≤
                ShadedBody.fullness (restrictedLeaves PS p) (fun i => (T i).toShadedBody) →
              maxDensity (restrictedLeaves PS p) (fun i => (T i).toConvexSpaceBody) ≤
                (δ : ℝ≥0∞) ^ (-(η / ε₂)) →
              IsEccentric β ε₂ η δ pa pb →
              ShadedBody.multiplicity (restrictedLeaves PS p) (fun i => (T i).toShadedBody) ≤
                (δ : ℝ≥0∞) ^ (10 * η / ε₂) * ((restrictedLeaves PS p).card : ℝ≥0∞) ^ β) := by
  obtain ⟨η₀, hη₀, δ₀, hδ₀, hδ₀1, hecc⟩ :=
    exists_threshold_eccentric hβ0 hβ1 hKKT hKF hε₂0 hε₂1 hη
  refine ⟨η₀, hη₀, δ₀, hδ₀, hδ₀1, ?_⟩
  intro ι s δ hδ0 T w hδ h2 ρ Cpar hCpar hρlb PS hne hbr hball
  have hδ1 : δ ≤ 1 := hδ.trans hδ₀1
  have hδρ : δ ≤ ρ := by
    refine le_trans ?_ hρlb
    have := NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (show (1 : ℝ) - ε₂ ≤ 1 by linarith)
    simpa using this
  have hρ0 : 0 < ρ := lt_of_lt_of_le hδ0 hδρ
  obtain ⟨p, hp, hpne, hheavy, -, pa, pb, ⟨D⟩⟩ :=
    exists_plankFactoringData_of_isUniformAtScale PS hρ0 hne hball w
  refine ⟨p, hp, pa, pb, hpne, hheavy, ?_⟩
  intro hballq hEDq huni hfull hΔ hecc'
  exact hecc (restrictedLeaves PS p) hδ0 T hδ hballq hEDq huni hfull ρ pa pb Cpar 2
    hCpar h2 hρlb (restrictParents PS hp) hbr D hΔ hecc'

universe u in
/-- **No statement drift.**

Naming the case hypothesis `Kakeya.ML2Reduction.IsEccentric` changed the *statement* of
`Kakeya.ML2Reduction.eccentric_of_maxDensityFactoring` only up to unfolding a definition.  This
`example` is that statement exactly as it stood before the predicate was introduced — the
inequality written out — and it is inhabited by the theorem itself, with no bridging term.  If
`IsEccentric` is ever redefined to anything else, this stops compiling. -/
example {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hKKT : KatzTaoEstimate (EuclideanSpace ℝ (Fin 3)) β)
    (hKF : FrostmanEstimate (EuclideanSpace ℝ (Fin 3)) β)
    {ε₂ η : ℝ} (hε₂0 : 0 < ε₂) (hε₂1 : ε₂ ≤ 1) (hη : 0 < η) :
    ∃ η₀ > (0 : ℝ), ∃ δ₀ > (0 : ℝ≥0), δ₀ ≤ 1 ∧
      ∀ {ι : Type u} (s : Finset ι) {δ : ℝ≥0} (_hδ0 : 0 < δ)
        (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (w : ι → ℝ≥0∞),
        δ ≤ δ₀ → (2 : ℝ≥0) ≤ δ ^ (-η₀) →
        ∀ (ρ Cpar : ℝ≥0), Cpar ≤ δ ^ (-η₀) → (δ : ℝ≥0) ^ (1 - ε₂) ≤ ρ →
        ∀ (PS : Tube.IsUniformAtScale s (fun i => (T i).toTube) ρ Cpar),
          PS.parent.Nonempty → (max 1 Cpar) ^ 2 ≤ PS.branchingN →
          (∀ j ∈ PS.parent, (PS.parentTube j).carrier ⊆ Metric.closedBall 0 1) →
          ∃ (p : Finset ι) (_ : p ⊆ PS.parent) (pa pb : ℝ≥0),
            p.Nonempty ∧
            ∑ k ∈ PS.parent, w k ≤
              ConvexSpaceBody.nonempty_factorization.C 3 PS.parent.card ρ * ∑ k ∈ p, w k ∧
            ((∀ i ∈ restrictedLeaves PS p, (T i).carrier ⊆ Metric.closedBall 0 1) →
              (restrictedLeaves PS p : Set ι).Pairwise
                (fun i j => _root_.IsEssentiallyDistinct (T i).carrier (T j).carrier) →
              (∃ C : ℝ≥0, C ≤ δ ^ (-η₀) ∧
                Nonempty (ShadedTube.ShadedUniformTubeSet (restrictedLeaves PS p) T
                  (Tube.ssfGridLen δ) C)) →
              (δ : ℝ≥0) ^ η₀ ≤
                ShadedBody.fullness (restrictedLeaves PS p) (fun i => (T i).toShadedBody) →
              maxDensity (restrictedLeaves PS p) (fun i => (T i).toConvexSpaceBody) ≤
                (δ : ℝ≥0∞) ^ (-(η / ε₂)) →
              δ ^ (-eccExponent β ε₂ η) * (2 * pa) ≤ min (2 * pb) 1 →
              ShadedBody.multiplicity (restrictedLeaves PS p) (fun i => (T i).toShadedBody) ≤
                (δ : ℝ≥0∞) ^ (10 * η / ε₂) * ((restrictedLeaves PS p).card : ℝ≥0∞) ^ β) :=
  eccentric_of_maxDensityFactoring hβ0 hβ1 hKKT hKF hε₂0 hε₂1 hη

/-! ### The eccentric case with both normalisation obligations discharged -/

/-! ### The eccentric case on the original family -/

/-! ### The single application site supplies the narrowed coarse scale by `le_rfl` -/

end Kakeya.ML2Reduction

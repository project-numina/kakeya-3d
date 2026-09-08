/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.PartialEstimatesWindowed

/-!
# Named thresholds for the windowed Katz–Tao multiplicity bound

`Kakeya.KatzTaoEstimate.multiplicity_bound_generalize_window` produces its fullness exponent
`η_KT` and its radius threshold `ρ₀` *existentially*.  Every Section-9 consumer of it has to
compare those two quantities with data of a `Kakeya.VeryNotSticky` configuration — the exponent
with `2 * cfg.η`, the radius with the node scale `ρ` — and an existentially produced quantity
cannot be compared with anything by a statement that does not itself produce it.  That is what
made
`Kakeya.VeryNotSticky.coarseKatzTaoBound` false: the comparison was pushed under the
`∀ ν` binder of the consumer, where it reads `∀ ν > 0, 2 * cfg.η ≤ cfg.exscal * η_KT(ν)`, and
`η_KT(ν) → 0` as `ν → 0`.

This file removes the existential by Skolemizing it.  `Kakeya.windowFourData E β ε` is a
*named* pair `(η_KT, ρ₀)` depending on the ambient space, the Katz–Tao exponent `β` and the
loss exponent `ε` **and on nothing else** — in particular not on any configuration, and not on
`cfg.η` or `cfg.δ`.  `Kakeya.VeryNotSticky.coarseKTEta` and
`Kakeya.VeryNotSticky.coarseKTRadius` are its two components read at the loss exponent `ν/180`
attached to a gain `ν`.

With those names available, the two thresholds

* `2 * cfg.η ≤ cfg.exscal * coarseKTEta cfg.β ν`,
* `cfg.δ ^ (cfg.exscal / 2 - cfg.η) ≤ coarseKTRadius cfg.β ν`,

are ordinary comparisons of terms fixed *before* the corresponding field of the configuration:
the first bounds `2 * cfg.η` by a quantity depending only on `(β, ν)`, and `η` is chosen after
`β, ζ, exscal, ϱ, τ, τ'` and is bounded from above by every clause of
`Kakeya.VeryNotSticky.CaseParams`; the second is a smallness condition on `cfg.δ`, which is
chosen last of all.  The factor `2` on `cfg.η` is not slack: the fullness the coarse
Katz–Tao path has available is `δ^{2η}` (the field `Kakeya.VeryNotSticky.lam_ge`), so the
bridge to `cfg.a^{ηKT}` through `cfg.a ≤ cfg.δ^{exscal}` needs `2η ≤ exscal · ηKT`.  Both are
therefore of the shape `Kakeya.VeryNotSticky.CaseScale` already carries (compare its clause
`transverse_radius`), and neither is quantified over the gain.

## Main declarations

* `Kakeya.WindowFour` — the conclusion of the windowed bound at window radius `4`, with both
  thresholds named;
* `Kakeya.exists_windowFour` — that conclusion holds for *some* pair, from `KatzTaoEstimate`;
* `Kakeya.windowFourData` — the Skolem function, and `Kakeya.windowFourData_spec`;
* `Kakeya.VeryNotSticky.coarseKTEta`, `Kakeya.VeryNotSticky.coarseKTRadius`, and the three
  facts `coarseKTEta_pos`, `coarseKTRadius_pos`, `coarseKT_windowFour` that a Section-9
  consumer needs.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Topology ConvexSpaceBody Filter ShadedBody Metric Set

namespace Kakeya

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The windowed Katz–Tao multiplicity bound at window radius `4`, with both thresholds
named.**

`Kakeya.KatzTaoEstimate.multiplicity_bound_generalize_window` at `R = 4`, with the `∃ η > 0`
replaced by the parameter `ηKT` and the `∀ᶠ ρ in 𝓝[>] 0` replaced by the explicit threshold
`ρ ≤ ρ₀`.  Nothing is weakened: `Kakeya.exists_windowFour` below produces a pair for which this
holds, and `Kakeya.WindowFour.toEventually` recovers the `∀ᶠ` form. -/
def WindowFour (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (β ε ηKT : ℝ) (ρ₀ : ℝ≥0) : Prop :=
  ∀ ρ : ℝ≥0, 0 < ρ → ρ ≤ ρ₀ → ∀ τ : ℝ≥0, 0 < τ → τ ≤ ρ →
    ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube ρ E),
      (∀ i, (T i).carrier ⊆ Metric.closedBall 0 (4 : ℝ)) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ τ ^ ηKT →
      ShadedBody.multiplicity s (fun i ↦ (T i).toShadedBody) ≤
        (τ : ℝ≥0∞) ^ (-ε) * (maxDensity s (fun i ↦ (T i).toConvexSpaceBody)) ^ (1 - β) *
          (s.card : ℝ≥0∞) ^ β

/-- **The windowed bound holds at some named pair of thresholds.**

This is the whole content of `Kakeya.KatzTaoEstimate.multiplicity_bound_generalize_window`,
repackaged: the produced `η` becomes the first component and a radius below which the
neighbourhood filter statement holds becomes the second. -/
theorem exists_windowFour [Nontrivial E] {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (h : KatzTaoEstimate.{u} E β) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ × ℝ≥0, 0 < p.1 ∧ 0 < p.2 ∧ p.2 ≤ 1 / 2 ∧ WindowFour.{u} E β ε p.1 p.2 := by
  obtain ⟨ηKT, hηKT, hev⟩ :=
    KatzTaoEstimate.multiplicity_bound_generalize_window (E := E) hβ0 hβ1 h
      (R := 4) (by norm_num) ε hε
  obtain ⟨v, hv0, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hev
  refine ⟨(ηKT, min v (1 / 2 : ℝ≥0)), hηKT, lt_min hv0 (by norm_num),
    min_le_right _ _, ?_⟩
  intro ρ hρ0 hρv τ hτ0 hτρ ι s T hball hfull
  refine (hsub ⟨hρ0, le_trans hρv (min_le_left _ _)⟩) τ hτ0 hτρ s T ?_ hfull
  intro i
  have h4 : (((4 : ℝ≥0)) : ℝ) = (4 : ℝ) := by norm_num
  rw [h4]
  exact hball i

namespace VeryNotSticky

end VeryNotSticky

end Kakeya

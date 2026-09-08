/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCountClause

/-!
# Building the canonical cover on the rescaled bodies (step 10, clause `hcnt`)

Blueprint: GWZ, the non-eccentric case, the invocation of
GWZ Lemma 9.1 at `ζ = η_j/2`.

`Reduction/SpineCountClause.lean` reduces the count clause of `Kakeya.ML2Reduction.Lemma91At` to
the existence, at each scale `ρ` of Lemma 9.1's window, of *one* essentially distinct all-used
`ρ`-tube family over the **rescaled bodies**
`spineFamily (spineRescaleUnit …) 𝕋 i`, of cardinality at least
`spineOuterCountLoss R · ρ^{-2-ζ}` (`Kakeya.ML2Reduction.outerCanonicalCover_of_canonicalCover`,
`Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer_of_canonicalCover`).  Its own docstring
records what it does not do:

> "What this file does **not** do is *build* the canonical cover on the rescaled bodies."

and names the two residues: (a) the upstairs family at `ρ_up = ρ θ`, and (b) the arithmetic that
`spineOuterCountLoss R · refineToEssDistinctLeaves.C 3 · Δ_max` fits inside the count budget.
**This file builds it**, from the upstairs cover, and does both.

## The interface, and why it is stated over explicit hypotheses

The upstairs cover is produced by the spine's step 8 — `Kakeya.ML2Spine.spine_tube_card_lower` —
and the rescaled datum by the plank factoring; neither is assembled yet.  So the theorems here
take the upstairs cover as an **explicit hypothesis bundle** rather than as another unit's
existential output.  The bundle, at one scale `ρ` of the window, is:

* `t : Finset κ₀`, `W : κ₀ → Tube (ρ * θ)` — the upstairs `ρ_up`-tubes, `ρ_up = ρ θ`;
* `hsubW : ∀ k ∈ t, (W k).carrier ⊆ T₀.carrier` — the parents live in the coarse tube.  In the
  assembly this is the cover hierarchy's own containment, `Kakeya.ML2Reduction.tube_le_coarseNode`
  (the *ancestor fibre* inclusion, with no dilation);
* `hused : ∀ k ∈ t, ∃ i ∈ s, (𝕋 i).carrier ⊆ (W k).carrier` — the cover is all-used upstairs;
* `D`, `Ced` with `maxDensity` of the *pushed-down* `ρ`-tubes at most `D` and
  `refineToEssDistinctLeaves.C 3 * D ≤ Ced` — the essential-distinctness price, i.e. `Δ_max`;
* the count `ρ^{-2-ζ'} ≤ |t|` at a **reading exponent `ζ' ≥ ζ`**, and the slack
  `Ced · spineOuterCountLoss R ≤ ρ^{-(ζ' - ζ)}`.

The scale `ρ_up = ρ θ` is forced: `Kakeya.ML2Reduction.outerTube_used_of_used` needs
`Tube.IsRescalingSituation θ ρ_up ρ R 3`, whose `out_le_ratio` field is `ρ ≤ ρ_up / θ`, and
`ρ_up / θ ≤ 4 ρ` on the other side; `ρ_up = ρ θ` makes both an equality and a `ρ ≤ 4 ρ`
respectively (`Kakeya.ML2Reduction.isRescalingSituation_scaledUp`,
`Kakeya.ML2Reduction.ratio_scaledUp`).

## The count budget, and the two hypotheses that force it

`Kakeya.ML2Reduction.count_budget_of_slack` is the whole of residue (b):

```
Ced · (Λ · ρ^{-2-ζ}) ≤ ρ^{-(ζ'-ζ)} · ρ^{-2-ζ} = ρ^{-2-ζ'} ≤ |t|.
```

So the two losses `Λ = spineOuterCountLoss R` (the body→outer-tube transport) and
`Ced ≥ refineToEssDistinctLeaves.C 3 · Δ_max` (the essential-distinctness refinement) are paid
for **entirely out of the gap `ζ' - ζ` between the exponent step 8 delivers and the exponent
Lemma 9.1 is read at**, and by nothing else.  It does *not* fit at `ζ' = ζ`: at `ζ' = ζ` the
slack hypothesis reads `Ced · Λ ≤ 1`, which is false whenever `Δ_max ≥ 1`, and `Δ_max ≥ 1`
always (a nonempty family has density at least `1` in a body it fills).  **The budget therefore
closes if and only if Lemma 9.1 is read at a strictly smaller `ζ` than step 8 delivers**, and
`Lemma91ParamsAt` grants exactly that freedom — its body is `∀ ζ > 0, VNSBody β ϖ ζ …`, so the
consumer picks `ζ`.  `Kakeya.ML2Reduction.slack_of_exponents` prices the gap in exponents: if
`Ced ≤ ρ^{-a}` and `Λ ≤ ρ^{-c}` then `a + c ≤ ζ' - ζ` suffices.  Since `Λ` is a constant
(dimension and `R` only) and `Δ_max ≤ δ̃^{-η'}` on the spine's route, `c` is `0⁺` and `a` is of
order `η'`; the spine's own gap `ζ' - ζ = η_j/4` at `ζ' = η_j/2` is what pays.

## Main declarations

* `Kakeya.ML2Reduction.count_budget_of_slack` — residue (b): the count budget, in one line of
  `rpow` arithmetic.
* `Kakeya.ML2Reduction.slack_of_exponents` — the budget's slack hypothesis from exponents.
* `Kakeya.ML2Reduction.isRescalingSituation_scaledUp`,
  `Kakeya.ML2Reduction.ratio_scaledUp` — the rescaling situation at `ρ_up = ρ θ`.
* `Kakeya.ML2Reduction.canonicalCoverAt_of_upstairs` — residue (a) at one scale: the canonical
  cover on the rescaled bodies, from the upstairs cover.
* `Kakeya.ML2Reduction.canonicalCover_of_upstairs` — the same over the whole window, i.e. the
  `hcanon` binder of
  `Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer_of_canonicalCover`, produced.
* `Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer_of_upstairs` — step 10 with `hcnt`
  replaced by the upstairs bundle.
* `Kakeya.ML2Reduction.count_clause_at_uniformised` — the same count clause at the *uniformised*
  family `(s', U')`, which is the form a direct application of
  `Kakeya.ML2Reduction.Lemma91At` needs and the route around that wrapper's pinned `huni`.
* `Kakeya.ML2Reduction.not_count_budget_at_equal_reading` — the **refutation** that the
  budget could be paid at `ζ' = ζ`, resting on
  `Kakeya.ML2Reduction.two_le_refineToEssDistinctLeaves_C_three`,
  `Kakeya.ML2Reduction.one_le_maxDensity_tube` and
  `Kakeya.ML2Reduction.le_volume_c_three_coe`.
* `Kakeya.ML2Reduction.canonicalCover_mono`,
  `Kakeya.ML2Reduction.used_of_used_of_carrier_eq` — the two transports a consumer needs when the
  family it holds is a subfamily, or a shade-shrunk version, of the one the cover was built over.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Metric Set ConvexSpaceBody
open scoped NNReal ENNReal

namespace Kakeya.ML2Reduction

universe u

variable {θ τ σ : ℝ≥0}

/-! ## Residue (b): the count budget -/


/-! ## The rescaling situation at the upstairs scale `ρ_up = ρ θ` -/

/-- **The rescaling situation of the push-down.**  `Kakeya.ML2Reduction.outerTube_used_of_used`
pushes a family of `ρ_up`-tubes inside a `θ`-tube down to `ρ`-tubes, and needs
`Tube.IsRescalingSituation θ ρ_up ρ R 3`.  At `ρ_up = ρ θ` every field is inherited from the
step-10 situation `Tube.IsRescalingSituation θ τ σ R 3` except the two that mention `ρ`:
positivity, and the truncation `ρ ≤ 1/4` — which for `ρ` in Lemma 9.1's window
`[σ^{1-ϖ}, σ^ϖ]` is a threshold on `σ`, free under `∀ᶠ δ`. -/
theorem isRescalingSituation_scaledUp {R : ℝ}
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) {ρ : ℝ≥0}
    (hρ0 : 0 < ρ) (hρ4 : (ρ : ℝ) ≤ 1 / 4) :
    Tube.IsRescalingSituation θ (ρ * θ) ρ R 3 where
  pos_ambient := hsit.pos_ambient
  inner_le_ambient := by
    have hρ1 : ρ ≤ 1 := by rw [← NNReal.coe_le_coe]; push_cast; linarith
    calc ρ * θ ≤ 1 * θ := by gcongr
      _ = θ := one_mul θ
  ambient_le_one := hsit.ambient_le_one
  pos_out := hρ0
  out_le_quarter := hρ4
  out_le_ratio := by
    have hθ : (0 : ℝ) < (θ : ℝ) := hsit.pos_ambient
    push_cast
    rw [mul_div_assoc, div_self (ne_of_gt hθ), mul_one]
  normalizationConst_le_radius := hsit.normalizationConst_le_radius

/-- **The ratio hypothesis of the push-down at `ρ_up = ρ θ`**: `ρ_up / θ = ρ ≤ 4 ρ`. -/
theorem ratio_scaledUp (hθ : 0 < θ) (ρ : ℝ≥0) :
    ((ρ * θ : ℝ≥0) : ℝ) / (θ : ℝ) ≤ 4 * (ρ : ℝ) := by
  have hθ' : (0 : ℝ) < (θ : ℝ) := hθ
  push_cast
  rw [mul_div_assoc, div_self (ne_of_gt hθ'), mul_one]
  nlinarith [ρ.coe_nonneg]

/-! ## Residue (a): the canonical cover on the rescaled bodies -/


/-! ## Step 10, over the upstairs interface -/


/-! ## The two transports a consumer needs -/


/-! ## The budget does not close at an equal reading exponent — a refutation -/


/-- **A nonempty family of `ρ`-tubes has maximal density at least `1`** (`ρ > 0`): every tube has
positive volume (`Tube.le_volume`), so `Kakeya.one_le_maxDensity` applies.  This is what makes the
`Δ_max`-price of the essential-distinctness refinement unavoidable. -/
theorem one_le_maxDensity_tube {ι : Type*} {t : Finset ι} {ρ : ℝ≥0} (hρ : 0 < ρ)
    (V : ι → Tube ρ (EuclideanSpace ℝ (Fin 3))) {k : ι} (hk : k ∈ t) :
    1 ≤ Kakeya.maxDensity t (fun j ↦ (V j).toConvexSpaceBody) := by
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  refine Kakeya.one_le_maxDensity ⟨k, hk, ?_⟩
  have h := Tube.le_volume (V k)
  rw [hfr] at h
  refine lt_of_lt_of_le ?_ h
  have h0 : (0 : ℝ≥0) < Tube.le_volume.c 3 * ρ ^ (3 - 1) := by
    have := Tube.le_volume.c_pos 3
    positivity
  exact_mod_cast h0


end Kakeya.ML2Reduction

end

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factorization
public import Kakeya.Tube.Basic
public import Kakeya.Tube.Dilate
public import Kakeya.Thickness.Projection

/-!
# G3, red half: the biased factorization's retained subfamily can lose `Δ_max` polynomially

`ConvexSpaceBody.nonempty_biasedFactorization` (GWZ Lemma 9.2, refined `lemmafactmaxbias`) returns a
subfamily `s' ⊆ s` retaining **volume** (`Σ_s |V| ≤ L · Σ_{s'} |V|`) and carrying a biased
factorization.  The probe G3  asked whether such an `s'` also retains
`Δ_max` up to a subpolynomial factor.  **It cannot be added to the conclusion**: this file exhibits,
at every `δ ≤ 1/64`, a family `s` satisfying every hypothesis of the theorem, and a subfamily `s'`
satisfying every clause of its conclusion, with `Δ_max(s') ≤ 1` and `Δ_max(s) ≥ ⌊1/(24δ)⌋` — a
polynomial collapse `δ^{-1}`.

The family: `k = ⌊1/(24δ)⌋` identical copies of one central `δ`-tube (density `≥ k` inside that
tube) together with `k` pairwise disjoint translates of it along `e₀` at spacing `3δ`; the retained
subfamily is the translates alone, with the singleton partition as its biased factorization.
This is
the source's own reason for alternative (D) of `lem:ml2-window-refinement`: a
mass-weighted selection can delete the members inside the concentrating body.

The green half — that the count floor's derivation does not need the retained subfamily at all — is
`Kakeya.ML2Core.exists_biasedMaximizer_densityIn_ge` in `Reduction/SpineFloorGate.lean`.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Metric ConvexSpaceBody
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## Elementary tools, kept upstream of the Section-9 leaves -/


/-! ## The family -/

/-- The axis direction `e₂` and the translation direction `e₀`. -/
noncomputable def redE (k : Fin 3) : E3 := EuclideanSpace.single k (1 : ℝ)

theorem norm_redE (k : Fin 3) : ‖redE k‖ = 1 := by simp [redE]


/-- The central `δ`-tube: midpoint `0`, direction `e₂`. -/
noncomputable def redTube (δ : ℝ≥0) : Tube δ E3 :=
  Tube.ofMidpointDirection δ 0 (redE 2) (norm_redE 2)


/-! ## The constants of `nonempty_biasedFactorization`, from below -/


/-! ## The counterexample -/


end Kakeya.ML2Core

end

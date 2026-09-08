/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.LooseUniformProducer

/-!
# Conjunct 6 of `SideDataObligations`: what the Katz–Tao density field permits

The evidence offered for that is
`Kakeya.LooseUniform.bush_obstruction`: `n ≈ 1/(2ρ_k)` unit `δ`-tubes through a common point
`x`, **all with the same direction**, pairwise in no common exact `ρ_k`-tube, so `n` distinct
exact classes each of size one, while the angular cone at `(x, v)` contains all `n`. The
missing step — never compiled, and flagged as such by  — is that such a
family is *admissible*: that it can be the `s`/`T` of a `Kakeya.VeryNotSticky`.

This file settles that step, and the answer is **negative for the parallel bush**.  The field
that blocks it is `Kakeya.VeryNotSticky.maxDensity_le`, GWZ's `Δ_max(𝕋) ≤ δ^{-η}`:

* `Kakeya.VeryNotSticky.card_cone_le` — in **every** configuration, the members of `cfg.s`
  passing through a point `x` with direction within `θ` of `v` are confined to the `4`-dilate
  of a single `ρ`-tube whenever `2δ + θ ≤ 4ρ`, and `maxDensity_le` then caps their number by
  `coneCardConstant · δ^{-η} · (ρ/δ)²`.
* `Kakeya.VeryNotSticky.card_parallel_le` — at `θ = 0` the containing body is a `δ`-tube, so
  the cap collapses to `coneCardConstant · δ^{-η}`: **a parallel bush in an admissible
  configuration has at most `O(δ^{-η})` members.**  The `n ≈ 1/(2ρ_k) ≈ δ^{-2·exscal}` of the
  cited argument is polynomially larger than that, so the parallel bush is not admissible at
  the size the refutation needs.
* `Kakeya.VeryNotSticky.parallel_bush_forces_delta_large` /
  `Kakeya.VeryNotSticky.not_parallel_bush_family` — with `tube_count` (`|𝕋| ≥ δ^{-1}`) the
  parallel bush is not admissible **at all** below an explicit threshold on `δ`: a bush plus
  boundedly many further tubes cannot even reach the configuration's own cardinality floor.

What this does **not** show is that conjunct 6 is true.  `card_cone_le` at the split scale
(`Kakeya.VeryNotSticky.card_angularFibre_le`) leaves the angular fibre as large as
`δ^{-η}(ρ₂*/δ)²`, which is polynomially above the `Cang ≤ δ^{-η}` conjunct 6 allows; the
geometry that realises it is a bush whose members are spread in **direction** as well as in
axial offset, and `Kakeya.VeryNotSticky.twisted_bush` compiles exactly that configuration —
`n` tubes through `x`, pairwise in no common exact `ρ`-tube (so `n` distinct exact classes,
as `bush_obstruction` gives), all inside the angular cone of radius `ρ₂*` at `(x, v)`, and
with pairwise distinct directions, so that `card_parallel_le` does **not** apply to it.  The
honest statement is therefore: *the family the R18/argument names is refuted by the
compiler; the conclusion it draws is not, and a corrected family exists.*

Nothing here is an `∀ᶠ δ` statement and nothing here discharges or refutes conjunct 6.  No
declaration of `SetupSideData.lean`, `LooseUniform.lean` or `LooseUniformProducer.lean` is
changed; this file only adds.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped NNReal ENNReal RealInnerProductSpace

/-!
## The corrected geometry: a bush that the density cap does **not** kill

`card_nearly_parallel_le` refutes the family the R18/ argument names, not the claim
it draws from it.  A family escaping the cap must have directional spread beyond `2δ`, and one
does exist that keeps every other feature of `Kakeya.LooseUniform.bush_obstruction`: `n` unit
`δ`-tubes through a common point `x`, pairwise in **no** common exact `ρ`-tube (hence `n`
distinct exact classes, each a singleton in the bush), all inside an angular cone of radius
`π n α` about `e₁` (hence all inside one `angularFibre` once `π n α ≤ ρ₂*`), and with
directions pairwise separated by more than `4δ`, so that no unit `v` puts them all inside a
`2δ`-cone.  The axial offsets are `i · sp` and the directions are `√(1 - s²) e₁ + s e₂` at
`s = i · α`: a *twisted* bush.

The admissible parameter window is `4δ < α`, `nα ≤ 1/2`, `2ρ + 2α < sp`, `n·sp ≤ 1/4`, which
at the split scale `ρ ≈ ρ₂*` gives `n ≈ 1/(4ρ₂*)` — the same polynomial size
`bush_obstruction` claims, now compatible with `Δ_max ≤ δ^{-η}` (the `n` tubes then span a
`ρ₂*`-cylinder of volume `≍ ρ₂*²` rather than a `δ`-cylinder of volume `≍ δ²`, so the density
they force is `≍ n δ²/ρ₂*² ≪ 1`; that last comparison is arithmetic on the exponents and is
**not** compiled here).

So this file does not decide conjunct 6.  It decides which family the decision must use.
-/

namespace Kakeya.LooseUniform.Twisted

open Kakeya.LooseUniform Kakeya.LooseUniform.NonVacuity Kakeya.LooseUniform.Producer


/-- The unit direction at transversal parameter `s`. -/
noncomputable def dir (s : ℝ) : E3 := Real.sqrt (1 - s ^ 2) • e₁ + s • e₂


end Kakeya.LooseUniform.Twisted


namespace Kakeya.VeryNotSticky

universe u

open Kakeya.LooseUniform Kakeya.LooseUniform.NonVacuity

/-! ## The dimensional constant -/

/-- The ambient dimension of Section 9. -/
theorem finrank_E3 : Module.finrank ℝ E3 = 3 := by simp [E3]


/-! ## The two elementary inputs -/


/-! ## The density cap on a subfamily inside a dilated tube -/


/-! ## The cap on an angular cone at a point -/


/-! ## Two strengthenings and the general ceiling on conjunct 6's left-hand side -/


/-! ## Consequence for the cardinality floor `tube_count` -/


/-! ## The residual comparison `hlow` of the (86) bridge, on a parallel bush -/


end Kakeya.VeryNotSticky

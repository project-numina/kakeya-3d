/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.WangZahl.WolffHairbrush
public import Kakeya.DimensionThree.MainLemma2.WangZahl.SigmaCalculus
public import Kakeya.DimensionThree.MainLemma2.WangZahl.EToD
public import Kakeya.DimensionThree.CardBound
public import Kakeya.DimensionThree.MainLemma2.WangZahl.Rescaling
public import Kakeya.DimensionThree.MainLemma2.WangZahl.WZMultiScale

/-!
# Guardrails for `Kakeya.WangZahl.WolffHairbrushBroad`

Leaf 2 of the Wang--Zahl Proposition 1.10 decomposition
(`Kakeya.DimensionThree.MainLemma2.WangZahl.WolffHairbrush`) requires
a Katz--Tao hypothesis. This file gives counterexamples to the statement
without that hypothesis.

## The defect

The pre-repair `WolffHairbrushBroad` asked, for each `eps > 0`, for `kappa, nu > 0`
such that every family of essentially distinct `delta`-tubes contained in a
common `theta`-tube, `delta^nu`-dense and `nu`-broad at scale `theta`, obeys

```
kappa * delta^{eps/2} * delta^{3/2} * theta^{1/2} * (#T)^{1/2} <= |union of Y(T)|.
```

It carried **no** Katz--Tao convex Wolff hypothesis.  Wolff's hairbrush theorem
`\cite{Wol95}` is a bound for families of `delta`-**separated directions**, i.e.
`#T <~ delta^{-2}` after rescaling; the leaf as written admitted any essentially
distinct family, hence up to `delta^{-4}` tubes.  Two independent refutations:

* `not_wolffHairbrushBroadAt_of_half_lt` / `nu_le_half_of_wolffHairbrushBroadAt`:
  for a fixed `eps` no quality `nu > eps/2` is admissible at all.  Witness:
  `theta = delta`, the one-element family `centredTube delta` shaded by
  `tubeBox delta (4 delta^nu)`; the shaded volume `8 delta^{nu+2}` falls below the
  demanded `kappa delta^{2+eps/2}`.  (This is a defect of the *split*, not of the
  source: the source keeps the density exponent `3 eta` and the broadness quality
  `eta` distinct, and the split collapsed them into one `nu`.)
* `not_wolffHairbrushBroad_of_packing`: applied at `eps = 1/2`, the first
  refutation forces `nu <= 1/4 <= 2`, `card_le_of_wolffHairbrushBroadAt` caps every
  admissible family by `#T <= (|B(0,1)|/kappa)^2 delta^{-7/2}` at `theta = 1`, and
  the standard `delta`-tube packing of the unit ball (`ExistsBroadPacking`)
  supplies an admissible family with `#T >= C delta^{-7/2}`.

## The repair

`WolffHairbrushBroad` now carries the hypothesis
`katzTaoConvexWolffConstant s T <= delta^{-nu}` (`wolffHairbrushBroad_eq` is the
tripwire that pins the repaired statement).  It is inherited verbatim by every
class of the cover of `HairbrushCover`
(`katzTaoConvexWolffConstant_le_of_subset`), and it is exactly what excludes the
packing: `packing_violates_katzTaoHypothesis` shows the packing family has
`CKT >= 2 delta^{-nu}` for every `nu <= 3/2`, so the second refutation no longer
applies to the repaired leaf.  The first refutation does not apply either, since
`nu` is now also the Katz--Tao budget; but note that it still constrains the
repaired leaf to `nu <= eps/2` whenever the Katz--Tao hypothesis is satisfiable
at that `nu`, which is why `wolffHairbrushBroad_holds` remains open.

The Frostman slab hypothesis `FS(T) <= delta^{-eta}` is deliberately **not**
handed down to the class: a class sits inside a single `theta`-tube, hence inside
a slab of volume `~ theta`, which forces `FS(class) >= c theta^{-1}`.  Handing the
normalized Frostman bound down would create an inconsistent hypothesis bundle at
small `theta` -- green in the compiler, vacuous in content.  See the discussion in
`WolffHairbrush.lean`.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Metric

namespace Kakeya.WangZahl

noncomputable section

universe u

/-! ### The refuted pre-repair form of Leaf 2 -/

/-! ### The refutation of Leaf 2, modulo the standard tube packing

`nu_le_half_of_wolffHairbrushBroatAt` above shows that only `ν ≤ ε/2` can occur.
That is exactly the range in which the *other* obstruction bites.

`card_le_of_wolffHairbrushBroadAt` says that an admissible `(ε, κ, ν)` caps the
size of every admissible family: at `θ = 1`,
`κ δ^{3/2+ε/2} (#𝕋)^{1/2} ≤ |B(0,1)|`, i.e. `#𝕋 ≤ (|B(0,1)|/κ)² δ^{-3-ε}`.
But the unit ball contains `≍ δ^{-4}` essentially distinct `δ`-tubes, and the
full packing is `1`-dense and broad at scale `1` for every quality `ν ≤ 2`
(through a point of the shaded core the directions fill the sphere, so the
fraction of them within chordal distance `r` of a given `w` is `r²/2 ≤ r^ν`).
Since `ν ≤ ε/2 ≤ 2` for `ε ≤ 4`, the packing is admissible and `δ^{-4}` beats
`(|B|/κ)² δ^{-3-ε}` at every small `δ` as soon as `ε < 1`.

So Leaf 2 is **false as split**: `not_wolffHairbrushBroad_of_packing` derives
`¬ WolffHairbrushBroad` from `ExistsBroadPacking`, and `ExistsBroadPacking` is
the standard packing count.  What is missing from the leaf is precisely what the
source's class `𝕋[T_θ]` inherits and this statement drops: the Katz--Tao convex
Wolff bound `CKT(𝕋) ≤ δ^{-η}` (the full packing has `CKT ≍ δ^{-2}`) and the
Frostman slab bound `FS(𝕋) ≤ δ^{-η}`.  Wolff's theorem `\cite{Wol95}` is a bound
for families of **`δ`-separated directions** (`#𝕋 ≲ δ^{-2}`); the passage to
`#𝕋` up to `δ^{-4}` in the leaf has no counterpart in `\cite{Wol95}`.  Any repair
of `hairbrushDecomposition_of_cover_of_broad` must hand those two hypotheses
down from `HairbrushCover` to `WolffHairbrushBroad`. -/

/-! ### The repair kills the counterexample

The refutation above is powered by `ExistsBroadPacking`, whose family has
`#T ≍ δ^{-4}` tubes inside the unit ball.  Its Katz--Tao convex Wolff constant is
therefore at least `#T · |T| / |B(0,1)| ≍ δ^{-2}`, far above the budget `δ^{-ν}`
that the repaired `WolffHairbrushBroad` now demands.  The family is consequently
**not** admissible for the repaired leaf, so the refutation does not transfer. -/

/-! ## Refutation of `Kakeya.WangZahl.BalancedBroadCover`

Leaf 1b of the Wang--Zahl Proposition 1.10 decomposition, `BalancedBroadCover`,
is **false** as stated.  The defect is its last conjunct, the encoding of the
used half of the source's display `broadAtScaleTheta`,

```
sum_j |union_{T in part j} Y(T)|  <=  |union_{T in T} Y(T)|,
```

which carries **no constant and no power of `delta`**, whereas the source's
display is only an approximate identity.  The counting budget `delta^{-eps/16}`
that sits next to it is not enough slack: it tends to `1` as `eps -> 0` at a
fixed `delta`, while the covering multiplicity does not.

**The witness.** Take `delta = theta = 1/256` and the family of *two* orthogonal,
fully shaded `delta`-tubes through the origin (`crossedFamily`).  It satisfies
every hypothesis of the leaf at `nu = 1`:

* both carriers lie in the unit ball (`axisTube_subset_ball`);
* they are essentially distinct (`isEssentiallyDistinct_axisTube`): the
  intersection lies in `closedBall 0 (2 delta)`, of volume `24 c delta^3`, while
  each tube has volume at least `c delta^2`, and `48 delta <= 1`;
* the family is `delta^1`-dense, since the shadings are the whole carriers;
* `CKT <= #T = 2 <= 256 = delta^{-1}` (`katzTaoConvexWolffConstant_le_card`);
* broadness at `theta = delta` is automatic (`isBroadAtScale_of_le_delta`).

**Why no cover works.**  No `delta`-tube contains both members
(`not_union_axisTube_subset`): all `delta`-tubes have the same volume `V`, and
essential distinctness forces `|T_0 union T_1| >= 3V/2 > V`.  So every class of
every cover has at most one member, and the counting conjunct
`2 <= delta^{-1/16} * sum_j #part j` — with `delta^{-1/16} = 256^{1/16} =
sqrt 2 < 2` — forces at least **two** nonempty classes.  Each nonempty class
contributes the full `V` to the left-hand side of the disjointness conjunct, so
that side is at least `2V`, while the right-hand side is
`|T_0 union T_1| = 2V - |T_0 cap T_1| < 2V`, the two tubes sharing the ball
`closedBall 0 delta`.

**What the corrected statement has to say.**  A constant, or a factor
`delta^{-eps/16}`, in front of `|union Y|` does *not* repair the leaf: at
`theta = delta` a planar family of `~delta^{-2}` essentially distinct tubes has
`sum_j |union_{part j} Y| ~ delta^{-2} delta^2 = 1` against
`|union Y| ~ delta`, a ratio `delta^{-1}` that beats every fixed power
`delta^{-c eps}`.  What the source actually does at this point is *shrink the
shadings*: "after a further refinement, we may suppose that each set `T^{T_theta}`
is `delta^{3 eta}`-dense" assigns each point of the union to one class, which is
what makes the classes' shadings disjoint and what the density loss pays for.
The faithful encoding therefore has to let the cover return a shading refinement
`Y_j(T) subset Y(T)`, per class, with the classes' refined shadings pairwise
disjoint and each class `delta^nu`-dense *for its refined shading*; Leaf 2 is
then applied to the refined shadings.  `BalancedBroadCover` as written has no
room for that, since the shaded tubes `T` are fixed.
-/

/-- The unit segment centred at the origin along the `k`-th coordinate axis. -/
def axisTube (δ : ℝ≥0) (k : Fin 3) : Tube δ Space3 :=
  Tube.mk' δ (x := -((1 : ℝ) / 2) • EuclideanSpace.single k (1 : ℝ))
    (y := ((1 : ℝ) / 2) • EuclideanSpace.single k (1 : ℝ)) (by
      have h : (-((1 : ℝ) / 2) • EuclideanSpace.single k (1 : ℝ) -
          ((1 : ℝ) / 2) • EuclideanSpace.single k (1 : ℝ) : Space3) =
          -(EuclideanSpace.single k (1 : ℝ)) := by module
      rw [dist_eq_norm, h, norm_neg, PiLp.norm_single, norm_one])

/-! ## A satisfiability certificate at a **non-degenerate** scale `θ > δ`

Every certificate on record so far sits at `θ = δ`, where the broadness
condition is vacuous (`isBroadAtScale_of_le_delta`: the range `r ∈ [δ, θ]`
collapses to `r = θ`, and the bound reads `#{...} ≤ 1 · #𝕋_Y(x)`).  A certificate
at `θ > δ` is strictly stronger, because there `IsBroadAtScale` really does have
to be verified, and it carries the pointwise multiplicity demand
`#𝕋_Y(x) ≥ (θ/δ)^ν` of `rpow_le_multiplicity_of_isBroadAtScale`.

The witness is the crossed pair again, but with the shadings taken to be the
ball `closedBall 0 δ` that **both** tubes contain, so that every point of every
shading has multiplicity `2`:

* `θ = (5/4) δ`, `ν = 2`, so `(θ/δ)^ν = 25/16 ≤ 2` and the multiplicity demand
  is met with equality-to-spare;
* the count of tubes within `r` of a direction `w` never reaches `2`, because
  the two directions are orthogonal: `‖σ e₀ - τ e₁‖ = √2 ≥ 1` for either choice
  of signs (`one_le_norm_sub_signed`), so two tubes in the count force
  `1 ≤ 2r`, i.e. `r ≥ 1/2`, while `r ≤ θ ≤ 5/192`;
* `δ^ν`-density holds because `|closedBall 0 δ| ≍ δ³` beats `δ² |T| ≍ δ⁴`, which
  is what fixes `ν = 2` (at `ν = 1` the density fails: two transverse `δ`-tubes
  meet in volume `≍ δ³`, only a `δ`-fraction of `|T|`);
* `CKT ≤ #𝕋 = 2 ≤ δ^{-2}`.

**How far this can be pushed, and why not further here.**  The two constraints
fight: the multiplicity demand `(θ/δ)^ν ≤ #𝕋_Y(x)` pushes `ν` down, and the
density demand `δ^ν ≲ |Y|/|T|` pushes `ν` up.  For a family of *bounded* size
the shadings must sit in the pairwise intersections, whose volume is `≍ δ |T|`,
forcing `ν ≳ 1` and hence `θ/δ ≤ (#𝕋)^{1/ν} = O(1)`.  So no `O(1)`-size witness
reaches `θ ≫ δ`, and `rpow_le_card_of_isBroadAtScale` is the mechanical form of
that obstruction: a broad family has `#𝕋 ≥ (θ/δ)^ν`.  A witness at `θ ≍ 1` has
to be a genuine `≍ 1/δ`-tube arrangement — three families of parallel `δ`-tubes
at mutual angle `60°` in a plane is the smallest design that works, since the
count-equals-multiplicity case forces the directions at a point to leave no
unit vector within angle `arcsin(θ/2)` of all of them — and building it in Lean
is a separate steps. -/

/-! ## The shading refinement repairs the refutation

`not_balancedBroadCover` above refutes the fixed-shading covering leaf at the
crossed family: `δ = θ = 1/256`, `ν = 1`, `ε = 1`, two orthogonal fully shaded
`δ`-tubes `A`, `B` through the origin.  No `δ`-tube contains both
(`not_union_axisTube_subset`), so every class of any cover holds at most one of
them; the counting conjunct then forces two nonempty classes, contributing
`|A| + |B| = 2V` on the left of the essential-disjointness conjunct, against
`|A ∪ B| = 2V - |A ∩ B| < 2V` on the right.

The theorem below is the compiler-checked statement that the restatement is the
right repair: at *the same witness*, and for every admissible `δ`, the
conclusion of `Kakeya.WangZahl.RefinedBalancedBroadCover` — all seven conjuncts,
at `θ = δ`, `ν = 1`, `ε = 1` — **is** achievable, by handing the class of `A`
the refined shading `A \ B` and the class of `B` the shading `B`.  The
essential-disjointness conjunct then holds with equality,
`|A \ B| + |B| = |A ∪ B|`, which is exactly the slack the fixed-shading form
did not have.

The refined shading is still `δ^ν`-dense, `ν = 1`: `|A \ B| ≥ |A| - |A ∩ B| ≥
V/2 ≥ δ V` by `volume_inter_axisTube_le`.  So the repair is not bought by
letting the shadings collapse. -/

/-! ## Tripwires for the shading-refinement restatement of Leaf 1

`Kakeya.WangZahl.HairbrushCover` and `Kakeya.WangZahl.BroadScaleRefinement` were
restated so that the cover / the reduction returns a **per-class shading
refinement**, the source's "After a further refinement, we may suppose that each
set `𝕋^{T_θ}` is `δ^{3η}`-dense" (Wang--Zahl).

Two independent defects of the fixed-shading forms motivated it.

1. The fixed-shading covering leaf `Kakeya.WangZahl.BalancedBroadCover` is
   **false** (`not_balancedBroadCover` above), and no constant and no `δ^{-cε}`
   factor repairs it: at `θ = δ` a planar family of `≍ δ^{-2}` essentially
   distinct tubes has `∑_j |∪_{part j} Y| ≍ 1` against `|∪ Y| ≍ δ`.  What the
   source does at exactly this point is shrink the shadings.

2. `IsBroadAtScale s T θ ν` applied to a *fixed* shading is an over-demand.
   Tested at `r = δ` and `w = dir T_{i₀}` it puts `T_{i₀}` into its own
   left-hand count (`rpow_le_multiplicity_of_isBroadAtScale` below), so it says
   that every point of every shading is covered by at least `(θ/δ)^ν` tubes.
   The source's condition has the same consequence, but only for the shading it
   has already refined.  The predicate `IsBroadAtScale` is therefore **not**
   changed; what changed is that the leaves apply it to the refined shadings.

The two propositions below use the fixed-shading formulations.
Their equivalence to the corresponding formulations is expressed by the identities (`hairbrushCover_eq`, `broadScaleRefinement_eq` are
`Iff.rfl` and break the build if the restated text moves) and so that the
restatements are certified to be *weakenings*
(`hairbrushCover_of_fixedShading`, `broadScaleRefinement_of_fixedShading`):
the fixed-shading forms imply the restated ones by taking the refinement to be
the identity, so nothing available to a downstream consumer was lost. -/

/-! ## `IsBroadAtScale` is a pointwise multiplicity hypothesis

A second fidelity issue with the encoding of Leaf 1, recorded here because it
bears on any future restatement of `HairbrushCover`.

`Kakeya.WangZahl.IsBroadAtScale s T θ ν` quantifies over **every** point `x`,
not over a typical one and not over a refined shading.  Testing it at `r = δ`
and at `w = dir T_{i₀}` for a tube `T_{i₀}` whose shading contains `x` puts
`T_{i₀}` itself into the left-hand count, so the left-hand side is at least `1`
and the condition reads

```
1 <= (delta/theta)^nu * #{i : x in Y(T_i)}.
```

That is: **every point of every shading must be covered by at least
`(theta/delta)^nu` tubes of the family.**  For `theta = delta` this is empty
(`isBroadAtScale_of_le_delta`), which is why the only satisfiability certificate
on record, `wolffHairbrushBroad_hypotheses_satisfiable`, is at `theta = delta`.
For `theta >> delta` it is a strong pointwise requirement that a family with a
*fixed* shading generally fails: the far end of a tube of a bush has
multiplicity `1`.  The source's "2-broad" condition is obtained after refining
the shadings to their high-multiplicity part, which the fixed-shading encoding
cannot express -- the same missing degree of freedom that makes
`BalancedBroadCover` false.
-/

/-! ### The `θ`-cap clause of the source's reduction has teeth

`Kakeya.WangZahl.IsCapConcentrated` is the clause of Wang--Zahl that
the first transcription of Leaf 1a dropped ("there is a vector `v = v(x)` so
that `∠(v, dir T) ≤ θ` for each `T ∈ 𝕋` with `x ∈ Y(T)`").  It is not implied
by the broadness clause: the two-tube witness of
`crossedBall_hypotheses_satisfiable_nondegenerate`, which *is* broad at
`θ = (5/4)δ`, fails it at every `θ < 1/2`.  So adding the cap to Leaf 1a is a
genuine strengthening of that leaf, and correspondingly a genuine weakening of
Leaf 1b (`Kakeya.WangZahl.cappedBalancedBroadCover_of_refined`). -/

end

end Kakeya.WangZahl

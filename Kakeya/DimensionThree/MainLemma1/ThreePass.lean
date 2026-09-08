/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Repair

/-!
# Main Lemma 1, Case (ii): Step 2 of the repair, the three passes (R2) → (R1) → (R2)

Blueprint `lem:ml1bootRepairThreePass`.  Move (R1) is
`Kakeya.ml1Boot.exists_repairEssDistinct`, stated and proved in
`Kakeya/DimensionThree/MainLemma1/Repair.lean`.  Move (R2) has **no** Lean statement: its former
one was deleted as refuted, see below.

**The assembly itself is not written**, and this docstring used to describe it as though it
were.  There is no `Kakeya.ml1Boot.exists_repairThreePass` and no
`Kakeya.ml1Boot.exists_repairUniformDiscard` anywhere in the project; where those names appear
in this file they name the *intended* declarations, not existing ones.  What the file actually
contains is the target bundle, the device the assembly would run, and the side facts its call
site needs:

* two exponent identities, `Kakeya.ml1Boot.nnrealPow_mul_self` and
  `Kakeya.ml1Boot.ennrealPow_neg_three`;
* the conclusion bundle `Kakeya.ml1Boot.IsRepairThreePass`;
* the post-selection trim `Kakeya.ml1Boot.exists_trimmedPass`, which is proved and which is what
  produces the fibrewise empty-or-share clause of that bundle;
* the bridging devices for the Case (ii) call site, from
  `Kakeya.ml1Boot.gridScale_le_gridScale` to `Kakeya.ml1Boot.eventually_rpow_le_quarter`.

## The premise the assembly would rest on is refuted

**Move (R2) is false.**  Its negation is proved, in
`Kakeya/DimensionThree/MainLemma1/Repair.lean`, as
`Kakeya.ml1Boot.not_exists_repairUniform`: the pass hypothesises nothing about the shadings
while concluding a positive lower bound on them at a leaf set its own clauses force nonempty, so
an all-empty shading contradicts it.  The statement has accordingly been deleted, and its
blueprint environment carries no `\leanok`.

An assembly that uses the bare (R2) pass twice therefore cannot establish the intended
conclusion. Move (R1) is unaffected.

**A second obstruction to (R2).** The pass has another defect, recorded in the docstring of
`Kakeya.ml1Boot.card_shadeClass_le_card_shadeClass` in
`Kakeya/DimensionThree/MainLemma1/Repair.lean`:
`Kakeya.ml1Boot.IsRepairUniformPass.unif` asserts uniformity
at the shading the pass is handed, and no hypothesis removes that, because uniformity is produced
only after *shrinking* the shading.  A repaired pass therefore returns a shading of its own, and
then this assembly is not reusable verbatim: two of its three passes are (R2), so the leaf shading
is shrunk twice, and three things here read the shading and not merely the index set — the two
refinement links composed by `ShadedBody.IsCRefinement.trans`, which would compose across three
distinct shadings; the weight and bracket arguments that read the *frozen* banding clause of
`Kakeya.ml1Boot.IsCaseTwoInput`, which is stated at the input shading and would not cover the
output; and `Kakeya.ml1Boot.IsRepairThreePass.unif`, which would be delivered at the twice-shrunk
shading.  Whether to pay that or to weaken `unif` at the source is an open design decision about
this assembly.

## Why the order is (R2) → (R1) → (R2), and why there are three passes and not two

Uniformity is not inherited by subfamilies.  Move (R1) *consumes* a uniform shaded family, so it
cannot run first; and it *deletes leaves*, so the uniformity it consumed does not survive it
either, while `Kakeya.ml1Boot.IsCaseTwoData.refine_unif` demands the final leaf family be uniform.
Hence a (R2) pass on each side.  Blueprint `note:ml1bootRepairOrderGWZ` records that this diverges
from the source's ordering, and `note:ml1bootRepairEDLeafShadedUniformity` records that the
divergence is what makes the chain statable at all.

## The node outputs of the two (R2) passes are discarded

The three-pass lemma returns move (R1)'s node sets `t'τ = t²τ ⊆ 𝒰'_b` and `t'θ = t¹θ`, not the
last pass's.  Discarding is free on the *upper* side: at a node a pass has dropped no retained
leaf lies, so the retained fine fibre there is empty and every upper Frostman bound holds at it
for nothing — `Kakeya.ml1Boot.fibre_eq_empty_of_notMem` and
`Kakeya.ml1Boot.fibreFrostman_of_mapsTo`.  That is what the intended
`Kakeya.ml1Boot.exists_repairUniformDiscard` would package: one (R2) pass, its node output
dropped, its fibrewise transport extended from the nodes it kept to *every* node.  The three-pass
proof would then make exactly three citations — that lemma twice and (R1) once — plus one call of
`Kakeya.ml1Boot.fibreFrostman_chain`.

Why the discard is worth making: it puts the whole of Case (ii)'s residual obligation on **one**
application of `Kakeya.ml1Boot.exists_essDistinct_parentFamily`, at an index set cut out of the
full node family `𝒰'_b` directly, rather than on a composite of three deletions two of which are
pigeonhole uniformizations that could not respect coarse fibres even in principle.  That obligation
is the fibrewise empty-or-share dichotomy `Kakeya.ml1Boot.IsFibrewiseEmptyOrShare`; blueprint
`note:ml1bootEssDistinctFibrewiseShare` is its record.

The trim construction supplies the fibrewise empty-or-share dichotomy.

## What the discard costs, and it is exactly one thing

The output node sets may contain nodes carrying *no* retained leaf: `t'τ` is (R1)'s and the third
pass deletes leaves after it, so a `k ∈ t'τ` need have no `i ∈ s₀` with `pτ i = k`.  Item (c) of
the blueprint lemma — here `Kakeya.ml1Boot.IsRepairThreePass.parentFine` — asserts the containment
`{pτ i : i ∈ s₀} ⊆ t'τ` and **not** its converse, and the analogue of
`Kakeya.ml1Boot.IsCoarseNodeParents.nodes_carry_leaf` at `(t'τ, s₀)` is therefore *not* available
downstream and must not be assumed from the input bundle having it at `(𝒰'_b, s')`.  Nothing in
the conclusion needs it: the fibrewise item is an *upper* bound, the essential-distinctness items
are conditions on pairs, and the containments are one-sided by design.

## No middle bound appears, in the hypotheses or the conclusion

Move (R1) is the only step that deletes a `τ`-node from the output, and it does not control what
survives inside a coarse fibre, so there is nothing for a middle clause to transport.  See
`Kakeya.ml1Boot.frostmanConstIn_retainedFibre_le` for the half of that item which *is* proved, and
blueprint `note:ml1bootEssDistinctFibrewiseShare` for the half which is not.  The fibrewise item
(e) below is at the **fine** fibres of `pτ`, a different statement, and it is transported by all
three passes.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ConvexSpaceBody Filter Topology

namespace Kakeya

namespace ml1Boot

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### Two exponent identities

The three-pass tally is `ε' + ε' = 2 ε'` on the refinement side and `-ε' - ε' - ε' = -3 ε'` on the
fibre side.  Both are pure `rpow` arithmetic, and both are stated separately here rather than
inlined, because the assembly below is otherwise plumbing and this is the only place in it where a
side condition on `δ` is read. -/

/-- **The conclusions of `Kakeya.ml1Boot.exists_repairThreePass`, one field per clause**
(blueprint `lem:ml1bootRepairThreePass`, items (a)–(e)).

Here `(𝕋, Y)` is the family of shaded `δ`-tubes indexed by the input leaf set `s'`, `(tτ, 𝕋_τ, pτ)`
and `(tθ, 𝕋_θ, pθ)` are the two ambient node parent families, `s₂` is where the first two passes
end and `s₀` where the third does, and `t'τ`, `t'θ` are move (R1)'s node sets.

*Why `s₂` is a parameter and not only `s₀`.*  The two chains
`Kakeya.ml1Boot.repairFullnessChain` and `Kakeya.ml1Boot.repairCountChain` are three-link chains
`s → s' → s₂ → s₀`, and the middle link is the composite of the first two passes; `s₂` is where
that composite ends, so it has to be visible.  The outer link `s → s'` is the caller's — the two
accuracy-carrying clauses of `Kakeya.ml1Boot.IsCaseTwoInput` — and is deliberately not read here:
this lemma is the passes and nothing else. -/
structure IsRepairThreePass {ι κ : Type*} [DecidableEq κ] {δ τ θ : ℝ≥0} (ε' : ℝ)
    (T : ι → ShadedTube δ E) (Tτ : κ → Tube τ E) (pτ : ι → κ) (Tθ : κ → Tube θ E) (pθ : κ → κ)
    (tτ tθ : Finset κ) (s' s₂ s₀ : Finset ι) (t'τ t'θ : Finset κ) : Prop where
  /-- (f) **The fibrewise empty-or-share dichotomy at the retained fine node set**
  (`Kakeya.ml1Boot.IsFibrewiseEmptyOrShare`), at the share `δ ^ (6 ε')`.

  This is the clause `Kakeya.ml1Boot.exists_caseTwoData` needs and that nothing used to supply:
  at every coarse node of `tθ`, the fibre of `t'τ` is either empty or carries a
  `δ ^ (6 ε')`-share of the fibre of the *ambient* fine node set `tτ`.  It is produced by the
  post-selection trim `Kakeya.ml1Boot.fibrewiseTrim`, run inside the proof between move (R1) and
  the third pass — the only point at which (R1)'s own weight retention and the first pass's count
  retention are both in scope.

  The exponent is `6 ε'` because the consumer reads this structure at `ε' = ε'_outer / 8` and asks
  for the share at `δ ^ (3 ε'_outer / 4) = δ ^ (6 ε')`.  The trim supplies a *larger* share and
  `Kakeya.ml1Boot.IsFibrewiseEmptyOrShare.mono_share` weakens it to this one.

  The ambient node sets `tτ`, `tθ` are structure parameters rather than a hierarchy: the dichotomy
  is a statement about two `Finset`s and a map, so this structure stays free-standing even though
  the theorem producing it no longer is. -/
  dichotomy : IsFibrewiseEmptyOrShare tτ tθ t'τ pθ ((δ : ℝ≥0∞) ^ (6 * ε'))
  /-- (a) The composite of the first two passes is a `δ ^ (2 ε')`-refinement. -/
  refineMid : ShadedBody.IsCRefinement s₂ (fun i => (T i).toShadedBody) s'
    (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ (2 * ε'), by positivity⟩
  /-- (a) …and the third pass is a `δ ^ ε'`-refinement on top of it. -/
  refineLast : ShadedBody.IsCRefinement s₀ (fun i => (T i).toShadedBody) s₂
    (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ ε', by positivity⟩
  /-- (a) The third pass retains all but a `δ ^ (-ε')` share of the index set.  Stated in `ℝ`,
  which is the spelling `Kakeya.ml1Boot.repairCountChain` reads. -/
  card : (s₂.card : ℝ) ≤ (δ : ℝ) ^ (-ε') * (s₀.card : ℝ)
  /-- (a) `s₂` is nonempty.  This is what the third pass consumes, and it comes from the mass
  retention of the first two together with the assumed positivity of the input shade mass. -/
  nonemptyMid : s₂.Nonempty
  /-- (a) `s₀` is nonempty. -/
  nonemptyLast : s₀.Nonempty
  /-- (b) The final leaf family is uniform, at the dimension-only constant
  `Kakeya.ml1Boot.uniformize.C 3`.  *This is why there are three passes and not two*: move (R1)
  deletes leaves, so the first pass's uniformity does not survive to `s₂`. -/
  unif : Nonempty (ShadedTube.ShadedUniformTubeSet s₀ T (Tube.ssfGridLen δ)
    (uniformize.C 3))
  /-- (c) `(t'τ, 𝕋_τ, pτ)` is a parent family for the retained leaves at scale `τ`.  Its `mapsTo`
  clause is the containment `{pτ i : i ∈ s₀} ⊆ t'τ`; the converse is **false** in general, `t'τ`
  being move (R1)'s and the third pass deleting leaves after it. -/
  parentFine : IsParentFamily s₀ (fun i => (T i).toTube) t'τ Tτ pτ
  /-- (c) `(t'θ, 𝕋_θ, pθ)` is a parent family for the retained `τ`-nodes at scale `θ`. -/
  parentCoarse : IsParentFamily t'τ Tτ t'θ Tθ pθ
  /-- (d) The retained `τ`-nodes are pairwise essentially distinct.  This is move (R1)'s own
  clause read verbatim, with no inheritance step. -/
  essDistinctFine : (t'τ : Set κ).Pairwise
    (fun k l => IsEssentiallyDistinct (Tτ k).carrier (Tτ l).carrier)
  /-- (d) The retained `θ`-nodes are pairwise essentially distinct. -/
  essDistinctCoarse : (t'θ : Set κ).Pairwise
    (fun k l => IsEssentiallyDistinct (Tθ k).carrier (Tθ l).carrier)
  /-- (e) The three passes' fibrewise Frostman transports, composed: the factor is `δ ^ (-3 ε')`,
  one `δ ^ (-ε')` per pass.  The side condition is at the pass's own *input* fibre over `s'`,
  which is what makes `Kakeya.ml1Boot.fibreFrostman_chain` applicable, and the bound is asserted at
  every `k ∈ t'τ` — including the nodes the third pass dropped, where it is free. -/
  fibreFrostman : ∀ k ∈ t'τ, ∀ K : ConvexSpaceBody E,
    (∀ i ∈ fibre s' pτ k, (T i).toConvexSpaceBody ≤ K) →
    frostmanConstIn (fibre s₀ pτ k) (fun i => (T i).toConvexSpaceBody) K
      ≤ (δ : ℝ≥0∞) ^ (-3 * ε')
        * frostmanConstIn (fibre s' pτ k) (fun i => (T i).toConvexSpaceBody) K

/-! ### Bridging devices for the Case (ii) call site

`Kakeya.ml1Boot.exists_caseTwoDataRepair` applies the three-pass lemma at the node families of a
hierarchy, and nine small facts stand between its hypotheses and the three-pass hypotheses.  Each
is two lines and none of them existed; they are collected here rather than at their subject matter
because each is used exactly once, at that call site.

The last three close the remaining places where a hypothesis would otherwise have to be massaged
inline at that call site, which is what this section exists to prevent.
`Kakeya.ml1Boot.sum_shade_pos_of_fullness_ge` takes the fullness bound in the shape
`Kakeya.ml1Boot.IsCaseFamily.fullness` actually has — a `δ`-power lower bound in `ENNReal`, not
the `NNReal` positivity that `Kakeya.ml1Boot.sum_shade_pos_of_fullness_pos` asks for;
`Kakeya.ml1Boot.nonempty_of_sum_shade_pos` supplies `s'.Nonempty`, the one three-pass hypothesis
for which the Case (ii) bundle offers no field at all; and
`Kakeya.ml1Boot.eventually_rpow_le_quarter` absorbs, into the eventual smallness of `δ`, the two
side conditions `δ ≤ 1` and `(δ : ℝ) ^ (ε' / 4) ≤ 1 / 4` that the Case (ii) chain lemmas carry —
a statement about the filter `δ → 0⁺` rather than about the passes.

*What is still missing after these nine is not a lemma but a hypothesis.*
`Kakeya.ml1Boot.isParentFamily_nodes_fine` asks for
`Set.InjOn (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody) (𝒰'.cover.indexSet b)`, and nothing in
the Case (ii) input supplies it: `Tube.UniformTubeSet.tube_injOn` gives injectivity of
`k ↦ 𝒰'.cover.tube b k` as a *tube*, which is strictly weaker, `Tube` carrying two endpoint fields
beyond its body.  It is needed by the *conclusion* as well, through
`Kakeya.ml1Boot.IsCaseTwoRepairData.parentFine`, so it is not an artefact of this route and cannot
be routed around.  At the coarse index it is free, being
`Kakeya.ml1Boot.IsCoarseNodeParents.parent.injOn`; at the fine index it must become a hypothesis of
`Kakeya.ml1Boot.exists_caseTwoDataRepair`. -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Bounded overlap weakens in the constant**.

This is a *companion* of blueprint `lem:ml1bootBoundedOverlapMono` and not a part of it: that
lemma restricts the two index sets at a **fixed** constant, and its three parts are the
parent-family clause and the two restrictions.  Weakening the constant is a fourth statement, and
it is stated separately so that no `\lean` tag claims one for the other.

In Lean it is the companion of `Kakeya.ml1Boot.HasBoundedOverlap.mono_leaves`.  It is what lets a
caller holding
the hierarchy's own overlap constant `C_ds`, which carries no lower bound, feed
`Kakeya.ml1Boot.exists_repairThreePass`, whose overlap parameter is asked to be at least `1`: run
the three-pass at `max 1 C_ds` and weaken. -/
theorem HasBoundedOverlap.mono_const {ι κ : Type*} {σ ρ : ℝ≥0} {s : Finset ι}
    {V : ι → Tube σ E} {t : Finset κ} {Vρ : κ → Tube ρ E} {Co Co' : ℝ≥0}
    (h : HasBoundedOverlap s V t Vρ Co) (hCo : Co ≤ Co') :
    HasBoundedOverlap s V t Vρ Co' :=
  fun W => le_trans (h W) hCo

/-- **A `c`-refinement is a `c'`-refinement for every smaller `c'`.**

`ShadedBody.IsCRefinement` bounds the retained shade mass *below* by `c` times the input's, so
lowering `c` weakens the assertion.  The Case (ii) chain lemmas
`Kakeya.ml1Boot.repairFullnessChain` and `Kakeya.ml1Boot.repairCountChain` each ask for their three
links at one common exponent, while the three passes deliver them at `ε'`, `2 ε'` and `ε'`; this is
what brings them to the common one. -/
theorem isCRefinement_mono {ι : Type*} {s u : Finset ι} {V' V : ι → ShadedBody E} {c c' : ℝ≥0}
    (h : ShadedBody.IsCRefinement u V' s V c) (hc : c' ≤ c) :
    ShadedBody.IsCRefinement u V' s V c' := by
  exact ⟨h.1, le_trans (mul_le_mul' (ENNReal.coe_le_coe.mpr hc) le_rfl) h.2⟩

/-! ### The three-pass assembly in banded / ED-up-to-multiplicity form

What follows is **additive**: `Kakeya.ml1Boot.IsRepairThreePass` above is untouched, and so is
its consumer `Kakeya.ml1Boot.caseTwoRepairData_of_isRepairThreePass`.  The assembly below lands
in a **new** record, `Kakeya.ml1Boot.IsRepairThreePassThreaded`, because two clauses of the old
one are not deliverable by any route available today; the differences are declared on that
structure rather than smuggled in.

The three passes are `Kakeya.ml1Boot.exists_repairUniformDiscard_banded` (twice) and
`Kakeya.ml1Boot.exists_repairEssDistinct_edUpToMult` (once), plus one call of
`Kakeya.ml1Boot.exists_trimmedPass` between the second and third.  Both citations carry
hypotheses the bare blueprint statements did not:

* the (R2) discard needs the **input band**, because the bare (R2) is refuted
  (`Kakeya.ml1Boot.not_exists_repairUniform`);

* the (R1) pass used here reads body-level `Kakeya.IsEDUpToMult` multiplicity of the two node
  families at a fixed `Co : ℕ`, in place of the leaf-mediated `Kakeya.ml1Boot.HasBoundedOverlap`
  of `Kakeya.ml1Boot.exists_essDistinct_parentFamily`. **Those two hypotheses have no supplier
  in this development**, and fixed-multiplicity essential distinctness of node families is in
  general false — `Kakeya.ml1Boot.not_exists_essDistinct_parentFamily`'s axial pencil produces
  `≍ ρ ⁻¹` pairwise non-essentially-distinct parents. A supplier would have to give a
  `δ`-dependent multiplicity. -/

/-- **The conclusions of the banded three-pass assembly** — the output-shading form of
`Kakeya.ml1Boot.IsRepairThreePass`, minus its fibrewise clause.

A **new** structure; `Kakeya.ml1Boot.IsRepairThreePass` is untouched above.  Relative to it:

* the extra parameter `Y₃ : ι → ShadedTube δ E` is the third pass's own output shading, with the
  new containment field `shadeTube`, and `unif` reads at `Y₃`.  Uniformity at a *handed* shading
  is undeliverable — see `Kakeya.ml1Boot.card_shadeClass_le_card_shadeClass` — so this is the
  minimal threading that lets the clause be produced at all.  Every other field still reads at
  the input shading `T`, including `refineMid` and `refineLast`, whose mass lower bounds
  transfer from `Y₃` to `T` for free along `(Y₃ i).shade ⊆ (T i).shade`.

* there is **no** `fibreFrostman` field.  `Kakeya.ml1Boot.IsRepairThreePass.fibreFrostman`
  composes the three passes' fibrewise Frostman transports at `δ ^ (-3 ε')`; the banded (R2)
  pass does not deliver its own factor (see
  `Kakeya.ml1Boot.IsRepairUniformPassThreaded`), so the composite is unavailable and is not
  claimed.  It stays an hypothesis on any consumer of this record — which is why
  `Kakeya.ml1Boot.caseTwoRepairData_of_isRepairThreePass`, which reads
  `Kakeya.ml1Boot.IsRepairThreePass.fibreFrostman`, is deliberately *not* rewritten against this
  record. -/
structure IsRepairThreePassThreaded {ι κ : Type*} [DecidableEq κ] {δ τ θ : ℝ≥0} (ε' : ℝ)
    (T : ι → ShadedTube δ E) (Tτ : κ → Tube τ E) (pτ : ι → κ) (Tθ : κ → Tube θ E) (pθ : κ → κ)
    (tτ tθ : Finset κ) (s' s₂ s₀ : Finset ι) (t'τ t'θ : Finset κ)
    (Y₃ : ι → ShadedTube δ E) : Prop where
  /-- (a) The third pass's output shading `Y₃` shades the same tubes as `T`, with shades
  contained in `T`'s, on the retained leaf set `s₀`. -/
  shadeTube : ∀ i ∈ s₀, (Y₃ i).toTube = (T i).toTube ∧ (Y₃ i).shade ⊆ (T i).shade
  /-- (f) The fibrewise empty-or-share dichotomy at the retained fine node set, at the share
  `δ ^ (6 ε')`; produced by `Kakeya.ml1Boot.exists_trimmedPass`, run between move (R1) and the
  third pass. -/
  dichotomy : IsFibrewiseEmptyOrShare tτ tθ t'τ pθ ((δ : ℝ≥0∞) ^ (6 * ε'))
  /-- (a) The composite of the first two passes is a `δ ^ (2 ε')`-refinement. -/
  refineMid : ShadedBody.IsCRefinement s₂ (fun i => (T i).toShadedBody) s'
    (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ (2 * ε'), by positivity⟩
  /-- (a) …and the third pass is a `δ ^ ε'`-refinement on top of it. -/
  refineLast : ShadedBody.IsCRefinement s₀ (fun i => (T i).toShadedBody) s₂
    (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ ε', by positivity⟩
  /-- (a) The third pass retains all but a `δ ^ (-ε')` share of the index set. -/
  card : (s₂.card : ℝ) ≤ (δ : ℝ) ^ (-ε') * (s₀.card : ℝ)
  /-- (a) `s₂` is nonempty. -/
  nonemptyMid : s₂.Nonempty
  /-- (a) `s₀` is nonempty. -/
  nonemptyLast : s₀.Nonempty
  /-- (b) The final leaf family is uniform at `Kakeya.ml1Boot.uniformize.C 3`, **at the third
  pass's output shading `Y₃`**. -/
  unif : Nonempty (ShadedTube.ShadedUniformTubeSet s₀ Y₃ (Tube.ssfGridLen δ)
    (uniformize.C 3))
  /-- (c) `(t'τ, 𝕋_τ, pτ)` is a parent family for the retained leaves at scale `τ`. -/
  parentFine : IsParentFamily s₀ (fun i => (T i).toTube) t'τ Tτ pτ
  /-- (c) `(t'θ, 𝕋_θ, pθ)` is a parent family for the retained `τ`-nodes at scale `θ`. -/
  parentCoarse : IsParentFamily t'τ Tτ t'θ Tθ pθ
  /-- (d) The retained `τ`-nodes are pairwise essentially distinct. -/
  essDistinctFine : (t'τ : Set κ).Pairwise
    (fun k l => IsEssentiallyDistinct (Tτ k).carrier (Tτ l).carrier)
  /-- (d) The retained `θ`-nodes are pairwise essentially distinct. -/
  essDistinctCoarse : (t'θ : Set κ).Pairwise
    (fun k l => IsEssentiallyDistinct (Tθ k).carrier (Tθ l).carrier)

end ml1Boot

end Kakeya

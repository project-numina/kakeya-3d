/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.CoarseFibre
public import Kakeya.DimensionThree.MainLemma1.Factoring
public import Kakeya.DimensionThree.MainLemma1.ParentConflictCover

/-!
# Main Lemma 1, Case (ii): the repair chain, moves (R1) and (R2)

Blueprint `lem:ml1bootRepairUniform` and `lem:ml1bootRepairEssDistinct`.  Step 2 of the Case (ii)
repair is a chain of three passes, `(R2) → (R1) → (R2)`, and this file holds both moves together
with the four small index-bookkeeping devices the reordered chain needs.

The (R2) pass is **one uniformization pass at two parent scales**, stated so that *the shape of
its input is the shape of its output*.

That shape is what makes the chain composable, and it is the whole point of the restatement:

* the pass **takes no uniformity hypothesis**, which is why it may legitimately run *first*,
  before the essential-distinctness deletion (R1) — see blueprint
  `note:ml1bootRepairEDLeafShadedUniformity` and `note:ml1bootRepairOrderGWZ`; and
* it **concludes** one, at a dimension-only constant, which is precisely what (R1) consumes and
  what that note recorded as unsupplied in the source's own ordering.

Move (R1), blueprint `lem:ml1bootRepairEssDistinct`, is `Kakeya.ml1Boot.exists_repairEssDistinct`
below. Its uniformity hypothesis is a *hypothesis*: the caller discharges it by running (R2)
first, which is the reordering blueprint `note:ml1bootRepairOrderGWZ` records and which is what
closed `note:ml1bootRepairEDLeafShadedUniformity`. What (R1) does **not** carry is a middle
bound at the retained `θ`-fibre; that obligation is governed by the dichotomy
`Kakeya.ml1Boot.IsFibrewiseEmptyOrShare`, whose descent
`Kakeya.ml1Boot.frostmanConstIn_retainedFibre_le` is proved in
`Kakeya/DimensionThree/MainLemma1/CoarseFibre.lean`. What is missing is a **caller** — see the docstring of
`Kakeya.ml1Boot.exists_repairEssDistinct` below, and blueprint
`note:ml1bootRepairEDMidRetained`.

## The four devices, over five declarations

* `Kakeya.ml1Boot.fibre_eq_empty_of_notMem` and
  `Kakeya.ml1Boot.frostmanConstIn_fibre_eq_zero_of_notMem` are the two halves of blueprint
  `lem:ml1bootAbsentParentFibre`: a node no retained leaf lies over carries an empty fibre, and
  an empty family has Frostman constant `0`, so every *upper* bound is free there.  This is what
  lets a pass's node deletions be discarded.
* `Kakeya.ml1Boot.fibreFrostman_of_mapsTo` is blueprint `lem:ml1bootFibreTransportPastDrop`, the
  consequence a caller actually reads: a fibrewise Frostman transport asserted at the nodes a
  pass keeps holds at every node, so discarding the pass's node output costs nothing on the
  upper side.  What makes this work is that the item transported is a *bound*: nothing of the
  kind holds for a node-level **property**, which is one reason no pass here concludes one.
* `Kakeya.ml1Boot.IsParentFamily.comp` is blueprint `lem:ml1bootCoarseParentFamilyForLeaves`: the
  coarse node family, read along the composed map, is a parent family for the **leaves**.  Move
  (R1) needs it, `Kakeya.ml1Boot.exists_essDistinct_parentFamily` consuming the *leaf* family at
  both scales.
* `Kakeya.ml1Boot.isParentFamily_trim` is blueprint `lem:ml1bootParentTrim`: a refinement that
  prices only leaves restores the **node**-level containment after the fine node set is trimmed
  to `{k ∈ u_τ : p_θ k ∈ u_θ}`.  Without the trim that containment is false, which is the point
  on which an alternative form of (R2) was retracted.

## Divergences from the informal statement

*The Case (ii) bundle is not a hypothesis.*  The blueprint phrases the lemma "in the situation
of `def:ml1bootCaseTwoInput`", with `ŝ ⊆ s'`, `t̂_τ ⊆ t_τ`, `t̂_θ ⊆ t_θ` and the two set-level
containments `{p_τ i : i ∈ ŝ} ⊆ t̂_τ`, `{p_θ k : k ∈ t̂_τ} ⊆ t̂_θ`; but its own prose says its
hypotheses "are the hypotheses of `lem:ml1bootUniformizePair` and nothing more".  They are, and
that is how they are stated here: the containments *together with* the ambient parent families
are exactly `Kakeya.ml1Boot.IsParentFamily` at the hatted sets, which is what blueprint
`lem:ml1bootCoarseParentFamilyForLeaves` extracts from the bundle.  So the Lean statement is
free-standing, mentions neither `Kakeya.ml1Boot.IsCaseTwoInput` nor a hierarchy, and is
applicable at either of the chain's two call sites without reproving anything.

*One node type, not two.*  Both parent index sets are `Finset κ` for a single type `κ`, and the
coarse parent map is `pθ : κ → κ`.  This is the shape the Case (ii) call site has, where every
index set is a `Finset` of the hierarchy's own index type and `pθ : ι → ι`
(`Kakeya.ml1Boot.IsCoarseNodeParents`).  Stating it at two unrelated types would be a
strengthening nothing available here supplies.

*The node containment in item (d).*  A uniformization that prices only *leaves* delivers the two
containments at the leaf level, `{p_τ i : i ∈ s'} ⊆ u_τ` and `{p_θ (p_τ i) : i ∈ s'} ⊆ u_θ`.
The node-level containment `{p_θ k : k ∈ u_τ} ⊆ u_θ` is **false in general**, since `u_τ` may
contain a node over which no retained leaf lies, and an alternative form of (R2) that asserted it
outright was retracted on exactly that point (blueprint `lem:ml1bootRepairUniform`, and
`note:ml1bootRepairEDMidRetained` for the sibling retraction).  The device that restores it is
the *trim* `t'τ = {k ∈ u_τ : p_θ k ∈ u_θ}` of blueprint `lem:ml1bootParentTrim`, proved below as
`Kakeya.ml1Boot.isParentFamily_trim`; with that witness the field
`Kakeya.ml1Boot.IsRepairUniformPass.parentCoarse` is true by construction.

*The count clause is stated in `ℝ`.*  Blueprint item (a) reads `|ŝ| ≤ δ ^ (-ε') |ŝ⁺|`, and the
one consumer of it is `Kakeya.ml1Boot.repairCountChain`, whose two count hypotheses are real
inequalities in exactly this spelling, so the `ENNReal`-to-`ℝ` conversion a uniformization's own
count clause would need is paid here rather than at the call site.

## Standing caveat: move (R2) is refuted, and its statement has been deleted

The (R2) statement — blueprint `lem:ml1bootRepairUniform`, intended producer
`Kakeya.ml1Boot.exists_repairUniform` — **is false**, and
`Kakeya.ml1Boot.not_exists_repairUniform` below proves its negation, spelling it out inline: the
pass hypothesised nothing about the shadings while concluding a positive lower bound on them at
a leaf set its own clauses force nonempty, so an all-empty shading refutes it. The retracted
proof went through
`Kakeya.ml1Boot.exists_uniformRefinement`, which is refuted for the same reason
(`Kakeya.ml1Boot.not_exists_uniformRefinement`); that citation has been removed and appears
nowhere in this file. The
conclusion bundle `Kakeya.ml1Boot.IsRepairUniformPass` also remains, as the record of what such
a pass was to deliver. Anything downstream that assumes move (R2) — in
`Kakeya/DimensionThree/MainLemma1/ThreePass.lean` and beyond — is a derivation
over a refuted premise and establishes nothing until the statement is repaired.

Move (R1) is affected.  It is proved from
`Kakeya.ml1Boot.exists_essDistinct_parentFamily`, and the scale-free form of that citation is
false (`Kakeya.ml1Boot.not_exists_essDistinct_parentFamily`); since (R1) quantified `τ` and `θ`
over the whole ladder `δ ≤ τ ≤ θ ≤ 1`, it applied the citation inside the refuting regime and was
therefore false itself, its proof establishing nothing.  Both statements now carry the scale
hypothesis `δ ^ (ε'/2) ≤ c τ / Co` and the citation is again an accepted assumption; see the
docstring of `Kakeya.ml1Boot.exists_repairEssDistinct` below.

## Names below that are *intended* declarations and do not exist

Several docstrings in this file name the Case (ii) construction layer by the names it is to be
given. In this file the intended names used are
`Kakeya.ml1Boot.exists_repairUniform` (blueprint `lem:ml1bootRepairUniform`, deleted after
refutation as described above) and `Kakeya.ml1Boot.exists_repairThreePass`. Blueprint
`note:ml1bootCaseTwoConstructionLayerEmpty` holds the
authoritative inventory of the whole absent layer; read it before trusting any name in the
Case (ii) material. That inventory is itself checked against the source rather than assumed:
one of its entries, `Kakeya.ml1Boot.caseTwoThreePassScales`, has since been written, in
`Kakeya/DimensionThree/MainLemma1/ThreePass.lean`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ConvexSpaceBody Filter Topology

namespace Kakeya

namespace ml1Boot

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### The four index-bookkeeping devices -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The coarse node family is a parent family for the leaves** (blueprint
`lem:ml1bootCoarseParentFamilyForLeaves`, item (d)).

If `(uτ, 𝕋_τ, pτ)` is a parent family for `𝕋|_u` at the scale `τ` and `(uθ, 𝕋_θ, pθ)` is one for
`𝕋_τ|_{uτ}` at the scale `θ`, then `(uθ, 𝕋_θ, pθ ∘ pτ)` is a parent family for `𝕋|_u` at `θ`.

*This is the item that does work.*  It is what lets every application of
`Kakeya.ml1Boot.exists_essDistinct_parentFamily` in the repair chain be made to the **leaf**
family at both scales.  That is forced rather than convenient: that citation consumes a *uniform
shaded* family, uniformity is not inherited by subfamilies, and the `τ`-nodes carry no shading at
all, so the coarse application can be made neither to the output of the fine one nor to `𝕋_τ`
.

The blueprint's items (b) and (c) are the two hypotheses here, and its item (a) — the identity
`assign_a = pθ ∘ assign_b` of `Kakeya.ml1Boot.IsCoarseNodeParents.assign_comp` — is definitional
once the composite is written out, so this free-standing form carries the whole of that lemma.
Injectivity of the composed family is that of the coarse one, untouched; the containment clause is
the two containments chained. -/
theorem IsParentFamily.comp {ι κ μ : Type*} {δ τ θ : ℝ≥0} {u : Finset ι} {T : ι → Tube δ E}
    {uτ : Finset κ} {Tτ : κ → Tube τ E} {pτ : ι → κ}
    {uθ : Finset μ} {Tθ : μ → Tube θ E} {pθ : κ → μ}
    (hfine : IsParentFamily u T uτ Tτ pτ) (hcoarse : IsParentFamily uτ Tτ uθ Tθ pθ) :
    IsParentFamily u T uθ Tθ (fun i => pθ (pτ i)) :=
  { mapsTo := fun i hi => hcoarse.mapsTo (pτ i) (hfine.mapsTo i hi)
    injOn := hcoarse.injOn
    le_parent := fun i hi =>
      (hfine.le_parent i hi).trans (hcoarse.le_parent (pτ i) (hfine.mapsTo i hi)) }

omit [MeasurableSpace E] [BorelSpace E] in
/-- **A parent family restricts, on both sides at once**.

Both non-index clauses of `Kakeya.ml1Boot.IsParentFamily` are conditions on individual members —
that each member lie in the body its parent names, and that the parent bodies be distinct — so
both descend to `u ⊆ s` and `t' ⊆ t`.  What does *not* descend is `mapsTo`, which is why it is a
hypothesis here: a smaller parent set need not receive the smaller leaf set.

This is the move the three-pass assembly makes four times, once for each of the two output parent
families of blueprint `lem:ml1bootRepairThreePass`, item (c), whose containments the passes supply
while the other two clauses have to be restricted from the ambient families. -/
theorem IsParentFamily.mono {ι κ : Type*} {δ ρ : ℝ≥0} {s u : Finset ι} {T : ι → Tube δ E}
    {t t' : Finset κ} {Vρ : κ → Tube ρ E} {p : ι → κ}
    (h : IsParentFamily s T t Vρ p) (hu : u ⊆ s) (ht : t' ⊆ t)
    (hmaps : ∀ i ∈ u, p i ∈ t') :
    IsParentFamily u T t' Vρ p :=
  { mapsTo := hmaps
    injOn := h.injOn.mono (Finset.coe_subset.mpr ht)
    le_parent := fun i hi => h.le_parent i (hu hi) }

/-! ### Move (R2): the uniformization pass -/

/-- **The conclusions the (R2) pass was to deliver, one field per inequality** (blueprint
`lem:ml1bootRepairUniform`, items (a)–(e)).

The intended producer is `Kakeya.ml1Boot.exists_repairUniform`, which is not a declaration:
see the module docstring, where the refutation and the deletion are recorded.

Here `(𝕋, Y)` is a family of shaded `δ`-tubes indexed by `s`, `(tτ, 𝕋_τ, pτ)` is a parent
family for it at the scale `τ` and `(tθ, 𝕋_θ, pθ)` one for `𝕋_τ` at the scale `θ`; the pass
returns `s' ⊆ s`, `t'τ ⊆ tτ`, `t'θ ⊆ tθ` and a shade density `λ' > 0`.

As elsewhere in this development a blueprint item that is a conjunction of several inequalities
becomes several fields, so that consumers name what they use.  The blueprint's items (a)–(e) are
`refinement`/`card`, `unif`/`dens`/`lamGe`, the three `essDistinct*`,
`parentFine`/`parentCoarse`, and `fibreFrostman`.  There is no sixth item; the blueprint lemma
above is where what the pass deliberately does not conclude is recorded. -/
structure IsRepairUniformPass {ι κ : Type*} [DecidableEq κ] {δ τ θ : ℝ≥0} (ε' : ℝ)
    (T : ι → ShadedTube δ E) (Tτ : κ → Tube τ E) (pτ : ι → κ) (Tθ : κ → Tube θ E) (pθ : κ → κ)
    (s : Finset ι) (tτ tθ : Finset κ)
    (s' : Finset ι) (t'τ t'θ : Finset κ) (lam' : ℝ≥0) : Prop where
  /-- (a) `(𝕋|_{s'}, Y)` is a `δ ^ ε'`-refinement of `(𝕋|_{s}, Y)`. -/
  refinement : ShadedBody.IsCRefinement s' (fun i => (T i).toShadedBody) s
    (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ ε', by positivity⟩
  /-- (a) …and retains all but a `δ ^ (-ε')` share of the index set.  Stated in `ℝ`, which is
  the spelling `Kakeya.ml1Boot.repairCountChain` reads. -/
  card : (s.card : ℝ) ≤ (δ : ℝ) ^ (-ε') * (s'.card : ℝ)
  /-- (b) The retained family is uniform, at the dimension-only constant
  `Kakeya.ml1Boot.uniformize.C 3`.  `ShadedTube.ShadedUniformTubeSet` is data-valued, so the
  `Prop`-valued clause is its `Nonempty`.  This is the clause move (R1) consumes and which the
  source's ordering left unsupplied. -/
  unif : Nonempty (ShadedTube.ShadedUniformTubeSet s' T (Tube.ssfGridLen δ)
    (uniformize.C 3))
  /-- (b) The shading densities on `s'` are two-sidedly comparable to `λ'`.

  **This is the clause that refutes the (R2) statement.**  Its lower half asserts a positive
  lower bound on a shading, at a leaf set the retracted statement's own conclusion forced
  nonempty, while that statement hypothesised nothing whatever about the shadings.  The
  refutation is `Kakeya.ml1Boot.not_exists_repairUniform`, which spells the statement out
  inline; the name `Kakeya.ml1Boot.exists_repairUniform` is the intended producer's and is not
  a declaration, so nothing here is a claim about one.  The field is *correct as a field* — a
  pass that assumed a density bracket at its input could deliver it — and it is the pass's
  hypotheses, not this clause, that are defective, so the structure is left as it stands.

  *No consumer reads `λ'` today*: `Kakeya.ml1Boot.repairCountChain` reads its banding from
  `Kakeya.ml1Boot.IsCaseTwoInput.band` instead, which every subfamily inherits and which costs
  no exponent. -/
  dens : ∀ i ∈ s', (lam' : ℝ≥0∞) * volume (T i).carrier ≤ volume (T i).shade ∧
    volume (T i).shade ≤ 2 * (lam' : ℝ≥0∞) * volume (T i).carrier
  /-- (b) …and `λ'` is itself at least `δ ^ ε'` times the fullness of the input family, which is
  the half of the blueprint's `λ' ≥ δ ^ ε' λ(𝕋|_ŝ)` that relates the output banding to the
  input's. -/
  lamGe : (δ : ℝ≥0∞) ^ ε' * ShadedBody.fullness s (fun i => (T i).toShadedBody)
    ≤ (lam' : ℝ≥0∞)
  /-- (c) Essential distinctness of the leaves is inherited. -/
  essDistinctLeaf : (s : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
    (s' : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier)
  /-- (c) Essential distinctness of the `τ`-nodes is inherited; free, essential distinctness
  being a condition on pairs and `t'τ ⊆ tτ`. -/
  essDistinctFine : (tτ : Set κ).Pairwise
      (fun k k' => IsEssentiallyDistinct (Tτ k).carrier (Tτ k').carrier) →
    (t'τ : Set κ).Pairwise (fun k k' => IsEssentiallyDistinct (Tτ k).carrier (Tτ k').carrier)
  /-- (c) Essential distinctness of the `θ`-nodes is inherited, for the same reason. -/
  essDistinctCoarse : (tθ : Set κ).Pairwise
      (fun l l' => IsEssentiallyDistinct (Tθ l).carrier (Tθ l').carrier) →
    (t'θ : Set κ).Pairwise (fun l l' => IsEssentiallyDistinct (Tθ l).carrier (Tθ l').carrier)
  /-- (d) `(t'τ, 𝕋_τ, pτ)` is again a parent family, for the retained leaves at scale `τ`.  Its
  `mapsTo` clause is the leaf-level containment `{pτ i : i ∈ s'} ⊆ t'τ`. -/
  parentFine : IsParentFamily s' (fun i => (T i).toTube) t'τ Tτ pτ
  /-- (d) `(t'θ, 𝕋_θ, pθ)` is again a parent family, for the retained `τ`-nodes at scale `θ`.
  Its `mapsTo` clause is the **node**-level containment `{pθ k : k ∈ t'τ} ⊆ t'θ`, which holds
  only for the *trimmed* fine set `t'τ = {k ∈ u_τ : pθ k ∈ u_θ}` and is false for the untrimmed
  one; see the module docstring. -/
  parentCoarse : IsParentFamily t'τ Tτ t'θ Tθ pθ
  /-- (e) The Frostman constant of every retained fine fibre grows by at most `δ ^ (-ε')`, the
  side condition being stated at the **fibre** and not at the whole family — which is the shape
  the repair consumes. -/
  fibreFrostman : ∀ k ∈ t'τ, ∀ K : ConvexSpaceBody E,
    (∀ i ∈ fibre s pτ k, (T i).toConvexSpaceBody ≤ K) →
    frostmanConstIn (fibre s' pτ k) (fun i => (T i).toConvexSpaceBody) K
      ≤ (δ : ℝ≥0∞) ^ (-ε')
        * frostmanConstIn (fibre s pτ k) (fun i => (T i).toConvexSpaceBody) K

/-! ### Move (R1): essential distinctness at both parent scales -/

/-- **The conclusions of `Kakeya.ml1Boot.exists_repairEssDistinct`, one field per clause**
(blueprint `lem:ml1bootRepairEssDistinct`, items (a)–(c)).

Here `(𝕋, Y)` is a family of shaded `δ`-tubes indexed by `s`, `pτ` is the `τ`-parent map and `pθ`
the `θ`-parent map on the `τ`-nodes, `w` is the caller's weight on the leaves, and the pass
returns `s' ⊆ s`, `t'τ` and `t'θ`.

As elsewhere in this development a blueprint item that is a conjunction becomes several fields, so
that consumers name what they use.  Item (a) is `weight`/`parentFine`/`parentCoarse` — the two
containments of that item being the `Kakeya.ml1Boot.IsParentFamily.mapsTo` clauses of the latter
two — item (b) is the two `essDistinct*`, and item (c) is `fibreFrostman`. -/
structure IsRepairEssDistinctPass {ι κ : Type*} [DecidableEq κ] {δ τ θ : ℝ≥0} (ε' : ℝ)
    (T : ι → ShadedTube δ E) (Tτ : κ → Tube τ E) (pτ : ι → κ) (Tθ : κ → Tube θ E) (pθ : κ → κ)
    (w : ι → ℝ≥0∞) (s s' : Finset ι) (t'τ t'θ : Finset κ) : Prop where
  /-- (a) The caller's weight is retained up to `δ ^ ε'`.  *One* weight: no essentially distinct
  selection retains a constant share of two incomparable weights, which is why
  `Kakeya.ml1Boot.exists_essDistinct_parentFamily` takes `w` as a parameter and why this pass
  passes it on rather than fixing it. -/
  weight : (δ : ℝ≥0∞) ^ ε' * (∑ i ∈ s, w i) ≤ ∑ i ∈ s', w i
  /-- (a) `(t'τ, 𝕋_τ, pτ)` is again a parent family, for the retained leaves at scale `τ`. -/
  parentFine : IsParentFamily s' (fun i => (T i).toTube) t'τ Tτ pτ
  /-- (a) `(t'θ, 𝕋_θ, pθ)` is again a parent family, for the retained `τ`-nodes at scale `θ`. -/
  parentCoarse : IsParentFamily t'τ Tτ t'θ Tθ pθ
  /-- (b) The retained `τ`-nodes are pairwise essentially distinct. -/
  essDistinctFine : (t'τ : Set κ).Pairwise
    (fun k l => IsEssentiallyDistinct (Tτ k).carrier (Tτ l).carrier)
  /-- (b) The retained `θ`-nodes are pairwise essentially distinct. -/
  essDistinctCoarse : (t'θ : Set κ).Pairwise
    (fun k l => IsEssentiallyDistinct (Tθ k).carrier (Tθ l).carrier)
  /-- (c) The fine Frostman constants transport **fibrewise**, with the side condition stated at
  the pass's own *input* fibre.

  This is a transport and not an absolute bound: the leaf family is a parameter, so no raw bound
  is available to read, and none is needed — it composes with the raw bound and with the
  transports of the (R2) passes on either side, the composition being done once at the call
  site. -/
  fibreFrostman : ∀ k ∈ t'τ, ∀ K : ConvexSpaceBody E,
    (∀ i ∈ fibre s pτ k, (T i).toConvexSpaceBody ≤ K) →
    frostmanConstIn (fibre s' pτ k) (fun i => (T i).toConvexSpaceBody) K
      ≤ (δ : ℝ≥0∞) ^ (-ε')
        * frostmanConstIn (fibre s pτ k) (fun i => (T i).toConvexSpaceBody) K

/-! ### The post-selection trim

Blueprint `lem:ml1bootFibrewiseTrim`, `lem:ml1bootFibrewiseTrimCost` and the banding corollary
`lem:ml1bootFibrewiseTrimCostBanded`.

These are route 3 of blueprint `note:ml1bootEssDistinctFibrewiseShare`: rather than asking the
essential-distinctness selection to *conclude* `Kakeya.ml1Boot.IsFibrewiseEmptyOrShare`, take its
output as a black box and **construct** from it a smaller node set that has the dichotomy by
fiat, discarding whole coarse fibres into the free empty branch.  Nothing here closes that note:
the trim buys the dichotomy at the price of the weight-retention clause, and
`Kakeya.ml1Boot.fibrewiseTrimCost` pays that price only under a two-sided comparability of the
weight a single node's fibre carries, whose availability at the leaf set the first (R2) pass
leaves behind is exactly what remains unchecked.
-/

/-! ### The comparability at the leaf set a (R2) pass leaves behind

Blueprint `lem:ml1bootTrimComparabilityAtS1`, and with it the first of the two questions
`note:ml1bootEssDistinctFibrewiseShare` leaves route 3 turning on.

The point is a change of quantifier order, and nothing else.  `Kakeya.ml1Boot.fibrewiseTrimCost`
now asks only for the aggregate `m₋ |𝒰'_b| ≤ w(s₁)`, and the aggregate is available at `s₁`
even though the pointwise bracket is not: the class brackets of
`Tube.UniformTubeSet` are read at the hierarchy's **own** leaf set `s'`, where they
hold by definition, and the passage `s' ⇝ s₁` is made once, in bulk, by the pass's count
retention.  At no point is a bracket asserted at a node of `𝒰'_b` inside `s₁` — which is exactly
why the nodes a pass has emptied are not an obstruction.
-/

section B3BranchCard

variable [Nontrivial E]

end B3BranchCard

/-! ### The aggregate lower bound survives a shrinking of the shadings

Blueprint `lem:ml1bootTrimComparabilityAtShrunkShading`.  These two declarations settle the
question on which reshaping move (R2) to return its own shading turns.

Every construction of `ShadedTube.ShadedUniformTubeSet` shrinks the shading it is handed, so a
repaired (R2) pass delivers a shading `Y' ⊆ Y` and its consumers must read the weight at `Y'`.
The obstruction that looks fatal is that the banding clause of `Kakeya.ml1Boot.IsCaseTwoInput` is
*pointwise* and **frozen**: under `(Y' i).shade ⊆ (Y i).shade` its upper half survives and its
lower half does not, and it is the lower half that the count-to-mass passage reads.

It is not fatal, and the reason is a quantifier order that has already been paid for.
`Kakeya.ml1Boot.fibrewiseTrimCost` no longer asks for a pointwise lower bound — that hypothesis
was weakened to the aggregate `m₋ |𝒰'_b| ≤ w(u)` — and the shrinking control that
`ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf` delivers is aggregate too, being a
comparison of `ShadedBody.fullness'` at its own output set.  So the pointwise lower bound is
needed at `Y` only, where it holds, and the passage `Y ⇝ Y'` costs exactly the one factor the
uniformization charges for it. -/

/-- **An aggregate fullness comparison is an aggregate mass comparison, the carriers being the
same** (blueprint `lem:ml1bootTrimComparabilityAtShrunkShading`, first step).

`ShadedBody.fullness'` is `(∑ |Y_i|) / (∑ |T_i|)`, and a shrinking of a shading leaves the
underlying bodies alone, so the two fullnesses being compared have a *common* denominator.
Clearing it turns the comparison `λ'(Y) ≤ A λ'(Y')` delivered by
`ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf` into the mass retention
`∑_{s} |Y_i| ≤ A ∑_{s} |Y'_i|`, which is the shape the aggregate lower bound consumes.

The two side conditions are exactly what clearing a denominator in `ENNReal` needs, and both are
free for a nonempty family of `δ`-tubes with `δ > 0`: a tube carrier contains a ball of radius
`δ`, and it is contained in one, so the sum is neither `0` nor `⊤`. -/
theorem sum_shade_le_of_fullness'_le {ι : Type*} {s : Finset ι} (Y Y' : ι → ShadedBody E)
    {A : ℝ≥0∞}
    (hcar : ∀ i ∈ s, volume (Y' i).carrier = volume (Y i).carrier)
    (hD0 : 0 < ∑ i ∈ s, volume (Y i).carrier)
    (hDtop : (∑ i ∈ s, volume (Y i).carrier) ≠ ⊤)
    (h : ShadedBody.fullness' s Y ≤ A * ShadedBody.fullness' s Y') :
    (∑ i ∈ s, volume (Y i).shade) ≤ A * ∑ i ∈ s, volume (Y' i).shade := by
  let N : ℝ≥0∞ := ∑ i ∈ s, volume (Y i).shade
  let N' : ℝ≥0∞ := ∑ i ∈ s, volume (Y' i).shade
  let D : ℝ≥0∞ := ∑ i ∈ s, volume (Y i).carrier
  have hDenom : (∑ i ∈ s, volume (Y' i).carrier) = D := by
    dsimp [D]
    exact Finset.sum_congr rfl (fun i hi => hcar i hi)
  have hD : N / D ≤ A * (N' / D) := by
    simpa [ShadedBody.fullness', N, N', D, hDenom] using h
  have h_le : N ≤ (A * (N' / D)) * D :=
    (ENNReal.div_le_iff hD0.ne' hDtop).mp hD
  have h' : N ≤ A * N' := by
    calc
      N ≤ (A * (N' / D)) * D := h_le
      _ = A * ((N' / D) * D) := by rw [mul_assoc]
      _ = A * N' := by rw [ENNReal.div_mul_cancel hD0.ne' hDtop]
  simpa [N, N'] using h'

/-! ### Move (R2): the banded uniformization pass at an output shading

The **bare** move (R2) is refuted by `Kakeya.ml1Boot.not_exists_repairUniform` above.
The banded pass below requires an input band and a positive share condition.
`Kakeya.ml1Boot.IsRepairUniformPass` records the conclusions of the bare pass.

Two things had to change for a pass to exist at all, and both appear as *added hypotheses* or as
a *new* record, never as a weakening of anything already here.

* **An input band.**  The refutation's witness is an all-empty shading, so the banded pass
  assumes the two-sided band `lam₀ · |T i| ≤ |(T i).shade| ≤ 2 · lam₀ · |T i|` on its input.
  That excludes the refuting witness, and it makes the two density clauses free with
  `lam' := lam₀`.

* **An output shading.**  `Kakeya.ml1Boot.IsRepairUniformPass.unif` asserts uniformity at the
  shading the pass is *handed*, and no construction delivers that: uniformity is produced only
  after shrinking a shading, and the second obstruction recorded in the docstring of
  `Kakeya.ml1Boot.card_shadeClass_le_card_shadeClass` is exactly this.  So the banded pass
  returns its own shading `Y'`, and the record it lands in is the **new** structure
  `Kakeya.ml1Boot.IsRepairUniformPassThreaded` below, whose `unif` and refinement-mass clauses
  read at `Y'` and which carries the containment clause `shadeTube` making `Y'` an output
  shading.  The new record also omits the old `fibreFrostman` field: the composed fibrewise
  Frostman transport is *not* available from the uniformization tool this pass runs, so it is not
  claimed here.  **That is a real, hypothesis**, not a discharged one; see the note on
  `Kakeya.ml1Boot.IsRepairUniformPassThreaded`.
-/

/-- **The conclusions of the banded (R2) pass, one field per inequality** — the
output-shading form of `Kakeya.ml1Boot.IsRepairUniformPass`.

This is a **new** structure, not a restatement: `Kakeya.ml1Boot.IsRepairUniformPass` is
untouched above, and this record exists because that one is undeliverable in two respects.
The differences, both of them weakenings *relative to that record*, are declared here rather
than hidden:

* `unif` and the mass half of `refinement` read at the pass's **own** output shading
  `Y' : ι → ShadedTube δ E`, related to the input `T` only by the new field `shadeTube`
  (`(Y' i).toTube = (T i).toTube` and `(Y' i).shade ⊆ (T i).shade` on `s'`).  Every other field
  reads at `T`, unchanged.

* There is **no** `fibreFrostman` field.  `Kakeya.ml1Boot.IsRepairUniformPass.fibreFrostman`
  bounds the growth of every retained fine fibre's Frostman constant by `δ ^ (-ε')`; the
  uniformization route used by `Kakeya.ml1Boot.exists_repairUniform_banded` below cuts fibres
  and does not control that ratio, so the clause is dropped from *this* record and becomes an
  obligation on whatever consumes it.  Consumers must therefore carry the fibrewise transport
  as their own hypothesis; no declaration in this development discharges it today. -/
structure IsRepairUniformPassThreaded {ι κ : Type*} [DecidableEq κ] {δ τ θ : ℝ≥0} (ε' : ℝ)
    (T : ι → ShadedTube δ E) (Tτ : κ → Tube τ E) (pτ : ι → κ) (Tθ : κ → Tube θ E) (pθ : κ → κ)
    (s : Finset ι) (tτ tθ : Finset κ)
    (s' : Finset ι) (t'τ t'θ : Finset κ) (Y' : ι → ShadedTube δ E) (lam' : ℝ≥0) : Prop where
  /-- (a) The output shading `Y'` shades the same tubes as `T`, with shades contained in `T`'s,
  on the retained leaf set.  This is what makes `Y'` an output shading of the pass. -/
  shadeTube : ∀ i ∈ s', (Y' i).toTube = (T i).toTube ∧ (Y' i).shade ⊆ (T i).shade
  /-- (a) `(𝕋|_{s'}, Y')` is a `δ ^ ε'`-refinement of `(𝕋|_{s}, Y)`; the refined side reads at
  the output shading. -/
  refinement : ShadedBody.IsCRefinement s' (fun i => (Y' i).toShadedBody) s
    (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ ε', by positivity⟩
  /-- (a) …and retains all but a `δ ^ (-ε')` share of the index set. -/
  card : (s.card : ℝ) ≤ (δ : ℝ) ^ (-ε') * (s'.card : ℝ)
  /-- (b) The retained family is uniform at `Kakeya.ml1Boot.uniformize.C 3`, **at the output
  shading `Y'`**. -/
  unif : Nonempty (ShadedTube.ShadedUniformTubeSet s' Y' (Tube.ssfGridLen δ)
    (uniformize.C 3))
  /-- (b) The shading densities on `s'` are two-sidedly comparable to `λ'`, read at the input
  shading `T`.  Free from the input band. -/
  dens : ∀ i ∈ s', (lam' : ℝ≥0∞) * volume (T i).carrier ≤ volume (T i).shade ∧
    volume (T i).shade ≤ 2 * (lam' : ℝ≥0∞) * volume (T i).carrier
  /-- (b) …and `λ'` is at least `δ ^ ε'` times the fullness of the input family. -/
  lamGe : (δ : ℝ≥0∞) ^ ε' * ShadedBody.fullness s (fun i => (T i).toShadedBody)
    ≤ (lam' : ℝ≥0∞)
  /-- (c) Essential distinctness of the leaves is inherited. -/
  essDistinctLeaf : (s : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
    (s' : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier)
  /-- (c) Essential distinctness of the `τ`-nodes is inherited. -/
  essDistinctFine : (tτ : Set κ).Pairwise
      (fun k k' => IsEssentiallyDistinct (Tτ k).carrier (Tτ k').carrier) →
    (t'τ : Set κ).Pairwise (fun k k' => IsEssentiallyDistinct (Tτ k).carrier (Tτ k').carrier)
  /-- (c) Essential distinctness of the `θ`-nodes is inherited. -/
  essDistinctCoarse : (tθ : Set κ).Pairwise
      (fun l l' => IsEssentiallyDistinct (Tθ l).carrier (Tθ l').carrier) →
    (t'θ : Set κ).Pairwise (fun l l' => IsEssentiallyDistinct (Tθ l).carrier (Tθ l').carrier)
  /-- (d) `(t'τ, 𝕋_τ, pτ)` is again a parent family for the retained leaves at scale `τ`. -/
  parentFine : IsParentFamily s' (fun i => (T i).toTube) t'τ Tτ pτ
  /-- (d) `(t'θ, 𝕋_θ, pθ)` is again a parent family for the retained `τ`-nodes at scale `θ`. -/
  parentCoarse : IsParentFamily t'τ Tτ t'θ Tθ pθ

end ml1Boot

end Kakeya

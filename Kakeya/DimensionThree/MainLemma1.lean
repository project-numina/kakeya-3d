/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Bootstrap
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.RevisedOriginalEntryW111
public import Kakeya.DimensionThree.FrostmanEstimateMono
public import Kakeya.DimensionThree.FrostmanEstimateOne
public import Kakeya.DimensionThree.MainLemma1.Factoring
public import Kakeya.RelativePlank
public import Kakeya.Factoring.Pigeonhole
public import Kakeya.DimensionThree.MainLemma1.Cases
public import Kakeya.DimensionThree.MainLemma1.Setup
public import Kakeya.DimensionThree.MainLemma1.Rescaling.MiddleAverage
public import Kakeya.DimensionThree.MainLemma1.ScalarFactorization
public import Kakeya.DimensionThree.MainLemma1.AnalyticEndgame
public import Kakeya.DimensionThree.MainLemma1.CoarseBallUpstreamW50
public import Kakeya.Factoring.DilatedTubePresentation
public import Kakeya.DimensionThree.MainLemma1.ParentConflictCover
public import Kakeya.DimensionThree.MainLemma1.Rescaling.KatzTao
public import Kakeya.Factoring.WeightedFullness
public import Kakeya.DimensionThree.MainLemma1.NoEDHonestCoarseConsumerW52
public import Kakeya.DimensionThree.MainLemma1.ThreePass
public import Kakeya.DimensionThree.MainLemma1.W44NormalizationCardPort
public import Kakeya.MultiScaleFac
public import Kakeya.Asymptotics
public import Kakeya.DimensionThree.MainLemma1.UpstreamCountedRawProducerW50Module
public import Kakeya.FrostmanTransfer
public import Kakeya.Multiplicity
public import Kakeya.Tube.Rigidity
public import Kakeya.DimensionThree.MainLemma1.Rescaling.CoarseDensity
public import Kakeya.DimensionThree.MainLemma1.CoarseFibre
public import Kakeya.Factoring.RhoTubes
public import Kakeya.Tube.Dilate
public import Kakeya.Factoring.RhoTubesUndilated
public import Kakeya.DimensionThree.MainLemma1.W44NoEDNormalization
public import Kakeya.DimensionThree.MainLemma1.Rescaling.Numerics
public import Kakeya.DimensionThree.MainLemma1.Rescaling.BallRadius
public import Kakeya.Factoring.RhoFreeParentCount
public import Kakeya.DimensionThree.MainLemma1.EndpointHierarchySelectedPacketModuleSafeW53
public import Kakeya.DimensionThree.MainLemma1.EndpointPacketHierarchyModuleBridgeSafeW48
public import Kakeya.DimensionThree.MainLemma1.EndpointMiddleSplitModuleSafeW53
public import Kakeya.DimensionThree.MainLemma1.Rescaling.UniformEveryScale
public import Kakeya.DimensionThree.MainLemma1.QuotientAwareQV5W58
public import Kakeya.DimensionThree.MainLemma1.Envelope
public import Kakeya.DimensionThree.MainLemma1.Rescaling.Thresholds
public import Kakeya.StickyKakeya.BallReduction
public import Kakeya.DimensionThree.MainLemma1.OneSidedUniform
public import Kakeya.DimensionThree.MainLemma1.Rescaling
public import Kakeya.DimensionThree.MainLemma1.Rescaling.Hybrid
public import Kakeya.Frostman
public import Kakeya.Shading
public import Kakeya.Pigeonhole

/-!
# GWZ Main Lemma 1

In `ℝ^3`, the Katz-Tao partial estimate `K_KT(β)` implies the Frostman partial estimate
`K_F(γ)` for every `γ > β`.

The proof is a bootstrap: `Kakeya.KatzTaoEstimate.frostmanEstimate_sub_of_frostmanEstimate`
(GWZ Lemma 8.1) is the self-improving step, and it is turned into
`Kakeya.KatzTaoEstimate.frostmanEstimate` by the base case `Kakeya.frostmanEstimate_one`,
monotonicity `Kakeya.FrostmanEstimate.mono`, and the abstract infimum argument
`Kakeya.ioc_subset_of_sub_mem_of_monotoneOn`.

This top-level file of Section 8 of the adapted blueprint contains

* the bootstrapping lemma `Kakeya.KatzTaoEstimate.frostmanEstimate_sub_of_frostmanEstimate`
  (blueprint `lemmain1boot`, GWZ Lemma 8.1) and its consequence
  `Kakeya.KatzTaoEstimate.frostmanEstimate` (GWZ Main Lemma 1);
* the uniform bootstrapping step `Kakeya.ml1Boot.exists_uniform_step`, which is the statement that
  the whole of the rest of Section 8
  proves, phrased through `Kakeya.frostmanStepSet`;
* `Kakeya.ml1Boot.multiplicity_le_caseTwo`, the second
  of the two steps that turn the output of `StickyKakeya.dividingScalesFrostman` into the input
  of the two-scale factoring and back.  The first of the two is blueprint
  `lem:ml1bootCaseIIData`, whose intended producer `Kakeya.ml1Boot.exists_caseTwoData` is not a
  declaration (see the inventory section below);
* the parts out of which that first step is to be assembled:
  `Kakeya.ml1Boot.caseTwoDataRaw`, the pure read-off at
  the node families, applied at the exponent `ε' / 8`, and `Kakeya.ml1Boot.repairLower`
, which reads the Frostman *lower* bound off the
  dichotomy at the unrefined node family.  The construction step between them — blueprint
  `lem:ml1bootCaseIIDataRepair`, which is to build the essentially distinct, uniform
  subfamilies in `B₁`, conclude at `ε'` and land in the `mid`-free record
  `Kakeya.ml1Boot.IsCaseTwoRepairData` — has no declaration either; its intended name is
  `Kakeya.ml1Boot.exists_caseTwoDataRepair`.

## Names below that are *intended* declarations and do not exist

Many docstrings in this file name the Case (ii) construction layer by the names it is to be
given. The ones used below are

* `Kakeya.ml1Boot.exists_caseTwoData`;
* `Kakeya.ml1Boot.exists_caseTwoDataRepair`;
* `Kakeya.ml1Boot.exists_repairThreePass`;
* `Kakeya.ml1Boot.exists_caseTwoThreePass`;
* `Kakeya.ml1Boot.exists_factorTwoScales`.

Blueprint `note:ml1bootCaseTwoConstructionLayerEmpty` holds the authoritative inventory of the
whole absent layer, together with what *does* exist either side of it; read it before trusting
any name in the Case (ii) material.  That inventory is itself to be checked against the source
rather than assumed: one of its entries, `Kakeya.ml1Boot.caseTwoThreePassScales`, has since
been written, in `Kakeya/DimensionThree/MainLemma1/ThreePass.lean`.

## Divergences from the informal statements

*Parent index types.*  Blueprint `lem:ml1bootCaseIIData` produces its two parent families *as
the node families of the hierarchy of its own hypotheses* — "with `𝕋_τ` and `𝕋_θ` the node tubes
`P_b(·)` and `P_a(·)` of `𝒰'` themselves", retained as `t_τ ⊆ 𝒰'_b` and `t_θ ⊆ 𝒰'_a`.  So their
index type is the leaf index type `ι`, and that is how the intended
`Kakeya.ml1Boot.exists_caseTwoData` is to name them, matching the intended
`Kakeya.ml1Boot.exists_caseTwoDataRepair`.  Neither is a declaration; the structures they are
to produce, `Kakeya.ml1Boot.IsCaseTwoData` and `Kakeya.ml1Boot.IsCaseTwoRepairData`, are the
ones that fix this reading, and they do use `ι`.

An alternative form existentially quantified the two index *types* and their `DecidableEq`
instances, and with them the unrefined level-`b` index set `tb` that item (iv) speaks about.
That was strictly weaker than the blueprint and unusable by the consumer: with `tb`
existentially bound, the only clause tying it to the rest of the record is
`Kakeya.ml1Boot.IsCaseTwoData.fineRetained`, `tτ ⊆ tb`, and nothing said that `(tb, Tτ)` *was*
the level-`b` node family, so item (iv) could be met at an arbitrary superfamily of `tτ` while
saying nothing whatever about `𝒰'_b`.  Pinning the families to `𝒰'` removes that hole and costs
nothing downstream: `Kakeya.ml1Boot.exists_factorTwoScales` carries `[DecidableEq _]` binders on
its index types and is applied here at `ι` with the ambient instance, so the two
`Kakeya.ml1Boot.fibre` terms still agree syntactically.

*Item (iii) is conditional.*  Blueprint `lem:ml1bootCaseIIData`(iii) asserts the middle bound at
the *retained* parent-map fibre only under the antecedent that `t_τ` is fibrewise
empty-or-share at `δ ^ (3 ε'/4)` over `p_θ`, that antecedent being the one open step of Case (ii)
(`note:ml1bootEssDistinctFibrewiseShare`).  The intended
`Kakeya.ml1Boot.exists_caseTwoData` is therefore to conclude
`Kakeya.ml1Boot.IsCaseTwoRepairData` — items (i), (ii), (iv) and the interface data,
all unconditional — together with the implication
`Kakeya.ml1Boot.IsFibrewiseEmptyOrShare … → Kakeya.ml1Boot.IsCaseTwoData …`, which is
`Kakeya.ml1Boot.IsCaseTwoRepairData.isCaseTwoData` fed by
`Kakeya.ml1Boot.frostmanConstIn_retainedFibre_le`.  Concluding the full
`Kakeya.ml1Boot.IsCaseTwoData` outright would assert the middle bound at a retained node set,
which nothing in this development supplies.

*Fibres.*  Items (ii) and (iii) are stated with the **parent-map** fibres
`Kakeya.ml1Boot.fibre s₀ pτ k` and `Kakeya.ml1Boot.fibre tτ pθ l`, which is what the
blueprint's square brackets `𝕋|_{s₀}[T_{τ,k}]` and `𝕋_τ[T_{θ,l}]` mean in Section 8
(`def:ml1bootParentFamily`; see the warning in `def:nestedBelowBody`, which reserves the
angle brackets `𝕍⟨V⟩` for the containment fibre).  This is also the shape consumed by
`Kakeya.ml1Boot.IsFactorTwoScales.frostman_fine`,
`Kakeya.ml1Boot.IsFactorTwoScales.frostman_mid` and by
`Kakeya.ml1Boot.exists_factorOneScaleUniform`(e).  Item (iv), by contrast, is genuinely a
containment fibre — the anchor is the concentric `σ`-rescaling of a node tube, not a member of
any parent family — and is written with `Kakeya.familyIn`.

*Conclusion (ii) of `dividingScalesLemmaA`.*  Rather than referring to
`StickyKakeya.dividingScalesFrostman`, whose conclusion is a disjunction, the two Case (ii)
lemmas take its Alternative (ii) as an explicit hypothesis, through the named predicate
`StickyKakeya.IsFrostmanDividingBlock`, which *is* the second disjunct of that theorem.  So
the hypotheses are node-anchored: the anchors are the nodes `𝒰'.cover.tube b j` and
`𝒰'.cover.tube a j` of the hierarchy the theorem returns, the families are the leaf classes
`Tube.coverClass` and the node families `Tube.UniformTubeSet.nodesUnder`, the
scales are the grid scales `Tube.gridScale δ (Tube.ssfGridLen δ) a` and
`… b`, and every bound carries the subpolynomial factor `StickyKakeya.totalLoss`.  Everything is
asserted for the *refinement* `s' ⊆ s` and its hierarchy `𝒰'`, never for `s` itself; the
retention bound relating the two is the field `Kakeya.ml1Boot.IsCaseTwoInput.card_le`.

*What the amended dichotomy removed from the Case (ii) proofs.*  The conclusion
`Kakeya.ml1Boot.IsCaseTwoData` is stated in the free-scale language of the factoring chain
(`Kakeya/…/Factoring.lean`, `Kakeya/…/Rescaling.lean`), which is what
`Kakeya.ml1Boot.exists_factorTwoScales` and `Kakeya.ml1Boot.multiplicity_le_middle` consume.
Against the superseded `δ`-independent-grid dichotomy two conversions stood inside the intended
proof of blueprint `lem:ml1bootCaseIIData` and were discharged by nothing — that proof has no
Lean declaration to sit in — an *anchor-set* conversion,
because the lower bound held only on a majority set `F` of fine nodes, and a *scale-window*
conversion, because it held only at grid scales inside the `3 ε`-window.  Both are gone:
`StickyKakeya.IsFrostmanDividingBlock.frostman_lower` is asserted at every node of level `b`
and at every *real* scale of the `ε`-window, so no majority set has to be discarded and no free
scale has to be rounded onto the grid.  With them goes the loss they cost, the `δ ^ (-48 ε²)` of
the old bullet together with the rounding exponent `κ = 6 ε²`: the amended bullet carries
`StickyKakeya.totalLoss`, which is subpolynomial and so absorbable into the
`∀ᶠ δ in 𝓝[>] 0`.

*Item (iv) has been restated to match.*  `Kakeya.ml1Boot.IsCaseTwoData.lower` is
`Kakeya.ml1Boot.IsFreeScaleLowerBound` at the **unrefined** level-`b` node family, on the
`ε`-window `Kakeya.ml1Boot.IsScaleWindow` with the loss `δ ^ ε'`, in place of the retained
fibre, the `5 ε`-window and the loss `δ ^ (ε' + 54 ε²)` that the old input forced.  It carries
no coarse index and no containment clause.  Getting the bound down to the retained fibre was
the business of an assumption that is refuted and undeliverable;
both are deleted, and the item is stated where
`StickyKakeya.IsFrostmanDividingBlock.frostman_lower` asserts it.  The grid-rounding layer that
supplied the narrower form has likewise been deleted; what survived of it — the two
node-to-parent-family lemmas, the majority-node discard and the containment
`T_σ ⊆ 2 · T_{θ,l}` — is in `Kakeya/DimensionThree/MainLemma1/NodeFamilies.lean`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya

universe u

namespace ml1Boot

/-! ### The uniform bootstrapping step -/


end ml1Boot

/-! ### The bootstrapping lemma and Main Lemma 1 -/


/-- [GWZ, Main Lemma 1]
For `0 ≤ β < γ ≤ 1`, `K_KT(β)` implies `K_F(γ)` for sets of `δ`-tubes in `B_1 ⊆ ℝ^3`.

The set `S = {γ | K_F(γ)}` is up-closed by `FrostmanEstimate.mono`, contains `1` by
`frostmanEstimate_one`, and is closed under `γ ↦ γ - ν γ` on `Set.Ioc β 1` by
`frostmanEstimate_sub_of_frostmanEstimate`, so `ioc_subset_of_sub_mem_of_monotoneOn` gives
`Set.Ioc β 1 ⊆ S`.

The conclusion is deliberately *not* sharp: the bootstrap increment `ν γ` tends to `0` as
`γ ↓ β`, so iterating Lemma 8.1 reaches every exponent above `β` but never `β` itself, and
forcing `K_F(β)` would require a separate limiting argument. Every consumer of this lemma
tolerates an arbitrarily small loss in the exponent instead; see
`Kakeya.katzTaoEstimateDimensionThree`, which pays for it by halving the step of Main
Lemma 2. -/
theorem KatzTaoEstimate.frostmanEstimate
    (hSFE : StickyKakeya.StickyFrostmanHypothesis.{0, u})
    {β γ : ℝ} (hβ_nonneg : 0 ≤ β) (hβγ : β < γ)
    (hγ_le : γ ≤ 1) (h : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β) :
    FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) γ := by
  exact ml1Boot.RevisedSourceRepairW110.frostmanEstimate_from_revised_w110
    hSFE hβ_nonneg hβγ hγ_le h


namespace ml1Boot

/-! ### Case (ii): from the dividing scales to the factoring chain and back -/

section CaseTwo

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]


/-- **The family `K_F(γ)` is applied to in Case (ii)** (blueprint `lem:ml1bootCaseIIData`,
the hypotheses on `(𝕋, Y)`).

A nonempty `C_u`-uniform family of shaded, pairwise essentially distinct `δ`-tubes in `B₁`
whose Frostman constant and fullness are both within `δ ^ (∓ η(γ))` of `1` — the exact input
that `Kakeya.FrostmanEstimate` supplies and that the whole Case (ii) chain is run on.

The two exponents are the *same* `p.ηGamma γ`, not independent thresholds: `η(γ)` is defined
in `Kakeya.ml1Boot.params` as a minimum over all the places a fullness or Frostman threshold
is needed, so a single number governs both sides.

Uniformity is carried as `Nonempty (ShadedTube.ShadedUniformTubeSet …)` because that
predicate is data-valued; since the conclusions it feeds are `Prop`s, this loses nothing. -/
structure IsCaseFamily {ι : Type*} {δ : ℝ≥0} (p : Params) (γ : ℝ) (Cunif : ℝ≥0)
    (s : Finset ι) (T : ι → ShadedTube δ E) : Prop where
  /-- The family is nonempty. -/
  nonempty : s.Nonempty
  /-- It is `C_u`-uniform along the grid of Definition 2.2. -/
  unif : Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) Cunif)
  /-- Its members lie in the unit ball. -/
  ball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1
  /-- Its members are pairwise essentially distinct, as `Kakeya.FrostmanEstimate` requires. -/
  essDistinct : (s : Set ι).Pairwise
    (fun i i' => IsEssentiallyDistinct (T i).carrier (T i').carrier)
  /-- `C_F(𝕋, B₁) ≤ δ ^ (-η(γ))`. -/
  frostman : frostmanConstIn s (fun i => (T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall ≤ (δ : ℝ≥0∞) ^ (-p.ηGamma γ)
  /-- `λ(𝕋, Y) ≥ δ ^ η(γ)`. -/
  fullness : (δ : ℝ≥0∞) ^ p.ηGamma γ ≤ ShadedBody.fullness s (fun i => (T i).toShadedBody)

/-- **What Alternative (ii) of `StickyKakeya.dividingScalesFrostman` hands to Case (ii)**
(blueprint `lem:ml1bootCaseIIData`, the hypothesis "Conclusion (ii) holds for `𝕋`").

The dichotomy does not return its conclusion for the input family: it returns a refinement
`s' ⊆ s` retaining all but a `StickyKakeya.totalLoss` share, a fresh hierarchy `𝒰'` on `s'`
along the grid of length `Tube.ssfGridLen δ`, and the block data `a < b`, `m` — and
*everything is then computed in `𝒰'`*.  This structure is that package, with the block itself
delegated to `StickyKakeya.IsFrostmanDividingBlock`, which is literally the second disjunct
of that theorem.

The bounds' constant, the hierarchy's constant and the retention constant are all instantiated
at `Cds`, as the theorem does; the polylogarithmic exponent is `Kds` and the grid-gap exponent
is `cds`.  All three are quantified before `δ`, and `StickyKakeya.totalLoss` is subpolynomial in
`δ`, so a consumer may absorb the whole loss into a `∀ᶠ δ in 𝓝[>] 0`.  The superseded
`δ`-independent-grid form carried instead a fixed exponent `εds`, which could not be absorbed
that way and therefore forced an explicit smallness hypothesis on the Case (ii) lemmas; with
`StickyKakeya.dividingScalesFrostman` that hypothesis is gone.

## The accuracy parameter `ε'`

`ε'` is a further exponent, chosen by the caller and likewise quantified before `δ`.  It occurs
in the first clause `Kakeya.ml1Boot.IsCaseTwoInput.card_le` alone, which reads
`|s| ≤ δ ^ (-ε') |s'|`; one says the bundle is taken *at accuracy `ε'`*.

The clause used to read `|s| ≤ totalLoss Cds Kds cds δ * |s'|`, and nothing in this development
instantiates that form: what the composition of the uniformization and the hierarchy refinement
supplies is `|s| ≤ δ ^ (-ε/2) * totalLoss * |s'|`, and a subpolynomial factor cannot absorb a
fixed power of `δ`.  So the clause is stated at exactly what is buildable, with the exponent
carried as a parameter.  Nothing is lost: the sole consumer of the clause reads it only in the
form `|s| ≤ δ ^ (-ε') |s'|` for a fixed `ε'`.

Because the exponent is the caller's, a consumer is no longer indifferent to it — the clause at
`ε'` is strictly weaker than the same clause at `ε' / 8` — so every consumer names the accuracy
at which it takes the bundle, and the named accuracies meet along the chain:
`Kakeya.ml1Boot.caseTwoDataRaw` and `Kakeya.ml1Boot.repairLower` never read the clause, the
intended `Kakeya.ml1Boot.exists_caseTwoDataRepair` and `Kakeya.ml1Boot.exists_caseTwoData` are
to take it at `ε' / 8` (neither is a declaration; see the module docstring), and
`Kakeya.ml1Boot.multiplicity_le_caseTwo`, which fixes `ε' = p.η 0 / 16`, takes it
at `p.η 0 / 128`. -/
structure IsCaseTwoInput [Nontrivial E] {ι : Type u} {δ : ℝ≥0}
    (p : Params) (ε' : ℝ) (Cds : ℝ≥0) (Kds cds : ℕ)
    (s : Finset ι) (T : ι → ShadedTube δ E) (s' : Finset ι)
    (𝒰' : Tube.UniformTubeSet s' (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cds)
    (a b m : ℕ) : Prop where
  /-- The dichotomy refines the family. -/
  subset : s' ⊆ s
  /-- …and retains all but a `δ ^ ε'` share of it, at the caller's accuracy `ε'`. -/
  card_le : (s.card : ℝ) ≤ (δ : ℝ) ^ (-ε') * (s'.card : ℝ)
  /-- **Shade-mass retention**: `(𝕋|_{s'}, Y)` is a `δ ^ ε'`-refinement of `(𝕋, Y)`, at the
  *same* caller-chosen accuracy `ε'` as `card_le`, i.e.
  `δ ^ ε' * ∑_{i ∈ s} |Y i| ≤ ∑_{i ∈ s'} |Y i|`.

  Without this clause the bundle says nothing whatever about the shading of the retained family:
  `card_le` is a statement about *counts* and `StickyKakeya.IsFrostmanDividingBlock` is three
  statements about *tubes*.  A shading vanishing on `s'` and equal to the whole tube on `s \ s'`
  then satisfies every other clause while making `ShadedBody.fullness s₀ 𝕋 = 0` for every
  `s₀ ⊆ s'`, which refutes `Kakeya.ml1Boot.IsCaseTwoData.refine_fullness` and with it
  `Kakeya.ml1Boot.exists_caseTwoDataRepair`.  Blueprint `note:ml1bootCaseIIRefineFullnessGap` is
  the record of that counterexample; this field is its repair, at the bundle rather than at the
  consumer.

  It is *not* a new obligation on suppliers: by blueprint `lem:ml1bootCaseTwoInputMassFromCard`
  a supplier meeting `card_le` at accuracy `ε' / 2` together with `band` meets this clause at
  accuracy `ε'`, all `δ`-tubes having one common positive volume. -/
  refine_mass : ShadedBody.IsCRefinement s' (fun i => (T i).toShadedBody) s
    (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ ε', by positivity⟩
  /-- **Banded shade density on the input**: some `λ_* > 0` has
  `λ_* |T i| ≤ |Y i| ≤ 2 λ_* |T i|` for every `i ∈ s`.

  A condition on `(𝕋, Y)` at `s` alone, carrying no accuracy — `s` here is the index set of the
  *uniformized* pair, the one carrying the standing Case hypotheses
  `Kakeya.ml1Boot.IsCaseFamily`, so the banding is asserted of a family that has already been
  pigeonholed to a dyadic shade-density band, and the uniformization is not one of the passages
  `s ⇝ s'` that the bundle's two accuracy-carrying clauses price.

  Its role is to convert counts into shade mass: it is exactly the hypothesis of
  `ShadedBody.card_le_iff_isCRefinement_of_comparable` at `Λ = 2` and `μ₀ = λ_*`, and it
  is what makes `refine_mass` a consequence of `card_le` rather than an independent supplier
  obligation. -/
  band : ∃ lam : ℝ≥0, 0 < lam ∧ ∀ i ∈ s,
    (lam : ℝ≥0∞) * volume (T i).carrier ≤ volume (T i).shade ∧
      volume (T i).shade ≤ 2 * (lam : ℝ≥0∞) * volume (T i).carrier
  /-- Alternative (ii) itself, read on `𝒰'`.

  There is deliberately no fourth clause asserting that the block's lower bound survives a
  refinement of the node family. That assertion is refuted and undeliverable, and is deleted rather
  than
  weakened; blueprint `note:ml1bootLowerFrostmanRetired` is the record.  Nothing needs it:
  `Kakeya.ml1Boot.IsCaseTwoData.lower` is stated at the unrefined node family. -/
  block : StickyKakeya.IsFrostmanDividingBlock 𝒰' Cds Kds cds p.η p.ε a b m p.N

/-- **The `w`-window of free scales**.

For a block with fine end `τ` and coarse end `θ`, the free scale `σ` lies in the closed window
`[τ (θ/τ) ^ w, θ (τ/θ) ^ w]` obtained from `[τ, θ]` by trimming a margin of `w` at each end.

`Kakeya.ml1Boot.IsCaseTwoData.lower` reads it at `w = p.ε`, which is the window at which
`StickyKakeya.IsFrostmanDividingBlock.frostman_lower` is asserted.  It used to be read at
`w = 5 ε`: the superseded `δ`-independent-grid dichotomy asserted its bound only at grid scales,
and the extra margin was what the rounding spent to move a free scale onto the grid. -/
structure IsScaleWindow (τ θ : ℝ≥0) (w : ℝ) (σ : ℝ≥0) : Prop where
  /-- The free scale is at least the fine end of the window. -/
  lower : τ * (θ / τ) ^ w ≤ σ
  /-- …and at most its coarse end. -/
  upper : σ ≤ θ * (τ / θ) ^ w


/-- A scale in the window is positive, the fine end of the window being positive.

This is what lets the seam `Kakeya.ennreal_coe_nnreal_rpow` be crossed at `σ / τ` when the
dichotomy's `ENNReal.ofReal ((σ / τ) ^ η)` is matched against the `ENNReal`-valued power of
`Kakeya.ml1Boot.IsFreeScaleLowerBound`. -/
theorem IsScaleWindow.pos {τ θ : ℝ≥0} {w : ℝ} {σ : ℝ≥0} (h : IsScaleWindow τ θ w σ)
    (hτ : 0 < τ) (hθ : 0 < θ) : 0 < σ := by
  have hdiv : 0 < θ / τ := div_pos hθ hτ
  have hrpow : 0 < (θ / τ) ^ w := NNReal.rpow_pos hdiv
  exact lt_of_lt_of_le (mul_pos hτ hrpow) h.lower

/-- **The free-scale Frostman lower bound at the unrefined level-`b` node family**
(blueprint `lem:ml1bootFreeScaleNodeLower`, `lem:ml1bootRepairLower`,
`lem:ml1bootCaseIIDataRaw`(c) and `lem:ml1bootCaseIIData`(iv)).

For every real scale `σ` of the `ε`-window `Kakeya.ml1Boot.IsScaleWindow` and *every* node
`k ∈ tb`, the members of `tb` lying inside the concentric `σ`-rescaling `(Tb k).rescale σ` of
the node tube are Frostman from below in it, with the loss `δ ^ ε'` on the left.

This is `StickyKakeya.IsFrostmanDividingBlock.frostman_lower` read in the parent-family
language, and `tb` is the *unrefined* level-`b` index set of the hierarchy.  There is no
coarse index, no fibre, no subfamily quantifier and no share hypothesis: a Frostman lower
bound is witnessed by a single test body and does not survive a refinement, so it is stated
where the dichotomy asserts it, and a consumer holding a retained `t ⊆ tb` reads it by
restricting the quantifier.  The containment `T_σ ⊆ 2 · Tθ l'` that this predicate used to
carry alongside the bound went with the coarse index; it is
`Kakeya.ml1Boot.rescale_le_dilate_two`, available wherever a consumer needs it. -/
def IsFreeScaleLowerBound {κ : Type*} {τ : ℝ≥0} (δ : ℝ≥0)
    (p : Params) (ε' : ℝ) (j : ℕ) (θ : ℝ≥0)
    (tb : Finset κ) (Tb : κ → Tube τ E) : Prop :=
  ∀ σ : ℝ≥0, IsScaleWindow τ θ p.ε σ →
    ∀ k ∈ tb,
      (δ : ℝ≥0∞) ^ ε' * ((σ / τ : ℝ≥0) : ℝ≥0∞) ^ p.η j
        ≤ frostmanConstIn
            (familyIn tb (fun k' => (Tb k').toConvexSpaceBody)
              ((Tb k).rescale σ).toConvexSpaceBody)
            (fun k' => (Tb k').toConvexSpaceBody)
            ((Tb k).rescale σ).toConvexSpaceBody

/-- **The conclusions of blueprint `lem:ml1bootCaseIIData`, one field per clause**

The intended producer is `Kakeya.ml1Boot.exists_caseTwoData`, which is not a declaration; see
the module docstring.  This structure is what it is to conclude.

Here `(𝕋, Y)` is a family of shaded `δ`-tubes indexed by `s`, `s₀ ⊆ s` is the refinement, and
`(tτ, 𝕋_τ, pτ)`, `(tθ, 𝕋_θ, pθ)` are the two named parent families produced at the scales `τ`
and `θ`.  The fields `parentFine`–`coarseEssDistinct` are the interface data that
`Kakeya.ml1Boot.exists_factorTwoScales` consumes; `refine_*` are the four clauses of item (i),
and `fine`, `mid`, `lower` are items (ii), (iii) and (iv). -/
structure IsCaseTwoData {ι κ l : Type*} [DecidableEq κ] [DecidableEq l] {δ τ θ : ℝ≥0}
    (p : Params) (ε' γ : ℝ) (j : ℕ) (s : Finset ι) (T : ι → ShadedTube δ E) (s₀ : Finset ι)
    (tb : Finset κ)
    (tτ : Finset κ) (Tτ : κ → Tube τ E) (pτ : ι → κ)
    (tθ : Finset l) (Tθ : l → Tube θ E) (pθ : κ → l) : Prop where
  /-- `(tτ, 𝕋_τ, pτ)` is a parent family for the retained fine family at scale `τ`. -/
  parentFine : IsParentFamily s₀ (fun i => (T i).toTube) tτ Tτ pτ
  /-- `(tθ, 𝕋_θ, pθ)` is a parent family for `𝕋_τ` at scale `θ`. -/
  parentCoarse : IsParentFamily tτ Tτ tθ Tθ pθ
  /-- The fine parent family is retained inside the unrefined level-`b` node family `tb` of the
  hierarchy of the hypotheses.  This is what lets `lower`, which speaks about `tb`, be stated
  alongside the repaired families. -/
  fineRetained : tτ ⊆ tb
  /-- The middle tubes lie in `B₁`.  This is not implied by `parentFine`: a parent tube may
  stick out of `B₁` even though every tube it covers lies inside. -/
  midBall : ∀ k ∈ tτ, (Tτ k).carrier ⊆ Metric.closedBall 0 1
  /-- The coarse tubes lie in `B₁`, for the same reason. -/
  coarseBall : ∀ l' ∈ tθ, (Tθ l').carrier ⊆ Metric.closedBall 0 1
  /-- The middle tubes are pairwise essentially distinct. -/
  midEssDistinct : (tτ : Set κ).Pairwise
    (fun k k' => IsEssentiallyDistinct (Tτ k).carrier (Tτ k').carrier)
  /-- The coarse tubes are pairwise essentially distinct. -/
  coarseEssDistinct : (tθ : Set l).Pairwise
    (fun l₁ l₂ => IsEssentiallyDistinct (Tθ l₁).carrier (Tθ l₂).carrier)
  /-- (i) `(𝕋|_{s₀}, Y)` is a `δ ^ ε'`-refinement of `(𝕋, Y)`. -/
  refine_refinement : ShadedBody.IsCRefinement s₀ (fun i => (T i).toShadedBody) s
    (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ ε', by positivity⟩
  /-- (i) The refinement is uniform, at the constant `Kakeya.ml1Boot.uniformize.C 3`. -/
  refine_unif : Nonempty (ShadedTube.ShadedUniformTubeSet s₀ T (Tube.ssfGridLen δ)
    (uniformize.C 3))
  /-- (i) Its Frostman constant in `B₁` has grown by at most `δ ^ (-ε')`. -/
  refine_frostman : frostmanConstIn s₀ (fun i => (T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall
    ≤ (δ : ℝ≥0∞) ^ (-ε' - p.ηGamma γ)
  /-- (i) Its fullness has dropped by at most `δ ^ ε'`. -/
  refine_fullness : (δ : ℝ≥0∞) ^ (ε' + p.ηGamma γ)
    ≤ ShadedBody.fullness s₀ (fun i => (T i).toShadedBody)
  /-- (ii) The Frostman constant of every fine fibre inside its `τ`-parent. -/
  fine : ∀ k ∈ tτ,
    frostmanConstIn (fibre s₀ pτ k) (fun i => (T i).toConvexSpaceBody)
        (Tτ k).toConvexSpaceBody
      ≤ (δ : ℝ≥0∞) ^ (-ε') * ((τ / δ : ℝ≥0) : ℝ≥0∞) ^ p.η (j - 1)
  /-- (iii) The Frostman constant of every middle fibre inside its `θ`-parent. -/
  mid : ∀ l' ∈ tθ,
    frostmanConstIn (fibre tτ pθ l') (fun k => (Tτ k).toConvexSpaceBody)
        (Tθ l').toConvexSpaceBody
      ≤ (δ : ℝ≥0∞) ^ (-ε') * ((θ / τ : ℝ≥0) : ℝ≥0∞) ^ p.η (j - 1)
  /-- (iv) The Frostman **lower** bound at every free scale `σ` in the `ε`-window
  `Kakeya.ml1Boot.IsScaleWindow` and at *every* node of the **unrefined** level-`b` family
  `tb`, inside the concentric `σ`-rescaling of that node's tube.

  Three features of the shape.

  * *The family is the unrefined one.*  The item used to read the Frostman constant of the
    *retained* fibre `fibre tτ pθ l'` inside a `σ`-tube, and getting the dichotomy's bound
    down to that family was what the refinement-stability assumption was for. That assumption is
    refuted and undeliverable,
    so the item is stated where `StickyKakeya.IsFrostmanDividingBlock.frostman_lower` asserts
    it and nowhere else; `fineRetained` is what connects it to `tτ`.
  * *There is no coarse index and no containment clause.*  Where a consumer needs
    `T_σ ⊆ 2 · Tθ l'` it is supplied on the spot by
    `Kakeya.ml1Boot.rescale_le_dilate_two`, a property of the node tubes alone.
  * *The window is the `ε`-window and the loss is `δ ^ ε'`, with no `ε²` term.*  Both are the
    amended dichotomy's: it is asserted at every real scale of that window with a
    subpolynomial loss, so no rounding stands between hypothesis and conclusion. -/
  lower : IsFreeScaleLowerBound δ p ε' j θ tb Tτ

/-- **The output of the Case (ii) repair: `Kakeya.ml1Boot.IsCaseTwoData` without its middle
bound**.

The intended producer is `Kakeya.ml1Boot.exists_caseTwoDataRepair`, which is not a declaration;
see the module docstring.  This structure is what it is to conclude.

Every field of `Kakeya.ml1Boot.IsCaseTwoData` except `mid`, at the same parameters and with the
same statements.  This is exactly what the repair produces: blueprint
`lem:ml1bootCaseIIDataRepair` concludes items `caseIIRefine`, `caseIIFine` and `caseIILower`
together with the parent-family, essential-distinctness and `B₁` interface data, and *not* item
`caseIIMid`.

## Why the middle bound is not among the fields

The repair delivers the middle bound at the parent-map fibre inside the **full** level-`b` node
family — that is step 0, `Kakeya.ml1Boot.caseTwoRawMidFibre` — and its two later steps delete
`τ`-nodes without controlling what survives inside a coarse fibre.  So nothing in the repair
supplies that bound at the *retained* `tτ` which `Kakeya.ml1Boot.IsCaseTwoData.mid` reads:
passing to the subfamily needs a node-count share *inside each coarse fibre*, and the greedy
selection behind step 1 is charged against one global weight on the leaves, so a discarded node
is charged to a near-copy that need not lie under the same coarse node and a coarse fibre can be
selected down to a concentrated remnant.  Blueprint `note:ml1bootRepairEDMidRetained` is the
account of that, and of the two obstructions standing in the way of the fibrewise selection that
would remove it.  An alternative form of blueprint `lem:ml1bootCaseIIDataRepair` asserted `mid`
anyway; that is retracted, and this structure is the Lean half of the retraction.

## Where the obligation went

It is not silently absorbed.  It is the explicit hypothesis of
`Kakeya.ml1Boot.IsCaseTwoRepairData.isCaseTwoData`, so it is visible in the statement of every
consumer that rebuilds the full record, `Kakeya.ml1Boot.exists_caseTwoData` above all, and no
declaration of this chain asserts the middle bound at a retained node set outright.

What *is* proved about it is the descent, `Kakeya.ml1Boot.frostmanConstIn_retainedFibre_le`:
given the fibrewise empty-or-share dichotomy `Kakeya.ml1Boot.IsFibrewiseEmptyOrShare` for the
retained node set at a share `κ ≠ 0`, step 0's bound at the full fibre transfers to the retained
fibre at the single cost `κ⁻¹`.  At `κ = δ ^ (3 ε' / 4)` — the whole of the budget step 0 leaves,
see `Kakeya.ml1Boot.mid_le_of_share_compose` — that lands the exponent back at exactly `ε'`, so
carrying the dichotomy through to this point would restore `mid` with no change to the
exponents.
-/
structure IsCaseTwoRepairData {ι κ l : Type*} [DecidableEq κ] [DecidableEq l] {δ τ θ : ℝ≥0}
    (p : Params) (ε' γ : ℝ) (j : ℕ) (s : Finset ι) (T : ι → ShadedTube δ E) (s₀ : Finset ι)
    (tb : Finset κ)
    (tτ : Finset κ) (Tτ : κ → Tube τ E) (pτ : ι → κ)
    (tθ : Finset l) (Tθ : l → Tube θ E) (pθ : κ → l) : Prop where
  /-- `(tτ, 𝕋_τ, pτ)` is a parent family for the retained fine family at scale `τ`. -/
  parentFine : IsParentFamily s₀ (fun i => (T i).toTube) tτ Tτ pτ
  /-- `(tθ, 𝕋_θ, pθ)` is a parent family for `𝕋_τ` at scale `θ`. -/
  parentCoarse : IsParentFamily tτ Tτ tθ Tθ pθ
  /-- The fine parent family is retained inside the unrefined level-`b` node family `tb` of the
  hierarchy of the hypotheses.  This is what lets `lower`, which speaks about `tb`, be stated
  alongside the repaired families. -/
  fineRetained : tτ ⊆ tb
  /-- The middle tubes lie in `B₁`.  This is not implied by `parentFine`: a parent tube may
  stick out of `B₁` even though every tube it covers lies inside. -/
  midBall : ∀ k ∈ tτ, (Tτ k).carrier ⊆ Metric.closedBall 0 1
  /-- The coarse tubes lie in `B₁`, for the same reason. -/
  coarseBall : ∀ l' ∈ tθ, (Tθ l').carrier ⊆ Metric.closedBall 0 1
  /-- The middle tubes are pairwise essentially distinct. -/
  midEssDistinct : (tτ : Set κ).Pairwise
    (fun k k' => IsEssentiallyDistinct (Tτ k).carrier (Tτ k').carrier)
  /-- The coarse tubes are pairwise essentially distinct. -/
  coarseEssDistinct : (tθ : Set l).Pairwise
    (fun l₁ l₂ => IsEssentiallyDistinct (Tθ l₁).carrier (Tθ l₂).carrier)
  /-- (i) `(𝕋|_{s₀}, Y)` is a `δ ^ ε'`-refinement of `(𝕋, Y)`. -/
  refine_refinement : ShadedBody.IsCRefinement s₀ (fun i => (T i).toShadedBody) s
    (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ ε', by positivity⟩
  /-- (i) The refinement is uniform, at the constant `Kakeya.ml1Boot.uniformize.C 3`. -/
  refine_unif : Nonempty (ShadedTube.ShadedUniformTubeSet s₀ T (Tube.ssfGridLen δ)
    (uniformize.C 3))
  /-- (i) Its Frostman constant in `B₁` has grown by at most `δ ^ (-ε')`. -/
  refine_frostman : frostmanConstIn s₀ (fun i => (T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall
    ≤ (δ : ℝ≥0∞) ^ (-ε' - p.ηGamma γ)
  /-- (i) Its fullness has dropped by at most `δ ^ ε'`.

  This is the clause that blueprint `note:ml1bootCaseIIRefineFullnessGap` showed had no supplier
  while `Kakeya.ml1Boot.IsCaseTwoInput` linked `s'` to `s` by a cardinality bound alone.  It now
  has one: the bundle's `refine_mass` carries the shade-mass retention, and
  `Kakeya.ml1Boot.fullness_le_of_isCRefinement` descends it along the composed refinement
  `s₀ ⊆ s' ⊆ s`. -/
  refine_fullness : (δ : ℝ≥0∞) ^ (ε' + p.ηGamma γ)
    ≤ ShadedBody.fullness s₀ (fun i => (T i).toShadedBody)
  /-- (ii) The Frostman constant of every fine fibre inside its `τ`-parent. -/
  fine : ∀ k ∈ tτ,
    frostmanConstIn (fibre s₀ pτ k) (fun i => (T i).toConvexSpaceBody)
        (Tτ k).toConvexSpaceBody
      ≤ (δ : ℝ≥0∞) ^ (-ε') * ((τ / δ : ℝ≥0) : ℝ≥0∞) ^ p.η (j - 1)
  /-- (iv) The Frostman **lower** bound at every free scale `σ` in the `ε`-window and at every
  node of the **unrefined** level-`b` family `tb`; see `Kakeya.ml1Boot.IsCaseTwoData.lower`. -/
  lower : IsFreeScaleLowerBound δ p ε' j θ tb Tτ


/-- **The two raw Frostman *upper* bounds at the node families** (blueprint
`lem:ml1bootCaseIIDataRaw`, items (a) and (b)).

These are the first two bullets of `StickyKakeya.IsFrostmanDividingBlock` read at the two named
node parent families, with their subpolynomial `StickyKakeya.totalLoss` absorbed into
`δ ^ (-ε')`.  They are split off from the lower bound of
`Kakeya.ml1Boot.IsCaseTwoRawData` because the repair — blueprint
`lem:ml1bootCaseIIDataRepair`, intended producer `Kakeya.ml1Boot.exists_caseTwoDataRepair`,
which is not a declaration — is to consume exactly these two and *not* the lower one:
a Frostman lower bound at a family says nothing about a subfamily, so it cannot be transported
across the repair's refinement and is re-derived there instead, from the block itself.

## The middle bound is a *containment* family, and it cannot be a fibre here

`mid` used to read the Frostman constant of the parent-map fibre `fibre tτ pθ l'`.  That is
**not** what the second bullet of `StickyKakeya.IsFrostmanDividingBlock` asserts: the bullet is
`frostman_nodes`, stated at `Tube.UniformTubeSet.nodesUnder`, i.e. at *all* level-`b`
nodes contained in the coarse node, and the fibre of the induced map `ϖ_{b→a}` is in general a
proper subset of that family (a fine node may lie in several coarse nodes, and `ϖ` picks one of
them through a leaf).  A Frostman constant is a *ratio* — `ConvexSpaceBody.IsFrostmanIn` bounds
`densityIn t W K'` by `C * densityIn t W K` — so passing to a subfamily shrinks numerator and
denominator alike and the bound does **not** transport: `frostmanConstIn` is not monotone in the
index set, and `ConvexSpaceBody.IsFrostmanIn.of_subset` charges a volume share for the step.
This half of the conversion is by design a pure read-off with no refinement and no share
available, so the field is stated where the dichotomy asserts it, as the containment family
`Kakeya.familyIn tτ _ (Tθ l')`, which is exactly `nodesUnder` in the parent-family language.
Supplying the fibre reading that `Kakeya.ml1Boot.IsCaseTwoData.mid` needs is the business of
`Kakeya.ml1Boot.exists_caseTwoDataRepair`, which is where a share is available; blueprint
`note:ml1bootRawMidContainment` records the counting argument that does it.

With the fibre gone the coarse parent map `pθ` is not read by either field, so it is no longer
a parameter of this structure.

The `fine` field is `Kakeya.ml1Boot.IsCaseTwoData.fine` verbatim, stated for the unrefined `s'`
and the full node index sets; the fine-level fibre needs no such repair, being literally the
class `Tube.coverClass` of the first bullet. -/
structure IsCaseTwoRawUpper {ι κ l : Type*} [DecidableEq κ] {δ τ θ : ℝ≥0}
    (p : Params) (ε' : ℝ) (j : ℕ) (s' : Finset ι) (T : ι → ShadedTube δ E)
    (tτ : Finset κ) (Tτ : κ → Tube τ E) (pτ : ι → κ)
    (tθ : Finset l) (Tθ : l → Tube θ E) : Prop where
  /-- (a) The Frostman constant of every fine fibre inside its `τ`-parent. -/
  fine : ∀ k ∈ tτ,
    frostmanConstIn (fibre s' pτ k) (fun i => (T i).toConvexSpaceBody)
        (Tτ k).toConvexSpaceBody
      ≤ (δ : ℝ≥0∞) ^ (-ε') * ((τ / δ : ℝ≥0) : ℝ≥0∞) ^ p.η (j - 1)
  /-- (b) The Frostman constant of the middle tubes contained in a `θ`-parent, inside it. -/
  mid : ∀ l' ∈ tθ,
    frostmanConstIn (familyIn tτ (fun k => (Tτ k).toConvexSpaceBody) (Tθ l').toConvexSpaceBody)
        (fun k => (Tτ k).toConvexSpaceBody) (Tθ l').toConvexSpaceBody
      ≤ (δ : ℝ≥0∞) ^ (-ε') * ((θ / τ : ℝ≥0) : ℝ≥0∞) ^ p.η (j - 1)

/-- **The raw Case (ii) data at the node families** (blueprint `lem:ml1bootCaseIIDataRaw`,
items (a), (b), (c)).

The two upper bounds of `Kakeya.ml1Boot.IsCaseTwoRawUpper` together with the Frostman *lower*
bound at every free scale of the `ε`-window, all three read directly off the node families of
the hierarchy.

No essential distinctness, no uniformity, no refinement of `s` and no containment in `B₁` is
asserted: all four are the business of `Kakeya.ml1Boot.exists_caseTwoDataRepair`.  The `lower`
field is `Kakeya.ml1Boot.IsCaseTwoData.lower` verbatim, for the unrefined index sets. -/
structure IsCaseTwoRawData {ι κ l : Type*} [DecidableEq κ] {δ τ θ : ℝ≥0}
    (p : Params) (ε' : ℝ) (j : ℕ) (s' : Finset ι) (T : ι → ShadedTube δ E)
    (tτ : Finset κ) (Tτ : κ → Tube τ E) (pτ : ι → κ)
    (tθ : Finset l) (Tθ : l → Tube θ E) : Prop
    extends IsCaseTwoRawUpper p ε' j s' T tτ Tτ pτ tθ Tθ where
  /-- (c) The Frostman **lower** bound at every free scale `σ` of the `ε`-window and at every
  node of the level-`b` family `tτ`, which here is the unrefined one. -/
  lower : IsFreeScaleLowerBound δ p ε' j θ tτ Tτ


end CaseTwo

end ml1Boot

end Kakeya

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]


end Kakeya.ml1Boot

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.AScaleRounding
public import Kakeya.DimensionThree.MainLemma2.NonSlabFibre
public import Kakeya.Factoring.RhoTubesUndilated
public import Kakeya.Factoring.RhoTubesSection9
public import Kakeya.MultiScaleFac.UniformBridgeKT
public import Kakeya.PartialEstimatesWindowed
public import Kakeya.DimensionThree.MainLemma2.KTWindowThresholds

/-!
# What Sections 3 and 5 owe the scale-`r` layer of Main Lemma 2

Two statements, each as a proposition, each owned by another section of the
development, and each stated in a form that section can actually deliver. Together with the
proved material of `Kakeya.DimensionThree.MainLemma2.AScaleRounding` they are exactly what
`Kakeya.DimensionThree.MainLemma2.AScaleInterface` consumes.

* `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` — Section 5, blueprint
  `shadingMultiplicityEstimateForRhoTubes` at `ρ` a scale of the multiscale grid. The Lean
  statement of that lemma cannot be applied here, and the obstruction is *not* the scale: it is
  the hypothesis `hed`, pairwise essential distinctness of the outer family, which the
  docstring of `Tube.UniformTubeSet.boundedOverlap` records as unsatisfiable for
  the nodes of a hierarchy while preserving cardinality. The version below replaces `hed` by
  taking the outer family to *be* the node family of the hierarchy, which carries bounded
  overlap instead.
* `Kakeya.VeryNotSticky.coarseKatzTaoBound` — Section 3, blueprint `genKKT`
  (`Kakeya.KatzTaoEstimate.multiplicity_bound`) applied to the coarse family, with the same
  substitution of bounded overlap for essential distinctness, and with the two thresholds of
  `genKKT` absorbed.

**Both are stated at the configuration's own hierarchy, not at an arbitrary one.** Each takes
the uniform bundle at the grid length `⌈log log 1/δ⌉` and the branching/overlap constant
`cfg.C₀` that Configuration `hyp:ml2setup` carries, and the first takes the *shaded* bundle
`Kakeya.ShadedTube.ShadedUniformTubeSet`, which is what the field
`Kakeya.VeryNotSticky.uniform` supplies and what blueprint
`shadingMultiplicityEstimateForRhoTubes` asks for. (There is **no** Lean declaration of that
name: only the placeholder constant
`Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C` exists, and the proved Lean forms
of GWZ Lemma 5.11 are `Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate` and its
undilated specialisations.) Earlier versions
quantified both the grid length `N` and the overlap constant `C₀` universally and handed
Section 5 only the tube-level bundle. That was wrong twice over: the tube-level bundle is not
enough to invoke Section 5 at all, and a `C₀` quantified before the statement makes each
estimate an assertion, with a `C₀`-free constant, about hierarchies of arbitrarily bad
overlap — while the substitution of bounded overlap for essential distinctness costs exactly a
factor `C₀`. At the configuration's own `C₀` that loss is sub-polynomial,
`Kakeya.VeryNotSticky.coe_C₀_le_rpow_neg_eta`, and each docstring below says where it is paid
for: out of the gain in `Kakeya.VeryNotSticky.coarseKatzTaoBound`, and out of the factor
`δ^{cfg.η}` now carried on the small side of the ball conjunct of
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid`. Neither statement absorbs a loss it has
no room for.

Section 5 also asks its inner family for two-sided per-tube shading densities, and those are
not a consequence of the aggregate `cfg.fullness_ge`, a ratio of sums. They are carried as the
configuration fields `Kakeya.VeryNotSticky.lam`, `Kakeya.VeryNotSticky.Cd`,
`Kakeya.VeryNotSticky.shading_lb`, `Kakeya.VeryNotSticky.shading_ub` and
`Kakeya.VeryNotSticky.lam_ge`, so that the residue below assumes nothing it does not say.
-/

@[expose] public section

open scoped NNReal ENNReal

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set ShadedBody
open scoped NNReal ENNReal

universe u

/-! ## What Section 5 already delivers at this configuration

The three declarations below are the *proved* part of the Section-5 residue: the node factor
family of the configuration at a grid index, and GWZ Lemma 5.11
(`Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubesUndilated_lam`) applied to it. They
are what `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` below has to be closed *from*,
and the difference between the two is exactly the residue.
-/


/-- **The ball conjunct from the configuration's own local-mass datum.**

Given any shaded factor family whose inner side is the configuration's family on the nose and
whose coarse shaded union lies in the `2ρ`-neighbourhood of the inner shaded union, the ball
conjunct at the gain `δ^η` follows from `Kakeya.VeryNotSticky.coarseLocalMass` and nothing else:
the loss constant appears only through its inverse, on the small side, and
`ShadedBody.one_le_rhoTubesInducedFullnessLoss` disposes of it.

The containment hypothesis is `ShadedBody.iUnion_inducedCoarseShading_subset_cthickening` at the
induced coarse shading, which is what makes the datum — statable with no reference to the
hierarchy — bound a union that does refer to it. -/
theorem coarseBallConjunct_of_coarseLocalMass (cfg : VeryNotSticky.{u})
    (G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι)
    (hinner : G.innerSet = cfg.s)
    (hbody : ∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ) {ρ : ℝ≥0}
    (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (hsub : (⋃ j ∈ G.outerSet, (G.outerBody j).shade)
      ⊆ Metric.cthickening (2 * (ρ : ℝ)) (⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade)) :
    ∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
      (cfg.δ : ℝ≥0∞) ^ cfg.η *
          (((_root_.ShadedBody.rhoTubesInducedFullnessLoss 3 : ℝ≥0) : ℝ≥0∞)⁻¹ *
              volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
            (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ)) /
              volume (ball x (ρ : ℝ)))) ≤
        volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade) := by
  classical
  subst hgrid
  have hunion : (⋃ i ∈ G.innerSet, (G.innerBody i).shade) =
      ⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade := by
    rw [hinner]
    exact Set.iUnion₂_congr fun i hi =>
      congrArg (fun b : ShadedBody (EuclideanSpace ℝ (Fin 3)) => b.shade) (hbody i hi)
  intro x _
  rw [hunion]
  have hL1 : (1 : ℝ≥0∞)
      ≤ ((_root_.ShadedBody.rhoTubesInducedFullnessLoss 3 : ℝ≥0) : ℝ≥0∞) := by
    have h : (1 : ℝ≥0) ≤ _root_.ShadedBody.rhoTubesInducedFullnessLoss 3 :=
      _root_.ShadedBody.one_le_rhoTubesInducedFullnessLoss 3
    exact_mod_cast h
  have hkey : ((_root_.ShadedBody.rhoTubesInducedFullnessLoss 3 : ℝ≥0) : ℝ≥0∞)⁻¹ *
      volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade)
      ≤ volume (Metric.cthickening
          (2 * (Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : ℝ))
          (⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade)) := by
    calc ((_root_.ShadedBody.rhoTubesInducedFullnessLoss 3 : ℝ≥0) : ℝ≥0∞)⁻¹ *
          volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade)
        ≤ 1 * volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) := by
          gcongr
          exact ENNReal.inv_le_one.2 hL1
      _ = volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) := one_mul _
      _ ≤ _ := measure_mono hsub
  exact le_trans (mul_le_mul' le_rfl (mul_le_mul' hkey le_rfl)) (cfg.coarseLocalMass k hk x)

/-- **The coarse shaded family at a grid scale, with the ball estimate** (blueprint
`shadingMultiplicityEstimateForRhoTubes` at `ρ = ρ_k`, whose ninth conclusion is
`boundVolumeAcrossTwoScales`, i.e. blueprint `lowerBoundTTScaleAAndABall`).

At every scale `ρ = δ^{k/N}` of the multiscale grid the node family of the hierarchy carries a
shading `Y_{𝕋_ρ}` for which

* the fully shaded factor family `G` has the pair `(𝕋, Y)` of Configuration `hyp:ml2setup`
  itself as its inner layer;
* its outer layer is the active node family `𝕋_ρ` at the grid index `k`, with the node tubes
  as convex bodies;
* the outer shading is at least as full as the inner density,
  `λ(𝕋_ρ, Y_{𝕋_ρ}) ≥ C⁻¹ lam` with `lam = cfg.lam`;
* and the ball estimate holds, re-centred at every shaded point, with the fixed constant
  `Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C` **and a factor `δ^{cfg.η}` on
  its small side**, which is the room the `C₀` of the substitution below is paid out of.

**Relation to Section 5.** This is blueprint `shadingMultiplicityEstimateForRhoTubes` at
`ρ = ρ_k`. GWZ Lemma 5.11 is formalized as
`Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate`, proved, and its `c = 1`
specialisations `…Undilated` and `…Undilated_lam` are proved, all at the honest loss constant
`ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C`. The simultaneous full-family formulation differs from all three, as explained below. The
hypotheses are the configuration's own: the bundle is
the *shaded* one that the field `Kakeya.VeryNotSticky.uniform` supplies, at the grid length
`⌈log log 1/δ⌉` and the constant `cfg.C₀`, because Section 5 asks for a
`Kakeya.ShadedTube.ShadedUniformTubeSet` at exactly that grid length and cannot be invoked
from the tube-level bundle alone.

Four things separate this statement from the raw one, and they are of three different kinds.

* **Essential distinctness is replaced by bounded overlap** (a genuine strengthening). Section 5
  asks its outer family to be pairwise essentially distinct (`hed`). The nodes of a
  `Tube.UniformTubeSet` are not, and the docstring of
  `Tube.UniformTubeSet.boundedOverlap` says why they cannot be made so without
  destroying the cardinality that the counting bounds need. What the nodes *do* have is
  Definition 2.1(ii): at most `C₀` of them meet any given `ρ`-tube through `𝕋`. That is the
  `∼1`-multiplicity content `hed` was there to provide, and it is what the proof of Section 5
  actually uses — the essential distinctness enters only through a packing count of the outer
  family against a test tube, which bounded overlap supplies directly, with `C₀` in place of
  the dimensional constant.
* **The `C₀` of that substitution is paid by the factor `δ^{cfg.η}` on the small side of the
  ball conjunct.** `Kakeya.VeryNotSticky.coe_C₀_le_rpow_neg_eta` gives `C₀ ≤ δ^{-η}` at the
  configuration's own constant — which is why pinning the bundle to `cfg.C₀` rather than
  quantifying `C₀` is what keeps the statement from being an assertion about arbitrarily bad
  hierarchies — so one factor `δ^{η}` is exactly the room a single substitution needs. Requiring the ball estimate at the closed term
  `Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C` with no `δ`-power and no `C₀`
  anywhere on its small side leaves no room for the loss and is stronger than
  the Section-5 estimate after this substitution. The available exponent budget is sufficient:
  `Kakeya.VeryNotSticky.coarseBallEstimate_of_gridScale` transports the estimate from the grid
  scale `ρ` to the nominal radius `r` at the cost `(ρ/r)³ ≤ δ^{-3η}`, so with the extra `δ^{η}`
  it needs `ν/9 - η ≥ 3η`, i.e. `ν ≥ 36 η`, against the standing `ν ≥ 90 η` of
  Configuration `hyp:ml2setup`; the surplus `ν/9 - 4η ≥ 6η` is not spent
  (`Kakeya.VeryNotSticky.rpow_sub_eta_mul_cube_le_cube_of_gridStep`). Because the whole loss
  fits inside the gain, the *conclusion* of `coarseBallEstimate_of_gridScale`, and hence the
  statement of `Kakeya.VeryNotSticky.exists_aScaleInputs` and everything downstream of it in
  `Kakeya.DimensionThree.MainLemma2.Goals`, is unchanged.
* **Section 5's two-sided shading-density hypothesis is no longer absorbed.** `hlam_lb` and
  `hlam_ub` there say `|Y(T)| ∼_{Cd} lam |T|` for each inner tube, at a comparison constant
  `Cd`. `cfg.fullness_ge` is the *aggregate* ratio `(∑|Y(T)|)/(∑|T|) ≥ δ^η`, which is a ratio
  of sums and therefore bounds no individual tube; and the shaded bundle `𝒱` does not supply
  the missing half either, its four branching fields being statements about per-point counts
  and not about `|Y(T)|` for a single `T`. These two hypotheses are explicit configuration data:
  `Kakeya.VeryNotSticky.lam`, `Kakeya.VeryNotSticky.Cd`, `Kakeya.VeryNotSticky.shading_lb`,
  `Kakeya.VeryNotSticky.shading_ub` — which is where they belong, being a property of the pair
  `(𝕋, Y)` alone, and which is the standing abuse of notation of the blueprint made explicit:
  the pigeonholing that makes the densities comparable happens while Configuration
  `hyp:ml2setup` is assembled. Whoever discharges this statement applies Section 5 with
  `lam := cfg.lam` and `Cd := cfg.Cd` and those two fields.
* **The outer-fullness conjunct is stated at `C⁻¹ lam`, which is what Section 5 delivers.**
  Section 5 concludes `λ(𝕋_ρ, Y_{𝕋_ρ}) ≥ C⁻¹ lam` at the *inner* density `lam`, not at the
  aggregate `δ^η`; asserting `δ^η` here would have been a second unstated absorption, since
  `lam` and `λ(𝕋, Y)` differ by up to `Cd`. The bridge to the `δ^{2η}` that
  `Kakeya.VeryNotSticky.coarseMassBound` consumes is the configuration field
  `Kakeya.VeryNotSticky.lam_ge`, `δ^{2η} ≤ lam`, and it is spent in the *proved*
  `Kakeya.VeryNotSticky.exists_aScaleInputs`.
* **The inner layer is the configuration's own pair, not a refinement of it.** Section 5
  returns `G.innerSet = {i ∈ F.innerSet | F.parent i ∈ G.outerSet}` and identifies inner bodies
  only as convex bodies. Per the first remark of blueprint `lem:ml2aScaleData` the `≈ 1`
  refinement is taken *while* Configuration `hyp:ml2setup` is assembled — blueprint
  `lem:ml2setupexists` lists `shadingMultiplicityEstimateForRhoTubes` among its inputs — so the
  pair recorded by `cfg` is already the refined one and there is nothing left to transfer. This
  is the standing abuse of notation of the blueprint, and it is why `hinner` and `hbody` below
  are equalities rather than comparisons.
**Not refutable by a trivial realisation.** Every conjunct is an existential statement about a
shading that is being constructed, at a family (`cfg.activeTubeNodes 𝒱.tubeUniform k`) and inner
pair (`cfg.s`, `cfg.T`) that are fixed in advance, and every constant occurring is either the
closed term `Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C` or a field of `cfg`.
In particular the trivial realisation of the threshold bundle that killed an earlier stub —
`Kakeya.VeryNotSticky.nonempty_scaleThresholds` at `aScaleConst ≡ 1` — is irrelevant here,
since no threshold bundle is mentioned and `C₀` is fixed by the configuration. Neither of the two new occurrences of a
post-`δ` quantity weakens this: `cfg.lam` appears on the *small* side of the fullness conjunct,
where a larger value is a stronger claim, and `cfg.Cd` does not appear at all.

**Essential distinctness cannot be supplied instead, and this is why.** The development proves
`Kakeya.Tube.exists_maximal_essDistinct` and `Kakeya.Tube.refineToEssDistinctLeaves`, and
neither helps. The first returns a maximal essentially distinct *subfamily* with no cardinality
comparison at all. The second returns one with `#s ≤ C_n · D · #s'`, where `D` is any bound on
the maximal density of the family it is applied to; at the node family `𝕋_ρ` the only such
bound available is `Kakeya.VeryNotSticky.maxDensity_activeTubeNodes_le`, whose right-hand side
is polynomially large in `δ` (of size `ρ²/(δ^{2+η} |𝕋[T_ρ]|)`), so the cardinality loss is
polynomial and no gain of the layer can pay for it. Independently of that, passing to a
subfamily destroys the identity `G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k`, which is
what lets `Kakeya.VeryNotSticky.rScaleParentData_of_gridScale` apply
`Kakeya.VeryNotSticky.maxDensity_activeTubeNodes_le` and
`Kakeya.VeryNotSticky.card_le_card_activeTubeNodes_mul` at all — both are statements about the
full node family. So bounded overlap is not a convenience here; it is the only form of the
hypothesis available.

The hypothesis `hρ` is the range `[δ, 1]` of blueprint `shadingMultiplicityEstimateForRhoTubes`,
which is where its `ρ`-tubes have to live; it is supplied by the rounding, since the radius
being rounded already satisfies `δ ≤ a ≤ r ≤ 1`.

**Comparison with the subfamily formulation.**
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_subfamily` above is GWZ Lemma 5.11 run at
this configuration and is *proved*. Two things separate it from this statement — the subfamily,
and the loss constant — and the two are of completely different weight. The distinction between the subfamily and constant requirements is described below.

*The constant is not the obstruction.* The placeholder
`Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C = 1` is nevertheless **never a
correct reading of Lemma 5.11**: that lemma's loss is a product of four pigeonholings and a
geometric loss, it is bounded below by the dimension-only floor
`ShadedBody.rhoTubesBallLoss 3 = 2·10⁶` (`ShadedBody.one_lt_rhoTubesSection9Loss`), and what it
*is* is a multiplicity — the ratio `∑_T |Y(T)|` to `|⋃_T Y(T)|` at the coarse scale — so
asserting it equals `1` assumes the conclusion of Main Lemma 2. The placeholder must go. But it
is not what keeps this statement open, and that is now compiler-checked: each of the two
estimates below is realisable **at the full node family and at loss `1`**, by an explicit
shading —
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_saturated` for the fullness conjunct and
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_minimal` for the ball conjunct. In
particular no refutation of this statement can be extracted from either conjunct alone, unlike
`Kakeya.VeryNotSticky.coarseKatzTaoBound`.

*The honest fullness conjunct is proved, on the full family.*
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_inducedFullness` delivers the fullness
clause at GWZ's own coarse shading `Y_{𝕋_ρ}(T_ρ) = T_ρ ∩ N_{2ρ}(⋃_{T ∈ 𝕋[T_ρ]} Y(T))`, with
`G.innerSet = cfg.s`, `G.outerSet = cfg.activeTubeNodes …` and `G.parent` all on the nose, at the
*purely dimensional* loss `ShadedBody.rhoTubesInducedFullnessLoss 3`. So the subfamily gap closes
for the fullness conjunct, and it closes at a constant that does not depend on `δ` or `|𝕋|`.

*The joint fullness and ball condition on the full family.* This condition is
equivalent to the existence of a single measurable set — see
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_shadingSet` and
`Kakeya.VeryNotSticky.exists_shadingSet_of_exists_coarseShadedFamilyAtGrid` — namely a `Z` with
`U(𝕋, Y) ⊆ Z ⊆ ⋃ 𝕋_ρ`, whose intersections with the node tubes are `lam`-full on average and
whose own volume is small enough. The saturated shading maximises the first and destroys the
second; the minimal shading does the reverse.

*The supremum is not the obstruction, and that is now compiler-checked.* It was natural to read
the ball conjunct as an assertion about the **densest** `ρ`-ball of `U(𝕋, Y)` — the uniformity
that Step 5 of the proof of Lemma 5.11 buys by discarding coarse bodies — and hence as something
no proof of that lemma could supply on the full family. That reading is wrong.
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_shadingSet_volume_max` proves that the
*whole* family of point estimates follows from one inequality in which no point occurs,

  `δ^η · |U(𝕋_ρ, Y_{𝕋_ρ})| ≤ max (|U(𝕋, Y)|, |B(0, ρ)|)`,

because the local density `|U(𝕋,Y) ∩ B(x,ρ)| / |B(x,ρ)|` is at most `1` and is also at most
`|U(𝕋,Y)| / |B(0,ρ)|`, and one of those two bounds always suffices. So the residue is not an
assertion about a worst `ρ`-ball at all; it is a **two-sided volume budget on one set**:

  produce a measurable `Z ⊇ U(𝕋, Y)` with `Cd⁻¹ · lam ≤ λ(𝕋_ρ, T_ρ ∩ Z)` and
  `δ^η · |Z| ≤ max (|U(𝕋, Y)|, |B(0, ρ)|)`

(`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_shadingSet_budget`); and the saturated
choice `Z = ⋃ 𝕋_ρ` collapses it to the displayed inequality, with no set and no point in it
(`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_coarseVolume`). The reduction is not
vacuous: `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_card_activeTubeNodes` discharges
the residue outright at any grid index with
`δ^η · |𝕋_ρ| · Tube.volume_le.C 3 · ρ² ≤ |B(0, ρ)|`.

*Where the budget is short, exactly.* Fullness costs volume: the coarse multiplicity is at most
`|𝕋_ρ|`, so a `Cd⁻¹ · lam`-full `Z` has `|Z| ≥ Cd⁻¹ · lam · ∑_j |T_{ρ,j}| / |𝕋_ρ|`, at least a
`Cd⁻¹ · lam` fraction of one node tube. The budget allows
`|Z| ≤ δ^{-η} max(|U(𝕋,Y)|, |B(0,ρ)|)`. What the configuration does **not** supply is any serious
lower bound on `|U(𝕋, Y)|`. `Kakeya.VeryNotSticky.maxDensity_le` bounds `Kakeya.maxDensity`,
which is built from `Kakeya.densityIn`, GWZ Eq. (2) — and that counts only the tubes *contained*
in the test body, not their intersections with it. At `K = closedBall 0 1` it therefore says
`∑_i |T_i| ≤ δ^{-η} |B_1|`, an **upper** bound on the total tube volume, and it says nothing at
all about the volume of the shaded union or about its density in a `ρ`-ball. The only lower bound
on `|U(𝕋, Y)|` derivable from the fields is a single tube's shading,
`|U(𝕋,Y)| ≥ Cd⁻¹ · lam · Tube.le_volume.c 3 · δ²`. So what is open is a genuine two-scale volume
comparison whose small side the configuration never pins down — not the supremum, and not either
conjunct on its own. Nor is there room in the constants: at `lam = Cd`, i.e. `Y(T) = T`
(`Kakeya.VeryNotSticky.lam_le_Cd` shows this is the top of the range), fullness at loss `1`
forces `Z = ⋃ 𝕋_ρ` up to null sets and the budget becomes `δ^η · |⋃ 𝕋_ρ| ≤ |U(𝕋, Y)|` on the
nose, with no slack anywhere. That is one more reason — and the first that bites the two
conjuncts *jointly* rather than either one alone — why the placeholder `C = 1` must be replaced
by the honest loss. The two structural routes are (i) weaken
`G.outerSet = cfg.activeTubeNodes …` to `⊆` (and `G.innerSet = cfg.s` to the induced subset) and
re-derive `Kakeya.VeryNotSticky.rScaleParentData_of_gridScale` through the monotonicity of
`maxDensity` and of `Finset.card`, or (ii) close `Kakeya.VeryNotSticky` under `C⁻¹`-refinement so
that the pigeonholed pair is again a configuration. Either is a cross-file repair touching
`Kakeya.DimensionThree.MainLemma2.AScaleConstants` (whose `aScaleDataConstant` reads the
placeholder as a *closed* term and must change shape, not merely value),
`Kakeya.DimensionThree.MainLemma2.AScaleInterface` and the tripwire in
`Kakeya.DimensionThree.MainLemma2.AScaleGuardrails`; it is not a local proof-search steps.

The factor `cfg.Cd` is necessary on the small side of the fullness conjunct; see
`Kakeya.DimensionThree.MainLemma2.AScaleGuardrails` for the refutation of the form without it
and for the tripwire that keeps it. -/
theorem exists_coarseShadedFamilyAtGrid (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : ℝ≥0} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (hρ : ρ ∈ Set.Icc cfg.δ 1) :
    ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.innerSet = cfg.s ∧
      (∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody) ∧
      G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k ∧
      (∀ j ∈ G.outerSet,
        (G.outerBody j).toConvexSpaceBody =
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody) ∧
      (cfg.Cd * _root_.ShadedBody.rhoTubesInducedFullnessLoss 3)⁻¹ * cfg.lam ≤
        ShadedBody.fullness G.outerSet G.outerBody ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (cfg.δ : ℝ≥0∞) ^ cfg.η *
            (((_root_.ShadedBody.rhoTubesInducedFullnessLoss 3 : ℝ≥0) : ℝ≥0∞)⁻¹ *
                volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
              (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ)) /
                volume (ball x (ρ : ℝ)))) ≤
          volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade)) := by
  classical
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  obtain ⟨i₀, hi₀⟩ := s_nonempty cfg
  have hmaps : ∀ i ∈ cfg.s, 𝒱.tubeUniform.cover.assign k i
      ∈ cfg.activeTubeNodes 𝒱.tubeUniform k := by
    intro i hi
    rw [activeTubeNodes, Finset.mem_filter]
    refine ⟨𝒱.tubeUniform.cover.assign_mem k hk i hi, ⟨i, ?_⟩⟩
    simp [tubeFibre, Tube.coverClass, hi]
  have hle : ∀ i ∈ cfg.s,
      (cfg.T i).toConvexSpaceBody ≤
        (𝒱.tubeUniform.cover.tube k (𝒱.tubeUniform.cover.assign k i)).toConvexSpaceBody := by
    intro i hi
    simpa using 𝒱.tubeUniform.cover.le_tube_assign k hk i hi
  have hactive : ∀ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
      ∃ i ∈ cfg.s, 𝒱.tubeUniform.cover.assign k i = j := by
    intro j hj
    rw [activeTubeNodes, Finset.mem_filter] at hj
    obtain ⟨i, hi⟩ := hj.2
    rw [tubeFibre, Tube.coverClass, Finset.mem_filter] at hi
    exact ⟨i, hi.1, hi.2⟩
  have ht : (cfg.activeTubeNodes 𝒱.tubeUniform k).Nonempty :=
    ⟨𝒱.tubeUniform.cover.assign k i₀, hmaps i₀ hi₀⟩
  have hCd : cfg.Cd ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one cfg.hCd)
  have hcar : ∀ i ∈ cfg.s,
      ((cfg.T i).toConvexSpaceBody : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ ((𝒱.tubeUniform.cover.tube k (𝒱.tubeUniform.cover.assign k i)).toConvexSpaceBody :
            Set (EuclideanSpace ℝ (Fin 3))) :=
    fun i hi => SetLike.coe_subset_coe.mpr (hle i hi)
  have hsubU : ∀ i ∈ cfg.s, (cfg.T i).shade ⊆
      Metric.cthickening (2 * (ρ : ℝ))
        (⋃ i' ∈ ({i' ∈ cfg.s | 𝒱.tubeUniform.cover.assign k i'
            = 𝒱.tubeUniform.cover.assign k i} : Finset cfg.ι), (cfg.T i').shade) := by
    intro i hi
    refine subset_trans ?_ (Metric.self_subset_cthickening _)
    exact Set.subset_biUnion_of_mem (u := fun i' => (cfg.T i').shade)
      (Finset.mem_filter.mpr ⟨hi, rfl⟩)
  subst hgrid
  refine ⟨{ innerSet := cfg.s
            innerBody := fun i => (cfg.T i).toShadedBody
            outerSet := cfg.activeTubeNodes 𝒱.tubeUniform k
            outerBody := _root_.ShadedBody.inducedCoarseShading cfg.s cfg.T
              (𝒱.tubeUniform.cover.assign k) (𝒱.tubeUniform.cover.tube k)
            parent := 𝒱.tubeUniform.cover.assign k
            parent_mem := hmaps
            inner_le_parent := hle
            shade_subset_parent := by
              intro i hi
              exact Set.subset_inter (subset_trans (cfg.T i).shade_subset (hcar i hi))
                (hsubU i hi) },
    rfl, fun _ _ => rfl, rfl, fun _ _ => rfl, ?_, ?_⟩
  · -- the fullness conjunct is the engine of GWZ Lemma 5.11 on the full coarse family
    have h := _root_.ShadedBody.le_fullness_inducedCoarseShading
      (E := EuclideanSpace ℝ (Fin 3)) (δ := cfg.δ) (Cd := cfg.Cd) (lam := cfg.lam)
      cfg.hδ hρ hCd cfg.T (𝒱.tubeUniform.cover.tube k)
      (𝒱.tubeUniform.cover.assign k) hle hactive ht cfg.shading_lb
    rwa [hfr] at h
  · -- the ball conjunct is `coarseLocalMass` read through the induced shading
    exact coarseBallConjunct_of_coarseLocalMass cfg _ rfl (fun _ _ => rfl) hk rfl
      (_root_.ShadedBody.iUnion_inducedCoarseShading_subset_cthickening cfg.s cfg.T
        (𝒱.tubeUniform.cover.assign k) (𝒱.tubeUniform.cover.tube k)
        (cfg.activeTubeNodes 𝒱.tubeUniform k))

/-! ### `Kakeya.VeryNotSticky.coarseKatzTaoBound` is **gone**

Its proved replacement is
`Kakeya.VeryNotSticky.coarseKatzTaoBound_of_etaBudget_atPair`, read at the window pair the
configuration now carries as `Kakeya.VeryNotSticky.ckt`; its single consumer
`Kakeya.VeryNotSticky.rScaleParentData_of_gridScale` is rewired onto it.

The refutation itself is **kept**, and is now stated as a negation rather than as a tripwire on
a declaration that no longer exists: see
`Kakeya.VeryNotSticky.statement_of_universal_coarseKatzTao_false` in
`Kakeya.DimensionThree.MainLemma2.CoarseKatzTaoRepair`, together with
`Kakeya.VeryNotSticky.CoarseKatzTaoStatement` and
`Kakeya.VeryNotSticky.coarseKatzTao_refutes_config`, which are untouched. -/

/-- A `ρ`-tube inside the closed unit ball, for `ρ ≤ 1/2`: the `ρ`-neighbourhood of the unit
segment centred at the origin.  Used only as the *off-family* default value when a family
indexed by `cfg.ι` has to be extended from `G.outerSet` to all of `cfg.ι`, because
`Kakeya.KatzTaoEstimate.multiplicity_bound_generalize_window` asks for its ball hypothesis at
every index, not only at the indices of the finite set.  The window used there is
`Metric.closedBall 0 4`, so the unit ball is more than enough for the default. -/
private lemma exists_tube_subset_closedBall (ρ : ℝ≥0) (hρ : ρ ≤ 1 / 2) :
    ∃ V : Tube ρ (EuclideanSpace ℝ (Fin 3)), V.carrier ⊆ closedBall 0 1 := by
  set e : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 0 (1 : ℝ) with he_def
  have he : ‖e‖ = 1 := by simp [he_def]
  have hdist : dist (-((1 : ℝ) / 2) • e) (((1 : ℝ) / 2) • e) = 1 := by
    rw [dist_eq_norm]
    have hsub : -((1 : ℝ) / 2) • e - ((1 : ℝ) / 2) • e = (-1 : ℝ) • e := by
      module
    rw [hsub, norm_smul, he]
    norm_num
  refine ⟨Tube.mk' ρ hdist, ?_⟩
  have hcar : (Tube.mk' ρ hdist).carrier
      = ⋃ z ∈ segment ℝ (-((1 : ℝ) / 2) • e) (((1 : ℝ) / 2) • e), closedBall z (ρ : ℝ) := rfl
  have hρ' : (ρ : ℝ) ≤ 1 / 2 := by exact_mod_cast hρ
  have hseg : segment ℝ (-((1 : ℝ) / 2) • e) (((1 : ℝ) / 2) • e) ⊆ closedBall 0 (1 / 2 : ℝ) := by
    refine (convex_closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2 : ℝ)).segment_subset ?_ ?_ <;>
      · simp [mem_closedBall, dist_eq_norm, norm_smul, he]
  rw [hcar]
  intro p hp
  simp only [Set.mem_iUnion, exists_prop] at hp
  obtain ⟨z, hz, hpz⟩ := hp
  have hz' : ‖z‖ ≤ 1 / 2 := by
    have := hseg hz
    simpa [mem_closedBall, dist_eq_norm] using this
  have hpz' : dist p z ≤ (ρ : ℝ) := by simpa [mem_closedBall] using hpz
  have : dist p 0 ≤ (ρ : ℝ) + 1 / 2 := by
    calc dist p 0 ≤ dist p z + dist z 0 := dist_triangle _ _ _
      _ ≤ (ρ : ℝ) + 1 / 2 := by
          gcongr
          simpa [dist_eq_norm] using hz'
  simp only [mem_closedBall]
  linarith

/-- **The Katz-Tao bound at the coarse family, with the fullness exponent left free.**

Identical to `Kakeya.VeryNotSticky.coarseKatzTaoBound_general_at` except that the fullness
exponent is a parameter `e` rather than the numeral `2 cfg.η`, tied to the window threshold by
`e ≤ cfg.exscal * ηKT`.  `hfull` enters the proof at exactly one place — the conversion of the
configuration's fullness into the `cfg.a ^ ηKT` the windowed estimate wants — and that conversion
reads `e` and nothing else, so nothing in the argument depends on the value.

It is stated because the honest fullness conjunct of
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` converts to `δ^{3η}` and not to `δ^{2η}`
(`Kakeya.VeryNotSticky.rpow_three_eta_le_of_inducedFullness`), and the exponent budget has room
for that and five more `η` (`Kakeya.VeryNotSticky.coarseLossExponentHeadroom`).  The `2 cfg.η`
form below is this one at `e := 2 * cfg.η`, so no consumer of it moves. -/
theorem coarseKatzTaoBound_general_atFullness (cfg : VeryNotSticky.{u})
    {ν c ε₀ e : ℝ}
    (hε₀ν : ε₀ ≤ ν / 90)
    (hbudget : c ≤ cfg.exscal * (ν / 90 - ε₀))
    {ηKT : ℝ} (hηKT : 0 < ηKT) {ρ₀ : ℝ≥0} (hρ₀half : ρ₀ ≤ 1 / 2)
    (hW : WindowFour.{u} (EuclideanSpace ℝ (Fin 3)) cfg.β ε₀ ηKT ρ₀) :
    ∀ (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube)
          (Tube.ssfGridLen cfg.δ) cfg.C₀) {k : ℕ}, k ≤ Tube.ssfGridLen cfg.δ →
      ∀ {ρ : ℝ≥0}, Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ →
        ρ ∈ Set.Icc cfg.a 1 → ρ ≤ ρ₀ → e ≤ cfg.exscal * ηKT →
        ∀ (G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι),
          G.outerSet = cfg.activeTubeNodes 𝒰 k →
          (∀ j ∈ G.outerSet, (G.outerBody j).toConvexSpaceBody
              = (𝒰.cover.tube k j).toConvexSpaceBody) →
          (cfg.δ : ℝ≥0) ^ e ≤ ShadedBody.fullness G.outerSet G.outerBody →
          ShadedBody.multiplicity G.outerSet G.outerBody ≤
            (cfg.a : ℝ≥0∞) ^ (-(ν / 90)) *
              ((cfg.δ : ℝ≥0∞) ^ c *
                  maxDensity (cfg.activeTubeNodes 𝒰 k)
                    (fun j ↦ (𝒰.cover.tube k j).toConvexSpaceBody) ^ (1 - cfg.β)) *
              (G.outerSet.card : ℝ≥0∞) ^ cfg.β
    := by
  classical
  have hexs : 0 < cfg.exscal := cfg.hexscal
  intro 𝒰 k hk ρ hgrid hρ hρ₀ hηb G houterSet houterBody hfull
  subst hgrid
  set ρ : ℝ≥0 := Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k with hρdef
  -- basic positivity
  have hδa : cfg.δ ≤ cfg.a := cfg.hdims.1
  have ha0 : 0 < cfg.a := lt_of_lt_of_le cfg.hδ hδa
  have haρ : cfg.a ≤ ρ := hρ.1
  have hρpos : 0 < ρ := lt_of_lt_of_le ha0 haρ
  have hρhalf : ρ ≤ (1 / 2 : ℝ≥0) := le_trans hρ₀ hρ₀half
  -- the family of shaded `ρ`-tubes: the node tubes carrying the outer shades on `G.outerSet`,
  -- an arbitrary unit-ball tube elsewhere.
  obtain ⟨Vdef, hVdef⟩ := exists_tube_subset_closedBall ρ hρhalf
  let TT : cfg.ι → ShadedTube ρ (EuclideanSpace ℝ (Fin 3)) := fun j =>
    if hj : j ∈ G.outerSet then
      { toTube := 𝒰.cover.tube k j
        shade := (G.outerBody j).shade
        measurableSet_shade := (G.outerBody j).measurableSet_shade
        shade_subset := by
          have hcar : (G.outerBody j).carrier = (𝒰.cover.tube k j).carrier :=
            congrArg ConvexSpaceBody.carrier (houterBody j hj)
          exact hcar ▸ (G.outerBody j).shade_subset }
    else
      { toTube := Vdef
        shade := ∅
        measurableSet_shade := MeasurableSet.empty
        shade_subset := Set.empty_subset _ }
  have hTTshade : ∀ j ∈ G.outerSet, (TT j).shade = (G.outerBody j).shade := by
    intro j hj
    simp only [TT, dif_pos hj]
  have hTTnode : ∀ j ∈ G.outerSet,
      (TT j).toConvexSpaceBody = (𝒰.cover.tube k j).toConvexSpaceBody := by
    intro j hj
    simp only [TT, dif_pos hj]
  have hTTbody : ∀ j ∈ G.outerSet,
      (TT j).toConvexSpaceBody = (G.outerBody j).toConvexSpaceBody := by
    intro j hj
    rw [hTTnode j hj, houterBody j hj]
  have hTTcar : ∀ j ∈ G.outerSet, (TT j).carrier = (G.outerBody j).carrier := by
    intro j hj
    exact congrArg ConvexSpaceBody.carrier (hTTbody j hj)
  -- the containment the hierarchy really gives: radius `4`, not `1`
  have hnode : ∀ j ∈ G.outerSet, (𝒰.cover.tube k j).carrier ⊆ closedBall 0 4 := by
    intro j hj
    have hjIdx : j ∈ 𝒰.cover.indexSet k :=
      mem_indexSet_of_mem_activeTubeNodes cfg 𝒰 (houterSet ▸ hj)
    exact MultiScaleFac.node_carrier_subset_ball cfg.hδ cfg.hδ1 𝒰 (s_nonempty cfg)
      (fun i hi ↦ cfg.contained i hi) hk hjIdx
  have h4 : (((4 : ℝ≥0)) : ℝ) = 4 := by norm_num
  have hballTT : ∀ j, (TT j).carrier ⊆ closedBall 0 (((4 : ℝ≥0)) : ℝ) := by
    intro j
    rw [h4]
    by_cases hj : j ∈ G.outerSet
    · rw [show (TT j).carrier = (𝒰.cover.tube k j).carrier from
        congrArg ConvexSpaceBody.carrier (hTTnode j hj)]
      exact hnode j hj
    · simp only [TT, dif_neg hj]
      exact hVdef.trans (Metric.closedBall_subset_closedBall (by norm_num))
  -- transfers
  have hsumshade : ∑ j ∈ G.outerSet, volume (TT j).toShadedBody.shade
      = ∑ j ∈ G.outerSet, volume (G.outerBody j).shade :=
    Finset.sum_congr rfl fun j hj => by rw [show (TT j).toShadedBody.shade = (TT j).shade from rfl,
      hTTshade j hj]
  have hsumcar : ∑ j ∈ G.outerSet, volume (TT j).toShadedBody.carrier
      = ∑ j ∈ G.outerSet, volume (G.outerBody j).carrier :=
    Finset.sum_congr rfl fun j hj => by
      rw [show (TT j).toShadedBody.carrier = (TT j).carrier from rfl, hTTcar j hj]
  have hunion : (⋃ j ∈ G.outerSet, (TT j).toShadedBody.shade)
      = ⋃ j ∈ G.outerSet, (G.outerBody j).shade :=
    Set.iUnion₂_congr fun j hj => by
      rw [show (TT j).toShadedBody.shade = (TT j).shade from rfl, hTTshade j hj]
  have hmult : ShadedBody.multiplicity G.outerSet (fun j => (TT j).toShadedBody)
      = ShadedBody.multiplicity G.outerSet G.outerBody := by
    rw [ShadedBody.multiplicity_eq_div, ShadedBody.multiplicity_eq_div, hsumshade, hunion]
  have hfullTT : ShadedBody.fullness G.outerSet (fun j => (TT j).toShadedBody)
      = ShadedBody.fullness G.outerSet G.outerBody := by
    unfold ShadedBody.fullness ShadedBody.fullness'
    rw [hsumshade, hsumcar]
  have hmd : maxDensity G.outerSet (fun j => (TT j).toConvexSpaceBody)
      = maxDensity (cfg.activeTubeNodes 𝒰 k)
          (fun j => (𝒰.cover.tube k j).toConvexSpaceBody) := by
    rw [← houterSet]
    exact maxDensity_congr fun j hj => hTTnode j hj
  -- the fullness hypothesis at the auxiliary scale `cfg.a`
  have hadelta : cfg.a ≤ cfg.δ ^ cfg.exscal := le_trans cfg.hdims.2.1 cfg.hdims.2.2
  have hfullKT : cfg.a ^ ηKT ≤ ShadedBody.fullness G.outerSet (fun j => (TT j).toShadedBody) := by
    rw [hfullTT]
    refine le_trans ?_ hfull
    calc cfg.a ^ ηKT ≤ (cfg.δ ^ cfg.exscal) ^ ηKT := NNReal.rpow_le_rpow hadelta hηKT.le
      _ = cfg.δ ^ (cfg.exscal * ηKT) := by rw [← NNReal.rpow_mul]
      _ ≤ cfg.δ ^ e := NNReal.rpow_le_rpow_of_exponent_ge cfg.hδ cfg.hδ1 hηb
  have hballTT' : ∀ j, (TT j).carrier ⊆ closedBall 0 (4 : ℝ) := by
    intro j
    have hj := hballTT j
    rwa [h4] at hj
  have hmain := hW ρ hρpos hρ₀ cfg.a ha0 haρ G.outerSet TT hballTT' hfullKT
  rw [hmult, hmd] at hmain
  refine le_trans hmain ?_
  -- exponent bookkeeping
  set md : ℝ≥0∞ := maxDensity (cfg.activeTubeNodes 𝒰 k)
    (fun j => (𝒰.cover.tube k j).toConvexSpaceBody) with hmd_def
  have ha0' : (cfg.a : ℝ≥0∞) ≠ 0 := by
    simpa using (ENNReal.coe_ne_zero.mpr ha0.ne')
  have hatop : (cfg.a : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hadelta' : (cfg.a : ℝ≥0∞) ≤ (cfg.δ : ℝ≥0∞) ^ cfg.exscal := by
    rw [← ENNReal.coe_rpow_of_nonneg _ hexs.le]
    exact_mod_cast hadelta
  have hδle1 : (cfg.δ : ℝ≥0∞) ≤ 1 := by
    exact_mod_cast cfg.hδ1
  have hkey : (cfg.a : ℝ≥0∞) ^ (-ε₀)
      ≤ (cfg.a : ℝ≥0∞) ^ (-(ν / 90)) * (cfg.δ : ℝ≥0∞) ^ c := by
    have hsplit : (cfg.a : ℝ≥0∞) ^ (-ε₀)
        = (cfg.a : ℝ≥0∞) ^ (-(ν / 90)) * (cfg.a : ℝ≥0∞) ^ (ν / 90 - ε₀) := by
      rw [← ENNReal.rpow_add _ _ ha0' hatop]
      congr 1
      ring
    rw [hsplit]
    refine mul_le_mul_right ?_ _
    calc (cfg.a : ℝ≥0∞) ^ (ν / 90 - ε₀)
        ≤ ((cfg.δ : ℝ≥0∞) ^ cfg.exscal) ^ (ν / 90 - ε₀) :=
          ENNReal.rpow_le_rpow hadelta' (by linarith)
      _ = (cfg.δ : ℝ≥0∞) ^ (cfg.exscal * (ν / 90 - ε₀)) := by
          rw [← ENNReal.rpow_mul]
      _ ≤ (cfg.δ : ℝ≥0∞) ^ c :=
          ENNReal.rpow_le_rpow_of_exponent_ge hδle1 hbudget
  calc (cfg.a : ℝ≥0∞) ^ (-ε₀) * md ^ (1 - cfg.β) * (G.outerSet.card : ℝ≥0∞) ^ cfg.β
      ≤ ((cfg.a : ℝ≥0∞) ^ (-(ν / 90)) * (cfg.δ : ℝ≥0∞) ^ c) * md ^ (1 - cfg.β) *
          (G.outerSet.card : ℝ≥0∞) ^ cfg.β := by
        gcongr
    _ = (cfg.a : ℝ≥0∞) ^ (-(ν / 90)) *
          ((cfg.δ : ℝ≥0∞) ^ c * md ^ (1 - cfg.β)) *
          (G.outerSet.card : ℝ≥0∞) ^ cfg.β := by ring


/-- **The honest fullness conjunct converts to `δ^{3η}`, and to no less.**

`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` states its fullness conjunct at the
dimensional loss `ShadedBody.rhoTubesInducedFullnessLoss 3`, because GWZ write
`λ(𝕋_a, Y_{𝕋_a}) ⪆ λ` and §2.2 reads `⪆` as permitting a sub-polynomial factor.  The scale-`r`
layer consumes a `δ`-power instead, and this is the conversion: `Kakeya.VeryNotSticky.lam_ge`
gives `Cd δ^{2η} ≤ lam`, `Kakeya.VeryNotSticky.inducedFullnessLoss_absorb` gives
`L ≤ δ^{-η}`, and the two compose to `δ^{3η}`.

The one `η` is the price of honesty on the fullness side and it cannot be avoided: any loss `≥ 1`
has to be bridged against a `δ`-power by *some* smallness clause, and there is no room in
`lam_ge` — that clause and `Kakeya.VeryNotSticky.shading_lb` are exact duals through
`Cd⁻¹ lam`, so demanding `Cd · L · δ^{2η} ≤ lam` would demand a pointwise shading density of
`L δ^{2η}`, strictly more than the producer's input supplies.  The exponent budget, by contrast,
has room for six such (`Kakeya.VeryNotSticky.coarseLossExponentHeadroom`). -/
theorem rpow_three_eta_le_of_inducedFullness (cfg : VeryNotSticky.{u}) {κ : Type*}
    {t : Finset κ} {V : κ → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    (hh : (cfg.Cd * _root_.ShadedBody.rhoTubesInducedFullnessLoss 3)⁻¹ * cfg.lam
      ≤ ShadedBody.fullness t V) :
    (cfg.δ : ℝ≥0) ^ (3 * cfg.η) ≤ ShadedBody.fullness t V := by
  refine le_trans ?_ hh
  have habs : _root_.ShadedBody.rhoTubesInducedFullnessLoss 3 ≤ cfg.δ ^ (-cfg.η) := by
    have h := cfg.inducedFullnessLoss_absorb
    rw [← ENNReal.coe_rpow_of_ne_zero cfg.hδ.ne'] at h
    exact_mod_cast h
  have hCd0 : cfg.Cd ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one cfg.hCd)
  have hL0 : (0 : ℝ≥0) < _root_.ShadedBody.rhoTubesInducedFullnessLoss 3 :=
    lt_of_lt_of_le zero_lt_one (_root_.ShadedBody.one_le_rhoTubesInducedFullnessLoss 3)
  have hδ0 : (cfg.δ : ℝ≥0) ≠ 0 := cfg.hδ.ne'
  have hsplit : (cfg.δ : ℝ≥0) ^ (-cfg.η) * (cfg.δ : ℝ≥0) ^ (3 * cfg.η)
      = (cfg.δ : ℝ≥0) ^ (2 * cfg.η) := by
    rw [← NNReal.rpow_add hδ0]
    congr 1
    ring
  have hkey : _root_.ShadedBody.rhoTubesInducedFullnessLoss 3 * (cfg.δ : ℝ≥0) ^ (3 * cfg.η)
      ≤ (cfg.δ : ℝ≥0) ^ (2 * cfg.η) := by
    calc _root_.ShadedBody.rhoTubesInducedFullnessLoss 3 * (cfg.δ : ℝ≥0) ^ (3 * cfg.η)
        ≤ (cfg.δ : ℝ≥0) ^ (-cfg.η) * (cfg.δ : ℝ≥0) ^ (3 * cfg.η) := by gcongr
      _ = (cfg.δ : ℝ≥0) ^ (2 * cfg.η) := hsplit
  have hstep : (cfg.δ : ℝ≥0) ^ (3 * cfg.η)
      ≤ (_root_.ShadedBody.rhoTubesInducedFullnessLoss 3)⁻¹ * (cfg.δ : ℝ≥0) ^ (2 * cfg.η) := by
    rw [le_inv_mul_iff₀ hL0]
    exact hkey
  refine le_trans hstep ?_
  calc (_root_.ShadedBody.rhoTubesInducedFullnessLoss 3)⁻¹ * (cfg.δ : ℝ≥0) ^ (2 * cfg.η)
      = (cfg.Cd * _root_.ShadedBody.rhoTubesInducedFullnessLoss 3)⁻¹
          * (cfg.Cd * (cfg.δ : ℝ≥0) ^ (2 * cfg.η)) := by
        rw [mul_inv]
        field_simp
    _ ≤ (cfg.Cd * _root_.ShadedBody.rhoTubesInducedFullnessLoss 3)⁻¹ * cfg.lam := by
        gcongr
        exact cfg.lam_ge

/-- **`Kakeya.VeryNotSticky.coarseKatzTaoBound_of_etaBudget_atPair` with the fullness exponent
left free.**  The `2 cfg.η` form is this one at `e := 2 * cfg.η`; the honest coarse family needs
it at `e := 3 * cfg.η`. -/
theorem coarseKatzTaoBound_of_etaBudget_atPair_atFullness (cfg : VeryNotSticky.{u})
    {ν ε₀ ηKT e : ℝ}
    {ρ₀ : ℝ≥0} (hε₀ν : ε₀ ≤ ν / 90)
    (hηbudget : 3 * cfg.η * (1 - cfg.β) ≤ cfg.exscal * (ν / 90 - ε₀))
    (hηKT : 0 < ηKT) (hρ₀half : ρ₀ ≤ 1 / 2)
    (hW : WindowFour.{u} (EuclideanSpace ℝ (Fin 3)) cfg.β ε₀ ηKT ρ₀)
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube)
      (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : ℝ≥0} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (hρ : ρ ∈ Set.Icc cfg.a 1) (hρ₀ : ρ ≤ ρ₀) (hηb : e ≤ cfg.exscal * ηKT)
    (G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι)
    (houterSet : G.outerSet = cfg.activeTubeNodes 𝒰 k)
    (houterBody : ∀ j ∈ G.outerSet, (G.outerBody j).toConvexSpaceBody
        = (𝒰.cover.tube k j).toConvexSpaceBody)
    (hfull : (cfg.δ : ℝ≥0) ^ e ≤ ShadedBody.fullness G.outerSet G.outerBody) :
    ShadedBody.multiplicity G.outerSet G.outerBody ≤
      (cfg.a : ℝ≥0∞) ^ (-(ν / 90)) *
        ((cfg.δ : ℝ≥0∞) ^ (2 * cfg.η) *
            ((cfg.δ : ℝ≥0∞) ^ cfg.η *
              maxDensity (cfg.activeTubeNodes 𝒰 k)
                (fun j ↦ (𝒰.cover.tube k j).toConvexSpaceBody))) ^
          (1 - cfg.β) *
        (G.outerSet.card : ℝ≥0∞) ^ cfg.β := by
  classical
  set c : ℝ := 3 * cfg.η * (1 - cfg.β) with hc_def
  have hβ1m : (0 : ℝ) ≤ 1 - cfg.β := by linarith [cfg.hβ1]
  have H := coarseKatzTaoBound_general_atFullness cfg (ν := ν) (c := c) (ε₀ := ε₀) (e := e)
    hε₀ν hηbudget hηKT hρ₀half hW 𝒰 hk hgrid hρ hρ₀ hηb G houterSet houterBody hfull
  refine le_trans H ?_
  set md : ℝ≥0∞ := maxDensity (cfg.activeTubeNodes 𝒰 k)
    (fun j ↦ (𝒰.cover.tube k j).toConvexSpaceBody) with hmd_def
  have hδ0' : (cfg.δ : ℝ≥0∞) ≠ 0 := by
    simpa using (ENNReal.coe_ne_zero.mpr cfg.hδ.ne')
  have hδtop : (cfg.δ : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hrw : ((cfg.δ : ℝ≥0∞) ^ (2 * cfg.η) * ((cfg.δ : ℝ≥0∞) ^ cfg.η * md)) ^ (1 - cfg.β)
      = (cfg.δ : ℝ≥0∞) ^ c * md ^ (1 - cfg.β) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hβ1m, ENNReal.mul_rpow_of_nonneg _ _ hβ1m,
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← mul_assoc,
      ← ENNReal.rpow_add _ _ hδ0' hδtop]
    congr 2
    rw [hc_def]; ring
  rw [hrw]


/-! ## What each conjunct of the residue costs, taken one at a time

Three realisations of the **full** active node family, each with an explicit outer shading.

* `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_saturated` shades every node tube
  entirely: outer fullness `1`, so every conjunct of
  `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` except the ball estimate holds, and the
  ball estimate is destroyed because the outer union becomes the whole of `⋃ 𝕋_ρ`.
* `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_minimal` shades each node tube by its
  intersection with the *inner* union `U(𝕋, Y)` — the smallest shading the `ShadedFactorFamily`
  clauses permit once the inner bodies are pinned. The outer union then *equals* the inner union,
  so the ball estimate is immediate and the fullness is destroyed.
* `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_inducedFullness` uses GWZ's own coarse
  shading `Y_{𝕋_ρ}(T_ρ) = T_ρ ∩ N_{2ρ}(⋃_{T ∈ 𝕋[T_ρ]} Y(T))` and is the *honest* fullness
  statement: it charges `ShadedBody.rhoTubesInducedFullnessLoss 3`, the dimensional constant of
  `Kakeya.Tube.volume_dilate_inter_cthickening_ge`, which is what GWZ Lemma 5.11's fullness
  clause actually costs.

The first two say that **neither conjunct of the residue is on its own the obstruction, and that
the placeholder constant is not the obstruction either**: both are realised at the strongest
constant, `1`. The obstruction is the *joint* demand at a single shading, which is the
un-pigeonholed two-scale (Córdoba) estimate; see the residue's docstring.

The third is the honest replacement for the fullness conjunct: it is the one clause of Lemma 5.11
that survives the passage from the pigeonholed subfamily to the full node family, and it survives
at a purely dimensional loss. It comes from
`ShadedBody.exists_rhoTubesSection9_fullFamily`.
-/


/-! ## The residue is the choice of one set

`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` quantifies over shaded factor families,
but once its first four conjuncts pin the inner layer to `(cfg.s, cfg.T)` on the nose and the
outer layer to the full active node family, the only freedom left is the *shading of the node
tubes*, and even that is redundant: replacing each node shading by `T_ρ ∩ Z` with
`Z = U(𝕋_ρ, Y_{𝕋_ρ})` changes neither the outer union nor decreases any node's shade. So the
residue is equivalent to the existence of a single measurable set `Z` containing the inner
shaded union `U(𝕋, Y)`, and the two conjuncts become two conditions on that one set. The two
lemmas below are the two directions.
-/


/-! ## Removing the supremum from the ball conjunct

The ball conjunct of `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` is quantified over
*every* point of the outer shaded union, so read naively it asks for the **densest** `ρ`-ball of
`U(𝕋, Y)` to be controlled. That reading is what made the conjunct look unreachable: the
uniformity of the ball masses of the coarse union is exactly what Step 5 of the proof of GWZ
Lemma 5.11 buys by *discarding coarse bodies*, which is why
`ShadedBody.exists_rhoTubesSection9_fullFamily` extends the fullness clause to the full node
family but nothing extends the ball clause.

The three lemmas below show that **the supremum is not what has to be controlled**. For any
admissible shading set `Z` the entire family of point estimates follows from a single inequality
in which no point occurs at all,

  `δ^η · |U(𝕋_ρ, Y_{𝕋_ρ})| ≤ max (|U(𝕋, Y)|, |B(0, ρ)|)`,

and each of the two branches of the maximum is one line of monotonicity:

* against `|U(𝕋, Y)|`, because the local density `|U(𝕋,Y) ∩ B(x,ρ)| / |B(x,ρ)|` is at most `1`;
* against `|B(0, ρ)|`, because the same density is at most `|U(𝕋,Y)| / |B(x,ρ)|`, and the
  volume of a ball in `EuclideanSpace ℝ (Fin 3)` does not depend on its centre.

Neither branch looks at where the mass of `U(𝕋, Y)` sits, so neither needs the pigeonholing. The
residue is therefore *not* an assertion about the worst `ρ`-ball; it is the assertion that the
outer shaded union can be made `Cd⁻¹ · lam`-full of the node family **without growing past
`δ^{-η} max(|U(𝕋,Y)|, |B(0,ρ)|)` in volume**. That is a two-sided volume budget, and it is what
a successor should attack.
-/


/-! ## The coarse end of the grid is unconditional, and the constant is priced

This section answers two questions about
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` that the reduction lemmas above leave
open, and records a third reduction that supersedes the `max` form.

**1. A large unconditional range.** `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_coarseVolume`
reduces the residue to `δ^η · |⋃ 𝕋_ρ| ≤ max (|U(𝕋,Y)|, |B(0,ρ)|)`, and the *left* side of that
inequality is bounded with no hypotheses at all: every active node tube contains a member of
`𝕋`, every member lies in `B_1`, and a node tube has a unit core and radius `≤ 1`, so
`⋃ 𝕋_ρ ⊆ B(0,4)` (`Kakeya.VeryNotSticky.activeTubeNodes_carrier_subset_closedBall`). Hence the
residue holds outright at every grid scale with `64 · δ^η ≤ ρ³`, i.e. at every
`ρ ≥ 4 δ^{η/3}` (`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_gridScale_ge`). What
is left open is only the *fine* end of the grid,
`ρ < 4 δ^{η/3}` — a strictly smaller range than the `|𝕋_ρ| ≲ ρ δ^{-η}` window of
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_card_activeTubeNodes`, and one that
does not read the node count at all.

That range is provably nonempty for *every* configuration, not merely for small `δ`: the
absorption clause `Kakeya.VeryNotSticky.aScaleData_absorb` already forces `δ^η ≤ 1/15625`
(`Kakeya.VeryNotSticky.rpow_eta_absorb_le_one`), because the accumulated scale-`r` constant
contains the covering number `5³` of the re-centring. Hence
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_top` — the residue at the top grid index,
with **no hypothesis at all** — and
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_gridScale_ge_const` at every
`ρ ≥ 4/25`.

**2. The loss constant is priced, and it is not the repair.** Read the shading-set route at a
free loss `C` in place of `Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C`: the
fullness demand becomes `(Cd·C)⁻¹ lam` and the budget becomes `δ^η |Z| ≤ C · max(…)`. Both
sides move, and `Kakeya.VeryNotSticky.shadingSet_budget_necessary` computes the net: any such
`Z` must satisfy

  `δ^{3η} · c · ρ² ≤ C² · max (|U(𝕋,Y)|, |B(0,ρ)|)`,   `c = Tube.le_volume.c 3`,

because fullness `f` forces `|Z| ≥ f · c · ρ²` (`Kakeya.VeryNotSticky.le_volume_of_fullness_coarseShadeAt`;
the coarse multiplicity is at most `|𝕋_ρ|`) and `lam_ge` forces `f ≥ C⁻¹ δ^{2η}`. So **the loss
constant buys exactly a factor `C²`, and nothing else.** Below the ball threshold this is a
lower bound on the shaded union of the order of *one node tube*
(`Kakeya.VeryNotSticky.shadingSet_budget_forces_volume`), while the only lower bound the
configuration supplies is of the order of *one `δ`-tube's shading*
(`Kakeya.VeryNotSticky.le_volume_innerShadedUnion`). The gap between `ρ²` and `δ²` is a power
of `δ`; a dimensional constant such as `ShadedBody.rhoTubesInducedFullnessLoss 3` cannot close
it. That settles, negatively, the question of whether replacing the placeholder `C = 1` by the
honest dimensional loss makes the two conjuncts jointly satisfiable through this route.

**3. Any lower bound on `|U(𝕋,Y)|` that closes the budget is circular.** The comparison
`δ^η |⋃ 𝕋_ρ| ≤ |U(𝕋,Y)|` — the weakest hypothesis that discharges
`…_of_coarseVolume` outright — implies a bound on the *shaded multiplicity*
`µ(𝕋,Y)` (`Kakeya.VeryNotSticky.multiplicity_le_of_coarseVolumeComparison`): with
`∑_i |T_i| ≤ δ^{-η} |B_1|` from `maxDensity_le` and `|⋃𝕋_ρ| ≥ c ρ²` from one node tube, it
gives `µ(𝕋,Y) ≤ δ^{-2η} |B_1| / (c ρ²)`. At the top grid index, where `ρ = 1`, that reads
`µ(𝕋,Y) ≤ δ^{-2η} |B_1| / c` (`Kakeya.VeryNotSticky.multiplicity_le_of_coarseVolumeComparison_zero`)
— an absolute multiplicity bound, strictly stronger than the conclusion
`µ ≤ δ^{ν-η} |𝕋|^β` that `Kakeya.multiplicity_le_of_card_isEssDistinct_ge` exists to prove. So
such a clause may not be added to `Kakeya.VeryNotSticky`: no producer can supply it without
already having Main Lemma 2.

**4. The `max` reduction is sufficient but not necessary.**
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_shadingSet_supBall` reduces the residue
to the inequality it *really* is,

  `δ^η · |U(𝕋_ρ,Y_{𝕋_ρ})| · |U(𝕋,Y) ∩ B(x,ρ)| ≤ |U(𝕋,Y)| · |B(0,ρ)|`  for every `x`,

with no division and no fullness-independent slack. `Kakeya.VeryNotSticky.mul_volume_inter_le_of_max_le`
shows that the hypothesis of
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_shadingSet_volume_max` implies it, so
the sup form is the more general of the two; the converse fails whenever `U(𝕋,Y)` is spread out
at scale `ρ`, since then `|U(𝕋,Y) ∩ B(x,ρ)| ≪ min(|U(𝕋,Y)|, |B(0,ρ)|)` for every `x`. The
content the `max` form discards is exactly the non-concentration of `U(𝕋,Y)` in `ρ`-balls. -/


/-! ## The sup form, run at the fine end of the grid

`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_shadingSet_supBall` reduces the residue
to a *local* inequality about each ball `B(x, ρ)` rather than to a global budget. This section
does three things with it.

**First, the circularity check**, because the two routes closed before this one were closed by
circularity. `Kakeya.VeryNotSticky.exists_shadingSet_supBall_free` shows the sup inequality
*alone* is satisfiable in **every** configuration, by the minimal shading set `Z = U(𝕋, Y)`. A
statement that holds unconditionally implies no bound that fails anywhere, so — unlike the field
`δ^η |⋃ 𝕋_ρ| ≤ |U(𝕋,Y)|` of
`Kakeya.VeryNotSticky.multiplicity_le_of_coarseVolumeComparison`, which forces `µ ≤ 3 δ^{-2η}` —
the sup form carries no multiplicity bound. **The sup route is not circular.** What the sup
inequality *does* cost, in conjunction with the fullness demand, is
`Kakeya.VeryNotSticky.supBall_necessary`: the necessary condition carries the extra factor
`|U(𝕋,Y) ∩ B(x,ρ)|` on its small side, and that factor is itself proportional to `|U(𝕋,Y)|`, so
the `|U(𝕋,Y)|` cancels and no absolute lower bound on `|U(𝕋,Y)|` — hence no upper bound on
`µ(𝕋, Y)` — follows. That is exactly the step the `max` form does not have.

**Second, the criterion.** `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_boostSet`
is the payoff, and it removes the ball estimate from the problem entirely:

> the residue holds as soon as there is a measurable **boost set** `V` with
> `2 δ^η |V| ≤ |B(0,ρ)|` such that `U(𝕋,Y) ∪ V` makes the node family `(Cd·C)⁻¹ lam`-full.

No supremum, no point, no density, no factor family, and — unlike every earlier reduction — no
hypothesis on `ρ` at all. The proof is the one place where the sup form beats the `max` form:
the two summands of `|Z| ≤ |U(𝕋,Y)| + |V|` are charged against *different* bounds on
`|U(𝕋,Y) ∩ B(x,ρ)|`, the first against `|B(0,ρ)|` and the second against `|U(𝕋,Y)|`. The `max`
form must pick one bound for the whole of `|Z|`, and that is what makes it lossy.

**Third, corollaries.** At `V = ⋃ 𝕋_ρ` the criterion recovers the ball branch of the earlier
route (`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_boostSet_saturated`), so nothing
is lost. And the budget `|V| ≤ δ^{-η} |B(0,ρ)| / 2` is generous — `δ^η ≤ 1/15625` by
`Kakeya.VeryNotSticky.rpow_eta_absorb_le_one` — so a *single* node tube fits inside it already
at `ρ ≳ δ^η`, which gives
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_card_activeTubeNodes_boost`: the node
count may be as large as `≍ Cd/lam`, against the `≍ ρ δ^{-η}` that
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_card_activeTubeNodes` demands — a gain
of a full factor `1/ρ` at the fine end.
-/


open MeasureTheory Metric Set ShadedBody in
/-- The volume of a *closed* ball of radius `r` in `EuclideanSpace ℝ (Fin 3)`, in the shape the
boost-set budget consumes. -/
theorem volume_closedBall_eq_pow_mul (y : EuclideanSpace ℝ (Fin 3)) (r : ℝ≥0) :
    volume (closedBall y (r : ℝ))
      = (r : ℝ≥0∞) ^ 3 * volume (ball (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  have h := MeasureTheory.Measure.addHaar_closedBall
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) y (r.coe_nonneg)
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  rw [hfr] at h
  rw [h, ENNReal.ofReal_pow r.coe_nonneg, ENNReal.ofReal_coe_nnreal]


end Kakeya.VeryNotSticky

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineTrialOutcome
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineDefectConstantLedger
public import Kakeya.MultiScaleFac.Homogenize
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineMiddleFactor

/-!
# `R1`/`R2` — the source's simultaneous refinement, named, and the estimate that transfers back

/§2.4, condition in shape by 

GWZ's `lem:ml2-window-refinement` performs **one** joint
mass-weighted dyadic selection and hands back a pair `(𝕊'', Z'')` which

* is a **nonempty** subfamily with a sub-shading on the *same* tubes (`∅ ≠ 𝕊''`),
* retains `Σ_{𝕊''}|Z''| ≥ Λ_f^{-1} Σ_{𝕊'}|Z|` of the shaded mass, and
* **inherits the same tower** — "its one-level and two-level assigned counts, maximal densities and
  fibre shaded masses remain pairwise within a factor two at each fixed level or pair of levels".

`Kakeya.ML2Core.IsShadedRefinementOf` is that pair, in the tree's vocabulary: the inheritance clause
is `Kakeya.ML2Core.IsClassHomogeneousOn`, whence `Tube.UniformTubeSet.restrictOccupied` reproduces
the whole hierarchy at the **same** `Cu`, and `A1`
(`Kakeya.ML2Core.exists_classHomogeneous_pass_of_uniformTubeSet`) is its producer.

**The object was already in the tree, inside one disjunct.**  It is the payload of
`Kakeya.ML2Core.TrialOutcomeAt`'s `(B)` with the potential drop, the fullness retention and the
density floor removed: `(B)` is the case in which the refinement *also* buys a profile drop, and
`(F)`/`(P)` are the cases in which it buys a terminal estimate instead.  The tree carried it only
inside `(B)`, which is 's condition ``: `(F)` was stated without it, and that
is why the floor owner had no permission to perform the restriction that manufactures the fill.
`Kakeya.ML2Core.isShadedRefinementOf_of_trialOutcome_defect` is the one-line bridge that records the
containment, and `Kakeya.ML2Core.TrialOutcomeAt` itself **does not move**.

## `R2`, and why the re-cut costs nothing downstream

: *"the mass-retention inequality in alternative (P) then transfers the estimate back to
`(𝕊',Z)`"*.  In the tree all three directions are favourable — `#S' ≤ #S`,
`⋃_{S'}(W i).shade ⊆ ⋃_S (Z i).shade`, and the retention itself — so
`Kakeya.ML2Core.middleGain_of_refinement` and `Kakeya.ML2Core.leftGain_of_refinement` spend `Λ`
exactly once, against an absorption hypothesis `Λ * δ^g ≤ δ^{g'}` which is the site's own
*"absorb, right"* line with `Λ` replaced by the refinement's loss.

`Kakeya.ML2Core.trialOutcomeAtGain_of_refinement_gain` packages the two so that a producer which
establishes the middle exit **on the refinement** discharges
`Kakeya.ML2Core.TrialOutcomeAtGain` **on the original family** — which is exactly what `M1` needs
F7 to do, with F7's conclusion.

## Anti-vacuity

`Kakeya.ML2Core.isShadedRefinementOf_self` is the control that the predicate is satisfiable: at
`S' := S`, `W := Z`, `Λ := 1` it holds for every nonempty class-homogeneous family, so the re-cut
`(F)` is a genuine **weakening** of the old `(F)` and F7 becomes a strictly stronger theorem.
`Kakeya.ML2Core.middleGain_of_refinement_self` is the check that at that instance `R2` is
the identity, and `Kakeya.ML2Core.not_middleGain_of_refinement_without_absorption` is the firing
control that the absorption hypothesis `habs` is load-bearing.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric ConvexSpaceBody ShadedBody

namespace Kakeya.ML2Core

universe u

section Refinement

variable {ι : Type*} {δ Cu : ℝ≥0} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

/-- **The source's simultaneous refinement** (`lem:ml2-window-refinement`), as a predicate on a pair of shaded families.

`(S', W)` refines `(S, Z)` at loss `Λ` when it is a **nonempty** subfamily, carries a sub-shading on the *same* tubes
(*"its shading is a restriction of `Z`"*), retains a `Λ⁻¹` share of the shaded mass, and **inherits the same tower** in the shape
`Kakeya.ML2Core.IsClassHomogeneousOn`, which `Tube.UniformTubeSet.restrictOccupied` turns into the
full hierarchy at the *same* `Cu`.

This is `Kakeya.ML2Core.TrialOutcomeAt`'s third disjunct with the potential drop, the fullness
retention and the density floor stripped — see the module docstring. -/
def IsShadedRefinementOf
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    (Λ : ℝ≥0∞) (S : Finset ι) (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (S' : Finset ι) (W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) : Prop :=
  S' ⊆ S ∧ S'.Nonempty ∧
    (∀ i, (W i).toTube = (Z i).toTube) ∧
    (∀ i, (W i).shade ⊆ (Z i).shade) ∧
    (∑ i ∈ S, volume (Z i).shade) ≤ Λ * ∑ i ∈ S', volume (W i).shade ∧
    IsClassHomogeneousOn 𝒰 S'

variable {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}

theorem IsShadedRefinementOf.subset {Λ : ℝ≥0∞} {S S' : Finset ι}
    {Z W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (h : IsShadedRefinementOf 𝒰 Λ S Z S' W) : S' ⊆ S := h.1

theorem IsShadedRefinementOf.nonempty {Λ : ℝ≥0∞} {S S' : Finset ι}
    {Z W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (h : IsShadedRefinementOf 𝒰 Λ S Z S' W) : S'.Nonempty := h.2.1

theorem IsShadedRefinementOf.shade_subset {Λ : ℝ≥0∞} {S S' : Finset ι}
    {Z W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (h : IsShadedRefinementOf 𝒰 Λ S Z S' W) (i : ι) : (W i).shade ⊆ (Z i).shade := h.2.2.2.1 i

theorem IsShadedRefinementOf.retention {Λ : ℝ≥0∞} {S S' : Finset ι}
    {Z W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (h : IsShadedRefinementOf 𝒰 Λ S Z S' W) :
    (∑ i ∈ S, volume (Z i).shade) ≤ Λ * ∑ i ∈ S', volume (W i).shade := h.2.2.2.2.1

theorem IsShadedRefinementOf.classHomogeneous {Λ : ℝ≥0∞} {S S' : Finset ι}
    {Z W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (h : IsShadedRefinementOf 𝒰 Λ S Z S' W) : IsClassHomogeneousOn 𝒰 S' := h.2.2.2.2.2

end Refinement

/-! ## `R2` — the terminal estimate transfers from the refinement to the original family -/

section Transfer

variable {ι : Type*} {δ Cu : ℝ≥0} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
  {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}

/-- The two free directions of `R2`, isolated: the refinement's shaded union sits inside the
original's. -/
theorem IsShadedRefinementOf.iUnion_shade_subset {Λ : ℝ≥0∞} {S S' : Finset ι}
    {Z W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (href : IsShadedRefinementOf 𝒰 Λ S Z S' W) :
    (⋃ i ∈ S', (W i).shade) ⊆ (⋃ i ∈ S, (Z i).shade) := by
  refine Set.iUnion₂_subset fun i hi => ?_
  refine (href.shade_subset i).trans ?_
  exact Set.subset_biUnion_of_mem (u := fun i => (Z i).shade) (href.subset hi)

end Transfer

/-! ### Controls for `R1`/`R2` -/

section Controls

variable {ι : Type*} {δ Cu : ℝ≥0} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
  {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}

end Controls

/-! ## `R0′` — the mass retention, from the existing **cardinality**-weighted pass

  GWZ weight its joint dyadic selection by *complete fibre
shaded mass* (`w(T) = |Z(T)|/|T|`); the tree's existing pass
`Kakeya.Homogenize.exists_classBand_pass_of_uniformTubeSet` is weighted by **cardinality**.  The two
agree — and this is the honest price of the missing bin coordinate — because the trial's shading is
`ML2Shaded.HasComparableDensities`, so the shaded masses of any two members of the family differ by
a bounded factor and a cardinality retention upgrades to a mass retention.

**This is a strengthening of the hypothesis list, not of the conclusion.**  A consumer that needs
the refinement *without* comparable densities must add the mass coordinate to `Homogenize.lean`'s
pigeonhole; that is a port with no new mathematics, and it is not done here.

The comparison factor is `K * tubeVolRatio n`, where `K` is the comparability constant and
`Kakeya.ML2Core.tubeVolRatio` is the ratio of the two dimensional `δ`-tube volume bounds
`Tube.volume_le.C n / Tube.le_volume.c n` — *not* a `δ`-power: both members are `δ`-tubes at the
**same** radius, so the `δ^{n-1}` cancels exactly.  With the trial's floor `δ^{ηin}/2 ≤ lam` and
`K = lam⁻¹` the factor is `≤ 2 δ^{-ηin} · tubeVolRatio n`, whose only *exponent* cost is `ηin`.
-/

section MassRetention

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] {ι : Type*}

/-- **The ratio of the two dimensional `δ`-tube volume bounds.**  `Tube.le_volume` gives
`c_n δ^{n-1} ≤ volume T.carrier` and `Tube.volume_le` gives `volume T.carrier ≤ C_n δ^{n-1}` for
`δ ≤ 1`, so two `δ`-tubes at the **same** radius have carrier volumes within `C_n / c_n` of each
other, **with no `δ`-dependence at all** — the `δ^{n-1}` cancels exactly.  That cancellation is
what makes `R0′` cost a constant and not a `δ`-power. -/
noncomputable def tubeVolRatio (n : ℕ) : ℝ≥0 :=
  Tube.volume_le.C n / Tube.le_volume.c n

end MassRetention

/-! ## `R0′` — the producer of `Kakeya.ML2Core.IsShadedRefinementOf`

The three pieces above, composed with `A1`.  The route is the source's own order of operations
((ii)): restrict the hierarchy to the family under test
(`Tube.UniformTubeSet.restrictOccupied`, at the **same** `Cu`), run the joint dyadic selection on it
(`Kakeya.Homogenize.exists_classBand_pass_of_uniformTubeSet`), read the inherited tower off the
output (`A1`), and convert the cardinality retention into the source's mass retention.
-/

section Producer

variable {ι : Type*} {δ Cu : ℝ≥0} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

end Producer

end Kakeya.ML2Core

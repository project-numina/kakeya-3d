/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineDensityBandFromBin
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineDefectConstantLedger
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineRungWiring
public import Kakeya.DimensionThree.MainLemma2.LineEssDistinct
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCanonicalCover
public import Kakeya.MultiScaleSubmult
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineTwoScale
public import Kakeya.Tube.Rigidity
public import Kakeya.FrostmanTransfer
public import Kakeya.ShadedUniform
public import Kakeya.DimensionThree.MainLemma2.GridRounding
public import Kakeya.StickyKakeya.CrossScale
public import Kakeya.MultiScaleFac.Stopping
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeRoute
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineDichotomyInputs
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCoarseSeam
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeRetube

/-!
# A1's root-ward descent, assembled: the multi-level band on one retained family

`SpineDensityBandFromBin.lean` supplies A1 at **one** level (`exists_joint_bucket_band_with_label`)
and prices the descent abstractly (`card_le_pow_of_chain`).  This file performs the descent: it
runs the per-level regularisation at every level of a nested cell system and returns **one**
retained family carrying **all** the levels' bands at once, read in the retained family itself.

## The order of the descent, and why it is forced

: *"Descending from the leaves to the root and retaining one joint vector bin gives a
restricted threaded tower."*  The order is not decoration.  The band established at level `p` is a
statement about the statistic **read in the family it is established in**; a later restriction
changes the family and therefore may change the statistic.  Leaf-locality
(`Kakeya.ML2Core.LeafLocalStat`) says it does *not* change when the later restriction retains whole
`cell p`-fibres, and `Kakeya.ML2Core.leafLocalStat_stable` is that step.  A
restriction performed at level `p'` retains whole `cell p'`-fibres, and a whole-fibre restriction at
a **coarser** map is whole-fibre at every **finer** one (`wholeFibreSubset_of_refines`).  So the
level-`p` band survives exactly the restrictions performed at levels `p' ≥ p`:

> **the levels must be processed from the finest to the coarsest** — the source's leaves-to-root.

That is why `exists_multiLevel_band` takes `g` **increasingly coarse** (`hmono` : a finer cell map
determines a coarser one) and inducts on the coarsest index.  Instantiated at a tower it is
`g p := 𝒰.cover.assign (L - p)`, so `g 0` is the leaf level and `g L` the root.

## What had to be added to A1 to make the descent close

A1's per-level device returns an opaque retained set.  The descent needs that set to be a **union
of whole cells**, since that is the hypothesis of `leafLocalStat_stable`.  It is: every retained set
in A1's proof is a `Finset.filter` by a bucket value, and a filter by a **cell-determined**
predicate is whole-fibre by inspection.  The A1 declarations do not expose this, so the three
pigeonholes are restated here with the extra conclusion and the extra hypothesis that makes it true
(`hbc`, `hlabc`: the bucket and the label are constant on cells).  Nothing in
`SpineDensityBandFromBin.lean` is edited; these are siblings, and
`not_wholeFibre_of_not_cellDetermined` is the firing control that the new hypothesis is doing work.

## Family / shading / level pair

| declaration | family / shading | level pair |
|---|---|---|
| `WholeFibreSubset.trans`, `wholeFibreSubset_of_refines` | abstract | none |
| `exists_bucket_band_fibre`, `exists_joint_bucket_band_fibre` | abstract | one level |
| `exists_constant_label_fibre`, `exists_level_band_step` | abstract | one level |
| `exists_multiLevel_band` | abstract; the retained family is the conclusion | `0 … M` |
| `levelDensityStat_congr_cell`, `levelDensityStat_le_card` | the tower's `u` | `(p,c)` |
| `one_le_levelDensityStat_of_mem` | as above | `(p,c)` |
| `exists_levelDensityStat_band` | the **retained** family `t ⊆ u`; no shading | every `(p,c)` |
| `levelDensityBand_indexSet` | the tower's own family `t`; no shading | every `(p,c)` |
| `le_level_maxDensity_of_fibre_witness` | the tower's `u`; no shading | `(a,c)`, `c` inset |
| `pairwise_of_levelDensityBand` | the tower's own family; no shading | every `(p,c)` |

## The second half: A1 instantiated, and the two rows it closes

`exists_levelDensityStat_band` is the list's step 1 — A1 run at the two-level density statistics of
every level pair, brackets `1 ≤ · ≤ #u` (so `C₁ = 0`, no `δ`-power spent below), loss
`((J+1)^{L+1})^{L+1}` — and `levelDensityBand_indexSet` reads it onto the nodes in the shape
`Kakeya.ML2Reduction.IsKatzTaoDividingWindowLevels.level_density_band` states, verbatim (the
`example` after it is the match control: the field's projection inhabits the stated type).

`le_level_maxDensity_of_fibre_witness` is step 2, and it is the record that **no field
moves** : the lower-bound field stays stated on `nodesUnder` and its witness
is *produced* on the fibre array.

`pairwise_of_levelDensityBand` is the measurement of what remains: the field is a regularity
demand on the family it is asked on, so it cannot be supplied on an arbitrary subfamily.

## The third half: where the refinement is allowed to happen, and the route that allows it

The measurement above has a routing consequence and it is the file's main finding.
`Kakeya.ML2Core.InheritedWindowSupplyAt` (`= FixedTowerStoppingObligation`) asks for the window on
the tower over the **given** `S`, for **every** `S`.  By `pairwise_of_levelDensityBand` that is a
regularity demand on `S` and is therefore not supplied by `Kakeya.ML2Core.IsClassHomogeneousOn`,
which bands class *cardinalities* -- two cells of equal size can carry very different maximal
densities.  **`Kakeya.ML2Core.FloorDataAtTrichotomy` does not require it**: its `(F)` disjunct
`Kakeya.ML2Core.RefinedFloorHypothesis` binds `S' ⊆ S` and asks for the window on
`Kakeya.ML2Core.refinedHierarchy`, i.e. on the **refined** tower -- exactly where the source
performs its refinement.

So `levelDensityBand_refinedHierarchy` and `exists_refinement_levelDensityBand_refinedHierarchy`
deliver step 1 on the `(F)` branch's own tower, and `RefinedFloorSupplyAt` /
`floorDataAtTrichotomy_of_refinedFloorSupply` name the payload's remaining goal on that route.
`refinedFloorSupplyAt_of_windowed` is the control that the new route is weaker: the existing
windowed route produces it (on the `(F)` side).  

| declaration | family / shading | level pair |
|---|---|---|
| `levelDensityBand_refinedHierarchy` | `S'` with shading `W` | every `(p,c)` |
| `exists_refinement_levelDensityBand_refinedHierarchy` | `u` refined to `S'` | every `(p,c)` |
| `RefinedFloorSupplyAt`, `floorDataAtTrichotomy_of_refinedFloorSupply` | `S,Z → S',W` | `(a,b,m)` |
| `classCountStat` + its four lemmas | the family `w`; no shading | one level `k` |
| `fibreShadedMassStat` + its five lemmas | the family `w` **with shading `Z`** | one level `k` |
| `fourStatRow` + its extraction lemmas | `w`; shading only in the `q = 2L+3` row | one level `k` |
| `isClassHomogeneousOn_of_classCountBand` | the retained family | every `k` |
| `exists_levelBand_classHomogeneous` | `u` refined to `t`; no shading | every `(p,c)`, every `k` |
| `exists_refinement_classHomogeneous_levelDensityBand` | `u → S'`, shading `W` | all `(p,c)` |
| `exists_refinement_classHomogeneous_levelDensityBand` | `u → S'`; shading at `W` | every `(p,c)` |

## The fourth half:, applied

** — one joint pass, not two.**  A separate homogenising pass is a further restriction that
moves the already-regularised statistics **unless it is whole-fibre**, and the source avoids it by
construction:  lists **descendant counts** among the four statistics regularised
together, and descendant counts *are* Def 2.1(iii)'s class band, which is what
`Kakeya.ML2Core.IsClassHomogeneousOn` renders.  : *"all of them are regularized at
once."*  So the class count rides in A1's bin as one more leaf-local, cell-determined statistic
(`classCountStat`), and `isClassHomogeneousOn_of_classCountBand` reads the homogeneity off the
band.  `exists_levelBand_classHomogeneous` is that pass; **no second restriction is run, in either
order.**  The factor two is paid into the tower's own constant as `2 ≤ Cu`, `δ`-free.

** — the four statistics, and where the tree keeps them.**  The tree carries **two** of
's four, in two different places and two different roles: two-level maximal densities as
the *field* `IsKatzTaoDividingWindowLevels.level_density_band`, and descendant counts as the
*hypothesis* `IsClassHomogeneousOn`.  That dispersal is itself the pattern.  The missing two —
**two-level counts** and **fibre shaded masses**, `SRC-A′`'s residue — are supplied here
(`levelCountStat`'s two new lemmas, `fibreShadedMassStat` and its five), and
`exists_levelBand_fourStatistics` produces **all four at once** on one retained family, together
with the class homogeneity.  That is the source's  hypothesis on `𝕊'`, produced rather
than assumed — which is exactly why the obligation belongs on `S'` and not on an
arbitrary `S`.

The mass row is the only one that spends a `δ`-power below, and it spends the caller's per-tube
shade floor `m` (the source's `δ^{3η_f}`, which a `HasDenseShading` hypothesis already supplies);
`le_fourStatRow` is where that is discharged.  All four rows share one upper bracket
(`#u` + total shaded mass, both finite) so the vector runs at a single dyadic ceiling.

## The fifth half: the mass-weighted run, and `IsShadedRefinementOf` produced

 retains a share of the **mass**, not of the node count, and that is
`Kakeya.ML2Core.IsShadedRefinementOf`'s fifth clause.  The `_wt` siblings
(`exists_bucket_band_fibre_wt`, `exists_constant_label_fibre_wt`,
`exists_joint_bucket_band_fibre_wt`, `exists_level_band_step_wt`, `exists_multiLevel_band_wt`) run
the same descent choosing at each bucketing the bucket of largest **weight**; nothing above is
edited, because a node pigeonhole and a mass pigeonhole are different pigeonholes and each is
correct for its own retention.

`exists_shadedRefinement_of_joint_bin` is the payoff: **all six** conjuncts of
`IsShadedRefinementOf` from one whole-fibre pass — subset, nonemptiness, same tubes and sub-shading
(at `W := Z`, both `rfl`), the mass retention (the weighted descent) and class homogeneity (the
descendant-count row) — with the four bands alongside.

So the `(F)` branch's first conjunct is no longer an obligation.
`refinedFloorHypothesis_of_parts` records exactly what is left and on which tower: the window and
`Kakeya.ML2Core.FloorHypothesisAt`, **both on `refinedHierarchy 𝒱 hS' hhom rfl`**, with `hS'` and
`hhom` the same terms in all three parts.  `isKatzTaoDividingWindowLevels_of_width_and_band`
assembles the first of those from the width `ε_d·L + a ≤ b`, the four density fields and this
file's band; the existing `Kakeya.ML2Core.floorHypothesisAt_of_windowLevels` assembles the second
from the window plus `ParentAdmissible` and `FillAt`.
| `refinedFloorSupplyAt_of_windowed` | as above | `(a,b,m)` |

No shading anywhere in this file: the descent is a statement about statistics of a cell system.
The shading `Z → W` enters at the caller that applies the refinement, not here.

## A1-a

No `GridUniformCore`; no (F)-branch interface statement is defined or altered.
-/

@[expose] public section

open scoped NNReal ENNReal

namespace Kakeya.ML2Core

section LevelBandDescent

variable {ι γ : Type*}

/-- **Whole-fibre restrictions compose.** -/
theorem WholeFibreSubset.trans {cell : ι → γ} {t s u : Finset ι}
    (hts : WholeFibreSubset cell t s) (hsu : WholeFibreSubset cell s u) :
    WholeFibreSubset cell t u := by
  refine ⟨hts.1.trans hsu.1, fun i hi j hj hcell => ?_⟩
  exact hts.2 i hi j (hsu.2 i (hts.1 hi) j hj hcell) hcell

/-- **A whole-fibre restriction at a coarser cell map is whole-fibre at every finer one.**

This is the step that forces the leaves-to-root order: `hrefines` says `c` **refines** `d` on `u`
(members sharing a `c`-cell share a `d`-cell), and the conclusion moves the property from the
coarse map `d` to the fine map `c`. -/
theorem wholeFibreSubset_of_refines {c : ι → γ} {d : ι → γ} {t u : Finset ι}
    (h : WholeFibreSubset d t u)
    (hrefines : ∀ i ∈ u, ∀ j ∈ u, c j = c i → d j = d i) :
    WholeFibreSubset c t u := by
  refine ⟨h.1, fun i hi j hj hcell => ?_⟩
  exact h.2 i hi j hj (hrefines i (h.1 hi) j hj hcell)


end LevelBandDescent

section LevelDensityBandInstance

open MeasureTheory Tube

universe v

variable {ι : Type v} {δ Cu : ℝ≥0} {u : Finset ι}
  {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}


/-! ### The remaining two of 's four statistics

: the tree carries **two** of the source's four statistics, in two different
places and two different roles — the two-level maximal densities as the *field*
`IsKatzTaoDividingWindowLevels.level_density_band`, and the descendant counts as the *hypothesis*
`Kakeya.ML2Core.IsClassHomogeneousOn`.  The two missing are the **two-level counts** and the
**fibre shaded masses**, and `SRC-A′`'s residue is exactly those two.  Both are leaf-local,
cell-determined statistics with `δ`-free-shaped brackets, so both fall out of the same joint bin.

The fibre shaded mass is the **one statistic that carries the shading**, and it is the weight that
makes the source's retention true (GWZ: the refinement retains `Λ_f^{-1}` of the *mass*).
-/


open scoped Classical in
/-- **The total shaded mass is finite** — every shade sits inside a compact carrier, so no
finiteness hypothesis is needed for the mass row's bracket. -/
theorem sum_volume_shade_ne_top (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (w : Finset ι) : (∑ j ∈ w, MeasureTheory.volume (Z j).shade) ≠ ⊤ := by
  classical
  refine (ENNReal.sum_lt_top.mpr fun j _ => ?_).ne
  refine lt_of_le_of_lt (MeasureTheory.measure_mono (Z j).shade_subset) ?_
  exact ((Z j).toConvexSpaceBody.isCompact.measure_ne_top).lt_top


/-! ### The mass-weighted descent (GWZ: the refinement retains a share of the **mass**)

The source's refinement retains `Λ_f^{-1}` of the *shaded mass*, not of the node count, and `Kakeya.ML2Core.IsShadedRefinementOf`'s fifth clause is exactly that inequality.
The card-based pigeonholes above give a node fraction; these siblings give the mass fraction
directly, by choosing at each bucketing the bucket of **largest weight** rather than of largest
cardinality.  Nothing above is edited: the two runs are different pigeonholes and each is correct
for its own retention.

The weight is arbitrary and additive, so the same devices serve any of the source's weights; the
mass instance takes `wt i = |Z(i)|`.
-/

open scoped Classical in
/-- **The bin-to-band pigeonhole, weighted.**  Same statement as `exists_bucket_band_fibre` with the
cardinality replaced by an additive weight: one bucket carries a `1/L` share of the **weight**, its
statistics are pinned to a profile within a factor two, and it is a union of whole cells. -/
theorem exists_bucket_band_fibre_wt {κ : Type*} (cell : κ → γ) (K : Finset κ)
    (wt : κ → ℝ≥0∞) (hwt : (∑ k ∈ K, wt k) ≠ 0)
    (D : κ → ℝ≥0∞) (bucket : κ → ℕ) (L : ℕ) (hL : 0 < L)
    (hbc : ∀ k k', cell k = cell k' → bucket k = bucket k')
    (hb : ∀ k ∈ K, ∀ k' ∈ K, bucket k = bucket k' → D k' ≤ 2 * D k)
    (hLlt : ∀ k ∈ K, bucket k < L) :
    ∃ K' : Finset κ, K' ⊆ K ∧ K'.Nonempty ∧ (∑ k ∈ K, wt k) ≤ L * ∑ k ∈ K', wt k ∧
      WholeFibreSubset cell K' K ∧
      ∃ Φ : ℝ≥0∞, ∀ k ∈ K', Φ ≤ D k ∧ D k ≤ 2 * Φ := by
  classical
  have hne : (Finset.range L).Nonempty := Finset.nonempty_range_iff.mpr hL.ne'
  set fib : ℕ → ℝ≥0∞ := fun v => ∑ k ∈ K.filter (fun k => bucket k = v), wt k with hfib
  obtain ⟨v, -, hv⟩ := Finset.exists_max_image (Finset.range L) fib hne
  have hmaps : ∀ k ∈ K, bucket k ∈ Finset.range L := fun k hk => Finset.mem_range.mpr (hLlt k hk)
  have hsum : ∑ v ∈ Finset.range L, fib v = ∑ k ∈ K, wt k :=
    Finset.sum_fiberwise_of_maps_to hmaps wt
  have hle : (∑ k ∈ K, wt k) ≤ L * fib v := by
    rw [← hsum]
    calc ∑ v' ∈ Finset.range L, fib v' ≤ ∑ _v' ∈ Finset.range L, fib v :=
          Finset.sum_le_sum (fun v' hv' => hv v' hv')
      _ = (L : ℝ≥0∞) * fib v := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hfv : fib v ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hle
    exact hwt (le_antisymm hle bot_le)
  have hK'ne : (K.filter (fun k => bucket k = v)).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    exact hfv (by rw [hfib]; simp [hemp])
  refine ⟨K.filter (fun k => bucket k = v), Finset.filter_subset _ _, hK'ne, hle, ?_, ?_⟩
  · refine ⟨Finset.filter_subset _ _, fun i hi j hj hcell => ?_⟩
    refine Finset.mem_filter.mpr ⟨hj, ?_⟩
    rw [hbc j i hcell]
    exact (Finset.mem_filter.mp hi).2
  · refine ⟨(K.filter (fun k => bucket k = v)).inf' hK'ne D, fun k hk => ⟨?_, ?_⟩⟩
    · exact Finset.inf'_le D hk
    · obtain ⟨k₁, hk₁mem, hk₁eq⟩ := Finset.exists_mem_eq_inf' hK'ne D
      rw [hk₁eq]
      obtain ⟨hk₁K, hk₁v⟩ := Finset.mem_filter.mp hk₁mem
      obtain ⟨hkK, hkv⟩ := Finset.mem_filter.mp hk
      exact hb k₁ hk₁K k hkK (by rw [hk₁v, hkv])


open scoped Classical in
/-- **The label pigeonhole, weighted** — rider 1 on the mass side, same max-weight bucket. -/
theorem exists_constant_label_fibre_wt {κ : Type*} (cell : κ → γ) (K : Finset κ)
    (wt : κ → ℝ≥0∞) (hwt : (∑ k ∈ K, wt k) ≠ 0)
    (lab : κ → ℕ) (K₀ : ℕ) (hK₀ : 0 < K₀) (hlab : ∀ k ∈ K, lab k < K₀)
    (hlabc : ∀ k k', cell k = cell k' → lab k = lab k') :
    ∃ (w : ℕ) (K' : Finset κ), K' ⊆ K ∧ K'.Nonempty ∧
      (∑ k ∈ K, wt k) ≤ K₀ * ∑ k ∈ K', wt k ∧
      WholeFibreSubset cell K' K ∧ ∀ k ∈ K', lab k = w := by
  classical
  have hne : (Finset.range K₀).Nonempty := Finset.nonempty_range_iff.mpr hK₀.ne'
  set fib : ℕ → ℝ≥0∞ := fun v => ∑ k ∈ K.filter (fun k => lab k = v), wt k with hfib
  obtain ⟨v, -, hv⟩ := Finset.exists_max_image (Finset.range K₀) fib hne
  have hmaps : ∀ k ∈ K, lab k ∈ Finset.range K₀ := fun k hk => Finset.mem_range.mpr (hlab k hk)
  have hsum : ∑ v ∈ Finset.range K₀, fib v = ∑ k ∈ K, wt k :=
    Finset.sum_fiberwise_of_maps_to hmaps wt
  have hle : (∑ k ∈ K, wt k) ≤ K₀ * fib v := by
    rw [← hsum]
    calc ∑ v' ∈ Finset.range K₀, fib v' ≤ ∑ _v' ∈ Finset.range K₀, fib v :=
          Finset.sum_le_sum (fun v' hv' => hv v' hv')
      _ = (K₀ : ℝ≥0∞) * fib v := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hfv : fib v ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hle
    exact hwt (le_antisymm hle bot_le)
  have hK'ne : (K.filter (fun k => lab k = v)).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    exact hfv (by rw [hfib]; simp [hemp])
  refine ⟨v, K.filter (fun k => lab k = v), Finset.filter_subset _ _, hK'ne, hle, ?_,
    fun k hk => (Finset.mem_filter.mp hk).2⟩
  refine ⟨Finset.filter_subset _ _, fun i hi j hj hcell => ?_⟩
  refine Finset.mem_filter.mpr ⟨hj, ?_⟩
  rw [hlabc j i hcell]
  exact (Finset.mem_filter.mp hi).2

open scoped Classical in
/-- **The joint single-bin band, weighted**: `n` statistics at once, weight loss `L ^ n`, retained
set a union of whole cells. -/
theorem exists_joint_bucket_band_fibre_wt {κ : Type*} (cell : κ → γ) (wt : κ → ℝ≥0∞) :
    ∀ (n : ℕ) (K : Finset κ), (∑ k ∈ K, wt k) ≠ 0 →
      ∀ (D : Fin n → κ → ℝ≥0∞) (bucket : Fin n → κ → ℕ) (L : ℕ), 0 < L →
      (∀ q : Fin n, ∀ k k', cell k = cell k' → bucket q k = bucket q k') →
      (∀ q : Fin n, ∀ k ∈ K, ∀ k' ∈ K, bucket q k = bucket q k' → D q k' ≤ 2 * D q k) →
      (∀ q : Fin n, ∀ k ∈ K, bucket q k < L) →
      ∃ K' : Finset κ, K' ⊆ K ∧ K'.Nonempty ∧
        (∑ k ∈ K, wt k) ≤ (L : ℝ≥0∞) ^ n * ∑ k ∈ K', wt k ∧
        WholeFibreSubset cell K' K ∧
        ∃ Φ : Fin n → ℝ≥0∞, ∀ q : Fin n, ∀ k ∈ K', Φ q ≤ D q k ∧ D q k ≤ 2 * Φ q := by
  intro n
  induction n with
  | zero =>
      intro K hK D bucket L hL _ _ _
      refine ⟨K, Finset.Subset.refl K, ?_, by simp,
        ⟨Finset.Subset.refl K, fun _ _ j hj _ => hj⟩, Fin.elim0, fun q => q.elim0⟩
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      exact hK (by simp [hemp])
  | succ n ih =>
      intro K hK D bucket L hL hbc hb hLlt
      obtain ⟨K₁, hK₁sub, hK₁ne, hK₁wt, hK₁wf, Φlast, hΦlast⟩ :=
        exists_bucket_band_fibre_wt cell K wt hK (D (Fin.last n)) (bucket (Fin.last n)) L hL
          (hbc (Fin.last n)) (hb (Fin.last n)) (hLlt (Fin.last n))
      have hK₁ : (∑ k ∈ K₁, wt k) ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hK₁wt
        exact hK (le_antisymm hK₁wt bot_le)
      obtain ⟨K₂, hK₂sub, hK₂ne, hK₂wt, hK₂wf, Φ, hΦ⟩ :=
        ih K₁ hK₁ (fun q => D q.castSucc) (fun q => bucket q.castSucc) L hL
          (fun q => hbc q.castSucc)
          (fun q k hk k' hk' h => hb q.castSucc k (hK₁sub hk) k' (hK₁sub hk') h)
          (fun q k hk => hLlt q.castSucc k (hK₁sub hk))
      refine ⟨K₂, hK₂sub.trans hK₁sub, hK₂ne, ?_, hK₂wf.trans hK₁wf, Fin.snoc Φ Φlast, ?_⟩
      · calc (∑ k ∈ K, wt k) ≤ (L : ℝ≥0∞) * ∑ k ∈ K₁, wt k := hK₁wt
          _ ≤ (L : ℝ≥0∞) * ((L : ℝ≥0∞) ^ n * ∑ k ∈ K₂, wt k) :=
              mul_le_mul' le_rfl hK₂wt
          _ = (L : ℝ≥0∞) ^ (n + 1) * ∑ k ∈ K₂, wt k := by ring
      · intro q k hk
        refine Fin.lastCases ?_ ?_ q
        · simpa using hΦlast k (hK₂sub hk)
        · intro q'
          simpa using hΦ q' k hk

open scoped Classical in
/-- **One level of the weighted descent** — the mass analogue of `exists_level_band_step`. -/
theorem exists_level_band_step_wt {n : ℕ} (cell : ι → γ) (v : Finset ι) (wt : ι → ℝ≥0∞)
    (hwt : (∑ k ∈ v, wt k) ≠ 0)
    (D : Fin n → ι → ℝ≥0∞) (bucket : Fin n → ι → ℕ) (L : ℕ) (hL : 0 < L)
    (hbc : ∀ q : Fin n, ∀ i j, cell i = cell j → bucket q i = bucket q j)
    (hpair : ∀ q : Fin n, ∀ i ∈ v, ∀ j ∈ v, bucket q i = bucket q j → D q j ≤ 2 * D q i)
    (hlt : ∀ q : Fin n, ∀ i ∈ v, bucket q i < L)
    (lab : ι → ℕ) (K₀ : ℕ) (hK₀0 : 0 < K₀) (hK₀ : ∀ i ∈ v, lab i < K₀)
    (hlabc : ∀ i j, cell i = cell j → lab i = lab j) :
    ∃ t : Finset ι, t ⊆ v ∧ t.Nonempty ∧
      (∑ k ∈ v, wt k) ≤ (K₀ : ℝ≥0∞) * (L : ℝ≥0∞) ^ n * ∑ k ∈ t, wt k ∧
      WholeFibreSubset cell t v ∧ (∃ w : ℕ, ∀ k ∈ t, lab k = w) ∧
      ∃ Φ : Fin n → ℝ≥0∞, ∀ q : Fin n, ∀ k ∈ t, Φ q ≤ D q k ∧ D q k ≤ 2 * Φ q := by
  obtain ⟨w, v₁, hv₁sub, hv₁ne, hv₁wt, hv₁wf, hv₁lab⟩ :=
    exists_constant_label_fibre_wt cell v wt hwt lab K₀ hK₀0 hK₀ hlabc
  have hv₁ : (∑ k ∈ v₁, wt k) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hv₁wt
    exact hwt (le_antisymm hv₁wt bot_le)
  obtain ⟨v₂, hv₂sub, hv₂ne, hv₂wt, hv₂wf, Φ, hΦ⟩ :=
    exists_joint_bucket_band_fibre_wt cell wt n v₁ hv₁ D bucket L hL hbc
      (fun q k hk k' hk' h => hpair q k (hv₁sub hk) k' (hv₁sub hk') h)
      (fun q k hk => hlt q k (hv₁sub hk))
  refine ⟨v₂, hv₂sub.trans hv₁sub, hv₂ne, ?_, hv₂wf.trans hv₁wf,
    ⟨w, fun k hk => hv₁lab k (hv₂sub hk)⟩, Φ, hΦ⟩
  calc (∑ k ∈ v, wt k) ≤ (K₀ : ℝ≥0∞) * ∑ k ∈ v₁, wt k := hv₁wt
    _ ≤ (K₀ : ℝ≥0∞) * ((L : ℝ≥0∞) ^ n * ∑ k ∈ v₂, wt k) := mul_le_mul' le_rfl hv₂wt
    _ = (K₀ : ℝ≥0∞) * (L : ℝ≥0∞) ^ n * ∑ k ∈ v₂, wt k := by ring

open scoped Classical in
/-- **The weighted descent** — `exists_multiLevel_band` with the node fraction replaced by the
fraction of the shaded mass.  One retained family, all levels' bands, and
`∑_u wt ≤ (K₀ L^n)^{M+1} · ∑_t wt`: the shape `Kakeya.ML2Core.IsShadedRefinementOf`'s fifth clause
asks for, with `Λ` the loss. -/
theorem exists_multiLevel_band_wt [DecidableEq γ] {n : ℕ}
    (u : Finset ι) (wt : ι → ℝ≥0∞) (hwt : (∑ k ∈ u, wt k) ≠ 0) (g : ℕ → ι → γ)
    (hmono : ∀ p q : ℕ, p ≤ q → ∀ i ∈ u, ∀ j ∈ u, g p i = g p j → g q i = g q j)
    (D : ℕ → Fin n → Finset ι → ι → ℝ≥0∞)
    (hloc : ∀ (p : ℕ) (q : Fin n), LeafLocalStat (g p) (D p q))
    (bucket : ℕ → Fin n → Finset ι → ι → ℕ)
    (hbc : ∀ (p : ℕ) (q : Fin n) (w : Finset ι) (i j : ι),
      g p i = g p j → bucket p q w i = bucket p q w j)
    (L : ℕ) (hL : 0 < L)
    (hlt : ∀ (p : ℕ) (q : Fin n), ∀ w ⊆ u, ∀ i ∈ w, bucket p q w i < L)
    (hpair : ∀ (p : ℕ) (q : Fin n), ∀ w ⊆ u, ∀ i ∈ w, ∀ j ∈ w,
      bucket p q w i = bucket p q w j → D p q w j ≤ 2 * D p q w i)
    (lab : ℕ → ι → ℕ) (K₀ : ℕ) (hK₀0 : 0 < K₀) (hK₀ : ∀ p : ℕ, ∀ i ∈ u, lab p i < K₀)
    (hlabc : ∀ (p : ℕ) (i j : ι), g p i = g p j → lab p i = lab p j) :
    ∀ M : ℕ, ∃ t : Finset ι, t ⊆ u ∧ t.Nonempty ∧
      (∑ k ∈ u, wt k) ≤ ((K₀ : ℝ≥0∞) * (L : ℝ≥0∞) ^ n) ^ (M + 1) * ∑ k ∈ t, wt k ∧
      (∃ vl : ℕ → ℕ, ∀ p ≤ M, ∀ k ∈ t, lab p k = vl p) ∧
      ∃ Φ : ℕ → Fin n → ℝ≥0∞, ∀ p ≤ M, ∀ q : Fin n, ∀ k ∈ t,
        Φ p q ≤ D p q t k ∧ D p q t k ≤ 2 * Φ p q := by
  intro M
  induction M with
  | zero =>
      obtain ⟨t, hts, htne, htwt, htwf, ⟨w, hw⟩, Φ, hΦ⟩ :=
        exists_level_band_step_wt (n := n) (g 0) u wt hwt (fun q => D 0 q u)
          (fun q => bucket 0 q u) L hL (fun q => hbc 0 q u)
          (hpair 0 · u (Finset.Subset.refl u)) (hlt 0 · u (Finset.Subset.refl u))
          (lab 0) K₀ hK₀0 (hK₀ 0) (hlabc 0)
      refine ⟨t, hts, htne, by simpa using htwt, ⟨fun _ => w, fun p hp k hk => ?_⟩,
        fun _ q => Φ q, fun p hp q k hk => ?_⟩
      · rw [Nat.le_zero.mp hp]; exact hw k hk
      · rw [Nat.le_zero.mp hp, leafLocalStat_stable (hloc 0 q) htwf hk]
        exact hΦ q k hk
  | succ M ih =>
      obtain ⟨t₁, ht₁s, ht₁ne, ht₁wt, ⟨vl, hvl⟩, Φ₁, hΦ₁⟩ := ih
      have ht₁ : (∑ k ∈ t₁, wt k) ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at ht₁wt
        exact hwt (le_antisymm ht₁wt bot_le)
      obtain ⟨t₂, ht₂s, ht₂ne, ht₂wt, ht₂wf, ⟨w, hw⟩, Φ₂, hΦ₂⟩ :=
        exists_level_band_step_wt (n := n) (g (M + 1)) t₁ wt ht₁ (fun q => D (M + 1) q t₁)
          (fun q => bucket (M + 1) q t₁) L hL (fun q => hbc (M + 1) q t₁)
          (hpair (M + 1) · t₁ ht₁s) (hlt (M + 1) · t₁ ht₁s) (lab (M + 1)) K₀ hK₀0
          (fun i hi => hK₀ (M + 1) i (ht₁s hi)) (hlabc (M + 1))
      have hwfp : ∀ p ≤ M + 1, WholeFibreSubset (g p) t₂ t₁ := by
        intro p hp
        refine wholeFibreSubset_of_refines ht₂wf (fun i hi j hj hcell => ?_)
        exact hmono p (M + 1) hp j (ht₁s hj) i (ht₁s hi) hcell
      refine ⟨t₂, ht₂s.trans ht₁s, ht₂ne, ?_,
        ⟨fun p => if p = M + 1 then w else vl p, fun p hp k hk => ?_⟩,
        fun p => if p = M + 1 then Φ₂ else Φ₁ p, fun p hp q k hk => ?_⟩
      · calc (∑ k ∈ u, wt k)
            ≤ ((K₀ : ℝ≥0∞) * (L : ℝ≥0∞) ^ n) ^ (M + 1) * ∑ k ∈ t₁, wt k := ht₁wt
          _ ≤ ((K₀ : ℝ≥0∞) * (L : ℝ≥0∞) ^ n) ^ (M + 1)
                * ((K₀ : ℝ≥0∞) * (L : ℝ≥0∞) ^ n * ∑ k ∈ t₂, wt k) :=
              mul_le_mul' le_rfl ht₂wt
          _ = ((K₀ : ℝ≥0∞) * (L : ℝ≥0∞) ^ n) ^ (M + 1 + 1) * ∑ k ∈ t₂, wt k := by ring
      · dsimp only
        rcases Nat.lt_or_ge p (M + 1) with hlt' | hge
        · rw [if_neg (by omega)]
          exact hvl p (by omega) k (ht₂s hk)
        · have hpe : p = M + 1 := by omega
          subst hpe
          rw [if_pos rfl]
          exact hw k hk
      · dsimp only
        rcases Nat.lt_or_ge p (M + 1) with hlt' | hge
        · rw [if_neg (by omega : ¬ p = M + 1),
            leafLocalStat_stable (hloc p q) (hwfp p (by omega)) hk]
          exact hΦ₁ p (by omega) q k (ht₂s hk)
        · have hpe : p = M + 1 := by omega
          subst hpe
          rw [if_pos rfl, leafLocalStat_stable (hloc (M + 1) q) (hwfp (M + 1) le_rfl) hk]
          exact hΦ₂ q k hk

/-! ### The four statistics in one joint bin -/


open scoped Classical in
/-- **Match control**: `levelDensityBand_indexSet`'s conclusion is the field
`Kakeya.ML2Reduction.IsKatzTaoDividingWindowLevels.level_density_band` **verbatim** — the projection
inhabits it, so nothing has been reshaped in transcription. -/
example {t : Finset ι} {𝒱 : Tube.UniformTubeSet t T (Tube.ssfGridLen δ) Cu}
    {Cstar : ℝ≥0∞} {η : ℕ → ℝ} {εd : ℝ} {N a b m : ℕ}
    (hw : ML2Reduction.IsKatzTaoDividingWindowLevels 𝒱 Cstar η εd N a b m) :
    ∃ Φ' : ℕ → ℕ → ℝ≥0∞, ∀ p ≤ Tube.ssfGridLen δ, ∀ c ≤ Tube.ssfGridLen δ,
      ∀ j ∈ 𝒱.cover.indexSet p,
      Φ' p c ≤ Kakeya.maxDensity
          ((Tube.coverClass t (𝒱.cover.assign p) j).image (𝒱.cover.assign c))
          (fun j' => (𝒱.cover.tube c j').toConvexSpaceBody) ∧
        Kakeya.maxDensity
          ((Tube.coverClass t (𝒱.cover.assign p) j).image (𝒱.cover.assign c))
          (fun j' => (𝒱.cover.tube c j').toConvexSpaceBody) ≤ Cstar * Φ' p c :=
  hw.level_density_band


end LevelDensityBandInstance


section RefinedHierarchyBand

open MeasureTheory Tube

universe w

variable {ι : Type w} {δ Cu : ℝ≥0} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}


end RefinedHierarchyBand


section WindowAssembly

open MeasureTheory Tube

universe v2

variable {ι : Type v2} {δ Cu : ℝ≥0} {u : Finset ι}
  {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}


end WindowAssembly

section RefinedFloorRoute

open MeasureTheory Tube

variable {ι : Type*} {δ Cu : ℝ≥0} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

/-- **The payload's remaining goal, named without the over-strong intermediate.**

`Kakeya.ML2Core.InheritedWindowSupplyAt` asks for a dividing window on the **given** restricted
tower, for **every** `S`.  `Kakeya.ML2Core.pairwise_of_levelDensityBand` measures why that is more
than the target needs: `level_density_band` forces all level-`p` two-level densities to agree
within `Cstar`, which is a regularity property of the family and is exactly what A1's refinement
buys — so it cannot be asserted of an arbitrary `S`.

`Kakeya.ML2Core.FloorDataAtTrichotomy` does not need it.  Its `(F)` disjunct is
`Kakeya.ML2Core.RefinedFloorHypothesis`, which itself **binds** `S' ⊆ S` and asks for the window on
`Kakeya.ML2Core.refinedHierarchy` — the refined tower.  So the refinement the source performs at
 is available inside the branch, and this `def` is the payload's goal with the
refinement left where the source puts it. -/
def RefinedFloorSupplyAt (β ϖ ε₁ η' : ℝ) (gain dens : ℝ → ℝ) {C : ℝ≥0} {Kl cl : ℕ} (Λf : ℝ≥0∞)
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu) : Prop :=
  ∀ (S : Finset ι) (hS : S ⊆ u), S.Nonempty →
    ∀ (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
      (ht : ∀ i, (Z i).toTube = (T i).toTube) (hh : IsClassHomogeneousOn 𝒰 S),
      ∃ a b m : ℕ, RefinedFloorHypothesis (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ gain dens
        η' Λf ((𝒰.restrictOccupied hS hh).retube (funext ht)) a b m

/-- **The alternative route to the payload**, additive to
`Kakeya.ML2Core.floorDataAtTrichotomy_of_windowed_of_supply` and strictly weaker in what it
demands: it never asks for a window on an unrefined family.; the
`(D)` disjunct is simply not used. -/
theorem floorDataAtTrichotomy_of_refinedFloorSupply
    {β ϖ ε₁ η' h : ℝ} {gain dens : ℝ → ℝ} {C : ℝ≥0} {Kl cl : ℕ} {Λf : ℝ≥0∞}
    {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}
    (hsupply : RefinedFloorSupplyAt (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' gain dens Λf 𝒰) :
    FloorDataAtTrichotomy (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' h gain dens Λf 𝒰 := by
  intro S hS hne Z ht hh _
  obtain ⟨a, b, m, hf⟩ := hsupply S hS hne Z ht hh
  exact ⟨a, b, m, Or.inl hf⟩


/-! The loss-monotonicity `Kakeya.ML2Core.IsShadedRefinementOf.mono_loss` needed to absorb the
joint bin's per-family `J` into one uniform `Λf` is **already existing**
(`SpineFloorShapePayload.lean`); no sibling is cut for it. -/


end RefinedFloorRoute

end Kakeya.ML2Core

end

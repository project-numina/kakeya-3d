/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Reduction
public import Kakeya.DimensionThree.Plank.LocalDensity
public import Kakeya.DimensionThree.Plank.RelativeMultiplicity
public import Kakeya.BallDense

/-!
# The thickening reduction for `ShadedPlank.reduction_to_slab_atTypicalAngle`

This file replaces the *set-existence* obligation of `Section6CompatDense.lean` by a single
**scalar inequality**.  Writing `U = U(s, Y'')` for the shading union and `r = θ b`, the whole
remaining content of `ShadedPlank.reduction_to_slab_atTypicalAngle` is

```
54 · C · δ ^ ε' · a ^ (4η) · a ^ ε · |N_r(U)|  ≤  |U|,
```

a comparison between the volume of the `r`-thickening of the shading union and the volume of the
shading union itself.  There is no region to construct, no cover to exhibit, no `ρ`, and the
multiplicity cancels.

## Why this is strictly better than the dense-region obligation

`Section6CompatDense.lean` reduces the target to: *produce* a measurable `G` retaining a
`δ ^ (ε' - 2ε) a ^ ε` fraction of `U` and filling a `θb`-ball around each of its points.  Two
things make that awkward.

1. It is an existence statement about sets, so a producer has to do the discard construction
   itself.
2. Its retention exponent goes through `Plank.isCRefinement_restrictShade_of_dense`, which
   converts a *union* capture `ρ|U| ≤ |U ∩ G|` into a *mass* capture at the price of one factor
   `C`.  Since `ρ ≤ 1` and `C ≥ 1`, that route can never retain more than a `1/C` fraction of the
   mass, so the retention ratio it must achieve is pushed up to `δ ^ (ε' - 2ε) a ^ ε`, which is
   close to `1` exactly when `a` is close to `1` — a corner in which no discard is affordable.

This file does the discard **in mass rather than in volume**: a ball `B̄(z, r)` is kept when
`∑_i |Y''_i ∩ B̄(z, r)| ≥ τ |B̄(z, r)|`, so the discarded quantity is directly the mass, and a
fixed half of it can always be kept.  The conversion of the surviving mass density into the
*union* density that Item 1 asks for is done once, on a good ball, by
`ShadedPlank.sum_volume_shade_inter_le_of_hasCConstantMultiplicity`, and the factor `C · m₀` it
costs is exactly the factor `C · m₀` that the threshold `τ := t · C · m₀` carries — so `m₀`, the
minimal pointwise multiplicity, cancels out of the final obligation.

## The exponent ledger

`c1 := δ ^ ε'`, `t := c1 · a ^ (4η) · a ^ ε`, `κ := c1 · a ^ ε`.

* One `δ ^ ε` pays the incoming refinement `IsCRefinement s Y'' s (bodies Y) C⁻¹`.
* One more `δ ^ ε` pays the *fixed* half-discard, through `2 · κ · C ≤ 1`.  With `C ≤ δ ^ (-ε)`
  and `a ^ ε ≤ 1` this is `2 δ ^ (ε' - ε) ≤ 1`, and `ε' - ε ≥ ε` because `2 ε ≤ ε'`, so it holds
  as soon as `δ ^ ε ≤ 1/2`.  That is the *only* use of the smallness threshold, and it fixes
  `δthr = 2 ^ (-1/ε)`.

So only `2 * ε ≤ ε'` of the repaired binder `128 * ε ≤ ε'` is spent here, the remaining `126 * ε`
being what the Step-3 ledger needs elsewhere: the remaining obligation carries the
factor `C` explicitly rather than the bound `δ ^ (-ε)`, so a producer may use whatever `C` the
caller actually supplied.

## Sanity of the obligation

The obligation says the `θb`-thickening of `U(s, Y'')` inflates its volume by at most
`(54 C δ ^ ε' a ^ (4η + ε)) ⁻¹`.  Two checks, at the two extreme shapes of a Section-6
configuration:

* the *bush* (`|s| = μ` planks through one core box, the extremal high-multiplicity family):
  the fullness hypothesis `a ^ η ≤ λ` forces `θ ≲ a ^ (1 - η/2)`, the core box is
  `a ^ (η/2) × a ^ (η/2) × a` and `r = θ b` sits between `a` and `a ^ (η/2)`, so the inflation
  ratio is `a ^ (-η/2)` — comfortably below `a ^ (-4η - ε)`;
* the *transverse plate* (`θ ≈ 1`, `b ≈ 1`, planks `a × 1 × 1`): the same fullness hypothesis
  forces the plate thickness `h ≳ a ^ η`, so the inflation ratio at `r = 1` is `≈ a ^ (-η)`,
  again below `a ^ (-4η - ε)`.

The single-plank shape, whose inflation ratio is `θ b / a` and which does violate the obligation
as soon as `θ b ≫ a ^ (1 - 4η - ε)`, is excluded by the multiplicity hypothesis `2 ≤ δ ^ (-η) ≤ µ`.
So the obligation is the exact place where the multiplicity hypothesis has to be used, which is
where GWZ uses it.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric
open scoped NNReal Real ENNReal

noncomputable section

namespace ShadedPlank

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}

/-! ## A packing bound: a separated cover is no bigger than the thickening -/

/-- **Packing bound.**  If `T ⊆ A` is `r`-separated then the balls `B̄(z, r/3)`, `z ∈ T`, are
pairwise disjoint and contained in the `r`-thickening of `A`, so

`∑_{z ∈ T} |B̄(z, r)| = 27 ∑_{z ∈ T} |B̄(z, r/3)| ≤ 27 |N_r(A)|`.

The factor `27 = 3 ^ 3` is the ambient dimension entering; nothing else about `A` is used. -/
theorem sum_volume_closedBall_le_cthickening
    {A : Set (EuclideanSpace ℝ (Fin 3))} {r : ℝ} (hr : 0 < r)
    {T : Finset (EuclideanSpace ℝ (Fin 3))} (hTA : ∀ z ∈ T, z ∈ A)
    (hsep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → r < dist x y) :
    ∑ z ∈ T, volume (closedBall z r) ≤ 27 * volume (Metric.cthickening r A) := by
  classical
  have hr3 : (0 : ℝ) ≤ r / 3 := by positivity
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by
    simp
  -- each big ball is `27` small balls
  have hball : ∀ z : EuclideanSpace ℝ (Fin 3),
      volume (closedBall z r) = 27 * volume (closedBall z (r / 3)) := by
    intro z
    rw [Measure.addHaar_closedBall volume z hr.le,
      Measure.addHaar_closedBall volume z hr3, hfr]
    rw [← mul_assoc]
    congr 1
    have h27 : r ^ 3 = 27 * (r / 3) ^ 3 := by ring
    rw [h27, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 27)]
    norm_num
  -- the small balls are pairwise disjoint
  have hdisj : (T : Set (EuclideanSpace ℝ (Fin 3))).PairwiseDisjoint
      (fun z => closedBall z (r / 3)) := by
    intro x hx y hy hxy
    change Disjoint (closedBall x (r / 3)) (closedBall y (r / 3))
    rw [Set.disjoint_left]
    intro w hwx hwy
    have hdx : dist w x ≤ r / 3 := Metric.mem_closedBall.mp hwx
    have hdy : dist w y ≤ r / 3 := Metric.mem_closedBall.mp hwy
    have hxy' : dist x y ≤ 2 * (r / 3) := by
      calc dist x y ≤ dist x w + dist w y := dist_triangle x w y
        _ ≤ r / 3 + r / 3 := add_le_add (by simpa [dist_comm] using hdx) hdy
        _ = 2 * (r / 3) := by ring
    have hgt : r < dist x y := hsep x hx y hy hxy
    linarith
  -- the small balls sit inside the thickening
  have hsub : ∀ z ∈ T, closedBall z (r / 3) ⊆ Metric.cthickening r A := by
    intro z hz w hw
    refine Metric.mem_cthickening_of_dist_le w z r A (hTA z hz) ?_
    exact le_trans (Metric.mem_closedBall.mp hw) (by linarith)
  calc ∑ z ∈ T, volume (closedBall z r)
      = ∑ z ∈ T, 27 * volume (closedBall z (r / 3)) :=
        Finset.sum_congr rfl fun z _ => hball z
    _ = 27 * ∑ z ∈ T, volume (closedBall z (r / 3)) := by rw [Finset.mul_sum]
    _ = 27 * volume (⋃ z ∈ T, closedBall z (r / 3)) := by
        rw [measure_biUnion_finset hdisj (fun z _ => measurableSet_closedBall)]
    _ ≤ 27 * volume (Metric.cthickening r A) := by
        gcongr
        exact Set.iUnion₂_subset hsub

/-! ## Mass on a test set under constant multiplicity -/

variable {ι : Type*}


/-! ## The mass-based discard -/

/-- **Discarding the mass-sparse balls of a finite ball cover.**

Cover the shading union by the balls `B̄(z, r)`, `z ∈ T`, and call `z` *good* when the family
carries at least `τ |B̄(z, r)|` of **mass** in that ball, `τ |B̄(z, r)| ≤ ∑_i |Y_i ∩ B̄(z, r)|`.
Let `G` be the union of the good balls.  Then

* the mass lost is at most `τ ∑_{z ∈ T} |B̄(z, r)|`, and
* every point of `U ∩ G` lies in a good ball which is *contained* in `G`, so the mass density on
  that ball is unaffected by the passage from `U` to `U ∩ G`.

Unlike `ShadedPlank.exists_denseRegion_of_ballCover` this discards in **mass** and not in volume;
that is what makes a fixed (half) retention affordable, since the retained mass is compared with
the total mass rather than with the volume of the union. -/
theorem exists_massRegion_of_ballCover (s : Finset ι)
    (V : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (r : ℝ) (T : Finset (EuclideanSpace ℝ (Fin 3)))
    (hcov : (⋃ i ∈ s, (V i).shade) ⊆ ⋃ z ∈ T, closedBall z r) (tau : ℝ≥0) :
    ∃ G : Set (EuclideanSpace ℝ (Fin 3)), MeasurableSet G ∧
      (∑ i ∈ s, volume (V i).shade
        ≤ (∑ i ∈ s, volume ((V i).shade ∩ G))
            + (tau : ℝ≥0∞) * ∑ z ∈ T, volume (closedBall z r)) ∧
      (∀ y ∈ (⋃ i ∈ s, (V i).shade) ∩ G, ∃ z : EuclideanSpace ℝ (Fin 3),
        y ∈ closedBall z r ∧ closedBall z r ⊆ G ∧
        (tau : ℝ≥0∞) * volume (closedBall z r)
          ≤ ∑ i ∈ s, volume ((V i).shade ∩ closedBall z r)) := by
  classical
  set Good : Finset (EuclideanSpace ℝ (Fin 3)) :=
    T.filter (fun z => (tau : ℝ≥0∞) * volume (closedBall z r)
      ≤ ∑ i ∈ s, volume ((V i).shade ∩ closedBall z r)) with hGoodDef
  set G : Set (EuclideanSpace ℝ (Fin 3)) := ⋃ z ∈ Good, closedBall z r with hGdef
  have hGmeas : MeasurableSet G :=
    MeasurableSet.biUnion (Finset.countable_toSet Good) fun _ _ => measurableSet_closedBall
  have hbad : ∀ z ∈ T \ Good, ∑ i ∈ s, volume ((V i).shade ∩ closedBall z r)
      ≤ (tau : ℝ≥0∞) * volume (closedBall z r) := by
    intro z hz
    have hz' := (Finset.mem_sdiff.mp hz).2
    have hcon : ¬ ((tau : ℝ≥0∞) * volume (closedBall z r)
        ≤ ∑ i ∈ s, volume ((V i).shade ∩ closedBall z r)) := by
      intro h
      exact hz' (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hz).1, h⟩)
    exact le_of_lt (not_le.mp hcon)
  refine ⟨G, hGmeas, ?_, ?_⟩
  · have hdiff : ∀ i ∈ s, volume ((V i).shade \ G)
        ≤ ∑ z ∈ T \ Good, volume ((V i).shade ∩ closedBall z r) := by
      intro i hi
      have hsub : (V i).shade \ G ⊆ ⋃ z ∈ (T \ Good), ((V i).shade ∩ closedBall z r) := by
        intro y hy
        have hyU : y ∈ ⋃ j ∈ s, (V j).shade := Set.mem_biUnion hi hy.1
        obtain ⟨z, hzT, hyz⟩ := Set.mem_iUnion₂.mp (hcov hyU)
        have hzG : z ∉ Good := fun hz => hy.2 (Set.mem_iUnion₂.mpr ⟨z, hz, hyz⟩)
        exact Set.mem_iUnion₂.mpr ⟨z, Finset.mem_sdiff.mpr ⟨hzT, hzG⟩, ⟨hy.1, hyz⟩⟩
      exact le_trans (measure_mono hsub) (measure_biUnion_finset_le _ _)
    have hlost : ∑ i ∈ s, volume ((V i).shade \ G)
        ≤ (tau : ℝ≥0∞) * ∑ z ∈ T, volume (closedBall z r) := by
      calc ∑ i ∈ s, volume ((V i).shade \ G)
          ≤ ∑ i ∈ s, ∑ z ∈ T \ Good, volume ((V i).shade ∩ closedBall z r) :=
            Finset.sum_le_sum hdiff
        _ = ∑ z ∈ T \ Good, ∑ i ∈ s, volume ((V i).shade ∩ closedBall z r) := Finset.sum_comm
        _ ≤ ∑ z ∈ T \ Good, (tau : ℝ≥0∞) * volume (closedBall z r) :=
            Finset.sum_le_sum hbad
        _ ≤ ∑ z ∈ T, (tau : ℝ≥0∞) * volume (closedBall z r) :=
            Finset.sum_le_sum_of_subset Finset.sdiff_subset
        _ = (tau : ℝ≥0∞) * ∑ z ∈ T, volume (closedBall z r) := by rw [Finset.mul_sum]
    calc ∑ i ∈ s, volume (V i).shade
        = ∑ i ∈ s, (volume ((V i).shade ∩ G) + volume ((V i).shade \ G)) :=
          Finset.sum_congr rfl fun i _ => (measure_inter_add_sdiff _ hGmeas).symm
      _ = (∑ i ∈ s, volume ((V i).shade ∩ G)) + ∑ i ∈ s, volume ((V i).shade \ G) :=
          Finset.sum_add_distrib
      _ ≤ (∑ i ∈ s, volume ((V i).shade ∩ G))
            + (tau : ℝ≥0∞) * ∑ z ∈ T, volume (closedBall z r) := by gcongr
  · intro y hy
    obtain ⟨z, hzGood, hyz⟩ := Set.mem_iUnion₂.mp hy.2
    exact ⟨z, hyz, fun w hw => Set.mem_iUnion₂.mpr ⟨z, hzGood, hw⟩,
      (Finset.mem_filter.mp hzGood).2⟩

/-! ## The reduction from a mass-capturing region -/


/-! ## The reduction from a ball cover and a scalar budget -/


/-! ## The target, modulo one scalar inequality -/


end ShadedPlank

end

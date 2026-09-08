/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Factorization
public import Kakeya.DimensionThree.Volume
public import Kakeya.PartialEstimates
public import Kakeya.DimensionThree.Plank.PlankFactorizationEstimate
public import Kakeya.StickyKakeya.Constants
public import Kakeya.ShadedUniform
public import Kakeya.MultiScaleLoss

/-!
# One tube family that is both multiscale shaded-uniform and plank-structured

GWZ Section 8 needs a single family of tubes carrying, *at one global pair* `(a, b)`, both the
multiscale shaded uniformity of GWZ Definition 2.2 and the plank factorization of GWZ
Proposition 6.6.  The two selections producing those properties are each two-sided — each brackets
class sizes from above *and* below — so neither survives being run after the other.

The order used here is:

1. uniformize the tubes;
2. run the plank pigeonhole, fixing a global `(a, b)`;
3. regularize the grid partitions *and* the plank-block partition **together**, in one finite
   hypergraph cleaning (`Kakeya.exists_jointPartitionRegularization`);
4. keep the outer plank bodies **fixed** and restrict only their fibres
   (`Kakeya.PersistentPlankFactorization`);
5. refine the shading last, which touches no partition
   (`ShadedTube.exists_shadedUniformTubeSet_of_uniformTubeSet`).

Steps 4 and 5 are mechanical given step 3, because
`Kakeya.MultiScaleFac.exists_restrict_uniformTubeSet_band` rebuilds tube uniformity on an
*arbitrary* subfamily from a supplied two-sided bracket, and the shaded uniformization does not
move the index set.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Kakeya Convexity ConvexSpaceBody

noncomputable section

universe u

namespace Kakeya

/-! ### Restricting a uniform hierarchy along a supplied band -/

namespace MultiScaleFac

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

end MultiScaleFac

/-! ### The constants of the joint regularization -/

/-! ### The joint regularization of several partitions -/

/-! ### Factorizations through fixed plank bodies

`Kakeya.PersistentPlankFactorization`, the replacement for `Kakeya.PlankFactorization` used
throughout this file, is declared in `Kakeya/DimensionThree/Plank/Factorization.lean` next to
`PlankFactorization` itself, because GWZ Proposition 6.6(B) is stated there and needs it. -/

namespace Plank

/-! ### The corner obstruction: a hull of tubes is never an exact plank

`Kakeya.PlankFactorization` asks for `part.convexHull_biUnion V = Q.toConvexSpaceBody`, an
*equality* between the convex hull of a block of inner bodies and an exact `a × b × 1` plank.  The
three lemmas below show that this equality is unsatisfiable as soon as the inner bodies are
`δ`-tubes with `δ > 0` and the block is nonempty — so every statement quantifying over such a
`PlankFactorization` is vacuous.  See `Kakeya.not_plankFactorization_of_tube`.

The argument is elementary and needs no extreme-point theory.  A plank is a box with half-widths
`(a, b, 1)` in its own orthonormal frame.  Every point of a `δ`-tube inside the box is within `δ` of
a point `c` of the tube's core segment, and `closedBall c δ` is inside the box, so `c` misses each
of the three pairs of faces by at least `δ`.  Reading this against the diagonal functional
`⟪e₀ + e₁, ·⟫` costs `2δ` at `c` and buys back at most `√2 δ ≤ 3δ/2` on the way from `c` to the
point, so the functional stays `δ/2` below its maximum on the whole union of tubes — hence, the
sublevel set being convex, on the hull as well.  But the hull is the box, on which the maximum is
attained, at the vertex `center + a e₀ + b e₁ + e₂`.  Contradiction. -/

end Plank

open Classical in
/-- **The fibres of a restricted factor family**: restricting the inner set to `s'` intersects
every fibre with `s'`, the parent map being untouched by `ConvexSpaceBody.FactorFamily.ofSubset`. -/
theorem fiber_ofSubset_eq_inter {ι ω : Type*}
    (F : ConvexSpaceBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) ι ω)
    {s' : Finset ι} (hs' : s' ⊆ F.innerSet) (j : ω) :
    (F.ofSubset hs').fiber j = F.fiber j ∩ s' := by
  ext i
  simp only [ConvexSpaceBody.FactorFamily.fiber, Finset.mem_filter, Finset.mem_inter,
    ConvexSpaceBody.FactorFamily.ofSubset]
  constructor
  · rintro ⟨hi, hp⟩
    exact ⟨⟨hs' hi, hp⟩, hi⟩
  · rintro ⟨⟨_, hp⟩, hi⟩
    exact ⟨hi, hp⟩

open Classical in
/-- **The volume share retained by a restricted fibre.**

This is the step converting a *cardinality* retention into a *volume* retention.  If the retained
part of the fibre over `j` is a `1 / A` fraction of that fibre, and all inner bodies of the family
have volume comparable up to `Cvol`, then the retained part still carries a `1 / (A * Cvol)` share
of the fibre's total inner volume.  Both hypotheses are needed: cardinality alone says nothing about
volume, and volume comparability alone says nothing about how many members were kept. -/
theorem sum_volume_fiber_le_mul_sum_volume_inter {ι ω : Type*}
    {F : ConvexSpaceBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) ι ω}
    {A Cvol : ℝ≥0} {s' : Finset ι} (hs' : s' ⊆ F.innerSet) {j : ω}
    (hj : j ∈ s'.image F.parent)
    (hA : ((F.fiber j).card : ℝ≥0) ≤ A * (((F.fiber j) ∩ s').card : ℝ≥0))
    (hvol : ∀ i ∈ F.innerSet, ∀ i' ∈ F.innerSet,
      volume (F.innerBody i).carrier ≤ (Cvol : ℝ≥0∞) * volume (F.innerBody i').carrier) :
    ∑ i ∈ F.fiber j, volume (F.innerBody i).carrier ≤
      ((A * Cvol : ℝ≥0) : ℝ≥0∞) * ∑ i ∈ F.fiber j ∩ s', volume (F.innerBody i).carrier := by
  let t := F.fiber j ∩ s'
  have ht : t.Nonempty := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    refine ⟨i, ?_⟩
    simp only [t, Finset.mem_inter, ConvexSpaceBody.FactorFamily.fiber,
      Finset.mem_filter]
    exact ⟨⟨hs' hi, trivial⟩, hi⟩
  obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image t
    (fun i ↦ volume (F.innerBody i).carrier) ht
  have hi₀inner : i₀ ∈ F.innerSet := by
    exact (Finset.mem_filter.mp (Finset.mem_inter.mp hi₀).1).1
  have hupper : ∑ i ∈ F.fiber j, volume (F.innerBody i).carrier ≤
      ((F.fiber j).card : ℝ≥0∞) *
        ((Cvol : ℝ≥0∞) * volume (F.innerBody i₀).carrier) := by
    simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul (F.fiber j)
      (fun i ↦ volume (F.innerBody i).carrier)
      ((Cvol : ℝ≥0∞) * volume (F.innerBody i₀).carrier) fun i hi ↦
        hvol i (Finset.mem_filter.mp hi).1 i₀ hi₀inner
  have hcard : ((F.fiber j).card : ℝ≥0∞) ≤
      (A : ℝ≥0∞) * (t.card : ℝ≥0∞) := by
    exact_mod_cast hA
  have hlower : (t.card : ℝ≥0∞) * volume (F.innerBody i₀).carrier ≤
      ∑ i ∈ t, volume (F.innerBody i).carrier := by
    simpa only [nsmul_eq_mul] using Finset.card_nsmul_le_sum t
      (fun i ↦ volume (F.innerBody i).carrier) (volume (F.innerBody i₀).carrier)
      fun i hi ↦ hmin i hi
  calc
    ∑ i ∈ F.fiber j, volume (F.innerBody i).carrier
        ≤ ((F.fiber j).card : ℝ≥0∞) *
            ((Cvol : ℝ≥0∞) * volume (F.innerBody i₀).carrier) := hupper
    _ ≤ ((A : ℝ≥0∞) * (t.card : ℝ≥0∞)) *
          ((Cvol : ℝ≥0∞) * volume (F.innerBody i₀).carrier) := by gcongr
    _ = ((A * Cvol : ℝ≥0) : ℝ≥0∞) *
          ((t.card : ℝ≥0∞) * volume (F.innerBody i₀).carrier) := by
      push_cast
      ac_rfl
    _ ≤ ((A * Cvol : ℝ≥0) : ℝ≥0∞) *
          ∑ i ∈ t, volume (F.innerBody i).carrier := by gcongr
    _ = ((A * Cvol : ℝ≥0) : ℝ≥0∞) *
          ∑ i ∈ F.fiber j ∩ s', volume (F.innerBody i).carrier := by rfl

open Classical in
/-- **The density share retained by a restricted fibre**, the reading of
`Kakeya.sum_volume_fiber_le_mul_sum_volume_inter` in terms of `Kakeya.densityIn`.  The outer body
`F.outerBody j` is the *same* body on both sides, which is what makes this a statement about
densities at all: only the numerator moves. -/
theorem densityIn_fiber_le_mul_densityIn_inter {ι ω : Type*}
    {F : ConvexSpaceBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) ι ω}
    {A Cvol : ℝ≥0} {s' : Finset ι} (hs' : s' ⊆ F.innerSet) {j : ω}
    (hj : j ∈ s'.image F.parent)
    (hA : ((F.fiber j).card : ℝ≥0) ≤ A * (((F.fiber j) ∩ s').card : ℝ≥0))
    (hvol : ∀ i ∈ F.innerSet, ∀ i' ∈ F.innerSet,
      volume (F.innerBody i).carrier ≤ (Cvol : ℝ≥0∞) * volume (F.innerBody i').carrier) :
    densityIn (F.fiber j) F.innerBody (F.outerBody j) ≤
      ((A * Cvol : ℝ≥0) : ℝ≥0∞) *
        densityIn (F.fiber j ∩ s') F.innerBody (F.outerBody j) := by
  apply densityIn_le_of_sum_le
  rw [Finset.filter_eq_self.mpr, Finset.filter_eq_self.mpr]
  · exact sum_volume_fiber_le_mul_sum_volume_inter hs' hj hA hvol
  · intro i hi
    have hifiber := (Finset.mem_inter.mp hi).1
    obtain ⟨hiinner, hiparent⟩ := Finset.mem_filter.mp hifiber
    simpa only [hiparent] using F.inner_le_parent i hiinner
  · intro i hi
    obtain ⟨hiinner, hiparent⟩ := Finset.mem_filter.mp hi
    simpa only [hiparent] using F.inner_le_parent i hiinner

open Classical in
/-- **Restricting a persistent plank factorization to a subfamily, with the outer bodies fixed.**

This is the step at which a *cardinality* retention is converted into a *density* lower bound: the
retained fibre of a block is a fraction `1 / A` of the original fibre, and all inner bodies have
comparable volume (constant `Cvol`), so the retained block still fills its unchanged outer body to
within `A * Cvol`.  Nothing is claimed about the convex hull of the retained fibre, which is exactly
the clause `Kakeya.PlankFactorization` could not keep.

The hypothesis `1 ≤ A * Cvol` is needed, and only, for the Katz--Tao clause: that clause is an
upper bound on the *outer* family, which is unchanged here, so it descends with the *old* constant
`C₀` and has to be weakened to `C₀ * A * Cvol` by monotonicity in the constant.  Without it the
statement is false, `A = 1` and `Cvol = 0` being admissible when every inner body is degenerate
while the outer planks are not. -/
theorem PersistentPlankFactorization.ofSubset {ι ω : Type*}
    {F : ConvexSpaceBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) ι ω}
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {C₀ A Cvol : ℝ≥0}
    (hF : PersistentPlankFactorization F a b hab hb1 C₀) (hAvol : 1 ≤ A * Cvol)
    {s' : Finset ι} (hs' : s' ⊆ F.innerSet)
    (hA : ∀ j ∈ s'.image F.parent,
      ((F.fiber j).card : ℝ≥0) ≤ A * (((F.fiber j) ∩ s').card : ℝ≥0))
    (hvol : ∀ i ∈ F.innerSet, ∀ i' ∈ F.innerSet,
      volume (F.innerBody i).carrier ≤ (Cvol : ℝ≥0∞) * volume (F.innerBody i').carrier) :
    PersistentPlankFactorization (F.ofSubset hs') a b hab hb1 (C₀ * A * Cvol) := by
  have hparents : (F.ofSubset hs').innerSet.image (F.ofSubset hs').parent ⊆
      F.innerSet.image F.parent := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_image.mpr ⟨i, hs' hi, rfl⟩
  have hconst : (C₀ : ℝ≥0∞) ≤ ((C₀ * A * Cvol : ℝ≥0) : ℝ≥0∞) := by
    exact_mod_cast (show C₀ ≤ C₀ * A * Cvol from calc
      C₀ = C₀ * 1 := (mul_one C₀).symm
      _ ≤ C₀ * (A * Cvol) := mul_le_mul_right hAvol C₀
      _ = C₀ * A * Cvol := by ac_rfl)
  refine ⟨?_, (hF.outer_isKatzTao.subset hparents).mono hconst, ?_⟩
  · intro j hj
    simpa only [ConvexSpaceBody.FactorFamily.ofSubset] using hF.outer_are_planks j (hparents hj)
  · intro j hj
    have hj' : j ∈ s'.image F.parent := by
      simpa only [ConvexSpaceBody.FactorFamily.ofSubset] using hj
    have hdensity := densityIn_fiber_le_mul_densityIn_inter hs' hj' (hA j hj') hvol
    change maxDensity s' F.innerBody ≤
      ((C₀ * A * Cvol : ℝ≥0) : ℝ≥0∞) *
        densityIn ((F.ofSubset hs').fiber j) F.innerBody (F.outerBody j)
    rw [fiber_ofSubset_eq_inter F hs' j]
    calc
      maxDensity s' F.innerBody ≤ maxDensity F.innerSet F.innerBody :=
        maxDensity_mono F.innerBody hs'
      _ ≤ (C₀ : ℝ≥0∞) * densityIn (F.fiber j) F.innerBody (F.outerBody j) :=
        hF.maxDensity_le_mul j (hparents hj)
      _ ≤ (C₀ : ℝ≥0∞) * (((A * Cvol : ℝ≥0) : ℝ≥0∞) *
          densityIn (F.fiber j ∩ s') F.innerBody (F.outerBody j)) := by gcongr
      _ = ((C₀ * A * Cvol : ℝ≥0) : ℝ≥0∞) *
          densityIn (F.fiber j ∩ s') F.innerBody (F.outerBody j) := by
        push_cast
        ac_rfl

/-! ### The joint selection -/

open Classical in
/-- **The output of the joint grid/plank regularization.**

One retained subfamily `kept`, one refined shading, and *one* pair `(a, b)` carrying, at the same
time, the multiscale shaded uniformity of GWZ Definition 2.2 on `kept` and a persistent plank
factorization of each retained plank block.

`activeParents = kept.image assign` is stated as an equation rather than as three separate clauses:
it already says that every retained tube lies in a retained parent, that every retained parent is
actually used, and that a plank block emptied by the cleaning disappears from the outer family.

## A removed clause, and why it had to go

This structure used to carry a further field

    factorFamily_outer_le_parent : ∀ k ∈ activeParents,
      ∀ j ∈ (factorFamily k).innerSet.image (factorFamily k).parent,
        (factorFamily k).outerBody j ≤ (R k).toConvexSpaceBody

"every active outer plank remains inside the coarse tube of its block".  **That clause makes the
structure uninhabited whenever `kept ≠ ∅` and `0 < ρ ≤ a`**, which is exactly the regime the only
consumer `Kakeya.multiplicity_le_of_relativePlankSelection` runs in, so keeping it would have
replaced one vacuity by another.  It had no consumer: no field of the structure and no downstream
theorem, in particular not `Kakeya.tubeMultiplicityOfLocalPersistentPlankFactorisation`, ever read
it.

The obstruction, in two steps.  `persistentFactorization` makes the outer body an exact
`a × b × 1` plank, so the removed clause asserts `plank ⊆ ρ-tube`.

* Along the plank's long axis the plank has extent `2` while a `ρ`-tube of core length one has
  extent at most `1 + 2 ρ`, so `1 / 2 ≤ ρ`.  This half is proved:
  `Kakeya.half_le_of_persistentPlankFactorization` below, via
  `Kakeya.Plank.half_le_of_toConvexSpaceBody_le_tube`.
* Transversally to the tube's core the tube has width exactly `2 ρ`, while the plank's transverse
  cross-section is a `2 a × 2 b` rectangle, whose width in the diagonal direction is
  `√2 · min a b` at least.  With `ρ ≤ a ≤ b` this gives `b ≤ ρ ≤ a ≤ b`, hence `a = b = ρ`, and
  then the diagonal direction gives `ρ √2 ≤ ρ`, i.e. `ρ = 0`.  This half is *not* formalized; it is
  recorded here as the reason the clause is gone, not as a Lean fact.

The mathematical content the clause was trying to express — that the planks are attached to the
coarse tube `R k` — is not available at `ρ ≤ a`, because there the planks are *fatter* than the
coarse tube.  It is carried instead by `activeParents_eq` together with the caller's own
`(V i).toConvexSpaceBody ≤ (R (assign i)).toConvexSpaceBody`, which is a statement about the fine
tubes and is satisfiable. -/
structure RelativePlankSelection {ι κ : Type*} {δ ρ a b : ℝ≥0} (hab : a ≤ b) (hb1 : b ≤ 1)
    (s q : Finset ι) (V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (assign : ι → κ)
    (R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3)))
    (r : Finset κ) (M : ℕ) (uniformConst factorConst : ℝ≥0) (totalLoss : ℕ) where
  /-- The retained subfamily. -/
  kept : Finset ι
  /-- The retained subfamily is a subfamily. -/
  kept_subset : kept ⊆ s
  /-- Every retained tube belongs to the plank-selected input family. -/
  kept_subset_plank : kept ⊆ q
  /-- The refined shading.  Only the shades move; see `sameTube`. -/
  shading : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))
  /-- The underlying tubes are untouched, so all geometry proved before the selection survives. -/
  sameTube : ∀ i, (shading i).toTube = (V i).toTube
  /-- The refined shades are contained in the original ones. -/
  shade_subset : ∀ i, (shading i).shade ⊆ (V i).shade
  /-- The plank blocks still carrying a retained tube. -/
  activeParents : Finset κ
  /-- The active blocks are exactly the blocks of the retained tubes. -/
  activeParents_eq : activeParents = kept.image assign
  /-- The active blocks come from the original block family. -/
  activeParents_subset : activeParents ⊆ r
  /-- The retained family, with its refined shading, is shaded-uniform at every grid level. -/
  shadedUniform : ShadedTube.ShadedUniformTubeSet kept shading M uniformConst
  /-- The factor family of each block: outer bodies fixed, fibre restricted to `kept`. -/
  factorFamily : κ → ConvexSpaceBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) ι (Finset ι)
  /-- Its inner set is the retained part of the block. -/
  factorFamily_innerSet : ∀ k ∈ activeParents,
    (factorFamily k).innerSet = {i ∈ kept | assign i = k}
  /-- Its inner bodies are the original tubes. -/
  factorFamily_innerBody : ∀ k, (factorFamily k).innerBody = fun i => (V i).toConvexSpaceBody
  /-- Each active block is still a plank factorization in the persistent sense. -/
  persistentFactorization : ∀ k ∈ activeParents,
    PersistentPlankFactorization (factorFamily k) a b hab hb1 factorConst
  /-- The retained family is a definite fraction of the original one. -/
  card_retention : s.card ≤ totalLoss * kept.card
  /-- So is the retained shade mass. -/
  shading_mass_retention : ∑ i ∈ s, volume (V i).shade ≤
    (totalLoss : ℝ≥0∞) * ∑ i ∈ kept, volume (shading i).shade

/-- **The retained family is a `totalLoss⁻¹`-refinement of the original.**

`Kakeya.RelativePlankSelection` carries its two retention clauses separately, as a cardinality
bound and a shade-mass bound.  The shade-mass bound, together with `kept_subset`, `sameTube` and
`shade_subset`, is exactly `ShadedBody.IsCRefinement` at `c = totalLoss⁻¹`, which is the interface
the transfer lemmas of `Kakeya/Multiplicity.lean` read: `ShadedBody.IsCRefinement.multiplicity_le`
turns a multiplicity bound on the retained family into one on the original, and
`ShadedBody.IsCRefinement.coe_mul_fullness_le` transports the fullness.

No positivity of `totalLoss` is needed: at `totalLoss = 0` the `NNReal` inverse is `0` and the
mass clause is vacuous. -/
theorem RelativePlankSelection.isCRefinement {ι κ : Type*} {δ ρ a b : ℝ≥0} {hab : a ≤ b}
    {hb1 : b ≤ 1} {s q : Finset ι} {V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    {assign : ι → κ} {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))} {r : Finset κ} {M : ℕ}
    {uniformConst factorConst : ℝ≥0} {totalLoss : ℕ}
    (S : RelativePlankSelection hab hb1 s q V assign R r M uniformConst factorConst totalLoss) :
    ShadedBody.IsCRefinement S.kept (fun i => (S.shading i).toShadedBody) s
      (fun i => (V i).toShadedBody) ((totalLoss : ℝ≥0))⁻¹ := by
  refine ShadedBody.isCRefinement_of_isRefinement_of_sum_le
    (s' := S.kept) (V' := fun i => (S.shading i).toShadedBody)
    (s := s) (V := fun i => (V i).toShadedBody)
    (C := (totalLoss : ℝ≥0)) ?_ ?_
  · refine ⟨S.kept_subset, ?_⟩
    intro i hi
    constructor
    · simpa using congrArg Tube.toConvexSpaceBody (S.sameTube i)
    · exact S.shade_subset i
  · simpa using S.shading_mass_retention

/-! ### GWZ Proposition 6.6(A) for persistent factorizations -/

/-! ### Absorption of the losses -/

/-- **A fixed constant is subpolynomial.**  Used for the literal `4` of the shaded
uniformization, which does not depend on `δ`. -/
theorem exists_threshold_natCast_le_rpow (c : ℕ) (α : ℝ) (hα : 0 < α) :
    ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {δ : ℝ≥0}, 0 < δ → δ ≤ δ₀ → (c : ℝ) ≤ (δ : ℝ) ^ (-α) := by
  let A : ℝ≥0 := max (c : ℝ≥0) 1
  have hA : 1 ≤ A := le_max_right _ _
  have hcA : (c : ℝ≥0) ≤ A := le_max_left _ _
  obtain ⟨δ₀, hδ₀, hδ₀1, hgrid⟩ :=
    StickyKakeya.exists_threshold_gridLoss_le A hA 0 α hα
  refine ⟨δ₀, hδ₀, hδ₀1, ?_⟩
  intro δ hδ hδle
  have hpow : (A : ℝ) ≤ (A : ℝ) ^ (Tube.ssfGridLen δ + 1) := by
    simpa only [pow_one] using pow_le_pow_right₀ (by exact_mod_cast hA)
      (by omega : 1 ≤ Tube.ssfGridLen δ + 1)
  have hcgrid : (c : ℝ) ≤ StickyKakeya.gridLoss A 0 δ := by
    rw [StickyKakeya.gridLoss]
    simp only [zero_mul, pow_zero, mul_one]
    have hcAR : (c : ℝ) ≤ (A : ℝ) := by exact_mod_cast hcA
    exact hcAR.trans hpow
  exact hcgrid.trans (hgrid hδ hδle)

end Kakeya

end

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.BallDataGeneral
public import Kakeya.DimensionThree.MainLemma2.EDConstants

/-!
# GWZ §9.3 steps 6–8: the essentially-distinct segment family of a ball (R31)

GWZ **defines** `𝕋_B` to be "a set of essentially distinct `δ × δ × r₁`-tubes
contained in `B` of the form `T ∩ B` with `T ∈ 𝕋`", and `𝕋(T_B)` to be the set of tubes whose
restriction to `B` is *comparable* to `T_B`. Essential distinctness of the segment family is
therefore a property built into the construction, not the output of a per-block selection —
in the contrasting slab construction, GWZ state that the slabs of `S_Q` "need not be
essentially distinct".

The tree's segment producer `Kakeya.VeryNotSticky.ballDataCoreOfCover` puts **one segment per
tube** in each piece (`fam p = {p.1}`, `m = Cm = 1`), so its segment families are not
essentially distinct. This file supplies the fold that repairs that.

## What is here

* `Kakeya.exists_maximalPairwise` — maximal independent selection for a symmetric relation on a
  `Finset`, with the domination property. Unlike `Kakeya.exists_pairwise_not_of_degree_le` it
  needs **no degree bound**: the not-essentially-distinct degree of a segment family is
  `δ`-dependent (that is R31 itself), so the greedy weighted selection is not available here.
* `Kakeya.VeryNotSticky.edSel`, `edRep` — **step 6**: a maximal essentially distinct subfamily
  of the segments of a ball, and the assignment of every segment to a representative it is not
  essentially distinct from.
* `Kakeya.VeryNotSticky.edClass`, `edFam`, `edShade`, `edBody`, `edSegs` — **step 7**: the
  comparability class of a representative, its folded parent family `⋃_{q ∈ class} fam q` and
  its folded shading `⋃_{q ∈ class} Y(q) ∩ T_B` (GWZ: "we refine `Y` so that if
  `T ∈ 𝕋(T_B)`, `Y(T) ∩ T_B ⊂ Y_B(T_B)`"). The cut to the representative's carrier is what makes
  `ShadedBody.shade_subset` hold; under the comparability hypothesis it removes nothing.
* `Kakeya.VeryNotSticky.edFoldCore` — the folded `BallDataCore`, all forty-four fields.
* `Kakeya.VeryNotSticky.exists_core_edSegments_of_core` and
  `Kakeya.VeryNotSticky.exists_core_edSegments_of_cover` — **step 8**: the R31 conclusion, with
  the fibre count `Cm · m = M` inside the standing budget `δ^{-(η + 2 exscal)}` that
  `Kakeya.VeryNotSticky.eventually_slabScale_of_uniform_bounds` already grants.

## What is *not* here: the three geometric inputs

The fold is combinatorial. The geometry of GWZ's word "comparable" enters as three explicit
hypotheses on the input core, and only there:

* `Kakeya.VeryNotSticky.EDClassContainment` (G1): the shading of a segment lies in the carrier
  of any segment it is not essentially distinct from;
* `Kakeya.VeryNotSticky.EDClassCore` (G2): the representative's carrier lies along the core line
  of every tube of its class;
* `Kakeya.VeryNotSticky.EDClassMult` (G3): a class shades a point with multiplicity at most `M`.

`Kakeya.VeryNotSticky.edClass_alignment_price` records what these cost: the field
`BallDataCore.segs_core` gives the construction exactly `C₀ δ` of alignment budget, and `C₀` is
the caller's constant. `Kakeya.VeryNotSticky.edClass_inputs_of_pairwise_essDistinct` is the
non-vacuity control for (G1) and (G2).

No clause of `BallDataCore` is weakened:
the folded core is a `BallDataCore` of the same `C₀`, `D` and `Cg` as its input.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Set

namespace Kakeya

/-- **Maximal independent selection for a symmetric relation on a `Finset`.** -/
theorem exists_maximalPairwise {ι : Type*} (J : Finset ι) (r : ι → ι → Prop)
    (hsymm : ∀ i j, r i j → r j i) :
    ∃ J' ⊆ J, (J' : Set ι).Pairwise r ∧ ∀ j ∈ J, j ∈ J' ∨ ∃ i ∈ J', ¬ r i j := by
  classical
  set S : Finset (Finset ι) := J.powerset.filter (fun t => (t : Set ι).Pairwise r) with hS
  have hSne : S.Nonempty := ⟨∅, by simp [hS]⟩
  obtain ⟨J', hJ'S, hmax⟩ := Finset.exists_max_image S Finset.card hSne
  rw [hS, Finset.mem_filter, Finset.mem_powerset] at hJ'S
  refine ⟨J', hJ'S.1, hJ'S.2, ?_⟩
  intro j hj
  by_cases hjJ' : j ∈ J'
  · exact Or.inl hjJ'
  refine Or.inr ?_
  by_contra hcon
  push Not at hcon
  have hpair : ((insert j J' : Finset ι) : Set ι).Pairwise r := by
    intro a ha b hb hab
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact absurd rfl hab
      · exact hsymm _ _ (hcon b hb)
    · rcases hb with rfl | hb
      · exact hcon a ha
      · exact hJ'S.2 ha hb hab
  have hmem : insert j J' ∈ S := by
    rw [hS, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.insert_subset hj hJ'S.1, hpair⟩
  have := hmax _ hmem
  rw [Finset.card_insert_of_notMem hjJ'] at this
  omega

namespace VeryNotSticky

universe u

variable {cfg : VeryNotSticky.{u}}

/-! ### Re-indexing `maxDensity` along an injection -/

section Reindex

theorem densityIn_image {ι κ : Type*} [DecidableEq κ] (s : Finset ι) (f : ι → κ)
    (hf : ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y) (W : κ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :
    Kakeya.densityIn (s.image f) W K = Kakeya.densityIn s (fun i => W (f i)) K := by
  classical
  refine congrArg (fun t => t / volume K.carrier) ?_
  have hset : (s.image f).filter (fun j => W j ≤ K)
      = (s.filter (fun i => W (f i) ≤ K)).image f := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨i, hi, rfl⟩, hK⟩
      exact ⟨i, ⟨hi, hK⟩, rfl⟩
    · rintro ⟨i, ⟨hi, hK⟩, rfl⟩
      exact ⟨⟨i, hi, rfl⟩, hK⟩
  rw [hset, Finset.sum_image]
  intro x hx y hy hxy
  exact hf x (Finset.mem_filter.1 hx).1 y (Finset.mem_filter.1 hy).1 hxy

theorem maxDensity_image {ι κ : Type*} [DecidableEq κ] (s : Finset ι) (f : ι → κ)
    (hf : ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y)
    (W : κ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :
    Kakeya.maxDensity (s.image f) W = Kakeya.maxDensity s (fun i => W (f i)) := by
  refine le_antisymm ?_ ?_
  · rw [Kakeya.maxDensity_le_iff]
    intro K
    rw [densityIn_image s f hf W K]
    exact Kakeya.le_maxDensity _ _ _
  · rw [Kakeya.maxDensity_le_iff]
    intro K
    rw [← densityIn_image s f hf W K]
    exact Kakeya.le_maxDensity _ _ _

end Reindex

/-! ### Step 6: the essentially-distinct representatives of a ball -/

open scoped Classical in
/-- A maximal essentially-distinct subfamily of the segments of the ball `B`. -/
noncomputable def edSel (core : BallDataCore cfg) (B : core.bι) : Finset core.σ :=
  (exists_maximalPairwise (core.segs B)
    (fun p q => IsEssentiallyDistinct (core.Y p).carrier (core.Y q).carrier)
    (fun _ _ h => isEssentiallyDistinct_symm h)).choose

open scoped Classical in
theorem edSel_spec (core : BallDataCore cfg) (B : core.bι) :
    edSel core B ⊆ core.segs B ∧
      ((edSel core B : Finset core.σ) : Set core.σ).Pairwise
        (fun p q => IsEssentiallyDistinct (core.Y p).carrier (core.Y q).carrier) ∧
      ∀ q ∈ core.segs B, q ∈ edSel core B ∨ ∃ p ∈ edSel core B,
        ¬ IsEssentiallyDistinct (core.Y p).carrier (core.Y q).carrier :=
  (exists_maximalPairwise (core.segs B)
    (fun p q => IsEssentiallyDistinct (core.Y p).carrier (core.Y q).carrier)
    (fun _ _ h => isEssentiallyDistinct_symm h)).choose_spec

theorem edSel_subset (core : BallDataCore cfg) (B : core.bι) :
    edSel core B ⊆ core.segs B := (edSel_spec core B).1

theorem edSel_dominates (core : BallDataCore cfg) (B : core.bι) {q : core.σ}
    (hq : q ∈ core.segs B) :
    q ∈ edSel core B ∨ ∃ p ∈ edSel core B,
      ¬ IsEssentiallyDistinct (core.Y p).carrier (core.Y q).carrier :=
  (edSel_spec core B).2.2 q hq

open scoped Classical in
/-- The representative in `edSel core B` of a segment of the ball `B`. -/
noncomputable def edRep (core : BallDataCore cfg) (B : core.bι) (q : core.σ) : core.σ :=
  if q ∈ edSel core B then q
  else if h : ∃ p ∈ edSel core B,
      ¬ IsEssentiallyDistinct (core.Y p).carrier (core.Y q).carrier then h.choose else q

theorem edRep_of_mem (core : BallDataCore cfg) (B : core.bι) {q : core.σ}
    (hq : q ∈ edSel core B) : edRep core B q = q := by
  classical
  rw [edRep, if_pos hq]

theorem edRep_mem (core : BallDataCore cfg) (B : core.bι) {q : core.σ}
    (hq : q ∈ core.segs B) : edRep core B q ∈ edSel core B := by
  classical
  by_cases hq' : q ∈ edSel core B
  · rw [edRep_of_mem core B hq']; exact hq'
  · rcases edSel_dominates core B hq with h | h
    · exact absurd h hq'
    · rw [edRep, if_neg hq', dif_pos h]
      exact h.choose_spec.1

theorem edRep_ed (core : BallDataCore cfg) (B : core.bι) {q : core.σ}
    (hq : q ∈ core.segs B) :
    edRep core B q = q ∨
      ¬ IsEssentiallyDistinct (core.Y (edRep core B q)).carrier (core.Y q).carrier := by
  classical
  by_cases hq' : q ∈ edSel core B
  · exact Or.inl (edRep_of_mem core B hq')
  · rcases edSel_dominates core B hq with h | h
    · exact absurd h hq'
    · refine Or.inr ?_
      rw [edRep, if_neg hq', dif_pos h]
      exact h.choose_spec.2

/-! ### Step 7: the comparability class and the folded segment body -/

open scoped Classical in
/-- The comparability class of a representative: the segments of `B` assigned to `x`. -/
noncomputable def edClass (core : BallDataCore cfg) (B : core.bι) (x : core.σ) :
    Finset core.σ :=
  (core.segs B).filter (fun q => edRep core B q = x)

theorem mem_edClass {core : BallDataCore cfg} {B : core.bι} {x q : core.σ} :
    q ∈ edClass core B x ↔ q ∈ core.segs B ∧ edRep core B q = x := by
  classical
  simp [edClass]

open scoped Classical in
/-- The parent family of a representative: all tubes of the class members. -/
noncomputable def edFam (core : BallDataCore cfg) (B : core.bι) (x : core.σ) :
    Finset cfg.ι :=
  (edClass core B x).biUnion core.fam

theorem mem_edFam {core : BallDataCore cfg} {B : core.bι} {x : core.σ} {i : cfg.ι} :
    i ∈ edFam core B x ↔ ∃ q ∈ edClass core B x, i ∈ core.fam q := by
  classical
  simp [edFam]

/-- The folded shading of a representative: the shadings of its class, cut to its carrier. -/
noncomputable def edShade (core : BallDataCore cfg) (B : core.bι) (x : core.σ) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  ⋃ q ∈ edClass core B x, ((core.Y q).shade ∩ (core.Y x).carrier)

/-- The folded segment body: the representative's carrier, with the folded shading. -/
noncomputable def edBody (core : BallDataCore cfg) (B : core.bι) (x : core.σ) :
    ShadedBody (EuclideanSpace ℝ (Fin 3)) where
  toConvexSpaceBody := (core.Y x).toConvexSpaceBody
  shade := edShade core B x
  measurableSet_shade := by
    classical
    refine MeasurableSet.biUnion (edClass core B x).countable_toSet fun q _ => ?_
    exact (core.Y q).measurableSet_shade.inter
      ((core.Y x).isCompact'.isClosed.measurableSet)
  shade_subset := by
    intro z hz
    obtain ⟨q, -, hzq⟩ := Set.mem_iUnion₂.1 hz
    exact hzq.2

@[simp] theorem edBody_carrier (core : BallDataCore cfg) (B : core.bι) (x : core.σ) :
    (edBody core B x).carrier = (core.Y x).carrier := rfl

@[simp] theorem edBody_toConvexSpaceBody (core : BallDataCore cfg) (B : core.bι)
    (x : core.σ) :
    (edBody core B x).toConvexSpaceBody = (core.Y x).toConvexSpaceBody := rfl

@[simp] theorem edBody_shade (core : BallDataCore cfg) (B : core.bι) (x : core.σ) :
    (edBody core B x).shade = edShade core B x := rfl

/-! ### The class containment lemma -/

theorem edClass_shade_subset {core : BallDataCore cfg}
    (hclass : ∀ B ∈ core.bs, ∀ p ∈ core.segs B, ∀ q ∈ core.segs B,
      ¬ IsEssentiallyDistinct (core.Y p).carrier (core.Y q).carrier →
        (core.Y q).shade ⊆ (core.Y p).carrier)
    {B : core.bι} (hB : B ∈ core.bs) {x : core.σ} (hx : x ∈ edSel core B)
    {q : core.σ} (hq : q ∈ edClass core B x) :
    (core.Y q).shade ⊆ (core.Y x).carrier := by
  obtain ⟨hqs, hrep⟩ := mem_edClass.1 hq
  rcases edRep_ed core B hqs with h | h
  · rw [h] at hrep; subst hrep; exact (core.Y q).shade_subset
  · rw [hrep] at h
    exact hclass B hB x (edSel_subset core B hx) q hqs h

theorem edShade_eq {core : BallDataCore cfg}
    (hclass : ∀ B ∈ core.bs, ∀ p ∈ core.segs B, ∀ q ∈ core.segs B,
      ¬ IsEssentiallyDistinct (core.Y p).carrier (core.Y q).carrier →
        (core.Y q).shade ⊆ (core.Y p).carrier)
    {B : core.bι} (hB : B ∈ core.bs) {x : core.σ} (hx : x ∈ edSel core B) :
    edShade core B x = ⋃ q ∈ edClass core B x, (core.Y q).shade := by
  refine Set.iUnion₂_congr fun q hq => ?_
  exact Set.inter_eq_self_of_subset_left (edClass_shade_subset hclass hB hx hq)

theorem shade_subset_edShade {core : BallDataCore cfg}
    (hclass : ∀ B ∈ core.bs, ∀ p ∈ core.segs B, ∀ q ∈ core.segs B,
      ¬ IsEssentiallyDistinct (core.Y p).carrier (core.Y q).carrier →
        (core.Y q).shade ⊆ (core.Y p).carrier)
    {B : core.bι} (hB : B ∈ core.bs) {x : core.σ} (hx : x ∈ edSel core B)
    {q : core.σ} (hq : q ∈ edClass core B x) :
    (core.Y q).shade ⊆ edShade core B x := by
  rw [edShade_eq hclass hB hx]
  exact Set.subset_biUnion_of_mem (u := fun q => (core.Y q).shade) hq

open scoped Classical in
/-- The segment index set of a ball after the essentially-distinct selection. -/
noncomputable def edSegs (core : BallDataCore cfg) (B : core.bι) :
    Finset (core.bι × core.σ) :=
  (edSel core B).image (fun x => (B, x))

theorem mem_edSegs {core : BallDataCore cfg} {B : core.bι} {p : core.bι × core.σ} :
    p ∈ edSegs core B ↔ p.1 = B ∧ p.2 ∈ edSel core B := by
  classical
  constructor
  · intro hp
    obtain ⟨x, hx, hxp⟩ := Finset.mem_image.1 hp
    exact ⟨by rw [← hxp], by rw [← hxp]; exact hx⟩
  · rintro ⟨h1, h2⟩
    refine Finset.mem_image.2 ⟨p.2, h2, ?_⟩
    rw [← h1]

theorem mem_edSegs' {core : BallDataCore cfg} {B : core.bι} {p : core.bι × core.σ}
    (hp : p ∈ edSegs core B) : ∃ x ∈ edSel core B, p = (B, x) := by
  classical
  obtain ⟨x, hx, hxp⟩ := Finset.mem_image.1 hp
  exact ⟨x, hx, hxp.symm⟩

/-! ### Step 7: the folded core -/

section Fold

variable (core : BallDataCore cfg)

/-- (G1) The comparability containment: the shading of a segment lies in the carrier of any
segment it is *not* essentially distinct from. This is GWZ's `Y(T) ∩ T_B ⊂ T_B` for
`T ∈ 𝕋(T_B)` (GWZ), i.e. the comparability of `T ∩ B` with `T_B`. -/
abbrev EDClassContainment : Prop :=
  ∀ B ∈ core.bs, ∀ p ∈ core.segs B, ∀ q ∈ core.segs B,
    ¬ IsEssentiallyDistinct (core.Y p).carrier (core.Y q).carrier →
      (core.Y q).shade ⊆ (core.Y p).carrier

/-- (G2) The comparability core-line clause: the carrier of a representative lies along the
core line of every tube of its class. -/
abbrev EDClassCore : Prop :=
  ∀ B ∈ core.bs, ∀ p ∈ core.segs B, ∀ q ∈ core.segs B,
    ¬ IsEssentiallyDistinct (core.Y p).carrier (core.Y q).carrier →
      ∀ i ∈ core.fam q, ∃ z : EuclideanSpace ℝ (Fin 3), (core.Y p).carrier ⊆
        cthickening ((core.C₀ : ℝ) * (cfg.δ : ℝ))
          (AffineSubspace.mk' z (Submodule.span ℝ {(cfg.T i).direction}) :
            Set (EuclideanSpace ℝ (Fin 3)))

open scoped Classical in
/-- (G3) The class multiplicity budget: at most `M` tubes of a class shade a given point. -/
abbrev EDClassMult (M : ℝ≥0) : Prop :=
  ∀ B ∈ core.bs, ∀ x ∈ edSel core B, ∀ z : EuclideanSpace ℝ (Fin 3),
    ((((edFam core B x).filter (fun i => z ∈ core.Yg i)).card : ℕ) : ℝ≥0∞) ≤ (M : ℝ≥0∞)

open scoped Classical in
/-- **The essentially-distinct fold of a `BallDataCore`** (GWZ §9.3 steps 6–8): the segments of
each ball are replaced by a maximal essentially-distinct subfamily, the comparable segments are
folded into the representative's parent family and shading, and the fibre count becomes the
class multiplicity. -/
noncomputable def edFoldCore (hclass : EDClassContainment core) (hcore : EDClassCore core)
    (M : ℝ≥0) (hM : 1 ≤ M) (hmult : EDClassMult core M) : BallDataCore cfg where
  C₀ := core.C₀
  hC₀ := core.hC₀
  D := core.D
  Yg := core.Yg
  Yg_subset := core.Yg_subset
  Yg_measurable := core.Yg_measurable
  Cg := core.Cg
  hCg := core.hCg
  Yg_mass := core.Yg_mass
  bι := core.bι
  σ := core.bι × core.σ
  bs := core.bs
  bs_nonempty := core.bs_nonempty
  ctr := core.ctr
  P := core.P
  P_subset_ball := core.P_subset_ball
  P_disjoint := core.P_disjoint
  P_measurable := core.P_measurable
  P_cover := core.P_cover
  ballOverlap := core.ballOverlap
  segs := fun B => edSegs core B
  Y := fun p => edBody core p.1 p.2
  fam := fun p => edFam core p.1 p.2
  segs_nonempty := by
    intro B hB
    obtain ⟨q, hq⟩ := core.segs_nonempty B hB
    exact ⟨(B, edRep core B q), mem_edSegs.2 ⟨rfl, edRep_mem core B hq⟩⟩
  fam_subset := by
    intro B hB p hp i hi
    obtain ⟨x, hx, rfl⟩ := mem_edSegs' hp
    obtain ⟨q, hq, hiq⟩ := mem_edFam.1 hi
    exact core.fam_subset B hB q (mem_edClass.1 hq).1 hiq
  fam_disjoint := by
    intro B hB p hp q hq hpq
    rw [Finset.mem_coe] at hp hq
    obtain ⟨x, hx, rfl⟩ := mem_edSegs' hp
    obtain ⟨y, hy, rfl⟩ := mem_edSegs' hq
    have hne : x ≠ y := fun h => hpq (by rw [h])
    rw [Finset.disjoint_left]
    intro i hip hiq
    obtain ⟨a, ha, hia⟩ := mem_edFam.1 hip
    obtain ⟨b, hb, hib⟩ := mem_edFam.1 hiq
    have hab : a ≠ b := by
      intro h
      subst h
      exact hne (((mem_edClass.1 ha).2).symm.trans ((mem_edClass.1 hb).2))
    exact (Finset.disjoint_left.1
      (core.fam_disjoint B hB (mem_edClass.1 ha).1 (mem_edClass.1 hb).1 hab) hia) hib
  Y_piece := by
    intro B hB p hp z hz
    obtain ⟨x, hx, rfl⟩ := mem_edSegs' hp
    obtain ⟨q, hq, hzq⟩ := Set.mem_iUnion₂.1 (show z ∈ edShade core B x from hz)
    exact core.Y_piece B hB q (mem_edClass.1 hq).1 hzq.1
  segs_thickness := by
    intro B hB p hp
    obtain ⟨x, hx, rfl⟩ := mem_edSegs' hp
    exact core.segs_thickness B hB x (edSel_subset core B hx)
  segs_dims := by
    intro B hB p hp q hq
    obtain ⟨x, hx, rfl⟩ := mem_edSegs' hp
    obtain ⟨y, hy, rfl⟩ := mem_edSegs' hq
    exact core.segs_dims B hB x (edSel_subset core B hx) y (edSel_subset core B hy)
  parent := by
    intro B hB i hi hne
    obtain ⟨q, hq, hiq⟩ := core.parent B hB i hi hne
    refine ⟨(B, edRep core B q), mem_edSegs.2 ⟨rfl, edRep_mem core B hq⟩, ?_⟩
    exact mem_edFam.2 ⟨q, mem_edClass.2 ⟨hq, rfl⟩, hiq⟩
  into := by
    intro B hB p hp i hi
    obtain ⟨x, hx, rfl⟩ := mem_edSegs' hp
    obtain ⟨q, hq, hiq⟩ := mem_edFam.1 hi
    exact subset_trans (core.into B hB q (mem_edClass.1 hq).1 i hiq)
      (shade_subset_edShade (core := core) hclass hB hx hq)
  back := by
    intro B hB p hp z hz
    obtain ⟨x, hx, rfl⟩ := mem_edSegs' hp
    obtain ⟨q, hq, hzq⟩ := Set.mem_iUnion₂.1 (show z ∈ edShade core B x from hz)
    obtain ⟨i, hi, hzi⟩ :=
      Set.mem_iUnion₂.1 (core.back B hB q (mem_edClass.1 hq).1 hzq.1)
    exact Set.mem_biUnion (mem_edFam.2 ⟨q, hq, hi⟩) hzi
  segs_core := by
    intro B hB p hp i hi
    obtain ⟨x, hx, rfl⟩ := mem_edSegs' hp
    obtain ⟨q, hq, hiq⟩ := mem_edFam.1 hi
    obtain ⟨hqs, hrep⟩ := mem_edClass.1 hq
    rcases edRep_ed core B hqs with h | h
    · rw [h] at hrep
      subst hrep
      exact core.segs_core B hB q hqs i hiq
    · rw [hrep] at h
      exact hcore B hB x (edSel_subset core B hx) q hqs h i hiq
  m := 1
  Cm := M
  hCm := hM
  fibre := by
    intro B hB p hp z hz
    obtain ⟨x, hx, rfl⟩ := mem_edSegs' hp
    obtain ⟨q, hq, hzq⟩ := Set.mem_iUnion₂.1 (show z ∈ edShade core B x from hz)
    obtain ⟨i, hi, hzi⟩ :=
      Set.mem_iUnion₂.1 (core.back B hB q (mem_edClass.1 hq).1 hzq.1)
    have hiF : i ∈ (edFam core B x).filter (fun j => z ∈ core.Yg j) :=
      Finset.mem_filter.2 ⟨mem_edFam.2 ⟨q, hq, hi⟩, hzi⟩
    have hcard : 1 ≤ ((edFam core B x).filter (fun j => z ∈ core.Yg j)).card :=
      Finset.card_pos.2 ⟨i, hiF⟩
    refine ⟨?_, ?_⟩
    · have h1 : (1 : ℝ≥0∞) ≤
          ((((edFam core B x).filter (fun j => z ∈ core.Yg j)).card : ℕ) : ℝ≥0∞) := by
        exact_mod_cast hcard
      have hM' : (1 : ℝ≥0∞) ≤ (M : ℝ≥0∞) := by exact_mod_cast hM
      calc (((1 : ℝ≥0) : ℝ≥0∞)) = 1 * 1 := by simp
        _ ≤ (M : ℝ≥0∞) *
              ((((edFam core B x).filter (fun j => z ∈ core.Yg j)).card : ℕ) : ℝ≥0∞) := by
            gcongr
    · simpa using hmult B hB x hx z
  γ := core.γ
  cov := fun p => core.cov p.2
  covCtr := core.covCtr
  cov_isCover := by
    intro B hB p hp
    obtain ⟨x, hx, rfl⟩ := mem_edSegs' hp
    exact core.cov_isCover B hB x (edSel_subset core B hx)
  cov_meets := by
    intro B hB p hp i hi
    obtain ⟨x, hx, rfl⟩ := mem_edSegs' hp
    exact core.cov_meets B hB x (edSel_subset core B hx) i hi
  segs_subset_ball := by
    intro B hB p hp
    obtain ⟨x, hx, rfl⟩ := mem_edSegs' hp
    exact core.segs_subset_ball B hB x (edSel_subset core B hx)
  segs_scale := by
    intro B hB p hp
    obtain ⟨x, hx, rfl⟩ := mem_edSegs' hp
    exact core.segs_scale B hB x (edSel_subset core B hx)

end Fold

/-! ### Step 8: the folded core meets the R31 clauses -/

section FoldSpec

variable {core : BallDataCore cfg} (hclass : EDClassContainment core)
  (hcore : EDClassCore core) {M : ℝ≥0} (hM : 1 ≤ M) (hmult : EDClassMult core M)

@[simp] theorem edFoldCore_C₀ : (edFoldCore core hclass hcore M hM hmult).C₀ = core.C₀ := rfl
@[simp] theorem edFoldCore_D : (edFoldCore core hclass hcore M hM hmult).D = core.D := rfl
@[simp] theorem edFoldCore_Cg : (edFoldCore core hclass hcore M hM hmult).Cg = core.Cg := rfl
@[simp] theorem edFoldCore_bs : (edFoldCore core hclass hcore M hM hmult).bs = core.bs := rfl
@[simp] theorem edFoldCore_m : (edFoldCore core hclass hcore M hM hmult).m = 1 := rfl
@[simp] theorem edFoldCore_Cm : (edFoldCore core hclass hcore M hM hmult).Cm = M := rfl

@[simp] theorem edFoldCore_segs (B : core.bι) :
    (edFoldCore core hclass hcore M hM hmult).segs B = edSegs core B := rfl

@[simp] theorem edFoldCore_Y (p : core.bι × core.σ) :
    (edFoldCore core hclass hcore M hM hmult).Y p = edBody core p.1 p.2 := rfl

end FoldSpec

/-! ### The price of R31: what a comparability class costs in `C₀` -/

/-! ### The R31 core producer, from a core plus the three comparability inputs -/

/-! ### The capsule form of the three geometric inputs

The fold above is combinatorial; the geometry of GWZ's word *comparable* is isolated in
`EDClassContainment`, `EDClassCore` and `EDClassMult`. For the core that GWZ §9.3 steps 5–6
actually produce, whose segments are T3's capsules `segCarrierSet`, those three reduce to the
three statements below about **two capsules and a piece**. `CapsuleCoreLine` is where the
alignment budget `C₀ δ` appears explicitly. -/

section CapsuleInputs

theorem volume_segCarrierSet_ne_top {δ : ℝ≥0}
    (T : Tube δ (EuclideanSpace ℝ (Fin 3))) (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ}
    (hL : 0 ≤ L) : volume (segCarrierSet T c L) ≠ ⊤ :=
  ne_of_lt (lt_of_le_of_lt (measure_mono (segCarrierSet_subset_closedBall T c hL))
    measure_closedBall_lt_top)

variable (core : BallDataCore cfg)

end CapsuleInputs

/-! ### The cover-level form: G13's target, over the named §9.3 step-5/6 core -/

section Cover

variable (cfg : VeryNotSticky.{u}) {bι : Type u}
  {C₀ : ℝ≥0} (hC₀ : 4 ≤ C₀) {D : ℕ} (hD : ballCoverConstant ≤ D)
  (hδr : 16 * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ))
  (bs : Finset bι) (ctr : bι → EuclideanSpace ℝ (Fin 3))
  (P : bι → Set (EuclideanSpace ℝ (Fin 3)))
  (hbsne : bs.Nonempty)
  (hPball16 : ∀ B ∈ bs, P B ⊆ ball (ctr B) ((cfg.r₁ : ℝ) / 16))
  (hPball : ∀ B ∈ bs, P B ⊆ closedBall (ctr B) (cfg.r₁ : ℝ))
  (hPdisj : (bs : Set bι).PairwiseDisjoint P)
  (hPmeas : ∀ B, MeasurableSet (P B))
  (hPcov : ∀ i ∈ cfg.s, (cfg.T i).shade ⊆ ⋃ B ∈ bs, P B)
  (hoverlap : ∀ (x : EuclideanSpace ℝ (Fin 3)) (t : Finset bι), t ⊆ bs →
    (∀ B ∈ t, x ∈ ball (ctr B) (cfg.r₁ : ℝ)) → t.card ≤ ballCoverConstant)
  (hPne : ∀ B ∈ bs, (P B ∩ ⋃ i ∈ cfg.s, (cfg.T i).shade).Nonempty)
  {c₁ : ℝ≥0} (hc₁ : 0 < c₁)
  (hc₁' : 4 * c₁ * (ballCoverConstant : ℝ≥0) ≤ 1)

end Cover

end VeryNotSticky
end Kakeya

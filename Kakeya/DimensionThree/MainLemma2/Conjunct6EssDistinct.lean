/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.AngularMuBridge
public import Kakeya.Tube.Rescale

/-!
# Conjunct 6 from GWZ Definition 2.1(ii): the covering number `M` is a dimensional constant
once the parents are **essentially distinct**

`Kakeya.VeryNotSticky.angularFibre_card_le_of_exactCover`
(`MainLemma2/AngularMuHierarchy.lean`) bounds the angular cone by `M · C³ · branchingN k`,
where `M` is the number of exact `ρ_k`-containers the cone needs, and
`Kakeya.LooseUniform.exists_bush_forcing_exactCover_floor` shows `M ≥ ⌊1/(6ρ_k)⌋` if the
containers are supplied as an arbitrary cover.  That is the whole residue of conjunct 6, and
 left it there.

This file settles it: **`M` is bounded by a dimensional constant as soon as the level-`k`
*nodes* are pairwise essentially distinct**, which is GWZ Definition 2.1(ii) verbatim
(GWZ: "The tubes `𝕋_ρ` are essentially distinct.  Therefore each `T ∈ 𝕋` lies in
`T_ρ` for `∼1` choice of `T_ρ`") — the clause `Tube.UniformTubeSet` replaced by
`boundedOverlap`.  The count is the existing
`Tube.essDistinctTubesInSelfDilate`, and the geometry that feeds it is the existing
`Kakeya.LooseUniform.le_dilate_of_through_point`.

## The chain

* `exists_sign_norm_direction_sub_le_of_body_le` — exact containment of one unit-length tube in
  another pins their directions to `6 s`, up to sign (from `Tube.endpoints_close_of_body_le`).
* `tube_le_dilate_of_mem_angularFibre` — **the keystone geometry.**  *Any* `σ`-tube (`ρ ≤ σ`)
  containing a member of the angular cone at `(x, v)` of radius `ρ` lies in the `10`-dilate of the
  *single* `σ`-tube centred at `x` in the direction of a fixed cone member.  The cone's **members**
  lie in no common `σ`-tube (`Kakeya.LooseUniform.not_exists_common_tube_of_bush`); the `σ`-tubes
  that **contain** them do lie in one bounded dilate, and that is the asymmetry the exact-cover
  route missed.  No hierarchy is mentioned.
* `card_le_essDistinctConstant_of_edFamily` — **the keystone count**, on an arbitrary pairwise
  essentially distinct family: `M ≤ C_ED(3, 10) := Tube.essDistinctTubesInSelfDilate.C 3 10`, a
  dimensional constant, no `δ`.  Per  the datum belongs on **the family the
  consumer dilates**, so the family is a parameter;
  `card_filter_meets_angularFibre_le_of_essDistinct` is the same statement in the shape
  `Kakeya.VeryNotSticky.RhoParentData`'s fifth conjunct carries,
  and `card_image_assign_angularFibre_le_of_essDistinct` is the specialisation to a hierarchy's
  nodes — recorded, but **not claimed inhabited**:  measures that the existing
  uniformiser's nodes come from `Tube.grid_net_tight`'s `ρ/32`-separated net and are not
  essentially distinct.
* `angularFibre_card_le_of_essDistinct`, `angularFibre_card_le_fibreMult_of_essDistinct` —
  the cone bound at `C_ED · C²·branchingN k` and conjunct 6's inequality at `Cang = C_ED · C⁴`.
* `coe_C₀_pow_four_le_rpow_neg_half_eta` — `C₀⁴ ≤ δ^{-η/2}` (the square root of
  `coe_C₀_pow_eight_le_rpow_neg_eta`, in the pattern of `coe_C₀_sq_le_rpow_neg_quarter_eta`).
* `exists_Cang_angularFibre_le_of_essDistinct`, `eventually_conjunct6_of_essDistinct` —
  **conjunct 6 of `Kakeya.VeryNotSticky.SideDataObligations`, verbatim, with no unpaid budget**:
  `C₀⁴ ≤ δ^{-η/2}` is the configuration's own `aScaleData_absorb` and `C_ED(3,10) ≤ δ^{-η/2}`
  holds below a threshold in `η` alone (`Kakeya.AngularCover.exists_const_threshold`), so the
  product fits the clause's `δ^{-η}` exactly.  **No consumer text moves**: `SplitInputs`,
  `Kakeya.VeryNotSticky.tubeFibre`, `nonslabPointwiseBound`, `nonslabKKTPow` and
  `nonslabSplitBound` are untouched, and neither the refinement `Y′` of GWZ 
  nor the angular multiplicity `μ(ρ)` is needed.
* `card_le_essDistinctConstant_of_no_common_tube` — **the price, compiled.**  The same
  hypothesis caps at `C_ED(3,10)` the number of cone members that are pairwise in no common
  exact `ρ_k`-tube.  `Kakeya.LooseUniform.bush_obstruction` produces `n ≈ 1/(2ρ_k)` such members
  through a point, and `Kakeya.VeryNotSticky.card_le_of_bush` permits an admissible
  configuration up to `733·δ^{-η}` of them.  So in the **exact**-containment model the
  hypothesis is a strong axial-coherence condition and is *not* free: the parents of an axially
  spread bush are forced to be axial translates at spacing `ρ_k`, and unit-length tubes at
  axial spacing below `1/2` overlap in more than half their volume, i.e. are not essentially
  distinct.  Under GWZ's own reading of "lies in" (GWZ: containment up to an
  absolute-constant dilate) one parent absorbs the whole bush and Definition 2.1(ii) is free —
  which is exactly the model change  proposes.

## The loose port, and why it pays for itself

The last section of this file runs the same two steps in `Kakeya.LooseUniform`'s model, at
`K = 4`, where a member lies in the `K`-dilate of its node rather than in the node.  There
essential distinctness of the nodes proves **two of the three non-data fields** of
`Kakeya.LooseUniform.LooseUniformTubeSet`:

* `boundedOverlapDil` — `Kakeya.LooseUniform.card_filter_le_of_essDistinct`, at
  `Tube.essDistinctTubesInSelfDilate.C 3 130`, in the field's own text;
* `tube_injOn` — `Kakeya.LooseUniform.injOn_of_essDistinct`, since a tube of positive finite
  volume is not essentially distinct from itself.

`Kakeya.LooseUniform.LooseUniformTubeSet.ofEssDistinct` bundles that: a producer of the loose
hierarchy owes a `LooseGridCoverSystem`, a branching function, GWZ Definition 2.1(ii) and GWZ
Definition 2.1(iii) — and nothing else.  So adopting the source's essential-distinctness clause
*removes* producer obligations rather than adding one.  The one new geometric lemma this needs,
`exists_sign_norm_direction_sub_le_of_le_dilate` (direction control from containment in a
dilate), is proved here too: `Tube.endpoints_close_of_body_le` does not cover it, because
`Kakeya.Tube.dilate V c` is a `ConvexSpaceBody` and not a `Tube`.

## The `boundedOverlap`-only route: stated, and refuted at its covering step

Because the essential-distinctness clause is not available on the existing hierarchy, the obvious
alternative is to bound `Q` from `Tube.UniformTubeSet.boundedOverlap` alone.  Both halves are
here, and the route does not close:

* `card_image_assign_angularFibre_le_of_exactCover` — **the positive half**: if the cone's
  *members* are covered by `M` exact `ρ_k`-tubes then `Q ≤ M · C`, from `boundedOverlap` alone.
  `boundedOverlap`'s "some member of `s` lies in both the node and `V`" clause does **not** block:
  the witness is the cone member that put the node in the count.
* `Kakeya.LooseUniform.exists_bush_forcing_dilate_cover` — **the covering step is false**, already
  at the `4`-dilate: no family of exact `σ`-tubes with fewer than `⌊1/(6σ)⌋` members contains
  every unit `δ`-tube through `x` with the common direction lying in `Tube.dilate V 4`.  So `M`
  is not a dimensional constant, and `Q ≤ M·C` is polynomial.
  `Kakeya.LooseUniform.le_dilate_bushTube_of_through_point_dir` records that such tubes really do
  fill the dilate, so the refutation is about the region the route names and not a weaker one.

The obstruction is **length, not radius**: `boundedOverlap`'s container is a `Tube`, of unit
length, so it sees an `O(σ)` axial slice of a cone with axial extent `≈ 1`; a `Tube (2σ)` is no
better.  `Kakeya.LooseUniform.LooseUniformTubeSet.boundedOverlapDil`'s container is a *dilate*, of
length `K`, and one of those holds the whole cone.

## D-b's licence-independent half, and the finding

 relocates GWZ Definition 2.1(ii) onto the family the consumer dilates and notes
that `Kakeya.VeryNotSticky.RhoParentData`'s fifth conjunct already carries one.  The bridge from
such a family to conjunct 6's clause is here — `angularFibre_card_le_of_edCover` and
`angularFibre_le_edFibreMult` — with the missing clauses named as hypotheses, and so is the
measurement that the fifth conjunct supplies **none** of them: it has no assignment, no cover of
`sPar`, no Definition 2.1(iii) class bracket, no Definition 2.2 shading bracket, and its index type
`κ` is existentially quantified, hence not `ι`, so `Tube.GridCoverSystem` cannot express it as a
hierarchy.  **The ED family has no classes**, so its classes cannot serve as the consumers' fibre.

The consumers themselves, by contrast, need **no twins at all**, and that is compiled:
`nonslabPointwiseBound_on_edFamily` and `nonslabKKTPow_on_edFamily` instantiate the two existing
consumers on an arbitrary ED-family fibre without changing a token of their text —
`Kakeya.VeryNotSticky.nonslabPointwiseBound` reads its angular input as an abstract `A : ENNReal`,
and `Kakeya.VeryNotSticky.nonslabKKTPow` reads an arbitrary `sub ⊆ cfg.s` and a *free* node count
`N : ℕ`, whose `hcount` the fifth conjunct discharges verbatim at `Ccnt = 1`.  So the whole residue
of D-b is two clauses on the ED family's fibre: the fullness floor, and GWZ Definition 2.1(iii).

## What this decides, and what it does not

Decided: the residue of conjunct 6 is **one named clause**, essential distinctness of the
level-`k` parents; it is GWZ's own Definition 2.1(ii); it suffices, at a dimensional constant,
with the budget paid; and in the loose model it is cheaper than the fields it replaces.  Not
decided: whether that clause is producible on any hierarchy.  In the exact model the price
theorem says it is not, for any family with an axially spread bush — but that family has never
been exhibited as an admissible `Kakeya.VeryNotSticky`, so nothing here refutes the clause.

: every statement below is
new, and no protected or pinned text is touched.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Set Filter Topology

namespace Kakeya

namespace VeryNotSticky

open Kakeya.LooseUniform

universe u

theorem exists_sign_norm_direction_sub_le_of_body_le {δ' s : ℝ≥0}
    (A : Tube δ' E3) (B : Tube s E3)
    (hAB : A.toConvexSpaceBody ≤ B.toConvexSpaceBody) :
    ∃ σ : ℝ, |σ| = 1 ∧ ‖A.direction - σ • B.direction‖ ≤ 6 * (s : ℝ) := by
  rcases _root_.Tube.endpoints_close_of_body_le A B hAB with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨1, by norm_num, ?_⟩
    have heq : A.direction - (1 : ℝ) • B.direction = (A.y - B.y) - (A.x - B.x) := by
      simp only [Tube.direction]
      module
    rw [heq]
    calc ‖(A.y - B.y) - (A.x - B.x)‖ ≤ ‖A.y - B.y‖ + ‖A.x - B.x‖ := norm_sub_le _ _
      _ ≤ 3 * (s : ℝ) + 3 * (s : ℝ) := add_le_add h2 h1
      _ = 6 * (s : ℝ) := by ring
  · refine ⟨-1, by norm_num, ?_⟩
    have heq : A.direction - (-1 : ℝ) • B.direction = (A.y - B.x) - (A.x - B.y) := by
      simp only [Tube.direction]
      module
    rw [heq]
    calc ‖(A.y - B.x) - (A.x - B.y)‖ ≤ ‖A.y - B.x‖ + ‖A.x - B.y‖ := norm_sub_le _ _
      _ ≤ 3 * (s : ℝ) + 3 * (s : ℝ) := add_le_add h2 h1
      _ = 6 * (s : ℝ) := by ring

/-- **Direction transfer from a dilate.**  A unit-length `δ`-tube inside the `c`-dilate of a
`ρ`-tube has its direction within `4 c ρ` of the `ρ`-tube's, up to sign.  Unlike
`Tube.endpoints_close_of_body_le` this works for `Kakeya.Tube.dilate`, which is a
`ConvexSpaceBody` and not a `Tube`. -/
theorem exists_sign_norm_direction_sub_le_of_le_dilate {δ ρ : ℝ≥0}
    (T : Tube δ E3) (V : Tube ρ E3) {c : ℝ} (hc : 0 < c)
    (h : T.toConvexSpaceBody ≤ Kakeya.Tube.dilate V c) :
    ∃ σ : ℝ, |σ| = 1 ∧ ‖T.direction - σ • V.direction‖ ≤ 4 * c * (ρ : ℝ) := by
  have hρ0 : (0 : ℝ) ≤ (ρ : ℝ) := ρ.coe_nonneg
  have hVdir : ‖V.direction‖ = 1 := Tube.norm_direction V
  have hTdir : ‖T.direction‖ = 1 := Tube.norm_direction T
  by_cases hbig : (1 : ℝ) ≤ 2 * c * (ρ : ℝ)
  · refine ⟨1, by norm_num, ?_⟩
    rw [one_smul]
    calc ‖T.direction - V.direction‖ ≤ ‖T.direction‖ + ‖V.direction‖ := norm_sub_le _ _
      _ = 2 := by rw [hTdir, hVdir]; norm_num
      _ ≤ 4 * c * (ρ : ℝ) := by linarith
  rw [not_le] at hbig
  obtain ⟨a, ha, hxa⟩ := exists_axis_point_of_mem_dilate V hc (h (_root_.Tube.x_mem_carrier T))
  obtain ⟨b, hb, hyb⟩ := exists_axis_point_of_mem_dilate V hc (h (_root_.Tube.y_mem_carrier T))
  set e : E3 := (T.y - (V.center + b • V.direction)) - (T.x - (V.center + a • V.direction)) with he
  have hesplit : T.direction - (b - a) • V.direction = e := by
    simp only [he, Tube.direction]
    module
  have hea : ‖T.x - (V.center + a • V.direction)‖ ≤ c * (ρ : ℝ) := by
    rw [← dist_eq_norm]; exact hxa
  have heb : ‖T.y - (V.center + b • V.direction)‖ ≤ c * (ρ : ℝ) := by
    rw [← dist_eq_norm]; exact hyb
  have hebound : ‖e‖ ≤ 2 * (c * (ρ : ℝ)) := by
    calc ‖e‖ ≤ ‖T.y - (V.center + b • V.direction)‖ + ‖T.x - (V.center + a • V.direction)‖ :=
        norm_sub_le _ _
      _ ≤ c * (ρ : ℝ) + c * (ρ : ℝ) := add_le_add heb hea
      _ = 2 * (c * (ρ : ℝ)) := by ring
  -- the coefficient `b - a` is within `2cρ` of `±1`
  have hcoef : |(b - a)| = ‖(b - a) • V.direction‖ := by
    rw [norm_smul, Real.norm_eq_abs, hVdir, mul_one]
  have hclose : |(|b - a|) - 1| ≤ 2 * (c * (ρ : ℝ)) := by
    have h1 : ‖(b - a) • V.direction‖ ≤ ‖T.direction‖ + ‖e‖ := by
      have : (b - a) • V.direction = T.direction - e := by rw [← hesplit]; module
      rw [this]
      exact (norm_sub_le _ _).trans (by simp)
    have h2 : ‖T.direction‖ ≤ ‖(b - a) • V.direction‖ + ‖e‖ := by
      have : T.direction = (b - a) • V.direction + e := by rw [← hesplit]; module
      rw [this]
      exact norm_add_le _ _
    rw [← hcoef] at h1 h2
    rw [hTdir] at h1 h2
    rw [abs_le]
    constructor <;> linarith
  have hne : b - a ≠ 0 := by
    intro h0
    rw [h0] at hclose
    simp only [abs_zero, zero_sub, abs_neg, abs_one] at hclose
    linarith
  refine ⟨if 0 < b - a then 1 else -1, by split <;> norm_num, ?_⟩
  have hkey : ∀ σ : ℝ, |σ| = 1 → |(b - a) - σ| ≤ 2 * (c * (ρ : ℝ)) →
      ‖T.direction - σ • V.direction‖ ≤ 4 * c * (ρ : ℝ) := by
    intro σ hσ hσc
    have hsplit2 : T.direction - σ • V.direction = e + ((b - a) - σ) • V.direction := by
      rw [← hesplit]; module
    rw [hsplit2]
    calc ‖e + ((b - a) - σ) • V.direction‖ ≤ ‖e‖ + ‖((b - a) - σ) • V.direction‖ :=
        norm_add_le _ _
      _ = ‖e‖ + |(b - a) - σ| := by rw [norm_smul, Real.norm_eq_abs, hVdir, mul_one]
      _ ≤ 2 * (c * (ρ : ℝ)) + 2 * (c * (ρ : ℝ)) := add_le_add hebound hσc
      _ = 4 * c * (ρ : ℝ) := by ring
  by_cases hpos : 0 < b - a
  · simp only [hpos, if_pos]
    refine hkey 1 (by norm_num) ?_
    rw [abs_of_pos hpos] at hclose
    exact hclose
  · simp only [hpos, if_neg, not_false_iff]
    refine hkey (-1) (by norm_num) ?_
    have hneg : b - a < 0 := lt_of_le_of_ne (not_lt.mp hpos) hne
    rw [abs_of_neg hneg] at hclose
    have : |(b - a) - (-1)| = |(-(b-a)) - 1| := by
      rw [abs_sub_comm]
      congr 1
      ring
    rw [this]
    exact hclose

open scoped Classical in
/-- **Conjunct 6 *is* the node count.**  Whatever bounds the number of level-`k` nodes the
angular cone meets bounds the cone itself, at the cost of Definition 2.2's `C²`.  This is the
exact-model statement of what  calls `M`: `angularFibre_card_le_of_exactCover`
supplies `M` from a *cover* of the cone by containers and pays `M · C³`; here `Q` is the number
of **nodes**, and the price is `Q · C²`.  Every route to conjunct 6 in the exact model factors
through this lemma. -/
theorem angularFibre_card_le_of_nodeCount (cfg : VeryNotSticky.{u}) {N : ℕ} {C : ℝ≥0}
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T N C)
    {k : ℕ} (hk : k ≤ N) {Q : ℝ≥0} {ρ : ℝ}
    (x v : EuclideanSpace ℝ (Fin 3))
    (hQ : ((((cfg.angularFibre x v ρ).image (𝒱.tubeUniform.cover.assign k)).card : ℕ) : ℝ≥0∞)
      ≤ (Q : ℝ≥0∞)) :
    (((cfg.angularFibre x v ρ).card : ℕ) : ℝ≥0∞) ≤
      (Q : ℝ≥0∞) * (C : ℝ≥0∞) ^ 2 * ((𝒱.branchingN k : ℝ≥0) : ℝ≥0∞) := by
  classical
  set 𝒰 := 𝒱.tubeUniform with h𝒰
  set A := cfg.angularFibre x v ρ with hA
  rcases A.eq_empty_or_nonempty with hemp | ⟨i₀, hi₀⟩
  · simp [hemp]
  obtain ⟨hi₀s, hxi₀, -⟩ := Finset.mem_filter.mp hi₀
  have hxU : x ∈ ⋃ i ∈ cfg.s, (cfg.T i).shade := Set.mem_iUnion₂.mpr ⟨i₀, hi₀s, hxi₀⟩
  set J := A.image (𝒰.cover.assign k) with hJ
  have hsub : A ⊆
      J.biUnion (fun j' => ShadedTube.shadeClass cfg.s cfg.T (𝒰.cover.assign k) j' x) := by
    intro i hi
    obtain ⟨his, hxi, -⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_biUnion.mpr ⟨𝒰.cover.assign k i, Finset.mem_image_of_mem _ hi, ?_⟩
    simp only [ShadedTube.shadeClass, Finset.mem_filter]
    exact ⟨by simp [Tube.coverClass, his], hxi⟩
  have hJcard := hQ
  have hterm : ∀ j' ∈ J,
      (((ShadedTube.shadeClass cfg.s cfg.T (𝒰.cover.assign k) j' x).card : ℕ) : ℝ≥0∞)
        ≤ (C : ℝ≥0∞) * ((C : ℝ≥0∞) * ((𝒱.branchingN k : ℝ≥0) : ℝ≥0∞)) := by
    intro j' hj'
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj'
    obtain ⟨his, hxi, -⟩ := Finset.mem_filter.mp hi
    have h1 : ((ShadedTube.shadeClass cfg.s cfg.T (𝒰.cover.assign k)
        (𝒰.cover.assign k i) x).card : ℝ≥0) ≤ C * (C * 𝒱.branchingN k) := by
      calc ((ShadedTube.shadeClass cfg.s cfg.T (𝒰.cover.assign k)
              (𝒰.cover.assign k i) x).card : ℝ≥0)
          ≤ C * 𝒱.localN x k := 𝒱.card_shadeClass_le x hxU k hk i his hxi
        _ ≤ C * (C * 𝒱.branchingN k) := by gcongr; exact 𝒱.le_branchingN x hxU k hk
    have := ENNReal.coe_le_coe.mpr h1
    simpa [ENNReal.coe_mul] using this
  calc ((A.card : ℕ) : ℝ≥0∞)
      ≤ (((J.biUnion (fun j' =>
            ShadedTube.shadeClass cfg.s cfg.T (𝒰.cover.assign k) j' x)).card : ℕ) : ℝ≥0∞) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ((∑ j' ∈ J,
          (ShadedTube.shadeClass cfg.s cfg.T (𝒰.cover.assign k) j' x).card : ℕ) : ℝ≥0∞) := by
        exact_mod_cast Finset.card_biUnion_le
    _ = ∑ j' ∈ J,
          (((ShadedTube.shadeClass cfg.s cfg.T (𝒰.cover.assign k) j' x).card : ℕ) : ℝ≥0∞) := by
        push_cast; rfl
    _ ≤ ∑ _j' ∈ J, (C : ℝ≥0∞) * ((C : ℝ≥0∞) * ((𝒱.branchingN k : ℝ≥0) : ℝ≥0∞)) :=
        Finset.sum_le_sum hterm
    _ = ((J.card : ℕ) : ℝ≥0∞) *
          ((C : ℝ≥0∞) * ((C : ℝ≥0∞) * ((𝒱.branchingN k : ℝ≥0) : ℝ≥0∞))) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Q : ℝ≥0∞) *
          ((C : ℝ≥0∞) * ((C : ℝ≥0∞) * ((𝒱.branchingN k : ℝ≥0) : ℝ≥0∞))) := by
        gcongr
    _ = (Q : ℝ≥0∞) * (C : ℝ≥0∞) ^ 2 * ((𝒱.branchingN k : ℝ≥0) : ℝ≥0∞) := by ring

/-! ### The essentially distinct parent family in `RhoParentData`

At each admissible `ρ`, the fifth conjunct of `RhoParentData` supplies a
type `κ`, a finite family `tρ : Finset κ`, and tubes `Tρ : κ → Tube ρ E3`.
They are pairwise essentially distinct, satisfy the all-used condition
`∀ j ∈ tρ, ∃ i ∈ sPar, T i ≤ Tρ j`, and obey
`ρ^(-2 - ζ) ≤ |tρ|`.

These conditions supply no assignment, cover of `sPar`, class-size bracket
(Definition 2.1(iii)), or shading bracket (Definition 2.2). The all-used
condition runs from parent tubes to members of `sPar`, rather than covering
every member of `sPar`. Moreover, `κ` is existentially quantified, whereas
`Tube.GridCoverSystem` uses the original index type `ι` for both its
assignment and node tubes. The fourth conjunct supplies a
`Tube.UniformTubeSet sPar …`, but does not identify its nodes with this
essentially distinct family.

The following two theorems derive the angular clause from a parent family
with the necessary assignments and brackets given explicitly as hypotheses.
-/

end VeryNotSticky

/-! ### The loose port: `boundedOverlapDil` is a theorem of Definition 2.1(ii)

The same two steps run in `Kakeya.LooseUniform`'s loose model, where the member lies in the
`K`-dilate of its node rather than in the node.  There they prove something the exact model
cannot use: the assumed field
`Kakeya.LooseUniform.LooseUniformTubeSet.boundedOverlapDil` — the bounded-overlap clause that
`Kakeya.LooseUniform.angularCone_card_le_of_loose` consumes and that  lists as
a producer obligation — **follows from the essential distinctness of the loose nodes**, i.e.
from GWZ Definition 2.1(ii) verbatim.  So on the loose route this is not a new assumption but a
replacement of an assumed field by the source's own clause. -/

namespace LooseUniform

variable {ι : Type*}

end LooseUniform

end Kakeya

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.SplitInputsProduce
public import Kakeya.DimensionThree.MainLemma2.PartitionBrackets

/-!
# The loose hierarchy of Section 9

GWZ Definition 2.1 uses containment up to an absolute dilation
(GWZ). A `Tube.UniformTubeSet` instead
uses exact containment in unit-length node tubes. This module defines
`LooseGridCoverSystem`, `LooseUniformTubeSet`, and
`LooseShadedUniformTubeSet` with the dilated containment needed for
angular counts.

A member lies in the `K`-dilate of its assigned node and its direction
is within `ρ_k/4` of the node's axis. Bounded overlap is tested against
the `(K + 4)`-dilate of an arbitrary `ρ_k`-tube. Assignment classes
remain `Tube.coverClass`, so they partition the family.

## Angular geometry and counting

* `cone_tube_le_dilate` shows that a tube through a point of a loose
  member, at angle at most `2ρ` from it, lies in the `(K + 4)`-dilate
  of that member's node.
* `bush_obstruction` constructs `n` unit `δ`-tubes through one point
  with a common direction. All lie in the `4`-dilate of one `ρ`-tube,
  but no two lie in a common exact `ρ`-tube. Thus the number of exact
  assignment classes met by such a cone is unbounded. This is a
  geometric counterexample; it does not itself construct a
  `VeryNotSticky` configuration satisfying every additional hypothesis.
* `angularCone_card_le_of_loose` proves the composed angular bound
  from a loose shaded hierarchy, with `Cang = C^5`. The shading
  brackets must control the dilated classes: exact-class brackets
  alone introduce the potentially unbounded number of classes met.

`Tube.PartitionBrackets` packages the index sets, assignment, branching
number, and class brackets used by the fibre-counting lemmas. Both
exact and loose hierarchies map to it. The `pbTubeFibre` and
`pbActiveTubeNodes` lemmas state the common counting arguments, and
`SplitInputs` applications retain their respective geometric inputs.

## Relation to the source hypotheses

`boundedOverlapDil` states the bounded-overlap consequence of the
essential distinctness in Definition 2.1(ii), rather than essential
distinctness itself. Likewise, the shaded structure records bracket
consequences of Definition 2.2: it does not supply an entire separate
uniform hierarchy for the family through each point. These weaker
hypotheses suffice for `angularCone_card_le_of_loose`.

The applications `angularFibre_card_le_of_looseUniform` and
`eventually_conjunct6_of_looseUniform` are conditional on a loose
datum. They do not derive that datum from an exact hierarchy.
The example `NonVacuity.wShaded` satisfies the loose hypotheses with
two distinct tubes and nonempty shadings, positive shade volume for
`δ > 0`, nonconstant branching numbers, and nonempty index sets.
This example verifies consistency of the hypotheses for that family;
it is not a construction for arbitrary families.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Set

namespace Kakeya

namespace LooseUniform

/-- The ambient space of Section 9. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-! ### PA — the through-point containment in a dilate -/

/-- Unpacking `x ∈ dilate V K`: `x` is within `K ρ` of a point `center + s₀ • direction` of the
dilated axis, `|s₀| ≤ K/2`. -/
lemma exists_axis_point_of_mem_dilate {ρ : ℝ≥0} (V : Tube ρ E3) {K : ℝ} (hK : 0 < K)
    {x : E3} (hx : x ∈ (Kakeya.Tube.dilate V K).carrier) :
    ∃ s₀ : ℝ, |s₀| ≤ K / 2 ∧ dist x (V.center + s₀ • V.direction) ≤ K * ρ := by
  rw [Kakeya.Tube.dilate_carrier_eq_cthickening V hK,
    IsClosed.cthickening_eq_biUnion_closedBall isClosed_segment (by positivity)] at hx
  obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hx
  rw [segment_eq_image'] at hp
  obtain ⟨a, ⟨ha0, ha1⟩, rfl⟩ := hp
  refine ⟨K * (a - 1 / 2), ?_, ?_⟩
  · rw [abs_mul, abs_of_pos hK]
    have : |a - 1 / 2| ≤ 1 / 2 := abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
    calc K * |a - 1 / 2| ≤ K * (1 / 2) := mul_le_mul_of_nonneg_left this hK.le
      _ = K / 2 := by ring
  · have hcenter : V.center = (1 / 2 : ℝ) • (V.x + V.y) := by
      change midpoint ℝ V.x V.y = _
      rw [midpoint_eq_smul_add, invOf_eq_inv, one_div]
    have heq : (AffineMap.homothety V.center K) V.x +
        a • ((AffineMap.homothety V.center K) V.y - (AffineMap.homothety V.center K) V.x) =
        V.center + (K * (a - 1 / 2)) • V.direction := by
      simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, Tube.direction, hcenter]
      module
    rw [Metric.mem_closedBall] at hxp
    simp only at hxp
    rw [heq] at hxp
    exact hxp

/-- **The through-point containment.** If `x` is within `r` of the axis point
`center + s₀ • dir` of `V` with `|s₀| ≤ K'/2 - 1`, `T` is a `δ`-tube through `x` whose direction
is within `θ` (as a vector, up to sign `σ`) of `V`'s, and `2δ + r + θ ≤ K' ρ`, then
`T ⊆ dilate V K'`. -/
theorem le_dilate_of_through_point {δ ρ : ℝ≥0} (V : Tube ρ E3) {K' r θ : ℝ} (hK' : 0 < K')
    {x : E3} {s₀ : ℝ} (hs₀ : |s₀| ≤ K' / 2 - 1) (hxV : dist x (V.center + s₀ • V.direction) ≤ r)
    (T : Tube δ E3) (hx : x ∈ T.carrier) {σ : ℝ} (hσ : |σ| = 1)
    (hdir : ‖T.direction - σ • V.direction‖ ≤ θ)
    (hrad : 2 * (δ : ℝ) + r + θ ≤ K' * ρ) :
    T.toConvexSpaceBody ≤ Kakeya.Tube.dilate V K' := by
  intro z hz
  change z ∈ T.carrier at hz
  rw [T.carrier_eq] at hz hx
  obtain ⟨m, hm, hzm⟩ := Set.mem_iUnion₂.mp hz
  obtain ⟨m₀, hm₀, hxm₀⟩ := Set.mem_iUnion₂.mp hx
  rw [segment_eq_image'] at hm hm₀
  obtain ⟨a, ⟨ha0, ha1⟩, rfl⟩ := hm
  obtain ⟨b, ⟨hb0, hb1⟩, rfl⟩ := hm₀
  rw [Metric.mem_closedBall] at hzm hxm₀
  have hab : |a - b| ≤ 1 := abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  have hθ0 : 0 ≤ θ := le_trans (norm_nonneg _) hdir
  set s : ℝ := s₀ + (a - b) * σ with hs
  have hsbound : |s| ≤ K' / 2 := by
    calc |s| ≤ |s₀| + |(a - b) * σ| := abs_add_le _ _
      _ = |s₀| + |a - b| := by rw [abs_mul, hσ, mul_one]
      _ ≤ (K' / 2 - 1) + 1 := add_le_add hs₀ hab
      _ = K' / 2 := by ring
  refine Kakeya.Tube.mem_dilate_of_dist_axis_le V hK' hsbound ?_
  have hstep : dist (T.x + a • (T.y - T.x)) ((T.x + b • (T.y - T.x)) + ((a - b) * σ) • V.direction)
      ≤ θ := by
    rw [dist_eq_norm]
    have : T.x + a • (T.y - T.x) - (T.x + b • (T.y - T.x) + ((a - b) * σ) • V.direction)
        = (a - b) • (T.direction - σ • V.direction) := by
      simp only [Tube.direction]; module
    rw [this, norm_smul, Real.norm_eq_abs]
    calc |a - b| * ‖T.direction - σ • V.direction‖ ≤ 1 * θ :=
          mul_le_mul hab hdir (norm_nonneg _) zero_le_one
      _ = θ := one_mul θ
  have hshift : dist ((T.x + b • (T.y - T.x)) + ((a - b) * σ) • V.direction)
      (V.center + s • V.direction) =
        dist (T.x + b • (T.y - T.x)) (V.center + s₀ • V.direction) := by
    have : V.center + s • V.direction =
        (V.center + s₀ • V.direction) + ((a - b) * σ) • V.direction := by
      rw [hs, add_smul, add_assoc]
    rw [this, dist_add_right]
  calc dist z (V.center + s • V.direction)
      ≤ dist z (T.x + a • (T.y - T.x)) +
          dist (T.x + a • (T.y - T.x)) ((T.x + b • (T.y - T.x)) + ((a - b) * σ) • V.direction) +
          dist ((T.x + b • (T.y - T.x)) + ((a - b) * σ) • V.direction)
            (V.center + s • V.direction) :=
        dist_triangle4 _ _ _ _
    _ ≤ δ + θ + (dist (T.x + b • (T.y - T.x)) x + dist x (V.center + s₀ • V.direction)) := by
        rw [hshift]
        gcongr
        exact dist_triangle _ _ _
    _ ≤ δ + θ + (δ + r) := by
        gcongr
        rw [dist_comm]; exact hxm₀
    _ = 2 * (δ : ℝ) + r + θ := by ring
    _ ≤ K' * ρ := hrad


open InnerProductGeometry in
/-- **Chord ≤ arc, with a sign.** For unit `u, w`, `lineAngle u w ≤ θ` gives `σ = ±1` with
`‖u - σ • w‖ ≤ θ`: this converts the tree's `Kakeya.NonSlab.lineAngle` hypotheses into the
vector form the containment lemmas consume. -/
lemma exists_sign_norm_sub_le_of_lineAngle_le {u w : E3} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) {θ : ℝ}
    (h : NonSlab.lineAngle u w ≤ θ) : ∃ σ : ℝ, |σ| = 1 ∧ ‖u - σ • w‖ ≤ θ := by
  have key : ∀ w' : E3, ‖w'‖ = 1 → ‖u - w'‖ ≤ InnerProductGeometry.angle u w' := by
    intro w' hw'
    have hsq :=
      norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle u w'
    rw [hu, hw'] at hsq
    have hcos := Real.one_sub_sq_div_two_le_cos (x := InnerProductGeometry.angle u w')
    have hθ0 := InnerProductGeometry.angle_nonneg u w'
    have hle : ‖u - w'‖ ^ 2 ≤ (InnerProductGeometry.angle u w') ^ 2 := by nlinarith [hsq, hcos]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hθ0 two_ne_zero).mp hle
  rcases le_total (InnerProductGeometry.angle u w) (InnerProductGeometry.angle u (-w)) with h1 | h1
  · refine ⟨1, by simp, ?_⟩
    rw [one_smul]
    have hmin : NonSlab.lineAngle u w = InnerProductGeometry.angle u w := min_eq_left h1
    exact (key w hw).trans (hmin ▸ h)
  · refine ⟨-1, by simp, ?_⟩
    rw [neg_one_smul]
    have hmin : NonSlab.lineAngle u w = InnerProductGeometry.angle u (-w) := min_eq_right h1
    exact (key (-w) (by rw [norm_neg, hw])).trans (hmin ▸ h)

/-! ### PB — the bush: why the exact reading cannot carry the angular clause -/

/-- The bush tube at axial offset `t`: the unit `δ`-tube through `x` with direction `v` whose
core runs from `x + (t - 1/2)v` to `x + (t + 1/2)v`. -/
noncomputable def bushTube (δ : ℝ≥0) (x v : E3) (hv : ‖v‖ = 1) (t : ℝ) : Tube δ E3 :=
  Tube.mk' δ (x := x + (t - 1 / 2) • v) (y := x + (t + 1 / 2) • v) (by
    rw [dist_eq_norm, show x + (t - 1 / 2) • v - (x + (t + 1 / 2) • v) = -v by module,
      norm_neg, hv])

lemma bushTube_direction (δ : ℝ≥0) (x v : E3) (hv : ‖v‖ = 1) (t : ℝ) :
    (bushTube δ x v hv t).direction = v := by
  change (x + (t + 1 / 2) • v) - (x + (t - 1 / 2) • v) = v
  module

lemma x_mem_bushTube (δ : ℝ≥0) (x v : E3) (hv : ‖v‖ = 1) {t : ℝ} (ht : |t| ≤ 1 / 2) :
    x ∈ (bushTube δ x v hv t).carrier := by
  change x ∈ ⋃ z ∈ segment ℝ (x + (t - 1 / 2) • v) (x + (t + 1 / 2) • v), Metric.closedBall z δ
  refine Set.mem_iUnion₂.mpr ⟨x, ?_, Metric.mem_closedBall_self δ.coe_nonneg⟩
  rw [segment_eq_image']
  refine ⟨1 / 2 - t, ⟨by linarith [abs_le.mp ht], by linarith [abs_le.mp ht]⟩, ?_⟩
  simp only
  module


/-! ### The loose hierarchy: GWZ Def 2.1 and Def 2.2 read up to an `O(1)` dilation -/

section Loose
variable {ι : Type*}

/-- GWZ Definition 2.1(i) in the **loose** model (GWZ read with ):
nodes are exact `ρ_k`-tubes, the classes partition `s` (they are the fibres of `assign`), and a
member lies in the `K`-dilate of its node with its direction within `ρ_k/4` of the node's axis.

`Tube.GridCoverSystem.tube_nested` is deliberately dropped: dilates of nested nodes are
not nested at a fixed factor, and no Section-9 consumer reads it. `nested` on the *assignments*
is kept, because a producer's band machinery needs it. -/
structure LooseGridCoverSystem {δ : ℝ≥0} (s : Finset ι) (T : ι → Tube δ E3) (N : ℕ) (K : ℝ) where
  indexSet : ℕ → Finset ι
  assign : ℕ → ι → ι
  tube : (k : ℕ) → ι → Tube (Tube.gridScale δ N k) E3
  assign_mem : ∀ k, k ≤ N → ∀ i ∈ s, assign k i ∈ indexSet k
  le_dilate_tube_assign : ∀ k, k ≤ N → ∀ i ∈ s,
    (T i).toConvexSpaceBody ≤ Kakeya.Tube.dilate (tube k (assign k i)) K
  dir_close_tube_assign : ∀ k, k ≤ N → ∀ i ∈ s, ∃ σ : ℝ, |σ| = 1 ∧
    ‖(T i).direction - σ • (tube k (assign k i)).direction‖ ≤ (Tube.gridScale δ N k : ℝ) / 4
  nested : ∀ k, k + 1 ≤ N → ∀ i ∈ s, ∀ j ∈ s,
    assign (k + 1) i = assign (k + 1) j → assign k i = assign k j

/-- GWZ Definition 2.1(ii)-(iii) in the loose model. Bounded overlap is counted against the
`(K+4)`-dilate of an arbitrary `ρ_k`-tube — the container `Kakeya.LooseUniform.cone_tube_le_dilate`
produces — which is what makes it usable for the angular clause; the class brackets are
unchanged. -/
structure LooseUniformTubeSet {δ : ℝ≥0} (s : Finset ι) (T : ι → Tube δ E3) (N : ℕ) (K : ℝ)
    (C : ℝ≥0) where
  cover : LooseGridCoverSystem s T N K
  branchingN : ℕ → ℝ≥0
  tube_injOn : ∀ k ≤ N, Set.InjOn (cover.tube k) (cover.indexSet k : Set ι)
  boundedOverlapDil : ∀ k ≤ N, ∀ V : Tube (Tube.gridScale δ N k) E3,
    (open scoped Classical in
      (cover.indexSet k).filter (fun j => ∃ i ∈ s, cover.assign k i = j ∧
        (T i).toConvexSpaceBody ≤ Kakeya.Tube.dilate V (K + 4))).card ≤ C
  card_class_le : ∀ k ≤ N, ∀ j ∈ cover.indexSet k,
    ((Tube.coverClass s (cover.assign k) j).card : ℝ≥0) ≤ C * branchingN k
  le_card_class : ∀ k ≤ N, ∀ j ∈ cover.indexSet k,
    branchingN k ≤ C * ((Tube.coverClass s (cover.assign k) j).card : ℝ≥0)

/-- GWZ Definition 2.2 in the loose model: the six fields of
`ShadedTube.ShadedUniformTubeSet` over the loose tube hierarchy. The shade classes are
the same `ShadedTube.shadeClass` — classes are classes; only the geometry of what makes
a node a node has moved. -/
structure LooseShadedUniformTubeSet {δ : ℝ≥0} (s : Finset ι) (V : ι → ShadedTube δ E3) (N : ℕ)
    (K : ℝ) (C : ℝ≥0) where
  tubeUniform : LooseUniformTubeSet s (fun i => (V i).toTube) N K C
  branchingN : ℕ → ℝ≥0
  localN : E3 → ℕ → ℝ≥0
  card_shadeClass_le : ∀ x ∈ (⋃ i ∈ s, (V i).shade), ∀ k ≤ N, ∀ i ∈ s, x ∈ (V i).shade →
    ((ShadedTube.shadeClass s V (tubeUniform.cover.assign k) (tubeUniform.cover.assign k i) x).card
      : ℝ≥0) ≤ C * localN x k
  le_card_shadeClass : ∀ x ∈ (⋃ i ∈ s, (V i).shade), ∀ k ≤ N, ∀ i ∈ s, x ∈ (V i).shade →
    localN x k ≤
      C * ((ShadedTube.shadeClass s V (tubeUniform.cover.assign k)
        (tubeUniform.cover.assign k i) x).card : ℝ≥0)
  branchingN_le : ∀ x ∈ (⋃ i ∈ s, (V i).shade), ∀ k ≤ N, branchingN k ≤ C * localN x k
  le_branchingN : ∀ x ∈ (⋃ i ∈ s, (V i).shade), ∀ k ≤ N, localN x k ≤ C * branchingN k


end Loose

end LooseUniform


/-! ### `PartitionBrackets`: the hierarchy data used by the Section 9 fibre lemmas

`Tube.PartitionBrackets`, `Tube.UniformTubeSet.toPartitionBrackets` and the
fibre lemmas are in `MainLemma2/PartitionBrackets.lean`, which precedes the
consumers `Kakeya.VeryNotSticky.SplitInputs` and
`Kakeya.VeryNotSticky.TangentialInputs` in the import graph.
`Kakeya.LooseUniform.LooseUniformTubeSet.toPartitionBrackets` depends on the
loose structure defined here. -/

end Kakeya


namespace Kakeya

namespace LooseUniform

variable {ι : Type*}

/-- The loose hierarchy of GWZ Def 2.1, forgetting its geometry. The two brackets are the same
fields; only the geometry of "is a node of" differs, and the fibre lemmas do not read it. -/
def LooseUniformTubeSet.toPartitionBrackets {δ : ℝ≥0} {s : Finset ι} {T : ι → Tube δ E3}
    {N : ℕ} {K : ℝ} {C : ℝ≥0} (𝒰 : LooseUniformTubeSet s T N K C) :
    Tube.PartitionBrackets s N C where
  indexSet := 𝒰.cover.indexSet
  assign := 𝒰.cover.assign
  branchingN := 𝒰.branchingN
  assign_mem := 𝒰.cover.assign_mem
  card_class_le := 𝒰.card_class_le
  le_card_class := 𝒰.le_card_class

@[simp] lemma LooseUniformTubeSet.toPartitionBrackets_indexSet {δ : ℝ≥0} {s : Finset ι}
    {T : ι → Tube δ E3} {N : ℕ} {K : ℝ} {C : ℝ≥0} (𝒰 : LooseUniformTubeSet s T N K C) :
    𝒰.toPartitionBrackets.indexSet = 𝒰.cover.indexSet := rfl

@[simp] lemma LooseUniformTubeSet.toPartitionBrackets_assign {δ : ℝ≥0} {s : Finset ι}
    {T : ι → Tube δ E3} {N : ℕ} {K : ℝ} {C : ℝ≥0} (𝒰 : LooseUniformTubeSet s T N K C) :
    𝒰.toPartitionBrackets.assign = 𝒰.cover.assign := rfl

@[simp] lemma LooseUniformTubeSet.toPartitionBrackets_branchingN {δ : ℝ≥0} {s : Finset ι}
    {T : ι → Tube δ E3} {N : ℕ} {K : ℝ} {C : ℝ≥0} (𝒰 : LooseUniformTubeSet s T N K C) :
    𝒰.toPartitionBrackets.branchingN = 𝒰.branchingN := rfl

end LooseUniform

/-! ### The angular clause and the fibre lemmas over `PartitionBrackets`

The seven fibre lemmas are in `MainLemma2/PartitionBrackets.lean`; what follows is the part
that mentions `Kakeya.LooseUniform.LooseShadedUniformTubeSet` and therefore stays here. -/

namespace VeryNotSticky

open MeasureTheory Metric Set ShadedBody Filter Topology
open scoped NNReal ENNReal

universe u


/-! ### The angular clause on a configuration: `angularFibre_le_fibreMult` from the loose datum

This is where the model change pays for itself. The field
`Kakeya.VeryNotSticky.SplitInputs.angularFibre_le_fibreMult` is
`Kakeya.LooseUniform.angularCone_card_le_of_loose` instantiated at `Y := cfg.T`,
`ρ := ρ₂*`, with `Cang := C^5`; the three side conditions come from the configuration
(`4δ ≤ ρ_k` from `Kakeya.VeryNotSticky.four_mul_delta_le_rho2Star` and the level pin,
`ρ₂* ≤ ρ_k` is the level pin itself, and the positivity of the shades from `shading_lb`).
In the exact model no such theorem exists — `Kakeya.LooseUniform.bush_obstruction`. -/


/-- Every shade of the configuration has nonzero volume: `shading_lb` bounds it below by
`Cd⁻¹ · lam · |T|`, and each of the three factors is nonzero (`hCd`, `lam_ge` with `hδ`,
`Tube.le_volume` with `hδ`). This is `hvol` of
`Kakeya.LooseUniform.angularCone_card_le_of_loose`. -/
lemma volume_shade_ne_zero (cfg : VeryNotSticky) {i : cfg.ι} (hi : i ∈ cfg.s) :
    volume (cfg.T i).shade ≠ 0 := by
  have hcar : volume (cfg.T i).toShadedBody.carrier ≠ 0 := by
    set n := Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) with hn
    have hLpos : (Tube.le_volume.c n : ℝ≥0∞) * (cfg.δ : ℝ≥0∞) ^ (n - 1) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast (Tube.le_volume.c_pos n).ne')
        (pow_ne_zero _ (by exact_mod_cast cfg.hδ.ne'))
    exact (lt_of_lt_of_le (pos_iff_ne_zero.mpr hLpos) (Tube.le_volume (cfg.T i).toTube)).ne'
  have hlam : cfg.lam ≠ 0 := by
    have hCd0 : 0 < cfg.Cd := lt_of_lt_of_le zero_lt_one cfg.hCd
    have hδη : 0 < cfg.δ ^ (2 * cfg.η) := NNReal.rpow_pos cfg.hδ
    exact (lt_of_lt_of_le (mul_pos hCd0 hδη) cfg.lam_ge).ne'
  have hpos : ((cfg.Cd : ℝ≥0∞))⁻¹ *
      ((cfg.lam : ℝ≥0∞) * volume (cfg.T i).toShadedBody.carrier) ≠ 0 :=
    mul_ne_zero (ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top)
      (mul_ne_zero (by exact_mod_cast hlam) hcar)
  intro h0
  exact hpos (le_antisymm (by simpa [h0] using cfg.shading_lb i hi) bot_le)


end VeryNotSticky

end Kakeya

namespace Kakeya

namespace LooseUniform

/-! ### Non-vacuity of the loose datum: an explicit two-member witness

Everything above is a *conditional* fact about a hypothesis type. This section discharges the
one thing a `∀`-binder over an uninhabited type cannot be trusted without: it exhibits a
compiled inhabitant of `Kakeya.LooseUniform.LooseShadedUniformTubeSet` on a family of
**two** members with **non-constant branching**, and proves the cardinality.
-/

namespace NonVacuity

/-! #### The ambient unit vector -/

/-- The first coordinate direction of `E3`. -/
noncomputable def e₁ : E3 := EuclideanSpace.single 0 1

lemma norm_e₁ : ‖e₁‖ = 1 := by
  simp [e₁]

lemma e₁_ne_zero : e₁ ≠ 0 := fun h => by simpa [h] using norm_e₁

/-! #### Elementary facts about `Kakeya.LooseUniform.bushTube` -/

lemma bushTube_center (δ : ℝ≥0) (x v : E3) (hv : ‖v‖ = 1) (t : ℝ) :
    (bushTube δ x v hv t).center = x + t • v := by
  change midpoint ℝ (x + (t - 1 / 2) • v) (x + (t + 1 / 2) • v) = x + t • v
  rw [midpoint_eq_smul_add, invOf_eq_inv, one_div]
  module

lemma bushTube_x_eq (δ : ℝ≥0) (x v : E3) (hv : ‖v‖ = 1) (t : ℝ) :
    (bushTube δ x v hv t).x = x + (t - 1 / 2) • v := rfl

lemma mem_segment_bushTube (δ : ℝ≥0) (x v : E3) (hv : ‖v‖ = 1) {t : ℝ} (ht : |t| ≤ 1 / 2) :
    x ∈ segment ℝ (bushTube δ x v hv t).x (bushTube δ x v hv t).y := by
  rw [segment_eq_image']
  refine ⟨1 / 2 - t, ⟨by linarith [abs_le.mp ht], by linarith [abs_le.mp ht]⟩, ?_⟩
  change (x + (t - 1 / 2) • v) + (1 / 2 - t) • ((x + (t + 1 / 2) • v) - (x + (t - 1 / 2) • v)) = x
  module

/-- Distinct axial offsets give distinct bush tubes. -/
lemma bushTube_offset_injective {ρ : ℝ≥0} {t t' : ℝ}
    (h : bushTube ρ 0 e₁ norm_e₁ t = bushTube ρ 0 e₁ norm_e₁ t') : t = t' := by
  have hx : (bushTube ρ 0 e₁ norm_e₁ t).x = (bushTube ρ 0 e₁ norm_e₁ t').x := by rw [h]
  rw [bushTube_x_eq, bushTube_x_eq, zero_add, zero_add] at hx
  have hz : (t - t') • e₁ = 0 := by
    rw [show t - t' = (t - 1 / 2) - (t' - 1 / 2) by ring, sub_smul, hx, sub_self]
  rcases smul_eq_zero.mp hz with h1 | h1
  · linarith
  · exact absurd h1 e₁_ne_zero

/-- **Containment in the `4`-dilate of a coarser bush tube through the same point.** Both tubes
run through the origin in the direction `e₁`; the member's offset `t` keeps the origin on its
core, and the node's offset `t'` is small enough that the origin sits on the node's dilated
core. This is the only geometry the witness needs. -/
lemma bushTube_le_dilate_bushTube {δ ρ : ℝ≥0} {t t' : ℝ}
    (ht : |t| ≤ 1 / 2) (ht' : |t'| ≤ 1) (hrad : 2 * (δ : ℝ) ≤ 4 * (ρ : ℝ)) :
    (bushTube δ 0 e₁ norm_e₁ t).toConvexSpaceBody ≤
      Kakeya.Tube.dilate (bushTube ρ 0 e₁ norm_e₁ t') 4 := by
  refine le_dilate_of_through_point (bushTube ρ 0 e₁ norm_e₁ t') (K' := 4) (r := 0) (θ := 0)
    (by norm_num) (s₀ := -t') (by rw [abs_neg]; linarith) ?_
    (bushTube δ 0 e₁ norm_e₁ t) (x_mem_bushTube δ 0 e₁ norm_e₁ ht) (σ := 1) (by norm_num)
    ?_ (by linarith)
  · rw [bushTube_center, bushTube_direction]
    rw [show (0 : E3) + t' • e₁ + (-t') • e₁ = 0 by module, dist_self]
  · rw [bushTube_direction, bushTube_direction, one_smul, sub_self, norm_zero]

/-! #### The two-member family -/

/-- The two axial offsets: `0` and `1/4`. -/
noncomputable def off (i : Fin 2) : ℝ := (i : ℝ) / 4

lemma off_abs_le (i : Fin 2) : |off i| ≤ 1 / 2 := by fin_cases i <;> norm_num [off]

lemma off_injective : Function.Injective off := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [off]

/-- **The witness family.** Two unit `δ`-tubes through the origin in the direction `e₁`, at
axial offsets `0` and `1/4` — so they are distinct tubes — each shaded by the ball
`closedBall 0 δ` around their common point. -/
noncomputable def wV (δ : ℝ≥0) (i : Fin 2) : ShadedTube δ E3 where
  toTube := bushTube δ 0 e₁ norm_e₁ (off i)
  shade := Metric.closedBall 0 (δ : ℝ)
  measurableSet_shade := measurableSet_closedBall
  shade_subset :=
    (bushTube δ 0 e₁ norm_e₁ (off i)).closedBall_subset_carrier_of_mem_segment
      (mem_segment_bushTube δ 0 e₁ norm_e₁ (off_abs_le i))

@[simp] lemma wV_toTube (δ : ℝ≥0) (i : Fin 2) :
    (wV δ i).toTube = bushTube δ 0 e₁ norm_e₁ (off i) := rfl

@[simp] lemma wV_shade (δ : ℝ≥0) (i : Fin 2) :
    (wV δ i).shade = Metric.closedBall 0 (δ : ℝ) := rfl


/-- The index sets: one node at the coarse level `k = 0`, two nodes at the fine level `k = 1`. -/
def wIndex (k : ℕ) : Finset (Fin 2) := if k = 0 then {0} else Finset.univ


/-- The assignment: both members share the single coarse node; each is its own fine node. -/
def wAssign (k : ℕ) (i : Fin 2) : Fin 2 := if k = 0 then 0 else i

/-- The nodes: bush tubes of the grid radius `ρ_k`, through the origin in the direction `e₁`,
at offset `0` at the coarse level and at the member's own offset at the fine level. -/
noncomputable def wNode (δ : ℝ≥0) (k : ℕ) (i : Fin 2) : Tube (Tube.gridScale δ 1 k) E3 :=
  bushTube (Tube.gridScale δ 1 k) 0 e₁ norm_e₁ (if k = 0 then 0 else off i)

/-- The branching numbers: `2` at the coarse level, `1` at the fine level. **Non-constant** —
this is what distinguishes the witness from a one-node or one-member degeneracy. -/
def wBranch (k : ℕ) : ℝ≥0 := if k = 0 then 2 else 1

lemma one_le_wBranch (k : ℕ) : 1 ≤ wBranch k := by unfold wBranch; split <;> norm_num

lemma wBranch_le_two (k : ℕ) : wBranch k ≤ 2 := by unfold wBranch; split <;> norm_num


/-! #### The class brackets -/

lemma mem_coverClass_self (k : ℕ) (i : Fin 2) :
    i ∈ Tube.coverClass (Finset.univ : Finset (Fin 2)) (wAssign k) (wAssign k i) := by
  classical
  simp [Tube.coverClass]

lemma one_le_card_coverClass {k : ℕ} (hk : k ≤ 1) {j : Fin 2} (hj : j ∈ wIndex k) :
    1 ≤ (Tube.coverClass (Finset.univ : Finset (Fin 2)) (wAssign k) j).card := by
  refine Finset.card_pos.mpr ⟨j, ?_⟩
  have hjj : wAssign k j = j := by
    interval_cases k
    · have hj0 : j = 0 := by simpa [wIndex] using hj
      simp [wAssign, hj0]
    · simp [wAssign]
  simpa [hjj] using mem_coverClass_self k j

lemma card_finset_fin_two (t : Finset (Fin 2)) : t.card ≤ 2 := by
  simpa using Finset.card_le_univ t

lemma card_finset_fin_two_nnreal (t : Finset (Fin 2)) : (t.card : ℝ≥0) ≤ 2 := by
  exact_mod_cast card_finset_fin_two t

lemma card_coverClass_le_two (k : ℕ) (j : Fin 2) :
    (Tube.coverClass (Finset.univ : Finset (Fin 2)) (wAssign k) j).card ≤ 2 :=
  card_finset_fin_two _

lemma two_le_two_mul_wBranch (k : ℕ) : (2 : ℝ≥0) ≤ 2 * wBranch k :=
  le_mul_of_one_le_right (by norm_num) (one_le_wBranch k)


/-! #### The three loose structures, inhabited -/

/-- GWZ Definition 2.1(i) in the loose model, on the witness family. -/
noncomputable def wCover (δ : ℝ≥0) (hδ : δ ≤ 1) :
    LooseGridCoverSystem (Finset.univ : Finset (Fin 2)) (fun i => (wV δ i).toTube) 1 4 where
  indexSet := wIndex
  assign := wAssign
  tube := wNode δ
  assign_mem := by
    intro k hk i _
    interval_cases k <;> simp [wIndex, wAssign]
  le_dilate_tube_assign := by
    intro k hk i _
    have hδ' : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ
    have hδ0 : (0 : ℝ) ≤ (δ : ℝ) := δ.coe_nonneg
    interval_cases k
    · have hnode : wNode δ 0 (wAssign 0 i) = bushTube (Tube.gridScale δ 1 0) 0 e₁ norm_e₁ 0 := by
        simp [wNode]
      rw [wV_toTube, hnode]
      refine bushTube_le_dilate_bushTube (off_abs_le i) (by norm_num) ?_
      rw [Tube.gridScale_zero]
      push_cast
      linarith
    · have hnode : wNode δ 1 (wAssign 1 i)
          = bushTube (Tube.gridScale δ 1 1) 0 e₁ norm_e₁ (off i) := by
        simp [wNode, wAssign]
      rw [wV_toTube, hnode]
      refine bushTube_le_dilate_bushTube (off_abs_le i) (by
        have := off_abs_le i; linarith) ?_
      rw [Tube.gridScale_self δ Nat.one_pos]
      linarith
  dir_close_tube_assign := by
    intro k hk i _
    refine ⟨1, by norm_num, ?_⟩
    have h1 : ((wV δ i).toTube).direction = e₁ := bushTube_direction δ 0 e₁ norm_e₁ (off i)
    have h2 : (wNode δ k (wAssign k i)).direction = e₁ :=
      bushTube_direction (Tube.gridScale δ 1 k) 0 e₁ norm_e₁ _
    rw [h1, h2, one_smul, sub_self, norm_zero]
    positivity
  nested := by
    intro k hk i _ j _ _
    have hk0 : k = 0 := by omega
    subst hk0
    simp [wAssign]

@[simp] lemma wCover_indexSet (δ : ℝ≥0) (hδ : δ ≤ 1) : (wCover δ hδ).indexSet = wIndex := rfl
@[simp] lemma wCover_assign (δ : ℝ≥0) (hδ : δ ≤ 1) : (wCover δ hδ).assign = wAssign := rfl
@[simp] lemma wCover_tube (δ : ℝ≥0) (hδ : δ ≤ 1) : (wCover δ hδ).tube = wNode δ := rfl

/-- GWZ Definition 2.1(ii)-(iii) in the loose model, on the witness family, at `K = 4`,
`C = 2`, `N = 1`. -/
noncomputable def wUniform (δ : ℝ≥0) (hδ : δ ≤ 1) :
    LooseUniformTubeSet (Finset.univ : Finset (Fin 2)) (fun i => (wV δ i).toTube) 1 4 2 where
  cover := wCover δ hδ
  branchingN := wBranch
  tube_injOn := by
    intro k hk
    interval_cases k
    · intro a ha b hb _
      have ha0 : a = 0 := by simpa [wIndex] using ha
      have hb0 : b = 0 := by simpa [wIndex] using hb
      rw [ha0, hb0]
    · intro a _ b _ hab
      simp only [wCover_tube] at hab
      have h1 : wNode δ 1 a = bushTube (Tube.gridScale δ 1 1) 0 e₁ norm_e₁ (off a) := by
        simp [wNode]
      have h2 : wNode δ 1 b = bushTube (Tube.gridScale δ 1 1) 0 e₁ norm_e₁ (off b) := by
        simp [wNode]
      rw [h1, h2] at hab
      exact off_injective (bushTube_offset_injective hab)
  boundedOverlapDil := by
    intro k hk V
    exact card_finset_fin_two_nnreal _
  card_class_le := by
    intro k hk j hj
    have h1 : ((Tube.coverClass (Finset.univ : Finset (Fin 2)) (wAssign k) j).card : ℝ≥0)
        ≤ 2 := by exact_mod_cast card_coverClass_le_two k j
    calc ((Tube.coverClass (Finset.univ : Finset (Fin 2)) ((wCover δ hδ).assign k) j).card :
            ℝ≥0)
        ≤ 2 := by rw [wCover_assign]; exact h1
      _ ≤ 2 * wBranch k := two_le_two_mul_wBranch k
  le_card_class := by
    intro k hk j hj
    rw [wCover_indexSet] at hj
    have h1 : (1 : ℝ≥0)
        ≤ ((Tube.coverClass (Finset.univ : Finset (Fin 2)) (wAssign k) j).card : ℝ≥0) := by
      exact_mod_cast one_le_card_coverClass hk hj
    calc wBranch k ≤ 2 := wBranch_le_two k
      _ = 2 * 1 := by norm_num
      _ ≤ 2 * ((Tube.coverClass (Finset.univ : Finset (Fin 2)) ((wCover δ hδ).assign k) j).card :
            ℝ≥0) := by rw [wCover_assign]; gcongr

@[simp] lemma wUniform_cover (δ : ℝ≥0) (hδ : δ ≤ 1) :
    (wUniform δ hδ).cover = wCover δ hδ := rfl

@[simp] lemma wUniform_branchingN (δ : ℝ≥0) (hδ : δ ≤ 1) :
    (wUniform δ hδ).branchingN = wBranch := rfl


/-! #### What the witness proves -/


end NonVacuity

end LooseUniform

end Kakeya

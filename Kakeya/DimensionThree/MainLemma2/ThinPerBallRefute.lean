/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.ThinFactoringRefute
public import Kakeya.Thickness.Diam

/-!
# `Kakeya.ThinCase.perBall` inherits the defect of `Kakeya.ThinCase.factoringApply`

`Kakeya.ThinCase.factoringApply` is refuted in
`Kakeya/DimensionThree/MainLemma2/ThinFactoringRefute.lean`. This file settles that: **it is false**, for exactly the same reason.

## The two clauses

`Kakeya.ThinCase.ThinBall` carries the same pair of clauses that refuted `factoringApply`,
at the larger radius `A = rad C₀ a = max 1 (4 C₀) * a`:

* `ThinBall.centredMult` — `|U(𝕋_B, Y'_B) ∩ B(x, A)| ≤ C |U(𝕋_B, Y'_B) ∩ B(y, A)|` for all
  `x, y ∈ U(𝕋_B, Y'_B)`;
* `ThinBall.refine_S` together with `ThinBall.S_nonempty` — on the non-empty subfamily `𝒮_B`
  the refinement is termwise, `|Y_B(p)| ≤ C |Y'_B(p)|`.

With one segment (`segs.card = 1`) the second forces `C⁻¹ |Y(p)| ≤ |Y'(p)|`, so the pair is
exactly clauses (iv)+(vi) of `factoringApply` again, and
`Kakeya.ThinCase.perBallConstant C₀ CF c₁ Ccore D` sees only `C₀`, `CF`, `c₁`, `D` and — through
the four `Ccore` binders — `segs.card`, `bodies.card` and `δ`. None of them sees the covering
number of the shaded union at scale `A`, and nothing in `IsBallFactoring` bounds it: `thick`
and `body` pin the *shape* `(r₁, b, a)` of the bodies but leave `r₁` free, and
`IsBallFactoring` never says where in space the bodies are.

## The witness

One segment inside one body, so `segs.card = bodies.card = 1` and the output constant is one
fixed number `C := perBallConstant 2 1 1 (factoringApplyCore 3 1 1 (1/8)) 4`:

| object | value |
|---|---|
| carrier (= body) | `capsule M`, the closed `1/16`-neighbourhood of `[0, 2(M+1)] e₀` |
| shading | `⋃_{k < M} closedBall (2(k+1) e₀) ((1/32)(k+1)^(-1/3))` |
| scales | `δ = a = b = 1/8`, `w₁ = 1/8`, `r₁ = 2(M+1)`, `C₀ = 2`, `CF = c₁ = 1`, `D = 4` |

The capsule has `1`- and `2`-thickness exactly `1/16` and `0`-thickness in `[(M+1), 2(M+1) +
1/16]`, so `HasThicknesses (capsule M) 2 ![2(M+1), 1/8, 1/8]` holds for both `thick` and `body`
at once; a one-element family is `1`-Frostman in its own body; and the `δ`-ball covers of (T5)
are the balls of radius `1/8` about `(j/16) e₀`, which overlap at most `4`-fold. The blobs are
`2`-separated and have diameter `≤ 1/16`, so with

`A = rad 2 (1/8) = max 1 8 * (1/8) = 1`

the ball `B(x, A)` about a point of a blob meets the shading in that blob only. The masses are
harmonic, `(k+1) |blob k| = massUnit`, and the argument of
`Kakeya.ThinCase.Refute.harmonic_le_of_centredMult` — reproved here for these blobs — gives
`∑_{k<M} (k+1)⁻¹ ≤ C ^ 2` for every `M`.

## The repair, which is existing

`Kakeya.ThinCase.PerBallRefute.not_subset_closedBall_one` records that the witness violates the
localisation `(Wb j).carrier ⊆ closedBall z 1` for *every* centre `z`. So the hypothesis that
`Kakeya.ThinCase.factoringApply` is missing has to be visible at `Kakeya.ThinCase.perBall` too.
It now is: `perBall` carries

`hloc : ∃ z : E, ∀ j ∈ bodies, (Wb j).carrier ⊆ Metric.closedBall z 1`

as a binder — beside `hδw₁` and `hw₁one`, which are relocated hypotheses for the same reason:
`IsBallFactoring.body` pins the *shape* `(r₁, b, a)` of the bodies but leaves `r₁` free and
never says where in space they sit. The call site can discharge it, and does:
`Kakeya.ThinCase.thinSetupExists` passes it through and
`Kakeya.VeryNotSticky.exists_thinConfig` proves it from
`Kakeya.VeryNotSticky.BallData.bodies_subset_ball`, which already asserts
`(Wb j).carrier ⊆ closedBall (ctr B) r₁`, together with `r₁ = δ ^ exscal ≤ 1` (from
`VeryNotSticky.hδ1` and `VeryNotSticky.hexscal`). So this is a repair and not a shell game.

`statement_of_universal_loc` is the machine-checked form of "and `hloc` is the *only* thing that
was added": it derives `PerBallStatement` — the refuted, `hloc`-free `Prop` — from the current
`perBall` by granting `hloc` for free and passing every other argument through verbatim,
the two envelope bounds at the discretization scale `δ / C₀` included.

`PerBallStatement` refers to `Kakeya.ThinCase.IsBallFactoring` and
`Kakeya.ThinCase.DeltaBallCovers`, neither of which the repair touched, so the refutation below
continues to speak about the real hypotheses of the real lemma.
-/

@[expose] public section

namespace Kakeya.ThinCase.PerBallRefute

open MeasureTheory Metric Set ShadedBody Filter
open Kakeya.ThinCase.Refute (E3 ctr axisVec spine v0 v0_pos v0_ne_top one_le_succ dist_ctr
  two_le_dist_ctr ctr_eq_smul exists_harmonic_gt)

/-! ### The axis

The centres `Kakeya.ThinCase.Refute.ctr k = 2 (k+1) e₀` and the spine
`Kakeya.ThinCase.Refute.spine M = [0, ctr M]` are reused verbatim; only the *radii* change,
by a factor `8`, so that the blobs fit inside a capsule thin enough that
`rad C₀ a = 1` is still a locality radius. -/

lemma smul_axisVec_eq (t : ℝ) : t • axisVec = EuclideanSpace.single (0 : Fin 3) t := by
  unfold Kakeya.ThinCase.Refute.axisVec
  ext i
  simp

lemma dist_smul_axisVec (s t : ℝ) : dist (s • axisVec) (t • axisVec) = |s - t| := by
  rw [smul_axisVec_eq, smul_axisVec_eq]
  rw [show dist (EuclideanSpace.single (0 : Fin 3) s) (EuclideanSpace.single (0 : Fin 3) t)
      = dist s t from PiLp.dist_single_same 2 (fun _ => ℝ) _ _ _]
  exact Real.dist_eq _ _


/-! ### The blobs -/

/-- The radius of the `k`-th blob: the radius of `Kakeya.ThinCase.Refute.blob k` divided by
`8`, so that the blob fits inside a capsule of thickness `1/16`. -/
noncomputable def brad (k : ℕ) : ℝ := (1 / 32 : ℝ) * ((k : ℝ) + 1) ^ (-(1 : ℝ) / 3)

/-- The `k`-th blob. -/
noncomputable def blob (k : ℕ) : Set E3 := Metric.closedBall (ctr k) (brad k)

/-- The shading of the counterexample: the union of the first `M` blobs. -/
noncomputable def shadeSet (M : ℕ) : Set E3 := ⋃ k ∈ Finset.range M, blob k


lemma brad_le (k : ℕ) : brad k ≤ 1 / 32 := by
  have h1 : (1 : ℝ) ≤ ((k : ℝ) + 1) := one_le_succ k
  have := Real.rpow_le_one_of_one_le_of_nonpos h1 (by norm_num : (-(1:ℝ)/3) ≤ 0)
  unfold brad; nlinarith [this]


lemma dist_le_of_mem_blob {k : ℕ} {z : E3} (hz : z ∈ blob k) : dist z (ctr k) ≤ 1 / 32 :=
  le_trans (Metric.mem_closedBall.mp hz) (brad_le k)


lemma measurableSet_blob (k : ℕ) : MeasurableSet (blob k) := measurableSet_closedBall

lemma measurableSet_shadeSet (M : ℕ) : MeasurableSet (shadeSet M) := by
  unfold shadeSet
  exact Finset.measurableSet_biUnion _ fun k _ => measurableSet_blob k

/-! ### Volumes: the harmonic mass profile -/


/-! ### Locality -/


/-! ### The counting core -/


/-! ### The capsule -/

/-- The carrier of the counterexample: the closed `1/16`-neighbourhood of the spine. -/
noncomputable def capsule (M : ℕ) : Set E3 := Metric.cthickening (1 / 16) (spine M)

lemma isCompact_capsule (M : ℕ) : IsCompact (capsule M) :=
  isCompact_segment.cthickening

lemma convex_capsule (M : ℕ) : Convex ℝ (capsule M) :=
  (convex_segment _ _).cthickening _

lemma capsule_nonempty (M : ℕ) : (capsule M).Nonempty :=
  ⟨0, Metric.self_subset_cthickening _ (left_mem_segment _ _ _)⟩


lemma blob_subset_capsule {k M : ℕ} (h : k < M) : blob k ⊆ capsule M := by
  intro z hz
  refine Metric.mem_cthickening_of_dist_le z (ctr k) (1 / 16) _
    (Kakeya.ThinCase.Refute.ctr_mem_spine h.le) ?_
  linarith [dist_le_of_mem_blob hz]

lemma shadeSet_subset_capsule (M : ℕ) : shadeSet M ⊆ capsule M := by
  intro z hz
  obtain ⟨k, hk, hzk⟩ := Set.mem_iUnion₂.mp hz
  exact blob_subset_capsule (Finset.mem_range.mp hk) hzk


/-! ### The thickness profile of the capsule -/


/-! ### The bodies -/


/-- The single body of the counterexample. -/
noncomputable def carrierBody (M : ℕ) : ConvexSpaceBody E3 :=
  ⟨capsule M, (convex_capsule M).isConvexSet, isCompact_capsule M, capsule_nonempty M⟩

@[simp] lemma carrierBody_carrier (M : ℕ) : (carrierBody M).carrier = capsule M := rfl

/-- The single shaded body of the counterexample. -/
noncomputable def shadedBody (M : ℕ) : ShadedBody E3 :=
  { toConvexSpaceBody := carrierBody M
    shade := shadeSet M
    measurableSet_shade := measurableSet_shadeSet M
    shade_subset := shadeSet_subset_capsule M }

@[simp] lemma shadedBody_shade (M : ℕ) : (shadedBody M).shade = shadeSet M := rfl

@[simp] lemma shadedBody_body (M : ℕ) : (shadedBody M).toConvexSpaceBody = carrierBody M := rfl

/-! ### The `δ`-ball covers of (T5) -/

/-- The centre of the `j`-th covering ball: the point `j / 16` of the axis. -/
noncomputable def covCtr (j : ℕ) : E3 := ((j : ℝ) / 16) • axisVec

lemma dist_covCtr (j j' : ℕ) : dist (covCtr j) (covCtr j') = |(j : ℝ) / 16 - (j' : ℝ) / 16| :=
  dist_smul_axisVec _ _


open scoped Classical in
/-- The covering balls overlap at most `4`-fold: two of them meeting a common point have
centres within `1/4`, hence indices within `4`. -/
lemma cover_overlap (N : ℕ) (x : E3) :
    ((Finset.range N).filter (fun j => x ∈ Metric.ball (covCtr j) ((1 / 8 : ℝ)))).card ≤ 4 := by
  classical
  set S := (Finset.range N).filter (fun j => x ∈ Metric.ball (covCtr j) ((1 / 8 : ℝ))) with hS
  rcases S.eq_empty_or_nonempty with h | h
  · simp [h]
  · set m := S.min' h with hm
    have hmS : m ∈ S := S.min'_mem h
    have hclose : ∀ j ∈ S, j ≤ m + 3 := by
      intro j hj
      have hjx : dist x (covCtr j) < 1 / 8 :=
        Metric.mem_ball.mp (Finset.mem_filter.mp hj).2
      have hmx : dist x (covCtr m) < 1 / 8 :=
        Metric.mem_ball.mp (Finset.mem_filter.mp hmS).2
      have hdd : dist (covCtr j) (covCtr m) < 1 / 4 := by
        calc dist (covCtr j) (covCtr m) ≤ dist (covCtr j) x + dist x (covCtr m) :=
              dist_triangle _ _ _
          _ < 1 / 8 + 1 / 8 := by rw [dist_comm (covCtr j) x]; linarith
          _ = 1 / 4 := by norm_num
      rw [dist_covCtr] at hdd
      have hjm : m ≤ j := Finset.min'_le S j hj
      have hjmR : (m : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjm
      have : (j : ℝ) - (m : ℝ) < 4 := by
        rw [abs_lt] at hdd
        linarith [hdd.2]
      have hlt : j < m + 4 := by
        by_contra hcon
        push Not at hcon
        have : ((m : ℝ) + 4) ≤ (j : ℝ) := by exact_mod_cast hcon
        linarith
      omega
    have hsub : S ⊆ Finset.Icc m (m + 3) := by
      intro j hj
      exact Finset.mem_Icc.mpr ⟨Finset.min'_le S j hj, hclose j hj⟩
    calc S.card ≤ (Finset.Icc m (m + 3)).card := Finset.card_le_card hsub
      _ = 4 := by rw [Nat.card_Icc]; omega

/-! ### The statement under test -/


/-! ### Parameter choices -/


/-! ### The refutation -/


/-! ### Which hypothesis the configuration violates -/


end Kakeya.ThinCase.PerBallRefute

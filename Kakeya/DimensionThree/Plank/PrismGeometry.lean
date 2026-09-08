/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Factorization

/-!
# Geometry of flat `a × b × c` prisms

This file collects the elementary Euclidean geometry
of a `Kakeya.Prism3D`, together with the two comparisons between a prism and a `Kakeya.Tube` that
the Section 6 factorisation arguments consume.  Nothing here depends on any factorisation datum;
every declaration is a statement about one prism, one tube, or one flat disc.

## Contents

* **Coordinates.**  `Kakeya.Prism3D.abs_repr_le` / `Kakeya.Prism3D.mem_of_abs_repr_le` are the
  `-ᵥ`-free membership criterion, and `Kakeya.Prism3D.corner` is the vertex at which all three
  defining inequalities are tight.
* **The transverse (rank-`2`) width.**  `Kakeya.Prism3D.ethickness_two_le` bounds it by the
  smallest half-width `a`; with `Kakeya.Tube.rho_le_of_le_prism3D` this gives the scale relation
  `ρ ≤ a` for a `ρ`-tube inside an `a × b × c` prism.
* **The corner obstruction.**  `Kakeya.Prism3D.ne_convexHull_biUnion_tubes`: for `0 < ρ`, the
  convex hull of a nonempty finite union of `ρ`-tubes is never an exact prism.  (This is the
  public, `Finset.convexHull_biUnion`-shaped companion of the private
  `convexHull_tubes_ne_prism` in `Kakeya/DimensionThree/Plank/Factorization.lean`.)
* **The long plane and flat discs.**  `Kakeya.Prism3D.mem_add_smul_mem_longPlane`,
  `Kakeya.Prism3D.containsFlatDisc` (every prism contains a flat disc of radius its *middle*
  half-width `b`), and the longitudinal (rank-`1`) lower bounds
  `Kakeya.Prism3D.b_le_ethickness_one`, `Kakeya.ContainsFlatDisc.le_ethickness_one`.  These give
  `b ≤ ρ` for a prism (or any set with a flat `b`-disc) inside a `ρ`-tube:
  `Kakeya.Plank.b_le_of_le_tube`, `Kakeya.ContainsFlatDisc.le_of_subset_tube`.
* **Tube-shapedness.**  `Kakeya.IsTubeShaped r K` says `K` lies inside *some* tube of radius `r`.
  `Kakeya.Prism3D.isTubeShaped` proves it, with `r = a + b`, for any prism whose long half-width is
  at most `1/2` — i.e. for the paper's normalisation of an `a × b × 1` plank as an object of
  longitudinal *extent* `1`.  `Kakeya.Plank.half_le_of_le_tube` is the matching negative result for
  the Lean `Plank a b = Prism3D a b 1`, whose longitudinal extent is `2`.
* **Two counting lemmas** used by the Section 6 slab non-concentration step:
  `Kakeya.card_le_of_comparable_fibres` and `Kakeya.card_le_of_frostmanIn`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Convexity ConvexSpaceBody
open scoped NNReal Real ENNReal Classical

noncomputable section

namespace Kakeya


/-! ### Coordinates of a `Prism3D` -/


/-! ### The least width of a plank, and the scale relation `ρ ≤ a` -/

/-- The rank-`2` `ethickness` of a `Prism3D` is at most its smallest half-width `a`: the carrier
lies within `a` of its own tangent plane, which is a two-dimensional affine subspace. -/
theorem Prism3D.ethickness_two_le {a b c : ℝ≥0} {hab : a ≤ b} {hbc : b ≤ c}
    (P : Prism3D a b c hab hbc) : Metric.ethickness ℝ P.carrier 2 ≤ (a : ℝ≥0∞) := by
  apply Metric.ethickness_le_of_cthickening (r := a) (A := P.tangentPlane)
  · rw [AffineSubspace.direction_mk']
    rw [← Module.finrank_eq_rank, P.finrank_longPlane]
  · exact P.carrier_subset_cthickening_tangentPlane


/-! ### The corner obstruction: no hull of `ρ`-tubes is an exact prism -/


/-! ### The Scale comparison: a plank inside a coarse tube is thin -/


/-- **The separation estimate.**  A linear functional `⟪e, ·⟫` whose direction is orthogonal to an
affine subspace `A` is constant on `A`, so on the `r`-neighbourhood of `A` it varies by at most
`2r`.  This is what forbids a wide flat disc from fitting around a line. -/
theorem abs_inner_sub_le_two_mul_of_subset_cthickening
    {s : Set (EuclideanSpace ℝ (Fin 3))} {r : ℝ≥0}
    {A : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3))}
    (hs : s ⊆ Metric.cthickening (r : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3))))
    {e : EuclideanSpace ℝ (Fin 3)} (he : ‖e‖ = 1)
    (heA : ∀ z ∈ A.direction, inner ℝ e z = (0 : ℝ))
    {x y : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ s) (hy : y ∈ s) :
    |inner ℝ e (x - y)| ≤ 2 * (r : ℝ) := by
  classical
  have hAne : (A : Set (EuclideanSpace ℝ (Fin 3))).Nonempty := by
    by_contra hA
    have hAeq : (A : Set (EuclideanSpace ℝ (Fin 3))) = ∅ := Set.eq_empty_iff_forall_notMem.mpr
      (by intro z hz; exact hA ⟨z, hz⟩)
    simpa [hAeq, Metric.cthickening_empty] using (hs hx)
  have exists_close : ∀ {w : EuclideanSpace ℝ (Fin 3)}, w ∈ s → ∀ η : ℝ, 0 < η →
      ∃ z ∈ (A : Set (EuclideanSpace ℝ (Fin 3))), dist w z ≤ (r : ℝ) + η := by
    intro w hw η hη
    have hmem : w ∈ Metric.cthickening (r : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3))) :=
      hs hw
    have hinfE : Metric.infEDist w (A : Set (EuclideanSpace ℝ (Fin 3))) ≤
        ENNReal.ofReal (r : ℝ) := by
      simpa using hmem
    have hinfD : Metric.infDist w (A : Set (EuclideanSpace ℝ (Fin 3))) ≤ (r : ℝ) := by
      change ENNReal.toReal (Metric.infEDist w (A : Set (EuclideanSpace ℝ (Fin 3)))) ≤ (r : ℝ)
      have hne1 : Metric.infEDist w (A : Set (EuclideanSpace ℝ (Fin 3))) ≠ ⊤ :=
        ne_of_lt (lt_of_le_of_lt hinfE ENNReal.ofReal_lt_top)
      calc
        ENNReal.toReal (Metric.infEDist w (A : Set (EuclideanSpace ℝ (Fin 3)))) ≤
            ENNReal.toReal (ENNReal.ofReal (r : ℝ)) :=
          (ENNReal.toReal_le_toReal hne1 ENNReal.ofReal_ne_top).mpr hinfE
        _ = (r : ℝ) := ENNReal.toReal_ofReal (NNReal.coe_nonneg r)
    have hlt : Metric.infDist w (A : Set (EuclideanSpace ℝ (Fin 3))) < (r : ℝ) + η :=
      lt_of_le_of_lt hinfD (lt_add_of_pos_right (r : ℝ) hη)
    rcases (Metric.infDist_lt_iff hAne).mp hlt with ⟨z, hz, hzlt⟩
    exact ⟨z, hz, le_of_lt hzlt⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  have hε2 : 0 < ε / 2 := div_pos hε (by norm_num)
  rcases exists_close hx (ε / 2) hε2 with ⟨z₁, hz₁, hxz₁⟩
  rcases exists_close hy (ε / 2) hε2 with ⟨z₂, hz₂, hyz₂⟩
  have hdirmem : z₁ -ᵥ z₂ ∈ A.direction := by
    simpa using AffineSubspace.vsub_mem_direction (s := A) (p₁ := z₁) (p₂ := z₂) hz₁ hz₂
  have hzero : inner ℝ e (z₁ - z₂) = (0 : ℝ) := by
    simpa [vsub_eq_sub] using heA (z₁ -ᵥ z₂) hdirmem
  calc
    |inner ℝ e (x - y)| ≤ |inner ℝ e (x - z₁)| + |inner ℝ e (z₂ - y)| := by
      have hxy : x - y = (x - z₁) + (z₁ - z₂) + (z₂ - y) := by abel
      rw [hxy]
      rw [inner_add_right, inner_add_right, hzero]
      simpa [add_zero] using abs_add_le (inner ℝ e (x - z₁)) (inner ℝ e (z₂ - y))
    _ ≤ ‖x - z₁‖ + ‖z₂ - y‖ := by
      have hb1 : |inner ℝ e (x - z₁)| ≤ ‖x - z₁‖ := by
        simpa [he] using (abs_real_inner_le_norm e (x - z₁))
      have hb2 : |inner ℝ e (z₂ - y)| ≤ ‖z₂ - y‖ := by
        simpa [he] using (abs_real_inner_le_norm e (z₂ - y))
      exact add_le_add hb1 hb2
    _ ≤ (r : ℝ) + ε / 2 + ((r : ℝ) + ε / 2) := by
      have hn1 : ‖x - z₁‖ ≤ (r : ℝ) + ε / 2 := by
        calc
          ‖x - z₁‖ = dist x z₁ := by rw [dist_eq_norm]
          _ ≤ (r : ℝ) + ε / 2 := hxz₁
      have hn2 : ‖z₂ - y‖ ≤ (r : ℝ) + ε / 2 := by
        calc
          ‖z₂ - y‖ = dist z₂ y := by rw [dist_eq_norm]
          _ = dist y z₂ := by rw [dist_comm]
          _ ≤ (r : ℝ) + ε / 2 := hyz₂
      exact add_le_add hn1 hn2
    _ = 2 * (r : ℝ) + ε := by ring


/-! ### The *longitudinal* scale relation, and why it is decisive

`Kakeya.Plank.b_le_of_le_tube` compares the transverse extents of a plank and a coarse tube.  The
longitudinal extents must also be compared, and doing so is much more restrictive.

In this development a `Plank a b` is `Prism3D a b 1`, whose `thicknesses` are *half*-widths
(`Kakeya.Prism3D.volume_carrier` is `8 * a * b * c`).  So a plank has longitudinal **extent 2**: it
contains the two points `centre ± e` for a unit `e` on its long axis, at distance `2`
(`Kakeya.Prism3D.mem_add_mem_longAxis`, `mem_sub_mem_longAxis`).

A `Tube ρ`, by contrast, is the `ρ`-neighbourhood of a *unit* segment, so it sits in a ball of
radius `1/2 + ρ` about its midpoint (`Kakeya.Tube.carrier_subset_closedBall_midpoint`) and therefore
has diameter at most `1 + 2ρ`.

Consequently a plank inside a `ρ`-tube forces `2 ≤ 1 + 2ρ`, i.e. `1/2 ≤ ρ`.  The two normalisations
disagree by a factor of two in the long direction, and the consequence is not cosmetic: the
`PlankFactorization` hypothesis of Proposition 6.6(A) is only satisfiable for `ρ ∈ [1/2, 1]`. -/

/-! ### The comparable-plank normalisation, and the local cover it unlocks

The covering datum above is still an *assumed* counting statement.  This section reduces it to a
single *containment*, which is both weaker and manifestly true in the paper's normalisation, and
proves the counting.

**The normalisation defect.**  `Plank a b` is `Prism3D a b 1`, and `Prism3D` records half-widths, so
a Lean plank has longitudinal *extent* `2`.  A `Tube r` is the `r`-neighbourhood of a segment of
length exactly `1` (`Tube.dist_eq_one`), hence has diameter at most `1 + 2r`.  A plank inside
a tube therefore forces `2 ≤ 1 + 2r`, i.e. `1/2 ≤ r` (`Kakeya.Plank.half_le_of_le_tube`).  This is a
fixed-constant mismatch between two normalisations, not a statement about the mathematics: the paper
asks only for dimensions *comparable* to `a × b × 1`, and its `θb × b × 1` plank does sit inside a
tube of radius comparable to `b`.  Because the deficiency is longitudinal and `Tube`'s core length
is pinned to `1`, no dilation of the covering radius repairs it, and neither does a position or a
direction net: a leaf has core length `1` and so does a covering tube, so covering a container of
extent `2` leafwise needs `⌈1/ρ⌉` tubes, not `O(1)`.

**The minimal comparable-plank interface.**  What the argument consumes is exactly
`IsTubeShaped r K` — the container lies in *some* tube of radius `r` — with `r` comparable to `b`.
`Kakeya.Prism3D.isTubeShaped` proves that this holds, with `r = a + b ≤ 2 * b`, for any prism whose
long half-width is at most `1/2`, i.e. for the paper's normalisation.  Nothing about
`PlankFactorization`, `Prism3D` or `Tube` is changed; the datum is simply requested where the paper
supplies it.

**What it buys.**  With a tube-shaped container the cover is a *singleton* and no `δ` enters at all:
a body inside `K` is inside `V₀`, hence inside `V₀.rescale ρ` as soon as `r ≤ ρ`.  So
`Ccover = 1`, the covering radius is exactly `ρ`, and the statement is available for arbitrarily
small `ρ` — the local theorem that `Kakeya.exists_leafwise_tube_cover` (which discretises all of
`B₁` and therefore needs `1/2 ≤ ρ`) is not. -/


/-- In `ℝ³` a two-dimensional subspace meets the orthogonal complement of any at most
one-dimensional subspace in a unit vector.  The submodule-level generalisation of
`Kakeya.Prism3D.exists_unit_longPlane_orthogonal`, whose proof used the prism only through
`finrank longPlane = 2`. -/
theorem exists_unit_mem_orthogonal_of_finrank_two
    (P : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) (hP : Module.finrank ℝ P = 2)
    (D : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) (hD : Module.finrank ℝ D ≤ 1) :
    ∃ e : EuclideanSpace ℝ (Fin 3), e ∈ P ∧ ‖e‖ = 1 ∧
      ∀ z ∈ D, inner ℝ e z = (0 : ℝ) := by
  have hDperp_ge : 2 ≤ Module.finrank ℝ Dᗮ := by
    have h_eq : Module.finrank ℝ D + Module.finrank ℝ Dᗮ =
        Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) :=
      Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 3)) D
    rw [finrank_euclideanSpace_fin] at h_eq
    omega
  have hinf_pos : 1 ≤ Module.finrank ℝ ((P ⊓ Dᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))) := by
    have h_sup_le : Module.finrank ℝ
        ((P ⊔ Dᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))) ≤
        Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) :=
      (P ⊔ Dᗮ).finrank_le
    have h_eq : Module.finrank ℝ ((P ⊔ Dᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))) +
          Module.finrank ℝ ((P ⊓ Dᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))) =
        Module.finrank ℝ P + Module.finrank ℝ Dᗮ :=
      Submodule.finrank_sup_add_finrank_inf_eq P Dᗮ
    rw [hP] at h_eq
    rw [finrank_euclideanSpace_fin] at h_sup_le
    omega
  have h_nonbot : (P ⊓ Dᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) ≠ ⊥ := by
    intro h_bot
    rw [h_bot] at hinf_pos
    simp at hinf_pos
  obtain ⟨w, hw_mem, hw_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h_nonbot
  have hw_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw_ne
  refine ⟨(‖w‖⁻¹ : ℝ) • w, ?_, ?_, ?_⟩
  · exact P.smul_mem (‖w‖⁻¹ : ℝ) (Submodule.mem_inf.mp hw_mem).1
  · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (ne_of_gt hw_pos)]
  · have hw_orth : w ∈ Dᗮ := (Submodule.mem_inf.mp hw_mem).2
    have he_orth : (‖w‖⁻¹ : ℝ) • w ∈ Dᗮ :=
      Submodule.smul_mem (Dᗮ) (‖w‖⁻¹ : ℝ) hw_orth
    intro z hz
    rw [real_inner_comm]
    exact (Submodule.mem_orthogonal D ((‖w‖⁻¹ : ℝ) • w)).mp he_orth z hz


/-- A flat disc of radius `b` cannot be squeezed into the `r`-neighbourhood of a line unless
`b ≤ r`: pick a unit `e` in the disc's plane orthogonal to the line's direction and test the two
points `c ± b • e`, on which `⟪e, ·⟫` — constant along the line — differs by `2b`.  The
normalisation-free form of `Kakeya.Prism3D.b_le_ethickness_one`. -/
theorem ContainsFlatDisc.le_ethickness_one {b : ℝ≥0}
    {S : Set (EuclideanSpace ℝ (Fin 3))} (h : ContainsFlatDisc b S) :
    (b : ℝ≥0∞) ≤ Metric.ethickness ℝ S 1 := by
  rw [Metric.le_ethickness_iff]
  intro r A hA hsub
  have hAfin : Module.finrank ℝ A.direction ≤ 1 := Module.finrank_le_of_rank_le hA
  rcases h with ⟨c, P, hP2, hmem⟩
  obtain ⟨e, heP, he1, heOrth⟩ :=
    exists_unit_mem_orthogonal_of_finrank_two P hP2 A.direction hAfin
  have hnx : ‖(b : ℝ) • e‖ = (b : ℝ) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg b.coe_nonneg, he1]
    simp
  have hx : c + (b : ℝ) • e ∈ S := by
    exact hmem ((b : ℝ) • e) (Submodule.smul_mem P (b : ℝ) heP)
      (le_of_eq hnx)
  have hny : ‖(-(b : ℝ)) • e‖ = (b : ℝ) := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg b.coe_nonneg, he1]
    simp
  have hy : c + (-(b : ℝ)) • e ∈ S := by
    exact hmem (-(b : ℝ) • e) (Submodule.smul_mem P (-(b : ℝ)) heP)
      (le_of_eq hny)
  have hkey : |inner ℝ e ((c + (b : ℝ) • e) - (c + (-(b : ℝ)) • e))| ≤
      2 * (r : ℝ) :=
    abs_inner_sub_le_two_mul_of_subset_cthickening hsub he1 heOrth hx hy
  have htwo : 2 * (b : ℝ) ≤ 2 * (r : ℝ) := by
    have hinner : inner ℝ e ((c + (b : ℝ) • e) - (c + (-(b : ℝ)) • e)) =
        2 * (b : ℝ) := by
      have hdiff : (c + (b : ℝ) • e) - (c + (-(b : ℝ)) • e) =
          (2 : ℝ) • ((b : ℝ) • e) := by
        rw [neg_smul, two_smul]
        abel
      rw [hdiff, inner_smul_right, inner_smul_right,
        real_inner_self_eq_norm_sq, he1]
      ring
    calc
      2 * (b : ℝ) = |inner ℝ e ((c + (b : ℝ) • e) - (c + (-(b : ℝ)) • e))| := by
        rw [hinner, abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) b.coe_nonneg)]
      _ ≤ 2 * (r : ℝ) := hkey
  have hbr : (b : ℝ) ≤ (r : ℝ) := by
    nlinarith [htwo]
  have hbl : b ≤ r := by
    exact_mod_cast hbr
  exact ENNReal.coe_le_coe.mpr hbl


/-! ### Inner slab non-concentration: the Part-(B) concentration step

The concentration parameter of Proposition 6.6(B) is *not* the part-(A) one.  The outer plank family
is Katz--Tao, so GWZ Lemma 6.1 is applied to it with `γ = 0`, where the slab hypothesis is vacuous
(`Kakeya.gammaZeroSlabBound`): no concentration bound, and in particular no cross-parent overlap
loss, is needed for the outer family.  The concentration that *is* needed is for the inner,
rescaled family, with `γ = 1` and a sub-polynomial constant.  The counting core of that bound is the
following.
-/

/-- **Inner slab non-concentration, counting core**.

Let `proj : q → r` assign to each fine index a coarse index, with all fibres of comparable size
`m` up to a factor `Cfib`, and let `qS ⊆ q` be a set of fine indices whose coarse indices all lie in
a selected set `sel` of coarse indices.  Then

`|qS| ≤ Cfib ^ 2 * (|sel| / |r|) * |q|`,

in the multiplicative form below.  Each selected coarse index carries at most `Cfib * m` fine
indices, while `|q| ≥ Cfib⁻¹ * m * |r|`; the common fibre size `m` then cancels, so no positivity
hypothesis on it is needed.

In the application `sel = {k | R k ≤ K_S}` is bounded by `C_F * θ * |r|` by the Frostman property of
the coarse fibre, which turns the conclusion into `|qS| ≤ C_F * Cfib ^ 2 * θ * |q|`: slab
non-concentration with exponent `γ = 1` and the sub-polynomial constant `C_F * Cfib ^ 2`. -/
theorem card_le_of_comparable_fibres {ιq ιr : Type*} [DecidableEq ιq] [DecidableEq ιr]
    {q : Finset ιq} {r : Finset ιr} {proj : ιq → ιr} {m Cfib : ℝ≥0}
    (hCfib : 1 ≤ Cfib)
    (hproj : ∀ i ∈ q, proj i ∈ r)
    (hlb : ∀ k ∈ r, Cfib⁻¹ * m ≤ (({i ∈ q | proj i = k}).card : ℝ≥0))
    (hub : ∀ k ∈ r, (({i ∈ q | proj i = k}).card : ℝ≥0) ≤ Cfib * m)
    {sel : Finset ιr} (hsel : sel ⊆ r)
    {qS : Finset ιq} (hqS : qS ⊆ q) (hmem : ∀ i ∈ qS, proj i ∈ sel) :
    ((qS.card : ℝ≥0)) * (r.card : ℝ≥0) ≤ Cfib ^ 2 * (sel.card : ℝ≥0) * (q.card : ℝ≥0) := by
  let fib : ιr → ℝ≥0 := fun k => ((q.filter fun i => proj i = k).card : ℝ≥0)
  -- upper bound on qS over sel
  have hUB : (qS.card : ℝ≥0) ≤ (sel.card : ℝ≥0) * Cfib * m := by
    have hsub : qS ⊆ q.filter (fun i => proj i ∈ sel) := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨hqS hi, hmem i hi⟩
    have hcard_sub : (qS.card : ℝ≥0) ≤ ((q.filter (fun i => proj i ∈ sel)).card : ℝ≥0) := by
      exact Nat.cast_le.2 (Finset.card_le_card hsub)
    have hfib_sum : ((q.filter (fun i => proj i ∈ sel)).card : ℝ≥0) = Finset.sum sel fib := by
      have hnat : (q.filter (fun i => proj i ∈ sel)).card =
          (∑ k ∈ sel, (q.filter (fun i => proj i = k)).card) :=
        (Finset.sum_card_fiberwise_eq_card_filter (s := q) (t := sel) (g := proj)).symm
      rw [hnat]
      push_cast
      rfl
    have hqS_le_sum : (qS.card : ℝ≥0) ≤ Finset.sum sel fib := hcard_sub.trans hfib_sum.le
    have hterm : ∀ k ∈ sel, fib k ≤ Cfib * m := by
      intro k hk
      exact hub k (hsel hk)
    calc
      (qS.card : ℝ≥0) ≤ Finset.sum sel fib := hqS_le_sum
      _ ≤ Finset.sum sel (fun _k => Cfib * m) := Finset.sum_le_sum (fun k hk => hterm k hk)
      _ = (sel.card : ℝ≥0) * Cfib * m := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
  -- lower bound for q
  have hLB : Cfib⁻¹ * m * (r.card : ℝ≥0) ≤ (q.card : ℝ≥0) := by
    have hQeq : q.filter (fun i => proj i ∈ r) = q := by
      ext i
      rw [Finset.mem_filter]
      constructor
      · rintro ⟨hi, _⟩
        exact hi
      · intro hi
        exact ⟨hi, hproj i hi⟩
    have hfib_sum_r : Finset.sum r fib = ((q.filter (fun i => proj i ∈ r)).card : ℝ≥0) := by
      have hnat : (q.filter (fun i => proj i ∈ r)).card =
          (∑ k ∈ r, (q.filter (fun i => proj i = k)).card) :=
        (Finset.sum_card_fiberwise_eq_card_filter (s := q) (t := r) (g := proj)).symm
      rw [hnat]
      push_cast
      rfl
    calc
      Cfib⁻¹ * m * (r.card : ℝ≥0) = (r.card : ℝ≥0) * (Cfib⁻¹ * m) := by ring
      _ ≤ Finset.sum r fib := by
        calc
          (r.card : ℝ≥0) * (Cfib⁻¹ * m) = Finset.sum r (fun _ : ιr => Cfib⁻¹ * m) := by
            rw [← nsmul_eq_mul, ← Finset.sum_const]
          _ ≤ Finset.sum r fib := Finset.sum_le_sum (fun k hk => hlb k hk)
      _ = (q.card : ℝ≥0) := by
        rw [hfib_sum_r, hQeq]
  -- combine
  have hCf0 : Cfib ≠ 0 := by
    exact (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 1) hCfib).ne'
  calc
    (qS.card : ℝ≥0) * (r.card : ℝ≥0)
        ≤ ((sel.card : ℝ≥0) * Cfib * m) * (r.card : ℝ≥0) := by
            exact mul_le_mul_of_nonneg_right hUB zero_le
    _ = Cfib ^ 2 * (sel.card : ℝ≥0) * (Cfib⁻¹ * m * (r.card : ℝ≥0)) := by
      field_simp [hCf0]
    _ ≤ Cfib ^ 2 * (sel.card : ℝ≥0) * (q.card : ℝ≥0) := by
      gcongr

/-- **Inner slab non-concentration, `γ = 1` form.**  Once the selected coarse set is known to be a
`Cθ`-fraction of the coarse family — in the application `Cθ = C_F * θ`, by the Frostman property of
the coarse fibre (`Kakeya.card_le_of_frostmanIn`) — the counting core
`Kakeya.card_le_of_comparable_fibres` gives exactly the slab non-concentration hypothesis of GWZ
Lemma 6.1 with exponent `γ = 1` and constant `Cfib ^ 2 * Cθ`. -/
theorem card_le_of_comparable_fibres_of_selected_le {ιq ιr : Type*} [DecidableEq ιq]
    [DecidableEq ιr] {q : Finset ιq} {r : Finset ιr} {proj : ιq → ιr} {m Cfib Cθ : ℝ≥0}
    (hCfib : 1 ≤ Cfib) (hr : r.Nonempty)
    (hproj : ∀ i ∈ q, proj i ∈ r)
    (hlb : ∀ k ∈ r, Cfib⁻¹ * m ≤ (({i ∈ q | proj i = k}).card : ℝ≥0))
    (hub : ∀ k ∈ r, (({i ∈ q | proj i = k}).card : ℝ≥0) ≤ Cfib * m)
    {sel : Finset ιr} (hsel : sel ⊆ r) (hselcard : (sel.card : ℝ≥0) ≤ Cθ * (r.card : ℝ≥0))
    {qS : Finset ιq} (hqS : qS ⊆ q) (hmem : ∀ i ∈ qS, proj i ∈ sel) :
    (qS.card : ℝ≥0) ≤ Cfib ^ 2 * Cθ * (q.card : ℝ≥0) := by
  have hmain : (qS.card : ℝ≥0) * (r.card : ℝ≥0)
      ≤ Cfib ^ 2 * (sel.card : ℝ≥0) * (q.card : ℝ≥0) := by
    exact card_le_of_comparable_fibres hCfib hproj hlb hub hsel hqS hmem
  have hrpos : 0 < (r.card : ℝ≥0) := by
    exact_mod_cast (Finset.card_pos.mpr hr)
  have hle : (qS.card : ℝ≥0) * (r.card : ℝ≥0)
      ≤ Cfib ^ 2 * Cθ * (q.card : ℝ≥0) * (r.card : ℝ≥0) := by
    calc
      (qS.card : ℝ≥0) * (r.card : ℝ≥0)
          ≤ Cfib ^ 2 * (sel.card : ℝ≥0) * (q.card : ℝ≥0) := hmain
      _ ≤ Cfib ^ 2 * Cθ * (q.card : ℝ≥0) * (r.card : ℝ≥0) := by
        have hnn : 0 ≤ Cfib ^ 2 * (q.card : ℝ≥0) := by positivity
        calc
          Cfib ^ 2 * (sel.card : ℝ≥0) * (q.card : ℝ≥0)
              = (Cfib ^ 2 * (q.card : ℝ≥0)) * (sel.card : ℝ≥0) := by ring
          _ ≤ (Cfib ^ 2 * (q.card : ℝ≥0)) * (Cθ * (r.card : ℝ≥0)) := by
            exact mul_le_mul_of_nonneg_left hselcard hnn
          _ = Cfib ^ 2 * Cθ * (q.card : ℝ≥0) * (r.card : ℝ≥0) := by ring
  exact le_of_mul_le_mul_right hle hrpos

/-- **The Frostman coarse count** (the first step of blueprint
`lem:factorInnerSlabNonconcentration`).

If the coarse family `(Rb k)_{k ∈ r}` is `C_F`-Frostman in `W`, all its members lie in `W`, their
volumes lie in `[vmin, vmax]` with `vmin ≠ 0`, and `K ≤ W`, then the number of coarse bodies
contained in `K` is controlled by the volume ratio `|K| / |W|`:

`|{k ∈ r | Rb k ≤ K}| * vmin ≤ C_F * (|r| * vmax) * (|K| / |W|)`.

Counting: the selected bodies each have volume at least `vmin`, their total volume is
`densityIn r Rb K * |K|`, the Frostman property bounds that density by `C_F * densityIn r Rb W`, and
the latter is `(∑_{k ∈ r} |Rb k|) / |W| ≤ |r| * vmax / |W|`.

Together with `Kakeya.card_le_of_comparable_fibres_of_selected_le` and the coarse-container volume
bound `|K_S| ≲ θ |W|` this is the `γ = 1` slab non-concentration input of GWZ Lemma 6.1 used by
Proposition 6.6(B); what is still missing is the *geometric* construction of the coarse container
`K_S` (blueprint Equation `eq:factor-coarse-container-compatibility`), which fine-tube containment
alone does not give. -/
theorem card_le_of_frostmanIn {ιr : Type*} [DecidableEq ιr] {r : Finset ιr}
    {Rb : ιr → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {W K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))} {CF : ℝ≥0∞}
    (hFrost : IsFrostmanIn r Rb W CF) (hRW : ∀ k ∈ r, Rb k ≤ W) (hKW : K ≤ W)
    {vmin vmax : ℝ≥0∞} (_hvmin : vmin ≠ 0)
    (hmin : ∀ k ∈ r, vmin ≤ volume (Rb k).carrier)
    (hmax : ∀ k ∈ r, volume (Rb k).carrier ≤ vmax)
    (_hW0 : volume W.carrier ≠ 0) (_hWtop : volume W.carrier ≠ ⊤) :
    (({k ∈ r | Rb k ≤ K}).card : ℝ≥0∞) * vmin
      ≤ CF * ((r.card : ℝ≥0∞) * vmax) * (volume K.carrier / volume W.carrier) := by
  let sel : Finset ιr := {k ∈ r | Rb k ≤ K}
  -- `densityIn r Rb W = (∑_{k ∈ r} |Rb k|) / |W| ≤ |r| * vmax / |W|`.
  have hdenW :
      densityIn r Rb W ≤ ((r.card : ℝ≥0∞) * vmax) / volume W.carrier := by
    rw [densityIn_of_all_le hRW]
    exact ENNReal.div_le_div_right
      (by simpa [nsmul_eq_mul] using
        Finset.sum_le_card_nsmul r (fun k => volume (Rb k).carrier) vmax hmax) _
  -- counting: each selected body has volume at least `vmin`.
  have hcount : (sel.card : ℝ≥0∞) * vmin ≤ ∑ k ∈ sel, volume (Rb k).carrier := by
    simpa [nsmul_eq_mul] using
      Finset.card_nsmul_le_sum sel (fun k => volume (Rb k).carrier) vmin
        (fun k hk => hmin k (Finset.mem_filter.mp hk).1)
  calc
    (sel.card : ℝ≥0∞) * vmin ≤ ∑ k ∈ sel, volume (Rb k).carrier := hcount
    _ = densityIn r Rb K * volume K.carrier := sum_volume_eq_densityIn_mul_volume r Rb K
    _ ≤ (CF * densityIn r Rb W) * volume K.carrier := by
      gcongr
      exact hFrost K hKW
    _ ≤ (CF * (((r.card : ℝ≥0∞) * vmax) / volume W.carrier)) * volume K.carrier := by
      gcongr
    _ = CF * ((r.card : ℝ≥0∞) * vmax) * (volume K.carrier / volume W.carrier) := by
      rw [mul_assoc, ENNReal.mul_comm_div, ← mul_assoc]

end Kakeya

end

end

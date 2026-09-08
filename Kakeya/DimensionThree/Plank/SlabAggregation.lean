/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.AssignedSlabFamily
public import Kakeya.DimensionThree.Plank.RelativeMultiplicity

/-!
# Aggregating slab-local union retention into global union retention

Phase E of GWZ Lemma 6.13 has to turn slab-local retention estimates into one global estimate
`ρ · |U| ≤ Nov · |U ∩ G|`, which is what `Plank.isCRefinement_restrictShade_of_dense` consumes.

The bridge is the pointwise slab-overlap bound `Nov` returned by
`Kakeya.plankReduction_preassembly`, and it is worth being precise about *which* overlap it bounds,
because there are two candidate readings and only one of them is both true and available.

`Nov` bounds, at each point `x`, the number of used slabs `S` such that `x` lies in the shading
union of the **geometric** family `Plank.inSlabFamilyC` of `S`.  It does *not* bound the number of
slabs having a selected *box* containing `x` — a point of a box of `S` need not be shaded by any
plank of `S` at all.  So the aggregation must be organised so that the sets being summed are
subsets of the slab shading unions, never of the slab boxes.

That is exactly what the assigned families give.  Each `i ∈ s'` is assigned to a single slab, so the
slab-local unions `U_S = ⋃_{i ∈ 𝒜_S} Y'_i` cover `U`, and
`Plank.assignedSlabFamily_subset_inSlabFamilyC` shows `𝒜_S ⊆ inSlabFamilyC … S`, hence
`U_S` is contained in the set `Nov` counts.  Any retained subset `A_S ⊆ U_S` therefore inherits the
pointwise overlap bound, and
`MeasureTheory.sum_measure_le_mul_measure_biUnion_of_card_filter_le` converts the sum of the
`|A_S|` into `Nov · |⋃_S A_S|`.

No disjointness of the slab unions is claimed or needed — they genuinely overlap, which is why the
factor `Nov` appears and why the *indices* rather than the *shadings* are what partition.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Convexity
open scoped NNReal Real ENNReal

noncomputable section

namespace Plank

variable {ι : Type*}


/-- **Sum-form capture upgrades to union-form capture, under constant multiplicity.**

Suppose the shadings lose at most an `f`-fraction of their *total mass* outside a measurable
set `W`, and the family has constant multiplicity `C`.  If `2 · f · C ≤ 1` then `W` captures at
least half of the shading *union*:

`|U| ≤ 2 · |U ∩ W|`.

This is the converse direction to `Plank.isCRefinement_restrictShade_of_dense`, and it is the bridge
the good-box selection needs: that selection controls its discarded mass in the sum norm, while the
dense-ball layer and the retention estimate live in the union norm.

The configuration-dependent factor `m = min_U µ` cancels between the two halves, exactly as in
`Plank.isCRefinement_restrictShade_of_dense`, which is why only the product `f · C` appears and no
uniform multiplicity upper bound is required.  Note the direction of the hypothesis on `f`: a
*smaller* discard fraction is needed when `C` is larger, so a caller with `C = Cmult · a ^ (-εint)`
must run its selection at discard fraction `~a ^ εint`, paying that from the epsilon budget. -/
theorem union_capture_of_sum_capture (s' : Finset ι)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (W : Set (EuclideanSpace ℝ (Fin 3))) (hW : MeasurableSet W)
    (C f : ℝ≥0)
    (hC : ShadedBody.HasCConstantMultiplicity s' Y' C)
    (hdiscard : ∑ i ∈ s', volume ((Y' i).shade \ W)
      ≤ (f : ℝ≥0∞) * ∑ i ∈ s', volume (Y' i).shade)
    (hfC : 2 * (f * C) ≤ 1)
    (hUtop : volume (⋃ i ∈ s', (Y' i).shade) ≠ ⊤) :
    volume (⋃ i ∈ s', (Y' i).shade)
      ≤ 2 * volume ((⋃ i ∈ s', (Y' i).shade) ∩ W) := by
  classical
  set U : Set (EuclideanSpace ℝ (Fin 3)) := ⋃ i ∈ s', (Y' i).shade with hUdef
  by_cases hne : U.Nonempty
  · -- `U` is nonempty: pick a point `y` of minimal pointwise multiplicity.
    obtain ⟨y, hyU, hmin⟩ := exists_min_pointwiseMultiplicity s' Y' (by simpa [hUdef] using hne)
    let m : ℝ≥0∞ := (ShadedBody.pointwiseMultiplicity s' Y' y : ℝ≥0∞)
    have hy_mem : ∃ i ∈ s', y ∈ (Y' i).shade := by
      rcases Set.mem_iUnion₂.mp hyU with ⟨i, hi, hysh⟩
      exact ⟨i, hi, hysh⟩
    have hm_ne_zero : m ≠ 0 := by
      dsimp [m]
      exact_mod_cast (ne_of_gt ((ShadedBody.pointwiseMultiplicity_pos_iff s' Y' y).mpr hy_mem))
    have hm_top : m ≠ ⊤ := by
      simp [m]
    -- h1: the discarded mass is at least `m` times the discarded union.
    have h1 : m * volume (U \ W) ≤ ∑ i ∈ s', volume ((Y' i).shade \ W) := by
      have h := mul_volume_inter_le_sum_volume_shade_inter s' Y' hmin Wᶜ
      simpa [hUdef, Set.sdiff_eq] using h
    -- h2: the total shading mass is at most `C * m * volume U`.
    have h2 : ∑ i ∈ s', volume (Y' i).shade ≤ (C : ℝ≥0∞) * m * volume U := by
      simpa [hUdef, m] using (sum_volume_shade_le_of_hasCConstantMultiplicity s' Y' hC hyU)
    -- Combine h1, hdiscard, h2 into an `m`-prefactored inequality.
    have hsum_le : m * volume (U \ W) ≤ (f : ℝ≥0∞) * ((C : ℝ≥0∞) * m * volume U) := by
      calc
        m * volume (U \ W) ≤ ∑ i ∈ s', volume ((Y' i).shade \ W) := h1
        _ ≤ (f : ℝ≥0∞) * ∑ i ∈ s', volume (Y' i).shade := hdiscard
        _ ≤ (f : ℝ≥0∞) * ((C : ℝ≥0∞) * m * volume U) := by
          exact mul_le_mul_right h2 (f : ℝ≥0∞)
    have hprod : (f : ℝ≥0∞) * ((C : ℝ≥0∞) * m * volume U) =
        m * (((f * C : ℝ≥0) : ℝ≥0∞) * volume U) := by
      simp [ENNReal.coe_mul, mul_assoc, mul_comm, mul_left_comm]
    have hmul_le : m * volume (U \ W) ≤ m * (((f * C : ℝ≥0) : ℝ≥0∞) * volume U) := by
      rw [← hprod]
      exact hsum_le
    have hdiff : volume (U \ W) ≤ ((f * C : ℝ≥0) : ℝ≥0∞) * volume U := by
      exact (ENNReal.mul_le_mul_iff_right hm_ne_zero hm_top).mp hmul_le
    -- Scale by 2 and use `2 * (f * C) ≤ 1`.
    have h2diff : 2 * volume (U \ W) ≤ volume U := by
      calc
        2 * volume (U \ W) ≤ 2 * (((f * C : ℝ≥0) : ℝ≥0∞) * volume U) := by
          exact mul_le_mul_right hdiff (2 : ℝ≥0∞)
        _ = ((2 * (f * C) : ℝ≥0) : ℝ≥0∞) * volume U := by
          norm_num [ENNReal.coe_mul, mul_assoc]
        _ ≤ (1 : ℝ≥0∞) * volume U := by
          exact mul_le_mul_left (ENNReal.coe_le_coe.mpr hfC) (volume U)
        _ = volume U := by
          rw [one_mul]
    -- `U = (U ∩ W) ∪ (U \ W)` gives `2 * |U| ≤ 2 * |U ∩ W| + |U|`; cancel one `|U|`.
    have hUeq : volume U = volume (U ∩ W) + volume (U \ W) :=
      (measure_inter_add_sdiff U hW).symm
    have hmain : 2 * volume U ≤ 2 * volume (U ∩ W) + volume U := by
      calc
        2 * volume U = 2 * (volume (U ∩ W) + volume (U \ W)) := by
          rw [hUeq]
        _ = 2 * volume (U ∩ W) + 2 * volume (U \ W) := by
          rw [mul_add]
        _ ≤ 2 * volume (U ∩ W) + volume U := by
          exact add_le_add le_rfl h2diff
    have hUtop' : volume U ≠ ⊤ := by simpa [← hUdef] using hUtop
    have hgoal : volume U ≤ 2 * volume (U ∩ W) := by
      have h2' : volume U + volume U ≤ 2 * volume (U ∩ W) + volume U := by
        simpa [two_mul] using hmain
      exact (ENNReal.add_le_add_iff_right hUtop').mp h2'
    exact hgoal
  · -- `U` is empty: both sides are zero.
    have hUempty : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp [hUempty]

/-- The discard fraction `(2 C_mult)⁻¹ a^{ε}` is exactly the reciprocal of twice the multiplicity
`C_mult a^{-ε}`: the two `rpow` factors cancel, needing only `a ≠ 0`, and no bound `a ≤ 1`. -/
theorem two_mul_discardRate_mul_multiplicity_eq_one {a Cmult : ℝ≥0} (εint : ℝ)
    (hCmult : 0 < Cmult) (ha : 0 < a) :
    2 * (((2 * Cmult)⁻¹ * a ^ εint) * (Cmult * a ^ (-εint))) = 1 := by
  have hrpow : a ^ εint * a ^ (-εint) = 1 := by
    rw [← NNReal.rpow_add ha.ne']
    simp
  have h2C : (2 * Cmult : ℝ≥0) ≠ 0 := mul_ne_zero two_ne_zero hCmult.ne'
  calc
    2 * (((2 * Cmult)⁻¹ * a ^ εint) * (Cmult * a ^ (-εint)))
      = ((2 * Cmult)⁻¹ * (2 * Cmult)) * (a ^ εint * a ^ (-εint)) := by ring
    _ = 1 := by
      rw [inv_mul_cancel₀ h2C, hrpow, mul_one]


/-- **Union-form capture at the `a^{-ε}` multiplicity rate.**  `Plank.union_capture_of_sum_capture`
specialised to the shape the plank layer actually produces: constant multiplicity
`C = C_mult a^{-ε_int}`, and a selection run at the matching discard fraction
`f = (2 C_mult)⁻¹ a^{ε_int}`, for which `2 · f · C = 1` holds exactly.

This is the packaged form of the trade-off noted on `Plank.union_capture_of_sum_capture`: a larger
multiplicity forces a smaller discard fraction, and the price is a power `a^{ε_int}` taken from the
epsilon budget.  Only `0 < C_mult` and `0 < a` are needed — in particular no `a ≤ 1`, since the
cancellation `a^{ε} · a^{-ε} = 1` is exact for every nonzero `a`. -/
theorem union_capture_of_sum_capture_rate {a : ℝ≥0} (s' : Finset ι)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (W : Set (EuclideanSpace ℝ (Fin 3))) (hW : MeasurableSet W)
    (Cmult : ℝ≥0) (εint : ℝ) (hCmult : 0 < Cmult) (ha : 0 < a)
    (hC : ShadedBody.HasCConstantMultiplicity s' Y' (Cmult * a ^ (-εint)))
    (hdiscard : ∑ i ∈ s', volume ((Y' i).shade \ W)
      ≤ (((2 * Cmult)⁻¹ * a ^ εint : ℝ≥0) : ℝ≥0∞) * ∑ i ∈ s', volume (Y' i).shade)
    (hUtop : volume (⋃ i ∈ s', (Y' i).shade) ≠ ⊤) :
    volume (⋃ i ∈ s', (Y' i).shade)
      ≤ 2 * volume ((⋃ i ∈ s', (Y' i).shade) ∩ W) := by
  have hfC : 2 * (((2 * Cmult)⁻¹ * a ^ εint) * (Cmult * a ^ (-εint))) ≤ 1 :=
    (two_mul_discardRate_mul_multiplicity_eq_one εint hCmult ha).le
  exact union_capture_of_sum_capture s' Y' W hW (Cmult * a ^ (-εint)) ((2 * Cmult)⁻¹ * a ^ εint)
    hC hdiscard hfC hUtop


/-- The refinement coefficient of a capture at rate `K⁻¹` against multiplicity `C_mult a^{-ε}` is
`(K C_mult)⁻¹ a^{ε}`, and the product is exactly `K⁻¹`: the two `rpow` factors cancel and `C_mult`
cancels, needing only `a ≠ 0`, `C_mult ≠ 0`, `K ≠ 0`. -/
theorem captureRate_mul_multiplicity_eq_inv {a Cmult K : ℝ≥0} (εint : ℝ)
    (hCmult : Cmult ≠ 0) (ha : a ≠ 0) (hK : K ≠ 0) :
    ((K * Cmult)⁻¹ * a ^ εint) * (Cmult * a ^ (-εint)) = K⁻¹ := by
  have hrpow : a ^ εint * a ^ (-εint) = 1 := by
    rw [← NNReal.rpow_add ha]
    simp
  calc
    ((K * Cmult)⁻¹ * a ^ εint) * (Cmult * a ^ (-εint))
        = ((K * Cmult)⁻¹ * Cmult) * (a ^ εint * a ^ (-εint)) := by ring
    _ = ((K * Cmult)⁻¹ * Cmult) := by rw [hrpow, mul_one]
    _ = K⁻¹ := by
          rw [mul_inv]
          field_simp

/-- **The final restriction is a quantitative refinement, at the localized capture rate.**

The `K = 256 · Nov` counterpart of `Plank.isCRefinement_restrictShade_of_unionCapture`: given the
aggregated localized capture `|U| ≤ K · |U ∩ G|` of
`Plank.volume_le_mul_volume_inter_of_localCapture` and the *global* constant multiplicity
`C_mult a^{-ε_int}`, cutting every shade to `G` is a `(K C_mult)⁻¹ a^{ε_int}`-refinement.

The coefficient is exact: `((K C_mult)⁻¹ a^{ε_int}) · (C_mult a^{-ε_int}) = K⁻¹`
(`Plank.captureRate_mul_multiplicity_eq_inv`), so the only loss on the fullness ledger is the single
factor `a^{ε_int}` plus the fixed constant `K = 256 · Nov`.  The index set is unchanged, so there is
no cardinality loss. -/
theorem isCRefinement_restrictShade_of_localCapture {a : ℝ≥0} (s' : Finset ι)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (Cmult : ℝ≥0) (εint : ℝ) (K : ℝ≥0) (hCmult : 0 < Cmult) (ha : 0 < a) (hK : 0 < K)
    (Gtot : Set (EuclideanSpace ℝ (Fin 3))) (hG : MeasurableSet Gtot)
    (hC : ShadedBody.HasCConstantMultiplicity s' Y' (Cmult * a ^ (-εint)))
    (hcap : volume (⋃ i ∈ s', (Y' i).shade)
      ≤ (K : ℝ≥0∞) * volume ((⋃ i ∈ s', (Y' i).shade) ∩ Gtot)) :
    ShadedBody.IsCRefinement s' (fun i => ShadedBody.restrictShade (Y' i) Gtot hG) s' Y'
      ((K * Cmult)⁻¹ * a ^ εint) := by
  have hKne : (K : ℝ≥0) ≠ 0 := hK.ne'
  have hKE : (K : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hKne
  have hdense : ((K⁻¹ : ℝ≥0) : ℝ≥0∞) * volume (⋃ i ∈ s', (Y' i).shade)
      ≤ volume ((⋃ i ∈ s', (Y' i).shade) ∩ Gtot) := by
    rw [ENNReal.coe_inv hKne]
    rw [ENNReal.inv_mul_le_iff hKE ENNReal.coe_ne_top]
    exact hcap
  exact isCRefinement_restrictShade_of_dense s' Y' hC hG hdense
    (le_of_eq (captureRate_mul_multiplicity_eq_inv εint hCmult.ne' ha.ne' hKne))


end Plank

end

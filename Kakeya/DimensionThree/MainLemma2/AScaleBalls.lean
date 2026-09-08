/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Covers
public import Kakeya.FactorFamily.Basic

/-!
# Ball geometry for the scale-`a` estimates of Main Lemma 2

The four elementary ball statements of the scale-`a` layer of Section 9
(GWZ), together with the one shading statement that
goes with them:

* blueprint `lem:ml2packingBound`, the packing bound `#F ≤ 5 ^ n` for an `r/2`-separated
  subset of an `r`-ball;
* blueprint `lem:ballCoverHalfRadius`, the cover of an `r`-ball by at most `5 ^ n` closed
  balls of radius `r/2`;
* blueprint `lem:ml2ballPigeonhole`, a half-radius piece of the cover carrying a `5^{-n}`
  fraction of the mass;
* blueprint `lem:ml2ballRecentre`, re-centring the ball at a point of the set itself, which is
  the form blueprint `boundVolumeAcrossTwoScales` needs;
* blueprint `lem:ml2coarseShaded`, that a point shaded at the fine scale is shaded at the
  coarse one.

All four reduce to the separated-net API of `Kakeya/Covers.lean`, and the fifth is the
`shade_subset_parent` field of `ShadedBody.ShadedFactorFamily` read at the level of unions.
They are consumed in `Kakeya/DimensionThree/MainLemma2/AScaleSetup.lean`, which carries the
rest of that layer.
-/

@[expose] public section

open scoped NNReal ENNReal

namespace Kakeya

open MeasureTheory Metric Set

section Balls

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]


/-- **Re-centring a ball at a point of the set**.

If `S` meets the ball `B(x₀, r)` then there is a point `x ∈ S` — not merely in the ball —
with `|S ∩ B(x₀, r)| ≤ 5 ^ n |S ∩ B(x, r)|`, at the same radius and hence at a ball of the
same measure.

The re-centred ball is *open*, which is what blueprint `boundVolumeAcrossTwoScales`, and so
`Kakeya.aScaleBall`, feeds on. No measurability of `S` is needed: this is
`Kakeya.exists_mem_volume_inter_ball_ge` applied to `S ∩ B(x₀, r)` at `K = 1`, whose constant
`(1 + 2)^n = 3 ^ n` is even better than the `5 ^ n` the blueprint records. -/
theorem exists_mem_volume_inter_ball_recentre {S : Set E} {x₀ : E} {r : ℝ} (hr : 0 < r)
    (hne : (S ∩ ball x₀ r).Nonempty) :
    ∃ x ∈ S,
      volume (S ∩ ball x₀ r) ≤
          (separatedNetCoverConstant (Module.finrank ℝ E) : ℝ≥0∞) * volume (S ∩ ball x r) ∧
        volume (ball x r) = volume (ball x₀ r) := by
  classical
  let S' : Set E := S ∩ ball x₀ r
  rcases exists_mem_volume_inter_ball_ge (S := S') hne hr (K := (1 : ℝ≥0)) (by norm_num) x₀
      (by intro x hx; exact inter_subset_right hx) (by simp) with ⟨y, hyS', hmain⟩
  refine ⟨y, hyS'.1, ?_, ?_⟩
  · have hc : (massSubballConstant (Module.finrank ℝ E) 1 : ℝ≥0∞) =
        (((3 : ℝ≥0) ^ Module.finrank ℝ E : ℝ≥0) : ℝ≥0∞)⁻¹ := by
      norm_num [massSubballConstant]
    have h3n0 : (((3 : ℝ≥0) ^ Module.finrank ℝ E : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
      exact ENNReal.coe_ne_zero.mpr (pow_ne_zero _ (by norm_num))
    have h3ntop : (((3 : ℝ≥0) ^ Module.finrank ℝ E : ℝ≥0) : ℝ≥0∞) ≠ ⊤ := by
      exact ENNReal.coe_ne_top
    have hV : volume S' ≤ (((3 : ℝ≥0) ^ Module.finrank ℝ E : ℝ≥0) : ℝ≥0∞) *
        volume (S' ∩ ball y r) := by
      rw [hc] at hmain
      exact (ENNReal.inv_mul_le_iff h3n0 h3ntop).mp hmain
    have hsub : S' ∩ ball y r ⊆ S ∩ ball y r := by
      intro x hx
      exact ⟨hx.1.1, hx.2⟩
    have hmono : volume (S' ∩ ball y r) ≤ volume (S ∩ ball y r) := measure_mono hsub
    have h3le5 : (((3 : ℝ≥0) ^ Module.finrank ℝ E : ℝ≥0) : ℝ≥0∞) ≤
        (separatedNetCoverConstant (Module.finrank ℝ E) : ℝ≥0∞) := by
      simpa only [separatedNetCoverConstant, ENNReal.coe_pow, ENNReal.coe_ofNat,
        Nat.cast_pow, Nat.cast_ofNat] using
        (ENNReal.pow_le_pow_left (by norm_num : (3 : ℝ≥0∞) ≤ 5) :
          (3 : ℝ≥0∞) ^ Module.finrank ℝ E ≤ 5 ^ Module.finrank ℝ E)
    calc
      volume S' ≤ (((3 : ℝ≥0) ^ Module.finrank ℝ E : ℝ≥0) : ℝ≥0∞) *
          volume (S' ∩ ball y r) := hV
      _ ≤ (((3 : ℝ≥0) ^ Module.finrank ℝ E : ℝ≥0) : ℝ≥0∞) *
          volume (S ∩ ball y r) := by
        gcongr
      _ ≤ (separatedNetCoverConstant (Module.finrank ℝ E) : ℝ≥0∞) *
          volume (S ∩ ball y r) := by
        gcongr
  · rw [MeasureTheory.Measure.addHaar_ball_center volume y r,
        MeasureTheory.Measure.addHaar_ball_center volume x₀ r]

end Balls

end Kakeya

namespace ShadedBody

open MeasureTheory Set
open scoped NNReal ENNReal

/-- **A shaded point is shaded at the coarse scale**.

If `x` lies in the shaded union `U(𝕋, Y')` of the inner family of a shaded factor family then
it lies in the shaded union `U(𝕋_a, Y_{𝕋_a})` of the outer family. This is exactly the
`shade_subset_parent` field, the blueprint's `pointwiseContainmenttube`, read at the level of
unions: the parent of a shaded index is an outer index, and it inherits the shade. -/
theorem mem_iUnion_outerShade_of_mem_iUnion_innerShade {E : Type*} [TopologicalSpace E]
    [MeasurableSpace E] [Convexity.ConvexSpace ℝ E] {ι κ : Type*}
    (G : ShadedFactorFamily E ι κ) {x : E}
    (hx : x ∈ ⋃ i ∈ G.innerSet, (G.innerBody i).shade) :
    x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade := by
  rcases Set.mem_iUnion₂.mp hx with ⟨i, hi, hxi⟩
  exact Set.mem_biUnion (G.parent_mem i hi) (G.shade_subset_parent i hi hxi)

end ShadedBody

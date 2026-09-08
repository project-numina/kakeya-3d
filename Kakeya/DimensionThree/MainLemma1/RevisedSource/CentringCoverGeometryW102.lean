/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceConstructionDefinitionsW97
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.CentringGeometryPrefixW112
public import Kakeya.Tube.CylinderApprox

/-!
# The small-ball centred cover of a tube family

Proves `Kakeya.ml1Boot.TrialRestartW94.exists_small_ball_centred_cover_w102`.  For a family of
`delta`-tubes inside the closed unit ball, with `delta <= 1/200`, it produces a finite set `H`
of centred `delta/2`-tubes inside the ball of radius `3/4` and a map `pi` such that the
`1/8`-scaled carrier of each `T i` lies in `pi i`, `H` is exactly the image of `pi`, and at most
`2 * 223^6` members of `H` lie in the `5 * (delta/2)`-neighbourhood of any affine line.  The
construction uses the centred net `Tube.exists_centred_net` and the line-packing count
`Tube.card_filter_line_le_of_centred_sep` from `MainLemma2.CanonicalCentredCover` (reached
through `CentringGeometryPrefixW112`) and `Kakeya.Tube.CylinderApprox`; it is consumed by
`CentringRepresentativesW102`.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped ENNReal NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

universe uE uI
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

open Kakeya.VeryNotSticky

theorem exists_small_ball_centred_cover_w102
    (hdim : Module.finrank ℝ E = 3)
    {delta : ℝ≥0} (hd : 0 < delta) (hdsmall : delta <= 1 / 200)
    {iota : Type uI} (F : Finset iota) (T : iota -> Tube delta E)
    (hball : ∀ i ∈ F, (T i).carrier ⊆ Metric.closedBall 0 1) :
    ∃ (H : Finset (Tube (delta / 2) E)) (pi : iota -> Tube (delta / 2) E),
      (∀ i ∈ F, pi i ∈ H) ∧
      (∀ W ∈ H, ∃ i ∈ F, pi i = W) ∧
      (∀ i ∈ F, (fun x : E => (1 / 8 : ℝ) • x) '' (T i).carrier ⊆ (pi i).carrier) ∧
      (∀ W ∈ H, W.IsCentred) ∧
      (∀ W ∈ H, W.carrier ⊆ Metric.closedBall 0 (3 / 4 : ℝ)) ∧
      (∀ o v : E, ‖v‖ = 1 ->
        ((H.filter (fun W => W.carrier ⊆ Metric.cthickening
          (5 * ((delta / 2 : ℝ≥0) : ℝ))
            (Set.range (fun t : ℝ => o + t • v)))).card : ℝ) <=
          2 * (223 : ℝ) ^ (6 : Nat)) := by
  classical
  let rho : ℝ≥0 := delta / 2
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hdR : (0 : ℝ) < delta := hd
  have hdRsmall : (delta : ℝ) <= 1 / 200 := by exact_mod_cast hdsmall
  have hrhoR : (rho : ℝ) = (delta : ℝ) / 2 := by simp [rho]
  let X : iota -> Set E := fun i => centringDilate '' (T i).carrier
  let p : iota -> E := fun i => centringDilate (T i).midpoint
  let d : iota -> E := fun i => (T i).direction
  have hXline : ∀ i, X i ⊆ Metric.cthickening ((rho : ℝ) / 4)
      (Set.range fun t : ℝ => p i + t • d i) := by
    intro i
    have h := centringDilate_image_subset_lineNbhd (T i)
    simpa only [X, p, d, hrhoR,
      show (delta : ℝ) / 2 / 4 = (delta : ℝ) / 8 by ring] using h
  have hXnorm : ∀ i ∈ F, ∀ z ∈ X i, ‖z‖ <= 1 / 8 := by
    intro i hi z hz
    obtain ⟨x, hx, rfl⟩ := hz
    have hxnorm : ‖x‖ <= 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hball i hi hx
    dsimp [centringDilate]
    rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
    linarith
  have hXne : ∀ i, (X i).Nonempty := fun i =>
    ⟨centringDilate (T i).midpoint, (T i).midpoint,
      Tube.midpoint_mem_carrier hd (T i), rfl⟩
  have hfoot : ∀ i, inner ℝ (Tube.lineFoot (p i) (d i)) (d i) = 0 :=
    fun i => inner_lineFoot_eq_zero _ _ (T i).norm_direction
  have hfootnorm : ∀ i ∈ F, ‖Tube.lineFoot (p i) (d i)‖ <= 1 / 6 := by
    intro i hi
    obtain ⟨z, hz⟩ := hXne i
    have h := norm_lineFoot_le (T i).norm_direction
      (show 0 <= (rho : ℝ) / 4 by positivity) (hXline i hz) (hXnorm i hi z hz)
    rw [hrhoR] at h
    linarith
  obtain ⟨H0, hcen, hmid, hsep, hcover⟩ :=
    Tube.exists_centred_net (E := E) rho (1 / 6) (ε := (rho : ℝ) / 4) (by positivity)
  have hchoice : ∀ i, ∃ W : Tube rho E, i ∈ F ->
      W ∈ H0 ∧ ‖Tube.lineFoot (p i) (d i) - W.midpoint‖ <= (rho : ℝ) / 2 ∧
        ‖d i - W.direction‖ <= (rho : ℝ) / 2 := by
    intro i
    by_cases hi : i ∈ F
    · obtain ⟨W, hW, hp, hd'⟩ := hcover (Tube.lineFoot (p i) (d i)) (d i)
        (hfoot i) (T i).norm_direction (hfootnorm i hi)
      refine ⟨W, fun _ => ⟨hW, ?_, ?_⟩⟩ <;> linarith
    · exact ⟨Tube.ofMidpointDirection rho 0 (T i).direction (T i).norm_direction,
        fun h => (hi h).elim⟩
  choose pi hpi using hchoice
  let H := F.image pi
  have hHsub : H ⊆ H0 := by
    intro W hW
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hW
    exact (hpi i hi).1
  refine ⟨H, pi, fun i hi => Finset.mem_image_of_mem _ hi, ?_, ?_,
    fun W hW => hcen W (hHsub hW), ?_, ?_⟩
  · intro W hW
    exact Finset.mem_image.mp hW
  · intro i hi z hz
    have hz : z ∈ X i := by simpa only [X, centringDilate, one_div] using hz
    obtain ⟨_, hp, hd'⟩ := hpi i hi
    let f := Tube.lineFoot (p i) (d i)
    have hzline : z ∈ Metric.cthickening ((rho : ℝ) / 4)
        (Set.range fun t : ℝ => f + t • d i) := by
      rw [range_line_lineFoot]
      exact hXline i hz
    let t : ℝ := inner ℝ (z - f) (d i)
    have herror : ‖z - (f + t • d i)‖ <= (rho : ℝ) / 4 := by
      rw [show t = inner ℝ (z - f) (d i) from rfl,
        Tube.norm_sub_foot_eq f (d i) z (T i).norm_direction]
      exact (Tube.mem_cthickening_line_iff (T i).norm_direction (by positivity)).mp hzline
    have htnorm : |t| <= 1 / 6 := by
      have heq : inner ℝ (f + t • d i) (d i) = t := by
        rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
          (T i).norm_direction, hfoot i]
        ring
      have htle : |t| <= ‖f + t • d i‖ := by
        calc
          _ = |inner ℝ (f + t • d i) (d i)| := by rw [heq]
          _ <= ‖f + t • d i‖ * ‖d i‖ := abs_real_inner_le_norm _ _
          _ = _ := by rw [(T i).norm_direction, mul_one]
      have hn := norm_sub_le z (z - (f + t • d i))
      rw [sub_sub_cancel] at hn
      have hzNorm := hXnorm i hi z hz
      rw [hrhoR] at herror
      linarith
    refine (pi i).mem_carrier_of_dist_le
      ((pi i).midpoint_add_smul_mem_segment (htnorm.trans (by norm_num))) ?_
    rw [dist_eq_norm]
    have heq : z - ((pi i).midpoint + t • (pi i).direction) =
        (z - (f + t • d i)) + ((f - (pi i).midpoint) + t • (d i - (pi i).direction)) := by
      module
    rw [heq]
    have hm := mul_le_mul htnorm hd' (norm_nonneg _) (by norm_num : (0 : ℝ) <= 1 / 6)
    calc
      _ <= ‖z - (f + t • d i)‖ +
          (‖f - (pi i).midpoint‖ + ‖t • (d i - (pi i).direction)‖) :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
      _ = ‖z - (f + t • d i)‖ +
          (‖f - (pi i).midpoint‖ + |t| * ‖d i - (pi i).direction‖) := by
        rw [norm_smul, Real.norm_eq_abs]
      _ <= (rho : ℝ) := by linarith
  · intro W hW z hz
    obtain ⟨t, g, ht, hg, rfl⟩ := W.exists_decomp_of_mem_carrier hz
    rw [Metric.mem_closedBall, dist_zero_right]
    have hm := hmid W (hHsub hW)
    have hn := (norm_add_le (W.midpoint + t • W.direction) g).trans
      (add_le_add (norm_add_le W.midpoint (t • W.direction)) le_rfl)
    have hs : ‖t • W.direction‖ = |t| := by
      rw [norm_smul, Real.norm_eq_abs, W.norm_direction, mul_one]
    rw [hs] at hn
    rw [hrhoR] at hg
    linarith
  · intro o v hv
    have h := Tube.card_filter_line_le_of_centred_sep H hrho (fun W => W)
      (fun W hW => hcen W (hHsub hW)) (by norm_num : (0 : ℝ) <= 1 / 6)
      (fun W hW => hmid W (hHsub hW)) (m := 4) (by norm_num)
      (fun W hW W' hW' hne => hsep W (hHsub hW) W' (hHsub hW') hne)
      (K := 5) (by norm_num) o v hv
    refine h.trans ?_
    norm_num [Tube.linePackingConstant, hdim]

end
end Kakeya.ml1Boot.TrialRestartW94

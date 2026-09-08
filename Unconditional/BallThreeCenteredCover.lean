/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Kakeya.DimensionThree.MainLemma1.RevisedSource.CentringCoverGeometryW102

/-!
# Ball Three Centered Cover

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

/- The net argument below adapts Numina's Apache-2.0 W102 proof to input ball radius 3. -/

noncomputable section

namespace KakeyaLink.DirectCenteredRoute

open Kakeya.ml1Boot.TrialRestartW94 Kakeya.VeryNotSticky
open MeasureTheory

set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

theorem exists_ball_three_centred_cover
    (hdim : Module.finrank Real E = 3)
    {delta : NNReal} (hd : 0 < delta) (hdsmall : delta ≤ 1 / 200)
    {I : Type v} (F : Finset I) (T : I -> Tube delta E)
    (hball : ∀ i ∈ F, (T i).carrier ⊆ Metric.closedBall 0 3) :
    ∃ (H : Finset (Tube (delta / 2) E)) (pi : I -> Tube (delta / 2) E),
      (∀ i ∈ F, pi i ∈ H) ∧
      (∀ W ∈ H, ∃ i ∈ F, pi i = W) ∧
      (∀ i ∈ F, (fun x : E => (1 / 8 : Real) • x) '' (T i).carrier ⊆ (pi i).carrier) ∧
      (∀ W ∈ H, W.IsCentred) ∧
      (∀ W ∈ H, ‖W.midpoint‖ ≤ (5 / 12 : Real)) ∧
      (∀ W ∈ H, W.carrier ⊆ Metric.closedBall 0 1) ∧
      (∀ o v : E, ‖v‖ = 1 ->
        ((H.filter (fun W : Tube (delta / 2) E => W.carrier ⊆ Metric.cthickening
          (5 * ((delta / 2 : NNReal) : Real))
            (Set.range (fun t : Real => o + t • v)))).card : Real) ≤
          2 * (223 : Real) ^ 6) := by
  classical
  let rho : NNReal := delta / 2
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hdRsmall : (delta : Real) ≤ 1 / 200 := by exact_mod_cast hdsmall
  have hrhoR : (rho : Real) = (delta : Real) / 2 := by simp [rho]
  let X : I -> Set E := fun i => centringDilate '' (T i).carrier
  let p : I -> E := fun i => centringDilate (T i).midpoint
  let d : I -> E := fun i => (T i).direction
  have hXline : ∀ i, X i ⊆ Metric.cthickening ((rho : Real) / 4)
      (Set.range fun t : Real => p i + t • d i) := by
    intro i
    have h := centringDilate_image_subset_lineNbhd (T i)
    simpa only [X, p, d, hrhoR,
      show (delta : Real) / 2 / 4 = (delta : Real) / 8 by ring] using h
  have hXnorm : ∀ i ∈ F, ∀ z ∈ X i, ‖z‖ ≤ 3 / 8 := by
    intro i hi z hz
    obtain ⟨x, hx, rfl⟩ := hz
    have hxnorm : ‖x‖ ≤ 3 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hball i hi hx
    dsimp [centringDilate]
    rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
    linarith
  have hXne : ∀ i, (X i).Nonempty := fun i =>
    ⟨centringDilate (T i).midpoint, (T i).midpoint,
      Tube.midpoint_mem_carrier hd (T i), rfl⟩
  have hfoot : ∀ i, inner Real (Tube.lineFoot (p i) (d i)) (d i) = 0 :=
    fun i => inner_lineFoot_eq_zero _ _ (T i).norm_direction
  have hfootnorm : ∀ i ∈ F, ‖Tube.lineFoot (p i) (d i)‖ ≤ 5 / 12 := by
    intro i hi
    obtain ⟨z, hz⟩ := hXne i
    have h := norm_lineFoot_le (T i).norm_direction
      (show 0 ≤ (rho : Real) / 4 by positivity) (hXline i hz) (hXnorm i hi z hz)
    rw [hrhoR] at h
    linarith
  obtain ⟨H0, hcen, hmid, hsep, hcover⟩ :=
    Tube.exists_centred_net (E := E) rho (5 / 12) (ε := (rho : Real) / 4) (by positivity)
  have hchoice : ∀ i, ∃ W : Tube rho E, i ∈ F ->
      W ∈ H0 ∧ ‖Tube.lineFoot (p i) (d i) - W.midpoint‖ ≤ (rho : Real) / 2 ∧
        ‖d i - W.direction‖ ≤ (rho : Real) / 2 := by
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
    fun W hW => hcen W (hHsub hW), fun W hW => hmid W (hHsub hW), ?_, ?_⟩
  · intro W hW
    exact Finset.mem_image.mp hW
  · intro i hi z hz
    have hz : z ∈ X i := by simpa only [X, centringDilate, one_div] using hz
    obtain ⟨_, hp, hd'⟩ := hpi i hi
    let f := Tube.lineFoot (p i) (d i)
    have hzline : z ∈ Metric.cthickening ((rho : Real) / 4)
        (Set.range fun t : Real => f + t • d i) := by
      rw [range_line_lineFoot]
      exact hXline i hz
    let t : Real := inner Real (z - f) (d i)
    have herror : ‖z - (f + t • d i)‖ ≤ (rho : Real) / 4 := by
      rw [show t = inner Real (z - f) (d i) from rfl,
        Tube.norm_sub_foot_eq f (d i) z (T i).norm_direction]
      exact (Tube.mem_cthickening_line_iff (T i).norm_direction (by positivity)).mp hzline
    have htnorm : |t| ≤ 5 / 12 := by
      have heq : inner Real (f + t • d i) (d i) = t := by
        rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
          (T i).norm_direction, hfoot i]
        ring
      have htle : |t| ≤ ‖f + t • d i‖ := by
        calc
          _ = |inner Real (f + t • d i) (d i)| := by rw [heq]
          _ ≤ ‖f + t • d i‖ * ‖d i‖ := abs_real_inner_le_norm _ _
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
    have hm := mul_le_mul htnorm hd' (norm_nonneg _) (by norm_num : (0 : Real) ≤ 5 / 12)
    calc
      _ ≤ ‖z - (f + t • d i)‖ +
          (‖f - (pi i).midpoint‖ + ‖t • (d i - (pi i).direction)‖) :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
      _ = ‖z - (f + t • d i)‖ +
          (‖f - (pi i).midpoint‖ + |t| * ‖d i - (pi i).direction‖) := by
        rw [norm_smul, Real.norm_eq_abs]
      _ ≤ (rho : Real) := by linarith
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
      (fun W hW => hcen W (hHsub hW)) (by norm_num : (0 : Real) ≤ 5 / 12)
      (fun W hW => hmid W (hHsub hW)) (m := 4) (by norm_num)
      (fun W hW W' hW' hne => hsep W (hHsub hW) W' (hHsub hW') hne)
      (K := 5) (by norm_num) o v hv
    refine h.trans ?_
    norm_num [Tube.linePackingConstant, hdim]

theorem exists_ball_three_centred_representatives
    (hdim : Module.finrank Real E = 3)
    {delta : NNReal} (hd : 0 < delta) (hdsmall : delta ≤ 1 / 200)
    {I : Type v} [DecidableEq I]
    (F : Finset I) (T : I -> Tube delta E) (hF : F.Nonempty)
    (hball : ∀ i ∈ F, (T i).carrier ⊆ Metric.closedBall 0 3) :
    ∃ (G : Finset I) (parent : I -> I) (W : I -> Tube (delta / 2) E),
      G.Nonempty ∧ G ⊆ F ∧ F.image parent = G ∧
      (∀ j ∈ G, parent j = j) ∧
      (∀ j ∈ G, (W j).IsCentred) ∧
      (∀ j ∈ G, ‖(W j).midpoint‖ ≤ (5 / 12 : Real)) ∧
      (∀ j ∈ G, (W j).carrier ⊆ Metric.closedBall 0 1) ∧
      lineEssentiallyDistinctW94 G W (2 * (223 : NNReal) ^ 6) ∧
      (∀ i ∈ F, (fun x : E => (1 / 8 : Real) • x) '' (T i).carrier ⊆
        (W (parent i)).carrier) := by
  classical
  obtain ⟨H, pi, hpi, hsurj, hcov, hcen, hmid, hball', hpack⟩ :=
    exists_ball_three_centred_cover hdim hd hdsmall F T hball
  obtain ⟨i0, hi0⟩ := hF
  have hchoice : ∀ U : Tube (delta / 2) E, ∃ i : I,
      U ∈ H -> i ∈ F ∧ pi i = U := by
    intro U
    by_cases hU : U ∈ H
    · obtain ⟨i, hi, heq⟩ := hsurj U hU
      exact ⟨i, fun _ => ⟨hi, heq⟩⟩
    · exact ⟨i0, fun h => (hU h).elim⟩
  choose rep hrep using hchoice
  let G := H.image rep
  let parent : I -> I := fun i => rep (pi i)
  have hG : ∀ j ∈ G, j ∈ F ∧ rep (pi j) = j ∧ pi j ∈ H := by
    intro j hj
    obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hj
    have h := hrep U hU
    exact ⟨h.1, by rw [h.2], by rw [h.2]; exact hU⟩
  have himage : F.image parent = G := by
    ext j
    constructor
    · intro hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_image_of_mem rep (hpi i hi)
    · intro hj
      obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hj
      obtain ⟨i, hi, heq⟩ := hsurj U hU
      exact Finset.mem_image.mpr ⟨i, hi, by dsimp [parent]; rw [heq]⟩
  have hparPi : ∀ i ∈ F, pi (parent i) = pi i := by
    intro i hi
    exact (hrep (pi i) (hpi i hi)).2
  refine ⟨G, parent, pi, ?_, fun j hj => (hG j hj).1, himage,
    fun j hj => (hG j hj).2.1, fun j hj => hcen (pi j) (hG j hj).2.2,
    fun j hj => hmid (pi j) (hG j hj).2.2,
    fun j hj => hball' (pi j) (hG j hj).2.2, ?_, ?_⟩
  · rw [← himage]
    exact ⟨parent i0, Finset.mem_image_of_mem _ hi0⟩
  · intro o v hv
    let Q := G.filter (fun j => liesInFiveDeltaLineTubeW94 (pi j) o v)
    have hQinj : Set.InjOn pi Q := by
      intro i hi j hj heq
      have hiG := (Finset.mem_filter.mp hi).1
      have hjG := (Finset.mem_filter.mp hj).1
      calc
        i = rep (pi i) := ((hG i hiG).2.1).symm
        _ = rep (pi j) := congrArg rep heq
        _ = j := (hG j hjG).2.1
    have hQsub : Q.image pi ⊆ H.filter (fun U => U.carrier ⊆
        Metric.cthickening (5 * ((delta / 2 : NNReal) : Real))
          (Set.range fun t : Real => o + t • v)) := by
      intro U hU
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hU
      obtain ⟨hjG, hjline⟩ := Finset.mem_filter.mp hj
      refine Finset.mem_filter.mpr ⟨(hG j hjG).2.2, ?_⟩
      intro x hx
      obtain ⟨t, ht⟩ := hjline x hx
      exact Metric.mem_cthickening_of_dist_le x (o + t • v) _ _ ⟨t, rfl⟩ ht
    have hcard : Q.card ≤ (H.filter (fun U => U.carrier ⊆
        Metric.cthickening (5 * ((delta / 2 : NNReal) : Real))
          (Set.range fun t : Real => o + t • v))).card := by
      rw [← Finset.card_image_of_injOn hQinj]
      exact Finset.card_le_card hQsub
    have hreal := (Nat.cast_le (α := Real).mpr hcard).trans (hpack o v hv)
    exact_mod_cast hreal
  · intro i hi
    rw [hparPi i hi]
    exact hcov i hi

end KakeyaLink.DirectCenteredRoute

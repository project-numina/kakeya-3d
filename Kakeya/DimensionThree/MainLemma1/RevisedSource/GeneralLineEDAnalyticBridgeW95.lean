/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.DetailedTrialDefinitionsW95
public import Kakeya.DimensionThree.MainLemma2.CanonicalCentredCover
public import Kakeya.DimensionThree.Plank.FlatPrismInnerEstimate

/-! E4 is a local analytic construction in the already chosen original
plank. It does not refactor the selected subfamily or change W's dimensions. -/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

universe uE uI

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

/-- Perpendicular axis coordinate only; the tube and shading are unchanged. -/
def axisFootW95 {delta : ℝ≥0} (T : Tube delta E) : E :=
  Tube.lineFoot T.center T.direction

/-- Delta-independent cardinality bound for the two sign boxes of line parameters. -/
def lineAmplificationBoundW95 (n : Nat) (R K : ℝ) : Nat :=
  Nat.ceil (2 * (4 * (R + 1) * (K - 1) * (1 + 8 * R) + 1) ^ n *
    (16 * (R + 1) * (K - 1) + 1) ^ n)

def nearLineFamilyW95 {iota : Type uI} {delta : ℝ≥0}
    (F : Finset iota) (T : iota -> Tube delta E) (o v : E) (K : ℝ) : Finset iota :=
  F.filter (fun i => (T i).carrier ⊆ VeryNotSticky.lineNbhd o v (K * (delta : ℝ)))

/-- E1: finite actual representatives for arbitrary, possibly noncentred
tubes. Assignment uses the representatives' complete axes; no tube moves. -/
theorem exists_radius_five_line_bins_w95
    {iota : Type uI} {delta : ℝ≥0} (hdelta : 0 < delta) (_hdelta_one : delta <= 1)
    (F : Finset iota) (T : iota -> Tube delta E)
    (R K : ℝ) (hR : 0 <= R) (hK : 1 <= K)
    (hcenter : ∀ i ∈ F, ‖(T i).center‖ <= R)
    (o v : E) (hv : ‖v‖ = 1) :
    ∃ (G : Finset iota) (assign : iota -> iota),
      G ⊆ nearLineFamilyW95 F T o v K ∧
      G.card <= lineAmplificationBoundW95 (Module.finrank ℝ E) R K ∧
      (∀ i ∈ nearLineFamilyW95 F T o v K, assign i ∈ G) ∧
      (∀ i ∈ nearLineFamilyW95 F T o v K,
        (T i).carrier ⊆ VeryNotSticky.lineNbhd
          (T (assign i)).center (T (assign i)).direction (5 * (delta : ℝ))) := by
  classical
  have hd : (0 : ℝ) < delta := by exact_mod_cast hdelta
  have hRp : 0 < R + 1 := by linarith
  have hKm : 0 <= K - 1 := sub_nonneg.mpr hK
  have hmid : ∀ i, (T i).midpoint = (T i).center := by
    intro i
    simp only [Tube.center, midpoint_eq_smul_add, Tube.midpoint]
    norm_num
  let H := nearLineFamilyW95 F T o v K
  let r : ℝ := (delta : ℝ) / (R + 1)
  let Rx : ℝ := (K - 1) * (delta : ℝ) * (1 + 8 * R)
  let Ry : ℝ := 4 * ((K - 1) * (delta : ℝ))
  have hr : 0 < r := div_pos hd hRp
  have hRx : 0 <= Rx := by dsimp [Rx]; positivity
  have hRy : 0 <= Ry := by dsimp [Ry]; positivity
  have hHF : H ⊆ F := Finset.filter_subset _ _
  have hparams : ∀ i ∈ H,
      (∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ‖(T i).direction - s • v‖ <= Ry) ∧
        ‖axisFootW95 (T i) - Tube.lineFoot o v‖ <= Rx := by
    intro i hi
    have hline : (T i).carrier ⊆ Metric.cthickening (K * (delta : ℝ))
        (Set.range fun t : ℝ => o + t • v) := by
      simpa only [VeryNotSticky.lineNbhd_eq_cthickening_range] using
        (Finset.mem_filter.mp hi).2
    have hcore : ∀ z ∈ segment ℝ (T i).x (T i).y,
        Tube.lineDist o v z <= (K - 1) * (delta : ℝ) := by
      intro z hz
      have hzdist := Tube.lineDist_le_of_carrier_subset (T i) hv
        (show (delta : ℝ) <= K * (delta : ℝ) by nlinarith) hline hz
      linarith
    obtain ⟨s, hs, hdir⟩ := Tube.exists_sign_norm_direction_sub_le (T i) hv
      (hcore _ (left_mem_segment ℝ _ _)) (hcore _ (right_mem_segment ℝ _ _))
    refine ⟨⟨s, hs, hdir⟩, ?_⟩
    have hw : ‖s • v‖ = 1 := by rcases hs with rfl | rfl <;> simp [hv]
    have hprojection : inner ℝ (T i).center v • v =
        inner ℝ (T i).center (s • v) • (s • v) := by
      rcases hs with rfl | rfl <;> simp
    have hproj : ‖inner ℝ (T i).center v • v -
        inner ℝ (T i).center (T i).direction • (T i).direction‖ <=
          2 * ‖(T i).center‖ * ‖(T i).direction - s • v‖ := by
      rw [hprojection]
      have hsplit : inner ℝ (T i).center (s • v) • (s • v) -
          inner ℝ (T i).center (T i).direction • (T i).direction =
            inner ℝ (T i).center (s • v) • (s • v - (T i).direction) +
              inner ℝ (T i).center (s • v - (T i).direction) • (T i).direction := by
        simp only [inner_sub_right]
        module
      rw [hsplit]
      calc
        _ <= ‖inner ℝ (T i).center (s • v) • (s • v - (T i).direction)‖ +
            ‖inner ℝ (T i).center (s • v - (T i).direction) • (T i).direction‖ :=
          norm_add_le _ _
        _ = |inner ℝ (T i).center (s • v)| * ‖s • v - (T i).direction‖ +
            |inner ℝ (T i).center (s • v - (T i).direction)| := by
          simp only [norm_smul, Real.norm_eq_abs, (T i).norm_direction, mul_one]
        _ <= (‖(T i).center‖ * ‖s • v‖) * ‖s • v - (T i).direction‖ +
            ‖(T i).center‖ * ‖s • v - (T i).direction‖ := by
          gcongr <;> exact abs_real_inner_le_norm _ _
        _ = 2 * ‖(T i).center‖ * ‖(T i).direction - s • v‖ := by
          rw [hw, norm_sub_rev (s • v)]
          ring
    have hcentre : Tube.lineDist o v (T i).center <= (K - 1) * (delta : ℝ) :=
      hcore _ (midpoint_mem_segment (𝕜 := ℝ) _ _)
    have hfoot : axisFootW95 (T i) - Tube.lineFoot o v =
        (((T i).center - o) - inner ℝ ((T i).center - o) v • v) +
          (inner ℝ (T i).center v • v -
            inner ℝ (T i).center (T i).direction • (T i).direction) := by
      dsimp [axisFootW95, Tube.lineFoot]
      rw [inner_sub_left]
      module
    rw [hfoot]
    calc
      _ <= Tube.lineDist o v (T i).center +
          ‖inner ℝ (T i).center v • v -
            inner ℝ (T i).center (T i).direction • (T i).direction‖ := norm_add_le _ _
      _ <= (K - 1) * (delta : ℝ) +
          2 * ‖(T i).center‖ * ‖(T i).direction - s • v‖ := add_le_add hcentre hproj
      _ <= (K - 1) * (delta : ℝ) + 2 * R * Ry := by
        gcongr
        · exact hcenter i (hHF hi)
      _ = Rx := by dsimp [Rx, Ry]; ring
  obtain ⟨G, hGH, hsep, hcover⟩ := exists_maximal_separated_finset H
    (fun i j => ‖axisFootW95 (T i) - axisFootW95 (T j)‖ +
      ‖(T i).direction - (T j).direction‖) (ε := r)
    (fun _ => by simpa using hr)
    (fun i j => by rw [norm_sub_rev (axisFootW95 (T i)), norm_sub_rev (T i).direction])
  let Gp := G.filter (fun i => ‖(T i).direction - (1 : ℝ) • v‖ <= Ry)
  let Gm := G.filter (fun i => ‖(T i).direction - (-1 : ℝ) • v‖ <= Ry)
  have hsplit : G ⊆ Gp ∪ Gm := by
    intro i hi
    obtain ⟨s, hs, hdir⟩ := (hparams i (hGH hi)).1
    rcases hs with rfl | rfl
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hi, hdir⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hi, hdir⟩))
  have hbox : ∀ (s : ℝ) (J : Finset iota), J ⊆ G ->
      (∀ i ∈ J, ‖(T i).direction - s • v‖ <= Ry) ->
      (J.card : ℝ) <= ((Rx + r / 4) / (r / 4)) ^ Module.finrank ℝ E *
        ((Ry + r / 4) / (r / 4)) ^ Module.finrank ℝ E := by
    intro s J hJG hJdir
    exact Tube.card_le_of_L1_separated_in_rectangle J (fun i => axisFootW95 (T i))
      (fun i => (T i).direction) (Tube.lineFoot o v) (s • v) hr hRx hRy
      (fun i hi j hj hij => hsep i (hJG hi) j (hJG hj) hij)
      (fun i hi => (hparams i (hGH (hJG hi))).2) hJdir
  have hp := hbox 1 Gp (Finset.filter_subset _ _) (fun i hi => (Finset.mem_filter.mp hi).2)
  have hm := hbox (-1) Gm (Finset.filter_subset _ _) (fun i hi => (Finset.mem_filter.mp hi).2)
  have hcard : (G.card : ℝ) <= (Gp.card : ℝ) + (Gm.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsplit).trans (Finset.card_union_le _ _)
  have hxratio : (Rx + r / 4) / (r / 4) = 4 * (R + 1) * (K - 1) * (1 + 8 * R) + 1 := by
    dsimp [Rx, r]
    field_simp
  have hyratio : (Ry + r / 4) / (r / 4) = 16 * (R + 1) * (K - 1) + 1 := by
    dsimp [Ry, r]
    field_simp
    ring
  rw [hxratio, hyratio] at hp hm
  have hGcard : G.card <= lineAmplificationBoundW95 (Module.finrank ℝ E) R K := by
    have hreal : (G.card : ℝ) <=
        2 * (4 * (R + 1) * (K - 1) * (1 + 8 * R) + 1) ^ Module.finrank ℝ E *
          (16 * (R + 1) * (K - 1) + 1) ^ Module.finrank ℝ E := by
      nlinarith only [hcard, hp, hm]
    exact_mod_cast hreal.trans (Nat.le_ceil _)
  let assign : iota -> iota := fun i => if hi : i ∈ H then (hcover i hi).choose else i
  have hass : ∀ i (hi : i ∈ H), assign i ∈ G ∧
      ‖axisFootW95 (T i) - axisFootW95 (T (assign i))‖ +
        ‖(T i).direction - (T (assign i)).direction‖ < r := by
    intro i hi
    simpa only [assign, dif_pos hi] using (hcover i hi).choose_spec
  refine ⟨G, assign, hGH, hGcard, fun i hi => (hass i hi).1, ?_⟩
  intro i hi x hx
  obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp ((T i).carrier_eq ▸ hx)
  obtain ⟨t, ht, hzt⟩ := (T i).exists_param_of_mem_segment hz
  rw [hmid] at hzt
  let c : ℝ := inner ℝ (T i).center (T i).direction + t
  have hc : |c| <= R + 1 := by
    calc
      |c| <= |inner ℝ (T i).center (T i).direction| + |t| := abs_add_le _ _
      _ <= ‖(T i).center‖ * ‖(T i).direction‖ + (1 / 2 : ℝ) :=
        add_le_add (abs_real_inner_le_norm _ _) ht
      _ <= R + 1 := by rw [(T i).norm_direction, mul_one]; linarith [hcenter i (hHF hi)]
  let j := assign i
  have hzaxis : z - ((T j).center +
      (c - inner ℝ (T j).center (T j).direction) • (T j).direction) =
        (axisFootW95 (T i) - axisFootW95 (T j)) + c • ((T i).direction - (T j).direction) := by
    rw [hzt]
    dsimp [axisFootW95, Tube.lineFoot, c]
    module
  have hzclose : dist z ((T j).center +
      (c - inner ℝ (T j).center (T j).direction) • (T j).direction) <= (delta : ℝ) := by
    rw [dist_eq_norm, hzaxis]
    calc
      _ <= ‖axisFootW95 (T i) - axisFootW95 (T j)‖ +
          |c| * ‖(T i).direction - (T j).direction‖ := by
        simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le
          (axisFootW95 (T i) - axisFootW95 (T j)) (c • ((T i).direction - (T j).direction))
      _ <= (R + 1) * (‖axisFootW95 (T i) - axisFootW95 (T j)‖ +
          ‖(T i).direction - (T j).direction‖) := by
        nlinarith [norm_nonneg (axisFootW95 (T i) - axisFootW95 (T j)),
          norm_nonneg ((T i).direction - (T j).direction)]
      _ <= (R + 1) * r := mul_le_mul_of_nonneg_left (hass i hi).2.le hRp.le
      _ = delta := by dsimp [r]; field_simp
  apply VeryNotSticky.mem_lineNbhd_of_dist_le
    (c - inner ℝ (T j).center (T j).direction)
  have hxz' := Metric.mem_closedBall.mp hxz
  have htriangle := dist_triangle x z ((T j).center +
    (c - inner ℝ (T j).center (T j).direction) • (T j).direction)
  linarith

/-- E1 counting corollary on the same unmodified family. -/
theorem lineED_five_implies_lineEDAt_w95
    {iota : Type uI} {delta : ℝ≥0} (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (F : Finset iota) (T : iota -> Tube delta E) (A : Nat)
    (hline : VeryNotSticky.IsLineEssDistinct A F T)
    (R K : ℝ) (hR : 0 <= R) (hK : 1 <= K)
    (hcenter : ∀ i ∈ F, ‖(T i).center‖ <= R) :
    VeryNotSticky.IsLineEssDistinctAt K
      (lineAmplificationBoundW95 (Module.finrank ℝ E) R K * A) F T := by
  classical
  intro o v hv
  obtain ⟨G, assign, hG, hcard, hassign, hcover⟩ :=
    exists_radius_five_line_bins_w95 hdelta hdelta_one F T R K hR hK hcenter o v hv
  let B : iota -> Finset iota := fun j => F.filter (fun i =>
    (T i).carrier ⊆ VeryNotSticky.lineNbhd (T j).center (T j).direction
      (5 * (delta : ℝ)))
  have hBcard : ∀ j, (B j).card <= A :=
    fun j => hline (T j).center (T j).direction (T j).norm_direction
  have hcovered : nearLineFamilyW95 F T o v K ⊆ G.biUnion B := by
    intro i hi
    exact Finset.mem_biUnion.mpr ⟨assign i, hassign i hi,
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1, hcover i hi⟩⟩
  calc
    (nearLineFamilyW95 F T o v K).card <= (G.biUnion B).card :=
      Finset.card_le_card hcovered
    _ <= ∑ j ∈ G, (B j).card := Finset.card_biUnion_le
    _ <= ∑ _j ∈ G, A := Finset.sum_le_sum (fun j _ => hBcard j)
    _ = G.card * A := by simp
    _ <= lineAmplificationBoundW95 (Module.finrank ℝ E) R K * A :=
      Nat.mul_le_mul_right A hcard

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- P1's pointwise distance predicate is the same closed line neighbourhood. -/
theorem pointwise_line_neighbourhood_iff_w95
    {delta : ℝ≥0} (T : Tube delta E) (o v : E) (hv : ‖v‖ = 1) :
    liesInFiveDeltaLineTubeW94 T o v ↔
      T.carrier ⊆ VeryNotSticky.lineNbhd o v (5 * (delta : ℝ)) := by
  constructor
  · intro h x hx
    obtain ⟨t, ht⟩ := h x hx
    exact VeryNotSticky.mem_lineNbhd_of_dist_le t ht
  · intro h x hx
    have hd : 0 <= 5 * (delta : ℝ) := by positivity
    have hdist := (Tube.mem_cthickening_line_iff hv hd).mp
      (show x ∈ Metric.cthickening (5 * (delta : ℝ))
        (Set.range fun t : ℝ => o + t • v) from by
          simpa only [VeryNotSticky.lineNbhd_eq_cthickening_range] using h hx)
    refine ⟨inner ℝ (x - o) v, ?_⟩
    simpa only [dist_eq_norm, Tube.norm_sub_foot_eq o v x hv] using hdist

/-- Integer counting against a real cap uses its floor, without a radius change. -/
theorem pointwise_lineED_iff_library_floor_w95
    {iota : Type uI} {delta : ℝ≥0} (F : Finset iota) (T : iota -> Tube delta E)
    (C : ℝ≥0) :
    lineEssentiallyDistinctW94 F T C ↔
      VeryNotSticky.IsLineEssDistinct (Nat.floor (C : ℝ)) F T := by
  have hfilter : ∀ o v, ‖v‖ = 1 ->
      F.filter (fun i => liesInFiveDeltaLineTubeW94 (T i) o v) =
        F.filter (fun i => (T i).carrier ⊆
          VeryNotSticky.lineNbhd o v (5 * (delta : ℝ))) := by
    intro o v hv
    exact Finset.filter_congr (fun i _ => pointwise_line_neighbourhood_iff_w95 (T i) o v hv)
  constructor
  · intro h o v hv
    apply (Nat.le_floor_iff C.coe_nonneg).mpr
    have hc := h o v hv
    rw [hfilter o v hv] at hc
    exact_mod_cast hc
  · intro h o v hv
    rw [hfilter o v hv]
    exact_mod_cast (Nat.le_floor_iff C.coe_nonneg).mp (h o v hv)

def lineSelectionMultiplicityW95 (n : Nat) (R : ℝ) (A : Nat) : Nat :=
  lineAmplificationBoundW95 n R (Kakeya.Tube.tubeOverlapCoreClose.C n) * A

/-- E2: the same actual pairwise family simultaneously retains mass and
cardinality and pays every analytic transport back to the original family. -/
theorem exists_pairwise_lineED_paid_w95
    {iota : Type uI} {delta : ℝ≥0} (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (F : Finset iota) (Y : iota -> ShadedTube delta E) (hF : F.Nonempty)
    (R : ℝ) (hR : 0 <= R) (hcenter : ∀ i ∈ F, ‖(Y i).center‖ <= R)
    (A : Nat) (hA : 1 <= A)
    (hline : VeryNotSticky.IsLineEssDistinct A F (fun i => (Y i).toTube))
    (K0 : ConvexSpaceBody E) (hcontained : ∀ i ∈ F, (Y i).toConvexSpaceBody <= K0)
    (_hmass : 0 < ∑ i ∈ F, volume (Y i).shade) :
    let M := lineSelectionMultiplicityW95 (Module.finrank ℝ E) R A
    ∃ q ⊆ F, q.Nonempty ∧
      (q : Set iota).Pairwise (fun i j => IsEssentiallyDistinct (Y i).carrier (Y j).carrier) ∧
      (∑ i ∈ F, volume (Y i).shade) <= (M : ℝ≥0∞) * (∑ i ∈ q, volume (Y i).shade) ∧
      F.card <= M * q.card ∧
      fullness' F (fun i => (Y i).toShadedBody) <=
        (M : ℝ≥0∞) * fullness' q (fun i => (Y i).toShadedBody) ∧
      frostmanConstIn q (fun i => (Y i).toConvexSpaceBody) K0 <=
        (M : ℝ≥0∞) * frostmanConstIn F (fun i => (Y i).toConvexSpaceBody) K0 ∧
      Kakeya.maxDensity q (fun i => (Y i).toConvexSpaceBody) <=
        Kakeya.maxDensity F (fun i => (Y i).toConvexSpaceBody) ∧
      ShadedBody.multiplicity F (fun i => (Y i).toShadedBody) <=
        (M : ℝ≥0∞) * ShadedBody.multiplicity q (fun i => (Y i).toShadedBody) := by
  classical
  let n := Module.finrank ℝ E
  let K := Kakeya.Tube.tubeOverlapCoreClose.C n
  let M := lineSelectionMultiplicityW95 n R A
  have hK : 1 <= K := (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C n).le
  have hB : 0 < lineAmplificationBoundW95 n R K := by
    apply Nat.ceil_pos.mpr
    have hKm : 0 <= K - 1 := sub_nonneg.mpr hK
    positivity
  have hM : 1 <= M := Nat.mul_pos hB (by omega)
  have hMzero : (M : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have hline' := lineED_five_implies_lineEDAt_w95 hdelta hdelta_one F
    (fun i => (Y i).toTube) A hline R K hR hK hcenter
  obtain ⟨q, hqF, hqED, hqmass, hqcard⟩ :=
    VeryNotSticky.exists_pairwise_of_isLineEssDistinctAt hdelta hdelta_one hline'
      (fun i => volume (Y i).shade)
  change (∑ i ∈ F, volume (Y i).shade) <= ((M - 1 + 1 : Nat) : ℝ≥0∞) *
    (∑ i ∈ q, volume (Y i).shade) at hqmass
  change F.card <= (M - 1 + 1) * q.card at hqcard
  rw [Nat.sub_add_cancel hM] at hqmass hqcard
  have hq : q.Nonempty := by
    by_contra hn
    have hqe : q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [hqe, hF.card_ne_zero] at hqcard
  have hsum : (∑ i ∈ q, volume (Y i).carrier) <=
      ∑ i ∈ F, volume (Y i).carrier := Finset.sum_le_sum_of_subset hqF
  have hfull : fullness' F (fun i => (Y i).toShadedBody) <=
      (M : ℝ≥0∞) * fullness' q (fun i => (Y i).toShadedBody) := by
    unfold fullness'
    rw [← mul_div_assoc]
    exact ENNReal.div_le_div hqmass hsum
  obtain ⟨i0, hi0⟩ := hF
  have hvol : ∀ i ∈ F, volume (Y i).carrier = volume (Y i0).carrier := by
    intro i hi
    exact Tube.volume_carrier_eq_volume_carrier (Y i).toTube (Y i0).toTube
  have hretain : (M : ℝ≥0∞)⁻¹ * (F.card : ℝ≥0∞) <= (q.card : ℝ≥0∞) := by
    apply (ENNReal.inv_mul_le_iff hMzero (by simp)).mpr
    exact_mod_cast hqcard
  have hCF : frostmanConstIn q (fun i => (Y i).toConvexSpaceBody) K0 <=
      (M : ℝ≥0∞) * frostmanConstIn F (fun i => (Y i).toConvexSpaceBody) K0 := by
    simpa only [inv_inv] using frostmanConstIn_subfamily_le ⟨i0, hi0⟩ hvol hcontained
      hqF (show (M : ℝ≥0∞)⁻¹ ≠ 0 by simp) hretain
  refine ⟨q, hqF, hq, hqED, hqmass, hqcard, hfull, hCF,
    Kakeya.maxDensity_mono _ hqF, ?_⟩
  apply ShadedBody.multiplicity_le_mul_of_sum_shade_le_of_biUnion_subset F
    (fun i => (Y i).toShadedBody) q (fun i => (Y i).toShadedBody) M _ hqmass
  intro x hx
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
  exact Set.mem_iUnion₂.mpr ⟨i, hqF hi, hxi⟩

end

end Kakeya.ml1Boot.TrialRestartW94

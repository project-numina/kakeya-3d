/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceAssignedAmbientTransport
public import Kakeya.StickyKakeya

/-!
# Sampled sub-towers and the sticky scale bracket

`sourceStickySampleIndex` samples every `M / M1`-th level; `source_sticky_subtower_radius`
relates the sampled radii. `SourceStickySubtower` and `source_exists_sticky_subtower` build a
sub-tower with the same leaves, occupied sampled nodes and assignments, preserving
`SourceTowerGeometry`, `SourceTowerNeighbourSharing` and `SourceTowerStatistics`.
`source_sticky_level_density_of_assigned_good` reads level density from the fixed assigned
good array, and `source_exists_sticky_scale_bracket` brackets each SSF grid scale between an
actual finer tower level and `40 * delta^(-1/M)` times it.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube

namespace Kakeya.ML2Core

universe u

def sourceStickySampleIndex (M M1 k : Nat) : Nat := k * (M / M1)

section Tower

variable {iota : Type u} {delta : ℝ≥0} {R : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace ℝ (Fin 3))} {M M1 C : Nat}

/-- An actual sub-tower has the same leaves, occupied sampled nodes and assignments. -/
structure SourceStickySubtower (Q : SourceThreadedTower R T M C)
    (Q1 : SourceThreadedTower R T M1 C) : Prop where
  index_identity : ∀ k, k <= M1 ->
    Q1.indexSet k = Q.indexSet (sourceStickySampleIndex M M1 k)
  assignment_identity : ∀ k, k <= M1 ->
    Q1.place k = Q.place (sourceStickySampleIndex M M1 k)
  tube_identity : ∀ k, k <= M1 -> ∀ j,
    (Q1.tube k j).toConvexSpaceBody =
      (Q.tube (sourceStickySampleIndex M M1 k) j).toConvexSpaceBody
  fibre_identity : ∀ a b, a <= M1 -> b <= M1 -> ∀ j,
    Q1.fibre a b j = Q.fibre (sourceStickySampleIndex M M1 a)
      (sourceStickySampleIndex M M1 b) j
  profile_identity : ∀ S : Finset iota, S <= R -> ∀ a b,
    a <= M1 -> b <= M1 ->
    Q1.assignedProfile S a b = Q.assignedProfile S
      (sourceStickySampleIndex M M1 a) (sourceStickySampleIndex M M1 b)

/-- The good array is the fixed Q assigned array, not an arbitrary terminal predicate. -/
theorem source_sticky_level_density_of_assigned_good (Q : SourceThreadedTower R T M C)
    {A0 A1 : Nat} (hM : 2 <= M) (hgeometry : SourceTowerGeometry Q A0 A1)
    {B : ℝ≥0} {N : Nat} {e : ℝ} (hB : 1 <= B) (he : 0 <= e)
    (hdelta0 : 0 < delta) (hdelta1 : delta <= 1)
    (hgood : SourceFixedKTArrayGood Q B N e) :
    ∀ k, k <= M -> Kakeya.maxDensity (Q.indexSet k)
      (fun j => (Q.tube k j).toConvexSpaceBody) <=
      (1280 ^ 6 : ℝ≥0∞) * (B : ℝ≥0∞) ^ (N + 1) *
        ENNReal.ofReal ((delta : ℝ) ^ (-(5 * e))) := by
  classical
  have hM0 : 0 < M := by omega
  have hrootcard : ((Q.indexSet 0).card : ℝ≥0∞) <= (1280 ^ 6 : ℝ≥0∞) := by
    have hc := hgeometry.coarse_card 0 hM0
    have hr : sourceTowerRadius delta M 0 = (1 / 40 : ℝ≥0) := by
      simp [sourceTowerRadius, hM0]
    rw [hr] at hc
    norm_num at hc ⊢
    exact_mod_cast hc
  have hpow : (1 : ℝ≥0∞) <= ENNReal.ofReal ((delta : ℝ) ^ (-(5 * e))) := by
    have hp : (1 : ℝ) <= (delta : ℝ) ^ (-(5 * e)) := by
      exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos
        (by exact_mod_cast hdelta0) (by exact_mod_cast hdelta1) (by nlinarith)
    exact_mod_cast ENNReal.ofReal_le_ofReal hp
  have hBpow : (1 : ℝ≥0∞) <= (B : ℝ≥0∞) ^ (N + 1) := by
    apply one_le_pow₀
    exact_mod_cast hB
  have hfac : (1 : ℝ≥0∞) <= (B : ℝ≥0∞) ^ (N + 1) *
      ENNReal.ofReal ((delta : ℝ) ^ (-(5 * e))) := by
    simpa using mul_le_mul' hBpow hpow
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    calc
      _ <= ((Q.indexSet 0).card : ℝ≥0∞) := Kakeya.maxDensity_le_card _ _
      _ <= (1280 ^ 6 : ℝ≥0∞) := hrootcard
      _ <= _ := by
        simpa only [mul_one, mul_assoc] using
          mul_le_mul_right hfac (1280 ^ 6 : ℝ≥0∞)
  · have hcover : Q.indexSet k <= (Q.indexSet 0).biUnion (Q.fibre 0 k) := by
      intro j hj
      obtain ⟨i, hi, hij⟩ := Q.place_surjective k hk j hj
      apply Finset.mem_biUnion.mpr
      refine ⟨Q.place 0 i, Q.place_mem 0 hM0.le i hi, ?_⟩
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩, hij⟩
    have hcell : ∀ j ∈ Q.indexSet 0, Kakeya.maxDensity (Q.fibre 0 k j)
        (fun i => (Q.tube k i).toConvexSpaceBody) <=
          (B : ℝ≥0∞) ^ (N + 1) * ENNReal.ofReal ((delta : ℝ) ^ (-(5 * e))) := by
      intro j hj
      obtain ⟨i, hi, hij⟩ := Q.place_surjective 0 hM0.le j hj
      have hin : j ∈ Q.assignedFootprint R 0 := Finset.mem_image.mpr ⟨i, hi, hij⟩
      have hle := Finset.le_sup (f := fun j =>
        Kakeya.maxDensity (Q.retainedAssignedFibre R 0 k j)
          (fun i => (Q.tube k i).toConvexSpaceBody)) hin
      have hgoodk := hgood k (by omega) hk
      have hconvert : (delta : ℝ≥0∞) ^ (-(5 * e)) =
          ENNReal.ofReal ((delta : ℝ) ^ (-(5 * e))) := by
        rw [← ENNReal.ofReal_rpow_of_pos (by exact_mod_cast hdelta0)]
        simp
      rw [hconvert] at hgoodk
      exact hle.trans hgoodk
    calc
      _ <= ∑ j ∈ Q.indexSet 0, Kakeya.maxDensity (Q.fibre 0 k j)
          (fun i => (Q.tube k i).toConvexSpaceBody) :=
        Kakeya.maxDensity_le_sum_of_subset_biUnion _ hcover
      _ <= ∑ _j ∈ Q.indexSet 0,
          (B : ℝ≥0∞) ^ (N + 1) * ENNReal.ofReal ((delta : ℝ) ^ (-(5 * e))) :=
        Finset.sum_le_sum hcell
      _ = ((Q.indexSet 0).card : ℝ≥0∞) *
          ((B : ℝ≥0∞) ^ (N + 1) * ENNReal.ofReal ((delta : ℝ) ^ (-(5 * e)))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ <= _ := by
        simpa only [mul_assoc] using mul_le_mul_left hrootcard
          ((B : ℝ≥0∞) ^ (N + 1) * ENNReal.ofReal ((delta : ℝ) ^ (-(5 * e))))

end Tower

/-- Each SSF radius is bracketed by an actual finer source level. The factor 40
is retained at the top and at the exceptional bottom step. -/
theorem source_exists_sticky_scale_bracket {delta : ℝ≥0} {M : Nat}
    (hM : 2 <= M) (hdelta0 : 0 < delta)
    (hdelta : delta < (400 : ℝ≥0) ^ (-(M : ℝ))) :
    ∃ fineLevel : Nat -> Nat, ∀ k, k <= ssfGridLen delta ->
      1 <= fineLevel k /\ fineLevel k <= M /\
      sourceTowerRadius delta M (fineLevel k) <= gridScale delta (ssfGridLen delta) k /\
      gridScale delta (ssfGridLen delta) k <=
        40 * delta ^ (-(1 / (M : ℝ))) * sourceTowerRadius delta M (fineLevel k) := by
  classical
  have hMr : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hd1 : delta <= 1 := hdelta.le.trans (by
    exact NNReal.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by simp))
  let x : ℝ≥0 := delta ^ (1 / (M : ℝ))
  have hx : 0 < x := by dsimp [x]; positivity
  have hx1 : x <= 1 := NNReal.rpow_le_one hd1 (by positivity)
  have hrep : ∀ k : Nat, delta ^ ((k : ℝ) / (M : ℝ)) = x ^ k := by
    intro k
    rw [show (k : ℝ) / (M : ℝ) = (1 / (M : ℝ)) * (k : ℝ) by ring,
      NNReal.rpow_mul, NNReal.rpow_natCast]
  have hbottom : delta = x ^ M := by
    simpa [div_self hMr.ne', NNReal.rpow_one] using hrep M
  have hinv : delta ^ (-(1 / (M : ℝ))) = x⁻¹ := NNReal.rpow_neg _ _
  have hfirst : 40 * x⁻¹ * sourceTowerRadius delta M 1 = 1 := by
    rw [sourceTowerRadius, if_pos (show 1 < M by omega), hrep, pow_one]
    field_simp
  have hstep : ∀ k, 1 <= k -> k < M ->
      sourceTowerRadius delta M k <= 40 * x⁻¹ * sourceTowerRadius delta M (k + 1) := by
    intro k hk hkM
    rw [sourceTowerRadius, if_pos hkM, hrep]
    by_cases hnext : k + 1 < M
    · rw [sourceTowerRadius, if_pos hnext, hrep, pow_succ]
      have heq : 40 * x⁻¹ * ((1 / 40) * (x ^ k * x)) = x ^ k := by
        field_simp
      rw [heq]
      exact mul_le_of_le_one_left (by positivity)
        (by norm_num [div_le_iff₀ (show (0 : ℝ≥0) < 40 by norm_num)])
    · have hMk : M = k + 1 := by omega
      rw [sourceTowerRadius, if_neg hnext, hbottom, hMk, pow_succ]
      have heq : 40 * x⁻¹ * (x ^ k * x) = 40 * x ^ k := by field_simp
      rw [heq]
      exact mul_le_mul_of_nonneg_right
        (by norm_num [div_le_iff₀ (show (0 : ℝ≥0) < 40 by norm_num)]) (by positivity)
  have hex : ∀ k : Nat, k <= ssfGridLen delta -> ∃ l : Nat,
      1 <= l ∧ l <= M ∧ sourceTowerRadius delta M l <= gridScale delta (ssfGridLen delta) k := by
    intro k hk
    refine ⟨M, by omega, le_rfl, ?_⟩
    simpa [sourceTowerRadius] using delta_le_gridScale hdelta0 hd1 hk
  let f : Nat -> Nat := fun k => if hk : k <= ssfGridLen delta then Nat.find (hex k hk) else M
  refine ⟨f, ?_⟩
  intro k hk
  have hf : f k = Nat.find (hex k hk) := dif_pos hk
  have hspec := Nat.find_spec (hex k hk)
  rw [← hf] at hspec
  refine ⟨hspec.1, hspec.2.1, hspec.2.2, ?_⟩
  rw [hinv]
  by_cases hf1 : f k = 1
  · rw [hf1, hfirst]
    exact gridScale_le_one hd1 _ _
  · have hprev : 1 <= f k - 1 := by omega
    have hnot := Nat.find_min (hex k hk) (show f k - 1 < Nat.find (hex k hk) by omega)
    have hprevM : f k - 1 < M := by omega
    have hless : gridScale delta (ssfGridLen delta) k < sourceTowerRadius delta M (f k - 1) := by
      exact lt_of_not_ge fun hh => hnot ⟨hprev, hprevM.le, hh⟩
    have hbound := hstep (f k - 1) hprev hprevM
    rw [show f k - 1 + 1 = f k by omega] at hbound
    exact hless.le.trans hbound

end Kakeya.ML2Core

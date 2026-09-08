/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.VeryNotStickyCase
public import Kakeya.DimensionThree.MainLemma2.BallCountRepair
public import Kakeya.DimensionThree.MainLemma2.SetupFullnessBudget
public import Kakeya.DimensionThree.MainLemma2.Reduction.Assembly

/-!
# Producing Configuration `hyp:ml2setup`
-/

@[expose] public section

open scoped NNReal ENNReal

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set Topology Filter ShadedBody

universe u

/-- **The density band of `Kakeya.VeryNotSticky` is exactly individual `δ^{2η}`-fullness.** -/
theorem exists_band_of_pointwise_two_eta {ι : Type*} {δ : ℝ≥0} {η : ℝ} {s : Finset ι}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : 0 < η)
    (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (hpt : ∀ i ∈ s, (δ : ℝ≥0∞) ^ (2 * η) * volume (T i).toShadedBody.carrier
      ≤ volume (T i).toShadedBody.shade) :
    ∃ lam Cd : ℝ≥0, 1 ≤ Cd ∧ Cd * δ ^ (2 * η) ≤ lam ∧
      (∀ i ∈ s, (Cd : ℝ≥0∞)⁻¹ * ((lam : ℝ≥0∞) * volume (T i).toShadedBody.carrier) ≤
        volume (T i).toShadedBody.shade) ∧
      (∀ i ∈ s, volume (T i).toShadedBody.shade ≤
        (Cd : ℝ≥0∞) * ((lam : ℝ≥0∞) * volume (T i).toShadedBody.carrier)) := by
  have hδ0 : δ ≠ 0 := hδ.ne'
  have hδE : (δ : ℝ≥0∞) ≠ 0 := by simpa using hδ0
  have hδEtop : (δ : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hcoeneg : ((δ ^ (-η) : ℝ≥0) : ℝ≥0∞) = (δ : ℝ≥0∞) ^ (-η) :=
    ENNReal.coe_rpow_of_ne_zero hδ0 _
  have hcoepos : ((δ ^ η : ℝ≥0) : ℝ≥0∞) = (δ : ℝ≥0∞) ^ η :=
    ENNReal.coe_rpow_of_ne_zero hδ0 _
  refine ⟨δ ^ η, δ ^ (-η), ?_, ?_, ?_, ?_⟩
  · exact NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  · rw [← NNReal.rpow_add hδ0]
    apply le_of_eq
    congr 1
    ring
  · intro i hi
    have hkey : ((δ ^ (-η) : ℝ≥0) : ℝ≥0∞)⁻¹ * ((δ ^ η : ℝ≥0) : ℝ≥0∞)
        = (δ : ℝ≥0∞) ^ (2 * η) := by
      rw [hcoeneg, hcoepos, ← ENNReal.rpow_neg, neg_neg, ← ENNReal.rpow_add _ _ hδE hδEtop]
      congr 1
      ring
    calc ((δ ^ (-η) : ℝ≥0) : ℝ≥0∞)⁻¹ *
          (((δ ^ η : ℝ≥0) : ℝ≥0∞) * volume (T i).toShadedBody.carrier)
        = (δ : ℝ≥0∞) ^ (2 * η) * volume (T i).toShadedBody.carrier := by
          rw [← mul_assoc, hkey]
      _ ≤ _ := hpt i hi
  · intro i hi
    have hkey : ((δ ^ (-η) : ℝ≥0) : ℝ≥0∞) * ((δ ^ η : ℝ≥0) : ℝ≥0∞) = 1 := by
      rw [hcoeneg, hcoepos, ← ENNReal.rpow_add _ _ hδE hδEtop]
      simp
    calc volume (T i).toShadedBody.shade ≤ volume (T i).toShadedBody.carrier :=
          measure_mono (T i).toShadedBody.shade_subset
      _ = ((δ ^ (-η) : ℝ≥0) : ℝ≥0∞) *
            (((δ ^ η : ℝ≥0) : ℝ≥0∞) * volume (T i).toShadedBody.carrier) := by
          rw [← mul_assoc, hkey, one_mul]


/-! ### The producer -/

namespace Produce

/-- The ambient space of Section 9. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

end Produce


/-! ### The (C4) group: the singleton biased factoring -/

/-- The partition of a `Finset` into its singletons. -/
def singletonFinpartition {ι : Type*} [DecidableEq ι] (s : Finset ι) : Finpartition s :=
  Finpartition.ofExistsUnique (s.image (fun i => ({i} : Finset ι)))
    (by
      intro p hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
      simpa using hi)
    (by
      intro a ha
      refine ⟨{a}, ⟨Finset.mem_image_of_mem _ ha, Finset.mem_singleton_self a⟩, ?_⟩
      rintro t ⟨ht, hat⟩
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ht
      rw [Finset.mem_singleton] at hat
      rw [hat])
    (by simp)

@[simp]
theorem singletonFinpartition_parts {ι : Type*} [DecidableEq ι] (s : Finset ι) :
    (singletonFinpartition s).parts = s.image (fun i => ({i} : Finset ι)) := rfl


/-! ### The single missing datum, and the eventual producer -/


/-! ### The residue, sharpened: the band and the mass budget are free -/


/-! ### The tube count, reduced to a covering statement about `ρ`-tubes -/


/-! ### What the `ρ`-count binder does and does not force -/


/-! ### The missing positive primitive: essential distinctness *from* angular separation -/


/-! ### What `tube_count` would need if it were a binder rather than a derivation -/


end Kakeya.VeryNotSticky

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set Topology Filter ShadedBody

universe u


end Kakeya.VeryNotSticky

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set Topology Filter ShadedBody

universe u


end Kakeya.VeryNotSticky

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set Topology Filter ShadedBody
open scoped NNReal ENNReal

universe u


end Kakeya.VeryNotSticky

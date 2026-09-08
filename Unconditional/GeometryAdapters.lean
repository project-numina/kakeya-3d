/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Kakeya.Shading
import MyLeanRepo.Kakeya.Streamlined.Families

/-!
# Numina to indexed BD geometry and shading adapters

Source definitions are in Numina `Kakeya/Tube/Basic.lean`,
`Kakeya/Shading.lean`, and BD `Kakeya/AssertionD.lean`,
`Kakeya/Streamlined/Families.lean`.

The BD families used here are the indexed `Kakeya.Streamlined` families consumed
by Pure WZ2 Theorem 5.2.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace KakeyaLink

universe u v

variable {delta rho : NNReal}

/-- BD's parametrized closed segment is Mathlib's closed segment. -/
theorem unitSegment_eq_segment (base direction : Kakeya.Point3) :
    Kakeya.unitSegment base direction = segment ℝ base (base + direction) := by
  simp [Kakeya.unitSegment, segment_eq_image']

/-- Keep the Numina starting endpoint and its oriented unit direction. -/
def toDeltaTube (T : Tube delta Kakeya.Point3) : Kakeya.DeltaTube (delta : ℝ) where
  base := T.x
  direction := T.direction
  direction_unit := T.norm_direction

/-- The two tube presentations have exactly the same closed carrier. -/
theorem toDeltaTube_carrier (T : Tube delta Kakeya.Point3) :
    (toDeltaTube T).carrier = T.carrier := by
  rw [T.carrier_eq_cthickening]
  change Metric.cthickening (delta : ℝ) (Kakeya.unitSegment T.x T.direction) = _
  rw [unitSegment_eq_segment]
  simp [Tube.direction]

theorem toDeltaTube_volume (T : Tube delta Kakeya.Point3) :
    (toDeltaTube T).volume = volume T.carrier := by
  exact congrArg volume (toDeltaTube_carrier T)


/-- This transports only the volume definition of distinctness. -/
theorem toDeltaTube_essentiallyDistinct_iff (T U : Tube delta Kakeya.Point3) :
    (toDeltaTube T).EssentiallyDistinct (toDeltaTube U) ↔
      _root_.IsEssentiallyDistinct T.carrier U.carrier := by
  simp only [Kakeya.DeltaTube.EssentiallyDistinct, toDeltaTube_carrier,
    toDeltaTube_volume, _root_.IsEssentiallyDistinct, one_div]

variable {ι : Type u}

/-- Enumerate exactly the selected indices, including when the finite set is empty. -/
def finsetIndex (s : Finset ι) : Fin s.card → ι :=
  fun k => (s.equivFin.symm k).val

theorem finsetIndex_mem (s : Finset ι) (k : Fin s.card) :
    finsetIndex s k ∈ s := by
  exact (s.equivFin.symm k).property

theorem finsetIndex_injective (s : Finset ι) :
    Function.Injective (finsetIndex s) := by
  exact Subtype.val_injective.comp s.equivFin.symm.injective

theorem range_finsetIndex (s : Finset ι) :
    Set.range (finsetIndex s) = (s : Set ι) := by
  ext i
  constructor
  · rintro ⟨k, rfl⟩
    exact finsetIndex_mem s k
  · intro hi
    exact ⟨s.equivFin ⟨i, hi⟩, by simp [finsetIndex]⟩

theorem sum_finsetIndex {M : Type v} [AddCommMonoid M]
    (s : Finset ι) (f : ι → M) :
    (∑ k : Fin s.card, f (finsetIndex s k)) = ∑ i ∈ s, f i := by
  rw [← Finset.sum_finset_coe f s]
  exact Fintype.sum_equiv s.equivFin.symm _ _ (fun _ => rfl)

theorem iUnion_finsetIndex {X : Type v} (s : Finset ι) (A : ι → Set X) :
    (⋃ k : Fin s.card, A (finsetIndex s k)) = ⋃ i ∈ s, A i := by
  ext x
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨k, hx⟩
    exact ⟨finsetIndex s k, finsetIndex_mem s k, hx⟩
  · rintro ⟨i, hi, hx⟩
    obtain ⟨k, rfl⟩ := (show i ∈ Set.range (finsetIndex s) by rwa [range_finsetIndex])
    exact ⟨k, hx⟩


/-- Forget convex-body structure only after retaining the exact indexed carrier. -/
def toBodyFamily (s : Finset ι) (W : ι → ConvexSpaceBody Kakeya.Point3) :
    Kakeya.Streamlined.BodyFamily where
  card := s.card
  body k := ⟨(W (finsetIndex s k)).carrier⟩

theorem toBodyFamily_mass (s : Finset ι) (W : ι → ConvexSpaceBody Kakeya.Point3) :
    (toBodyFamily s W).mass = ∑ i ∈ s, volume (W i).carrier := by
  exact sum_finsetIndex s (fun i => volume (W i).carrier)


theorem toBodyFamily_containedMass (s : Finset ι)
    (W : ι → ConvexSpaceBody Kakeya.Point3) (K : Set Kakeya.Point3) :
    (toBodyFamily s W).containedMass K =
      ∑ i ∈ s.filter (fun i => (W i).carrier ⊆ K), volume (W i).carrier := by
  unfold Kakeya.Streamlined.BodyFamily.containedMass
    Kakeya.Streamlined.BodyFamily.containedIndices
  change (∑ k ∈ Finset.univ.filter (fun k : Fin s.card =>
    (W (finsetIndex s k)).carrier ⊆ K), volume (W (finsetIndex s k)).carrier) = _
  rw [Finset.sum_filter, Finset.sum_filter]
  exact sum_finsetIndex s (fun i => if (W i).carrier ⊆ K then volume (W i).carrier else 0)


/-- Distinct original indices remain distinct even when tube carriers coincide. -/
def toTubeFamily (s : Finset ι) (T : ι → Tube delta Kakeya.Point3) :
    Kakeya.Streamlined.TubeFamily (delta : ℝ) where
  card := s.card
  tube k := toDeltaTube (T (finsetIndex s k))

theorem toTubeFamily_toBodyFamily (s : Finset ι)
    (T : ι → Tube delta Kakeya.Point3) :
    (toTubeFamily s T).toBodyFamily =
      toBodyFamily s (fun i => (T i).toConvexSpaceBody) := by
  unfold Kakeya.Streamlined.TubeFamily.toBodyFamily toTubeFamily toBodyFamily
  congr 1
  funext k
  exact congrArg Kakeya.Streamlined.Body.mk (toDeltaTube_carrier (T (finsetIndex s k)))


theorem toTubeFamily_isEssentiallyDistinct_iff (s : Finset ι)
    (T : ι → Tube delta Kakeya.Point3) :
    (toTubeFamily s T).IsEssentiallyDistinct ↔
      (s : Set ι).Pairwise
        (fun i j => _root_.IsEssentiallyDistinct (T i).carrier (T j).carrier) := by
  change (∀ k l : Fin s.card, k ≠ l →
    (toDeltaTube (T (finsetIndex s k))).EssentiallyDistinct
      (toDeltaTube (T (finsetIndex s l)))) ↔ _
  simp only [toDeltaTube_essentiallyDistinct_iff]
  constructor
  · intro h i hi j hj hij
    obtain ⟨k, rfl⟩ := (show i ∈ Set.range (finsetIndex s) by rwa [range_finsetIndex])
    obtain ⟨l, rfl⟩ := (show j ∈ Set.range (finsetIndex s) by rwa [range_finsetIndex])
    exact h k l (fun hkl => hij (congrArg (finsetIndex s) hkl))
  · intro h k l hkl
    exact h (finsetIndex_mem s k) (finsetIndex_mem s l)
      (fun hidx => hkl (finsetIndex_injective s hidx))

theorem toTubeFamily_mass (s : Finset ι) (T : ι → Tube delta Kakeya.Point3) :
    (toTubeFamily s T).toBodyFamily.mass = ∑ i ∈ s, volume (T i).carrier := by
  rw [toTubeFamily_toBodyFamily, toBodyFamily_mass]


theorem toTubeFamily_mass_pos (hdelta : 0 < delta)
    (s : Finset ι) (T : ι → Tube delta Kakeya.Point3) (hs : s.Nonempty) :
    0 < (toTubeFamily s T).toBodyFamily.mass := by
  rw [toTubeFamily_mass]
  obtain ⟨i, hi⟩ := hs
  apply lt_of_lt_of_le _ (Finset.single_le_sum (fun _ _ => bot_le) hi)
  exact lt_of_lt_of_le
    (Metric.measure_closedBall_pos volume (T i).x (by exact_mod_cast hdelta))
    (measure_mono ((T i).closedBall_subset_carrier_of_mem_segment
      (left_mem_segment ℝ (T i).x (T i).y)))

theorem shadedTube_shade_subset_toDeltaTube (V : ShadedTube delta Kakeya.Point3) :
    V.shade ⊆ (toDeltaTube V.toTube).carrier := by
  rw [toDeltaTube_carrier]
  exact V.shade_subset

/-- Preserve the original shade on every enumerated tube. -/
def toTubeShading (s : Finset ι) (V : ι → ShadedTube delta Kakeya.Point3) :
    Kakeya.Streamlined.TubeShading
      (toTubeFamily s (fun i => (V i).toTube)) where
  carrier k := (V (finsetIndex s k)).shade
  measurable_carrier k := (V (finsetIndex s k)).measurableSet_shade
  subset_body k := shadedTube_shade_subset_toDeltaTube (V (finsetIndex s k))

theorem toTubeShading_union (s : Finset ι) (V : ι → ShadedTube delta Kakeya.Point3) :
    (toTubeShading s V).union = ⋃ i ∈ s, (V i).shade := by
  rw [← iUnion_finsetIndex]
  ext x
  change (∃ k : Fin s.card, x ∈ (V (finsetIndex s k)).shade) ↔
    x ∈ ⋃ k : Fin s.card, (V (finsetIndex s k)).shade
  simp only [Set.mem_iUnion]

theorem toTubeShading_mass (s : Finset ι) (V : ι → ShadedTube delta Kakeya.Point3) :
    (toTubeShading s V).mass = ∑ i ∈ s, volume (V i).shade := by
  exact sum_finsetIndex s (fun i => volume (V i).shade)

theorem toTubeShading_mass_div_mass (s : Finset ι)
    (V : ι → ShadedTube delta Kakeya.Point3) :
    (toTubeShading s V).mass /
        (toTubeFamily s (fun i => (V i).toTube)).toBodyFamily.mass =
      ShadedBody.fullness' s (fun i => (V i).toShadedBody) := by
  rw [toTubeShading_mass, toTubeFamily_mass]

/-- The forward density bridge also covers empty families and zero-radius tubes. -/
theorem toTubeShading_isLambdaDense_of_fullness (s : Finset ι)
    (V : ι → ShadedTube delta Kakeya.Point3) {lambda : ENNReal}
    (hfull : lambda ≤ ShadedBody.fullness' s (fun i => (V i).toShadedBody)) :
    (toTubeShading s V).IsLambdaDense lambda := by
  rw [← toTubeShading_mass_div_mass] at hfull
  exact ENNReal.mul_le_of_le_div hfull


end KakeyaLink

end

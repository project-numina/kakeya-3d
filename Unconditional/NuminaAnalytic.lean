/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Kakeya.Sticky
import Kakeya.Tube.Dilate

/-!
# Numina Analytic

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

open MeasureTheory

namespace KakeyaLink.Analytic

attribute [local instance] Classical.propDecidable

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]
  {iota : Type*}

theorem containedMass_le_maxDensity_mul_volume
    (s : Finset iota) (W : iota -> ConvexSpaceBody E)
    (K : Set E) (hK : Convex Real K) :
    (Finset.sum (s.filter (fun i => (W i).carrier <= K))
        (fun i => volume (W i).carrier)) <=
      Kakeya.maxDensity s W * volume K := by
  classical
  let t := s.filter (fun i => (W i).carrier <= K)
  by_cases ht : t.Nonempty
  · have hsub : (t.convexHull_biUnion W).carrier ⊆ K :=
      (ht.convexHull_biUnion_subset_iff W hK.isConvexSet).2
        (fun i hi => (Finset.mem_filter.mp hi).2)
    calc
      ∑ i ∈ t, volume (W i).carrier
          ≤ Kakeya.maxDensity t W * volume (t.convexHull_biUnion W).carrier :=
        Kakeya.sum_volume_le_maxDensity_mul_volume'
          (fun i hi => Finset.le_convexHull_biUnion W hi)
      _ ≤ Kakeya.maxDensity s W * volume K :=
        mul_le_mul' (Kakeya.maxDensity_mono W (Finset.filter_subset _ _))
          (measure_mono hsub)
  · have he : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    change ∑ i ∈ t, volume (W i).carrier ≤ _
    simp [he]

theorem frostman_containedMass_mul_volume_le
    (s : Finset iota) (W : iota -> ConvexSpaceBody E)
    (anchor : ConvexSpaceBody E) (C : ENNReal)
    (hcontained : forall i, i ∈ s -> W i <= anchor)
    (hfrost : ConvexSpaceBody.IsFrostmanIn s W anchor C)
    (K : Set E) (hK : Convex Real K) :
    (Finset.sum (s.filter (fun i => (W i).carrier <= K))
        (fun i => volume (W i).carrier)) * volume anchor.carrier <=
      C * (Finset.sum s (fun i => volume (W i).carrier)) * volume K := by
  calc
    _ ≤ (Kakeya.maxDensity s W * volume K) * volume anchor.carrier :=
      mul_le_mul_right' (containedMass_le_maxDensity_mul_volume s W K hK) _
    _ ≤ ((C * Kakeya.densityIn s W anchor) * volume K) * volume anchor.carrier :=
      mul_le_mul_right' (mul_le_mul_right'
        (hfrost.maxDensity_le_of_carrier_subset hcontained) _) _
    _ = C * (Finset.sum s (fun i => volume (W i).carrier)) * volume K := by
      rw [Kakeya.sum_volume_eq_densityIn_mul_volume' hcontained]
      ac_rfl

variable [Nontrivial E]


end KakeyaLink.Analytic

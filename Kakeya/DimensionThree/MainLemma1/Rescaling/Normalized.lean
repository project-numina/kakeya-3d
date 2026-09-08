/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Cases
public import Kakeya.DimensionThree.MainLemma1.PlankTube
public import Kakeya.DimensionThree.MainLemma1.Rescaling.Thresholds
public import Kakeya.Factoring.FlatPrisms
public import Kakeya.DimensionThree.MainLemma1.Setup
public import Kakeya.Thickness.Lemmas
public import Kakeya.Tube.Dilate
public import Kakeya.Tube.IntersectionVolume
public import Kakeya.DimensionThree.MainLemma1.Rescaling.UniformEveryScale
public import Kakeya.DimensionThree.MainLemma1.Rescaling.Hybrid

/-!
# Main Lemma 1, Case (ii): Rescaling the middle factor to the unit ball

Split out of `Kakeya/DimensionThree/MainLemma1/Rescaling.lean`.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya

namespace ml1Boot

/-! ### Rescaling the middle factor to the unit ball -/

section Rescale

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]


/-- The constant at which `Kakeya.ml1Boot.exists_normalizedMiddleData` returns the uniformity of
the rescaled family, given the uniformity constant `Cunif` of the input family and the two-sided
shading constant `Λ`.  It is a `max 1` of a raw value, so `1 ≤ ·` is a theorem
(`Kakeya.ml1Boot.normalizedUnif.one_le_C`) rather than an assumption. -/
noncomputable def normalizedUnif.C (Cunif Λ : ℝ≥0) : ℝ≥0 :=
  max 1 (fineFactor.C * Cunif * Λ ^ 2)

/-- The uniformity constant of the normalized middle family is at least `1`. -/
theorem normalizedUnif.one_le_C (Cunif Λ : ℝ≥0) : 1 ≤ normalizedUnif.C Cunif Λ :=
  le_max_left _ _


end Rescale

end ml1Boot

end Kakeya
open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya
namespace ml1Boot

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]


end ml1Boot
end Kakeya

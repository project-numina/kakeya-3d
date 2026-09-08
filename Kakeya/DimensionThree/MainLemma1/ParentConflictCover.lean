/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.EnlargementCover
public import Kakeya.DimensionThree.BoundedOverlapCount

/-!
# Axial covers for parent conflicts

This file supplies the geometric core of the essentially-distinct parent selection used in
Section 8.  A family of same-scale parents which all fail essential distinctness against one
fixed parent lies in a bounded homothetic dilate of that parent.  Such a dilate is not covered by
constantly many same-scale tubes: unit cores may slide along the axis, and there are genuinely
`O(ρ⁻¹)` possible axial positions.  The declarations below isolate exactly that freedom.

For a thin tube `U` in the overlap dilate of a `ρ`-tube `V`, first orient `U` along `V`, round its
axial midpoint coordinate to an integer multiple of `ρ`, and place it in a concentric rescaling
of the corresponding axial translate of `V`.  The already-proved fixed-size rescaling cover
`Kakeya.ml1Boot.exists_cover_of_subset_rescale` then replaces that rescaling by one of constantly
many actual `ρ`-tubes.  The integer slice is returned explicitly; a later counting lemma bounds
the number of slices by `O(ρ⁻¹)`.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Metric Set Filter Topology ConvexSpaceBody

namespace Kakeya.ml1Boot

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

namespace parentConflictCover

/-- The rescaling ratio used within one axial slice.  It depends only on the ambient dimension. -/
noncomputable def Lambda (n : ℕ) : ℝ≥0 :=
  4 * ((Kakeya.Tube.tubeOverlapCoreClose.C n).toNNReal + 1)

/-- Dimensional constant in the axial parent-conflict count. -/
noncomputable def C (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [ProperSpace E] : ℝ≥0 :=
  (enlargementCoverConstant E (Lambda (Module.finrank ℝ E)) + 1 : ℕ) *
    (3 * (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E)).toNNReal + 2)

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem C_pos : 0 < C E := by
  unfold C
  positivity

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem C_coe : (C E : ℝ) =
    (enlargementCoverConstant E (Lambda (Module.finrank ℝ E)) + 1 : ℕ) *
      (3 * Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) + 2) := by
  unfold C
  push_cast
  rw [Real.coe_toNNReal _ (le_trans zero_le_one
    (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C (Module.finrank ℝ E)).le)]

/-- The `z`-th same-scale axial translate of `V`, with midpoint shifted by `z ρ`. -/
noncomputable def axialTube {ρ : ℝ≥0} (V : Tube ρ E) (z : ℤ) : Tube ρ E :=
  Tube.ofMidpointDirection ρ
    (V.center + ((z : ℝ) * (ρ : ℝ)) • V.direction) V.direction V.norm_direction

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
@[simp] theorem axialTube_midpoint {ρ : ℝ≥0} (V : Tube ρ E) (z : ℤ) :
    (axialTube V z).midpoint = V.center + ((z : ℝ) * (ρ : ℝ)) • V.direction := by
  simp [axialTube, Tube.midpoint]
  module

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
@[simp] theorem axialTube_direction {ρ : ℝ≥0} (V : Tube ρ E) (z : ℤ) :
    (axialTube V z).direction = V.direction := by
  simp [axialTube, Tube.direction]
  module

end parentConflictCover

end Kakeya.ml1Boot

namespace Kakeya.ml1Boot

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end Kakeya.ml1Boot

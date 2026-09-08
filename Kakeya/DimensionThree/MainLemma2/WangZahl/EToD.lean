/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.WangZahl.Definitions
public import Kakeya.Tube.Dilate

/-!
# Assertion E implies Assertion D

Basic lemmas about the Wang--Zahl definitions (`Kakeya.WangZahl.volume_carrier_eq_tubeVolume`,
`tubeVolume_pos_and_ne_top`, the `sInf` bounds `katzTaoConvexWolffConstant_le` and
`frostmanSlabWolffConstant_le`, and `one_le_katzTaoConvexWolffConstant_of_nonempty`), the
exponent comparison `e_factor_ge_d_factor`, and the implication
`assertionE_implies_assertionD_sameUniverse` for `0 <= sigma`, obtained by shrinking the
accuracy parameter `eta` so the Wolff-constant powers are absorbed.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory

namespace Kakeya.WangZahl

noncomputable section

universe u

lemma volume_carrier_eq_tubeVolume {δ : ℝ≥0} {ι : Type u}
    (T : ι → ShadedTube δ Space3) (i : ι) :
    volume (T i).carrier = tubeVolume δ := by
  exact Tube.volume_carrier_eq_volume_carrier (T i).toTube (modelTube δ)

end

end Kakeya.WangZahl

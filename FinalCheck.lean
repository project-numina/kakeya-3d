/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Kakeya.DimensionThree.KakeyaConjecture

/-! Final checks for the public theorem chain and the Sticky hypothesis it carries. -/

universe u v

-- The Sticky hypothesis carried by the public theorem, stated in full.
example : StickyKakeya.StickyFrostmanHypothesis.{u, v} =
    (forall {E : Type u} [NormedAddCommGroup E] [InnerProductSpace Real E]
      [FiniteDimensional Real E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E],
      Module.finrank Real E = 3 -> StickyKakeya.StickyFrostmanEstimate.{u, v} (E := E)) :=
  rfl

#check (KakeyaDimensionThree :
  StickyKakeya.StickyFrostmanHypothesis.{0, 0} -> KakeyaSetConjecture 3)

/-- info: 'Kakeya.KatzTaoEstimate.frostmanEstimate' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Kakeya.KatzTaoEstimate.frostmanEstimate

/-- info: 'Kakeya.KatzTaoEstimate.katzTaoEstimate_sub_of_frostmanEstimate' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Kakeya.KatzTaoEstimate.katzTaoEstimate_sub_of_frostmanEstimate

/-- info: 'Kakeya.katzTaoEstimateDimensionThree' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Kakeya.katzTaoEstimateDimensionThree

/-- info: 'KakeyaEstimateDimensionThree_pos' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KakeyaEstimateDimensionThree_pos

/-- info: 'dimH_ge_three_of_kakeyaEstimate' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dimH_ge_three_of_kakeyaEstimate

/-- info: 'KakeyaDimensionThree' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KakeyaDimensionThree

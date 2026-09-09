/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Unconditional.KakeyaConjecture

/-!
# Axiom assertions for the unconditional result

The two endpoints of the linking layer must depend on Lean's three standard
axioms and on nothing else.
-/

#check (Unconditional.KakeyaDimensionThree : KakeyaSetConjecture 3)

/-- info: 'stickyFrostmanHypothesis_of_pureWZ2' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stickyFrostmanHypothesis_of_pureWZ2

/-- info: 'Unconditional.KakeyaDimensionThree' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Unconditional.KakeyaDimensionThree

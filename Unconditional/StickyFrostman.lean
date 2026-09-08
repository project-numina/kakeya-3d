/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Kakeya.Sticky
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Theorem5_2Unconditional
import Unconditional.DirectConversion
import Unconditional.DirectConversionAssembly

/-!
# Exact linking target

The linking target: `StickyKakeya.StickyFrostmanHypothesis` of `Kakeya/Sticky.lean`.
The declaration retains both universe parameters and assumes no conversion theorem.
-/

universe uE uI

theorem stickyFrostmanHypothesis_of_pureWZ2 :
    StickyKakeya.StickyFrostmanHypothesis.{uE, uI} := by
  exact KakeyaLink.stickyFrostmanHypothesis_of_directConversion.{uE, uI}
    KakeyaLink.directConversion.{uE, uI}

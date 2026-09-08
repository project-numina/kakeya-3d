/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Unconditional.DirectConversionStatement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Theorem5_2Unconditional

/-!
# Direct Conversion Assembly

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

open MeasureTheory

namespace KakeyaLink

universe uE uI

theorem stickyFrostmanHypothesis_of_directConversion
    (conversion : DirectConversionStatement.{uE, uI}) :
    StickyKakeya.StickyFrostmanHypothesis.{uE, uI} := by
  intro E _ _ _ _ _ _ hdim epsilon hepsilon
  obtain ⟨outputLoss, theoremDelta0, houtputLoss, htheoremDelta0,
    _htheoremDelta0One, estimate⟩ :=
    Kakeya.Assouad.PureWZ2Theorem5_2Unconditional epsilon hepsilon
  obtain ⟨inputLoss, conversionDelta0, hinputLoss, hconversionDelta0, convert⟩ :=
    conversion hdim outputLoss houtputLoss
  refine ⟨inputLoss, min theoremDelta0 conversionDelta0, hinputLoss,
    lt_min htheoremDelta0 hconversionDelta0, ?_⟩
  intro delta hdelta hdeltaSmall ι s V hsupport C hC U hfull hFrostman
  obtain ⟨family, shading, hfamily, hCWA, hdense, hvolume⟩ :=
    convert hdelta (hdeltaSmall.trans (min_le_right _ _))
      s V hsupport hC U hfull hFrostman
  have hdeltaReal : 0 < (delta : ℝ) := hdelta
  exact (estimate (delta : ℝ) hdeltaReal
    (hdeltaSmall.trans (min_le_left _ _)) family hfamily hCWA shading hdense).trans hvolume

end KakeyaLink

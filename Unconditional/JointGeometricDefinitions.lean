/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZBridge
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.AnchoredParentContainment

/-!
Joint P6/P7 construction interfaces. These declarations concern one common
selection at finitely many small scales. Large-scale witnesses and nearby-scale
rounding remain separate consumers. Every theorem body is a proof obligation.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace KakeyaLink.JointSelection

open Kakeya.Streamlined Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- The reciprocal of the source's fixed-power refinement fraction. -/
def geometricSelectionLoss (delta : ℝ) (logExponent : ℕ) : ENNReal :=
  ENNReal.ofReal (Real.log (1 / delta)) ^ logExponent

/-- Canonical radius `8 * A * rho` parents with the original finite indexing. -/
def canonicalReanchoredParents {rho : ℝ} (A : ℝ) (center : Kakeya.Point3)
    (coarse : TubeFamily rho) : TubeFamily (8 * A * rho) where
  card := coarse.card
  tube index := pureWZ2ReanchoredParentTube (A := A) center (coarse.tube index)

/-- One localized selection, with exact source provenance and the paid global loss. -/
structure JointLocalizedSelectionData
    {delta : ℝ} {source : TubeFamily delta}
    (sourceShading : TubeShading source) (density weightLoss : ENNReal) where
  selected : TubeSubfamily source
  center : Kakeya.Point3
  localized : PureWZ2LocalizedReanchoringData sourceShading selected center (1 / 4)
  source_indices_eq :
    Finset.univ.image localized.sourceIndex = Finset.univ.image selected.embedding
  canonical_tube : ∀ index,
    localized.family.tube index =
      pureWZ2ReanchoredTube center (source.tube (localized.sourceIndex index))
  nonempty : localized.family.Nonempty
  positive_weights : ∀ index, 0 < volume (localized.shading.carrier index)
  ordinary_distinct : WZ2PaperOrdinaryIsEssentiallyDistinct localized.family
  retained_mass : sourceShading.mass ≤ weightLoss * localized.shading.mass
  global_mass_ratio : source.toBodyFamily.mass ≤
    (weightLoss / density) * localized.family.toBodyFamily.mass
  weight_band : ∃ weightLevel : ENNReal, 0 < weightLevel ∧
    ∀ index, weightLevel ≤ volume (localized.shading.carrier index) ∧
      volume (localized.shading.carrier index) ≤ 2 * weightLevel


end KakeyaLink.JointSelection

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Unconditional.JointGeometricDefinitions
import Unconditional.NuminaCoarseRepresentatives
import Unconditional.GeometryAdapters
import Kakeya.Tube.Dilate

/-!
Numina P6/P7 consumer. Original grid assignments remain coordinates after
maximal coarse-representative grouping. The joint producer explicitly consumes
the separately reviewed leaf normalization; no BD exact-scale input is assumed.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace KakeyaLink.JointSelection

open Kakeya.Streamlined Kakeya.Assouad

attribute [local instance] Classical.propDecidable

universe u

variable {I : Type u} {delta : NNReal}
  {s : Finset I} {V : I → ShadedTube delta Kakeya.Point3} {N : ℕ} {C : NNReal}

/-- A selected old class, indexed in the final reanchored family. -/
def selectedNuminaOldClass
    {density weightLoss : ENNReal}
    (selection : JointLocalizedSelectionData (toTubeShading s V) density weightLoss)
    (assign : I → I) (oldParent : I) : Finset (Fin selection.localized.family.card) :=
  Finset.univ.filter fun index =>
    assign (finsetIndex s (selection.localized.sourceIndex index)) = oldParent


end KakeyaLink.JointSelection

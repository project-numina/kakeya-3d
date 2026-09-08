/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.CollarPlankPresentation
public import Kakeya.DimensionThree.Plank.GlobalPlankDatumBridge
public import Kakeya.DimensionThree.Volume

/-!
# The plank-presented outer family of GWZ 6.6(B) is not the representative family

GWZ Proposition 5.1 returns its outer shading on the `scale`-collar of the cell body, never on the
cell's representative plank (`ShadedBody.FactoringAndMultPropCoreAtScale.outer_carrier`).  The
collar does not fit inside an `a × b × 1` `Plank`: the long half-width of a plank is pinned at
`1` and the collar of a body reaching the working window reaches `1 + s`.  So the Section-6 outer
family has to be *presented*, and the presentation in this library is the single common homothety
`Kakeya.collarPlank`, whose underlying plank is
`Kakeya.comparablePlankEnvelope.plank (windowConst R Cw) a b hab hb1 K` — the exact envelope of the
**shrunk** collar of the body `K` (`Kakeya.collarPlank_toPrism3D`).

Before steps, the small-`b` branch of Proposition 6.6(B)
(`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_of_masterScaleLemma61`) obtained the pairwise
essential distinctness that its `γ = 0` application of Lemma 6.1 needs from the exported clause

`∀ x, (W x).toPrism3D = D.factor.repr x`

through `Kakeya.pairwise_isEssentiallyDistinct_of_toPrism3D_eq`.  That route is unavailable for a
presented family, and this file is the machine-checked reason.

## What is refuted, and why one witness does both

`Kakeya.collarPlank hR hCw hab hb1 K Y`'s plank depends on the body `K` **only** — the shading `Y`
enters the shade and not the prism, and the representative plank `D.factor.repr x` does not enter at
all.  Hence any two cells with the same body have the *same* presented plank, whatever their
representatives are.  The witness is exactly that configuration, and it is legal at every scale:

* the common body is `Kakeya.CollarPlankRefute.cellBody`, the quarter-scale prism with half-widths
  `(a/4, b/4, 1/4)`.  It has plank-comparable dimensions `Kakeya.IsPlankOfDimensions Cw a b` for
  every `Cw ≥ 4` — in particular for the `Cw = 128` of the Main-Lemma-2 call site
  (`Kakeya.ML2Reduction.PlankFactoringData.toGlobalPlankFactorization`) — and it lies in the working
  window at every radius `R ≥ 1`, so in the radius-`4` window of
  `Kakeya.Section6PartBFactorisation.repr_window`;
* the two representatives are `Kakeya.CollarPlankRefute.refPlank` at centres `± (a/2) e₀`.  Both
  contain the body, they are **distinct** planks, and they are **essentially distinct**: their
  intersection lies in the prism of half-widths `(a/2, b, 1)`, of volume `4ab`, exactly half of
  `8ab`.

Both refutations follow:

* `not_statement_of_universal_presentedPlank_eq_repr` — the identification cannot hold, since it
  would identify the two distinct representatives with the one presented plank;
* `not_statement_of_universal_presentedPlank_ED` — neither can the transport
  `ED(representatives) ⟹ ED(presented planks)`, since the two presented planks are *equal*, and a
  set of positive finite volume is never essentially distinct from itself
  (`not_isEssentiallyDistinct_self`).

The second is the sharper statement: it says that the clause the consumer actually needs is not
recoverable from the datum's own essential-distinctness hypothesis by any argument, so a presented
outer family owes that clause an **extraction** (the tree's tool is
`Kakeya.exists_pairwise_plank_subset_of_isThickeningNonconcentrated`, whose non-concentration input
is not supplied by `Kakeya.Section6PartBData`), not a transport.

Nothing here is specific to the ratio `Kakeya.comparablePlankEnvelope.shrink (windowConst R Cw)`:
the witness never computes the homothety.  It only uses that the presentation is a function of the
body.  The quantitative statement — that *every* position-shrinking presentation breaks essential
distinctness, because the borderline pair at transverse separation exactly `a` is essentially
distinct before the shrink and not after — is not needed for the refutation and is not claimed here.

## What the presented family owes instead, and with what

The clause `Kakeya.factoringAndMultPropGlobal` now exports is the outer family's own pairwise
essential distinctness.  For a homothety-presented family that is an **extraction**, and every step
of it except one is already proved in this library:

* the extraction itself — `Kakeya.exists_pairwise_plank_subset_of_isThickeningNonconcentrated`, or
  its refinement form `Kakeya.exists_pairwise_plank_CRefinement_of_isThickeningNonconcentrated`,
  which returns the retained subfamily together with a
  `ShadedBody.IsCRefinement` of coefficient `(d + 1)⁻¹`;
* the fullness of the retained subfamily — `Kakeya.mul_fullness_le_of_isCRefinement`;
* the multiplicity comparison back to the full family —
  `ShadedBody.multiplicity_le_of_isCRefinement`;
* Katz--Tao, the window containment and the cardinality clause restrict to a subset for free.

What is **missing** is the extraction's own hypothesis,
`Plank.IsThickeningNonconcentrated ts (fun x => (W x).toPrism3D) C_NC (C * (b / a))`: a
conflict-degree count for the presented planks.  `Kakeya.Section6PartBData` carries no such datum —
its cell data are `body`, `cellOf`, `repr`, `body_le_repr`, `repr_window`,
`coarse_fibre_frostman`, `isKatzTao`, and nothing that separates two cells — and the refutations
below say the count cannot be manufactured from the datum's essential distinctness of the
representatives.  The tree's engine for such counts,
`Kakeya.exists_ED_directionCap_degree_bound` (used by
`Kakeya.exists_inner_plank_conflict_degree_bound` for the *inner* family), is stated for a family of
`Tube δ E`s at a single radius `δ`, with a direction cap of radius `A · δ` and a container of
volume at most `M · δ ^ (finrank - 1)`; an `a × b × 1` plank family has two transverse widths and is
not an instance of it.  Part (A) faced the same obstruction and resolved it by making the count an
explicit hypothesis of its proposition, `Kakeya.ParentOverlapAtDilatedPlanks`, converted by
`Kakeya.isThickeningNonconcentrated_of_parentOverlapAtDilatedPlanks`; that is the precedent for what
Part (B) will need, and whether the Main-Lemma-2 call site
(`Kakeya.ML2Reduction.exists_threshold_eccentric`) can supply it is not settled here.

## Fidelity

The clause that replaced the identification in `Kakeya.factoringAndMultPropGlobal` is the pairwise
essential distinctness of the outer family itself.  It is **weaker**:
`Kakeya.pairwise_isEssentiallyDistinct_of_toPrism3D_eq` derives it from the identification together
with the datum's hypothesis on the representatives, so every producer of the old form produces the
new one, and the top-level statements of Proposition 6.6(B)
(`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` and
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_of_masterScaleLemma61`) are unchanged.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Metric
open scoped ENNReal NNReal

noncomputable section

namespace Kakeya

/-! ### The witness family, and the two refutations -/

namespace CollarPlankRefute


abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-! ### The mechanism: the presented plank sees the body and nothing else -/


/-- The common cell body: the quarter-scale prism with the same frame, centred at the origin. -/
def cellBody (a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1) :
    Prism3D (a / 4) (b / 4) (1 / 4)
      (by exact div_le_div_of_nonneg_right hab (by norm_num))
      (by exact div_le_div_of_nonneg_right hb1 (by norm_num)) where
  toPrismNDim := PrismNDim.mk' (0 : E3) (EuclideanSpace.basisFun (Fin 3) ℝ) ![a / 4, b / 4, 1 / 4]
  thicknesses_eq := rfl


variable {a b : ℝ≥0}

/-- The two representative planks are the standard-frame `a × b × 1` planks centred at
`± (a / 2) e₀`. -/
def refCentre (t : ℝ) : E3 := EuclideanSpace.single (0 : Fin 3) t

@[simp] theorem refCentre_apply_zero (t : ℝ) : refCentre t 0 = t := by
  simp [refCentre]

@[simp] theorem refCentre_apply_one (t : ℝ) : refCentre t 1 = 0 := by
  simp [refCentre]

@[simp] theorem refCentre_apply_two (t : ℝ) : refCentre t 2 = 0 := by
  simp [refCentre]


end CollarPlankRefute
end Kakeya

end

end

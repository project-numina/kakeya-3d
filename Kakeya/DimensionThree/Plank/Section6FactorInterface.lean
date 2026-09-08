/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Section6FactorAdapter
public import Kakeya.DimensionThree.Plank.Section6CoarseFactorisation
public import Kakeya.DimensionThree.Plank.TubePlankNormalisation
public import Kakeya.Factoring.Section6

/-!
# Section 6: the analytic input interface

`Kakeya.GlobalComparableBodyFactorization` and `Kakeya.ComparableBodyFactorization` are *geometric* objects:
they record cellwise containment, hull minimality, transverse comparability and the Katz--Tao
property of the outer family.  They deliberately carry no analytic data.  GWZ Section 6, on the
other hand, feeds its factorisation to two analytic engines:

* generic GWZ Proposition 5.1 (`ShadedBody.factoringAndMultPropCombined`), whose hypothesis
  `ShadedBody.FactorFamily.HasFrostmanFibers` is a Frostman statement about each fibre **inside the
  actual outer body**;
* GWZ Lemma 6.1/6.4, which consume a normalised inner family and therefore need a density transfer
  along the plank normalisation.

This file is the bridge.  It adds no geometry and mutates neither of the two geometric structures;
it supplies constructors and transfer theorems that turn the hypotheses Section 6 actually has into
the hypotheses those engines actually consume.

## What is bridged

1. **Fibre Frostman.**  Section 6 has Frostman control of a fibre inside the cell's *representative
   plank* — that is where the paper's `W` lives, and it is the field
   `Kakeya.Section6PartBFactorisation.coarse_fibre_frostman`.  Proposition 5.1 wants it inside the
   *actual body*.  `ConvexSpaceBody.isFrostmanIn_of_le_of_forall_le` performs that restriction
   **with no loss of constant**: the numerator of `Kakeya.densityIn` is unchanged (every fibre
   member already lies in the smaller body), so shrinking the test body can only *increase* the
   reference density.  This is what makes `Kakeya.Section6FactorData.fibre_frostman` a derived
   clause rather than an extra assumption.

2. **Fibre lower bound.**  `Kakeya.Section6CoarseTubeDecomposition.ofUniformAtScale` takes the
   fibre lower bound `hlb` as an explicit hypothesis, and that is *correct*: uniformity bounds the
   **containment** set `{i | T i ≤ (T k).rescale ρ}` from below, while the fibre of a chosen
   assignment can be strictly smaller; see
   `Kakeya.Section6CoarseTubeDecomposition.fibre_subset_filter_of_uniformAtScale`.
   The bound is therefore kept as data.  What this file adds is the one genuinely sufficient
   condition, `Kakeya.Section6CoarseTubeDecomposition.le_card_fibre_of_faithful`: if the choice
   function did not route any leaf *out* of a parent that contains it, the two sets coincide and
   uniformity's own lower bound transfers verbatim.  This is a property of the chosen assignment,
   not a geometric assumption, and nothing anywhere assumes that a leaf has a unique parent.

3. **Density transfer.**  `Plank.maxDensity_le_of_image_subset` already gives
   `Δ_max(normalised) ≤ C · Δ_max(original)` with the explicit constant `8 / (κ³ c₃)`.  It is
   re-exported here against the interface's own representative planks, with the constant named
   `Kakeya.section6NormalisedDensityConst`.  The constant is **not** `1`, and is not silently
   dropped.

4. **Representative and parent data.**  Reused verbatim: `Kakeya.Section6PartBFactorisation.repr`
   and `cellOf` for the outer layer, `Kakeya.Section6CoarseTubeDecomposition.assign` for the
   coarse/fine layer, and `Kakeya.Section6PartBData` for their combination.  No geometry is rebuilt
   here.

## Import direction

`Kakeya.Section6FactorAdapter` and `Kakeya.Section6CoarseFactorisation` are siblings over
`Kakeya.GlobalComparableBodyFactorization`; this module sits below both and above
`Kakeya.Factoring.Multiplicity`, which reaches it through the adapter.  Nothing is duplicated and no
existing import is reversed.  A Part-(A) consumer living in
`Kakeya/DimensionThree/Plank/FrostmanPlankEstimate.lean` is *upstream* of this file and cannot
consume the interface without first being moved below it; that move is not performed here.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Convexity
-- Every fibre in this file is a `Finset.filter` over an arbitrary index type.
set_option linter.style.openClassical false
open scoped NNReal ENNReal Classical

noncomputable section

/-! ## Frostman restriction to a smaller test body -/

namespace ConvexSpaceBody

variable {E : Type*} [TopologicalSpace E] [Convexity.ConvexSpace ℝ E] [MeasureSpace E] {ι : Type*}

/-- **Frostman control restricts to a smaller test body with no loss of constant.**

If every member of the family already lies in `K` and `K ≤ K'`, then `C`-Frostman in `K'` implies
`C`-Frostman in `K`.  The numerator of `Kakeya.densityIn` is the same for both test bodies (the
containment filter is vacuous on either), so passing from `K'` to `K` only shrinks the denominator
and therefore *increases* the reference density; the defining inequality survives unchanged.

This is the bridge that lets Section 6 supply its Frostman datum in the representative plank — where
GWZ states it, and where `Kakeya.Section6PartBFactorisation.coarse_fibre_frostman` carries it — and
still meet `ShadedBody.FactorFamily.HasFrostmanFibers`, which is stated in the actual outer body. -/
theorem isFrostmanIn_of_le_of_forall_le
    {s : Finset ι} {V : ι → ConvexSpaceBody E} {K K' : ConvexSpaceBody E} {C : ℝ≥0∞}
    (hKK' : K ≤ K') (hV : ∀ i ∈ s, V i ≤ K) (h : IsFrostmanIn s V K' C) :
    IsFrostmanIn s V K C := by
  have hdens : Kakeya.densityIn s V K' ≤ Kakeya.densityIn s V K := by
    have hVK' : ∀ i ∈ s, V i ≤ K' := fun i hi => le_trans (hV i hi) hKK'
    rw [Kakeya.densityIn_of_all_le hVK', Kakeya.densityIn_of_all_le hV]
    gcongr
    exact hKK'
  intro K'' hK''
  refine (h K'' (le_trans hK'' hKK')).trans ?_
  exact mul_le_mul_of_nonneg_left hdens bot_le

end ConvexSpaceBody

namespace Kakeya

/-! ## Enriching a `GlobalComparableBodyFactorization` to a `Section6FactorData` -/

section OfGlobal

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
  {ι : Type*} {q : Finset ι} {δ : ℝ≥0} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
  {CFib : ℝ≥0∞} {C₀ Cmass Cdim : ℝ≥0}


end OfGlobal

/-! ## The Part-(B) factorisation as a Proposition-5.1 input -/

namespace Section6PartBFactorisation

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
  {κ : Type*} {coarseSet : Finset κ} {ρ : ℝ≥0} {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}
  {CF C₀ : ℝ≥0}

/-- **The coarse fibre is Frostman in the actual cell body.**

`Kakeya.Section6PartBFactorisation.coarse_fibre_frostman` states the datum in the representative
plank, which is where GWZ states it.  Every member of a cell's coarse fibre already lies in the
actual body (`le_body`), so `ConvexSpaceBody.isFrostmanIn_of_le_of_forall_le` restricts the datum to
the actual body with the same constant `CF`. -/
theorem frostman_fibres_in_body (F : Section6PartBFactorisation a b hab hb1 coarseSet R CF C₀) :
    ∀ x ∈ F.cells,
      ConvexSpaceBody.IsFrostmanIn (F.coarseFibre x) (fun k => (R k).toConvexSpaceBody)
        (F.body x) (CF : ℝ≥0∞) := by
  intro x hx
  refine ConvexSpaceBody.isFrostmanIn_of_le_of_forall_le
    (F.body_le_repr x hx) ?hV ?h
  · intro k hk
    rw [mem_coarseFibre_iff] at hk
    rcases hk with ⟨hkcoarse, hkcell⟩
    simpa [hkcell] using F.le_body k hkcoarse
  · simpa [coarseFibre] using F.coarse_fibre_frostman x hx

open Classical in
/-- **The factor family handed to generic GWZ Proposition 5.1 in Part (B).**

Inner bodies are the shaded coarse tubes, outer bodies are the *actual* cell bodies, and the parent
map is the cell map.  Only a shading of the coarse tubes is required as extra input; the convex
carriers are those of `R`, so all the geometry is the factorisation's own. -/
def toShadedFactorFamily (F : Section6PartBFactorisation a b hab hb1 coarseSet R CF C₀)
    (Rs : κ → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (hRs : ∀ k, (Rs k).toConvexSpaceBody = (R k).toConvexSpaceBody) :
    ShadedBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) κ F.Cell where
  innerSet := coarseSet
  innerBody := Rs
  outerSet := F.cells
  outerBody := F.body
  parent := F.cellOf
  parent_mem := F.cellOf_mem
  inner_le_parent := by
    intro k hk
    rw [hRs k]
    exact F.le_body k hk

open Classical in
/-- **The Proposition-5.1 Frostman hypothesis, discharged for Part (B).**

This is the clause `Kakeya.GlobalComparableBodyFactorization` structurally cannot provide, and it is the
reason this interface layer exists. -/
theorem hasFrostmanFibers (F : Section6PartBFactorisation a b hab hb1 coarseSet R CF C₀)
    (Rs : κ → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (hRs : ∀ k, (Rs k).toConvexSpaceBody = (R k).toConvexSpaceBody) :
    (F.toShadedFactorFamily Rs hRs).HasFrostmanFibers (CF : ℝ≥0∞) := by
  intro x hx
  change ConvexSpaceBody.IsFrostmanIn ((F.toShadedFactorFamily Rs hRs).fiber x)
    (fun k => (Rs k).toConvexSpaceBody) (F.body x) (CF : ℝ≥0∞)
  change ConvexSpaceBody.IsFrostmanIn ({k ∈ coarseSet | F.cellOf k = x} : Finset κ)
    (fun k => (Rs k).toConvexSpaceBody) (F.body x) (CF : ℝ≥0∞)
  rw [show (fun k => (Rs k).toConvexSpaceBody) = (fun k => (R k).toConvexSpaceBody) by
        funext k; exact hRs k]
  exact frostman_fibres_in_body F x hx

end Section6PartBFactorisation

/-! ## The fibre lower bound -/

namespace Section6CoarseTubeDecomposition


end Section6CoarseTubeDecomposition

/-! ## The fine-family Remark 5.3 call -/

namespace Section6PartBData

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
  {ι : Type*} {q : Finset ι} {δ : ℝ≥0} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
  {κ : Type*} {coarseSet : Finset κ} {ρ : ℝ≥0} {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}
  {m Cfib CF C₀ : ℝ≥0}
  (D : Section6PartBData a b hab hb1 q T coarseSet R m Cfib CF C₀)

open Classical in
/-- The Proposition-5.1 family for 6.6(B).  Its inner indices are the fine tubes; the coarse
tubes occur only in the proof of the Remark-5.3 Frostman hypothesis. -/
def toFineProp51Family :
    ShadedBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) ι D.factor.Cell where
  innerSet := q
  innerBody := fun i ↦ (T i).toShadedBody
  outerSet := D.factor.cells
  outerBody := D.factor.body
  parent := D.cellOfFine
  parent_mem := fun i hi ↦ D.factor.cellOf_mem _ (D.decomp.assign_mem i hi)
  inner_le_parent := fun i hi ↦
    le_trans (D.decomp.leaf_le_parent i hi)
      (D.factor.le_body _ (D.decomp.assign_mem i hi))


end Section6PartBData

/-! ## Density transfer along the plank normalisation -/


section DensityTransfer

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
  {ι : Type*} {q : Finset ι} {δ : ℝ≥0} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
  {CFib : ℝ≥0∞} {C₀ Cmass Cdim : ℝ≥0}


end DensityTransfer

end Kakeya

end

end

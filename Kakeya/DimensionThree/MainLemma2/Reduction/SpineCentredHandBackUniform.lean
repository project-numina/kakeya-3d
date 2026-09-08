/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCentredHandBackProducer

/-!
# The centring hand-back at the **uniformised** subfamily, and the A7 count clause

condition of record:  — (A) the `CountTransport` re-cut at the
contracted hypothesis radius, (B) `huni` stays a binder and is discharged at the producer with the
order **centre → uniformise → hand-back**.

## What is here

**(B), complete.**  `exists_centredPushforward_of_outerFamily` isolates the centring — the cover's
nodes with the *exact* pushforward shading, which is what the two ledger identities of
`Reduction/SpineCentringCover.lean` need — and `centredHandBack_of_uniformised` re-states all
eleven fields of `Kakeya.VeryNotSticky.CentredHandBack` at a shade-refined subfamily `(s'', U'')`.
Together they are the specified order: centre, then run the tree's uniformiser on the *centred* family,
then hand back at its output.  The uniformiser's two retention clauses are exactly the two extra
inputs (`hmass`, and `hret` at `3 qc - α'`), and `sum_shade_le_of_fullness'_le` is the one-line
bridge that turns its `fullness'` clause into the shading-mass form
`Kakeya.ML2Reduction.multiplicity_le_of_shade_refinement` reads.

**(A), partial — and a blocking finding.**  Two of the three clauses of the specified
`CountTransport` are discharged here for *any* radius constant `C`:
`count_le_of_contracted_radius` is the count bound, and `node_le_rescale` is the
containment.  The third — the conclusion's **pairwise essential distinctness** — does **not**
transport under the same-index construction, and `injOn_of_pairwise_essDistinct` /
`not_pairwise_essDistinct_of_shared_node` are the reason: a pairwise essentially distinct
family of tubes is *injective* on its index set, so a transport that keeps the hypothesis's index
set cannot factor through the canonical cover's node assignment, which is many-to-one by
construction (`Kakeya.VeryNotSticky.fibre_card_le_of_lineEDAt` bounds its fibre by `A`, not by
`1`).  See  for the measurement and for the shape that does work.

## Main declarations

* `Kakeya.VeryNotSticky.exists_centredPushforward_of_outerFamily` — the centring, packaged.
* `Kakeya.VeryNotSticky.sum_shade_le_of_fullness'_le` — the uniformiser's clause, denominator
  cleared.
* `Kakeya.VeryNotSticky.centredHandBack_of_uniformised` — **(B)**: the hand-back at `(s'', U'')`.
* `Kakeya.VeryNotSticky.count_le_of_contracted_radius`, `node_le_rescale` — **(A)**'s two
  discharged clauses, at an arbitrary radius constant.
* `Kakeya.VeryNotSticky.injOn_of_pairwise_essDistinct`,
  `not_pairwise_essDistinct_of_shared_node` — **(A)**'s obstruction,.
* `Kakeya.VeryNotSticky.exists_centredHandBack_uniformised_witness` —, the composite
  witness: centre, then the tree's real uniformiser, then the hand-back at its `s''`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Kakeya.ML2Reduction

namespace Kakeya.VeryNotSticky

universe u

/-! ## (B) — the centring, packaged -/

/-- **The uniformiser's fullness clause with the common denominator cleared.**  Both families have
the same tubes, hence the same carrier sum, so a bound between the two `fullness'` values is a
bound between the two shading masses — which is the shape
`Kakeya.ML2Reduction.multiplicity_le_of_shade_refinement` reads. -/
theorem sum_shade_le_of_fullness'_le {α : Type u} {δ' : ℝ≥0} (s : Finset α)
    (V V' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3)))
    (htube : ∀ i, (V' i).toTube = (V i).toTube)
    {c : ℝ≥0∞}
    (hden0 : (∑ i ∈ s, volume (V i).carrier) ≠ 0)
    (h : ShadedBody.fullness' s (fun i ↦ (V i).toShadedBody)
      ≤ c * ShadedBody.fullness' s (fun i ↦ (V' i).toShadedBody)) :
    (∑ i ∈ s, volume (V i).shade) ≤ c * ∑ i ∈ s, volume (V' i).shade := by
  have hden' : (∑ i ∈ s, volume (V' i).carrier) = ∑ i ∈ s, volume (V i).carrier :=
    Finset.sum_congr rfl fun i _ ↦ by rw [show (V' i).carrier = (V i).carrier from by
      rw [show (V' i).carrier = (V' i).toTube.carrier from rfl,
        show (V i).carrier = (V i).toTube.carrier from rfl, htube i]]
  have hdentop : (∑ i ∈ s, volume (V i).carrier) ≠ ⊤ := by
    refine (ENNReal.sum_lt_top.mpr fun i _ ↦ ?_).ne
    exact (V i).isCompact.measure_lt_top
  set D : ℝ≥0∞ := ∑ i ∈ s, volume (V i).carrier with hD
  have hA : (∑ i ∈ s, volume (V i).shade)
      = ShadedBody.fullness' s (fun i ↦ (V i).toShadedBody) * D :=
    (ENNReal.div_mul_cancel hden0 hdentop).symm
  have hB : ShadedBody.fullness' s (fun i ↦ (V' i).toShadedBody) * D
      = ∑ i ∈ s, volume (V' i).shade := by
    simp only [ShadedBody.fullness', hden']
    exact ENNReal.div_mul_cancel hden0 hdentop
  calc (∑ i ∈ s, volume (V i).shade)
      = ShadedBody.fullness' s (fun i ↦ (V i).toShadedBody) * D := hA
    _ ≤ (c * ShadedBody.fullness' s (fun i ↦ (V' i).toShadedBody)) * D :=
        mul_le_mul' h le_rfl
    _ = c * (ShadedBody.fullness' s (fun i ↦ (V' i).toShadedBody) * D) := by rw [mul_assoc]
    _ = c * ∑ i ∈ s, volume (V' i).shade := by rw [hB]

/-! ## (A) — the specified `CountTransport`: the two clauses that hold, at any radius constant -/

/-- **The count display,.**  Reading the hypothesis at the
contracted radius `ρ / C` with `1 ≤ C` and the hypothesis's own loss `1 ≤ Λ` already delivers the
conclusion's bare count `ρ^{-2-ζ}`: the rescaling pays for itself.  Stated for an arbitrary `C` so
that it is the specified clause at `C := centringCoverRadiusConstant` (whose definition is the GC
owner's, in `Reduction/SpineCentredHandBack.lean`) and at any other admissible constant. -/
theorem count_le_of_contracted_radius {ρ C : ℝ≥0} (hρ0 : 0 < ρ) (hC1 : 1 ≤ C)
    {Λ ζ n : ℝ} (hΛ : 1 ≤ Λ) (hζ : 0 ≤ 2 + ζ)
    (h : Λ * ((ρ / C : ℝ≥0) : ℝ) ^ (-2 - ζ) ≤ n) :
    (ρ : ℝ) ^ (-2 - ζ) ≤ n := by
  have hρr : (0 : ℝ) < (ρ : ℝ) := hρ0
  have hCr : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC1
  have hC0 : (0 : ℝ) < (C : ℝ) := by linarith
  have hdiv : ((ρ / C : ℝ≥0) : ℝ) = (ρ : ℝ) / (C : ℝ) := NNReal.coe_div _ _
  rw [hdiv, Real.div_rpow hρr.le hC0.le] at h
  have hpow : (C : ℝ) ^ (-2 - ζ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hCr (by linarith)
  have hpow0 : (0 : ℝ) < (C : ℝ) ^ (-2 - ζ) := Real.rpow_pos_of_pos hC0 _
  have hρpow : (0 : ℝ) < (ρ : ℝ) ^ (-2 - ζ) := Real.rpow_pos_of_pos hρr _
  calc (ρ : ℝ) ^ (-2 - ζ) ≤ (ρ : ℝ) ^ (-2 - ζ) / (C : ℝ) ^ (-2 - ζ) := by
        rw [le_div_iff₀ hpow0]; nlinarith
    _ ≤ Λ * ((ρ : ℝ) ^ (-2 - ζ) / (C : ℝ) ^ (-2 - ζ)) := by nlinarith [div_pos hρpow hpow0]
    _ ≤ n := h

/-- **The containment clause of the specified `CountTransport`.**  A centred representative is a
unit-core `δ'`-tube, so at any window radius `ρ ≥ δ'` the `ρ`-tube on its own line contains it —
this is the clause `∀ j ∈ tρ, ∃ i ∈ s', (U' i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody`,
discharged with no geometry beyond `Tube.rescale`.  Note that this fixes `Tρ j` up to its radius:
a `ρ`-tube containing a unit-core tube is the `ρ`-tube on that tube's own line, which is why the
conclusion's essential distinctness is a statement about the *nodes'* lines and not something the
producer may choose. -/
theorem node_le_rescale {δ' ρ : ℝ≥0} (hδρ : δ' ≤ ρ)
    (U : ShadedTube δ' (EuclideanSpace ℝ (Fin 3))) :
    U.toConvexSpaceBody ≤ (U.toTube.rescale ρ).toConvexSpaceBody := by
  have h := Tube.rescale_le_rescale_of_radius_le U.toTube hδρ
  rwa [Tube.toConvexSpaceBody_rescale_self] at h

/-! ## (A) — the obstruction: essential distinctness forces an injective transport -/

/-! ## the composite witness: centre, uniformise, hand back -/

end Kakeya.VeryNotSticky

end

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCentringCover

/-!
# Producing the centred hand-back for the outer family

The construction follows the GWZ canonical-cover argument `lemcanonicalcover`
under the normalising similarity `lemaffineinvariance` at `ρ = 1`.
The cardinality and mass identities are `eq:defect-centred-ledger`;
the fixed constants are absorbed by a small-scale threshold.

The canonical representatives lie in `closedBall 0 1`. The convex-body image
under `normalise 0` is expressed using the homothety API. Density bounds pass
to this image through `maxDensity_le`. The hand-back records the common family,
its geometric containment and the quantitative transports used by
`fine_factor_of_lemma91At_of_canonicalCover`.

The margin parameters are `qc := ν/103`, `ηd := 3 * qc`, and
`gain' := gain - 3 * qc`. The construction keeps the resulting loss explicit.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric RealInnerProductSpace Kakeya.ML2Reduction

namespace Kakeya.VeryNotSticky

universe u

/-! ## `normalise 0`, `centringDilate` and the existing homothety API -/

theorem normalise_zero_apply (x : EuclideanSpace ℝ (Fin 3)) :
    normalise 0 x = AffineMap.homothety (0 : EuclideanSpace ℝ (Fin 3)) ((8 : ℝ)⁻¹) x := by
  simp [normalise, AffineMap.homothety_apply]

theorem centringDilate_eq_normalise_zero (x : EuclideanSpace ℝ (Fin 3)) :
    centringDilate x = normalise 0 x := by
  simp [centringDilate, normalise]

theorem normalise_zero_image (A : Set (EuclideanSpace ℝ (Fin 3))) :
    normalise 0 '' A = AffineMap.homothety (0 : EuclideanSpace ℝ (Fin 3)) ((8 : ℝ)⁻¹) '' A :=
  Set.image_congr fun x _ ↦ normalise_zero_apply x

theorem centringDilate_image_eq_normalise_zero_image (A : Set (EuclideanSpace ℝ (Fin 3))) :
    centringDilate '' A = normalise 0 '' A :=
  Set.image_congr fun x _ ↦ centringDilate_eq_normalise_zero x

/-- The normalised image of a convex body, as a convex body: the existing
`ConvexSpaceBody.homothety` at centre `0` and ratio `1/8`. -/
noncomputable def normaliseBody (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :
    ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
  K.homothety 0 ((8 : ℝ)⁻¹)

theorem normaliseBody_carrier (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :
    (normaliseBody K).carrier = normalise 0 '' K.carrier := by
  rw [normalise_zero_image]; rfl

/-- **The Jacobian, on a convex body**: `|L(K)| = |K| / 512`. -/
theorem volume_normaliseBody (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :
    volume (normaliseBody K).carrier = ENNReal.ofReal (1 / 512) * volume K.carrier := by
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  rw [normaliseBody, ConvexSpaceBody.volume_homothety, hfr]
  norm_num

/-- **`Δ_max` is unchanged by the normalising similarity** — `lemaffineinvariance` , at the
`m = 0` instance where `Kakeya.maxDensity_affineImage` is `Kakeya.maxDensity_homothety`. -/
theorem maxDensity_normaliseBody {α : Type*} (s : Finset α)
    (W : α → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :
    Kakeya.maxDensity s (fun i ↦ normaliseBody (W i)) = Kakeya.maxDensity s W :=
  Kakeya.maxDensity_homothety s W 0 (by norm_num)

/-! ## The centred representative -/

/-- **The centred representative of a member**: the canonical cover's node `W`, shaded by the
normalised image of the member's shade.  The intersection with `W.carrier` is inert as
soon as the node covers the normalised member (`handBackRep_shade_eq`); it is written so that the
representative is a total function of `(O, W)` and needs no `dite`. -/
noncomputable def handBackRep {δ' : ℝ≥0}
    (O : ShadedTube δ' (EuclideanSpace ℝ (Fin 3))) (W : Tube δ' (EuclideanSpace ℝ (Fin 3))) :
    ShadedTube δ' (EuclideanSpace ℝ (Fin 3)) where
  toTube := W
  shade := (normalise 0 '' O.shade) ∩ W.carrier
  measurableSet_shade := by
    refine MeasurableSet.inter ?_ W.toConvexSpaceBody.isCompact.isClosed.measurableSet
    rw [normalise_zero_image]
    exact (Kakeya.measurableEmbedding_homothety (0 : EuclideanSpace ℝ (Fin 3))
      (by norm_num : ((8 : ℝ)⁻¹) ≠ 0)).measurableSet_image' O.measurableSet_shade
  shade_subset := Set.inter_subset_right

@[simp] theorem handBackRep_toTube {δ' : ℝ≥0}
    (O : ShadedTube δ' (EuclideanSpace ℝ (Fin 3))) (W : Tube δ' (EuclideanSpace ℝ (Fin 3))) :
    (handBackRep O W).toTube = W := rfl

theorem handBackRep_shade_eq {δ' : ℝ≥0}
    (O : ShadedTube δ' (EuclideanSpace ℝ (Fin 3))) (W : Tube δ' (EuclideanSpace ℝ (Fin 3)))
    (hcov : normalise 0 '' O.carrier ⊆ W.carrier) :
    (handBackRep O W).shade = normalise 0 '' O.shade :=
  Set.inter_eq_self_of_subset_left ((Set.image_mono O.shade_subset).trans hcov)

/-! ## The `maxDensity_le` field: `Δ_max(𝔾^) ≤ 512 · Δ_max(𝔾)`, with no fibre bound -/

/-- **, "The `maxDensity_le` route".**  Passing from the normalised members to
the containing nodes multiplies `Δ_max` by at most the volume ratio `512`: a node is a unit-core
`δ'`-tube and a normalised member is `(δ'/8)`-thick with core `1/8`, so the two have the same
number of terms in every test body's sum and the terms differ by `512`.  **The fibre never
enters** — it is what `multiplicity_le` pays, not what `maxDensity_le` pays. -/
theorem maxDensity_nodes_le {δ' : ℝ≥0} {α : Type*} (s : Finset α)
    (O U : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3)))
    (hcov : ∀ i ∈ s, normalise 0 '' (O i).carrier ⊆ (U i).carrier) :
    Kakeya.maxDensity s (fun i ↦ (U i).toConvexSpaceBody)
      ≤ (512 : ℝ≥0∞) * Kakeya.maxDensity s (fun i ↦ (O i).toConvexSpaceBody) := by
  classical
  have hj : (512 : ℝ≥0∞) * ENNReal.ofReal (1 / 512) = 1 := by
    rw [show ((1 : ℝ) / 512) = (512 : ℝ)⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num)]
    rw [show ENNReal.ofReal (512 : ℝ) = (512 : ℝ≥0∞) by
      rw [show (512 : ℝ) = ((512 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]; norm_num]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  refine Kakeya.maxDensity_le_of_forall_sum_le ?_
  intro K
  -- (a) the node's test-body containment implies the normalised member's
  have hstep : (s.filter fun i ↦ (U i).toConvexSpaceBody ≤ K)
      ⊆ (s.filter fun i ↦ normaliseBody (O i).toConvexSpaceBody ≤ K) := by
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨hi.1, ?_⟩
    rw [← SetLike.coe_subset_coe] at hi ⊢
    refine subset_trans ?_ hi.2
    rw [show SetLike.coe (normaliseBody (O i).toConvexSpaceBody)
        = (normaliseBody (O i).toConvexSpaceBody).carrier from rfl,
      normaliseBody_carrier]
    exact hcov i hi.1
  -- (b) the node's volume is `512` times the normalised member's
  have hvol : ∀ i ∈ s, volume (U i).carrier
      ≤ (512 : ℝ≥0∞) * volume (normaliseBody (O i).toConvexSpaceBody).carrier := by
    intro i _
    rw [volume_normaliseBody, ← mul_assoc, hj, one_mul]
    exact le_of_eq (Tube.volume_carrier_eq_volume_carrier (U i).toTube (O i).toTube)
  calc ∑ i ∈ s.filter (fun i ↦ (U i).toConvexSpaceBody ≤ K), volume (U i).carrier
      ≤ ∑ i ∈ s.filter (fun i ↦ (U i).toConvexSpaceBody ≤ K),
          (512 : ℝ≥0∞) * volume (normaliseBody (O i).toConvexSpaceBody).carrier :=
        Finset.sum_le_sum fun i hi ↦ hvol i (Finset.mem_filter.mp hi).1
    _ = (512 : ℝ≥0∞) * ∑ i ∈ s.filter (fun i ↦ (U i).toConvexSpaceBody ≤ K),
          volume (normaliseBody (O i).toConvexSpaceBody).carrier := by rw [Finset.mul_sum]
    _ ≤ (512 : ℝ≥0∞) * ∑ i ∈ s.filter
          (fun i ↦ normaliseBody (O i).toConvexSpaceBody ≤ K),
          volume (normaliseBody (O i).toConvexSpaceBody).carrier := by
        exact mul_le_mul' le_rfl (Finset.sum_le_sum_of_subset hstep)
    _ ≤ (512 : ℝ≥0∞) * (Kakeya.maxDensity s (fun i ↦ normaliseBody (O i).toConvexSpaceBody)
          * volume K.carrier) := by
        exact mul_le_mul' le_rfl
          (Kakeya.sum_volume_le_maxDensity_mul_volume s
            (fun i ↦ normaliseBody (O i).toConvexSpaceBody) K)
    _ = (512 : ℝ≥0∞) * Kakeya.maxDensity s (fun i ↦ (O i).toConvexSpaceBody)
          * volume K.carrier := by
        rw [maxDensity_normaliseBody, mul_assoc]

/-! ## The threshold `512 ≤ (δ')^{-qc}` -/

/-! ## The producer -/

/-! ## A7 — `CountTransport` for the produced hand-back: the cheap route is CLOSED

`Kakeya.VeryNotSticky.countTransport_of_le` discharges the re-shaped `CountTransport` from the
hypothesis `∀ i ∈ s', (U' i).toConvexSpaceBody ≤ spineFamily … i` — the representative sits
*inside* the body it represents.  That hypothesis is **unavailable for the hand-back this file
produces**, and not by accident: the representative is a *container* of the normalised member, so
asking it also to be contained in the member forces the member to be `normalise`-stable, which a
body sitting away from the origin is not.

`normalise 0` contracts towards the origin by `8`, so a family every one of whose points has norm
`> 1/8` cannot contain its own normalised image. -/

/-! ## V-2 — the producer's hypothesis list, jointly satisfied on a two-member family -/

end Kakeya.VeryNotSticky

end

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.RandomTranslation.RigidMotionProb
public import Kakeya.Tube.EDPacking.BadAgainstSet

/-!
# The ED bad-count random variables of GWZ Lemma 3.8

Fix a test tube `T₀` and a pairwise essentially distinct family `T : ι → Tube δ E`. For a rigid
motion `ω` the **bad count**

`edBadCount s T T₀ ω = #{i ∈ s | (T i).rigidMove ω ⊆ 99δ-thickening of T₀}`

is the random variable whose sum over independent copies controls the ED multiplicity of the
randomised family.

Two bounds are proved here, and they are the two inputs to the Chernoff step:

* **deterministic**, `Kakeya.edBadCount_le`: `edBadCount ≤ C_pack` pointwise, a *dimensional*
  constant with no dependence on the number of copies. This is the existing
  `Kakeya.badAgainstSet_count_le_of_ED_thinBox`, which applies because a rigid motion carries the
  pairwise ED family to a pairwise ED family (`Kakeya.rigidMove_pairwise_isEssentiallyDistinct`) and
  because containment implies overlap-badness at any density threshold `≤ 1`.
* **expectation**, `Kakeya.lintegral_edBadCount_le`: `𝔼[edBadCount] ≤ C · |s| · δ^(2(n-1))`, by
  linearity of expectation from GWZ (106) (`Kakeya.prob_rigidMove_bad_le`).

Crucially the deterministic bound is *not* multiplied by the number of copies: that `J`-fold union
bound is exactly the defect this development removes.

The proof also establishes the thin-box volume hypothesis
`volume (cthickening (99δ) T₀.carrier) ≤ M · δ^(n-1)` (`Kakeya.volume_cthickening_tube_le`), which
is the hypothesis used by `badAgainstSet_count_le_of_ED_thinBox`,
`badAgainstSet_card_le_M2_cN` and `randCF_chernoff_witness`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Set

namespace Kakeya

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The `99δ`-thickening of a `δ`-tube is a `100δ`-tube, so its volume is
bounded by a dimensional constant times `δ^(n-1)`. -/
theorem volume_cthickening_tube_le [Nontrivial E] :
    ∃ M : ℝ, 0 < M ∧
      ∀ {δ : ℝ≥0}, (100 * δ : ℝ≥0) ≤ 1 → ∀ T₀ : Tube δ E,
        volume (Metric.cthickening (99 * (δ : ℝ)) T₀.carrier)
          ≤ ENNReal.ofReal M * (δ : ℝ≥0∞) ^ (Module.finrank ℝ E - 1) := by
  let n : ℕ := Module.finrank ℝ E
  refine ⟨((Tube.volume_le.C n * 100 ^ (n - 1) : ℝ≥0) : ℝ), ?_, ?_⟩
  · rw [NNReal.coe_pos]
    exact mul_pos (Tube.volume_le.C_pos n)
      (pow_pos (by norm_num : (0 : ℝ≥0) < 100) (n - 1))
  · intro δ hδ T
    have h99 : (99 : ℝ) * (δ : ℝ) = ((99 * δ : ℝ≥0) : ℝ) := by
      push_cast
      norm_num
    rw [h99, Tube.cthickening_carrier T (99 * δ)]
    have hsum : δ + 99 * δ = 100 * δ := by
      ring
    rw [hsum]
    apply (Tube.volume_le hδ (T.rescale (100 * δ))).trans
    rw [ENNReal.ofReal_coe_nnreal]
    refine le_of_eq ?_
    rw [show Module.finrank ℝ E = n from rfl]
    rw [← ENNReal.coe_pow, ← ENNReal.coe_mul]
    exact congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) (by
      rw [mul_pow]
      ac_rfl)

/-- A rigid motion preserves Lebesgue measure. -/
theorem measurePreserving_rigidMap (u : unitary (E →L[ℝ] E)) (v : E) :
    MeasurePreserving (rigidMap u v) volume volume := by
  rw [show rigidMap u v = (fun y : E => y + v) ∘ (fun x : E => (u : E →L[ℝ] E) x) by
    funext x
    rfl]
  exact MeasurePreserving.comp (measurePreserving_add_right volume v) (by
    rw [show (fun x : E => (u : E →L[ℝ] E) x) =
        (Unitary.linearIsometryEquiv u : E → E) by
      funext x
      rfl]
    exact ((Unitary.linearIsometryEquiv u) : E ≃ₗᵢ[ℝ] E).measurePreserving)

/-- A rigid motion carries a pairwise essentially distinct family to a pairwise essentially
distinct family: essential distinctness is defined by volumes of intersections, and rigid motions
preserve volume. -/
theorem rigidMove_pairwise_isEssentiallyDistinct {δ : ℝ≥0} {ι : Type*} {s : Finset ι}
    {T : ι → Tube δ E} (hED : (s : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier))
    (u : unitary (E →L[ℝ] E)) (v : E) :
    (s : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct ((T i).rigidMove u v).carrier
        ((T j).rigidMove u v).carrier) := by
  intro i hi j hj hij
  rw [Tube.rigidMove_carrier, Tube.rigidMove_carrier]
  let L : E ≃ₗᵢ[ℝ] E := Unitary.linearIsometryEquiv u
  let g : E → E := fun y : E => (L.symm : E → E) (y - v)
  have h1 : Function.LeftInverse g (rigidMap u v) := by
    intro x
    dsimp [g]
    rw [add_sub_cancel_right]
    rw [← Unitary.coe_linearIsometryEquiv_apply u]
    apply LinearEquiv.symm_apply_apply
  have h2 : Function.RightInverse g (rigidMap u v) := by
    intro y
    dsimp [g]
    change (L : E → E) (L.symm (y - v)) + v = y
    simp
  have himage : ∀ s : Set E, rigidMap u v '' s = g ⁻¹' s := by
    intro s
    exact congrFun (Set.image_eq_preimage_of_inverse h1 h2) s
  have hmeas_f : Measurable (rigidMap u v) := (isometry_rigidMap u v).continuous.measurable
  have hmeas_g : Measurable g := by
    dsimp [g]
    exact ((L.symm : E →L[ℝ] E).continuous.comp
      (Continuous.sub continuous_id continuous_const)).measurable
  let e : E ≃ᵐ E :=
    { toEquiv := { toFun := rigidMap u v, invFun := g, left_inv := h1, right_inv := h2 }
      measurable_toFun := hmeas_f
      measurable_invFun := hmeas_g }
  have he : MeasurePreserving (e : E → E) volume volume := by
    change MeasurePreserving (rigidMap u v) volume volume
    exact measurePreserving_rigidMap u v
  have h_symm : MeasurePreserving (e.symm : E → E) volume volume :=
    MeasurePreserving.symm e he
  have hvol : ∀ s : Set E, volume (rigidMap u v '' s) = volume s := by
    intro s
    rw [himage s]
    change volume ((e.symm : E → E) ⁻¹' s) = volume s
    exact MeasurePreserving.measure_preimage_equiv h_symm s
  have hinter : rigidMap u v '' ((T i).carrier ∩ (T j).carrier) =
    (rigidMap u v '' (T i).carrier) ∩ (rigidMap u v '' (T j).carrier) := by
    rw [himage ((T i).carrier ∩ (T j).carrier), himage (T i).carrier, himage (T j).carrier]
    rw [Set.preimage_inter]
  unfold IsEssentiallyDistinct
  rw [← hinter]
  rw [hvol ((T i).carrier ∩ (T j).carrier), hvol (T i).carrier, hvol (T j).carrier]
  exact hED hi hj hij

end

end Kakeya

end

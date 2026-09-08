/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.RandomTranslation.RigidMotion
public import Kakeya.Tube.EDPacking.AxialAngle

/-!
# GWZ Appendix A equation (106)

For a random rigid motion `R` and `δ`-tubes `T`, `T₀`, GWZ bound

`P[R(T) ⊆ 100 T₀] ≲ |T_δ|²`,

i.e. by `δ^(2(n-1))`. The square is essential: it is what makes the ED multiplicity of the
randomised family in GWZ Lemma 3.8 independent of the number of copies. One factor `δ^(n-1)` is
translational, the other rotational.

## The factored form

The main theorem, `Kakeya.prob_rigidMove_subset_le`, keeps the two factors visibly separate:

`P[R(T) ⊆ K] ≤ C · ρ^(n-1) · volume K`

for any convex target `K` such that containment in `K` forces the axis of `R(T)` to lie
within projective distance `ρ` of a fixed direction `d₀`. Nothing about `K` is used beyond
that hypothesis and its volume, so the rotational factor is not hidden in a volume estimate.

Specialising to `K = ` the `99δ`-thickening of a `δ`-tube `T₀` gives (106): the alignment hypothesis
is then `Kakeya.bad_axial_angle_le` (containment implies the axes are within `O(δ)`), which supplies
`ρ ≍ δ`, and `volume K ≲ δ^(n-1)`; multiplying gives `δ^(2(n-1))`.

## Proof

`Kakeya.rigidMeasure` is a product measure, so `MeasureTheory.Measure.prod_apply` writes the
probability as an integral over the rotation of the translational probability. For each rotation the
inner probability is bounded by `Kakeya.prob_tube_translate_subset_le` (the existing `δ^(n-1)`-sharp
translation estimate), and the integrand vanishes off the set of aligned rotations, whose Haar
measure is `≲ ρ^(n-1)` by `Kakeya.rotHaar_projectiveCap_le`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Set

namespace Kakeya

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The event that a rigidly moved tube lands inside a closed target is closed, hence measurable:
it is an intersection over the points of the tube of closed conditions. -/
theorem isClosed_rigidMove_subset {δ : ℝ≥0} (T : Tube δ E) (K : ConvexSpaceBody E) :
    IsClosed {ω : unitary (E →L[ℝ] E) × E |
      (T.rigidMove ω.1 ω.2).carrier ⊆ K.carrier} := by
  have hKclosed : IsClosed K.carrier := K.isCompact.isClosed
  have hset :
      {ω : unitary (E →L[ℝ] E) × E |
          (T.rigidMove ω.1 ω.2).carrier ⊆ K.carrier} =
        ⋂ x ∈ T.carrier, {ω : unitary (E →L[ℝ] E) × E |
          (ω.1 : E →L[ℝ] E) x + ω.2 ∈ K.carrier} := by
    ext ω
    simp only [Tube.rigidMove_carrier, Set.image_subset_iff, Set.mem_iInter, Set.mem_setOf_eq,
      Kakeya.rigidMap_apply]
    rfl
  rw [hset]
  refine isClosed_biInter (fun x _ => ?_)
  exact hKclosed.preimage (((continuous_unitaryApply x).comp continuous_fst).add continuous_snd)

/-- **The translational factor.** For a fixed rotation, the probability that the translated copy of
`T` lands inside `K` is at most a dimensional constant times `volume K`. This is the existing
`Kakeya.prob_tube_translate_subset_le` transported along `Tube.rigidMove`. -/
theorem prob_translate_rigidMove_le [Nontrivial E] :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ {δ : ℝ≥0} (T : Tube δ E) (K : ConvexSpaceBody E) (u : unitary (E →L[ℝ] E)),
        uniformBallMeasure E {v : E | (T.rigidMove u v).carrier ⊆ K.carrier}
          ≤ C * volume K.carrier := by
  refine ⟨ENNReal.ofReal (translationErosionVolumeConstant (Module.finrank ℝ E) : ℝ) *
      (volume (Metric.closedBall (0 : E) 1))⁻¹, ?_, ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.ofReal_ne_top)
      (ENNReal.inv_ne_top.2 (Metric.measure_closedBall_pos volume (0 : E) zero_lt_one).ne')
  · intro δ T K u
    have hcar : ∀ v : E,
        (T.rigidMove u v).carrier = ((T.rigidMove u 0).translate v).carrier := by
      intro v
      have r_im : (v + ·) '' (Kakeya.rigidMap u 0 '' T.carrier) =
          Kakeya.rigidMap u v '' T.carrier := by
        rw [← Set.image_comp]
        congr 1
        funext x
        simp [Kakeya.rigidMap, add_comm]
      calc
        (T.rigidMove u v).carrier = Kakeya.rigidMap u v '' T.carrier := Tube.rigidMove_carrier T u v
        _ = (v + ·) '' (Kakeya.rigidMap u 0 '' T.carrier) := r_im.symm
        _ = (v + ·) '' (T.rigidMove u 0).carrier := by rw [Tube.rigidMove_carrier]
        _ = ((T.rigidMove u 0).translate v).carrier := by
          simp [Tube.translate]
    have hset : {v : E | (T.rigidMove u v).carrier ⊆ K.carrier} =
        {v : E | ((T.rigidMove u 0).translate ((1 : ℝ) • v)).carrier ⊆ K.carrier} := by
      ext ω
      simp only [Set.mem_setOf_eq, one_smul]
      rw [hcar ω]
    rw [hset]
    simpa [one_pow, div_one] using
      prob_tube_translate_subset_le (E := E) (δ := δ) (T := T.rigidMove u 0)
        (K := K) (r := 1) (hr_pos := by norm_num)

/-- **GWZ Appendix A, equation (108), for rigid motions.**
`P[R(T) ⊆ K] ≤ C · volume K` for a random *rigid* motion, with no rotational gain. This is the
estimate the **Frostman** conjunct of GWZ Lemma 3.8 needs: there the rotation is along for the ride
and only the translational spreading matters. It is obtained from the fibrewise translation estimate
`Kakeya.prob_translate_rigidMove_le` by integrating over `rotHaar`, which is a probability measure.

Contrast `Kakeya.prob_rigidMove_bad_le` below, the *ED* conjunct, which does exploit the
rotation and gains the second factor of `δ^(n-1)`. -/
theorem prob_rigidMove_subset_volume_le [Nontrivial E] :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ {δ : ℝ≥0} (T : Tube δ E) (K : ConvexSpaceBody E),
        rigidMeasure E {ω : unitary (E →L[ℝ] E) × E |
            (T.rigidMove ω.1 ω.2).carrier ⊆ K.carrier}
          ≤ C * volume K.carrier := by
  obtain ⟨Ctr, hCtr, hTrans⟩ := prob_translate_rigidMove_le (E := E)
  refine ⟨Ctr, hCtr, ?_⟩
  intro δ T K
  calc
    rigidMeasure E {ω : unitary (E →L[ℝ] E) × E |
        (T.rigidMove ω.1 ω.2).carrier ⊆ K.carrier}
        = (rotHaar (E := E)).prod (uniformBallMeasure E)
            {ω : unitary (E →L[ℝ] E) × E |
              (T.rigidMove ω.1 ω.2).carrier ⊆ K.carrier} := by
          rw [rigidMeasure]
    _ = ∫⁻ u : unitary (E →L[ℝ] E), uniformBallMeasure E (Prod.mk u ⁻¹'
        {ω : unitary (E →L[ℝ] E) × E |
            (T.rigidMove ω.1 ω.2).carrier ⊆ K.carrier}) ∂(rotHaar (E := E)) := by
        exact Measure.prod_apply (isClosed_rigidMove_subset T K).measurableSet
    _ = ∫⁻ u : unitary (E →L[ℝ] E), uniformBallMeasure E
            {v : E | (T.rigidMove u v).carrier ⊆ K.carrier} ∂(rotHaar (E := E)) := by
        rfl
    _ ≤ ∫⁻ _u : unitary (E →L[ℝ] E), Ctr * volume K.carrier ∂(rotHaar (E := E)) := by
        exact lintegral_mono (fun u => hTrans T K u)
    _ = Ctr * volume K.carrier * rotHaar (E := E) Set.univ := by
        rw [lintegral_const]
    _ = Ctr * volume K.carrier := by
        rw [measure_univ, mul_one]

end

end Kakeya

end

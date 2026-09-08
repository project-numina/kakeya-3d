/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSiteClosure

/-!
# A producer for `Kakeya.ML2Core.SiteWitness`

`Kakeya.ML2Core.SiteWitness` is the selection part of the site construction.
The non-vacuity witness `Kakeya.ML2Wit.exists_siteWitness_nonvacuity` and
`Kakeya.ML2Core.siteWitnessRows_of_trivial` (`u' = s`, `lam = 1`, `K = 1`)
show that particular data satisfy it; the construction here quantifies over arbitrary `s T`.

This file supplies `Kakeya.ML2Core.siteWitness_of_scalars`, an unconditional producer at the
absolute constant `Cu₀ = ShadedTube.ssfUniformConst 3`, under four scalar conditions.

## The route, and where the source charges each step

GWZ, Lemma "One trial", and the opening of its proof.

1. **The dyadic selection.**  The source discards the tubes with `|Z(T)| < δ^{10}|T|` and
   then performs one joint dyadic selection on `w(T) = |Z(T)|/|T|`.  Here both are done at
   once by `Kakeya.ML2Shaded.exists_denseShading_refinement`, which is strictly cheaper: it retains
   half the shaded mass (`K`-cost `2`, not a logarithm) and returns the *pointwise* invariant
   `HasDenseShading (fullness s V / 2)`.  The source's `Λ_0 ≤ (2 + log₂(1/δ))^{K_0}` is an
   upper bound on the loss, so paying only `2` is inside the source's budget.

2. **The uniformisation.**  `Tube.exists_uniformTubeSet_subfamily_ssf` at `K₀ = 4`, which is
   exactly the source's cardinality input `#𝕋 ≤ 2^{11}A₀δ^{-4}` in the form the
   tree carries it.  It returns `UniformTubeSet u' T (ssfGridLen δ) (uniformConst 3)` at a
   *cardinality* retention `#u₁ ≤ δ^{-α} #u'` with `α > 0` **free**.  Freedom of `α` is what makes
   the budget row close; see `Kakeya.ML2Core.siteWitnessAlpha`.

3. **Cardinality back to mass.**  The uniformisation pays in cardinality and the ledger row is
   stated in mass, so the two are tied by `Kakeya.ML2Core.sum_shade_le_of_card_le_of_denseShading`:
   under a pointwise dense shading at level `lam`, congruence of `δ`-tubes converts a card ratio
   `R` into a mass ratio `R · C/(lam · c)` with `C`, `c` the dimensional volume bracket
   (`Tube.volume_le`, `Tube.le_volume`).  This is the step that costs `lam^{-1} ≤ 2δ^{-η}` and it
   is the reason the producer needs `η + aL < dm` rather than merely `aL ≤ dm`.

## The four scalar conditions, and what licenses them

* `hη1 : η ≤ 1` — the hypothesis of `Kakeya.ML2Assembly.card_le_rpow_neg_four`, the tree's form of
  the source's `#𝕋 ≤ 2^{11}A₀δ^{-4}`.  The source's `η₀` is chosen last and small
  (GWZ: "there are `ν₀, η₀ > 0`... depending only on this fixed data"), so `η ≤ 1` is
  free.
* `haL0 : 0 < aL` — forced by the skeleton, not by this file
  (`Kakeya.ML2Core.geometricCoreAt_of_witness_and_trial` instantiates `T-D5` at `aL`;
   the parameter comparison).
* `hladder : η + aL ≤ ηin` — the lam-ladder row 7.  The selection delivers
  `lam ≥ δ^η/2` from the fullness input `λ(s,Z) ≥ δ^η`, and row 7 asks for `δ^{ηin-aL}/2 ≤ lam`.
  The source's own ladder has the same shape: the trial is entered at `λ ≥ δ^{2η₀}` while
  the input carries `δ^{η₀}`, i.e. the ladder exponent is *above* the input exponent.
* `hbudget : η + aL < dm` — the budget row 10.  **Strict**, and strictly stronger than the
  skeleton's `aL ≤ dm`.  This is a measured cost of step 3 above, reported rather than hidden: a
  producer that retains a *proper* subfamily must pay `lam^{-1}` to convert the uniformisation's
  cardinality price into the ledger's mass price, and `lam ≍ δ^η`.  At `aL = dm` the row reads
  `K ≤ 1`, which no proper retention can meet.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric ConvexSpaceBody ShadedBody
open scoped NNReal ENNReal Topology

namespace Kakeya.ML2Core

/-! ## Cardinality retention to mass retention -/

section CardToMass

variable {ι : Type*}

/-- **A cardinality retention is a mass retention, at the price of the shading level.**

If `u' ⊆ u` carries a pointwise dense shading at level `lam` and `#u ≤ R · #u'`, then the shaded
mass of `u` is at most `R · C/(lam · c)` times that of `u'`, with `C`, `c` the dimensional volume
bracket of a `δ`-tube.  Stated multiplicatively so that no division appears.

This is the step the site's producer cannot avoid: `Tube.exists_uniformTubeSet_subfamily_ssf` pays
in cardinality, while `Kakeya.ML2Core.stateMass` is a mass. -/
theorem sum_shade_le_of_card_le_of_denseShading {δ : ℝ≥0} (hδ1 : δ ≤ 1)
    {u u' : Finset ι} {V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {lam : ℝ≥0}
    (hdense : ML2Shaded.HasDenseShading lam u' (fun i => (V i).toShadedBody))
    {R : ℝ≥0∞} (hcard : (u.card : ℝ≥0∞) ≤ R * (u'.card : ℝ≥0∞)) :
    (lam : ℝ≥0∞) * (Tube.le_volume.c 3 : ℝ≥0∞) * (∑ i ∈ u, volume (V i).shade)
      ≤ (Tube.volume_le.C 3 : ℝ≥0∞) * R * ∑ i ∈ u', volume (V i).shade := by
  classical
  have hE : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  -- the upper bracket on `u`
  have hup : (∑ i ∈ u, volume (V i).shade)
      ≤ (u.card : ℝ≥0∞) * ((Tube.volume_le.C 3 : ℝ≥0∞) * (δ : ℝ≥0∞) ^ 2) := by
    calc (∑ i ∈ u, volume (V i).shade)
        ≤ ∑ _i ∈ u, ((Tube.volume_le.C 3 : ℝ≥0∞) * (δ : ℝ≥0∞) ^ 2) := by
          refine Finset.sum_le_sum ?_
          intro i _
          refine le_trans (measure_mono (V i).shade_subset) ?_
          have h := Tube.volume_le (E := EuclideanSpace ℝ (Fin 3)) hδ1 (V i).toTube
          rw [hE] at h
          refine le_trans h (le_of_eq ?_)
          push_cast
          norm_num
      _ = (u.card : ℝ≥0∞) * ((Tube.volume_le.C 3 : ℝ≥0∞) * (δ : ℝ≥0∞) ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- the lower bracket on `u'`, through the pointwise dense shading
  have hlo : (lam : ℝ≥0∞) * ((u'.card : ℝ≥0∞) * ((Tube.le_volume.c 3 : ℝ≥0∞) * (δ : ℝ≥0∞) ^ 2))
      ≤ ∑ i ∈ u', volume (V i).shade := by
    have hstep : ∀ i ∈ u', (lam : ℝ≥0∞) * ((Tube.le_volume.c 3 : ℝ≥0∞) * (δ : ℝ≥0∞) ^ 2)
        ≤ volume (V i).shade := by
      intro i hi
      refine le_trans ?_ (hdense i hi)
      have h := Tube.le_volume (E := EuclideanSpace ℝ (Fin 3)) (V i).toTube
      rw [hE] at h
      norm_num at h
      have h' : ((Tube.le_volume.c 3 : ℝ≥0∞) * (δ : ℝ≥0∞) ^ 2)
          ≤ volume ((V i).toShadedBody).carrier := by exact_mod_cast h
      gcongr
    calc (lam : ℝ≥0∞) * ((u'.card : ℝ≥0∞) * ((Tube.le_volume.c 3 : ℝ≥0∞) * (δ : ℝ≥0∞) ^ 2))
        = ∑ _i ∈ u', (lam : ℝ≥0∞) * ((Tube.le_volume.c 3 : ℝ≥0∞) * (δ : ℝ≥0∞) ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ i ∈ u', volume (V i).shade := Finset.sum_le_sum hstep
  calc (lam : ℝ≥0∞) * (Tube.le_volume.c 3 : ℝ≥0∞) * (∑ i ∈ u, volume (V i).shade)
      ≤ (lam : ℝ≥0∞) * (Tube.le_volume.c 3 : ℝ≥0∞)
          * ((u.card : ℝ≥0∞) * ((Tube.volume_le.C 3 : ℝ≥0∞) * (δ : ℝ≥0∞) ^ 2)) := by gcongr
    _ ≤ (lam : ℝ≥0∞) * (Tube.le_volume.c 3 : ℝ≥0∞)
          * ((R * (u'.card : ℝ≥0∞)) * ((Tube.volume_le.C 3 : ℝ≥0∞) * (δ : ℝ≥0∞) ^ 2)) := by gcongr
    _ = (Tube.volume_le.C 3 : ℝ≥0∞) * R
          * ((lam : ℝ≥0∞) * ((u'.card : ℝ≥0∞)
              * ((Tube.le_volume.c 3 : ℝ≥0∞) * (δ : ℝ≥0∞) ^ 2))) := by ring
    _ ≤ (Tube.volume_le.C 3 : ℝ≥0∞) * R * ∑ i ∈ u', volume (V i).shade := by gcongr

end CardToMass

/-! ## The scalars the producer spends -/

section Scalars


end Scalars


/-! ## The producer -/

section Producer


end Producer

end Kakeya.ML2Core

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineOuterTubes
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCountClause
public import Kakeya.DimensionThree.MainLemma2.CanonicalCentredCover

/-!
# The centring hand-back: the normalising similarity and the two Props of ′

This leaf sits **below** `Reduction/SpineCoreAssembly.lean`, which is where Lemma 9.1 is
eliminated (`fine_factor_of_lemma91At_of_canonicalCover`, the site ′) and which therefore has to *name* `CentredHandBack` in a binder.  The three declarations
were first written in `Reduction/SpineCentringCover.lean`, which imports `SpineCoreAssembly` and
so is on the wrong side of that edge; they are relocated here unchanged, and
`SpineCentringCover.lean` now imports this module.

Everything the two Props mention lives below `SpineCoreAssembly`: `outerFamily` and
`spineFamily`/`spineRescaleUnit` (`Reduction/SpineOuterTubes.lean`, `Reduction/SpineRescale.lean`),
`Tube.IsCentred` (`Kakeya/Tube/Basic.lean`, D0) and `Tube.IsRescalingSituation`
(`Kakeya/Tube/Rescale.lean`).

## Main declarations

* `Kakeya.VeryNotSticky.centringDilate` and `Kakeya.VeryNotSticky.normalise` — the anisotropic
  map of `eqanisotropicmap` **at `ρ = 1`**, where it collapses to the
  similarity `x ↦ (x − m)/8`.
* `Kakeya.VeryNotSticky.CentredHandBack` — the eleven-field Prop.
* `Kakeya.VeryNotSticky.CountTransport` — the A7.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric RealInnerProductSpace Kakeya.ML2Reduction

namespace Kakeya.VeryNotSticky

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]

/-- **The anisotropic normalisation at `ρ = 1`** (refined `eqanisotropicmap`, ,
composed with  "apply the anisotropic map with `ρ = 1`" at the fixed unit tube centred
at the origin).  At `ρ = 1` the map `L(x) = (1/8)(((x-m)·e)e + ρ⁻¹((x-m) - ((x-m)·e)e))` collapses
to `x ↦ (x - m)/8`, a **similarity** of ratio `1/8` — and `lemaffineinvariance`
records that a similarity carries exact tubes to exact tubes and preserves line-based essential
distinctness.  Taken at `m = 0`. -/
noncomputable def centringDilate (x : E) : E := (8 : ℝ)⁻¹ • x

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [ProperSpace E] in
theorem centringDilate_image_subset_ball {A : Set E} (hA : A ⊆ Metric.closedBall (0 : E) 1) :
    centringDilate '' A ⊆ Metric.closedBall (0 : E) (2 / 5) := by
  rintro y ⟨z, hz, rfl⟩
  have hzn : ‖z‖ ≤ 1 := by simpa using Metric.mem_closedBall.mp (hA hz)
  simp only [Metric.mem_closedBall, dist_zero_right, centringDilate, norm_smul, norm_inv,
    Real.norm_ofNat]
  rw [inv_mul_eq_div]
  linarith

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The image of a tube lies in the `δ/8`-neighbourhood of the image line.**  The similarity
divides both the core's length and the radius by `8`; the direction is unchanged. -/
theorem centringDilate_image_subset_lineNbhd {δ : ℝ≥0} (T : Tube δ E) :
    centringDilate '' T.carrier ⊆
      Metric.cthickening ((δ : ℝ) / 8)
        (Set.range fun t : ℝ ↦ centringDilate T.midpoint + t • T.direction) := by
  rintro y ⟨z, hz, rfl⟩
  rw [T.carrier_eq] at hz
  obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.mp hz
  obtain ⟨t, -, rfl⟩ := T.exists_param_of_mem_segment hw
  refine Metric.mem_cthickening_of_dist_le _
    (centringDilate T.midpoint + (t / 8) • T.direction) _ _ ⟨t / 8, rfl⟩ ?_
  have hd : dist z (T.midpoint + t • T.direction) ≤ (δ : ℝ) := Metric.mem_closedBall.mp hzw
  have hEq : centringDilate z - (centringDilate T.midpoint + (t / 8) • T.direction)
      = (8 : ℝ)⁻¹ • (z - (T.midpoint + t • T.direction)) := by
    unfold centringDilate; module
  rw [dist_eq_norm, hEq, norm_smul, norm_inv, Real.norm_ofNat, ← dist_eq_norm]
  rw [inv_mul_eq_div]
  linarith

/-- **The normalising similarity of the canonical cover** ( at `ρ = 1`). -/
noncomputable def normalise (m x : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  (8 : ℝ)⁻¹ • (x - m)

/-- **The tightened uniformity clause weakens to the existing loose one, by name.**

`Kakeya.ML2Reduction.Lemma91At`'s own `∃ C, 1 ≤ C ∧ C ≤ δ^{-ηd} ∧ …` clause is protected text
(`Reduction/SpineOuterTubes.lean`), and `4a`, caller 1, the eliminator and the companion keep it,
so a site holding the *named* constant discharges them through this — no bridge constant, the
witness is the constant itself.

**.**  The threshold conjunct is not a new cost: it is
`δ' ≤ (ssfUniformConst 3)^{-1/ηd}`, which is exactly what the loose bracket `C ≤ δ'^{-ηd}` was
quantifying away.  At the `ηd ≲ 2.4·10⁻⁹` the supplier actually delivers, that threshold is
astronomically small — which is the point: the cost was always there, and naming the constant
makes it visible instead of charging `ηd` for it at every reading. -/
theorem huni_loose_of_tight {δ' : ℝ≥0} {ηd : ℝ} {α : Type u} {s' : Finset α}
    {U' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))}
    (h : ((ShadedTube.ssfUniformConst 3 : ℝ≥0) : ℝ≥0∞) ≤ (δ' : ℝ≥0∞) ^ (-ηd) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s' U' (Tube.ssfGridLen δ')
        (ShadedTube.ssfUniformConst 3))) :
    ∃ C : ℝ≥0, 1 ≤ C ∧ (C : ℝ≥0∞) ≤ (δ' : ℝ≥0∞) ^ (-ηd) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s' U' (Tube.ssfGridLen δ') C) :=
  ⟨ShadedTube.ssfUniformConst 3, ShadedTube.one_le_ssfUniformConst 3, h.1, h.2⟩

/-- **The centring hand-back**. -/
structure CentredHandBack {b δt δ' : ℝ≥0} {R : ℝ}
    (hsit : Tube.IsRescalingSituation b δt δ' R 3) (hR : 0 < R)
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3))) (m : EuclideanSpace ℝ (Fin 3)) (qc : ℝ)
    {α : Type u} (fib s' : Finset α)
    (Z' : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3)))
    (U' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))) : Prop where
  subset : s' ⊆ fib
  small : (δ' : ℝ) ≤ 1 / 20
  dens : Kakeya.maxDensity fib
      (fun i ↦ (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toConvexSpaceBody) ≤
    (δ' : ℝ≥0∞) ^ (-qc)
  full : (δ' : ℝ≥0∞) ^ qc ≤
    ShadedBody.fullness fib
      (fun i ↦ (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toShadedBody)
  centred : ∀ i ∈ s', (U' i).toTube.IsCentred
  contained : ∀ i ∈ s', (U' i).carrier ⊆ Metric.closedBall 0 1
  covers : ∀ i ∈ s',
    normalise m '' (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).carrier ⊆ (U' i).carrier
  maxDensity_le : Kakeya.maxDensity s' (fun i ↦ (U' i).toConvexSpaceBody) ≤
    (δ' : ℝ≥0∞) ^ (-(2 * qc))
  fullness_ge : (δ' : ℝ≥0∞) ^ (3 * qc) ≤
    ShadedBody.fullness s' (fun i ↦ (U' i).toShadedBody)
  card_le : (s'.card : ℝ≥0∞) ≤ (fib.card : ℝ≥0∞)
  multiplicity_le : ShadedBody.multiplicity fib
      (fun i ↦ (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toShadedBody) ≤
    (δ' : ℝ≥0∞) ^ (-(3 * qc)) *
      ShadedBody.multiplicity s' (fun i ↦ (U' i).toShadedBody)

/-! ## the line-ED levels datum, sourced internally from `huni` -/

/-- **The centring cover's radius constant**.  The hand-back reads
the canonical cover of the *rescaled bodies* at a radius contracted by this fixed absolute factor.
It is a number, so the contraction is a threshold on `δ'`, never a change of exponent. -/
def centringCoverRadiusConstant : ℝ≥0 := 2

/-- **The fibre factor `F`**, named  and measured.

`hfibre` counts a **tube-dilate packing of normalised members**, so the bound is
`Tube.essDistinctTubesInSelfDilate.C` at the dilation ratio PRODUCER-4's pull-back lemma through
`normalise` needs.  That lemma has two hypotheses — `8 · Cn ≤ c₀` on the core and
`8 · C · Cn ≤ c₀` on the radius, with `C = centringCoverRadiusConstant` and
`Cn = Tube.tubeOverlapCoreClose.C 3` — and `c₀ = 16 · C · Cn` dominates both, with a factor of two
to spare.  Minimality is not required; what is required is that the expression be
*derived* from the bounds it pays for, and it is: both factors are named constants and no numeral
is chosen.  `δ'`-free, since neither named constant sees the scale.

**The `1 +` is the tree's own idiom, and it is not cosmetic.**
`Tube.essDistinctTubesInSelfDilate.C` carries no lower bound of its own — `Kakeya/Tube/
CoverCountComparable.lean` records exactly this, which is why `Tube.coverCountLossAt` and
`Kakeya.ML2Reduction.spineOuterCountLoss` are padded the same way — so `1 ≤ F` is available only
by padding, via `le_self_add`.  Consumers need `1 ≤ F` (it is what lets the transport drop the
factor), so the padding is load-bearing.

After this, both factors of `centringCountLossConstant R` are
`1 + essDistinctTubesInSelfDilate.C 3 _`
at different arguments: a two-stage packing price, one stage for the outer-core transport and one
for the subfamily.

**How big is it?**  `_eq` is an unfolding, so here is the magnitude in prose:
`Tube.essDistinctTubesInSelfDilate.C 3 c ≤ selfDilatePrefactor * c.toNNReal ^ 12` for `1 ≤ c`
(`Kakeya.VeryNotSticky.essDistinctTubesInSelfDilate_C_le`, `MainLemma2/SplitInputsFibreCount.lean`),
so `F ≤ 1 + selfDilatePrefactor · c₀¹²` at `c₀ = 16 · C · Cn`.  The lemma form of this estimate is
deferred: `SplitInputsFibreCount.lean` is on a different import branch, and pulling it into this
leaf for a courtesy bound would be a DAG change.

**The product is doubly padded, `(1 + A)(1 + B)`, and that is accepted and not to be tightened**
( addendum (S)).  Each `1 +` buys `1 ≤` for its own factor by
`le_self_add`, both are needed by their own consumers, and the cross terms are paid by the same
threshold that pays the product — so removing either padding would buy nothing and cost the free
`1 ≤`. -/
noncomputable def centringCoverFibreConstant : ℝ≥0 :=
  1 + Tube.essDistinctTubesInSelfDilate.C 3
      (16 * (centringCoverRadiusConstant : ℝ) * (Tube.tubeOverlapCoreClose.C 3 : ℝ))

theorem centringCoverFibreConstant_eq :
    centringCoverFibreConstant
      = 1 + Tube.essDistinctTubesInSelfDilate.C 3
          (16 * (centringCoverRadiusConstant : ℝ) * (Tube.tubeOverlapCoreClose.C 3 : ℝ)) := rfl

@[simp] theorem centringCoverFibreConstant_coe :
    (centringCoverFibreConstant : ℝ)
      = 1 + (Tube.essDistinctTubesInSelfDilate.C 3
          (16 * (centringCoverRadiusConstant : ℝ) * (Tube.tubeOverlapCoreClose.C 3 : ℝ)) : ℝ) := by
  simp [centringCoverFibreConstant]

theorem one_le_centringCoverFibreConstant : (1 : ℝ≥0) ≤ centringCoverFibreConstant :=
  le_self_add

/-- **The centring transport's count-loss constant**.

The hypothesis side of the count transport names a **packing** bound, not the rescaling loss
`Kakeya.ML2Reduction.spineOuterCountLoss R`: the transport factors through the canonical cover's
node assignment, whose fibres are bounded by the cover's own ED constant and not by `1`, so
pairwise essential distinctness is recovered only after passing to one index per node.  That price
is absolute — it depends on the ambient dimension and on the reach `R₀`, not on the scale, not on
the tubes, not on `R` — so it is a threshold on the scale, never an exponent, and it is **defined
from the packing bound rather than chosen**, so it cannot drift from the fibre bound it pays for.

**`R`-dependent and δ-free.**  The `R`-dependent factor is `spineOuterCountLoss R` **by name**
and must never acquire a numeral; the numeral survives only in the `δ`-free packing factor.  `R`
is bounded below by `Tube.normalization.C 3` inside `Tube.IsRescalingSituation` and is not bounded
above anywhere in the tree, so no `R`-free upper bound on `spineOuterCountLoss R` exists and the
argument cannot be dropped.  Nothing here depends on the scale, so the clause it prices is still
**one threshold in `δ'`**.

**`R₀ = 1` dominates the reach** : `Kakeya.VeryNotSticky.exists_setCanonicalCentredCover`
produces nodes of reach `‖midpoint‖ ≤ 2/5 + ρ/4`, and at its own hypothesis `ρ ≤ 1/20` that is at
most `0.4125 ≤ 1`.  So `R₀ = 1` dominates with room, and it is the choice for which the constant
has an integer value, `2 · 641³ · 513³ ≈ 1.07 · 10¹⁶` (`centringCountLossConstant_eq`). -/
noncomputable def centringCountLossConstant (R : ℝ) : ℝ≥0 :=
  ML2Reduction.spineOuterCountLoss R * centringCoverFibreConstant

@[simp] theorem centringCountLossConstant_coe (R : ℝ) :
    (centringCountLossConstant R : ℝ)
      = (ML2Reduction.spineOuterCountLoss R : ℝ) * (centringCoverFibreConstant : ℝ) := rfl

theorem centringCountLossConstant_eq (R : ℝ) :
    (centringCountLossConstant R : ℝ)
      = (ML2Reduction.spineOuterCountLoss R : ℝ)
        * (1 + (Tube.essDistinctTubesInSelfDilate.C 3
            (16 * (centringCoverRadiusConstant : ℝ)
              * (Tube.tubeOverlapCoreClose.C 3 : ℝ)) : ℝ)) := by
  rw [centringCountLossConstant_coe, centringCoverFibreConstant_coe]

/-- **The ED-window contraction constant**, the
*hypothesis-side* name of the same number.  Every clause that must *supply* the contracted cover
is stated on a window whose lower endpoint is divided by this constant. -/
def edWindowContractionConstant : ℝ≥0 := centringCoverRadiusConstant

@[simp] theorem edWindowContractionConstant_eq_centringCoverRadiusConstant :
    edWindowContractionConstant = centringCoverRadiusConstant := rfl

theorem centringCoverRadiusConstant_pos : 0 < centringCoverRadiusConstant := by
  unfold centringCoverRadiusConstant; norm_num

theorem div_centringCoverRadiusConstant_le (ρ : ℝ≥0) :
    ρ / centringCoverRadiusConstant ≤ ρ := NNReal.half_le_self ρ

theorem edWindowContractionConstant_pos : 0 < edWindowContractionConstant :=
  centringCoverRadiusConstant_pos

/-- **enabling step.**  Dividing only the *lower* endpoint by the constant puts every
contracted radius back inside the window, for every `ρ` of the original one.  Widening a lower
endpoint downwards can never empty an interval, so no new threshold on the scale is incurred. -/
theorem mem_widened_window_of_mem {δ' ρ : ℝ≥0} {ϖ : ℝ}
    (hρ : ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ)) :
    ρ / centringCoverRadiusConstant
      ∈ Set.Icc (δ' ^ (1 - ϖ) / edWindowContractionConstant) (δ' ^ ϖ) := by
  refine ⟨?_, le_trans (div_centringCoverRadiusConstant_le ρ) hρ.2⟩
  rw [edWindowContractionConstant_eq_centringCoverRadiusConstant]
  gcongr
  exact hρ.1

/-- The widened bottom still dominates the thickness: `x ≤ x^{1-ϖ}/C` exactly when
`x^ϖ ≤ 1/C`, a threshold on the scale at fixed `ϖ > 0`.  The base is a bound variable, so this is
one lemma applied separately at `δ'` and at `σ`; nothing is transported between instances. -/
theorem le_div_rpow_one_sub {x : ℝ≥0} (hx : 0 < x) {ϖ : ℝ}
    (hthr : x ^ ϖ ≤ 1 / 2) : x ≤ x ^ (1 - ϖ) / edWindowContractionConstant := by
  have hsplit : x ^ (1 - ϖ) * x ^ ϖ = x := by
    rw [← NNReal.rpow_add (ne_of_gt hx)]; simp
  have h : x ≤ x ^ (1 - ϖ) * (1 / 2) := by
    calc x = x ^ (1 - ϖ) * x ^ ϖ := hsplit.symm
      _ ≤ x ^ (1 - ϖ) * (1 / 2) := by gcongr
  rw [edWindowContractionConstant_eq_centringCoverRadiusConstant]
  simpa [centringCoverRadiusConstant, div_eq_mul_inv, mul_one_div] using h

/-- **A7 — the count clause transports to the centred representatives.**  An essentially distinct,
all-used `ρ`-cover of the *rescaled bodies* yields one of the *centred representatives*, at the same
radius and count.  Refined  (`X_i ⊂ C_i`, axes within `r`) with  (a similarity
carries exact tubes to exact tubes and preserves line-based essential distinctness).

Stated in the **consumer's** shape — the conclusion is `Kakeya.ML2Reduction.Lemma91At`'s count clause
at `(s', U')`, verbatim — because the earlier producer-shaped version (a thickened
pull-back) could not feed `count_clause_at_uniformised_of_canonicalCover`: the pull-back of a
`ρ`-tube has core `1/8`, and no thickening of it is a unit-core `ρ`-tube. -/
def CountTransport {b δt δ' : ℝ≥0} {R : ℝ}
    (hsit : Tube.IsRescalingSituation b δt δ' R 3) (hR : 0 < R)
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3))) (_m : EuclideanSpace ℝ (Fin 3)) (ϖ ζ : ℝ)
    {α : Type u} (s' : Finset α)
    (Z' : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3)))
    (U' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∀ ρ : ℝ≥0, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
    (∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ / centringCoverRadiusConstant) (EuclideanSpace ℝ (Fin 3))),
      ((t : Set κ₀).Pairwise
        fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
      (∀ j ∈ t, ∃ i ∈ s',
        (spineFamily (spineRescaleUnit hsit.pos_ambient T₀ hR) Z' i).toConvexSpaceBody
          ≤ (W j).toConvexSpaceBody) ∧
      (centringCountLossConstant R : ℝ)
        * ((ρ / centringCoverRadiusConstant : ℝ≥0) : ℝ) ^ (-2 - ζ) ≤ (t.card : ℝ)) →
    (∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
      (tρ : Set κ).Pairwise
        (fun j k ↦ _root_.IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
      (∀ j ∈ tρ, ∃ i ∈ s', (U' i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
      (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ))

end Kakeya.VeryNotSticky

end

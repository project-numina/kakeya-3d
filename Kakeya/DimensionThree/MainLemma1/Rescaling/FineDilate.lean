/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Rescaling.DensityTransfer
public import Kakeya.DimensionThree.MainLemma1.Rescaling.Thresholds

/-!
# Main Lemma 1, Case (ii): reduction to the `b`-tubes — the fine factor over a `2`-dilate

Split out of `Kakeya/DimensionThree/MainLemma1/Rescaling.lean`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya

universe u

namespace ml1Boot

section ReduceToTb

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! #### The fine factor over a dilate of a parent tube

What the plank-in-tube chain supplies is not `T i ⊆ T_b` but `T i ⊆ c · T_b`, together with a
Frostman bound taken *in* the dilate (`Kakeya.ml1Boot.frostmanConstIn_fibre_le_rpow`).  This
block restates the fine factor under that weaker containment, on top of the dilate
normalization `Kakeya.ml1Boot.exists_fineNormalization_dilate` of
`Kakeya/DimensionThree/MainLemma1/Cases.lean`.  The dilation ratio `c` is free throughout, and
is carried as an `NNReal` because it is read both as the real ratio of `Kakeya.Tube.dilate` and
inside the `NNReal`-valued constant `Kakeya.ml1Boot.fineNormalizeDilate.C`.
`Kakeya.ml1Boot.reduceToTb_fine_bound` is **not** superseded: it remains correct and the dilate
form is a separate declaration. -/

/-- **The constant `C_{lem:ml1bootReduceToTbFineBoundDilate}(c, C_F)`**, at dilation ratio `c` and
Frostman budget
constant `C_F`.

Writing `C₃(c) = Kakeya.ml1Boot.fineNormalizeDilate.C c`, this is `4 C₃(c)² (2 C_F)`: the
prefactor `4 C₂² (2 C_T)` of `Kakeya.ml1Boot.reduceToTb_fine_bound` with
`C₂ = Kakeya.ml1Boot.fineFactor.C` replaced by `C₃(c)` and
`C_T = Kakeya.ml1Boot.densityTransfer.C` replaced by the parameter `C_F`.  The factor `4` is the
`Λ²` of `Kakeya.ml1Boot.fine_genKF_dilate` at `Λ = 2`, one power of `C₃(c)` comes from that
lemma's prefactor and one from the Frostman constant fed into it, and `2 C_F` is the Frostman
budget the caller's hypothesis (a) is read at.

`C_F` is a **parameter** and not `C_T`, because the Frostman bound this chain consumes is
whatever a caller can produce.  The density-transfer route
`Kakeya.ml1Boot.frostmanConstIn_fibre_le_rpow` produces it at `C_T`, i.e. at `C_F = C_T`, which
is the previous statement verbatim; the hull route
`Kakeya.ml1Boot.frostmanConstIn_fibre_convexHull_le` produces it at the larger
`Kakeya.ml1Boot.fibreMassShare.C`, which no declaration below that module can name, and the
parameter is how the wider constant is carried without an import cycle.  The constant is
**spent** here, on a conclusion side, so the widening is a loosening of this bound and is paid
in the caller's loss budget rather than in its Frostman budget.

It depends only on the ambient dimension `3`, on the ratio `c` and on `C_F`; in particular not
on `δ̃`, `ap`, `bp`, `ρ`, `γ`, `j`, or the family. -/
noncomputable abbrev reduceToTbFineBoundDilate.C (c CF : ℝ≥0) : ℝ≥0 :=
  4 * fineNormalizeDilate.C c ^ 2 * (2 * CF)

/-- **The fine-factor input package over a dilate** (blueprint
`lem:ml1bootReduceToTbFineInput`, hypotheses (i)–(iii)).

`(𝕋̃|_{u'}, Ỹ')` is the refined fine family and `l₀` a parent index; the fields are items (a),
(c) and (d) of `Kakeya.ml1Boot.IsFactorOneScaleDilate` read at that single index, which is
exactly what `Kakeya.ml1Boot.exists_factorOneScaleUniform_dilate` returns.

Throughout, `𝕋̃[T̃_{b,l₀}]` means the **parent-map** fibre `Kakeya.ml1Boot.fibre _ p_b l₀`, and
never the containment fibre `𝕋̃[K] = (T̃ i)_{T̃ i ⊆ K}` that the density-transfer chain of
`Kakeya.ml1Boot.maxDensity_fibre_le_density_dilate` writes with the same bracket.  One reading
is fixed here and used in every field.

Neither the parent family nor the scale `b` occurs: the package is pure bookkeeping about the
fibre, which is why the parent tube is not a parameter. -/
structure IsFineInputDilate {ι κ : Type*} [DecidableEq κ] {δt : ℝ≥0} (ap' : ℝ)
    (u : Finset ι) (T : ι → ShadedTube δt E) (p : ι → κ)
    (u' : Finset ι) (T' : ι → ShadedTube δt E) (lamσ : ℝ≥0∞) (l₀ : κ) : Prop where
  /-- The refined index set is a subset of the given one. -/
  subset : u' ⊆ u
  /-- `Ỹ'` shades the same tubes as `𝕋̃`. -/
  tube_eq : ∀ i ∈ u', (T' i).toTube = (T i).toTube
  /-- (i) The fibre over `l₀` survives the refinement. -/
  fibre_nonempty : (fibre u' p l₀).Nonempty
  /-- (i) Its tubes are pairwise essentially distinct. -/
  fibre_essDistinct : ((fibre u' p l₀ : Finset ι) : Set ι).Pairwise
    (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier)
  /-- (ii) The refined shading densities are two-sidedly comparable to `λ_σ`. -/
  dens : ∀ i ∈ u', lamσ * volume (T i).carrier ≤ volume (T' i).shade ∧
    volume (T' i).shade ≤ 2 * lamσ * volume (T i).carrier
  /-- (ii) `λ_σ ≥ δ̃ ^ ap' λ(𝕋̃, Ỹ)`. -/
  lamσ_ge : (δt : ℝ≥0∞) ^ ap'
      * (ShadedBody.fullness u (fun i => (T i).toShadedBody) : ℝ≥0∞) ≤ lamσ
  /-- (iii) The fibre Frostman constant grows by at most `δ̃ ^ (-ap')` under the refinement,
  in *every* convex body containing the whole fibre. -/
  frostman_refine : ∀ K : ConvexSpaceBody E,
    (∀ i ∈ u, p i = l₀ → (T i).toConvexSpaceBody ≤ K) →
    frostmanConstIn (fibre u' p l₀) (fun i => (T i).toConvexSpaceBody) K
      ≤ (δt : ℝ≥0∞) ^ (-ap')
        * frostmanConstIn (fibre u p l₀) (fun i => (T i).toConvexSpaceBody) K

end ReduceToTb

end ml1Boot

end Kakeya

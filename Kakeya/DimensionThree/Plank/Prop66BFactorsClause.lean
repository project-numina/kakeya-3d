/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.GlobalPlankDatumBridge
public import Kakeya.DimensionThree.Volume

/-!
# `def:Factors` clause (ii): the hull reading and the plank reading

The blueprint's `def:Factors` (the factoring definitions) asks, for a factorization
of a family `𝕍 = (V i)` by outer bodies `(W t)`, that

  (ii)  `Δ_max(𝕍) ≤ C · Δ(𝕍_t, W_t)`   for every block `t`,

where `W_t` is, in the definition's own words, *"a convex body containing `V i` for every `i ∈ t`"*.
The blueprint then records, immediately after the definition, that

  *"The Lean structure uses the canonical choice `W_t = conv(⋃_{i∈t} V i)`.  The more flexible
  condition above also permits a specified containing body, which is convenient when the outer
  bodies are planks or tubes."*

In GWZ Proposition 6.6(B) the outer bodies **are** planks, so GWZ reads clause (ii) against the
plank; `ConvexSpaceBody.Factorization` hard-wires the hull.  This file settles the relation between
the two readings.

## What is proved here

* `Kakeya.FactorsDensityAt.hull` — **the plank reading implies the hull reading**, at the same
  constant and with no hypothesis beyond `V i ≤ W t`.  Hence GWZ's hypothesis for 6.6(B) is
  *stronger* than the one `Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` assumes, so that
  statement is at least as strong as GWZ Proposition 6.6(B) and needs no restatement.  This is the
  fidelity settlement.

* `Kakeya.isFrostmanIn_of_le_of_volume_le` and
  `Kakeya.GlobalPlankFactorization.isFrostmanIn_plank_of_isPlankOfDimensions` — the converse
  direction, **quantified**.  The hull reading gives the plank reading against *any* outer plank
  `P₂ ⊇ W`, with the loss `8 C³ / c₃ · (|P₂| / |W|)`, and the plank reading against a plank of
  half-widths `(a₂, b₂, 1)` costs exactly the volume ratio `a₂ b₂ / (a' b)`, where `a'` is the
  actual thin thickness of the cell hull `W`.

* `Kakeya.HasPlankEnvelope` — the residual geometric obligation isolated: an outer plank of
  half-widths comparable to `(a', b, 1)`, i.e. one that is *tight* on the hull.  Against the plank
  handed over by `Kakeya.GlobalPlankFactorization.le_plank` the loss carries the unbounded factor
  `a / a'` (`Kakeya.GlobalPlankFactorization.exists_isFrostmanIn_le_plank_of_thin_comparable` makes
  the dependence explicit); against a tight envelope the loss depends only on the comparability
  constant.

## Why this is the shape of the repair

`Kakeya.Section6PartBFactorisation.coarse_fibre_frostman` is exactly clause (ii) in the plank
reading, and it is what the tree's proved Part-(B) pipeline
(`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_of_partBData`) consumes.  Producing it from the
6.6(B) datum is therefore the bridge that the proposition's proof needs, and by the results here
that bridge is *purely* a matter of exhibiting a tight outer plank: no further Frostman input is
required.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Convexity ConvexSpaceBody

open scoped NNReal Real ENNReal

noncomputable section

namespace Kakeya

/-! ### The two readings of clause (ii) -/

section ClauseTwo

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} [DecidableEq ι]


omit [DecidableEq ι] in
/-- **Changing the ambient body of a Frostman estimate at an explicit volume cost.**

`ConvexSpaceBody.IsFrostmanIn.change_ambient` pays the exact ratio `|L| / |K|`; this packages the
ratio as a single bound `|L| ≤ L₀ · |K|`, which is the form in which the plank-versus-hull loss is
computed below. -/
theorem isFrostmanIn_of_le_of_volume_le {s : Finset ι} {V : ι → ConvexSpaceBody E}
    {K L : ConvexSpaceBody E} {C L₀ : ℝ≥0∞}
    (hFr : IsFrostmanIn s V K C) (hVK : ∀ i ∈ s, V i ≤ K) (hKL : K ≤ L)
    (hK0 : volume (K.carrier : Set E) ≠ 0)
    (hvol : volume (L.carrier : Set E) ≤ L₀ * volume (K.carrier : Set E)) :
    IsFrostmanIn s V L (C * L₀) := by
  have hsub : (K.carrier : Set E) ⊆ (L.carrier : Set E) :=
    (SetLike.coe_subset_coe (S := K) (T := L)).mp hKL
  have hL0 : volume (L.carrier : Set E) ≠ 0 := fun h =>
    hK0 (le_antisymm (h ▸ measure_mono hsub) bot_le)
  have hratio : volume (L.carrier : Set E) / volume (K.carrier : Set E) ≤ L₀ :=
    ENNReal.div_le_of_le_mul hvol
  refine (hFr.change_ambient hVK (fun i hi => (hVK i hi).trans hKL) hK0 hL0).mono ?_
  gcongr

end ClauseTwo

/-! ### The plank reading of the GWZ 6.6(B) datum -/

/-- The absolute part of the loss incurred by reading `def:Factors` clause (ii) against an outer
plank rather than against the cell hull: the ratio between the crude volume upper bound `8 a₂ b₂`
of a plank and the `Kakeya.IsPlankOfDimensions.volume_lower` lower bound for the hull. -/
def plankFrostmanLoss (C : ℝ≥0) : ℝ≥0 := 8 * C ^ 3 * (Metric.lt_volume_convexHull.c 3)⁻¹


/-- **The volume of an outer plank, against the volume of the body it wraps.**

If `W` has the dimensions of an `a' × b × 1` plank up to `C`, and `P₂` is an exact
`a₂ × b₂ × 1` plank whose transverse area is at most `K` times `a' * b`, then
`|P₂| ≤ plankFrostmanLoss C * K * |W|`.  The whole content is `8 a₂ b₂ ≤ 8 K a' b` together with
`Kakeya.IsPlankOfDimensions.volume_lower`. -/
theorem volume_plank_le_mul_volume_of_isPlankOfDimensions
    {C a' b a₂ b₂ K : ℝ≥0} {hab₂ : a₂ ≤ b₂} {hb₂1 : b₂ ≤ 1}
    {W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    (hC : 1 ≤ C) (hdimW : IsPlankOfDimensions C a' b W)
    (P₂ : Plank a₂ b₂ hab₂ hb₂1) (hcmp : a₂ * b₂ ≤ K * (a' * b)) :
    volume ((P₂.carrier : Set (EuclideanSpace ℝ (Fin 3))))
      ≤ ((plankFrostmanLoss C * K : ℝ≥0) : ℝ≥0∞) * volume (W.carrier : Set _) := by
  have hC0 : (C : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, ENNReal.coe_eq_zero]
    exact (lt_of_lt_of_le zero_lt_one hC).ne'
  have hc0 : (Metric.lt_volume_convexHull.c 3 : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (Metric.lt_volume_convexHull.c_pos 3).ne'
  have hC3ne : ((C : ℝ≥0∞) ^ 3) ≠ 0 := pow_ne_zero _ hC0
  have hC3top : ((C : ℝ≥0∞) ^ 3) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hlow := hdimW.volume_lower (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3)
  have hcoe : ((plankFrostmanLoss C * K : ℝ≥0) : ℝ≥0∞)
      = 8 * (C : ℝ≥0∞) ^ 3 * (Metric.lt_volume_convexHull.c 3 : ℝ≥0∞)⁻¹ * (K : ℝ≥0∞) := by
    rw [plankFrostmanLoss]
    push_cast [ENNReal.coe_inv (Metric.lt_volume_convexHull.c_pos 3).ne']
    ring
  set cc : ℝ≥0∞ := (Metric.lt_volume_convexHull.c 3 : ℝ≥0∞) with hccdef
  have hcancel : ((plankFrostmanLoss C * K : ℝ≥0) : ℝ≥0∞)
      * ((((C : ℝ≥0∞) ^ 3)⁻¹ * cc) * ((a' : ℝ≥0∞) * (b : ℝ≥0∞)))
      = 8 * ((K : ℝ≥0∞) * ((a' : ℝ≥0∞) * (b : ℝ≥0∞))) := by
    rw [hcoe, show 8 * (C : ℝ≥0∞) ^ 3 * cc⁻¹ * (K : ℝ≥0∞)
          * ((((C : ℝ≥0∞) ^ 3)⁻¹ * cc) * ((a' : ℝ≥0∞) * (b : ℝ≥0∞)))
        = (8 * ((K : ℝ≥0∞) * ((a' : ℝ≥0∞) * (b : ℝ≥0∞))))
          * (((C : ℝ≥0∞) ^ 3 * ((C : ℝ≥0∞) ^ 3)⁻¹) * (cc⁻¹ * cc)) from by ring,
      ENNReal.mul_inv_cancel hC3ne hC3top, ENNReal.inv_mul_cancel hc0 ENNReal.coe_ne_top,
      mul_one, mul_one]
  have hstep : (8 : ℝ≥0∞) * ((a₂ : ℝ≥0∞) * (b₂ : ℝ≥0∞))
      ≤ 8 * ((K : ℝ≥0∞) * ((a' : ℝ≥0∞) * (b : ℝ≥0∞))) := by
    refine mul_le_mul' le_rfl ?_
    exact_mod_cast hcmp
  calc volume ((P₂.carrier : Set (EuclideanSpace ℝ (Fin 3))))
      = 8 * (a₂ : ℝ≥0∞) * (b₂ : ℝ≥0∞) * ((1 : ℝ≥0) : ℝ≥0∞) := P₂.volume_carrier
    _ = 8 * ((a₂ : ℝ≥0∞) * (b₂ : ℝ≥0∞)) := by push_cast; ring
    _ ≤ 8 * ((K : ℝ≥0∞) * ((a' : ℝ≥0∞) * (b : ℝ≥0∞))) := hstep
    _ = ((plankFrostmanLoss C * K : ℝ≥0) : ℝ≥0∞)
          * ((((C : ℝ≥0∞) ^ 3)⁻¹ * cc) * ((a' : ℝ≥0∞) * (b : ℝ≥0∞))) := hcancel.symm
    _ ≤ ((plankFrostmanLoss C * K : ℝ≥0) : ℝ≥0∞) * volume (W.carrier : Set _) := by
        refine mul_le_mul' le_rfl ?_
        calc (((C : ℝ≥0∞) ^ 3)⁻¹ * cc) * ((a' : ℝ≥0∞) * (b : ℝ≥0∞))
            = ((C : ℝ≥0∞) ^ 3)⁻¹ * cc * ((a' : ℝ≥0∞) * (b : ℝ≥0∞)) := by ring
          _ ≤ volume (W.carrier : Set _) := hlow


/-! ### The datum-level plank reading -/

namespace GlobalPlankFactorization

variable {κ : Type*} [DecidableEq κ] {Cw a b ρ C₀ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
  {r : Finset κ} {Rt : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}

variable (Fz : GlobalPlankFactorization Cw a b hab hb1 r
  (fun k => (Rt k).toConvexSpaceBody) C₀)

omit [DecidableEq κ] in
/-- A cell hull with the dimensions of an `a' × b × 1` plank has positive volume. -/
theorem volume_cellBody_ne_zero {C a' : ℝ≥0} {part : Finset κ}
    (ha' : 0 < a') (hb0 : 0 < b)
    (hdimW : IsPlankOfDimensions C a' b (cellBody part Rt)) :
    volume ((cellBody part Rt).carrier : Set (EuclideanSpace ℝ (Fin 3))) ≠ 0 := by
  have hlow := hdimW.volume_lower (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3)
  have hpos : ((C : ℝ≥0∞) ^ 3)⁻¹ * (Metric.lt_volume_convexHull.c 3 : ℝ≥0∞)
      * ((a' : ℝ≥0∞) * (b : ℝ≥0∞)) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
    · exact ENNReal.inv_ne_zero.mpr (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    · exact ENNReal.coe_ne_zero.mpr (Metric.lt_volume_convexHull.c_pos 3).ne'
    · exact mul_ne_zero (ENNReal.coe_ne_zero.mpr ha'.ne')
        (ENNReal.coe_ne_zero.mpr hb0.ne')
  exact fun h => hpos (le_antisymm (h ▸ hlow) bot_le)

include Fz in
/-- **Clause (ii) against an arbitrary outer body, at an explicit volume cost.** -/
theorem isFrostmanIn_of_volume_le {part : Finset κ} (hpart : part ∈ Fz.parts)
    {L₀ : ℝ≥0∞} {L : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    (hWL : cellBody part Rt ≤ L)
    (h0 : volume ((cellBody part Rt).carrier : Set (EuclideanSpace ℝ (Fin 3))) ≠ 0)
    (hvol : volume (L.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ≤ L₀ * volume ((cellBody part Rt).carrier : Set (EuclideanSpace ℝ (Fin 3)))) :
    IsFrostmanIn part (fun k => (Rt k).toConvexSpaceBody) L ((C₀ : ℝ≥0∞) * L₀) :=
  isFrostmanIn_of_le_of_volume_le (Fz.isFrostmanIn_cellBody hpart)
    (fun _ hk => Finset.le_convexHull_biUnion (fun j => (Rt j).toConvexSpaceBody) hk) hWL h0 hvol

include Fz in
/-- **`def:Factors` clause (ii) in GWZ's reading, produced from the tree's hull reading.**

If the cell hull has the dimensions of an `a' × b × 1` plank up to `C`, and `P₂` is an exact
`a₂ × b₂ × 1` plank containing it whose transverse area is at most `K` times `a' * b`, then the
coarse fibre of the cell is Frostman **in `P₂`** with constant
`C₀ * plankFrostmanLoss C * K`.

This is exactly the field `Kakeya.Section6PartBFactorisation.coarse_fibre_frostman`, so the whole
gap between `Kakeya.GlobalPlankFactorization` and the tree's Part-(B) datum, as far as clause (ii)
is concerned, is the *tightness* hypothesis `hcmp`. -/
theorem isFrostmanIn_plank_of_isPlankOfDimensions {part : Finset κ} (hpart : part ∈ Fz.parts)
    {C a' a₂ b₂ K : ℝ≥0} {hab₂ : a₂ ≤ b₂} {hb₂1 : b₂ ≤ 1}
    (hC : 1 ≤ C) (ha' : 0 < a') (hb0 : 0 < b)
    (hdimW : IsPlankOfDimensions C a' b (cellBody part Rt))
    (P₂ : Plank a₂ b₂ hab₂ hb₂1) (hP₂ : cellBody part Rt ≤ P₂.toConvexSpaceBody)
    (hcmp : a₂ * b₂ ≤ K * (a' * b)) :
    IsFrostmanIn part (fun k => (Rt k).toConvexSpaceBody) P₂.toConvexSpaceBody
      ((C₀ : ℝ≥0∞) * ((plankFrostmanLoss C * K : ℝ≥0) : ℝ≥0∞)) :=
  Fz.isFrostmanIn_of_volume_le hpart hP₂ (volume_cellBody_ne_zero ha' hb0 hdimW)
    (volume_plank_le_mul_volume_of_isPlankOfDimensions hC hdimW P₂ hcmp)


end GlobalPlankFactorization

/-! ### The residual geometric obligation: a tight outer plank -/


namespace GlobalPlankFactorization

variable {κ : Type*} [DecidableEq κ] {Cw a b ρ C₀ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
  {r : Finset κ} {Rt : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}

variable (Fz : GlobalPlankFactorization Cw a b hab hb1 r
  (fun k => (Rt k).toConvexSpaceBody) C₀)


end GlobalPlankFactorization


/-! ### Constructing a tight plank envelope

A body whose *longest* thickness — the circumradius `Metric.thickness ℝ W 0` — is at most `1` has a
tight envelope on the nose: the exact prism `Kakeya.outerPrism W`, whose half-widths are the three
thicknesses of `W`, becomes an `a₂ × b₂ × 1` plank after the long half-width is relaxed from
`thickness ℝ W 0` up to `1`.

`Metric.thickness ℝ W 0 ≤ 1` is **not** a consequence of the GWZ 6.6(B) datum: `le_plank` gives only
`thickness ℝ W 0 ≤ a + b + 1`, and a body genuinely spanning a diagonal of its `a × b × 1` plank has
circumradius up to `√(a² + b² + 1) > 1`. This
section discharges the case that does not need one. -/

/-- The `k`-th thickness of a convex body, as a nonnegative real. -/
def thicknessNN (W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (k : ℕ) : ℝ≥0 :=
  ⟨Metric.thickness ℝ (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) k,
    Metric.thickness_nonneg _ _⟩

theorem coe_thicknessNN (W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (k : ℕ) :
    ((thicknessNN W k : ℝ≥0) : ℝ≥0∞)
      = Metric.ethickness ℝ (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) k := by
  rw [Metric.ethickness_thickness' W.isCompact'.isBounded k, thicknessNN,
    ENNReal.ofReal_eq_coe_nnreal (Metric.thickness_nonneg _ _)]
  rfl

theorem thicknessNN_le_of_ethickness_le {W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))} {k : ℕ}
    {rr : ℝ≥0}
    (h : Metric.ethickness ℝ (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) k ≤ (rr : ℝ≥0∞)) :
    thicknessNN W k ≤ rr := by
  rw [← ENNReal.coe_le_coe, coe_thicknessNN]
  exact h

theorem le_thicknessNN_of_le_ethickness {W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))} {k : ℕ}
    {rr : ℝ≥0}
    (h : (rr : ℝ≥0∞) ≤ Metric.ethickness ℝ (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) k) :
    rr ≤ thicknessNN W k := by
  rw [← ENNReal.coe_le_coe, coe_thicknessNN]
  exact h

theorem thicknessNN_antitone (W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) {m n : ℕ}
    (h : m ≤ n) : thicknessNN W n ≤ thicknessNN W m :=
  Metric.thickness_antitone W.isCompact'.isBounded h

/-- The exact outer prism of a convex body of `ℝ³`: the box whose half-widths are the three
thicknesses of the body (`Kakeya.outerPrism`). -/
def rawPrism (W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :
    PrismNDim 3 (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)) :=
  outerPrism (by simp) W.isCompact' W.nonempty'


/-! ### The circumradius side condition is checkable, and satisfied by tube blocks -/

/-- A body inside a ball of radius `R` has circumradius at most `R`.  This is the form in which
the side condition `hcirc` of
`Kakeya.GlobalPlankFactorization.exists_coarseFibreFrostman` is checked. -/
theorem thicknessNN_zero_le_of_subset_closedBall {W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {c : EuclideanSpace ℝ (Fin 3)} {R : ℝ≥0}
    (h : (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ Metric.closedBall c (R : ℝ)) :
    thicknessNN W 0 ≤ R :=
  Metric.thickness_le_of_subset_closedBall h R.coe_nonneg 0


/-! ### The headline: the Part-(B) coarse-fibre Frostman clause, from the 6.6(B) datum -/

namespace GlobalPlankFactorization

variable {κ : Type*} [DecidableEq κ] {Cw a b ρ C₀ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
  {r : Finset κ} {Rt : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}

variable (Fz : GlobalPlankFactorization Cw a b hab hb1 r
  (fun k => (Rt k).toConvexSpaceBody) C₀)

/-- The Frostman constant of the plank reading of a `Kakeya.GlobalPlankFactorization`: a fixed
polynomial in the datum's own constants `Cw` and `C₀`, with no dependence on the scales
`δ, ρ, a, b`.  With `Cw ≤ δ ^ (-η)` and `C₀ ≤ δ ^ (-η)` — the budget GWZ 6.6(B) already spends — it
is `≤ 48 · 3⁵ · δ ^ (-5 η)`, hence sub-polynomial. -/
def coarseFibreFrostmanConst (Cw C₀ : ℝ≥0) : ℝ≥0 :=
  C₀ * (plankFrostmanLoss (plankReadingConst Cw C₀) * plankReadingConst Cw C₀ ^ 2)


end GlobalPlankFactorization

end Kakeya

end

end

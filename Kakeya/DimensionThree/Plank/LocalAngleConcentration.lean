/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.BoxDensityTransfer
public import Kakeya.DimensionThree.Plank.AngleConcentration

/-!
# Markov selection, local mass bounds, and hypothesis (5) localised to the good-cover boxes

The per-representative density estimates of the Item 2 route consume five data.  Four of them are
produced by the good-cover layer.  The fifth is the *local* typical intersection-angle
concentration, hypothesis (5): for the box-local families `T_q^u ⊆ s` and the restricted shadings
`Z_q^u`,

`∑_{i,j ∈ T_q^u} |Z_q^u i ∩ Z_q^u j| ≤ Mtyp · ∑_{i,j : θ₀ - a/b ≤ ∠(Vᵢ,Vⱼ) ≤ 2θ₀} |…|`,

together with `a/b ≤ θ₀ ≤ 1`, `θ ≤ Cstar · θ₀` and the product bound `Cstar · Mtyp ≤ Ceta · a^{-η}`.
This file isolates that hypothesis as `Plank.LocalAngleConcentration`, discharges it for
*saturated* families (`Plank.localAngleConcentration_of_saturated` and its scaled variant), and
proves the two of the three inputs of
`Plank.exists_typicalIntersectionAngle_of_stableFibres` that *do* transfer from the global family
to the box-local families.

## Why (5) is not obtained by applying Phase B to the local families

`Plank.exists_typicalIntersectionAngle_of_stableFibres` needs three inputs.

* The angle *upper* bound `Kakeya.HasMaxPlankAngleBound` transfers, because shade fibres only
  shrink under restriction and `Kakeya.maxPlankAngle` is monotone: this is
  `Kakeya.HasMaxPlankAngleBound.mono`, specialised to the good-cover shape as
  `Plank.hasMaxPlankAngleBound_boxPrism`.
* The dyadic ladder length `hN` transfers, because it does not mention the family at all: the
  reduced angular range has ratio `≤ 16 · Cang · Cstab` whatever the family is
  (`Plank.exists_bandCount_uniform`).
* The *stability* clause does **not** transfer.  It is a lower bound on the maximal plank angle of
  every large sub-fibre, and the box-local family at a point `x ∈ B_q ∩ Pr u` is the set of planks
  of the representative fibre `F_u` that cross `B_q` and pass through `x` — an arbitrary subset of
  the global fibre.  Two essentially distinct planks through a common point are forced apart in
  direction only by `≍ a/b`, which is far below `θ / Cstab` in the regime of interest, so the local
  geometry alone gives no lower bound; and the restriction can isolate an angularly adjacent pair,
  so no refinement of the *global* selection is inherited either.

What the stability clause buys is exactly `Cstar`: the pigeonhole runs without it, and
`Mtyp = 2(N+1)` with `N = O(log(θb/a))` is still sub-polynomial, but a band `θ₀` at the bottom of
the ladder makes `Cstar = θ/θ₀ ≍ θb/a` polynomial in `a⁻¹` and the product bound
`Cstar · Mtyp ≤ Ceta · a^{-η}` fails.  Stability is what forces `θ₀` to the top of the range.

`Plank.LocalShadeFibreStable` names the local stability clause, and
`Plank.exists_localTypicalIntersectionAngle_of_localStability` proves (5) from it, so the
stability-based route is checked in Lean and not asserted in prose.  Note however that pointwise
local stability is *stronger* than (5) needs: it fails at any point of `B_q ∩ Pr u` whose local
fibre is a singleton, whereas (5) is an integrated statement and tolerates such points.  That is
why the hypothesis exposed to the assembly is (5) itself, `Plank.LocalAngleConcentration`, and not
the stability clause.

## `θ₀` varies with the box

Phase B chooses the band `θ₀` by a pigeonhole *inside one family*, so different `(u,q)` select
different bands and no single `θ₀` serves all of them.  The comparability constant
`Cstar = 8 · Kakeya.plankAngleScaleB a` and the loss `Mtyp = 2(N+1)` *are* uniform, since `Cstab`
does not depend on the family and `hN` does not either.  Accordingly the whole downstream chain is
stated with `θ₀` indexed by the box (and the representative), which is a strictly weaker hypothesis
than a constant `θ₀`; the constant-`θ₀` specialisations were retired once the per-box form was
available, so `Plank.LocalAngleConcentration` below is the only form the route uses.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Convexity
open scoped NNReal Real ENNReal

noncomputable section

namespace Plank

section GoodCover

variable {ι : Type*}

/-! ## Markov selection and local mass bounds for Item 2 of GWZ Lemma 6.13

This section holds the route-independent ingredients of the good-box selection: the two Markov
steps, the aggregation identity that makes a representative-level selection non-circular, the
local upper bounds on the tangential mass of one box, and the two conversions between a retained
local mass and
the data a per-representative density estimate consumes.

### The two localisations that make a box selection non-circular

A mass-level box selection over one shifted grid is global and gives no per-representative count.
Two changes localise it.

1. **The local family is the fibre-local tangential family** `T_q ∩ F_u`, not `T_q`.  This is what
   makes the bad-box charge local: by `Plank.card_tangentialBoxes_mul_le` each plank of the fibre
   is tangential to at most `64 c_tan / b` boxes of a fixed shift, so
   `Plank.badBoxes_localMass_le` charges the deleted boxes only `512 c_tan · lam · a b · #F_u` —
   the factor `b` in the box-normalised threshold cancels the `1/b` of the incidence count exactly,
   as in the global statement, but now against `#F_u` and not against `#s`.
2. **The good boxes are counted with the tangential upper bound**, not with a pointwise
   multiplicity: `|Y_i ∩ B_q ∩ P| ≤ |V_i ∩ B_q| ≤ c_tan a b²`, so a local good mass of
   `κ · c_tan · a b · #F` already forces `#(D u) ≥ κ / b`
   (`Plank.boxVolumeSum_of_goodBoxMass`).  No bound on the number of representatives meeting one
   box, and no lower bound on the fibre size, is used.

With those two, the per-representative score does **not** depend on which representatives survive,
so a selection can be a plain Markov step (`Plank.markov_retained_half`).  Its aggregate input is
`Plank.sum_fibreLocalMass_eq`: summing the fibre-local masses over the representatives reassembles
the box double sum of the whole family, hence is bounded below by the captured-mass inequality of
`Plank.exists_shift_halfBox_capture_of_fullness`.

### What used to live here

The fibre-local good-cover construction — the cover from the aggregate captured mass, its retention
accounting, and the packaging with the shift selection — has been retired.  Its only consumer was
the fibre-local Item 2 endpoint, whose exposed angular hypothesis is unsatisfiable for
repr-fibre-local families (`Plank.not_localAngleConcentration_of_singleton`).  The live route is the
saturated one: `Plank.exists_goodCover_saturated_aggregate` builds the cover and
`Plank.aggregateShading_of_goodCover` closes Item 2 from it, both C-linear in the
captured-mass density and both taking the cover fraction as a parameter rather than selecting it.
-/

/-! ### The Markov step, in the half-retention and free-threshold forms -/

/-- **Markov retention.**  If the total mass over `D` is at least `M`, and twice the mass the
threshold `τ` can discard is still at most `M`, then the members that clear the threshold carry at
least `M / 2`.  The `ENNReal` cancellation needs `M ≠ ⊤`, which is why `M` is a parameter rather
than the total mass itself.  It is applied both over boxes and over representatives. -/
theorem markov_retained_half {β : Type*} (D : Finset β) (m w : β → ℝ≥0∞) (τ M : ℝ≥0∞)
    (hM : M ≤ ∑ q ∈ D, m q) (hτw : 2 * (τ * ∑ q ∈ D, w q) ≤ M) (hMtop : M ≠ ⊤)
    (good : β → Prop) [DecidablePred good]
    (hbad : ∀ q ∈ D, ¬ good q → m q ≤ τ * w q) :
    M ≤ 2 * ∑ q ∈ D with good q, m q := by
  have h1 := markov_mass_split D m w τ good hbad
  have h3 : M ≤ (∑ q ∈ D with good q, m q) + τ * ∑ q ∈ D, w q := le_trans hM h1
  have h5 : M + M ≤ 2 * (∑ q ∈ D with good q, m q) + M := by
    calc M + M = 2 * M := by ring
      _ ≤ 2 * ((∑ q ∈ D with good q, m q) + τ * ∑ q ∈ D, w q) := mul_le_mul_right h3 2
      _ = 2 * (∑ q ∈ D with good q, m q) + 2 * (τ * ∑ q ∈ D, w q) := by ring
      _ ≤ 2 * (∑ q ∈ D with good q, m q) + M := add_le_add le_rfl hτw
  exact (ENNReal.add_le_add_iff_right hMtop).mp h5

/-- **The Markov step at a caller-chosen discard fraction.**

`Plank.markov_retained_half` is stated in the "retains at least half" form, with the factor `2`
baked in.  What a caller composing with `Plank.union_capture_of_sum_capture` needs instead is
a bound on the *discarded* mass at an arbitrary threshold `τ`, because the admissible discard
fraction is dictated by the constant multiplicity `C` and is not `1/2`.

The content is only that the bad members are bad: summing `m q ≤ τ · w q` over the members failing
`good` and enlarging the weight sum back to all of `D`.  No cancellation, no total-mass hypothesis
and no finiteness hypothesis is needed, which is why this form is strictly more flexible than the
half-retention one. -/
theorem markov_discarded_le {β : Type*} (D : Finset β) (m w : β → ℝ≥0∞) (τ : ℝ≥0∞)
    (good : β → Prop) [DecidablePred good]
    (hbad : ∀ q ∈ D, ¬ good q → m q ≤ τ * w q) :
    ∑ q ∈ D with ¬ good q, m q ≤ τ * ∑ q ∈ D, w q := by
  calc
    ∑ q ∈ D with ¬ good q, m q ≤ ∑ q ∈ D with ¬ good q, τ * w q := by
      apply Finset.sum_le_sum
      intro q hq
      rcases Finset.mem_filter.mp hq with ⟨hqD, hqbad⟩
      exact hbad q hqD hqbad
    _ = τ * ∑ q ∈ D with ¬ good q, w q := by
      rw [← Finset.mul_sum]
    _ ≤ τ * ∑ q ∈ D, w q := by
      exact mul_le_mul_right (Finset.sum_le_sum_of_subset (Finset.filter_subset _ D)) τ

/-! ### The aggregation identity -/

/-- **The fibre-local masses reassemble the tangential double sum.**  Let `rep` assign to each
member of `s` a representative in `𝒯`, and suppose each shading sits inside the carrier of its own
representative (the hypothesis `hsub` that the whole thickened-shading layer threads).
Then summing the *fibre-local* masses over the representatives recovers the full double sum:

`∑_{u ∈ 𝒯} ∑_{q ∈ 𝒦} ∑_{i ∈ T_q, rep i = u} |Y_i ∩ B_q ∩ Pc u| = ∑_{q ∈ 𝒦} ∑_{i ∈ T_q} |Y_i ∩
B_q|`.

This is what makes a representative-level selection non-circular: its aggregate input is
the captured-mass inequality of `Plank.exists_shift_halfBox_capture_of_fullness`, which is a
statement about the whole family, while the per-representative score is a fixed function of the
data.  Pure index
shuffling plus `hsub`; no geometry, no measurability. -/
theorem sum_fibreLocalMass_eq {σ : Type*} [DecidableEq σ] (𝒯 : Finset σ)
    (𝒦 : Finset (Fin 3 → ℤ)) (s : Finset ι) (T : (Fin 3 → ℤ) → Finset ι) (rep : ι → σ)
    (B : (Fin 3 → ℤ) → Set (EuclideanSpace ℝ (Fin 3)))
    (Pc : σ → Set (EuclideanSpace ℝ (Fin 3)))
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (hTs : ∀ q, T q ⊆ s) (hmaps : ∀ i ∈ s, rep i ∈ 𝒯)
    (hsub : ∀ i ∈ s, (Y i).shade ⊆ Pc (rep i)) :
    ∑ u ∈ 𝒯, ∑ q ∈ 𝒦, ∑ i ∈ (T q).filter (fun i => rep i = u),
        volume ((Y i).shade ∩ B q ∩ Pc u)
      = ∑ q ∈ 𝒦, ∑ i ∈ T q, volume ((Y i).shade ∩ B q) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hTq_s : T q ⊆ s := hTs q
  have hmaps_Tq : ∀ i ∈ T q, rep i ∈ 𝒯 := by
    intro i hi; exact hmaps i (hTq_s hi)
  calc
    ∑ u ∈ 𝒯, ∑ i ∈ (T q).filter (fun i => rep i = u), volume ((Y i).shade ∩ B q ∩ Pc u)
        = ∑ u ∈ 𝒯, ∑ i ∈ (T q).filter (fun i => rep i = u), volume ((Y i).shade ∩ B q) := by
      refine Finset.sum_congr rfl fun u hu => ?_
      refine Finset.sum_congr rfl fun i hi => ?_
      rcases Finset.mem_filter.mp hi with ⟨hiTq, hrep⟩
      have hi_s : i ∈ s := hTq_s hiTq
      have h_sub_inter : (Y i).shade ∩ B q ⊆ Pc (rep i) :=
        (Set.inter_subset_left (s := (Y i).shade) (t := B q)).trans (hsub i hi_s)
      calc
        volume ((Y i).shade ∩ B q ∩ Pc u)
            = volume ((Y i).shade ∩ B q ∩ Pc (rep i)) := by rw [hrep]
        _ = volume ((Y i).shade ∩ B q) := by
          rw [Set.inter_eq_left.mpr h_sub_inter]
    _ = ∑ i ∈ T q, volume ((Y i).shade ∩ B q) := by
      rw [Finset.sum_fiberwise_of_maps_to hmaps_Tq]

/-! ### The local upper bounds -/

/-- **The tangential mass of one box, from above.**  Every tangential piece obeys
`|Y_i ∩ B_q ∩ P| ≤ |V_i ∩ B_q| ≤ c_tan a b²`, the second inequality being the *upper* half of the
tangential comparability.  Summing over the local family gives a bound proportional to the local
family's cardinality and to the box scale `a b²` — never to the box volume `8 θ b³`.  This is the
estimate that replaces a pointwise-multiplicity bound in the good-box count below, and it is why no
`N_ov` enters this layer. -/
theorem fibreLocalMass_box_le {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1}
    (cTan : ℝ≥0) (S : Slab θ hθ1) (sh : Fin 3 → ℝ) (q : Fin 3 → ℤ)
    (F : Finset ι) (V : ι → Plank a b hab hb1)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (P : Set (EuclideanSpace ℝ (Fin 3)))
    (hshV : ∀ i ∈ F, (Y i).shade ⊆ ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (htan : ∀ i ∈ F, Kakeya.ComparableScalars cTan
      (volume (((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
        (shiftedSlabBox S b sh q).carrier)).toNNReal (a * b ^ 2)) :
    ∑ i ∈ F, volume ((Y i).shade ∩
        ((shiftedSlabBox S b sh q).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩ P)
      ≤ (F.card : ℝ≥0∞) * ((cTan * (a * b ^ 2) : ℝ≥0) : ℝ≥0∞) := by
  refine (Finset.sum_le_sum (g := fun _ => ((cTan * (a * b ^ 2) : ℝ≥0) : ℝ≥0∞))
    fun i hi => ?_).trans_eq (by rw [Finset.sum_const, nsmul_eq_mul])
  have hfin : volume (((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
      ((shiftedSlabBox S b sh q).carrier : Set (EuclideanSpace ℝ (Fin 3)))) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [Prism3D.volume_carrier (V i)]; simp; finiteness)
      (measure_mono Set.inter_subset_left)
  refine (measure_mono (Set.inter_subset_left.trans
    (Set.inter_subset_inter_left _ (hshV i hi)))).trans ?_
  rw [← ENNReal.coe_toNNReal hfin]
  exact_mod_cast (htan i hi).1

/-- **The local bad-box charge, with the `1/b` cancelled.**  For a *fibre-local* family
`Tq q ⊆ F`, the mass that a Markov step at the box-normalised threshold `τ = b · lam` can discard
is at most

`τ · ∑_q #(Tq q) · 8ab = 8 lam · ((∑_q #(Tq q)) · a b²) ≤ 512 c_tan · lam · a b · #F`,

by `Plank.sum_card_tangential_mul_le` applied to the fibre `F`: the extra factor `b` in `τ` cancels
the `1/b` of the incidence count exactly.  The bound involves only `#F`, not `#s`, which is what
localises the box-level Markov step to a single representative. -/
theorem badBoxes_localMass_le {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1}
    (cTan lam : ℝ≥0) (S : Slab θ hθ1) (hb : 0 < b) (hθ : 0 < θ) (sh : Fin 3 → ℝ)
    (𝒦 : Finset (Fin 3 → ℤ)) (F : Finset ι) (V : ι → Plank a b hab hb1)
    (Tq : (Fin 3 → ℤ) → Finset ι) (hTsub : ∀ q, Tq q ⊆ F)
    (htan : ∀ q, ∀ i ∈ Tq q, Kakeya.ComparableScalars cTan
      (volume (((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
        (shiftedSlabBox S b sh q).carrier)).toNNReal (a * b ^ 2)) :
    ((b * lam : ℝ≥0) : ℝ≥0∞) *
        ∑ q ∈ 𝒦, (((Tq q).card : ℝ≥0∞) * ((8 * a * b : ℝ≥0) : ℝ≥0∞))
      ≤ ((512 * cTan * lam * (a * b) : ℝ≥0) : ℝ≥0∞) * (F.card : ℝ≥0∞) := by
  calc ((b * lam : ℝ≥0) : ℝ≥0∞) *
        ∑ q ∈ 𝒦, (((Tq q).card : ℝ≥0∞) * ((8 * a * b : ℝ≥0) : ℝ≥0∞))
      = ((b * lam : ℝ≥0) : ℝ≥0∞) *
          ((∑ q ∈ 𝒦, ((Tq q).card : ℝ≥0∞)) * ((8 * a * b : ℝ≥0) : ℝ≥0∞)) := by
        rw [← Finset.sum_mul]
      _ = ((8 * lam : ℝ≥0) : ℝ≥0∞) *
          ((∑ q ∈ 𝒦, ((Tq q).card : ℝ≥0∞)) * ((a * b ^ 2 : ℝ≥0) : ℝ≥0∞)) := by
        push_cast; ring
      _ ≤ ((8 * lam : ℝ≥0) : ℝ≥0∞) *
          (((64 * cTan * a * b : ℝ≥0) : ℝ≥0∞) * (F.card : ℝ≥0∞)) := by
        have hX := sum_card_tangential_mul_le cTan S hb hθ sh 𝒦 F V Tq hTsub htan
        exact mul_le_mul_right hX ((8 * lam : ℝ≥0) : ℝ≥0∞)
      _ = ((512 * cTan * lam * (a * b) : ℝ≥0) : ℝ≥0∞) * (F.card : ℝ≥0∞) := by
        push_cast; ring

/-! ### From a retained local mass to the density data -/

/-- **Box-normalised local fullness from the Markov threshold.**  A nonempty local family whose
shading mass clears `b · lam` times its total carrier volume `#T · 8ab` has box-normalised local
fullness at least `b · lam`, which is hypothesis (4) of
`Plank.denseBoxEstimate_boxNormalised_combined` in the form the per-representative density
estimates consume. -/
theorem localFullness_of_goodBox {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (lam : ℝ≥0) (T : Finset ι) (V : ι → Plank a b hab hb1)
    (Z : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (ha : 0 < a) (hb : 0 < b) (hne : T.Nonempty)
    (hZcar : ∀ i ∈ T, (Z i).carrier = (V i).carrier)
    (hgood : ((b * lam : ℝ≥0) : ℝ≥0∞) *
        ((T.card : ℝ≥0∞) * ((8 * a * b : ℝ≥0) : ℝ≥0∞))
      ≤ ∑ i ∈ T, volume (Z i).shade) :
    b * lam ≤ ShadedBody.fullness T Z := by
  -- Compute the total carrier volume
  have hcar : ∑ i ∈ T, volume ((Z i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = (T.card : ℝ≥0∞) * ((8 * a * b : ℝ≥0) : ℝ≥0∞) := by
    calc
      ∑ i ∈ T, volume ((Z i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
          = ∑ i ∈ T, volume ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))) :=
            Finset.sum_congr rfl fun i hi => by rw [hZcar i hi]
      _ = ∑ i ∈ T, (8 * (a : ℝ≥0∞) * (b : ℝ≥0∞)) :=
        Finset.sum_congr rfl fun i hi => by
          rw [Prism3D.volume_carrier (V i)]
          simp
      _ = (T.card : ℝ≥0∞) * (8 * (a : ℝ≥0∞) * (b : ℝ≥0∞)) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ = (T.card : ℝ≥0∞) * ((8 * a * b : ℝ≥0) : ℝ≥0∞) := by
        push_cast
        ring
  -- Denominator is nonzero (finite positive)
  have hwne : ∑ i ∈ T, volume ((Z i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ≠ 0 := by
    rw [hcar]
    refine mul_ne_zero ?_ ?_
    · exact mod_cast (Finset.card_pos.mpr hne).ne'
    · exact ENNReal.coe_ne_zero.mpr (by positivity)
  -- Denominator is not ∞
  have hwtop : ∑ i ∈ T, volume ((Z i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ≠ ⊤ := by
    rw [hcar]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.coe_ne_top
  -- Convert to ENNReal and use the division condition of fullness
  rw [← ENNReal.coe_le_coe, ShadedBody.coe_fullness T Z]
  rw [ShadedBody.fullness']
  refine (ENNReal.le_div_iff_mul_le (Or.inl hwne) (Or.inl hwtop)).mpr ?_
  rw [hcar]
  exact hgood

/-- **The box count from a good-box mass, at an arbitrary cut region.**  If the boxes of `Dg` carry
local tangential mass at least `κ · c_tan · a b · #F` for the fibre `F`, then, since each box
carries at most `#F · c_tan · a b²` of it (`Plank.fibreLocalMass_box_le`), there are at least
`κ / b` of them; as every grid box has volume `8 θ b³`, this is exactly the covering inequality

`κ · 8θb² ≤ ∑_{q ∈ Dg} |B_q|`

that the per-representative density estimates consume.  The fibre size `#F` cancels between the two
sides, so the count does not degrade as fibres grow; only `κ` and `c_tan` enter.

The region enters only as the ambient set of `Plank.fibreLocalMass_box_le`, so it is an arbitrary
set `Pset` rather than a typed prism: that is what the saturated route needs once the shadings are
cut by a fixed *dilation* of the representative. -/
theorem boxVolumeSum_of_goodBoxMass {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1}
    (cTan κ : ℝ≥0) (hcTan : 1 ≤ cTan) (S : Slab θ hθ1) (sh : Fin 3 → ℝ)
    (Dg : Finset (Fin 3 → ℤ)) (F : Finset ι) (V : ι → Plank a b hab hb1)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (Tq : (Fin 3 → ℤ) → Finset ι) (Pset : Set (EuclideanSpace ℝ (Fin 3)))
    (ha : 0 < a) (hb : 0 < b) (hFne : F.Nonempty)
    (hTsub : ∀ q, Tq q ⊆ F)
    (hshV : ∀ i ∈ F, (Y i).shade ⊆ ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (htan : ∀ q, ∀ i ∈ Tq q, Kakeya.ComparableScalars cTan
      (volume (((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
        (shiftedSlabBox S b sh q).carrier)).toNNReal (a * b ^ 2))
    (hgood : ((κ * cTan * (a * b) : ℝ≥0) : ℝ≥0∞) * (F.card : ℝ≥0∞)
      ≤ ∑ q ∈ Dg, ∑ i ∈ Tq q, volume ((Y i).shade ∩
          ((shiftedSlabBox S b sh q).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩ Pset)) :
    (κ : ℝ≥0∞) * ((8 * θ * b * b : ℝ≥0) : ℝ≥0∞)
      ≤ ∑ q ∈ Dg, volume ((shiftedSlabBox S b sh q).carrier) := by
  -- (1) The retained mass is at most `#Dg · (#F · c_tan a b²)`.
  have h_main : ((κ * cTan * (a * b) : ℝ≥0) : ℝ≥0∞) * (F.card : ℝ≥0∞) ≤
      (Dg.card : ℝ≥0∞) * ((F.card : ℝ≥0∞) * ((cTan * (a * b ^ 2) : ℝ≥0) : ℝ≥0∞)) :=
    hgood.trans ((Finset.sum_le_sum fun q _ =>
      (fibreLocalMass_box_le cTan S sh q (Tq q) V Y Pset
            (fun i hi => hshV i (hTsub q hi)) (htan q)).trans
        (mul_le_mul_left (Nat.cast_le.mpr (Finset.card_le_card (hTsub q))) _)).trans_eq
      (by rw [Finset.sum_const, nsmul_eq_mul]))
  -- (2) Cancel the common factor `#F · c_tan a b`, leaving `κ ≤ #Dg · b`.
  set C : ℝ≥0∞ := (F.card : ℝ≥0∞) * ((cTan * (a * b) : ℝ≥0) : ℝ≥0∞) with hCdef
  have h_kappa_bound : (κ : ℝ≥0∞) ≤ (Dg.card : ℝ≥0∞) * (b : ℝ≥0∞) := by
    refine (ENNReal.mul_le_mul_iff_right (a := C)
      (mul_ne_zero (Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hFne).ne')
        (ENNReal.coe_ne_zero.mpr
          (mul_pos (lt_of_lt_of_le zero_lt_one hcTan) (mul_pos ha hb)).ne'))
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.coe_ne_top)).mp ?_
    calc C * (κ : ℝ≥0∞) = ((κ * cTan * (a * b) : ℝ≥0) : ℝ≥0∞) * (F.card : ℝ≥0∞) := by
          rw [hCdef]; push_cast; ring
      _ ≤ (Dg.card : ℝ≥0∞) * ((F.card : ℝ≥0∞) * ((cTan * (a * b ^ 2) : ℝ≥0) : ℝ≥0∞)) :=
          h_main
      _ = C * ((Dg.card : ℝ≥0∞) * (b : ℝ≥0∞)) := by rw [hCdef]; push_cast; ring
  -- (3) `|B_q| = 8θb³` turns the count into the covering inequality.
  have h_box_sum : ∑ q ∈ Dg, volume ((shiftedSlabBox S b sh q).carrier) =
      (Dg.card : ℝ≥0∞) * ((8 * θ * b * b * b : ℝ≥0) : ℝ≥0∞) := by
    have h_box_vol : ∀ q : Fin 3 → ℤ, volume ((shiftedSlabBox S b sh q).carrier) =
        ((8 * θ * b * b * b : ℝ≥0) : ℝ≥0∞) := fun q => by
      rw [shiftedSlabBox_volume S b sh q]; push_cast; ring
    simp_rw [h_box_vol]
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [h_box_sum]
  calc (κ : ℝ≥0∞) * ((8 * θ * b * b : ℝ≥0) : ℝ≥0∞)
      ≤ ((Dg.card : ℝ≥0∞) * (b : ℝ≥0∞)) * ((8 * θ * b * b : ℝ≥0) : ℝ≥0∞) :=
        mul_le_mul_left h_kappa_bound _
    _ = (Dg.card : ℝ≥0∞) * ((8 * θ * b * b * b : ℝ≥0) : ℝ≥0∞) := by push_cast; ring

end GoodCover

/-! ## The two Phase-B inputs that transfer to the box-local families -/


/-- **The dyadic ladder length `hN` is family-independent.**  The reduced angular range of
`Plank.exists_typicalIntersectionAngle_of_stableFibres` runs from
`ρ = max (a/b) (θ / (8 Cstab))` to `2 · Cang · θ`, and `2 Cang θ / ρ ≤ 16 · Cang · Cstab` whatever
`a/b` is.  So one `N`, with the bound on `N` that `Plank.exists_combined_absorption` consumes,
serves *every* subfamily of the configuration simultaneously — in particular every box-local
family `T_q^u` of a good cover. -/
theorem exists_bandCount_uniform {a b θ Cang : ℝ≥0} (Cstab : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hθ : 0 < θ) (hCang : 1 ≤ Cang) (hCstab : 1 ≤ Cstab) :
    ∃ N : ℕ,
      2 * (Cang : ℝ) * (θ : ℝ)
          ≤ 2 ^ N * max ((a / b : ℝ≥0) : ℝ) ((θ : ℝ) / (8 * Cstab)) ∧
        (N : ℝ) ≤ Real.logb 2 (16 * (Cang : ℝ) * Cstab) + 1 := by
  have hb' : (0 : ℝ) < b := mod_cast hb
  have hθ' : (0 : ℝ) < θ := mod_cast hθ
  have hCang' : (1 : ℝ) ≤ Cang := mod_cast hCang
  have hab_pos : 0 < ((a / b : ℝ≥0) : ℝ) := by
    rw [NNReal.coe_div]; exact div_pos (mod_cast ha) hb'
  have h8 : (0 : ℝ) < 8 * Cstab := by linarith
  set ρ := max ((a / b : ℝ≥0) : ℝ) ((θ : ℝ) / (8 * Cstab)) with hρ
  have hρ_pos : 0 < ρ := hab_pos.trans_le (le_max_left _ _)
  obtain ⟨N, hN_mul, hN_log⟩ := Plank.exists_pow_two_mul_ge ρ (2 * (Cang : ℝ) * (θ : ℝ)) hρ_pos
  refine ⟨N, hN_mul, ?_⟩
  have hCC : (1 : ℝ) * 1 ≤ (Cang : ℝ) * Cstab :=
    mul_le_mul hCang' hCstab zero_le_one (by linarith)
  have h_ratio_bound : max ((2 * (Cang : ℝ) * (θ : ℝ)) / ρ) 1 ≤ 16 * (Cang : ℝ) * Cstab := by
    refine max_le ?_ (by linarith)
    rw [div_le_iff₀ hρ_pos]
    have h := (div_le_iff₀ h8).mp (le_max_right ((a / b : ℝ≥0) : ℝ) ((θ : ℝ) / (8 * Cstab)))
    linarith [mul_le_mul_of_nonneg_left h
      (mul_nonneg zero_le_two (NNReal.coe_nonneg Cang) : (0 : ℝ) ≤ 2 * (Cang : ℝ))]
  have := Real.logb_le_logb_of_le (b := 2) (by norm_num)
    (zero_lt_one.trans_le (le_max_right _ _)) h_ratio_bound
  linarith

/-! ## The local stability clause, and the concentration it yields -/

/-- **Local angular stability of the shade fibres of one box-local family.**  The stability clause
of `Plank.exists_typicalIntersectionAngle_of_stableFibres`, asked of the family `(T, Z)` instead of
the global family: at every point of the local union, every sub-fibre retaining an `A⁻¹`-fraction
of the fibre still has maximal plank angle at least `θ / Cstab`.

This is a genuine angular (incidence) statement about the planks, not a density statement.  It is
*not* implied by the global stability clause: the local fibre at `x` is an arbitrary subset of the
global fibre at `x`, and it is exactly as large as the good cover happens to make it.  It is also
strictly stronger than what `Plank.LocalAngleConcentration` needs, since it fails at any point
whose local fibre is a singleton (`Kakeya.maxPlankAngle` of a singleton is the floor `a/b`). -/
def LocalShadeFibreStable {ι : Type*} {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (V : ι → Plank a b hab hb1) (T : Finset ι)
    (Z : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (θ : ℝ≥0) (Cstab A : ℝ) : Prop :=
  ∀ x ∈ ⋃ i ∈ T, (Z i).shade, ∀ t ⊆ Kakeya.shadeFibre T Z x,
    A⁻¹ * ((Kakeya.shadeFibre T Z x).card : ℝ) ≤ (t.card : ℝ) →
      (θ : ℝ) / Cstab ≤ ((Kakeya.maxPlankAngle V t : ℝ≥0) : ℝ)

/-- **Local stability from global stability and pointwise fibre retention.**  The one route by
which the stability clause *can* be transported: if the local fibre keeps an `A'⁻¹`-fraction of the
global fibre at every point of the local union, then a sub-fibre keeping an `A⁻¹`-fraction of the
local fibre keeps an `(A·A')⁻¹`-fraction of the global one, so global stability at scale `A · A'`
gives local stability at scale `A` with the *same* `Cstab`.

This isolates the missing geometric input of the stability route: a lower bound on how much of a
shade fibre survives the restriction to one tangential box of one representative prism.  Note that
the reps partition `s`, so such a retention bound cannot hold with a uniform `A'` for many
representatives at once; the honest form of the retention statement is relative to the
representative fibre `F_u`, and supplying it is exactly the open part. -/
theorem localShadeFibreStable_of_fibreRetention {ι : Type*} {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {s T : Finset ι} {V : ι → Plank a b hab hb1}
    {Y Z : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} {θ : ℝ≥0} {Cstab A A' : ℝ}
    (hA : 0 < A)
    (hTs : T ⊆ s) (hZ : ∀ i ∈ T, (Z i).shade ⊆ (Y i).shade)
    (hret : ∀ x ∈ ⋃ i ∈ T, (Z i).shade,
      A'⁻¹ * ((Kakeya.shadeFibre s Y x).card : ℝ) ≤ ((Kakeya.shadeFibre T Z x).card : ℝ))
    (hglob : ∀ x ∈ ⋃ i ∈ s, (Y i).shade, ∀ t ⊆ Kakeya.shadeFibre s Y x,
      (A * A')⁻¹ * ((Kakeya.shadeFibre s Y x).card : ℝ) ≤ (t.card : ℝ) →
        (θ : ℝ) / Cstab ≤ ((Kakeya.maxPlankAngle V t : ℝ≥0) : ℝ)) :
    LocalShadeFibreStable V T Z θ Cstab A := by
  intro x hx t ht hcard
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
  have hfibre_sub : Kakeya.shadeFibre T Z x ⊆ Kakeya.shadeFibre s Y x := fun j hj => by
    rw [Kakeya.mem_shadeFibre] at hj ⊢
    exact ⟨hTs hj.1, hZ j hj.1 hj.2⟩
  refine hglob x (Set.mem_iUnion₂.mpr ⟨i, hTs hi, hZ i hi hxi⟩) t (ht.trans hfibre_sub) ?_
  rw [mul_inv, mul_assoc]
  exact (mul_le_mul_of_nonneg_left (hret x hx) (inv_nonneg.mpr hA.le)).trans hcard

/-! ### Saturated local families: the case where the fibre is not lost at all -/

/-- **The shade fibre of a *saturated* local family is the global shade fibre.**  Call a local
family `T ⊆ s` *saturated for a region `R`* when every member of `s` with a shaded point in `R`
belongs to `T`.  If moreover the local shading is the restriction of the global one to `R`, then at
every point of the local union the local fibre contains — hence equals, by the automatic reverse
inclusion — the global fibre.

This is the whole content of the saturated condition: the restriction to `R` is invisible to the
fibre at points of `R`, so a saturated family loses nothing and the retention constant of
`Plank.localShadeFibreStable_of_fibreRetention` is `1`.  A family restricted to one representative
fibre `F_u` is never saturated, and that is not repairable: the fibres partition `s`, so at a point
where planks of several representatives meet, the `F_u`-part is a proper subset of the global
fibre. -/
theorem shadeFibre_subset_of_saturated {ι : Type*} {s T : Finset ι}
    {Y Z : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    (R : Set (EuclideanSpace ℝ (Fin 3)))
    (hZ : ∀ i ∈ T, (Z i).shade = (Y i).shade ∩ R)
    (hsat : ∀ i ∈ s, ∀ x ∈ (Y i).shade, x ∈ R → i ∈ T)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ ⋃ i ∈ T, (Z i).shade) :
    Kakeya.shadeFibre s Y x ⊆ Kakeya.shadeFibre T Z x := by
  -- from `hx` get some `j ∈ T` with `x ∈ (Z j).shade = (Y j).shade ∩ R`, so `x ∈ R`
  obtain ⟨j, hjT, hxZj⟩ := Set.mem_iUnion₂.mp hx
  rw [hZ j hjT] at hxZj
  intro i hi
  rw [Kakeya.mem_shadeFibre] at hi ⊢
  -- `hsat` puts `i` in `T`, and then `hZ i` puts `x` in `(Z i).shade`
  have hiT : i ∈ T := hsat i hi.1 x hi.2 hxZj.2
  exact ⟨hiT, by rw [hZ i hiT]; exact ⟨hi.2, hxZj.2⟩⟩

/-- **Local stability from global stability, with no loss.**  The case `A' = 1` of
`Plank.localShadeFibreStable_of_fibreRetention`: if the local fibre contains the global fibre at
every point of the local union — which is what `Plank.shadeFibre_subset_of_saturated` gives for a
saturated family — then the global stability clause transfers to `Plank.LocalShadeFibreStable` with
the *same* `A` and the same `Cstab`.

This is the step that the repr-fibre-local route could not take: there the retention constant would
have to bound the global fibre by its `F_u`-part, and no uniform constant does that for several
representatives at one point (see the note on
`Plank.localShadeFibreStable_of_fibreRetention`). -/
theorem localShadeFibreStable_of_fibreEq {ι : Type*} {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {s T : Finset ι} {V : ι → Plank a b hab hb1}
    {Y Z : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} {θ : ℝ≥0} {Cstab A : ℝ}
    (hA : 0 < A) (hTs : T ⊆ s) (hZ : ∀ i ∈ T, (Z i).shade ⊆ (Y i).shade)
    (hfib : ∀ x ∈ ⋃ i ∈ T, (Z i).shade,
      Kakeya.shadeFibre s Y x ⊆ Kakeya.shadeFibre T Z x)
    (hglob : ∀ x ∈ ⋃ i ∈ s, (Y i).shade, ∀ t ⊆ Kakeya.shadeFibre s Y x,
      A⁻¹ * ((Kakeya.shadeFibre s Y x).card : ℝ) ≤ (t.card : ℝ) →
        (θ : ℝ) / Cstab ≤ ((Kakeya.maxPlankAngle V t : ℝ≥0) : ℝ)) :
    LocalShadeFibreStable V T Z θ Cstab A := by
  refine localShadeFibreStable_of_fibreRetention (A' := (1 : ℝ)) hA hTs hZ (fun x hx => ?_)
    (fun x hx t ht hcard => hglob x hx t ht (by simpa using hcard))
  rw [inv_one, one_mul]
  exact mod_cast Finset.card_le_card (hfib x hx)

/-- **Hypothesis (5): the local typical intersection-angle concentration.**  The single remaining
input of Item 2, named once.  For the good-cover data `(𝒯', D, T_q^u, Z_q^u)` there are a band
`θ₀ u q ∈ [a/b, 1]` for each retained representative `u` and each of its good boxes `q`, and
*uniform* constants `Cstar`, `Mtyp` with `Cstar · Mtyp ≤ Ceta · a^{-η}`, such that `θ ≤ Cstar · θ₀`
and the pairwise intersection mass of the local family concentrates, with loss `Mtyp`, on the pairs
whose plank angle lies in `[θ₀ - a/b, 2θ₀]`.

`Cstar` and `Mtyp` are uniform over `(u,q)` — Phase B returns `Cstar = 8·Kakeya.plankAngleScaleB a`
and `Mtyp = 2(N+1)` with `N` family-independent — but `θ₀` is not: the band is chosen by a
pigeonhole inside one family.  Everything downstream is proved for this per-box form; see
`Plank.aggregateShading_of_goodCover`. -/
def LocalAngleConcentration {ι σ : Type*} {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (V : ι → Plank a b hab hb1) (θ : ℝ≥0)
    (𝒯' : Finset σ) (D : σ → Finset (Fin 3 → ℤ))
    (Tq : σ → (Fin 3 → ℤ) → Finset ι)
    (Z : σ → (Fin 3 → ℤ) → ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (Ceta : ℝ≥0) (η : ℝ) : Prop :=
  ∃ (θ0 : σ → (Fin 3 → ℤ) → ℝ) (Cstar Mtyp : ℝ≥0),
    (Cstar : ℝ≥0∞) * (Mtyp : ℝ≥0∞) ≤ (Ceta : ℝ≥0∞) * (a : ℝ≥0∞) ^ (-η) ∧
      ∀ u ∈ 𝒯', ∀ q ∈ D u,
        ((a / b : ℝ≥0) : ℝ) ≤ θ0 u q ∧ θ0 u q ≤ 1 ∧ (θ : ℝ) ≤ (Cstar : ℝ) * θ0 u q ∧
          (∑ i ∈ Tq u q, ∑ j ∈ Tq u q, volume ((Z u q i).shade ∩ (Z u q j).shade))
            ≤ (Mtyp : ℝ≥0∞) * (∑ i ∈ Tq u q, ∑ j ∈ Tq u q with
                (θ0 u q - ((a / b : ℝ≥0) : ℝ) ≤ Prism3D.angle (V i) (V j) ∧
                  Prism3D.angle (V i) (V j) ≤ 2 * θ0 u q),
              volume ((Z u q i).shade ∩ (Z u q j).shade))


/-- **Hypothesis (5) from local stability, at a rescaled stability constant.**
`Plank.exists_localTypicalIntersectionAngle_of_localStability` with the stability scale
`Kakeya.plankAngleScaleB a` replaced by `K · Kakeya.plankAngleScaleB a` for a fixed `K ≥ 1`.  The
losses become `Cstar = 8 K · Kakeya.plankAngleScaleB a` and `Mtyp = 2(N+1)`, and the product
bound is `Plank.exists_combined_absorption_scaled`; `Plank.exists_bandCount_uniform` is already
stated for an arbitrary stability constant, so nothing else changes.  Like the unscaled form,
this holds for every
`0 < a < 1`: the rescaling by `K` is absorbed into the uniform `Ceta`. -/
theorem exists_localTypicalIntersectionAngle_of_localStability_scaled
    (K Cang : ℝ≥0) (hK : 1 ≤ K) (hCang : 1 ≤ Cang) {η : ℝ} (hη : 0 < η) :
    ∃ Ceta : ℝ≥0, 0 < Ceta ∧
      ∀ {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι σ : Type*}
        (s : Finset ι) (V : ι → Plank a b hab hb1)
        (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (𝒯' : Finset σ) (D : σ → Finset (Fin 3 → ℤ))
        (Tq : σ → (Fin 3 → ℤ) → Finset ι)
        (Z : σ → (Fin 3 → ℤ) → ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (A : ℝ),
        0 < a → a < 1 → 0 < b → 0 < θ → θ ≤ 1 → 2 ≤ A →
        Kakeya.HasMaxPlankAngleBound s Y V θ Cang →
        (∀ u ∈ 𝒯', ∀ q ∈ D u, Tq u q ⊆ s) →
        (∀ u ∈ 𝒯', ∀ q ∈ D u, ∀ i ∈ Tq u q, (Z u q i).shade ⊆ (Y i).shade) →
        (∀ u ∈ 𝒯', ∀ q ∈ D u,
          LocalShadeFibreStable V (Tq u q) (Z u q) θ
            ((K : ℝ) * Kakeya.plankAngleScaleB a) A) →
        LocalAngleConcentration V θ 𝒯' D Tq Z Ceta η := by
  -- Step 1: obtain Ceta from Plank.exists_combined_absorption_scaled
  obtain ⟨Ceta, hCetapos, habs⟩ := Plank.exists_combined_absorption_scaled K Cang hK hη
  refine ⟨Ceta, hCetapos, ?_⟩
  intro a b θ hab hb1 ι σ s V Y 𝒯' D Tq Z A ha ha1' hb hθ hθ1 hA hang_global hTs hZsub hstab
  have hCstab : 1 ≤ (K : ℝ) * Kakeya.plankAngleScaleB a := by
    have h_one_lt_B : 1 < Kakeya.plankAngleScaleB a := Kakeya.one_lt_plankAngleScaleB ha ha1'
    have hK' : (1 : ℝ) ≤ K := mod_cast hK
    nlinarith
  set Cstab := (K : ℝ) * Kakeya.plankAngleScaleB a with hCstab_def
  -- Step 2: obtain N from exists_bandCount_uniform, and set the uniform losses
  obtain ⟨N, hN, hNlog⟩ := Plank.exists_bandCount_uniform (a := a) (b := b) (θ := θ) (Cang := Cang)
    Cstab ha hb hθ hCang hCstab
  set Cstar := (8 * Cstab).toNNReal with hCstar_def
  set Mtyp := ((2 * (N + 1 : ℕ) : ℕ) : ℝ≥0) with hMtyp_def
  have h_Cstar_real : (Cstar : ℝ) = 8 * Cstab := Real.coe_toNNReal _ (by linarith)
  -- Step 3: box by box, apply exists_typicalIntersectionAngle_of_stableFibres
  have h_ex : ∀ (u : σ) (q : Fin 3 → ℤ), ∃ θ0 : ℝ, u ∈ 𝒯' → q ∈ D u →
      ((a / b : ℝ≥0) : ℝ) ≤ θ0 ∧ θ0 ≤ 1 ∧ (θ : ℝ) ≤ (Cstar : ℝ) * θ0 ∧
        (∑ i ∈ Tq u q, ∑ j ∈ Tq u q, volume ((Z u q i).shade ∩ (Z u q j).shade))
          ≤ (Mtyp : ℝ≥0∞) * (∑ i ∈ Tq u q, ∑ j ∈ Tq u q with
              (θ0 - ((a / b : ℝ≥0) : ℝ) ≤ Prism3D.angle (V i) (V j) ∧
                Prism3D.angle (V i) (V j) ≤ 2 * θ0),
            volume ((Z u q i).shade ∩ (Z u q j).shade)) := by
    intro u q
    by_cases hu : u ∈ 𝒯'
    · by_cases hq : q ∈ D u
      · obtain ⟨θ0, h1, h2, h3, h4⟩ :=
          exists_typicalIntersectionAngle_of_stableFibres (V := V) (T := Tq u q) (Z := Z u q)
            (θ := θ) (Cang := Cang) (Cstab := Cstab) (A := A) (N := N)
            ha hb hθ1 hA hCstab (hang_global.mono (hTs u hu q hq) (hZsub u hu q hq))
            (hstab u hu q hq) hN
        exact ⟨θ0, fun _ _ => ⟨h1, h2, h_Cstar_real ▸ h3, h4⟩⟩
      · exact ⟨1, fun _ hq' => absurd hq' hq⟩
    · exact ⟨1, fun hu' => absurd hu' hu⟩
  choose θ0 hθ0 using h_ex
  exact ⟨θ0, Cstar, Mtyp, habs ha ha1' N hNlog, fun u hu q hq => hθ0 u q hu hq⟩

/-- **Hypothesis (5) for saturated families, at a rescaled stability constant.**
`Plank.localAngleConcentration_of_saturated` with the global stability clause asked at
`K · Kakeya.plankAngleScaleB a` rather than at `Kakeya.plankAngleScaleB a`.

This is the form the assembly of Lemma 6.13 can actually feed, at `K = 2`: what
`Kakeya.findingTypicalAngleOfIntersection_stable` delivers is
`θ ≤ 2 · Kakeya.plankAngleScaleB a · M(V, t)`, the factor `2` coming from the dyadic selection
of the global typical angle. -/
theorem localAngleConcentration_of_saturated_scaled
    (K Cang : ℝ≥0) (hK : 1 ≤ K) (hCang : 1 ≤ Cang) {η : ℝ} (hη : 0 < η) :
    ∃ Ceta : ℝ≥0, 0 < Ceta ∧
      ∀ {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι σ : Type*}
        (s : Finset ι) (V : ι → Plank a b hab hb1)
        (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (𝒯' : Finset σ) (D : σ → Finset (Fin 3 → ℤ))
        (R : σ → (Fin 3 → ℤ) → Set (EuclideanSpace ℝ (Fin 3)))
        (Tq : σ → (Fin 3 → ℤ) → Finset ι)
        (Z : σ → (Fin 3 → ℤ) → ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (A : ℝ),
        0 < a → a < 1 → 0 < b → 0 < θ → θ ≤ 1 → 2 ≤ A →
        Kakeya.HasMaxPlankAngleBound s Y V θ Cang →
        (∀ u ∈ 𝒯', ∀ q ∈ D u, Tq u q ⊆ s) →
        (∀ u ∈ 𝒯', ∀ q ∈ D u, ∀ i ∈ Tq u q, (Z u q i).shade = (Y i).shade ∩ R u q) →
        (∀ u ∈ 𝒯', ∀ q ∈ D u, ∀ i ∈ s, ∀ x ∈ (Y i).shade, x ∈ R u q → i ∈ Tq u q) →
        (∀ x ∈ ⋃ i ∈ s, (Y i).shade, ∀ t ⊆ Kakeya.shadeFibre s Y x,
          A⁻¹ * ((Kakeya.shadeFibre s Y x).card : ℝ) ≤ (t.card : ℝ) →
            (θ : ℝ) / ((K : ℝ) * Kakeya.plankAngleScaleB a)
              ≤ ((Kakeya.maxPlankAngle V t : ℝ≥0) : ℝ)) →
        LocalAngleConcentration V θ 𝒯' D Tq Z Ceta η := by
  -- Step 1: get Ceta from exists_localTypicalIntersectionAngle_of_localStability_scaled
  obtain ⟨Ceta, hCetapos, hmain⟩ :=
    Plank.exists_localTypicalIntersectionAngle_of_localStability_scaled K Cang hK hCang hη
  refine ⟨Ceta, hCetapos, ?_⟩
  intro a b θ hab hb1 ι σ s V Y 𝒯' D R Tq Z A ha ha1' hb hθ hθ1 hA
    hang_global hTs hZeq hsat hglob_stab
  -- From hZeq we get the ⊆ condition that hmain needs
  have hZsub : ∀ u ∈ 𝒯', ∀ q ∈ D u, ∀ i ∈ Tq u q, (Z u q i).shade ⊆ (Y i).shade := by
    intro u hu q hq i hi
    rw [hZeq u hu q hq i hi]
    exact Set.inter_subset_left
  have hApos : 0 < A := by linarith
  -- For each u ∈ 𝒯', q ∈ D u, use shadeFibre_subset_of_saturated +
  -- localShadeFibreStable_of_fibreEq
  -- to turn the global stability hypothesis into local stability
  have hstab_local : ∀ u ∈ 𝒯', ∀ q ∈ D u,
    LocalShadeFibreStable V (Tq u q) (Z u q) θ ((K : ℝ) * Kakeya.plankAngleScaleB a) A := by
    intro u hu q hq
    have hTs_q : Tq u q ⊆ s := hTs u hu q hq
    have hZsub_q : ∀ i ∈ Tq u q, (Z u q i).shade ⊆ (Y i).shade := hZsub u hu q hq
    have hfib : ∀ x ∈ ⋃ i ∈ Tq u q, (Z u q i).shade,
      Kakeya.shadeFibre s Y x ⊆ Kakeya.shadeFibre (Tq u q) (Z u q) x := by
      intro x hx
      exact shadeFibre_subset_of_saturated (R u q) (hZeq u hu q hq) (hsat u hu q hq) hx
    have hglob_q : ∀ x ∈ ⋃ i ∈ s, (Y i).shade, ∀ t ⊆ Kakeya.shadeFibre s Y x,
      A⁻¹ * ((Kakeya.shadeFibre s Y x).card : ℝ) ≤ (t.card : ℝ) →
        (θ : ℝ) / ((K : ℝ) * Kakeya.plankAngleScaleB a) ≤ ((Kakeya.maxPlankAngle V t : ℝ≥0) : ℝ) :=
      hglob_stab
    exact localShadeFibreStable_of_fibreEq hApos hTs_q hZsub_q hfib hglob_q
  -- Now hmain gives us the LocalAngleConcentration
  exact hmain s V Y 𝒯' D Tq Z A ha ha1' hb hθ hθ1 hA hang_global hTs hZsub hstab_local

/-! ### Why the repr-fibre-local form of (5) is false -/


/-! ## The middle half of a grid box -/

/-- **The middle half of a shifted grid box**, i.e. the concentric half-dilation of
`Plank.shiftedSlabBox S b sh q`.  This is the region a box-local family must be *saturated* for:
a plank meeting it is automatically tangential to the box
(`Plank.comparableScalars_of_mem_halfBox`), whereas a plank merely meeting the box need not be, so
the middle half is what makes "every plank whose shade meets the region" a *tangential* family. -/
def halfSlabBox {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1) (b : ℝ≥0)
    (sh : Fin 3 → ℝ) (q : Fin 3 → ℤ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  (((shiftedSlabBox S b sh q).toPrismNDim.dilation 2⁻¹).carrier :
    Set (EuclideanSpace ℝ (Fin 3)))

/-- The middle half of a shifted grid box sits inside the box. -/
theorem halfSlabBox_subset {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1) (b : ℝ≥0)
    (sh : Fin 3 → ℝ) (q : Fin 3 → ℤ) :
    halfSlabBox S b sh q
      ⊆ ((shiftedSlabBox S b sh q).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
  set P := (shiftedSlabBox S b sh q).toPrismNDim with hP
  unfold halfSlabBox
  calc
    ((P.dilation (2⁻¹ : ℝ≥0)).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ (P.dilation (1 : ℝ≥0)).carrier :=
      P.dilation_carrier_mono (by norm_num)
    _ = P.carrier := by
      ext x
      simp [PrismNDim.mem_carrier_iff]

end Plank

end

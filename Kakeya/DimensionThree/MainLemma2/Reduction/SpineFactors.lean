/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCoreWindow
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineInheritance

/-!
# Branch (ii) of the geometric core: the outer two factors of the triple product

`Kakeya.ML2Core.exists_spineTwoScale_ofChain_translated`  bounds the multiplicity of the
leaf family by a subpolynomial loss times a product of **three** multiplicities,

`μ(s₁, V) ≤ L · μ(𝕋[T_τ], Y') · μ(𝕋_τ[T_θ], Y_τ') · μ(𝕋_θ, Y_θ)`.

This file bounds the fine and coarse outer factors in the GWZ argument.  The middle factor is the whole of the rescaled
argument (the estimate … the estimate) and is not touched here.

## the estimate, the fine factor

GWZ argues: Remark 3.3(B) gives `C_KT(𝕋[T_τ], T_τ) ≤ δ^{-η}`, one may *choose* `T_τ` so that
`λ(𝕋[T_τ], Y) ⪆ λ(𝕋, Y)`, and then `K_KT(β)` applied to the fibre rescaled to `B₁` at scale
`δ/τ` gives `μ(𝕋[T_τ], Y) ≤ (δ/τ)^{-η₁} |𝕋[T_τ]|^β`.

**The rescaling is not needed, and this file does not perform it.**  The reason is measured, not
stylistic:

* `C_KT(𝕋[T_τ], T_τ)` is `Δ_max` of the fibre read after *any* affine change of variables taking
  `T_τ` to the unit ball, and `Kakeya.maxDensity` is exactly invariant under such a change
  (`Kakeya.maxDensity_affineImage`), so `C_KT(𝕋[T_τ], T_τ) = Δ_max(𝕋[T_τ])` — the content of
  `Kakeya.ML2Spine.isKatzTao_familyIn_affineImage`, restated here as
  `Kakeya.ML2Core.isKatzTao_fibre_anchored`;
* the fibre already consists of honest `δ`-tubes inside `B₁` (that is exactly what seam
  delivers), so `K_KT(β)` applies to it *at the scale `δ`*, with no rescaling and no outer-tube
  volume loss;
* `(δ/τ)^{-η₁} ≤ δ^{-η₁}` because `τ ≤ 1`, so GWZ's conclusion **implies** the `δ`-form and the
  `δ`-form is the one the assembly consumes: every other loss on branch (ii) is a power of `δ`.

Rescaling would therefore buy a strictly stronger bound that the assembly immediately throws
away, at the price of the distortion package `Kakeya.ML2Reduction.outerTube_spec` (whose
`Δ_max` transport across the enclosing outer tube is *not* in the tree) — so the direct route is
taken.  `Kakeya.ML2Core.exists_fine_factor` is the analytic core and
`Kakeya.ML2Core.exists_fine_factor_at_window` is it wired to output, including GWZ's
"we can choose `T_τ`": the choice is the mediant pigeonhole
`Kakeya.ML2Core.exists_fibre_fullness_le'`, which costs **nothing**, fullness being a ratio.

## the estimate, the coarse factor

`K_KT(β)` at the *coarse* scale `θ` cannot be applied with the fullness bound read at `θ`: what
the argument owns is `λ(𝕋_θ, Y_θ) ⪆ λ(𝕋, Y) ≥ δ^{η}`, and `δ^{η} ≥ θ^{η'}` fails for every fixed
`η` once `θ = δ^{a/M}` with `M = ssfGridLen δ → ∞`.  The lemma that decouples the two scales is
`Kakeya.KatzTaoEstimate.multiplicity_bound_generalize` (GWZ Remark 3.6 applied to Lemma 3.7),
which reads both the fullness hypothesis and the loss at an auxiliary scale `δ ≤ θ`; that is what
`Kakeya.ML2Core.exists_coarse_factor` uses, and the `Δ_max^{1-β}` factor of Lemma 3.7 is where
the window's `coarse_maxDensity_le` field enters.

Lemma 3.7 carries a smallness threshold **on the tube scale**, here `θ`, and `θ` is not small in
general: at `a = 0` the coarse grid scale is `Tube.gridScale δ M 0 = 1` exactly.  For `1 ≤ a` the
threshold is eventually met, and that is `Kakeya.ML2Core.eventually_gridScale_le`, proved from
the doubly logarithmic size of `Kakeya.ssfGridLen` exactly as
`Kakeya.ML2Core.gridScale_le_quarter` is.  At `a = 0` the only exit is the trivial bound
`Kakeya.ML2Core.multiplicity_le_of_card_le`, which needs a cardinality bound on the retained
coarse node set that output does not carry; the row is left there and the obligation is
named, rather than bridged by a new `Prop`.

The coarse family's ball containment is likewise **not** supplied by the estimate: seam is run
at the *fine* level `b`, and a level-`a` node containing a level-`b` node inside `B₁` is only
inside `B̄(0, 1 + 4θ)` (`Kakeya.ML2Core.coverTube_carrier_subset_closedBall`).  It is therefore an
explicit hypothesis of `Kakeya.ML2Core.exists_coarse_factor_at_window`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ShadedBody ConvexSpaceBody Tube Filter
open scoped NNReal ENNReal Topology

namespace Kakeya.ML2Core

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ## Bookkeeping shared by the two factors -/

section Bookkeeping

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The union of the shades over `Finset.attach` is the union over the finset. -/
theorem biUnion_shade_attach {ι : Type*} (s : Finset ι) (V : ι → ShadedBody E) :
    (⋃ x ∈ s.attach, (V x.1).shade) = ⋃ i ∈ s, (V i).shade := by
  ext y
  simp only [Set.mem_iUnion, Finset.mem_attach, exists_prop, true_and, Subtype.exists]

/-- Multiplicity is unchanged by the `Finset.attach` reindexing.  This is the special case of
`Kakeya.ShadedBody.multiplicity_map` that lets a statement quantified over *all* indices of the
ambient type be applied to a family whose hypotheses hold only on a finset; the general `map`
form lives in a `Plank` module this file does not import. -/
theorem multiplicity_attach_val {ι : Type*} (s : Finset ι) (V : ι → ShadedBody E) :
    ShadedBody.multiplicity s.attach (fun x => V x.1) = ShadedBody.multiplicity s V := by
  rw [ShadedBody.multiplicity_eq_div, ShadedBody.multiplicity_eq_div,
    Finset.sum_attach s (fun i => volume (V i).shade), biUnion_shade_attach]

/-- Fullness is unchanged by the `Finset.attach` reindexing. -/
theorem fullness_attach_val {ι : Type*} (s : Finset ι) (V : ι → ShadedBody E) :
    ShadedBody.fullness s.attach (fun x => V x.1) = ShadedBody.fullness s V := by
  rw [← ENNReal.coe_inj, ShadedBody.fullness_def, ShadedBody.fullness_def,
    Finset.sum_attach s (fun i => volume (V i).shade),
    Finset.sum_attach s (fun i => volume (V i).carrier)]

/-- `Δ_max` is unchanged by the `Finset.attach` reindexing. -/
theorem maxDensity_attach_val {ι : Type*} (s : Finset ι) (W : ι → ConvexSpaceBody E) :
    Kakeya.maxDensity s.attach (fun x => W x.1) = Kakeya.maxDensity s W := by
  have h := Kakeya.maxDensity_map s.attach (Function.Embedding.subtype (fun x => x ∈ s)) W
  rw [Finset.attach_map_val] at h
  exact h.symm


/-- **Mediant fibre selection for fullness, at a general ambient space.**

`Kakeya.exists_fibre_fullness_le` is this statement at `E = EuclideanSpace ℝ (Fin 3)`, where its
Proposition-5.1 consumer pinned it; the proof is the same mediant argument, and the general form
is what the branch-(ii) families — stated over an abstract `E` throughout `Reduction/` — need.

Fullness is a *ratio*, not a mass, so passing from the whole family to the fullest fibre costs no
cardinality factor at all.  This is GWZ's "we can choose `T_τ` so that
`λ(𝕋[T_τ], Y) ⪆ λ(𝕋, Y)`", and the `⪆` is in fact an `≥`. -/
theorem exists_fibre_fullness_le' {ι κ : Type*} [DecidableEq κ] (s : Finset ι)
    (V : ι → ShadedBody E) (ts : Finset κ) (p : ι → κ) (hp : ∀ i ∈ s, p i ∈ ts)
    (hts : ts.Nonempty)
    (hB0 : (∑ i ∈ s, volume (V i).carrier) ≠ 0)
    (hBtop : (∑ i ∈ s, volume (V i).carrier) ≠ ⊤) :
    ∃ x ∈ ts, ShadedBody.fullness s V
      ≤ ShadedBody.fullness ({i ∈ s | p i = x} : Finset ι) V := by
  classical
  let A : ℝ≥0∞ := ∑ i ∈ s, volume (V i).shade
  let B : ℝ≥0∞ := ∑ i ∈ s, volume (V i).carrier
  let Ax : κ → ℝ≥0∞ := fun x => ∑ i ∈ {i ∈ s | p i = x}, volume (V i).shade
  let Bx : κ → ℝ≥0∞ := fun x => ∑ i ∈ {i ∈ s | p i = x}, volume (V i).carrier
  have hB0' : B ≠ 0 := by simpa [B] using hB0
  have hBtop' : B ≠ ⊤ := by simpa [B] using hBtop
  obtain ⟨x₀, hx₀ts, hx₀⟩ :=
    Finset.exists_max_image ts (fun x => ShadedBody.fullness ({i ∈ s | p i = x} : Finset ι) V) hts
  have hsumA : (∑ x ∈ ts, Ax x) = A := by
    simpa [Ax, A] using (Finset.sum_fiberwise_of_maps_to hp (fun i => volume (V i).shade))
  have hsumB : (∑ x ∈ ts, Bx x) = B := by
    simpa [Bx, B] using (Finset.sum_fiberwise_of_maps_to hp (fun i => volume (V i).carrier))
  have hAmul : (ShadedBody.fullness s V : ℝ≥0∞) * B = A := by
    simpa [A, B] using (ShadedBody.sum_volumeReal_shade_eq_fullness_mul s V).symm
  have hAximul : ∀ x : κ,
      Ax x = (ShadedBody.fullness ({i ∈ s | p i = x} : Finset ι) V : ℝ≥0∞) * Bx x := by
    intro x
    simpa [Ax, Bx] using
      (ShadedBody.sum_volumeReal_shade_eq_fullness_mul ({i ∈ s | p i = x} : Finset ι) V)
  have hle : (ShadedBody.fullness s V : ℝ≥0∞) * B ≤
      (ShadedBody.fullness ({i ∈ s | p i = x₀} : Finset ι) V : ℝ≥0∞) * B := by
    calc
      (ShadedBody.fullness s V : ℝ≥0∞) * B = A := hAmul
      _ = ∑ x ∈ ts, Ax x := hsumA.symm
      _ = ∑ x ∈ ts, (ShadedBody.fullness ({i ∈ s | p i = x} : Finset ι) V : ℝ≥0∞) * Bx x :=
        Finset.sum_congr rfl (fun x _ => hAximul x)
      _ ≤ ∑ x ∈ ts,
          (ShadedBody.fullness ({i ∈ s | p i = x₀} : Finset ι) V : ℝ≥0∞) * Bx x :=
        Finset.sum_le_sum (fun x hx =>
          mul_le_mul_left (ENNReal.coe_le_coe.mpr (hx₀ x hx)) (Bx x))
      _ = (ShadedBody.fullness ({i ∈ s | p i = x₀} : Finset ι) V : ℝ≥0∞) * ∑ x ∈ ts, Bx x := by
        rw [← Finset.mul_sum]
      _ = (ShadedBody.fullness ({i ∈ s | p i = x₀} : Finset ι) V : ℝ≥0∞) * B := by rw [hsumB]
  exact ⟨x₀, hx₀ts, ENNReal.coe_le_coe.mp ((ENNReal.mul_le_mul_iff_left hB0' hBtop').mp hle)⟩

/-- **The trivial multiplicity bound, in the shape the assembly multiplies.**

`μ ≤ |t|` always, so a cardinality ceiling `C` on the family gives `μ ≤ C^{1-β} |t|^β`.  This is
the only exit available at a degenerate scale, where `K_KT(β)`'s smallness threshold cannot be
met; it is stated here because `Tube.gridScale δ M 0 = 1` makes that case real on branch (ii),
and it needs no smallness, no shading and no density hypothesis. -/
theorem multiplicity_le_of_card_le {ι : Type*} {t : Finset ι} {V : ι → ShadedBody E}
    {β : ℝ} (hβ1 : β ≤ 1) {C : ℝ≥0∞} (hC : (t.card : ℝ≥0∞) ≤ C) :
    ShadedBody.multiplicity t V ≤ C ^ (1 - β) * (t.card : ℝ≥0∞) ^ β := by
  rcases Nat.eq_zero_or_pos t.card with h0 | h0
  · have ht : t = ∅ := Finset.card_eq_zero.mp h0
    subst ht
    simp [ShadedBody.multiplicity]
  · have hc0 : ((t.card : ℝ≥0∞)) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    have hctop : ((t.card : ℝ≥0∞)) ≠ ⊤ := ENNReal.natCast_ne_top _
    calc ShadedBody.multiplicity t V ≤ (t.card : ℝ≥0∞) := ShadedBody.multiplicity_le_card t V
      _ = (t.card : ℝ≥0∞) ^ (1 - β) * (t.card : ℝ≥0∞) ^ β := by
          rw [← ENNReal.rpow_add _ _ hc0 hctop]
          simp
      _ ≤ C ^ (1 - β) * (t.card : ℝ≥0∞) ^ β := by
          have h1b : (0 : ℝ) ≤ 1 - β := by linarith
          gcongr

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `ENNReal.ofReal` of a real power of a positive `NNReal` is the `ENNReal` power.  The window's
three density fields are stated with `ENNReal.ofReal`; every consumer wants the `rpow`. -/
theorem ofReal_rpow_coe {ρ : ℝ≥0} (hρ : 0 < ρ) (x : ℝ) :
    ENNReal.ofReal ((ρ : ℝ) ^ x) = (ρ : ℝ≥0∞) ^ x := by
  rw [← NNReal.coe_rpow, ENNReal.ofReal_coe_nnreal, ENNReal.coe_rpow_of_ne_zero hρ.ne']

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A negative power is antitone in the base: `δ ≤ θ ≤ 1` and `0 ≤ x` give `θ^{-x} ≤ δ^{-x}`. -/
theorem rpow_neg_le_rpow_neg_of_le {δ θ : ℝ≥0} (hδθ : δ ≤ θ) {x : ℝ} (hx : 0 ≤ x) :
    (θ : ℝ≥0∞) ^ (-x) ≤ (δ : ℝ≥0∞) ^ (-x) := by
  rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
  exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow (by exact_mod_cast hδθ) hx)

end Bookkeeping

/-! ## the estimate: the fine factor (GWZ) -/

section FineFactor

variable [Nontrivial E]


/-- **the estimate, the analytic core: `K_KT(β)` applied to a fibre, at the leaf scale.**

A family of `δ`-tubes in `B₁` with `Δ_max ≤ δ^{-η}` and `λ ≥ δ^{η}` has multiplicity at most
`δ^{-ε} |·|^β`.  This is `Kakeya.KatzTaoEstimate.generalize` read at its own scale — the
`τ`-decoupling it offers is not needed here, the fibre living at the leaf scale `δ`, but the
memberwise ball hypothesis `∀ i ∈ f` (rather than `∀ i`) is, since shaded families are
total functions on the ambient index type and only their retained members are normalised into
`B₁`. -/
theorem exists_fine_factor {β : ℝ} (hβ0 : 0 ≤ β) (hKT : Kakeya.KatzTaoEstimate.{u} E β)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η > (0 : ℝ), ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0,
      ∀ {ι : Type u} (f : Finset ι) (Y : ι → ShadedTube δ E),
        (∀ i ∈ f, (Y i).carrier ⊆ Metric.closedBall (0 : E) 1) →
        Kakeya.maxDensity f (fun i => (Y i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-η) →
        (δ : ℝ≥0) ^ η ≤ ShadedBody.fullness f (fun i => (Y i).toShadedBody) →
        ShadedBody.multiplicity f (fun i => (Y i).toShadedBody)
          ≤ (δ : ℝ≥0∞) ^ (-ε) * (f.card : ℝ≥0∞) ^ β := by
  obtain ⟨η, hη, hev⟩ := Kakeya.KatzTaoEstimate.generalize E hβ0 hKT ε hε
  refine ⟨η, hη, ?_⟩
  filter_upwards [hev, self_mem_nhdsWithin] with δ hδ hδ0
  intro ι f Y hball hmax hfull
  exact hδ δ hδ0 le_rfl f Y hball hmax hfull


end FineFactor

/-! ## the estimate: the coarse factor (GWZ) -/

section CoarseFactor


variable [Nontrivial E]

/-- **the estimate, the analytic core: GWZ Lemma 3.7 with the two scales decoupled.**

At tube scale `θ` and auxiliary scale `dt ≤ θ`, a family of `θ`-tubes in `B₁` with
`λ ≥ dt^{η}` and `Δ_max ≤ dt^{-η_c}` has multiplicity at most `dt^{-(ε + η_c)} |·|^β`.

Two things are load-bearing.  First, the fullness hypothesis is read at `dt`, not at `θ`: what
the reduction owns for the coarse family is `λ(𝕋_θ, Y_θ) ⪆ λ(𝕋, Y) ≥ δ^{η}`, and no fixed `η`
makes that a bound of the form `θ^{η'}` when `θ = δ^{a/M}` with `M = ssfGridLen δ` unbounded.
`Kakeya.KatzTaoEstimate.multiplicity_bound_generalize` is exactly GWZ Remark 3.6 applied to
Lemma 3.7 and is what decouples them.  Second, `Δ_max` enters only through Lemma 3.7's
`Δ_max^{1-β}` factor, so **no smallness of `η_c` is needed** — which matters, because the window
hands out `η_{j-1}`, an exponent of the ladder that is not small compared with the accuracy.

`θ₀` is the smallness threshold Lemma 3.7 puts on the tube scale; it is discharged for the
window's coarse scale by `Kakeya.ML2Core.eventually_gridScale_le` when `1 ≤ a`. -/
theorem exists_coarse_factor {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hKT : Kakeya.KatzTaoEstimate.{u} E β) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > (0 : ℝ), ∃ θ₀ : ℝ≥0, 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ {θ : ℝ≥0}, 0 < θ → θ ≤ θ₀ →
      ∀ (dt : ℝ≥0), 0 < dt → dt ≤ θ →
      ∀ {ηc : ℝ}, 0 ≤ ηc →
      ∀ {ι : Type u} (t : Finset ι) (Y : ι → ShadedTube θ E),
        (∀ k ∈ t, (Y k).carrier ⊆ Metric.closedBall (0 : E) 1) →
        (dt : ℝ≥0) ^ η ≤ ShadedBody.fullness t (fun k => (Y k).toShadedBody) →
        Kakeya.maxDensity t (fun k => (Y k).toConvexSpaceBody) ≤ (dt : ℝ≥0∞) ^ (-ηc) →
        ShadedBody.multiplicity t (fun k => (Y k).toShadedBody)
          ≤ (dt : ℝ≥0∞) ^ (-(ε + ηc)) * (t.card : ℝ≥0∞) ^ β := by
  classical
  obtain ⟨η, hη, hev⟩ := Kakeya.KatzTaoEstimate.multiplicity_bound_generalize E hβ0 hKT ε hε
  obtain ⟨θ₁, hθ₁0, hth⟩ := Kakeya.StickyKakeya.exists_threshold_of_eventually_nhdsGT hev
  refine ⟨η, hη, min θ₁ 1, lt_min hθ₁0 zero_lt_one, min_le_right _ _, ?_⟩
  intro θ hθ0 hθle dt hdt0 hdtθ ηc hηc ι t Y hball hfull hmax
  have hθ₁ : θ ≤ θ₁ := hθle.trans (min_le_left _ _)
  have hθ1 : θ ≤ 1 := hθle.trans (min_le_right _ _)
  have hdt1 : dt ≤ 1 := hdtθ.trans hθ1
  have hdtE1 : (dt : ℝ≥0∞) ≤ 1 := by exact_mod_cast hdt1
  have hdtE0 : (dt : ℝ≥0∞) ≠ 0 := by simpa using hdt0.ne'
  set Y' : {x // x ∈ t} → ShadedTube θ E := fun x => Y x.1 with hY'
  have hballs : ∀ x : {x // x ∈ t}, (Y' x).carrier ⊆ Metric.closedBall (0 : E) 1 :=
    fun x => hball x.1 x.2
  have hfull' : ShadedBody.fullness t.attach (fun x => (Y' x).toShadedBody) ≥ dt ^ η := by
    rw [show (fun x : {x // x ∈ t} => (Y' x).toShadedBody)
        = (fun x : {x // x ∈ t} => ((fun i => (Y i).toShadedBody) x.1)) from rfl,
      fullness_attach_val t (fun i => (Y i).toShadedBody)]
    exact hfull
  have hraw := hth hθ0 hθ₁ dt hdt0 hdtθ t.attach Y' hballs hfull'
  rw [show (fun x : {x // x ∈ t} => (Y' x).toShadedBody)
      = (fun x : {x // x ∈ t} => ((fun i => (Y i).toShadedBody) x.1)) from rfl,
    multiplicity_attach_val t (fun i => (Y i).toShadedBody),
    show (fun x : {x // x ∈ t} => (Y' x).toConvexSpaceBody)
      = (fun x : {x // x ∈ t} => ((fun i => (Y i).toConvexSpaceBody) x.1)) from rfl,
    maxDensity_attach_val t (fun i => (Y i).toConvexSpaceBody), Finset.card_attach] at hraw
  refine hraw.trans ?_
  have hdens : Kakeya.maxDensity t (fun k => (Y k).toConvexSpaceBody) ^ (1 - β)
      ≤ (dt : ℝ≥0∞) ^ (-ηc) := by
    calc Kakeya.maxDensity t (fun k => (Y k).toConvexSpaceBody) ^ (1 - β)
        ≤ ((dt : ℝ≥0∞) ^ (-ηc)) ^ (1 - β) := ENNReal.rpow_le_rpow hmax (by linarith)
      _ = (dt : ℝ≥0∞) ^ (-ηc * (1 - β)) := by rw [← ENNReal.rpow_mul]
      _ ≤ (dt : ℝ≥0∞) ^ (-ηc) := by
          refine ENNReal.rpow_le_rpow_of_exponent_ge hdtE1 ?_
          nlinarith
  calc (dt : ℝ≥0∞) ^ (-ε) * Kakeya.maxDensity t (fun k => (Y k).toConvexSpaceBody) ^ (1 - β)
        * (t.card : ℝ≥0∞) ^ β
      ≤ (dt : ℝ≥0∞) ^ (-ε) * (dt : ℝ≥0∞) ^ (-ηc) * (t.card : ℝ≥0∞) ^ β := by gcongr
    _ = (dt : ℝ≥0∞) ^ (-(ε + ηc)) * (t.card : ℝ≥0∞) ^ β := by
        rw [← ENNReal.rpow_add _ _ hdtE0 (by simp)]
        ring_nf


end CoarseFactor

/-! ## compatibility: output is input -/

section Tripwire

variable [Nontrivial E]


end Tripwire

end Kakeya.ML2Core

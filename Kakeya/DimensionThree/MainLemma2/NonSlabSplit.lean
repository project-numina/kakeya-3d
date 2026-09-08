/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.NonSlabAngle
public import Kakeya.DimensionThree.MainLemma2.NonSlabFibre
public import Kakeya.DimensionThree.MainLemma2.ThinConfig

/-!
# Splitting the multiplicity in the non-slab case of Main Lemma 2

This file formalizes the compatible refinement of the non-slab case and the resulting
splitting of `μ(𝕋, Y)` into an outer (body) factor and an inner (angular) factor: blueprint
`lem:ml2nonslabSegmentLocalise`, `lem:ml2nonslabCompat`, `lem:ml2nonslabPiecewise`,
`lem:ml2nonslabPointwiseMult`, `lem:ml2nonslabMultSplit` and `lem:ml2nonslabKKT`.

As in `Kakeya.DimensionThree.MainLemma2.ThinSetup`, the global Configurations
`hyp:ml2setup` and `hyp:ml2thinsetup` are not bundled into a single Lean object; the data
they supply is passed explicitly. The names follow the blueprint: `I` indexes `𝕋` with
shadings `Yg = Y` and `Y' `, `Pc B = B̂` is the piece of the subordinate partition of (C2)
attached to the ball `B`, `segs = 𝕋_B` with `carr` its carriers and `Yb = Y_B`, `Yb' = Y'_B`
its shadings, `fam p = 𝕋(T_B)` is the family of parent tubes of a segment, `blk` is the block
map of the factoring of (C4) and `bodies' B = 𝕎'_B` with shading `Wsh = Y_{𝕎'_B}` and axes
`ax j = v(W)`.
-/

@[expose] public section

open scoped NNReal ENNReal

namespace Kakeya.NonSlab

open MeasureTheory Metric Set ShadedBody

section Compat

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
/-- **Localising the tubes through a point to their parent segments**.

Let `x` lie in the partition piece `B̂` and let `T ∈ 𝕋` shade `x` for the refined shading
`Y'`. Since `Y'(T) ⊆ Y(T)` the set `Y(T) ∩ B̂` is non-empty, so by (C5) the tube `T` belongs
to `𝕋(T_B)` for a segment `T_B ∈ 𝕋_B`, and `Y(T) ∩ B̂ ⊆ Y_B(T_B) ⊆ T_B`; in particular
`x ∈ T_B`. Therefore `x ∈ Y'(T) ∩ T_B ∩ B̂`, which lies in `Y'_B(T_B)` by the forward
compatibility of (T1). So

`𝕋_{Y'}(x) ⊆ ⋃_{T_B ∈ 𝕋_B, x ∈ Y'_B(T_B)} 𝕋(T_B)`,

which is what the conclusion says pointwise.

The forward compatibility used here is local to the piece `B̂`; see the implementation note
following blueprint Definition `hyp:ml2thinsetup` for why no version valid on the whole ball
`B` is available. -/
theorem segmentLocalise {ι σ : Type*} (I : Finset ι) (Yg Y' : ι → Set E) (Pc : Set E)
    (segs : Finset σ) (fam : σ → Finset ι) (carr Yb Yb' : σ → Set E)
    (hY' : ∀ T ∈ I, Y' T ⊆ Yg T)
    (hparent : ∀ T ∈ I, (Yg T ∩ Pc).Nonempty → ∃ p ∈ segs, T ∈ fam p)
    (hinto : ∀ p ∈ segs, ∀ T ∈ fam p, Yg T ∩ Pc ⊆ Yb p)
    (hYbcarr : ∀ p ∈ segs, Yb p ⊆ carr p)
    (hfwd : ∀ p ∈ segs, ∀ T ∈ fam p, Y' T ∩ carr p ∩ Pc ⊆ Yb' p)
    {x : E} (hx : x ∈ Pc) :
    ∀ T ∈ I, x ∈ Y' T → ∃ p ∈ segs, x ∈ Yb' p ∧ T ∈ fam p := by
  intro T hTI hxTY
  have hxYg : x ∈ Yg T := hY' T hTI hxTY
  have hnonempty : (Yg T ∩ Pc).Nonempty := ⟨x, ⟨hxYg, hx⟩⟩
  rcases hparent T hTI hnonempty with ⟨p, hpseg, hTfam⟩
  have hxYb : x ∈ Yb p := hinto p hpseg T hTfam ⟨hxYg, hx⟩
  have hxcarr : x ∈ carr p := hYbcarr p hpseg hxYb
  have hxYb' : x ∈ Yb' p := hfwd p hpseg T hTfam ⟨⟨hxTY, hxcarr⟩, hx⟩
  exact ⟨p, hpseg, hxYb', hTfam⟩

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- **Compatible refinements in the non-slab case**.

Combining `Kakeya.NonSlab.segmentLocalise` with the pointwise containment (T3) — every
segment shading `x` lies in a block whose body is shaded at `x` — and with the angular bound
`∠(T, v(W)) ≤ C_{lem:ml2bodyAngle}(C₀) ρ₂` of
`Kakeya.NonSlab.lineAngle_bodyAxis_le` gives, for every `x ∈ U(𝕋, Y') ∩ B̂`,

`𝕋_{Y'}(x) ⊆ ⋃_{W ∈ 𝕎'_B, x ∈ Y_{𝕎'_B}(W)} {T ∈ 𝕋_Y(x) : ∠(T, v(W)) ≤ C ρ₂}`.

The restriction to the partition piece `B̂` is essential; the hypotheses of
`segmentLocalise` are only available there. -/
theorem compat {ι σ ω : Type*} (I : Finset ι) (Yg Y' : ι → Set E) (dir : ι → E) (Pc : Set E)
    (segs : Finset σ) (fam : σ → Finset ι) (carr Yb Yb' : σ → Set E) (blk : σ → ω)
    (bodies' : Finset ω) (Wsh : ω → ShadedBody E) (ax : ω → E) {ρ : ℝ}
    (hY' : ∀ T ∈ I, Y' T ⊆ Yg T)
    (hparent : ∀ T ∈ I, (Yg T ∩ Pc).Nonempty → ∃ p ∈ segs, T ∈ fam p)
    (hinto : ∀ p ∈ segs, ∀ T ∈ fam p, Yg T ∩ Pc ⊆ Yb p)
    (hYbcarr : ∀ p ∈ segs, Yb p ⊆ carr p)
    (hfwd : ∀ p ∈ segs, ∀ T ∈ fam p, Y' T ∩ carr p ∩ Pc ⊆ Yb' p)
    -- (T3): the containment `containmentWWB`
    (hT3 : ∀ p ∈ segs, ∀ y ∈ Yb' p, blk p ∈ bodies' ∧ y ∈ (Wsh (blk p)).shade)
    -- the angular bound of `lem:ml2bodyAngle`, uniform over the blocks
    (hangle : ∀ p ∈ segs, ∀ T ∈ fam p, lineAngle (dir T) (ax (blk p)) ≤ ρ)
    {x : E} (hx : x ∈ Pc) :
    ∀ T ∈ I, x ∈ Y' T →
      ∃ j ∈ bodies', x ∈ (Wsh j).shade ∧ x ∈ Yg T ∧ lineAngle (dir T) (ax j) ≤ ρ := by
  intro T hT hxY'
  rcases segmentLocalise I Yg Y' Pc segs fam carr Yb Yb' hY' hparent hinto hYbcarr hfwd hx
      T hT hxY' with ⟨p, hp, hxYb', hTfam⟩
  rcases hT3 p hp x hxYb' with ⟨hblk, hshade⟩
  refine ⟨blk p, hblk, hshade, hY' T hT hxY', hangle p hp T hTfam⟩

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
/-- **Every shaded point is handled in exactly one piece**.

The pieces `B̂`, `B ∈ 𝔅`, of (C2) are pairwise disjoint and cover `U(𝕋, Y)`; since
`Y'(T) ⊆ Y(T)` for every `T`, the union `U(𝕋, Y')` is contained in `U(𝕋, Y)`, so every
shaded point lies in exactly one piece. `Kakeya.NonSlab.compat` then applies in that piece,
with constants that do not depend on it: the only constant occurring is
`C_{lem:ml2bodyAngle}(C₀)`, where the single comparison constant `C₀` and the properties of
Configuration `hyp:ml2thinsetup` are shared by all `B ∈ 𝔅`.

The localisation costs nothing. The pieces are pairwise *disjoint*, so no factor `D` is lost,
in contrast with a covering argument run over the balls `B` themselves, where the `O(D)`
balls containing `x` would each contribute. -/
theorem piecewise {ι bι : Type*} (I : Finset ι) (Yg Y' : ι → Set E) (bs : Finset bι)
    (Pc : bι → Set E) (hdisj : (bs : Set bι).PairwiseDisjoint Pc)
    (hcov : ∀ T ∈ I, Yg T ⊆ ⋃ B ∈ bs, Pc B) (hY' : ∀ T ∈ I, Y' T ⊆ Yg T)
    {x : E} (hx : ∃ T ∈ I, x ∈ Y' T) :
    ∃! B, B ∈ bs ∧ x ∈ Pc B := by
  rcases hx with ⟨T, hTI, hxY'⟩
  have hxYg : x ∈ Yg T := hY' T hTI hxY'
  rcases Set.mem_iUnion₂.mp (hcov T hTI hxYg) with ⟨B, hB, hxB⟩
  exact existsUnique_of_exists_of_unique ⟨B, hB, hxB⟩ (by
    intro B₁ B₂ hB₁ hB₂
    exact hdisj.elim_set hB₁.1 hB₂.1 x hB₁.2 hB₂.2)


/-- **Splitting the multiplicity in the non-slab case**.

`Kakeya.NonSlab.pointwiseMult` bounds `|𝕋_{Y'}(x)|` by the product of the outer multiplicity
`μ(𝕎'_B, Y_{𝕎'_B})` and the inner multiplicity `μ(𝕋[T_{ρ₂*}], Y)` at every point of
`U(𝕋, Y')`. Taking the supremum over `x` bounds `μ(𝕋, Y')` by the same product, and since
`(𝕋, Y')` is a `⪆ 1` refinement of `(𝕋, Y)` by (T1) the multiplicity of `(𝕋, Y)` is
controlled by that of `(𝕋, Y')`, up to the refinement constant `c⁻¹`. -/
theorem multSplit {ι ω : Type*} (I : Finset ι) (Y Y' : ι → ShadedBody E)
    (bodies' : Finset ω) (Wsh : ω → ShadedBody E) (inn : Finset ι) (Yin : ι → ShadedBody E)
    {c C : ℝ≥0} (hc : 0 < c) (href : ShadedBody.IsCRefinement I Y' I Y c)
    (hpt : ∀ x ∈ iUnionShade I Y', (pointwiseMultiplicity I Y' x : ℝ≥0∞) ≤
      (C : ℝ≥0∞) * multiplicity bodies' Wsh * multiplicity inn Yin) :
    multiplicity I Y ≤
      (c : ℝ≥0∞)⁻¹ * C * multiplicity bodies' Wsh * multiplicity inn Yin := by
  let t : ℝ≥0∞ := C * multiplicity bodies' Wsh * multiplicity inn Yin
  have hptE : ∀ x ∈ iUnionShade I Y', (pointwiseMultiplicity I Y' x : ℝ≥0∞) ≤ t := by
    intro x hx
    simpa [t] using hpt x hx
  have hY' : multiplicity I Y' ≤ t := by
    exact ShadedBody.multiplicity_le_of_pointwiseMultiplicity_le (s := I) (V := Y') hptE
  have hmul : (c : ℝ≥0∞) * multiplicity I Y ≤ multiplicity I Y' :=
    ShadedBody.IsCRefinement.mul_multiplicity_le (s' := I) (V' := Y') (s := I) (V := Y) href
  have hcE : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast (ne_of_gt hc)
  have hcTop : (c : ℝ≥0∞) ≠ ⊤ := ne_of_lt (ENNReal.coe_lt_top : (c : ℝ≥0∞) < ⊤)
  have hinv : multiplicity I Y ≤ (c : ℝ≥0∞)⁻¹ * multiplicity I Y' := by
    calc
      multiplicity I Y = (c : ℝ≥0∞)⁻¹ * ((c : ℝ≥0∞) * multiplicity I Y) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hcE hcTop, one_mul]
      _ ≤ (c : ℝ≥0∞)⁻¹ * multiplicity I Y' := by
        exact mul_le_mul_of_nonneg_left hmul (zero_le : 0 ≤ (c : ℝ≥0∞)⁻¹)
  calc
    multiplicity I Y ≤ (c : ℝ≥0∞)⁻¹ * multiplicity I Y' := hinv
    _ ≤ (c : ℝ≥0∞)⁻¹ * t := by
      exact mul_le_mul_of_nonneg_left hY' (zero_le : 0 ≤ (c : ℝ≥0∞)⁻¹)
    _ = (c : ℝ≥0∞)⁻¹ * C * multiplicity bodies' Wsh * multiplicity inn Yin := by
      simp [t, mul_assoc]

end Compat

end Kakeya.NonSlab

namespace Kakeya.VeryNotSticky

universe u

open MeasureTheory Metric Set ShadedBody
open scoped NNReal ENNReal

/-- **The Katz–Tao estimate at the fixed scale `δ`**, as a predicate on the configuration and
the loss `ε` (blueprint Configuration `hyp:ml2scale`, cross-section of Definition `def:KKT`).

`KTScaleData cfg ε` says that `K_KT(β)` may be run on any subfamily of `𝕋` at this `δ` with
loss `δ^{-ε}`, at the density and fullness thresholds `δ^{-η}` and `δ^{2η}` of (C1):

`Δ_max(𝕊) ≤ δ^{-η}` and `λ(𝕊, Y_𝕊) ≥ δ^{2η}` imply `μ(𝕊, Y_𝕊) ≤ δ^{-ε} |𝕊|^β`.

The fullness threshold reads `δ^{2η}` and not `δ^{η}` because that is what the configuration
supplies: `Kakeya.VeryNotSticky.fullness_ge` is asserted at `δ^{2η}` (at `δ^{η}` it was rigid —
see that field), and `Kakeya.VeryNotSticky.exists_full_fibre` transports exactly that to the
fibre. Weakening the *antecedent* makes this predicate **stronger**, and it stays available:
`Kakeya.VeryNotSticky.ktScaleData_of_le` produces it from `Kakeya.KatzTaoEstimate.generalize`
at any exponent threshold `η₁ ≥ 2η`, and `η₁` belongs to the pair `(ε, β)` and is therefore
fixed after `η`.

This is exactly the conclusion of `Kakeya.KatzTaoEstimate.generalize` applied to
`cfg.ktEstimate` at `ε`, read at `τ = δ`, and it carries no `Δ_max^{1-β}` factor and no upper
bound on `β`: those belong to `Kakeya.KatzTaoEstimate.multiplicity_bound`, the variant valid for an
arbitrary `Δ_max`, which is not what the blueprint proof
of `lem:ml2nonslabKKT` uses.

Being a predicate rather than a direct application of `cfg.ktEstimate` is forced by the shape
of `Kakeya.KatzTaoEstimate`: that definition holds only *eventually* in `δ`, and the exponent
`η'` it produces for a given `ε` is existentially bound. `KTScaleData cfg ε` is the fixed-`δ`
cross-section, obtained once `δ` is below the threshold belonging to `ε` and `cfg.η ≤ η'`,
which is the blueprint's `η ≪ ϱ`. It plays for `def:KKT` the role that
`Kakeya.VeryNotSticky.AScaleData` plays for the scale-`a` estimates. -/
def KTScaleData (cfg : VeryNotSticky.{u}) (ε : ℝ) : Prop :=
  ∀ s' : Finset cfg.ι, s' ⊆ cfg.s →
    ConvexSpaceBody.IsKatzTao s' (fun i ↦ (cfg.T i).toConvexSpaceBody)
      ((cfg.δ : ℝ≥0∞) ^ (-cfg.η)) →
    ShadedBody.fullness s' (fun i ↦ (cfg.T i).toShadedBody) ≥ cfg.δ ^ (2 * cfg.η) →
    multiplicity s' (fun i ↦ (cfg.T i).toShadedBody) ≤
      (cfg.δ : ℝ≥0∞) ^ (-ε) * (s'.card : ℝ≥0∞) ^ cfg.β


/-- **Katz–Tao bound for the inner factor**.

Here `sub` is the subfamily `𝕋[T_{ρ₂*}]` of the tubes of `𝕋` inside a fixed `ρ₂*`-tube. The
conclusion is `K_KT(β)` applied to `𝕋[T_{ρ₂*}]` with `ϱ` in place of `ε`, i.e.
`cfg.ktEstimate` read at this `δ` through `Kakeya.VeryNotSticky.KTScaleData`. Its two
hypotheses are (C1) at the subfamily: `Δ_max(𝕋[T_{ρ₂*}]) ≤ Δ_max(𝕋) ≤ δ^{-η}` is `hsub`
together with `cfg.maxDensity_le` and `ConvexSpaceBody.IsKatzTao.subset`, while `hfull`
is a genuine hypothesis, fullness not being inherited by subfamilies. There is no
`Δ_max^{1-β}` factor to absorb, so the loss is `δ^{-ϱ}` and not `δ^{-(ϱ+η)}`, and no upper
bound on `β` is needed; the `+η` and the hypothesis `β ≤ 1` enter one step later, in
`Kakeya.VeryNotSticky.nonslabKKTPow`.

The counting bound `|𝕋[T_{ρ₂*}]| ≤ K · Ccnt · ρ₂^{2+ζ} |𝕋|`, the second display of the
blueprint statement, is a logically independent conclusion with no Katz–Tao content, and is
stated separately as `Kakeya.VeryNotSticky.nonslabFibreCount`, whose count constant `Ccnt` is a
parameter (it was the δ-free `(2 C_{lem:ml2bodyAngle}(C₀))²`
before it); consumers that need both invoke both. -/
theorem nonslabKKT (cfg : VeryNotSticky)
    (hKT : cfg.KTScaleData cfg.ϱ)
    {sub : Finset cfg.ι} (hsub : sub ⊆ cfg.s)
    (hfull : ShadedBody.fullness sub (fun i ↦ (cfg.T i).toShadedBody) ≥ cfg.δ ^ (2 * cfg.η)) :
    multiplicity sub (fun i ↦ (cfg.T i).toShadedBody) ≤
      (cfg.δ : ℝ≥0∞) ^ (-cfg.ϱ) * (sub.card : ℝ≥0∞) ^ cfg.β :=
  hKT sub hsub
    (ConvexSpaceBody.IsKatzTao.subset
      ((ConvexSpaceBody.IsKatzTao_def cfg.s (fun i ↦ (cfg.T i).toConvexSpaceBody)).mpr
        cfg.maxDensity_le) hsub) hfull

/-- **Positivity of the angular scale `ρ₂`.**

`ρ₂ = b / r₁` with `0 < δ ≤ a ≤ b` and `r₁ = δ^{exscal} > 0`, so `ρ₂ > 0`. This is the side
condition of `Kakeya.VeryNotSticky.nonslabFibreCount`, read off from the configuration. -/
theorem rho2_pos (cfg : VeryNotSticky) : 0 < cfg.rho2 := by
  have hb_pos : 0 < cfg.b :=
    lt_of_lt_of_le (lt_of_lt_of_le cfg.hδ cfg.hdims.1) cfg.hdims.2.1
  have hr₁ : 0 < cfg.r₁ := by
    simpa [r₁] using NNReal.rpow_pos cfg.hδ
  rw [rho2]
  exact div_pos hb_pos hr₁

/-- **The Katz–Tao bound in powered form**.

The form of `Kakeya.VeryNotSticky.nonslabKKT` that the splitting actually consumes: the
counting bound is raised to the `β`-th power and substituted into the multiplicity bound, so
that the inner factor is expressed directly against `ρ₂^{2+ζ}|𝕋|`.

This is where `hβ1 : β ≤ 1` is spent, and it is the only place in the non-slab chain that
spends it: raising `|𝕋[T_{ρ₂*}]| ≤ K Ccnt ρ₂^{2+ζ}|𝕋|` to the `β`-th power costs
`(K Ccnt)^β`, and `(K Ccnt)^β ≤ (δ^{-Mη})^β = δ^{-Mηβ} ≤ δ^{-Mη}` by `hCδ` together with
`β ≤ 1`, `0 ≤ M` and `δ ≤ 1`. That loss is then carried into `δ^{-(ϱ + Mη)}`, which is where
the `+Mη` of the conclusion comes from; neither conclusion of `nonslabKKT` carries it.

`K` is the constant of the fibre count `hfib : |𝕋_{ρ₂*}| · |𝕋[T_{ρ₂*}]| ≤ K |𝕋|` — `Cu²` for
the hierarchy constant `Cu` of `Tube.UniformTubeSet`, as `Kakeya.VeryNotSticky.SplitInputs`
carries it (GWZ Def 2.1(iii) reads "constant up to a factor `∼ 1`",
GWZ, so the exact-branching `K = 1` was over-strong). `Ccnt` is the constant of the
count hypothesis `hcount`, and `M` the exponent of the joint threshold; both are **parameters**, which forbids baking a numeral into this lemma. The numerals
live at the call sites: `M = 19` at `Kakeya.VeryNotSticky.nonslabSplitBound`, where
`K = Cu²` costs `δ^{-η}` through `Kakeya.VeryNotSticky.SplitInputs.fibreConstant` and
`Ccnt` costs `δ^{-18η}` through `Kakeya.VeryNotSticky.SplitInputs.countConstant` ( (c) measured the `+1`), and `M = 1` at
`Kakeya.KKTResidual.nonslabKKTPow_of_fibreKTData`, whose datum still fixes
`Ccnt = (2 C_{lem:ml2bodyAngle}(C₀))²`.

That absorption is the hypothesis `hCδ`, blueprint `fibreConstantThreshold`. It is a genuine
extra assumption, not a consequence of the others: without it the statement is false, as
`δ = 1` shows. It is a fixed-scale threshold of the same kind as the four fields of
`Kakeya.VeryNotSticky.CaseScale`, satisfied once `δ` is small with `C₀`, `K` and `η` fixed
first, but it is not one of them, and it does not follow from `scale.rho2Star_le_one` together
with `2η < exscal`: that bounds `2 C_{lem:ml2bodyAngle}(C₀) δ^{exscal}` and says nothing about
`C_{lem:ml2bodyAngle}(C₀)²` on its own. -/
theorem nonslabKKTPow (cfg : VeryNotSticky) (hβ1 : cfg.β ≤ 1)
    (hKT : cfg.KTScaleData cfg.ϱ)
    {K Ccnt : ℝ≥0} {M : ℝ} (hM : 0 ≤ M)
    (hCδ : (K : ℝ≥0∞) * (Ccnt : ℝ≥0∞) ≤ (cfg.δ : ℝ≥0∞) ^ (-(M * cfg.η)))
    {sub : Finset cfg.ι} (hsub : sub ⊆ cfg.s)
    (hfull : ShadedBody.fullness sub (fun i ↦ (cfg.T i).toShadedBody) ≥ cfg.δ ^ (2 * cfg.η))
    (N : ℕ) (hfib : (N : ℝ) * (sub.card : ℝ) ≤ (K : ℝ) * (cfg.s.card : ℝ))
    (hcount : (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤ (Ccnt : ℝ) * (N : ℝ)) :
    multiplicity sub (fun i ↦ (cfg.T i).toShadedBody) ≤
      (cfg.δ : ℝ≥0∞) ^ (-(cfg.ϱ + M * cfg.η)) *
        ((cfg.rho2 : ℝ≥0∞) ^ (2 + cfg.ζ) * (cfg.s.card : ℝ≥0∞)) ^ cfg.β := by
  have hmult := nonslabKKT cfg hKT hsub hfull
  have hcard := nonslabFibreCount cfg (rho2_pos cfg) N hfib hcount
  have hpow := nonslabFibreCountPow cfg hβ1 hM hCδ hcard
  have hδne0 : (cfg.δ : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast ne_of_gt cfg.hδ
  have hδneTop : (cfg.δ : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hexp : (cfg.δ : ℝ≥0∞) ^ (-(M * cfg.η)) * (cfg.δ : ℝ≥0∞) ^ (-cfg.ϱ) =
      (cfg.δ : ℝ≥0∞) ^ (-(cfg.ϱ + M * cfg.η)) := by
    rw [← ENNReal.rpow_add (-(M * cfg.η)) (-cfg.ϱ) hδne0 hδneTop]
    congr
    ring
  calc
    multiplicity sub (fun i ↦ (cfg.T i).toShadedBody) ≤
        (cfg.δ : ℝ≥0∞) ^ (-cfg.ϱ) * (sub.card : ℝ≥0∞) ^ cfg.β := by
      exact hmult
    _ = (sub.card : ℝ≥0∞) ^ cfg.β * (cfg.δ : ℝ≥0∞) ^ (-cfg.ϱ) := by
      rw [mul_comm]
    _ ≤ ((cfg.δ : ℝ≥0∞) ^ (-(M * cfg.η)) *
          ((cfg.rho2 : ℝ≥0∞) ^ (2 + cfg.ζ) * (cfg.s.card : ℝ≥0∞)) ^ cfg.β) *
          (cfg.δ : ℝ≥0∞) ^ (-cfg.ϱ) := by
      exact mul_le_mul_left hpow _
    _ = (cfg.δ : ℝ≥0∞) ^ (-(cfg.ϱ + M * cfg.η)) *
          ((cfg.rho2 : ℝ≥0∞) ^ (2 + cfg.ζ) * (cfg.s.card : ℝ≥0∞)) ^ cfg.β := by
      have hre : (cfg.δ : ℝ≥0∞) ^ (-(M * cfg.η)) *
            ((cfg.rho2 : ℝ≥0∞) ^ (2 + cfg.ζ) * (cfg.s.card : ℝ≥0∞)) ^ cfg.β *
            (cfg.δ : ℝ≥0∞) ^ (-cfg.ϱ) =
          (cfg.δ : ℝ≥0∞) ^ (-(cfg.ϱ + M * cfg.η)) *
            ((cfg.rho2 : ℝ≥0∞) ^ (2 + cfg.ζ) * (cfg.s.card : ℝ≥0∞)) ^ cfg.β := by
        rw [mul_right_comm, hexp]
      exact hre

/-! ### The angular input of the compatible refinement -/

/-- **The non-slab hypothesis in the shape the angular range lemmas want.**

`Kakeya.VeryNotSticky.nonslabSplitBound` receives the non-slab hypothesis as
`b ≤ δ^{2 exscal}`, the shape `Kakeya.VeryNotSticky.CaseScale.body_fits_ball` is stated in,
whereas `Kakeya.VeryNotSticky.rho2_range` and `Kakeya.VeryNotSticky.rho2Star_range` want
`b ≤ δ^{exscal} r₁`. Since `r₁ = δ^{exscal}` the two are the same bound, `δ^{exscal} δ^{exscal}
= δ^{2 exscal}`; only the `NNReal.rpow` bookkeeping differs. -/
theorem b_le_pow_mul_r₁ (cfg : VeryNotSticky) (hnotslab : cfg.b ≤ cfg.δ ^ (2 * cfg.exscal)) :
    cfg.b ≤ cfg.δ ^ cfg.exscal * cfg.r₁ := by
  change cfg.b ≤ cfg.δ ^ cfg.exscal * (cfg.δ ^ cfg.exscal)
  rw [← NNReal.rpow_add (ne_of_gt cfg.hδ) cfg.exscal cfg.exscal]
  rw [← two_mul cfg.exscal]
  exact hnotslab

/-- **The thin-case refinement constant is below the fixed-scale threshold.**

The seventh clause `Kakeya.VeryNotSticky.CaseScale.transverse_ballFill` of Configuration
`hyp:ml2scale` reads `1000 · C_transfer(C, C₀) ≤ δ^{-η}` in `NNReal`, and
`Kakeya.ThinCase.transferConstant C C₀` dominates `C` once `1 ≤ C` and `1 ≤ C₀`. This is that
clause read in `ENNReal`, which is where `Kakeya.VeryNotSticky.tangentialSlabMultAbsorb`
consumes it. -/
theorem thinConstant_le (cfg : VeryNotSticky.{u}) {bd : BallData cfg} (tc : ThinConfig cfg bd)
    {B : bd.bι} (hB : B ∈ bd.bs) {τ τ' νA : ℝ} {thr : ScaleThresholds}
    (scale : CaseScale cfg bd τ τ' νA tc.C thr) :
    (tc.C : ℝ≥0∞) ≤ (cfg.δ : ℝ≥0∞) ^ (-cfg.η) := by
  have hC1 : (1 : ℝ≥0) ≤ tc.C := (tc.thinBall hB).one_le_C
  have hw1b : (0 : ℝ≥0) ≤ ThinCase.w1Constant bd.C₀ := zero_le
  have h1w : (1 : ℝ≥0) ≤ 1 + ThinCase.w1Constant bd.C₀ := by
    exact le_add_of_nonneg_right hw1b
  have hw1 : (1 : ℝ≥0) ≤ (1 + ThinCase.w1Constant bd.C₀) ^ 3 := by
    simpa using (pow_le_pow_left₀ (zero_le : (0 : ℝ≥0) ≤ 1) h1w 3)
  have hCsq : (1 : ℝ≥0) ≤ tc.C ^ 2 := by
    simpa using (pow_le_pow_left₀ (zero_le : (0 : ℝ≥0) ≤ 1) hC1 2)
  have hbig : (1 : ℝ≥0) ≤ 2 ^ 12 * tc.C ^ 2 := by
    calc
      (1 : ℝ≥0) ≤ 2 ^ 12 := by norm_num
      _ = 2 ^ 12 * 1 := by ring
      _ ≤ 2 ^ 12 * tc.C ^ 2 := mul_le_mul_of_nonneg_left hCsq (by positivity)
  have hC2 : tc.C ≤ 2 ^ 12 * tc.C ^ 3 := by
    calc
      tc.C = tc.C * 1 := by ring
      _ ≤ tc.C * (2 ^ 12 * tc.C ^ 2) :=
        mul_le_mul_of_nonneg_left hbig (zero_le : (0 : ℝ≥0) ≤ tc.C)
      _ = 2 ^ 12 * tc.C ^ 3 := by ring
  have hupper : 2 ^ 12 * tc.C ^ 3 ≤ ThinCase.netUpperConstant tc.C bd.C₀ := by
    calc
      2 ^ 12 * tc.C ^ 3 = (2 ^ 12 * tc.C ^ 3) * 1 := by ring
      _ ≤ (2 ^ 12 * tc.C ^ 3) * (1 + ThinCase.w1Constant bd.C₀) ^ 3 :=
        mul_le_mul_of_nonneg_left hw1 (by positivity)
      _ = 2 ^ 12 * tc.C ^ 3 * (1 + ThinCase.w1Constant bd.C₀) ^ 3 := by ring
      _ ≤ ThinCase.netUpperConstant tc.C bd.C₀ := le_max_right _ _
  have hCnet : tc.C ≤ ThinCase.netUpperConstant tc.C bd.C₀ := le_trans hC2 hupper
  have hnu_le_tr :
      ThinCase.netUpperConstant tc.C bd.C₀ ≤ ThinCase.transferConstant tc.C bd.C₀ := by
    rw [ThinCase.transferConstant]
    calc
      ThinCase.netUpperConstant tc.C bd.C₀ = ThinCase.netUpperConstant tc.C bd.C₀ * 1 := by ring
      _ ≤ ThinCase.netUpperConstant tc.C bd.C₀ * (2 ^ 3 : ℝ≥0) :=
        mul_le_mul_of_nonneg_left (by norm_num : (1 : ℝ≥0) ≤ (2 ^ 3 : ℝ≥0))
          (zero_le : (0 : ℝ≥0) ≤ ThinCase.netUpperConstant tc.C bd.C₀)
      _ ≤ (ThinCase.netUpperConstant tc.C bd.C₀ * (2 ^ 3 : ℝ≥0)) *
            ThinCase.netLowerConstant tc.C := by
        simpa using
          mul_le_mul_of_nonneg_left (ThinCase.one_le_netLowerConstant tc.C)
            (zero_le : (0 : ℝ≥0) ≤
              ThinCase.netUpperConstant tc.C bd.C₀ * (2 ^ 3 : ℝ≥0))
      _ = (2 ^ 3 : ℝ≥0) * ThinCase.netUpperConstant tc.C bd.C₀ *
            ThinCase.netLowerConstant tc.C := by ring
  have hCdom : tc.C ≤ 1000 * ThinCase.transferConstant tc.C bd.C₀ := by
    calc
      tc.C ≤ ThinCase.netUpperConstant tc.C bd.C₀ := hCnet
      _ ≤ ThinCase.transferConstant tc.C bd.C₀ := hnu_le_tr
      _ ≤ 1000 * ThinCase.transferConstant tc.C bd.C₀ := by
        simpa [mul_comm] using
          mul_le_mul_of_nonneg_left (by norm_num : (1 : ℝ≥0) ≤ (1000 : ℝ≥0))
            (zero_le : (0 : ℝ≥0) ≤ ThinCase.transferConstant tc.C bd.C₀)
  have hC : tc.C ≤ cfg.δ ^ (-cfg.η) := le_trans hCdom scale.transverse_ballFill
  calc
    (tc.C : ℝ≥0∞) ≤ ((cfg.δ ^ (-cfg.η) : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_le_coe.mpr hC
    _ = (cfg.δ : ℝ≥0∞) ^ (-cfg.η) := ENNReal.coe_rpow_of_ne_zero cfg.hδ.ne' _

/-- **The angle between a tube and the axis of its factoring body**, at the configuration
.

Let `T_B ∈ 𝕋_B` be a segment in the ball `B` and let `T ∈ 𝕋(T_B)` be one of its parent tubes.
By (C3) the segment is an `r₁ × δ × δ` body lying within `C₀δ` of the core line of `T`, and by
(C4) it lies in the factoring body `W = W(T_B)`, an `r₁ × b × a` body. So
`Kakeya.NonSlab.lineAngle_bodyAxis_le` applies and gives
`∠(T, v(W)) ≤ C_{lem:ml2bodyAngle}(C₀) · b/r₁ = C_{lem:ml2bodyAngle}(C₀) ρ₂ = ρ₂*/2`.

The factor `1/2` in the statement is not cosmetic: `Kakeya.VeryNotSticky.angularInnerCount`
doubles the angle when it passes from the axis `v(W)` to a *tube* through the point, and it is
the doubled angle that must be `ρ₂*`. That is exactly how `ρ₂*` is defined. -/
theorem segAngle (cfg : VeryNotSticky.{u}) {bd : BallData cfg} {B : bd.bι} (hB : B ∈ bd.bs)
    {p : bd.σ} (hp : p ∈ bd.segs B) {i : cfg.ι} (hi : i ∈ bd.fam p) :
    NonSlab.lineAngle (cfg.T i).direction (bodyAxis (bd.Wb (bd.blk p))) ≤
      (cfg.rho2Star bd.C₀ : ℝ) / 2 := by
  have hbr₁ : cfg.b ≤ cfg.r₁ := by
    simpa [r₁] using cfg.hdims.2.2
  rcases bd.segs_core B hB p hp i hi with ⟨q, hST⟩
  have hu : ‖(cfg.T i).direction‖ = 1 := (cfg.T i).norm_direction
  have hSW : (bd.Y p).carrier ⊆ (bd.Wb (bd.blk p)).carrier := by
    exact SetLike.coe_subset_coe.mpr (bd.segs_le B hB p hp)
  calc
    NonSlab.lineAngle (cfg.T i).direction (bodyAxis (bd.Wb (bd.blk p))) ≤
        (NonSlab.bodyAngleConstant bd.C₀ : ℝ) * ((cfg.b : ℝ) / (cfg.r₁ : ℝ)) := by
      exact NonSlab.lineAngle_bodyAxis_le (E := EuclideanSpace ℝ (Fin 3)) (C₀ := bd.C₀)
        (δ := cfg.δ) (a := cfg.a) (b := cfg.b) (r₁ := cfg.r₁) (S := (bd.Y p).carrier)
        (p := q) (u := (cfg.T i).direction)
        finrank_euclideanSpace_fin bd.hC₀ cfg.hδ
        cfg.hdims.1 cfg.hdims.2.1 hbr₁ (bd.Wb (bd.blk p))
        (bd.bodies_thickness B hB (bd.blk p) (bd.blk_mem B hB p hp))
        hSW
        (bd.segs_thickness B hB p hp) hu (by simpa using hST)
    _ = (cfg.rho2Star bd.C₀ : ℝ) / 2 := by
      simp [rho2Star, rho2, NNReal.coe_div, NNReal.coe_mul]
      ring

/-- **The compatible refinement at a piece of the partition** (blueprint
`lem:ml2nonslabCompat`, at the configuration).

`Kakeya.NonSlab.compat` instantiated at the ball `B`, with the working shading `Yg := bd.Yg`: its six set-theoretic hypotheses are the fields
`Kakeya.VeryNotSticky.ThinConfig.Y'_subset`, `Kakeya.VeryNotSticky.BallData.parent`,
`Kakeya.VeryNotSticky.BallData.into`, the carrier containment of `bd.Y p`,
`Kakeya.VeryNotSticky.ThinConfig.compat_forward` and
`Kakeya.ThinCase.ThinBall.shade_containment`; its angular hypothesis is
`Kakeya.VeryNotSticky.segAngle`. The conclusion is repackaged as membership in
`Kakeya.VeryNotSticky.angularFibre`, which is the form the counting step consumes; the point
lies in `Y_g(T) ⊆ Y(T)` by `Kakeya.VeryNotSticky.BallData.Yg_subset`. -/
theorem nonslabCompatAt (cfg : VeryNotSticky.{u}) {bd : BallData cfg} (tc : ThinConfig cfg bd)
    {B : bd.bι} (hB : B ∈ bd.bs) {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ bd.P B) :
    ∀ i ∈ cfg.s, x ∈ tc.Y' i →
      ∃ j ∈ (tc.thinBall hB).bodies', x ∈ ((tc.thinBall hB).W j).shade ∧
        i ∈ cfg.angularFibre x (bodyAxis (bd.Wb j)) ((cfg.rho2Star bd.C₀ : ℝ) / 2) := by
  classical
  intro i hi hxY'
  rcases Kakeya.NonSlab.compat (I := cfg.s) (Yg := bd.Yg)
      (Y' := tc.Y') (dir := fun i ↦ (cfg.T i).direction) (Pc := bd.P B)
      (segs := bd.segs B) (fam := bd.fam) (carr := fun p ↦ (bd.Y p).carrier)
      (Yb := fun p ↦ (bd.Y p).shade) (Yb' := fun p ↦ ((tc.thinBall hB).Y' p).shade)
      (blk := bd.blk) (bodies' := (tc.thinBall hB).bodies') (Wsh := (tc.thinBall hB).W)
      (ax := fun j ↦ bodyAxis (bd.Wb j)) (ρ := (cfg.rho2Star bd.C₀ : ℝ) / 2)
      tc.Y'_subset (bd.parent B hB) (bd.into B hB)
      (fun p _ ↦ (bd.Y p).shade_subset) (tc.compat_forward B hB)
      ((tc.thinBall hB).shade_containment)
      (fun p hp i' hi' ↦ segAngle cfg hB hp hi') hx i hi hxY' with
    ⟨j, hj, hshade, hxYg, hangle⟩
  refine ⟨j, hj, hshade, ?_⟩
  rw [angularFibre]
  exact Finset.mem_filter.mpr ⟨hi, bd.Yg_subset i hi hxYg, hangle⟩

/-- **The pointwise product bound at the maximising ball**.

Let `B'` be the piece of the subordinate partition of (C2) containing `x`, which exists by
`Kakeya.VeryNotSticky.BallData.P_cover` (on the working shading `Y_g ⊇ Y'`). Reading
`Kakeya.VeryNotSticky.nonslabCompatAt` there
places every tube of `𝕋_{Y'}(x)` in one of the angular fibres
`{T ∈ 𝕋_Y(x) : ∠(T, v(W)) ≤ ρ₂*/2}`, indexed by the bodies `W ∈ 𝕎'_{B'}` shading `x`. There
are at most `C μ(𝕎'_{B'}, Y_{𝕎'_{B'}}) ≤ C μ(𝕎'_B, Y_{𝕎'_B})` such bodies — the first step by
(T4)(a) and `Kakeya.ShadedBody.pointwiseMultiplicity_le_mul_multiplicity`, the second by the
maximality of `B` — and each fibre, being contained in the angular fibre at the full radius
`ρ₂*`, has at most `A` elements by the hypothesis `hang`. Multiplying the two counts gives the
bound.

`hang` is GWZ's "the cardinality of the inner set is `⪅ μ(ρ₂)`" (GWZ), taken as a
bound on the inner angular count at *every* point and direction; the splitting supplies it from
the field `Kakeya.VeryNotSticky.SplitInputs.angularFibre_le_fibreMult` at the selected node,
with `A = Cang · μ(𝕋[T_{ρ₂*}], Y)` (the separate angular formulation took the angular
multiplicity function `μ(ρ)` of GWZ's step 1, through
`Kakeya.VeryNotSticky.angularFibre_card_le_mul_mu`, as the intermediary). The range binders
`δ ≤ ρ₂* ≤ 1`, which placed `ρ₂*` in the domain of `μ`, are received in lockstep with
`Kakeya.VeryNotSticky.nonslabSplitBound` for the statement's shape only and are not used.

Both losses are independent of `B'`, which is what allows the bound to be stated at the single
maximising ball while the argument runs at the varying ball. -/
theorem nonslabPointwiseBound (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    (tc : ThinConfig cfg bd) {B : bd.bι} (hB : B ∈ bd.bs)
    (hBmax : ∀ B' (hB' : B' ∈ bd.bs),
      ShadedBody.multiplicity (tc.thinBall hB').bodies' (tc.thinBall hB').W ≤
        ShadedBody.multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W)
    {A : ℝ≥0∞}
    (hang : ∀ x v : EuclideanSpace ℝ (Fin 3),
      (((cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) : ℝ≥0∞) ≤ A)
    (_hδρ : (cfg.δ : ℝ) ≤ (cfg.rho2Star bd.C₀ : ℝ))
    (_hρ1 : (cfg.rho2Star bd.C₀ : ℝ) ≤ 1)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ ShadedBody.iUnionShade cfg.s tc.Y'Body) :
    (ShadedBody.pointwiseMultiplicity cfg.s tc.Y'Body x : ℝ≥0∞) ≤
      ((tc.C : ℝ≥0∞) *
          ShadedBody.multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W) * A := by
  classical
  rcases Set.mem_iUnion₂.mp hx with ⟨i₀, hi₀s, hxi₀⟩
  rw [ThinConfig.Y'Body_shade tc hi₀s] at hxi₀
  have hxTi₀ : x ∈ bd.Yg i₀ := tc.Y'_subset i₀ hi₀s hxi₀
  rcases Set.mem_iUnion₂.mp (bd.P_cover i₀ hi₀s hxTi₀) with ⟨B', hB', hxB'⟩
  let tb' : ThinCase.ThinBall tc.C bd.C₀ (bd.segs B') bd.Y (bd.bodies B') bd.Wb bd.blk
      cfg.δ cfg.a (2 * cfg.η) := tc.thinBall hB'
  let ρ : ℝ := (cfg.rho2Star bd.C₀ : ℝ) / 2
  let f : bd.ω → Finset cfg.ι := fun j => cfg.angularFibre x (bodyAxis (bd.Wb j)) ρ
  let J : Finset bd.ω := {j ∈ tb'.bodies' | x ∈ (tb'.W j).shade}
  let M : ℝ≥0∞ := ShadedBody.multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W
  have hcompat : ∀ i ∈ cfg.s, x ∈ tc.Y' i →
      ∃ j ∈ tb'.bodies', x ∈ (tb'.W j).shade ∧ i ∈ f j := by
    intro i hi hxi
    rcases nonslabCompatAt cfg tc hB' hxB' i hi hxi with ⟨j, hj, hjx, hij⟩
    exact ⟨j, hj, hjx, hij⟩
  have hsub : {i ∈ cfg.s | x ∈ (tc.Y'Body i).shade} ⊆ J.biUnion f := by
    intro i hi
    rcases Finset.mem_filter.mp hi with ⟨hi₀s, hxi₀⟩
    rw [ThinConfig.Y'Body_shade tc hi₀s] at hxi₀
    rcases hcompat i hi₀s hxi₀ with ⟨j, hj, hjx, hij⟩
    refine Finset.mem_biUnion.mpr ⟨j, ?_, hij⟩
    simp [J, Finset.mem_filter, hj, hjx]
  -- the half-radius fibre sits inside the angular fibre at the full radius `ρ₂*`
  have hρle : ρ ≤ (cfg.rho2Star bd.C₀ : ℝ) := by
    have h0 : (0 : ℝ) ≤ (cfg.rho2Star bd.C₀ : ℝ) := NNReal.coe_nonneg _
    dsimp [ρ]
    linarith
  have hfsub : ∀ j, f j ⊆ cfg.angularFibre x (bodyAxis (bd.Wb j)) (cfg.rho2Star bd.C₀ : ℝ) := by
    intro j i hi
    change i ∈ cfg.angularFibre x (bodyAxis (bd.Wb j)) ρ at hi
    rw [angularFibre] at hi ⊢
    rcases Finset.mem_filter.mp hi with ⟨his, hxi, hiang⟩
    exact Finset.mem_filter.mpr ⟨his, hxi, hiang.trans hρle⟩
  have hinnerE : ∀ j ∈ J, ((f j).card : ℝ≥0∞) ≤ A := by
    intro j _
    calc
      ((f j).card : ℝ≥0∞)
          ≤ (((cfg.angularFibre x (bodyAxis (bd.Wb j)) (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) :
              ℝ≥0∞) := by
            exact_mod_cast Finset.card_le_card (hfsub j)
      _ ≤ A := hang x (bodyAxis (bd.Wb j))
  have hsumE : (∑ j ∈ J, ((f j).card : ℝ≥0∞)) ≤ (J.card : ℝ≥0∞) * A := by
    calc
      (∑ j ∈ J, ((f j).card : ℝ≥0∞)) ≤ (∑ _j ∈ J, A) := Finset.sum_le_sum hinnerE
      _ = (J.card : ℝ≥0∞) * A := by
            rw [Finset.sum_const, nsmul_eq_mul]
  have hptw : (ShadedBody.pointwiseMultiplicity cfg.s tc.Y'Body x : ℝ≥0∞) ≤
      (J.card : ℝ≥0∞) * A := by
    calc
      (ShadedBody.pointwiseMultiplicity cfg.s tc.Y'Body x : ℝ≥0∞)
          ≤ (((J.biUnion f).card : ℕ) : ℝ≥0∞) := by
            exact_mod_cast (Finset.card_le_card hsub)
      _ ≤ ((∑ j ∈ J, (f j).card : ℕ) : ℝ≥0∞) := by
            exact_mod_cast (Finset.card_biUnion_le (s := J) (t := f))
      _ = (∑ j ∈ J, ((f j).card : ℝ≥0∞)) := by
            simp [Nat.cast_sum]
      _ ≤ (J.card : ℝ≥0∞) * A := hsumE
  have hC : 0 < tc.C := lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 1) tb'.one_le_C
  have hrefl : ShadedBody.IsCRefinement tb'.bodies' tb'.W tb'.bodies' tb'.W 1 := by
    refine ⟨?_, ?_⟩
    · exact ⟨Finset.Subset.rfl, fun i _ => ⟨rfl, Set.Subset.rfl⟩⟩
    · simp
  have hne : volume (ShadedBody.iUnionShade tb'.bodies' tb'.W) ≠ 0 :=
    (thinBallPositivity_iUnionShade_pos cfg tc hB' zero_lt_one hrefl).ne'
  have hJcard : (J.card : ℝ≥0∞) ≤ (tc.C : ℝ≥0∞) * M := by
    calc
      (J.card : ℝ≥0∞)
          = (ShadedBody.pointwiseMultiplicity tb'.bodies' tb'.W x : ℝ≥0∞) := by simp [J]
      _ ≤ (tc.C : ℝ≥0∞) * ShadedBody.multiplicity tb'.bodies' tb'.W := by
            exact pointwiseMultiplicity_le_mul_multiplicity tb'.bodies' tb'.W hC hne
              tb'.constMult_bodies x
      _ ≤ (tc.C : ℝ≥0∞) * M := by
            exact mul_le_mul_of_nonneg_left (by simpa [tb', M] using hBmax B' hB')
              (zero_le : 0 ≤ (tc.C : ℝ≥0∞))
  calc
    (ShadedBody.pointwiseMultiplicity cfg.s tc.Y'Body x : ℝ≥0∞) ≤
        (J.card : ℝ≥0∞) * A := hptw
    _ ≤ ((tc.C : ℝ≥0∞) * M) * A := by
          exact mul_le_mul_of_nonneg_right hJcard (zero_le : 0 ≤ A)

/-! ### The splitting bound at one ball, packaged -/

/-- **Input of the non-slab splitting at the ball `B`** (blueprint
`lem:ml2tangentialSplit`(i)–(iii), i.e. `lem:ml2tangential`(c)).

These are the hypotheses that `Kakeya.VeryNotSticky.nonslabKKT` and
`Kakeya.VeryNotSticky.nonslabKKTPow` do not discharge for themselves and that nothing in the
non-slab case discharges either. They mention neither the ball `B` nor the angle `θ`, which
is why they form a bundle over `cfg` and `bd` alone.

* `katzTao` is item (i), the availability of `K_KT(β)` at this fixed `δ` with loss `ϱ` — the
  cross-section that blueprint `lem:ml2ktScaleDataAvail` produces from `δ ≤ δ₀(ϱ, β)` and
  `η ≤ η₁(ϱ, β)`. It is not derivable from `cfg.ktEstimate`, which holds only eventually in
  `δ`, and it is not implied by `Kakeya.VeryNotSticky.CaseParams`.
* `fibreConstant` is item (ii), blueprint `fibreConstantThreshold`: the hypothesis of
  `Kakeya.VeryNotSticky.nonslabKKTPow`, the sole source of the `+η` in `muTTRhoPow`, which
  `δ = 1` falsifies. It also absorbs the hierarchy constant `Cu²`
  of `fibreCount` as well.
* `N`, `Cu`, `uniform`, `k`, `k_le`, `gridScale_ge`, `gridScale_le`, `fibreCount` and
  `fibreScaleCount` **replace** item (iii) of the blueprint statement. Where the blueprint
  assumes the exact fibre count `exactFibreCount` at every `T_{ρ₂*} ∈ 𝕋_{ρ₂*}`, the Lean form
  assumes a uniform hierarchy for `(𝕋, Y)` with a grid level `k` sitting at the dilated scale
  `ρ₂*` up to the grid rounding `δ^{-η}`: its
  assignment classes structurally partition the leaf family, so a *full* fibre can be selected
  without assuming the count. This is a deliberate divergence, recorded in the blueprint
  statement of `lem:ml2tangentialSplit`; `fibreScaleCount` is the price it costs, and
  `fibreCount` is, at its constant `Cu²`, a consequence of `uniform`
  (`Kakeya.VeryNotSticky.card_indexSet_mul_card_tubeFibre_le`) kept as a field for the
  interface; both are described on the fields themselves.

**The angular clause.** `Cang`, `angularConstant` and `angularFibre_le_fibreMult` carry GWZ's
composed bound at GWZ — "the cardinality of the inner set is `⪅ μ(ρ₂) ≈
μ(𝕋[T_{ρ₂}], Y)`" — at this configuration: the inner angular count at every point and
direction is at most `Cang` times the multiplicity of the fibre of any active node at the
level `k`, with a fixed-scale threshold on `Cang`. The angular multiplicity function `μ(ρ)` of
GWZ's step 1, through which GWZ derive that bound, is
not recorded here: GWZ assert (86) on a shading that is not the uniform one and use only this
consequence. See the fields themselves.

**Why the hierarchy is not required to be the one `cfg` already carries — and why it may be.** `cfg.uniform` asserts the existence of a
`ShadedTube.ShadedUniformTubeSet` for `(𝕋, Y)` at the *fixed* grid length
`Tube.ssfGridLen δ = ⌈log log (1/δ)⌉`, that being the grid the sticky/non-sticky
dichotomy of Section 3 runs on. Its levels sit at the scales `δ^{k/⌈log log (1/δ)⌉}`, and
`ρ₂* = 2 C_{lem:ml2bodyAngle}(C₀) b / r₁` is determined by the configuration's dimensions and
by `C₀`; nothing makes it one of those finitely many scales, so an *exact* level at `ρ₂*` —
the field's earlier form, `gridScale_eq : Tube.gridScale cfg.δ N k = cfg.rho2Star bd.C₀` —
would have been unsatisfiable at `N = ssfGridLen δ`, which is why `N` was left free. That
exactness was over-strong against the source: GWZ have the hierarchy only at the grid scales
`δ^{k/M}` (Def 2.1, GWZ ) and at every other `ρ ∈ [δ, 1]` only up to `≈` (the
remark after Def 2.2), and they write the same rounding out for the transverse
radius, `θb ≤ r ≤ δ^{-η} θb`. The fields `gridScale_ge` and `gridScale_le`
therefore pin the level `k` to `ρ₂*` *two-sidedly*, `ρ₂* ≤ δ^{k/N} ≤ δ^{-η} ρ₂*`. With `N := Tube.ssfGridLen δ` such a level exists once `1 ≤ η · ssfGridLen δ`
(`Kakeya.VeryNotSticky.eventually_gridFine`), because `ρ₂* ∈ [δ, 1]`
(`Kakeya.VeryNotSticky.rho2Star_range`), so `uniform` *may* be the tube part of
`cfg.uniform`'s hierarchy; nothing here requires it, and `N` stays free. In the other direction
the field asks for less than `cfg.uniform` does: only the underlying tube hierarchy is used
(fibre selection and counting are both statements about the assignment classes
`Kakeya.VeryNotSticky.tubeFibre`), so a `Tube.UniformTubeSet` suffices and no
shading-uniformity clause is assumed. The two-sided pin is spent nowhere as an equality:
`Kakeya.VeryNotSticky.exists_full_fibre` and `Kakeya.VeryNotSticky.nonslabFibrePartition`
receive it in lockstep and do not use it. -/
structure SplitInputs (cfg : VeryNotSticky.{u}) (bd : BallData cfg) where
  /-- the number of grid levels of the hierarchy -/
  N : ℕ
  /-- the uniformity constant of the hierarchy -/
  Cu : ℝ≥0
  /-- item (iii): a uniform hierarchy for the family `𝕋` -/
  uniform : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) N Cu
  /-- the grid level sitting at the dilated angular scale `ρ₂*`, up to the grid rounding -/
  k : ℕ
  /-- that level is one of the `N` levels -/
  k_le : k ≤ N
  /-- The scale comparison is `ρ₂* ≤ δ^{k/N}`; it is one-sided because
GWZ Definition 2.2 specifies approximate grid scales. -/
  gridScale_ge : cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ N k
  /-- and from above with the grid rounding loss `δ^{-η}`, `δ^{k/N} ≤ δ^{-η} ρ₂*` — the same
  rounding GWZ write out for the transverse radius, `θb ≤ r ≤ δ^{-η} θb` -/
  gridScale_le : Tube.gridScale cfg.δ N k ≤ cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀
  /-- item (i): `K_KT(β)` at this `δ` with loss `ϱ` -/
  katzTao : cfg.KTScaleData cfg.ϱ
  /-- item (ii): blueprint `fibreConstantThreshold`, with the hierarchy constant `Cu²` of
  `fibreCount` absorbed alongside `(2 C_{lem:ml2bodyAngle}(C₀))²` -/
  fibreConstant : ((Cu : ℝ≥0∞) ^ 2) *
      ((2 * NonSlab.bodyAngleConstant bd.C₀ : ℝ≥0) : ℝ≥0∞) ^ 2 ≤
    (cfg.δ : ℝ≥0∞) ^ (-cfg.η)
  /-- Blueprint `uniformSetOfTubes` item (iii) — GWZ Def 2.1(iii), "`|𝕋[T_ρ]|` is constant up
  to a factor `∼ 1`" (GWZ) — in the inequality shape that
  `Kakeya.VeryNotSticky.nonslabKKTPow` consumes as its hypothesis `hfib`:
  `|𝕋_{ρ₂*}| · |𝕋[T_{ρ₂*}]| ≤ Cu² |𝕋|`, uniformly over the nodes at level `k`, with the
  hierarchy's own constant `Cu` squared.

  At this constant the clause *is* derivable from `uniform`:
  `Kakeya.VeryNotSticky.card_indexSet_mul_card_tubeFibre_le` proves it from
  `Tube.UniformTubeSet.card_class_le`, `le_card_class` and the partition of `cfg.s` into the
  assignment classes. It is kept as a field so that the interface of the splitting is
  unchanged; a producer populates it by that lemma. Stating it for every node is what lets the
  fibre selected by `Kakeya.VeryNotSticky.exists_full_fibre` be used. -/
  fibreCount : ∀ j ∈ uniform.cover.indexSet k,
    ((uniform.cover.indexSet k).card : ℝ) * ((cfg.tubeFibre uniform k j).card : ℝ) ≤
      ((Cu : ℝ) ^ 2) * (cfg.s.card : ℝ)
  /-- The constant of the `ρ₂`-count clause `fibreScaleCount`: a `δ^{-O(η)}` of the same kind
  as `Cang`, and **not** the δ-free `(2 C_{lem:ml2bodyAngle}(C₀))²` this field used to carry.
  A fixed constant independent of `δ` is insufficient for this comparison: the
  field counts bounded-overlap nodes of `cfg.splitHierarchy`, the configuration counts
  essentially distinct covers of a *parent* family
  (`Kakeya.VeryNotSticky.RhoParentData`), and both transports — `ρ₂ → ρ_k` and
  ED-parents → nodes — cost powers of `δ^{-η}` with the wrong sign for a δ-free conclusion. -/
  Ccnt : ℝ≥0
  /-- The fixed-scale threshold on that constant, the exact analogue of `fibreConstant` and of
  `angularConstant`, at the exponent `18` measured by the producer
  `Kakeya.VeryNotSticky.exists_fibreScaleCount_of_rhoParentData` (the general form requires `M ≥ 4`). GWZ carry an explicit `δ^{-O(η)}` at exactly
  the site where this count is spent (GWZ), and the `≈`/`⪅` of Def 2.1(iii) is `δ^{-O(η)}` in their own bookkeeping. -/
  countConstant : (Ccnt : ℝ≥0∞) ≤ (cfg.δ : ℝ≥0∞) ^ (-(18 * cfg.η))
  /-- The `ρ₂`-counting input of `Kakeya.VeryNotSticky.nonslabKKTPow`, its hypothesis
  `hcount`: the number of nodes of the hierarchy at the level `k` is at least
  `Ccnt^{-1} ρ₂^{-2-ζ}`.

  In the blueprint this is not a hypothesis: it is `rho2_range`,
  which bounds `|𝕋_{ρ₂}| ≥ ρ₂^{-2-ζ}` from below, transported from the scale `ρ₂` to the
  dilated scale `ρ₂*` by `lem:ml2tubeScaleCompare`. Neither step is available for this
  hierarchy at the δ-free constant, and the obstruction is the same at both:

  * `rho2_range` fires only for a family of `ρ₂`-tubes covering `𝕋` that is *pairwise
    essentially distinct*, and `Tube.UniformTubeSet` deliberately does not provide
    that — its `boundedOverlap` replaces essential distinctness, which is unsatisfiable while
    preserving cardinality;
  * `Kakeya.VeryNotSticky.tubeScaleCompare` compares two grid *levels* of one hierarchy, and
    `gridScale_ge`/`gridScale_le` pin a level only at `ρ₂*` (up to `δ^{-η}`); a second level
    at `ρ₂` would still need `rho2_range` there, so it does not help.

  Both are paid for by `Ccnt`/`countConstant`, which is what makes the clause producible:
  `Kakeya.VeryNotSticky.exists_fibreScaleCount_of_rhoParentData` derives it from
  `cfg.rho_count`. It is carried in exactly the shape `nonslabKKTPow` consumes, and it travels
  with the rest of item (iii) — it is created by the divergence recorded above, not by the
  blueprint. -/
  fibreScaleCount : (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤
    (Ccnt : ℝ) * ((uniform.cover.indexSet k).card : ℝ)
  /-- The constant hidden in GWZ's "`⪅ μ(ρ₂) ≈ μ(𝕋[T_{ρ₂}], Y)`" (GWZ): a
  `δ^{-O(η)}` of dyadic-pigeonhole origin, not absolute. -/
  Cang : ℝ≥0
  /-- The fixed-scale threshold on that constant, the exact analogue of `fibreConstant`. -/
  angularConstant : (Cang : ℝ≥0∞) ≤ (cfg.δ : ℝ≥0∞) ^ (-cfg.η)
  /-- **GWZ (100)–(101) composed** (GWZ): at every point `x` and for every
  direction `v`, the tubes of `𝕋_Y(x)` within angle `ρ₂*` of `v` number at most `Cang` times the
  multiplicity of the fibre `𝕋[T_{ρ₂*}]` of any active node of the hierarchy at the level `k`.
  This is what `Kakeya.VeryNotSticky.nonslabPointwiseBound` consumes; the angular multiplicity
  function `μ(ρ)` of GWZ's step 1, through which GWZ derive it, is not recorded:
  GWZ assert (86) on a shading that is not the uniform one and use only this consequence.
  Quantified over the active nodes for the reason recorded on
  `Kakeya.VeryNotSticky.exists_full_fibre`. -/
  angularFibre_le_fibreMult : ∀ j ∈ cfg.activeTubeNodes uniform k,
    ∀ x v : EuclideanSpace ℝ (Fin 3),
      (((cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) : ℝ≥0∞) ≤
        (Cang : ℝ≥0∞) *
          ShadedBody.multiplicity (cfg.tubeFibre uniform k j) (fun i ↦ (cfg.T i).toShadedBody)


end Kakeya.VeryNotSticky

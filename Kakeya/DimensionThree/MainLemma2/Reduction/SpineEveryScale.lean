/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.MultiScaleFac
public import Kakeya.MultiScaleLoss
public import Kakeya.StickyKakeya
public import Kakeya.StickyKakeya.Reindex
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineParams

/-!
# Main Lemma 2, the spine: the dividing-scales dichotomy and its every-scale branch

The first two sentences of the blueprint's "Proof of Main Lemma~\ref{lemmain2}"
(GWZ):

> Apply Lemma `dividingScalesLemmaB` to `𝕋`.  If Conclusion (i) holds, then (provided we select
> `ε₂ ≤ ε₁/5`) we have that `𝕋` is `δ^{-ε₁}` Katz–Tao at every scale, and hence by Theorem
> `katzTaoAtEveryScaleImpliesMultSmall` we have `μ(𝕋,Y) ≤ δ^{-ε}`, and thus `(mugoalml2quant)`
> is satisfied.

Four things are carried here.

* **The dichotomy**, `Kakeya.ML2Reduction.exists_dichotomy_katzTaoDividingWindow`: GWZ Lemma
  7.7(B) (`StickyKakeya.dividingScalesKatzTao`) read at the Main-Lemma-2 parameters
  `N = stepCount ε₂` and `ε_div = epsDiv N = 1/√N`, with alternative (ii) bundled into the named
  predicate `Kakeya.ML2Reduction.IsKatzTaoDividingWindow` and alternative (i) already stated at
  the accuracy `ε₂` rather than at the lemma's own `5 ε_div`.
* **The `ε₂ ≤ ε₁/5` bookkeeping**, `Kakeya.ML2Reduction.exists_threshold_katzTaoError_le` and
  `Kakeya.ML2Reduction.exists_dichotomy_katzTaoAtEveryScale`: alternative (i) of GWZ Lemma 7.7(B)
  reads `Δ_max(𝕋_ρ) ≤ C · L(δ) · δ^{-5 ε_div}` with a *displayed* subpolynomial loss `L(δ)`
  (`StickyKakeya.totalLoss`), not a clean power.  Choosing `N = ⌈25/ε₂²⌉` makes `5 ε_div ≤ ε₂`,
  and `ε₂ ≤ ε₁/5` then leaves the four fifths `4ε₁/5` of the budget free to absorb `C · L(δ)`,
  which is what `StickyKakeya.exists_threshold_totalLoss_le` does below a threshold depending only
  on `C`, `K`, `c` and `ε₁`.  The output is the clean `δ^{-ε₁}` that GWZ Theorem 7.3(B) asks for.
* **The every-scale branch**, `Kakeya.ML2Reduction.exists_everyScale_multiplicity_le` and
  `Kakeya.ML2Reduction.exists_everyScale_goal`: GWZ Theorem 7.3(B), which this development owns as
  `StickyKakeya.StickyKatzTaoEstimate` and *proves* from sticky Kakeya 7.3(A)
  (`StickyKakeya.StickyFrostmanEstimateAt`, the one external assumption, carried as a
  hypothesis) by
  `StickyKakeya.stickyKatzTaoEstimate_of_stickyFrostmanEstimate`.
* **The assembly with the parameter spine**,
  `Kakeya.ML2Reduction.exists_dichotomy_katzTaoAtEveryScale_params`,
  `Kakeya.ML2Reduction.exists_dichotomy_katzTaoAtEveryScale_of_isSpine`,
  `Kakeya.ML2Reduction.exists_everyScale_exponent` and
  `Kakeya.ML2Reduction.exists_ml2_epsFree_dichotomy`.  `Kakeya.ML2Spine.IsSpine`
  (`Reduction/SpineParams.lean`) commits to its own `N` and `e = 1/√N` through `stepCount_eq`
  and `div_eq`, so the `stepCount`/`epsDiv` versions above, which fix those internally, cannot be
  applied to it; the `_params` version takes `(N, e)` from the caller, and the `_of_isSpine`
  version additionally discharges all four ladder hypotheses of GWZ Lemma 7.7(B) from the spine.
  `exists_ml2_epsFree_dichotomy` is the witness that the three pieces compose, with **both
  `ν` and `ε₁` bound before `∀ ε > 0`**.

  `StickyKakeya.dividingScalesKatzTao`'s side condition `4096 ≤ N` **is** discharged: it is the
  field `Kakeya.ML2Spine.IsSpine.four_thousand_le_stepCount`, added to `IsSpine` together with the
  tightening of `Kakeya.ML2Spine.spineEps₂` from `min … (1/2)` to `min … (1/64)` that makes it
  realizable (`⌈25/ε₂²⌉ ≥ 25 · 64² = 102400`).  Neither
  `Kakeya.ML2Reduction.exists_dichotomy_katzTaoAtEveryScale_of_isSpine` nor
  `Kakeya.ML2Reduction.exists_ml2_epsFree_dichotomy` carries it as a hypothesis any more.
  `Kakeya.ML2Reduction.four_thousand_le_of_div_eq` remains, for callers that hold the exponent
  `e = 1/√N` rather than a spine; `Kakeya.ML2Spine.IsSpine.div_le_inv64` is its converse.

## `ε₀` is absolute, and that is why `|𝕋| ≥ δ^{-1}` is needed

Per Prof. Hong Wang's clarification of 2026-08-30, the published dependency chain
`ε → ε₁ → ε₂ → (N, η_i) → ν` must not make `ν` depend on `ε`.  The only place where `ε` could
leak into the chain is the accuracy at which GWZ Theorem 7.3(B) is read, so **that accuracy is a
parameter `ε₀` of `Kakeya.ML2Reduction.exists_everyScale_multiplicity_le`, and the caller is meant
to fix it once from `β` alone** — never from its own `ε`.  Everything downstream of it (`ε₁`, and
hence `ε₂`, `N`, the ladder `η_i` and `ν`) is then a function of `β` alone.

The price is that the branch concludes `μ(𝕋, Y) ≤ δ^{-ε₀}` with `ε₀` possibly much *larger* than
the goal's `ε`.  It is `Kakeya.ML2Reduction.ofReal_rpow_neg_le_mul_card_rpow` that closes the gap,
and it is the one place where the cardinality lower bound
`|𝕋| ≥ δ^{-1}` of the same clarification is spent: `|𝕋|^{β-ν} ≥ δ^{-(β-ν)}`, so
`δ^{-ε₀} ≤ δ^{-ε} |𝕋|^{β-ν}` as soon as `ε₀ ≤ ε + (β - ν)`, which a choice such as `ε₀ = β/2`
meets for every `ε > 0` once `ν ≤ β/2`.  Without the cardinality bound the branch supplies only
`μ(𝕋, Y) ≤ δ^{-ε₀} |𝕋|^{β-ν}` (`Kakeya.ML2Reduction.multiplicity_le_mul_card_rpow_of_le`), which
is the goal only when `ε₀ ≤ ε`.

## What is *not* here

The dichotomy hands back a subfamily `s' ⊆ s` carrying a *new* tube hierarchy `𝒰'`, while GWZ
Theorem 7.3(B) consumes a `ShadedTube.ShadedUniformTubeSet` — a uniform *shading* — read on the very
hierarchy the every-scale hypothesis is stated against.  Bridging the two is
`ShadedTube.exists_shadedUniformTubeSet_of_uniformTubeSet`, which refines the shading over the given
hierarchy without touching the index set or the nodes; that bridge, and the transport of the
resulting multiplicity bound back from `s'` to `s` across the cardinality loss
`|s| ≤ L(δ) |s'|`, belong to the assembly and are not asserted here.
`Kakeya.ML2Reduction.isKatzTaoAtEveryScale_of_cover_eq` is the small piece of that bridge which is
proved here, since it is a fact about `Tube.UniformTubeSet.IsKatzTaoAtEveryScale` alone.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric ShadedBody StickyKakeya Tube

namespace Kakeya.ML2Reduction

universe u w

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-! ### The two dividing-scales parameters -/

/-- **The number of stopping steps** of GWZ Lemma 7.7(B) at accuracy `ε₂`: the blueprint's
`N = ⌈25/ε₂²⌉`, floored at the `4096` that `StickyKakeya.dividingScalesKatzTao` requires.

The floor is harmless: the only property of `N` the reduction spends is
`Kakeya.ML2Reduction.five_mul_epsDiv_stepCount_le`, which a *larger* `N` only improves. -/
noncomputable def stepCount (ε₂ : ℝ) : ℕ := max 4096 ⌈25 / ε₂ ^ 2⌉₊

theorem four_thousand_le_stepCount (ε₂ : ℝ) : 4096 ≤ stepCount ε₂ := le_max_left _ _

/-! ### The dividing window: alternative (ii) of GWZ Lemma 7.7(B), bundled -/

/-- **The dividing window** of GWZ Lemma 7.7(B), alternative (ii), as a named predicate.

The seven fields are, in order and verbatim, the seven clauses of the right disjunct of
`StickyKakeya.dividingScalesKatzTao`.  The two scales of the blueprint are `θ = ρ_a` and
`τ = ρ_b`, so `a < b` is `τ ≤ θ`, `b ≤ ssfGridLen δ` is `δ ≤ τ`, and `scale_sep` is
`τ ≤ δ^{ε_div} θ`; the blueprint's step index `j` with `1 ≤ j ≤ N` is `m + 1` here, so its
`η_{j-1}` is `η m` and its `η_j` is `η (m + 1)` and no truncated subtraction occurs.

`Cstar` is the single error the three density clauses are read at.  At the one point where the
dichotomy produces a window it is `C · L(δ)` — the uniformity constant that
`StickyKakeya.dividingScalesKatzTao` *returns* times the subpolynomial loss
`StickyKakeya.totalLoss` it carries — but the predicate does not pin it, because every consumer
absorbs it into a fixed negative power of the scale rather than reading its value.

The factor `Cstar` sits on the right of `le_window_maxDensity` rather than as a `Cstar⁻¹` on the
left, which is the same statement, and it is the weaker of the two placements the blueprint
allows; the reduction takes the weaker form because that is the form the Lean statement of GWZ
Lemma 7.7(B) delivers. -/
structure IsKatzTaoDividingWindow {ι : Type*} {δ Cst : ℝ≥0} {s : Finset ι} {T : ι → Tube δ E}
    (𝒰 : UniformTubeSet s T (ssfGridLen δ) Cst) (Cstar : ℝ≥0∞) (η : ℕ → ℝ) (εd : ℝ)
    (N a b m : ℕ) : Prop where
  /-- The step index lies below the number of stopping steps; the blueprint's `j` is `m + 1`. -/
  step_lt : m < N
  /-- `θ = ρ_a` is coarser than `τ = ρ_b`. -/
  coarse_lt_fine : a < b
  /-- Both scales lie on the grid of `δ`. -/
  fine_le_gridLen : b ≤ ssfGridLen δ
  /-- The two scales are `ε_div`-separated: `τ ≤ δ^{ε_div} θ`. -/
  scale_sep : (gridScale δ (ssfGridLen δ) b : ℝ)
    ≤ (δ : ℝ) ^ εd * (gridScale δ (ssfGridLen δ) a : ℝ)
  /-- `Δ_max(𝕋_θ) ≤ C_⋆ θ^{-η_{j-1}}`. -/
  coarse_maxDensity_le :
    Kakeya.maxDensity (𝒰.cover.indexSet a) (fun j => (𝒰.cover.tube a j).toConvexSpaceBody)
      ≤ Cstar * ENNReal.ofReal ((gridScale δ (ssfGridLen δ) a : ℝ) ^ (-η m))
  /-- `Δ_max(𝕋_{τ∣θ}[T_θ]) ≤ C_⋆ (θ/τ)^{η_{j-1}}` at every level-`θ` node. -/
  middle_maxDensity_le : ∀ j ∈ 𝒰.cover.indexSet a,
    Kakeya.maxDensity (𝒰.nodesUnder b a j) (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody)
      ≤ Cstar * ENNReal.ofReal
          (((gridScale δ (ssfGridLen δ) a : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ η m)
  /-- `(θ/ρ)^{η_j} ≤ C_⋆ Δ_max(𝕋_{ρ∣θ}[T_θ])` at every intermediate scale `ρ` of the window and
  every level-`θ` node. -/
  le_window_maxDensity : ∀ ρ : ℝ≥0,
    (gridScale δ (ssfGridLen δ) b : ℝ)
        * ((gridScale δ (ssfGridLen δ) a : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ εd
      ≤ (ρ : ℝ) →
    (ρ : ℝ) ≤ (gridScale δ (ssfGridLen δ) a : ℝ)
        * ((gridScale δ (ssfGridLen δ) b : ℝ) / (gridScale δ (ssfGridLen δ) a : ℝ)) ^ εd →
    ∀ j ∈ 𝒰.cover.indexSet a,
      ENNReal.ofReal (((gridScale δ (ssfGridLen δ) a : ℝ) / (ρ : ℝ)) ^ η (m + 1))
        ≤ Cstar * Kakeya.maxDensity (𝒰.nodesUnder b a j)
            (fun j' => ((𝒰.cover.tube b j').rescale ρ).toConvexSpaceBody)

open scoped Classical in
/-- **The dividing window with the source's own intermediate clause.**  Two fields the tree's proof
of GWZ 7.7(B) already establishes and the existing statement discards: the multiplicity-free
level-cell lower bound (refined `eqdividingKwitness`, ; the third non-sticky window
inequality of `lem:ml2-window-refinement`) and the two-level maximal-density
homogenization band (rendered at the tree's own `Cstar` rather than at the
source's factor `2`).

This is a **twin**, not two extra fields on `Kakeya.ML2Reduction.IsKatzTaoDividingWindow`: every
existing consumer keeps the parent predicate, keeps its text **and** its meaning, and reads this
through `toIsKatzTaoDividingWindow`; and `Kakeya.ML2Core.gridModel_window` -- the sticky grid family
of `Reduction/SpineCountFloorObstruction.lean`, which satisfies the parent and must **not** satisfy
this -- keeps compiling as the permanent record of why the parent cannot carry a count floor. -/
structure IsKatzTaoDividingWindowLevels {ι : Type*} {δ Cst : ℝ≥0} {s : Finset ι}
    {T : ι → Tube δ E} (𝒰 : UniformTubeSet s T (ssfGridLen δ) Cst) (Cstar : ℝ≥0∞)
    (η : ℕ → ℝ) (εd : ℝ) (N a b m : ℕ) : Prop
    extends IsKatzTaoDividingWindow 𝒰 Cstar η εd N a b m where
  /-- `(θ/ρ_c)^{η_j} ≤ C_⋆ Δ_max(𝕋_c[T_θ])` on the **distinct level-`c` cells** -- no rescaling and
  no multiplicity -- at every level `c` of the `ε_div`-inset window and every level-`θ` node.
  Refined . -/
  le_level_maxDensity : ∀ c : ℕ,
    a + ⌈εd * ((b : ℝ) - (a : ℝ))⌉₊ ≤ c → c + ⌈εd * ((b : ℝ) - (a : ℝ))⌉₊ ≤ b →
    ∀ j ∈ 𝒰.cover.indexSet a,
      ENNReal.ofReal (((gridScale δ (ssfGridLen δ) a : ℝ)
          / (gridScale δ (ssfGridLen δ) c : ℝ)) ^ η (m + 1))
        ≤ Cstar * Kakeya.maxDensity (𝒰.nodesUnder c a j)
            (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
  /-- The **two-level maximal densities** are pinned to one profile `Φ` within the factor `Cstar`
  at **every pair of levels** and uniformly in the coarse node — GWZ's
  , *"pairwise within a factor two at every fixed level or pair of levels"*.  The
  window's own coarse level `a` is the specialisation `p := a`; the genuine parent `p` of
  alternative (F) is why the general form is needed (`le_maxDensity_nodesUnder_of_band` at the pair
  `(p, c)`).  The descendant counts, the two-level counts and the fibre shaded masses of that
  sentence are still **not** carried here. -/
  level_density_band : ∃ Φ : ℕ → ℕ → ℝ≥0∞, ∀ p ≤ ssfGridLen δ, ∀ c ≤ ssfGridLen δ,
    ∀ j ∈ 𝒰.cover.indexSet p,
    Φ p c ≤ Kakeya.maxDensity
        ((coverClass s (𝒰.cover.assign p) j).image (𝒰.cover.assign c))
        (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) ∧
      Kakeya.maxDensity
        ((coverClass s (𝒰.cover.assign p) j).image (𝒰.cover.assign c))
        (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) ≤ Cstar * Φ p c

/-! ### (a) The dichotomy at the Main-Lemma-2 parameters -/

/-! ### (c) The `ε₂ ≤ ε₁/5` bookkeeping -/

/-! ### (a) + (c): the dichotomy with alternative (i) already at `δ^{-ε₁}` -/

/-! ### (a) + (c) at externally supplied parameters `(N, e)` -/

/-! ### (b) The every-scale branch: GWZ Theorem 7.3(B) at an absolute accuracy -/

omit [Nontrivial E] in
/-- `δ^x` computed in `ℝ` and pushed into `ENNReal` is `δ^x` computed in `ENNReal`. -/
theorem ofReal_rpow_coe {δ : ℝ≥0} (hδ : 0 < δ) (x : ℝ) :
    ENNReal.ofReal ((δ : ℝ) ^ x) = (δ : ℝ≥0∞) ^ x := by
  rw [← NNReal.coe_rpow, ENNReal.ofReal_coe_nnreal, ENNReal.coe_rpow_of_ne_zero hδ.ne']

/-! ### The hierarchy bridge: transporting the every-scale bound along equal covers -/

/-! ### From `μ ≤ δ^{-ε₀}` to the Main Lemma 2 goal `μ ≤ δ^{-ε} |𝕋|^{β-ν}` -/

/-! ### Feeding the dichotomy from `Kakeya.ML2Spine.IsSpine` -/

/-- **The ladder hypothesis of GWZ Lemma 7.7(B), read off the spine.**

`StickyKakeya.dividingScalesKatzTao` wants `η k ≤ e · η (k+1)` for `k < N`; the spine
carries the sharper separation `Kakeya.ML2Spine.IsSpine.sep_le`,
`12 η_k/(e β) ≤ e η_{k+1}/4`, which gives `η k ≤ e² β η_{k+1}/48` and hence the lemma's form as
soon as `e β ≤ 48` — true with room to spare, since `e ≤ ε₂/5 ≤ 1/10` and `β ≤ 1`. -/
theorem rung_le_div_mul_rung_succ {β ϖ ε₁ ε₂ e : ℝ} {gain dens : ℝ → ℝ} {N : ℕ} {η : ℕ → ℝ}
    (h : Kakeya.ML2Spine.IsSpine β ϖ ε₁ gain dens ε₂ e N η) (hβ : 0 < β) (hβ1 : β ≤ 1)
    {k : ℕ} (hk : k < N) : η k ≤ e * η (k + 1) := by
  have hepos : 0 < e := h.div_pos
  have hη1 : 0 < η (k + 1) := h.rung_pos (k + 1)
  have hd : e ≤ ε₂ / 5 := h.div_le
  have hhalf : ε₂ ≤ 1 / 2 := h.eps₂_le_half
  have he10 : e ≤ 1 / 10 := by linarith
  have hab : e * β ≤ 1 := by nlinarith
  have hsep := h.sep_le k hk
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < e * β)] at hsep
  nlinarith [mul_nonneg (mul_pos hepos hη1).le (by linarith : (0 : ℝ) ≤ 48 - e * β), hsep]

end Kakeya.ML2Reduction

end

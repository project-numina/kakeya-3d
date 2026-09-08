/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Rescaling.Numerics
public import Kakeya.DimensionThree.MainLemma1.Repair
public import Kakeya.DimensionThree.HybridParentPacking
public import Kakeya.DimensionThree.MainLemma1.Rescaling.BallRadius
public import Kakeya.DimensionThree.MainLemma1.Rescaling.CoarseDensity
public import Kakeya.DimensionThree.MainLemma1.OneSidedUniform
public import Kakeya.DimensionThree.MainLemma1.Rescaling.Normalized

/-!
# Main Lemma 1, Case (ii): The coarse bound and the middle factor

Split out of `Kakeya/DimensionThree/MainLemma1/Rescaling.lean`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya

universe u

namespace ml1Boot

/-! ### The coarse bound and the middle factor -/

section KatzTao

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### One-sided uniformity, as Section 6 reads it -/

/-- **The raw Katz–Tao bound at the `b`-tube scale**.

Suppose `K_KT(β)` holds in `ℝ³` and write `β' = β'(γ)`.  Then there is a fullness threshold
`ηs > 0` — the one supplied by `Kakeya.KatzTaoEstimate.multiplicity_bound` at loss exponent
`ε` and exponent `β'` — such that for all sufficiently small `δ̃ > 0`, every
`b ∈ [δ̃, δ̃ ^ (1 - 5 ε)]` and every nonempty shaded family of `b`-tubes in `B₁` with
`λ ≥ δ̃ ^ ((1 - 5 ε) ηs)`,

`μ(𝕋̃_b, Y) ≤ δ̃ ^ (-ε) Δ_max(𝕋̃_b) ^ (1 - β') |𝕋̃_b| ^ β'`.

This is `Kakeya.KatzTaoEstimate.multiplicity_bound` verbatim at the exponent `β'`, with the
loss `b ^ (-ε)` weakened to `δ̃ ^ (-ε)` using `b ≥ δ̃`; separating it from
`Kakeya.ml1Boot.multiplicity_coarse_le` isolates the single use of the Katz–Tao hypothesis
from the bracket bookkeeping that converts its right-hand side into `multTildeTb`.

The family is **not** asked to be pairwise essentially distinct, and nothing replaces the
hypothesis.  `Kakeya.KatzTaoEstimate.multiplicity_bound` carries no such hypothesis: what
excludes degenerate repetition there is the fullness bound, and the conclusion is invariant
under duplicating each index, since `μ`, `Δ_max` and `|𝕋̃_b|` all scale by the multiplicity of
the duplication while `λ` is unchanged and the right-hand side scales by
`m ^ (1 - β') m ^ β' = m`.
See blueprint `note:ml1bootCoarseEDInert`.

The `b`-window is `[δ̃, δ̃ ^ (1 - 5 ε)]` and not `[δ̃, δ̃ ^ (1 - ε)]` because
`Kakeya.ml1Boot.plankWidth_le`, which produces the honest `b`-tube scale, now speaks on the
`5 ε`-window; see blueprint `note:ml1bootWindowConsumers`(3).

`5 ε < 1` is required, not merely `ε ≤ 1`.  The Katz–Tao input is available only below a
threshold at the *tube* scale `b`, and what pushes `b` below it is `b ≤ δ̃ ^ (1 - 5 ε)`
together with `δ̃ → 0`; at `5 ε = 1` the upper end of the range is `δ̃ ^ 0 = 1`, so `b` need
not be small and no choice of `δ̃` makes the input applicable.  The `δ̃ ^ (-ε)` slack does not
repair this, being a factor on the conclusion rather than on the range of `b`.  This costs
nothing: the consumers read `ε` off `Kakeya.ml1Boot.Params`, where
`96 ε ≤ gap β γ₀ ≤ 1/2` forces `ε ≤ 1/192` (`Kakeya.ml1Boot.params_spec`). -/
theorem multiplicity_coarse_raw (hdim : Module.finrank ℝ E = 3)
    {β γ : ℝ} (hβ0 : 0 ≤ β) (hKKT : KatzTaoEstimate.{u} E β)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : 5 * ε < 1) :
    ∃ ηs > (0 : ℝ),
    ∀ᶠ (δt : ℝ≥0) in 𝓝[>] 0, ∀ b : ℝ≥0, δt ≤ b → b ≤ δt ^ (1 - 5 * ε) →
      ∀ {κ : Type u} {t : Finset κ} (Tb : κ → ShadedTube b E),
        t.Nonempty →
        (∀ l ∈ t, (Tb l).carrier ⊆ Metric.closedBall 0 1) →
        (δt : ℝ≥0∞) ^ ((1 - 5 * ε) * ηs)
          ≤ ShadedBody.fullness t (fun l => (Tb l).toShadedBody) →
        ShadedBody.multiplicity t (fun l => (Tb l).toShadedBody)
          ≤ (δt : ℝ≥0∞) ^ (-ε)
            * maxDensity t (fun l => (Tb l).toConvexSpaceBody) ^ (1 - betaPrime β γ)
            * (t.card : ℝ≥0∞) ^ betaPrime β γ := by
  classical
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (by
    rw [hdim]; norm_num : 0 < Module.finrank ℝ E)
  have hKTB : KatzTaoEstimate.{u} E (betaPrime β γ) := by
    refine KatzTaoEstimate.mono ?_ hKKT
    dsimp [betaPrime]
    exact le_max_left β (γ / 2)
  have hβ'0 : 0 ≤ betaPrime β γ := by
    dsimp [betaPrime]
    exact le_trans hβ0 (le_max_left β (γ / 2))
  obtain ⟨η, hη_pos, hP⟩ :=
    KatzTaoEstimate.multiplicity_bound (E := E) (β := betaPrime β γ) hβ'0 hKTB ε hε0
  refine ⟨η, hη_pos, ?_⟩
  · -- Case `5 ε < 1`: the transfer of `K_KT` from small scales to `b ∈ [δ̃, δ̃^(1-5ε)]`.
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff_ball] at hP
    rcases hP with ⟨δ₁, hδ₁_pos, hP_near⟩
    have hδt_rpow_lt : ∀ᶠ (δt : ℝ≥0) in 𝓝[>] (0 : ℝ≥0),
        (δt : ℝ≥0) ^ (1 - 5 * ε) < δ₁ := by
      have h1m : 0 < 1 - 5 * ε := by linarith
      have hcoet : Tendsto (fun δt : ℝ≥0 => (δt : ℝ))
          (𝓝[>] (0 : ℝ≥0)) (𝓝 (0 : ℝ)) := by
        simpa using ((NNReal.continuous_coe.tendsto (0 : ℝ≥0)).mono_left nhdsWithin_le_nhds)
      have htendR : Tendsto (fun δt : ℝ≥0 => (δt : ℝ) ^ (1 - 5 * ε))
          (𝓝[>] (0 : ℝ≥0)) (𝓝 (0 : ℝ)) :=
        hcoet.rpow_const_nhds_zero h1m
      have h_ev : ∀ᶠ (δt : ℝ≥0) in 𝓝[>] (0 : ℝ≥0),
          (δt : ℝ) ^ (1 - 5 * ε) < (δ₁ : ℝ) :=
        htendR.eventually (eventually_lt_nhds (by exact_mod_cast hδ₁_pos))
      filter_upwards [h_ev] with δt hδt
      simpa [NNReal.coe_rpow] using hδt
    have hδt_pos_ev : ∀ᶠ (δt : ℝ≥0) in 𝓝[>] (0 : ℝ≥0), (0 : ℝ≥0) < δt :=
      self_mem_nhdsWithin
    filter_upwards [hδt_rpow_lt, hδt_pos_ev] with δt hδt_rpow hδt_pos
    intro b hδt_le_b hb_le
    have hb0 : 0 < b := lt_of_lt_of_le hδt_pos hδt_le_b
    have hb_lt_δ₁ : b < δ₁ := lt_of_le_of_lt hb_le hδt_rpow
    intro κ t Tb ht_nonempty hballs hfull
    rcases ht_nonempty with ⟨l₀, hl₀⟩
    let T_ext : κ → ShadedTube b E := fun i => if i ∈ t then Tb i else Tb l₀
    have hext_eq : ∀ i ∈ t, T_ext i = Tb i := by
      intro i hi
      simp [T_ext, hi]
    have hball_total : ∀ i, (T_ext i).carrier ⊆ Metric.closedBall 0 1 := by
      intro i
      by_cases hi : i ∈ t
      · rw [hext_eq i hi]
        exact hballs i hi
      · rw [show T_ext i = Tb l₀ by simp [T_ext, hi]]
        exact hballs l₀ hl₀
    have hfull_real : (b : ℝ) ^ η ≤ (ShadedBody.fullness t (fun l => (Tb l).toShadedBody) : ℝ) := by
      have hbridge : (δt : ℝ) ^ ((1 - 5 * ε) * η) ≤
          (ShadedBody.fullness t (fun l => (Tb l).toShadedBody) : ℝ) := by
        have htoReal : ENNReal.toReal ((δt : ℝ≥0∞) ^ ((1 - 5 * ε) * η)) ≤
            ENNReal.toReal (ShadedBody.fullness t (fun l => (Tb l).toShadedBody) : ℝ≥0∞) := by
          have hne' : (ShadedBody.fullness t (fun l => (Tb l).toShadedBody) : ℝ≥0∞) ≠ ⊤ :=
            ENNReal.coe_ne_top
          exact ENNReal.toReal_mono hne' hfull
        simpa [ennreal_coe_nnreal_rpow_toReal hδt_pos ((1 - 5 * ε) * η), ENNReal.coe_toReal]
          using htoReal
      have hmono : (b : ℝ) ^ η ≤ (δt : ℝ) ^ ((1 - 5 * ε) * η) := by
        have hb_le_real : (b : ℝ) ≤ (δt : ℝ) ^ (1 - 5 * ε) := by exact_mod_cast hb_le
        have h1 : (b : ℝ) ^ η ≤ ((δt : ℝ) ^ (1 - 5 * ε)) ^ η :=
          Real.rpow_le_rpow (by positivity : 0 ≤ (b : ℝ)) hb_le_real (le_of_lt hη_pos)
        rwa [← Real.rpow_mul (by positivity : 0 ≤ (δt : ℝ)) (1 - 5 * ε) η] at h1
      exact le_trans hmono hbridge
    have hfull_eqENN : (ShadedBody.fullness t (fun i => (T_ext i).toShadedBody) : ℝ≥0∞) =
        (ShadedBody.fullness t (fun l => (Tb l).toShadedBody) : ℝ≥0∞) := by
      rw [ShadedBody.coe_fullness, ShadedBody.coe_fullness]
      unfold ShadedBody.fullness'
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        simp [hext_eq i hi]
      · apply Finset.sum_congr rfl
        intro i hi
        simp [hext_eq i hi]
    have hfull_eq : ShadedBody.fullness t (fun i => (T_ext i).toShadedBody) =
        ShadedBody.fullness t (fun l => (Tb l).toShadedBody) := by
      exact_mod_cast hfull_eqENN
    have hfull_ext :
        (ShadedBody.fullness t (fun i => (T_ext i).toShadedBody) : ℝ) ≥ (b : ℝ) ^ η := by
      rw [hfull_eq]
      exact hfull_real
    have hb_dist : dist b 0 < δ₁ := by
      simpa [NNReal.dist_eq, abs_of_nonneg (by exact_mod_cast hb0.le : (0 : ℝ) ≤ (b : ℝ))]
        using hb_lt_δ₁
    have hb_ball : b ∈ Metric.ball (0 : ℝ≥0) δ₁ := by
      rw [Metric.mem_ball]
      exact hb_dist
    have hbP := hP_near b hb_ball hb0 (ι := κ)
    have hbP_res : ShadedBody.multiplicity t (fun i => (T_ext i).toShadedBody) ≤
        (b : ℝ≥0∞) ^ (-ε) *
          maxDensity t (fun i => (T_ext i).toConvexSpaceBody) ^ (1 - betaPrime β γ) *
          (t.card : ℝ≥0∞) ^ betaPrime β γ :=
      hbP t T_ext hball_total hfull_ext
    have hmu_eq : ShadedBody.multiplicity t (fun i => (T_ext i).toShadedBody) =
        ShadedBody.multiplicity t (fun l => (Tb l).toShadedBody) := by
      refine multiplicity_eq_of_eqOn (E := E) t ?_
      intro i hi
      rw [hext_eq i hi]
    have hext_convex : ∀ i ∈ t, (T_ext i).toConvexSpaceBody = (Tb i).toConvexSpaceBody := by
      intro i hi
      rw [hext_eq i hi]
    have hΔ_eq : maxDensity t (fun i => (T_ext i).toConvexSpaceBody) =
        maxDensity t (fun l => (Tb l).toConvexSpaceBody) := by
      apply le_antisymm
      · rw [maxDensity_le_iff]
        intro K
        rw [densityIn_eq_of_eqOn (E := E) t hext_convex K]
        exact le_maxDensity t (fun l => (Tb l).toConvexSpaceBody) K
      · rw [maxDensity_le_iff]
        intro K
        rw [← densityIn_eq_of_eqOn (E := E) t hext_convex K]
        exact le_maxDensity t (fun i => (T_ext i).toConvexSpaceBody) K
    have hloss : (b : ℝ≥0∞) ^ (-ε) ≤ (δt : ℝ≥0∞) ^ (-ε) := by
      have hδtle : (δt : ℝ≥0∞) ≤ (b : ℝ≥0∞) := by exact_mod_cast hδt_le_b
      have hεle : (δt : ℝ≥0∞) ^ ε ≤ (b : ℝ≥0∞) ^ ε :=
        ENNReal.rpow_le_rpow hδtle hε0.le
      rw [show (b : ℝ≥0∞) ^ (-ε) = ((b : ℝ≥0∞) ^ ε)⁻¹ from by
            rw [← ENNReal.rpow_neg (b : ℝ≥0∞) ε],
          show (δt : ℝ≥0∞) ^ (-ε) = ((δt : ℝ≥0∞) ^ ε)⁻¹ from by
            rw [← ENNReal.rpow_neg (δt : ℝ≥0∞) ε]]
      exact ENNReal.inv_le_inv.mpr hεle
    calc
      ShadedBody.multiplicity t (fun l => (Tb l).toShadedBody)
          = ShadedBody.multiplicity t (fun i => (T_ext i).toShadedBody) := hmu_eq.symm
      _ ≤ (b : ℝ≥0∞) ^ (-ε) *
            maxDensity t (fun i => (T_ext i).toConvexSpaceBody) ^ (1 - betaPrime β γ) *
            (t.card : ℝ≥0∞) ^ betaPrime β γ := hbP_res
      _ ≤ (δt : ℝ≥0∞) ^ (-ε) *
            maxDensity t (fun l => (Tb l).toConvexSpaceBody) ^ (1 - betaPrime β γ) *
            (t.card : ℝ≥0∞) ^ betaPrime β γ := by
            rw [hΔ_eq]
            gcongr

/-- **The Katz-Tao coarse multiplicity bound at an ambient radius `R ≥ 1`**.

`Kakeya.ml1Boot.multiplicity_coarse_raw` with the unit ball replaced by `closedBall 0 R` for an
arbitrary scale-independent `R ≥ 1`, at the cost of one extra hypothesis `(b : ℝ) ≤ 1 / 4` and of
nothing at all in the conclusion.

This is what the `b`-scale plank tubes of the coarse endgame need, and the reason they need it is
that they do **not** lie in the unit ball and cannot be made to: a `Kakeya.Tube` has core length
exactly `1`, so a tube attached to a plank hugging `∂B₁` pokes out, and
`Kakeya.ml1Boot.plankTube_carrier_subset_closedBall` gives only
`closedBall 0 (3/2 + √3 + C b)`, with `3/2 + √3 > 1` and no slack.  Under the plank-width side
condition `C b ≤ 1` that radius is at most `9 / 2`
(`Kakeya.ml1Boot.plankTube_carrier_subset_closedBall_of_le`), which is the `R` to use here.

The proof is `Kakeya.ml1Boot.multiplicity_le_of_ball_of_unitBall` applied to the radius-`1`
statement at the *same* accuracy `ε`, with the loss given away in the conclusion instead: the
reduction's two losses — the factor `2` of the low-shading discard and the cell count `M` of the
ball assignment — are fixed before the scale, so `Kakeya.ml1Boot.eventually_mul_rpow_le_rpow`
absorbs `2 M δ̃ ^ (-ε)` into `δ̃ ^ (-ε₂)` for any `ε₂ > ε`.

**This is a real charge on the coarse budget, and the ledger of
`Kakeya.ml1Boot.multTildeT_of_planksClose` does not record it.**  The reduction cannot be had at
the same loss exponent: absorbing a constant requires widening an exponent, and the only exponent
free to widen is the loss, the range of `b` being pinned by the caller.  So item (6) of that
ledger — the unit-ball containment of the `b`-tubes — is *repairable but not free*: whoever routes
`Kakeya.ml1Boot.multiplicity_coarse_le_of_const` through this statement has to find the gap
`ε₂ - ε` somewhere in the `-72 ε` budget of its `hnum`, and ultimately in
`Kakeya.ml1Boot.Params.Spec`.  The exponent is left as a parameter precisely so that the consumer
may choose how small a charge to pay.

*Why the loss cannot instead be bought by shrinking `ε`.*  In
`Kakeya.ml1Boot.multiplicity_coarse_raw` the accuracy and the admissible range of `b` are tied to
the same `ε`: the loss is `δ̃ ^ (-ε)` and the range is `b ≤ δ̃ ^ (1 - 5 ε)`.  Running it at `ε / 2`
would halve the loss but also shrink the range to `b ≤ δ̃ ^ (1 - 5 ε / 2) ≤ δ̃ ^ (1 - 5 ε)`, which
the caller's hypothesis does not supply.  Widening the conclusion is the exit that costs the
caller nothing, every consumer reading `ε` off `Kakeya.ml1Boot.Params` where it is free to halve.
The
fullness threshold is handed out at `ηs / 2` rather than `ηs` for the same reason: the discard
delivers a subfamily fullness of only half the family's, and halving is absorbed by moving the
exponent. -/
theorem multiplicity_coarse_raw_ball (hdim : Module.finrank ℝ E = 3)
    {β γ : ℝ} (hβ0 : 0 ≤ β) (hβ'1 : betaPrime β γ ≤ 1) (hKKT : KatzTaoEstimate.{u} E β)
    {ε ε₂ : ℝ} (hε0 : 0 < ε) (hε1 : 5 * ε < 1) (hεε₂ : ε < ε₂) (R : ℝ) (hR : 1 ≤ R) :
    ∃ ηs > (0 : ℝ),
    ∀ᶠ (δt : ℝ≥0) in 𝓝[>] 0, ∀ b : ℝ≥0, 0 < b → δt ≤ b → b ≤ δt ^ (1 - 5 * ε) →
      (b : ℝ) ≤ 1 / 4 →
      ∀ {κ : Type u} (t : Finset κ) (Tb : κ → ShadedTube b E),
        t.Nonempty →
        (∀ l ∈ t, (Tb l).carrier ⊆ Metric.closedBall 0 R) →
        (δt : ℝ≥0∞) ^ ((1 - 5 * ε) * ηs)
          ≤ ShadedBody.fullness t (fun l => (Tb l).toShadedBody) →
        ShadedBody.multiplicity t (fun l => (Tb l).toShadedBody)
          ≤ (δt : ℝ≥0∞) ^ (-ε₂)
            * maxDensity t (fun l => (Tb l).toConvexSpaceBody) ^ (1 - betaPrime β γ)
            * (t.card : ℝ≥0∞) ^ betaPrime β γ := by
  classical
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (by
    rw [hdim]; norm_num : 0 < Module.finrank ℝ E)
  obtain ⟨M, hM0, hred⟩ := multiplicity_le_of_ball_of_unitBall (E := E) R hR
  obtain ⟨ηs', hηs'0, hraw⟩ :=
    multiplicity_coarse_raw (E := E) (γ := γ) hdim hβ0 hKKT (ε := ε) hε0 hε1
  have h15 : (0 : ℝ) < 1 - 5 * ε := by linarith
  have hβ'0 : 0 ≤ betaPrime β γ := le_trans hβ0 (le_max_left β (γ / 2))
  refine ⟨ηs' / 2, by positivity, ?_⟩
  filter_upwards [hraw,
    eventually_mul_rpow_le_rpow (K := (2 : ℝ≥0∞) * (M : ℝ≥0∞))
      (ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top M))
      (p := -ε) (q := -ε₂) (by linarith),
    eventually_mul_rpow_le_rpow (K := (2 : ℝ≥0∞)) (by simp)
      (p := (1 - 5 * ε) * ηs') (q := (1 - 5 * ε) * (ηs' / 2)) (by nlinarith)]
    with δt hrawδ habs hslack
  intro b hb0 hδtb hbub hb4 κ t Tb ht hball hfull
  set lam : ℝ≥0 := δt ^ ((1 - 5 * ε) * (ηs' / 2)) with hlam
  have hexp : (0 : ℝ) ≤ (1 - 5 * ε) * (ηs' / 2) := by positivity
  have hlamcoe : (lam : ℝ≥0∞) = (δt : ℝ≥0∞) ^ ((1 - 5 * ε) * (ηs' / 2)) := by
    rw [hlam, ENNReal.coe_rpow_of_nonneg _ hexp]
  have hexp1 : (0 : ℝ) ≤ 1 - betaPrime β γ := by linarith
  set Bound : ℝ≥0∞ := (δt : ℝ≥0∞) ^ (-ε)
      * maxDensity t (fun l => (Tb l).toConvexSpaceBody) ^ (1 - betaPrime β γ)
      * (t.card : ℝ≥0∞) ^ betaPrime β γ with hBound
  -- The radius-`1` statement, read on a translated subfamily.
  have hunit : ∀ (t' : Finset κ) (v : E), t' ⊆ t → t'.Nonempty →
      (∀ l ∈ t', ((Tb l).translate v).carrier ⊆ Metric.closedBall 0 1) →
      ((lam / 2 : ℝ≥0) : ℝ≥0∞)
        ≤ (ShadedBody.fullness t' (fun l => ((Tb l).translate v).toShadedBody) : ℝ≥0∞) →
      ShadedBody.multiplicity t' (fun l => ((Tb l).translate v).toShadedBody) ≤ Bound := by
    intro t' v hsub hne hballu hfullu
    have hcast : ((lam / 2 : ℝ≥0) : ℝ≥0∞) = (lam : ℝ≥0∞) / 2 := by
      rw [ENNReal.coe_div (by norm_num)]
      norm_num
    have hfull' : (δt : ℝ≥0∞) ^ ((1 - 5 * ε) * ηs')
        ≤ ShadedBody.fullness t' (fun l => ((Tb l).translate v).toShadedBody) := by
      refine le_trans ?_ hfullu
      rw [hcast, ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))]
      calc (δt : ℝ≥0∞) ^ ((1 - 5 * ε) * ηs') * 2
          = 2 * (δt : ℝ≥0∞) ^ ((1 - 5 * ε) * ηs') := by ring
        _ ≤ (δt : ℝ≥0∞) ^ ((1 - 5 * ε) * (ηs' / 2)) := hslack
        _ = (lam : ℝ≥0∞) := hlamcoe.symm
    have hkey := hrawδ b hδtb hbub (t := t') (fun l => (Tb l).translate v) hne hballu hfull'
    have hmd : maxDensity t' (fun l => ((Tb l).translate v).toConvexSpaceBody)
        = maxDensity t' (fun l => (Tb l).toConvexSpaceBody) := by
      have hpt : ∀ l, ((Tb l).translate v).toConvexSpaceBody
          = (((Tb l).toTube).translate v).toConvexSpaceBody := by
        intro l
        rw [StickyKakeya.shadedTube_translate_toTube]
      simp only [hpt]
      exact StickyKakeya.maxDensity_tube_translate t' (fun l => (Tb l).toTube) v
    rw [hmd] at hkey
    have hmdle : maxDensity t' (fun l => (Tb l).toConvexSpaceBody)
        ≤ maxDensity t (fun l => (Tb l).toConvexSpaceBody) :=
      maxDensity_mono (fun l => (Tb l).toConvexSpaceBody) hsub
    have hcard : (t'.card : ℝ≥0∞) ≤ (t.card : ℝ≥0∞) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    refine hkey.trans ?_
    rw [hBound]
    gcongr
  -- The reduction, then the absorption of its two losses.
  have hfullLam : (lam : ℝ≥0∞)
      ≤ (ShadedBody.fullness t (fun l => (Tb l).toShadedBody) : ℝ≥0∞) := by
    rw [hlamcoe]; exact hfull
  refine (hred hb0 hb4 t Tb hball hfullLam hunit).trans ?_
  rw [hBound]
  calc 2 * (M : ℝ≥0∞) * ((δt : ℝ≥0∞) ^ (-ε)
        * maxDensity t (fun l => (Tb l).toConvexSpaceBody) ^ (1 - betaPrime β γ)
        * (t.card : ℝ≥0∞) ^ betaPrime β γ)
      = (2 * (M : ℝ≥0∞) * (δt : ℝ≥0∞) ^ (-ε))
        * (maxDensity t (fun l => (Tb l).toConvexSpaceBody) ^ (1 - betaPrime β γ)
          * (t.card : ℝ≥0∞) ^ betaPrime β γ) := by ring
    _ ≤ (δt : ℝ≥0∞) ^ (-ε₂)
        * (maxDensity t (fun l => (Tb l).toConvexSpaceBody) ^ (1 - betaPrime β γ)
          * (t.card : ℝ≥0∞) ^ betaPrime β γ) := by gcongr
    _ = (δt : ℝ≥0∞) ^ (-ε₂)
        * maxDensity t (fun l => (Tb l).toConvexSpaceBody) ^ (1 - betaPrime β γ)
        * (t.card : ℝ≥0∞) ^ betaPrime β γ := by ring

/-- **`1 ≤ C_Δ`.**

`Kakeya.ml1Boot.coarsePlank.C` is `C_{dilateTestBody} · 2 · C_{plankInTube} · C_{cardBound}`
and each factor is at least `1`.  Extracted from the body of
`Kakeya.ml1Boot.multiplicity_coarse_le`, which now takes its constant as a parameter and
needs this only to instantiate it. -/
theorem coarsePlank.one_le_C : (1 : ℝ≥0) ≤ coarsePlank.C := by
  have one_le_volC : ∀ n : ℕ, (1 : ℝ≥0) ≤ Metric.volume_comparison.C n := by
    intro n
    have hCval : Metric.volume_comparison.C n = ((4 : ℝ) ^ n * (Nat.factorial n : ℝ) : ℝ) := by
      dsimp [Metric.volume_comparison.C, Metric.lt_volume_convexHull.c]
      push_cast
      field_simp
    have h4 : (1 : ℝ) ≤ (4 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have hfac : (1 : ℝ) ≤ (Nat.factorial n : ℝ) :=
      mod_cast Nat.succ_le_of_lt (Nat.factorial_pos n)
    have : (1 : ℝ) ≤ (Metric.volume_comparison.C n : ℝ) := by
      rw [hCval]
      nlinarith
    exact_mod_cast this
  have hdilate : (1 : ℝ≥0) ≤ dilateTestBody.C := by
    dsimp [dilateTestBody.C]
    exact one_le_mul (by norm_num : (1 : ℝ≥0) ≤ 3 ^ 3) (one_le_volC 3)
  have hplink : (1 : ℝ≥0) ≤ plankInTube.C := by
    dsimp [plankInTube.C]
    have hCw : (1 : ℝ≥0) ≤ plankPigeonhole.C := by
      dsimp [plankPigeonhole.C]
      exact one_le_mul (by norm_num : (1 : ℝ≥0) ≤ 16) (one_le_volC 3)
    exact one_le_mul (one_le_mul (by norm_num : (1 : ℝ≥0) ≤ 256) (one_le_pow₀ hCw))
      (one_le_volC 3)
  dsimp [coarsePlank.C]
  exact one_le_mul (one_le_mul (one_le_mul hdilate (by norm_num : (1 : ℝ≥0) ≤ 2)) hplink)
    cardBound.one_le_C

/-- **(GWZ Lemma 8.1) The Katz–Tao bound for the `b`-tubes, at an ambient radius `R ≥ 1`.**

`Kakeya.ml1Boot.multiplicity_coarse_le_of_const` with `Metric.closedBall 0 1` replaced by
`Metric.closedBall 0 R` in the containment hypothesis and by
`ConvexSpaceBody.closedBall 0 R` in the ambient body of hypothesis (c).  The conclusion is
 to the unit-ball form: no exponent moves.

Two hypotheses are added and one is widened:

* `(b : ℝ) ≤ 1 / 4`, the plank-width side condition of
  `Kakeya.ml1Boot.multiplicity_coarse_raw_ball` — bought from the eventually filter on the
  Section 8 route by `Kakeya.ml1Boot.eventually_mul_two_rpow_le`, and identical to the `hbq1`
  the `b`-tube producers already ask for;
* the loss exponent `ε₂` with `ε < ε₂ ≤ 2 ε`, which is what
  `Kakeya.ml1Boot.multiplicity_coarse_raw_ball` charges for the ball reduction.

**The `ε₂` charge is already funded and costs `Kakeya.ml1Boot.Params.Spec` nothing.**  The
budget hypothesis `hnum` is unchanged at `-72 ε`, and
`Kakeya.ml1Boot.exponent_budget_loss` shows `71 ε` is all that is needed; `ε₂ = 3 ε / 2` is
therefore admissible with `ε / 2` still to spare.  This contradicts the warning carried by
`Kakeya.ml1Boot.multiplicity_coarse_raw_ball`'s own docstring, that the caller "has to find the
gap `ε₂ - ε` … ultimately in `Kakeya.ml1Boot.Params.Spec`": the gap is inside `hnum` already.

The ambient radius enters the proof in exactly two places, and both are volume bookkeeping:
`Kakeya.ml1Boot.multiplicity_coarse_raw_ball` (already on the tree, previously with no
consumer) and `Kakeya.ml1Boot.bracket_mem_Icc_ball`, whose only change is the constant
`c₃ = max 3 r ↦ max (3 R³) r`.  That constant is absorbed by the `∀ᶠ` filter through
`cI * δ̃ ^ (g/2) ≤ 1`, so it is free. -/
theorem multiplicity_coarse_le_of_const_ball (hdim : Module.finrank ℝ E = 3)
    {β γ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hKKT : KatzTaoEstimate.{u} E β)
    {ε ε₂ ap' : ℝ} (hε0 : 0 < ε) (hε1 : 5 * ε < 1) (hap' : 0 < ap')
    (hεε₂ : ε < ε₂) (hε₂2 : ε₂ ≤ 2 * ε)
    (hnum : γ - betaPrime β γ
      ≤ -72 * ε - 2 * ap' + 2 * (γ - betaPrime β γ))
    (hnum' : 10 * ap' ≤ (γ - betaPrime β γ) / 2)
    {CDelta : ℝ≥0} (hCDelta : 1 ≤ CDelta) (R : ℝ≥0) (hR : 1 ≤ R) :
    ∃ ηs > (0 : ℝ),
    ∀ᶠ (δt : ℝ≥0) in 𝓝[>] 0, ∀ b : ℝ≥0, δt ≤ b → b ≤ δt ^ (1 - 5 * ε) →
      (b : ℝ) ≤ 1 / 4 →
      ∀ {κ : Type u} (t : Finset κ) (Tb : κ → ShadedTube b E),
        t.Nonempty →
        (∀ l ∈ t, (Tb l).carrier ⊆ Metric.closedBall 0 (R : ℝ)) →
        (δt : ℝ≥0∞) ^ ((1 - 5 * ε) * ηs)
          ≤ ShadedBody.fullness t (fun l => (Tb l).toShadedBody) →
        maxDensity t (fun l => (Tb l).toConvexSpaceBody)
          ≤ (CDelta : ℝ≥0∞) * (δt : ℝ≥0∞) ^ (-30 * ε - ap') →
        frostmanConstIn t (fun l => (Tb l).toConvexSpaceBody)
            (ConvexSpaceBody.closedBall (0 : E) (R : ℝ) R.coe_nonneg)
          ≤ (CDelta : ℝ≥0∞) * (δt : ℝ≥0∞) ^ (-ap') →
        ShadedBody.multiplicity t (fun l => (Tb l).toShadedBody)
          ≤ (δt : ℝ≥0∞) ^ (10 * ap') * (b : ℝ≥0∞) ^ (-2 * γ)
            * ((t.card : ℝ≥0∞) * (b : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
  classical
  have hεlt1 : ε < 1 := by linarith
  have hg2lt : γ / 2 < 1 := by nlinarith [hγ1]
  have hβ'1 : betaPrime β γ ≤ 1 := by
    dsimp [betaPrime]
    exact max_le hβ1.le hg2lt.le
  obtain ⟨ηs, hηs, hraw⟩ :=
    multiplicity_coarse_raw_ball (E := E) (γ := γ) hdim hβ0 hβ'1 hKKT hε0 hε1 hεε₂
      (R : ℝ) (by exact_mod_cast hR)
  obtain ⟨c₃, hc₃, hbr0⟩ := bracket_mem_Icc_ball (E := E) hdim R hR
  let β' : ℝ := betaPrime β γ
  let g : ℝ := γ - β'
  let h : ℝ := 30 * ε + ap'
  let cNN : ℝ≥0 := c₃ * CDelta
  let ce : ℝ≥0∞ := (c₃ : ℝ≥0∞) * (CDelta : ℝ≥0∞)
  let cI : ℝ≥0∞ := (CDelta : ℝ≥0∞) * ce
  have hβ'0 : 0 < β' := by
    dsimp [β', betaPrime]
    exact lt_of_lt_of_le (div_pos hγ0 (by norm_num)) (le_max_right β (γ / 2))
  have he0 : -1 ≤ γ / 2 + β' - 1 := by nlinarith [hγ0, hβ'0]
  have he1 : γ / 2 + β' - 1 ≤ 1 := by nlinarith [hg2lt, hβ'1]
  have hgap0 : 0 < γ - β' := by
    have h10 : 0 < 10 * ap' := by positivity
    have hle : 10 * ap' ≤ (γ - β') / 2 := by simpa [β'] using hnum'
    have hpos : 0 < (γ - β') / 2 := lt_of_lt_of_le h10 hle
    nlinarith
  have hgap1 : γ - β' ≤ 1 := by nlinarith [hγ1, hβ'0]
  have hg : 0 < g := by simpa [g] using hgap0
  have hh : 0 ≤ h := by dsimp [h]; positivity
  have h1m : 0 < 1 - 5 * ε := by linarith
  have hCp : (1 : ℝ≥0) ≤ CDelta := hCDelta
  have hcNN1 : (1 : ℝ≥0) ≤ cNN := one_le_mul hc₃ hCp
  have hce_ne0 : ce ≠ 0 := by
    dsimp [ce]
    exact mul_ne_zero (ENNReal.coe_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one hc₃)))
      (ENNReal.coe_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one hCp)))
  have hce_ne_top : ce ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
  have hcI_ne_top : cI ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top hce_ne_top
  have hcI_ne0 : cI ≠ 0 := by
    dsimp [cI]
    exact mul_ne_zero (ENNReal.coe_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one hCp)))
      hce_ne0
  have hcI_inv_pos : 0 < cI ⁻¹ := by rw [ENNReal.inv_pos]; exact hcI_ne_top
  have hsmall0 : ∀ᶠ (δt : ℝ≥0) in 𝓝[>] (0 : ℝ≥0), (δt : ℝ≥0∞) ^ (g / 2) ≤ cI ⁻¹ :=
    ENNReal.eventually_coe_rpow_le_of_pos (div_pos hg (by norm_num)) hcI_inv_pos
  have hsmall : ∀ᶠ (δt : ℝ≥0) in 𝓝[>] (0 : ℝ≥0), cI * (δt : ℝ≥0∞) ^ (g / 2) ≤ 1 := by
    filter_upwards [hsmall0] with δt hδ
    calc
      cI * (δt : ℝ≥0∞) ^ (g / 2) ≤ cI * cI⁻¹ := mul_le_mul_of_nonneg_left hδ (by positivity)
      _ = 1 := ENNReal.mul_inv_cancel hcI_ne0 hcI_ne_top
  refine ⟨ηs, hηs, ?_⟩
  filter_upwards [hraw, self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ≥0) < (1 : ℝ≥0))), hsmall]
    with δt hrawδ (hδ0 : 0 < δt) (hδ1 : δt < 1) hcIsmall
  intro b hδt_le_b hb_le hb4
  have hδt1 : δt ≤ 1 := hδ1.le
  have hδtE : (δt : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ0.ne'
  have hδtEt : (δt : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hδt1E : (δt : ℝ≥0∞) ≤ 1 := by exact_mod_cast hδt1
  have hb0 : 0 < b := lt_of_lt_of_le hδ0 hδt_le_b
  have hdtpow : (1 : ℝ≥0∞) ≤ (δt : ℝ≥0∞) ^ (-h) := by
    calc (1 : ℝ≥0∞) = (δt : ℝ≥0∞) ^ (0 : ℝ) := by simp
      _ ≤ (δt : ℝ≥0∞) ^ (-h) := ENNReal.rpow_le_rpow_of_exponent_ge hδt1E (by linarith : -h ≤ 0)
  have hb1 : b ≤ 1 := by
    have hδ1mNN : (δt : ℝ≥0) ^ (1 - 5 * ε) ≤ 1 := by
      calc
        (δt : ℝ≥0) ^ (1 - 5 * ε) ≤ (1 : ℝ≥0) ^ (1 - 5 * ε) :=
          NNReal.rpow_le_rpow hδt1 h1m.le
        _ = 1 := by simp
    exact le_trans hb_le hδ1mNN
  intro κ t Tb ht_nonempty hball hfull hmaxdens hfrost
  let Tbm : κ → Tube b E := fun l => (Tb l).toTube
  have hconn : ∀ l, (Tbm l).toConvexSpaceBody = (Tb l).toConvexSpaceBody := fun l => rfl
  have hdens_eq : maxDensity t (fun l => (Tbm l).toConvexSpaceBody) =
      maxDensity t (fun l => (Tb l).toConvexSpaceBody) := by
    apply congr_arg (fun f : κ → ConvexSpaceBody E => maxDensity t f)
    funext l
    exact hconn l
  have hfrost_eq : frostmanConstIn t (fun l => (Tbm l).toConvexSpaceBody)
        (ConvexSpaceBody.closedBall (0 : E) (R : ℝ) R.coe_nonneg) =
      frostmanConstIn t (fun l => (Tb l).toConvexSpaceBody)
        (ConvexSpaceBody.closedBall (0 : E) (R : ℝ) R.coe_nonneg) := by
    apply congr_arg (fun f : κ → ConvexSpaceBody E =>
      frostmanConstIn t f (ConvexSpaceBody.closedBall (0 : E) (R : ℝ) R.coe_nonneg))
    funext l
    exact hconn l
  have hball_m : ∀ l ∈ t, (Tbm l).carrier ⊆ Metric.closedBall 0 (R : ℝ) := by
    intro l hl
    simpa [Tbm] using hball l hl
  let CFb : ℝ≥0∞ := (CDelta : ℝ≥0∞) * (δt : ℝ≥0∞) ^ (-h)
  have hCFb : (1 : ℝ≥0∞) ≤ CFb :=
    one_le_mul (by exact_mod_cast hCp) hdtpow
  have hmaxdens_m : maxDensity t (fun l => (Tbm l).toConvexSpaceBody)
      ≤ (CDelta : ℝ≥0∞) * (δt : ℝ≥0∞) ^ (-h) := by
    rw [hdens_eq]
    calc
      maxDensity t (fun l => (Tb l).toConvexSpaceBody)
          ≤ (CDelta : ℝ≥0∞) * (δt : ℝ≥0∞) ^ (-30 * ε - ap') := by simpa using hmaxdens
      _ = (CDelta : ℝ≥0∞) * (δt : ℝ≥0∞) ^ (-h) := by
            congr 2
            dsimp [h]
            ring
  have hfrost_m : frostmanConstIn t (fun l => (Tbm l).toConvexSpaceBody)
        (ConvexSpaceBody.closedBall (0 : E) (R : ℝ) R.coe_nonneg) ≤ CFb := by
    rw [hfrost_eq]
    dsimp [CFb]
    calc
      frostmanConstIn t (fun l => (Tb l).toConvexSpaceBody)
            (ConvexSpaceBody.closedBall (0 : E) (R : ℝ) R.coe_nonneg)
          ≤ (CDelta : ℝ≥0∞) * (δt : ℝ≥0∞) ^ (-ap') := by simpa using hfrost
      _ ≤ (CDelta : ℝ≥0∞) * (δt : ℝ≥0∞) ^ (-h) := by
            have hpow : (δt : ℝ≥0∞) ^ (-ap') ≤ (δt : ℝ≥0∞) ^ (-h) :=
              ENNReal.rpow_le_rpow_of_exponent_ge hδt1E (by dsimp [h]; linarith [hε0] : -h ≤ -ap')
            exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hbr := hbr0 hδ0 hδt_le_b hb1 (CFb := CFb) hCFb (CΔ := CDelta) hCp (h := h) hh
      (κ := κ) (t := t) (Tb := Tbm) ht_nonempty hball_m hfrost_m hmaxdens_m
  let Q : ℝ≥0∞ := (b : ℝ≥0∞) ^ (2 : ℕ) * (t.card : ℝ≥0∞)
  have hcard0 : 0 < t.card := (Finset.card_pos).mpr ht_nonempty
  have hcardE0 : (t.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast (ne_of_gt hcard0)
  have hcardEtop : (t.card : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hcI_form : (c₃ : ℝ≥0∞) * CFb = ce * (δt : ℝ≥0∞) ^ (-h) := by
    dsimp [CFb, ce]
    ac_rfl
  have hbr1 : ((c₃ : ℝ≥0∞) * CFb)⁻¹ ≤ (t.card : ℝ≥0∞) * (b : ℝ≥0∞) ^ (2 : ℕ) := hbr.1
  have hbr2 : (t.card : ℝ≥0∞) * (b : ℝ≥0∞) ^ (2 : ℕ)
      ≤ (c₃ : ℝ≥0∞) * (CDelta : ℝ≥0∞) * (δt : ℝ≥0∞) ^ (-h) := hbr.2
  have hidt : (δt : ℝ≥0∞) ^ h = ((δt : ℝ≥0∞) ^ (-h))⁻¹ := by
    rw [← ENNReal.rpow_neg (x := (δt : ℝ≥0∞)) (-h)]
    congr 1
    ring
  have hlb : (ce)⁻¹ * (δt : ℝ≥0∞) ^ h ≤ (b : ℝ≥0∞) ^ (2 : ℕ) * (t.card : ℝ≥0∞) := by
    calc
      (ce)⁻¹ * (δt : ℝ≥0∞) ^ h = (ce)⁻¹ * ((δt : ℝ≥0∞) ^ (-h))⁻¹ := by rw [hidt]
      _ = (ce * (δt : ℝ≥0∞) ^ (-h))⁻¹ := by
            rw [← ENNReal.mul_inv (Or.inl hce_ne0) (Or.inl hce_ne_top)]
      _ ≤ (b : ℝ≥0∞) ^ (2 : ℕ) * (t.card : ℝ≥0∞) := by
            rw [← hcI_form]
            simpa [mul_comm] using hbr1
  have hub : (b : ℝ≥0∞) ^ (2 : ℕ) * (t.card : ℝ≥0∞)
      ≤ ce * (δt : ℝ≥0∞) ^ (-h) := by
    calc
      (b : ℝ≥0∞) ^ (2 : ℕ) * (t.card : ℝ≥0∞)
          = (t.card : ℝ≥0∞) * (b : ℝ≥0∞) ^ (2 : ℕ) := by rw [mul_comm]
      _ ≤ (c₃ : ℝ≥0∞) * (CDelta : ℝ≥0∞) * (δt : ℝ≥0∞) ^ (-h) := hbr2
      _ = ce * (δt : ℝ≥0∞) ^ (-h) := by rfl
  have hcardβ : (t.card : ℝ≥0∞) ^ β'
      ≤ ce * (δt : ℝ≥0∞) ^ (-h) * (b : ℝ≥0∞) ^ (-2 * β') * Q ^ (1 - γ / 2) := by
    have hlbr := card_rpow_le_bracket (b := b) (δt := δt) hb0 hδt1
      (β' := β') (γ := γ) he0 he1
      (P := (t.card : ℝ≥0∞)) hcardE0 hcardEtop (C := cNN) hcNN1 (h := h) hh hlb hub
    simpa [cNN, ce, Q, ENNReal.coe_mul] using hlbr
  have hbudget : (δt : ℝ≥0∞) ^ (-ε₂ - 2 * (30 * ε + ap')) * (b : ℝ≥0∞) ^ (-2 * β')
      ≤ (δt : ℝ≥0∞) ^ (γ - β') * (b : ℝ≥0∞) ^ (-2 * γ) :=
    exponent_budget_loss (ε := ε) (ε₂ := ε₂) (β' := betaPrime β γ) (γ := γ) (ap' := ap')
      hε0 hεlt1.le hap'.le hε₂2 hgap0 hgap1 hnum hδ0 hδt1 hδt_le_b hb_le
  let M : ℝ≥0∞ := maxDensity t (fun l => (Tb l).toConvexSpaceBody)
  have h1 : ShadedBody.multiplicity t (fun l => (Tb l).toShadedBody)
      ≤ (δt : ℝ≥0∞) ^ (-ε₂) * M ^ (1 - β') * (t.card : ℝ≥0∞) ^ β' := by
    simpa [M, β'] using hrawδ b hb0 hδt_le_b hb_le hb4 t Tb ht_nonempty hball hfull
  have hconvpow : M ^ (1 - β') ≤ (CDelta : ℝ≥0∞) * (δt : ℝ≥0∞) ^ (-h) := by
    calc
      M ^ (1 - β') ≤ ((CDelta : ℝ≥0∞) * (δt : ℝ≥0∞) ^ (-h)) ^ (1 - β') :=
        ENNReal.rpow_le_rpow (by simpa [M] using (hdens_eq ▸ hmaxdens_m)) (by linarith)
      _ ≤ ((CDelta : ℝ≥0∞) * (δt : ℝ≥0∞) ^ (-h)) ^ (1 : ℝ) :=
        ENNReal.rpow_le_rpow_of_exponent_le (one_le_mul (by exact_mod_cast hCp) hdtpow)
          (by linarith)
      _ = (CDelta : ℝ≥0∞) * (δt : ℝ≥0∞) ^ (-h) := by simp
  have hpows : (δt : ℝ≥0∞) ^ (-ε₂) * (δt : ℝ≥0∞) ^ (-h) * (δt : ℝ≥0∞) ^ (-h)
      = (δt : ℝ≥0∞) ^ (-ε₂ - 2 * h) := by
    rw [← ENNReal.rpow_add (x := (δt : ℝ≥0∞)) (-ε₂) (-h) hδtE hδtEt]
    rw [← ENNReal.rpow_add (x := (δt : ℝ≥0∞)) (-ε₂ + -h) (-h) hδtE hδtEt]
    congr 1
    ring
  have hμ0 : ShadedBody.multiplicity t (fun l => (Tb l).toShadedBody)
      ≤ (δt : ℝ≥0∞) ^ (-ε₂) * ((CDelta : ℝ≥0∞) * (δt : ℝ≥0∞) ^ (-h))
          * (ce * (δt : ℝ≥0∞) ^ (-h) * (b : ℝ≥0∞) ^ (-2 * β') * Q ^ (1 - γ / 2)) := by
    let B : ℝ≥0∞ := ce * (δt : ℝ≥0∞) ^ (-h) * (b : ℝ≥0∞) ^ (-2 * β') * Q ^ (1 - γ / 2)
    have hA : (δt : ℝ≥0∞) ^ (-ε₂) * M ^ (1 - β') * (t.card : ℝ≥0∞) ^ β'
        ≤ (δt : ℝ≥0∞) ^ (-ε₂) * M ^ (1 - β') * B :=
      mul_le_mul_of_nonneg_left (a := (δt : ℝ≥0∞) ^ (-ε₂) * M ^ (1 - β')) hcardβ bot_le
    have hB : (δt : ℝ≥0∞) ^ (-ε₂) * M ^ (1 - β') * B
        ≤ (δt : ℝ≥0∞) ^ (-ε₂) * ((CDelta : ℝ≥0∞) * (δt : ℝ≥0∞) ^ (-h)) * B := by
      have hM : (δt : ℝ≥0∞) ^ (-ε₂) * M ^ (1 - β')
          ≤ (δt : ℝ≥0∞) ^ (-ε₂) * ((CDelta : ℝ≥0∞) * (δt : ℝ≥0∞) ^ (-h)) :=
        mul_le_mul_of_nonneg_left (a := (δt : ℝ≥0∞) ^ (-ε₂)) hconvpow bot_le
      exact mul_le_mul_of_nonneg_right (a := B) hM bot_le
    calc
      ShadedBody.multiplicity t (fun l => (Tb l).toShadedBody)
          ≤ (δt : ℝ≥0∞) ^ (-ε₂) * M ^ (1 - β') * (t.card : ℝ≥0∞) ^ β' := h1
      _ ≤ (δt : ℝ≥0∞) ^ (-ε₂) * M ^ (1 - β') * B := hA
      _ ≤ (δt : ℝ≥0∞) ^ (-ε₂) * ((CDelta : ℝ≥0∞) * (δt : ℝ≥0∞) ^ (-h)) * B := hB
  have hμ1 : ShadedBody.multiplicity t (fun l => (Tb l).toShadedBody)
      ≤ cI * (δt : ℝ≥0∞) ^ (-ε₂ - 2 * h) * (b : ℝ≥0∞) ^ (-2 * β') * Q ^ (1 - γ / 2) := by
    calc
      ShadedBody.multiplicity t (fun l => (Tb l).toShadedBody)
          ≤ (δt : ℝ≥0∞) ^ (-ε₂) * ((CDelta : ℝ≥0∞) * (δt : ℝ≥0∞) ^ (-h))
              * (ce * (δt : ℝ≥0∞) ^ (-h) * (b : ℝ≥0∞) ^ (-2 * β') * Q ^ (1 - γ / 2)) := hμ0
      _ = cI * (δt : ℝ≥0∞) ^ (-ε₂ - 2 * h) * (b : ℝ≥0∞) ^ (-2 * β') * Q ^ (1 - γ / 2) := by
            dsimp [cI]
            rw [← hpows]
            ac_rfl
  have hμ2 : ShadedBody.multiplicity t (fun l => (Tb l).toShadedBody)
      ≤ cI * (δt : ℝ≥0∞) ^ (γ - β') * (b : ℝ≥0∞) ^ (-2 * γ) * Q ^ (1 - γ / 2) := by
    have hbdex : (δt : ℝ≥0∞) ^ (-ε₂ - 2 * h) * (b : ℝ≥0∞) ^ (-2 * β')
        ≤ (δt : ℝ≥0∞) ^ (γ - β') * (b : ℝ≥0∞) ^ (-2 * γ) := by
      simpa [h] using hbudget
    calc
      ShadedBody.multiplicity t (fun l => (Tb l).toShadedBody)
          ≤ cI * (δt : ℝ≥0∞) ^ (-ε₂ - 2 * h) * (b : ℝ≥0∞) ^ (-2 * β') * Q ^ (1 - γ / 2) := hμ1
      _ = cI * Q ^ (1 - γ / 2) * ((δt : ℝ≥0∞) ^ (-ε₂ - 2 * h) * (b : ℝ≥0∞) ^ (-2 * β')) := by
            ac_rfl
      _ ≤ cI * Q ^ (1 - γ / 2) * ((δt : ℝ≥0∞) ^ (γ - β') * (b : ℝ≥0∞) ^ (-2 * γ)) :=
            mul_le_mul_of_nonneg_left (a := cI * Q ^ (1 - γ / 2)) hbdex bot_le
      _ = cI * (δt : ℝ≥0∞) ^ (γ - β') * (b : ℝ≥0∞) ^ (-2 * γ) * Q ^ (1 - γ / 2) := by
            ac_rfl
  have hg_half : (δt : ℝ≥0∞) ^ g = (δt : ℝ≥0∞) ^ (g / 2) * (δt : ℝ≥0∞) ^ (g / 2) := by
    rw [← ENNReal.rpow_add (x := (δt : ℝ≥0∞)) (g / 2) (g / 2) hδtE hδtEt]
    congr 1
    ring
  have htail0 : cI * (δt : ℝ≥0∞) ^ g * (b : ℝ≥0∞) ^ (-2 * γ) * Q ^ (1 - γ / 2)
      = (cI * (δt : ℝ≥0∞) ^ (g / 2)) * (δt : ℝ≥0∞) ^ (g / 2)
          * (b : ℝ≥0∞) ^ (-2 * γ) * Q ^ (1 - γ / 2) := by
    rw [hg_half]
    ac_rfl
  have hnum'g : 10 * ap' ≤ g / 2 := by simpa [g, β'] using hnum'
  have htail : (cI * (δt : ℝ≥0∞) ^ (g / 2)) * (δt : ℝ≥0∞) ^ (g / 2)
        * (b : ℝ≥0∞) ^ (-2 * γ) * Q ^ (1 - γ / 2)
      ≤ (δt : ℝ≥0∞) ^ (10 * ap') * (b : ℝ≥0∞) ^ (-2 * γ) * Q ^ (1 - γ / 2) := by
    have hpowg : (δt : ℝ≥0∞) ^ (g / 2) ≤ (δt : ℝ≥0∞) ^ (10 * ap') :=
      ENNReal.rpow_le_rpow_of_exponent_ge hδt1E hnum'g
    calc
      (cI * (δt : ℝ≥0∞) ^ (g / 2)) * (δt : ℝ≥0∞) ^ (g / 2)
            * (b : ℝ≥0∞) ^ (-2 * γ) * Q ^ (1 - γ / 2)
          ≤ 1 * (δt : ℝ≥0∞) ^ (g / 2) * (b : ℝ≥0∞) ^ (-2 * γ) * Q ^ (1 - γ / 2) := by
            gcongr
      _ = (δt : ℝ≥0∞) ^ (g / 2) * (b : ℝ≥0∞) ^ (-2 * γ) * Q ^ (1 - γ / 2) := by simp
      _ ≤ (δt : ℝ≥0∞) ^ (10 * ap') * (b : ℝ≥0∞) ^ (-2 * γ) * Q ^ (1 - γ / 2) :=
            mul_le_mul_of_nonneg_right (a := Q ^ (1 - γ / 2))
              (mul_le_mul_of_nonneg_right (a := (b : ℝ≥0∞) ^ (-2 * γ)) hpowg bot_le) bot_le
  calc
    ShadedBody.multiplicity t (fun l => (Tb l).toShadedBody)
        ≤ cI * (δt : ℝ≥0∞) ^ g * (b : ℝ≥0∞) ^ (-2 * γ) * Q ^ (1 - γ / 2) := by
          simpa [g, β'] using hμ2
    _ = (cI * (δt : ℝ≥0∞) ^ (g / 2)) * (δt : ℝ≥0∞) ^ (g / 2)
          * (b : ℝ≥0∞) ^ (-2 * γ) * Q ^ (1 - γ / 2) := htail0
    _ ≤ (δt : ℝ≥0∞) ^ (10 * ap') * (b : ℝ≥0∞) ^ (-2 * γ) * Q ^ (1 - γ / 2) := htail
    _ = (δt : ℝ≥0∞) ^ (10 * ap') * (b : ℝ≥0∞) ^ (-2 * γ)
          * ((t.card : ℝ≥0∞) * (b : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
          rw [show Q ^ (1 - γ / 2) =
              ((t.card : ℝ≥0∞) * (b : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2) from by
            dsimp [Q]
            apply congrArg (fun x : ℝ≥0∞ => x ^ (1 - γ / 2))
            exact mul_comm ((b : ℝ≥0∞) ^ (2 : ℕ)) (t.card : ℝ≥0∞)]

/-! ### Acceptance records for repair route (i)

Two checks: the exponent charge is free, and the supply already on the tree meets the demand. -/

/-- **the `ε₂ - ε` charge is free.**

`Kakeya.ml1Boot.multiplicity_coarse_le_of_const_ball` instantiates at `ε₂ = 3 ε / 2` with the
budget hypothesis `hnum` **unchanged** and no other numeric side condition.  So routing the
coarse route through the ambient radius costs `Kakeya.ml1Boot.Params.Spec` nothing, contrary to
the warning on `Kakeya.ml1Boot.multiplicity_coarse_raw_ball`. -/
example (hdim : Module.finrank ℝ E = 3)
    {β γ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hKKT : KatzTaoEstimate.{u} E β)
    {ε ap' : ℝ} (hε0 : 0 < ε) (hε1 : 5 * ε < 1) (hap' : 0 < ap')
    (hnum : γ - betaPrime β γ
      ≤ -72 * ε - 2 * ap' + 2 * (γ - betaPrime β γ))
    (hnum' : 10 * ap' ≤ (γ - betaPrime β γ) / 2)
    {CDelta : ℝ≥0} (hCDelta : 1 ≤ CDelta) :
    ∃ ηs > (0 : ℝ),
    ∀ᶠ (δt : ℝ≥0) in 𝓝[>] 0, ∀ b : ℝ≥0, δt ≤ b → b ≤ δt ^ (1 - 5 * ε) →
      (b : ℝ) ≤ 1 / 4 →
      ∀ {κ : Type u} (t : Finset κ) (Tb : κ → ShadedTube b E),
        t.Nonempty →
        (∀ l ∈ t, (Tb l).carrier ⊆ Metric.closedBall 0 (((11 : ℝ≥0) / 2 : ℝ≥0) : ℝ)) →
        (δt : ℝ≥0∞) ^ ((1 - 5 * ε) * ηs)
          ≤ ShadedBody.fullness t (fun l => (Tb l).toShadedBody) →
        maxDensity t (fun l => (Tb l).toConvexSpaceBody)
          ≤ (CDelta : ℝ≥0∞) * (δt : ℝ≥0∞) ^ (-30 * ε - ap') →
        frostmanConstIn t (fun l => (Tb l).toConvexSpaceBody)
            (ConvexSpaceBody.closedBall (0 : E) (((11 : ℝ≥0) / 2 : ℝ≥0) : ℝ)
              ((11 : ℝ≥0) / 2 : ℝ≥0).coe_nonneg)
          ≤ (CDelta : ℝ≥0∞) * (δt : ℝ≥0∞) ^ (-ap') →
        ShadedBody.multiplicity t (fun l => (Tb l).toShadedBody)
          ≤ (δt : ℝ≥0∞) ^ (10 * ap') * (b : ℝ≥0∞) ^ (-2 * γ)
            * ((t.card : ℝ≥0∞) * (b : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 - γ / 2) :=
  multiplicity_coarse_le_of_const_ball (ε₂ := 3 * ε / 2) hdim hβ0 hβ1 hγ0 hγ1 hKKT hε0 hε1 hap'
    (by linarith) (by linarith) hnum hnum' hCDelta ((11 : ℝ≥0) / 2)
    (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)

/-- **the supply already on the tree meets that demand.**

All four `b`-tube producers of `Rescaling/CoarseDensity.lean` export the location clause
`(Tb j).carrier ⊆ closedBall 0 (5/2 + 3 C_𝕎 bp)`
(`Kakeya.ml1Boot.exists_plankTube_parentFamily` and its three siblings, the source construction, i.e. **after** the ledger of `Kakeya.ml1Boot.multTildeT_of_planksClose` recorded
that "nothing in this repository produces `b`-tubes inside the unit ball" and that the dilate
clause is "the *only* location clause").  Under the plank-width side condition
`hbq1 : C_𝕎 bp ≤ 1` — closed by `Kakeya.ml1Boot.eventually_plankPigeonhole_C_mul_le_one`, and
the same condition the producers already carry — that radius is at most `11/2`, which is exactly
the `R` reads. -/
example {bp : ℝ≥0} (hbq1 : plankPigeonhole.C * bp ≤ 1)
    {b : ℝ≥0} {κ : Type*} {t : Finset κ} (Tb : κ → ShadedTube b E)
    (hloc : ∀ l ∈ t, (Tb l).carrier ⊆ Metric.closedBall (0 : E)
      (5 / 2 + 3 * ((plankPigeonhole.C * bp : ℝ≥0) : ℝ))) :
    ∀ l ∈ t, (Tb l).carrier
      ⊆ Metric.closedBall (0 : E) (((11 : ℝ≥0) / 2 : ℝ≥0) : ℝ) := by
  intro l hl
  refine (hloc l hl).trans (Metric.closedBall_subset_closedBall ?_)
  have hb : ((plankPigeonhole.C * bp : ℝ≥0) : ℝ) ≤ 1 := by exact_mod_cast hbq1
  push_cast
  linarith

/-! ### The parameter instantiation of the middle factor

The assembly of `Kakeya.ml1Boot.multiplicity_le_middle` runs the rescaled chain at three
exponents derived from the package, and they are *not* the naive ones.  Writing
`β₀ = β'(γ₀)`, `a = η_{j-1}` and `g₀ = γ₀ - β₀`:

* the **fullness** exponent is `aλ = a γ₀ / β₀`, strictly above `a`;
* the **Frostman** exponent is `aF = 5 aλ / ε`, strictly above `a + η₀ / ε`;
* the **eccentricity** exponent is `ap' = 10 aλ / (ε γ)`, still below `η'_{j-1}`.

The inflation of `a` to `aλ` is forced twice over and is the content of
`Kakeya.ml1Boot.middleFactor_numerics`.  First, the conclusion of the rescaled chain is
`δ̃ ^ (10 aλ / ε)`, and `δ̃ ≤ δ ^ ε` turns that into `δ ^ (10 aλ)`; the target asks for
`δ ^ (10 a)`, so `aλ > a` is exactly the room in which the fixed constant `C₂ Λ²` of
`Kakeya.ml1Boot.exists_normalizedMiddleData`(i) is absorbed into the smallness of `δ`.
Secondly, item (iii) of that lemma bounds the rescaled Frostman constant only by
`C₂ δ ^ (-η₀) δ̃ ^ (-a)`, and `δ ^ (-η₀) ≤ δ̃ ^ (-η₀ / ε)` is all that `δ̃ ≤ δ ^ ε` gives, so
the exponent the rescaled family honestly satisfies is `a + η₀ / ε` and not `a`.

That second point is why the fullness and the Frostman exponents have to be *decoupled*, and
it is the reason the retired coupled dichotomy — which forced them into a single `a` — could
not be applied at the value `a = η_{j-1}` the ladder supplies; the live form is
`Kakeya.ml1Boot.flatPrism_dichotomy_decoupled`.  Unwinding
`Kakeya.multiplicity_le_of_factorsThroughFlatPrisms'`, the dichotomy at fullness exponent
`aλ`, Frostman exponent `aF` and eccentricity exponent `ap' = 10 aλ / (ε γ)` needs only
`aF (1 - γ/2) + (loss) ≤ 5 aλ / ε`, and `aF = 5 aλ / ε` is exactly that budget.  The coupled
form is the special case `aF = aλ`, which the rescaled family does not satisfy. -/

/-! #### The scale transfer `δ̃ ≤ δ ^ ε`

The four lemmas below are the whole arithmetic content of the passage between the outer scale
`δ` and the middle scale `δ̃ = τ/θ` in `Kakeya.ml1Boot.multiplicity_le_middle`.  They are
stated abstractly, in `ENNReal`, because nothing geometric is involved: the multiplicities,
fullnesses and Frostman constants enter only as opaque values. -/

/-! `Kakeya.ml1Boot.normalizedUnif.C` and `Kakeya.ml1Boot.normalizedUnif.one_le_C` have moved
upstream to `Kakeya/DimensionThree/MainLemma1/Rescaling/Normalized.lean`, beside the lemma that
now returns the uniformity.

`Kakeya.ml1Boot.exists_normalizedMiddleData_unif`, which was
`Kakeya.ml1Boot.exists_normalizedMiddleData` with the uniformity hypothesis and conclusion added,
has been **retired**: that hypothesis and that conclusion are now part of
`Kakeya.ml1Boot.exists_normalizedMiddleData` itself, which also gained the ambient family the
blueprint requires (`note:ml1bootRescaledLowerAmbient`).  Use it directly. -/

/-! ### The plank conclusion is preserved by keeping whole parts

The plank clause of `Kakeya.ml1Boot.exists_plankDimensions_uniformSelection` asks, for every
parent `m`, for a `ConvexSpaceBody.Factorization` of the *whole* fibre `fibre u'' pρ m` all of
whose parts are `ap × bp × 1` planks.  Which selections that clause survives is therefore a
question about the atoms of the factorization, and the answer is that the atom is the **part**:

* keeping a sub-collection of whole parts is free — `ConvexSpaceBody.Factorization.ofSubsetParts`
  for the factorization and `Kakeya.ml1Boot.isPlankFamilyOfDimensions_subset` for the plank
  dimensions, packaged as `Kakeya.ml1Boot.exists_plankFactorization_of_subsetParts`;
* discarding a whole fibre is free — `Kakeya.ml1Boot.exists_plankFactorization_of_eq_empty`;
* dropping members *inside* a part is not free, and no lemma here does it: the part's hull
  shrinks, and `Kakeya.IsPlankOfDimensions` is two-sided (`Kakeya/Factoring/FlatPrisms.lean`),
  so the lower bounds `C⁻¹ ≤ τ₀`, `C⁻¹ b ≤ τ₁`, `C⁻¹ a ≤ τ₂` are the ones that fail.

`Kakeya.ml1Boot.isPlankFamilyOfDimensions_subset` is a general fact about
`Kakeya.IsPlankFamilyOfDimensions` and belongs beside its definition in
`Kakeya/Factoring/FlatPrisms.lean`; it is stated here because that file is not open for this
round.
-/

/-! ### Absorbing the dyadic-pigeonhole factor of the coarse Frostman bound

`Kakeya.ml1Boot.exists_frostmanConstIn_coarse_le` delivers the coarse Frostman bound with the
factor `C_↑(3, |u|, δ̃) = 2 (1 + log₂ (8 |u| / (c₃ δ̃ ^ 3)))₊` of
`ConvexSpaceBody.IsFrostmanIn.inherited_upwards.C`, while hypothesis (c) of
`Kakeya.ml1Boot.multiplicity_coarse_le` reads a bound of the shape `C_Δ δ̃ ^ (-ap')`.  That
factor is *not* a constant, but it is subpolynomial once `|u|` is bounded, and on this chain it
is bounded: the fine family is a nonempty family of pairwise essentially distinct `δ̃`-tubes in
`B₁`, so `Kakeya.ml1Boot.card_le` gives `|u| ≤ C_card δ̃ ^ (-4)` and therefore
`C_↑(3, |u|, δ̃) ≤ A (1 + log₂ (1 / δ̃))` with `A` depending only on `C_card` and on the
dimensional constant `c₃ = Kakeya.lt_volume_convexHull.c 3`.

The three lemmas below carry out the absorption in the same shape as the plank-pigeonhole
absorption `Kakeya.ml1Boot.eventually_plankPigeonhole_loss_le`: the cardinality bound enters as
a hypothesis on `n = |u|`, the polylogarithm is absorbed by
`ENNReal.eventually_ofReal_one_add_logb_pow_le_rpow_neg` and the fixed constant by
`Kakeya.absorb_const_le_rpow_neg`, both at half the available exponent.

The exponent room `σ` is not created here; it is read off the parameter instantiation.  With
`aF ≤ 6 aλ / ε` (the Frostman binder of `Kakeya.ml1Boot.multTildeT_of_planksClose`),
`10 aλ / (ε γ) ≤ η'_{j-1}` (`Kakeya.ml1Boot.middleFactor_numerics`(vi)) and `γ ≤ 1`, one gets
`aF ≤ (3/5) η'_{j-1}`, so at the intended `ap' = η'_{j-1}` any
`σ ≤ (2/5) η'_{j-1}` satisfies `aF + σ ≤ ap'`.  This spends none of the room that
`Kakeya.ml1Boot.multiplicity_coarse_le` itself needs: its `hnum` and `hnum'` constrain `ap'`,
`ε` and `g = γ - β'` only, and are untouched by the choice of `σ`. -/

end KatzTao

end ml1Boot

end Kakeya

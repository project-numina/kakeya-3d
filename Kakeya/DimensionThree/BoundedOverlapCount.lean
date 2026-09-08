/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Tube.Nets
public import Kakeya.Uniform
public import Kakeya.DimensionThree.MainLemma1.TubeAxis

/-!
# Counting the parents of a bounded-overlap family in `ℝ³`

`Tube.HasBoundedOverlap s V t Vρ Co` says that every `ρ`-tube `W` shares a member of the leaf
family `𝕍 = (V i)_{i ∈ s}` with at most `Co` of the parents `(Vρ k)_{k ∈ t}`.  If in addition
every parent actually has a leaf under it, the parents can be counted outright: there are at
most `Co · C · ρ ^ (-5)` of them.

The argument is a covering argument and uses no essential distinctness, which is the whole point:
`Kakeya.ml1Boot.card_le` needs `Pairwise IsEssentiallyDistinct` and is unavailable for the node
families of a hierarchy, which cannot satisfy it while preserving cardinality.

## The net

The proof takes a finite family of `ρ`-tubes so dense that *every* `σ`-tube with carrier in
`B̄(0,1)` lies inside one of them, and applies the bounded-overlap hypothesis once per net
element.  A `σ`-tube lies inside a `ρ`-tube whose direction is within `ε_dir` and whose midpoint
is within `ε_pos` as soon as `ε_pos + ε_dir / 2 + σ ≤ ρ` (`Tube.tube_carrier_subset_of_close`),
so the net is the product of

* a `ρ/32`-separated net of unit directions (`Tube.sphere_sep_net`), of cardinality
  `O(ρ ^ (-2))` because the `ρ`-thickening of the unit sphere is a shell of volume `O(ρ)`
  (`Kakeya.ml1Boot.volume_annulus_le`);
* a `ρ/32`-separated net of midpoints in `B̄(0,3)` (`Tube.midpoint_sep_net`), of cardinality
  `O(ρ ^ (-3))`.

Both counts come from the packing bound `Tube.card_le_of_separated_parameterSpace`.

## Why the exponent is `-5` and not `-4`

The `ρ ^ (-4)` of `Kakeya.ml1Boot.card_le` counts tubes *up to essential distinctness*: the
longitudinal position along the core is not a separated parameter there, because a slide along
the core by `|α| ≤ c_*` produces a tube that is not essentially distinct from the original
(`Tube.not_essDistinct_of_axial_slide`), and it is paid for by the bounded factor `8n + 1` of
`Kakeya.ml1Boot.card_axisCell_le` rather than by a power of `ρ`.

Bounded overlap gives no such identification, and `ρ ^ (-4)` is false for it.  Take `σ = ρ`,
`s = t` and `V = Vρ` a family of `ρ`-tubes in `B̄(0,1)` whose endpoint pairs are `100ρ`-separated.
By `Tube.endpoints_close_of_body_le`, `V i ≤ Vρ k` forces the endpoints of `V i` and `V k` to
agree to within `3ρ`, so for each `ρ`-tube `W` at most one `k` is counted and
`Tube.HasBoundedOverlap s V t Vρ 1` holds; yet the family has `≍ ρ ^ (-5)` members, three of the
five parameters being the unconstrained midpoint.  So `-5` is the correct exponent here, and it
is sharp for the same reason.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric

namespace Kakeya.ml1Boot

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### The two net counts -/

/-- **Constant in Lemma `Kakeya.ml1Boot.card_le_of_unit_separated`**: the packing constant for a
separated set of unit vectors in `ℝ³`, namely `C_cov(3)⁻¹ · 3 · 2³ · ω₃`.  It is the packing
constant of `Tube.card_le_of_separated_parameterSpace` in dimension three times the shell
constant of `Kakeya.ml1Boot.volume_annulus_le` in dimension three, and depends on nothing else,
the ambient dimension being fixed to `3`. -/
noncomputable def dirNet.C : ℝ≥0 :=
  (Metric.coveringNumber_mul_pow_le_volume_cthickening.C 3)⁻¹ * (3 * 2 ^ 3 * unitBallVolume 3)

/-- **A separated set of unit vectors in `ℝ³` has `O(η ^ (-2))` members.**

The `η`-thickening of the unit sphere is the shell `{ω : |‖ω‖ - 1| ≤ η}`, of volume `O(η)` by
`Kakeya.ml1Boot.volume_annulus_le`; feeding that into the packing bound
`Tube.card_le_of_separated_parameterSpace`, whose dimensional factor is `η ^ (-3)`, leaves
`η ^ (-2)`.  This is the codimension-one saving that makes the direction net cheaper than a net
of the whole ball. -/
theorem card_le_of_unit_separated (hdim : Module.finrank ℝ E = 3) {η : ℝ≥0}
    (hη : 0 < η) (hη1 : η ≤ 1) {D : Finset E}
    (hunit : ∀ d ∈ D, ‖d‖ = 1)
    (hsep : ∀ a ∈ D, ∀ b ∈ D, a ≠ b → (η : ℝ) < ‖a - b‖) :
    (D.card : ℝ≥0∞) ≤ (dirNet.C : ℝ≥0∞) * (η : ℝ≥0∞)⁻¹ ^ 2 := by
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hdim]; norm_num)
  have hηne : (η : ℝ≥0∞) ≠ 0 := by exact_mod_cast ne_of_gt hη
  have hηtop : (η : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  let hA : Set E := {ω : E | ‖ω‖ = 1}
  let hS : Set E := {ω : E | |‖ω‖ - 1| ≤ (η : ℝ)}
  -- Pairwise separation for the packing bound
  have hpair : (D : Set E).Pairwise fun a b : E => (η : ℝ) < dist a b := by
    intro a ha b hb hneq
    have : (η : ℝ) < ‖a - b‖ := hsep a ha b hb hneq
    simpa [dist_eq_norm] using this
  -- every element of D is a unit vector
  have hGA : ∀ d ∈ D, d ∈ hA := by
    intro d hd
    dsimp [hA]
    exact hunit d hd
  have hcard : (D.card : ℝ≥0∞)
      ≤ (Metric.coveringNumber_mul_pow_le_volume_cthickening.C (Module.finrank ℝ E) : ℝ≥0∞)⁻¹
        * (η : ℝ≥0∞)⁻¹ ^ Module.finrank ℝ E * volume (cthickening (η : ℝ) hA) :=
    Tube.card_le_of_separated_parameterSpace (r := η) hη hGA hpair
  have hcard3 : (D.card : ℝ≥0∞)
      ≤ (Metric.coveringNumber_mul_pow_le_volume_cthickening.C 3 : ℝ≥0∞)⁻¹
        * (η : ℝ≥0∞)⁻¹ ^ 3 * volume (cthickening (η : ℝ) hA) := by
    simpa [hdim, hA] using hcard
  -- the η-thickening of the unit sphere is inside the shell
  have hsub : Metric.cthickening (η : ℝ) hA ⊆ hS := by
    intro x hx
    have hxe : Metric.infEDist x hA ≤ ENNReal.ofReal (η : ℝ) := Metric.mem_cthickening_iff.mp hx
    have hlow : ENNReal.ofReal |‖x‖ - 1| ≤ Metric.infEDist x hA := by
      rw [Metric.le_infEDist]
      intro y hy
      have hy1 : ‖y‖ = 1 := by simpa [hA] using hy
      have hnorm : |‖x‖ - ‖y‖| ≤ ‖x - y‖ := abs_norm_sub_norm_le x y
      have h' : |‖x‖ - 1| ≤ dist x y := by
        simpa [hy1, ← dist_eq_norm] using hnorm
      rw [edist_dist]
      exact (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mpr h'
    have hle : ENNReal.ofReal |‖x‖ - 1| ≤ ENNReal.ofReal (η : ℝ) := hlow.trans hxe
    exact (ENNReal.ofReal_le_ofReal_iff (show 0 ≤ (η : ℝ) from NNReal.coe_nonneg _)).mp hle
  have hvolmono : volume (cthickening (η : ℝ) hA) ≤ volume hS := measure_mono hsub
  -- shell volume is O(η) in dimension 3
  have hvol3 : volume (cthickening (η : ℝ) hA) ≤
      ENNReal.ofReal (3 * 2 ^ 3 * (unitBallVolume 3 : ℝ) * (η : ℝ)) := by
    have hr0 : 0 < (η : ℝ) := by exact_mod_cast hη
    have hr1 : (η : ℝ) ≤ 1 := by exact_mod_cast hη1
    have hann : volume hS ≤ ENNReal.ofReal ((Module.finrank ℝ E : ℝ) * 2 ^ Module.finrank ℝ E
        * (unitBallVolume (Module.finrank ℝ E) : ℝ) * (η : ℝ)) :=
      Kakeya.ml1Boot.volume_annulus_le (E := E) (r := (η : ℝ)) hr0 hr1
    have h1 : volume (cthickening (η : ℝ) hA) ≤
        ENNReal.ofReal ((Module.finrank ℝ E : ℝ) * 2 ^ Module.finrank ℝ E
        * (unitBallVolume (Module.finrank ℝ E) : ℝ) * (η : ℝ)) := hvolmono.trans hann
    simpa [hdim] using h1
  have hconv : ENNReal.ofReal (3 * 2 ^ 3 * (unitBallVolume 3 : ℝ) * (η : ℝ))
      = (3 * 2 ^ 3 * unitBallVolume 3 : ℝ≥0) * (η : ℝ≥0∞) := by
    rw [← ENNReal.coe_mul]
    rw [← ENNReal.ofReal_coe_nnreal]
    congr
  let c3 : ℝ≥0∞ := (Metric.coveringNumber_mul_pow_le_volume_cthickening.C 3 : ℝ≥0∞)⁻¹
  let shell : ℝ≥0∞ := ((3 * 2 ^ 3 * unitBallVolume 3 : ℝ≥0) : ℝ≥0∞)
  have hvolShell : volume (cthickening (η : ℝ) hA) ≤ shell * (η : ℝ≥0∞) := by
    simpa [shell] using hvol3.trans_eq hconv
  -- assemble: c3 · η⁻³ · (shell · η) = dirNet.C · η⁻²
  have hpow : (η : ℝ≥0∞)⁻¹ ^ 3 * (η : ℝ≥0∞) = (η : ℝ≥0∞)⁻¹ ^ 2 := by
    rw [pow_succ]
    rw [mul_assoc, ENNReal.inv_mul_cancel hηne hηtop, mul_one]
  have hdir : c3 * shell = (dirNet.C : ℝ≥0∞) := by
    dsimp [c3, shell]
    rw [show (dirNet.C : ℝ≥0∞) =
        ↑((Metric.coveringNumber_mul_pow_le_volume_cthickening.C 3 : ℝ≥0)⁻¹
        * (3 * 2 ^ 3 * unitBallVolume 3 : ℝ≥0)) by rfl]
    rw [ENNReal.coe_mul]
    rw [ENNReal.coe_inv (ne_of_gt (Metric.coveringNumber_mul_pow_le_volume_cthickening.C_pos 3))]
    rfl
  calc
    (D.card : ℝ≥0∞)
        ≤ c3 * (η : ℝ≥0∞)⁻¹ ^ 3 * volume (cthickening (η : ℝ) hA) := by
          simpa [c3] using hcard3
    _ ≤ c3 * (η : ℝ≥0∞)⁻¹ ^ 3 * (shell * (η : ℝ≥0∞)) := by
          exact mul_le_mul_of_nonneg_left hvolShell (by positivity)
    _ = c3 * shell * (η : ℝ≥0∞)⁻¹ ^ 2 := by
          rw [← hpow]
          ac_rfl
    _ = (dirNet.C : ℝ≥0∞) * (η : ℝ≥0∞)⁻¹ ^ 2 := by
          rw [hdir]

/-- **Constant in Lemma `Kakeya.ml1Boot.card_le_of_ball_separated`**: the packing constant for a
separated subset of `B̄(0,3) ⊆ ℝ³`, namely `C_cov(3)⁻¹ · ω₃ · 4³`.  The `4³` is the volume of the
ball `B̄(0,4)` that contains every `η`-thickening of `B̄(0,3)` for `η ≤ 1`. -/
noncomputable def posNet.C : ℝ≥0 :=
  (Metric.coveringNumber_mul_pow_le_volume_cthickening.C 3)⁻¹ * (unitBallVolume 3 * 4 ^ 3)

/-- **A separated subset of `B̄(0,3) ⊆ ℝ³` has `O(η ^ (-3))` members.**

Straight volume packing: the `η`-thickening of `B̄(0,3)` sits inside `B̄(0,4)` for `η ≤ 1`, so
`Tube.card_le_of_separated_parameterSpace` gives the full dimensional factor `η ^ (-3)` with no
saving. -/
theorem card_le_of_ball_separated (hdim : Module.finrank ℝ E = 3) {η : ℝ≥0}
    (hη : 0 < η) (hη1 : η ≤ 1) {P : Finset E}
    (hmem : ∀ p ∈ P, ‖p‖ ≤ 3)
    (hsep : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → (η : ℝ) < ‖a - b‖) :
    (P.card : ℝ≥0∞) ≤ (posNet.C : ℝ≥0∞) * (η : ℝ≥0∞)⁻¹ ^ 3 := by
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hdim]; norm_num)
  let hA : Set E := Metric.closedBall (0 : E) 3
  -- Pairwise separation for the packing bound
  have hpair : (P : Set E).Pairwise fun a b : E => (η : ℝ) < dist a b := by
    intro a ha b hb hneq
    have : (η : ℝ) < ‖a - b‖ := hsep a ha b hb hneq
    simpa [dist_eq_norm] using this
  -- every element of P is in the ball B̄(0,3)
  have hGA : ∀ p ∈ P, p ∈ hA := by
    intro p hp
    rw [Metric.mem_closedBall, dist_eq_norm]
    simpa using hmem p hp
  have hcard : (P.card : ℝ≥0∞)
      ≤ (Metric.coveringNumber_mul_pow_le_volume_cthickening.C (Module.finrank ℝ E) : ℝ≥0∞)⁻¹
        * (η : ℝ≥0∞)⁻¹ ^ Module.finrank ℝ E * volume (cthickening (η : ℝ) hA) :=
    Tube.card_le_of_separated_parameterSpace (r := η) hη hGA hpair
  have hcard3 : (P.card : ℝ≥0∞)
      ≤ (Metric.coveringNumber_mul_pow_le_volume_cthickening.C 3 : ℝ≥0∞)⁻¹
        * (η : ℝ≥0∞)⁻¹ ^ 3 * volume (cthickening (η : ℝ) hA) := by
    simpa [hdim, hA] using hcard
  -- the η-thickening of B̄(0,3) is inside B̄(0,4)
  have hsub : Metric.cthickening (η : ℝ) hA ⊆ Metric.closedBall (0 : E) 4 := by
    have hcpt : IsCompact hA := isCompact_closedBall (0 : E) 3
    rw [hcpt.cthickening_eq_biUnion_closedBall (NNReal.coe_nonneg η)]
    refine Set.iUnion₂_subset fun x hx => ?_
    refine Metric.closedBall_subset_closedBall' ?_
    have hx3 : dist x (0 : E) ≤ 3 := by simpa [hA] using hx
    have hηr : (η : ℝ) ≤ 1 := NNReal.coe_le_coe.mpr hη1
    linarith
  have hvolmono : volume (cthickening (η : ℝ) hA) ≤ volume (Metric.closedBall (0 : E) 4) :=
    measure_mono hsub
  -- closed-ball volume in dimension 3
  have hvol4 : volume (Metric.closedBall (0 : E) 4) =
      ENNReal.ofReal ((unitBallVolume 3 : ℝ) * 4 ^ 3) := by
    have hv : volume (Metric.closedBall (0 : E) 4) =
        ENNReal.ofReal ((unitBallVolume (Module.finrank ℝ E) : ℝ) * 4 ^ Module.finrank ℝ E) := by
      rw [volume_closedBall_eq_ccov_mul_pow (E := E) (r := 4) (by norm_num : (0 : ℝ) ≤ 4)]
      congr 1
    simpa [hdim] using hv
  have hvol3 : volume (cthickening (η : ℝ) hA) ≤ ENNReal.ofReal ((unitBallVolume 3 : ℝ) * 4 ^ 3) :=
    hvolmono.trans_eq hvol4
  have hconv : ENNReal.ofReal ((unitBallVolume 3 : ℝ) * 4 ^ 3)
      = ((unitBallVolume 3 * 4 ^ 3 : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (unitBallVolume 3 : ℝ))]
    rw [ENNReal.ofReal_coe_nnreal]
    rw [show ENNReal.ofReal ((4 : ℝ) ^ 3) = ((4 ^ 3 : ℝ≥0) : ℝ≥0∞) by norm_num]
    rw [← ENNReal.coe_mul]
  let c3 : ℝ≥0∞ := (Metric.coveringNumber_mul_pow_le_volume_cthickening.C 3 : ℝ≥0∞)⁻¹
  let ball : ℝ≥0∞ := ((unitBallVolume 3 * 4 ^ 3 : ℝ≥0) : ℝ≥0∞)
  have hvolBall : volume (cthickening (η : ℝ) hA) ≤ ball := by
    simpa [ball] using hvol3.trans_eq hconv
  have hdir : c3 * ball = (posNet.C : ℝ≥0∞) := by
    dsimp [c3, ball]
    rw [show (posNet.C : ℝ≥0∞) =
        ↑((Metric.coveringNumber_mul_pow_le_volume_cthickening.C 3 : ℝ≥0)⁻¹
        * (unitBallVolume 3 * 4 ^ 3 : ℝ≥0)) by rfl]
    rw [ENNReal.coe_mul]
    rw [ENNReal.coe_inv (ne_of_gt (Metric.coveringNumber_mul_pow_le_volume_cthickening.C_pos 3))]
    rfl
  calc
    (P.card : ℝ≥0∞)
        ≤ c3 * (η : ℝ≥0∞)⁻¹ ^ 3 * volume (cthickening (η : ℝ) hA) := by
          simpa [c3] using hcard3
    _ ≤ c3 * (η : ℝ≥0∞)⁻¹ ^ 3 * ball := by
          exact mul_le_mul_of_nonneg_left hvolBall (by positivity)
    _ = (posNet.C : ℝ≥0∞) * (η : ℝ≥0∞)⁻¹ ^ 3 := by
          rw [← hdir]
          ac_rfl

/-! ### The direction–midpoint net -/

/-- **Constant in Lemma `Kakeya.ml1Boot.card_parents_le_of_hasBoundedOverlap`**: the size of the
direction–midpoint net at scale `ρ`, namely `64 ^ 5 · dirNet.C · posNet.C`.  The nets are built
at separation `ρ/32` and counted at strict separation `ρ/64`, which is where the `64 ^ 5` comes
from; the exponent `5 = 2 + 3` is `2` directions plus `3` positions. -/
noncomputable def parentCount.C : ℝ≥0 := 64 ^ 5 * (dirNet.C * posNet.C)

/-- **The direction–midpoint net at scale `ρ`.**

A finite set of pairs `(d, p)` with `‖d‖ = 1`, of cardinality at most
`parentCount.C · ρ ^ (-5)`, such that every unit direction is within `ρ/16` of some `d` and
every point of `B̄(0,1)` is within `ρ/16` of the matching `p` — the two pairs being chosen
independently, so the net is the full product of a direction net and a midpoint net.

This is the covering input of `Kakeya.ml1Boot.card_parents_le_of_hasBoundedOverlap`, kept
tube-free: turning a pair into a `ρ`-tube is `Tube.ofMidpointDirection`, and the containment
step is `Tube.tube_carrier_subset_of_close`. -/
theorem exists_dirPos_net (hdim : Module.finrank ℝ E = 3) {ρ : ℝ≥0}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ S : Finset (E × E),
      (∀ q ∈ S, ‖q.1‖ = 1) ∧
      (S.card : ℝ≥0∞) ≤ (parentCount.C : ℝ≥0∞) * (ρ : ℝ≥0∞)⁻¹ ^ 5 ∧
      ∀ u m : E, ‖u‖ = 1 → ‖m‖ ≤ 1 →
        ∃ q ∈ S, ‖u - q.1‖ ≤ (ρ : ℝ) / 16 ∧ ‖m - q.2‖ ≤ (ρ : ℝ) / 16 := by
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hdim]; norm_num)
  let ε : ℝ := (ρ : ℝ) / 32
  have hε : 0 < ε := by
    dsimp [ε]
    exact div_pos (by exact_mod_cast hρ) (by norm_num : (0 : ℝ) < 32)
  have hε1 : ε ≤ 1 := by
    dsimp [ε]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 32)]
    have hρ1r : (ρ : ℝ) ≤ 1 := NNReal.coe_le_coe.mpr hρ1
    nlinarith
  have h2ε : 2 * ε = (ρ : ℝ) / 16 := by
    dsimp [ε]
    ring
  let η : ℝ≥0 := ρ / 64
  have hη0 : 0 < η := by
    dsimp [η]
    positivity
  have hη1 : η ≤ 1 := by
    dsimp [η]
    rw [← NNReal.coe_le_coe]
    rw [NNReal.coe_div]
    norm_num
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 64)]
    have hρ1r : (ρ : ℝ) ≤ 1 := NNReal.coe_le_coe.mpr hρ1
    nlinarith
  have hηε : (η : ℝ) < ε := by
    dsimp [η, ε]
    calc
      (ρ : ℝ) / 64 = (ρ : ℝ) * ((1 : ℝ) / 64) := by ring
      _ < (ρ : ℝ) * ((1 : ℝ) / 32) := by
        exact mul_lt_mul_of_pos_left (by norm_num : (1 : ℝ) / 64 < 1 / 32)
          (by exact_mod_cast hρ)
      _ = (ρ : ℝ) / 32 := by ring
  obtain ⟨D, hD_unit, hD_sep, hD_cover⟩ := Tube.sphere_sep_net (E := E) hε hε1
  obtain ⟨Pm, hPm_ball, hPm_sep, hPm_cover⟩ := Tube.midpoint_sep_net (E := E) hε
  have hD_strict : ∀ a ∈ D, ∀ b ∈ D, a ≠ b → (η : ℝ) < ‖a - b‖ := by
    intro a ha b hb hne
    exact lt_of_lt_of_le hηε (hD_sep a ha b hb hne)
  have hP_strict : ∀ a ∈ Pm, ∀ b ∈ Pm, a ≠ b → (η : ℝ) < ‖a - b‖ := by
    intro a ha b hb hne
    exact lt_of_lt_of_le hηε (hPm_sep a ha b hb hne)
  have hP_norm : ∀ p ∈ Pm, ‖p‖ ≤ 3 := by
    intro p hp
    have hmem : p ∈ Metric.closedBall (0 : E) 3 := hPm_ball p hp
    rw [Metric.mem_closedBall, dist_eq_norm] at hmem
    simpa using hmem
  have hDcard : (D.card : ℝ≥0∞) ≤ (dirNet.C : ℝ≥0∞) * (η : ℝ≥0∞)⁻¹ ^ 2 :=
    card_le_of_unit_separated hdim hη0 hη1 hD_unit hD_strict
  have hPcard : (Pm.card : ℝ≥0∞) ≤ (posNet.C : ℝ≥0∞) * (η : ℝ≥0∞)⁻¹ ^ 3 :=
    card_le_of_ball_separated hdim hη0 hη1 hP_norm hP_strict
  let S : Finset (E × E) := D ×ˢ Pm
  have hη_coe : (η : ℝ≥0∞) = (ρ : ℝ≥0∞) / ((64 : ℝ≥0) : ℝ≥0∞) := by
    dsimp [η]
    rw [ENNReal.coe_div (by norm_num : (64 : ℝ≥0) ≠ 0)]
    norm_num
  have hηinv : (η : ℝ≥0∞)⁻¹ = ((64 : ℝ≥0) : ℝ≥0∞) * (ρ : ℝ≥0∞)⁻¹ := by
    rw [hη_coe]
    rw [div_eq_mul_inv]
    rw [ENNReal.mul_inv (Or.inl (by exact_mod_cast ne_of_gt hρ))
      (Or.inl ENNReal.coe_ne_top)]
    rw [inv_inv]
    rw [mul_comm]
  have hpow5 : (η : ℝ≥0∞)⁻¹ ^ 5 = (((64 : ℝ≥0) : ℝ≥0∞) ^ 5) * (ρ : ℝ≥0∞)⁻¹ ^ 5 := by
    rw [hηinv]
    rw [mul_pow]
  have hconst : ((dirNet.C * posNet.C : ℝ≥0) : ℝ≥0∞) * (((64 : ℝ≥0) : ℝ≥0∞) ^ 5)
      = (parentCount.C : ℝ≥0∞) := by
    rw [← ENNReal.coe_pow]
    rw [← ENNReal.coe_mul]
    rw [mul_comm]
    rfl
  have hparent : (dirNet.C * posNet.C : ℝ≥0) * (η : ℝ≥0∞)⁻¹ ^ 5
      = (parentCount.C : ℝ≥0∞) * (ρ : ℝ≥0∞)⁻¹ ^ 5 := by
    rw [hpow5]
    rw [← hconst]
    ac_rfl
  have hmul : (dirNet.C : ℝ≥0∞) * (η : ℝ≥0∞)⁻¹ ^ 2
      * ((posNet.C : ℝ≥0∞) * (η : ℝ≥0∞)⁻¹ ^ 3)
      = (dirNet.C * posNet.C : ℝ≥0) * (η : ℝ≥0∞)⁻¹ ^ 5 := by
    calc
      (dirNet.C : ℝ≥0∞) * (η : ℝ≥0∞)⁻¹ ^ 2 * ((posNet.C : ℝ≥0∞) * (η : ℝ≥0∞)⁻¹ ^ 3)
          = ((dirNet.C : ℝ≥0∞) * (posNet.C : ℝ≥0∞))
              * (((η : ℝ≥0∞)⁻¹ ^ 2) * ((η : ℝ≥0∞)⁻¹ ^ 3)) := by
            ac_rfl
      _ = ((dirNet.C * posNet.C : ℝ≥0) : ℝ≥0∞) * ((η : ℝ≥0∞)⁻¹ ^ (2 + 3)) := by
            rw [← ENNReal.coe_mul]
            rw [← pow_add]
      _ = (dirNet.C * posNet.C : ℝ≥0) * (η : ℝ≥0∞)⁻¹ ^ 5 := by
            rfl
  have hScard : (S.card : ℝ≥0∞) ≤ (parentCount.C : ℝ≥0∞) * (ρ : ℝ≥0∞)⁻¹ ^ 5 := by
    calc
      (S.card : ℝ≥0∞) = (D.card : ℝ≥0∞) * (Pm.card : ℝ≥0∞) := by
        dsimp [S]
        rw [Finset.card_product]
        norm_cast
      _ ≤ (dirNet.C : ℝ≥0∞) * (η : ℝ≥0∞)⁻¹ ^ 2
          * ((posNet.C : ℝ≥0∞) * (η : ℝ≥0∞)⁻¹ ^ 3) := by
        exact mul_le_mul' hDcard hPcard
      _ = (dirNet.C * posNet.C : ℝ≥0) * (η : ℝ≥0∞)⁻¹ ^ 5 := hmul
      _ = (parentCount.C : ℝ≥0∞) * (ρ : ℝ≥0∞)⁻¹ ^ 5 := hparent
  have hS_unit : ∀ q ∈ S, ‖q.1‖ = 1 := by
    intro q hq
    exact hD_unit q.1 (Finset.mem_product.mp hq).1
  have hcover : ∀ u m : E, ‖u‖ = 1 → ‖m‖ ≤ 1 →
        ∃ q ∈ S, ‖u - q.1‖ ≤ (ρ : ℝ) / 16 ∧ ‖m - q.2‖ ≤ (ρ : ℝ) / 16 := by
    intro u m hu hm
    obtain ⟨d, hd, hdu⟩ := hD_cover u hu
    have hm_ball : m ∈ Metric.closedBall (0 : E) 3 := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have : ‖m‖ ≤ 3 := le_trans hm (by norm_num)
      simpa using this
    obtain ⟨p, hp, hpm⟩ := hPm_cover m hm_ball
    refine ⟨(d, p), ?_, ?_, ?_⟩
    · rw [Finset.mem_product]
      exact ⟨hd, hp⟩
    · rw [← h2ε]
      exact hdu
    · rw [← h2ε]
      exact hpm
  refine ⟨S, hS_unit, hScard, hcover⟩

/-! ### The count -/

/-! ### The occupied-parent count for an assignment map

The consumers of GWZ Proposition 6.6(A) do not present their parent data as a containment: a
leaf `i` carries a *label* `assign i`, and the geometric relation to the labelled parent is only
`V i ≤ Tube.dilate (Vρ (assign i)) D`.  What has to be counted is the set of *occupied labels*,
`{k ∈ r | ∃ i ∈ q, assign i = k}`, which is exactly the parent-map fibre support used by
Proposition 5.1.  The two lemmas below do that count from bounded overlap, and show that the
label form of bounded overlap is *implied* by `Tube.HasBoundedOverlap` for any parent family
whose leaves lie under their labelled parents — which is the `le_parent` field of
`Kakeya.ml1Boot.IsParentFamily`.  No essential distinctness anywhere.
-/

end Kakeya.ml1Boot

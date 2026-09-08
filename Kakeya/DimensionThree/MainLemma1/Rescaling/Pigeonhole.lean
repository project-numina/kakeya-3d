/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Rescaling.Normalized

/-!
# Main Lemma 1, Case (ii): The plank pigeonhole

Split out of `Kakeya/DimensionThree/MainLemma1/Rescaling.lean`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya

namespace ml1Boot

/-! ### The plank pigeonhole -/

/-- **The constant `C_{lem:ml1bootPlankPigeonhole}`** of the plank pigeonhole: the total loss of the
plank pigeonhole, the product of the
factoring constant `2` of `lemmafactmax`, of the constant `8` absorbing the passage from the
dyadic classes of the two affine thicknesses `τ₁, τ₂` to a single pair `(a, b)`, and of the
volume-comparison constant `Metric.volume_comparison.C 3` in `ℝ³`.

It depends only on the ambient dimension `3`; in particular not on `δ̃`, on `ρ`, on `γ`, on
`j`, or on the family. -/
noncomputable abbrev plankPigeonhole.C : ℝ≥0 := 16 * Metric.volume_comparison.C 3

/-- **The constant `C^vol_{lem:ml1bootPlankPigeonhole}`**: the *volume* counterpart of the shape
constant
`Kakeya.ml1Boot.plankPigeonhole.C`, used in item `item:plankVolume` of
`Kakeya.ml1Boot.exists_plankDimensions`.

The exponent on `C_𝕎` is `3` and not `1`: it is the shape constant of `item:plankDims`
propagated through a product of three thicknesses.  Like `Kakeya.ml1Boot.plankPigeonhole.C`
it depends only on the ambient dimension `3`; in particular not on `δ̃`, `a`, `b`, `ρ`, `γ`,
`j`, or the family.  See blueprint `note:ml1bootPlankVolumeConstantCubed`. -/
noncomputable abbrev plankPigeonhole.C_vol : ℝ≥0 :=
  8 * plankPigeonhole.C ^ 3 * Metric.volume_comparison.C 3

/-- **Both numerical requirements on the plank volume constant**.

The declared value `8 C³ · Metric.volume_comparison.C 3` of
`Kakeya.ml1Boot.plankPigeonhole.C_vol` dominates the two quantities that the proof of
`Kakeya.ml1Boot.exists_plankDimensions`(iv) has to weaken, namely the upper constant `8 C³`
and the reciprocal of the lower constant `c₃ C⁻³` of
`Kakeya.ml1Boot.volume_bounds_of_isPlankOfDimensions`.

Writing `V = Metric.volume_comparison.C 3 = 4³ / c₃ ≥ 64`, the first reads `8 C³ ≤ 8 C³ V`
and the second `C³ V / 64 ≤ 8 C³ V`.  No tight computation is claimed.  As in
`Kakeya.ml1Boot.plankInTube_constant_bounds` the constant is carried as a parameter;
instantiating `C := Kakeya.ml1Boot.plankPigeonhole.C` returns the blueprint statement. -/
theorem plankPigeonhole_volume_constant_bounds {C : ℝ≥0} (hC : 1 ≤ C) :
    8 * C ^ 3 ≤ 8 * C ^ 3 * Metric.volume_comparison.C 3 ∧
      C ^ 3 / Metric.lt_volume_convexHull.c 3 ≤ 8 * C ^ 3 * Metric.volume_comparison.C 3 := by
  have hc_pos : 0 < Metric.lt_volume_convexHull.c 3 := Metric.lt_volume_convexHull.c_pos 3
  have hc_ne : Metric.lt_volume_convexHull.c 3 ≠ 0 := hc_pos.ne'
  have hV : Metric.volume_comparison.C 3 = 4 ^ 3 / Metric.lt_volume_convexHull.c 3 := rfl
  constructor
  · have hVge1 : 1 ≤ Metric.volume_comparison.C 3 := by
      dsimp [Metric.volume_comparison.C, Metric.lt_volume_convexHull.c]
      norm_num
    exact le_mul_of_one_le_right (by positivity : 0 ≤ 8 * C ^ 3) hVge1
  · rw [div_le_iff₀ hc_pos, hV]
    have hclear : (8 * C ^ 3 * (4 ^ 3 / Metric.lt_volume_convexHull.c 3)) *
        Metric.lt_volume_convexHull.c 3 = 8 * C ^ 3 * 4 ^ 3 := by
      rw [mul_assoc, div_mul_cancel₀ (4 ^ 3) hc_ne]
    rw [hclear]
    calc
      C ^ 3 ≤ C ^ 3 * (8 * 4 ^ 3) := by
        exact le_mul_of_one_le_right (by positivity : 0 ≤ (C ^ 3 : ℝ≥0))
          (by norm_num : (1 : ℝ≥0) ≤ 8 * 4 ^ 3)
      _ = 8 * C ^ 3 * 4 ^ 3 := by ring

section Pigeonhole

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **`ENNReal.dyadic_pigeonhole₁''` made nonemptiness-preserving**, at no cost in hypotheses.

The engine `Real.dyadic_pigeonhole` (`Kakeya/Pigeonhole.lean:105`-`106`) short-circuits on
`s.sum w ≤ 0` and answers `∅`, so `ENNReal.dyadic_pigeonhole₁''` retains no index at all when the
total weight vanishes.  That is harmless for the weight inequality and fatal for any caller that
needs a surviving index.

The repair needs neither positive weight nor fullness: on the degenerate branch the returned
weight inequality already forces `s.sum w = 0`, so *any* singleton `{i₀}` with `i₀ ∈ s` satisfies
the same inequality, and the dyadic comparison over a singleton is `f i₀ ≤ 2 * f i₀`.

Nonemptiness is stated as an implication rather than as a bare `s'.Nonempty` because that is the
unconditional form: a subset of an empty `s` cannot be nonempty. -/
theorem exists_dyadicClass_nonempty {ι : Type*} {s : Finset ι}
    (w : ι → ℝ≥0∞) (f : ι → ℝ≥0∞) {a b : ℝ≥0} (ha : 0 < a)
    (h : ∀ i ∈ s, f i ∈ Set.Icc (a : ℝ≥0∞) (b : ℝ≥0∞)) :
    ∃ s' ⊆ s, (s.Nonempty → s'.Nonempty) ∧
      (∑ i ∈ s, w i
          ≤ ENNReal.ofReal (1 + Real.logb (2 : ℝ) ((b : ℝ) / (a : ℝ))) * ∑ i ∈ s', w i) ∧
        ∀ i ∈ s', ∀ j ∈ s', f i ≤ 2 * f j := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · exact ⟨∅, by simp, by simp, by simp, by simp⟩
  · obtain ⟨s', hsub, hsum, hdy⟩ := ENNReal.dyadic_pigeonhole₁'' s w f ha h
    rcases s'.eq_empty_or_nonempty with rfl | hne
    · have hsum0 : (∑ i ∈ s, w i) = 0 := by
        apply le_antisymm
        · simpa using hsum
        · exact zero_le
      refine ⟨{i₀}, ?_, ?_, ?_, ?_⟩
      · exact Finset.singleton_subset_iff.mpr hi₀
      · intro _
        exact Finset.singleton_nonempty i₀
      · rw [hsum0]
        exact zero_le
      · intro i hi j hj
        rw [Finset.mem_singleton] at hi hj
        subst hi
        subst hj
        exact le_mul_of_one_le_left zero_le one_le_two
    · exact ⟨s', hsub, fun _ => hne, hsum, hdy⟩

/-- **(after GWZ Lemma 4.1, the cross-`m` step) One pair of dimensions for all parents at once**
.

`ConvexSpaceBody.Factorization.simDims` compares the affine thicknesses of two parts of the
*same* factorization, so it makes the planks over a single parent `m` comparable with
constant `2` and says nothing across different `m`.  This lemma is the missing upgrade: given
a designated part `rep m` over each parent and the a priori ranges of the three affine
thicknesses, two applications of `ENNReal.dyadic_pigeonhole₁''` — one for `τ₁`, one for `τ₂`,
both weighted by `w` — retain a set of parents `tρ'` carrying all but a
`(1 + log₂ (ρ / δ̃))²` fraction of the weight, on which a *single* pair `(ap, bp)` describes
every plank over every surviving parent.

The constants multiply as `2 · 2 · 2 = 8`: a factor `2` from `simDims` inside each of the two
factorizations being compared, and a factor `2` from each dyadic class.  Hence the hypothesis
`8 ≤ C`, which `Kakeya.ml1Boot.plankPigeonhole.C ≥ 1024` satisfies with room to spare.

The two range hypotheses are exactly what the geometry of the intended application supplies:
`τ₀ ∈ [1/2, 1]` because a plank contains a `δ̃`-tube (whose core is a unit segment, so its
circumradius is at least `1/2`) and lies in `B₁`; and `τ₁, τ₂ ∈ [δ̃, ρ]` because a plank
contains a `δ̃`-tube and lies in a `ρ`-tube, which is within `ρ` of a line.

`rep` is taken as data rather than chosen internally so that the caller controls which part
represents each parent; the conclusion is vacuous over a parent whose set of parts is empty,
which is what happens to a parent whose fibre is emptied by the refinement.

The clause `t_ρ.Nonempty → t_ρ'.Nonempty` costs nothing and is not a positivity assumption on
the weight: it comes from `Kakeya.ml1Boot.exists_dyadicClass_nonempty` in place of
`ENNReal.dyadic_pigeonhole₁''`, which returns `∅` when the total weight vanishes.  It is stated
as an implication because that is the unconditional form. -/
theorem exists_commonPlankDims {C ρ δt : ℝ≥0} (hC : 8 ≤ C) (hδt : 0 < δt) (hδρ : δt ≤ ρ)
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u : Finset ι} {tρ : Finset κ}
    (V : ι → ConvexSpaceBody E) (pρ : ι → κ) (w : κ → ℝ≥0∞)
    (F : (m : κ) → ConvexSpaceBody.Factorization (fibre u pρ m) V 2)
    (rep : κ → Finset ι) (hrep : ∀ m ∈ tρ, rep m ∈ (F m).parts)
    (hτ₀ : ∀ m ∈ tρ, ∀ part ∈ (F m).parts,
      Metric.ethickness ℝ (part.convexHull_biUnion V).carrier 0 ∈
        Set.Icc (2⁻¹ : ℝ≥0∞) 1)
    (hτ₁ : ∀ m ∈ tρ, ∀ part ∈ (F m).parts,
      Metric.ethickness ℝ (part.convexHull_biUnion V).carrier 1 ∈
        Set.Icc (δt : ℝ≥0∞) (ρ : ℝ≥0∞))
    (hτ₂ : ∀ m ∈ tρ, ∀ part ∈ (F m).parts,
      Metric.ethickness ℝ (part.convexHull_biUnion V).carrier 2 ∈
        Set.Icc (δt : ℝ≥0∞) (ρ : ℝ≥0∞)) :
    ∃ tρ' ⊆ tρ, (tρ.Nonempty → tρ'.Nonempty) ∧ ∃ ap bp : ℝ≥0, δt ≤ ap ∧ ap ≤ bp ∧ bp ≤ ρ ∧
      ∑ m ∈ tρ, w m
          ≤ ENNReal.ofReal (1 + Real.logb 2 ((ρ : ℝ) / (δt : ℝ))) ^ 2 * ∑ m ∈ tρ', w m ∧
        ∀ m ∈ tρ', IsPlankFamilyOfDimensions C ap bp (F m).parts
          (fun part => part.convexHull_biUnion V) := by
  classical
  let t₁ : κ → ℝ≥0∞ := fun m => Metric.ethickness ℝ ((rep m).convexHull_biUnion V).carrier 1
  let t₂ : κ → ℝ≥0∞ := fun m => Metric.ethickness ℝ ((rep m).convexHull_biUnion V).carrier 2
  let L : ℝ≥0∞ := ENNReal.ofReal (1 + Real.logb 2 ((ρ : ℝ) / (δt : ℝ)))
  have hτ₁rep : ∀ m ∈ tρ, t₁ m ∈ Set.Icc (δt : ℝ≥0∞) (ρ : ℝ≥0∞) := by
    intro m hm
    simpa [t₁] using hτ₁ m hm (rep m) (hrep m hm)
  have hτ₂rep : ∀ m ∈ tρ, t₂ m ∈ Set.Icc (δt : ℝ≥0∞) (ρ : ℝ≥0∞) := by
    intro m hm
    simpa [t₂] using hτ₂ m hm (rep m) (hrep m hm)
  obtain ⟨tρ₁, htρ₁sub, htρ₁ne, htρ₁sum, htρ₁dyad⟩ :=
    exists_dyadicClass_nonempty (s := tρ) w t₁ (a := δt) (b := ρ) hδt hτ₁rep
  have hτ₂rep₁ : ∀ m ∈ tρ₁, t₂ m ∈ Set.Icc (δt : ℝ≥0∞) (ρ : ℝ≥0∞) :=
    fun m hm => hτ₂rep m (htρ₁sub hm)
  obtain ⟨tρ', htρ'sub₁, htρ'ne₁, htρ'sum, htρ'dyad⟩ :=
    exists_dyadicClass_nonempty (s := tρ₁) w t₂ (a := δt) (b := ρ) hδt hτ₂rep₁
  have htρ'sub : tρ' ⊆ tρ := htρ'sub₁.trans htρ₁sub
  have htρ'ne : tρ.Nonempty → tρ'.Nonempty := fun hne => htρ'ne₁ (htρ₁ne hne)
  have hsum : (∑ m ∈ tρ, w m) ≤ L ^ 2 * (∑ m ∈ tρ', w m) := by
    dsimp [L]
    calc
      (∑ m ∈ tρ, w m)
          ≤ ENNReal.ofReal (1 + Real.logb 2 ((ρ : ℝ) / (δt : ℝ))) * (∑ m ∈ tρ₁, w m) := htρ₁sum
      _ ≤ ENNReal.ofReal (1 + Real.logb 2 ((ρ : ℝ) / (δt : ℝ))) *
            (ENNReal.ofReal (1 + Real.logb 2 ((ρ : ℝ) / (δt : ℝ))) * (∑ m ∈ tρ', w m)) := by
          exact mul_le_mul_right htρ'sum _
      _ = ENNReal.ofReal (1 + Real.logb 2 ((ρ : ℝ) / (δt : ℝ))) ^ 2 * (∑ m ∈ tρ', w m) := by
          rw [← mul_assoc, pow_two]
  rcases tρ'.eq_empty_or_nonempty with htρ'empty | ⟨m₀, hm₀⟩
  · refine ⟨tρ', htρ'sub, htρ'ne, δt, ρ, le_rfl, hδρ, le_rfl, ?_, ?_⟩
    · simpa [htρ'empty] using hsum
    · intro m hm
      simp [htρ'empty] at hm
  · let ap : ℝ≥0 := (t₂ m₀).toNNReal
    let bp : ℝ≥0 := (t₁ m₀).toNNReal
    have hm₀ρ : m₀ ∈ tρ := htρ'sub hm₀
    have hm₀₁ : m₀ ∈ tρ₁ := htρ'sub₁ hm₀
    have ht₂top : t₂ m₀ ≠ ⊤ := by
      exact ne_of_lt (lt_of_le_of_lt (hτ₂rep m₀ hm₀ρ).2 ENNReal.coe_lt_top)
    have ht₁top : t₁ m₀ ≠ ⊤ := by
      exact ne_of_lt (lt_of_le_of_lt (hτ₁rep m₀ hm₀ρ).2 ENNReal.coe_lt_top)
    have ht₂eq : (ap : ℝ≥0∞) = t₂ m₀ := by
      dsimp [ap]
      exact ENNReal.coe_toNNReal ht₂top
    have ht₁eq : (bp : ℝ≥0∞) = t₁ m₀ := by
      dsimp [bp]
      exact ENNReal.coe_toNNReal ht₁top
    have hδap : δt ≤ ap := ENNReal.coe_le_coe.mp (by
      rw [ht₂eq]
      exact (hτ₂rep m₀ hm₀ρ).1)
    have hapbp : ap ≤ bp := ENNReal.coe_le_coe.mp (by
      rw [ht₂eq, ht₁eq]
      dsimp [t₁, t₂]
      exact Metric.ethickness_antitone (by norm_num : (1 : ℕ) ≤ (2 : ℕ)))
    have hbpρ : bp ≤ ρ := ENNReal.coe_le_coe.mp (by
      rw [ht₁eq]
      exact (hτ₁rep m₀ hm₀ρ).2)
    have hplank : ∀ m ∈ tρ', IsPlankFamilyOfDimensions C ap bp (F m).parts
        (fun part => part.convexHull_biUnion V) := by
      intro m hm part hpart
      let W := part.convexHull_biUnion V
      let eth0 : ℝ≥0∞ := Metric.ethickness ℝ W.carrier 0
      let eth1 : ℝ≥0∞ := Metric.ethickness ℝ W.carrier 1
      let eth2 : ℝ≥0∞ := Metric.ethickness ℝ W.carrier 2
      have hmρ : m ∈ tρ := htρ'sub hm
      have hm₁ : m ∈ tρ₁ := htρ'sub₁ hm
      have hτ₀part : (2⁻¹ : ℝ≥0∞) ≤ eth0 ∧ eth0 ≤ 1 := by
        simpa [eth0, W] using (hτ₀ m hmρ part hpart)
      have hsim1_up : eth1 ≤ 2 * t₁ m := by
        dsimp [eth1, W, t₁]
        exact (F m).simDims part hpart (rep m) (hrep m hmρ) 1
      have hsim1_lo : t₁ m ≤ 2 * eth1 := by
        dsimp [eth1, W, t₁]
        exact (F m).simDims (rep m) (hrep m hmρ) part hpart 1
      have hsim2_up : eth2 ≤ 2 * t₂ m := by
        dsimp [eth2, W, t₂]
        exact (F m).simDims part hpart (rep m) (hrep m hmρ) 2
      have hsim2_lo : t₂ m ≤ 2 * eth2 := by
        dsimp [eth2, W, t₂]
        exact (F m).simDims (rep m) (hrep m hmρ) part hpart 2
      have ht₁up : t₁ m ≤ 2 * t₁ m₀ := htρ₁dyad m hm₁ m₀ hm₀₁
      have ht₁lo : t₁ m₀ ≤ 2 * t₁ m := htρ₁dyad m₀ hm₀₁ m hm₁
      have ht₂up : t₂ m ≤ 2 * t₂ m₀ := htρ'dyad m hm m₀ hm₀
      have ht₂lo : t₂ m₀ ≤ 2 * t₂ m := htρ'dyad m₀ hm₀ m hm
      have hC0 : (C : ℝ≥0∞)⁻¹ ≤ eth0 ∧ eth0 ≤ (C : ℝ≥0∞) := by
        constructor
        · have h8C : (8 : ℝ≥0∞) ≤ (C : ℝ≥0∞) := by exact_mod_cast hC
          have hC8 : (C : ℝ≥0∞)⁻¹ ≤ (8 : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.mpr h8C
          have h82 : (8 : ℝ≥0∞)⁻¹ ≤ (2 : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.mpr (by norm_num)
          exact le_trans (le_trans hC8 h82) hτ₀part.1
        · have h1C : (1 : ℝ≥0∞) ≤ (C : ℝ≥0∞) := by
            exact le_trans (by norm_num : (1 : ℝ≥0∞) ≤ (8 : ℝ≥0∞)) (by exact_mod_cast hC)
          exact le_trans hτ₀part.2 h1C
      have hC1 : (C : ℝ≥0∞)⁻¹ * (bp : ℝ≥0∞) ≤ eth1 ∧
          eth1 ≤ (C : ℝ≥0∞) * (bp : ℝ≥0∞) := by
        constructor
        · have hbp4 : (bp : ℝ≥0∞) ≤ 4 * eth1 := by
            calc
              (bp : ℝ≥0∞) = t₁ m₀ := ht₁eq
              _ ≤ 2 * t₁ m := ht₁lo
              _ ≤ 2 * (2 * eth1) := by
                exact mul_le_mul_right hsim1_lo (2 : ℝ≥0∞)
              _ = 4 * eth1 := by rw [← mul_assoc]; norm_num
          have h4inv : (4 : ℝ≥0∞)⁻¹ * (bp : ℝ≥0∞) ≤ eth1 :=
            (ENNReal.inv_mul_le_iff (by norm_num : (4 : ℝ≥0∞) ≠ 0)
              (by exact ENNReal.coe_ne_top : (4 : ℝ≥0∞) ≠ ⊤)).mpr hbp4
          have hC4inv : (C : ℝ≥0∞)⁻¹ ≤ (4 : ℝ≥0∞)⁻¹ := by
            have h4C : (4 : ℝ≥0∞) ≤ (C : ℝ≥0∞) := by
              exact le_trans (by norm_num : (4 : ℝ≥0∞) ≤ (8 : ℝ≥0∞)) (by exact_mod_cast hC)
            exact ENNReal.inv_le_inv.mpr h4C
          exact le_trans (mul_le_mul_left hC4inv (bp : ℝ≥0∞)) h4inv
        · have h4bp : eth1 ≤ 4 * (bp : ℝ≥0∞) := by
            calc
              eth1 ≤ 2 * t₁ m := hsim1_up
              _ ≤ 2 * (2 * t₁ m₀) := by
                exact mul_le_mul_right ht₁up (2 : ℝ≥0∞)
              _ = 4 * t₁ m₀ := by rw [← mul_assoc]; norm_num
              _ = 4 * (bp : ℝ≥0∞) := by rw [ht₁eq]
          have h4C : (4 : ℝ≥0∞) ≤ (C : ℝ≥0∞) := by
            exact le_trans (by norm_num : (4 : ℝ≥0∞) ≤ (8 : ℝ≥0∞)) (by exact_mod_cast hC)
          exact le_trans h4bp (mul_le_mul_left h4C (bp : ℝ≥0∞))
      have hC2 : (C : ℝ≥0∞)⁻¹ * (ap : ℝ≥0∞) ≤ eth2 ∧
          eth2 ≤ (C : ℝ≥0∞) * (ap : ℝ≥0∞) := by
        constructor
        · have hap4 : (ap : ℝ≥0∞) ≤ 4 * eth2 := by
            calc
              (ap : ℝ≥0∞) = t₂ m₀ := ht₂eq
              _ ≤ 2 * t₂ m := ht₂lo
              _ ≤ 2 * (2 * eth2) := by
                exact mul_le_mul_right hsim2_lo (2 : ℝ≥0∞)
              _ = 4 * eth2 := by rw [← mul_assoc]; norm_num
          have h4inv : (4 : ℝ≥0∞)⁻¹ * (ap : ℝ≥0∞) ≤ eth2 :=
            (ENNReal.inv_mul_le_iff (by norm_num : (4 : ℝ≥0∞) ≠ 0)
              (by exact ENNReal.coe_ne_top : (4 : ℝ≥0∞) ≠ ⊤)).mpr hap4
          have hC4inv : (C : ℝ≥0∞)⁻¹ ≤ (4 : ℝ≥0∞)⁻¹ := by
            have h4C : (4 : ℝ≥0∞) ≤ (C : ℝ≥0∞) := by
              exact le_trans (by norm_num : (4 : ℝ≥0∞) ≤ (8 : ℝ≥0∞)) (by exact_mod_cast hC)
            exact ENNReal.inv_le_inv.mpr h4C
          exact le_trans (mul_le_mul_left hC4inv (ap : ℝ≥0∞)) h4inv
        · have h4ap : eth2 ≤ 4 * (ap : ℝ≥0∞) := by
            calc
              eth2 ≤ 2 * t₂ m := hsim2_up
              _ ≤ 2 * (2 * t₂ m₀) := by
                exact mul_le_mul_right ht₂up (2 : ℝ≥0∞)
              _ = 4 * t₂ m₀ := by rw [← mul_assoc]; norm_num
              _ = 4 * (ap : ℝ≥0∞) := by rw [ht₂eq]
          have h4C : (4 : ℝ≥0∞) ≤ (C : ℝ≥0∞) := by
            exact le_trans (by norm_num : (4 : ℝ≥0∞) ≤ (8 : ℝ≥0∞)) (by exact_mod_cast hC)
          exact le_trans h4ap (mul_le_mul_left h4C (ap : ℝ≥0∞))
      exact ⟨hC0, hC1, hC2⟩
    refine ⟨tρ', htρ'sub, htρ'ne, ap, bp, hδap, hapbp, hbpρ, hsum, hplank⟩

/-- **Item (iv) of the plank pigeonhole from item (iii)**.

A plank of dimensions `a × b × 1` with shape constant `C_𝕎` has volume comparable to `a b` with
the *volume* constant `C^vol`.  This is `Kakeya.ml1Boot.volume_bounds_of_isPlankOfDimensions`
at `C := plankPigeonhole.C`, with both sides weakened by
`Kakeya.ml1Boot.plankPigeonhole_volume_constant_bounds`.

No ethickness/affine-thickness translation is needed: `Kakeya.IsPlankOfDimensions` is already
stated in the ethicknesses, which is what the cited volume lemma consumes.  The blueprint
statement carries `0 < a ≤ b ≤ 1`; they are not needed here, so the Lean form is stronger. -/
theorem volume_bounds_of_isPlankOfDimensions_vol (hdim : Module.finrank ℝ E = 3)
    {a b : ℝ≥0} {W : ConvexSpaceBody E}
    (hW : IsPlankOfDimensions plankPigeonhole.C a b W) :
    (plankPigeonhole.C_vol : ℝ≥0∞)⁻¹ * (a : ℝ≥0∞) * (b : ℝ≥0∞) ≤ volume W.carrier ∧
      volume W.carrier
        ≤ (plankPigeonhole.C_vol : ℝ≥0∞) * (a : ℝ≥0∞) * (b : ℝ≥0∞) := by
  have hVge : (1 : ℝ≥0) ≤ Metric.volume_comparison.C 3 := by
    dsimp [Metric.volume_comparison.C, Metric.lt_volume_convexHull.c]
    norm_num
  have hC1 : 1 ≤ plankPigeonhole.C := by
    dsimp [plankPigeonhole.C]
    exact le_trans (by norm_num : (1 : ℝ≥0) ≤ (16 : ℝ≥0))
      (le_mul_of_one_le_right (by norm_num : (0 : ℝ≥0) ≤ 16) hVge)
  have hC0 : plankPigeonhole.C ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hC1)
  have hc3pos : 0 < Metric.lt_volume_convexHull.c 3 := Metric.lt_volume_convexHull.c_pos 3
  have hCvol0 : plankPigeonhole.C_vol ≠ 0 := by
    have hCvolpos : 0 < plankPigeonhole.C_vol := by
      dsimp [plankPigeonhole.C_vol]
      positivity
    exact ne_of_gt hCvolpos
  have hVol :=
    volume_bounds_of_isPlankOfDimensions hdim hC1 (C := plankPigeonhole.C) hW
  obtain ⟨hL, hU⟩ := hVol
  have hcb := plankPigeonhole_volume_constant_bounds hC1
  have hcmulNN : (plankPigeonhole.C : ℝ≥0) ^ 3 ≤
      plankPigeonhole.C_vol * Metric.lt_volume_convexHull.c 3 := by
    have hx : (plankPigeonhole.C : ℝ≥0) ^ 3 / Metric.lt_volume_convexHull.c 3 ≤
        plankPigeonhole.C_vol := by
      simpa [plankPigeonhole.C_vol] using hcb.2
    exact (div_le_iff₀ hc3pos).mp hx
  have hcmulE : (plankPigeonhole.C : ℝ≥0∞) ^ 3 ≤
      (plankPigeonhole.C_vol : ℝ≥0∞) * (Metric.lt_volume_convexHull.c 3 : ℝ≥0∞) := by
    exact_mod_cast hcmulNN
  have hCvolE : (plankPigeonhole.C_vol : ℝ≥0∞) =
      8 * (plankPigeonhole.C : ℝ≥0∞) ^ 3 * (Metric.volume_comparison.C 3 : ℝ≥0∞) := by
    change ((8 * plankPigeonhole.C ^ 3 * Metric.volume_comparison.C 3 : ℝ≥0) : ℝ≥0∞) =
      8 * (plankPigeonhole.C : ℝ≥0∞) ^ 3 * (Metric.volume_comparison.C 3 : ℝ≥0∞)
    simp [ENNReal.coe_mul, ENNReal.coe_pow]
  have hVgeE : (1 : ℝ≥0∞) ≤ (Metric.volume_comparison.C 3 : ℝ≥0∞) := by
    exact_mod_cast hVge
  constructor
  · have hC3E0 : (plankPigeonhole.C : ℝ≥0∞) ^ 3 ≠ 0 := by
      exact pow_ne_zero 3 (by exact_mod_cast hC0)
    have hC3Et : (plankPigeonhole.C : ℝ≥0∞) ^ 3 ≠ ⊤ := by
      exact ENNReal.pow_ne_top ENNReal.coe_ne_top
    have hCvolE0 : (plankPigeonhole.C_vol : ℝ≥0∞) ≠ 0 := by exact_mod_cast hCvol0
    have hCvolEt : (plankPigeonhole.C_vol : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
    have hA : (plankPigeonhole.C_vol : ℝ≥0∞)⁻¹ * (plankPigeonhole.C : ℝ≥0∞) ^ 3 ≤
        (Metric.lt_volume_convexHull.c 3 : ℝ≥0∞) := by
      calc
        (plankPigeonhole.C_vol : ℝ≥0∞)⁻¹ * (plankPigeonhole.C : ℝ≥0∞) ^ 3
            ≤ (plankPigeonhole.C_vol : ℝ≥0∞)⁻¹ *
                ((plankPigeonhole.C_vol : ℝ≥0∞) *
                  (Metric.lt_volume_convexHull.c 3 : ℝ≥0∞)) := by
              exact mul_le_mul_right hcmulE (plankPigeonhole.C_vol : ℝ≥0∞)⁻¹
        _ = (Metric.lt_volume_convexHull.c 3 : ℝ≥0∞) := by
          rw [← mul_assoc]
          rw [ENNReal.inv_mul_cancel hCvolE0 hCvolEt]
          rw [one_mul]
    have hinv : (plankPigeonhole.C_vol : ℝ≥0∞)⁻¹ ≤
        ((plankPigeonhole.C : ℝ≥0∞) ^ 3)⁻¹ *
          (Metric.lt_volume_convexHull.c 3 : ℝ≥0∞) := by
      calc
        (plankPigeonhole.C_vol : ℝ≥0∞)⁻¹
            = (plankPigeonhole.C_vol : ℝ≥0∞)⁻¹ * 1 := (mul_one _).symm
        _ = (plankPigeonhole.C_vol : ℝ≥0∞)⁻¹ *
              ((plankPigeonhole.C : ℝ≥0∞) ^ 3 *
                ((plankPigeonhole.C : ℝ≥0∞) ^ 3)⁻¹) := by
              rw [ENNReal.mul_inv_cancel hC3E0 hC3Et]
        _ = ((plankPigeonhole.C_vol : ℝ≥0∞)⁻¹ * (plankPigeonhole.C : ℝ≥0∞) ^ 3) *
              ((plankPigeonhole.C : ℝ≥0∞) ^ 3)⁻¹ := by
              rw [← mul_assoc]
        _ ≤ (Metric.lt_volume_convexHull.c 3 : ℝ≥0∞) *
              ((plankPigeonhole.C : ℝ≥0∞) ^ 3)⁻¹ := by
              exact mul_le_mul_left hA ((plankPigeonhole.C : ℝ≥0∞) ^ 3)⁻¹
        _ = ((plankPigeonhole.C : ℝ≥0∞) ^ 3)⁻¹ *
              (Metric.lt_volume_convexHull.c 3 : ℝ≥0∞) := by
              rw [mul_comm]
    calc
      (plankPigeonhole.C_vol : ℝ≥0∞)⁻¹ * (a : ℝ≥0∞) * (b : ℝ≥0∞)
          = (plankPigeonhole.C_vol : ℝ≥0∞)⁻¹ * ((a : ℝ≥0∞) * (b : ℝ≥0∞)) := by
            rw [mul_assoc]
      _ ≤ ((plankPigeonhole.C : ℝ≥0∞) ^ 3)⁻¹ * (Metric.lt_volume_convexHull.c 3 : ℝ≥0∞) *
              ((a : ℝ≥0∞) * (b : ℝ≥0∞)) := by
            exact mul_le_mul_left hinv ((a : ℝ≥0∞) * (b : ℝ≥0∞))
      _ ≤ volume W.carrier := hL
  · calc
      volume W.carrier
          ≤ 8 * (plankPigeonhole.C : ℝ≥0∞) ^ 3 * ((a : ℝ≥0∞) * (b : ℝ≥0∞)) := hU
      _ ≤ 8 * (plankPigeonhole.C : ℝ≥0∞) ^ 3 * (Metric.volume_comparison.C 3 : ℝ≥0∞) *
              ((a : ℝ≥0∞) * (b : ℝ≥0∞)) := by
            have hb : 8 * (plankPigeonhole.C : ℝ≥0∞) ^ 3 ≤
                8 * (plankPigeonhole.C : ℝ≥0∞) ^ 3 *
                  (Metric.volume_comparison.C 3 : ℝ≥0∞) :=
              le_mul_of_one_le_right (by positivity : 0 ≤ 8 * (plankPigeonhole.C : ℝ≥0∞) ^ 3)
                hVgeE
            exact mul_le_mul_left hb ((a : ℝ≥0∞) * (b : ℝ≥0∞))
      _ ≤ (plankPigeonhole.C_vol : ℝ≥0∞) * ((a : ℝ≥0∞) * (b : ℝ≥0∞)) := by
        rw [hCvolE]
      _ = (plankPigeonhole.C_vol : ℝ≥0∞) * (a : ℝ≥0∞) * (b : ℝ≥0∞) := by
        rw [← mul_assoc]

/-- **The two pigeonhole losses, as a single polylogarithm**.

`ConvexSpaceBody.nonempty_factorization.C 3 n δ̃` is the loss `L_{3,n,δ̃}` of the weighted
factorization lemma, and `(1 + log₂ (ρ / δ̃)) ^ 2` the loss of the cross-parent pigeonhole
`Kakeya.ml1Boot.exists_commonPlankDims`.  Their product is a single polylogarithm of degree
`6` times a constant fixed before `δ̃`.  No filter occurs. -/
theorem plankPigeonhole_loss_le_polylog {Ccard : ℝ≥0} (hCcard : 1 ≤ Ccard)
    {δt ρ : ℝ≥0} (hδt0 : 0 < δt) (hδt1 : δt ≤ 1) (hδρ : δt ≤ ρ) (hρ1 : ρ ≤ 1)
    {n : ℕ} (hn1 : 1 ≤ n) (hn : (n : ℝ) ≤ (Ccard : ℝ) * (δt : ℝ) ^ (-4 : ℝ)) :
    ConvexSpaceBody.nonempty_factorization.C 3 n δt
        * ENNReal.ofReal (1 + Real.logb 2 ((ρ : ℝ) / (δt : ℝ))) ^ 2
      ≤ ENNReal.ofReal (4 * (1 + Real.logb 2 (Ccard : ℝ)))
          * ENNReal.ofReal (1 + Real.logb 2 (1 / (δt : ℝ))) ^ 6 := by
  -- `x := log₂ (1/δ̃) ≥ 0` is the polylogarithm base; `c := log₂ Ccard ≥ 0`.
  let x : ℝ := Real.logb 2 (1 / (δt : ℝ))
  have hδtpos : (0 : ℝ) < (δt : ℝ) := by exact_mod_cast hδt0
  have h1_δ : (1 : ℝ) ≤ 1 / (δt : ℝ) := by
    exact (one_le_div hδtpos).mpr (by exact_mod_cast hδt1)
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) h1_δ
  -- ρ/δ̃ ∈ [1, 1/δ̃], so log₂ (ρ/δ̃) ∈ [0, x]
  have hδinv0 : 0 ≤ (δt : ℝ)⁻¹ := inv_nonneg.mpr hδtpos.le
  have hρδ_le : (ρ : ℝ) / (δt : ℝ) ≤ 1 / (δt : ℝ) := by
    have hmρ : (ρ : ℝ) * (δt : ℝ)⁻¹ ≤ (1 : ℝ) * (δt : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hρ1) hδinv0
    calc
      (ρ : ℝ) / (δt : ℝ) = (ρ : ℝ) * (δt : ℝ)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ (1 : ℝ) * (δt : ℝ)⁻¹ := hmρ
      _ = 1 / (δt : ℝ) := by rw [div_eq_mul_inv]
  have hρδ_1 : (1 : ℝ) ≤ (ρ : ℝ) / (δt : ℝ) := by
    exact (one_le_div hδtpos).mpr (by exact_mod_cast hδρ)
  have hρpos : (0 : ℝ) < (ρ : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le hδt0 hδρ)
  have hρδ_pos : (0 : ℝ) < (ρ : ℝ) / (δt : ℝ) := div_pos hρpos hδtpos
  have hlogρδ : Real.logb 2 ((ρ : ℝ) / (δt : ℝ)) ≤ x := by
    simpa [x] using
      Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hρδ_pos hρδ_le
  have hB2 : ENNReal.ofReal (1 + Real.logb 2 ((ρ : ℝ) / (δt : ℝ))) ^ 2 ≤
      ENNReal.ofReal (1 + x) ^ 2 := by
    exact pow_le_pow_left₀ zero_le
      (ENNReal.ofReal_le_ofReal (by linarith)) 2
  -- the `n` factor: 1 + log₂ n ≤ 4 (1 + c) (1 + x)
  let c : ℝ := Real.logb 2 (Ccard : ℝ)
  have hc0 : 0 ≤ c := by
    dsimp [c]
    exact Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (by exact_mod_cast hCcard)
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hn1)
  have hlogbδ : Real.logb 2 (δt : ℝ) = -Real.logb 2 (1 / (δt : ℝ)) := by
    rw [one_div, Real.logb_inv]
    ring
  have hlogδ4 : Real.logb 2 ((δt : ℝ) ^ (-4 : ℝ)) = 4 * x := by
    calc
      Real.logb 2 ((δt : ℝ) ^ (-4 : ℝ)) = (-4 : ℝ) * Real.logb 2 (δt : ℝ) := by
        rw [Real.logb_rpow_eq_mul_logb_of_pos hδtpos]
      _ = 4 * x := by
        rw [hlogbδ]
        dsimp [x]
        ring
  have hδ4pos : (0 : ℝ) < (δt : ℝ) ^ (-4 : ℝ) := Real.rpow_pos_of_pos hδtpos (-4 : ℝ)
  have hδ4ne : (δt : ℝ) ^ (-4 : ℝ) ≠ 0 := ne_of_gt hδ4pos
  have hCpos : (0 : ℝ) < (Ccard : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 1) hCcard)
  have hlogb_n : Real.logb 2 (n : ℝ) ≤ c + 4 * x := by
    calc
      Real.logb 2 (n : ℝ) ≤ Real.logb 2 ((Ccard : ℝ) * (δt : ℝ) ^ (-4 : ℝ)) := by
        exact Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hnpos
          (by exact hn)
      _ = Real.logb 2 (Ccard : ℝ) + Real.logb 2 ((δt : ℝ) ^ (-4 : ℝ)) := by
        rw [Real.logb_mul (ne_of_gt hCpos) hδ4ne]
      _ = c + 4 * x := by
        dsimp [c]
        rw [hlogδ4]
  have hpoly : (1 : ℝ) + Real.logb 2 (n : ℝ) ≤ (4 * (1 + c)) * (1 + x) := by
    calc
      1 + Real.logb 2 (n : ℝ) ≤ 1 + (c + 4 * x) := by linarith
      _ ≤ (1 + c) * (1 + 4 * x) := by
        have hcx : 0 ≤ c * x := mul_nonneg hc0 hx0
        nlinarith
      _ ≤ (1 + c) * (4 * (1 + x)) := by
        have h14 : 1 + 4 * x ≤ 4 * (1 + x) := by nlinarith
        have h1c : (0 : ℝ) ≤ 1 + c := by nlinarith
        exact mul_le_mul_of_nonneg_left h14 h1c
      _ = 4 * (1 + c) * (1 + x) := by ring
  -- push the real bounds through `ENNReal.ofReal`
  have hEn : ENNReal.ofReal (1 + Real.logb 2 ((n : ℝ) / 1)) ≤
      ENNReal.ofReal (4 * (1 + c)) * ENNReal.ofReal (1 + x) := by
    calc
      ENNReal.ofReal (1 + Real.logb 2 ((n : ℝ) / 1)) ≤
          ENNReal.ofReal ((4 * (1 + c)) * (1 + x)) := by
        apply ENNReal.ofReal_le_ofReal
        rwa [div_one]
      _ = ENNReal.ofReal (4 * (1 + c)) * ENNReal.ofReal (1 + x) := by
        exact ENNReal.ofReal_mul (by nlinarith [hc0] : 0 ≤ 4 * (1 + c))
  calc
    ConvexSpaceBody.nonempty_factorization.C 3 n δt
        * ENNReal.ofReal (1 + Real.logb 2 ((ρ : ℝ) / (δt : ℝ))) ^ 2
        = ENNReal.ofReal (1 + Real.logb 2 ((n : ℝ) / 1)) * ENNReal.ofReal (1 + x) ^ 3 *
            ENNReal.ofReal (1 + Real.logb 2 ((ρ : ℝ) / (δt : ℝ))) ^ 2 := by
          unfold ConvexSpaceBody.nonempty_factorization.C
          dsimp [x]
    _ ≤ ENNReal.ofReal (1 + Real.logb 2 ((n : ℝ) / 1)) *
          ENNReal.ofReal (1 + x) ^ 3 * ENNReal.ofReal (1 + x) ^ 2 := by
        gcongr
    _ ≤ (ENNReal.ofReal (4 * (1 + c)) * ENNReal.ofReal (1 + x)) *
          ENNReal.ofReal (1 + x) ^ 3 * ENNReal.ofReal (1 + x) ^ 2 := by
        gcongr
    _ = ENNReal.ofReal (4 * (1 + c)) * ENNReal.ofReal (1 + x) ^ 6 := by
        ring
    _ = ENNReal.ofReal (4 * (1 + Real.logb 2 (Ccard : ℝ))) *
          ENNReal.ofReal (1 + Real.logb 2 (1 / (δt : ℝ))) ^ 6 := by
        simp [c, x]

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Ethickness ranges of a plank spanned by `δ̃`-tubes**.

Six inequalities, each a containment followed by `Metric.ethickness_monotone`.  The lower bounds
come from a single contained `δ̃`-tube through `Kakeya.ml1Boot.tube_ethickness_bounds`; the
`τ₀` upper bound from `W ⊆ B₁` through `Metric.ethickness_le_of_subset_closedBall`, and the
`τ₁, τ₂` upper bounds from `W ⊆ T_ρ` through the same tube lemma applied to `T_ρ`.

These are exactly the three range hypotheses of
`Kakeya.ml1Boot.exists_commonPlankDims`, which is why they are proved here. -/
theorem ethickness_bounds_convexHull_tubes (hdim : Module.finrank ℝ E = 3)
    {δt ρ : ℝ≥0} (_hδt0 : 0 < δt) (_hδρ : δt ≤ ρ) (_hρ1 : ρ ≤ 1)
    {ι : Type*} {t : Finset ι} (ht : t.Nonempty)
    (T : ι → Tube δt E) (Tρ : Tube ρ E)
    (hball : ∀ i ∈ t, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hsub : ∀ i ∈ t, (T i).carrier ⊆ Tρ.carrier) :
    Metric.ethickness ℝ
          (t.convexHull_biUnion fun i => (T i).toConvexSpaceBody).carrier 0 ∈
        Set.Icc (2⁻¹ : ℝ≥0∞) 1 ∧
      Metric.ethickness ℝ
            (t.convexHull_biUnion fun i => (T i).toConvexSpaceBody).carrier 1 ∈
          Set.Icc (δt : ℝ≥0∞) (ρ : ℝ≥0∞) ∧
        Metric.ethickness ℝ
              (t.convexHull_biUnion fun i => (T i).toConvexSpaceBody).carrier 2 ∈
            Set.Icc (δt : ℝ≥0∞) (ρ : ℝ≥0∞) := by
  classical
  let W : ConvexSpaceBody E := t.convexHull_biUnion fun i => (T i).toConvexSpaceBody
  have hn : 2 ≤ Module.finrank ℝ E := by
    omega
  have hk1 : (1 : ℕ) ≤ Module.finrank ℝ E - 1 := by
    omega
  have hk2 : (2 : ℕ) ≤ Module.finrank ℝ E - 1 := by
    omega
  have hmem : ∀ i : ι, i ∈ t → (T i).carrier ⊆ W.carrier := by
    intro i hi
    dsimp [W]
    rw [Finset.Nonempty.convexHull_biUnion_carrier ht]
    exact fun x hx =>
      Convexity.subset_convexHull_self (Set.subset_biUnion_of_mem hi hx)
  have hWsub : W.carrier ⊆ Tρ.carrier := by
    dsimp [W]
    rw [Finset.Nonempty.convexHull_biUnion_subset_iff ht
      (fun i => (T i).toConvexSpaceBody) Tρ.convex']
    intro i hi
    exact hsub i hi
  have hWball : W.carrier ⊆ Metric.closedBall (0 : E) 1 := by
    dsimp [W]
    rw [Finset.Nonempty.convexHull_biUnion_subset_iff ht
      (fun i => (T i).toConvexSpaceBody) (convex_closedBall 0 1).isConvexSet]
    intro i hi
    exact hball i hi
  have h0up : Metric.ethickness ℝ W.carrier 0 ≤ (1 : ℝ≥0∞) := by
    exact Metric.ethickness_le_of_subset_closedBall (x := (0 : E)) 1 hWball 0
  have h1up : Metric.ethickness ℝ W.carrier 1 ≤ (ρ : ℝ≥0∞) := by
    exact (Metric.ethickness_monotone hWsub 1).trans
      (le_of_eq ((tube_ethickness_bounds hn Tρ).2.2 1 (by norm_num) hk1))
  have h2up : Metric.ethickness ℝ W.carrier 2 ≤ (ρ : ℝ≥0∞) := by
    exact (Metric.ethickness_monotone hWsub 2).trans
      (le_of_eq ((tube_ethickness_bounds hn Tρ).2.2 2 (by norm_num) hk2))
  obtain ⟨i, hi⟩ := ht
  have h0lo0 : (2⁻¹ : ℝ≥0∞) ≤ Metric.ethickness ℝ (T i).carrier 0 := by
    simpa using (tube_ethickness_bounds hn (T i)).1
  have h0lo : (2⁻¹ : ℝ≥0∞) ≤ Metric.ethickness ℝ W.carrier 0 := by
    exact h0lo0.trans (Metric.ethickness_monotone (hmem i hi) 0)
  have h1lo : (δt : ℝ≥0∞) ≤ Metric.ethickness ℝ W.carrier 1 := by
    calc
      (δt : ℝ≥0∞) = Metric.ethickness ℝ (T i).carrier 1 :=
        ((tube_ethickness_bounds hn (T i)).2.2 1 (by norm_num) hk1).symm
      _ ≤ Metric.ethickness ℝ W.carrier 1 := Metric.ethickness_monotone (hmem i hi) 1
  have h2lo : (δt : ℝ≥0∞) ≤ Metric.ethickness ℝ W.carrier 2 := by
    calc
      (δt : ℝ≥0∞) = Metric.ethickness ℝ (T i).carrier 2 :=
        ((tube_ethickness_bounds hn (T i)).2.2 2 (by norm_num) hk2).symm
      _ ≤ Metric.ethickness ℝ W.carrier 2 := Metric.ethickness_monotone (hmem i hi) 2
  exact ⟨⟨h0lo, h0up⟩, ⟨⟨h1lo, h1up⟩, ⟨h2lo, h2up⟩⟩⟩

/-- **Gluing the per-parent subfamilies into one index set**.

Each block `um m` lies in the fibre over `m`, so the blocks lie in distinct fibres of `pρ` and
cutting the union down to the fibre over `m` returns `um m` when `m ∈ tρ'` and nothing
otherwise.  This is what makes discarding the parents outside `tρ'` harmless: it deletes only
whole fibres, so the factorizations over the surviving parents are untouched, and items (iii)
and (iv) of `Kakeya.ml1Boot.exists_plankDimensions` become statements about an empty set of
parts over a discarded parent. -/
theorem fibre_biUnion_eq {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {u : Finset ι} {tρ tρ' : Finset κ} (htρ' : tρ' ⊆ tρ) (pρ : ι → κ)
    (um : κ → Finset ι) (hum : ∀ m ∈ tρ, um m ⊆ fibre u pρ m) :
    (∀ m ∈ tρ', fibre (tρ'.biUnion um) pρ m = um m) ∧
      ∀ m ∈ tρ, m ∉ tρ' → fibre (tρ'.biUnion um) pρ m = ∅ := by
  constructor
  · intro m hmtρ'
    ext i
    constructor
    · intro hi
      rw [fibre] at hi
      rw [Finset.mem_filter] at hi
      rcases hi with ⟨hbi, hpi⟩
      rw [Finset.mem_biUnion] at hbi
      rcases hbi with ⟨m', hm', him'⟩
      have hfib' : i ∈ u.filter (fun j => pρ j = m') := hum m' (htρ' hm') him'
      have hpm' : pρ i = m' := (Finset.mem_filter.mp hfib').2
      have hm'eq : m' = m := hpm'.symm.trans hpi
      rw [hm'eq] at him'
      exact him'
    · intro him
      have hfib : i ∈ u.filter (fun j => pρ j = m) := hum m (htρ' hmtρ') him
      have hpm : pρ i = m := (Finset.mem_filter.mp hfib).2
      rw [fibre]
      rw [Finset.mem_filter]
      rw [Finset.mem_biUnion]
      exact ⟨⟨m, hmtρ', him⟩, hpm⟩
  · intro m hmtρ hmn
    rw [Finset.eq_empty_iff_forall_notMem]
    intro i hi
    rw [fibre] at hi
    rw [Finset.mem_filter] at hi
    rcases hi with ⟨hbi, hpi⟩
    rw [Finset.mem_biUnion] at hbi
    rcases hbi with ⟨m', hm', him'⟩
    have hfib' : i ∈ u.filter (fun p => pρ p = m') := hum m' (htρ' hm') him'
    have hpm' : pρ i = m' := (Finset.mem_filter.mp hfib').2
    have hm'eq : m' = m := hpm'.symm.trans hpi
    exact hmn (by simpa [hm'eq] using hm')

/-- The empty factorization.  `ConvexSpaceBody.Factorization` extends `Finpartition`, and
`Finpartition.empty` partitions `⊥ = (∅ : Finset ι)` with no parts, so the two quantified fields
`maxDensity_le_mul` and `simDims` are vacuous and `isKatzTao` is `maxDensity ∅ _ ≤ C`.

Stated as an existence statement rather than a `def` so that its `parts` are pinned down by a
theorem.  It is what supplies a factorization over a parent whose fibre has been emptied. -/
theorem exists_emptyFactorization {ι : Type*} [DecidableEq ι]
    (V : ι → ConvexSpaceBody E) (C : ℝ≥0) :
    ∃ F : ConvexSpaceBody.Factorization (∅ : Finset ι) V C, F.parts = ∅ := by
  let P : Finpartition (∅ : Finset ι) := Finpartition.empty (α := Finset ι)
  let F : ConvexSpaceBody.Factorization (∅ : Finset ι) V C :=
    ⟨P, by simp [IsKatzTao, P], by simp [P], by simp [P]⟩
  exact ⟨F, rfl⟩

/-- Transport of a factorization along an equality of the index set, with its parts unchanged.

Needed twice in `Kakeya.ml1Boot.exists_plankDimensions_geom`: the factorizations come indexed by
the blocks `um m`, whereas `Kakeya.ml1Boot.exists_commonPlankDims` and the conclusion of the plank
pigeonhole index them by the fibres `fibre (tρ.biUnion um) pρ m` and
`fibre (tρ'.biUnion um) pρ m`, which are the same `Finset`s but not syntactically. -/
theorem exists_factorizationCopy {ι : Type*} [DecidableEq ι] {V : ι → ConvexSpaceBody E}
    {C : ℝ≥0} {s s' : Finset ι} (F : ConvexSpaceBody.Factorization s V C) (h : s = s') :
    ∃ F' : ConvexSpaceBody.Factorization s' V C, F'.parts = F.parts := by
  subst h
  exact ⟨F, rfl⟩

omit [BorelSpace E] in
/-- The three thickness ranges over a single part of a single parent (blueprint
`lem:ml1bootPlankEthicknessRanges`, specialised to a part of the factorization of a fibre).

`Kakeya.ml1Boot.ethickness_bounds_convexHull_tubes` applied to the tubes indexed by `part`, whose
containment in the parent tube `Tρ m` is `Kakeya.ml1Boot.IsParentFamily.le_parent` read at the
fixed parent `m`, using that `pρ i = m` for every `i` in a fibre over `m`. -/
private lemma perParent_ethickness_ranges (hdim : Module.finrank ℝ E = 3)
    {δt ρ : ℝ≥0} (hδt : 0 < δt) (hδρ : δt ≤ ρ) (hρ1 : ρ ≤ 1)
    {ι κ : Type*} [DecidableEq κ] {u : Finset ι} {tρ : Finset κ}
    (T : ι → ShadedTube δt E) (Tρ : κ → Tube ρ E) (pρ : ι → κ)
    (hball : ∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hparent : IsParentFamily u (fun i => (T i).toTube) tρ Tρ pρ)
    {m : κ} {part : Finset ι} (hpart : part ⊆ fibre u pρ m) (hne : part.Nonempty) :
    Metric.ethickness ℝ
          (part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)).carrier 0
        ∈ Set.Icc (2⁻¹ : ℝ≥0∞) 1 ∧
      Metric.ethickness ℝ
            (part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)).carrier 1
          ∈ Set.Icc (δt : ℝ≥0∞) (ρ : ℝ≥0∞) ∧
        Metric.ethickness ℝ
              (part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)).carrier 2
            ∈ Set.Icc (δt : ℝ≥0∞) (ρ : ℝ≥0∞) := by
  classical
  exact ethickness_bounds_convexHull_tubes hdim hδt hδρ hρ1 hne
      (fun i => (T i).toTube) (Tρ m) (by
        intro i hi
        exact hball i ((Finset.mem_filter.mp (hpart hi)).1)) (by
        intro i hi
        have hpm : pρ i = m := (Finset.mem_filter.mp (hpart hi)).2
        have hle : (T i).toTube.toConvexSpaceBody ≤ (Tρ (pρ i)).toConvexSpaceBody :=
          hparent.le_parent i ((Finset.mem_filter.mp (hpart hi)).1)
        rw [hpm] at hle
        exact SetLike.coe_subset_coe.mpr hle)

/-- The weighted maximal-density factorization of the fibre over a single parent: the application
of `ConvexSpaceBody.nonempty_factorization.factorization_weighted` with the shading masses
`|Ỹ i|` as the weight, which is what makes the retained block heavy in shading rather than merely
in body volume.

Its `δ̃ ≤ ethickness.scale` hypothesis is `Tube.le_ethickness_scale`, and its unit-ball hypothesis
is `hball` restricted along `fibre u pρ m ⊆ u`. -/
private lemma exists_fibreFactorization (hdim : Module.finrank ℝ E = 3) {δt : ℝ≥0}
    (hδt : 0 < δt) {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u : Finset ι}
    (T : ι → ShadedTube δt E) (pρ : ι → κ)
    (hball : ∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall 0 1)
    {m : κ} (hne : (fibre u pρ m).Nonempty) :
    ∃ s' ⊆ fibre u pρ m, s'.Nonempty ∧
      ∑ i ∈ fibre u pρ m, volume ((T i).toShadedBody).shade
          ≤ ConvexSpaceBody.nonempty_factorization.C 3 (fibre u pρ m).card δt
            * ∑ i ∈ s', volume ((T i).toShadedBody).shade ∧
        ∃ F : ConvexSpaceBody.Factorization s' (fun i => (T i).toConvexSpaceBody) 2,
          F.parts.Nonempty := by
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (by rw [hdim]; norm_num)
  let s : Finset ι := fibre u pρ m
  let V : ι → ConvexSpaceBody E := fun i => (T i).toConvexSpaceBody
  let w : ι → ℝ≥0∞ := fun i => volume ((T i).toShadedBody).shade
  have hs1 : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1 := by
    intro i hi
    have hif : i ∈ fibre u pρ m := by simpa [s] using hi
    rw [fibre] at hif
    have hiu : i ∈ u := (Finset.mem_filter.mp hif).1
    simpa [V] using hball i hiu
  have hs2 : ∀ i ∈ s, δt ≤ Metric.ethickness.scale ℝ (V i).carrier := by
    intro i hi
    simpa [V] using Tube.le_ethickness_scale (T i).toTube
  rcases ConvexSpaceBody.nonempty_factorization.factorization_weighted
      (s := s) (V := V) (δ := δt) (w := w) hδt hne hs1 hs2 with
    ⟨s', hsub, hne', hsum, F, hFne⟩
  refine ⟨s', hsub, hne', ?_, F, hFne⟩
  rw [hdim] at hsum
  simpa [s, V, w] using hsum

/-- ** The factorization over a single parent,
with the three thickness ranges**, gathered over all parents at once.

The proof applies the *weighted* factorization lemma
`ConvexSpaceBody.nonempty_factorization.factorization_weighted` to the fibre over each parent, with
the weight `w i = |Ỹ i|`; this is `Kakeya.ml1Boot.exists_fibreFactorization`.  It is essential that
the weighted form is cited and not
`ConvexSpaceBody.nonempty_factorization.weight_subfamily`, whose heavy-subfamily bound is on the
*body* volumes `volume (V i).carrier`: for a family of `δ̃`-tubes those volumes are all equal, so
that bound degenerates to a statement about cardinality and says nothing about where the shading
sits, hence cannot produce the shading-mass loss required below.  The three thickness ranges over a
part are `Kakeya.ml1Boot.perParent_ethickness_ranges`, and everything else here is the gathering of
the per-parent statements into total functions.

Two differences from the blueprint statement, both bookkeeping.  First, the blueprint fixes one
parent `m ∈ t_ρ` and returns a nonempty `u_m` with a factorization of it; here the conclusion is
gathered into total functions `um : κ → Finset ι` and
`F : (m : κ) → ConvexSpaceBody.Factorization (um m) _ 2`, because
`Kakeya.ml1Boot.exists_commonPlankDims` consumes a factorization for *every* `m : κ` and gathering
the per-parent statements would need choice at the type level.  Off `t_ρ` nothing is asserted, so
`um m = ∅` with the empty factorization there.  Second, nonemptiness of `u_m` is recorded in the
form actually used, namely `(F m).parts.Nonempty`, which is what supplies the representative part
of `Kakeya.ml1Boot.exists_commonPlankDims`. -/
theorem exists_perParentFactorization (hdim : Module.finrank ℝ E = 3)
    {δt ρ : ℝ≥0} (hδt : 0 < δt) (_hδt2 : δt ≤ 2⁻¹) (hδρ : δt ≤ ρ) (hρ1 : ρ ≤ 1)
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u : Finset ι} {tρ : Finset κ}
    (T : ι → ShadedTube δt E) (Tρ : κ → Tube ρ E) (pρ : ι → κ)
    (hball : ∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hparent : IsParentFamily u (fun i => (T i).toTube) tρ Tρ pρ)
    (hsurj : Set.SurjOn pρ u tρ) :
    ∃ um : κ → Finset ι, (∀ m ∈ tρ, um m ⊆ fibre u pρ m) ∧
      ∃ F : (m : κ) → ConvexSpaceBody.Factorization (um m)
          (fun i => (T i).toConvexSpaceBody) 2,
        (∀ m ∈ tρ, (F m).parts.Nonempty) ∧
          (∀ m ∈ tρ, ∑ i ∈ fibre u pρ m, volume ((T i).toShadedBody).shade
              ≤ ConvexSpaceBody.nonempty_factorization.C 3 (fibre u pρ m).card δt
                * ∑ i ∈ um m, volume ((T i).toShadedBody).shade) ∧
            ∀ m ∈ tρ, ∀ part ∈ (F m).parts,
              Metric.ethickness ℝ (part.convexHull_biUnion
                    (fun i => (T i).toConvexSpaceBody)).carrier 0
                  ∈ Set.Icc (2⁻¹ : ℝ≥0∞) 1 ∧
                Metric.ethickness ℝ (part.convexHull_biUnion
                      (fun i => (T i).toConvexSpaceBody)).carrier 1
                    ∈ Set.Icc (δt : ℝ≥0∞) (ρ : ℝ≥0∞) ∧
                  Metric.ethickness ℝ (part.convexHull_biUnion
                        (fun i => (T i).toConvexSpaceBody)).carrier 2
                      ∈ Set.Icc (δt : ℝ≥0∞) (ρ : ℝ≥0∞) := by
  classical
  have hfib : ∀ m ∈ tρ, (fibre u pρ m).Nonempty := by
    intro m hm
    obtain ⟨i, hiu, hpi⟩ := hsurj hm
    exact ⟨i, by rw [fibre]; exact Finset.mem_filter.mpr ⟨hiu, hpi⟩⟩
  have key : ∀ m ∈ tρ,
      ∃ s' ⊆ fibre u pρ m, s'.Nonempty ∧
        (∑ i ∈ fibre u pρ m, volume ((T i).toShadedBody).shade
          ≤ ConvexSpaceBody.nonempty_factorization.C 3 (fibre u pρ m).card δt
            * ∑ i ∈ s', volume ((T i).toShadedBody).shade) ∧
          ∃ F : ConvexSpaceBody.Factorization s' (fun i => (T i).toConvexSpaceBody) 2,
            F.parts.Nonempty :=
    fun m hm => exists_fibreFactorization hdim hδt T pρ hball (hfib m hm)
  obtain ⟨E0, _hE0⟩ := exists_emptyFactorization
    (V := fun i => (T i).toConvexSpaceBody) 2
  let um : κ → Finset ι := fun m => if h : m ∈ tρ then (key m h).choose else ∅
  let F : (m : κ) → ConvexSpaceBody.Factorization (um m) (fun i => (T i).toConvexSpaceBody) 2 :=
    fun m => if h : m ∈ tρ then
        (exists_factorizationCopy ((key m h).choose_spec.2.2.2).choose (by simp [um, h])).choose
      else (exists_factorizationCopy E0 (by simp [um, h])).choose
  have hum : ∀ m ∈ tρ, um m ⊆ fibre u pρ m := by
    intro m hm
    dsimp [um]
    rw [dif_pos hm]
    exact (key m hm).choose_spec.1
  have hon : ∀ m : κ, ∀ h : m ∈ tρ, (F m).parts = (((key m h).choose_spec.2.2.2).choose).parts := by
    intro m hm
    dsimp [F]
    rw [dif_pos hm]
    exact (exists_factorizationCopy ((key m hm).choose_spec.2.2.2).choose
      (by simp [um, hm])).choose_spec
  have hFne : ∀ m ∈ tρ, (F m).parts.Nonempty := by
    intro m hm
    rw [hon m hm]
    exact ((key m hm).choose_spec.2.2.2).choose_spec
  have hsum : ∀ m ∈ tρ,
      (∑ i ∈ fibre u pρ m, volume ((T i).toShadedBody).shade
        ≤ ConvexSpaceBody.nonempty_factorization.C 3 (fibre u pρ m).card δt
          * ∑ i ∈ um m, volume ((T i).toShadedBody).shade) := by
    intro m hm
    dsimp [um]
    rw [dif_pos hm]
    exact (key m hm).choose_spec.2.2.1
  have hper : ∀ m ∈ tρ, ∀ part ∈ (F m).parts,
      Metric.ethickness ℝ (part.convexHull_biUnion
            (fun i => (T i).toConvexSpaceBody)).carrier 0
          ∈ Set.Icc (2⁻¹ : ℝ≥0∞) 1 ∧
        Metric.ethickness ℝ (part.convexHull_biUnion
              (fun i => (T i).toConvexSpaceBody)).carrier 1
            ∈ Set.Icc (δt : ℝ≥0∞) (ρ : ℝ≥0∞) ∧
          Metric.ethickness ℝ (part.convexHull_biUnion
                (fun i => (T i).toConvexSpaceBody)).carrier 2
              ∈ Set.Icc (δt : ℝ≥0∞) (ρ : ℝ≥0∞) := by
    intro m hm part hpart
    have partNe : part.Nonempty := (F m).nonempty_of_mem_parts hpart
    have partSub : part ⊆ um m := (F m).toFinpartition.subset hpart
    have hmsub : part ⊆ fibre u pρ m := by
      intro i hi
      exact hum m hm (partSub hi)
    exact perParent_ethickness_ranges hdim hδt hδρ hρ1 T Tρ pρ hball hparent hmsub partNe
  exact ⟨um, hum, F, hFne, hsum, hper⟩

/-- The companion of `Kakeya.ml1Boot.fibre_biUnion_eq` outside the parent set: a glued index set
has an empty fibre over any `m` which is not a parent at all, because each block lies in a fibre
over a genuine parent. -/
theorem fibre_biUnion_eq_empty_of_notMem {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {u : Finset ι} {tρ tρ' : Finset κ} (htρ' : tρ' ⊆ tρ) (pρ : ι → κ) (um : κ → Finset ι)
    (hum : ∀ m ∈ tρ, um m ⊆ fibre u pρ m) {m : κ} (hm : m ∉ tρ) :
    fibre (tρ'.biUnion um) pρ m = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro i hi
  rw [fibre] at hi
  rw [Finset.mem_filter] at hi
  rcases hi with ⟨hbi, hpi⟩
  rw [Finset.mem_biUnion] at hbi
  rcases hbi with ⟨m', hm', him'⟩
  have hfib' : i ∈ u.filter (fun p => pρ p = m') := hum m' (htρ' hm') him'
  have hpm' : pρ i = m' := (Finset.mem_filter.mp hfib').2
  have hm'eq : m' = m := hpm'.symm.trans hpi
  exact hm (by simpa [hm'eq] using htρ' hm')

/-! ### Can the plank conclusion be established at an externally prescribed subfamily?

`Kakeya.ml1Boot.exists_plankDimensions` chooses its own subfamily, and so does the uniformity
producer `ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf`.  Composing them raises the
question of whether the plank half can instead be run at an index set chosen elsewhere.  The six
declarations below settle that question on the plank side.  **They are recorded and not used**,
and they change no existing statement.

**(C1) There is no whole-fibre factorization, and there cannot be one at a constant that depends
only on the ambient dimension.**  Every producer of `ConvexSpaceBody.Factorization` in the
repository returns a factorization of a *selected* set:
`ConvexSpaceBody.nonempty_factorization.factorization_weighted` (`Kakeya/Factorization.lean:815`)
and `ConvexSpaceBody.nonempty_factorization.factorization` (`Kakeya/Factorization.lean:535`) both
return an `s' ⊆ s` chosen by two dyadic pigeonholes;
`ConvexSpaceBody.nonempty_biasedFactorization` (`Kakeya/Factorization.lean:1588`) does the same
for `ConvexSpaceBody.BiasedFactorization`;
`ConvexSpaceBody.Factorization.ofSubsetParts` (`Kakeya/Factorization.lean:186`) keeps a
sub-collection of *whole* parts; and
`ConvexSpaceBody.exists_factorization_of_eq_empty` (`Kakeya/Factorization.lean:222`) together with
`Kakeya.ml1Boot.exists_emptyFactorization` covers the empty set.

The nearest thing to a whole-set producer is the private
`ConvexSpaceBody.nonempty_factorization.exists_factorization_of_parts`
(`Kakeya/Factorization.lean:700`), which factorizes `A.sup id` for an *arbitrary* sub-collection
`A` of the blocks of `ConvexSpaceBody.greedy_partition`.  At `A = (greedy_partition s V).parts` its
conclusion is a factorization of the whole of `s`, by `Finpartition.sup_parts`.  What blocks that
instantiation is its two hypotheses, and they are exactly what the two pigeonholes buy:

* `hcomp` (`Kakeya/Factorization.lean:703`), `maxDensity t V ≤ 2 * maxDensity t' V` across
  retained blocks, bought by `ConvexSpaceBody.nonempty_factorization.constructA_weighted`
  (`Kakeya/Factorization.lean:552`) at the weight loss `1 + log₂ |s|`.  Over the whole greedy
  partition it fails: the blocks are extracted in decreasing density and the a priori range of
  that score is `[1, |s|]` (`Kakeya/Factorization.lean:353`-`363`).
* `hsim` (`Kakeya/Factorization.lean:704`), the `simDims` clause, bought by
  `ConvexSpaceBody.nonempty_factorization.constructB_weighted` (`Kakeya/Factorization.lean:584`)
  at the weight loss `(1 + log₂ (1 / δ̃)) ^ dim`.  Over the whole partition it fails for the same
  reason: the a priori range of each ethickness is `[δ̃, 1]`
  (`Kakeya/Factorization.lean:376`-`385`).

So a whole-fibre variant would need `hcomp` at a constant `≥ |s|` and `hsim` at a constant
`≥ 1 / δ̃`.  Both are `δ̃`-dependent and both flow into the factorization constant `C`, hence into
the plank constant, hence into `Kakeya.IsPlankOfDimensions C ap bp` — whose brackets
`[C⁻¹ bp, C bp]` assert nothing once `C ≥ 1 / δ̃`.  A "worse constant" therefore does not buy the
whole fibre, and intra-fibre discarding does not disappear.  Two further facts make the route
unavailable even in the degenerate `δ̃`-dependent form:
`ConvexSpaceBody.nonempty_factorization.exists_factorization_of_parts` is `private`, and
`ConvexSpaceBody.nonempty_factorization.maxDensity_le_mul_of_parts`
(`Kakeya/Factorization.lean:620`) hard-codes the constant `2`.

**(C2) A factorization of `fibre u₁ pρ m` into `ap × bp × 1` planks does not restrict to
`fibre s' pρ m` at the same band, and the constant leaves no slack.**  Of the six brackets of
`Kakeya.IsPlankOfDimensions` (`Kakeya/Factoring/FlatPrisms.lean:79`-`85`) the three *upper* ones
descend to any sub-body, by monotonicity of `Metric.ethickness`; that is
`Kakeya.ml1Boot.ethickness_le_of_subset_of_isPlankOfDimensions` below.  The failure is confined
to the two *lower* brackets `C⁻¹ * b ≤ τ₁` (`Kakeya/Factoring/FlatPrisms.lean:82`) and
`C⁻¹ * a ≤ τ₂` (`Kakeya/Factoring/FlatPrisms.lean:84`), and it is quantitative rather than
qualitative: by `Kakeya.ml1Boot.le_mul_ethickness_of_isPlankOfDimensions` those two brackets pin
the band to the part's own thicknesses, `b ≤ C τ₁` and `a ≤ C τ₂`, so a *common* band forces any
two parts to have thicknesses within a factor `C ^ 2` of one another
(`Kakeya.ml1Boot.ethickness_le_sq_mul_of_isPlankOfDimensions_pair`).  An arbitrary `s'` may meet
one part in a single `δ̃`-tube while leaving another part whole, and then
`Kakeya.ml1Boot.plankBand_le_mul_of_subset_tube` caps the band at `C δ̃` while the untouched part
still needs `bp`, which `Kakeya.ml1Boot.exists_plankDimensions_geom` allows anywhere up to `ρ`.
`Kakeya.ml1Boot.not_exists_commonPlankBand_of_subset_tube` is that contradiction as a theorem:
once `C ^ 2 δ̃ < τ₁` of the untouched part, *no* pair `(a, b)` bands both.  Since
`plankPigeonhole.C` is fixed before `δ̃` and `ρ = δ̃ ^ (6 ε)`, the hypothesis of that theorem is
satisfiable for all small `δ̃`.  So the answer to (C2) is no, with no slack.

Re-grouping does not repair it.  Merging parts thickens the merged hull, which is the direction
the lower bracket wants and the wrong direction for the upper bracket `τ₁ ≤ C b` at the same `b`;
and it changes the `Finpartition`, so the merged blocks are no longer blocks of
`ConvexSpaceBody.greedy_partition` and
`ConvexSpaceBody.nonempty_factorization.exists_factorization_of_parts` no longer applies.
Re-banding, on the other hand, *is* free part by part:
`Kakeya.ml1Boot.exists_isPlankOfDimensions_ownBand` shows every nonempty block of `δ̃`-tubes
inside `B₁ ∩ T_ρ` is a plank at constant `2` for its own band `τ₂ × τ₁ × 1`.  The obstruction is
therefore not plankness but the *common* band, and restoring a common band means a dyadic
pigeonhole over the parts, which discards parts, which discards members of the prescribed
`fibre s' pρ m` — precisely the freedom a caller-prescribed index set withholds.

**(C3) There is no analogue of `Kakeya.ml1Boot.exists_plankFactorization_of_subsetParts`
(`Kakeya/DimensionThree/MainLemma1/Rescaling/KatzTao.lean:1679`) that keeps `t ∩ s'` from each
part `t` and re-bands.**  Two independent fields fail, both on the same configuration as (C2):

* `ConvexSpaceBody.Factorization.simDims` (`Kakeya/Factorization.lean:98`), which asks the parts'
  ethicknesses to be pairwise comparable at the factorization constant `2`.  A part thinned to a
  single `δ̃`-tube has `τ₁ = δ̃` while an untouched part has `τ₁` up to `ρ`, a ratio up to
  `ρ / δ̃ = δ̃ ^ (6 ε - 1)`, unbounded as `δ̃ → 0`.  Re-banding cannot help: `simDims` mentions no
  band.
* `ConvexSpaceBody.Factorization.maxDensity_le_mul` (`Kakeya/Factorization.lean:96`), for the
  reason already recorded at `Kakeya/Factorization.lean:183`-`185`: its right-hand side is
  attached to the part's own hull, which shrinks when members are dropped from inside the part.

`ConvexSpaceBody.Factorization.ofSubsetParts` survives dropping *other* parts precisely because
neither field is disturbed then; intersecting every part with `s'` disturbs both.  So (C3) is no,
and the smallest failing points are `Kakeya/Factorization.lean:98` and
`Kakeya/Factorization.lean:96`, ahead of the plank brackets at
`Kakeya/Factoring/FlatPrisms.lean:82` and `:84`.
-/

end Pigeonhole

end ml1Boot

end Kakeya

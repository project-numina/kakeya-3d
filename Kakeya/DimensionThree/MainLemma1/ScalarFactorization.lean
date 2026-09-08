/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Cases
public import Kakeya.DimensionThree.MainLemma1.Repair

/-!
# Scalar factorization: the one-scale selected wrapper and the independent two-scale product

This file carries Steps 1, 3 and 4 of the Main Lemma 1 repair blueprint: the zero-extension
view lemmas, the *one-scale selected certificate* `Kakeya.ml1Boot.IsOneScaleSelected` (B2),
and the *independent two-scale scalar factorization* `Kakeya.ml1Boot.IsTwoScaleFactors` (B3).

It replaces the synchronisation demands of the mega-structure
`Kakeya.ml1Boot.IsFactorTwoScales` by the two things GWZ actually provides.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya

namespace ml1Boot

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ## Step 1: zero-extension views -/

section ZeroExtend

/-- The tube `T` shaded by `∅`. -/
def nullShaded {σ : ℝ≥0} (T : Tube σ E) : ShadedTube σ E where
  toTube := T
  shade := ∅
  measurableSet_shade := MeasurableSet.empty
  shade_subset := Set.empty_subset _

omit [BorelSpace E] in
@[simp] theorem nullShaded_toTube {σ : ℝ≥0} (T : Tube σ E) :
    (nullShaded T).toTube = T := rfl

omit [BorelSpace E] in
@[simp] theorem nullShaded_shade {σ : ℝ≥0} (T : Tube σ E) :
    (nullShaded T).shade = (∅ : Set E) := rfl

/-- **Zero-extension of a shading off the active support** (blueprint §2.2).

`zeroExtend a T Z` keeps the shading `Z i` on the active index set `a` and replaces it by the
empty shading elsewhere, *without touching the underlying tube*.  This is the only operation
by which a shading defined on an active subfamily is transported to the fixed ambient
skeleton; by the lemmas below it preserves shade mass, shaded union, multiplicity and point
fibres, and it preserves nothing else. -/
noncomputable def zeroExtend {ι : Type*} [DecidableEq ι] {σ : ℝ≥0} (a : Finset ι)
    (T : ι → Tube σ E) (Z : ι → ShadedTube σ E) : ι → ShadedTube σ E :=
  fun i => if i ∈ a then Z i else nullShaded (T i)

omit [BorelSpace E] in
theorem zeroExtend_toTube_of_mem {ι : Type*} [DecidableEq ι] {σ : ℝ≥0} {a : Finset ι}
    {T : ι → Tube σ E} {Z : ι → ShadedTube σ E} {i : ι} (hi : i ∈ a) :
    (zeroExtend a T Z i).toTube = (Z i).toTube := by
  unfold zeroExtend; simp [hi]

omit [BorelSpace E] in
theorem zeroExtend_toTube_of_not_mem {ι : Type*} [DecidableEq ι] {σ : ℝ≥0} {a : Finset ι}
    {T : ι → Tube σ E} {Z : ι → ShadedTube σ E} {i : ι} (hi : i ∉ a) :
    (zeroExtend a T Z i).toTube = T i := by
  unfold zeroExtend; simp [hi]

/-- **The zero-extension lives on the fixed ambient skeleton.**  If the active shading shades
the ambient tubes, the zero-extension shades *every* ambient tube. -/
theorem zeroExtend_toTube {ι : Type*} [DecidableEq ι] {σ : ℝ≥0} {a : Finset ι}
    {T : ι → Tube σ E} {Z : ι → ShadedTube σ E} (hT : ∀ i ∈ a, (Z i).toTube = T i) (i : ι) :
    (zeroExtend a T Z i).toTube = T i := by
  by_cases hi : i ∈ a
  · rw [zeroExtend_toTube_of_mem hi]; exact hT i hi
  · exact zeroExtend_toTube_of_not_mem hi

theorem volume_carrier_zeroExtend {ι : Type*} [DecidableEq ι] {σ : ℝ≥0} (a : Finset ι)
    (T : ι → Tube σ E) (Z : ι → ShadedTube σ E) (i : ι) :
    volume (zeroExtend a T Z i).carrier = volume (T i).carrier := by
  by_cases hi : i ∈ a
  · rw [show (zeroExtend a T Z i).carrier = ((zeroExtend a T Z i).toTube).carrier from rfl,
      zeroExtend_toTube_of_mem hi]
    exact _root_.Tube.volume_carrier_eq_volume_carrier (Z i).toTube (T i)
  · rw [zeroExtend]; simp [hi]

omit [BorelSpace E] in
theorem zeroExtend_shade_of_mem {ι : Type*} [DecidableEq ι] {σ : ℝ≥0} {a : Finset ι}
    {T : ι → Tube σ E} {Z : ι → ShadedTube σ E} {i : ι} (hi : i ∈ a) :
    (zeroExtend a T Z i).shade = (Z i).shade := by
  unfold zeroExtend; simp [hi]

omit [BorelSpace E] in
theorem zeroExtend_shade_of_not_mem {ι : Type*} [DecidableEq ι] {σ : ℝ≥0} {a : Finset ι}
    {T : ι → Tube σ E} {Z : ι → ShadedTube σ E} {i : ι} (hi : i ∉ a) :
    (zeroExtend a T Z i).shade = (∅ : Set E) := by
  unfold zeroExtend; simp [hi]

variable {ι : Type*} [DecidableEq ι] {σ : ℝ≥0}

/-- **Zero-extension preserves shade mass.** -/
theorem sum_volume_shade_zeroExtend (s a : Finset ι) (T : ι → Tube σ E)
    (Z : ι → ShadedTube σ E) :
    ∑ i ∈ s, volume (zeroExtend a T Z i).shade = ∑ i ∈ s ∩ a, volume (Z i).shade := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not s (· ∈ a)]
  have h₁ : ∑ i ∈ s.filter (· ∈ a), volume (zeroExtend a T Z i).shade
      = ∑ i ∈ s ∩ a, volume (Z i).shade := by
    rw [Finset.filter_mem_eq_inter]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [zeroExtend_shade_of_mem (Finset.mem_inter.mp hi).2]
  have h₂ : ∑ i ∈ s.filter (¬ · ∈ a), volume (zeroExtend a T Z i).shade = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [zeroExtend_shade_of_not_mem (Finset.mem_filter.mp hi).2]
    simp
  rw [h₁, h₂, add_zero]

/-- **Zero-extension preserves the shaded union.** -/
theorem iUnionShade_zeroExtend (s a : Finset ι) (T : ι → Tube σ E)
    (Z : ι → ShadedTube σ E) :
    (⋃ i ∈ s, (zeroExtend a T Z i).shade) = ⋃ i ∈ s ∩ a, (Z i).shade := by
  classical
  ext x
  simp only [Set.mem_iUnion, exists_prop, Finset.mem_inter]
  constructor
  · rintro ⟨i, hi, hx⟩
    by_cases hia : i ∈ a
    · exact ⟨i, ⟨hi, hia⟩, by rwa [zeroExtend_shade_of_mem hia] at hx⟩
    · rw [zeroExtend_shade_of_not_mem hia] at hx; exact absurd hx (Set.notMem_empty x)
  · rintro ⟨i, ⟨hi, hia⟩, hx⟩
    exact ⟨i, hi, by rwa [zeroExtend_shade_of_mem hia]⟩

/-- **Zero-extension preserves multiplicity.** -/
theorem multiplicity_zeroExtend (s a : Finset ι) (T : ι → Tube σ E)
    (Z : ι → ShadedTube σ E) :
    ShadedBody.multiplicity s (fun i => (zeroExtend a T Z i).toShadedBody)
      = ShadedBody.multiplicity (s ∩ a) (fun i => (Z i).toShadedBody) := by
  classical
  rw [ShadedBody.multiplicity_eq_div, ShadedBody.multiplicity_eq_div]
  congr 1
  · exact sum_volume_shade_zeroExtend s a T Z
  · exact congrArg volume (iUnionShade_zeroExtend s a T Z)

/-- The special case of `Kakeya.ml1Boot.multiplicity_zeroExtend` at an active support already
contained in the ambient index set. -/
theorem multiplicity_zeroExtend_of_subset {s a : Finset ι} (h : a ⊆ s)
    (T : ι → Tube σ E) (Z : ι → ShadedTube σ E) :
    ShadedBody.multiplicity s (fun i => (zeroExtend a T Z i).toShadedBody)
      = ShadedBody.multiplicity a (fun i => (Z i).toShadedBody) := by
  rw [multiplicity_zeroExtend, Finset.inter_eq_right.mpr h]

theorem sum_volume_shade_zeroExtend_of_subset {s a : Finset ι} (h : a ⊆ s)
    (T : ι → Tube σ E) (Z : ι → ShadedTube σ E) :
    ∑ i ∈ s, volume (zeroExtend a T Z i).shade = ∑ i ∈ a, volume (Z i).shade := by
  rw [sum_volume_shade_zeroExtend, Finset.inter_eq_right.mpr h]

/-- **The selected child shading on the fixed ambient skeleton**: the child shading `Z'` on
its active support `act'`, zero-extended over the ambient tubes of the input family `V`. -/
noncomputable def selectedShade (act' : Finset ι) (V Z' : ι → ShadedTube σ E) :
    ι → ShadedTube σ E :=
  zeroExtend act' (fun i => (V i).toTube) Z'

theorem selectedShade_toTube {act' : Finset ι} {V Z' : ι → ShadedTube σ E}
    (hT : ∀ i ∈ act', (Z' i).toTube = (V i).toTube) (i : ι) :
    (selectedShade act' V Z' i).toTube = (V i).toTube :=
  zeroExtend_toTube hT i

end ZeroExtend

/-! ## The averaging step: one good child fibre

GWZ Lemma 5.11 does **not** assert that every surviving child fibre is full; the wrapper
selects **one** by mass averaging.  These are the two ingredients: a finite pigeonhole in
`ℝ≥0∞`, and the selection lemma itself. -/

section Selection

/-- A ratio comparison in `ℝ≥0∞` with finite nonzero denominators. -/
theorem div_le_div_of_mul_le_mul {x y u v : ℝ≥0∞} (hu0 : u ≠ 0) (hut : u ≠ ⊤)
    (hv0 : v ≠ 0) (hvt : v ≠ ⊤) (h : x * v ≤ y * u) : x / u ≤ y / v := by
  have hswap : y / v * u = y * u / v := by
    rw [div_eq_mul_inv, div_eq_mul_inv]; ring
  rw [ENNReal.div_le_iff hu0 hut, hswap, ENNReal.le_div_iff_mul_le
    (Or.inl hv0) (Or.inl hvt)]
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

/-- **Finite mass pigeonhole.**  If a total mass `A` is spread over the cells of `t`, whose
weights `n` sum to at most `N`, then some cell carries at least the average density. -/
theorem exists_mul_natCast_le {κ : Type*} (t : Finset κ) (ht : t.Nonempty)
    (a : κ → ℝ≥0∞) (n : κ → ℕ) (A : ℝ≥0∞) (N : ℕ)
    (hafin : ∀ k ∈ t, a k ≠ ⊤) (hAtop : A ≠ ⊤)
    (hA : A ≤ ∑ k ∈ t, a k) (hn : ∑ k ∈ t, n k ≤ N) :
    ∃ k ∈ t, A * (n k : ℝ≥0∞) ≤ a k * (N : ℝ≥0∞) := by
  classical
  set a' : κ → ℝ≥0 := fun k => (a k).toNNReal with ha'
  set A' : ℝ≥0 := A.toNNReal with hA'
  have hcoe : ∀ k ∈ t, ((a' k : ℝ≥0) : ℝ≥0∞) = a k := fun k hk =>
    ENNReal.coe_toNNReal (hafin k hk)
  have hAcoe : ((A' : ℝ≥0) : ℝ≥0∞) = A := ENNReal.coe_toNNReal hAtop
  have hAle : A' ≤ ∑ k ∈ t, a' k := by
    rw [← ENNReal.coe_le_coe, hAcoe, ENNReal.coe_finset_sum]
    exact le_trans hA (le_of_eq (Finset.sum_congr rfl fun k hk => (hcoe k hk).symm))
  have hsum : ∑ k ∈ t, A' * (n k : ℝ≥0) ≤ ∑ k ∈ t, a' k * (N : ℝ≥0) := by
    calc ∑ k ∈ t, A' * (n k : ℝ≥0) = A' * ∑ k ∈ t, (n k : ℝ≥0) := by
          rw [Finset.mul_sum]
      _ ≤ A' * (N : ℝ≥0) := by
          have : ∑ k ∈ t, (n k : ℝ≥0) ≤ (N : ℝ≥0) := by
            rw [← Nat.cast_sum]; exact_mod_cast hn
          exact mul_le_mul_right this A'
      _ ≤ (∑ k ∈ t, a' k) * (N : ℝ≥0) := by
          exact mul_le_mul_left hAle _
      _ = ∑ k ∈ t, a' k * (N : ℝ≥0) := by rw [Finset.sum_mul]
  obtain ⟨k, hk, hle⟩ := Finset.exists_le_of_sum_le ht hsum
  refine ⟨k, hk, ?_⟩
  have := (ENNReal.coe_le_coe.mpr hle)
  rw [ENNReal.coe_mul, ENNReal.coe_mul, hAcoe, hcoe k hk] at this
  simpa using this

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {σ : ℝ≥0}

/-- The zero-extended fibre mass is the mass of the *active* fibre. -/
theorem sum_shade_fibre_zeroExtend {amb act : Finset ι} (hact : act ⊆ amb) (p : ι → κ)
    (T : ι → Tube σ E) (Z : ι → ShadedTube σ E) (k : κ) :
    ∑ i ∈ fibre amb p k, volume (zeroExtend act T Z i).shade
      = ∑ i ∈ fibre act p k, volume (Z i).shade := by
  classical
  rw [sum_volume_shade_zeroExtend]
  congr 1
  unfold fibre
  ext i
  simp only [Finset.mem_inter, Finset.mem_filter]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hact h.1, h.2⟩, h.1⟩⟩

/-- **One good child fibre, by averaging** (blueprint §3 B2, selection certificate).

Given a fixed ambient carrier `amb` at scale `σ`, an active subfamily `act` all of whose
parents lie in `t`, and a shading of positive total mass, some parent `k₀ ∈ t` has a
**nonempty ambient fibre** whose fullness — computed against the *full* ambient fibre, with
the shading zero-extended over the inactive tubes — is at least the ambient average fullness.

This is the only place where a "good fibre" is produced, and it produces exactly one; the
source gives no statement about the remaining fibres. -/
theorem exists_selected_fibre [Nontrivial E] {τ : ℝ≥0} (hτ0 : 0 < τ)
    {amb act : Finset ι} (hact : act ⊆ amb) {p : ι → κ} {t : Finset κ}
    (hmaps : ∀ i ∈ act, p i ∈ t) (T : ι → Tube τ E) (Z : ι → ShadedTube τ E)
    (hpos : 0 < ∑ i ∈ act, volume (Z i).shade) :
    ∃ k₀ ∈ t, (fibre amb p k₀).Nonempty ∧
      (ShadedBody.fullness amb (fun i => (zeroExtend act T Z i).toShadedBody) : ℝ≥0∞)
        ≤ (ShadedBody.fullness (fibre amb p k₀)
            (fun i => (zeroExtend act T Z i).toShadedBody) : ℝ≥0∞) := by
  classical
  set W : ι → ShadedTube τ E := zeroExtend act T Z with hW
  -- the common carrier volume of a `τ`-tube
  obtain ⟨i₁, hi₁⟩ : act.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h] at hpos; simp at hpos
  have hi₁amb : i₁ ∈ amb := hact hi₁
  set v : ℝ≥0∞ := volume (Z i₁).carrier with hv
  have hvol : ∀ i : ι, volume (W i).carrier = v := by
    intro i
    rw [hW, volume_carrier_zeroExtend, hv]
    exact _root_.Tube.volume_carrier_eq_volume_carrier (T i) (Z i₁).toTube
  have hv_pos : 0 < v := by
    have hc : 0 < (_root_.Tube.le_volume.c (Module.finrank ℝ E) : ℝ≥0∞) :=
      ENNReal.coe_pos.mpr (_root_.Tube.le_volume.c_pos (Module.finrank ℝ E))
    have hδp : 0 < (τ : ℝ≥0∞) ^ (Module.finrank ℝ E - 1) :=
      ENNReal.pow_pos (ENNReal.coe_pos.mpr hτ0) (Module.finrank ℝ E - 1)
    exact lt_of_lt_of_le (ENNReal.mul_pos hc.ne' hδp.ne')
      (by simpa [hv] using _root_.Tube.le_volume (Z i₁).toTube)
  have hv_top : v ≠ ⊤ := by
    rw [hv]; exact (Z i₁).isCompact.measure_ne_top
  -- the cells
  set tp : Finset κ := t.filter (fun k => 0 < (fibre amb p k).card) with htp
  set aa : κ → ℝ≥0∞ := fun k => ∑ i ∈ fibre amb p k, volume (W i).shade with haa
  set M : ℝ≥0∞ := ∑ i ∈ act, volume (Z i).shade with hM
  have hMtop : M ≠ ⊤ := by
    rw [hM]
    refine ENNReal.sum_ne_top.mpr fun i _ => ?_
    exact ne_top_of_le_ne_top (Z i).isCompact.measure_ne_top
      (measure_mono (Z i).shade_subset)
  have hafin : ∀ k ∈ tp, aa k ≠ ⊤ := by
    intro k _
    rw [haa]
    refine ENNReal.sum_ne_top.mpr fun i _ => ?_
    exact ne_top_of_le_ne_top (W i).isCompact.measure_ne_top
      (measure_mono (W i).shade_subset)
  -- (1) the cells carry the whole active mass
  have hfib : ∀ k : κ, aa k = ∑ i ∈ fibre act p k, volume (Z i).shade := fun k =>
    sum_shade_fibre_zeroExtend hact p T Z k
  have hsum_t : ∑ k ∈ t, aa k = M := by
    simp_rw [hfib]
    rw [hM]
    exact Finset.sum_fiberwise_of_maps_to hmaps (fun i => volume (Z i).shade)
  have hsum_tp : ∑ k ∈ tp, aa k = M := by
    rw [← hsum_t, htp]
    refine Finset.sum_filter_of_ne fun k _ hne => ?_
    by_contra hcon
    have hz : fibre amb p k = ∅ :=
      Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos hcon)
    exact hne (by simp [haa, hz])
  -- (2) the cells do not overcount the ambient carrier
  have hcard : ∑ k ∈ tp, (fibre amb p k).card ≤ amb.card := by
    set s₁ : Finset ι := amb.filter (fun i => p i ∈ tp) with hs₁
    have hmapsTo : Set.MapsTo p (s₁ : Set ι) (tp : Set κ) := by
      intro i hi
      exact_mod_cast (Finset.mem_filter.mp hi).2
    have hsplit : s₁.card = ∑ k ∈ tp, (fibre amb p k).card := by
      rw [Finset.card_eq_sum_card_fiberwise hmapsTo]
      refine Finset.sum_congr rfl fun k hk => ?_
      have : fibre s₁ p k = fibre amb p k := fibre_filter_mem amb p tp hk
      simpa [fibre, hs₁] using congrArg Finset.card this
    rw [← hsplit, hs₁]
    exact Finset.card_filter_le _ _
  -- (3) at least one cell is nonempty
  have hk₁ : p i₁ ∈ tp := by
    refine Finset.mem_filter.mpr ⟨hmaps i₁ hi₁, ?_⟩
    exact Finset.card_pos.mpr ⟨i₁, Finset.mem_filter.mpr ⟨hi₁amb, rfl⟩⟩
  -- (4) pigeonhole
  obtain ⟨k₀, hk₀, hpig⟩ := exists_mul_natCast_le tp ⟨_, hk₁⟩ aa
    (fun k => (fibre amb p k).card) M amb.card hafin hMtop (le_of_eq hsum_tp.symm) hcard
  have hk₀t : k₀ ∈ t := (Finset.mem_filter.mp hk₀).1
  have hk₀ne : (fibre amb p k₀).Nonempty :=
    Finset.card_pos.mp (Finset.mem_filter.mp hk₀).2
  refine ⟨k₀, hk₀t, hk₀ne, ?_⟩
  -- (5) the two fullnesses, as ratios with a common tube volume
  have hambmass : ∑ i ∈ amb, volume (W i).shade = M := by
    rw [hW, sum_volume_shade_zeroExtend_of_subset hact]
  have hambcar : ∑ i ∈ amb, volume (W i).carrier = (amb.card : ℝ≥0∞) * v := by
    rw [Finset.sum_congr rfl (fun i _ => hvol i), Finset.sum_const, nsmul_eq_mul]
  have hfibcar : ∑ i ∈ fibre amb p k₀, volume (W i).carrier
      = ((fibre amb p k₀).card : ℝ≥0∞) * v := by
    rw [Finset.sum_congr rfl (fun i _ => hvol i), Finset.sum_const, nsmul_eq_mul]
  have hn₀ : (1 : ℝ≥0∞) ≤ ((fibre amb p k₀).card : ℝ≥0∞) := by
    exact_mod_cast Nat.succ_le_of_lt (Finset.card_pos.mpr hk₀ne)
  have hN : (1 : ℝ≥0∞) ≤ (amb.card : ℝ≥0∞) := by
    exact_mod_cast Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨i₁, hi₁amb⟩)
  rw [ShadedBody.coe_fullness, ShadedBody.coe_fullness]
  show (∑ i ∈ amb, volume (W i).shade) / (∑ i ∈ amb, volume (W i).carrier)
      ≤ (∑ i ∈ fibre amb p k₀, volume (W i).shade)
        / (∑ i ∈ fibre amb p k₀, volume (W i).carrier)
  rw [hambmass, hambcar, hfibcar]
  refine div_le_div_of_mul_le_mul ?_ ?_ ?_ ?_ ?_
  · exact mul_ne_zero (by positivity) hv_pos.ne'
  · exact ENNReal.mul_ne_top (by simp) hv_top
  · exact mul_ne_zero (by positivity) hv_pos.ne'
  · exact ENNReal.mul_ne_top (by simp) hv_top
  · calc M * (((fibre amb p k₀).card : ℝ≥0∞) * v)
        = (M * ((fibre amb p k₀).card : ℝ≥0∞)) * v := by ring
      _ ≤ (aa k₀ * (amb.card : ℝ≥0∞)) * v := by gcongr
      _ = aa k₀ * ((amb.card : ℝ≥0∞) * v) := by ring

end Selection

/-! ## B2: the one-scale selected certificate -/

section OneScale

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {σ ρ : ℝ≥0}

/-- The active part of an ambient fibre. -/
theorem fibre_inter {amb act : Finset ι} (hact : act ⊆ amb) (p : ι → κ) (k : κ) :
    fibre amb p k ∩ act = fibre act p k := by
  classical
  unfold fibre
  ext i
  simp only [Finset.mem_inter, Finset.mem_filter]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hact h.1, h.2⟩, h.1⟩⟩

/-- **B2: the one-scale selected certificate** (blueprint §3 B2, §9 Step 3).

A faithful wrapper around GWZ Lemma 5.11, in two layers.

*The raw one-scale certificate* (`child_*`, `parent_*`, `scalar`) records what Lemma 5.11
gives: a child refinement with its **true shade-mass retention** `c`, the active parent
family `tAct` inside the fixed parent skeleton `tAmb` together with the induced parent
shading `Zρ`, the parent's **average** fullness `lamP`, the containment (26), and the scalar
inequality (25) for **every** active parent.

*The selection certificate* (`sel_*`) records the one thing averaging buys: **one** good
child fibre `k₀`, whose fullness `lamF` is measured against that fibre's *full ambient
skeleton* `fibre amb p k₀` with the shading zero-extended over the inactive tubes.

Deliberately absent, because the source does not provide them:

* "every surviving child fibre is good" — only `k₀` is;
* Definition 2.2 shaded uniformity of any output family;
* a permanent per-tube density bracket on the selected fibre;
* any compatibility of `k₀` with a selection made at another scale.

The active/ambient separation of blueprint §2.1 is in the binder: `amb` is the fixed carrier
that the analytic estimates and the parent maps read, `act` is the currently shaded support
that the *next* Lemma 5.11 reads, and `shade_off` says the input shading is already
zero-extended. -/
structure IsOneScaleSelected (c L : ℝ≥0∞)
    (amb act : Finset ι) (V : ι → ShadedTube σ E)
    (tAmb : Finset κ) (Vρ : κ → Tube ρ E) (p : ι → κ)
    (act' : Finset ι) (Z' : ι → ShadedTube σ E)
    (tAct : Finset κ) (Zρ : κ → ShadedTube ρ E)
    (k₀ : κ) (lamP lamF : ℝ≥0) : Prop where
  /-- The active support sits inside the fixed ambient carrier. -/
  active_subset : act ⊆ amb
  /-- The input shading is zero-extended: it is empty off the active support. -/
  shade_off : ∀ i ∈ amb, i ∉ act → (V i).shade = ∅
  /-- (raw) The child refinement is a subfamily of the active support. -/
  child_subset : act' ⊆ act
  /-- (raw) The child shading shades the same tubes and is contained in the input shading. -/
  child_shade : ∀ i ∈ act', (Z' i).toTube = (V i).toTube ∧ (Z' i).shade ⊆ (V i).shade
  /-- (raw) The child refinement's **true shade-mass retention** (blueprint §2.3). -/
  child_retention : c * (∑ i ∈ act, volume (V i).shade) ≤ ∑ i ∈ act', volume (Z' i).shade
  /-- (raw) The active parent family sits inside the fixed parent skeleton. -/
  parent_subset : tAct ⊆ tAmb
  /-- (raw) Every retained child has its parent active. -/
  parent_mapsTo : ∀ i ∈ act', p i ∈ tAct
  /-- (raw) The induced parent shading shades the parent tubes. -/
  parent_tube : ∀ k ∈ tAct, (Zρ k).toTube = Vρ k
  /-- (raw) GWZ (26): the child shadings are nested in the parent ones. -/
  parent_contain : ∀ i ∈ act', (Z' i).shade ⊆ (Zρ (p i)).shade
  /-- (raw) The parent family's **average** fullness — not a per-tube bracket. -/
  parent_fullness : (lamP : ℝ≥0∞)
    ≤ (ShadedBody.fullness tAct (fun k => (Zρ k).toShadedBody) : ℝ≥0∞)
  /-- (raw) GWZ (25), for **every** active parent. -/
  scalar : ∀ k ∈ tAct, ShadedBody.multiplicity amb (fun i => (V i).toShadedBody)
    ≤ L * ShadedBody.multiplicity tAct (fun k' => (Zρ k').toShadedBody)
      * ShadedBody.multiplicity (fibre act' p k) (fun i => (Z' i).toShadedBody)
  /-- (selection) The selected parent is active. -/
  sel_mem : k₀ ∈ tAct
  /-- (selection) Its ambient fibre is nonempty. -/
  sel_nonempty : (fibre amb p k₀).Nonempty
  /-- (selection) The good fibre's fullness, computed against the **full ambient fibre** with
  the child shading zero-extended over the inactive tubes. -/
  sel_fullness : (lamF : ℝ≥0∞)
    ≤ (ShadedBody.fullness (fibre amb p k₀)
        (fun i => (selectedShade act' V Z' i).toShadedBody) : ℝ≥0∞)
  /-- (selection) That fullness is at least the retention factor times the input fullness. -/
  sel_fullness_lb : c * (ShadedBody.fullness amb (fun i => (V i).toShadedBody) : ℝ≥0∞)
    ≤ (lamF : ℝ≥0∞)

namespace IsOneScaleSelected

variable {c L : ℝ≥0∞} {amb act : Finset ι} {V : ι → ShadedTube σ E}
  {tAmb : Finset κ} {Vρ : κ → Tube ρ E} {p : ι → κ}
  {act' : Finset ι} {Z' : ι → ShadedTube σ E}
  {tAct : Finset κ} {Zρ : κ → ShadedTube ρ E} {k₀ : κ} {lamP lamF : ℝ≥0}

variable (h : IsOneScaleSelected c L amb act V tAmb Vρ p act' Z' tAct Zρ k₀ lamP lamF)

include h

theorem child_subset_amb : act' ⊆ amb := h.child_subset.trans h.active_subset

/-- **The scalar inequality instantiated at the selected parent**, with the fine factor read
on the *full ambient fibre* of `k₀` and the zero-extended shading.  This is the form the
two-scale composition consumes; it is the raw `scalar` at `k₀` plus
`Kakeya.ml1Boot.multiplicity_zeroExtend`, i.e. zero-extension is free for multiplicity. -/
theorem sel_scalar :
    ShadedBody.multiplicity amb (fun i => (V i).toShadedBody)
      ≤ L * ShadedBody.multiplicity tAct (fun k => (Zρ k).toShadedBody)
        * ShadedBody.multiplicity (fibre amb p k₀)
            (fun i => (selectedShade act' V Z' i).toShadedBody) := by
  have hfib : fibre amb p k₀ ∩ act' = fibre act' p k₀ :=
    fibre_inter h.child_subset_amb p k₀
  rw [selectedShade, multiplicity_zeroExtend, hfib]
  exact h.scalar k₀ h.sel_mem

end IsOneScaleSelected

end OneScale

/-! ## The B2 producer: projecting GWZ Lemma 5.11, then averaging -/

section OneScaleProducer

variable {ι κ lc : Type*} [DecidableEq ι] [DecidableEq κ] [DecidableEq lc] {σ ρ δ : ℝ≥0}

end OneScaleProducer

/-! ## B3: the independent two-scale scalar factorization -/

section TwoScale

variable {ι κ lc : Type*} [DecidableEq ι] [DecidableEq κ] [DecidableEq lc]
  {δ τ θ : ℝ≥0}

/-- **B3: the two-scale scalar factorization, with independently selected fibres**
(blueprint §3 B3, §9 Step 4).

One fixed carrier skeleton `𝕋_δ → 𝕋_τ → 𝕋_θ` (`amb`, `tτAmb`, `tθAmb` with the parent maps
`pτ`, `pθ`), one fine fibre `𝓕 = fibre amb pτ kF` and one middle fibre
`𝓜 = fibre tτAmb pθ lM`, **chosen independently**: GWZ equation (59) holds for each `T_τ` and
each `T_θ` separately, so there is no nested witness relating `kF` to `lM` and this structure
carries none.  The three shadings are zero-extended over their full ambient index sets and
come with their *actual* average-fullness lower bounds `lamF`, `lamM`, `lamC`.

The whole cost of the construction is the **single** factor `Lfact`, paid once in `product`;
the retention factors of the two refinements are already absorbed into it and are not charged
again against the fullnesses.

The three analytic multiplicity conclusions (fine, middle, coarse) are **not** here: they are
the consumers' business, and `product` is exactly the shape
`Kakeya.ml1Boot.multiplicity_le_of_middle` consumes. -/
structure IsTwoScaleFactors (Lfact Lcard : ℝ≥0∞)
    (amb : Finset ι) (V : ι → ShadedTube δ E)
    (tτAmb : Finset κ) (Vτ : κ → Tube τ E) (pτ : ι → κ)
    (tθAmb : Finset lc) (Vθ : lc → Tube θ E) (pθ : κ → lc)
    (kF : κ) (Yf : ι → ShadedTube δ E) (lamF : ℝ≥0)
    (lM : lc) (Ym : κ → ShadedTube τ E) (lamM : ℝ≥0)
    (tθAct : Finset lc) (Yc : lc → ShadedTube θ E) (lamC : ℝ≥0) : Prop where
  /-- The fixed skeleton: every ambient `δ`-tube has its `τ`-parent in the fixed middle
  carrier. -/
  skeleton_fine : ∀ i ∈ amb, pτ i ∈ tτAmb
  /-- The fixed skeleton: every ambient `τ`-tube has its `θ`-parent in the fixed coarse
  carrier. -/
  skeleton_mid : ∀ k ∈ tτAmb, pθ k ∈ tθAmb
  /-- The selected fine parent lies in the fixed middle carrier. -/
  fine_mem : kF ∈ tτAmb
  /-- Its ambient fine fibre is nonempty. -/
  fine_nonempty : (fibre amb pτ kF).Nonempty
  /-- The fine shading shades the ambient fine tubes (it is zero-extended, not restricted). -/
  fine_tube : ∀ i ∈ fibre amb pτ kF, (Yf i).toTube = (V i).toTube
  /-- The fine fibre's actual average fullness. -/
  fine_fullness : (lamF : ℝ≥0∞)
    ≤ (ShadedBody.fullness (fibre amb pτ kF) (fun i => (Yf i).toShadedBody) : ℝ≥0∞)
  /-- The selected middle parent lies in the fixed coarse carrier.  It is chosen
  **independently** of `kF`. -/
  mid_mem : lM ∈ tθAmb
  /-- Its ambient middle fibre is nonempty. -/
  mid_nonempty : (fibre tτAmb pθ lM).Nonempty
  /-- The middle shading shades the ambient middle tubes. -/
  mid_tube : ∀ k ∈ fibre tτAmb pθ lM, (Ym k).toTube = Vτ k
  /-- The middle fibre's actual average fullness. -/
  mid_fullness : (lamM : ℝ≥0∞)
    ≤ (ShadedBody.fullness (fibre tτAmb pθ lM) (fun k => (Ym k).toShadedBody) : ℝ≥0∞)
  /-- The active coarse family sits inside the fixed coarse carrier. -/
  coarse_subset : tθAct ⊆ tθAmb
  /-- It is nonempty. -/
  coarse_nonempty : tθAct.Nonempty
  /-- The coarse shading shades the coarse tubes. -/
  coarse_tube : ∀ l ∈ tθAct, (Yc l).toTube = Vθ l
  /-- The coarse family's actual average fullness. -/
  coarse_fullness : (lamC : ℝ≥0∞)
    ≤ (ShadedBody.fullness tθAct (fun l => (Yc l).toShadedBody) : ℝ≥0∞)
  /-- The branch/cardinality comparison: the product of the three retained cardinalities is
  controlled by the ambient cardinality. -/
  branch_card : ((fibre amb pτ kF).card : ℝ≥0∞) * ((fibre tτAmb pθ lM).card : ℝ≥0∞)
      * (tθAct.card : ℝ≥0∞) ≤ Lcard * (amb.card : ℝ≥0∞)
  /-- **(F)** the scalar product inequality, with the single total factor loss. -/
  product : ShadedBody.multiplicity amb (fun i => (V i).toShadedBody)
    ≤ Lfact * ShadedBody.multiplicity (fibre amb pτ kF) (fun i => (Yf i).toShadedBody)
      * ShadedBody.multiplicity (fibre tτAmb pθ lM) (fun k => (Ym k).toShadedBody)
      * ShadedBody.multiplicity tθAct (fun l => (Yc l).toShadedBody)

namespace IsTwoScaleFactors

variable {Lfact Lcard : ℝ≥0∞}
  {amb : Finset ι} {V : ι → ShadedTube δ E}
  {tτAmb : Finset κ} {Vτ : κ → Tube τ E} {pτ : ι → κ}
  {tθAmb : Finset lc} {Vθ : lc → Tube θ E} {pθ : κ → lc}
  {kF : κ} {Yf : ι → ShadedTube δ E} {lamF : ℝ≥0}
  {lM : lc} {Ym : κ → ShadedTube τ E} {lamM : ℝ≥0}
  {tθAct : Finset lc} {Yc : lc → ShadedTube θ E} {lamC : ℝ≥0}

variable (h : IsTwoScaleFactors Lfact Lcard amb V tτAmb Vτ pτ tθAmb Vθ pθ
  kF Yf lamF lM Ym lamM tθAct Yc lamC)

include h

end IsTwoScaleFactors

end TwoScale

/-! ### Replacing the independently proved branch-cardinality comparison -/

section B3Recard

variable [Nontrivial E]

end B3Recard

/-! ## (F) keeps the Case (ii) collapse usable -/

section Collapse

variable {ι κ lc : Type*} [DecidableEq ι] [DecidableEq κ] [DecidableEq lc]

end Collapse

/-! ## Satisfiability witnesses

Both structures are bundles of inequalities.  These are the satisfiability witnesses, and
they are **not** degenerate:
every shading below has positive volume, so every multiplicity, fullness and mass inequality
is tested at a nonzero value. -/

section Witnesses

/-- A tube shaded by the whole of its carrier. -/
def fullShade {σ : ℝ≥0} (T : Tube σ E) : ShadedTube σ E where
  toTube := T
  shade := T.carrier
  measurableSet_shade := T.toConvexSpaceBody.isCompact.isClosed.measurableSet
  shade_subset := subset_rfl

@[simp] theorem fullShade_toTube {σ : ℝ≥0} (T : Tube σ E) : (fullShade T).toTube = T := rfl

@[simp] theorem fullShade_shade {σ : ℝ≥0} (T : Tube σ E) :
    (fullShade T).shade = T.carrier := rfl

end Witnesses

/-! ### The fine and middle selections really are independent

The one clause the retired mega-structure carried and the source does not is a nesting
witness tying the fine parent to the selected middle fibre.  The witness below has
`pθ kF ≠ lM`, so `Kakeya.ml1Boot.IsTwoScaleFactors` provably does **not** imply one. -/

section Independence

end Independence

end ml1Boot

end Kakeya

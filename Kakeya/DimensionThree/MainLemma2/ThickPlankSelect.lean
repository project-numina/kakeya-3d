/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.GreedyIndependentSetCard
public import Kakeya.AffineMap
public import Kakeya.DimensionThree.MainLemma2.PlankPresentation
public import Kakeya.DimensionThree.MainLemma2.ThickPlankInterface
public import Kakeya.DimensionThree.MainLemma2.LineEssDistinct

/-!
# Plank selection inside a block

A single selected subfamily supplies `sel_card`, `essDistinct`, and
the shaded-mass retention used by `ThickPlankPresentation.fullness_ge`.

GWZ define the per-ball family `𝕋_B` to be essentially
distinct. Its normalized block `𝒫 = L(𝕋_{B,W})` inherits that
property by affine invariance. Here it is an explicit hypothesis `hED`:

* `edImages_of_edSegments` transports essential distinctness of the
  segment bodies to the images `L(T_p)` by
  `IsEssentiallyDistinct.image_affineEquiv`.
* `thickPlankSelection_of_edImages` applies
  `plankSubfamilySelection_card` to those images. Its conclusions
  supply essential distinctness, cardinality retention, and weight
  retention at `y p = |Y_p.shade|`.

## Simultaneous mass and cardinality retention

Two independent selections do not suffice: the selected subfamily
can depend on the weight, whereas both `sel_card` and `fullness_ge`
refer to the same `sel`. Nor can one generally retain constant
fractions of two arbitrary weights. In a clique on `D + 1` vertices,
independent sets are singletons and two weights can be supported on
different vertices.

The additional weight here is the constant `1`. The greedy selection
of `Kakeya.exists_pairwise_not_of_degree_le` is maximal, and every
maximal independent set in a graph of degree at most `D` contains
at least `1/(D + 1)` of the vertices. The combined lemma
`Kakeya.exists_pairwise_not_of_degree_le_card` therefore retains
both the prescribed mass and the cardinality in one selection.
`plankSubfamilySelection_card` applies it with the fixed constant
`Kakeya.VeryNotSticky.plankSelectionConstant C₀`.
-/

@[expose] public section

open scoped NNReal ENNReal

open Finset MeasureTheory Metric Set ShadedBody

noncomputable section

namespace Kakeya.VeryNotSticky

open Kakeya

/-- Shorthand for the ambient space of the thick case. -/
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

universe u

/-! ### The selection, retaining a weight and the cardinality at once -/

/-! ### R31-a: essential distinctness transports to the normalised images -/

/-! ### R31-b: the per-block selection -/

/-! ### R31 at a degree bound: the additive twins

The refined text's per-ball capsule family is line-based `A₀`-essentially distinct and **not**
pairwise essentially distinct , so the
per-ball hypothesis of the thick case arrives as a **non-ED degree bound**
`{q ∈ segs B | q ≠ p ∧ ¬ IsEssentiallyDistinct (Y p) (Y q)}.ncard ≤ edMultiplicityConstant`
(`MainLemma2/LineEssDistinct.lean`, row E0; the constant is A-C1 symbol).  The three
theorems above are true — they are the degree-`0` instances — and keep their consumer
`thickPlankSelection_of_edImages`; the twins below take the degree bound and are what
`thickPlankPresentable_of_ballData` now reads.  The `q ≠ p` is load-bearing: a body of positive
finite volume is never essentially distinct from itself, and `exists_pairwise_not_of_degree_le`'s
relation has to be irreflexive. -/

/-- **The clustering relation has bounded degree, from a degree bound on the inner bodies**
(twin of `Kakeya.VeryNotSticky.plankClusterBound`).

If every inner body `K i` is non-essentially-distinct from at most `D_K` others, then the planks
clustered with `P i` number at most `(D_K + 1)(D + 1) − 1`, `D` the pairwise cluster constant:
inside `{i} ∪ cluster(i)` a greedy independent set for the `K`-relation that **contains `i`** (the
weight is the indicator of `i`) retains a `1/(D_K + 1)` fraction of the cardinality, and on it
`plankClusterBound` applies.  Stated as `ncard + 1 ≤ (D_K + 1)(D + 1)` to avoid `ℕ`-subtraction. -/
theorem plankClusterBound_of_degree {C₀ : ℝ≥0} (hC₀ : 1 ≤ C₀)
    {a' b' : ℝ≥0} (ha' : 0 < a') (hab' : a' ≤ b') (hb1' : b' ≤ 1)
    {ι : Type*} (s : Finset ι) (P : ι → Plank a' b' hab' hb1') (K : ι → ConvexSpaceBody E₃)
    (hKP : ∀ j ∈ s, ((K j).carrier : Set E₃) ⊆ (P j).carrier)
    (hKvol : ∀ j ∈ s, 8 * (a' : ℝ≥0∞) * b'
      ≤ (plankEnclosureConstant C₀ : ℝ≥0∞) * volume ((K j).carrier : Set E₃))
    {D_K : ℕ}
    (hKdeg : ∀ i ∈ s, {j ∈ (s : Set ι) | j ≠ i ∧
      ¬ IsEssentiallyDistinct ((K i).carrier : Set E₃) ((K j).carrier : Set E₃)}.ncard ≤ D_K) :
    ∀ i ∈ s, {j ∈ (s : Set ι) | j ≠ i ∧ ¬ IsEssentiallyDistinct
          ((P i).carrier : Set E₃) ((P j).carrier : Set E₃)}.ncard + 1
        ≤ (D_K + 1) * (cardEssDistinctConvexInPrismConstant 3
            (((clusterDilationConstant : ℝ) ^ 3 * (plankEnclosureConstant C₀ : ℝ))⁻¹) + 1) := by
  classical
  intro i hi
  set Dcl : ℕ := cardEssDistinctConvexInPrismConstant 3
    (((clusterDilationConstant : ℝ) ^ 3 * (plankEnclosureConstant C₀ : ℝ))⁻¹) with hDcl
  set J : Finset ι := s.filter fun j => j ≠ i ∧
    ¬ IsEssentiallyDistinct ((P i).carrier : Set E₃) ((P j).carrier : Set E₃) with hJ
  have hJs : J ⊆ s := Finset.filter_subset _ _
  have hiJ : i ∉ J := by simp [hJ]
  set Ji : Finset ι := insert i J with hJi
  have hJis : Ji ⊆ s := Finset.insert_subset hi hJs
  let r : ι → ι → Prop := fun a b => a ≠ b ∧
    ¬ IsEssentiallyDistinct ((K a).carrier : Set E₃) ((K b).carrier : Set E₃)
  have hsymm : ∀ a b, r a b → r b a :=
    fun _ _ h => ⟨h.1.symm, fun h' => h.2 (isEssentiallyDistinct_symm h')⟩
  have hirr : ∀ a, ¬ r a a := fun _ h => h.1 rfl
  have hdeg : ∀ a ∈ Ji, {b ∈ (Ji : Set ι) | r b a}.ncard ≤ D_K := by
    intro a ha
    refine le_trans (Set.ncard_le_ncard ?_ (s.finite_toSet.subset fun _ hb => hb.1))
      (hKdeg a (hJis ha))
    rintro b ⟨hb, hba, hn⟩
    exact ⟨hJis hb, hba, fun h => hn (isEssentiallyDistinct_symm h)⟩
  obtain ⟨J', hJ'sub, hpair, hsum, hcard⟩ :=
    Kakeya.exists_pairwise_not_of_degree_le_card Ji r hsymm hirr hdeg
      (fun j => if j = i then (1 : ℝ≥0∞) else 0)
  have hiJ' : i ∈ J' := by
    by_contra hne
    have h1 : ∑ j ∈ Ji, (if j = i then (1 : ℝ≥0∞) else 0) = 1 := by
      rw [Finset.sum_ite_eq' Ji i]
      simp [hJi]
    have h2 : ∑ j ∈ J', (if j = i then (1 : ℝ≥0∞) else 0) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [if_neg]
      intro h
      subst h
      exact hne hj
    rw [h1, h2, mul_zero] at hsum
    exact absurd hsum (by simp)
  have hedJ' : (J' : Set ι).Pairwise fun a b =>
      IsEssentiallyDistinct ((K a).carrier : Set E₃) ((K b).carrier : Set E₃) := by
    intro a ha b hb hab
    by_contra hn
    exact hpair ha hb hab ⟨hab, hn⟩
  have hcl := plankClusterBound hC₀ ha' hab' hb1' J' P K
    (fun j hj => hKP j (hJis (hJ'sub hj))) (fun j hj => hKvol j (hJis (hJ'sub hj))) hedJ' i hiJ'
  have hJ'set : {j ∈ (J' : Set ι) | j ≠ i ∧ ¬ IsEssentiallyDistinct
      ((P i).carrier : Set E₃) ((P j).carrier : Set E₃)} = ((J'.erase i : Finset ι) : Set ι) := by
    ext j
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_erase]
    constructor
    · rintro ⟨hj, hji, -⟩
      exact ⟨hji, hj⟩
    · rintro ⟨hji, hj⟩
      refine ⟨hj, hji, ?_⟩
      have hmem : j ∈ Ji := hJ'sub hj
      rw [hJi, Finset.mem_insert] at hmem
      rcases hmem with h | h
      · exact absurd h hji
      · rw [hJ, Finset.mem_filter] at h
        exact h.2.2
  rw [hJ'set, Set.ncard_coe_finset, Finset.card_erase_of_mem hiJ'] at hcl
  have hJcard : {j ∈ (s : Set ι) | j ≠ i ∧ ¬ IsEssentiallyDistinct
      ((P i).carrier : Set E₃) ((P j).carrier : Set E₃)}.ncard = J.card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext j
    simp [hJ]
  have hJicard : Ji.card = J.card + 1 := Finset.card_insert_of_notMem hiJ
  rw [hJcard]
  calc J.card + 1 = Ji.card := hJicard.symm
    _ ≤ (D_K + 1) * J'.card := hcard
    _ ≤ (D_K + 1) * (Dcl + 1) := by
        apply Nat.mul_le_mul_left
        omega

/-- **The plank subfamily selection with the cardinality clause, from a degree bound on the
inner bodies**.  Same conclusion; the pairwise hypothesis becomes the non-ED degree bound
`hKdeg`, and the selection constant's floor is `(D_K + 1) · C^{sel}(C₀)` (P3 floor form): the
cluster degree is `(D_K + 1)(D + 1) − 1` by `plankClusterBound_of_degree`, and the greedy
selection retains `1/(degree + 1) = 1/((D_K + 1) C^{sel}(C₀))`. -/
theorem plankSubfamilySelection_card_of_degree {C₀ Csel : ℝ≥0} (hC₀ : 1 ≤ C₀) {D_K : ℕ}
    (hCsel : ((D_K : ℝ≥0) + 1) * plankSelectionConstant C₀ ≤ Csel)
    {a' b' : ℝ≥0} (ha' : 0 < a') (hab' : a' ≤ b') (hb1' : b' ≤ 1)
    {ι : Type*} (s : Finset ι) (P : ι → Plank a' b' hab' hb1') (K : ι → ConvexSpaceBody E₃)
    (hKP : ∀ j ∈ s, ((K j).carrier : Set E₃) ⊆ (P j).carrier)
    (hKvol : ∀ j ∈ s, 8 * (a' : ℝ≥0∞) * b'
      ≤ (plankEnclosureConstant C₀ : ℝ≥0∞) * volume ((K j).carrier : Set E₃))
    (hKdeg : ∀ i ∈ s, {j ∈ (s : Set ι) | j ≠ i ∧
      ¬ IsEssentiallyDistinct ((K i).carrier : Set E₃) ((K j).carrier : Set E₃)}.ncard ≤ D_K)
    (y : ι → ℝ≥0∞) :
    ∃ sel ⊆ s, (sel : Set ι).Pairwise
        (fun i j => IsEssentiallyDistinct ((P i).carrier : Set E₃) ((P j).carrier : Set E₃)) ∧
      (Csel : ℝ≥0∞)⁻¹ * ∑ j ∈ s, y j ≤ ∑ j ∈ sel, y j ∧
      (Csel : ℝ≥0∞)⁻¹ * ((s.card : ℕ) : ℝ≥0∞) ≤ ((sel.card : ℕ) : ℝ≥0∞) := by
  classical
  set Dcl : ℕ := cardEssDistinctConvexInPrismConstant 3
    (((clusterDilationConstant : ℝ) ^ 3 * (plankEnclosureConstant C₀ : ℝ))⁻¹) with hDcl
  have hpos : 1 ≤ (D_K + 1) * (Dcl + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  set D : ℕ := (D_K + 1) * (Dcl + 1) - 1 with hD
  have hD1 : D + 1 = (D_K + 1) * (Dcl + 1) := by omega
  let r : ι → ι → Prop := fun i j =>
    i ≠ j ∧ ¬ IsEssentiallyDistinct ((P i).carrier : Set E₃) ((P j).carrier : Set E₃)
  have hsymm : ∀ i j, r i j → r j i := by
    intro i j hij
    rcases hij with ⟨hne, hnot⟩
    exact ⟨hne.symm, fun hji => hnot (isEssentiallyDistinct_symm hji)⟩
  have hirr : ∀ i, ¬ r i i := fun i h => (h.1 rfl).elim
  have hDeg : ∀ i ∈ s, {j ∈ (s : Set ι) | r j i}.ncard ≤ D := by
    intro i hi
    have hbound := plankClusterBound_of_degree hC₀ ha' hab' hb1' s P K hKP hKvol hKdeg i hi
    rw [← hDcl] at hbound
    have hset : {j ∈ (s : Set ι) | r j i} = {j ∈ (s : Set ι) | j ≠ i ∧
        ¬ IsEssentiallyDistinct ((P i).carrier : Set E₃) ((P j).carrier : Set E₃)} := by
      ext j
      simp only [Set.mem_setOf_eq, r]
      constructor
      · rintro ⟨hjs, hjne, hnot⟩
        exact ⟨hjs, hjne, fun hij => hnot (isEssentiallyDistinct_symm hij)⟩
      · rintro ⟨hjs, hjne, hnot⟩
        exact ⟨hjs, hjne, fun hji => hnot (isEssentiallyDistinct_symm hji)⟩
    rw [hset]
    omega
  rcases Kakeya.exists_pairwise_not_of_degree_le_card s r hsymm hirr (D := D) hDeg y with
    ⟨sel, hselSub, hpair, hsum, hcard⟩
  have hcncl_pair : (sel : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct ((P i).carrier : Set E₃) ((P j).carrier : Set E₃)) := by
    intro i hi j hj hij
    by_cases hED : IsEssentiallyDistinct ((P i).carrier : Set E₃) ((P j).carrier : Set E₃)
    · exact hED
    · exact (hpair hi hj hij ⟨hij, hED⟩).elim
  have hpsc : plankSelectionConstant C₀ = (Dcl : ℝ≥0) + 1 := by
    simp [plankSelectionConstant, hDcl]
  have hD1' : ((D : ℝ≥0) + 1) = ((D_K : ℝ≥0) + 1) * plankSelectionConstant C₀ := by
    rw [hpsc]
    have h : ((D : ℝ≥0) + 1) = ((D + 1 : ℕ) : ℝ≥0) := by push_cast; ring
    rw [h, hD1]
    push_cast
    ring
  have hC_nn : (D : ℝ≥0) + 1 ≤ Csel := by rw [hD1']; exact hCsel
  have hC : ((D : ℝ≥0) + 1 : ℝ≥0∞) ≤ (Csel : ℝ≥0∞) := by exact_mod_cast hC_nn
  have h1leCsel : (1 : ℝ≥0) ≤ Csel :=
    le_trans (by norm_num : (1 : ℝ≥0) ≤ (D : ℝ≥0) + 1) hC_nn
  have hcnonzero : (Csel : ℝ≥0∞) ≠ 0 := by
    have hone : (1 : ℝ≥0∞) ≤ (Csel : ℝ≥0∞) := by exact_mod_cast h1leCsel
    exact (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) hone))
  have hclear : ∀ X Z : ℝ≥0∞, X ≤ (Csel : ℝ≥0∞) * Z → (Csel : ℝ≥0∞)⁻¹ * X ≤ Z := by
    intro X Z hXZ
    calc
      (Csel : ℝ≥0∞)⁻¹ * X ≤ (Csel : ℝ≥0∞)⁻¹ * ((Csel : ℝ≥0∞) * Z) := by gcongr
      _ = Z := by
        rw [← mul_assoc,
          ENNReal.inv_mul_cancel hcnonzero (ENNReal.coe_ne_top : (Csel : ℝ≥0∞) ≠ ⊤), one_mul]
  refine ⟨sel, hselSub, hcncl_pair, hclear _ _ ?_, hclear _ _ ?_⟩
  · have hsumNN : ∑ j ∈ s, y j ≤ ((D : ℝ≥0) + 1 : ℝ≥0∞) * ∑ j ∈ sel, y j := by
      simpa using hsum
    exact le_trans hsumNN (by gcongr)
  · have hcardE : ((s.card : ℕ) : ℝ≥0∞) ≤ ((D : ℝ≥0) + 1 : ℝ≥0∞) *
        ((sel.card : ℕ) : ℝ≥0∞) := by
      have h := (Nat.cast_le (α := ℝ≥0∞)).2 hcard
      simpa [Nat.cast_mul] using h
    exact le_trans hcardE (by gcongr)

/-- **The degree bound transports to the normalised images** (twin of
`Kakeya.VeryNotSticky.edImages_of_edSegments`, R31-a at a degree bound): essential distinctness
is preserved by every affine equivalence (`IsEssentiallyDistinct.image_affineEquiv`), so two
images that are *not* essentially distinct come from two segments that are not, and the count on
any subfamily `t ⊆ segs B` is at most the count on `segs B`. -/
theorem edImages_of_edSegments_degree {cfg : VeryNotSticky.{u}} (bd : BallData cfg)
    {B : bd.bι} (t : Finset bd.σ) (ht : t ⊆ bd.segs B) {D_K : ℕ}
    (hEDdeg : ∀ p ∈ bd.segs B, {q ∈ (bd.segs B : Set bd.σ) | q ≠ p ∧
      ¬ _root_.IsEssentiallyDistinct (bd.Y p).carrier (bd.Y q).carrier}.ncard ≤ D_K)
    (L : E₃ ≃ᵃ[ℝ] E₃) :
    ∀ p ∈ t, {q ∈ (t : Set bd.σ) | q ≠ p ∧
      ¬ _root_.IsEssentiallyDistinct (L '' (bd.Y p).carrier) (L '' (bd.Y q).carrier)}.ncard
        ≤ D_K := by
  intro p hp
  refine le_trans (Set.ncard_le_ncard ?_ ((bd.segs B).finite_toSet.subset fun _ hq => hq.1))
    (hEDdeg p (ht hp))
  rintro q ⟨hq, hqp, hn⟩
  exact ⟨ht hq, hqp, fun h => hn (h.image_affineEquiv L)⟩

end Kakeya.VeryNotSticky

end

end

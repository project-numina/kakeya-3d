/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.ChainUniform
public import Kakeya.MultiScaleFac.FibreDensity
public import Kakeya.Frostman
public import Kakeya.GridScale
public import Kakeya.FibreCommon
public import Kakeya.Thickness.ConvexSpaceBody
public import Kakeya.Sticky
public import Kakeya.Uniform
public import Mathlib.Tactic.Linarith.NNRealPreprocessor
public import Kakeya.Density
public import Kakeya.Tube.Basic
public import Kakeya.Tube.Nets
public import Kakeya.KatzTao
public import Kakeya.Mathlib.Finset
public import Mathlib.Tactic.NormNum.RealSqrt

/-!
# The stopping-time framework of GWZ §7.5–7.7

This file builds the combinatorial skeleton that GWZ Lemma 7.7(A) runs on: the geometric grid
of scales `δ^{k/M}`, the stopping-time test that decides whether a block of grid indices should
be split, and the maximal set of cut points produced by iterating that test.

**Two natural-number parameters, deliberately kept apart.**  `M` is the **grid length**: block
indices range over `0..M` and the scales are `gridScale δ M k = δ^{k/M}`, as in GWZ
Definition 2.1.  `N` is the **step budget**: it bounds the number of stopping-time steps and
indexes the exponent chain `η : ℕ → ℝ`, and GWZ obtain it from `∏ δ_j ≈ δ` together with
`δ_j < δ^{ε²}`, without reference to the grid.  The two used to be one parameter, tied to `ε` by
`ε = 1/√N`; the grid-side lemmas below now ask only for facts about `ε` and `M`, such as
`0 < ε`, `ε ≤ 1/4` and the threshold `4 ≤ ε · M`, so that the grid may be taken as long as one
likes.  The only link this file can supply is combinatorial — each cut consumes a grid point, so
at most `M - 1` cuts occur — and it appears as an explicit hypothesis `M ≤ N` of the two
stopping-time theorems.

The pieces are:

* `gridScale δ M k = δ^{k/M}` with the arithmetic the chain needs — the endpoints
  `gridScale δ M 0 = 1` and `gridScale δ M M = δ`, antitonicity in `k`, the ratio formula, and
  the `16`-separation of consecutive grid scales that
  `MultiScaleFac.frostmanConstant_fibre_le_prod` requires (valid once `δ ≤ 16^{-M}`).

* `BlockFrostman`, the per-block Frostman bound `C_F(𝕋_{σ_b∣σ_a}[i₀]) ≤ C · (σ_a/σ_b)^ζ`, and
  `SplitTest`, the stopping-time test: the block `(a,b)` splits if some grid index `c` well
  inside the block already carries the block bound on its fine half.  The multiplicative
  constant `C` is carried explicitly: the analytic steps that move a block bound between
  sub-blocks (`BlockRestrictStep`, `exists_blockFrostman_truncate`) genuinely lose a
  `δ`-independent factor, and pretending otherwise would make those steps false.

* `exists_maximal_cuts_abstract`, the stopping time itself, stated for abstract predicates on
  pairs of indices so that the induction is pure combinatorics on `Finset ℕ`.  Its output is a
  cut set `S` whose adjacent blocks all satisfy the block bound and are either short or fail the
  test.

* `cutChain`, which reads a cut set `S` as the decreasing chain `σ : Fin (J+3) → ℝ≥0` of scales
  demanded by `MultiScaleFac.frostmanConstant_fibre_le_prod`, together with the verification of
  every hypothesis of that theorem and the resulting product bound
  `frostmanConstant_fibre_le_prod_of_cuts`.

The analytic step that transfers a block bound from a block to its coarse sub-block (GWZ's
appeal to the inherited upward property, `ConvexSpaceBody.IsFrostmanIn.inherited_upwards_uniform`)
is packaged as the predicate `BlockRestrictStep` and enters `exists_maximal_cuts` as the
hypothesis `hrestrict`.  Keeping it a hypothesis is what makes the stopping time itself
independent of the geometry; it is the only interface this file leaves open, and it is where the
exponent gap `η k ≤ ε · η (k+1)` of Lemma 7.7(A) is spent.

Because `ConvexSpaceBody.IsFrostmanIn.inherited_upwards_uniform` concludes at the constant
`C' * C` rather than at `C`, each cut multiplies the block constant by a fixed `δ`-independent
factor `C'`.  After `m` cuts the constant is `C' ^ m`, and `m < N` bounds it by `C' ^ N`; that
uniform bound is precisely the source of the existentially quantified constant `C` in the
statement of GWZ Lemma 7.7(A).

`⪅` does not appear: every bound carries an explicit constant, as required by.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Real Metric
open Tube

namespace Kakeya

open StickyKakeya
open MultiScaleFac

namespace MultiScaleFac

open _root_.StickyKakeya
open scoped NNReal ENNReal

universe u

/-! ### The stopping time -/

/-- **A set of grid indices with pairwise gaps at least `w` is small.**  If any two distinct
elements of `S ⊆ [0, M]` differ by at least `w`, then `x ↦ x / w` is injective on `S` and lands in
`[0, M / w]`, so `S` has at most `M / w + 1` elements.  This replaces the crude "each cut consumes a
grid point" bound of `exists_maximal_cuts_abstract`. -/
private theorem card_le_div_succ_of_gap {w M : ℕ} (hw : 0 < w) {S : Finset ℕ}
    (hsub : S ⊆ Finset.range (M + 1))
    (hgap : ∀ x ∈ S, ∀ y ∈ S, x < y → x + w ≤ y) :
    S.card ≤ M / w + 1 := by
  classical
  have key : ∀ x ∈ S, ∀ y ∈ S, x < y → x / w + 1 ≤ y / w := by
    intro x hx y hy hxy
    rw [← Nat.add_div_right x hw]
    exact Nat.div_le_div_right (hgap x hx y hy hxy)
  have hcard := Finset.card_le_card_of_injOn (t := Finset.range (M / w + 1)) (fun x => x / w)
    (fun x hx => Finset.mem_range.mpr (Nat.lt_succ_of_le
      (Nat.div_le_div_right (Nat.le_of_lt_succ (Finset.mem_range.mp (hsub hx))))))
    (fun x hx y hy h => by
      have h' : x / w = y / w := h
      rcases lt_trichotomy x y with hxy | hxy | hxy
      · have := key x hx y hy hxy; omega
      · exact hxy
      · have := key y hy x hx hxy; omega)
  simpa using hcard

/-- **A `w`-separated cut set of `[0,M]` has at most `N` cuts** when `M ≤ w N`.
`card_le_div_succ_of_gap` bounds `S.card` by `M / w + 1`, so `S.card = m + 2` gives `m + 1 ≤ M / w`;
multiplying by `w` and using `(M / w) w ≤ M ≤ w N` gives `(m+1) w ≤ N w`, whence `m + 1 ≤ N`. -/
private theorem succ_le_of_card_gap {M N w m : ℕ} (hw : 0 < w) (hwN : M ≤ w * N)
    {S : Finset ℕ} (hsub : S ⊆ Finset.range (M + 1))
    (hgap : ∀ x ∈ S, ∀ y ∈ S, x < y → x + w ≤ y) (hcard : S.card = m + 2) :
    m + 1 ≤ N := by
  have hcnt : S.card ≤ M / w + 1 := card_le_div_succ_of_gap hw hsub hgap
  have hm1 : m + 1 ≤ M / w := by omega
  have hmw : (m + 1) * w ≤ (M / w) * w := Nat.mul_le_mul_right w hm1
  have hdivM : (M / w) * w ≤ M := Nat.div_mul_le_self M w
  have hmwN : (m + 1) * w ≤ w * N := le_trans (le_trans hmw hdivM) hwN
  have hmwN' : (m + 1) * w ≤ N * w := by
    calc
      (m + 1) * w ≤ w * N := hmwN
      _ = N * w := mul_comm w N
  exact Nat.le_of_mul_le_mul_right hmwN' hw

/-- **Inserting a cut that sits `w` inside its block keeps the cut set `w`-separated.**

The new point `c` lies in the adjacent block `(a,b)` at distance at least `w` from both ends, and
`(a,b)` contains no old point, so every old point is either `≤ a` or `≥ b`; the gap to `c` is
therefore at least `w` on both sides, and gaps between old points are unchanged. -/
private theorem gap_insert_of_cut {w a b c : ℕ} {S : Finset ℕ}
    (hadj : ∀ x ∈ S, ¬(a < x ∧ x < b))
    (hac : a + w ≤ c) (hcb : c + w ≤ b) (hac' : a < c) (hcb' : c < b)
    (hgap : ∀ x ∈ S, ∀ y ∈ S, x < y → x + w ≤ y) :
    ∀ x ∈ insert c S, ∀ y ∈ insert c S, x < y → x + w ≤ y := by
  intro x hx y hy hxy
  rcases Finset.mem_insert.mp hx with hxc | hxS
  · rw [hxc] at hxy ⊢
    rcases Finset.mem_insert.mp hy with hyc | hyS
    · rw [hyc] at hxy ⊢
      exact (lt_irrefl c hxy).elim
    · have hby : b ≤ y := by
        by_contra h
        have hyltb : y < b := Nat.lt_of_not_ge h
        have hacy : a < y := lt_trans hac' hxy
        exact hadj y hyS ⟨hacy, hyltb⟩
      exact le_trans hcb hby
  · rcases Finset.mem_insert.mp hy with hyc | hyS
    · rw [hyc] at hxy ⊢
      have hxa : x ≤ a := by
        by_contra h
        have halt : a < x := Nat.lt_of_not_ge h
        have hxlb : x < b := lt_trans hxy hcb'
        exact hadj x hxS ⟨halt, hxlb⟩
      exact le_trans (Nat.add_le_add_right hxa w) hac
    · exact hgap x hxS y hyS hxy

/-- **The block-bound invariant survives one cut, in the stateful form.**  After inserting `c` into
`S`, an adjacent pair of `insert c S` is either one of the two halves `(a,c)`, `(c,b)` of the block
that was cut — where the split supplies the bound at the new state — or an untouched adjacent pair
of `S`, whose old bound is raised by `hmono` and then transported by `hdescend`. -/
private theorem invState_insert_of_cut {σ : Type*} {Good : ℕ → ℕ → ℕ → σ → Prop}
    {Rel : ℕ → σ → σ → Prop} {M N : ℕ}
    (hmono : ∀ j j' : ℕ, j ≤ j' → j' ≤ N → ∀ a b : ℕ, a < b → ∀ x : σ, Good j a b x → Good j' a b x)
    (hdescend : ∀ j a b : ℕ, a < b → b ≤ M → ∀ x y : σ, Rel 1 x y → Good j a b x → Good j a b y)
    {S : Finset ℕ} {m : ℕ} {x y : σ} {a b c : ℕ}
    (hsub : S ⊆ Finset.range (M + 1)) (haS : a ∈ S) (hbS : b ∈ S)
    (hadj : ∀ z ∈ S, ¬(a < z ∧ z < b)) (hac : a < c) (hcb : c < b) (hle1 : m + 1 ≤ N)
    (hxy : Rel 1 x y) (gac : Good (m + 1) a c y) (gcb : Good (m + 1) c b y)
    (hINV : ∀ p ∈ S, ∀ q ∈ S, p < q → (∀ z ∈ S, ¬(p < z ∧ z < q)) → Good m p q x) :
    ∀ p ∈ insert c S, ∀ q ∈ insert c S, p < q → (∀ z ∈ insert c S, ¬(p < z ∧ z < q)) →
      Good (m + 1) p q y := by
  intro a' ha' b' hb' hab' hadj'
  rcases Finset.mem_insert.mp ha' with ha'c | haS'
  · rw [ha'c] at hab' hadj'
    have hbS' : b' ∈ S := by
      rcases Finset.mem_insert.mp hb' with hb'c | hbS''
      · rw [hb'c] at hab'
        exact (lt_irrefl c hab').elim
      · exact hbS''
    have hb_le_b' : b ≤ b' := by
      by_contra h
      have hb'ltb : b' < b := Nat.lt_of_not_ge h
      have ha_lt_b' : a < b' := lt_trans hac hab'
      exact hadj b' hbS' ⟨ha_lt_b', hb'ltb⟩
    have hb'_le_b : b' ≤ b := by
      by_contra h
      have hblt : b < b' := Nat.lt_of_not_ge h
      exact hadj' b (Finset.mem_insert.mpr (Or.inr hbS)) ⟨hcb, hblt⟩
    have hb'_eq : b' = b := Nat.le_antisymm hb'_le_b hb_le_b'
    rw [ha'c, hb'_eq]
    exact gcb
  · rcases Finset.mem_insert.mp hb' with hb'c | hbS'
    · rw [hb'c] at hab' hadj'
      have ha_le_a' : a ≤ a' := by
        by_contra h
        have ha'lt : a' < a := Nat.lt_of_not_ge h
        exact hadj' a (Finset.mem_insert.mpr (Or.inr haS)) ⟨ha'lt, hac⟩
      have ha'_le_a : a' ≤ a := by
        by_contra h
        have halt : a < a' := Nat.lt_of_not_ge h
        have ha'ltb : a' < b := lt_trans hab' hcb
        exact hadj a' haS' ⟨halt, ha'ltb⟩
      have ha'_eq : a' = a := Nat.le_antisymm ha'_le_a ha_le_a'
      rw [ha'_eq, hb'c]
      exact gac
    · have hadjS : ∀ y ∈ S, ¬(a' < y ∧ y < b') := by
        intro z hz hmid
        exact hadj' z (Finset.mem_insert.mpr (Or.inr hz)) hmid
      have hgS : Good m a' b' x := hINV a' haS' b' hbS' hab' hadjS
      have hgS1 : Good (m + 1) a' b' x :=
        hmono m (m + 1) (Nat.le_succ m) hle1 a' b' hab' x hgS
      have hb'M : b' ≤ M := Nat.le_of_lt_succ (Finset.mem_range.mp (hsub hbS'))
      exact hdescend (m + 1) a' b' hab' hb'M x y hxy hgS1

/-- **The induction behind `exists_maximal_cuts_abstract_state_margin`.**  The loop of
`exists_maximal_cuts_abstract_state` run with the extra invariant that the cut points are pairwise
`w`-separated, so that the terminal index is bounded through `succ_le_of_card_gap` rather than
through a hypothesis `M ≤ N`.  The recursion is on `n = M + 1 - S.card`. -/
private theorem exists_maximal_cuts_abstract_state_margin_aux {σ : Type*} (M N w : ℕ)
    (hw : 0 < w) (hwN : M ≤ w * N)
    (Good Test : ℕ → ℕ → ℕ → σ → Prop) (Long : ℕ → ℕ → Prop) (Rel : ℕ → σ → σ → Prop) (x₀ : σ)
    (hcomp : ∀ (k l : ℕ) (x y z : σ), Rel k x y → Rel l y z → Rel (k + l) x z)
    (hmono : ∀ j j' : ℕ, j ≤ j' → j' ≤ N → ∀ a b : ℕ, a < b → ∀ x : σ, Good j a b x → Good j' a b x)
    (hdescend : ∀ j a b : ℕ, a < b → b ≤ M → ∀ x y : σ, Rel 1 x y → Good j a b x → Good j a b y)
    (hsplit : ∀ j a b : ℕ, j + 1 ≤ N → a < b → b ≤ M → Long a b → ∀ x : σ, Good j a b x →
      Test (j + 1) a b x →
      ∃ (y : σ) (c : ℕ), Rel 1 x y ∧ a + w ≤ c ∧ c + w ≤ b ∧
        Good (j + 1) a c y ∧ Good (j + 1) c b y) :
    ∀ n : ℕ, ∀ S : Finset ℕ, ∀ m : ℕ, ∀ x : σ,
      0 ∈ S → M ∈ S → S ⊆ Finset.range (M + 1) → S.card = m + 2 →
      (∀ p ∈ S, ∀ q ∈ S, p < q → p + w ≤ q) → Rel m x₀ x →
      (∀ a ∈ S, ∀ b ∈ S, a < b → (∀ y ∈ S, ¬(a < y ∧ y < b)) → Good m a b x) →
      n = M + 1 - S.card →
      ∃ (S' : Finset ℕ) (m' : ℕ) (x' : σ), m' < N ∧ Rel m' x₀ x' ∧ 0 ∈ S' ∧ M ∈ S' ∧
        S' ⊆ Finset.range (M + 1) ∧ S'.card = m' + 2 ∧
        ∀ a ∈ S', ∀ b ∈ S', a < b → (∀ y ∈ S', ¬(a < y ∧ y < b)) →
          Good m' a b x' ∧ (¬ Long a b ∨ ¬ Test (m' + 1) a b x') := by
  classical
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih S m x h0 hMmem hsub hcard hgap hRel hINV hn
  have hle1 : m + 1 ≤ N := succ_le_of_card_gap hw hwN hsub hgap hcard
  by_cases hsplit_case : ∃ a ∈ S, ∃ b ∈ S, a < b ∧
      (∀ y ∈ S, ¬(a < y ∧ y < b)) ∧ Long a b ∧ Test (m + 1) a b x
  · rcases hsplit_case with ⟨a, haS, b, hbS, hab, hadj, hlong, htest⟩
    have hbM : b ≤ M := by
      exact Nat.le_of_lt_succ (Finset.mem_range.mp (hsub hbS))
    have hg : Good m a b x := hINV a haS b hbS hab hadj
    have hgm : Good (m + 1) a b x := hmono m (m + 1) (Nat.le_succ m) hle1 a b hab x hg
    rcases hsplit m a b hle1 hab hbM hlong x hg htest with ⟨y, c, hxy, hac, hcb, gac, gcb⟩
    have hac' : a < c := by omega
    have hcb' : c < b := by omega
    have hc_notS : c ∉ S := by
      intro hcS
      exact hadj c hcS ⟨hac', hcb'⟩
    have hcR : c ∈ Finset.range (M + 1) := by
      exact Finset.mem_range.mpr (by omega)
    have hS'card : (insert c S).card = (m + 1) + 2 := by
      simpa [hcard] using (Finset.card_insert_of_notMem hc_notS)
    have hS'Sub : insert c S ⊆ Finset.range (M + 1) := by
      intro x hx
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hxS
      · exact hcR
      · exact hsub hxS
    have h0in : 0 ∈ insert c S := Finset.mem_insert.mpr (Or.inr h0)
    have hMin : M ∈ insert c S := Finset.mem_insert.mpr (Or.inr hMmem)
    have hRel' : Rel (m + 1) x₀ y := (hcomp m 1 x₀ x y) hRel hxy
    have hINV' : ∀ p ∈ insert c S, ∀ q ∈ insert c S, p < q →
        (∀ z ∈ insert c S, ¬(p < z ∧ z < q)) → Good (m + 1) p q y := by
      exact invState_insert_of_cut hmono hdescend hsub haS hbS hadj hac' hcb' hle1 hxy gac gcb hINV
    have hgap' : ∀ p ∈ insert c S, ∀ q ∈ insert c S, p < q → p + w ≤ q := by
      exact gap_insert_of_cut hadj hac hcb hac' hcb' hgap
    have hle_card : (insert c S).card ≤ M + 1 := by
      have hle2 : (insert c S).card ≤ (Finset.range (M + 1)).card :=
        Finset.card_le_card hS'Sub
      simpa [Finset.card_range] using hle2
    have hmeasure : M + 1 - (insert c S).card < n := by
      have hci : (insert c S).card = S.card + 1 := Finset.card_insert_of_notMem hc_notS
      omega
    exact (ih (M + 1 - (insert c S).card) hmeasure) (insert c S) (m + 1) y h0in hMin hS'Sub
      hS'card hgap' hRel' hINV' rfl
  · refine ⟨S, m, x, by omega, hRel, h0, hMmem, hsub, hcard, ?_⟩
    intro a haS b hbS hab hadj
    constructor
    · exact hINV a haS b hbS hab hadj
    · by_cases hl : Long a b
      · right
        intro ht
        exact hsplit_case ⟨a, haS, b, hbS, hab, hadj, hl, ht⟩
      · exact Or.inl hl

/-- **The maximal cut set with a refining state, with the step bound decoupled from the grid
length.**  The common refinement of `exists_maximal_cuts_abstract_state` and
`exists_maximal_cuts_abstract_margin`: the stopping time carries a state refined at every cut, *and*
the number of cuts is bounded through the margin `w` rather than through the crude `M ≤ N`.  This is
what the refined Lemma 7.7(A) needs on the diverging grid of GWZ Definition 2.1. -/
theorem exists_maximal_cuts_abstract_state_margin {σ : Type*} (M N w : ℕ)
    (hw : 0 < w) (hwM : w ≤ M) (hwN : M ≤ w * N)
    (Good Test : ℕ → ℕ → ℕ → σ → Prop) (Long : ℕ → ℕ → Prop) (Rel : ℕ → σ → σ → Prop) (x₀ : σ)
    (hrefl : ∀ x : σ, Rel 0 x x)
    (hcomp : ∀ (k l : ℕ) (x y z : σ), Rel k x y → Rel l y z → Rel (k + l) x z)
    (hGood : Good 0 0 M x₀)
    (hmono : ∀ j j' : ℕ, j ≤ j' → j' ≤ N → ∀ a b : ℕ, a < b → ∀ x : σ, Good j a b x → Good j' a b x)
    (hdescend : ∀ j a b : ℕ, a < b → b ≤ M → ∀ x y : σ, Rel 1 x y → Good j a b x → Good j a b y)
    (hsplit : ∀ j a b : ℕ, j + 1 ≤ N → a < b → b ≤ M → Long a b → ∀ x : σ, Good j a b x →
      Test (j + 1) a b x →
      ∃ (y : σ) (c : ℕ), Rel 1 x y ∧ a + w ≤ c ∧ c + w ≤ b ∧
        Good (j + 1) a c y ∧ Good (j + 1) c b y) :
    ∃ (S : Finset ℕ) (m : ℕ) (x : σ), m < N ∧ Rel m x₀ x ∧ 0 ∈ S ∧ M ∈ S ∧
      S ⊆ Finset.range (M + 1) ∧ S.card = m + 2 ∧
      ∀ a ∈ S, ∀ b ∈ S, a < b → (∀ y ∈ S, ¬(a < y ∧ y < b)) →
        Good m a b x ∧ (¬ Long a b ∨ ¬ Test (m + 1) a b x) := by
  refine exists_maximal_cuts_abstract_state_margin_aux M N w hw hwN Good Test Long Rel x₀ hcomp
    hmono hdescend hsplit
    (M + 1 - ({0, M} : Finset ℕ).card) ({0, M} : Finset ℕ) 0 x₀ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  · simp
  · simp
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxN
    · exact Finset.mem_range.mpr (by omega)
    · have hxeq : x = M := by simpa using hxN
      rw [hxeq]
      exact Finset.mem_range.mpr (by omega)
  · have h0neN : (0 : ℕ) ≠ M := by omega
    have h0mn : 0 ∉ ({M} : Finset ℕ) := by
      intro h
      exact h0neN (by simpa using h)
    simp [Finset.card_insert_of_notMem h0mn]
  · intro x hx y hy hxy
    rcases Finset.mem_insert.mp hx with rfl | hxM
    · rcases Finset.mem_insert.mp hy with rfl | hyM
      · exact (lt_irrefl 0 hxy).elim
      · have hyeq : y = M := by simpa using hyM
        rw [hyeq]
        simpa using hwM
    · have hxeq : x = M := by simpa using hxM
      rw [hxeq] at hxy ⊢
      rcases Finset.mem_insert.mp hy with rfl | hyM
      · simp at hxy
      · have hyeq : y = M := by simpa using hyM
        rw [hyeq] at hxy
        exact (lt_irrefl M hxy).elim
  · exact hrefl x₀
  · intro a ha b hb hab hadj
    have ha_eq : a = 0 := by
      rcases Finset.mem_insert.mp ha with h0 | hN0
      · exact h0
      · exfalso
        have haN : a = M := by simpa using hN0
        rcases Finset.mem_insert.mp hb with hb0 | hbN
        · omega
        · have hbN' : b = M := by simpa using hbN
          omega
    have hb_eq : b = M := by
      rcases Finset.mem_insert.mp hb with hb0 | hbN
      · exfalso
        omega
      · simpa using hbN
    rw [ha_eq, hb_eq]
    exact hGood

section Geometry

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

/-- **The per-block Frostman bound at a single anchor.**  `BlockFrostmanAt s T M C ζ a b i₀` says
that the fibre family `𝕋[T_{i₀}^{(σ_a)}] = {i : T_i ⊆ T_{i₀}^{(σ_a)}}`, with its members thickened
to the fine grid scale `σ_b`, has Frostman constant at most `C · (σ_a/σ_b)^ζ` in the doubled anchor
`T_{i₀}^{(2σ_a)}`.  Here `M` is the **grid length**, `σ_k = gridScale δ M k = δ^{k/M}`, and the
index set is fixed at the leaf scale, which is GWZ's own convention. -/
def BlockFrostmanAt {δ : ℝ≥0} (s : Finset ι) (T : ι → Tube δ E) (M : ℕ) (C : ℝ≥0) (ζ : ℝ)
    (a b : ℕ) (i₀ : ι) : Prop :=
  ConvexSpaceBody.frostmanConstant (fibreIndex s T δ (gridScale δ M a) i₀)
      (fibreBodies T (gridScale δ M b))
      ((T i₀).rescale (2 * gridScale δ M a)).toConvexSpaceBody
    ≤ (C : ℝ≥0∞) * ENNReal.ofReal (((gridScale δ M a : ℝ) / (gridScale δ M b : ℝ)) ^ ζ)

/-- **The per-block Frostman bound.**  `BlockFrostman s T M C ζ a b` says that for every anchor
`i₀ ∈ s` the fibre family `𝕋_{σ_b∣σ_a}[i₀]` of tubes thickened to the fine grid scale `σ_b` and
contained in `T_{i₀}^{(σ_a)}` has Frostman constant at most `C · (σ_a/σ_b)^ζ`, where
`σ_k = gridScale δ M k`.  This is the quantity GWZ Lemma 7.7(A) tracks along the dividing scales. -/
def BlockFrostman {δ : ℝ≥0} (s : Finset ι) (T : ι → Tube δ E) (M : ℕ) (C : ℝ≥0) (ζ : ℝ)
    (a b : ℕ) : Prop :=
  ∀ i₀ ∈ s, BlockFrostmanAt s T M C ζ a b i₀

omit [Nontrivial E] in
/-- **The block bound at a single anchor weakens as the constant and the exponent grow.**  The
one-anchor form of `BlockFrostman.mono`; the ratio `σ_a/σ_b` is at least `1`, so raising the
exponent enlarges the right-hand side. -/
private theorem BlockFrostmanAt.mono {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {s : Finset ι}
    {T : ι → Tube δ E} {M : ℕ} {C C' : ℝ≥0} {ζ ζ' : ℝ} (hCC' : C ≤ C') (_hζ : 0 ≤ ζ)
    (hζζ' : ζ ≤ ζ') {a b : ℕ} (hab : a ≤ b) {i₀ : ι}
    (h : BlockFrostmanAt s T M C ζ a b i₀) : BlockFrostmanAt s T M C' ζ' a b i₀ := by
  let r : ℝ := (gridScale δ M a : ℝ) / (gridScale δ M b : ℝ)
  have hb_pos : 0 < (gridScale δ M b : ℝ) := by
    exact_mod_cast (gridScale_pos hδ M b)
  have hblea : gridScale δ M b ≤ gridScale δ M a := gridScale_antitone hδ hδ1 M hab
  have hr1 : (1 : ℝ) ≤ r := by
    dsimp [r]
    exact (one_le_div hb_pos).mpr (by exact_mod_cast hblea)
  calc
    ConvexSpaceBody.frostmanConstant (fibreIndex s T δ (gridScale δ M a) i₀)
        (fibreBodies T (gridScale δ M b))
        ((T i₀).rescale (2 * gridScale δ M a)).toConvexSpaceBody
        ≤ (C : ℝ≥0∞) * ENNReal.ofReal (((gridScale δ M a : ℝ) / (gridScale δ M b : ℝ)) ^ ζ) :=
        h
    _ ≤ (C' : ℝ≥0∞) * ENNReal.ofReal (r ^ ζ) := by
      dsimp [r]
      exact mul_le_mul' (ENNReal.coe_le_coe.mpr hCC') le_rfl
    _ ≤ (C' : ℝ≥0∞) * ENNReal.ofReal (r ^ ζ') := by
      exact mul_le_mul' le_rfl
        (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hr1 hζζ'))

omit [Nontrivial E] in
/-- **The block bound weakens as the constant and the exponent grow.**  Since `a ≤ b` makes the
ratio `σ_a/σ_b` at least `1`, raising the exponent enlarges the right-hand side; raising the
constant obviously does.  This is the `hmono` hypothesis of `exists_maximal_cuts_abstract`: the
blocks that a split does not touch keep their bound when the stopping time's constant and
exponent indices advance. -/
theorem BlockFrostman.mono {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {s : Finset ι}
    {T : ι → Tube δ E} {M : ℕ} {C C' : ℝ≥0} {ζ ζ' : ℝ} (hCC' : C ≤ C') (hζ : 0 ≤ ζ)
    (hζζ' : ζ ≤ ζ') {a b : ℕ} (hab : a ≤ b)
    (h : BlockFrostman s T M C ζ a b) : BlockFrostman s T M C' ζ' a b := by
  intro i₀ hi₀
  exact (h i₀ hi₀).mono hδ hδ1 hCC' hζ hζζ' hab

end Geometry


/-! ### Arithmetic of the sampling exponent `ε = 1/√N`

Three throwaway facts about `ε = 1 / Real.sqrt N` under `16 ≤ N`.  They exist so that the
grid-side lemmas below can be stated in terms of `ε` and the grid length alone, and every call
site that still carries `16 ≤ N` and `ε = 1/√N` can discharge them in one step. -/


/-! ### The exponent chain -/

section Geometry2

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}


end Geometry2

section GeometryUniform

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]


/- Removed: `exists_blockFrostman_truncate`.  Reaching a grid index interior to a block is now
done directly in `MultiScaleFac.frostmanConstant_gridScale_le_of_cuts` by anchor deflation
(`MultiScaleFac.anchorGraded_of_isUniformAtScale` followed by
`MultiScaleFac.frostmanConstant_fibre_le_of_card_le_sharp`), which is the same mechanism with an
honest exponent: the loss is a power of `σ_a/σ_k` that no `δ`-independent constant can absorb,
so it belongs in that lemma's conclusion rather than in a separate block-bound step. -/

/- **The block bound descends to a fine sub-block, at the cost of a `δ`-independent factor and
of the ratio by which the parent shrank.**

`BlockRestrictStep` shrinks the *fine* end of a block; this lemma shrinks the *coarse* end,
replacing the parent thickening `T_{i₀}^{(σ_a)}` by the smaller `T_{i₀}^{(σ_k)}` for `a ≤ k < b`.
It is what reaches a grid index lying strictly inside a block, and nothing else in this
development provides that direction.

The fibre index set shrinks (`fibreIndex` is monotone in the parent scale) and the anchor body
shrinks with it, so the numerator `Δ_max` only decreases; the denominator
`Δ(𝕋_{σ_b∣σ_k}, T^{(σ_k)})` is comparable to `Δ(𝕋_{σ_b∣σ_a}, T^{(σ_a)})` up to a factor controlled
by the uniformity constant `Cu`, because the number of `σ_b`-tubes in a `σ_a`-parent is the number
in a `σ_k`-parent times the `σ_k`-branching, which the packing bound compares to the volume ratio
`(σ_a/σ_k)^{n-1}`.  Hence the loss is `Cl · (σ_a/σ_k)^ζ`, the second factor being pure rebasing of
the right-hand side from `(σ_a/σ_b)^ζ` to `(σ_k/σ_b)^ζ`.

The rebasing factor is why alternative (i) of GWZ Lemma 7.7(A) needs every block to be *short*:
`(σ_a/σ_k)^ζ ≤ (σ_a/σ_b)^ζ ≤ δ^{-εζ}` holds exactly for a short block, and a factor `δ^{-εζ}` is
affordable only against the `5ε` exponent budget, never against a `δ`-independent constant.

**How the anchor-shrinking count is reached.**  Unwinding both sides through
`ConvexSpaceBody.frostmanConstant_eq_maxDensity_div`, the numerator `Δ_max` only decreases (the
`σ_k`-fibre is a subset of the `σ_a`-fibre), so the whole content is the denominator, and it
reduces to the count comparison

`|s_{σ_b∣σ_a}(i₀)| ≤ Cl · (σ_a/σ_k)^{2n} · |s_{σ_b∣σ_k}(i₀)|`.

That is exactly `MultiScaleFac.anchorGraded_of_isUniformAtScale`, applied at a grid scale below
`σ_k` — the `8`-fold inflation it leaves on the right is absorbed by the `16`-separation of the
grid.  The exponent is `2n`, not the `n-1` one might expect from the anchor volumes: the tube
parameters are direction, transverse offset and longitudinal offset, each ranging over an
interval of length `σ_a`, so `2n-1` is already forced and `2n` is what the `L¹` endpoint-metric
packing count delivers.  The surplus is harmless because the ratio `σ_a/σ_k` is at most
`δ^{-(1+ε)/N}` for a short block, so the whole loss is `δ^{-O(1/N)} = δ^{-O(ε²)}`. -/


end GeometryUniform

/-! ### From a cut set to the chain of scales -/

/-- Consecutive values of the order isomorphism `Fin (n+1) ≃o S` are adjacent in `S`: they are
strictly increasing and nothing of `S` lies strictly between them. -/
theorem orderIsoOfFin_castSucc_lt_succ {S : Finset ℕ} {n : ℕ} (hcard : S.card = n + 1)
    (m : Fin n) :
    ((S.orderIsoOfFin hcard m.castSucc : ℕ) < (S.orderIsoOfFin hcard m.succ : ℕ)) ∧
      ∀ x ∈ S, ¬((S.orderIsoOfFin hcard m.castSucc : ℕ) < x ∧
        x < (S.orderIsoOfFin hcard m.succ : ℕ)) := by
  constructor
  · simp
  · intro x hx hlt
    let j : Fin (n + 1) := (S.orderIsoOfFin hcard).symm ⟨x, hx⟩
    have huS : (S.orderIsoOfFin hcard m.castSucc : S) < (⟨x, hx⟩ : S) := hlt.1
    have hj1 : m.castSucc < j := by
      simpa [j] using (S.orderIsoOfFin hcard).symm.lt_iff_lt.mpr huS
    have hvS : (⟨x, hx⟩ : S) < (S.orderIsoOfFin hcard m.succ : S) := hlt.2
    have hj2 : j < m.succ := by
      simpa [j] using (S.orderIsoOfFin hcard).symm.lt_iff_lt.mpr hvS
    have hj3 : ¬ (m.castSucc < j ∧ j < m.succ) := by
      intro hb
      have hb1 : (m.castSucc : ℕ) < (j : ℕ) := (Fin.lt_def).mp hb.1
      have hb2 : (j : ℕ) < (m.succ : ℕ) := (Fin.lt_def).mp hb.2
      have h1 : m.val < (j : ℕ) := by
        simpa [Fin.val_castSucc] using hb1
      have h2 : (j : ℕ) < m.val + 1 := by
        simpa [Fin.val_succ] using hb2
      omega
    exact hj3 ⟨hj1, hj2⟩

/-- The smallest element of a cut set containing `0` is `0`. -/
theorem orderIsoOfFin_zero_eq {S : Finset ℕ} {n : ℕ} (hcard : S.card = n + 1) (h0 : 0 ∈ S) :
    (S.orderIsoOfFin hcard 0 : ℕ) = 0 := by
  let e : Fin (n + 1) ≃o (S : Set ℕ) := S.orderIsoOfFin hcard
  let j : Fin (n + 1) := e.symm ⟨0, h0⟩
  have hzero : (e j : ℕ) = 0 := by
    change ((e (e.symm ⟨0, h0⟩) : (S : Set ℕ)) : ℕ) = 0
    rw [OrderIso.apply_symm_apply]
  have hle : (e 0 : ℕ) ≤ (e j : ℕ) := by
    exact (OrderIso.le_iff_le e).mpr (Fin.zero_le j)
  rw [hzero] at hle
  exact le_antisymm hle (Nat.zero_le _)

/-- The largest element of a cut set inside `[0,N]` containing `N` is `N`. -/
theorem orderIsoOfFin_last_eq {S : Finset ℕ} {n N : ℕ} (hcard : S.card = n + 1) (hN : N ∈ S)
    (hsub : S ⊆ Finset.range (N + 1)) :
    (S.orderIsoOfFin hcard (Fin.last n) : ℕ) = N := by
  let e : Fin (n + 1) ≃o (S : Set ℕ) := S.orderIsoOfFin hcard
  let j : Fin (n + 1) := e.symm ⟨N, hN⟩
  have hN_val : (e j : ℕ) = N := by
    change ((e (e.symm ⟨N, hN⟩) : (S : Set ℕ)) : ℕ) = N
    rw [OrderIso.apply_symm_apply]
  have hle_sub : (e j : ℕ) ≤ (e (Fin.last n) : ℕ) := by
    exact (OrderIso.le_iff_le e).mpr (Fin.le_last j)
  rw [hN_val] at hle_sub
  have hv : (e (Fin.last n) : ℕ) ∈ S := (e (Fin.last n)).property
  have hvrange : (e (Fin.last n) : ℕ) ∈ Finset.range (N + 1) := hsub hv
  have hupper : (e (Fin.last n) : ℕ) ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hvrange)
  exact le_antisymm hupper hle_sub

/-- Every element of a cut set inside `[0,N]` is at most `N`. -/
theorem orderIsoOfFin_le {S : Finset ℕ} {n N : ℕ} (hcard : S.card = n + 1)
    (hsub : S ⊆ Finset.range (N + 1)) (k : Fin (n + 1)) :
    (S.orderIsoOfFin hcard k : ℕ) ≤ N := by
  have hv : (S.orderIsoOfFin hcard k : ℕ) ∈ S :=
    (S.orderIsoOfFin hcard k).property
  have hvrange : (S.orderIsoOfFin hcard k : ℕ) ∈ Finset.range (N + 1) := hsub hv
  exact Nat.le_of_lt_succ (Finset.mem_range.mp hvrange)


/-! ### Reindexing a cut set as a chain

`MultiScaleFac.exists_maximal_cuts` returns a cut set with `S.card = m + 2`, whereas `cutChain`
and `MultiScaleFac.frostmanConstant_fibre_le_prod_of_cuts` are indexed by `Fin (J + 3)`.  The two
match with `J = m - 1`, which needs `1 ≤ m`; the degenerate case `m = 0` is the two-element cut
set `S = {0, N}`, which is handled by the long-block alternative instead (see
`Kakeya.MultiScaleFac.Assembly`).  The next three lemmas are the whole bridge. -/

/-! ### Restricting a cut set to reach an interior cut scale

`frostmanConstant_fibre_le_prod_of_cuts` only ever bounds the fibre Frostman constant at the
*second* scale of the chain, `cutChain δ N J S hcard 1`, whereas
`Kakeya.MultiScaleFac.Assembly.frostmanConstant_cutScale_le_of_cuts` needs it at an arbitrary cut
index `k ∈ S`.  The bridge is to run the chain not on `S` but on `restrictCuts S k`: discarding
every cut strictly below `k` makes `k` itself the second element, so the chain's index `1` is
`σ_k`, while the blocks that survive are exactly the adjacent blocks of `S` lying above `k` and
therefore still carry the block bound.  The discarded part collapses into the single gap
`(0, k)`, which costs nothing because `MultiScaleFac.frostmanConstant_fibre_le_prod` requires no
Frostman hypothesis on its `m = 0` gap (only `1 ≤ X 0`).

This is what makes the *sharp* exponent `(σ_k/δ)^ζ` of `frostmanConstant_cutScale_le_of_cuts`
reachable: taking `X 0 = 1` and `X m = (σ_m/σ_{m+1})^ζ` for `m ≠ 0` telescopes to `(σ_k/δ)^ζ`
rather than to `(1/δ)^ζ`. -/


section Package

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]


end Package

end MultiScaleFac

end Kakeya

-- touch

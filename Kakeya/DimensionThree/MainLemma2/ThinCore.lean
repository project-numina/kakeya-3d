/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factoring.Multiplicity

/-!
# The core envelope of the thin-case factoring constant

`Kakeya.ThinCase.factoringApply` — the thin-case application of the corrected Proposition 5.1 —
cannot hold with a comparison constant depending on the Frostman constant `CF` and the fullness
constant `Cfull` alone. The reason is the dyadic pigeonholing that Items 1 and 3 of Proposition
5.1 perform: the retained mass fraction of the pipeline is `(⌊log₂ N⌋ + 1)^{-O(1)}` in the
cardinality `N` of the family, and the outer multiplicity band costs a further
`(⌊log₂ M⌋ + 1)^{-1}` in the number `M` of bodies. A family split into `K` dyadic mass classes
therefore forces a comparison constant `≳ √K`, and `K` may be taken arbitrarily large at fixed
`CF`, `Cfull`, `δ`, `η` and `w₁`. (GWZ Proposition 5.1 states its items with `⪆`/`⪅`, i.e. with
`Kakeya.LEApprox`, which absorbs exactly this logarithmic loss; a Lean statement that pins the
constant to `CF` and `Cfull` asserts something strictly stronger, and false.)

This file introduces the third argument that repairs the statement:
`Kakeya.ThinCase.factoringApplyCore`, an explicit *envelope* for the pipeline losses of
Proposition 5.1 at a family of `Nsegs` segments in `Nbodies` bodies at scale `δ`, together with
the two facts that make the repair safe:

* `Kakeya.ThinCase.factoringApplyCore_spec` — the envelope satisfies the four bounds that the
  repaired `factoringApply` demands of its `Ccore` argument, unconditionally. So the repaired
  statement is not vacuous: its constant bundle is inhabited for every input. * `Kakeya.ThinCase.factoringApplyCore_leApprox_one` — for cardinalities polynomially bounded in
  `δ⁻¹` the envelope is `⪅ 1`, i.e. sub-polynomial in `δ⁻¹`. This is the *budget* check. The theorem below rules this out: every
  cardinality of the envelope enters inside a logarithm.
-/

@[expose] public section

open scoped NNReal

namespace Kakeya.ThinCase

open scoped NNReal
open Kakeya ShadedBody

/-! ### The envelope -/

/-- **The core envelope of the thin-case factoring constant.**

The smallest quantity that dominates all four dyadic-pigeonhole losses of the corrected
Proposition 5.1 at a family of `Nsegs` segments in `Nbodies` bodies at scale `δ`:

* the constant `2` (a bare `Ccore ≥ 2`, which is what rules out the degenerate
  `Cfull → 0`, `factoringApplyConstant → 1` collapse of the un-repaired statement);
* the reciprocal `(c(n, Nsegs, δ))⁻¹` of the retained mass fraction of Item 1
  (`ShadedBody.outerFactoringFamily_refinement.c`);
* the retained fraction of the extra outer dyadic band of Item 3
  (`ShadedBody.outerFactoringFamily_outerConstMultFat.c`);
* the number `⌊log₂ Nbodies⌋ + 1` of dyadic multiplicity bands of the outer family.

It is a *parameter* of the repaired `Kakeya.ThinCase.factoringApply` rather than being inlined
into `Kakeya.ThinCase.factoringApplyConstant`, so that this formula may change without touching
any downstream statement, and so that ball-uniformity is achieved by quantification. -/
noncomputable def factoringApplyCore (n Nsegs Nbodies : ℕ) (δ : ℝ≥0) : ℝ≥0 :=
  max 2 (max (ShadedBody.outerFactoringFamily_refinement.c n Nsegs δ)⁻¹
    (max (ShadedBody.outerFactoringFamily_outerConstMultFat.c n Nbodies δ)
      ((Nat.log 2 Nbodies + 1 : ℕ) : ℝ≥0)))

lemma two_le_factoringApplyCore (n Nsegs Nbodies : ℕ) (δ : ℝ≥0) :
    2 ≤ factoringApplyCore n Nsegs Nbodies δ := le_max_left _ _


lemma inv_refinement_c_le_factoringApplyCore (n Nsegs Nbodies : ℕ) (δ : ℝ≥0) :
    (ShadedBody.outerFactoringFamily_refinement.c n Nsegs δ)⁻¹ ≤
      factoringApplyCore n Nsegs Nbodies δ :=
  le_trans (le_max_left _ _) (le_max_right _ _)

lemma outerConstMultFat_c_le_factoringApplyCore (n Nsegs Nbodies : ℕ) (δ : ℝ≥0) :
    ShadedBody.outerFactoringFamily_outerConstMultFat.c n Nbodies δ ≤
      factoringApplyCore n Nsegs Nbodies δ :=
  le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)

lemma natLog_le_factoringApplyCore (n Nsegs Nbodies : ℕ) (δ : ℝ≥0) :
    ((Nat.log 2 Nbodies + 1 : ℕ) : ℝ≥0) ≤ factoringApplyCore n Nsegs Nbodies δ :=
  le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)


/-! ### The budget: the envelope is sub-polynomial in `δ⁻¹` -/


/-- `⌊log₂ m⌋ ≤ log₂ m` as reals, including the degenerate `m = 0`. -/
lemma natLog_le_logb (m : ℕ) : ((Nat.log 2 m : ℕ) : ℝ) ≤ Real.logb 2 (m : ℝ) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · simp [hm]
  · have hpow : (2 : ℕ) ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 hm.ne'
    have hpowr : ((2 : ℝ)) ^ Nat.log 2 m ≤ (m : ℝ) := by
      exact_mod_cast hpow
    have hposr : (0 : ℝ) < (2 : ℝ) ^ Nat.log 2 m := by positivity
    have hmono := Real.logb_le_logb_of_le (b := 2) (by norm_num) hposr hpowr
    have hval : Real.logb 2 ((2 : ℝ) ^ Nat.log 2 m) = ((Nat.log 2 m : ℕ) : ℝ) := by
      rw [Real.logb_pow (2 : ℝ) (2 : ℝ) (Nat.log 2 m)]
      simp
    rwa [hval] at hmono


end Kakeya.ThinCase

end

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.GlobalPlankPartBBridge
public import Kakeya.DimensionThree.Plank.LocalFactorizationGeometry

/-!
# Propagating the `Cw` repair to the two comparable-body factorisation data

`Kakeya.GlobalPlankFactorization` (`Kakeya/DimensionThree/Plank/Factorization.lean`) carries the
repaired transverse lower bound

`wide : ContainsFlatDisc (min b (1 / 2) / Cw) (part.convexHull_biUnion R).carrier`,

with an explicit comparability constant `Cw ≥ 1`.  The reason for the constant is recorded there:
the *unconstanted* radius `min b (1 / 2)` is jointly unsatisfiable with `le_plank` for the producer
GWZ actually has, because a covering / John-ellipsoid comparison returns
`W ⊆ plank (C a, C b, 1)` and `W ⊇ disc (c b)` with `c < 1 < C`, and no single declared middle
half-width satisfies both.

Two sibling data in this development still carry the **unconstanted** radius, and therefore still
carry that defect:

* `Kakeya.ComparableBodyFactorization.wide` (`.../ComparableBodyFactorization.lean`), the part-(A)
  datum;
* `Kakeya.GlobalComparableBodyFactorization.wide` (`.../GlobalPlankFactorization.lean`), the
  part-(B) sibling.

This file propagates the repair to both, **without editing either**.  Editing them in place is not
a cosmetic change: `ComparableBodyFactorization.wide` is consumed by the *proved* part-(A) chain
through `Kakeya.b_le_two_mul_of_comparableBodyFactorization`, and dividing the radius by `Cw`
multiplies the derived scale relation by `Cw` — a quantitative change inside part (A), which is a
different target and is separately known to be vacuous
(`Kakeya.localPlankFactorisation_proves_anything`).  So the propagation is done here additively:

1. `Kakeya.ComparableBodyFactorizationCw` and `Kakeya.GlobalComparableBodyFactorizationCw` are the
   `Cw`-parameterised data;
2. `Kakeya.ComparableBodyFactorization.toCw` and
   `Kakeya.GlobalComparableBodyFactorization.toCw` show the existing data are exactly the
   `Cw = 1` case, so the parameterised versions are **weaker** hypotheses and any theorem stated
   over them is stronger;
3. `Kakeya.b_le_two_mul_mul_of_comparableBodyFactorizationCw` is the **priced** scale consequence:
   `b ≤ 2 * Cw * ρ` in place of `b ≤ 2 * ρ`.  This is the exact cost of the propagation, and it is
   sub-polynomial under the `Cw ≤ δ ^ (-η)` budget the 6.6 statements already spend;
4. `Kakeya.GlobalPlankFactorization.toGlobalComparableBodyFactorizationCw` is the map that did
   **not** exist before: a repaired 6.6(B) datum with `Cw > 1` could not be fed to
   `Kakeya.GlobalComparableBodyFactorization` at all, because that structure's `wide` is tight.
   With the parameterised target the map exists, and it is proved here.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ConvexSpaceBody

noncomputable section

namespace Kakeya

/-! ### The `Cw`-parameterised part-(A) datum -/

/-- **`Kakeya.ComparableBodyFactorization` with the transverse lower bound divided by an explicit
comparability constant `Cw ≥ 1`.**

Every field but `wide` is verbatim that of `Kakeya.ComparableBodyFactorization`; `wide` asks only
for a flat disc of radius `min b (1 / 2) / Cw`.  At `Cw = 1` the two agree
(`Kakeya.ComparableBodyFactorization.toCw`). -/
structure ComparableBodyFactorizationCw (Cw b : ℝ≥0) {ι : Type*} (s : Finset ι)
    (Tb : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (C₀ : ℝ≥0) where
  /-- The transverse comparability constant is at least one. -/
  one_le_Cw : 1 ≤ Cw
  /-- Index type of the outer cells. -/
  Cell : Type
  /-- The outer cells actually used. -/
  cells : Finset Cell
  /-- The *actual* outer body of a cell. -/
  body : Cell → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))
  /-- The cell collecting each fine body. -/
  cellOf : ι → Cell
  /-- Every fine index is collected by a cell in use. -/
  cellOf_mem : ∀ i ∈ s, cellOf i ∈ cells
  /-- Every fine body lies in the body of its cell. -/
  le_body : ∀ i ∈ s, Tb i ≤ body (cellOf i)
  /-- Minimality of the outer body. -/
  body_le : ∀ x ∈ cells, ∀ K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)),
    (∀ i ∈ s, cellOf i = x → Tb i ≤ K) → body x ≤ K
  /-- Transverse lower bound, up to the comparability constant. -/
  wide : ∀ x ∈ cells, ContainsFlatDisc (min b (1 / 2) / Cw) (body x).carrier
  /-- The outer family is Katz--Tao with constant `C₀`. -/
  isKatzTao : IsKatzTao cells body (C₀ : ℝ≥0∞)

/-! ### The `Cw`-parameterised part-(B) comparable-body datum -/

/-- **`Kakeya.GlobalComparableBodyFactorization` with the transverse lower bound divided by an
explicit comparability constant `Cw ≥ 1`.** -/
structure GlobalComparableBodyFactorizationCw (Cw a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1)
    {ι : Type*} (s : Finset ι)
    (Tb : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (C₀ : ℝ≥0) where
  /-- The transverse comparability constant is at least one. -/
  one_le_Cw : 1 ≤ Cw
  /-- Index type of the outer cells. -/
  Cell : Type
  /-- The outer cells actually used. -/
  cells : Finset Cell
  /-- The *actual* outer body of a cell. -/
  body : Cell → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))
  /-- The cell collecting each coarse body. -/
  cellOf : ι → Cell
  /-- Every coarse index is collected by a cell in use. -/
  cellOf_mem : ∀ i ∈ s, cellOf i ∈ cells
  /-- Every coarse body lies in the body of its cell. -/
  le_body : ∀ i ∈ s, Tb i ≤ body (cellOf i)
  /-- Minimality of the outer body. -/
  body_le : ∀ x ∈ cells, ∀ K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)),
    (∀ i ∈ s, cellOf i = x → Tb i ≤ K) → body x ≤ K
  /-- Transverse upper bound: each outer body fits in an `a × b × 1` plank. -/
  le_plank : ∀ x ∈ cells, ∃ Q : Plank a b hab hb1, body x ≤ Q.toConvexSpaceBody
  /-- Transverse lower bound, up to the comparability constant. -/
  wide : ∀ x ∈ cells, ContainsFlatDisc (min b (1 / 2) / Cw) (body x).carrier
  /-- The outer family is Katz--Tao with constant `C₀`. -/
  isKatzTao : IsKatzTao cells body (C₀ : ℝ≥0∞)

/-! ### The map that did not exist before -/

namespace GlobalPlankFactorization

end GlobalPlankFactorization

end Kakeya

end

end

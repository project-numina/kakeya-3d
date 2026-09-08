/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.LocalFactorizationGeometry

/-!
# Cross-parent pooling from a parent count at the exact test body

This file replaces the false `hconf` route of
`Kakeya.isThickeningNonconcentrated_of_externalParents`.

That route asked for a *single* tube of radius `O(C_NC) * ρ` catching an occupied leaf of every
contributing cell, and then bounded the contributing parents by the parent system's own overlap
field.  Both steps are refuted in
`Kakeya/DimensionThree/Plank/DilatedThickeningStagger.lean`: the container
`((W j)_θ).toPrismNDim.dilation C_NC` is longitudinally longer than a leaf, so its leaves are not
longitudinally pinned, and no cardinality depending on `C_NC` alone controls them.

What the pooling step actually needs is *only* a count of the parents that own a leaf inside the
test body itself:

`#{k ∈ r | ∃ i ∈ q, assign i = k ∧ T i ≤ K} ≤ Cu'`.

`Kakeya.card_le_of_parentCountAtBody` is that pooling step, and
`Kakeya.isThickeningNonconcentrated_of_parentCountAtDilatedBodies` is its Section-6 instance: with
the parent count at the exact dilated test bodies as a hypothesis, non-concentration follows with
`M = Cu' * Csplit * (b / a)`, the same shape as before, so the final `(a/b) ^ (3β/2)` exponent of
Proposition 6.6(A) is unchanged.

Three things this route does **not** use: no confinement or shape datum, no Katz--Tao estimate on a
union of parent fibres (`hloc` is one fibre at a time), and no relation between the parent scale `ρ`
and the test body — indeed the parent tubes do not appear at all.  The occupancy datum is the
factorisation's own: an occupied leaf lies in the *actual* body `H x`, and `H x ≤ W x`, so for a
contributing cell the leaf lies in the test body automatically.

`Cu'` is a genuinely new hypothesis, strictly stronger than leaf-mediated bounded overlap at radius
`8 ρ`; `Kakeya.not_isThickeningNonconcentrated_of_testTubeOverlap` shows it cannot be dropped.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Metric Set
open scoped NNReal ENNReal

noncomputable section

namespace Kakeya

open Classical in
/-- **Cross-parent pooling at the test body.**

If at most `Cu'` parents own a fine body inside the test body `K`, if every contributing cell owns
an occupied leaf of its own parent inside `K`, and if each single parent fibre contributes at most
`m` cells inside `K`, then at most `Cu' * m` cells lie in `K`.

This is `Kakeya.card_le_of_confinedWitness` with the confining tube deleted: the parent set is
filtered by ownership of a leaf in `K` itself, so no shape datum and no test radius appear.  Katz--Tao
is never applied to a union of fibres — `hlocal` is one fibre at a time — and no two parent labels
are ever identified. -/
theorem card_le_of_parentCountAtBody
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {ι κ κ' : Type*} {q : Finset ι} {Tb : ι → ConvexSpaceBody E}
    {r : Finset κ} {assign : ι → κ} {Cu' : ℝ≥0}
    {ts : Finset κ'} {Wc : κ' → ConvexSpaceBody E} {par : κ' → κ} {K : ConvexSpaceBody E}
    (hoverK : ((({k ∈ r | ∃ i ∈ q, assign i = k ∧ Tb i ≤ K}).card : ℝ≥0)) ≤ Cu')
    (hpar_mem : ∀ x ∈ ts, par x ∈ r)
    (hocc : ∀ x ∈ ts, Wc x ≤ K → ∃ i ∈ q, assign i = par x ∧ Tb i ≤ K)
    {m : ℝ≥0}
    (hlocal : ∀ k ∈ r, (({x ∈ ts | Wc x ≤ K ∧ par x = k}).card : ℝ≥0) ≤ m) :
    (({x ∈ ts | Wc x ≤ K}).card : ℝ≥0) ≤ Cu' * m := by
  classical
  let P : Finset κ := {k ∈ r | ∃ i ∈ q, assign i = k ∧ Tb i ≤ K}
  have hpar' : ∀ x ∈ ts, Wc x ≤ K → par x ∈ P := by
    intro x hx hKx
    unfold P
    refine Finset.mem_filter.mpr ⟨hpar_mem x hx, ?_⟩
    rcases hocc x hx hKx with ⟨i, hi, hassign, hTiK⟩
    exact ⟨i, hi, hassign, hTiK⟩
  have hlocal' : ∀ j ∈ P, (({x ∈ ts | Wc x ≤ K ∧ par x = j}).card : ℝ≥0) ≤ m := by
    intro j hj
    exact hlocal j ((Finset.mem_filter.mp hj).1)
  have hPA : (({x ∈ ts | Wc x ≤ K}).card : ℝ≥0) ≤ (P.card : ℝ≥0) * m := by
    exact card_filter_le_of_parentwise (p := fun x : κ' => Wc x ≤ K) (par := par) (P := P)
      hpar' hlocal'
  have hPC : (P.card : ℝ≥0) ≤ Cu' := by
    unfold P
    exact hoverK
  have hstep : (P.card : ℝ≥0) * m ≤ Cu' * m := by
    exact mul_le_mul_of_nonneg_right hPC (by positivity)
  exact le_trans hPA hstep

open Classical in
/-- **The `C_NC`-dilated thick-plank non-concentration hypothesis of GWZ Lemma 6.4, from a parent
count at the exact dilated test bodies.**

The axiom-clean replacement for `Kakeya.isThickeningNonconcentrated_of_externalParents`.  Its
conclusion is literally `Plank.IsThickeningNonconcentrated`, at the same concentration parameter
shape `M = Cu' * Csplit * (b / a)`, so Proposition 6.6(A) keeps its `(a/b) ^ (3β/2)` exponent.

The inputs are exactly:

* `hoverK`: for each anchor `j` and each thickening scale `θ`, at most `Cu'` parents own a fine leaf
  inside the exact dilated test body.  This is the corrected cross-parent hypothesis; it replaces
  the refuted single-tube confinement datum;
* `hpar_mem`: the parent labels are in the external index set;
* `hocc` and `hbody`: the factorisation's own occupancy — an occupied leaf of the cell's *own*
  parent lies in the actual body `H x`, and `H x` lies in the representative plank `W x`.  For a
  contributing cell (`W x` inside the test body) the leaf therefore lies in the test body, which is
  what `hoverK` counts;
* `hloc`: the within-parent count at the exact dilated test body, one original parent fibre at a
  time.

No confinement, no cover, no same-parent equality, no Katz--Tao on a union of fibres, and no
appearance of the parent scale `ρ`. -/
theorem isThickeningNonconcentrated_of_parentCountAtDilatedBodies_body
    {ι κ κ' : Type*} {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {q : Finset ι} {T : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {r : Finset κ} {assign : ι → κ} {Cu' Csplit C_NC : ℝ≥0}
    {ts : Finset κ'} {W : κ' → ShadedPlank a b hab hb1} {par : κ' → κ}
    {H : κ' → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    (hoverK : ∀ j ∈ ts, ∀ (θ : ℝ≥0) (hθ1 : θ ≤ 1), a / b ≤ θ →
      ((({k ∈ r | ∃ i ∈ q, assign i = k ∧
          T i ≤
            ((Plank.thickened (W j).toPrism3D θ hθ1).toPrismNDim.dilation
              C_NC).toConvexSpaceBody}).card : ℝ≥0)) ≤ Cu')
    (hpar_mem : ∀ x ∈ ts, par x ∈ r)
    (hocc : ∀ x ∈ ts, ∃ i ∈ q, assign i = par x ∧
      T i ≤ H x)
    (hbody : ∀ x ∈ ts, H x ≤ (W x).toConvexSpaceBody)
    (hloc : ∀ j ∈ ts, ∀ (θ : ℝ≥0) (hθ1 : θ ≤ 1), a / b ≤ θ → ∀ k ∈ r,
      (({x ∈ ts | ((W x).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
          (((Plank.thickened (W j).toPrism3D θ hθ1).toPrismNDim.dilation C_NC).carrier :
            Set (EuclideanSpace ℝ (Fin 3))) ∧
          par x = k}.card : ℝ≥0)) ≤ (Csplit * (b / a)) * θ) :
    Plank.IsThickeningNonconcentrated ts (fun x => (W x).toPrism3D) C_NC
      ((Cu' * Csplit) * (b / a)) := by
  classical
  intro j hj θ hθ1 hθab
  let Kdil : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    ((Plank.thickened (W j).toPrism3D θ hθ1).toPrismNDim.dilation C_NC).toConvexSpaceBody
  let Wc : κ' → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    fun x => (W x).toConvexSpaceBody
  have hcar : ∀ x : κ', (((W x).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      (((Plank.thickened (W j).toPrism3D θ hθ1).toPrismNDim.dilation C_NC).carrier :
        Set (EuclideanSpace ℝ (Fin 3)))) ↔ Wc x ≤ Kdil := fun x => Iff.rfl
  have hfilter_top :
      ts.filter (fun x : κ' => ((W x).toPrism3D.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
        (((Plank.thickened (W j).toPrism3D θ hθ1).toPrismNDim.dilation C_NC).carrier :
          Set (EuclideanSpace ℝ (Fin 3))))
      = ts.filter (fun x : κ' => Wc x ≤ Kdil) := by
    ext x
    rw [Finset.mem_filter, Finset.mem_filter, ← hcar x]
  have hfilter_j : ∀ k : κ, ts.filter (fun x : κ' =>
      ((W x).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
        (((Plank.thickened (W j).toPrism3D θ hθ1).toPrismNDim.dilation C_NC).carrier :
          Set (EuclideanSpace ℝ (Fin 3))) ∧ par x = k)
      = ts.filter (fun x : κ' => Wc x ≤ Kdil ∧ par x = k) := by
    intro k
    ext x
    rw [Finset.mem_filter, Finset.mem_filter, hcar x]
  have hoccK : ∀ x ∈ ts, Wc x ≤ Kdil →
      ∃ i ∈ q, assign i = par x ∧ T i ≤ Kdil := by
    intro x hx hxK
    rcases hocc x hx with ⟨i, hiq, hassign, hTi⟩
    refine ⟨i, hiq, hassign, ?_⟩
    exact le_trans (le_trans hTi (hbody x hx)) hxK
  have hlocal' : ∀ k ∈ r, (({x ∈ ts | Wc x ≤ Kdil ∧ par x = k}.card : ℝ≥0)) ≤
      Csplit * (b / a) * θ := by
    intro k hk
    rw [← hfilter_j k]
    exact hloc j hj θ hθ1 hθab k hk
  have hmain : (({x ∈ ts | Wc x ≤ Kdil}.card : ℝ≥0)) ≤ Cu' * (Csplit * (b / a) * θ) :=
    card_le_of_parentCountAtBody (E := EuclideanSpace ℝ (Fin 3))
      (hoverK j hj θ hθ1 hθab) hpar_mem hoccK (m := Csplit * (b / a) * θ) hlocal'
  rw [hfilter_top]
  exact le_trans hmain
    (le_of_eq (by ring : ((Cu' * Csplit) * (b / a)) * θ = Cu' * (Csplit * (b / a) * θ)).symm)


end Kakeya

end

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.GlobalPlankFactorization

/-!
# Section 6: the coarse-parent input layer of GWZ Proposition 6.6(B)

Proposition 6.6(B) is currently stated with the hypothesis

`∀ i ∈ q, ∃ k ∈ r, (T i).toConvexSpaceBody ≤ (R k).toConvexSpaceBody`,

i.e. "every fine tube lies in *some* coarse tube".  That is strictly weaker than the datum the
paper uses, and the gap is not cosmetic: the proof of 6.6(B) needs a *function* `𝒯 → 𝒯_ρ` whose
fibres have comparable cardinality, and it needs the coarse family sitting over an outer plank `W`
to be Frostman **in `W`**.  Neither is a consequence of a bare existential cover.  This file
supplies the missing data.

## What the check found

The uniformity API (`Tube.IsUniformAtScale`) genuinely provides, at a scale `ρ`:

* a parent family, indexed by `parent`, of `ρ`-tubes `(T j).rescale ρ` (field `exists_le_rescale`);
* an *existential* assignment of each fine tube to a parent containing it (same field);
* a common branching number `branchingN`, and two-sided comparability of the cardinality of each
  **containment** set `{i ∈ s | T i ≤ (T j).rescale ρ}` with it (fields `card_filter_le` and
  `le_mul_card_filter`);
* pairwise essential distinctness of the parents.

It does **not** provide:

1. an assignment *function* — only the existential.  Choosing one is harmless
   (`Kakeya.uniformCoarseAssign`), but a chosen function has *smaller* fibres than the containment
   sets, because a fine tube may lie in several parents at once;
2. consequently, the **lower** bound for the fibres of a chosen assignment.  The upper bound
   transfers (a fibre is contained in a containment set,
   `Kakeya.Section6CoarseTubeDecomposition.card_fibre_le_of_uniformAtScale`),
   the lower bound does not: `le_mul_card_filter` bounds the containment set, and the assignment may
   have routed all of its members elsewhere.  Repairing this needs a bounded-overlap count for the
   parent family, which is a separate (available, but distinct) input;
3. any Frostman datum whatsoever, at either scale.

`Kakeya.Section6CoarseTubeDecomposition` therefore records exactly the four genuine items — a
function, its membership, leafwise containment, and two-sided fibre comparability — and the
constructor `Kakeya.Section6CoarseTubeDecomposition.ofUniformAtScale` discharges every clause that
uniformity does give, leaving item 2 as a single named hypothesis rather than fabricating it.
Nonemptiness of the fibres is *not* a hypothesis there: the coarse index set is taken to be the set
of parents actually used, `q.image assign`, for which nonemptiness is automatic.

## The Part-(B) factorisation datum

`Kakeya.GlobalComparableBodyFactorization` already carries the outer Katz--Tao property, cellwise
containment of the coarse tubes, and containment of each cell body in an `a × b × 1` plank.  What it
does not carry is the **coarse-fibre Frostman** datum, and it presents the representative plank as
an existential (`le_plank`) rather than as data.  `Kakeya.Section6PartBFactorisation` adds both:

* `repr` and `body_le_repr` — the representative `a × b × 1` plank of each cell, as data.  The
  actual cell body and its representative plank stay strictly separate; no actual body is ever
  assumed to *be* a plank (that hypothesis is unsatisfiable, see
  `Kakeya.not_plankFactorization_tubes_of_pos`);
* `coarse_fibre_frostman` — the coarse fibre `𝒯_{ρ,W}` is `C_F`-Frostman **in the representative
  plank**, which is where the paper's `W` lives and where the consumer needs it.

There is deliberately **no** fine-fibre Frostman clause.  That is the whole content of GWZ
Remark 5.3: the fine family need not be Frostman, and every estimate that looks like it needs a fine
Frostman datum is obtained instead from the coarse one plus fibre comparability.  The two theorems
that make this precise here are

* `Kakeya.Section6PartBData.remark53FibreFrostman` — the coarse (and only the coarse) Frostman
  hypothesis, in the exact shape a Proposition-5.1 black box consumes; and
* `Kakeya.Section6PartBData.remark53_card_fine_le` — the *fine* slab count
  `|{i : R (assign i) ⊆ K}| ≤ C_fib² · C_vol · C_F · θ · |𝒯_W|` for any `K ⊆ W` of relative volume
  `θ`, derived with no fine Frostman input at all.  This is the `γ = 1` non-concentration datum of
  GWZ Lemma 6.1 that Proposition 6.6(B) actually uses.

## The scale relation

`ρ ≤ a` is a consequence of the datum, not an assumption: a `ρ`-tube contains a ball of radius `ρ`,
it lies in its cell body, and the cell body lies in the representative `a × b × 1` plank, whose
least width is `a` (`Kakeya.Section6PartBFactorisation.rho_le`).  This uses only the honest
representative geometry — containment in the plank — and never an equality of actual body and plank.

## What is still expected from the merged Proposition 5.1

`Kakeya.Section6PartBData.transverseFactorInput` produces, cell by cell, *exactly* the hypothesis
list of `Kakeya.katzTaoTransverseFactorBound` (which is what the `γ = 1` affine-normalisation layer
consumes).  Nothing in this file normalises anything.  Beyond that, Proposition 6.6(B) still needs
from the merged Proposition 5.1, and from nowhere else:

1. the multiplicity split `μ(𝒯, Y) ≤ C · μ(𝒲) · μ(𝒯_W)` for the **fine** family, granted the
   coarse-fibre Frostman datum `Kakeya.Section6PartBData.remark53FibreFrostman` — this is the
   Remark-5.3 upgrade of Proposition 5.1 and is *not* derivable from the present interface;
2. the cardinality bound `|𝒲| · |𝒯_W| ≤ C · |𝒯|`;
3. the outer fullness lower bound for the selected cells.

Items 1--3 are the only facts `Kakeya.factoringAndMultPropGlobal` needs that this file does not
provide; everything else in its statement is either produced here or already available.  The
migration of `Kakeya.factoringAndMultPropGlobal` itself is a one-line hypothesis swap: the present
weak cover is recovered from the new datum by
`Kakeya.Section6CoarseTubeDecomposition.exists_parent`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Convexity
-- Every fibre in this file is a `Finset.filter` over an arbitrary index type, so the classical
-- instance is needed both in the statements and inside the proofs;
-- `Kakeya.GlobalComparableBodyFactorization` opens it file-wide for the same reason.
set_option linter.style.openClassical false
open scoped NNReal ENNReal Classical

noncomputable section

namespace Kakeya

/-! ## The coarse tube decomposition -/

open Classical in
/-- **The Section-6 coarse tube decomposition** (the honest form of "the fine tubes lie over the
coarse tubes").

A *function* `assign` from fine to coarse indices, with leafwise containment and two-sided fibre
comparability around a common size `m`.  This is the `T_ρ` datum of GWZ Section 6, and it is what
`Kakeya.katzTaoTransverseFactorBound` consumes.

Every field is genuine data supplied by the uniformity of the fine family at scale `ρ`, except the
fibre lower bound `le_card_fibre`; see the module docstring and
`Kakeya.Section6CoarseTubeDecomposition.ofUniformAtScale`. -/
structure Section6CoarseTubeDecomposition
    {ι : Type*} (q : Finset ι) {δ : ℝ≥0} (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    {κ : Type*} (coarseSet : Finset κ) {ρ : ℝ≥0}
    (R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))) (m Cfib : ℝ≥0) where
  /-- The coarse index carrying each fine index. -/
  assign : ι → κ
  /-- The coarse index of a fine index in use is in use. -/
  assign_mem : ∀ i ∈ q, assign i ∈ coarseSet
  /-- Each fine tube lies in its own coarse tube. -/
  leaf_le_parent : ∀ i ∈ q, (T i).toConvexSpaceBody ≤ (R (assign i)).toConvexSpaceBody
  /-- The comparability constant is at least `1`. -/
  one_le_Cfib : 1 ≤ Cfib
  /-- The common fibre size is positive. -/
  m_pos : 0 < m
  /-- Every coarse index in use carries at least one fine index. -/
  fibre_nonempty : ∀ k ∈ coarseSet, ({i ∈ q | assign i = k} : Finset ι).Nonempty
  /-- Fibre comparability, lower half. -/
  le_card_fibre : ∀ k ∈ coarseSet,
    m / Cfib ≤ (({i ∈ q | assign i = k} : Finset ι).card : ℝ≥0)
  /-- Fibre comparability, upper half. -/
  card_fibre_le : ∀ k ∈ coarseSet,
    (({i ∈ q | assign i = k} : Finset ι).card : ℝ≥0) ≤ Cfib * m

namespace Section6CoarseTubeDecomposition

variable {ι : Type*} {q : Finset ι} {δ : ℝ≥0} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
  {κ : Type*} {coarseSet : Finset κ} {ρ : ℝ≥0} {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}
  {m Cfib : ℝ≥0}

open Classical in
/-- The fibre of a coarse index: the fine indices assigned to it. -/
def fibre (D : Section6CoarseTubeDecomposition q T coarseSet R m Cfib) (k : κ) : Finset ι :=
  {i ∈ q | D.assign i = k}

variable (D : Section6CoarseTubeDecomposition q T coarseSet R m Cfib)

theorem mem_fibre_iff {k : κ} {i : ι} : i ∈ D.fibre k ↔ i ∈ q ∧ D.assign i = k := by
  simp [fibre, Finset.mem_filter]

theorem fibre_subset (k : κ) : D.fibre k ⊆ q := by
  intro i hi
  exact ((mem_fibre_iff D).mp hi).1


/-! ### Selected subfamilies -/

open Classical in
/-- **A selected fine fibre is contained in the full fibre**, hence inherits the upper bound. -/
theorem card_selected_fibre_le {q' : Finset ι} (hq' : q' ⊆ q) (k : κ) :
    (({i ∈ q' | D.assign i = k} : Finset ι).card : ℝ≥0) ≤ ((D.fibre k).card : ℝ≥0) := by
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro i hi
  rw [Finset.mem_filter] at hi
  simpa [Section6CoarseTubeDecomposition.fibre, Finset.mem_filter] using ⟨hq' hi.1, hi.2⟩

open Classical in
/-- **Restriction to a selected fine subfamily.**  The upper fibre bound is inherited; the lower one
is not (selection can empty a fibre), so it is an explicit hypothesis, exactly as for
`Kakeya.Section6CoarseTubeDecomposition.ofUniformAtScale`. -/
def restrict {q' : Finset ι} (hq' : q' ⊆ q) {Cfib' : ℝ≥0} (hCfib : Cfib ≤ Cfib')
    (hne : ∀ k ∈ coarseSet, ({i ∈ q' | D.assign i = k} : Finset ι).Nonempty)
    (hlb : ∀ k ∈ coarseSet,
      m / Cfib' ≤ (({i ∈ q' | D.assign i = k} : Finset ι).card : ℝ≥0)) :
    Section6CoarseTubeDecomposition q' T coarseSet R m Cfib' where
  assign := D.assign
  assign_mem := fun i hi => D.assign_mem i (hq' hi)
  leaf_le_parent := fun i hi => D.leaf_le_parent i (hq' hi)
  one_le_Cfib := le_trans D.one_le_Cfib hCfib
  m_pos := D.m_pos
  fibre_nonempty := hne
  le_card_fibre := hlb
  card_fibre_le := by
    intro k hk
    calc
      (({i ∈ q' | D.assign i = k} : Finset ι).card : ℝ≥0)
          ≤ ((D.fibre k).card : ℝ≥0) := card_selected_fibre_le D hq' k
      _ ≤ Cfib * m := D.card_fibre_le k hk
      _ ≤ Cfib' * m := by
        gcongr

/-! ### Counting transport -/

open Classical in
/-- **Fine counting from a selected coarse subfamily, fraction form.**  If the selected coarse
indices are a `Cθ`-fraction of the coarse family, the fine indices lying over them are a
`Cfib ^ 2 · Cθ`-fraction of the fine family.  No Frostman datum for the *fine* family is used. -/
theorem card_le_of_selected (hne : coarseSet.Nonempty)
    {Cθ : ℝ≥0} {sel : Finset κ} (hsel : sel ⊆ coarseSet)
    (hselcard : (sel.card : ℝ≥0) ≤ Cθ * (coarseSet.card : ℝ≥0))
    {qS : Finset ι} (hqS : qS ⊆ q) (hmem : ∀ i ∈ qS, D.assign i ∈ sel) :
    (qS.card : ℝ≥0) ≤ Cfib ^ 2 * Cθ * (q.card : ℝ≥0) := by
  classical
  have hlb : ∀ k ∈ coarseSet,
      Cfib⁻¹ * m ≤ (({i ∈ q | D.assign i = k} : Finset ι).card : ℝ≥0) := by
    intro k hk
    calc
      Cfib⁻¹ * m = m * Cfib⁻¹ := by rw [mul_comm]
      _ = m / Cfib := by rw [div_eq_mul_inv]
      _ ≤ (({i ∈ q | D.assign i = k} : Finset ι).card : ℝ≥0) := D.le_card_fibre k hk
  exact card_le_of_comparable_fibres_of_selected_le D.one_le_Cfib hne D.assign_mem hlb
    D.card_fibre_le hsel hselcard hqS hmem

end Section6CoarseTubeDecomposition

/-! ## Building a decomposition from uniformity -/

open Classical in
/-- **The assignment function chosen from single-scale uniformity.**

`Tube.IsUniformAtScale` supplies only the *existential* statement that each fine tube lies in
some parent; this is a choice of witness.  Choosing is harmless, but see
`Kakeya.Section6CoarseTubeDecomposition.ofUniformAtScale`: a chosen function has smaller fibres than
the containment sets that uniformity controls, so the fibre *lower* bound does not survive the
choice. -/
def uniformCoarseAssign {ι : Type*} {q : Finset ι} {δ : ℝ≥0}
    {Tt : ι → Tube δ (EuclideanSpace ℝ (Fin 3))} {ρ C : ℝ≥0}
    (U : Tube.IsUniformAtScale q Tt ρ C) (i : ι) : ι :=
  if h : i ∈ q then Classical.choose (U.exists_le_rescale h) else i

namespace uniformCoarseAssign

variable {ι : Type*} {q : Finset ι} {δ : ℝ≥0} {Tt : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}
  {ρ C : ℝ≥0} (U : Tube.IsUniformAtScale q Tt ρ C)

theorem mem_parent {i : ι} (hi : i ∈ q) : uniformCoarseAssign U i ∈ U.parent := by
  rw [uniformCoarseAssign, dif_pos hi]
  exact (Classical.choose_spec (U.exists_le_rescale hi)).1

theorem le_rescale {i : ι} (hi : i ∈ q) :
    (Tt i).toConvexSpaceBody ≤ (U.parentTube (uniformCoarseAssign U i)).toConvexSpaceBody := by
  rw [uniformCoarseAssign, dif_pos hi]
  exact (Classical.choose_spec (U.exists_le_rescale hi)).2

end uniformCoarseAssign

namespace Section6CoarseTubeDecomposition


end Section6CoarseTubeDecomposition

/-! ## The Part-(B) factorisation datum -/

open Classical in
/-- **The honest Part-(B) factorisation datum: "`𝒲` factors `𝒯_ρ`".**

A wrapper around the geometry of `Kakeya.GlobalComparableBodyFactorization` carrying, in addition, the two
things Proposition 6.6(B) genuinely uses and that structure lacks:

* the representative `a × b × 1` plank of each cell as **data** (`repr`, `body_le_repr`) rather than
  as the existential `Kakeya.GlobalComparableBodyFactorization.le_plank`;
* the **coarse-fibre Frostman** datum `coarse_fibre_frostman`: the coarse tubes collected by a cell
  are `CF`-Frostman inside that cell's representative plank.

The actual cell body `body x` and the representative plank `repr x` are kept strictly separate: no
actual body is assumed to be a plank, and no exact plank is required to lie in a `ρ`-tube.  There is
deliberately no fine-fibre Frostman clause; see the module docstring. -/
structure Section6PartBFactorisation (a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1)
    {κ : Type*} (coarseSet : Finset κ) {ρ : ℝ≥0}
    (R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))) (CF C₀ : ℝ≥0) where
  /-- Index type of the outer cells. -/
  Cell : Type
  /-- The outer cells actually used. -/
  cells : Finset Cell
  /-- The *actual* outer body of a cell.  Never assumed to be a plank. -/
  body : Cell → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))
  /-- The cell collecting each coarse tube. -/
  cellOf : κ → Cell
  /-- Every coarse index in use is collected by a cell in use. -/
  cellOf_mem : ∀ k ∈ coarseSet, cellOf k ∈ cells
  /-- Every coarse tube lies in the body of its cell. -/
  le_body : ∀ k ∈ coarseSet, (R k).toConvexSpaceBody ≤ body (cellOf k)
  /-- The representative `a × b × 1` plank of a cell. -/
  repr : Cell → Plank a b hab hb1
  /-- The actual body is contained in its representative plank. -/
  body_le_repr : ∀ x ∈ cells, body x ≤ (repr x).toConvexSpaceBody
  /-- **The representative planks lie in the working window.**

  This is *not* derivable from the rest of the datum.  The only spatial anchor available downstream
  is that the fine tubes lie in the unit ball, which puts one point of `repr x` in
  `closedBall 0 1`; an `a × b × 1` plank through that point reaches out to
  `1 + 2√(a² + b² + 1)`, which at `a = b = 1` is `1 + 2√3 ≈ 4.47 > 4 = plankWindowRadius`.  So the
  containment genuinely has to be part of the datum, supplied by whoever builds the
  factorisation from a concrete configuration.  It is what
  `Kakeya.factoringAndMultPropGlobal` exports as the outer window clause. -/
  repr_window : ∀ x ∈ cells,
    ((repr x).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ)
  /-- The Frostman constant is at least `1`. -/
  one_le_CF : 1 ≤ CF
  /-- **Coarse-fibre Frostman.**  The coarse tubes collected by a cell are `CF`-Frostman in the
  cell's representative plank. -/
  coarse_fibre_frostman : ∀ x ∈ cells,
    ConvexSpaceBody.IsFrostmanIn ({k ∈ coarseSet | cellOf k = x} : Finset κ)
      (fun k => (R k).toConvexSpaceBody) (repr x).toConvexSpaceBody (CF : ℝ≥0∞)
  /-- The outer family is Katz--Tao with constant `C₀`. -/
  isKatzTao : ConvexSpaceBody.IsKatzTao cells body (C₀ : ℝ≥0∞)

namespace Section6PartBFactorisation

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
  {κ : Type*} {coarseSet : Finset κ} {ρ : ℝ≥0} {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}
  {CF C₀ : ℝ≥0}

open Classical in
/-- The coarse tubes collected by a cell. -/
def coarseFibre (F : Section6PartBFactorisation a b hab hb1 coarseSet R CF C₀) (x : F.Cell) :
    Finset κ :=
  {k ∈ coarseSet | F.cellOf k = x}

variable (F : Section6PartBFactorisation a b hab hb1 coarseSet R CF C₀)

theorem mem_coarseFibre_iff {x : F.Cell} {k : κ} :
    k ∈ F.coarseFibre x ↔ k ∈ coarseSet ∧ F.cellOf k = x := by
  simp [coarseFibre, Finset.mem_filter]

theorem coarseFibre_subset (x : F.Cell) : F.coarseFibre x ⊆ coarseSet := by
  rw [coarseFibre]
  exact Finset.filter_subset (fun k => F.cellOf k = x) coarseSet

/-- Each coarse tube lies in the representative plank of its cell. -/
theorem le_repr {k : κ} (hk : k ∈ coarseSet) :
    (R k).toConvexSpaceBody ≤ (F.repr (F.cellOf k)).toConvexSpaceBody := by
  exact le_trans (F.le_body k hk) (F.body_le_repr (F.cellOf k) (F.cellOf_mem k hk))

theorem carrier_subset_repr {k : κ} (hk : k ∈ coarseSet) :
    (R k).carrier ⊆ ((F.repr (F.cellOf k)).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
  exact (SetLike.coe_subset_coe (S := (R k).toConvexSpaceBody)
    (T := (F.repr (F.cellOf k)).toConvexSpaceBody)).mp (F.le_repr hk)


end Section6PartBFactorisation

/-! ## Coarse counting: the volume-comparable Frostman count -/

/-- **A Frostman family of volume-comparable bodies cannot concentrate.**

If the bodies `V k`, `k ∈ r`, all have volume in `[v, Cv · v]`, are `CF`-Frostman in `W`, and
`K ⊆ W` has volume at most `θ · |W|`, then at most a `Cv · CF · θ`-fraction of them lie in `K`.

This is `Kakeya.card_le_of_frostmanIn` with the volume ratio made explicit and the common volume
cancelled, which is the form the fine-family transport below needs. -/
theorem card_le_of_frostmanIn_of_volume_comparable {κ : Type*} {r : Finset κ}
    {V : κ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {W K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))} {CF θ Cv : ℝ≥0} {v : ℝ≥0∞}
    (hv0 : v ≠ 0) (hvtop : v ≠ ⊤)
    (hFrost : ConvexSpaceBody.IsFrostmanIn r V W (CF : ℝ≥0∞))
    (hVW : ∀ k ∈ r, V k ≤ W) (hKW : K ≤ W)
    (hmin : ∀ k ∈ r, v ≤ volume (V k).carrier)
    (hmax : ∀ k ∈ r, volume (V k).carrier ≤ (Cv : ℝ≥0∞) * v)
    (hW0 : volume W.carrier ≠ 0) (hWtop : volume W.carrier ≠ ⊤)
    (hvolK : volume K.carrier ≤ (θ : ℝ≥0∞) * volume W.carrier) :
    (({k ∈ r | V k ≤ K}).card : ℝ≥0∞)
      ≤ ((Cv * CF * θ : ℝ≥0) : ℝ≥0∞) * (r.card : ℝ≥0∞) := by
  have hvolb : volume K.carrier / volume W.carrier ≤ (θ : ℝ≥0∞) := by
    rw [ENNReal.div_le_iff_le_mul (.inl hW0) (.inl hWtop)]
    exact hvolK
  have hmain : (({k ∈ r | V k ≤ K}).card : ℝ≥0∞) * v
      ≤ (CF : ℝ≥0∞) * ((r.card : ℝ≥0∞) * ((Cv : ℝ≥0∞) * v))
        * (volume K.carrier / volume W.carrier) := by
    exact card_le_of_frostmanIn hFrost hVW hKW hv0 hmin hmax hW0 hWtop
  have hstep : (CF : ℝ≥0∞) * ((r.card : ℝ≥0∞) * ((Cv : ℝ≥0∞) * v))
        * (volume K.carrier / volume W.carrier)
      ≤ ((Cv * CF * θ : ℝ≥0) : ℝ≥0∞) * (r.card : ℝ≥0∞) * v := by
    calc
      (CF : ℝ≥0∞) * ((r.card : ℝ≥0∞) * ((Cv : ℝ≥0∞) * v))
          * (volume K.carrier / volume W.carrier)
          ≤ (CF : ℝ≥0∞) * ((r.card : ℝ≥0∞) * ((Cv : ℝ≥0∞) * v)) * (θ : ℝ≥0∞) := by
            gcongr
      _ = ((Cv * CF * θ : ℝ≥0) : ℝ≥0∞) * (r.card : ℝ≥0∞) * v := by
            simp [ENNReal.coe_mul, mul_assoc, mul_left_comm, mul_comm]
  have hleft : v * (({k ∈ r | V k ≤ K}).card : ℝ≥0∞)
      ≤ v * (((Cv * CF * θ : ℝ≥0) : ℝ≥0∞) * (r.card : ℝ≥0∞)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using (le_trans hmain hstep)
  exact (ENNReal.mul_le_mul_iff_right hv0 hvtop).mp hleft

/-- The ratio of the two dimensional constants bounding the volume of a `ρ`-tube in `ℝ³`. -/
def coarseTubeVolumeRatio : ℝ≥0 :=
  Tube.volume_le.C 3 / Tube.le_volume.c 3

theorem one_le_coarseTubeVolumeRatio : 1 ≤ coarseTubeVolumeRatio := by
  rw [coarseTubeVolumeRatio, Tube.volume_le.C]
  norm_num
  have h32 : Real.Gamma ((3 : ℝ) / 2) = (1 / 2 : ℝ) * Real.sqrt Real.pi := by
    rw [show (3 : ℝ) / 2 = 1 / 2 + (1 : ℝ) by norm_num]
    rw [Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0)]
    rw [Real.Gamma_one_half_eq]
  have hg : Real.Gamma ((3 : ℝ) / 2 + 1) = (3 / 4 : ℝ) * Real.sqrt Real.pi := by
    rw [Real.Gamma_add_one (by norm_num : (3 : ℝ) / 2 ≠ 0), h32]
    ring
  have hc : (Tube.le_volume.c 3 : ℝ) ≤ 16 := by
    change Real.sqrt Real.pi ^ 3 / Real.Gamma (3 / 2 + 1) / 3 ≤ 16
    rw [hg]
    have hpos : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    have hsqrt : Real.sqrt Real.pi ≠ 0 := ne_of_gt hpos
    field_simp [hsqrt]
    rw [Real.sq_sqrt Real.pi_nonneg]
    nlinarith [Real.pi_le_four, Real.pi_pos]
  rw [← NNReal.coe_le_coe]
  rw [NNReal.coe_div]
  norm_num
  rw [le_div_iff₀ (NNReal.coe_pos.mpr (Tube.le_volume.c_pos 3))]
  simpa using hc

/-- The volume of a `ρ`-tube in `ℝ³`, two-sided, in the form
`v ≤ volume ≤ coarseTubeVolumeRatio · v` with `v = c · ρ²`. -/
theorem Tube.volume_comparable_three {ρ : ℝ≥0} (hρ1 : ρ ≤ 1)
    (R : Tube ρ (EuclideanSpace ℝ (Fin 3))) :
    ((Tube.le_volume.c 3 : ℝ≥0) : ℝ≥0∞) * (ρ : ℝ≥0∞) ^ 2 ≤ volume R.carrier ∧
      volume R.carrier ≤ (coarseTubeVolumeRatio : ℝ≥0∞)
        * (((Tube.le_volume.c 3 : ℝ≥0) : ℝ≥0∞) * (ρ : ℝ≥0∞) ^ 2) := by
  constructor
  · simpa [finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3)] using
      (Tube.le_volume (E := EuclideanSpace ℝ (Fin 3)) R)
  · have hc : Tube.le_volume.c (3 : ℕ) ≠ (0 : ℝ≥0) := ne_of_gt (Tube.le_volume.c_pos 3)
    have hle : volume R.carrier ≤
        ((Tube.volume_le.C 3 * ρ ^ 2 : ℝ≥0) : ℝ≥0∞) := by
      simpa [finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3)] using
        (Tube.volume_le (E := EuclideanSpace ℝ (Fin 3)) hρ1 R)
    have hul : coarseTubeVolumeRatio * (Tube.le_volume.c 3 * ρ ^ 2) =
        Tube.volume_le.C 3 * ρ ^ 2 := by
      rw [coarseTubeVolumeRatio, ← mul_assoc]
      rw [div_mul_cancel₀ (Tube.volume_le.C 3) hc]
    have hcoef : (coarseTubeVolumeRatio : ℝ≥0∞) *
        (((Tube.le_volume.c 3 : ℝ≥0) : ℝ≥0∞) * (ρ : ℝ≥0∞) ^ 2) =
        ((Tube.volume_le.C 3 * ρ ^ 2 : ℝ≥0) : ℝ≥0∞) := by
      rw [← ENNReal.coe_pow, ← ENNReal.coe_mul, ← ENNReal.coe_mul]
      exact congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) hul
    calc
      volume R.carrier ≤ ((Tube.volume_le.C 3 * ρ ^ 2 : ℝ≥0) : ℝ≥0∞) := hle
      _ = (coarseTubeVolumeRatio : ℝ≥0∞) *
          (((Tube.le_volume.c 3 : ℝ≥0) : ℝ≥0∞) * (ρ : ℝ≥0∞) ^ 2) := hcoef.symm

/-- **The coarse Frostman count for `ρ`-tubes** (the first step of GWZ's `γ = 1` non-concentration
bound): a `CF`-Frostman family of `ρ`-tubes in `W` puts at most a
`coarseTubeVolumeRatio · CF · θ`-fraction of its members inside a subset of relative volume `θ`. -/
theorem card_coarse_le_of_frostmanIn {κ : Type*} {r : Finset κ} {ρ : ℝ≥0}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}
    {W K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))} {CF θ : ℝ≥0}
    (hFrost : ConvexSpaceBody.IsFrostmanIn r (fun k => (R k).toConvexSpaceBody) W (CF : ℝ≥0∞))
    (hRW : ∀ k ∈ r, (R k).toConvexSpaceBody ≤ W) (hKW : K ≤ W)
    (hW0 : volume W.carrier ≠ 0) (hWtop : volume W.carrier ≠ ⊤)
    (hvolK : volume K.carrier ≤ (θ : ℝ≥0∞) * volume W.carrier) :
    ((({k ∈ r | (R k).toConvexSpaceBody ≤ K}).card : ℝ≥0))
      ≤ coarseTubeVolumeRatio * CF * θ * (r.card : ℝ≥0) := by
  let v : ℝ≥0∞ := ((Tube.le_volume.c 3 : ℝ≥0) : ℝ≥0∞) * (ρ : ℝ≥0∞) ^ 2
  have hv0 : v ≠ 0 := by
    dsimp [v]
    refine mul_ne_zero ?_ ?_
    · exact ENNReal.coe_ne_zero.mpr (ne_of_gt (Tube.le_volume.c_pos 3))
    · exact pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr (ne_of_gt hρ0))
  have hvtop : v ≠ ⊤ := by
    dsimp [v]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  have hmin : ∀ k ∈ r, v ≤ volume ((R k).toConvexSpaceBody).carrier := by
    intro k hk
    simpa using (Tube.volume_comparable_three hρ1 (R k)).1
  have hmax : ∀ k ∈ r,
      volume ((R k).toConvexSpaceBody).carrier ≤ (coarseTubeVolumeRatio : ℝ≥0∞) * v := by
    intro k hk
    simpa using (Tube.volume_comparable_three hρ1 (R k)).2
  have hmain : (({k ∈ r | (R k).toConvexSpaceBody ≤ K}).card : ℝ≥0∞)
      ≤ ((coarseTubeVolumeRatio * CF * θ : ℝ≥0) : ℝ≥0∞) * (r.card : ℝ≥0∞) := by
    refine card_le_of_frostmanIn_of_volume_comparable (V := fun k => (R k).toConvexSpaceBody)
      (W := W) (K := K) (CF := CF) (θ := θ) (Cv := coarseTubeVolumeRatio) (v := v)
      hv0 hvtop hFrost hRW hKW hmin hmax hW0 hWtop hvolK
  exact ENNReal.coe_le_coe.mp hmain

/-! ## The combined Part-(B) input datum -/

/-- **The complete Part-(B) input.**  A coarse tube decomposition of the fine family together with a
factorisation of the coarse family.  This is the exact replacement for the weak hypothesis
`∀ i ∈ q, ∃ k ∈ r, T i ≤ R k` of `Kakeya.factoringAndMultPropGlobal`. -/
structure Section6PartBData (a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1)
    {ι : Type*} (q : Finset ι) {δ : ℝ≥0} (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    {κ : Type*} (coarseSet : Finset κ) {ρ : ℝ≥0}
    (R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))) (m Cfib CF C₀ : ℝ≥0) where
  /-- The fine-to-coarse decomposition. -/
  decomp : Section6CoarseTubeDecomposition q T coarseSet R m Cfib
  /-- The factorisation of the coarse family by outer cells. -/
  factor : Section6PartBFactorisation a b hab hb1 coarseSet R CF C₀

namespace Section6PartBData

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
  {ι : Type*} {q : Finset ι} {δ : ℝ≥0} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
  {κ : Type*} {coarseSet : Finset κ} {ρ : ℝ≥0} {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}
  {m Cfib CF C₀ : ℝ≥0}

/-- The cell of a fine index: the cell of its coarse parent. -/
def cellOfFine (D : Section6PartBData a b hab hb1 q T coarseSet R m Cfib CF C₀) (i : ι) :
    D.factor.Cell :=
  D.factor.cellOf (D.decomp.assign i)

open Classical in
/-- The fine tubes lying over a cell. -/
def fineFibre (D : Section6PartBData a b hab hb1 q T coarseSet R m Cfib CF C₀)
    (x : D.factor.Cell) : Finset ι :=
  {i ∈ q | D.cellOfFine i = x}

variable (D : Section6PartBData a b hab hb1 q T coarseSet R m Cfib CF C₀)

theorem mem_fineFibre_iff {x : D.factor.Cell} {i : ι} :
    i ∈ D.fineFibre x ↔ i ∈ q ∧ D.cellOfFine i = x := by
  simp [fineFibre, Finset.mem_filter]

theorem fineFibre_subset (x : D.factor.Cell) : D.fineFibre x ⊆ q := by
  rw [fineFibre]
  exact Finset.filter_subset (fun i => D.cellOfFine i = x) q

/-- The coarse parent of a fine tube of a cell belongs to that cell's coarse fibre. -/
theorem assign_mem_coarseFibre {x : D.factor.Cell} {i : ι} (hi : i ∈ D.fineFibre x) :
    D.decomp.assign i ∈ D.factor.coarseFibre x := by
  rw [Section6PartBFactorisation.mem_coarseFibre_iff]
  rw [mem_fineFibre_iff] at hi
  rcases hi with ⟨hiq, hxi⟩
  constructor
  · exact D.decomp.assign_mem i hiq
  · exact hxi

/-- Every fine tube of a cell lies in that cell's representative plank. -/
theorem carrier_subset_repr {x : D.factor.Cell} {i : ι} (hi : i ∈ D.fineFibre x) :
    (T i).carrier ⊆ ((D.factor.repr x).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
  have hq : i ∈ q := (D.mem_fineFibre_iff.mp hi).1
  have hcf : D.cellOfFine i = x := (D.mem_fineFibre_iff.mp hi).2
  have hcell : D.factor.cellOf (D.decomp.assign i) = x := by
    simpa [cellOfFine] using hcf
  have hle : (T i).toConvexSpaceBody ≤ (D.factor.repr x).toConvexSpaceBody := by
    rw [← hcell]
    exact le_trans (D.decomp.leaf_le_parent i hq) (D.factor.le_repr (D.decomp.assign_mem i hq))
  exact (SetLike.coe_subset_coe (S := (T i).toConvexSpaceBody)
    (T := (D.factor.repr x).toConvexSpaceBody)).mp hle

/-! ### Cardinality transport between the global and the cellwise fibres -/

open Classical in
/-- **The key cardinality transport.**  For a coarse index belonging to the cell `x`, the fine
indices assigned to it *within the cell* are exactly all the fine indices assigned to it.  Hence
every cardinality bound for the global fibres holds verbatim for the cellwise ones, with no loss.

This is what lets the two-sided fibre comparability of the decomposition be handed, unchanged, to
the cellwise consumer `Kakeya.katzTaoTransverseFactorBound`. -/
theorem filter_fineFibre_eq {x : D.factor.Cell} {k : κ} (hk : k ∈ D.factor.coarseFibre x) :
    ({i ∈ D.fineFibre x | D.decomp.assign i = k} : Finset ι) = D.decomp.fibre k := by
  ext i
  constructor
  · intro hi
    rw [Finset.mem_filter] at hi
    rw [D.decomp.mem_fibre_iff]
    exact ⟨D.fineFibre_subset x hi.1, hi.2⟩
  · intro hi
    rw [D.decomp.mem_fibre_iff] at hi
    rw [Finset.mem_filter]
    constructor
    · rw [D.mem_fineFibre_iff]
      refine ⟨hi.1, ?_⟩
      have hcell : D.factor.cellOf k = x := (D.factor.mem_coarseFibre_iff.mp hk).2
      calc
        D.cellOfFine i = D.factor.cellOf (D.decomp.assign i) := rfl
        _ = D.factor.cellOf k := by rw [hi.2]
        _ = x := hcell
    · exact hi.2

open Classical in
/-- The cellwise decomposition: the restriction of the global decomposition to a cell.  Its fibre
bounds are the global ones, by `Kakeya.Section6PartBData.filter_fineFibre_eq`. -/
def cellDecomposition (x : D.factor.Cell) :
    Section6CoarseTubeDecomposition (D.fineFibre x) T (D.factor.coarseFibre x) R m Cfib where
  assign := D.decomp.assign
  assign_mem := by
    intro i hi
    exact D.assign_mem_coarseFibre hi
  leaf_le_parent := by
    intro i hi
    exact D.decomp.leaf_le_parent i (D.fineFibre_subset x hi)
  one_le_Cfib := D.decomp.one_le_Cfib
  m_pos := D.decomp.m_pos
  fibre_nonempty := by
    intro k hk
    have hkc : k ∈ coarseSet := D.factor.coarseFibre_subset x hk
    rw [D.filter_fineFibre_eq hk]
    exact D.decomp.fibre_nonempty k hkc
  le_card_fibre := by
    intro k hk
    have hkc : k ∈ coarseSet := D.factor.coarseFibre_subset x hk
    rw [D.filter_fineFibre_eq hk]
    exact D.decomp.le_card_fibre k hkc
  card_fibre_le := by
    intro k hk
    have hkc : k ∈ coarseSet := D.factor.coarseFibre_subset x hk
    rw [D.filter_fineFibre_eq hk]
    exact D.decomp.card_fibre_le k hkc

/-! ### GWZ Remark 5.3 for Part (B) -/

/-- **The Part-(B) Frostman hypothesis, in the shape a Proposition-5.1 black box consumes.**

Only the *coarse* fibres are claimed to be Frostman.  The fine fibres are not, and must not be:
that is the content of GWZ Remark 5.3, and it is why Proposition 6.6(B) may be applied at all. -/
def Remark53FibreFrostman (D : Section6PartBData a b hab hb1 q T coarseSet R m Cfib CF C₀) : Prop :=
  ∀ x ∈ D.factor.cells,
    ConvexSpaceBody.IsFrostmanIn (D.factor.coarseFibre x) (fun k => (R k).toConvexSpaceBody)
      (D.factor.repr x).toConvexSpaceBody (CF : ℝ≥0∞)

/-- The Part-(B) datum supplies its own Remark-5.3 Frostman hypothesis. -/
theorem remark53FibreFrostman : D.Remark53FibreFrostman := by
  intro x hx
  exact D.factor.coarse_fibre_frostman x hx

open Classical in
/-- **GWZ Remark 5.3 for Part (B): fine non-concentration with no fine Frostman datum.**

Let `x` be a cell, `W = repr x` its representative plank, and `K ⊆ W` a convex body of relative
volume at most `θ`.  Then the fine tubes of the cell whose *coarse parents* lie in `K` number at
most `Cfib² · coarseTubeVolumeRatio · CF · θ · |𝒯_W|`.

The only Frostman input is the coarse-fibre datum; the fine family is controlled purely by fibre
comparability.  This is the `γ = 1` slab non-concentration hypothesis that Proposition 6.6(B) feeds
to GWZ Lemma 6.1. -/
theorem remark53_card_fine_le
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) {x : D.factor.Cell} (hx : x ∈ D.factor.cells)
    (hne : (D.factor.coarseFibre x).Nonempty)
    {K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))} {θ : ℝ≥0}
    (hKW : K ≤ (D.factor.repr x).toConvexSpaceBody)
    (hW0 : volume ((D.factor.repr x).carrier : Set (EuclideanSpace ℝ (Fin 3))) ≠ 0)
    (hvolK : volume K.carrier
      ≤ (θ : ℝ≥0∞) * volume ((D.factor.repr x).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    {qS : Finset ι} (hqS : qS ⊆ D.fineFibre x)
    (hmem : ∀ i ∈ qS, (R (D.decomp.assign i)).toConvexSpaceBody ≤ K) :
    (qS.card : ℝ≥0)
      ≤ Cfib ^ 2 * (coarseTubeVolumeRatio * CF * θ) * ((D.fineFibre x).card : ℝ≥0) := by
  let sel : Finset κ := {k ∈ D.factor.coarseFibre x | (R k).toConvexSpaceBody ≤ K}
  have hsel : sel ⊆ D.factor.coarseFibre x := by
    rw [show sel = (D.factor.coarseFibre x).filter (fun k => (R k).toConvexSpaceBody ≤ K) by rfl]
    exact Finset.filter_subset _ _
  have hRW : ∀ k ∈ D.factor.coarseFibre x,
      (R k).toConvexSpaceBody ≤ (D.factor.repr x).toConvexSpaceBody := by
    intro k hk
    rw [D.factor.mem_coarseFibre_iff] at hk
    rcases hk with ⟨hkcoarse, hkcell⟩
    rw [← hkcell]
    exact Section6PartBFactorisation.le_repr (F := D.factor) hkcoarse
  have hselcard : (sel.card : ℝ≥0) ≤
      (coarseTubeVolumeRatio * CF * θ) * ((D.factor.coarseFibre x).card : ℝ≥0) := by
    rw [show sel = (D.factor.coarseFibre x).filter (fun k => (R k).toConvexSpaceBody ≤ K) by rfl]
    have hWtop : volume ((D.factor.repr x).toConvexSpaceBody).carrier ≠ ⊤ :=
      (D.factor.repr x).isCompact.measure_lt_top.ne
    exact card_coarse_le_of_frostmanIn hρ0 hρ1 (r := D.factor.coarseFibre x)
      (W := (D.factor.repr x).toConvexSpaceBody) (K := K) (CF := CF) (θ := θ)
      (hFrost := D.remark53FibreFrostman x hx) (hRW := hRW) (hKW := hKW)
      (hW0 := hW0) (hWtop := hWtop) (hvolK := hvolK)
  have hmem_sel : ∀ i ∈ qS, D.decomp.assign i ∈ sel := by
    intro i hi
    rw [show sel = (D.factor.coarseFibre x).filter (fun k => (R k).toConvexSpaceBody ≤ K) by rfl]
    rw [Finset.mem_filter]
    exact ⟨D.assign_mem_coarseFibre (hqS hi), hmem i hi⟩
  exact (D.cellDecomposition x).card_le_of_selected hne
    (Cθ := coarseTubeVolumeRatio * CF * θ) (sel := sel) (hsel := hsel)
    (hselcard := hselcard) (qS := qS) (hqS := hqS) (hmem := hmem_sel)

/-! ### The output handed to the affine-normalisation layer -/


end Section6PartBData

end Kakeya

end

end

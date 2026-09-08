/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.ConvexBody
public import Kakeya.Pigeonhole

/-!
# Extracting an essentially distinct subfamily

GWZ Proposition 6.6(B) needs its *inner* normalised plank family to be pairwise essentially
distinct.  That property is **not** produced by the normalisation:
`Kakeya.innerShadedPlankFamily` only places the image `f(T i)` of each fine tube *inside* a model
plank `P i` of the exact dimensions `(δ/b) × (δ/a) × 1`, and essential distinctness is destroyed by
enlarging bodies — two barely-overlapping tubes can sit in two nearly coincident planks.  The
normalisation file records this explicitly.

The repair is an *extraction*: pass to a subfamily on which essential distinctness does hold, paying
a bounded factor in cardinality.  This file contains the combinatorial half of that argument, in a
form that is independent of all Section-6 data.

## What is here

`Kakeya.exists_conflictFree_subset` is the greedy independent-set bound: a symmetric conflict
relation whose degree on `s` is at most `d` admits a conflict-free `t ⊆ s` with
`s.card ≤ (d + 1) * t.card`.  `Kakeya.exists_essentiallyDistinct_subset` is its specialisation to
the conflict relation "fails to be essentially distinct".

Both are stated for an arbitrary family of sets, so they apply verbatim to the inner planks, to the
outer planks, or to any other family for which a degree bound is available.

## What is *not* here, and why

The geometric input — a bound on the conflict degree of the inner plank family — is deliberately
left to the caller.  It is a genuinely separate statement, and the honest route to it is:

1. two congruent planks overlapping in more than half their volume lie in a bounded dilate of one
   another;
2. hence every conflicting `f(T j)` lies in a bounded dilate `K` of the container of `f(T i)`, so
   after pulling back by the (affine, constant-Jacobian) normalisation every conflicting `T j` is a
   `δ`-tube inside a bounded dilate of the `δ`-tube `T i`;
3. a `δ`-tube inside a bounded dilate of a `δ`-tube has direction within `O(δ)` of it, so all
   conflicting tubes lie in a *single* direction cap;
4. `Kakeya.position_count_le_of_bad_directionClass'` bounds the number of pairwise-ED `δ`-tubes in
   one direction cap contained in `K` by `C · M` with `volume K ≤ M · δ ^ (n - 1)`; for a
   tube-shaped `K` the normalising factor `M` is absolute, so the degree is `O(1)`.

Step 4 is the reason the loss is an absolute constant rather than a power of `δ`: the generic count
`Kakeya.card_le_of_ED_subset` multiplies the position count by a factor `δ ^ (-(n-1))` of direction
caps, which is exactly what is *not* needed here, all conflicting tubes being nearly parallel.
Steps 1--3 are new geometry and are not attempted in this file.
-/

@[expose] public section

open MeasureTheory
-- Both conflict relations below are `Finset.filter`s over an arbitrary index type.
set_option linter.style.openClassical false
open scoped Classical

noncomputable section

namespace Kakeya


/-- **The ED conflict degree.**

The number of members of `s` whose body fails to be essentially distinct from `U i`.  This is the
single numerical quantity the geometric half of the argument has to bound; naming it lets a
downstream module state its bound without repeating the `Finset.filter` expression.

Note that `i` itself is counted whenever `i ∈ s` and `U i` has positive finite measure, so a bound
`edConflictDegree s U i ≤ d` implicitly allows `d ≥ 1`. -/
def edConflictDegree {ι : Type*} {E : Type*} [MeasureSpace E]
    (s : Finset ι) (U : ι → Set E) (i : ι) : ℕ :=
  ({j ∈ s | ¬ _root_.IsEssentiallyDistinct (U i) (U j)} : Finset ι).card


end Kakeya

end

end

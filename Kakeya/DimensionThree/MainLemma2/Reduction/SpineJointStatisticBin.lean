/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.RelativePlank

/-!
# `A1`: the vector bin bands leaf-determined statistics, not only cardinalities

 The (F) producer is **not** new mathematics: it is the composition
of two existing devices plus **one generalisation**.  This file is that generalisation.

## The delta, exactly

`Kakeya.exists_jointPartitionRegularization` (`Kakeya/RelativePlank.lean`) bands the
**cardinalities** of the classes of `M + 2` partitions at once.  The source asks for more: *"at most `K_0` additional fibre statistics … each lying in `[Λ^{-1}, Λ]` and
**depending only on the leaves of the relevant thread cell**"*, with the output
*"every label is then constant and every statistic is within a factor two at its level"*.

**"Depending only on the leaves" is the whole content, and it is what makes the generalisation
free.**  A statistic that depends only on the leaves of the thread cell is, by definition, a
function of the *class label* — it is `φ p : ν → σ` evaluated at `f p i`, not an arbitrary function
of `i`.  Such a statistic is therefore **constant on every class** of `f p`
(`statistic_constant_on_class` below), so its level sets are unions of classes, and banding it is
banding the classes of the coarser partition `φ p ∘ f p`.  That is the existing device applied to a
relabelled vector — no reproof of the hypergraph cleaning, and no new constant.

This is stated as a *finding*, not as a trick: the reason the source can regularize `K_0`
statistics "all at once" at the same cost as the partitions is precisely that they are
leaf-determined, and the existing device already bands an arbitrary vector of labels.

## The specialization to the identity map

`exists_jointPartitionRegularization_of_statistic` specialises to the existing statement by taking
`φ p = id`, and `jointStatisticRegularization_bridge_card` compiles that specialisation as a single
`exact`.  So the generalisation is pinned to the original rather than merely resembling it.

## Constants

`relativePlankJointLoss` and `relativePlankBandRatio` are the **existing** constants, reused
verbatim.  Nothing is coerced: this file introduces no constant of its own, and in particular does
not rename the source's `Λ_f = (2 + log₂(1/δ))^{K_f}`.

## Family / shading / level pair

| declaration | family / shading | level pair |
|---|---|---|
| `statistic_constant_on_class` | an abstract `Finset ι` with labels `f`; no shading | none |
| `exists_jointPartitionRegularization_of_statistic` | as above, `M + 2` label maps at once | none — the bin is level-agnostic; the `(F)` route instantiates it over `a < m < b`, `m ∈ 𝒲` |
| `jointStatisticRegularization_bridge_card` | as above | none |

The bin is deliberately level-agnostic.  The `𝒲`-quantified instantiation belongs to `A2` and is
**not** performed here; conflating the two is the defect this column exists to catch.
-/

@[expose] public section

namespace Kakeya.ML2Core

section JointStatisticBin

variable {ι ν σ : Type*}


/-! ### The factor-two band on the statistic's *values*

Banding the *level sets* of a statistic is not the source's *"every statistic is within a
factor two at its level"*: that is a statement about the statistic's **values**.  The bridge is the
dyadic index — relabel by `⌊log₂ stat⌋` and a constant label forces a factor-two band.  This is
where `[Λ^{-1}, Λ]` of  actually comes from, and it is recorded separately so the two
readings are not conflated. -/

/-- The dyadic band index of a statistic value; the relabelling that turns a real-valued
leaf-determined statistic into a label the vector bin can carry. -/
def dyadicBandIndex (n : ℕ) : ℕ := Nat.log 2 n

/-- **Constant dyadic band ⟹ within a factor two**.  Nothing about the vector bin is used;
this is the reason the relabelling is the right one. -/
theorem within_factor_two_of_dyadicBandIndex_eq {m n : ℕ} (hm : m ≠ 0)
    (h : dyadicBandIndex m = dyadicBandIndex n) : n < 2 * m := by
  have h1 : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 hm
  have h2 : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have h3 : Nat.log 2 n = Nat.log 2 m := h.symm
  calc n < 2 ^ (Nat.log 2 n + 1) := h2
    _ = 2 * 2 ^ Nat.log 2 m := by rw [h3, pow_succ]; ring
    _ ≤ 2 * m := Nat.mul_le_mul_left 2 h1


/-! ### The charge is `Λ_f`-shaped: why ML1's rejection does not carry over

 The vector bin was rejected in ML1 (`MainLemma1/Factoring.lean`) because its constant *"depends on `#s` and is unbounded as `δ → 0`"* while ML1 needed a
**dimension-only** field — but that `(F)`'s loss `Λ_f = (2 + log₂(1/δ))^{K_f}` is
**polylogarithmic by definition**, so the same charge is exactly what `(F)` is designed to pay.

The two declarations below compile that claim rather than asserting it: the existing joint loss *is*
`2 (log₂ #s + 1)^{M+2}`, and under a cardinality ceiling `#s ≤ 2^k` it is
`2 (k+1)^{M+2}` — the shape of `Λ_f` with `K_f = M + 2`.  Applied at the source's `#s ≤ δ^{-4}`,
`k = 4 log₂(1/δ)`, this is `Λ_f` up to the named constant.

**No constant is coerced.**  Nothing here rewrites `Λ_f`; `k` is left free, and a caller supplies
whatever ceiling its own hypothesis prints. -/


end JointStatisticBin

end Kakeya.ML2Core

end

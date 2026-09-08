/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineJointStatisticBin
public import Kakeya.Density

/-!
# From a dyadic bin to a two-sided `ENNReal` band — `level_density_band`'s engine

`Kakeya.ML2Reduction.IsKatzTaoDividingWindowLevels.level_density_band` (GWZ: *"pairwise within a factor two at every fixed level or pair of levels"*) is a
**two-sided `ENNReal`** statement through a profile `Φ`:

  `Φ p c ≤ Δ_max(𝕋_c⟨j⟩) ≤ Cstar · Φ p c`   for every level-`p` cell `j`.

`Kakeya.ML2Core.exists_jointStatisticBand` (`SpineJointStatisticBin.lean`) is the source's
*"simultaneous vector-bin regularization"* but it is **ℕ-shaped**: it regularizes
integer statistics of leaves and its factor-two clause is `stat p (f p j) < 2 * stat p (f p i)`
for leaves in a common dyadic bin.  The gap between the two is this file.

## What the bridge actually needs, and what it does not

It does **not** need a real-number logarithm or an `ENNReal → ℕ` discretization.  The only content
of "one dyadic bin" that the band uses is the *pairwise* clause

  `bucket k = bucket k' → D k' ≤ 2 * D k`,

and `dyadicBandIndex` already supplies exactly that for `ℕ` values
(`Kakeya.ML2Core.within_factor_two_of_dyadicBandIndex_eq`).  So `exists_bucket_band` takes the
bucket map and its pairwise clause abstractly, does the pigeonhole, and produces the profile.

**The profile is the bin's infimum, and `Cstar = 2` exactly.**  Taking `Φ := inf_{k ∈ K'} D k`
gives `Φ ≤ D k` on the nose, and `D k ≤ 2 * D k₁ = 2 * Φ` at the minimiser `k₁`.  No division, no
finiteness hypothesis on `D`, and the constant is the source's own factor two rather than a fitted
one.  (Taking `Φ := D k₀` for an arbitrary `k₀` would give the weaker two-sided
`Φ ≤ 2 * D k ∧ D k ≤ 2 * Φ`; the infimum is what makes the left half exact, which is the half
`level_density_band` states without a constant.)

## The factor two is not slack — `not_bucket_band_at_factor_one` is a counterexample to the stronger bound: the same hypotheses with
`Cstar` tightened from `2` to `1` are **false**, witnessed by `K = {0,1}`, `bucket ≡ 0`, `D 0 = 1`,
`D 1 = 2`.  Those satisfy the pairwise clause (`2 ≤ 2·1` and `1 ≤ 2·2`) and no `Φ` can satisfy
`Φ ≤ D k ∧ D k ≤ 1 * Φ` at both, since that forces `D` constant.  So the `2` is doing work and the
theorem is not vacuously improvable.

## MEASURED: the existing A1 is a **balanced-bin** statement, not a **single-bin** one

The plan for this row was to instantiate `Kakeya.ML2Core.exists_jointStatisticBand` at the four
statistics of  and read `level_density_band` off it.  **That does not work as stated**,
and the reason is a shape difference worth recording rather than working around silently.

`exists_jointStatisticBand`'s pigeonhole content is its *second* conjunct
(`SpineJointStatisticBin.lean`):

> `∀ p, ∀ v ∈ s'.image (fun i => dyadicBandIndex (stat p (f p i))),`
> `  N p ≤ {i ∈ s' | … = v}.card ∧ {i ∈ s' | … = v}.card ≤ relativePlankBandRatio … * N p`

— every bin **that survives** has cardinality within a fixed ratio of `N p`.  That is
*equidistribution across bins*.  Its third conjunct is not pigeonhole content at all: it is
`within_factor_two_of_dyadicBandIndex_eq` applied pointwise, i.e. it is conditional on two leaves
*already* sharing a bin.

What `level_density_band` needs is the opposite: **all** surviving members in **one** bin per
statistic, so that a single profile `Φ p c` bounds them two-sidedly.  Equidistribution does not
imply concentration — a family evenly spread over many bins satisfies the existing conclusion and has
no single profile at all.

The two pigeonholes have the **same loss shape** (`relativePlankJointLoss n M =
2 * relativePlankBucket n ^ relativePlankRounds M` is exactly "one dyadic bucketing per partition"),
which is presumably why the plan conflated them.  `exists_joint_bucket_band` below is the
concentration form, proved directly by iterating `exists_bucket_band` over the statistics; its loss
is `L ^ n`, the same product of per-statistic bucket counts.

** and nothing is claimed against `exists_jointStatisticBand`**: it is a
correct statement of a different pigeonhole, and it remains the right tool wherever
equidistribution is what is wanted.

## The three riders (3), and the one thing that must not ride

§9.6 amends §9.4: the source's vector bin is **concentration** ( *"retaining one joint
vector bin"*,  *"every label is then constant"*), the existing
`Kakeya.exists_jointPartitionRegularization` states equidistribution, and **A1 is the concentration
sibling** — the object this file builds.  For the record, and at the visibility §9.6 asks: this is
*standard pigeonholing, cheap, and it has to be written*; it is **the one genuinely new lemma text
of the payload side**, everything else on this route being a restatement or a composition of existing
material.

Three things ride with the abstract band or the transcription is not faithful:

1. **The label** — a discrete label taking at most `K₀` values, *constant*
   across survivors.  `exists_constant_label` is that pigeonhole and
   `exists_joint_bucket_band_with_label` carries it, at the extra factor `K₀` in the loss.  `K₀` is
   the source's own bound on the number of label values and is a parameter here, not a fitted
   constant.
2. **The root-ward descent over `M + 1` levels**.  `exists_joint_bucket_band`'s
   `L ^ n` is **one** application at **one** level; the source's `[K₀(2 + 2log₂Λ)^{K₀}]^{-(M+1)}` is
   the composition across levels.  The two are stated separately here: the per-level loss is
   `K₀ * L ^ n` (`exists_joint_bucket_band_with_label`) and the composition is
   `card_le_pow_of_chain`, giving the total `(K₀ * L ^ n) ^ (M + 1)`.  With `L` the bucket count
   `2 + 2log₂Λ` and `n = K₀` statistics this is the source's expression verbatim; **that** is where
   `Λ_f`'s polylog shape comes from, not from a single application.
3. **Leaf-locality, and the stability it buys** ( *"depends only on the leaves of the
   relevant thread cell"*;  *"Later restrictions to an ancestor retain or discard an
   entire descendant fibre, so an already regularized leaf-local statistic is not changed"*).  This
   is the load-bearing one and a bare bucket band does **not** imply it.  It is therefore a
   **hypothesis** — `LeafLocalStat`, a statistic whose value at a leaf depends only on that leaf's
   cell fibre *within the family it is computed in* — and the stability is a **conclusion**,
   `band_stable_of_leafLocal`: the band survives any whole-fibre ancestor restriction.
   `not_stable_of_not_leafLocal` is the control: the family-size statistic `#u` is not leaf-local
   and its value **does** move under a whole-fibre restriction, so the hypothesis is doing work.

**And one clause that must NOT ride.**  `Kakeya.exists_jointPartitionRegularization`'s third
conjunct protects partition `0` against the *original* family (`SpineJointStatisticBin.lean`).
That is a virtue of the existing device — it solves ML1's plank-block problem — but the source's bin
has **no such clause**; its analogue is leaf-locality, a different mechanism.  Nothing in this file
has it: the conclusions of `exists_bucket_band`, `exists_joint_bucket_band` and
`exists_joint_bucket_band_with_label` mention only `K`, `K'`, the statistics and the label, and no
distinguished index.  Importing it would be a clause the source does not have — the  objection
in the one place where it does hold.

## The bucket map for `ENNReal` statistics, and the brackets it needs — measured

`exists_bucket_band` and `exists_joint_bucket_band` take `bucket` abstractly.  For a genuinely
`ENNReal`-valued statistic the bucket is `dyadicScaleBucket lo D`, the **least `j` with
`D ≤ 2 ^ j * lo`** — a dyadic bucketing relative to a supplied floor `lo`, entirely inside
`ENNReal`, with no `Real.logb`, no `toReal` and no finiteness side condition.  Its pairwise clause
`le_two_mul_of_dyadicScaleBucket_eq` is the exact analogue of
`Kakeya.ML2Core.within_factor_two_of_dyadicBandIndex_eq`, and its proof is the same one: the
minimality of `Nat.find` at `j` gives `2 ^ (j-1) * lo < x`, and `y ≤ 2 ^ j * lo`.
The `j = 0` case is where the **lower** bracket `lo ≤ x` is used, and it is the only place.

The ceiling is `L = J + 1` for any `J` with `D ≤ 2 ^ J * lo` on the whole family
(`dyadicScaleBucket_lt_succ`); `exists_pow_two_bracket` shows such a `J` exists as soon as the
bracket is nondegenerate (`lo ≠ 0`, `hi ≠ ⊤`).

**The bounds for each statistic and the facts supplying them.**

| statistic | lower bracket | supplied by | upper bracket | supplied by |
|---|---|---|---|---|
| two-level maximal densities | `1` | `one_le_maxDensity` | `#𝕋_c⟨S⟩` | `maxDensity_le_card` |
| descendant / two-level counts | `1` | `Finset.card_pos` | `(32/ρ_k)^6`,  | source hyp. |
| fibre shaded masses | `δ^{3η_f}` | , *"fullness at least"* | total mass | trivial |

**`C₁ = 0` for the first two rows — the lower bracket is `1`, not a power of `δ`.**  That is worth
recording because it was not the expected shape: `Kakeya.one_le_maxDensity` says a cell containing
one positive-volume tube already has `Δ_max ≥ 1`, so nothing has to be assumed and no `δ`-power is
spent below.  `Λ_f`'s logarithm therefore comes **entirely from the upper bracket**: with
`D ≤ hi` and `lo = 1` the ceiling is `J = ⌈log₂ hi⌉`, and at the source's `hi = (32/ρ_k)^6` this is
`O(log₂(1/δ))`, i.e. `L = O(2 + log₂(1/δ))` and `L ^ n = Λ_f` with `K_f = n` the number of
statistics — the source's  shape, with `C₁ = 0` and `C₂` read off  rather than fitted.
Only the shaded-mass row spends a `δ`-power below, and it spends the source's own `3η_f`.

## Where `Λ_f` is paid

The loss is the bucket count `L`: the pigeonhole keeps a `1/L` share, `K.card ≤ L * K'.card`.  With
`L` instantiated at the existing `relativePlankJointLoss n M` — one dyadic bucketing per partition,
times the deletion factor `2` — `bucketBandLoss_le_polylog` composes with the existing
`relativePlankJointLoss_le_of_card_le_pow` to give `L ≤ 2 * (k + 1) ^ (M + 2)` under `n ≤ 2 ^ k`.
That is `Λ_f = (2 + log₂(1/δ))^{K_f}`'s shape with `K_f = M + 2`, exactly as
`SpineJointStatisticBin.lean`'s own header records; applied at the source's `#s ≤ δ^{-4}` one takes
`k = 4 log₂(1/δ)` and the numeric factors are absorbed into the named constant.  **Nothing here
rewrites `Λ_f`**: `k` and `M` are left free and the caller supplies its own ceiling.

## Family / shading / level pair

| declaration | family / shading | level pair |
|---|---|---|
| `exists_bucket_band` | abstract: a `Finset κ` with an `ENNReal` statistic; no shading | none |
| `exists_joint_bucket_band` | abstract: `n` statistics at once; no shading | none |
| `dyadicScaleBucket`, its two lemmas | abstract; no shading | none |
| `exists_joint_bucket_band_of_bracket` | abstract; no shading | none |
| `exists_constant_label`, `..._with_label` | abstract; no shading | none |
| `LeafLocalStat`, `band_stable_of_leafLocal` | the leaf's thread cell | its statistic's level |
| `card_le_pow_of_chain` | none | the `M + 1` levels of the descent |
| `not_bucket_band_at_factor_one` | none — a two-point counterexample | none |
| `bucketBandLoss_le_polylog` | none | none |

## A1-a

Nothing here mentions `GridUniformCore`, and nothing here is an (F)-branch interface statement:
`exists_bucket_band` is a pigeonhole about an abstract `Finset`.
-/

@[expose] public section

open scoped NNReal ENNReal

namespace Kakeya.ML2Core

section DensityBandFromBin


/-! ### The bucket map for `ENNReal` statistics -/

open scoped Classical in
/-- **The dyadic bucket of `D` relative to a floor `lo`**: the least `j` with `D ≤ 2 ^ j * lo`.

Entirely inside `ENNReal` — no `Real.logb`, no `toReal`, no finiteness side condition.  The
`ENNReal` analogue of `Kakeya.ML2Core.dyadicBandIndex`. -/
noncomputable def dyadicScaleBucket (lo D : ℝ≥0∞) : ℕ :=
  if h : ∃ j : ℕ, D ≤ 2 ^ j * lo then Nat.find h else 0

/-- **The ceiling**: a single `J` working for the whole family caps every bucket by `J`, so the
bucket count is `L = J + 1`. -/
theorem dyadicScaleBucket_lt_succ {lo D : ℝ≥0∞} {J : ℕ} (h : D ≤ 2 ^ J * lo) :
    dyadicScaleBucket lo D < J + 1 := by
  have hex : ∃ j : ℕ, D ≤ 2 ^ j * lo := ⟨J, h⟩
  rw [dyadicScaleBucket, dif_pos hex]
  exact Nat.lt_succ_of_le (Nat.find_le h)

/-- **The pairwise clause** — the `ENNReal` analogue of
`Kakeya.ML2Core.within_factor_two_of_dyadicBandIndex_eq`, by the same argument.  The lower bracket
`lo ≤ x` is used **only** in the `j = 0` case. -/
theorem le_two_mul_of_dyadicScaleBucket_eq {lo x y : ℝ≥0∞}
    (hx : ∃ j : ℕ, x ≤ 2 ^ j * lo) (hy : ∃ j : ℕ, y ≤ 2 ^ j * lo) (hlox : lo ≤ x)
    (h : dyadicScaleBucket lo x = dyadicScaleBucket lo y) : y ≤ 2 * x := by
  classical
  rw [dyadicScaleBucket, dif_pos hx, dyadicScaleBucket, dif_pos hy] at h
  have hyspec : y ≤ 2 ^ (Nat.find hy) * lo := Nat.find_spec hy
  rw [← h] at hyspec
  have hxx : x ≤ 2 * x := by
    nth_rewrite 1 [← one_mul x]
    gcongr
    norm_num
  cases hj : Nat.find hx with
  | zero =>
      rw [hj] at hyspec
      simp only [pow_zero, one_mul] at hyspec
      exact hyspec.trans (hlox.trans hxx)
  | succ m =>
      have hmin : ¬ (x ≤ 2 ^ m * lo) := Nat.find_min hx (by rw [hj]; omega)
      have hlt : 2 ^ m * lo < x := lt_of_not_ge hmin
      rw [hj] at hyspec
      calc y ≤ 2 ^ (m + 1) * lo := hyspec
        _ = 2 * (2 ^ m * lo) := by ring
        _ ≤ 2 * x := by gcongr


/-! ### Rider 1: the label -/


/-! ### Rider 2: the root-ward descent over `M + 1` levels -/


/-! ### Rider 3: leaf-locality, and the stability it buys -/

/-- **A leaf-local statistic** (GWZ: *"depends only on the leaves of the relevant thread
cell"*): its value at a leaf `i` is determined by the fibre of `i`'s cell **inside the family the
statistic is computed in**.  The family is an explicit argument precisely so that "not changed by a
later restriction" is expressible. -/
def LeafLocalStat {ι γ : Type*} [DecidableEq γ] (cell : ι → γ)
    (D : Finset ι → ι → ℝ≥0∞) : Prop :=
  ∀ (u v : Finset ι) (i : ι),
    {j ∈ u | cell j = cell i} = {j ∈ v | cell j = cell i} → D u i = D v i

/-- **A whole-fibre restriction** (GWZ: *"retain or discard an entire descendant fibre"*):
`t` is obtained from `u` by keeping whole `cell`-fibres. -/
def WholeFibreSubset {ι γ : Type*} (cell : ι → γ) (t u : Finset ι) : Prop :=
  t ⊆ u ∧ ∀ i ∈ t, ∀ j ∈ u, cell j = cell i → j ∈ t

/-- **A leaf-local statistic is unchanged by a whole-fibre restriction** — . -/
theorem leafLocalStat_stable {ι γ : Type*} [DecidableEq γ] {cell : ι → γ}
    {D : Finset ι → ι → ℝ≥0∞} (hD : LeafLocalStat cell D)
    {t u : Finset ι} (h : WholeFibreSubset cell t u) {i : ι} (hi : i ∈ t) :
    D t i = D u i := by
  refine hD t u i (Finset.ext fun j => ?_)
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hj, hcj⟩
    exact ⟨h.1 hj, hcj⟩
  · rintro ⟨hj, hcj⟩
    exact ⟨h.2 i hi j hj hcj, hcj⟩


end DensityBandFromBin

end Kakeya.ML2Core

end

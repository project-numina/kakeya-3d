/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.NonSlabAngle
public import Kakeya.Uniform

/-!
# The `ρ₂*`-fibres of the non-slab case of Main Lemma 2

The inner factor of the non-slab splitting is the multiplicity of a single fibre
`𝕋[T_{ρ₂*}]` of the parent family `𝕋_{ρ₂*}` of blueprint `uniformSetOfTubes`. This file
collects everything that is needed *about the fibres themselves*, before any Katz–Tao input
is consumed:

* the two purely combinatorial inputs, blueprint `lem:coverCardEqDisjoint` (a finite cover of
  exact total size is a partition) and blueprint `lem:mediantSelect` (mediant selection),
  neither of which is in Mathlib;
* blueprint `lem:ml2fullnessOfPartition`, the fullness of a family split over a partition;
* blueprint `lem:ml2tubeScaleCompare`, the comparison `|𝕋_ρ| ≤ (ρ'/ρ)² |𝕋_{ρ'}|` of the
  parent families at two angular scales — an *assumption*, see the note on its statement;
* blueprint `lem:ml2nonslabFibreCount`, the resulting bound
  `|𝕋[T_{ρ₂*}]| ≤ K · Ccnt · ρ₂^{2+ζ}|𝕋|` at the hierarchy constant `K` and the count constant
  `Ccnt` (both explicit parameters), and the fibre count `|𝕋_{ρ₂*}| · |𝕋[T_{ρ₂*}]| ≤ Cu² |𝕋|` as a theorem of
  `Tube.UniformTubeSet`;
* blueprint `lem:ml2nonslabFibrePartition` and `lem:ml2nonslabFullFibre`, which use the
  hierarchy assignment classes to partition `𝕋` and select a fibre at least as full as `𝕋`.

The last of these is what discharges the fullness hypothesis of
`Kakeya.VeryNotSticky.nonslabKKT`: fullness is not inherited by an arbitrary subfamily, but
the fibres partition `𝕋`, so at least one of them is at least as full as `𝕋`.
-/

@[expose] public section

open scoped NNReal ENNReal

namespace Kakeya

section Combinatorics


/-- **Mediant selection**.

For nonnegative `p j` and finite positive `q j` over a finite nonempty index set, some index
beats the mediant: `(∑ p) / (∑ q) ≤ p j / q j` for some `j`.

Writing `L` for the left-hand side one has `∑_j L * q j = ∑_j p j`, so
`Finset.exists_le_of_sum_le` supplies a `j` with `L * q j ≤ p j`, and dividing by `q j` gives
the claim. Mathlib has no mediant selection lemma, so it is recorded here.

The statement is in `ℝ≥0∞` rather than in `ℝ`, because that is the type of the numerator and
denominator of `ShadedBody.fullness'`, which is where it is consumed; the hypotheses
`q j ≠ 0` and `q j ≠ ⊤` are the blueprint's `0 < q_j < ∞`. -/
theorem exists_sum_div_sum_le {κ : Type*} {J : Finset κ} (hJ : J.Nonempty)
    (p q : κ → ℝ≥0∞) (hq0 : ∀ j ∈ J, q j ≠ 0) (hqtop : ∀ j ∈ J, q j ≠ ⊤) :
    ∃ j ∈ J, (∑ k ∈ J, p k) / (∑ k ∈ J, q k) ≤ p j / q j := by
  classical
  let Sp : ℝ≥0∞ := ∑ k ∈ J, p k
  let Sq : ℝ≥0∞ := ∑ k ∈ J, q k
  let L : ℝ≥0∞ := Sp / Sq
  have hSq0 : Sq ≠ 0 := by
    intro hSq0
    rcases hJ with ⟨j, hj⟩
    have hqj0 : q j = 0 := by
      have hle : q j ≤ Sq := by
        dsimp [Sq]
        exact Finset.single_le_sum (fun x _ => zero_le) hj
      rw [hSq0] at hle
      exact le_antisymm hle zero_le
    exact hq0 j hj hqj0
  have hSqt : Sq ≠ ⊤ := by
    dsimp [Sq]
    exact (ENNReal.sum_ne_top (s := J) (f := q)).2 (fun k hk => hqtop k hk)
  have hL : L * Sq = Sp := by
    dsimp [L]
    rw [ENNReal.div_mul_cancel hSq0 hSqt]
  have hsum_eq : (∑ k ∈ J, L * q k) = Sp := by
    calc
      (∑ k ∈ J, L * q k) = L * (∑ k ∈ J, q k) := by rw [Finset.mul_sum]
      _ = L * Sq := rfl
      _ = Sp := hL
  rcases ENNReal.exists_le_of_sum_le hJ (f := fun k => L * q k) (g := p) (by
      exact le_of_eq (by rw [hsum_eq])) with ⟨j, hj, hLqle⟩
  refine ⟨j, hj, ?_⟩
  rw [ENNReal.le_div_iff_mul_le (Or.inl (hq0 j hj)) (Or.inl (hqtop j hj))]
  exact hLqle

/-- **Markov on densities**, division-free form.

If `d` is any *lower* bound for the aggregate density in the sense that `d · ∑ v ≤ ∑ m`, then the
blocks whose own density beats `κ d`, that is `{j ∈ J | κ · d · v j ≤ m j}`, carry all but a `κ`
fraction of the mass `∑ m`.

This is the form that `Kakeya.le_sum_filter_dense` --- the blueprint statement
`lem:densityMarkov`, with `d = M / V` --- is deduced from, and the form that is easiest to
consume downstream, since no division occurs in it. -/
theorem le_sum_filter_of_mul_sum_le {ι : Type*} {J : Finset ι} {m v : ι → ℝ≥0∞}
    {d κ : ℝ≥0∞} (hm : ∑ j ∈ J, m j ≠ ⊤) (_hκ : κ ≤ 1)
    (hd : d * ∑ j ∈ J, v j ≤ ∑ j ∈ J, m j) :
    (1 - κ) * ∑ j ∈ J, m j ≤ ∑ j ∈ {j ∈ J | κ * d * v j ≤ m j}, m j := by
  let M : ℝ≥0∞ := ∑ j ∈ J, m j
  let S : Finset ι := {j ∈ J | κ * d * v j ≤ m j}
  let T : Finset ι := J.filter (fun j => ¬ κ * d * v j ≤ m j)
  have hmM : M ≠ ⊤ := by simpa [M] using hm
  have hTJ : T ⊆ J := by
    simp [T]
  have hsplit : M = (∑ j ∈ S, m j) + (∑ j ∈ T, m j) := by
    unfold M S T
    rw [← Finset.sum_filter_add_sum_filter_not J (fun j => κ * d * v j ≤ m j) (fun j => m j)]
  have hTm : ∀ j ∈ T, m j ≤ κ * d * v j := by
    intro j hj
    exact le_of_lt (not_le.mp (Finset.mem_filter.mp hj).2)
  have hsumT : (∑ j ∈ T, m j) ≤ κ * M := by
    calc
      (∑ j ∈ T, m j) ≤ ∑ j ∈ T, κ * d * v j := Finset.sum_le_sum hTm
      _ = κ * d * (∑ j ∈ T, v j) := by
        rw [← Finset.mul_sum]
      _ ≤ κ * d * (∑ j ∈ J, v j) :=
        mul_le_mul_right (Finset.sum_le_sum_of_subset hTJ) (κ * d)
      _ ≤ κ * M := by
        calc
          κ * d * (∑ j ∈ J, v j) = κ * (d * (∑ j ∈ J, v j)) := by rw [mul_assoc]
          _ ≤ κ * M := mul_le_mul_right hd κ
  have hle : M ≤ (∑ j ∈ S, m j) + κ * M := by
    calc
      M = (∑ j ∈ S, m j) + (∑ j ∈ T, m j) := hsplit
      _ ≤ (∑ j ∈ S, m j) + κ * M := by
        simpa [add_comm, add_left_comm, add_assoc] using
          (add_le_add_left hsumT (∑ j ∈ S, m j))
  have hsub : (1 - κ) * M = M - κ * M := by
    calc
      (1 - κ) * M = 1 * M - κ * M := ENNReal.sub_mul (fun _ _ => hmM)
      _ = M - κ * M := by rw [one_mul]
  rw [hsub, tsub_le_iff_right]
  exact hle


end Combinatorics

end Kakeya

namespace ShadedBody

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Fullness of a partitioned family**.

If the subfamilies `f j`, `j ∈ J`, are pairwise disjoint, then both the numerator and the
denominator of the fullness of their union split over the partition; this is
`Finset.sum_biUnion` applied to `V ↦ |Y(V)|` and to `V ↦ |V|`. -/
theorem fullness'_biUnion {ι κ : Type*} [DecidableEq ι] {J : Finset κ} {f : κ → Finset ι}
    (V : ι → ShadedBody E) (hdisj : (J : Set κ).PairwiseDisjoint f) :
    fullness' (J.biUnion f) V =
      (∑ j ∈ J, ∑ i ∈ f j, volume (V i).shade) /
        (∑ j ∈ J, ∑ i ∈ f j, volume (V i).carrier) := by
  classical
  unfold fullness'
  rw [Finset.sum_biUnion hdisj, Finset.sum_biUnion hdisj]

end ShadedBody

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set ShadedBody
open scoped NNReal ENNReal

open scoped Classical in
/-- The fibre `𝕋[T_ρ]` of a node in the uniform tube hierarchy: the tubes assigned to the node
indexed by `j` at grid level `k`. -/
noncomputable def tubeFibre (cfg : VeryNotSticky) {N : ℕ} {C : ℝ≥0}
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) N C)
    (k : ℕ) (j : cfg.ι) : Finset cfg.ι :=
  Tube.coverClass cfg.s (𝒰.cover.assign k) j

lemma tubeFibre_subset (cfg : VeryNotSticky) {N : ℕ} {C : ℝ≥0}
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) N C)
    (k : ℕ) (j : cfg.ι) : cfg.tubeFibre 𝒰 k j ⊆ cfg.s := by
  simp [tubeFibre, Tube.coverClass]

open scoped Classical in
/-- The nodes at level `k` that have a nonempty assignment class. -/
noncomputable def activeTubeNodes (cfg : VeryNotSticky) {N : ℕ} {C : ℝ≥0}
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) N C)
    (k : ℕ) : Finset cfg.ι :=
  (𝒰.cover.indexSet k).filter fun j ↦ (cfg.tubeFibre 𝒰 k j).Nonempty


/-- **Counting the tubes in a `ρ₂*`-fibre**.

Here `N = |𝕋_{ρ₂*}|` and `sub = 𝕋[T_{ρ₂*}]`. The hypothesis `hfib` is item (iii) of blueprint
`uniformSetOfTubes` — GWZ Def 2.1(iii), "`|𝕋[T_ρ]|` is constant up to a factor `∼ 1`"
(GWZ) — in the inequality shape `N |𝕋[T_{ρ₂*}]| ≤ K |𝕋|` with the hierarchy
constant `K`, which is all this
bound needs; the hypothesis `hcount` is the lower bound
`ρ₂^{-2-ζ} ≤ Ccnt · N` at a **general** count constant `Ccnt` (fixing `Ccnt = (2 C_{lem:ml2bodyAngle}(C₀))²`, which no producer of
`Kakeya.VeryNotSticky.SplitInputs.fibreScaleCount` can supply —  — so the constant
is now a parameter and the numeral lives at the call site only). In the blueprint that lower
bound comes from `rho2_range` at the scale `ρ₂` and from
`Kakeya.VeryNotSticky.tubeScaleCompare` at `(ρ₂, ρ₂*)`, whose ratio is exactly
`2 C_{lem:ml2bodyAngle}(C₀)`; the existing producer
`Kakeya.VeryNotSticky.exists_fibreScaleCount_of_rhoParentData` reaches it instead at
`Ccnt ≤ δ^{-18 η}`.

The *undilated* `ρ₂` appears on the right because `rho2_range` is not available at `ρ₂*`,
which may exceed `δ^{exscal}`; the ratio `ρ₂*/ρ₂` is fixed once `C₀` is, so this costs only
the displayed constant. This is the second display of blueprint `lem:ml2nonslabKKT`, stated on
its own rather than as a conjunct of `Kakeya.VeryNotSticky.nonslabKKT`, so that the consumers
of the counting bound do not have to carry the Katz–Tao hypothesis. -/
theorem nonslabFibreCount (cfg : VeryNotSticky)
    (hrho2 : 0 < cfg.rho2) {sub : Finset cfg.ι} (N : ℕ) {K Ccnt : ℝ≥0}
    (hfib : (N : ℝ) * (sub.card : ℝ) ≤ (K : ℝ) * (cfg.s.card : ℝ))
    (hcount : (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤ (Ccnt : ℝ) * (N : ℝ)) :
    (sub.card : ℝ) ≤ (K : ℝ) * (Ccnt : ℝ) *
      (cfg.rho2 : ℝ) ^ (2 + cfg.ζ) * (cfg.s.card : ℝ) := by
  let ρ : ℝ := (cfg.rho2 : ℝ)
  let C : ℝ := (Ccnt : ℝ)
  have hCnonneg : (0 : ℝ) ≤ C := Ccnt.coe_nonneg
  have hρgt : 0 < ρ := by
    dsimp [ρ]
    exact_mod_cast hrho2
  have hρnonneg : 0 ≤ ρ := le_of_lt hρgt
  have h1 : ρ ^ (2 + cfg.ζ) * ρ ^ (-2 - cfg.ζ) = 1 := by
    rw [← Real.rpow_add hρgt]
    have hexp : (2 + cfg.ζ) + (-2 - cfg.ζ) = 0 := by ring
    rw [hexp, Real.rpow_zero]
  have hstep1 : (1 : ℝ) ≤ C * ρ ^ (2 + cfg.ζ) * (N : ℝ) := by
    rw [← h1]
    calc
      ρ ^ (2 + cfg.ζ) * ρ ^ (-2 - cfg.ζ) ≤ ρ ^ (2 + cfg.ζ) * (C * (N : ℝ)) := by
        exact mul_le_mul_of_nonneg_left (by simpa [ρ, C] using hcount)
          (Real.rpow_nonneg hρnonneg (2 + cfg.ζ))
      _ = C * ρ ^ (2 + cfg.ζ) * (N : ℝ) := by ring
  calc
    (sub.card : ℝ) = 1 * (sub.card : ℝ) := by rw [one_mul]
    _ ≤ (C * ρ ^ (2 + cfg.ζ) * (N : ℝ)) * (sub.card : ℝ) := by
      exact mul_le_mul_of_nonneg_right hstep1 (Nat.cast_nonneg sub.card)
    _ = C * ρ ^ (2 + cfg.ζ) * ((N : ℝ) * (sub.card : ℝ)) := by ring
    _ ≤ C * ρ ^ (2 + cfg.ζ) * ((K : ℝ) * (cfg.s.card : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hfib
        (mul_nonneg hCnonneg (Real.rpow_nonneg hρnonneg (2 + cfg.ζ)))
    _ = (K : ℝ) * C * ρ ^ (2 + cfg.ζ) * (cfg.s.card : ℝ) := by ring

/-- **The fibre count in powered form**.

Raising the count `|𝕋[T_{ρ₂*}]| ≤ K Ccnt ρ₂^{2+ζ}|𝕋|` of
`Kakeya.VeryNotSticky.nonslabFibreCount` to the `β`-th power costs `(K Ccnt)^β`, and
`(K Ccnt)^β ≤ (δ^{-Mη})^β = δ^{-Mηβ} ≤ δ^{-Mη}` by `hCδ` together with `β ≤ 1`, `0 ≤ M` and
`δ ≤ 1`; this is the only use of `β ≤ 1` in the non-slab chain. `K` is the constant of the
fibre count, `Cu²` for the hierarchy constant `Cu` of `Tube.UniformTubeSet`, and `Ccnt` is the constant of the count clause, a parameter.

`M` is likewise a parameter, not a numeral: the numeral is fixed at each call site, `M = 19` at
`Kakeya.VeryNotSticky.nonslabSplitBound` (`19 = 1` for the hierarchy constant `Cu²` inside
`Kakeya.VeryNotSticky.SplitInputs.fibreConstant` plus `18` for
`Kakeya.VeryNotSticky.SplitInputs.countConstant`) and `M = 1` at `Kakeya.KKTResidual.nonslabKKTPow_of_fibreKTData`.

That absorption is the hypothesis `hCδ`, blueprint `fibreConstantThreshold`. It is a genuine
extra assumption, not a consequence of the others — `δ = 1` falsifies the statement without
it — and it is a fixed-scale threshold of the same kind as the four fields of
`Kakeya.VeryNotSticky.CaseScale` without being one of them: it does not follow from
`rho2Star_le_one` together with `2η < exscal`, which bounds
`2 C_{lem:ml2bodyAngle}(C₀) δ^{exscal}` and says nothing about `C_{lem:ml2bodyAngle}(C₀)²`
alone. No lower bound on `K Ccnt` is assumed: a separate binder `1 ≤ K Ccnt` is unnecessary because `Kakeya.VeryNotSticky.SplitInputs` carries only the upper bound
`countConstant`, so the powered step is routed through `hCδ` and `0 ≤ M` instead — a strictly
weaker side condition, discharged by `norm_num` at both call sites.

The hypothesis is stated over `ℝ`, as `nonslabFibreCount` produces it, and the conclusion
over `ℝ≥0∞`, as `nonslabKKTPow` consumes it. -/
theorem nonslabFibreCountPow (cfg : VeryNotSticky) (hβ1 : cfg.β ≤ 1)
    {K Ccnt : ℝ≥0} {M : ℝ} (hM : 0 ≤ M)
    (hCδ : (K : ℝ≥0∞) * (Ccnt : ℝ≥0∞) ≤ (cfg.δ : ℝ≥0∞) ^ (-(M * cfg.η)))
    {sub : Finset cfg.ι}
    (hcard : (sub.card : ℝ) ≤ (K : ℝ) * (Ccnt : ℝ) *
      (cfg.rho2 : ℝ) ^ (2 + cfg.ζ) * (cfg.s.card : ℝ)) :
    (sub.card : ℝ≥0∞) ^ cfg.β ≤ (cfg.δ : ℝ≥0∞) ^ (-(M * cfg.η)) *
      ((cfg.rho2 : ℝ≥0∞) ^ (2 + cfg.ζ) * (cfg.s.card : ℝ≥0∞)) ^ cfg.β := by
  let P : ℝ≥0∞ := (cfg.rho2 : ℝ≥0∞) ^ (2 + cfg.ζ) * (cfg.s.card : ℝ≥0∞)
  let KC : ℝ≥0∞ := (K : ℝ≥0∞) * (Ccnt : ℝ≥0∞)
  have hβ0 : 0 ≤ cfg.β := cfg.hβ.le
  have hρζ : 0 ≤ 2 + cfg.ζ := by linarith [cfg.hζ]
  have hδ1e : (cfg.δ : ℝ≥0∞) ≤ 1 := by exact_mod_cast cfg.hδ1
  -- transport `hcard` to `ENNReal`
  have hcardN : (sub.card : ℝ≥0) ≤
      K * Ccnt * (cfg.rho2 ^ (2 + cfg.ζ) : ℝ≥0) * (cfg.s.card : ℝ≥0) := by
    exact_mod_cast hcard
  have hcardE : (sub.card : ℝ≥0∞) ≤ (K : ℝ≥0∞) * (Ccnt : ℝ≥0∞) *
      (cfg.rho2 : ℝ≥0∞) ^ (2 + cfg.ζ) * (cfg.s.card : ℝ≥0∞) := by
    have h := ENNReal.coe_le_coe.mpr hcardN
    simpa [ENNReal.coe_rpow_of_nonneg cfg.rho2 hρζ] using h
  -- `(K Ccnt)^β ≤ (δ^{-Mη})^β = δ^{-Mηβ} ≤ δ^{-Mη}`
  have hKCδ : KC ^ cfg.β ≤ (cfg.δ : ℝ≥0∞) ^ (-(M * cfg.η)) := by
    have hstep : KC ^ cfg.β ≤ ((cfg.δ : ℝ≥0∞) ^ (-(M * cfg.η))) ^ cfg.β :=
      ENNReal.rpow_le_rpow (by simpa [KC] using hCδ) hβ0
    have hmulr : ((cfg.δ : ℝ≥0∞) ^ (-(M * cfg.η))) ^ cfg.β =
        (cfg.δ : ℝ≥0∞) ^ (-(M * cfg.η) * cfg.β) := by
      rw [← ENNReal.rpow_mul]
    have hmono : (cfg.δ : ℝ≥0∞) ^ (-(M * cfg.η) * cfg.β) ≤
        (cfg.δ : ℝ≥0∞) ^ (-(M * cfg.η)) := by
      apply ENNReal.rpow_le_rpow_of_exponent_ge hδ1e
      nlinarith [mul_nonneg (mul_nonneg hM cfg.hη.le) (sub_nonneg.mpr hβ1)]
    exact hstep.trans (by rw [hmulr]; exact hmono)
  have hbound : KC * P = (K : ℝ≥0∞) * (Ccnt : ℝ≥0∞) * (cfg.rho2 : ℝ≥0∞) ^ (2 + cfg.ζ)
      * (cfg.s.card : ℝ≥0∞) := by
    simp [KC, P, mul_assoc]
  calc
    (sub.card : ℝ≥0∞) ^ cfg.β ≤
        ((K : ℝ≥0∞) * (Ccnt : ℝ≥0∞) * (cfg.rho2 : ℝ≥0∞) ^ (2 + cfg.ζ) *
            (cfg.s.card : ℝ≥0∞)) ^ cfg.β :=
        ENNReal.rpow_le_rpow hcardE hβ0
    _ = (KC * P) ^ cfg.β := by
        rw [← hbound]
    _ = KC ^ cfg.β * P ^ cfg.β := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hβ0]
    _ ≤ (cfg.δ : ℝ≥0∞) ^ (-(M * cfg.η)) * P ^ cfg.β := by
        have hm : P ^ cfg.β * KC ^ cfg.β ≤
            P ^ cfg.β * (cfg.δ : ℝ≥0∞) ^ (-(M * cfg.η)) :=
          mul_le_mul_right hKCδ (P ^ cfg.β)
        convert hm using 1 <;> ac_rfl


open scoped Classical in
/-- **The fibre count at the hierarchy constant is a theorem of `uniform`** (GWZ Def 2.1(iii),
GWZ: "`|𝕋[T_ρ]|` is constant up to a factor `∼ 1`").

At every node `j` of the level `k`, `|𝕋_{ρ}| · |𝕋[T_ρ]| ≤ Cu² |𝕋|`: the assignment classes
partition `𝕋` (`Tube.GridCoverSystem.assign_mem`, `Finset.card_eq_sum_card_fiberwise`), each
has at least `N_k / Cu` members (`Tube.UniformTubeSet.le_card_class`), so
`|𝕋_ρ| · N_k ≤ Cu |𝕋|`, and the class of `j` has at most `Cu · N_k` members
(`Tube.UniformTubeSet.card_class_le`). This is the clause the field
`Kakeya.VeryNotSticky.SplitInputs.fibreCount` carries, and what a producer of that structure
populates it with. -/
theorem card_indexSet_mul_card_tubeFibre_le (cfg : VeryNotSticky) {N : ℕ} {Cu : ℝ≥0}
    (uniform : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) N Cu) (k : ℕ)
    (hk : k ≤ N) :
    ∀ j ∈ uniform.cover.indexSet k,
      ((uniform.cover.indexSet k).card : ℝ) * ((cfg.tubeFibre uniform k j).card : ℝ) ≤
        ((Cu : ℝ) ^ 2) * (cfg.s.card : ℝ) := by
  intro j hj
  have hpart : (cfg.s.card : ℝ) =
      ∑ j' ∈ uniform.cover.indexSet k, ((cfg.tubeFibre uniform k j').card : ℝ) := by
    have h := Finset.card_eq_sum_card_fiberwise (s := cfg.s) (t := uniform.cover.indexSet k)
      (f := uniform.cover.assign k) (fun i hi => uniform.cover.assign_mem k hk i hi)
    rw [h]
    push_cast
    refine Finset.sum_congr rfl fun j' _ => ?_
    congr 2
  have hup : ((cfg.tubeFibre uniform k j).card : ℝ) ≤ (Cu : ℝ) * (uniform.branchingN k : ℝ) := by
    have h := uniform.card_class_le k hk j hj
    exact_mod_cast h
  have hlo : ∀ j' ∈ uniform.cover.indexSet k,
      (uniform.branchingN k : ℝ) ≤ (Cu : ℝ) * ((cfg.tubeFibre uniform k j').card : ℝ) := by
    intro j' hj'
    have h := uniform.le_card_class k hk j' hj'
    exact_mod_cast h
  have hsum : ((uniform.cover.indexSet k).card : ℝ) * (uniform.branchingN k : ℝ) ≤
      (Cu : ℝ) * (cfg.s.card : ℝ) := by
    rw [hpart, Finset.mul_sum]
    have := Finset.sum_le_sum hlo
    simpa [Finset.sum_const, nsmul_eq_mul] using this
  have hCu : (0 : ℝ) ≤ (Cu : ℝ) := NNReal.coe_nonneg _
  have hidx : (0 : ℝ) ≤ ((uniform.cover.indexSet k).card : ℝ) := Nat.cast_nonneg _
  calc ((uniform.cover.indexSet k).card : ℝ) * ((cfg.tubeFibre uniform k j).card : ℝ)
      ≤ ((uniform.cover.indexSet k).card : ℝ) * ((Cu : ℝ) * (uniform.branchingN k : ℝ)) :=
        mul_le_mul_of_nonneg_left hup hidx
    _ = (Cu : ℝ) * (((uniform.cover.indexSet k).card : ℝ) * (uniform.branchingN k : ℝ)) := by
        ring
    _ ≤ (Cu : ℝ) * ((Cu : ℝ) * (cfg.s.card : ℝ)) := mul_le_mul_of_nonneg_left hsum hCu
    _ = (Cu : ℝ) ^ 2 * (cfg.s.card : ℝ) := by ring


end Kakeya.VeryNotSticky

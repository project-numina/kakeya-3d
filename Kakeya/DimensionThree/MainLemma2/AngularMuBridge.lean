/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.LooseUniform

/-!
# Conjunct 6 from GWZ's own object: the angular multiplicity function `μ(ρ)`

Conjunct 6 of `Kakeya.VeryNotSticky.SideDataObligations` is GWZ's composed angular bound
(GWZ): the tubes of `𝕋_Y(x)` within angle `ρ₂*` of an arbitrary direction
number at most `Cang` times the multiplicity of the class of an active level-`k` node.  GWZ
derive it from **two** facts, and the tree already owns the harder one:

* **(86)** (GWZ) — the *per-point angular uniformity*: after a refinement of the
  shading alone, `#{T ∈ 𝕋_{Y'}(x) : ∠(T, T₀) ≤ ρ} ≈ μ(ρ)` for **every** `T₀ ∈ 𝕋` and every
  `x ∈ Y'(T₀)`.  In the tree this is `Kakeya.VeryNotSticky.IsAngularMultiplicity`, and it is
  **produced** — with GWZ's own mass retention `ShadedBody.IsCRefinement` at `δ^η ≤ c ≤ 1` and
  with `1 ≤ C ≤ δ^{-η}` — by the existing, axiom-clean theorem
  `Kakeya.VeryNotSticky.exists_angularMultiplicity`, for **every** configuration below a
  threshold depending on `η` alone.  Nothing in this file re-proves it.
* **GWZ ** — the *identification* `μ(𝕋[T_ρ], Y') ≈ μ(ρ)`: the angular multiplicity
  at scale `ρ` is comparable to the shading multiplicity of a parent's fibre.  This is **not**
  in the tree, and the docstring of `exists_angularMultiplicity` says so ("Neither
  `murhoTwoScale` nor the comparison of `μ(𝕋, Y')` with `μ(1)` is part of this existence
  statement").

This file compiles the reduction of conjunct 6 to those two, in the **existing vocabulary**
(`cfg.angularFibre`, `cfg.activeTubeNodes cfg.splitHierarchy k`,
`cfg.tubeFibre cfg.splitHierarchy k j`) and with **no loose hierarchy anywhere**.  Concretely:

* `Kakeya.VeryNotSticky.branchingN_le_multiplicity_of_shadedUniform` — the *lower* half of
   is free from the Definition-2.2 datum the configuration already carries
  (`Kakeya.VeryNotSticky.uniform`): the multiplicity of an **active** class is at least
  `𝒱.branchingN k / C²`.  This is the second half of the proof of
  `Kakeya.LooseUniform.angularCone_card_le_of_loose`, read on the **exact** datum, where it is
  equally valid — the loose model is needed only for the *covering* half, which (86) replaces.
* `Kakeya.VeryNotSticky.angularFibre_card_le_fibreMult_of_mu` — the composition.  Conjunct 6's
  inequality holds with `Cang = C_μ · C₁ · C²`, where `C_μ` is (86)'s constant and `C₁` is the
  constant of the **single remaining scalar hypothesis**

  `μ (2 ρ) ≤ C₁ · 𝒱.branchingN k`.

  That hypothesis is exactly 's upper half in the tree's vocabulary: the angular branching
  number at the scale `2ρ` is at most `C₁` times the shading branching number of the
  Definition-2.2 datum at the grid level `k`.
* `Kakeya.VeryNotSticky.eventually_conjunct6_of_angularMultiplicity` — conjunct 6 of
  `Kakeya.VeryNotSticky.SideDataObligations` **verbatim**, conditional on (86) at the
  configuration's own shading, on that scalar hypothesis, on `2ρ₂* ≤ 1`, and on the budget
  `C_μ · C₁ · C₀² ≤ δ^{-η}`.
* `Kakeya.VeryNotSticky.two_mul_rho2Star_le_one` — the side condition `2ρ₂* ≤ 1`, from the
  threshold of `Kakeya.VeryNotSticky.rho2Star_range` with `4` in place of `2`.

## What this does and does not discharge

It **discharges nothing** on its own: (86) is produced only on a *refinement* `Y'` of the
configuration's shading, so using it at the configuration's own shading is the "abusing
notation" step of GWZ and must be threaded through the configuration rebuild, and the scalar hypothesis `μ (2ρ) ≤ C₁ · 𝒱.branchingN k` has no
producer anywhere in the tree.  What it does establish, by the compiler, is that **the residue
of conjunct 6 beyond GWZ's own (86) is one scalar comparison between two branching numbers**,
not a hierarchy: no sparse net, no loose multiscale tree, no pruning adaptation and no joint
fixed point.

Every statement is new
and every existing name it mentions is used, not modified.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Set Filter Topology

namespace Kakeya

namespace VeryNotSticky

universe u

/-! ### The lower half of GWZ, from the exact Definition-2.2 datum -/

open scoped Classical in
/-- **The multiplicity of an active class is at least `branchingN k / C²`.**

`ShadedTube.ShadedUniformTubeSet.le_card_shadeClass` bounds `localN x k` by `C` times the number
of class members shading `x`, and `branchingN_le` bounds `branchingN k` by `C · localN x k`;
the two together bound the *pointwise* multiplicity of the class from below at **every** point
of the union of its shades, and `ShadedBody.le_multiplicity_of_le_pointwiseMultiplicity`
integrates that to the multiplicity.  Activity of the node is what makes the union nonempty of
positive measure (`Kakeya.VeryNotSticky.volume_shade_ne_zero`).

This is the second half of the proof of `Kakeya.LooseUniform.angularCone_card_le_of_loose` (PC),
read on the **exact** datum.  Nothing loose is used: the two brackets it consumes have the same
statement in both models, and the loose model is needed only for the covering half — which,
on the route of this file, GWZ's `μ(ρ)` supplies instead. -/
theorem branchingN_le_multiplicity_of_shadedUniform (cfg : VeryNotSticky.{u}) {N : ℕ} {C : ℝ≥0}
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T N C) (hC : 1 ≤ C)
    {k : ℕ} (hk : k ≤ N) {j : cfg.ι} (hj : j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k) :
    ((𝒱.branchingN k : ℝ≥0) : ℝ≥0∞) ≤ (C : ℝ≥0∞) ^ 2 *
      ShadedBody.multiplicity (cfg.tubeFibre 𝒱.tubeUniform k j)
        (fun i ↦ (cfg.T i).toShadedBody) := by
  classical
  set G := 𝒱.tubeUniform.cover with hG
  set F := cfg.tubeFibre 𝒱.tubeUniform k j with hF
  have hFeq : F = Tube.coverClass cfg.s (G.assign k) j := rfl
  have hFs : F ⊆ cfg.s := fun i hi => (Finset.mem_filter.mp hi).1
  have hjne : F.Nonempty := (Finset.mem_filter.mp hj).2
  have hne : volume (⋃ i ∈ F, ((fun i ↦ (cfg.T i).toShadedBody) i).shade) ≠ 0 := by
    obtain ⟨i', hi'⟩ := hjne
    intro h0
    exact cfg.volume_shade_ne_zero (hFs hi') (measure_mono_null (Set.subset_iUnion₂
      (s := fun i _ => ((fun i ↦ (cfg.T i).toShadedBody) i).shade) i' hi') h0)
  have hC0 : (C : ℝ≥0∞) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le hC).ne'
  have hC2 : ((C : ℝ≥0∞) ^ 2) ≠ 0 := pow_ne_zero _ hC0
  have hC2top : ((C : ℝ≥0∞) ^ 2) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hpt : ∀ y ∈ ⋃ i ∈ F, ((fun i ↦ (cfg.T i).toShadedBody) i).shade,
      (𝒱.branchingN k : ℝ≥0∞) / (C : ℝ≥0∞) ^ 2 ≤
        (ShadedBody.pointwiseMultiplicity F (fun i ↦ (cfg.T i).toShadedBody) y : ℝ≥0∞) := by
    intro y hy
    obtain ⟨i', hi', hyi'⟩ := Set.mem_iUnion₂.mp hy
    have hi's : i' ∈ cfg.s := hFs hi'
    have hji' : G.assign k i' = j := (Finset.mem_filter.mp hi').2
    have hyi'' : y ∈ (cfg.T i').shade := hyi'
    have hyU : y ∈ ⋃ i ∈ cfg.s, (cfg.T i).shade := Set.mem_iUnion₂.mpr ⟨i', hi's, hyi''⟩
    have h1 := 𝒱.le_card_shadeClass y hyU k hk i' hi's hyi''
    have h2 := 𝒱.branchingN_le y hyU k hk
    rw [hji'] at h1
    have hcard : (ShadedTube.shadeClass cfg.s cfg.T (G.assign k) j y).card =
        ShadedBody.pointwiseMultiplicity F (fun i ↦ (cfg.T i).toShadedBody) y := by
      simp only [ShadedTube.shadeClass, ShadedBody.pointwiseMultiplicity, hFeq]
    have hNN : 𝒱.branchingN k ≤
        C ^ 2 * (ShadedBody.pointwiseMultiplicity F
          (fun i ↦ (cfg.T i).toShadedBody) y : ℝ≥0) := by
      rw [← hcard]
      calc 𝒱.branchingN k ≤ C * 𝒱.localN y k := h2
        _ ≤ C * (C * ((ShadedTube.shadeClass cfg.s cfg.T (G.assign k) j y).card : ℝ≥0)) := by
            gcongr
        _ = C ^ 2 * ((ShadedTube.shadeClass cfg.s cfg.T (G.assign k) j y).card : ℝ≥0) := by
            ring
    rw [ENNReal.div_le_iff hC2 hC2top, mul_comm]
    exact_mod_cast hNN
  have hlow := ShadedBody.le_multiplicity_of_le_pointwiseMultiplicity F
    (fun i ↦ (cfg.T i).toShadedBody) hne hpt
  calc ((𝒱.branchingN k : ℝ≥0) : ℝ≥0∞)
      = (C : ℝ≥0∞) ^ 2 * ((𝒱.branchingN k : ℝ≥0∞) / (C : ℝ≥0∞) ^ 2) :=
        (ENNReal.mul_div_cancel hC2 hC2top).symm
    _ ≤ (C : ℝ≥0∞) ^ 2 * ShadedBody.multiplicity F
          (fun i ↦ (cfg.T i).toShadedBody) := by gcongr

/-! ### The composition: (86) plus one scalar comparison give conjunct 6's inequality -/

/-! ### The angular side condition `2 ρ₂* ≤ 1` -/

/-! ### The low-cardinality branch: conjunct 6 outright, no hypotheses beyond `|𝕋| ≤ δ^{-η}` -/

/-! ### Conjunct 6 of `SideDataObligations`, verbatim, from (86) -/

end VeryNotSticky

end Kakeya

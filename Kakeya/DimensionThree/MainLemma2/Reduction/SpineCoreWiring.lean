/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineMiddleFactor
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCoarseSeam

/-!
# The branch-(ii) wiring: from the window package to the mass gain

This file is composition only.  It carries the window branch of
`Kakeya.ML2Core.exists_dichotomyLeft_or_window_dim3` down to the node-restricted family on which
`Kakeya.ML2Core.mass_gain_of_three_factors` acts, and back up to the original family `(𝕋, Y)`,
which is the shape `Kakeya.ML2Assembly.Dichotomy`'s right disjunct states.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody
open Tube ShadedTube

namespace Kakeya.ML2Core

universe u w

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

section EpsOneShrink

end EpsOneShrink

section Pushback

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E] [ProperSpace E]
  {ι : Type*}

/-- **The pushback of branch (ii), in one inequality.**

The window branch produces its gain on the *node-restricted* family `s₁ ⊆ u' ⊆ s`, and
`Kakeya.ML2Assembly.Dichotomy` asks for it on `s`.  Two discards separate them, and both are paid
by the same pointwise density invariant:

* `s ⇝ u'` is the dividing-scales package's own mass loss `hmassloss`;
* `u' ⇝ s₁` is the parent seam's cardinality discard, converted to mass by
  `Kakeya.ML2Core.sum_shade_le_of_node_subfamily`.

The union moves the helpful way for free, so no third loss appears.  Everything is multiplied
out: `lam * c₃` is cancelled once at the end by `ENNReal.mul_le_mul_iff_left`, never divided by,
so no `≠ 0`/`≠ ⊤` side condition escapes into the caller beyond the two on `lam` itself. -/
theorem sum_shade_le_of_node_gain {δ : ℝ≥0} (hδ1 : δ ≤ 1) {s u s₁ : Finset ι}
    (hus : u ⊆ s) (hs₁ : s₁ ⊆ u) {V : ι → ShadedTube δ E} {lam Kc : ℝ≥0}
    (hlam0 : 0 < lam)
    (hdense : ML2Shaded.HasDenseShading lam u (fun i ↦ (V i).toShadedBody))
    (hcard : (u.card : ℝ≥0) ≤ Kc * (s₁.card : ℝ≥0))
    {A G Λ : ℝ≥0∞}
    (hmassloss : (lam : ℝ≥0∞) * (Tube.le_volume.c (Module.finrank ℝ E) : ℝ≥0∞)
        * (∑ i ∈ s, volume (V i).shade)
      ≤ A * ∑ i ∈ u, volume (V i).shade)
    (hgain : ∑ i ∈ s₁, volume (V i).shade ≤ G * volume (⋃ i ∈ s₁, (V i).shade))
    (habs : A * ((Kc : ℝ≥0∞) * (Tube.volume_le.C (Module.finrank ℝ E) : ℝ≥0∞)) * G
      ≤ ((lam : ℝ≥0∞) * (Tube.le_volume.c (Module.finrank ℝ E) : ℝ≥0∞))
          * ((lam : ℝ≥0∞) * (Tube.le_volume.c (Module.finrank ℝ E) : ℝ≥0∞)) * Λ) :
    ∑ i ∈ s, volume (V i).shade ≤ Λ * volume (⋃ i ∈ s, (V i).shade) := by
  classical
  set c : ℝ≥0∞ := (Tube.le_volume.c (Module.finrank ℝ E) : ℝ≥0∞) with hc
  set C : ℝ≥0∞ := (Tube.volume_le.C (Module.finrank ℝ E) : ℝ≥0∞) with hC
  have hc0 : c ≠ 0 := by
    simpa [hc] using (Tube.le_volume.c_pos (Module.finrank ℝ E)).ne'
  have hctop : c ≠ (⊤ : ℝ≥0∞) := by simp [hc]
  have hlamE0 : ((lam : ℝ≥0) : ℝ≥0∞) ≠ 0 := by simpa using hlam0.ne'
  have hlamEtop : ((lam : ℝ≥0) : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := ENNReal.coe_ne_top
  have hK0 : (lam : ℝ≥0∞) * c ≠ 0 := mul_ne_zero hlamE0 hc0
  have hKtop : (lam : ℝ≥0∞) * c ≠ (⊤ : ℝ≥0∞) := ENNReal.mul_ne_top hlamEtop hctop
  -- the seam's discard, as a mass retention
  have hseam : (lam : ℝ≥0∞) * c * ∑ i ∈ u, volume (V i).shade
      ≤ (Kc : ℝ≥0∞) * C * ∑ i ∈ s₁, volume (V i).shade :=
    sum_shade_le_of_node_subfamily hδ1 hs₁ hdense hcard
  -- the union moves the helpful way
  have hunion : volume (⋃ i ∈ s₁, (V i).shade) ≤ volume (⋃ i ∈ s, (V i).shade) := by
    refine measure_mono ?_
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨i, hus (hs₁ hi), hxi⟩
  refine (ENNReal.mul_le_mul_iff_left (mul_ne_zero hK0 hK0)
    (ENNReal.mul_ne_top hKtop hKtop)).mp ?_
  calc (∑ i ∈ s, volume (V i).shade) * ((lam : ℝ≥0∞) * c * ((lam : ℝ≥0∞) * c))
      = (lam : ℝ≥0∞) * c * ((lam : ℝ≥0∞) * c * ∑ i ∈ s, volume (V i).shade) := by ring
    _ ≤ (lam : ℝ≥0∞) * c * (A * ∑ i ∈ u, volume (V i).shade) := by gcongr
    _ = A * ((lam : ℝ≥0∞) * c * ∑ i ∈ u, volume (V i).shade) := by ring
    _ ≤ A * ((Kc : ℝ≥0∞) * C * ∑ i ∈ s₁, volume (V i).shade) := by gcongr
    _ ≤ A * ((Kc : ℝ≥0∞) * C * (G * volume (⋃ i ∈ s₁, (V i).shade))) := by gcongr
    _ ≤ A * ((Kc : ℝ≥0∞) * C * (G * volume (⋃ i ∈ s, (V i).shade))) := by gcongr
    _ = (A * ((Kc : ℝ≥0∞) * C) * G) * volume (⋃ i ∈ s, (V i).shade) := by ring
    _ ≤ (((lam : ℝ≥0∞) * c) * ((lam : ℝ≥0∞) * c) * Λ)
          * volume (⋃ i ∈ s, (V i).shade) := by gcongr
    _ = (Λ * volume (⋃ i ∈ s, (V i).shade))
          * ((lam : ℝ≥0∞) * c * ((lam : ℝ≥0∞) * c)) := by ring

end Pushback

section ActiveCount

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  {ι : Type*} {δ : ℝ≥0} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {σ : ℕ → ℝ≥0}

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
open Classical in
/-- **An active node carries a leaf, and distinct active nodes carry distinct leaves.**

So the level-`k` node count never exceeds the leaf count.  This is the crude ceiling the
subpolynomial absorption of `Kakeya.ML2Reduction.spineScaleLoss` needs at the *node* scale, and it
is the only cardinality fact about `Kakeya.ML2Reduction.activeNodes` the wiring uses. -/
theorem card_activeNodes_le_card (𝒞 : Tube.ChainCoverSystem s T N σ) (k : ℕ) :
    (ML2Reduction.activeNodes 𝒞 k).card ≤ s.card := by
  classical
  have hsub : ML2Reduction.activeNodes 𝒞 k ⊆ s.image (𝒞.assign k) := by
    intro j hj
    obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hj).2
    simp only [Tube.coverClass, Finset.mem_filter] at hi
    exact Finset.mem_image.mpr ⟨i, hi.1, hi.2⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

end ActiveCount

section Split

variable {ι : Type u}

open Classical in
/-- **The three factors, the seam's discard and the package's mass loss, in one inequality.**

`Kakeya.ML2Core.mass_gain_of_three_factors` lands the gain on the *node-restricted* family
`{i ∈ u | assign b i ∈ t₁}`; `Kakeya.ML2Core.sum_shade_le_of_node_gain` carries it back to the
original family `s`, which is the side `Kakeya.ML2Assembly.Dichotomy` states it on.  Nothing here
is geometric: it is the two existing rows composed, with the loss ledger written out once. -/
theorem sum_shade_gain_of_split
    {β : ℝ} (hβ0 : 0 ≤ β) {δ : ℝ≥0} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {Cu Kc lam : ℝ≥0} (hlam0 : 0 < lam)
    {s u : Finset ι} {V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} (hus : u ⊆ s)
    (hdense : ML2Shaded.HasDenseShading lam u (fun i ↦ (V i).toShadedBody))
    {Nn : ℕ} {σ : ℕ → ℝ≥0}
    (𝒰 : Tube.ChainUniformTubeSet u (fun i ↦ (V i).toTube) Nn σ Cu)
    {a b : ℕ} (hab : a ≤ b) (haN : a ≤ Nn) (hbN : b ≤ Nn)
    {t₁ tτ' tθ' : Finset ι} (ht₁ : t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover b)
    (htτ : tτ' ⊆ t₁) (htθ : tθ' ⊆ 𝒰.cover.indexSet a)
    {jτ jθ : ι} (hjτ : jτ ∈ t₁)
    {Yτ' : ι → ShadedTube (σ b) (EuclideanSpace ℝ (Fin 3))}
    {Yθ : ι → ShadedTube (σ a) (EuclideanSpace ℝ (Fin 3))}
    {Y' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    {L A : ℝ≥0∞} {εf gm εc κ g gt : ℝ}
    (hprod : ShadedBody.multiplicity ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
          (fun i ↦ (V i).toShadedBody)
        ≤ L
          * ShadedBody.multiplicity
              ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
                𝒰.cover.assign b i = jτ} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
          * ShadedBody.multiplicity
              ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover a b j = jθ} : Finset ι)
              (fun j ↦ (Yτ' j).toShadedBody)
          * ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody))
    (hfine : ShadedBody.multiplicity
          ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
            𝒰.cover.assign b i = jτ} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
        ≤ (δ : ℝ≥0∞) ^ (-εf)
          * ((({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
                𝒰.cover.assign b i = jτ} : Finset ι)).card : ℝ≥0∞) ^ β)
    (hmid : ShadedBody.multiplicity
          ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover a b j = jθ} : Finset ι)
          (fun j ↦ (Yτ' j).toShadedBody)
        ≤ (δ : ℝ≥0∞) ^ gm
          * ((({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover a b j = jθ}
                : Finset ι)).card : ℝ≥0∞) ^ β)
    (hcoarse : ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody)
        ≤ (δ : ℝ≥0∞) ^ (-εc) * ((tθ'.card : ℕ) : ℝ≥0∞) ^ β)
    (hL : L * (((Cu ^ 5 : ℝ≥0) : ℝ≥0∞)) ^ β ≤ (δ : ℝ≥0∞) ^ (-κ))
    (hexp : g ≤ gm - εf - εc - κ)
    (hmassloss : (lam : ℝ≥0∞)
          * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞)
          * (∑ i ∈ s, volume (V i).shade)
        ≤ A * ∑ i ∈ u, volume (V i).shade)
    (hcardseam : (u.card : ℝ≥0)
      ≤ Kc * ((({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)).card : ℝ≥0))
    (habs : A * ((Kc : ℝ≥0∞)
          * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞))
          * (δ : ℝ≥0∞) ^ g
        ≤ ((lam : ℝ≥0∞)
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞))
          * ((lam : ℝ≥0∞)
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞))
          * (δ : ℝ≥0∞) ^ gt) :
    ∑ i ∈ s, volume (V i).shade
      ≤ (δ : ℝ≥0∞) ^ gt * (s.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ s, (V i).shade) := by
  classical
  have hδE0 : (δ : ℝ≥0∞) ≠ 0 := by simpa using hδ0.ne'
  have hδE1 : (δ : ℝ≥0∞) ≤ 1 := by exact_mod_cast hδ1
  have hgain := mass_gain_of_three_factors (V := V) 𝒰 hab haN hbN ht₁ (htτ.trans ht₁) htθ
    (jθ := jθ) hjτ (Yτ' := Yτ') (Yθ := Yθ) (Y' := Y') hδE0 hδE1 hβ0 hprod hfine hmid hcoarse
    hL hexp
  have hcardβ : ((u.card : ℕ) : ℝ≥0∞) ^ β ≤ ((s.card : ℕ) : ℝ≥0∞) ^ β := by
    have : ((u.card : ℕ) : ℝ≥0∞) ≤ ((s.card : ℕ) : ℝ≥0∞) := by
      exact_mod_cast Finset.card_le_card hus
    exact ENNReal.rpow_le_rpow this hβ0
  refine sum_shade_le_of_node_gain hδ1 hus (Finset.filter_subset _ _) hlam0 hdense hcardseam
    hmassloss hgain ?_
  calc A * ((Kc : ℝ≥0∞)
          * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞))
        * ((δ : ℝ≥0∞) ^ g * ((u.card : ℕ) : ℝ≥0∞) ^ β)
      = (A * ((Kc : ℝ≥0∞)
          * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞))
          * (δ : ℝ≥0∞) ^ g) * ((u.card : ℕ) : ℝ≥0∞) ^ β := by ring
    _ ≤ (((lam : ℝ≥0∞)
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞))
          * ((lam : ℝ≥0∞)
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞))
          * (δ : ℝ≥0∞) ^ gt) * ((s.card : ℕ) : ℝ≥0∞) ^ β := by gcongr
    _ = ((lam : ℝ≥0∞)
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞))
          * ((lam : ℝ≥0∞)
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞))
          * ((δ : ℝ≥0∞) ^ gt * ((s.card : ℕ) : ℝ≥0∞) ^ β) := by ring

end Split

section Window

variable {ι : Type u}

open Classical in
/-- **The branch-(ii) wiring at one scale: from the split's three factors to the mass gain.**

The two-scale split of the estimate and the three factors enter together as one existential package
`hfac` — together, because the three factors are statements *about the objects the split
produces*, and quantifying over all objects that merely satisfy the split's output clauses would
be a strictly stronger demand than GWZ's (a one-node retained set `tτ'` satisfies them and admits
no middle gain).  What this theorem discharges is everything on either side of that package:
cardinality bound and arithmetic below it
(`Kakeya.ML2Core.sum_shade_gain_of_split`), and the two mass discards above it
(`Kakeya.ML2Core.sum_shade_le_of_node_gain`). -/
theorem sum_shade_gain_of_window
    {β : ℝ} (hβ0 : 0 ≤ β) {δ : ℝ≥0} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {Cu Kc lam : ℝ≥0} (hlam0 : 0 < lam)
    {s u : Finset ι} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} (hus : u ⊆ s)
    (hdense : ML2Shaded.HasDenseShading lam u (fun i ↦ (T i).toShadedBody))
    (𝒰 : Tube.UniformTubeSet u (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu)
    {Cstar : ℝ≥0∞} {ηl : ℕ → ℝ} {εd : ℝ} {Nw a b m : ℕ}
    (hwin : ML2Reduction.IsKatzTaoDividingWindow 𝒰 Cstar ηl εd Nw a b m)
    {t₁ : Finset ι} (ht₁ : t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain b)
    (hcardseam : (u.card : ℝ≥0) ≤ Kc * ((({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)).card :
        ℝ≥0))
    (hmasspos : 0 < ∑ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), volume (T i).shade)
    {A : ℝ≥0∞} {εf gm εc κ g gt : ℝ}
    (hcardu : (u.card : ℝ≥0) ≤ δ ^ (-(4 : ℝ)))
    (hfac : ∃ (tτ' tθ' : Finset ι)
        (Yτ' : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b) (EuclideanSpace ℝ (Fin 3)))
        (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a) (EuclideanSpace ℝ (Fin 3)))
        (Y' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (jτ jθ : ι),
        tτ' ⊆ t₁ ∧ tθ' ⊆ 𝒰.cover.indexSet a ∧ jτ ∈ t₁ ∧ jθ ∈ tθ' ∧ tτ'.Nonempty ∧
        ShadedBody.multiplicity ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) (fun i ↦ (T
            i).toShadedBody)
            ≤ ((ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) ({i ∈ u
                | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ *
                  ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) tτ'.card
                    (Tube.gridScale δ (Tube.ssfGridLen δ) b) : ℝ≥0) : ℝ≥0∞)
              * ShadedBody.multiplicity ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
                  𝒰.cover.assign b i = jτ} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
              * ShadedBody.multiplicity ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j
                  = jθ} : Finset ι) (fun j ↦ (Yτ' j).toShadedBody)
              * ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody) ∧
        ShadedBody.multiplicity ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
            𝒰.cover.assign b i = jτ} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
            ≤ (δ : ℝ≥0∞) ^ (-εf) * ((({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
                𝒰.cover.assign b i = jτ} : Finset ι)).card : ℝ≥0∞) ^ β ∧
        ShadedBody.multiplicity ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} :
            Finset ι) (fun j ↦ (Yτ' j).toShadedBody)
            ≤ (δ : ℝ≥0∞) ^ gm * ((({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j =
                jθ} : Finset ι)).card : ℝ≥0∞) ^ β ∧
        ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody)
            ≤ (δ : ℝ≥0∞) ^ (-εc) * ((tθ'.card : ℕ) : ℝ≥0∞) ^ β)
    (hL : ∀ n₁ n₂ : ℕ, 0 < n₁ → 0 < n₂ →
      (n₁ : ℝ≥0) ≤ δ ^ (-(4 : ℝ)) → (n₂ : ℝ≥0) ≤ δ ^ (-(4 : ℝ)) →
      ((ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) n₁ δ *
          ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) n₂
            (Tube.gridScale δ (Tube.ssfGridLen δ) b) : ℝ≥0) : ℝ≥0∞)
        * (((Cu ^ 5 : ℝ≥0) : ℝ≥0∞)) ^ β ≤ (δ : ℝ≥0∞) ^ (-κ))
    (hexp : g ≤ gm - εf - εc - κ)
    (hmassloss : (lam : ℝ≥0∞) * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
        : ℝ≥0∞)
          * (∑ i ∈ s, volume (T i).shade)
        ≤ A * ∑ i ∈ u, volume (T i).shade)
    (habs : A * ((Kc : ℝ≥0∞) * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
        : ℝ≥0∞)) * (δ : ℝ≥0∞) ^ g
        ≤ ((lam : ℝ≥0∞) * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) :
            ℝ≥0∞))
          * ((lam : ℝ≥0∞) * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) :
              ℝ≥0∞)) * (δ : ℝ≥0∞) ^ gt) :
    ∑ i ∈ s, volume (T i).shade
      ≤ (δ : ℝ≥0∞) ^ gt * (s.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ s, (T i).shade) := by
  classical
  have hab : a ≤ b := hwin.coarse_lt_fine.le
  have hbN : b ≤ Tube.ssfGridLen δ := hwin.fine_le_gridLen
  have haN : a ≤ Tube.ssfGridLen δ := hab.trans hbN
  obtain ⟨tτ', tθ', Yτ', Yθ, Y', jτ, jθ, htτ', htθ', hjτ, hjθ, hτne, hprod, hfine, hmid,
    hcoarse⟩ := hfac
  have hs₁ne : (({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)).Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    rw [hcon] at hmasspos
    simp at hmasspos
  have hs₁pos : 0 < (({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)).card := Finset.card_pos.mpr
      hs₁ne
  have hτpos : 0 < tτ'.card := Finset.card_pos.mpr hτne
  have hs₁card : (((({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)).card : ℕ) : ℝ≥0) ≤ δ ^ (-(4
      : ℝ)) := by
    refine le_trans ?_ hcardu
    exact_mod_cast Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))
  have hτcard : ((tτ'.card : ℕ) : ℝ≥0) ≤ δ ^ (-(4 : ℝ)) := by
    refine le_trans ?_ hcardu
    have h1 : tτ'.card ≤ (ML2Reduction.activeNodes 𝒰.cover.toChain b).card :=
      Finset.card_le_card (htτ'.trans ht₁)
    have h2 := card_activeNodes_le_card (E := (EuclideanSpace ℝ (Fin 3))) 𝒰.cover.toChain b
    exact_mod_cast Nat.cast_le.mpr (h1.trans h2)
  exact sum_shade_gain_of_split hβ0 hδ0 hδ1 hlam0 hus hdense 𝒰.toChain hab haN hbN ht₁ htτ'
    htθ' (jθ := jθ) hjτ hprod hfine hmid hcoarse
    (hL _ _ hs₁pos hτpos hs₁card hτcard) hexp hmassloss hcardseam habs

end Window

section LossAbsorption

/-- **The two-scale loss of the estimate, absorbed into one `δ`-power.**

`Kakeya.ML2Reduction.spineScaleLoss` is `ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C`
at dilation `1`, which is subpolynomial jointly in the inner cardinality and the inner scale
(`C_leApprox`).  The two applications the two-scale split makes live at the *leaf* scale `δ` and at
the *node* scale `σ ≥ δ`, and both cardinalities are below the crude ceiling `δ^{-4}`, so the whole
product is `δ^{-10 ε}` for the `ε` the approximation is read at. -/
theorem spineScaleLoss_prod_le {n : ℕ} {δ σ : ℝ≥0} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hδσ : δ ≤ σ) (hσ1 : σ ≤ 1) {n₁ n₂ : ℕ} (h1 : 0 < n₁) (h2 : 0 < n₂)
    (hn1 : (n₁ : ℝ≥0) ≤ δ ^ (-(4 : ℝ))) (hn2 : (n₂ : ℝ≥0) ≤ δ ^ (-(4 : ℝ)))
    {ε : ℝ} (hε : 0 < ε) {Cε : ℝ≥0}
    (hCε : ∀ N : ℕ, 0 < N → ∀ d : ℝ≥0, 0 < d → d ≤ 1 → ∀ c : ℝ≥0, 1 ≤ c →
      ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C n N d c
        ≤ Cε * c ^ n * d ^ (-ε) * (N : ℝ≥0) ^ ε) :
    ML2Reduction.spineScaleLoss n n₁ δ * ML2Reduction.spineScaleLoss n n₂ σ
      ≤ Cε ^ 2 * δ ^ (-(10 * ε)) := by
  have hσ0 : 0 < σ := lt_of_lt_of_le hδ0 hδσ
  have e1 : ML2Reduction.spineScaleLoss n n₁ δ ≤ Cε * δ ^ (-ε) * ((n₁ : ℕ) : ℝ≥0) ^ ε := by
    simpa [ML2Reduction.spineScaleLoss] using hCε n₁ h1 δ hδ0 hδ1 1 le_rfl
  have e2 : ML2Reduction.spineScaleLoss n n₂ σ ≤ Cε * σ ^ (-ε) * ((n₂ : ℕ) : ℝ≥0) ^ ε := by
    simpa [ML2Reduction.spineScaleLoss] using hCε n₂ h2 σ hσ0 hσ1 1 le_rfl
  have hpow : ∀ k : ℕ, ((k : ℕ) : ℝ≥0) ≤ δ ^ (-(4 : ℝ)) →
      ((k : ℕ) : ℝ≥0) ^ ε ≤ δ ^ (-(4 * ε)) := by
    intro k hk
    calc ((k : ℕ) : ℝ≥0) ^ ε ≤ (δ ^ (-(4 : ℝ))) ^ ε := NNReal.rpow_le_rpow hk hε.le
      _ = δ ^ (-(4 * ε)) := by rw [← NNReal.rpow_mul]; ring_nf
  have g2 : σ ^ (-ε) ≤ δ ^ (-ε) := by
    have h := ML2Core.rpow_neg_le_rpow_neg_of_le hδσ hε.le
    rwa [← ENNReal.coe_rpow_of_ne_zero hσ0.ne', ← ENNReal.coe_rpow_of_ne_zero hδ0.ne',
      ENNReal.coe_le_coe] at h
  calc ML2Reduction.spineScaleLoss n n₁ δ * ML2Reduction.spineScaleLoss n n₂ σ
      ≤ (Cε * δ ^ (-ε) * δ ^ (-(4 * ε))) * (Cε * δ ^ (-ε) * δ ^ (-(4 * ε))) := by
        refine mul_le_mul' (e1.trans ?_) (e2.trans ?_)
        · exact mul_le_mul' le_rfl (hpow n₁ hn1)
        · exact mul_le_mul' (mul_le_mul' le_rfl g2) (hpow n₂ hn2)
    _ = Cε ^ 2 * (δ ^ (-ε) * δ ^ (-(4 * ε)) * (δ ^ (-ε) * δ ^ (-(4 * ε)))) := by ring
    _ = Cε ^ 2 * δ ^ (-(10 * ε)) := by
        simp only [← NNReal.rpow_add hδ0.ne']
        congr 1
        ring_nf

end LossAbsorption

section Package

end Package

section TopLevel

end TopLevel

section SplitProducer

variable {ι : Type u}

end SplitProducer

section MiddleOnly

end MiddleOnly

end Kakeya.ML2Core

end

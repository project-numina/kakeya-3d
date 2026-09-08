/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factoring.RhoTubesUndilated
public import Kakeya.ShadedUniform

/-! # The Section-9 interface of GWZ Lemma 5.11, at the honest loss constant

Section 9 (`Kakeya/DimensionThree/MainLemma2/*`) states its coarse-family residues against the
placeholder `Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C = 1`
(`Kakeya/DimensionThree/MainLemma2/AScaleConstants.lean`), i.e. against the assertion that the
transfer of GWZ Lemma 5.11 from the fine family `(𝕋, Y)` to a coarse family `(𝕋_ρ, Y_{𝕋_ρ})` is
*lossless*. It is not: the blueprint constant
`def:shadingMultiplicityRhoTubesDilateConstant` is a product of five pigeonholing losses with a
geometric one, and the Lean constant
`ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C` records exactly that product. Only
two facts about it are ever used: `1 ≤ C`, and joint subpolynomiality in `1/δ` and in the
cardinality of the inner family.

This file supplies the honest interface, so that Section-9 statements can be restated against
something true.

## Main definitions

* `ShadedBody.rhoTubesSection9Loss n N δ` — the loss GWZ Lemma 5.11 actually charges at a
  Section-9 call site: `shadingMultiplicityEstimateForRhoTubesDilate.C n N δ 1`, the undilated
  (`c = 1`) constant. It is at least `1`;
* `ShadedBody.rhoTubesInducedFullnessLoss n` — the (purely dimensional) loss of the *fullness*
  clause alone, `max 1 (Kakeya.Tube.dilateFullness.C n)`.

## Main results

* `ShadedBody.rhoTubesSection9Loss_le_rpow_neg` — the currency conversion. For every `η > 0`
  and every polynomial cardinality budget `N ≤ δ^{-K}` there is a threshold below which
  `rhoTubesSection9Loss n N δ ≤ δ^{-η}`. This is what lets a Section-9 statement pay the honest
  loss out of a `δ^{η}` gain, which is the currency the whole layer is written in;
* `ShadedBody.exists_rhoTubesSection9` — GWZ Lemma 5.11 through a parent map, in the vocabulary
  the Section-9 consumer uses (`ShadedFactorFamily`, `ShadedBody.fullness`,
  `ShadedBody.multiplicity`), at the honest constant and with the outer fullness read at the
  inner density parameter `lam`;
* `ShadedBody.exists_rhoTubesSection9_gridScale` — the same at a grid scale
  `Tube.gridScale δ N k`;
* `ShadedBody.exists_rhoTubesSection9_rpow` — the same with the honest constant already
  converted to `δ^{-η}`;
* `ShadedBody.exists_rhoTubesSection9_fullFamily` — the *fullness* clause of Lemma 5.11 on the
  **whole** coarse family, not on a pigeonholed subfamily, with the induced shading and at the
  dimensional constant `rhoTubesInducedFullnessLoss`. This closes, for that clause only, the
  second of the two gaps between Lemma 5.11 and the Section-9 residue
  `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid`.

## What is *not* here, and why

The `boundVolumeAcrossTwoScales` ball estimate is **not** available on the whole coarse family.
Its proof compares the mass of the fine union in a ball centred at the worst point of the coarse
union with its mass in every other ball of a separated net, and those masses are only comparable
after the Step 5 pigeonholing, which discards coarse bodies. On the full family the estimate is
an assertion about the *densest* `ρ`-ball and nothing bounds it. That is why
`exists_rhoTubesSection9` returns a subfamily, exactly as Lemma 5.11 does.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Set Convexity

namespace ShadedBody

section Section9

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι κ : Type*}

/-! ## The honest loss -/

/-- **The loss constant GWZ Lemma 5.11 charges at a Section-9 call site.**

Section 9 applies Lemma 5.11 with an *undilated* coarse family of `ρ`-tubes, i.e. at the
dilation factor `c = 1`, so the constant it charges is
`ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C n N δ 1` — the same constant that
`ShadedBody.shadingMultiplicityEstimateForRhoTubesUndilated` and
`ShadedBody.shadingMultiplicityEstimateForRhoTubesUndilated_lam` are proved at. It is a product
of the Step 0 loss `2`, the chained Step 1 and Step 2 loss, the Step 3 loss, the self-pigeonholed
Step 5 loss and the geometric fullness loss, truncated below at `1`.

It is emphatically **not** the numeral `1`: see
`Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C` in
`Kakeya/DimensionThree/MainLemma2/AScaleConstants.lean` for the placeholder this replaces. -/
noncomputable def rhoTubesSection9Loss (n N : ℕ) (δ : ℝ≥0) : ℝ≥0 :=
  shadingMultiplicityEstimateForRhoTubesDilate.C n N δ 1

/-- The honest Section-9 loss is at least `1`, so its inverse really is a loss. -/
theorem one_le_rhoTubesSection9Loss (n N : ℕ) (δ : ℝ≥0) : 1 ≤ rhoTubesSection9Loss n N δ :=
  shadingMultiplicityEstimateForRhoTubesDilate.one_le_C n N δ 1

theorem rhoTubesSection9Loss_pos (n N : ℕ) (δ : ℝ≥0) : 0 < rhoTubesSection9Loss n N δ :=
  lt_of_lt_of_le zero_lt_one (one_le_rhoTubesSection9Loss n N δ)

/-- **Absorbing a fixed constant into `δ ^ (-η)`.** For an absolute `C ≥ 1` and `η > 0` there is a
threshold below which `C ≤ δ ^ (-η)`; take `δ₀ = C ^ (-1/η)`.

This is a private copy of `Kakeya.exists_threshold_le_rpow_neg`, which lives downstream of this
file. -/
private theorem rpowConstAbsorbNN (C : ℝ≥0) (hC : 1 ≤ C) {η : ℝ} (hη : 0 < η) :
    ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧ ∀ δ : ℝ≥0, 0 < δ → δ ≤ δ₀ → C ≤ δ ^ (-η) := by
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hη_ne : η ≠ 0 := ne_of_gt hη
  refine ⟨C ^ (-1 / η), NNReal.rpow_pos hC0, fun δ hδ hδle => ?_⟩
  have hscalar : (-1 / η) * (-η) = (1 : ℝ) := by field_simp
  have hδ₀_neg : (C ^ (-1 / η)) ^ (-η) = C := by
    rw [← NNReal.rpow_mul, hscalar, NNReal.rpow_one]
  calc
    C = (C ^ (-1 / η)) ^ (-η) := hδ₀_neg.symm
    _ = ((C ^ (-1 / η)) ^ η)⁻¹ := by rw [NNReal.rpow_neg]
    _ ≤ (δ ^ η)⁻¹ :=
        (inv_le_inv₀ (NNReal.rpow_pos (NNReal.rpow_pos hC0)) (NNReal.rpow_pos hδ)).mpr
          (NNReal.rpow_le_rpow hδle hη.le)
    _ = δ ^ (-η) := (NNReal.rpow_neg δ η).symm

/-- **The currency conversion: the honest loss is `δ^{-η}` for small `δ`.**

Every Section-9 statement is written in the currency `δ^{±η}`; the honest loss of Lemma 5.11 is
not a closed term but a function of `δ` and of the inner cardinality `N`. This lemma converts:
for every `η > 0` and every polynomial cardinality budget `N ≤ δ^{-K}`, below an explicit
threshold the whole loss is at most `δ^{-η}`.

It is the honest replacement for the placeholder `= 1`. The placeholder made the loss a *closed*
term (which is what `Kakeya.aScaleDataConstant` was built to exploit); the truth is that the loss
is not closed but is `δ^{-o(1)}`, and is therefore payable out of the `η`-budget the layer
already carries. The input is
`ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C_leApprox`. -/
theorem rhoTubesSection9Loss_le_rpow_neg (n : ℕ) {η K : ℝ} (hη : 0 < η) (hK : 0 ≤ K) :
    ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧
      ∀ δ : ℝ≥0, 0 < δ → δ ≤ δ₀ → δ ≤ 1 → ∀ N : ℕ, 0 < N → (N : ℝ≥0) ≤ δ ^ (-K) →
        rhoTubesSection9Loss n N δ ≤ δ ^ (-η) := by
  set ε : ℝ := η / (2 * (1 + K)) with hεdef
  have hK1 : (0 : ℝ) < 1 + K := by linarith
  have hε : 0 < ε := by rw [hεdef]; positivity
  obtain ⟨Cε, hCε⟩ := shadingMultiplicityEstimateForRhoTubesDilate.C_leApprox n ε hε
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := rpowConstAbsorbNN (max 1 Cε) (le_max_left _ _) (half_pos hη)
  refine ⟨δ₁, hδ₁pos, fun δ hδ hδle hδ1 N hN hNbd => ?_⟩
  have hδ0' : δ ≠ 0 := hδ.ne'
  -- the subpolynomial bound, read at `c = 1`
  have h1 : rhoTubesSection9Loss n N δ ≤ Cε * 1 ^ n * δ ^ (-ε) * (N : ℝ≥0) ^ ε :=
    hCε N hN δ hδ hδ1 1 le_rfl
  -- convert the cardinality factor
  have hNpow : (N : ℝ≥0) ^ ε ≤ δ ^ (-(K * ε)) := by
    calc
      (N : ℝ≥0) ^ ε ≤ (δ ^ (-K)) ^ ε := NNReal.rpow_le_rpow hNbd hε.le
      _ = δ ^ (-(K * ε)) := by rw [← NNReal.rpow_mul]; ring_nf
  have h2 : rhoTubesSection9Loss n N δ ≤ Cε * (δ ^ (-ε) * δ ^ (-(K * ε))) := by
    calc
      rhoTubesSection9Loss n N δ ≤ Cε * 1 ^ n * δ ^ (-ε) * (N : ℝ≥0) ^ ε := h1
      _ = Cε * δ ^ (-ε) * (N : ℝ≥0) ^ ε := by rw [one_pow, mul_one]
      _ ≤ Cε * δ ^ (-ε) * δ ^ (-(K * ε)) := by gcongr
      _ = Cε * (δ ^ (-ε) * δ ^ (-(K * ε))) := by ring
  have harith : -ε + -(K * ε) = -(η / 2) := by
    rw [hεdef]
    field_simp
    ring
  have hsum : δ ^ (-ε) * δ ^ (-(K * ε)) = δ ^ (-(η / 2)) := by
    rw [← NNReal.rpow_add hδ0' (-ε) (-(K * ε)), harith]
  have h3 : Cε ≤ δ ^ (-(η / 2)) :=
    le_trans (le_max_right 1 Cε) (hδ₁ δ hδ hδle)
  calc
    rhoTubesSection9Loss n N δ ≤ Cε * (δ ^ (-ε) * δ ^ (-(K * ε))) := h2
    _ = Cε * δ ^ (-(η / 2)) := by rw [hsum]
    _ ≤ δ ^ (-(η / 2)) * δ ^ (-(η / 2)) := by gcongr
    _ = δ ^ (-η) := by
        rw [← NNReal.rpow_add hδ0' (-(η / 2)) (-(η / 2))]
        congr 1
        ring

/-! ## GWZ Lemma 5.11 in the Section-9 vocabulary, at the honest loss -/

open Classical in
/-- **GWZ Lemma 5.11 through a parent map, at the honest loss constant.**

The Section-9 consumer does not hold a `ShadedBody.FactorFamily`: it holds a finite family of
shaded `δ`-tubes `(T i)_{i ∈ s}`, a finite family of `ρ`-tubes `(W j)_{j ∈ t}` (the nodes of the
hierarchy at a grid index), and the hierarchy's own assignment map `p`. This is Lemma 5.11
packaged for that data, in exactly the shape
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` asks for — outer fullness read at the
inner density parameter `lam`, ball estimate at every shaded centre — but with the honest loss
`ShadedBody.rhoTubesSection9Loss` in place of the placeholder
`Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C = 1`.

Two things are *not* claimed, and both are properties of Lemma 5.11 rather than of this
packaging: the coarse index set is a subset of `t` and not all of it, and the fine index set is
correspondingly cut down to the members whose parent survived. Those are the pigeonholing steps
of the proof.

This is `ShadedBody.shadingMultiplicityEstimateForRhoTubesUndilated_lam` with the factor family
assembled from `p`. -/
theorem exists_rhoTubesSection9
    {δ ρ Cd lam : ℝ≥0} (hδ : 0 < δ) (hρ : ρ ∈ Set.Icc δ 1) (hCd : Cd ≠ 0)
    {s : Finset ι} {t : Finset κ}
    (T : ι → ShadedTube δ E) (W : κ → Tube ρ E) (p : ι → κ)
    (hmaps : ∀ i ∈ s, p i ∈ t)
    (hle : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ (W (p i)).toConvexSpaceBody)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
    (hs0 : ∑ i ∈ s, volume (T i).carrier ≠ 0)
    (hlam : ∀ i ∈ s,
      (Cd : ℝ≥0∞)⁻¹ * ((lam : ℝ≥0∞) * volume (T i).carrier) ≤ volume (T i).shade) :
    ∃ G : ShadedFactorFamily E ι κ,
      G.outerSet ⊆ t ∧
      G.innerSet = {i ∈ s | p i ∈ G.outerSet} ∧
      G.parent = p ∧
      (∀ j ∈ G.outerSet, (G.outerBody j).toConvexSpaceBody = (W j).toConvexSpaceBody) ∧
      (∀ i ∈ s, (G.innerBody i).toConvexSpaceBody = (T i).toConvexSpaceBody) ∧
      (0 < ∑ i ∈ s, volume (T i).shade → G.outerSet.Nonempty) ∧
      -- outer fullness at the inner density parameter, at the honest loss
      (Cd * rhoTubesSection9Loss (Module.finrank ℝ E) s.card δ)⁻¹ * lam
        ≤ fullness G.outerSet G.outerBody ∧
      -- the fine family is a refinement, at the honest loss
      IsCRefinement G.innerSet G.innerBody s (fun i => (T i).toShadedBody)
        (rhoTubesSection9Loss (Module.finrank ℝ E) s.card δ)⁻¹ ∧
      -- `boundMuTTYAcrossTwoScales`, at the honest loss
      (∀ j ∈ G.outerSet,
        multiplicity s (fun i => (T i).toShadedBody)
          ≤ (rhoTubesSection9Loss (Module.finrank ℝ E) s.card δ : ℝ≥0∞)
            * multiplicity G.outerSet G.outerBody
            * multiplicity (G.fiber j) G.innerBody) ∧
      -- `pointwiseContainmenttube`
      (∀ i ∈ G.innerSet, (G.innerBody i).shade ⊆ (G.outerBody (p i)).shade) ∧
      -- `boundVolumeAcrossTwoScales`, at the honest loss
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (rhoTubesSection9Loss (Module.finrank ℝ E) s.card δ : ℝ≥0∞)⁻¹
          * volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade)
          * (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ))
              / volume (ball x (ρ : ℝ)))
          ≤ volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade))
      -- GWZ Definition 5.7, exposed: the outer shading contains the `2ρ`-neighbourhood, inside the
      -- outer carrier, of every selected inner shade of its fibre
      ∧ (∀ j ∈ G.outerSet, ∀ i ∈ G.innerSet, G.parent i = j →
          (G.outerBody j).carrier ∩ Metric.cthickening (2 * (ρ : ℝ)) (G.innerBody i).shade
            ⊆ (G.outerBody j).shade) := by
  classical
  let F : FactorFamily E ι κ :=
    { innerSet := s
      innerBody := fun i => (T i).toShadedBody
      outerSet := t
      outerBody := fun j => (W j).toConvexSpaceBody
      parent := p
      parent_mem := hmaps
      inner_le_parent := hle }
  obtain ⟨G, h1, h2, h3, h4, h5, h6, hfull, href, hmult, hcontain, hvol, hthick⟩ :=
    shadingMultiplicityEstimateForRhoTubesUndilated_lam (E := E) (δ := δ) (ρ := ρ)
      (Cd := Cd) (lam := lam) hδ hρ hCd F T W (fun _ _ => rfl) (fun _ _ => rfl)
      (fun i hi => hball i hi) hs0 hlam
  exact ⟨G, h1, h2, h3, h4, h5, h6, hfull, href, hmult, hcontain, hvol, hthick⟩

open Classical in
/-- **GWZ Lemma 5.11 at a scale of the multiscale grid**, at the honest loss.

`ShadedBody.exists_rhoTubesSection9` read at `ρ = Tube.gridScale δ N k`, which is the only place
Section 9 ever invokes it: `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` is stated at
`Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k`, and the nominal radius is rounded to that grid
by `Kakeya.VeryNotSticky.exists_gridIndex`. The grid membership `hρ` is the range `[δ, 1]` that
Lemma 5.11 needs, and is automatic from `δ ≤ 1`. -/
theorem exists_rhoTubesSection9_gridScale
    {δ Cd lam : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hCd : Cd ≠ 0) {N k : ℕ} (hk : k ≤ N)
    {s : Finset ι} {t : Finset κ}
    (T : ι → ShadedTube δ E) (W : κ → Tube (Tube.gridScale δ N k) E) (p : ι → κ)
    (hmaps : ∀ i ∈ s, p i ∈ t)
    (hle : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ (W (p i)).toConvexSpaceBody)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
    (hs0 : ∑ i ∈ s, volume (T i).carrier ≠ 0)
    (hlam : ∀ i ∈ s,
      (Cd : ℝ≥0∞)⁻¹ * ((lam : ℝ≥0∞) * volume (T i).carrier) ≤ volume (T i).shade) :
    ∃ G : ShadedFactorFamily E ι κ,
      G.outerSet ⊆ t ∧
      G.innerSet = {i ∈ s | p i ∈ G.outerSet} ∧
      G.parent = p ∧
      (∀ j ∈ G.outerSet, (G.outerBody j).toConvexSpaceBody = (W j).toConvexSpaceBody) ∧
      (∀ i ∈ s, (G.innerBody i).toConvexSpaceBody = (T i).toConvexSpaceBody) ∧
      (0 < ∑ i ∈ s, volume (T i).shade → G.outerSet.Nonempty) ∧
      (Cd * rhoTubesSection9Loss (Module.finrank ℝ E) s.card δ)⁻¹ * lam
        ≤ fullness G.outerSet G.outerBody ∧
      IsCRefinement G.innerSet G.innerBody s (fun i => (T i).toShadedBody)
        (rhoTubesSection9Loss (Module.finrank ℝ E) s.card δ)⁻¹ ∧
      (∀ j ∈ G.outerSet,
        multiplicity s (fun i => (T i).toShadedBody)
          ≤ (rhoTubesSection9Loss (Module.finrank ℝ E) s.card δ : ℝ≥0∞)
            * multiplicity G.outerSet G.outerBody
            * multiplicity (G.fiber j) G.innerBody) ∧
      (∀ i ∈ G.innerSet, (G.innerBody i).shade ⊆ (G.outerBody (p i)).shade) ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (rhoTubesSection9Loss (Module.finrank ℝ E) s.card δ : ℝ≥0∞)⁻¹
          * volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade)
          * (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade)
              ∩ ball x ((Tube.gridScale δ N k : ℝ≥0) : ℝ))
              / volume (ball x ((Tube.gridScale δ N k : ℝ≥0) : ℝ)))
          ≤ volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade))
      -- GWZ Definition 5.7, exposed: the outer shading contains the `2ρ`-neighbourhood, inside the
      -- outer carrier, of every selected inner shade of its fibre
      ∧ (∀ j ∈ G.outerSet, ∀ i ∈ G.innerSet, G.parent i = j →
          (G.outerBody j).carrier ∩
              Metric.cthickening (2 * ((Tube.gridScale δ N k : ℝ≥0) : ℝ)) (G.innerBody i).shade
            ⊆ (G.outerBody j).shade) := by
  have hmem : Tube.gridScale δ N k ∈ Set.Icc δ 1 := by
    refine ⟨?_, Tube.gridScale_le_one hδ1 N k⟩
    rcases Nat.eq_zero_or_pos N with hN | hN
    · have hk0 : k = 0 := Nat.le_zero.mp (hN ▸ hk)
      simpa [hk0, Tube.gridScale_zero] using hδ1
    · calc
        δ = Tube.gridScale δ N N := (Tube.gridScale_self δ hN).symm
        _ ≤ Tube.gridScale δ N k := Tube.gridScale_antitone hδ hδ1 N hk
  exact exists_rhoTubesSection9 hδ hmem hCd T W p hmaps hle hball hs0 hlam

/-! ## Paying the honest loss out of the `η`-budget -/

/-! ## The fullness clause on the *whole* coarse family -/

/-- **The loss of the fullness clause of GWZ Lemma 5.11, alone.**

`max 1 (Kakeya.Tube.dilateFullness.C n)`: the constant of the capsule-fullness estimate
`Kakeya.Tube.volume_dilate_inter_cthickening_ge` read at the dilation factor `c = 1`, truncated
below at `1`. Unlike `ShadedBody.rhoTubesSection9Loss` it is *purely dimensional* — it depends on
neither `δ` nor the cardinality of the fine family — because the fullness clause alone needs no
pigeonholing. -/
noncomputable def rhoTubesInducedFullnessLoss (n : ℕ) : ℝ≥0 :=
  max 1 (Kakeya.Tube.dilateFullness.C n)

theorem one_le_rhoTubesInducedFullnessLoss (n : ℕ) : 1 ≤ rhoTubesInducedFullnessLoss n :=
  le_max_left _ _

theorem rhoTubesInducedFullnessLoss_ne_zero (n : ℕ) : rhoTubesInducedFullnessLoss n ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_rhoTubesInducedFullnessLoss n))

open Classical in
/-- **The induced shading of a coarse body** (GWZ's `Y_{𝕋_ρ}`): the part of the coarse tube
`W j` within `2ρ` of the shading of the fine tubes assigned to it. -/
noncomputable def inducedCoarseShading {δ ρ : ℝ≥0} (s : Finset ι) (T : ι → ShadedTube δ E)
    (p : ι → κ) (W : κ → Tube ρ E) (j : κ) : ShadedBody E where
  toConvexSpaceBody := (W j).toConvexSpaceBody
  shade := (W j).carrier ∩
    Metric.cthickening (2 * (ρ : ℝ)) (⋃ i ∈ ({i ∈ s | p i = j} : Finset ι), (T i).shade)
  measurableSet_shade :=
    (W j).isCompact'.isClosed.measurableSet.inter Metric.isClosed_cthickening.measurableSet
  shade_subset := Set.inter_subset_left

omit [Nontrivial E] in
@[simp]
theorem inducedCoarseShading_toConvexSpaceBody {δ ρ : ℝ≥0} (s : Finset ι) (T : ι → ShadedTube δ E)
    (p : ι → κ) (W : κ → Tube ρ E) (j : κ) :
    (inducedCoarseShading s T p W j).toConvexSpaceBody = (W j).toConvexSpaceBody := rfl

omit [Nontrivial E] in
/-- **The induced coarse shading of the whole family lies in the `2ρ`-neighbourhood of the inner
shaded union.**

By construction `Y_{𝕋_ρ}(T_ρ) = T_ρ ∩ N_{2ρ}(⋃_{T ∈ 𝕋[T_ρ]} Y(T))`, and the fibre `𝕋[T_ρ]` is a
subset of `𝕋`, so the union over all coarse bodies is contained in `N_{2ρ}(U(𝕋, Y))`.  This is the
containment that lets a datum stated against `Metric.cthickening (2ρ) (U(𝕋, Y))` — which a
configuration can name — bound the coarse union `U(𝕋_ρ, Y_{𝕋_ρ})`, which it cannot. -/
theorem iUnion_inducedCoarseShading_subset_cthickening
    {δ ρ : ℝ≥0} (s : Finset ι) (T : ι → ShadedTube δ E) (p : ι → κ)
    (W : κ → Tube ρ E) (t : Finset κ) :
    (⋃ j ∈ t, (inducedCoarseShading s T p W j).shade)
      ⊆ Metric.cthickening (2 * (ρ : ℝ)) (⋃ i ∈ s, (T i).toShadedBody.shade) := by
  classical
  refine Set.iUnion₂_subset fun j _ => ?_
  refine Set.Subset.trans Set.inter_subset_right ?_
  refine Metric.cthickening_subset_of_subset _ ?_
  refine Set.iUnion₂_subset fun i hi => ?_
  exact Set.subset_biUnion_of_mem (u := fun i => (T i).toShadedBody.shade)
    (Finset.mem_filter.mp hi).1

open Classical in
/-- **The fullness engine of GWZ Lemma 5.11 on the full coarse family, at the named shading.**

This is the fullness conclusion of `ShadedBody.exists_rhoTubesSection9_fullFamily` stated about
`ShadedBody.inducedCoarseShading` itself rather than about an existentially bound family, so that
a caller which needs to know *what* the coarse shading is — for instance to bound its union by
`Metric.cthickening (2ρ) (U(𝕋, Y))` — can have both facts about the same term.  The proof is that
theorem's proof from the point where the family has been constructed. -/
theorem le_fullness_inducedCoarseShading
    {δ ρ Cd lam : ℝ≥0} (hδ : 0 < δ) (hρ : ρ ∈ Set.Icc δ 1) (hCd : Cd ≠ 0)
    {s : Finset ι} {t : Finset κ}
    (T : ι → ShadedTube δ E) (W : κ → Tube ρ E) (p : ι → κ)
    (hle : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ (W (p i)).toConvexSpaceBody)
    (hactive : ∀ j ∈ t, ∃ i ∈ s, p i = j) (ht : t.Nonempty)
    (hlam : ∀ i ∈ s,
      (Cd : ℝ≥0∞)⁻¹ * ((lam : ℝ≥0∞) * volume (T i).carrier) ≤ volume (T i).shade) :
    (Cd * rhoTubesInducedFullnessLoss (Module.finrank ℝ E))⁻¹ * lam
      ≤ fullness t (inducedCoarseShading s T p W) := by
  classical
  have hρ0 : 0 < ρ := lt_of_lt_of_le hδ hρ.1
  have hcar : ∀ i ∈ s, ((T i).toConvexSpaceBody : Set E) ⊆ ((W (p i)).toConvexSpaceBody : Set E) :=
    fun i hi => SetLike.coe_subset_coe.mpr (hle i hi)
  have key : ∀ j ∈ t,
      ((Cd : ℝ≥0∞)⁻¹ * (lam : ℝ≥0∞)) * volume (W j).carrier
        ≤ (rhoTubesInducedFullnessLoss (Module.finrank ℝ E) : ℝ≥0∞) *
            volume (inducedCoarseShading s T p W j).shade := by
    intro j hj
    obtain ⟨i, hi, hpi⟩ := hactive j hj
    subst hpi
    have hTcar0 : volume (T i).carrier ≠ 0 := by
      have h := Tube.le_volume (T i).toTube
      have hc : (0 : ℝ≥0∞) <
          ((Tube.le_volume.c (Module.finrank ℝ E) : ℝ≥0) : ℝ≥0∞) *
            (δ : ℝ≥0∞) ^ (Module.finrank ℝ E - 1) :=
        ENNReal.mul_pos (ne_of_gt (ENNReal.coe_pos.mpr (Tube.le_volume.c_pos _)))
          (ne_of_gt (ENNReal.pow_pos (ENNReal.coe_pos.mpr hδ) _))
      exact ne_of_gt (lt_of_lt_of_le hc (by simpa using h))
    have hTcarTop : volume (T i).carrier ≠ ⊤ := (T i).isCompact'.measure_ne_top
    have hdens : (Cd : ℝ≥0∞)⁻¹ * (lam : ℝ≥0∞)
        ≤ volume (T i).shade / volume (T i).carrier := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl hTcar0) (Or.inl hTcarTop), mul_assoc]
      exact hlam i hi
    have hgeo := Kakeya.Tube.volume_dilate_inter_cthickening_ge (E := E) hδ hρ.1 hρ.2
      (c := (1 : ℝ)) le_rfl (T i).toTube (W (p i))
      (by rw [Kakeya.Tube.dilate_one]; exact hcar i hi) (T i).shade_subset
    rw [Kakeya.Tube.dilate_one] at hgeo
    simp only [one_pow, ENNReal.ofReal_one, mul_one] at hgeo
    have hmono : volume ((W (p i)).carrier ∩ Metric.cthickening (2 * (ρ : ℝ)) (T i).shade)
        ≤ volume (inducedCoarseShading s T p W (p i)).shade :=
      measure_mono (Set.inter_subset_inter_right _
        (Metric.cthickening_subset_of_subset _
          (Set.subset_biUnion_of_mem (u := fun i' => (T i').shade)
            (Finset.mem_filter.mpr ⟨hi, rfl⟩))))
    calc
      ((Cd : ℝ≥0∞)⁻¹ * (lam : ℝ≥0∞)) * volume (W (p i)).carrier
          ≤ (volume (T i).shade / volume (T i).carrier) * volume (W (p i)).carrier :=
            mul_le_mul' hdens le_rfl
      _ ≤ (Kakeya.Tube.dilateFullness.C (Module.finrank ℝ E) : ℝ≥0∞) *
            volume ((W (p i)).carrier ∩ Metric.cthickening (2 * (ρ : ℝ)) (T i).shade) := hgeo
      _ ≤ (rhoTubesInducedFullnessLoss (Module.finrank ℝ E) : ℝ≥0∞) *
            volume (inducedCoarseShading s T p W (p i)).shade :=
            mul_le_mul' (ENNReal.coe_le_coe.mpr (le_max_right _ _)) hmono
  obtain ⟨j₀, hj₀⟩ := ht
  have hWpos : ∀ j : κ, 0 < volume (W j).carrier := by
    intro j
    have h := Tube.le_volume (W j)
    have hc : (0 : ℝ≥0∞) <
        ((Tube.le_volume.c (Module.finrank ℝ E) : ℝ≥0) : ℝ≥0∞) *
          (ρ : ℝ≥0∞) ^ (Module.finrank ℝ E - 1) :=
      ENNReal.mul_pos (ne_of_gt (ENNReal.coe_pos.mpr (Tube.le_volume.c_pos _)))
        (ne_of_gt (ENNReal.pow_pos (ENNReal.coe_pos.mpr hρ0) _))
    exact lt_of_lt_of_le hc (by simpa using h)
  have ht0 : ∑ j ∈ t, volume (inducedCoarseShading s T p W j).carrier ≠ 0 := by
    refine ne_of_gt (lt_of_lt_of_le (hWpos j₀) ?_)
    exact Finset.single_le_sum
      (f := fun j => volume (inducedCoarseShading s T p W j).carrier)
      (fun _ _ => by positivity) hj₀
  have httop : ∑ j ∈ t, volume (inducedCoarseShading s T p W j).carrier ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun j _ => (W j).isCompact'.measure_ne_top
  have hfull := le_fullness_of_forall_mul_volume_carrier_le
    (t := t) (W := inducedCoarseShading s T p W)
    (a := (Cd : ℝ≥0∞)⁻¹ * (lam : ℝ≥0∞))
    (b := (rhoTubesInducedFullnessLoss (Module.finrank ℝ E) : ℝ≥0∞))
    (ENNReal.coe_ne_zero.mpr (rhoTubesInducedFullnessLoss_ne_zero _))
    ENNReal.coe_ne_top ht0 httop key
  have hne : Cd * rhoTubesInducedFullnessLoss (Module.finrank ℝ E) ≠ 0 :=
    mul_ne_zero hCd (rhoTubesInducedFullnessLoss_ne_zero _)
  rw [← ENNReal.coe_le_coe]
  refine le_trans (le_of_eq ?_) hfull
  rw [ENNReal.coe_mul, ENNReal.coe_inv hne, ENNReal.coe_mul,
    ENNReal.mul_inv (Or.inl (ENNReal.coe_ne_zero.mpr hCd)) (Or.inl ENNReal.coe_ne_top),
    ENNReal.div_eq_inv_mul]
  ring

/-! ## The composed interface: Lemma 5.11 with the loss already in `δ^{-η}` -/

end Section9

end ShadedBody

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Kakeya.DimensionThree.MainLemma1.RevisedSource.CentringShadingW102

/-!
# Centring Dense Shading

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace KakeyaLink.DirectCenteredRoute

open Kakeya.ml1Boot.TrialRestartW94

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {iota : Type v} [DecidableEq iota]

theorem centered_shading_perTube_density
    (hdim : Module.finrank Real E = 3)
    {delta : NNReal} (hsmall : delta ≤ 1 / 200)
    (F G : Finset iota) (Y : iota -> ShadedTube delta E)
    (parent : iota -> iota) (W : iota -> Tube (delta / 2) E)
    (hcov : forall i, i ∈ F ->
      (fun x : E => (1 / 8 : Real) • x) '' (Y i).carrier ⊆ (W (parent i)).carrier)
    (hsurj : forall j, j ∈ G -> exists i, i ∈ F ∧ parent i = j)
    (density : ENNReal)
    (hdense : forall i, i ∈ F -> density * volume (Y i).carrier ≤ volume (Y i).shade) :
    forall j, j ∈ G ->
      density * volume (W j).carrier ≤
        384 * volume (sourceCentringShadingW102 F Y parent W hcov j).shade := by
  intro j hj
  obtain ⟨i, hi, hij⟩ := hsurj j hj
  have hshade :
      (fun x : E => (1 / 8 : Real) • x) '' (Y i).shade ⊆
        (sourceCentringShadingW102 F Y parent W hcov j).shade := by
    intro x hx
    apply Set.mem_iUnion₂.mpr
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, hij⟩, hx⟩
  have himage : (1 / 512 : ENNReal) * volume (Y i).shade ≤
      volume (sourceCentringShadingW102 F Y parent W hcov j).shade := by
    rw [← volume_source_centring_image_w102 hdim]
    exact measure_mono hshade
  calc
    density * volume (W j).carrier ≤
        density * ((384 : ENNReal) * (1 / 512 : ENNReal) * volume (Y i).carrier) :=
      mul_le_mul_right (half_radius_carrier_volume_w102 hdim hsmall (Y i).toTube (W j)) _
    _ = 384 * ((1 / 512 : ENNReal) * (density * volume (Y i).carrier)) := by ring
    _ ≤ 384 * ((1 / 512 : ENNReal) * volume (Y i).shade) := by gcongr; exact hdense i hi
    _ ≤ 384 * volume (sourceCentringShadingW102 F Y parent W hcov j).shade := by
      gcongr

theorem exists_centered_dense_quotient
    (hdim : Module.finrank Real E = 3)
    {delta : NNReal} (hdelta : 0 < delta) (hsmall : delta ≤ 1 / 200)
    (F : Finset iota) (Y : iota -> ShadedTube delta E)
    (hF : F.Nonempty)
    (hball : forall i, i ∈ F -> (Y i).carrier ⊆ Metric.closedBall 0 1)
    (density : ENNReal)
    (hdense : forall i, i ∈ F -> density * volume (Y i).carrier ≤ volume (Y i).shade) :
    exists (G : Finset iota) (parent : iota -> iota)
      (Z : iota -> ShadedTube (delta / 2) E),
      G.Nonempty ∧ G ⊆ F ∧ F.image parent = G ∧
      (forall j, j ∈ G -> (Z j).carrier ⊆ Metric.closedBall 0 (3 / 4 : Real)) ∧
      (forall j, j ∈ G -> centredTubeW94 (Z j).toTube) ∧
      lineEssentiallyDistinctW94 G (fun j => (Z j).toTube)
        (2 * (223 : NNReal) ^ (6 : Nat)) ∧
      (forall i, i ∈ F -> (fun x : E => (1 / 8 : Real) • x) '' (Y i).carrier ⊆
        (Z (parent i)).carrier) ∧
      (⋃ j ∈ G, (Z j).shade) =
        (fun x : E => (1 / 8 : Real) • x) '' (⋃ i ∈ F, (Y i).shade) ∧
      volume (⋃ j ∈ G, (Z j).shade) =
        (1 / 512 : ENNReal) * volume (⋃ i ∈ F, (Y i).shade) ∧
      (forall j, j ∈ G -> density * volume (Z j).carrier ≤ 384 * volume (Z j).shade) := by
  classical
  have hline : lineEssentiallyDistinctW94 F (fun i => (Y i).toTube) (F.card : NNReal) := by
    intro o v hv
    exact_mod_cast Finset.card_filter_le F _
  obtain ⟨G, parent, W, hG, hGF, himage, hfix, hballW, hcenter, hlineW, hcov, _⟩ :=
    exists_source_centred_representatives_w102 hdim hdelta hsmall F
      (fun i => (Y i).toTube) (F.card : NNReal) hF hball hline
  let Z := sourceCentringShadingW102 F Y parent W hcov
  have hmap : forall i, i ∈ F -> parent i ∈ G := by
    intro i hi
    rw [← himage]
    exact Finset.mem_image_of_mem parent hi
  have hsurj : forall j, j ∈ G -> exists i, i ∈ F ∧ parent i = j := by
    intro j hj
    rw [← himage] at hj
    exact Finset.mem_image.mp hj
  have hunion : (⋃ j ∈ G, (Z j).shade) =
      (fun x : E => (1 / 8 : Real) • x) '' (⋃ i ∈ F, (Y i).shade) :=
    source_centring_shaded_union_w102 F G Y parent W hcov hmap
  refine ⟨G, parent, Z, hG, hGF, himage, hballW, hcenter, hlineW, hcov,
    hunion, ?_, ?_⟩
  · rw [hunion, volume_source_centring_image_w102 hdim]
  · exact centered_shading_perTube_density hdim hsmall F G Y parent W hcov
      hsurj density hdense

end KakeyaLink.DirectCenteredRoute

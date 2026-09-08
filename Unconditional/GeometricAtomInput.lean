/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Unconditional.BalancedOriginalAtomSelection
import Unconditional.CentringDenseShading
import Unconditional.CenteredCoarseIncidence

/-!
# Geometric Atom Input

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

open MeasureTheory
open scoped Classical

namespace KakeyaLink.DirectCenteredRoute

open Kakeya.ml1Boot.TrialRestartW94

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

theorem actual_coarse_tuple_bound
    {I : Type v} {m : Nat} {delta eta : NNReal}
    (source : Finset I) (original : I -> Tube delta E)
    (fine : I -> Tube eta E) (fineParent : I -> I)
    (rho : Fin m -> NNReal) (hrho : forall k, 0 < rho k)
    (hrhoOne : forall k, rho k ≤ 1) (hscale : forall k, eta ≤ rho k)
    (coarseSet : Fin m -> Finset I) (coarse : forall k, I -> Tube (rho k) E)
    (coarseParent : Fin m -> I -> I)
    (hparent : forall k, forall i, i ∈ source -> coarseParent k i ∈ coarseSet k)
    (hline : forall k, lineEssentiallyDistinctW94 (coarseSet k) (coarse k)
      (2 * (223 : NNReal) ^ (6 : Nat)))
    (hcenter : forall k, forall j, j ∈ coarseSet k -> ‖(coarse k j).center‖ ≤ 1)
    (hfine : forall i, i ∈ source ->
      (fun x : E => (1 / 8 : Real) • x) '' (original i).carrier ⊆
        (fine (fineParent i)).carrier)
    (hcoarse : forall k, forall i, i ∈ source ->
      (fun x : E => (1 / 8 : Real) • x) '' (original i).carrier ⊆
        (coarse k (coarseParent k i)).carrier) :
    forall q, forall k,
      ((source.filter (fun i => fineParent i = q)).image (coarseParent k)).card ≤
        lineAmplificationBoundW95 (Module.finrank Real E) 1 128 * (2 * 223 ^ 6) := by
  classical
  intro q k
  have h := homothetic_coarse_parent_image_card_le (hrho k) (hrhoOne k) (hscale k)
    (source.filter (fun i => fineParent i = q)) original (coarseSet k) (coarse k)
    (coarseParent k) _ (hline k) 1 (by norm_num) (hcenter k) (fine q)
    (fun i hi => hparent k i (Finset.mem_filter.mp hi).1)
    (fun i hi => by
      obtain ⟨hi, heq⟩ := Finset.mem_filter.mp hi
      simpa only [heq] using hfine i hi)
    (fun i hi => hcoarse k i (Finset.mem_filter.mp hi).1)
  exact_mod_cast h

theorem exists_balanced_geometric_original_atoms
    {I : Type v} {m : Nat} {delta : NNReal}
    (hdim : Module.finrank Real E = 3) (hdelta : 0 < delta) (hsmall : delta ≤ 1 / 200)
    (source dense : Finset I) (V : I -> ShadedTube delta E)
    (hdense : dense ⊆ source) (hnonempty : dense.Nonempty)
    (hball : forall i, i ∈ dense -> (V i).carrier ⊆ Metric.closedBall 0 1)
    (density : ENNReal)
    (hpointwise : forall i, i ∈ dense -> density * volume (V i).carrier ≤ volume (V i).shade)
    (rho : Fin m -> NNReal) (hrho : forall k, 0 < rho k)
    (hrhoOne : forall k, rho k ≤ 1) (hscale : forall k, delta / 2 ≤ rho k)
    (coarseSet : Fin m -> Finset I) (coarse : forall k, I -> Tube (rho k) E)
    (coarseParent : Fin m -> I -> I)
    (hparent : forall k, forall i, i ∈ source -> coarseParent k i ∈ coarseSet k)
    (hline : forall k, lineEssentiallyDistinctW94 (coarseSet k) (coarse k)
      (2 * (223 : NNReal) ^ (6 : Nat)))
    (hcenter : forall k, forall j, j ∈ coarseSet k -> ‖(coarse k j).center‖ ≤ 1)
    (hcoarse : forall k, forall i, i ∈ source ->
      (fun x : E => (1 / 8 : Real) • x) '' (V i).carrier ⊆
        (coarse k (coarseParent k i)).carrier) :
    exists fineSet : Finset I, exists fineParent : I -> I,
    exists Z : I -> ShadedTube (delta / 2) E,
    exists initial selected : Finset (Option I × (Fin m -> I)),
    exists descended : Fin m -> I -> I,
      fineSet.Nonempty ∧ fineSet ⊆ dense ∧ dense.image fineParent = fineSet ∧
      (forall j, j ∈ fineSet -> (Z j).carrier ⊆ Metric.closedBall 0 (3 / 4 : Real)) ∧
      (forall j, j ∈ fineSet -> centredTubeW94 (Z j).toTube) ∧
      lineEssentiallyDistinctW94 fineSet (fun j => (Z j).toTube) (2 * (223 : NNReal) ^ 6) ∧
      (forall i, i ∈ dense -> (fun x : E => (1 / 8 : Real) • x) '' (V i).carrier ⊆
        (Z (fineParent i)).carrier) ∧
      volume (⋃ j ∈ fineSet, (Z j).shade) = (1 / 512 : ENNReal) * volume (⋃ i ∈ dense, (V i).shade) ∧
      (forall j, j ∈ fineSet -> density * volume (Z j).carrier ≤ 384 * volume (Z j).shade) ∧
      initial ⊆ source.image (denseJointCode dense fineParent coarseParent) ∧
      selected ⊆ initial ∧ selected.Nonempty ∧
      Set.InjOn (fun a : Option I × (Fin m -> I) => a.1) initial ∧
      initial.card ≤ fineSet.card ∧
      (source.filter (fun i => denseJointCode dense fineParent coarseParent i ∈ selected)).Nonempty ∧
      (source.filter (fun i => denseJointCode dense fineParent coarseParent i ∈ selected)) ⊆ dense ∧
      (dense.card : Real) ≤
        ((lineAmplificationBoundW95 3 1 128 * (2 * 223 ^ 6)) ^ m : Nat) *
          (2 * (1 + Real.logb 2 (2 * (initial.card : Real)))) *
            ((source.filter (fun i => denseJointCode dense fineParent coarseParent i ∈ selected)).card : Real) ∧
      (forall a, a ∈ selected -> forall b, b ∈ selected ->
        ((source.filter (fun i => denseJointCode dense fineParent coarseParent i = a)).card : ENNReal) ≤
          2 * ((source.filter (fun i => denseJointCode dense fineParent coarseParent i = b)).card : ENNReal)) ∧
      (forall i, i ∈ source -> denseJointCode dense fineParent coarseParent i ∈ selected ->
        forall k, descended k (fineParent i) = coarseParent k i) := by
  classical
  obtain ⟨fineSet, fineParent, Z, hne, hsub, himage, hballZ, hcenterZ, hlineZ,
    hcoverZ, _hunionZ, hvolumeZ, hdensityZ⟩ :=
    exists_centered_dense_quotient hdim hdelta hsmall dense V hnonempty hball density hpointwise
  have hbound := actual_coarse_tuple_bound dense (fun i => (V i).toTube)
    (fun j => (Z j).toTube) fineParent rho hrho hrhoOne hscale coarseSet coarse coarseParent
    (fun k i hi => hparent k i (hdense hi)) hline hcenter hcoverZ
    (fun k i hi => hcoarse k i (hdense hi))
  rw [hdim] at hbound
  obtain ⟨initial, selected, descended, hinitial, hselected, hselectedNe, hinj,
    hcard, hpullback, hpullDense, hmass, hbalance, hdescended⟩ :=
    exists_balanced_original_flagged_atoms source dense hdense hnonempty fineParent coarseParent
      (lineAmplificationBoundW95 3 1 128 * (2 * 223 ^ 6)) hbound
  rw [himage] at hcard
  exact ⟨fineSet, fineParent, Z, initial, selected, descended, hne, hsub, himage,
    hballZ, hcenterZ, hlineZ, hcoverZ, hvolumeZ, hdensityZ, hinitial, hselected,
    hselectedNe, hinj, hcard, hpullback, hpullDense, hmass, hbalance, hdescended⟩

end KakeyaLink.DirectCenteredRoute

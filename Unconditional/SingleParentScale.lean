/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Unconditional.BodyCWAToJohn
import MyLeanRepo.Kakeya.Assouad.PureWZ2.BodyCWASubfamilyTransfer

/-!
# Single Parent Scale

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

def singleParentScaleOfBodyCWA
    {delta rho : ℝ} (deltaPos : 0 < delta) (rhoPos : 0 < rho)
    (family : Kakeya.Streamlined.TubeFamily delta) (parent : Kakeya.DeltaTube rho)
    (contained : ∀ i, (family.tube i).carrier ⊆ parent.carrier)
    {ordinaryConstant outputConstant : ENNReal}
    (ordinary : WZ2PaperBodyConvexWolffBound family.toBodyFamily ordinaryConstant)
    (outputOne : 1 ≤ outputConstant)
    (johnBudget : 27 * (ordinaryConstant * volume parent.carrier) ≤ outputConstant) :
    WZ2PaperPureScaleCoverData family rho outputConstant := by
  let coarse : Kakeya.Streamlined.TubeFamily rho := { card := 1, tube := fun _ => parent }
  have allIndices : ∀ j : Fin coarse.card,
      wz2PaperOrdinaryFullFiberIndices family coarse j = Finset.univ := by
    intro j
    ext i
    simp only [mem_wz2PaperOrdinaryFullFiberIndices_iff, Finset.mem_univ, iff_true]
    exact contained i
  refine {
    delta_pos := deltaPos
    rho_pos := rhoPos
    coarse := coarse
    cover := { covers := ?_, doubled_fibers_disjoint := ?_ }
    full_fiber_uniform := ?_
    rescaledFiber := ?_ }
  · intro i
    exact ⟨0, by rw [allIndices]; simp⟩
  · intro first second different
    exact (different (Subsingleton.elim first second)).elim
  · intro first second
    simp only [wz2PaperOrdinaryFullFiberCount, allIndices]
    simpa [mul_comm] using mul_le_mul_right outputOne (family.card : ENNReal)
  · intro j
    let sub := Kakeya.Streamlined.TubeSubfamily.fromFinset family
      (wz2PaperOrdinaryFullFiberIndices family coarse j)
    let bodySub : Kakeya.Streamlined.Subfamily family.toBodyFamily :=
      { family := sub.family.toBodyFamily
        embedding := sub.embedding
        carrier_eq := fun i => congrArg Kakeya.DeltaTube.carrier (sub.tube_eq i) }
    have subCWA : WZ2PaperBodyConvexWolffBound sub.family.toBodyFamily ordinaryConstant := by
      have h := ordinary.subfamily_of_cardinality bodySub (K := 1) (by
        change (family.card : ENNReal) ≤
          1 * ((wz2PaperOrdinaryFullFiberIndices family coarse j).card : ENNReal)
        rw [allIndices]
        simp)
      simpa only [one_mul] using h
    let normalization := WZ2PaperAssouadUnitRescalingData.ofTube (coarse.tube j) rhoPos
    have john := bodyCWA_to_john_rescaled deltaPos rhoPos j
      (fun i => by rw [sub.tube_eq]; exact contained (sub.embedding i)) normalization subCWA
    refine ⟨{ normalization := normalization, convex_wolff := ?_ }⟩
    change WZ2PaperBodyConvexWolffBound
      (wz2PaperPureUnitRescaledFullFiberBodyFamily j normalization)
      (27 * (ordinaryConstant * volume (coarse.tube j).carrier)) at john
    intro set convexSet
    exact (john set convexSet).trans (by gcongr)

end Kakeya.Assouad

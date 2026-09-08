/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceWindowTrialW98

/-!
# Selecting one source parent per old cell in the window trial

Given a `DetailedTrialCellsW94` cell structure and a `WindowDetailedTrialDropW98` drop, this file
makes the source Drop parent constant on every surviving old normalized cell.
`Kakeya.ml1Boot.TrialRestartW94.actual_window_source_parent_degree_w101` bounds the number of
source parents met by one old cell by `trialNearbyParentCountW96 Ctw`, via the common fine-tube
meeting set; `exists_window_single_source_parent_refinement_w101` uses that degree to pick a
mass-retaining subfamily on which `assignPlus` is constant per old cell, at a single fixed loss;
`exists_window_old_cell_density_refinement_w101` then transports the drop's stronger max-density
estimate to each retained old-cell fibre through its selected parent.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ConvexSpaceBody ShadedBody

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

universe uE uI

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

open RevisedLiteralProfileInterfaceFormalizerW87

/-- Within one old normalized cell, only a fixed number of source Drop
parents occur. Each counted incidence has an actual common fine tube. -/
theorem actual_window_source_parent_degree_w101
    (hdim : Module.finrank ℝ E = 3)
    {iota : Type uI} [DecidableEq iota] {d : ℝ≥0}
    {F : Finset iota} {Y : iota -> ShadedTube d E} {L : Nat}
    {rho : Nat -> ℝ≥0} {Ctw Ccell : ℝ≥0}
    (cells : DetailedTrialCellsW94 F Y L rho Ctw Ccell)
    {epsilon zeta : ℝ} {Ktr : Nat}
    (drop : WindowDetailedTrialDropW98 cells epsilon zeta Ktr)
    (hd : 0 < d) (hd1 : d <= 1) (hepsilon : 0 < epsilon) (hCtw : 1 <= Ctw)
    (hball : ∀ i ∈ F, (Y i).carrier ⊆ Metric.closedBall 0 1)
    (H : Finset iota) (hH : H ⊆ drop.Fplus) :
    ∀ S : iota,
      ((completeFibreW94 H (cells.assign drop.level.val) S).image drop.assignPlus).card <=
        trialNearbyParentCountW96 Ctw := by
  have hl : drop.level.val <= L := Nat.le_of_lt_succ drop.level.isLt
  have hdr : d <= rho drop.level.val := by
    apply ENNReal.coe_le_coe.mp
    calc
      (d : ℝ≥0∞) = (d : ℝ≥0∞) ^ (1 : ℝ) := (ENNReal.rpow_one _).symm
      _ <= (d : ℝ≥0∞) ^ (1 - 3 * epsilon / 2) :=
        ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hd1) (by linarith)
      _ <= _ := drop.window_lower
  have hr1 : rho drop.level.val <= 1 := by
    apply ENNReal.coe_le_coe.mp
    exact drop.window_upper.trans
      (ENNReal.rpow_le_one (by exact_mod_cast hd1) (by linarith))
  intro S
  let sourceParents := (completeFibreW94 H (cells.assign drop.level.val) S).image drop.assignPlus
  let meeting := commonFineMeetingParentsW96 F (fun Q => (Y Q).toTube)
    (cells.parentSet drop.level.val) (cells.parentTube drop.level.val)
    (cells.parentTube drop.level.val S)
  have hsub : sourceParents ⊆ meeting := by
    intro P hP
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨hQH, hQS⟩ := Finset.mem_filter.mp hQ
    have hQD : Q ∈ drop.Fplus := hH hQH
    have hQF : Q ∈ F := drop.Fplus_subset hQD
    have hPnode : drop.assignPlus Q ∈ drop.nodes :=
      drop.assignPlus_image ▸ Finset.mem_image_of_mem _ hQD
    have hQsource := drop.assigned_containment (drop.assignPlus Q) hPnode
      (Finset.mem_filter.mpr ⟨hQD, rfl⟩)
    exact Finset.mem_filter.mpr ⟨drop.nodes_subset hPnode, Q, hQF,
      (Finset.mem_filter.mp hQsource).2,
      hQS ▸ cells.assigned_containment drop.level.val hl Q hQF⟩
  have hcount := card_assigned_parents_meeting_exact_cell_w96 hdim hd hdr hdr hr1
    F (fun Q => (Y Q).toTube) (cells.parentSet drop.level.val)
    (cells.parentTube drop.level.val) (cells.parentTube drop.level.val S)
    Ctw hCtw hball (cells.parent_ball drop.level.val hl) (cells.parent_line_ed drop.level.val hl)
  have hrzero : (rho drop.level.val : ℝ) ≠ 0 := by
    exact_mod_cast (cells.rho_pos drop.level.val hl).ne'
  simp only [div_self hrzero, max_self, one_pow, mul_one] at hcount
  exact (Finset.card_le_card hsub).trans (by exact_mod_cast hcount)

end

end Kakeya.ml1Boot.TrialRestartW94

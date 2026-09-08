/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.ActualSourceTerminalCentredW103
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourcePassNumericsConstructionW104
public import Kakeya.DimensionThree.MainLemma1.MassRetention

/-!
# Source input alternative

`actual_every_scale_node_w104` converts `actualEveryScaleW95` into
`CanonicalProfileNetW87.IsFrostmanAtEveryScale`. `exists_source_input_alternative_w104` is the
terminal alternative of the source run: for a centred, line-ED family in the unit ball with
fullness and Frostman inputs `delta^(±eInput)`, either the source multiplicity bound holds with
loss `delta^(-bLoss)`, or there is a subfamily `A ⊆ F` with reduced shadings retaining
`delta^bLoss` of the mass, a regularized working tower on it, and the every-scale Frostman
bound. It wraps `exists_actual_source_terminal_run_w95` from `ActualSourceTerminalCentredW103`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory ConvexSpaceBody ShadedBody

namespace Kakeya.ml1Boot.TrialRestartW94

open RevisedLiteralProfileInterfaceFormalizerW87

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
attribute [local instance] Classical.propDecidable

universe uE uI
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

omit [Nontrivial E] in
theorem actual_every_scale_node_w104
    {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}
    {F : Finset iota} {Y : iota -> ShadedTube delta E} {M N : Nat} {Ccan BF : ℝ≥0}
    {eps : ℝ} (U : CanonicalProfileNetW87 F (fun i => (Y i).toTube) M Ccan)
    (h : actualEveryScaleW95 U eps N BF) :
    U.IsFrostmanAtEveryScale ((BF : ℝ≥0∞) ^ (N + 1) * (delta : ℝ≥0∞) ^ (-3 * eps)) := by
  intro k hk R hR
  apply ConvexSpaceBody.frostmanConstant_le_iff.mp
  convert h k hk R hR using 1
  simp [frostmanConstIn_eq_frostmanConstant, completeFibreW94, Tube.coverClass]
  congr 1
  ext i
  simp

theorem exists_source_input_alternative_w104
    (hdim : Module.finrank ℝ E = 3)
    {p : Params} {beta gammaZero gamma xiMin : ℝ}
    {xi : Fin (p.N + 1) -> ℝ} {M : Nat}
    (hp : SourcePassNumericsW95 p beta gammaZero xi xiMin M)
    (hgamma : gamma ∈ Set.Icc gammaZero 1)
    (hKT : KatzTaoEstimate.{uI} E beta) (hKF : FrostmanEstimate.{uI} E gamma)
    (Csource : ℝ≥0) (hCsource : 1 <= Csource)
    (bLoss : ℝ) (hbLoss : 0 < bLoss) :
    ∃ (Cgood Cwork Ctw Ccell BF : ℝ≥0) (eInput : ℝ) (delta0 : ℝ≥0),
      1 <= Cgood ∧ 1 <= Cwork ∧ 1 <= Ctw ∧ 1 <= Ccell ∧ 1 <= BF ∧
      0 < eInput ∧ eInput < p.η 0 / 1000 ∧ 0 < delta0 ∧ delta0 < 1 ∧
      ∀ {delta : ℝ≥0}, 0 < delta -> delta < delta0 ->
      ∀ {iota : Type uI} [DecidableEq iota] (F : Finset iota) (Y : iota -> ShadedTube delta E),
        F.Nonempty -> (∀ i ∈ F, (Y i).carrier ⊆ Metric.closedBall 0 1) ->
        (∀ i ∈ F, centredTubeW94 (Y i).toTube) ->
        lineEssentiallyDistinctW94 F (fun i => (Y i).toTube) Csource ->
        (delta : ℝ≥0∞) ^ eInput <= fullness' F (fun i => (Y i).toShadedBody) ->
        frostmanConstIn F (fun i => (Y i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall <=
          (delta : ℝ≥0∞) ^ (-eInput) ->
        (ShadedBody.multiplicity F (fun i => (Y i).toShadedBody) <=
          (Cgood : ℝ≥0∞) * (delta : ℝ≥0∞) ^ (18 * xiMin - bLoss) *
          (delta : ℝ≥0∞) ^ (-2 * gamma) *
          ((F.card : ℝ≥0∞) * (delta : ℝ≥0∞) ^ (2 : Nat)) ^ (1 - gamma / 2)) ∨
        (∃ (A : Finset iota) (Z : iota -> ShadedTube delta E)
          (U : CanonicalProfileNetW87 A (fun i => (Z i).toTube) M Cwork),
          A.Nonempty ∧ A ⊆ F ∧
          (∀ i ∈ A, (Z i).toTube = (Y i).toTube) ∧
          (∀ i ∈ A, (Z i).shade ⊆ (Y i).shade) ∧
          (delta : ℝ≥0∞) ^ bLoss * (∑ i ∈ F, volume (Y i).shade) <=
            ∑ i ∈ A, volume (Z i).shade ∧
          Nonempty (SourceRegularizedWorkingTowerW95 U Ctw Ccell) ∧
          U.IsFrostmanAtEveryScale ((BF : ℝ≥0∞) ^ (p.N + 1) * (delta : ℝ≥0∞) ^ (-3 * p.ε))) := by
  obtain ⟨Ccan, CbaseTw, CbaseCell, Cwork, Ctw, Ccell, BF, Cgood, Cpass, CM, Kmax,
    eInput, eFull, eCF, aInitial, bInitial, fInitial, bReserve, delta0,
    hCcan, hCbaseTw, hCbaseCell, hCwork, hCtw, hCcell, hBF, hCgood, hCpass,
    hCM, hKmax, heInput, heInputSmall, heFull, heCF, haInitial, hbInitial,
    hfInitial, hbReserve, hbsum, hasum, hfsum, hdelta0, hdelta1, hThresh, hRun⟩ :=
    exists_actual_source_terminal_run_w95 hdim hp hgamma hKT hKF Csource hCsource bLoss hbLoss
  refine ⟨Cgood, Cwork, Ctw, Ccell, BF, eInput, delta0,
    hCgood, hCwork, hCtw, hCcell, hBF, heInput, heInputSmall, hdelta0, hdelta1, ?_⟩
  intro delta hd hdsmall iota _ F Y hF hball hcentred hline hfull hCF
  obtain ⟨B, base, U0, initial, trace, terminal, hBFset, hreg, hcard,
    hmassB, hbaseLambda, hbaseFrostman, hinitA, hinitY, hinitR, htrace,
    hDrop, hstates, htermSubset, htermShade, htermret, hmassTerminal, hterminal⟩ :=
    (hRun hd hdsmall).2 F Y hF hball hcentred hline hfull hCF
  have hAF : terminal.active ⊆ F := terminal.active_subset.trans hBFset
  rcases hterminal with hgood | ⟨U, hregular, hevery⟩
  · left
    have hde0 : (delta : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hd.ne'
    have hp0 : (delta : ℝ≥0∞) ^ bLoss ≠ 0 := by
      simp only [ne_eq, ENNReal.rpow_eq_zero_iff, hde0, ENNReal.coe_ne_top, false_and, or_self, not_false_eq_true]
    have hpTop : (delta : ℝ≥0∞) ^ bLoss ≠ ⊤ := by finiteness
    have hmass : (∑ i ∈ F, volume (Y i).shade) <=
        (delta : ℝ≥0∞) ^ (-bLoss) * (∑ i ∈ terminal.active, volume (terminal.shading i).shade) := by
      rw [ENNReal.rpow_neg]
      calc
        (∑ i ∈ F, volume (Y i).shade) = ((delta : ℝ≥0∞) ^ bLoss)⁻¹ *
            ((delta : ℝ≥0∞) ^ bLoss * (∑ i ∈ F, volume (Y i).shade)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hp0 hpTop, one_mul]
        _ <= _ := mul_le_mul_right hmassTerminal _
    have hunion : (⋃ i ∈ terminal.active, (terminal.shading i).shade) ⊆ ⋃ i ∈ F, (Y i).shade := by
      intro x hx
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
      exact Set.mem_iUnion₂.mpr ⟨i, hAF hi, terminal.subshade i hi hxi⟩
    have hmu := Kakeya.ml1Boot.multiplicity_le_mul_of_shade_mass
      (fun i => (Y i).toShadedBody) (fun i => (terminal.shading i).toShadedBody) hunion hmass
    have hq : 0 <= 1 - gamma / 2 := by linarith [hgamma.2]
    have hcard' : (terminal.active.card : ℝ≥0∞) <= (F.card : ℝ≥0∞) := by
      exact_mod_cast Finset.card_le_card hAF
    have hpow : (delta : ℝ≥0∞) ^ (-bLoss) * (delta : ℝ≥0∞) ^ (18 * xiMin) =
        (delta : ℝ≥0∞) ^ (18 * xiMin - bLoss) := by
      rw [← ENNReal.rpow_add _ _ hde0 ENNReal.coe_ne_top]
      congr 1
      ring
    calc
      ShadedBody.multiplicity F (fun i => (Y i).toShadedBody) <=
          (delta : ℝ≥0∞) ^ (-bLoss) * ShadedBody.multiplicity terminal.active
            (fun i => (terminal.shading i).toShadedBody) := hmu
      _ <= (delta : ℝ≥0∞) ^ (-bLoss) * ((Cgood : ℝ≥0∞) * (delta : ℝ≥0∞) ^ (18 * xiMin) *
          (delta : ℝ≥0∞) ^ (-2 * gamma) *
          ((delta : ℝ≥0∞) ^ (2 : Nat) * (terminal.active.card : ℝ≥0∞)) ^ (1 - gamma / 2)) :=
        mul_le_mul_right hgood _
      _ <= (delta : ℝ≥0∞) ^ (-bLoss) * ((Cgood : ℝ≥0∞) * (delta : ℝ≥0∞) ^ (18 * xiMin) *
          (delta : ℝ≥0∞) ^ (-2 * gamma) *
          ((delta : ℝ≥0∞) ^ (2 : Nat) * (F.card : ℝ≥0∞)) ^ (1 - gamma / 2)) := by gcongr
      _ = (Cgood : ℝ≥0∞) * ((delta : ℝ≥0∞) ^ (-bLoss) * (delta : ℝ≥0∞) ^ (18 * xiMin)) *
          (delta : ℝ≥0∞) ^ (-2 * gamma) *
          ((F.card : ℝ≥0∞) * (delta : ℝ≥0∞) ^ (2 : Nat)) ^ (1 - gamma / 2) := by
        rw [mul_comm ((delta : ℝ≥0∞) ^ (2 : Nat)) (F.card : ℝ≥0∞)]
        ring
      _ = _ := by rw [hpow]
  · exact Or.inr ⟨terminal.active, terminal.shading, U, terminal.active_nonempty, hAF,
      terminal.same_tube, terminal.subshade, hmassTerminal, hregular, actual_every_scale_node_w104 U hevery⟩

end
end Kakeya.ml1Boot.TrialRestartW94

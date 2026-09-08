/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceCanonicalTransportW97
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceWindowTrialW98

/-!
# Canonical drop constructors (W100)

Builds the canonical-level data of a source drop from a positive fine lift.
`exists_canonical_drop_support_and_mass_w100` constructs canonical shadings `W`, `Wplus` on
the `CanonicalQNodeW87` support `Fplus` retaining the fine mass fraction;
`exists_canonical_drop_partition_w100` descends a fibre-consistent fine parent assignment to a
disjoint partition of `Fplus`; `exists_actual_window_drop_canonical_shadings_w100` produces
positive fine and canonical shadings on common supports from the window-trial drops of
`SourceWindowTrialW98`, with retained fraction `(1/2) * trialRetainedFractionW94`; and
`canonical_drop_part_parent_containment_w100` places each canonical part inside the
`5 σ`-enlargement of its threaded parent tube.
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

/-- The canonical shadings and exact support constructed from a positive fine
lift retain the same mass fraction as that lift. -/
theorem exists_canonical_drop_support_and_mass_w100
    {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0} (hd : 0 < delta)
    {B : Finset iota} {V : iota -> ShadedTube delta E} {M : Nat} {Ccan : ℝ≥0}
    (U0 : CanonicalProfileNetW87 B (fun i => (V i).toTube) M Ccan)
    (current : RetainedStateW94 B V) (q : Fin (M + 1))
    (F G : Finset iota) (Y Z : iota -> ShadedTube delta E)
    (hF : F ⊆ current.active) (hG : G ⊆ F) (hGne : G.Nonempty)
    (hY : ∀ i ∈ F, (Y i).toTube = (current.shading i).toTube)
    (hZ : ∀ i ∈ G, (Z i).toTube = (Y i).toTube ∧ (Z i).shade ⊆ (Y i).shade)
    (hZpos : ∀ i ∈ G, 0 < volume (Z i).shade)
    (r : ℝ≥0∞)
    (hret : r * (∑ i ∈ F, volume (Y i).shade) <= ∑ i ∈ G, volume (Z i).shade) :
    ∃ (c : ℝ≥0)
      (W Wplus : CanonicalQNodeW87 U0 current.active q ->
        ShadedTube (Tube.gridScale delta M q.val) E)
      (Fplus : Finset (CanonicalQNodeW87 U0 current.active q)),
      0 < c ∧ Fplus.Nonempty ∧ Fplus ⊆ canonicalQNodeFinsetW87 U0 current.active q ∧
      G.image (U0.cover.assign q.val) = Fplus.image Subtype.val ∧
      (∀ w ∈ Fplus, ∃ i ∈ G, U0.cover.assign q.val i = w.val ∧
        0 < volume (Z i).shade) ∧
      (∀ w, (W w).toTube = U0.cover.tube q.val w.val ∧
        (Wplus w).toTube = U0.cover.tube q.val w.val ∧ (Wplus w).shade ⊆ (W w).shade) ∧
      (∀ w, (W w).shade ⊆
        ⋃ i ∈ completeFibreW94 F (U0.cover.assign q.val) w.val, (Y i).shade) ∧
      (∀ w, (Wplus w).shade ⊆
        ⋃ i ∈ completeFibreW94 G (U0.cover.assign q.val) w.val, (Z i).shade) ∧
      (∀ w, volume (W w).shade = (c : ℝ≥0∞) *
        ∑ i ∈ completeFibreW94 F (U0.cover.assign q.val) w.val, volume (Y i).shade) ∧
      (∀ w, volume (Wplus w).shade = (c : ℝ≥0∞) *
        ∑ i ∈ completeFibreW94 G (U0.cover.assign q.val) w.val, volume (Z i).shade) ∧
      (∀ w ∈ Fplus, 0 < volume (Wplus w).shade) ∧
      r * (∑ w ∈ canonicalQNodeFinsetW87 U0 current.active q, volume (W w).shade) <=
        ∑ w ∈ Fplus, volume (Wplus w).shade := by
  have hpos : 0 < ∑ i ∈ G, volume (Z i).shade := by
    obtain ⟨i, hi⟩ := hGne
    exact (hZpos i hi).trans_le
      (Finset.single_le_sum (f := fun i => volume (Z i).shade) (fun _ _ => bot_le) hi)
  obtain ⟨c, W, Wplus, hc, htube, hWsub, hWplusSub, hWvol, hWplusVol, hplusPos⟩ :=
    exists_actual_canonical_induced_shadings_w97 hd U0 current q F G Y Z hF hG hY hZ hpos
  let nodes := canonicalQNodeFinsetW87 U0 current.active q
  let Fplus := nodes.filter (fun w => w.val ∈ G.image (U0.cover.assign q.val))
  have hFplus : Fplus ⊆ nodes := Finset.filter_subset _ _
  have hmemNodes : ∀ w : CanonicalQNodeW87 U0 current.active q, w ∈ nodes := by
    intro w
    exact Finset.mem_attach _ _
  have himage : G.image (U0.cover.assign q.val) = Fplus.image Subtype.val := by
    ext w
    constructor
    · intro hw
      have hwcurrent : w ∈ canonicalAncestorFamilyW87 U0 current.active q :=
        Finset.image_mono _ (hG.trans hF) hw
      let v : CanonicalQNodeW87 U0 current.active q := ⟨w, hwcurrent⟩
      exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hmemNodes v, hw⟩, rfl⟩
    · intro hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      exact (Finset.mem_filter.mp hv).2
  have hsupport : ∀ w ∈ Fplus, ∃ i ∈ G, U0.cover.assign q.val i = w.val ∧
      0 < volume (Z i).shade := by
    intro w hw
    obtain ⟨i, hi, hiw⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hw).2
    exact ⟨i, hi, hiw, hZpos i hi⟩
  have hplusne : Fplus.Nonempty := by
    have hne : (Fplus.image Subtype.val).Nonempty := himage ▸ hGne.image _
    exact Finset.image_nonempty.mp hne
  have htotal (H : Finset iota) (T : iota -> ShadedTube delta E)
      (hH : H ⊆ current.active) :
      (∑ w ∈ nodes, ∑ i ∈ completeFibreW94 H (U0.cover.assign q.val) w.val,
        volume (T i).shade) = ∑ i ∈ H, volume (T i).shade := by
    change (∑ w ∈ (canonicalAncestorFamilyW87 U0 current.active q).attach,
      ∑ i ∈ H.filter (fun i => U0.cover.assign q.val i = w.val), volume (T i).shade) = _
    exact (Finset.sum_attach _ _).trans
      (Finset.sum_fiberwise_of_maps_to
        (fun i hi => Finset.mem_image_of_mem _ (hH hi)) (fun i => volume (T i).shade))
  have htotalW : (∑ w ∈ nodes, volume (W w).shade) =
      (c : ℝ≥0∞) * ∑ i ∈ F, volume (Y i).shade := by
    calc
      _ = ∑ w ∈ nodes, (c : ℝ≥0∞) *
          ∑ i ∈ completeFibreW94 F (U0.cover.assign q.val) w.val, volume (Y i).shade :=
        Finset.sum_congr rfl (fun w hw => hWvol w)
      _ = _ := by rw [← Finset.mul_sum, htotal F Y hF]
  have htotalPlus : (∑ w ∈ Fplus, volume (Wplus w).shade) =
      (c : ℝ≥0∞) * ∑ i ∈ G, volume (Z i).shade := by
    have hfullsum : (∑ w ∈ Fplus, volume (Wplus w).shade) =
        ∑ w ∈ nodes, volume (Wplus w).shade := by
      apply Finset.sum_subset hFplus
      intro w hw hwnot
      rw [hWplusVol]
      have hempty : completeFibreW94 G (U0.cover.assign q.val) w.val = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        obtain ⟨hiG, hiw⟩ := Finset.mem_filter.mp hi
        exact hwnot (Finset.mem_filter.mpr ⟨hw, Finset.mem_image.mpr ⟨i, hiG, hiw⟩⟩)
      rw [hempty, Finset.sum_empty, mul_zero]
    rw [hfullsum]
    calc
      _ = ∑ w ∈ nodes, (c : ℝ≥0∞) *
          ∑ i ∈ completeFibreW94 G (U0.cover.assign q.val) w.val, volume (Z i).shade :=
        Finset.sum_congr rfl (fun w hw => hWplusVol w)
      _ = _ := by rw [← Finset.mul_sum, htotal G Z (hG.trans hF)]
  refine ⟨c, W, Wplus, Fplus, hc, hplusne, hFplus, himage, hsupport, htube,
    hWsub, hWplusSub, hWvol, hWplusVol, ?_, ?_⟩
  · intro w hw
    obtain ⟨i, hi, hiw, hzi⟩ := hsupport w hw
    rw [hWplusVol]
    apply ENNReal.mul_pos (ENNReal.coe_pos.mpr hc).ne'
    exact (hzi.trans_le (Finset.single_le_sum (f := fun i => volume (Z i).shade) (fun _ _ => bot_le)
      (Finset.mem_filter.mpr ⟨hi, hiw⟩))).ne'
  · rw [htotalW, htotalPlus, mul_left_comm]
    exact mul_le_mul_right hret _

omit [Nontrivial E] in
/-- A synchronized fine assignment descends to a disjoint partition of the
canonical support, with every part retaining its actual fine witnesses. -/
theorem exists_canonical_drop_partition_w100
    {iota : Type uI} [DecidableEq iota] {delta : ℝ≥0}
    {B : Finset iota} {V : iota -> ShadedTube delta E} {M : Nat} {Ccan : ℝ≥0}
    (U0 : CanonicalProfileNetW87 B (fun i => (V i).toTube) M Ccan)
    (current : RetainedStateW94 B V) (q : Fin (M + 1))
    (G : Finset iota) (hGne : G.Nonempty)
    (Fplus : Finset (CanonicalQNodeW87 U0 current.active q))
    (himage : G.image (U0.cover.assign q.val) = Fplus.image Subtype.val)
    (parent : iota -> iota)
    (hconsistent : ∀ i ∈ G, ∀ j ∈ G, U0.cover.assign q.val i = U0.cover.assign q.val j ->
      parent i = parent j) :
    ∃ (nodeFamily : Finset iota)
      (part : iota -> Finset (CanonicalQNodeW87 U0 current.active q)),
      nodeFamily = G.image parent ∧ nodeFamily.Nonempty ∧
      Fplus = nodeFamily.biUnion part ∧
      (nodeFamily : Set iota).Pairwise (fun P Q => Disjoint (part P) (part Q)) ∧
      (∀ P ∈ nodeFamily, part P ⊆ Fplus ∧ (part P).Nonempty) ∧
      (∀ P ∈ nodeFamily, ∀ w ∈ part P,
        (∃ i ∈ G, U0.cover.assign q.val i = w.val ∧ parent i = P) ∧
        (∀ i ∈ G, U0.cover.assign q.val i = w.val -> parent i = P)) := by
  have hfine : ∀ w ∈ Fplus, ∃ i ∈ G, U0.cover.assign q.val i = w.val := by
    intro w hw
    have h := Finset.mem_image_of_mem Subtype.val hw
    rw [← himage] at h
    exact Finset.mem_image.mp h
  choose representative representativeMem representativeEq using hfine
  obtain ⟨default, hdefault⟩ := hGne
  let assignment := fun w : CanonicalQNodeW87 U0 current.active q =>
    if hw : w ∈ Fplus then parent (representative w hw) else parent default
  let part := fun P => Fplus.filter (fun w => assignment w = P)
  let nodeFamily := G.image parent
  have hrepresentative : ∀ w ∈ Fplus, ∀ i ∈ G,
      U0.cover.assign q.val i = w.val -> parent i = assignment w := by
    intro w hw i hi hiw
    dsimp only [assignment]
    rw [dif_pos hw]
    exact hconsistent i hi (representative w hw) (representativeMem w hw)
      (hiw.trans (representativeEq w hw).symm)
  have hassignment : ∀ w ∈ Fplus, assignment w ∈ nodeFamily := by
    intro w hw
    dsimp only [assignment]
    rw [dif_pos hw]
    exact Finset.mem_image_of_mem parent (representativeMem w hw)
  have hcover : Fplus = nodeFamily.biUnion part := by
    ext w
    constructor
    · intro hw
      exact Finset.mem_biUnion.mpr ⟨assignment w, hassignment w hw,
        Finset.mem_filter.mpr ⟨hw, rfl⟩⟩
    · intro hw
      obtain ⟨P, hP, hwP⟩ := Finset.mem_biUnion.mp hw
      exact (Finset.mem_filter.mp hwP).1
  refine ⟨nodeFamily, part, rfl, Finset.Nonempty.image ⟨default, hdefault⟩ _, hcover, ?_, ?_, ?_⟩
  · intro P hP Q hQ hPQ
    apply Finset.disjoint_left.mpr
    intro w hwP hwQ
    exact hPQ ((Finset.mem_filter.mp hwP).2.symm.trans (Finset.mem_filter.mp hwQ).2)
  · intro P hP
    refine ⟨Finset.filter_subset _ _, ?_⟩
    obtain ⟨i, hi, hiP⟩ := Finset.mem_image.mp hP
    have hwi : U0.cover.assign q.val i ∈ Fplus.image Subtype.val :=
      himage ▸ Finset.mem_image_of_mem _ hi
    obtain ⟨w, hw, hwi⟩ := Finset.mem_image.mp hwi
    exact ⟨w, Finset.mem_filter.mpr ⟨hw,
      (hrepresentative w hw i hi hwi.symm).symm.trans hiP⟩⟩
  · intro P hP w hwP
    obtain ⟨hw, hwP⟩ := Finset.mem_filter.mp hwP
    refine ⟨⟨representative w hw, representativeMem w hw, representativeEq w hw, ?_⟩, ?_⟩
    · exact (hrepresentative w hw _ (representativeMem w hw) (representativeEq w hw)).trans hwP
    · intro i hi hiw
      exact (hrepresentative w hw i hi hiw).trans hwP

omit [Nontrivial E] in
/-- Canonical parts sharing actual fine members with a threaded parent lie
inside its fixed-radius enlargement, including the full finite tube caps. -/
theorem canonical_drop_part_parent_containment_w100
    {iota : Type uI} [DecidableEq iota] {delta sigma : ℝ≥0}
    {B : Finset iota} {V : iota -> ShadedTube delta E} {M : Nat} {Ccan : ℝ≥0}
    (U0 : CanonicalProfileNetW87 B (fun i => (V i).toTube) M Ccan)
    (current : RetainedStateW94 B V) (q : Fin (M + 1))
    (hd : 0 < delta) (hd1 : delta <= 1) (hM : 1 <= M)
    (hscale : Tube.gridScale delta M q.val <= sigma)
    (G parents : Finset iota) (hG : G ⊆ current.active)
    (parent : iota -> iota) (parentTube : iota -> Tube sigma E)
    (hparent : ∀ i ∈ G,
      (current.shading i).toConvexSpaceBody <= (parentTube (parent i)).toConvexSpaceBody)
    (part : iota -> Finset (CanonicalQNodeW87 U0 current.active q))
    (hpart : ∀ P ∈ parents, ∀ w ∈ part P,
      ∃ i ∈ G, U0.cover.assign q.val i = w.val ∧ parent i = P)
    (Wplus : CanonicalQNodeW87 U0 current.active q -> ShadedTube (Tube.gridScale delta M q.val) E)
    (hWplus : ∀ P ∈ parents, ∀ w ∈ part P, (Wplus w).toTube = U0.cover.tube q.val w.val) :
    ∀ P ∈ parents, ∀ w ∈ part P,
      (Wplus w).toConvexSpaceBody <= ((parentTube P).rescale (5 * sigma)).toConvexSpaceBody := by
  have hdeltaTau : delta <= Tube.gridScale delta M q.val := by
    simpa only [Tube.gridScale_self delta hM] using
      Tube.gridScale_antitone hd hd1 M (Nat.le_of_lt_succ q.isLt)
  intro P hP w hw
  obtain ⟨i, hi, hiw, hiP⟩ := hpart P hP w hw
  have hfine : (current.shading i).toConvexSpaceBody <=
      (U0.cover.tube q.val w.val).toConvexSpaceBody := by
    rw [show (current.shading i).toConvexSpaceBody = (V i).toConvexSpaceBody from
      congrArg Tube.toConvexSpaceBody (current.same_tube i (hG hi))]
    exact hiw ▸ U0.cover.le_tube_assign q.val (Nat.le_of_lt_succ q.isLt) i
      (current.active_subset (hG hi))
  have hwide := Tube.le_rescale_of_subset (current.shading i).toTube
    (U0.cover.tube q.val w.val) hfine
  have hthicken := Tube.rescale_le_rescale_of_body_le (current.shading i).toTube
    (parentTube P)
    (show delta <= 4 * Tube.gridScale delta M q.val from hdeltaTau.trans (by nlinarith))
    (show sigma + 4 * Tube.gridScale delta M q.val <= 5 * sigma by nlinarith)
    (by simpa only [hiP] using hparent i hi)
  rw [show (Wplus w).toConvexSpaceBody = (U0.cover.tube q.val w.val).toConvexSpaceBody from
    congrArg Tube.toConvexSpaceBody (hWplus P hP w hw)]
  exact hwide.trans hthicken

end

end Kakeya.ml1Boot.TrialRestartW94

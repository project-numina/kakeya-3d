/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.SlabAssignment

/-!
# Controlled slab non-concentration bridge (GWZ Lemma 6.1 input)

The paper-facing slab non-concentration hypothesis of GWZ Lemma 6.1 is stated for the *exact*
slab subfamily `Plank.inSlabFamily`, whereas the formalised plank-to-tube reduction (GWZ Lemma
6.13) only returns membership in a *controlled* subfamily.  This file bridges the two, up to a
multiplicative loss depending only on the fixed controlled-comparability constants.

## Which relaxation is bridgeable

Exact slab membership is rigid in the two *long* directions: a `Slab φ` has half-widths
`(φ, 1, 1)` and an `a × b × 1` plank has long half-width exactly `1`, so
`(V i).carrier ⊆ S.carrier` pins the plank's long extent to the slab's.  Consequently:

* Relaxing the **thin** half-width (`θ ↦ Cset · θ`) and the **angle** (`θ ↦ Cang · θ`) is
  absorbed by a *single* comparison slab at the comparable scale `φ = max Cset Cang · θ`
  (`Plank.inSlabFamilyThin_subset_inSlabFamily_reslab`): no covering, `Nctrl = 1`.
* Relaxing the two long half-widths (`1 ↦ Cset`), as `Plank.inSlabFamilyC` does through
  `PrismNDim.dilation`, is **not** bridgeable by any constant depending only on `Cset, Cang`.
  Take `b = 1/2`, `θ = a / b`, `S` the slab centred at `0` with frame `(e₀, e₁, e₂)`, and `N`
  planks with that same frame, half-widths `(a, 1/2, 1)` and centres `t_j • e₂` for distinct
  `t_j ∈ [0, 1]`.  All of them lie in `S.dilation 2` at angle `0`, so the controlled family is
  everything, while every exact family `inSlabFamily s V S'` (any thickness `φ ≤ 1`, any slab
  `S'`) contains at most one index, because exact containment forces the long extent
  `[t_j - 1, t_j + 1]` to sit inside an interval of length `2`.  With `η = 0`, `γ = 1` and
  `N = ⌈1 / (2a)⌉` the exact hypothesis holds while the controlled conclusion would force
  `Cctrl ≥ 1 / (2a)`.

So the thin-direction family `Plank.inSlabFamilyThin` is the correct target of the bridge, and
`Plank.inSlabFamilyC` is bridgeable exactly in the case `Cset = 1`, where the dilation contributes
nothing in the long directions.

## The full dilation under pairwise essential distinctness

Adding pairwise essential distinctness of the planks *does* repair the bridge for the full
`Plank.inSlabFamilyC`, and the counterexample above is destroyed by it: two planks that are
translates of one another along the long direction by `d` intersect in a fraction `1 - d / 2` of
their volume, so essential distinctness forces `d ≥ 1`, leaving only `O(Cset)` long positions
inside the `Cset`-dilation instead of the `⌈1 / (2a)⌉` used there.

The remaining geometric content is a *bounded exact cover*: the controlled family is a union of at
most `N = N(Cset, Cang)` exact families at a comparable scale `φ ≍ θ`.  In the directions where
exact containment has slack (the thin direction, the plank angle, and any in-plane rotation
bounded away from the slab axes) the cover is geometric; in the rigid directions (long position,
and in-plane rotation within `O(b)` of a slab axis) essential distinctness caps the number of
classes.  This file reduces the cardinality estimate to exactly that covering statement
(`Plank.card_inSlabFamilyC_le_of_exactCover`, `Plank.card_inSlabFamilyC_le_of_capture` and the
packaged `Plank.exists_ctrl_card_inSlabFamilyC_le_of_pairwiseED_cover`), so that no analytic
bookkeeping is left in the geometric argument.

## What GWZ Lemma 6.1 actually consumes

Lemma 6.1 does not need the bound for an arbitrary controlled family: it needs the number of active
thickened *representatives* assigned to one selected slab.  Those come with an anchor index
`rep Q ∈ s` satisfying `R.repr (rep Q) = Q`, whose plank lies *exactly* in its own candidate slab
`(V (rep Q)).toSlab θ`, and that candidate slab is not essentially distinct from the selected slab.
Two consequences, both proved here:

* the anchor lies in the controlled subfamily of the selected slab for **absolute** constants
  (`Plank.exists_absolute_mem_inSlabFamilyC_of_candidateSlab_notED`), so nothing in the final loss
  depends on `cThk` or on the Lemma 6.13 constants;
* `rep` is injective on `R.indexSet`, so representatives may be counted by their anchors
  (`Plank.card_anchors_le_card_inSlabFamilyC`).

`Plank.exists_canchor_card_candidateAnchors_le_of_cover` assembles these with the analytic bridge
into the statement Lemma 6.1 consumes, still from the paper-facing `hslab`.
-/

@[expose] public section

open scoped NNReal

open MeasureTheory Convexity
open scoped NNReal Real

noncomputable section

universe u

namespace Slab

variable {θ : ℝ≥0} {hθ1 : θ ≤ 1}

/-- **Rescale a slab in its thin direction**: the `Slab φ` with the same centre and orthonormal
frame as `S`, i.e. half-widths `![φ, 1, 1]`.  This is the slab analogue of `Plank.toSlab`, and the
single comparison slab used by the controlled-to-exact bridge. -/
def reslab (S : Slab θ hθ1) (φ : ℝ≥0) (hφ1 : φ ≤ 1) : Slab φ hφ1 where
  toPrismNDim := PrismNDim.mk' S.center S.basis ![φ, 1, 1]
  thicknesses_eq := PrismNDim.thicknesses_mk' _ _ _

@[simp] theorem reslab_center (S : Slab θ hθ1) (φ : ℝ≥0) (hφ1 : φ ≤ 1) :
    (S.reslab φ hφ1).center = S.center := rfl

@[simp] theorem reslab_basis (S : Slab θ hθ1) (φ : ℝ≥0) (hφ1 : φ ≤ 1) :
    (S.reslab φ hφ1).basis = S.basis := rfl


/-- **Widen a slab to the working window**: the `φ × R × R` prism with the same centre and frame as
`S`.  GWZ's slabs are `θ`-neighbourhoods of *planes* intersected with the working window, so their
long extent is that of the window, not `1`; `Slab θ = Prism3D θ 1 1` has long half-widths equal to a
plank's own length, which makes exact containment in it a far stronger requirement.  `widen` is the
faithful model, and the target of the window-aware bridge below. -/
def widen (S : Slab θ hθ1) (φ R : ℝ≥0) (hφR : φ ≤ R) : Prism3D φ R R hφR le_rfl where
  toPrismNDim := PrismNDim.mk' S.center S.basis ![φ, R, R]
  thicknesses_eq := PrismNDim.thicknesses_mk' _ _ _

@[simp] theorem widen_center (S : Slab θ hθ1) (φ R : ℝ≥0) (hφR : φ ≤ R) :
    (S.widen φ R hφR).center = S.center := rfl

@[simp] theorem widen_basis (S : Slab θ hθ1) (φ R : ℝ≥0) (hφR : φ ≤ R) :
    (S.widen φ R hφR).basis = S.basis := rfl


/-- The angle with a rescaled slab is the angle with the original slab: `reslab` keeps the frame,
and `Prism3D.angle` only sees `basis 0`. -/
theorem angle_reslab {a' b' c' : ℝ≥0} {hab' : a' ≤ b'} {hbc' : b' ≤ c'}
    (Q : Prism3D a' b' c' hab' hbc') (S : Slab θ hθ1) (φ : ℝ≥0) (hφ1 : φ ≤ 1) :
    Prism3D.angle Q (S.reslab φ hφ1) = Prism3D.angle Q S := by
  rw [Prism3D.angle_def, Prism3D.angle_def, reslab_basis]


end Slab

namespace Plank

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}


/-! ### The window-aware bridge: long directions are governed by the window

`Plank.inSlabFamilyC` relaxes *all three* half-widths of a `Slab θ = Prism3D θ 1 1`, and the module
docstring records that the long-direction relaxation is not controlled by the exact `Slab`-family
hypothesis — not even for pairwise essentially distinct planks.  The reason is that a `Slab` has long
half-widths `1`, exactly a plank's own length, whereas GWZ's slab is the `θ`-neighbourhood of a
*plane* intersected with the working window.  For a windowed family the two long coordinates of a
plank relative to any slab centred in the window are bounded by twice the window radius *for free*,
so the controlled family is an **exact** family of one widened slab `Slab.widen` at the comparable
scale.  This is the unconditional replacement for the false long-direction bridge. -/

open scoped Classical in
/-- The exact subfamily of a **wide** slab `Prism3D φ R R`: the GWZ-faithful slab family. -/
def inWideSlabFamily {φ R : ℝ≥0} {hφR : φ ≤ R} (s : Finset ι) (V : ι → Plank a b hab hb1)
    (Sφ : Prism3D φ R R hφR le_rfl) : Finset ι :=
  {i ∈ s | (V i).carrier ⊆ Sφ.carrier ∧ Prism3D.angle (V i) Sφ ≤ (φ : ℝ)}

theorem mem_inWideSlabFamily {φ R : ℝ≥0} {hφR : φ ≤ R} {s : Finset ι}
    {V : ι → Plank a b hab hb1} {Sφ : Prism3D φ R R hφR le_rfl} {i : ι} :
    i ∈ inWideSlabFamily s V Sφ ↔
      i ∈ s ∧ (V i).carrier ⊆ Sφ.carrier ∧ Prism3D.angle (V i) Sφ ≤ (φ : ℝ) := by
  classical
  simp [inWideSlabFamily]

theorem inWideSlabFamily_subset {φ R : ℝ≥0} {hφR : φ ≤ R} {s : Finset ι}
    {V : ι → Plank a b hab hb1} {Sφ : Prism3D φ R R hφR le_rfl} :
    inWideSlabFamily s V Sφ ⊆ s := by
  intro i hi; exact (mem_inWideSlabFamily.mp hi).1

/-- The **wide slab of a plank**: the `φ × R × R` prism with the plank's own centre and frame.  This
is the wide analogue of `Plank.toSlab`, and the witness that a plank belongs to the wide slab family
of *some* slab at every legal thickness. -/
def toWideSlab (P : Plank a b hab hb1) (φ R : ℝ≥0) (hφR : φ ≤ R) : Prism3D φ R R hφR le_rfl where
  toPrismNDim := PrismNDim.mk' P.center P.basis ![φ, R, R]
  thicknesses_eq := PrismNDim.thicknesses_mk' _ _ _

@[simp] theorem toWideSlab_center (P : Plank a b hab hb1) (φ R : ℝ≥0) (hφR : φ ≤ R) :
    (P.toWideSlab φ R hφR).center = P.center := rfl

@[simp] theorem toWideSlab_basis (P : Plank a b hab hb1) (φ R : ℝ≥0) (hφR : φ ≤ R) :
    (P.toWideSlab φ R hφR).basis = P.basis := rfl

/-- Every plank belongs to the exact wide slab family of its own wide slab, at any thickness
`φ ≥ a` and long half-width `R ≥ 1`.  This is what makes the wide slab hypothesis of GWZ Lemma 6.1
non-vacuous, and it is the input to the low-multiplicity branch (GWZ Remark 6.3). -/
theorem mem_inWideSlabFamily_toWideSlab {s : Finset ι} {V : ι → Plank a b hab hb1} {i : ι}
    (hi : i ∈ s) {φ R : ℝ≥0} (hφa : a ≤ φ) (hR1 : 1 ≤ R) (hφR : φ ≤ R) :
    i ∈ inWideSlabFamily s V ((V i).toWideSlab φ R hφR) := by
  rw [mem_inWideSlabFamily]
  refine ⟨hi, ?_, ?_⟩
  · intro x hx
    rw [((V i).toWideSlab φ R hφR).mem_carrier_iff]
    rw [(V i).mem_carrier_iff] at hx
    intro j
    refine (hx j).trans ?_
    rw [(V i).thicknesses_eq, ((V i).toWideSlab φ R hφR).thicknesses_eq, NNReal.coe_le_coe]
    fin_cases j
    · exact hφa
    · exact hb1.trans hR1
    · exact hR1
  · rw [Prism3D.angle_def, toWideSlab_basis, real_inner_self_eq_norm_sq, (V i).basis.norm_eq_one,
      one_pow, abs_one, Real.arccos_one]
    exact NNReal.coe_nonneg φ


/-- The **wide slab at a prescribed centre and frame**.  GWZ Lemma 6.13 hands back its selected
slabs as values of an abstract function, so nothing is known about where their centres sit; the
comparison slab of the window-aware bridge is therefore recentred at a plank of the family, keeping
only the slab's *frame*. -/
def wideSlabAt (c : EuclideanSpace ℝ (Fin 3))
    (basis : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))) (φ R : ℝ≥0) (hφR : φ ≤ R) :
    Prism3D φ R R hφR le_rfl where
  toPrismNDim := PrismNDim.mk' c basis ![φ, R, R]
  thicknesses_eq := PrismNDim.thicknesses_mk' _ _ _

@[simp] theorem wideSlabAt_center (c : EuclideanSpace ℝ (Fin 3))
    (basis : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))) (φ R : ℝ≥0) (hφR : φ ≤ R) :
    (wideSlabAt c basis φ R hφR).center = c := rfl

@[simp] theorem wideSlabAt_basis (c : EuclideanSpace ℝ (Fin 3))
    (basis : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))) (φ R : ℝ≥0) (hφR : φ ≤ R) :
    (wideSlabAt c basis φ R hφR).basis = basis := rfl

/-- The angle with a recentred wide slab of `S`'s frame is the angle with `S`. -/
theorem angle_wideSlabAt {a' b' c' : ℝ≥0} {hab' : a' ≤ b'} {hbc' : b' ≤ c'}
    (Q : Prism3D a' b' c' hab' hbc') {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1)
    (c : EuclideanSpace ℝ (Fin 3)) (φ R : ℝ≥0) (hφR : φ ≤ R) :
    Prism3D.angle Q (wideSlabAt c S.basis φ R hφR) = Prism3D.angle Q S := by
  rw [Prism3D.angle_def, Prism3D.angle_def, wideSlabAt_basis]

/-- **Window-aware containment, recentred.**  A plank of the window contained in the `Cset`-dilation
of `S` lies in the wide slab of `S`'s frame centred at *any* point `c` of that dilation which is
itself in the window, once `2 · Cset · θ ≤ φ` and `2r ≤ R`.  The thin coordinate is paid for twice
(once for the plank, once for the recentring); the two long coordinates come from the window. -/
theorem carrier_subset_wideSlabAt_of_window {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1)
    (P : Plank a b hab hb1) {Cset : ℝ≥0} {r : ℝ} {c : EuclideanSpace ℝ (Fin 3)}
    (hdil : (P.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      (S.toPrismNDim.dilation Cset).carrier)
    (hc : c ∈ (S.toPrismNDim.dilation Cset).carrier)
    (hwin : (P.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ Metric.closedBall 0 r)
    (hcwin : ‖c‖ ≤ r) {φ R : ℝ≥0} (hφR : φ ≤ R)
    (hφ : 2 * (Cset * θ) ≤ φ) (hR : 2 * r ≤ (R : ℝ)) :
    (P.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ (wideSlabAt c S.basis φ R hφR).carrier := by
  intro x hx
  rw [(wideSlabAt c S.basis φ R hφR).mem_carrier_iff]
  have hxr : ‖x‖ ≤ r := by
    have hxwin := hwin hx
    rw [Metric.mem_closedBall, dist_zero_right] at hxwin
    exact hxwin
  have hlong : ∀ i, |S.basis.repr (x -ᵥ c) i| ≤ (R : ℝ) := by
    intro i
    calc
      |S.basis.repr (x -ᵥ c) i| ≤ dist x c := by
        rw [S.basis.repr_apply_apply, dist_eq_norm, ← vsub_eq_sub]
        refine le_trans (abs_real_inner_le_norm _ _) ?_
        rw [S.basis.norm_eq_one i, one_mul]
      _ ≤ ‖x‖ + ‖c‖ := by
        rw [dist_eq_norm]
        exact norm_sub_le _ _
      _ ≤ r + r := by exact add_le_add hxr hcwin
      _ = 2 * r := by ring
      _ ≤ (R : ℝ) := hR
  intro i
  fin_cases i
  · have h0dil := ((S.toPrismNDim.dilation Cset).mem_carrier_iff x).mp (hdil hx)
    have h0c := ((S.toPrismNDim.dilation Cset).mem_carrier_iff c).mp hc
    have hthin1 : |S.basis.repr (x -ᵥ S.center) 0| ≤ (Cset * θ : ℝ) :=
      (h0dil 0).trans (by rw [PrismNDim.dilation_thicknesses, S.thicknesses_eq]; simp)
    have hthin2 : |S.basis.repr (S.center -ᵥ c) 0| ≤ (Cset * θ : ℝ) := by
      rw [show S.basis.repr (S.center -ᵥ c) 0 = -(S.basis.repr (c -ᵥ S.center) 0) by
        rw [← neg_vsub_eq_vsub_rev, map_neg]
        rfl, abs_neg]
      exact (h0c 0).trans (by rw [PrismNDim.dilation_thicknesses, S.thicknesses_eq]; simp)
    have hdecomp : S.basis.repr (x -ᵥ c) 0
        = S.basis.repr (x -ᵥ S.center) 0 + S.basis.repr (S.center -ᵥ c) 0 := by
      rw [(vsub_add_vsub_cancel x S.center c).symm, map_add]; rfl
    have hthin : |S.basis.repr (x -ᵥ c) 0| ≤ (φ : ℝ) := by
      rw [hdecomp]
      exact (abs_add_le _ _).trans (by
        have hs : |S.basis.repr (x -ᵥ S.center) 0| + |S.basis.repr (S.center -ᵥ c) 0|
            ≤ (Cset * θ : ℝ) + (Cset * θ : ℝ) := add_le_add hthin1 hthin2
        exact hs.trans (by rw [← two_mul]; exact_mod_cast hφ))
    exact hthin
  · exact hlong 1
  · exact hlong 2

/-- **The window-aware slab non-concentration bridge, recentred at a member of the family.**  This
is the form GWZ Lemma 6.1 consumes: the selected slab `S` of Lemma 6.13 is opaque, so the comparison
slab is built from `S`'s frame and the centre `c` of one plank assigned to `S`.  Loss
`2 * max Cset Cang`. -/
theorem card_le_of_wideSlabNonconcentration_recentred {Cset Cang R : ℝ≥0} (hCang : 1 ≤ Cang)
    (hR1 : 1 ≤ R) (s : Finset ι) (V : ι → Plank a b hab hb1) {η γ : ℝ}
    (ha : 0 < a) (hη : 0 ≤ η) (hγ1 : γ ≤ 1)
    (hwide : ∀ (φ : ℝ≥0) (hφR : φ ≤ R), a / b ≤ φ → ∀ Sφ : Prism3D φ R R hφR le_rfl,
      ((inWideSlabFamily s V Sφ).card : ℝ≥0) ≤ a ^ (-η) * φ ^ γ * (s.card : ℝ≥0))
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} (hθ : a / b ≤ θ) (S : Slab θ hθ1)
    {r : ℝ} (hRr : 2 * r ≤ (R : ℝ)) {c : EuclideanSpace ℝ (Fin 3)}
    (hc : c ∈ (S.toPrismNDim.dilation Cset).carrier) (hcwin : ‖c‖ ≤ r)
    (G : Finset ι) (hG : G ⊆ s)
    (hdil : ∀ i ∈ G, (V i).carrier ⊆ (S.toPrismNDim.dilation Cset).carrier)
    (hang : ∀ i ∈ G, Prism3D.angle (V i) S ≤ (Cang : ℝ) * (θ : ℝ))
    (hwin : ∀ i ∈ G, (V i).carrier ⊆ Metric.closedBall 0 r) :
    (G.card : ℝ≥0) ≤ 2 * max Cset Cang * a ^ (-η) * θ ^ γ * (s.card : ℝ≥0) := by
  let Cctrl : ℝ≥0 := 2 * max Cset Cang
  have hCctrl1 : 1 ≤ Cctrl := by
    calc
      1 ≤ max Cset Cang := le_trans hCang (le_max_right Cset Cang)
      _ ≤ 2 * max Cset Cang := le_mul_of_one_le_left (by positivity) (by norm_num)
      _ = Cctrl := rfl
  have ha1 : a ≤ 1 := hab.trans hb1
  by_cases hsmall : Cctrl * θ ≤ R
  · -- small regime: use the recentred wide slab at scale Cctrl * θ
    have habφ : a / b ≤ Cctrl * θ := by
      exact hθ.trans (by simpa using mul_le_mul' hCctrl1 le_rfl)
    have h2C : 2 * Cset ≤ Cctrl := by
      calc
        2 * Cset ≤ 2 * max Cset Cang := mul_le_mul' le_rfl (le_max_left Cset Cang)
        _ = Cctrl := rfl
    have hφ : 2 * (Cset * θ) ≤ Cctrl * θ := by
      calc
        2 * (Cset * θ) = 2 * Cset * θ := by ring
        _ ≤ Cctrl * θ := mul_le_mul' h2C le_rfl
    have hsub : G ⊆ inWideSlabFamily s V (wideSlabAt c S.basis (Cctrl * θ) R hsmall) := by
      intro i hi
      rw [mem_inWideSlabFamily]
      refine ⟨hG hi, ?_, ?_⟩
      · exact carrier_subset_wideSlabAt_of_window S (V i) (hdil i hi) hc (hwin i hi) hcwin hsmall
          hφ hRr
      · have hangφ : Prism3D.angle (V i) S ≤ ((Cctrl * θ : ℝ≥0) : ℝ) := by
          have hCangC : Cang ≤ Cctrl := by
            calc
              Cang ≤ max Cset Cang := le_max_right Cset Cang
              _ ≤ 2 * max Cset Cang := le_mul_of_one_le_left (by positivity) (by norm_num)
              _ = Cctrl := rfl
          have hCangθ : Cang * θ ≤ Cctrl * θ := mul_le_mul' hCangC le_rfl
          exact (hang i hi).trans (by exact_mod_cast hCangθ)
        rw [angle_wideSlabAt (V i) S c (Cctrl * θ) R hsmall]
        exact hangφ
    have hbind : (G.card : ℝ≥0) ≤
        ((inWideSlabFamily s V (wideSlabAt c S.basis (Cctrl * θ) R hsmall)).card : ℝ≥0) := by
      exact_mod_cast (Finset.card_le_card hsub)
    have hw : ((inWideSlabFamily s V (wideSlabAt c S.basis (Cctrl * θ) R hsmall)).card : ℝ≥0) ≤
        a ^ (-η) * (Cctrl * θ) ^ γ * (s.card : ℝ≥0) :=
      hwide (Cctrl * θ) hsmall habφ (wideSlabAt c S.basis (Cctrl * θ) R hsmall)
    calc
      (G.card : ℝ≥0) ≤
          ((inWideSlabFamily s V (wideSlabAt c S.basis (Cctrl * θ) R hsmall)).card : ℝ≥0) := hbind
      _ ≤ a ^ (-η) * (Cctrl * θ) ^ γ * (s.card : ℝ≥0) := hw
      _ = a ^ (-η) * (Cctrl ^ γ * θ ^ γ) * (s.card : ℝ≥0) := by
        rw [NNReal.mul_rpow]
      _ = (Cctrl ^ γ * a ^ (-η) * θ ^ γ) * (s.card : ℝ≥0) := by ring
      _ ≤ (Cctrl * a ^ (-η) * θ ^ γ) * (s.card : ℝ≥0) := by
        have hγc : Cctrl ^ γ ≤ Cctrl := by
          simpa [NNReal.rpow_one] using NNReal.rpow_le_rpow_of_exponent_le hCctrl1 hγ1
        have hmid : Cctrl ^ γ * a ^ (-η) * θ ^ γ ≤ Cctrl * a ^ (-η) * θ ^ γ :=
          mul_le_mul' (mul_le_mul' hγc le_rfl) le_rfl
        exact mul_le_mul' hmid le_rfl
  · -- large regime: R < Cctrl * θ, trivial bound card ≤ s.card suffices
    have hlarge : R < Cctrl * θ := lt_of_not_ge hsmall
    have h1lt : 1 < Cctrl * θ := lt_of_le_of_lt hR1 hlarge
    have hcards : (G.card : ℝ≥0) ≤ (s.card : ℝ≥0) := by
      exact_mod_cast (Finset.card_le_card hG)
    have hprod : 0 < Cctrl * θ := lt_trans (by norm_num : (0 : ℝ≥0) < 1) h1lt
    have hposC : 0 < Cctrl := lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 1) hCctrl1
    have hθpos : 0 < θ := (mul_pos_iff_of_pos_left hposC).mp hprod
    have haη1 : 1 ≤ a ^ (-η) := by
      have h0 : a ^ (0 : ℝ) ≤ a ^ (-η) :=
        NNReal.rpow_le_rpow_of_exponent_ge ha ha1 (by linarith : -η ≤ 0)
      simpa using h0
    have hθγ : θ ≤ θ ^ γ := by
      simpa [NNReal.rpow_one] using NNReal.rpow_le_rpow_of_exponent_ge hθpos hθ1 hγ1
    have hscalar : 1 ≤ Cctrl * a ^ (-η) * θ ^ γ := by
      have hθle : θ ≤ a ^ (-η) * θ ^ γ := by
        exact hθγ.trans (le_mul_of_one_le_left (by positivity) haη1)
      have hCθ : Cctrl * θ ≤ Cctrl * (a ^ (-η) * θ ^ γ) :=
        mul_le_mul_of_nonneg_left hθle (by positivity : (0 : ℝ≥0) ≤ Cctrl)
      calc
        1 ≤ Cctrl * θ := le_of_lt h1lt
        _ ≤ Cctrl * (a ^ (-η) * θ ^ γ) := hCθ
        _ = Cctrl * a ^ (-η) * θ ^ γ := by rw [← mul_assoc]
    calc
      (G.card : ℝ≥0) ≤ (s.card : ℝ≥0) := hcards
      _ ≤ Cctrl * a ^ (-η) * θ ^ γ * (s.card : ℝ≥0) := by
        exact le_mul_of_one_le_left (by positivity) hscalar


/-! ### The representative-anchor family of GWZ Lemma 6.13

The slab assignment of GWZ Lemma 6.13 (`Plank.exists_pairwiseDistinct_slabAssignment`) assigns to
each active thickened representative `Q ∈ R.indexSet` a *selected* candidate slab, the candidates
being `Q ↦ (V (rep Q)).toSlab θ hθ1` for an anchor index `rep Q ∈ s` with `R.repr (rep Q) = Q`.  The
representatives assigned to one selected slab `S` therefore carry much more structure than a general
member of `inSlabFamilyC`: the anchor plank lies *exactly* in its own candidate slab, and that
candidate slab is not essentially distinct from `S`.  The three results below turn that structure
into a cardinality statement about anchors, with **absolute** controlled constants. -/


open scoped Classical in
/-- **The `1/N` step of GWZ Lemma 6.1.**  Every plank of `s'` whose representative is assigned to the
slab `S` lies in `G` (in the application, `G` is the controlled subfamily of `S` supplied by GWZ
Lemma 6.13), and every representative fibre has at least `L` elements (in the application
`L = N / cN`).  Since the fibres are disjoint, the number of representatives assigned to `S` is at
most `L⁻¹ · |G|`.

Keeping this factor is what makes the `N` of Lemma 6.13's Item 4 cancel: Item 4 contributes `a·N/(b·θ)`
and the representative density estimate contributes `(b·θ/(a·N))^(1-β)`, so the cardinality estimate
must contribute `N^(-β)`. -/
theorem card_assignedRepr_mul_le_card_of_fibre_lb
    {s' : Finset ι} {V : ι → Plank a b hab hb1} {θ : ℝ≥0} {hθ1 : θ ≤ 1} {cThk : ℝ≥0}
    (R : ThickenedRepr s' V θ hθ1 cThk) (slabOf : ThickenedPlank θ b hθ1 hb1 → Slab θ hθ1)
    {L : ℝ} (_hL0 : 0 ≤ L)
    (hfib : ∀ Q ∈ R.indexSet, L ≤ (((s'.filter fun i => R.repr i = Q).card : ℕ) : ℝ))
    (S : Slab θ hθ1) (G : Finset ι)
    (hsub : ∀ i ∈ s', slabOf (R.repr i) = S → i ∈ G) :
    L * (((R.indexSet.filter (fun Q => slabOf Q = S)).card : ℕ) : ℝ) ≤ ((G.card : ℕ) : ℝ) := by
  classical
  set A := R.indexSet.filter (fun Q => slabOf Q = S) with hA
  set F := s'.filter (fun i => slabOf (R.repr i) = S) with hF
  -- 1. fibrewise decomposition of F over A
  have hmap : ∀ i ∈ F, R.repr i ∈ A := by
    intro i hi
    rw [hF, Finset.mem_filter] at hi
    exact Finset.mem_filter.mpr ⟨R.repr_mem_indexSet hi.1, hi.2⟩
  have hcardF : F.card = ∑ Q ∈ A, (F.filter fun i => R.repr i = Q).card :=
    Finset.card_eq_sum_card_fiberwise hmap
  -- 2. on A the two filters agree
  have hfilter : ∀ Q ∈ A, (F.filter fun i => R.repr i = Q) = s'.filter (fun i => R.repr i = Q) := by
    intro Q hQ
    rw [hA, Finset.mem_filter] at hQ
    ext i
    simp only [hF, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hi, -⟩, hrepr⟩; exact ⟨hi, hrepr⟩
    · rintro ⟨hi, hrepr⟩; exact ⟨⟨hi, by rw [hrepr]; exact hQ.2⟩, hrepr⟩
  -- 3. each fibre has at least L elements, so L * A.card ≤ F.card
  have hsum : L * (A.card : ℝ) ≤ (F.card : ℝ) := by
    calc
      L * (A.card : ℝ) = ∑ Q ∈ A, L := by simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ Q ∈ A, (((F.filter fun i => R.repr i = Q).card : ℕ) : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro Q hQ
        rw [hfilter Q hQ]
        exact hfib Q (by
          rw [hA] at hQ
          exact (Finset.mem_filter.mp hQ).1)
      _ = (F.card : ℝ) := by exact_mod_cast hcardF.symm
  -- 4. F ⊆ G
  have hFG : F ⊆ G := by
    intro i hi
    rw [hF, Finset.mem_filter] at hi
    exact hsub i hi.1 hi.2
  exact hsum.trans (by exact_mod_cast (Finset.card_le_card hFG))

open scoped Classical in
/-- **The assigned-representative cardinality bound of GWZ Lemma 6.1, with the crucial `1/N`.**

Combining the fibre count (`Plank.card_assignedRepr_mul_le_card_of_fibre_lb`) with the window-aware
slab bridge (`Plank.card_le_of_wideSlabNonconcentration_recentred`): if every plank of the refined
family `s'` lies in the controlled subfamily of the slab assigned to its representative, and every
representative fibre has at least `L` members, then the number of representatives assigned to a fixed
slab `S` is at most `L⁻¹ · 2 · max Cset Cang · a ^ (-η) · θ ^ γ · |s|`.

This is the step where the `N` of Lemma 6.13 Item 4 is paid back: `L = N / cN`. -/
theorem card_assignedRepr_mul_le_of_wideSlabNonconcentration
    {Cset Cang R : ℝ≥0} (hCang : 1 ≤ Cang) (hR1 : 1 ≤ R)
    {s s' : Finset ι} (hs' : s' ⊆ s) (V : ι → Plank a b hab hb1) {η γ : ℝ}
    (ha : 0 < a) (hη : 0 ≤ η) (hγ1 : γ ≤ 1)
    (hwide : ∀ (φ : ℝ≥0) (hφR : φ ≤ R), a / b ≤ φ → ∀ Sφ : Prism3D φ R R hφR le_rfl,
      ((inWideSlabFamily s V Sφ).card : ℝ≥0) ≤ a ^ (-η) * φ ^ γ * (s.card : ℝ≥0))
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} (hθ : a / b ≤ θ) {cThk : ℝ≥0}
    (Rep : ThickenedRepr s' V θ hθ1 cThk)
    (slabOf : ThickenedPlank θ b hθ1 hb1 → Slab θ hθ1)
    (hslabmem : ∀ i ∈ s', i ∈ inSlabFamilyC Cset Cang s' V (slabOf (Rep.repr i)))
    {L : ℝ} (hL0 : 0 ≤ L)
    (hfib : ∀ Q ∈ Rep.indexSet, L ≤ (((s'.filter fun i => Rep.repr i = Q).card : ℕ) : ℝ))
    {r : ℝ} (hRr : 2 * r ≤ (R : ℝ)) (hwin : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 r)
    (S : Slab θ hθ1) :
    L * (((Rep.indexSet.filter (fun Q => slabOf Q = S)).card : ℕ) : ℝ)
      ≤ ((2 * max Cset Cang * a ^ (-η) * θ ^ γ * (s.card : ℝ≥0) : ℝ≥0) : ℝ) := by
  classical
  set G := inSlabFamilyC Cset Cang s' V S with hG
  -- Step 1: the fibre count (the 1/N step)
  have hsub : ∀ i ∈ s', slabOf (Rep.repr i) = S → i ∈ G := by
    intro i hi hEq
    have hmem : i ∈ inSlabFamilyC Cset Cang s' V S := by
      simpa [hEq] using hslabmem i hi
    simpa [hG] using hmem
  have hstep1 : L * (((Rep.indexSet.filter (fun Q => slabOf Q = S)).card : ℕ) : ℝ)
      ≤ ((G.card : ℕ) : ℝ) :=
    card_assignedRepr_mul_le_card_of_fibre_lb Rep slabOf hL0 hfib S G hsub
  -- Step 2: the window-aware slab bridge for G, recentred at a plank of G
  have hGs : G ⊆ s := by
    intro i hi
    have hi' : i ∈ inSlabFamilyC Cset Cang s' V S := by simpa [hG] using hi
    exact hs' (inSlabFamilyC_subset hi')
  rcases Finset.eq_empty_or_nonempty G with hGe | ⟨i₁, hi₁⟩
  · -- G empty: step 1 already gives `L * card ≤ 0 ≤ RHS`
    rw [hGe] at hstep1
    simp at hstep1
    exact hstep1.trans (NNReal.coe_nonneg _)
  · have hdil : ∀ i ∈ G, (V i).carrier ⊆ (S.toPrismNDim.dilation Cset).carrier := by
      intro i hi
      have hi' : i ∈ inSlabFamilyC Cset Cang s' V S := by simpa [hG] using hi
      exact (mem_inSlabFamilyC.mp hi').2.1
    have hang : ∀ i ∈ G, Prism3D.angle (V i) S ≤ (Cang : ℝ) * (θ : ℝ) := by
      intro i hi
      have hi' : i ∈ inSlabFamilyC Cset Cang s' V S := by simpa [hG] using hi
      exact (mem_inSlabFamilyC.mp hi').2.2
    have hwinG : ∀ i ∈ G, (V i).carrier ⊆ Metric.closedBall 0 r := by
      intro i hi
      exact hwin i (hGs hi)
    -- the recentring point: the centre of the plank `V i₁`
    have hc : (V i₁).center ∈ (S.toPrismNDim.dilation Cset).carrier :=
      hdil i₁ hi₁ (V i₁).center_mem_carrier
    have hcwin : ‖(V i₁).center‖ ≤ r := by
      have hmem : (V i₁).center ∈ Metric.closedBall 0 r :=
        hwinG i₁ hi₁ (V i₁).center_mem_carrier
      rw [Metric.mem_closedBall, dist_zero_right] at hmem
      exact hmem
    have hstep2 : (G.card : ℝ≥0) ≤ 2 * max Cset Cang * a ^ (-η) * θ ^ γ * (s.card : ℝ≥0) :=
      card_le_of_wideSlabNonconcentration_recentred hCang hR1 s V ha hη hγ1 hwide hθ S hRr
        hc hcwin G hGs hdil hang hwinG
    -- combine
    exact hstep1.trans (by exact_mod_cast hstep2)


end Plank

end

end

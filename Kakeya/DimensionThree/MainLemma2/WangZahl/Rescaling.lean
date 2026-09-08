/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.WangZahl.EToD
public import Kakeya.DimensionThree.Prism
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
The Wang--Zahl rescaling map `phi_W` and the rescaled family `U^W`.

Source: Wang--Zahl
  * Definition `defnPhiW` : the affine map `phi_W` taking the outer John
    ellipsoid of a convex set `W` to the unit ball, with the `j`-th axis sent
    to the `x_j` axis;
  * the definition immediately after : `U[W]`, `U^W = phi_W(U[W])` and
    the transported shading `Y^W`;
  * Definition `defnOfCover` : covers, `K`-almost partitioning covers,
    `K`-balanced covers;
  * Definition `defnConvexPrime`  and Remark
    `remarksFollowingConvexWolffDefn` : the Katz--Tao and Frostman Wolff
    constants `CKT`, `CFC`, `FS` of an arbitrary family of convex sets;
  * definitions of factoring from above and below: `W` factors `U` from above / from below.

The `WangZahl` namespace previously had no rescaling map and no `U^W` at all,
which is why Definition `convexAtEveryScaleFromAssouadPaper`  and
Proposition `tubeTricotProp`  were not statable.  This file supplies the
vocabulary; the two source statements are in `TubeTrichotomy.lean`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory

namespace Kakeya.WangZahl

noncomputable section

universe u

/-! ### The rescaling frame

Wang--Zahl Definition `defnPhiW`  attaches to a convex set `W` the affine
map `phi_W` that takes the outer John ellipsoid of `W` to the unit ball, in
such a way that the `j`-th axis of that ellipsoid (ordered by increasing
length) goes to the `x_j` axis of `R^n`.

The John ellipsoid itself is not available in this project, and the source uses
it only through the two properties that (a) `phi_W` is affine with the
prescribed axis behaviour, and (b) `phi_W(W)` is comparable to the unit ball.
Every convex set the source actually rescales -- a `rho`-tube in the every-scale definition
and in clause (B) of Proposition `tubeTricotProp`, an `a x b x 1` prism in clause (C) -- is a
*box*: it carries a distinguished centre, an orthonormal frame of axis
directions and three half-widths.  `Frame3` records exactly that data, and
`Frame3.map` is the corresponding `phi_W`, normalised so that the box goes to
the cube `[-1,1]^3` rather than to the unit ball.  The two normalisations
differ by the fixed linear map `sqrt 3`-scaling, which is inside the source's
own `~`.
-/

/-- A **rescaling frame** in `R^3`: a centre, an orthonormal frame of axis
directions, and three positive half-widths.  This is the data that Wang--Zahl
Definition `defnPhiW`  reads off the outer John ellipsoid of a convex
set. -/
structure Frame3 where
  /-- The centre of the box. -/
  center : Space3
  /-- The axis directions, in the source's increasing-length order. -/
  basis : OrthonormalBasis (Fin 3) ℝ Space3
  /-- The half-widths along the axes. -/
  len : Fin 3 → ℝ
  /-- The half-widths are positive. -/
  len_pos : ∀ i, 0 < len i

namespace Frame3

variable (F : Frame3)

/-- The box cut out by a frame: the source's `W` in Definition `defnPhiW`. -/
def box : Set Space3 := {z | ∀ i, |F.basis.repr (z - F.center) i| ≤ F.len i}

/-- The diagonal part of `phi_W`, in the coordinates of the frame: the linear
map sending the `j`-th axis direction of the frame to `(len j)⁻¹` times the
`j`-th standard basis vector of `R^3`. -/
def linearMap : Space3 →ₗ[ℝ] Space3 where
  toFun v := (WithLp.toLp 2) fun i => F.basis.repr v i / F.len i
  map_add' v w := by
    ext i
    simp [add_div]
  map_smul' a v := by
    ext i
    simp [mul_div_assoc]

/-- **Wang--Zahl `phi_W`** (Definition `defnPhiW`) for a box: the affine
map taking the centre to the origin and the `j`-th axis of the box to the
`x_j` axis, normalised so that the box becomes the cube `[-1,1]^3`. -/
def map (z : Space3) : Space3 := F.linearMap (z - F.center)

variable {F}

@[simp] theorem linearMap_apply (v : Space3) (i : Fin 3) :
    F.linearMap v i = F.basis.repr v i / F.len i := rfl

@[simp] theorem map_apply (z : Space3) (i : Fin 3) :
    F.map z i = F.basis.repr (z - F.center) i / F.len i := rfl

/-! ### `phi_W` is an affine bijection, and how it moves volume -/

/-- The diagonal part of `phi_W` in standard coordinates. -/
def diagMap (len : Fin 3 → ℝ) : Space3 →ₗ[ℝ] Space3 where
  toFun v := (WithLp.toLp 2) fun i => v i / len i
  map_add' v w := by ext i; simp [add_div]
  map_smul' a v := by ext i; simp [mul_div_assoc]

@[simp] theorem diagMap_apply (len : Fin 3 → ℝ) (v : Space3) (i : Fin 3) :
    diagMap len v i = v i / len i := rfl

/-- `phi_W` as an affine map. -/
def affineMap (F : Frame3) : Space3 →ᵃ[ℝ] Space3 where
  toFun := F.map
  linear := F.linearMap
  map_vadd' p v := by
    show F.linearMap (v + p - F.center) = F.linearMap v + F.linearMap (p - F.center)
    rw [← map_add]
    congr 1
    abel

@[simp] theorem affineMap_apply (F : Frame3) (z : Space3) : F.affineMap z = F.map z := rfl

theorem convex_image (F : Frame3) {A : Set Space3} (hA : Convex ℝ A) :
    Convex ℝ (F.map '' A) := hA.affine_image F.affineMap

/-- The volume factor of `phi_W`. -/
noncomputable def volumeFactor (F : Frame3) : ℝ≥0∞ :=
  ENNReal.ofReal (∏ i, (F.len i)⁻¹)

end Frame3

/-! ### The frame of a tube

The convex sets Wang--Zahl rescales in Definition
`convexAtEveryScaleFromAssouadPaper`  and in clause (B) of Proposition
`tubeTricotProp`  are `rho`-tubes.  A `rho`-tube is a box: its axes are
any two unit vectors orthogonal to its direction, together with the direction
itself, and its half-widths are `rho, rho, 1/2 + rho` (the source's `rho x rho
x 1`, with the endpoint balls included).
-/

/-- Any unit vector of `R^3` is the last vector of some orthonormal basis. -/
theorem exists_orthonormalBasis_last {v : Space3} (hv : ‖v‖ = 1) :
    ∃ b : OrthonormalBasis (Fin 3) ℝ Space3, b 2 = v := by
  have hcard : Module.finrank ℝ Space3 = Fintype.card (Fin 3) := by simp [Space3]
  have hon : Orthonormal ℝ (Set.restrict ({2} : Set (Fin 3)) (fun _ : Fin 3 => v)) := by
    constructor
    · intro i; simpa using hv
    · rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
      exact absurd (Subtype.ext (hi.trans hj.symm)) hij
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq hcard
  exact ⟨b, hb 2 rfl⟩

/-- A choice of orthonormal basis of `R^3` whose last vector is the direction
of the tube `T`. -/
def tubeAxes {ρ : ℝ≥0} (T : Tube ρ Space3) : OrthonormalBasis (Fin 3) ℝ Space3 :=
  Classical.choose (exists_orthonormalBasis_last T.norm_direction)

/-- **The rescaling frame of a `rho`-tube**: centre at the midpoint of the
defining segment, axes as above, half-widths `rho, rho, 1/2 + rho`.  This is
the box the source's `phi_{T_rho}` normalises. -/
def tubeFrame3 {ρ : ℝ≥0} (hρ : 0 < ρ) (T : Tube ρ Space3) : Frame3 where
  center := T.center
  basis := tubeAxes T
  len := ![(ρ : ℝ), (ρ : ℝ), 1 / 2 + (ρ : ℝ)]
  len_pos := by
    intro i
    have hρ' : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ
    fin_cases i <;> simp <;> first | exact hρ | linarith

@[simp] theorem tubeFrame3_center {ρ : ℝ≥0} (hρ : 0 < ρ) (T : Tube ρ Space3) :
    (tubeFrame3 hρ T).center = T.center := rfl

@[simp] theorem tubeFrame3_basis {ρ : ℝ≥0} (hρ : 0 < ρ) (T : Tube ρ Space3) :
    (tubeFrame3 hρ T).basis = tubeAxes T := rfl

/-! ### The frame of a prism

Clause (C) of Proposition `tubeTricotProp`  rescales `a x b x 1`
prisms, so those need frames too.  A `Prism3D` already carries exactly the
data of a `Frame3`; note that the project's `Prism3D a b c` has *half*-widths
`a, b, c`, hence dimensions `2a x 2b x 2c` (this is the trap recorded in
`Plank.half_le_of_le_tube`), so the source's `a x b x 1` prism is the frame
with half-widths `a/2, b/2, 1/2`. -/

/-! ### Wolff constants of an arbitrary family of convex sets

Wang--Zahl Definition `defnConvexPrime`  and Remark
`remarksFollowingConvexWolffDefn`(A)  define `CKT`, `CFC` and `FS` for an
*arbitrary* collection `U` of convex subsets of `R^n`, not only for a family of
congruent `delta`-tubes.  That generality is exactly what the rescaled families
`U^W` need: `phi_W` of a `delta`-tube is not a tube, only a convex set.

The project's `katzTaoConvexWolffConstant`, `frostmanConvexWolffConstant` and
`frostmanSlabWolffConstant` are the tube specialisations, in which the source's
`sum_{U in U[W]} |U|` has been divided by the common tube volume `|T|`.  The
versions below are the source's literal, undivided ones; the two agree on tube
families (`katzTaoConvexWolffConstantSets_eq`,
`frostmanConvexWolffConstantSets_eq`, `frostmanSlabWolffConstantSets_eq`). -/

/-- `U^W`, Wang--Zahl : the carriers of `U[W]` pushed forward by
`phi_W`. -/
def rescaleCarriers {ι : Type u} (F : Frame3) (U : ι → Set Space3) : ι → Set Space3 :=
  fun i => F.map '' U i

@[simp] theorem rescaleCarriers_apply {ι : Type u} (F : Frame3) (U : ι → Set Space3)
    (i : ι) : rescaleCarriers F U i = F.map '' U i := rfl

/-- A Wang--Zahl slab is a convex test set: it is the intersection of the unit
ball with a closed thickening of an affine subspace. -/
def SlabTestSet.toConvexTestSet (W : SlabTestSet) : ConvexTestSet where
  carrier := W.carrier
  convex_carrier := by
    rw [SlabTestSet.carrier]
    exact (convex_closedBall (0 : Space3) 1).inter
      (W.plane.carrier.convex.cthickening _)

@[simp] theorem SlabTestSet.toConvexTestSet_carrier (W : SlabTestSet) :
    W.toConvexTestSet.carrier = W.carrier := rfl

/-! ### The tube specialisations agree with the general definitions -/

/-- The convex test set obtained by pushing a convex test set forward by
`phi_W`. -/
def ConvexTestSet.push (F : Frame3) (V : ConvexTestSet) : ConvexTestSet where
  carrier := F.map '' V.carrier
  convex_carrier := F.convex_image V.convex_carrier

/-! ### How the Wolff constants of `U^W` relate to those of `U`

The source normalises `CKT` by `|W|` on both sides, so it is *invariant* under
the affine rescaling; `CFC` carries an extra copy of `sum |U|` on the right, so
it picks up exactly one factor of the volume Jacobian.  (Compare Remark
`remarksFollowingConvexWolffDefn`(C), where the source discusses the
normalisation that makes these quantities transform naturally.)

Note that the family index set is *not* cut down here: the source's `U^W` is
this construction applied to `U[W]` (`subfamilyIn`), and these identities hold
for any index family. -/

end

end Kakeya.WangZahl

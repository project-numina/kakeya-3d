/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Geometry
public import Kakeya.DimensionThree.Plank.RepresentativeFrostman
public import Kakeya.DimensionThree.Plank.SlabAssignmentGeometry
public import Kakeya.DimensionThree.Plank.SlabTubeSelection
public import Kakeya.DimensionThree.Plank.SlabFibreFrostman
public import Kakeya.DimensionThree.Plank.SlabFibreTubes
public import Kakeya.DimensionThree.Plank.SlabFrostmanEstimate
public import Kakeya.DimensionThree.Plank.DilatedSlabTube
public import Kakeya.FrostmanConstant
public import Kakeya.PartialEstimates
public import Kakeya.Thickening

/-!
# GWZ Section 6 geometry: dependency lemmas for the Frostman plank estimate

This file states the geometry lemmas that the Frostman estimate for planks
(`Kakeya.FrostmanEstimate.plankEstimate`, GWZ Lemma 6.4) consumes.

The three lemmas consumed by GWZ Lemma 6.4 are stated here:
`thickenedRepresentativeFibreCardinality` (fibre concentration, `N ≲ Mθ`),
`frostmanThickenedSlabFibre` (local Frostman constant of an assigned slab fibre, S6G15, using the
scalar `Kakeya.frostmanConstant`), and `normaliseSlabFamilyToTubes` (the fixed-loss affine
slab-to-tube normalisation with comparable fullness/multiplicity/cardinality/Frostman).

All three carry their loss constants explicitly, and in the correct order: the representative
dilation `cThk`, the controlled slab-membership losses `Cset`, `Cang`, and the slab-fibre loss `Cfib`
are quantified *before* the constants that depend on them. Slab membership is the controlled
`Plank.inSlabFamilyC`, and the slab-fibre data is packaged as `Plank.SlabFibreGeometry`.

## Note on the normalisation window (repaired)

`PrismNDim.thicknesses` are *half*-widths, so for an `a × b × 1` plank with `a > 0` the constraint
`(V i).carrier ⊆ Metric.closedBall 0 1` is **unsatisfiable**: the long half-axis already has length
`1`, so its endpoint is at distance `1` from the centre, and any point displaced from it in a
transverse direction (possible because `a`, `b` are positive) is at distance `> 1` — concretely
`‖(a, 0, 1)‖ = √(1 + a²) > 1`.

Plank-level statements therefore use `Kakeya.plankWindowRadius` (an absolute constant, value `4`)
and the reference body `Kakeya.plankWindow`, with `Kakeya.plank_carrier_subset_plankWindow` and
`Kakeya.ShadedPlank.carrier_subset_plankWindow` as the producers' entry points. Tube-level
statements keep the unit ball, which a `δ`-tube of axis length `1` does fit; the one place where a
`b`-tube family is *produced* (`Plank.normaliseSlabFamilyToTubes` below) carries the explicit
small-scale hypothesis `b ≤ 1 / 4` that the containment needs.

No proof in Section 6 ever derived anything from the earlier vacuity, and none does now.

The boundedness field of `Plank.SlabFibreGeometry` avoids the problem locally: it asks only for
containment in `Metric.closedBall 0 (4 · Cfib)` with `1 ≤ Cfib`, which is what the 6.13 output can
actually supply for a thickened representative — the representative's centre lies in the working
window of radius `Plank.windowRadius = 4` and its `Cfib`-dilation adds at most `3 · Cfib`, so the
radius must be a fixed multiple of `Cfib`, not `Cfib` itself.

## Note on the shading carrier

`Plank.SlabFibreGeometry` deliberately separates the *geometric* representative prism `Q` (undilated,
and the only object asserted to be pairwise essentially distinct) from the *shading* body `Yθ Q`,
whose carrier is the controlled dilation `Q.dilation Cfib`. This is forced by the plank-to-tube
reduction, which only controls `(P i).carrier ⊆ ((Qθ (repr i)).dilation cThk).carrier`. Asserting
`(Yθ Q).carrier = Q.carrier` would be a claim the reduction cannot support.

## The one missing geometric input

`Plank.normaliseSlabFamilyToTubes` exports pairwise essential distinctness of the *cores*
`g '' Q.carrier` — an affine invariant of the fibre's own essential distinctness — but **not** of
the enclosing tubes, which inflate the cores by a fixed factor.
`Kakeya.FrostmanEstimate.multiplicity_bound` (GWZ Lemma 3.9) demands pairwise essential distinctness
of the tubes, and the gap between the two is exactly one anisotropic packing estimate, which the
repository does not contain:

> There is `MED : ℕ` depending only on the shape constants such that, for every finite family of
> prisms with thickness vector `(θb, b, 1)` that is pairwise essentially distinct and whose members
> all lie in a fixed dilation of a common `θ × 1 × 1` slab, the enclosing `b/8`-tube family
> satisfies `Kakeya.IsEDUpToMult u (fun k => (T k).carrier) MED`.

It is true — a tube sees only the direction and the transverse position of its core, and tangency
confines the fibre's roll angles to a range of size `≈ Cfib · θ`, so only boundedly many pairwise
essentially distinct cores can share one tube — and it is the prism analogue of GWZ Lemma 3.8
(`Kakeya.badAgainstSet_count_le_of_ED_thinBox`); but that lemma is stated for tubes and already
assumes the family is pairwise essentially distinct, so it cannot be reused as it stands.

Once it exists, `Kakeya.IsEDUpToMult.exists_pairwise_subset_with_weight` converts it into a
genuinely pairwise essentially distinct subfamily at the fixed cost `MED + 1` in shade mass, which
is all `Plank.frostmanSlabUnionVolumeLowerBound` needs: the union over a subfamily is contained in
the union over the whole family, so a lower bound for the subfamily is one for the family.

### The route to that estimate

The count has to be run at the *prism* level, where essential distinctness survives, and with the
anisotropic weights `w = (a, b, 1)`. Both halves already exist in the repository:

* `Plank.plank_not_essentiallyDistinct_of_pose_close`
  (`Kakeya/DimensionThree/Plank/ThickenedReprGeometry.lean`) is the anisotropic separation input —
  planks whose frame entries and centre offsets are small at the weights `w` are not essentially
  distinct;
* `Plank.card_le_of_pose_confined_separated` (`Kakeya/DimensionThree/Plank/SlabBoxAPI.lean`) is the
  metric packing engine in the twelve-dimensional pose space.

What is missing is the reduction of the first to a *single* pose map, so that the second applies.
The pose to use reads the frame entries of each prism against a fixed reference prism `P₀` with the
anisotropic normalisation `96 R · w p / w q`, and the centre coordinates with `48 R / w q`; the
confinement hypothesis must be the *symmetric* one,
`max (w j) (w k) · |⟪e j, e' k⟫| ≤ R · min (w j) (w k)`, since the one-sided form
`w j · |⟪e j, e' k⟫| ≤ R · w k` leaves the off-diagonal entry unconstrained when `w q ≫ w k` and the
cross terms of the frame expansion then fail to close. With those normalisations the three terms of
the expansion each contribute exactly `w k / 96` (resp. `w k / 48`), matching the `/32` and `/16`
demanded by `plank_not_essentiallyDistinct_of_pose_close`, and the packing engine returns
`(768 R² + 2) ^ 12`. Both directions of the symmetric confinement are available at the call site,
because the normalising map of `Plank.slabTube` is exactly the one that makes the fibre's anisotropy
isotropic. Contrast `Plank.ThickenedRepr.phi_packing_bound`, which uses the same engine but
normalises all twelve coordinates at the *shortest* half-width and so only reaches `a ^ (-12)`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Kakeya
open scoped NNReal Real Classical ENNReal

noncomputable section

namespace Plank


/-- **`N ≲ M θ`** (the form GWZ Lemma 6.4 consumes). For every `cThk ≥ 1` and every pigeonhole
constant `cN > 0` there is `Cfib ≥ 1` such that a uniform fibre scale `N` supplied by GWZ Lemma 6.13
— i.e. one with `N / cN ≤ |repr⁻¹(Q)|` for every active `Q` — obeys `N ≤ Cfib · M · θ`.

`Cfib = cN` works: the fibre bound of `Plank.thickenedRepresentativeFibreCardinality` gives
`|repr⁻¹(Q)| ≤ M θ` at any active `Q`, and the pigeonhole lower bound converts it. No power of
`b / a` appears anywhere. -/
theorem thickenedRepresentativeFibreScale (cThk cN : ℝ≥0) (_hcThk : 1 ≤ cThk) (hcN : 1 ≤ cN) :
    ∃ Cfib : ℝ≥0, 1 ≤ Cfib ∧
      ∀ {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}
        (s : Finset ι) (V : ι → Plank a b hab hb1) (θ : ℝ≥0) (hθ1 : θ ≤ 1)
        (R : ThickenedRepr s V θ hθ1 cThk) (M : ℝ≥0) (N : ℕ),
        0 < θ → a / b ≤ θ → 1 ≤ M →
        IsThickeningNonconcentrated s V (ThickenedRepr.fibreDilation cThk) M →
        R.indexSet.Nonempty →
        (∀ Q ∈ R.indexSet, (N : ℝ) / (cN : ℝ) ≤ ((s.filter (fun i => R.repr i = Q)).card : ℝ)) →
        (N : ℝ≥0) ≤ Cfib * M * θ := by
  refine ⟨cN, hcN, ?_⟩
  intro a b hab hb1 ι s V θ hθ1 R M N _ hθa _ hM hne hfib
  exact ThickenedRepr.fibreScale_le_of_nonconcentration R hM hθa
    (lt_of_lt_of_le zero_lt_one hcN) hne hfib

/-- **Local Frostman constant of an assigned slab fibre** (`lem:geometryLocalFrostmanThickened`,
S6G15). There are absolute constants `cThk ≥ 1` and `C_loc ≥ 1` with the following property. Let `R`
be a `cThk`-thickened representative ensemble with a `(Cset, Cang)`-controlled slab assignment `SA`;
write `𝒯 = R.indexSet` for all active representatives and, for a used slab `S`,
`𝒯_S = 𝒯.filter (SA.slabOf · = S)` for the representatives assigned to `S`. If the original plank
family is `C_F`-Frostman in the unit ball (`IsFrostmanIn … CF`), then, for every used slab `S` with a
nonempty fibre `𝒯_S`, the scalar Frostman constant of the fibre inside the slab obeys
`C_F(𝒯_S, S) ≤ C_loc · CF · (|𝒯| / |𝒯_S|) · |S|`.
The actual fibre quotient `|𝒯|/|𝒯_S|` is retained (it cancels after summing per-slab lower bounds),
so equal slab-fibre cardinalities are not needed.

Three honesty points about the quantifiers, two of which are corrections to the earlier interface.

* `cThk`, and the slab-assignment losses `Cset`, `Cang`, are quantified *before* `C_loc`: the
  transfer of a Frostman bound from the planks to their representatives costs a factor depending on
  all three, so a `C_loc` uniform in them would be false.
* The transfer also needs the representative fibres to have comparable sizes, which an arbitrary
  `ThickenedRepr` does not provide. That comparison (`hfibre`, the `N`/`cN` data produced by the
  dyadic pigeonhole `ThickenedRepr.pigeonholeThickenedMultiplicity_of_card_positive`) is therefore an
  explicit hypothesis rather than something silently assumed. **`cN` is now quantified before
  `C_loc`**: the transfer pays `cN` twice — once for the fibre lower bound and once for
  `|s| ≤ cN · N · |𝒯|` — so `C_loc` genuinely depends on it and a `cN`-uniform `C_loc` is false
  (make the fibres over `𝒯_S` minimal and the others maximal).
* **The plank family must be known to lie in the window.** `IsFrostmanIn s V plankWindow CF` on its
  own says nothing about a family sitting outside the window: with every plank outside, `CF = 0`
  satisfies the hypothesis while the left-hand side is positive. The containment hypothesis
  `∀ i ∈ s, (V i).toConvexSpaceBody ≤ plankWindow` is what turns the Frostman hypothesis into the
  usable `Δ_max(𝒫) · |B| ≤ CF · ∑ |P_i|`
  (`Kakeya.maxDensity_mul_volume_le_of_isFrostmanIn`); every producer has it.

The proof is `Plank.ThickenedRepr.frostmanConstant_slabFibre_le`, applied to the slab fibre as an
arbitrary subset of `R.indexSet` — the slab assignment `SA` plays no role beyond naming the fibre,
and no containment of the fibre in (a dilation of) `S` is used, because the `|S|` on the right is the
`|K|` of `Kakeya.frostmanConstant` rather than the result of a slab-versus-ball comparison. -/
theorem frostmanThickenedSlabFibre (cThk Cset Cang cN : ℝ≥0)
    (_hcThk : 1 ≤ cThk) (_hCset : 1 ≤ Cset) (_hCang : 1 ≤ Cang) (hcN : 1 ≤ cN) :
    ∃ Cloc : ℝ≥0, 1 ≤ Cloc ∧
      ∀ {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}
        (s : Finset ι) (V : ι → Plank a b hab hb1) (θ : ℝ≥0) (hθ1 : θ ≤ 1)
        (R : ThickenedRepr s V θ hθ1 cThk)
        (SA : SlabAssignment s V θ hθ1 R.repr Cset Cang)
        (N : ℕ) (CF : ℝ≥0∞),
        0 < a → 0 < θ → 1 ≤ N →
        (∀ Q ∈ R.indexSet,
          (N : ℝ) / (cN : ℝ) ≤ ((s.filter (fun i => R.repr i = Q)).card : ℝ) ∧
            ((s.filter (fun i => R.repr i = Q)).card : ℝ) ≤ (cN : ℝ) * (N : ℝ)) →
        (∀ i ∈ s, (V i).toConvexSpaceBody ≤ plankWindow) →
        ConvexSpaceBody.IsFrostmanIn s (fun i => (V i).toConvexSpaceBody) plankWindow CF →
        ∀ S ∈ SA.used, (R.indexSet.filter (fun Q => SA.slabOf Q = S)).Nonempty →
          Kakeya.frostmanConstant (R.indexSet.filter (fun Q => SA.slabOf Q = S))
              (fun Q => Q.toConvexSpaceBody) S.toConvexSpaceBody
            ≤ (Cloc : ℝ≥0∞) * CF *
                ((R.indexSet.card : ℝ≥0∞)
                  / ((R.indexSet.filter (fun Q => SA.slabOf Q = S)).card : ℝ≥0∞))
                * volume S.carrier := by
  classical
  refine ⟨1 + enlargementConst cThk * cN ^ 2, ?_, ?_⟩
  · exact le_self_add
  · intro a b hab hb1 ι s V θ hθ1 R SA N CF ha hθ hN hfibre hVwin hFrost S hSused hfibre_ne
    set T : Finset (ThickenedPlank θ b hθ1 hb1) := R.indexSet.filter (fun Q => SA.slabOf Q = S)
    have hT : T ⊆ R.indexSet := by
      dsimp [T]
      exact Finset.filter_subset _ _
    have hb : 0 < b := lt_of_lt_of_le ha hab
    have hlo : ∀ Q ∈ R.indexSet, (N : ℝ) / (cN : ℝ) ≤ ((s.filter fun i => R.repr i = Q).card : ℝ) :=
      fun Q hQ => (hfibre Q hQ).1
    have hhi : ∀ Q ∈ R.indexSet, ((s.filter fun i => R.repr i = Q).card : ℝ) ≤ (cN : ℝ) * (N : ℝ) :=
      fun Q hQ => (hfibre Q hQ).2
    have h_le := ThickenedRepr.frostmanConstant_slabFibre_le R hT hfibre_ne hN hcN ha hb hθ hlo hhi
      hVwin hFrost S
    have hconst : ((enlargementConst cThk * cN ^ 2 : ℝ≥0) : ℝ≥0∞) ≤
        ((1 + enlargementConst cThk * cN ^ 2 : ℝ≥0) : ℝ≥0∞) := by
      exact ENNReal.coe_le_coe.mpr (le_add_of_nonneg_left (zero_le (a := (1 : ℝ≥0))))
    calc
      Kakeya.frostmanConstant T (fun Q => Q.toConvexSpaceBody) S.toConvexSpaceBody
          ≤ ((enlargementConst cThk * cN ^ 2 : ℝ≥0) : ℝ≥0∞) * CF *
              ((R.indexSet.card : ℝ≥0∞) / (T.card : ℝ≥0∞)) * volume S.carrier := h_le
      _ ≤ ((1 + enlargementConst cThk * cN ^ 2 : ℝ≥0) : ℝ≥0∞) * CF *
              ((R.indexSet.card : ℝ≥0∞) / (T.card : ℝ≥0∞)) * volume S.carrier := by
        gcongr

/-! ## The slab-fibre interface, and where it now lives

`Plank.SlabFibreGeometry`, `Plank.fibreTubeConst` and their immediate consequences have moved to
`Kakeya.DimensionThree.Plank.SlabFibreGeometry`. That module sits *below* the anisotropic
ED-packing bridge (`Kakeya.DimensionThree.Plank.SlabTubeEssentialDistinctness`,
`…SlabFibreFrame`, `…SlabTubeSelection`), which needs the structure; this module imports the
bridge, so every one of those names is still in scope here and for all downstream consumers. -/


/-- **Per-slab Frostman volume lower bound** (analysis leaf for GWZ Lemma 6.4).
For every `ε > 0`, every per-slab fullness constant `c2 > 0` and every slab-fibre loss `Cfib ≥ 1`
there are `η, b₀ > 0` and a constant `K > 0` with the following property. Consider one used slab `S`
at angle `θ` and the fibre `fibre ⊆ 𝒯` of thickened representative prisms assigned to it, shaded by
`Yθ`, with the slab-fibre geometry of `Plank.SlabFibreGeometry`, fullness `≥ c2·a^(4η)`, and with the
local Frostman constant of the fibre inside `S` controlled by `Cloc·CF·(|𝒯|/|fibre|)·|S|`. Applying the
affine slab-to-tube normalisation and the generalized (τ-flexible) Frostman tube estimate at scale
`b` gives the per-slab union-volume lower bound (up to the loss `K`)
`a^ε · CF^(β/2-1) · b^(2β) · (b²)^(β/2) · θ^(β/2) · |𝒯|^(β/2-1) · |fibre| ≤ K · |U(fibre, Yθ)|`.
This is the honest per-slab step of the proof of GWZ Lemma 6.4; the `θ^(β/2)` factor cancels
against `∑_S |fibre_S| = |𝒯|` when summing over slabs.

The prisms *are* the fibre elements, and `SlabFibreGeometry` is what connects them, their shadings
`Yθ`, and the slab `S`; the alternative signature carried an unrelated `Qθ` with no hypothesis linking it
to `S`. The loss `Cfib` is quantified before `K`, since the normalisation loss depends on it — and
`Cfib` is now also (i) the radius of the controlled ball containing the fibre
(`SlabFibreGeometry.subset_controlledBall`) and (ii) the dilation factor carrying the shading bodies
(`SlabFibreGeometry.shade_body`, `(Yθ Q).carrier = (Q.dilation Cfib).carrier`). So `K` absorbs both
the fixed contraction that `Plank.normaliseSlabFamilyToTubes` performs and the fixed
volume/fullness loss of passing from `Q` to `Q.dilation Cfib`. The shading bodies are *not* assumed
to be carried by the undilated representatives: that is not something the plank-to-tube reduction
can supply.

## The local Frostman loss `Cloc`

The Frostman constant governing a *fibre of thickened representatives* inside `S` is not the Frostman
constant `CF` of the original plank family: transferring the bound from the planks to their
representatives costs the fixed factor `Cloc` of `Plank.frostmanThickenedSlabFibre`. That is why the
Frostman hypothesis below is stated in the honest form

`C_F(fibre, S) ≤ Cloc · CF · (|𝒯| / |fibre|) · |S|`,

with `Cloc` an explicit parameter quantified **before** `η`, `b₀` and `K`, and *not* as the
`Cloc`-free bound that the consumer cannot supply.

Since `β / 2 - 1 ≤ 0`, running the tube estimate with the effective local constant `Cloc · CF`
produces `(Cloc · CF) ^ (β/2 - 1) = Cloc ^ (β/2 - 1) · CF ^ (β/2 - 1)`, i.e. it costs the fixed
factor `Cloc ^ (1 - β/2)` relative to the plain-`CF` form stated in the conclusion. That factor is
retained honestly: it is absorbed into this lemma's own fixed loss `K`, which is exactly why `K` is
quantified after `Cloc`. The `CF` in the conclusion is therefore the Frostman constant of the original
family, which is what `Kakeya.aggregateSlabVolume` and GWZ Lemma 6.4 consume — no step anywhere
rewrites `Cloc * CF` to `CF`.

The proof is `Plank.frostmanSlabUnionVolumeLowerBound_proof`
(`Kakeya.DimensionThree.Plank.SlabFrostmanEstimate`), where the analytic input — the two-scale,
free-Frostman-constant form of GWZ Lemma 3.9 — is isolated as the single explicit hypothesis of
`Plank.frostmanSlabUnionVolumeLowerBound_of_twoScaleKF`. -/
theorem frostmanSlabUnionVolumeLowerBound {β : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1)
    (hKF : Kakeya.FrostmanEstimate (EuclideanSpace ℝ (Fin 3)) β) :
    ∀ ε > (0 : ℝ), ∀ c2 > (0 : ℝ≥0), ∀ Cfib : ℝ≥0, 1 ≤ Cfib → ∀ Cloc : ℝ≥0, 1 ≤ Cloc →
      ∃ η > (0 : ℝ), ∃ b₀ > (0 : ℝ≥0), ∃ K : ℝ≥0, 0 < K ∧
      ∀ {a b : ℝ≥0} (_ha : 0 < a) (_hab : a ≤ b) (_hb0 : b ≤ b₀) (hb1 : b ≤ 1)
        {θ : ℝ≥0} (_hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (_hθa : a / b ≤ θ)
        (Yθ : ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (𝒯 fibre : Finset (ThickenedPlank θ b hθ1 hb1)) (S : Slab θ hθ1) (CF : ℝ≥0∞),
        fibre ⊆ 𝒯 → fibre.Nonempty → 1 ≤ CF → CF ≠ ⊤ →
        SlabFibreGeometry fibre Yθ S Cfib →
        (c2 : ℝ≥0) * a ^ (4 * η) ≤ ShadedBody.fullness fibre Yθ →
        Kakeya.frostmanConstant fibre (fun Q => Q.toConvexSpaceBody) S.toConvexSpaceBody
            ≤ (Cloc : ℝ≥0∞) * CF
              * ((𝒯.card : ℝ≥0∞) / (fibre.card : ℝ≥0∞)) * volume S.carrier →
        (a : ℝ≥0∞) ^ ε * CF ^ (β / 2 - 1) * (b : ℝ≥0∞) ^ (2 * β)
              * ((b : ℝ≥0∞) ^ 2) ^ (β / 2) * (θ : ℝ≥0∞) ^ (β / 2)
              * (𝒯.card : ℝ≥0∞) ^ (β / 2 - 1) * (fibre.card : ℝ≥0∞)
            ≤ (K : ℝ≥0∞) * volume (⋃ Q ∈ fibre, (Yθ Q).shade) :=
  frostmanSlabUnionVolumeLowerBound_proof hβpos hβle hKF

/-- `f` **normalises** the plank `W` with contraction `κ > 0` and target frame `g`: it rotates `W`'s
ordered frame `W.basis` onto `g` and scales the `i`-th coordinate by `κ / W.thicknesses i`, i.e. by
`κ/a`, `κ/b`, `κ` respectively. This is exactly the map produced by
`Plank.factorNormalisingAffineEquiv` (translate the centre, rotate the frame to a standard basis,
compose with `diag (a⁻¹, b⁻¹, 1)` and one fixed contraction).

Carrying this structural description is *necessary* for S6G18, not cosmetic. Without it `f` is
constrained only by a volume identity, and then **no** lower bound on the least width of
`W ∩ f⁻¹(S)` can hold: take `f = id`, `θ = 1` and `S ⊇ W`, so that `W ∩ f⁻¹(S) = W`, whose least
width is exactly `a` by `Prism3D.a_le_ethickness_scale` and `Prism3D.ethickness_scale_le_a`, while
`a/b` may be arbitrarily small. -/
def IsPlankNormalisation {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (W : Plank a b hab hb1)
    (f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)) (κ : ℝ)
    (g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∀ x : EuclideanSpace ℝ (Fin 3), f x = f W.center
    + ∑ i, (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ (x - W.center) (W.basis i)) • g i

/-- **The diagonal normalising linear map of a plank**: in the frame `W.basis` it scales the `i`-th
coordinate by `κ / W.thicknesses i`, and its determinant is `κ ^ 3 / (a * b)`. -/
private theorem exists_diagonalNormalisingLinearMap {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (_ha : 0 < a) (W : Plank a b hab hb1) (κ : ℝ) :
    ∃ L : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3),
      (∀ v, L v = ∑ i, (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ v (W.basis i)) • W.basis i) ∧
      LinearMap.det L = κ ^ 3 * ((a : ℝ) * (b : ℝ))⁻¹ := by
  set bsis := W.basis.toBasis
  have hsum : ∀ v, v = ∑ i, inner ℝ v (W.basis i) • W.basis i := by
    intro v
    calc
      v = ∑ i, inner ℝ (W.basis i) v • W.basis i := by
        rw [W.basis.sum_repr' v]
      _ = ∑ i, inner ℝ v (W.basis i) • W.basis i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [real_inner_comm]
  let L : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    bsis.constr ℝ (fun i => (κ * ((W.thicknesses i : ℝ))⁻¹) • W.basis i)
  have hL_formula : ∀ v, L v = ∑ i, (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ v (W.basis i)) • W.basis i := by
    intro v
    calc
      L v = L (∑ i, inner ℝ v (W.basis i) • W.basis i) :=
        congrArg L (hsum v)
      _ = ∑ i, inner ℝ v (W.basis i) • L (W.basis i) := by
        simp [map_sum]
      _ = ∑ i, inner ℝ v (W.basis i) • ((κ * ((W.thicknesses i : ℝ))⁻¹) • W.basis i) := by
        simp [L, bsis]
      _ = ∑ i, (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ v (W.basis i)) • W.basis i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [smul_smul, mul_comm, mul_assoc]
  have h_diag : LinearMap.toMatrix bsis bsis L = Matrix.diagonal (fun i => κ * ((W.thicknesses i : ℝ))⁻¹) := by
    ext i j
    simp [LinearMap.toMatrix_apply, L, bsis, Matrix.diagonal_apply]
    split_ifs with h
    · rw [h]
    · rfl
  have h_det : LinearMap.det L = κ ^ 3 * ((a : ℝ) * (b : ℝ))⁻¹ := by
    calc
      LinearMap.det L = Matrix.det (LinearMap.toMatrix bsis bsis L) := by
        rw [LinearMap.det_toMatrix]
      _ = Matrix.det (Matrix.diagonal (fun i => κ * ((W.thicknesses i : ℝ))⁻¹)) := by rw [h_diag]
      _ = ∏ i : Fin 3, (κ * ((W.thicknesses i : ℝ))⁻¹) := by rw [Matrix.det_diagonal]
      _ = (κ * ((W.thicknesses 0 : ℝ))⁻¹) * (κ * ((W.thicknesses 1 : ℝ))⁻¹) * (κ * ((W.thicknesses 2 : ℝ))⁻¹) := by
        rw [Fin.prod_univ_three]
      _ = κ ^ 3 * ((a : ℝ) * (b : ℝ))⁻¹ := by
        rw [W.thicknesses_eq]
        simp
        ring
  refine ⟨L, hL_formula, h_det⟩

/-- Volume of the image of an arbitrary set under `x ↦ L (x - c)`. -/
private theorem volume_image_sub_linearMap
    (L : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3))
    (c : EuclideanSpace ℝ (Fin 3)) (S : Set (EuclideanSpace ℝ (Fin 3))) :
    volume ((fun x => L (x - c)) '' S) = ENNReal.ofReal |LinearMap.det L| * volume S := by
  have h_image : (fun x => L (x - c)) '' S = (fun y => y - L c) '' (L '' S) :=
  calc
    (fun x => L (x - c)) '' S = ((fun y => y - L c) ∘ L) '' S := by
      refine congrArg (· '' S) ?_
      ext x; simp [map_sub L]
    _ = (fun y => y - L c) '' (L '' S) := (Set.image_image (fun y => y - L c) L S).symm
  calc
    volume ((fun x => L (x - c)) '' S)
        = volume ((fun y => y - L c) '' (L '' S)) := by rw [h_image]
    _ = volume (L '' S) := by
      simp [sub_eq_add_neg, add_comm]
    _ = ENNReal.ofReal |LinearMap.det L| * volume S := by
      rw [MeasureTheory.Measure.addHaar_image_linearMap volume L S]

/-- **Affine map normalising a factor plank** (`lem:geometryFactorAffineMap`).

For an `a × b × 1` factor plank `W` there is an affine map `f` with linear part comparable to
`diag (a⁻¹, b⁻¹, 1)`, sending `W` into the unit ball, and with a constant Jacobian `J`: translate
the centre of `W` to the origin, rotate its ordered frame to the standard basis, compose with
`diag (a⁻¹, b⁻¹, 1)` and one fixed contraction. Since `|W| = 8ab`, the Jacobian obeys
`J · (a · b) ∼ 1`, which is how the comparability of the linear factors is recorded here.

Following `Plank.boxRescaleAffine`, the map is delivered as an `→ᵃ[ℝ]` together with the volume
identity `volume (f '' E) = J · volume E` rather than as a bundled `AffineEquiv`.

The contraction `κ` and the target frame `g` are exposed as well, via
`Plank.IsPlankNormalisation`: `κ` is absolute (it is the fixed contraction taking the normalised
cube into `B₁`), while `g` depends on `W`. S6G18 needs this structural description — a bare volume
identity does not determine `f` enough for any width bound to hold. The proof constructs the explicit
diagonal normalisation map. -/
theorem factorNormalisingAffineEquiv :
    ∃ (κ : ℝ) (cfac Cfac : ℝ≥0), 0 < κ ∧ 0 < cfac ∧ 1 ≤ Cfac ∧
      ∀ {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (_ha : 0 < a) (W : Plank a b hab hb1),
        ∃ (f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)) (J : ℝ≥0)
          (g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))),
          0 < J ∧
          IsPlankNormalisation W f κ g ∧
          (∀ E : Set (EuclideanSpace ℝ (Fin 3)), volume (f '' E) = (J : ℝ≥0∞) * volume E) ∧
          f '' W.carrier ⊆ Metric.closedBall 0 1 ∧
          (∀ x ∈ W.carrier, ‖f x - f W.center‖ ≤ 1) ∧
          cfac ≤ J * (a * b) ∧ J * (a * b) ≤ Cfac := by
  refine ⟨(1 : ℝ)/3, (27 : ℝ≥0)⁻¹, 1, by norm_num, by norm_num, le_rfl, ?_⟩
  intro a b hab hb1 ha W
  have hbpos : 0 < b := lt_of_lt_of_le ha hab
  have hane : ((a : ℝ)) ≠ 0 := by exact_mod_cast ha.ne.symm
  have hbne : ((b : ℝ)) ≠ 0 := by exact_mod_cast hbpos.ne.symm
  have hthick_pos : ∀ i : Fin 3, (0 : ℝ) < (W.thicknesses i : ℝ) := by
    intro i; rw [W.thicknesses_eq]; fin_cases i
    · exact_mod_cast ha
    · exact_mod_cast hbpos
    · norm_num
  obtain ⟨L, hL_formula, hL_det⟩ := exists_diagonalNormalisingLinearMap ha W ((1 : ℝ)/3)
  set f := AffineMap.mk' (fun x => L (x - W.center)) L W.center (by intro p'; simp) with hf_def
  have hfapp : ∀ x, f x = L (x - W.center) := by
    intro x
    rw [hf_def, AffineMap.coe_mk']
  have hfc : f W.center = 0 := by
    rw [hfapp, sub_self, map_zero]
  set J : ℝ≥0 := (27 : ℝ≥0)⁻¹ * (a * b)⁻¹ with hJ_def
  have hJpos : 0 < J := by
    dsimp [J]
    refine mul_pos (by norm_num) (inv_pos.mpr ?_)
    exact mul_pos ha hbpos
  -- IsPlankNormalisation
  have h_plank_norm : IsPlankNormalisation W f ((1 : ℝ)/3) W.basis := by
    intro x
    rw [hfapp, hfc, zero_add]
    exact hL_formula (x - W.center)
  -- Volume identity
  have hJreal : ((J : ℝ≥0) : ℝ) = |LinearMap.det L| := by
    dsimp [J]
    rw [hL_det]
    have hpos : 0 < ((1 : ℝ)/3) ^ 3 * ((a : ℝ) * (b : ℝ))⁻¹ := by
      refine mul_pos (by norm_num) (inv_pos.mpr ?_)
      exact mul_pos (by exact_mod_cast ha) (by exact_mod_cast hbpos)
    rw [abs_of_pos hpos]
    field_simp [hane, hbne]
    ring
  have hJcoe : (J : ℝ≥0∞) = ENNReal.ofReal |LinearMap.det L| := by
    rw [← hJreal, ENNReal.ofReal_coe_nnreal]
  have h_vol : ∀ E : Set (EuclideanSpace ℝ (Fin 3)), volume (f '' E) = (J : ℝ≥0∞) * volume E := by
    intro E
    calc
      volume (f '' E) = volume ((fun x => L (x - W.center)) '' E) := by
        simp [hfapp]
      _ = ENNReal.ofReal |LinearMap.det L| * volume E := volume_image_sub_linearMap L W.center E
      _ = (J : ℝ≥0∞) * volume E := by rw [hJcoe]
  -- Norm bound
  have h_norm : ∀ x ∈ W.carrier, ‖f x - f W.center‖ ≤ 1 := by
    intro x hx
    rw [hfapp, hfc, sub_zero]
    have hx_inner : ∀ i : Fin 3, |inner ℝ (x - W.center) (W.basis i)| ≤ (W.thicknesses i : ℝ) := by
      intro i
      have hmem := (W.mem_carrier_iff (x := x)).mp hx i
      rw [W.basis.repr_apply_apply, vsub_eq_sub] at hmem
      rw [real_inner_comm] at hmem
      exact hmem
    have hthick_ne_zero : ∀ i : Fin 3, (W.thicknesses i : ℝ) ≠ 0 := by
      intro i; exact ne_of_gt (hthick_pos i)
    have h_term_bound : ∀ i : Fin 3,
        |(1/3 : ℝ) * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ (x - W.center) (W.basis i)| ≤ 1/3 := by
      intro i
      calc
        |(1/3 : ℝ) * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ (x - W.center) (W.basis i)|
            = (1/3 : ℝ) * ((W.thicknesses i : ℝ))⁻¹ * |inner ℝ (x - W.center) (W.basis i)| := by
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1/3),
            abs_of_pos (inv_pos.mpr (hthick_pos i))]
        _ ≤ (1/3 : ℝ) * ((W.thicknesses i : ℝ))⁻¹ * (W.thicknesses i : ℝ) := by
          gcongr; exact hx_inner i
        _ = (1/3 : ℝ) := by
          field_simp [hthick_ne_zero i]
    calc
      ‖L (x - W.center)‖ = ‖∑ i : Fin 3, ((1/3 : ℝ) * ((W.thicknesses i : ℝ))⁻¹
          * inner ℝ (x - W.center) (W.basis i)) • W.basis i‖ := by
        rw [hL_formula (x - W.center)]
      _ ≤ ∑ i : Fin 3, ‖(((1/3 : ℝ) * ((W.thicknesses i : ℝ))⁻¹
          * inner ℝ (x - W.center) (W.basis i)) • W.basis i)‖ := norm_sum_le _ _
      _ = ∑ i : Fin 3, |(1/3 : ℝ) * ((W.thicknesses i : ℝ))⁻¹
          * inner ℝ (x - W.center) (W.basis i)| := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_smul, W.basis.norm_eq_one i, mul_one, Real.norm_eq_abs]
      _ ≤ ∑ i : Fin 3, (1/3 : ℝ) :=
        Finset.sum_le_sum fun i _ => h_term_bound i
      _ = 3 * (1/3 : ℝ) := by simp
      _ = 1 := by norm_num
  -- closedBall containment
  have h_closedBall : f '' W.carrier ⊆ Metric.closedBall 0 1 := by
    rintro y ⟨x, hx, rfl⟩
    have hx' : ‖f x - f W.center‖ ≤ 1 := h_norm x hx
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    calc
      ‖f x‖ = ‖f x - f W.center‖ := by simp [hfc]
      _ ≤ 1 := hx'
  -- Comparability goals
  have hJab_val : ((J * (a * b) : ℝ≥0) : ℝ) = ((27 : ℝ≥0)⁻¹ : ℝ) := by
    dsimp [J]
    field_simp [hane, hbne]
  have hJab : J * (a * b) = (27 : ℝ≥0)⁻¹ := by
    apply NNReal.coe_injective
    simpa using hJab_val
  refine ⟨f, J, W.basis, hJpos, h_plank_norm, h_vol, h_closedBall, h_norm, ?_, ?_⟩
  · -- cfac ≤ J * (a * b), i.e., (27 : ℝ≥0)⁻¹ ≤ (27 : ℝ≥0)⁻¹
    simp [hJab]
  · -- J * (a * b) ≤ Cfac, i.e., (27 : ℝ≥0)⁻¹ ≤ 1
    rw [hJab]
    have h27inv : (27 : ℝ≥0)⁻¹ ≤ 1 := by
      have h' : ((27 : ℝ≥0)⁻¹ : ℝ) ≤ (1 : ℝ) := by
        calc
          ((27 : ℝ≥0)⁻¹ : ℝ) = (27 : ℝ)⁻¹ := by norm_num
          _ = (1/27 : ℝ) := by norm_num
          _ ≤ (1 : ℝ) := by norm_num
      exact_mod_cast h'
    exact h27inv

/-- **A `θ × 1 × 1` slab meets the unit ball in volume `≤ 8θ`.** In the slab's own orthonormal
frame the intersection is trapped in the `θ × 1 × 1` box whose thin centre coordinate is that of `S`
and whose two long centre coordinates are `0`, because `‖y‖ ≤ 1` forces `|⟪y, S.basis i⟫| ≤ 1`. -/
theorem volume_closedBall_inter_slab_le {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1) :
    volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 ∩ S.carrier)
      ≤ 8 * (θ : ℝ≥0∞) := by
  let c : EuclideanSpace ℝ (Fin 3) := (inner ℝ S.center (S.basis 0)) • S.basis 0
  let S' : Slab θ hθ1 :=
    { toPrismNDim := PrismNDim.mk' c S.basis ![θ, 1, 1], thicknesses_eq := rfl }
  have hsubset : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 ∩ S.carrier ⊆ S'.carrier := by
    intro y hy
    rcases hy with ⟨hyB, hyS⟩
    rw [S'.mem_carrier_iff]
    intro i
    have h_inner : S'.basis.repr (y -ᵥ S'.center) i = inner ℝ (y -ᵥ S'.center) (S'.basis i) := by
      rw [S'.basis.repr_apply_apply, real_inner_comm]
    rw [h_inner, vsub_eq_sub]
    have hyB' : ‖y‖ ≤ 1 := by
      have hd := Metric.mem_closedBall.mp hyB
      rw [dist_eq_norm, sub_zero] at hd
      exact hd
    fin_cases i
    · -- i = 0
      dsimp [S', PrismNDim.mk']
      have hc0 : inner ℝ c (S.basis 0) = inner ℝ S.center (S.basis 0) := by
        dsimp [c]
        rw [real_inner_smul_left, real_inner_self_eq_norm_sq, S.basis.norm_eq_one 0]
        norm_num
      have h_eq : inner ℝ (y - c) (S.basis 0) = inner ℝ (y - S.center) (S.basis 0) := by
        calc
          inner ℝ (y - c) (S.basis 0) = inner ℝ y (S.basis 0) - inner ℝ c (S.basis 0) := by
            rw [inner_sub_left]
          _ = inner ℝ y (S.basis 0) - inner ℝ S.center (S.basis 0) := by rw [hc0]
          _ = inner ℝ (y - S.center) (S.basis 0) := by rw [← inner_sub_left]
      have hyS0 : |inner ℝ (y - S.center) (S.basis 0)| ≤ (θ : ℝ) := by
        have hmem := (S.mem_carrier_iff (x := y)).mp hyS 0
        rw [S.basis.repr_apply_apply, real_inner_comm, vsub_eq_sub, S.thicknesses_eq] at hmem
        simpa using hmem
      rw [h_eq]
      simpa using hyS0
    · -- i = 1
      dsimp [S', PrismNDim.mk']
      have hc1 : inner ℝ c (S.basis 1) = 0 := by
        dsimp [c]
        rw [real_inner_smul_left]
        simp
      have hb : |inner ℝ (y - c) (S.basis 1)| ≤ 1 := by
        rw [inner_sub_left, hc1, sub_zero]
        calc
          |inner ℝ y (S.basis 1)| ≤ ‖y‖ * ‖S.basis 1‖ := abs_real_inner_le_norm _ _
          _ = ‖y‖ := by simp [S.basis.norm_eq_one 1]
          _ ≤ 1 := hyB'
      simpa using hb
    · -- i = 2
      dsimp [S', PrismNDim.mk']
      have hc2 : inner ℝ c (S.basis 2) = 0 := by
        dsimp [c]
        rw [real_inner_smul_left]
        simp
      have hb : |inner ℝ (y - c) (S.basis 2)| ≤ 1 := by
        rw [inner_sub_left, hc2, sub_zero]
        calc
          |inner ℝ y (S.basis 2)| ≤ ‖y‖ * ‖S.basis 2‖ := abs_real_inner_le_norm _ _
          _ = ‖y‖ := by simp [S.basis.norm_eq_one 2]
          _ ≤ 1 := hyB'
      simpa using hb
  have hvol : volume S'.carrier = 8 * (θ : ℝ≥0∞) := by
    rw [Prism3D.volume_carrier S']
    simp
  exact (measure_mono hsubset).trans hvol.le

/-- **Volume of a pulled-back normalised slab** (`lem:geometryPullbackSlabVolume`, S6G17).

For a `θ × 1 × 1` slab `S` in normalised coordinates, the pullback
`K_{W,S} = W ∩ f⁻¹(S)` is convex and `|K_{W,S}| ≤ C_pull · θ · |W|`.

Convexity is immediate (affine preimages of convex sets are convex, and intersecting with the
convex plank `W` preserves convexity). For the volume: `f(K_{W,S}) = f(W) ∩ S ⊆ B₁ ∩ S`, and in the
frame of `S` Fubini bounds `|B₁ ∩ S|` by the short width `≲ θ` times the area of a fixed
two-dimensional ball; the inverse Jacobian identity
(`MeasureTheory.Measure.addHaar_preimage_linearMap`) then converts this into the stated bound, using
that `J · (a · b)` is bounded above and below by absolute constants.

The lower bound `cfac ≤ J · (a · b)` is essential: with a contraction `f x = ε • (x - W.center)`
on the unit cube `a = b = 1`, `ε ≤ min θ (1 / 2)`, and `S` the `θ × 1 × 1` slab centred at `0`,
`W.carrier ∩ f ⁻¹' S.carrier = W.carrier` and the claimed bound collapses to `1 ≤ C_pull · θ`,
which is false for small `θ`. -/
theorem volumePullbackNormalisedSlab (cfac : ℝ≥0) (hcfac : 0 < cfac) :
    ∃ Cpull : ℝ≥0, 1 ≤ Cpull ∧
      ∀ {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (_ha : 0 < a) (W : Plank a b hab hb1)
        (f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)) (J : ℝ≥0),
        0 < J →
        (∀ E : Set (EuclideanSpace ℝ (Fin 3)), volume (f '' E) = (J : ℝ≥0∞) * volume E) →
        f '' W.carrier ⊆ Metric.closedBall 0 1 →
        cfac ≤ J * (a * b) →
        ∀ (θ : ℝ≥0) (hθ1 : θ ≤ 1) (S : Slab θ hθ1),
          Convexity.IsConvexSet ℝ (W.carrier ∩ f ⁻¹' S.carrier) ∧
          volume (W.carrier ∩ f ⁻¹' S.carrier)
            ≤ (Cpull : ℝ≥0∞) * (θ : ℝ≥0∞) * volume W.carrier := by
  refine ⟨max 1 cfac⁻¹, ?_, ?_⟩
  · exact le_max_left (1 : ℝ≥0) cfac⁻¹
  · intro a b hab hb1 ha W f J hJ hvolf himg hJab θ hθ1 S
    have hWconv : Convexity.IsConvexSet ℝ (W.carrier : Set _) := by
      exact W.convex'
    have hSconv : Convexity.IsConvexSet ℝ (S.carrier : Set _) := by
      exact S.convex'
    have hpre : Convexity.IsConvexSet ℝ (f ⁻¹' S.carrier) :=
      Convexity.IsConvexSet.affineMap_preimage f hSconv
    have hconv : Convexity.IsConvexSet ℝ (W.carrier ∩ f ⁻¹' S.carrier) :=
      hWconv.inter hpre
    refine ⟨hconv, ?_⟩
    let K : Set (EuclideanSpace ℝ (Fin 3)) := W.carrier ∩ f ⁻¹' S.carrier
    have hK : f '' K = f '' W.carrier ∩ S.carrier := by
      dsimp [K]
      rw [Set.image_inter_preimage]
    have hvol : volume (f '' W.carrier ∩ S.carrier) = (J : ℝ≥0∞) * volume K := by
      rw [← hK, hvolf K]
    have hsub : f '' W.carrier ∩ S.carrier ⊆
        Metric.closedBall 0 1 ∩ S.carrier := by
      intro y hy
      rcases hy with ⟨hyf, hyS⟩
      constructor
      · rw [Set.mem_image] at hyf
        rcases hyf with ⟨x, hxW, rfl⟩
        exact himg ⟨x, hxW, rfl⟩
      · exact hyS
    have htm : (J : ℝ≥0∞) * volume K ≤ 8 * (θ : ℝ≥0∞) := by
      rw [← hvol]
      exact (measure_mono hsub).trans (volume_closedBall_inter_slab_le S)
    have hJne : (J : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hJ.ne'
    have hJnt : (J : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
    have hVle : volume K ≤ (J : ℝ≥0∞)⁻¹ * (8 * (θ : ℝ≥0∞)) := by
      exact (ENNReal.mul_le_iff_le_inv hJne hJnt).mp htm
    have hbpos : 0 < b := lt_of_lt_of_le ha hab
    have hab_pos : 0 < a * b := mul_pos ha hbpos
    -- J⁻¹ ≤ cfac⁻¹ * (a * b), from cfac ≤ J * (a * b) by inverting (order-reversing) and
    -- multiplying back by the positive factor a * b.
    have hJinv_le : (J⁻¹ : ℝ≥0) ≤ cfac⁻¹ * (a * b) := by
      have h_invNN : (J * (a * b))⁻¹ ≤ cfac⁻¹ :=
        (inv_le_inv₀ (mul_pos hJ hab_pos) hcfac).mpr hJab
      have hfac_pos : (a * b) ≠ 0 := hab_pos.ne'
      calc
        (J⁻¹ : ℝ≥0) = (J⁻¹ * (a * b)⁻¹) * (a * b) := by
          rw [mul_assoc, inv_mul_cancel₀ hfac_pos, mul_one]
        _ = (J * (a * b))⁻¹ * (a * b) := by rw [← mul_inv]
        _ ≤ cfac⁻¹ * (a * b) := mul_le_mul_of_nonneg_right h_invNN (by positivity)
    -- cfac⁻¹ ≤ max 1 cfac⁻¹, so J⁻¹ ≤ max 1 cfac⁻¹ * (a * b).
    have hkey : (J⁻¹ : ℝ≥0) ≤ max 1 cfac⁻¹ * (a * b) := by
      calc
        (J⁻¹ : ℝ≥0) ≤ cfac⁻¹ * (a * b) := hJinv_le
        _ ≤ max 1 cfac⁻¹ * (a * b) := by
          exact mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ≥0) cfac⁻¹) (by positivity)
    have hJinv_cast : (J : ℝ≥0∞)⁻¹ = ((J⁻¹ : ℝ≥0) : ℝ≥0∞) := by
      rw [ENNReal.coe_inv hJ.ne']
    have hVle' : volume K ≤ ((J⁻¹ : ℝ≥0) : ℝ≥0∞) * (8 * (θ : ℝ≥0∞)) := by
      simpa [hJinv_cast] using hVle
    have hVle'' : volume K ≤ ((max 1 cfac⁻¹ * (a * b) : ℝ≥0) : ℝ≥0∞) * (8 * (θ : ℝ≥0∞)) :=
      hVle'.trans (mul_le_mul' (ENNReal.coe_le_coe.mpr hkey) le_rfl)
    have hWvol : volume W.carrier = 8 * ((a * b : ℝ≥0) : ℝ≥0∞) := by
      rw [Prism3D.volume_carrier W, mul_assoc, ENNReal.coe_mul]
      norm_num
      ring
    have hfinalEq : ((max 1 cfac⁻¹ * (a * b) : ℝ≥0) : ℝ≥0∞) * (8 * (θ : ℝ≥0∞))
        = ((max 1 cfac⁻¹ : ℝ≥0) : ℝ≥0∞) * (θ : ℝ≥0∞) * volume W.carrier := by
      rw [hWvol]
      exact_mod_cast (by
        ring : (max 1 cfac⁻¹ * (a * b) : ℝ≥0) * (8 * θ) = (max 1 cfac⁻¹) * θ * (8 * (a * b)))
    calc
      volume K ≤ ((max 1 cfac⁻¹ * (a * b) : ℝ≥0) : ℝ≥0∞) * (8 * (θ : ℝ≥0∞)) := hVle''
      _ = ((max 1 cfac⁻¹ : ℝ≥0) : ℝ≥0∞) * (θ : ℝ≥0∞) * volume W.carrier := hfinalEq

/-- The **pullback normal**: the vector `m` representing, in `W`'s own frame, the linear functional
that a slab's unit normal `n` induces on the source of a plank normalisation. Explicitly
`m = ∑ᵢ (κ / W.thicknesses i) · ⟪n, g i⟫ • W.basis i`, i.e. `m = Dᵀn` read in the frame `W.basis`,
where `D = diag (κ/a, κ/b, κ)` is the diagonal part of the normalisation.

Its defining property is `Plank.inner_pullbackNormal`: `⟪f x - f W.center, n⟫ = ⟪x - W.center, m⟫`.
So the preimage under `f` of the slab constraint `|⟪y - S.center, n⟫| ≤ θ` is the strip of normal `m`
and half-width `θ / ‖m‖`, which is why bounding `‖m‖` above bounds the strip's width below. -/
def pullbackNormal {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (W : Plank a b hab hb1) (κ : ℝ)
    (g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)))
    (n : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  ∑ i, (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ n (g i)) • W.basis i

/-- **Defining property of the pullback normal.** For a plank normalisation `f` of `W`, testing the
displacement `f x - f W.center` against `n` is the same as testing `x - W.center` against
`Plank.pullbackNormal W κ g n`. Pure algebra: expand `f` through `IsPlankNormalisation`, pull the
inner product through the finite sum, and use symmetry of the real inner product. -/
theorem inner_pullbackNormal {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (W : Plank a b hab hb1)
    {f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)} {κ : ℝ}
    {g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))}
    (hnorm : IsPlankNormalisation W f κ g) (n x : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ (f x - f W.center) n = inner ℝ (x - W.center) (pullbackNormal W κ g n) := by
  have hfx : f x - f W.center
      = ∑ i, (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ (x - W.center) (W.basis i)) • g i := by
    rw [hnorm x]
    abel
  rw [hfx, pullbackNormal]
  calc
    inner ℝ (∑ i, (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ (x - W.center) (W.basis i)) • g i) n
        = ∑ i, inner ℝ ((κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ (x - W.center) (W.basis i)) • g i) n := by
      rw [sum_inner]
    _ = ∑ i, (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ (x - W.center) (W.basis i)) * inner ℝ (g i) n := by
      simp_rw [real_inner_smul_left]
    _ = ∑ i, (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ (x - W.center) (W.basis i)) * inner ℝ n (g i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_comm (g i) n]
    _ = inner ℝ (x - W.center) (∑ i, (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ n (g i)) • W.basis i) := by
      rw [inner_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_smul_right]
      ring

/-- **The wedge-product estimate of S6G18.** The pullback normal has norm `≲ κ · θ / a`.

`‖m‖ ≤ ∑ᵢ κ · |⟪n, g i⟫| / W.thicknesses i` by the triangle inequality and orthonormality of
`W.basis`, and the three terms are bounded separately, with `W.thicknesses = ![a, b, 1]`:
* `i = 0`: the tangency hypothesis gives `|⟪n, g 0⟫| ≤ C_tang · θ`, so the term is `≤ κ·C_tang·θ/a`;
* `i = 1`: `|⟪n, g 1⟫| ≤ 1`, so the term is `≤ κ/b ≤ κ·θ/a`, using `a/b ≤ θ`;
* `i = 2`: `|⟪n, g 2⟫| ≤ 1`, so the term is `≤ κ ≤ κ·θ/a`, using `a ≤ a/b ≤ θ` (as `b ≤ 1`).

This is the quantitative content of the blueprint's "`‖Dᵀn‖ ≤ C/b`" step — note that in the corrected
normalisation the relevant bound is `≲ κθ/a`, which is what yields a strip of width `≳ a/κ` and hence
the `c_tr · a` conclusion of S6G18 rather than the (impossible) `c_tr · θ · b`. -/
theorem norm_pullbackNormal_le {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (W : Plank a b hab hb1)
    {κ : ℝ} (hκ : 0 < κ) (ha : 0 < a)
    {g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))}
    {n : EuclideanSpace ℝ (Fin 3)} (hn : ‖n‖ = 1)
    {θ : ℝ≥0} (hθab : a / b ≤ θ) {Ctang : ℝ≥0}
    (htang : |inner ℝ n (g 0)| ≤ (Ctang : ℝ) * (θ : ℝ)) :
    ‖pullbackNormal W κ g n‖ ≤ κ * ((Ctang : ℝ) + 2) * (θ : ℝ) / (a : ℝ) := by
  set_option maxHeartbeats 1000000 in
  -- scalar facts
  have hap : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha
  have hbp : (0:ℝ) < (b:ℝ) := by exact_mod_cast (ha.trans_le hab)
  have hb1' : (b:ℝ) ≤ 1 := by exact_mod_cast hb1
  have hθmul : (a:ℝ) ≤ (θ:ℝ) * (b:ℝ) := by
    have h : (a:ℝ) / (b:ℝ) ≤ (θ:ℝ) := by exact_mod_cast hθab
    rwa [div_le_iff₀ hbp] at h
  have hθp : (0:ℝ) ≤ (θ:ℝ) := (θ : ℝ≥0).coe_nonneg
  -- 1/b ≤ θ/a  and  1 ≤ θ/a
  have key1 : ((b:ℝ))⁻¹ ≤ (θ:ℝ) / (a:ℝ) := by
    rw [inv_eq_one_div]
    refine (div_le_div_iff₀ hbp hap).mpr ?_
    calc
      (1:ℝ) * (a:ℝ) = (a:ℝ) := by ring
      _ ≤ (θ:ℝ) * (b:ℝ) := hθmul
  have key2 : (1:ℝ) ≤ (θ:ℝ) / (a:ℝ) := by
    rw [le_div_iff₀ hap]
    calc
      (1:ℝ) * (a:ℝ) = (a:ℝ) := by ring
      _ ≤ (θ:ℝ) * (b:ℝ) := hθmul
      _ ≤ (θ:ℝ) * 1 := mul_le_mul_of_nonneg_left hb1' (by positivity : 0 ≤ (θ:ℝ))
      _ = (θ:ℝ) := mul_one _
  -- for each i, |inner ℝ n (g i)| ≤ 1
  have hgi : ∀ i, |inner ℝ n (g i)| ≤ 1 := by
    intro i
    calc |inner ℝ n (g i)| ≤ ‖n‖ * ‖g i‖ := abs_real_inner_le_norm _ _
      _ = 1 := by rw [hn, g.norm_eq_one i, mul_one]
  -- STEP 1 — triangle inequality plus orthonormality of W.basis
  rw [pullbackNormal]
  have hstep : ‖∑ i, (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ n (g i)) • W.basis i‖
      ≤ ∑ i, |κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ n (g i)| := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
    intro i _
    rw [norm_smul, Real.norm_eq_abs, W.basis.norm_eq_one i, mul_one]
  refine hstep.trans ?_
  -- STEP 2 — expand the three terms and evaluate the thicknesses
  have ht0 : ((W.thicknesses 0 : ℝ)) = (a:ℝ) := by
    rw [W.thicknesses_eq]
    simp
  have ht1 : ((W.thicknesses 1 : ℝ)) = (b:ℝ) := by
    rw [W.thicknesses_eq]
    simp
  have ht2 : ((W.thicknesses 2 : ℝ)) = (1:ℝ) := by
    rw [W.thicknesses_eq]
    simp
  rw [Fin.sum_univ_three, ht0, ht1, ht2]
  -- STEP 3 — bound the three absolute values
  have hb0 : |κ * ((a:ℝ))⁻¹ * inner ℝ n (g 0)| ≤ κ * ((a:ℝ))⁻¹ * ((Ctang : ℝ) * (θ : ℝ)) := by
    calc
      |κ * ((a:ℝ))⁻¹ * inner ℝ n (g 0)| = κ * ((a:ℝ))⁻¹ * |inner ℝ n (g 0)| := by
        rw [abs_mul, abs_mul, abs_of_pos hκ, abs_of_pos (inv_pos.mpr hap)]
      _ ≤ κ * ((a:ℝ))⁻¹ * ((Ctang : ℝ) * (θ : ℝ)) := by
        gcongr
  have hb1'val : |κ * ((b:ℝ))⁻¹ * inner ℝ n (g 1)| ≤ κ * ((b:ℝ))⁻¹ := by
    calc
      |κ * ((b:ℝ))⁻¹ * inner ℝ n (g 1)| = κ * ((b:ℝ))⁻¹ * |inner ℝ n (g 1)| := by
        rw [abs_mul, abs_mul, abs_of_pos hκ, abs_of_pos (inv_pos.mpr hbp)]
      _ ≤ κ * ((b:ℝ))⁻¹ * 1 := by
        gcongr; exact hgi 1
      _ = κ * ((b:ℝ))⁻¹ := by ring
  have hb2 : |κ * ((1:ℝ))⁻¹ * inner ℝ n (g 2)| ≤ κ := by
    calc
      |κ * ((1:ℝ))⁻¹ * inner ℝ n (g 2)| = κ * |inner ℝ n (g 2)| := by
        simp [abs_mul, abs_of_pos hκ, inv_one]
      _ ≤ κ * 1 := by
        gcongr; exact hgi 2
      _ = κ := by ring
  -- STEP 4 — finish
  have c1 : κ * ((b:ℝ))⁻¹ ≤ κ * ((θ:ℝ) / (a:ℝ)) :=
    mul_le_mul_of_nonneg_left key1 hκ.le
  have c2 : κ ≤ κ * ((θ:ℝ) / (a:ℝ)) := by
    calc κ = κ * 1 := (mul_one κ).symm
      _ ≤ κ * ((θ:ℝ) / (a:ℝ)) := mul_le_mul_of_nonneg_left key2 hκ.le
  have hrhs : κ * ((a:ℝ))⁻¹ * ((Ctang : ℝ) * (θ : ℝ)) + κ * ((θ:ℝ)/(a:ℝ)) + κ * ((θ:ℝ)/(a:ℝ))
      = κ * ((Ctang : ℝ) + 2) * (θ : ℝ) / (a : ℝ) := by
    field_simp
    ring
  calc
    |κ * ((a:ℝ))⁻¹ * inner ℝ n (g 0)| + |κ * ((b:ℝ))⁻¹ * inner ℝ n (g 1)| + |κ * ((1:ℝ))⁻¹ * inner ℝ n (g 2)|
        ≤ κ * ((a:ℝ))⁻¹ * ((Ctang : ℝ) * (θ : ℝ)) + κ * ((b:ℝ))⁻¹ + κ := by
      nlinarith
    _ ≤ κ * ((a:ℝ))⁻¹ * ((Ctang : ℝ) * (θ : ℝ)) + κ * ((θ:ℝ)/(a:ℝ)) + κ * ((θ:ℝ)/(a:ℝ)) := by
      nlinarith
    _ = κ * ((Ctang : ℝ) + 2) * (θ : ℝ) / (a : ℝ) := hrhs


/-- The displacement form of `Plank.inner_pullbackNormal`: testing `f x - f y` against `n` is the
same as testing `x - y` against the pullback normal. Immediate by subtracting the identity at `x`
and at `y`. -/
theorem inner_pullbackNormal_sub {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (W : Plank a b hab hb1)
    {f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)} {κ : ℝ}
    {g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))}
    (hnorm : IsPlankNormalisation W f κ g) (n x y : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ (f x - f y) n = inner ℝ (x - y) (pullbackNormal W κ g n) := by
  have hx := inner_pullbackNormal W hnorm n x
  have hy := inner_pullbackNormal W hnorm n y
  have hL : f x - f y = (f x - f W.center) - (f y - f W.center) := by abel
  have hR : x - y = (x - W.center) - (y - W.center) := by abel
  calc
    inner ℝ (f x - f y) n = inner ℝ ((f x - f W.center) - (f y - f W.center)) n := by rw [hL]
    _ = inner ℝ (f x - f W.center) n - inner ℝ (f y - f W.center) n := by rw [inner_sub_left]
    _ = inner ℝ (x - W.center) (pullbackNormal W κ g n) - inner ℝ (y - W.center) (pullbackNormal W κ g n) := by rw [hx, hy]
    _ = inner ℝ ((x - W.center) - (y - W.center)) (pullbackNormal W κ g n) := by rw [← inner_sub_left]
    _ = inner ℝ (x - y) (pullbackNormal W κ g n) := by rw [hR]


end Plank

end

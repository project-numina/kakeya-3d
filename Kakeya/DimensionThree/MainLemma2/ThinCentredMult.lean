/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factoring.Pipeline
public import Kakeya.Covers
public import Kakeya.Mathlib.Topology.CoveringNumber
public import Kakeya.ConstantMultiplicity

/-!
# The finer ball-net pigeonhole, and the cell outer shading

Two constructions that the factoring pipeline of `Kakeya/Factoring/Multiplicity.lean` does not
perform and that conjuncts (iii)(a) and (iv) of `Kakeya.ThinCase.factoringApply` need.

## The equal-radius centred multiplicity, conjunct (iv)

Item 7 of GWZ Proposition 5.1, `ShadedBody.outerFactoringFamily_avgMultOnBalls`, compares the mass
of the inner shaded union in `ball x w₁` with its mass in `closedBall y (7 w₁)`, and its own
docstring records that the equal-radius form is **false** for the constructed family. Conjunct
(iv) demands equal radii. The gap is exactly one factor: the pipeline's Step 5 equalises the ball
masses at the *comparison* radius `w₁`, so a point `y` of the outer union — which lies only within
`2 τ₂ ≍ w₁` of the inner union — cannot be guaranteed to see a heavy ball inside `ball y w₁`.

Running the pipeline at a smaller ball radius does not help:
`ShadedBody.outerFactoringFamily_avgMultOnBalls` carries `F.OuterIsAtScale 2 w₁`, which is the
width clause `hw₁` of `factoringApply` at the *same* `w₁` as the ball radius.

`Kakeya.ThinCase.exists_ballNetRefinement` performs a **second, finer** pigeonhole at scale
`w₁ / 8`: a
maximal `w₁/8`-separated net of the shaded union, a dyadic pigeonhole of the Lebesgue ball masses
(`ShadedBody.exists_self_dyadic`), and the restriction of the union to the retained net balls.
The retained union then has ball masses comparable at the equal radius `8 r = w₁` for every
`y` in the `2 r = w₁/4` collar, with the purely dimensional constant
`Kakeya.ThinCase.equalRadiusMultConstant`. The cost is `Kakeya.ThinCase.ballNetLoss`, one further
logarithmic factor — the same shape as the pipeline's own Step-5 loss, and therefore inside the
`Ccore` budget of `Kakeya.VeryNotSticky.CaseScale.transverse_ballFill`; the localisation
alternative of `Kakeya.ThinCase.Localise.exists_localised_refinement` costs a genuine power of
`1/δ` and is not.

## The cell outer shading, conjunct (iii)(a)

Conjunct (iii)(a) asks for constant multiplicity of the *outer* shaded family, while (ii) forces
every outer shade to contain its block's inner union and (v) forces it into the `2 τ₂`-collar of
that same union. A dyadic band of the outer multiplicity — the pigeonhole
`ShadedBody.exists_constantMultiplicity_refinement` performs, and the one
`ShadedBody.outerFactoringFamily_outerConstMultFat` goes through — is therefore **not** available
here: restricting the outer shades to a band breaks (ii), and repairing (ii) by restricting the
inner shades to the same band breaks (v), whose right-hand side is the *retained* inner union.
Iterating does not terminate.

`Kakeya.ThinCase.exists_cellOuterShading` avoids the regress. It pigeonholes the **net cells**
rather than the multiplicity function: the number of blocks meeting a given net ball is a function
of the cell, not of the point, so a dyadic band of *that* count makes the outer multiplicity
literally constant, while the outer shades — built out of whole cells of a measurable partition
subordinate to the retained net balls — contain their blocks' inner unions and sit inside the
`2 r`-collar by construction. No inner shade is restricted beyond the common set
`⋃ c ∈ T'', closedBall c r`, so the inner clauses and the inner multiplicity band survive
verbatim.

## The collar comparison

`Kakeya.ThinCase.volume_cthickening_le_mul_volume_cthickening` compares the volume of the
`S`-collar of a set with that of its `s`-collar, `0 < s ≤ S`, at a purely dimensional cost. It is
what lets conjunct (i) — whose Córdoba lower bound
`ShadedBody.lambdaForInducedShading_of_measurable` is stated for the collar of radius `2 τ₂` —
survive the truncation of the outer shading to the `w₁/8`-scale cells that (iv) forces.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric Set ShadedBody

namespace Kakeya.ThinCase

section BallNet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The dimensional constant of the **equal-radius** centred multiplicity estimate. -/
def equalRadiusMultConstant (n : ℕ) : ℝ≥0 := 2 * 21 ^ n

/-- An upper bound for the cardinality of an `r`-separated set inside a ball of radius `R`. -/
noncomputable def netCardBound (n : ℕ) (r R : ℝ) : ℕ := ⌈(1 + 2 * R / r) ^ n⌉₊

/-- The mass loss of the finer ball-net pigeonhole at scale `r` inside a ball of radius `R`. -/
noncomputable def ballNetLoss (n : ℕ) (r R : ℝ) : ℝ≥0 :=
  5 ^ n * (2 * Kakeya.factoringStep1FiberPigeonholeConstant 1 (netCardBound n r R))

/-- An `r`-separated finset inside a ball of radius `R` has at most `netCardBound n r R`
elements. -/
lemma card_le_netCardBound {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) {z : E} {T : Finset E}
    (hsep : ∀ y ∈ (T : Set E), ∀ w ∈ (T : Set E), y ≠ w → r ≤ dist y w)
    (hT : (T : Set E) ⊆ Metric.ball z R) :
    T.card ≤ netCardBound (Module.finrank ℝ E) r R := by
  obtain ⟨-, hcard⟩ := Kakeya.finite_and_card_le_of_separated hr hR z hsep hT
  have hcard' : ((T.card : ℝ)) ≤ (1 + 2 * R / r) ^ Module.finrank ℝ E := by simpa using hcard
  exact_mod_cast hcard'.trans (Nat.le_ceil ((1 + 2 * R / r) ^ Module.finrank ℝ E))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `Metric.IsSeparated` at an `NNReal` radius, in the real-distance form the packing bound of
`Kakeya.finite_and_card_le_of_separated` takes. -/
lemma dist_ge_of_isSeparated {r : ℝ≥0} {T : Finset E}
    (hsep : Metric.IsSeparated (r : ℝ≥0∞) (T : Set E)) :
    ∀ y ∈ (T : Set E), ∀ w ∈ (T : Set E), y ≠ w → (r : ℝ) ≤ dist y w := by
  intro y hy w hw hyw
  have h : (r : ℝ≥0∞) < edist y w := hsep hy hw hyw
  rw [edist_dist, ← ENNReal.ofReal_coe_nnreal (p := r)] at h
  exact le_of_lt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg r.coe_nonneg).mp h)

/-- Monotonicity of the dyadic pigeonhole loss in the family size. -/
lemma pigeonholeConstant_mono {a b : ℕ} (hab : a ≤ b) :
    Kakeya.factoringStep1FiberPigeonholeConstant 1 (a : ℝ≥0)
      ≤ Kakeya.factoringStep1FiberPigeonholeConstant 1 (b : ℝ≥0) := by
  unfold Kakeya.factoringStep1FiberPigeonholeConstant
  refine Real.toNNReal_le_toNNReal_iff'.mpr (Or.inl ?_)
  have hcoe : ∀ m : ℕ, (((m : ℝ≥0) : ℝ) / ((1 : ℝ≥0) : ℝ)) = (m : ℝ) := by
    intro m; push_cast; ring
  rw [hcoe a, hcoe b]
  have hb : (0:ℝ) ≤ Real.logb 2 (b : ℝ) := by
    rcases Nat.eq_zero_or_pos b with rfl | hbpos
    · simp
    · have : (1:ℝ) ≤ (b:ℝ) := by exact_mod_cast hbpos
      exact Real.logb_nonneg (by norm_num) this
  rcases Nat.eq_zero_or_pos a with rfl | hapos
  · simp only [Nat.cast_zero, Real.logb_zero]
    linarith
  · have hapos' : (0:ℝ) < (a:ℝ) := by exact_mod_cast hapos
    have hab' : (a:ℝ) ≤ (b:ℝ) := by exact_mod_cast hab
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) hapos' hab'
    linarith

/-- The dimensional constant comparing a large collar with a small one. -/
noncomputable def collarCompareConstant (n : ℕ) (s S : ℝ) : ℝ≥0 :=
  Real.toNNReal ((2 * (S + 2 * s) / s) ^ n)

/-- **Comparing collars of two radii** (the estimate that reconciles conjunct (i) with the
truncation conjunct (iv) forces).

For a bounded nonempty `U` and `0 < s ≤ S`, the `S`-collar of `U` has volume at most a purely
dimensional multiple of its `s`-collar. Consequently the Córdoba lower bound of GWZ Item 2, which
is stated for the collar of radius `2 τ₂`, survives truncation of the outer shading to the collar
of radius `w₁ / 4` at the cost of one dimensional factor. -/
theorem volume_cthickening_le_mul_volume_cthickening {U : Set E} (_hU : U.Nonempty)
    (hbdd : Bornology.IsBounded U) {s S : ℝ} (hs : 0 < s) (hsS : s ≤ S) :
    volume (Metric.cthickening S U) ≤
      (collarCompareConstant (Module.finrank ℝ E) s S : ℝ≥0∞) *
        volume (Metric.cthickening s U) := by
  classical
  set n := Module.finrank ℝ E with hn
  set v₁ : ℝ≥0∞ := volume (Metric.ball (0 : E) 1) with hv₁
  have hs' : (0 : ℝ≥0) < Real.toNNReal s := by
    simpa [Real.toNNReal_pos] using hs
  have hscoe : ((Real.toNNReal s : ℝ≥0) : ℝ) = s := Real.coe_toNNReal s hs.le
  obtain ⟨P, hPsub, hPsep, hPcover, -⟩ :=
    hbdd.exists_finset_isSeparated_isCover_closedBall hs'
  rw [hscoe] at hPcover
  -- the `S`-collar is covered by the `(S + 2 s)`-balls around the net
  have hcov : Metric.cthickening S U ⊆ ⋃ p ∈ P, Metric.closedBall p (S + 2 * s) := by
    intro x hx
    have hxth : x ∈ Metric.thickening (S + s / 2) U :=
      Metric.cthickening_subset_thickening' (by linarith) (by linarith) _ hx
    obtain ⟨u, hu, hdu⟩ := Metric.mem_thickening_iff.mp hxth
    obtain ⟨p, hp, hup⟩ := Set.mem_iUnion₂.mp (hPcover hu)
    have hup' : dist u p ≤ s := by simpa [Metric.mem_closedBall] using hup
    refine Set.mem_biUnion hp ?_
    rw [Metric.mem_closedBall]
    calc dist x p ≤ dist x u + dist u p := dist_triangle x u p
      _ ≤ (S + s / 2) + s := by linarith
      _ ≤ S + 2 * s := by linarith
  -- the half-balls around the net are disjoint and sit inside the `s`-collar
  have hdisj : (P : Set E).PairwiseDisjoint fun p => Metric.ball p (s / 2) := by
    intro p hp q hq hpq
    refine Metric.ball_disjoint_ball ?_
    have h : (Real.toNNReal s : ℝ≥0∞) < edist p q := hPsep hp hq hpq
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal] at h
    have := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Real.toNNReal s).coe_nonneg).mp h
    rw [hscoe] at this
    linarith
  have hsub_s : ∀ p ∈ P, Metric.ball p (s / 2) ⊆ Metric.cthickening s U := by
    intro p hp w hw
    refine Metric.closedBall_subset_cthickening (hPsub (Finset.mem_coe.mpr hp)) s ?_
    rw [Metric.mem_closedBall]
    have : dist w p < s / 2 := by simpa [Metric.mem_ball] using hw
    linarith
  -- volumes of balls
  have hvolball : ∀ (p : E) (t : ℝ), 0 < t →
      volume (Metric.ball p t) = ENNReal.ofReal (t ^ n) * v₁ := by
    intro p t ht
    simpa [hn, hv₁] using MeasureTheory.Measure.addHaar_ball_of_pos (μ := volume) p ht
  have hvolcball : ∀ (p : E) (t : ℝ), 0 < t →
      volume (Metric.closedBall p t) = ENNReal.ofReal (t ^ n) * v₁ := by
    intro p t ht
    simpa [hn, hv₁] using MeasureTheory.Measure.addHaar_closedBall (μ := volume) p ht.le
  have hStwo : (0:ℝ) < S + 2 * s := by linarith
  have hhalf : (0:ℝ) < s / 2 := by linarith
  have hupper : volume (Metric.cthickening S U)
      ≤ (P.card : ℝ≥0∞) * (ENNReal.ofReal ((S + 2 * s) ^ n) * v₁) := by
    refine le_trans (measure_mono hcov) ?_
    refine le_trans (measure_biUnion_finset_le P _) ?_
    rw [show (∑ p ∈ P, volume (Metric.closedBall p (S + 2 * s)))
        = ∑ _p ∈ P, (ENNReal.ofReal ((S + 2 * s) ^ n) * v₁) from
      Finset.sum_congr rfl fun p _ => hvolcball p _ hStwo, Finset.sum_const, nsmul_eq_mul]
  have hlower : (P.card : ℝ≥0∞) * (ENNReal.ofReal ((s / 2) ^ n) * v₁)
      ≤ volume (Metric.cthickening s U) := by
    have := MeasureTheory.measure_biUnion_finset (μ := volume) hdisj
      (fun p _ => (measurableSet_ball : MeasurableSet (Metric.ball p (s / 2))))
    calc (P.card : ℝ≥0∞) * (ENNReal.ofReal ((s / 2) ^ n) * v₁)
        = ∑ _p ∈ P, (ENNReal.ofReal ((s / 2) ^ n) * v₁) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ∑ p ∈ P, volume (Metric.ball p (s / 2)) :=
          Finset.sum_congr rfl fun p _ => (hvolball p _ hhalf).symm
      _ = volume (⋃ p ∈ P, Metric.ball p (s / 2)) := this.symm
      _ ≤ volume (Metric.cthickening s U) :=
          measure_mono (Set.iUnion₂_subset hsub_s)
  have hfac : ENNReal.ofReal ((S + 2 * s) ^ n)
      = (collarCompareConstant n s S : ℝ≥0∞) * ENNReal.ofReal ((s / 2) ^ n) := by
    rw [collarCompareConstant,
      show ((Real.toNNReal ((2 * (S + 2 * s) / s) ^ n) : ℝ≥0) : ℝ≥0∞)
        = ENNReal.ofReal ((2 * (S + 2 * s) / s) ^ n) from rfl,
      ← ENNReal.ofReal_mul (by positivity), ← mul_pow]
    congr 2
    field_simp
  calc volume (Metric.cthickening S U)
      ≤ (P.card : ℝ≥0∞) * (ENNReal.ofReal ((S + 2 * s) ^ n) * v₁) := hupper
    _ = (collarCompareConstant n s S : ℝ≥0∞) *
          ((P.card : ℝ≥0∞) * (ENNReal.ofReal ((s / 2) ^ n) * v₁)) := by
        rw [hfac]; ring
    _ ≤ (collarCompareConstant n s S : ℝ≥0∞) * volume (Metric.cthickening s U) := by
        gcongr

/-! ### The net as an input

`Kakeya.ThinCase.exists_ballNetRefinement` hides the net it builds, which makes its conclusion
unusable after a *further* pigeonhole of that net — and the cell construction of
`Kakeya.ThinCase.exists_cellOuterShading` is exactly such a pigeonhole. The two halves are
therefore restated here with the net exposed: `Kakeya.ThinCase.exists_comparableNet` produces it,
`Kakeya.ThinCase.centredMult_of_separatedNet` consumes it. Both `Metric.IsSeparated` and the
mass comparability restrict to a subnet, and the covering hypothesis holds for
`V := U ∩ ⋃ c ∈ T'', closedBall c r` by construction, so the equal-radius estimate survives the
second pigeonhole verbatim. -/

/-- **The equal-radius centred multiplicity from a separated net with comparable ball masses.** -/
theorem centredMult_of_separatedNet {V : Set E} {T : Finset E} {r : ℝ≥0} (hr : 0 < r)
    (hsep : Metric.IsSeparated (r : ℝ≥0∞) (T : Set E))
    (hcov : V ⊆ ⋃ c ∈ T, Metric.closedBall c (r : ℝ))
    (hcomp : ∀ c ∈ T, ∀ c' ∈ T,
      volume (V ∩ Metric.closedBall c (r : ℝ)) ≤ 2 * volume (V ∩ Metric.closedBall c' (r : ℝ))) :
    ∀ x : E, ∀ y ∈ Metric.cthickening (2 * (r : ℝ)) V,
      volume (V ∩ Metric.ball x (8 * (r : ℝ))) ≤
        (equalRadiusMultConstant (Module.finrank ℝ E) : ℝ≥0∞) *
          volume (V ∩ Metric.ball y (8 * (r : ℝ))) := by
  classical
  set n := Module.finrank ℝ E with hn
  have hrR : (0:ℝ) < (r:ℝ) := hr
  set g : E → ℝ≥0∞ := fun c => volume (V ∩ Metric.closedBall c (r : ℝ)) with hgdef
  intro x y hy
  have hthick : y ∈ Metric.thickening (5 * (r : ℝ) / 2) V :=
    Metric.cthickening_subset_thickening' (by linarith) (by linarith) _ hy
  obtain ⟨u, hu, hdu⟩ := Metric.mem_thickening_iff.mp hthick
  obtain ⟨c, hc, hcu⟩ := Set.mem_iUnion₂.mp (hcov hu)
  have hcu' : dist u c ≤ (r : ℝ) := by simpa [Metric.mem_closedBall] using hcu
  have hyc : dist y c < 5 * (r : ℝ) / 2 + (r : ℝ) :=
    lt_of_le_of_lt (dist_triangle y u c) (by linarith)
  have hballsub : Metric.closedBall c (r : ℝ) ⊆ Metric.ball y (8 * (r : ℝ)) := by
    intro w hw
    rw [Metric.mem_closedBall] at hw
    rw [Metric.mem_ball]
    calc dist w y ≤ dist w c + dist c y := dist_triangle w c y
      _ < (r : ℝ) + (5 * (r : ℝ) / 2 + (r : ℝ)) := by
          rw [dist_comm c y]; exact add_lt_add_of_le_of_lt hw hyc
      _ ≤ 8 * (r : ℝ) := by linarith
  have hlow : g c ≤ volume (V ∩ Metric.ball y (8 * (r : ℝ))) :=
    measure_mono fun w hw => ⟨hw.1, hballsub hw.2⟩
  set T₀ : Finset E := {c' ∈ T | dist c' x ≤ 9 * (r : ℝ)} with hT₀
  have hT₀T : T₀ ⊆ T := Finset.filter_subset _ _
  have hup : volume (V ∩ Metric.ball x (8 * (r : ℝ))) ≤ ∑ c' ∈ T₀, g c' := by
    refine le_trans (measure_mono ?_) (measure_biUnion_finset_le T₀ _)
    intro w hw
    obtain ⟨c', hc', hwc'⟩ := Set.mem_iUnion₂.mp (hcov hw.1)
    have hwx : dist w x < 8 * (r : ℝ) := by simpa [Metric.mem_ball] using hw.2
    have hwc'' : dist w c' ≤ (r : ℝ) := by simpa [Metric.mem_closedBall] using hwc'
    have hd : dist c' x ≤ 9 * (r : ℝ) := by
      calc dist c' x ≤ dist c' w + dist w x := dist_triangle c' w x
        _ ≤ (r : ℝ) + 8 * (r : ℝ) := by rw [dist_comm c' w]; linarith
        _ = 9 * (r : ℝ) := by ring
    exact Set.mem_biUnion (Finset.mem_filter.mpr ⟨hc', hd⟩) ⟨hw.1, hwc'⟩
  have hcard₀ : T₀.card ≤ 21 ^ n := by
    have hsub : (T₀ : Set E) ⊆ Metric.ball x (10 * (r : ℝ)) := by
      intro c' hc'
      have hd := (Finset.mem_filter.mp (Finset.mem_coe.mp hc')).2
      rw [Metric.mem_ball]
      linarith
    have hsep₀ := dist_ge_of_isSeparated (hsep.subset (by exact_mod_cast hT₀T))
    obtain ⟨-, hcard⟩ :=
      Kakeya.finite_and_card_le_of_separated hrR (by linarith : (0:ℝ) ≤ 10 * (r:ℝ)) x hsep₀ hsub
    have hc21 : ((T₀.card : ℝ)) ≤ (1 + 2 * (10 * (r:ℝ)) / (r:ℝ)) ^ n := by simpa using hcard
    have h21 : (1 + 2 * (10 * (r:ℝ)) / (r:ℝ)) = 21 := by field_simp; ring
    rw [h21] at hc21
    exact_mod_cast hc21
  calc volume (V ∩ Metric.ball x (8 * (r : ℝ)))
      ≤ ∑ c' ∈ T₀, g c' := hup
    _ ≤ ∑ _c' ∈ T₀, 2 * g c := Finset.sum_le_sum fun c' hc' => hcomp c' (hT₀T hc') c hc
    _ = (T₀.card : ℝ≥0∞) * (2 * g c) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((21 ^ n : ℕ) : ℝ≥0∞) * (2 * g c) := by gcongr
    _ = (equalRadiusMultConstant n : ℝ≥0∞) * g c := by
        rw [equalRadiusMultConstant]; push_cast; ring
    _ ≤ (equalRadiusMultConstant n : ℝ≥0∞) *
          volume (V ∩ Metric.ball y (8 * (r : ℝ))) := by gcongr

/-- **The finer ball-net pigeonhole, with the net exposed.** -/
theorem exists_comparableNet {U : Set E} (hU : MeasurableSet U)
    {r : ℝ≥0} (hr : 0 < r) {R : ℝ} (hR : 0 ≤ R) {z : E} (hUsub : U ⊆ Metric.ball z R) :
    ∃ T' : Finset E, (T' : Set E) ⊆ U ∧ Metric.IsSeparated (r : ℝ≥0∞) (T' : Set E) ∧
      (∀ c ∈ T', ∀ c' ∈ T',
        volume (U ∩ Metric.closedBall c (r : ℝ)) ≤
          2 * volume (U ∩ Metric.closedBall c' (r : ℝ))) ∧
      volume U ≤ (ballNetLoss (Module.finrank ℝ E) r R : ℝ≥0∞) *
        volume (U ∩ ⋃ c ∈ T', Metric.closedBall c (r : ℝ)) := by
  classical
  set n := Module.finrank ℝ E with hn
  have hrR : (0:ℝ) < (r:ℝ) := hr
  have hbdd : Bornology.IsBounded U := Metric.isBounded_ball.subset hUsub
  have hUtop : volume U ≠ ⊤ :=
    ne_top_of_le_ne_top (MeasureTheory.measure_ball_lt_top (x := z) (r := R)).ne
      (measure_mono hUsub)
  obtain ⟨T, hTsub, hTsep, hTcover, -⟩ :=
    hbdd.exists_finset_isSeparated_isCover_closedBall hr
  set g : E → ℝ≥0∞ := fun c => volume (U ∩ Metric.closedBall c (r : ℝ)) with hgdef
  have hg : ∀ c ∈ T, g c ≠ ⊤ := fun c _ =>
    ne_top_of_le_ne_top hUtop (measure_mono Set.inter_subset_left)
  obtain ⟨T', hT'T, hsumg, hcomp, -⟩ := ShadedBody.exists_self_dyadic T g hg
  set S : Set E := ⋃ c ∈ T', Metric.closedBall c (r : ℝ) with hSdef
  have hSmeas : MeasurableSet S :=
    Finset.measurableSet_biUnion _ fun c _ => measurableSet_closedBall
  have hT'sep : Metric.IsSeparated (r : ℝ≥0∞) (T' : Set E) :=
    hTsep.subset (by exact_mod_cast hT'T)
  have hballS : ∀ c ∈ T', Metric.closedBall c (r : ℝ) ⊆ S := fun c hc w hw =>
    Set.mem_biUnion hc hw
  refine ⟨T', fun c hc => hTsub (Finset.mem_coe.mpr (hT'T (Finset.mem_coe.mp hc))), hT'sep,
    hcomp, ?_⟩
  have hoverlap2 : ∀ x : E, {c ∈ T' | x ∈ Metric.ball c (2 * (r : ℝ))}.card ≤ 5 ^ n := by
    intro x
    refine Metric.IsSeparated.card_le_pow_of_dist_le (x := x) hr (hT'sep.subset ?_) ?_
    · exact_mod_cast Finset.filter_subset _ _
    · intro c hc
      have hb := (Finset.mem_filter.mp hc).2
      rw [Metric.mem_ball, dist_comm] at hb
      exact hb.le
  have h1 : volume U ≤ ∑ c ∈ T, g c :=
    MeasureTheory.measure_le_sum_measure_inter_of_subset_biUnion volume T
      (fun c => Metric.closedBall c (r : ℝ)) hTcover
  have h3 : ∑ c ∈ T', g c ≤ ((5 ^ n : ℕ) : ℝ≥0∞) * volume (U ∩ S) := by
    have hle : ∀ c ∈ T', g c ≤ volume ((U ∩ S) ∩ Metric.ball c (2 * (r : ℝ))) := by
      intro c hc
      refine measure_mono fun w hw => ⟨⟨hw.1, hballS c hc hw.2⟩, ?_⟩
      exact Metric.closedBall_subset_ball (by linarith) hw.2
    calc ∑ c ∈ T', g c
        ≤ ∑ c ∈ T', volume ((U ∩ S) ∩ Metric.ball c (2 * (r : ℝ))) := Finset.sum_le_sum hle
      _ ≤ ((5 ^ n : ℕ) : ℝ≥0∞) * volume (U ∩ S) :=
          Kakeya.sum_volume_inter_ball_le T' (fun c => c) (fun _ => 2 * (r : ℝ))
            hoverlap2 (hU.inter hSmeas)
  have hcardT : T.card ≤ netCardBound n r R :=
    card_le_netCardBound hrR hR (dist_ge_of_isSeparated hTsep) (hTsub.trans hUsub)
  have hph : (2 * Kakeya.factoringStep1FiberPigeonholeConstant 1 (T.card : ℝ≥0) : ℝ≥0)
      ≤ 2 * Kakeya.factoringStep1FiberPigeonholeConstant 1 ((netCardBound n r R : ℕ) : ℝ≥0) :=
    by gcongr ?_ * ?_ <;> [exact le_rfl; exact pigeonholeConstant_mono hcardT]
  calc volume U ≤ ∑ c ∈ T, g c := h1
    _ ≤ ((2 * Kakeya.factoringStep1FiberPigeonholeConstant 1 (T.card : ℝ≥0) : ℝ≥0) :
          ℝ≥0∞) * ∑ c ∈ T', g c := hsumg
    _ ≤ ((2 * Kakeya.factoringStep1FiberPigeonholeConstant 1
          ((netCardBound n r R : ℕ) : ℝ≥0) : ℝ≥0) : ℝ≥0∞) *
          (((5 ^ n : ℕ) : ℝ≥0∞) * volume (U ∩ S)) :=
        mul_le_mul' (by exact_mod_cast hph) h3
    _ = (ballNetLoss n r R : ℝ≥0∞) * volume (U ∩ S) := by
        rw [ballNetLoss, ← mul_assoc]
        congr 1
        push_cast
        ring

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- **Restricting every shade to a common set does not move the multiplicity on that set.**

This is what makes the inner dyadic band of `ShadedBody.exists_constantMultiplicity_refinement`
stable under every later restriction — the net restriction of
`Kakeya.ThinCase.exists_comparableNet` and the cell restriction of
`Kakeya.ThinCase.exists_cellOuterShading` — and hence what lets conjunct (iii)(b) and the band be
established once and never revisited. The *outer* multiplicity has no such stability; that is the
regress `Kakeya.ThinCase.exists_cellOuterShading` is built to avoid. -/
lemma pointwiseMultiplicity_restrictShade {ι : Type*} (s : Finset ι) (V : ι → ShadedBody E)
    (S : Set E) (hS : MeasurableSet S) {x : E} (hx : x ∈ S) :
    ShadedBody.pointwiseMultiplicity s (fun i => (V i).restrictShade S hS) x
      = ShadedBody.pointwiseMultiplicity s V x := by
  classical
  refine congrArg Finset.card ?_
  ext i
  simp [ShadedBody.shade_restrictShade, hx]

/-! ### Three facts that make a common restriction composable

`Kakeya.ThinCase.pointwiseMultiplicity_restrictShade` above says that restricting every shade to a
common set leaves the multiplicity alone *on that set*. The first lemma here is the same fact
stated from the *defining equation* `(V' i).shade = (V i).shade ∩ S` rather than from the
`ShadedBody.restrictShade` constructor, which is the form the exposed band of
`ShadedBody.exists_constantMultiplicity_refinement_band` and the two later restrictions actually
arrive in; it also only asks for the equation on `s`, so the final inner family may be left
untouched off the retained index set (which conjunct (c) of `Kakeya.ThinCase.factoringApply`
requires).

The other two price the *mass* of a restriction to a net's balls. The ball-net pigeonhole
`Kakeya.ThinCase.exists_comparableNet` bounds the Lebesgue measure of the shaded **union**, but
conjunct (vi) is about the **sum** of the shade volumes, and the two differ by the multiplicity —
which is exactly what the exposed band controls. Passing between them costs the overlap of the
net's own balls: an `r`-separated net has at most `5 ^ n` of its `r`-balls through any one point,
because those centres lie in `closedBall x r ⊆ ball x (2 r)` and
`Kakeya.ThinCase.card_le_netCardBound` bounds an `r`-separated subset of a `2 r`-ball by
`netCardBound n r (2 r) = 5 ^ n`. That `5 ^ n` is the same factor already carried by
`Kakeya.ThinCase.ballNetLoss`. -/

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma pointwiseMultiplicity_of_shade_inter {ι : Type*} (s : Finset ι) (V V' : ι → ShadedBody E)
    (S : Set E) (hV : ∀ i ∈ s, (V' i).shade = (V i).shade ∩ S) {x : E} (hx : x ∈ S) :
    ShadedBody.pointwiseMultiplicity s V' x = ShadedBody.pointwiseMultiplicity s V x := by
  classical
  refine congrArg Finset.card (Finset.filter_congr ?_)
  intro i hi
  rw [hV i hi]
  simp [hx]

lemma netCardBound_two_mul {r : ℝ} (hr : 0 < r) (n : ℕ) :
    netCardBound n r (2 * r) = 5 ^ n := by
  have : (1 + 2 * (2 * r) / r) = 5 := by field_simp; ring
  rw [netCardBound, this]
  exact_mod_cast Nat.ceil_natCast (R := ℝ) (5 ^ n)

/-- **Bounded overlap of the `r`-balls of an `r`-separated net.** -/
lemma sum_volume_inter_closedBall_le_of_isSeparated {r : ℝ≥0} (hr : 0 < r) {T : Finset E}
    (hsep : Metric.IsSeparated (r : ℝ≥0∞) (T : Set E)) {A : Set E} (hA : MeasurableSet A) :
    ∑ c ∈ T, volume (A ∩ Metric.closedBall c (r : ℝ))
      ≤ (5 : ℝ≥0∞) ^ (Module.finrank ℝ E) *
          volume (A ∩ ⋃ c ∈ T, Metric.closedBall c (r : ℝ)) := by
  classical
  have hr' : (0:ℝ) < (r:ℝ) := hr
  set n := Module.finrank ℝ E with hn
  set reg : Set E := ⋃ c ∈ T, Metric.closedBall c (r : ℝ) with hreg
  have hmeas : ∀ c : E, MeasurableSet (A ∩ Metric.closedBall c (r:ℝ)) :=
    fun c => hA.inter measurableSet_closedBall
  have hregmeas : MeasurableSet (A ∩ reg) :=
    hA.inter (Finset.measurableSet_biUnion _ fun c _ => measurableSet_closedBall)
  -- the pointwise overlap count
  have hcount : ∀ x : E, ∑ c ∈ T, (A ∩ Metric.closedBall c (r:ℝ)).indicator (1 : E → ℝ≥0∞) x
      ≤ (A ∩ reg).indicator (fun _ => ((5 : ℝ≥0∞) ^ n)) x := by
    intro x
    have hsum : ∑ c ∈ T, (A ∩ Metric.closedBall c (r:ℝ)).indicator (1 : E → ℝ≥0∞) x
        = ((({c ∈ T | x ∈ A ∩ Metric.closedBall c (r:ℝ)}).card : ℕ) : ℝ≥0∞) := by
      simp [Set.indicator_apply, Finset.sum_boole]
    rw [hsum]
    by_cases hxA : x ∈ A ∩ reg
    · rw [Set.indicator_apply, if_pos hxA]
      set T₀ : Finset E := {c ∈ T | x ∈ A ∩ Metric.closedBall c (r:ℝ)} with hT₀
      have hsub : (T₀ : Set E) ⊆ Metric.ball x (2 * (r:ℝ)) := by
        intro c hc
        simp only [hT₀, Finset.coe_filter, Set.mem_setOf_eq] at hc
        have hd : dist x c ≤ (r:ℝ) := by
          simpa [Metric.mem_closedBall] using hc.2.2
        rw [Metric.mem_ball, dist_comm]
        linarith
      have hsep₀ : ∀ y ∈ (T₀ : Set E), ∀ w ∈ (T₀ : Set E), y ≠ w → (r:ℝ) ≤ dist y w :=
        dist_ge_of_isSeparated (hsep.subset (by
          exact_mod_cast (Finset.filter_subset _ T : T₀ ⊆ T)))
      have hcard := card_le_netCardBound (E := E) hr' (by positivity : (0:ℝ) ≤ 2 * (r:ℝ))
        hsep₀ hsub
      rw [netCardBound_two_mul hr'] at hcard
      exact_mod_cast hcard
    · have hz : ({c ∈ T | x ∈ A ∩ Metric.closedBall c (r:ℝ)}) = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun c hc => ?_
        obtain ⟨hcT, hxc⟩ := Finset.mem_filter.mp hc
        exact hxA ⟨hxc.1, Set.mem_biUnion hcT hxc.2⟩
      rw [hz]
      simp
  calc ∑ c ∈ T, volume (A ∩ Metric.closedBall c (r:ℝ))
      = ∑ c ∈ T, ∫⁻ x, (A ∩ Metric.closedBall c (r:ℝ)).indicator (1 : E → ℝ≥0∞) x :=
        Finset.sum_congr rfl fun c _ => (lintegral_indicator_one (hmeas c)).symm
    _ = ∫⁻ x, ∑ c ∈ T, (A ∩ Metric.closedBall c (r:ℝ)).indicator (1 : E → ℝ≥0∞) x :=
        (lintegral_finsetSum T fun c _ => measurable_const.indicator (hmeas c)).symm
    _ ≤ ∫⁻ x, (A ∩ reg).indicator (fun _ => ((5 : ℝ≥0∞) ^ n)) x := lintegral_mono hcount
    _ = (5 : ℝ≥0∞) ^ n * volume (A ∩ reg) := lintegral_indicator_const hregmeas _

end BallNet

/-! ### The cell outer shading: conjunct (iii)(a) without touching the inner shading

Conjunct (iii)(a) of `Kakeya.ThinCase.factoringApply` asks for constant multiplicity of the
*outer* shaded family, while conjunct (ii) forces every outer shade to contain its block's inner
union and conjunct (v) forces it into the `2 τ₂`-collar of that union. A dyadic band of the
outer multiplicity — the pigeonhole `ShadedBody.exists_constantMultiplicity_refinement` performs
on the outer shading — is therefore *not* available: restricting the outer shades to a band
breaks (ii), and repairing (ii) by restricting the inner shades to the same band breaks (v),
whose right-hand side is the *retained* inner union. The regress is genuine.

The construction below avoids it. Rather than pigeonholing the multiplicity function, it
pigeonholes the **net cells**: on a `w₁/8`-net of the inner union, the number of blocks meeting a
given net ball is a function of the *cell*, not of the point, so making it dyadically constant
makes the outer multiplicity literally constant on the retained region — and the outer shades are
built from whole cells, so (ii) and (v) hold by construction and no inner shade is touched. -/

section CellShading

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
open Classical in
/-- **The number of blocks meeting one net ball.** A function of the *cell*, not of the point,
which is what makes the pigeonhole of `Kakeya.ThinCase.exists_cellOuterShading` stable where a
band of the outer multiplicity is not. -/
noncomputable def cellBlockCount {ω : Type*} (bodies' : Finset ω) (A : ω → Set E) (r : ℝ)
    (c : E) : ℕ :=
  ({j ∈ bodies' | (A j ∩ Metric.closedBall c r).Nonempty}).card

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
open Classical in
/-- **The cell outer shading.**

`A j` is the shaded union of the block over the body `j`, `T` a net of centres and `r` the net
radius. The theorem produces a sub-net `T''` — dyadically pigeonholed so that the number of
blocks meeting a net ball is constant up to a factor `2` along it, at a cost of
`Nat.log 2 bodies'.card + 1` against any weight `f` on the centres — and an outer shading `Sh`
built out of whole cells of a measurable partition subordinate to the net balls of `T''`, with

* `Sh j ⊆ cthickening (2 r) (A j)`, which is conjunct (v) with room to spare;
* `A j ∩ (net region) ⊆ Sh j`, which is conjunct (ii) once the inner shades are restricted to the
  net region;
* every `Sh j` inside the net region, which is the collar hypothesis of
  `Kakeya.ThinCase.centredMult_of_cthickening`, i.e. conjunct (iv);
* **`2`-constant multiplicity**, which is conjunct (iii)(a).

Nothing here restricts the inner shading beyond the common set `⋃ c ∈ T'', closedBall c r`, so
conjuncts (c), (d), (iii)(b) and the inner multiplicity band are untouched. -/
theorem exists_cellOuterShading {ω : Type*} (bodies' : Finset ω) (A : ω → Set E)
    (T : Finset E) (r : ℝ) (f : E → ℝ≥0∞)
    (hf0 : ∀ c ∈ T, cellBlockCount bodies' A r c = 0 → f c = 0) :
    ∃ (T'' : Finset E) (P : E → Set E) (m : ℕ) (Sh : ω → Set E),
      T'' ⊆ T ∧
      (∑ c ∈ T, f c ≤ ((Nat.log 2 bodies'.card + 1 : ℕ) : ℝ≥0∞) * ∑ c ∈ T'', f c) ∧
      -- the measurable partition subordinate to the retained net balls
      (∀ c ∈ T'', P c ⊆ Metric.closedBall c r) ∧
      (∀ c ∈ T'', MeasurableSet (P c)) ∧
      (T'' : Set E).PairwiseDisjoint P ∧
      (⋃ c ∈ T'', P c) = (⋃ c ∈ T'', Metric.closedBall c r) ∧
      -- the dyadic band of the block count along the retained cells
      (∀ c ∈ T'', 2 ^ m ≤ cellBlockCount bodies' A r c ∧
        cellBlockCount bodies' A r c < 2 ^ (m + 1)) ∧
      -- the outer shades are unions of whole cells
      (∀ j, Sh j = ⋃ c ∈ {c ∈ T'' | (A j ∩ Metric.closedBall c r).Nonempty}, P c) ∧
      (∀ j, MeasurableSet (Sh j)) ∧
      (∀ j ∈ bodies', Sh j ⊆ Metric.cthickening (2 * r) (A j)) ∧
      (∀ j ∈ bodies', A j ∩ (⋃ c ∈ T'', Metric.closedBall c r) ⊆ Sh j) ∧
      ((⋃ j ∈ bodies', Sh j) ⊆ ⋃ c ∈ T'', Metric.closedBall c r) ∧
      (∀ x ∈ ⋃ j ∈ bodies', Sh j, ∀ y ∈ ⋃ j ∈ bodies', Sh j,
        ({j ∈ bodies' | x ∈ Sh j}).card ≤ 2 * ({j ∈ bodies' | y ∈ Sh j}).card) := by
  classical
  -- the number of blocks meeting the net ball around `c`
  set beta : E → ℕ := fun c => cellBlockCount bodies' A r c with hbeta
  have hbeta_le : ∀ c, beta c ≤ bodies'.card := fun c => Finset.card_filter_le _ _
  set Bands : Finset ℕ := Finset.range (Nat.log 2 bodies'.card + 1) with hBands
  set band : ℕ → Finset E := fun m => {c ∈ T | Nat.log 2 (beta c) = m ∧ beta c ≠ 0} with hband
  have hmem : ∀ c ∈ T, Nat.log 2 (beta c) ∈ Bands := by
    intro c _
    simp only [hBands, Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.log_mono_right (hbeta_le c)
  obtain ⟨m, -, hmmax⟩ :=
    Finset.exists_max_image Bands (fun m => ∑ c ∈ band m, f c)
      (Finset.nonempty_range_iff.2 (Nat.succ_ne_zero _))
  have hsplit : ∑ c ∈ T, f c ≤ ((Bands.card : ℕ) : ℝ≥0∞) * ∑ c ∈ band m, f c := by
    have hzero : ∑ c ∈ T, f c = ∑ c ∈ {c ∈ T | beta c ≠ 0}, f c := by
      rw [← Finset.sum_filter_add_sum_filter_not T (fun c => beta c ≠ 0) f]
      have hz : ∑ c ∈ {c ∈ T | ¬ (beta c ≠ 0)}, f c = 0 := by
        refine Finset.sum_eq_zero fun c hc => ?_
        obtain ⟨hcT, hc0⟩ := Finset.mem_filter.mp hc
        exact hf0 c hcT (by simpa using hc0)
      rw [hz, add_zero]
    have hcover : ∑ c ∈ {c ∈ T | beta c ≠ 0}, f c = ∑ k ∈ Bands, ∑ c ∈ band k, f c := by
      rw [hband]
      rw [← Finset.sum_biUnion]
      · refine Finset.sum_congr ?_ fun _ _ => rfl
        ext c
        simp only [Finset.mem_biUnion, Finset.mem_filter]
        constructor
        · rintro ⟨hc, hc0⟩
          exact ⟨Nat.log 2 (beta c), hmem c hc, hc, rfl, hc0⟩
        · rintro ⟨k, -, hc, -, hc0⟩; exact ⟨hc, hc0⟩
      · intro a _ b _ hab
        simp only [Function.onFun, Finset.disjoint_left, Finset.mem_filter]
        rintro c ⟨-, hca, -⟩ ⟨-, hcb, -⟩
        exact hab (hca ▸ hcb ▸ rfl)
    rw [hzero, hcover]
    calc ∑ k ∈ Bands, ∑ c ∈ band k, f c
        ≤ ∑ _k ∈ Bands, ∑ c ∈ band m, f c := Finset.sum_le_sum fun k hk => hmmax k hk
      _ = ((Bands.card : ℕ) : ℝ≥0∞) * ∑ c ∈ band m, f c := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- the partition subordinate to the retained net balls
  obtain ⟨P, hPsub, hPmeas, hPdisj, hPunion⟩ :=
    Kakeya.exists_subordinatePartition (band m) (fun c => Metric.closedBall c r)
      (fun c _ => measurableSet_closedBall)
  refine ⟨band m, P, m,
    fun j => ⋃ c ∈ {c ∈ band m | (A j ∩ Metric.closedBall c r).Nonempty}, P c,
    Finset.filter_subset _ _, ?_, hPsub, hPmeas, hPdisj, hPunion,
    ?_, fun j => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hBands, Finset.card_range] using hsplit
  · intro c hc
    obtain ⟨-, hlog, hne0⟩ := Finset.mem_filter.mp hc
    refine ⟨?_, ?_⟩
    · calc (2 : ℕ) ^ m = 2 ^ Nat.log 2 (beta c) := by rw [hlog]
        _ ≤ beta c := Nat.pow_log_le_self 2 hne0
    · calc beta c < 2 ^ (Nat.log 2 (beta c) + 1) :=
            Nat.lt_pow_succ_log_self (by norm_num) (beta c)
        _ = 2 ^ (m + 1) := by rw [hlog]
  · exact fun j => Finset.measurableSet_biUnion _ fun c hc =>
      hPmeas c (Finset.mem_filter.mp hc).1
  · -- (v): each cell is within `2 r` of the block union
    intro j _ x hx
    obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨hcT, hne⟩ := Finset.mem_filter.mp hc
    obtain ⟨a, haA, hac⟩ := hne
    refine Metric.mem_cthickening_of_dist_le x a (2 * r) _ haA ?_
    have hx' : dist x c ≤ r := by
      simpa [Metric.mem_closedBall] using hPsub c hcT hxc
    have ha' : dist a c ≤ r := by simpa [Metric.mem_closedBall] using hac
    calc dist x a ≤ dist x c + dist c a := dist_triangle x c a
      _ ≤ r + r := by rw [dist_comm c a]; linarith
      _ = 2 * r := by ring
  · -- (ii): the block union inside the net region is covered by its own cells
    intro j _ x hx
    obtain ⟨hxA, hxnet⟩ := hx
    have : x ∈ ⋃ c ∈ band m, P c := by rw [hPunion]; exact hxnet
    obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.mp this
    refine Set.mem_iUnion₂.mpr ⟨c, Finset.mem_filter.mpr ⟨hc, ⟨x, hxA, hPsub c hc hxc⟩⟩, hxc⟩
  · -- the outer union lies in the net region
    refine Set.iUnion₂_subset fun j _ => Set.iUnion₂_subset fun c hc => ?_
    have hcT := (Finset.mem_filter.mp hc).1
    exact fun w hw => Set.mem_biUnion hcT (hPsub c hcT hw)
  · -- (iii)(a): the multiplicity is the block count of the (unique) cell containing the point
    have hkey : ∀ x ∈ ⋃ j ∈ bodies', (⋃ c ∈ {c ∈ band m | (A j ∩ Metric.closedBall c r).Nonempty},
        P c), ∃ c ∈ band m,
          ({j ∈ bodies' | x ∈ ⋃ c' ∈ {c' ∈ band m | (A j ∩ Metric.closedBall c' r).Nonempty},
            P c'}) = {j ∈ bodies' | (A j ∩ Metric.closedBall c r).Nonempty} := by
      intro x hx
      obtain ⟨j₀, hj₀, hxj₀⟩ := Set.mem_iUnion₂.mp hx
      obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.mp hxj₀
      have hcT : c ∈ band m := (Finset.mem_filter.mp hc).1
      refine ⟨c, hcT, ?_⟩
      ext j
      constructor
      · intro hj
        obtain ⟨hjb, hxj⟩ := Finset.mem_filter.mp hj
        refine Finset.mem_filter.mpr ⟨hjb, ?_⟩
        obtain ⟨c', hc', hxc'⟩ := Set.mem_iUnion₂.mp hxj
        obtain ⟨hc'T, hne'⟩ := Finset.mem_filter.mp hc'
        have hcc : c' = c := by
          by_contra hne''
          exact Set.not_disjoint_iff.mpr ⟨x, hxc', hxc⟩
            (hPdisj (Finset.mem_coe.mpr hc'T) (Finset.mem_coe.mpr hcT) hne'')
        exact hcc ▸ hne'
      · intro hj
        obtain ⟨hjb, hne'⟩ := Finset.mem_filter.mp hj
        exact Finset.mem_filter.mpr ⟨hjb,
          Set.mem_iUnion₂.mpr ⟨c, Finset.mem_filter.mpr ⟨hcT, hne'⟩, hxc⟩⟩
    intro x hx y hy
    obtain ⟨cx, hcx, hxeq⟩ := hkey x hx
    obtain ⟨cy, hcy, hyeq⟩ := hkey y hy
    rw [hxeq, hyeq]
    have hlogx : Nat.log 2 (beta cx) = m := (Finset.mem_filter.mp hcx).2.1
    have hlogy : Nat.log 2 (beta cy) = m := (Finset.mem_filter.mp hcy).2.1
    have hnex : beta cx ≠ 0 := (Finset.mem_filter.mp hcx).2.2
    have hney : beta cy ≠ 0 := (Finset.mem_filter.mp hcy).2.2
    have hub : beta cx < 2 ^ (m + 1) := by
      calc beta cx < 2 ^ (Nat.log 2 (beta cx) + 1) :=
            Nat.lt_pow_succ_log_self (by norm_num) (beta cx)
        _ = 2 ^ (m + 1) := by rw [hlogx]
    have hlb : (2 : ℕ) ^ m ≤ beta cy := by
      calc (2 : ℕ) ^ m = 2 ^ Nat.log 2 (beta cy) := by rw [hlogy]
        _ ≤ beta cy := Nat.pow_log_le_self 2 hney
    have : beta cx ≤ 2 * beta cy := by
      have h2 : (2 : ℕ) ^ (m + 1) = 2 * 2 ^ m := by ring
      omega
    exact this

end CellShading

end Kakeya.ThinCase

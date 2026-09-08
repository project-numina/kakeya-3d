/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.FrostmanPlankGeometry
public import Kakeya.DimensionThree.Plank.TubePlankNormalisation
public import Kakeya.DimensionThree.Plank.Section6CoarseFactorisation

/-!
# GWZ Section 6 geometry: thickened pullback slabs, transversality, slab non-concentration

Second half of the Section 6 geometry development, split off from
`Kakeya.DimensionThree.Plank.FrostmanPlankGeometry` for file size. It contains the volume estimates for
thickened pullback slabs (S6G19), the coarse/fine fibre slab count (S6G20), and the two
consumer-facing results `Plank.katzTaoTransverseFactorBound` and `Plank.slabNonconcentration_of_factorization` behind
GWZ Proposition 6.6(B).
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Kakeya
open scoped NNReal Real Classical ENNReal

noncomputable section

namespace Plank


/-- The slab with the **same frame** as `S`, thin half-width `θ'`, and centre re-positioned so that it
agrees with `S` in the thin coordinate but is centred at `c` in the two long coordinates:
`c + ⟪S.center - c, S.basis 0⟫ • S.basis 0`.

Re-centring is what makes the dilated slab usable. Enlarging only the thin thickness cannot work,
since the type `Slab` pins the two long thicknesses to `1`, while points of a thickening of `f⁻¹(S)`
overshoot the long constraints of `S` as well. After re-centring at `c = f W.center`, the long
coordinate of `f x` is `⟪f x - f W.center, S.basis j⟫`, bounded by `‖f x - f W.center‖ ≤ 1` for
`x ∈ W`, with no dependence on the thickening radius. -/
def recentredThinSlab {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1)
    (c : EuclideanSpace ℝ (Fin 3)) (θ' : ℝ≥0) (hθ'1 : θ' ≤ 1) : Slab θ' hθ'1 where
  toPrismNDim :=
    PrismNDim.mk' (c + (inner ℝ (S.center - c) (S.basis 0)) • S.basis 0) S.basis ![θ', 1, 1]
  thicknesses_eq := rfl

/-- **The containment behind the dilated-slab route.** A thickening of the pullback, intersected with
`W`, lands in the pullback of the re-centred dilated slab, provided the thin thickness `θ'` absorbs
`θ + r‖m₀‖`.

The thin coordinate is unchanged by re-centring (the shift is parallel to `S.basis 0`), so it is
bounded by `θ + r‖m₀‖` using `Plank.inner_pullbackNormal_sub` and Cauchy--Schwarz against a nearby
point of the pullback. The two long coordinates are bounded by `‖f x - f W.center‖ ≤ 1` and involve no
`r`. -/
theorem subset_preimage_recentredThinSlab {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (W : Plank a b hab hb1)
    {f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)} {κ : ℝ}
    {g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))}
    (hnorm : IsPlankNormalisation W f κ g)
    (hWimg : ∀ x ∈ W.carrier, ‖f x - f W.center‖ ≤ 1)
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1)
    {θ' : ℝ≥0} (hθ'1 : θ' ≤ 1) {r : ℝ} (hr : 0 ≤ r)
    (hthin : (θ : ℝ) + r * ‖pullbackNormal W κ g (S.basis 0)‖ ≤ (θ' : ℝ)) :
    W.carrier ∩ Metric.cthickening r (W.carrier ∩ f ⁻¹' S.carrier)
      ⊆ f ⁻¹' (recentredThinSlab S (f W.center) θ' hθ'1).carrier := by
  intro x hx
  rcases hx with ⟨hxW, hxN⟩
  set c := f W.center
  set n := S.basis 0
  set m := pullbackNormal W κ g n
  set P := recentredThinSlab S c θ' hθ'1
  have hcenter : P.center = c + (inner ℝ (S.center - c) n) • n := rfl
  have hbasis : P.basis = S.basis := rfl
  have hthicknesses : P.thicknesses = ![θ', 1, 1] := rfl
  -- Goal: f x ∈ P.carrier
  rw [Set.mem_preimage, P.mem_carrier_iff, hbasis, hthicknesses]
  intro i
  have h_inner : S.basis.repr (f x -ᵥ P.center) i = inner ℝ (f x -ᵥ P.center) (S.basis i) := by
    rw [S.basis.repr_apply_apply, real_inner_comm]
  rw [h_inner, vsub_eq_sub, hcenter]
  -- three cases: i = 0 (thin coordinate), i = 1, 2 (long coordinates)
  by_cases hi0 : i = 0
  · subst hi0; simp
    -- i = 0: thickness is θ'.  Show that inner ℝ (f x - (c + (inner ℝ (S.center - c) n) • n)) n = inner ℝ (f x - S.center) n
    -- because the shift cancels orthogonally
    have h_eq : inner ℝ (f x - (c + (inner ℝ (S.center - c) n) • n)) n = inner ℝ (f x - S.center) n := by
      calc
        inner ℝ (f x - (c + (inner ℝ (S.center - c) n) • n)) n
            = inner ℝ (f x - c - (inner ℝ (S.center - c) n) • n) n := by
              rw [show f x - (c + (inner ℝ (S.center - c) n) • n) = (f x - c) - (inner ℝ (S.center - c) n) • n by abel]
        _ = inner ℝ (f x - c) n - inner ℝ ((inner ℝ (S.center - c) n) • n) n := by rw [inner_sub_left]
        _ = inner ℝ (f x - c) n - (inner ℝ (S.center - c) n) * inner ℝ n n := by
          rw [inner_smul_left]; simp
        _ = inner ℝ (f x - c) n - (inner ℝ (S.center - c) n) * 1 := by
          rw [real_inner_self_eq_norm_sq, S.basis.norm_eq_one 0]; norm_num
        _ = inner ℝ (f x - c) n - inner ℝ (S.center - c) n := by ring
        _ = inner ℝ (f x - c - (S.center - c)) n := by
          simp [inner_sub_left, sub_sub]
        _ = inner ℝ (f x - S.center) n := by
          simp [sub_sub]
    rw [h_eq]
    set K := W.carrier ∩ f ⁻¹' S.carrier
    have hK_nonempty_or : K = ∅ ∨ K.Nonempty :=
      Set.eq_empty_or_nonempty _
    rcases hK_nonempty_or with (hK_empty | hK_nonempty)
    · -- If K is empty, then cthickening r ∅ = ∅, so hxN gives a contradiction
      rw [hK_empty] at hxN
      rw [Metric.cthickening_empty] at hxN
      exact absurd hxN (Set.notMem_empty _)
    · -- K is nonempty, we can use the Metric.infEDist approach
      have h_mem_cthick : Metric.infEDist x K ≤ ENNReal.ofReal r := by
        rw [← Metric.mem_cthickening_iff]
        exact hxN
      -- Show |inner ℝ (f x - S.center) n| ≤ θ + r * ‖m‖
      have h_bound : |inner ℝ (f x - S.center) n| ≤ θ + r * ‖m‖ := by
        -- For any η > 0, pick ε = η / (‖m‖ + 1) so that (r + ε) * ‖m‖ ≤ r * ‖m‖ + η
        refine le_of_forall_pos_le_add fun η hη => ?_
        have hnm : 0 ≤ ‖m‖ := norm_nonneg _
        set ε := η / (‖m‖ + 1) with hε_def
        have hε_pos : 0 < ε := by
          refine div_pos hη ?_
          nlinarith
        have h_ineq : (r + ε) * ‖m‖ ≤ r * ‖m‖ + η := by
          calc
            (r + ε) * ‖m‖ = r * ‖m‖ + ε * ‖m‖ := by ring
            _ ≤ r * ‖m‖ + ε * (‖m‖ + 1) := by
              gcongr; nlinarith
            _ = r * ‖m‖ + η := by
              dsimp [ε]
              field_simp [show ‖m‖ + 1 ≠ 0 from by nlinarith]
        have h_lt : Metric.infEDist x K < ENNReal.ofReal (r + ε) := by
          calc
            Metric.infEDist x K ≤ ENNReal.ofReal r := h_mem_cthick
            _ < ENNReal.ofReal (r + ε) := by
              rw [ENNReal.ofReal_lt_ofReal_iff (by nlinarith : 0 < r + ε)]
              nlinarith
        obtain ⟨z, hzK, hz_edist⟩ := Metric.infEDist_lt_iff.mp h_lt
        have hz_dist : dist x z < r + ε := by
          have : edist x z = ENNReal.ofReal (dist x z) := edist_dist x z
          rw [this] at hz_edist
          have hpos : 0 < r + ε := by nlinarith
          have := (ENNReal.ofReal_lt_ofReal_iff hpos).mp hz_edist
          exact this
        rcases hzK with ⟨hzW, hzfS⟩
        have hz_fS : f z ∈ S.carrier := hzfS
        have hz_S_mem : |inner ℝ (f z - S.center) n| ≤ (θ : ℝ) := by
          rw [S.mem_carrier_iff] at hz_fS
          have hz0 := hz_fS 0
          have h_inner' : S.basis.repr (f z -ᵥ S.center) 0 = inner ℝ (f z -ᵥ S.center) (S.basis 0) := by
            rw [S.basis.repr_apply_apply, real_inner_comm]
          rw [h_inner', vsub_eq_sub, S.thicknesses_eq] at hz0
          simpa using hz0
        have h_inner_sub : inner ℝ (f x - S.center) n = inner ℝ (f z - S.center) n + inner ℝ (f x - f z) n := by
          rw [show f x - S.center = (f z - S.center) + (f x - f z) by abel, inner_add_left]
        have h_inner_fx_fz_n : inner ℝ (f x - f z) n = inner ℝ (x - z) m :=
          W.inner_pullbackNormal_sub hnorm n x z
        have h_abs_inner : |inner ℝ (f x - f z) n| ≤ dist x z * ‖m‖ := by
          rw [h_inner_fx_fz_n]
          calc
            |inner ℝ (x - z) m| ≤ ‖x - z‖ * ‖m‖ := abs_real_inner_le_norm _ _
            _ = dist x z * ‖m‖ := by rw [dist_eq_norm]
        calc
          |inner ℝ (f x - S.center) n|
              = |inner ℝ (f z - S.center) n + inner ℝ (f x - f z) n| := by rw [h_inner_sub]
          _ ≤ |inner ℝ (f z - S.center) n| + |inner ℝ (f x - f z) n| := abs_add_le _ _
          _ ≤ (θ : ℝ) + dist x z * ‖m‖ := by nlinarith
          _ ≤ (θ : ℝ) + (r + ε) * ‖m‖ := by
            gcongr
          _ ≤ (θ : ℝ) + (r * ‖m‖ + η) := by gcongr
          _ = (θ : ℝ) + r * ‖m‖ + η := by ring
      have h_goal : |inner ℝ (f x - S.center) n| ≤ (θ' : ℝ) := by
        nlinarith
      simpa [hthicknesses] using h_goal
  · by_cases hi1 : i = 1
    · subst hi1; simp
      -- i = 1: long coordinate, thickness 1
      have h_orth : inner ℝ ((inner ℝ (S.center - c) n) • n) (S.basis 1) = 0 := by
        rw [inner_smul_left, S.basis.inner_eq_zero (show (0 : Fin 3) ≠ 1 by decide), mul_zero]
      have h_eq : inner ℝ (f x - (c + (inner ℝ (S.center - c) n) • n)) (S.basis 1) = inner ℝ (f x - c) (S.basis 1) := by
        calc
          inner ℝ (f x - (c + (inner ℝ (S.center - c) n) • n)) (S.basis 1)
              = inner ℝ (f x - c - (inner ℝ (S.center - c) n) • n) (S.basis 1) := by
                rw [show f x - (c + (inner ℝ (S.center - c) n) • n) = (f x - c) - (inner ℝ (S.center - c) n) • n by abel]
          _ = inner ℝ (f x - c) (S.basis 1) - inner ℝ ((inner ℝ (S.center - c) n) • n) (S.basis 1) := by rw [inner_sub_left]
          _ = inner ℝ (f x - c) (S.basis 1) - 0 := by rw [h_orth]
          _ = inner ℝ (f x - c) (S.basis 1) := sub_zero _
      rw [h_eq]
      calc
        |inner ℝ (f x - c) (S.basis 1)| ≤ ‖f x - c‖ * ‖S.basis 1‖ := abs_real_inner_le_norm _ _
        _ = ‖f x - c‖ * 1 := by rw [S.basis.norm_eq_one 1]
        _ = ‖f x - c‖ := by ring
        _ ≤ 1 := hWimg x hxW
        _ = (1 : ℝ) := by norm_num
    · have hi2 : i = 2 := by
        fin_cases i <;> simp at hi0 hi1; tauto
      subst hi2; simp
      -- i = 2: long coordinate, thickness 1
      have h_orth : inner ℝ ((inner ℝ (S.center - c) n) • n) (S.basis 2) = 0 := by
        rw [inner_smul_left, S.basis.inner_eq_zero (show (0 : Fin 3) ≠ 2 by decide), mul_zero]
      have h_eq : inner ℝ (f x - (c + (inner ℝ (S.center - c) n) • n)) (S.basis 2) = inner ℝ (f x - c) (S.basis 2) := by
        calc
          inner ℝ (f x - (c + (inner ℝ (S.center - c) n) • n)) (S.basis 2)
              = inner ℝ (f x - c - (inner ℝ (S.center - c) n) • n) (S.basis 2) := by
                rw [show f x - (c + (inner ℝ (S.center - c) n) • n) = (f x - c) - (inner ℝ (S.center - c) n) • n by abel]
          _ = inner ℝ (f x - c) (S.basis 2) - inner ℝ ((inner ℝ (S.center - c) n) • n) (S.basis 2) := by rw [inner_sub_left]
          _ = inner ℝ (f x - c) (S.basis 2) - 0 := by rw [h_orth]
          _ = inner ℝ (f x - c) (S.basis 2) := sub_zero _
      rw [h_eq]
      calc
        |inner ℝ (f x - c) (S.basis 2)| ≤ ‖f x - c‖ * ‖S.basis 2‖ := abs_real_inner_le_norm _ _
        _ = ‖f x - c‖ * 1 := by rw [S.basis.norm_eq_one 2]
        _ = ‖f x - c‖ := by ring
        _ ≤ 1 := hWimg x hxW
        _ = (1 : ℝ) := by norm_num

/-- **Volume of the thickened pullback, via the dilated slab** — the replacement for the least-width
route to the volume half of S6G19.

`Plank.volumeCthickeningPullbackSlab` above is true and proved, but its least-width hypothesis cannot
be discharged: the honest width bound for `K_{W,S}` is `δ` (see
`Plank.pullbackNormalisedSlabMinWidthOfTube`, and the counterexample in its docstring showing that
`c_tr · a` is false), while the thickening radius is `C_rad · ρ` with `δ ≤ ρ ≤ a`. So the ratio of
radius to width is unbounded and that route is closed.

The route that does work avoids widths entirely. By `Plank.inner_pullbackNormal` the `S.basis 0`
constraint pulls back to the strip `|⟪x - x_c, m₀⟫| ≤ θ`, so thickening by `r` enlarges it to
`|⟪x - x_c, m₀⟫| ≤ θ + r‖m₀‖`, i.e. `N_r(K_{W,S})` lies in the pullback of the slab `S` *dilated in
its thin direction* by the factor `1 + r‖m₀‖/θ`. By `Plank.norm_pullbackNormal_le`,
`‖m₀‖ ≤ κ(C_tang + 2)·θ/a`, and `r = C_rad·ρ ≤ C_rad·a`, so that factor is at most
`1 + C_rad·κ(C_tang + 2)` — an absolute constant, with both `a` and `θ` cancelling. Applying S6G17
(`Plank.volumePullbackNormalisedSlab`) to the dilated slab bounds the volume by
`C_pull · (1 + C_rad κ(C_tang+2)) · θ · |W|`, which is the claim.

The dilated slab must be **re-centred**: enlarging only the thin thickness is not enough, because
points of `N_r(K_{W,S})` also overshoot the two *long* constraints of `S`, whose thickness is pinned to
`1` by the type `Slab`. Moving the centre to `f W.center` in the long directions fixes this: the long
coordinate of `f x` relative to the new centre is `⟪f x - f W.center, S.basis j⟫`, which is at most
`‖f x - f W.center‖ ≤ 1` for `x ∈ W` and carries no `r` at all. Only the thin direction has to absorb
`r‖m₀‖`. See `Plank.recentredThinSlab` and `Plank.subset_preimage_recentredThinSlab`. -/
theorem thickenedPullbackSlabVolume (κ : ℝ) (hκ : 0 < κ) (Ctang Cpull Crad : ℝ≥0)
    (hCpull : 1 ≤ Cpull) (hCrad : 1 ≤ Crad) :
    ∃ Cctr : ℝ≥0, 1 ≤ Cctr ∧
      ∀ {a b ρ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (_ha : 0 < a) (_hρa : ρ ≤ a)
        (W : Plank a b hab hb1)
        (f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3))
        (g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))),
        IsPlankNormalisation W f κ g →
        (∀ x ∈ W.carrier, ‖f x - f W.center‖ ≤ 1) →
        (∀ (θ' : ℝ≥0) (hθ'1 : θ' ≤ 1) (S' : Slab θ' hθ'1),
            volume (W.carrier ∩ f ⁻¹' S'.carrier)
              ≤ (Cpull : ℝ≥0∞) * (θ' : ℝ≥0∞) * volume W.carrier) →
        ∀ (θ : ℝ≥0) (_hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (S : Slab θ hθ1), a / b ≤ θ →
          |inner ℝ (S.basis 0) (g 0)| ≤ (Ctang : ℝ) * (θ : ℝ) →
          volume (W.carrier ∩ Metric.cthickening ((Crad * ρ : ℝ≥0) : ℝ)
              (W.carrier ∩ f ⁻¹' S.carrier))
            ≤ (Cctr : ℝ≥0∞) * (Cpull : ℝ≥0∞) * (θ : ℝ≥0∞) * volume W.carrier := by
  set L : ℝ≥0 := 1 + Crad * Real.toNNReal κ * (Ctang + 2) with hL
  have hκ_real : (Real.toNNReal κ : ℝ) = κ := Real.coe_toNNReal κ hκ.le
  have hκ_nonneg : 0 ≤ κ := hκ.le
  have hL_one : (1 : ℝ≥0) ≤ L := by
    have hpos : (1 : ℝ) ≤ (L : ℝ) := by
      have hpos' : (0 : ℝ) ≤ (Crad : ℝ) * κ * ((Ctang : ℝ) + 2) := by
        positivity
      calc
        (1 : ℝ) ≤ 1 + (Crad : ℝ) * κ * ((Ctang : ℝ) + 2) := by nlinarith
        _ = 1 + (Crad : ℝ) * (Real.toNNReal κ : ℝ) * ((Ctang : ℝ) + 2) := by simp [hκ_real]
        _ = ((1 + Crad * Real.toNNReal κ * (Ctang + 2) : ℝ≥0) : ℝ) := by
          push_cast
          ring
        _ = (L : ℝ) := rfl
    exact_mod_cast hpos
  refine ⟨L, hL_one, ?_⟩
  intro a b ρ hab hb1 ha hρa W f g hnorm hWimg hS17 θ hθ0 hθ1 S hθab htang
  have hθ_nonneg : 0 ≤ (θ : ℝ) := θ.coe_nonneg
  have hρ_nonneg : 0 ≤ (ρ : ℝ) := ρ.coe_nonneg
  have ha_nonneg : 0 ≤ (a : ℝ) := a.coe_nonneg
  have ha_pos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hane : (a : ℝ) ≠ 0 := by linarith
  have hn_norm : ‖S.basis 0‖ = 1 := S.basis.norm_eq_one 0
  have hnorm_m : ‖pullbackNormal W κ g (S.basis 0)‖
      ≤ κ * ((Ctang : ℝ) + 2) * (θ : ℝ) / (a : ℝ) :=
    W.norm_pullbackNormal_le hκ ha hn_norm hθab htang
  set r : ℝ := ((Crad * ρ : ℝ≥0) : ℝ) with hr
  have hr_nonneg : 0 ≤ r := by positivity
  have hr_bound : r ≤ (Crad : ℝ) * (a : ℝ) := by
    dsimp [r]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hρa) (by positivity : 0 ≤ (Crad : ℝ))
  by_cases hcase : (L : ℝ≥0) * θ ≤ 1
  · -- Main case: L * θ ≤ 1, so we can form a dilated slab
    have hθ'1 : L * θ ≤ 1 := hcase
    set θ' : ℝ≥0 := L * θ with hθ'
    set S' : Slab (L * θ) hθ'1 := recentredThinSlab S (f W.center) (L * θ) hθ'1 with hS'
    have hthin : (θ : ℝ) + r * ‖pullbackNormal W κ g (S.basis 0)‖ ≤ ((L * θ : ℝ≥0) : ℝ) := by
      calc
        (θ : ℝ) + r * ‖pullbackNormal W κ g (S.basis 0)‖
            ≤ (θ : ℝ) + ((Crad : ℝ) * (a : ℝ)) * (κ * ((Ctang : ℝ) + 2) * (θ : ℝ) / (a : ℝ)) := by
          have h_mul_bound : r * ‖pullbackNormal W κ g (S.basis 0)‖
              ≤ ((Crad : ℝ) * (a : ℝ)) * (κ * ((Ctang : ℝ) + 2) * (θ : ℝ) / (a : ℝ)) := by
            have h_mul_r : r * ‖pullbackNormal W κ g (S.basis 0)‖
                ≤ (Crad : ℝ) * (a : ℝ) * ‖pullbackNormal W κ g (S.basis 0)‖ :=
              mul_le_mul_of_nonneg_right hr_bound (norm_nonneg _)
            calc
              r * ‖pullbackNormal W κ g (S.basis 0)‖
                  ≤ (Crad : ℝ) * (a : ℝ) * ‖pullbackNormal W κ g (S.basis 0)‖ := h_mul_r
              _ ≤ (Crad : ℝ) * (a : ℝ) * (κ * ((Ctang : ℝ) + 2) * (θ : ℝ) / (a : ℝ)) :=
                mul_le_mul_of_nonneg_left hnorm_m (by positivity : 0 ≤ (Crad : ℝ) * (a : ℝ))
              _ = ((Crad : ℝ) * (a : ℝ)) * (κ * ((Ctang : ℝ) + 2) * (θ : ℝ) / (a : ℝ)) := by ring
          nlinarith
        _ = (θ : ℝ) + (Crad : ℝ) * κ * ((Ctang : ℝ) + 2) * (θ : ℝ) := by
          field_simp [hane]
        _ = (1 + (Crad : ℝ) * κ * ((Ctang : ℝ) + 2)) * (θ : ℝ) := by ring
        _ = ((L : ℝ≥0) : ℝ) * (θ : ℝ) := by
          dsimp [L]
          simp [hκ.le, mul_comm, mul_assoc]
        _ = ((L * θ : ℝ≥0) : ℝ) := by push_cast; ring
    have hsub : W.carrier ∩ Metric.cthickening r (W.carrier ∩ f ⁻¹' S.carrier)
        ⊆ W.carrier ∩ f ⁻¹' S'.carrier := by
      refine Set.subset_inter Set.inter_subset_left ?_
      have := W.subset_preimage_recentredThinSlab hnorm hWimg S hθ'1 hr_nonneg hthin
      -- The lemma returns subset of f⁻¹'(recentredThinSlab...).carrier
      simpa [hS'] using this
    have hvol : volume (W.carrier ∩ f ⁻¹' S'.carrier)
        ≤ (Cpull : ℝ≥0∞) * ((L * θ : ℝ≥0) : ℝ≥0∞) * volume W.carrier :=
      hS17 (L * θ) hθ'1 S'
    calc
      volume (W.carrier ∩ Metric.cthickening r (W.carrier ∩ f ⁻¹' S.carrier))
          ≤ volume (W.carrier ∩ f ⁻¹' S'.carrier) := measure_mono hsub
      _ ≤ (Cpull : ℝ≥0∞) * ((L * θ : ℝ≥0) : ℝ≥0∞) * volume W.carrier := hvol
      _ = (Cpull : ℝ≥0∞) * ((L : ℝ≥0∞) * (θ : ℝ≥0∞)) * volume W.carrier := by
        simp [ENNReal.coe_mul]
      _ = (L : ℝ≥0∞) * (Cpull : ℝ≥0∞) * (θ : ℝ≥0∞) * volume W.carrier := by ring
  · -- Degenerate case: L * θ > 1, use trivial bound
    have hLθ_gt_one : (1 : ℝ≥0) < (L : ℝ≥0) * θ := by
      refine lt_of_not_ge hcase
    have hLθ_one : (1 : ℝ≥0) ≤ (L : ℝ≥0) * θ := le_of_lt hLθ_gt_one
    have hLCθ_one : (1 : ℝ≥0) ≤ L * Cpull * θ := by
      calc
        (1 : ℝ≥0) ≤ L * θ := hLθ_one
        _ = (L * θ) * 1 := by ring
        _ ≤ (L * θ) * Cpull := mul_le_mul_of_nonneg_left hCpull (by positivity : 0 ≤ L * θ)
        _ = L * Cpull * θ := by ring
    have h_one_enn : (1 : ℝ≥0∞) ≤ (L : ℝ≥0∞) * (Cpull : ℝ≥0∞) * (θ : ℝ≥0∞) := by
      calc
        (1 : ℝ≥0∞) = ((1 : ℝ≥0) : ℝ≥0∞) := by simp
        _ ≤ ((L * Cpull * θ : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_le_coe.mpr hLCθ_one
        _ = (L : ℝ≥0∞) * (Cpull : ℝ≥0∞) * (θ : ℝ≥0∞) := by simp [ENNReal.coe_mul]
    have hvol_mono : volume (W.carrier ∩ Metric.cthickening ((Crad * ρ : ℝ≥0) : ℝ)
        (W.carrier ∩ f ⁻¹' S.carrier)) ≤ volume W.carrier :=
      measure_mono Set.inter_subset_left
    calc
      volume (W.carrier ∩ Metric.cthickening ((Crad * ρ : ℝ≥0) : ℝ)
          (W.carrier ∩ f ⁻¹' S.carrier))
          ≤ volume W.carrier := hvol_mono
      _ = (1 : ℝ≥0∞) * volume W.carrier := by simp
      _ ≤ ((L : ℝ≥0∞) * (Cpull : ℝ≥0∞) * (θ : ℝ≥0∞)) * volume W.carrier := by
        gcongr
      _ = (L : ℝ≥0∞) * (Cpull : ℝ≥0∞) * (θ : ℝ≥0∞) * volume W.carrier := by ring


end Plank

end

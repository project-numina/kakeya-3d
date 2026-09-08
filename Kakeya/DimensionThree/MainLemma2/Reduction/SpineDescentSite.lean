/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineDefectDichotomy

/-!
# The site wiring: `Kakeya.ML2Core.DescentInputs` from the existing site data

`Kakeya.ML2Core.descent_disjuncts_of_inputs` closes the descent from the eight fields of
`Kakeya.ML2Core.DescentInputs`.  This file discharges the ones the descent block can discharge and
leaves the rest as **named binders**, so that the run's remaining work is a list a source can tick
off rather than prose.

## The exponent bookkeeping, and why the site runs its package one margin lower

The trial's fixed floor is `δ^{ηin}/2 ≤ lam`, and the descent's ladder must survive `Λ ^ P_max` of decay.  So the *top* family has
to start a margin above the floor: with `lam0 := δ^{ηin−α}/2` the two ladder fields read

```
 base   :  Λ^P · (δ^{ηin}/2)  ≤  δ^{ηin−α}/2        ⟸  Λ^P ≤ δ^{-α}   (T-D5)
 ladder :  δ^{ηin−α}/2 ≤ lam                        ⟸  the site's package at `ηin − α`
```

which is GWZ's own arrangement: the induction carries `λ ≥ Λ^{P−P_max}δ^{η₀}` and
`Λ^{P_max+1} ≤ δ^{-a₀}` re-establishes the trial's fixed `λ ≥ δ^{2η₀}`.  The site
therefore reads `Kakeya.ML2Core.exists_dichotomyLeft_or_window_spine_levels` at the **lowered**
density exponent `ηin − α`, which is free: that theorem is parametric in its `ηin`.

## What this file discharges, and what it does not

Discharged here, from the descent block's own lemmas:

* `top` — the ambient family is admissible on its own hierarchy, `IsClassHomogeneousOn` included
  (`Kakeya.ML2Core.isClassHomogeneousOn_self`);
* `ceiling` — `Kakeya.ML2Core.potential_le_potentialCeil_five`, from `#u ≤ δ^{-4}` and
  `Cu ≤ δ^{-1}`.

Left as binders, because they are the site's or the floor block's: the loss `Λ`'s two properties,
the two cardinality/constant thresholds, the top family's package clauses, the ladder base
(`T-D5` at the call site), and — the only one carrying mathematics — `trial`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Metric ConvexSpaceBody ShadedBody

namespace Kakeya.ML2Core

section Site

variable {ι : Type*} {δ Cu : ℝ≥0} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

end Site

section OuterTransfer

variable {ι : Type*} {δ : ℝ≥0}

/-- The state functionals are monotone in the family, at a fixed shading. -/
theorem stateLeft_mono_family (ε₀ : ℝ) {s u' : Finset ι} (hsub : u' ⊆ s)
    (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (l l' : ℝ≥0) :
    stateLeft δ ε₀ ((u', T, l) : DescentState ι δ)
      ≤ stateLeft δ ε₀ ((s, T, l') : DescentState ι δ) :=
  mul_le_mul' le_rfl (measure_mono (iUnion_shade_subset hsub (fun _ => Set.Subset.refl _)))

theorem stateRight_mono_family (g : ℝ) {β : ℝ} (hβ : 0 ≤ β) {s u' : Finset ι} (hsub : u' ⊆ s)
    (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (l l' : ℝ≥0) :
    stateRight δ g β ((u', T, l) : DescentState ι δ)
      ≤ stateRight δ g β ((s, T, l') : DescentState ι δ) := by
  refine mul_le_mul' (mul_le_mul' le_rfl ?_)
    (measure_mono (iUnion_shade_subset hsub (fun _ => Set.Subset.refl _)))
  exact ENNReal.rpow_le_rpow (by exact_mod_cast Nat.cast_le.mpr (Finset.card_le_card hsub)) hβ

/-- **The outer transfer, `u' → s`**.

The descent runs on the retained family `u'`; `Dichotomy` speaks about `s`.  `hmass` is the chain's
own mass ledger, `K` its loss, and the two absorptions spend `K` on the exits exactly as the
descent's own `Λ ^ P` is spent — one more factor of the same shape, at the same kind of
`δ`-threshold. -/
theorem descent_disjuncts_transfer_to_ambient {s u' : Finset ι} (hsub : u' ⊆ s)
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {l l' : ℝ≥0}
    {ε₀ g ε₀' g' β : ℝ} (hβ : 0 ≤ β) {K : ℝ≥0∞}
    (hmass : stateMass ((s, T, l') : DescentState ι δ)
      ≤ K * stateMass ((u', T, l) : DescentState ι δ))
    (hdisj : stateMass ((u', T, l) : DescentState ι δ)
          ≤ stateLeft δ ε₀ ((u', T, l) : DescentState ι δ) ∨
        stateMass ((u', T, l) : DescentState ι δ)
          ≤ stateRight δ g β ((u', T, l) : DescentState ι δ))
    (habsL : K * (δ : ℝ≥0∞) ^ (-ε₀) ≤ (δ : ℝ≥0∞) ^ (-ε₀'))
    (habsR : K * (δ : ℝ≥0∞) ^ g ≤ (δ : ℝ≥0∞) ^ g') :
    stateMass ((s, T, l') : DescentState ι δ)
        ≤ stateLeft δ ε₀' ((s, T, l') : DescentState ι δ) ∨
      stateMass ((s, T, l') : DescentState ι δ)
        ≤ stateRight δ g' β ((s, T, l') : DescentState ι δ) := by
  rcases hdisj with hL | hR
  · refine Or.inl (hmass.trans ?_)
    refine le_trans (mul_le_mul' le_rfl (hL.trans (stateLeft_mono_family ε₀ hsub T l l'))) ?_
    rw [stateLeft, stateLeft, ← mul_assoc]
    exact mul_le_mul' habsL le_rfl
  · refine Or.inr (hmass.trans ?_)
    refine le_trans (mul_le_mul' le_rfl (hR.trans (stateRight_mono_family g hβ hsub T l l'))) ?_
    rw [stateRight, stateRight]
    calc K * ((δ : ℝ≥0∞) ^ g * (s.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ s, (T i).shade))
        = (K * (δ : ℝ≥0∞) ^ g)
          * ((s.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ s, (T i).shade)) := by ring
      _ ≤ (δ : ℝ≥0∞) ^ g' * ((s.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ s, (T i).shade)) :=
          mul_le_mul' habsR le_rfl
      _ = (δ : ℝ≥0∞) ^ g' * (s.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ s, (T i).shade) := by ring

end OuterTransfer

/-! ## The assembly: the descent's output at the ambient family, from the chain -/

section Assembly

variable {ι : Type*} {δ Cu : ℝ≥0}

/-- **`Dichotomy`'s two disjuncts at the ambient family `s`, from the existing window chain.**

This is the whole site discharge except for the rows marked WAITING  the parameter comparison, and it deliberately targets
`Kakeya.ML2Assembly.Dichotomy`'s own body rather than `hsite`'s existential block: the chain hands
back a hierarchy on `u' ⊆ s`, so `hsite` as cut asks for something the producer does not give
(the parameter comparison), and re-shaping `hsite` needs a condition I do not have.  Everything below is under that question.

The hypotheses, in the order the chain supplies them:

* `hsub`, `hu'ne`, `hlam0`, `hdense` — the retained family, its shading level, its dense shading;
  the chain gives the last **on `T`**, which is why the descent's state is `(u', T, lam)` (the parameter comparison);
* `hball'`, `hmax'` — the ball and Katz–Tao bounds, restricted to `u'` by `maxDensity_mono`;
* `hcard'`, `hCu` — rows 7 and 8;
* `hhomog` — the ambient family of `𝒰` is class-homogeneous on itself
  (`isClassHomogeneousOn_self`), which the caller supplies as `rfl`-level;
* `hbase`, `hladder` — the ladder, at the lowered exponent `ηin − α`;
* **`htrial`** — row 15, the WAITING composite;
* `habsL`, `habsR` — the descent's two absorptions (`absorbL_of_loss_le`, `absorbR_of_loss_le`);
* `houter`, `hKL`, `hKR` — the outer transfer `u' → s` and its own two absorptions. -/
theorem dichotomy_disjuncts_of_chain {s u' : Finset ι}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} (hsub : u' ⊆ s)
    (𝒰 : Tube.UniformTubeSet u' (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    {ε₀ g ε₀' g' β ηin h α : ℝ} {Λ K : ℝ≥0∞} {lam : ℝ≥0}
    (hβ : 0 ≤ β) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hh : 0 < h)
    (hΛ1 : 1 ≤ Λ) (hΛtop : Λ ≠ ⊤)
    (hcard' : (u'.card : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ)))
    (hCu : (Cu : ℝ) ≤ (δ : ℝ) ^ (-(1 : ℝ)))
    (hu'ne : u'.Nonempty)
    (hball' : ∀ i ∈ u', (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hmax' : Kakeya.maxDensity u' (fun i => (T i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-ηin))
    (hlam0 : 0 < lam)
    (hdense : ML2Shaded.HasDenseShading lam u' (fun i => (T i).toShadedBody))
    (hbase : Λ ^ potentialCeil h 5 δ * (((δ : ℝ≥0) ^ ηin / 2 : ℝ≥0) : ℝ≥0∞)
      ≤ (((δ : ℝ≥0) ^ (ηin - α) / 2 : ℝ≥0) : ℝ≥0∞))
    (hladder : (((δ : ℝ≥0) ^ (ηin - α) / 2 : ℝ≥0) : ℝ≥0∞) ≤ (lam : ℝ≥0∞))
    (htrial : IsTrialAtGain ε₀ g β h ηin 𝒰 Λ)
    (habsL : Λ ^ potentialCeil h 5 δ * (δ : ℝ≥0∞) ^ (-ε₀) ≤ (δ : ℝ≥0∞) ^ (-ε₀'))
    (habsR : Λ ^ potentialCeil h 5 δ * (δ : ℝ≥0∞) ^ g ≤ (δ : ℝ≥0∞) ^ g')
    (houter : stateMass ((s, T, (1 : ℝ≥0)) : DescentState ι δ)
      ≤ K * stateMass ((u', T, lam) : DescentState ι δ))
    {ε₀'' g'' : ℝ}
    (hKL : K * (δ : ℝ≥0∞) ^ (-ε₀') ≤ (δ : ℝ≥0∞) ^ (-ε₀''))
    (hKR : K * (δ : ℝ≥0∞) ^ g' ≤ (δ : ℝ≥0∞) ^ g'') :
    stateMass ((s, T, (1 : ℝ≥0)) : DescentState ι δ)
        ≤ stateLeft δ ε₀'' ((s, T, (1 : ℝ≥0)) : DescentState ι δ) ∨
      stateMass ((s, T, (1 : ℝ≥0)) : DescentState ι δ)
        ≤ stateRight δ g'' β ((s, T, (1 : ℝ≥0)) : DescentState ι δ) := by
  have hinner0 :=
    dichotomy_disjuncts_of_trialDescent_level (Adm := TrialAdmissible ηin 𝒰) 𝒰 hβ hΛ1
      (fun x hx => potential_le_potentialCeil_five 𝒰 hx.1 hh hδ0 hδ1 hCu hcard')
      (fun x hx S' hS' W lam' hne htube hshade hhom hlam'0 hdense' =>
        trialAdmissible_of_step 𝒰 hx hS' hne htube hshade hhom hlam'0 hdense')
      (fun x hx hlad => by
        obtain ⟨hsu, hne, hZt, hZs, hhom, hb, hm, hl0, hd⟩ := hx
        exact htrial x.1 hsu x.2.1 x.2.2 hne hZt hZs hhom hb hm hd
          (hd.hasComparableDensities hl0)
          (floor_of_ladder hΛ1 hΛtop (Nat.sub_le _ _) hbase hlad) hcard')
      ((u', T, lam) : DescentState ι δ)
      ⟨Finset.Subset.refl u', hu'ne, fun _ => rfl, fun _ => Set.Subset.refl _,
        isClassHomogeneousOn_self 𝒰, hball', hmax', hlam0, hdense⟩ hladder
  have hinner : stateMass ((u', T, lam) : DescentState ι δ)
        ≤ stateLeft δ ε₀' ((u', T, lam) : DescentState ι δ) ∨
      stateMass ((u', T, lam) : DescentState ι δ)
        ≤ stateRight δ g' β ((u', T, lam) : DescentState ι δ) := by
    rcases hinner0 with hL | hR
    · refine Or.inl (hL.trans ?_)
      rw [stateLeft, stateLeft, ← mul_assoc]
      exact mul_le_mul' habsL le_rfl
    · refine Or.inr (hR.trans ?_)
      rw [stateRight, stateRight]
      calc Λ ^ potentialCeil h 5 δ
            * ((δ : ℝ≥0∞) ^ g * (u'.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ u', (T i).shade))
          = (Λ ^ potentialCeil h 5 δ * (δ : ℝ≥0∞) ^ g)
            * ((u'.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ u', (T i).shade)) := by ring
        _ ≤ (δ : ℝ≥0∞) ^ g' * ((u'.card : ℝ≥0∞) ^ β
            * volume (⋃ i ∈ u', (T i).shade)) := mul_le_mul' habsR le_rfl
        _ = (δ : ℝ≥0∞) ^ g' * (u'.card : ℝ≥0∞) ^ β
            * volume (⋃ i ∈ u', (T i).shade) := by ring
  exact descent_disjuncts_transfer_to_ambient hsub hβ houter hinner hKL hKR

end Assembly

/-! ## The top-level assembly, and the one exponent the interface still owes -/

section TopLevel

universe v

/-- **`Kakeya.ML2Assembly.GeometricCoreAt` from the site, with the open items as binders.**

`hsite` is the whole hypothesis of the run, in one place: for each exponent `β` at which
both partial estimates hold, the site produces its accuracy `ε₁`, its density exponent `η`, **a
`δ`-free uniformity ceiling `Cu₀`**, and — eventually in `δ`, on every admissible family — a
hierarchy, a shading level, the trial at the **margin-shifted** exponents, and the two absorptions
that spend `Λ ^ P` once.

**The descent runs on the retained family `u' ⊆ s`, and the shading is `T`, not `W`**
((C), condition;  the parameter comparison).  Two things about
this block typecheck either way and are provable only one way, so both are recorded here at the
definition:

* the chain (`exists_dichotomyLeft_or_window_spine_levels`) hands back a hierarchy on the
  **retained** family `u' ⊆ s`, never on `s`; the source does the same — the trial runs on the
  prepared family `𝕊'` and transfers back by the mass ledger.  The row
  `stateMass (s,T,1) ≤ K · stateMass (u',T,lam)` **is the direction the chain proves**
  [MEASURED: its ledger reads `lam · c · ∑_{i∈s} |Z_i| ≤ K₀ · ∑_{i∈u'} |Z_i|`, with `s` on the small
  side], with `K = K₀/(lam·c)`;
* the chain's *pointwise* dense shading is on the **ambient** `T`
  (`HasDenseShading lam u' (fun i ↦ (T i).toShadedBody)`); for the refined `W` it gives only an
  aggregate bound.  So the descent's state is `(u', T, lam)` and `W` appears only inside the trial.
  Had the row been written on `W` it would still elaborate — and be unprovable.

The two **outer** absorptions (`K · δ^{-ε₀'} ≤ δ^{-β/2}` and `K · δ^{g'} ≤ δ^{4ν}`) sit **beside**
the descent's own two, not merged with them: the rule that a derived row goes beside its
primitive.  `Kakeya.ML2Core.descent_disjuncts_of_site` remains as the `u' = s` corollary, never as
the primary statement.

**`Cu₀` is quantified before `δ`**: the hierarchy constant is `δ`-free, exactly
as `Kakeya.ML2Core.geometricCoreAt_of_rungMiddleFactor`'s `∀ Cu₀ : NNReal` and
`Kakeya.MultiScaleFac.dividingScalesKatzTao`'s `Cbig` are, and as GWZ fix
`A₀, A₁, C` once.  The row `Cu ≤ Cu₀` is the primitive; the `δ`-dependent
`(Cu : ℝ) ≤ δ^{-1}` is **kept beside it** rather than replaced, because it is what
`Kakeya.ML2Core.potential_le_potentialCeil_five` consumes (it is the `−1` of the exponent `5`).

`descent_disjuncts_of_site` does the rest; the state functionals ignore the shading level
(`stateMass_level` and friends), so the output is `Dichotomy`'s. -/
theorem geometricCoreAt_of_site
    (hsite : ∀ (β ϖ : ℝ) (gain dens : ℝ → ℝ), 0 < β → β ≤ 1 →
      ML2Assembly.Lemma91ParamsAt.{v} β ϖ gain dens →
      KatzTaoEstimate.{v} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{v} (EuclideanSpace ℝ (Fin 3)) β →
      ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∃ Cu₀ : ℝ≥0,
        ∀ᶠ (δ : ℝ≥0) in nhdsWithin 0 (Set.Ioi 0),
          ∀ {ι : Type v} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
            (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
            IsKatzTao s (fun i => (T i).toConvexSpaceBody) ((δ : ℝ≥0∞) ^ (-η)) →
            ShadedBody.fullness s (fun i => (T i).toShadedBody) ≥ δ ^ η →
            (δ : ℝ)⁻¹ ≤ (s.card : ℝ) →
            ∃ u' : Finset ι, u' ⊆ s ∧
            ∃ (Cu : ℝ≥0) (𝒰 : Tube.UniformTubeSet u' (fun i => (T i).toTube)
                (Tube.ssfGridLen δ) Cu) (lam : ℝ≥0) (Λ K : ℝ≥0∞)
                (ε₀ g ε₀' g' ηin h α : ℝ),
              Cu ≤ Cu₀ ∧
              0 < δ ∧ δ < 1 ∧ 0 < h ∧ 1 ≤ Λ ∧ Λ ≠ ⊤ ∧
              (u'.card : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ)) ∧
              (Cu : ℝ) ≤ (δ : ℝ) ^ (-(1 : ℝ)) ∧
              u'.Nonempty ∧
              Kakeya.maxDensity u' (fun i => (T i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-ηin) ∧
              0 < lam ∧
              ML2Shaded.HasDenseShading lam u' (fun i => (T i).toShadedBody) ∧
              (Λ ^ potentialCeil h 5 δ * (((δ : ℝ≥0) ^ ηin / 2 : ℝ≥0) : ℝ≥0∞)
                ≤ (((δ : ℝ≥0) ^ (ηin - α) / 2 : ℝ≥0) : ℝ≥0∞)) ∧
              ((((δ : ℝ≥0) ^ (ηin - α) / 2 : ℝ≥0) : ℝ≥0∞) ≤ (lam : ℝ≥0∞)) ∧
              IsTrialAtGain ε₀ g β h ηin 𝒰 Λ ∧
              (Λ ^ potentialCeil h 5 δ * (δ : ℝ≥0∞) ^ (-ε₀) ≤ (δ : ℝ≥0∞) ^ (-ε₀')) ∧
              (Λ ^ potentialCeil h 5 δ * (δ : ℝ≥0∞) ^ g ≤ (δ : ℝ≥0∞) ^ g') ∧
              stateMass ((s, T, (1 : ℝ≥0)) : DescentState ι δ)
                ≤ K * stateMass ((u', T, lam) : DescentState ι δ) ∧
              (K * (δ : ℝ≥0∞) ^ (-ε₀') ≤ (δ : ℝ≥0∞) ^ (-(β / 2))) ∧
              (K * (δ : ℝ≥0∞) ^ g'
                ≤ (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens))) :
    ML2Assembly.GeometricCoreAt.{v} := by
  refine geometricCoreAt_of_descent (fun β ϖ gain dens hβ0 hβ1 hp hKT hF => ?_)
  obtain ⟨ε₁, hε₁, η, hη0, hη1, Cu₀, hev⟩ := hsite β ϖ gain dens hβ0 hβ1 hp hKT hF
  refine ⟨ε₁, hε₁, η, hη0, hη1, ?_⟩
  filter_upwards [hev] with δ hδ
  intro ι s T hball hKTs hfull hcard
  obtain ⟨u', hsub, Cu, 𝒰, lam, Λ, K, ε₀, g, ε₀', g', ηin, h, α, -, hδ0, hδ1, hh, hΛ1, hΛtop,
    hcardu, hCu, hune, hmax, hlam0, hdense, hbase, hladder, htrial, habsL, habsR,
    houter, hKL, hKR⟩ := hδ s T hball hKTs hfull hcard
  exact dichotomy_disjuncts_of_chain hsub 𝒰 hβ0.le hδ0 hδ1 hh hΛ1 hΛtop hcardu hCu hune
    (fun i hi => hball i (hsub hi)) hmax hlam0 hdense hbase hladder htrial habsL habsR
    houter hKL hKR

end TopLevel

/-! ## The left margin is necessary, not merely convenient -/

section LeftMargin

variable {ι : Type*} {δ : ℝ≥0}

end LeftMargin

end Kakeya.ML2Core

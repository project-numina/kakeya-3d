/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.VeryNotStickyCase
public import Kakeya.DimensionThree.MainLemma2.SetupAbsorption
public import Kakeya.DimensionThree.MainLemma2.ThinEstimates
public import Kakeya.DimensionThree.MainLemma2.BallJoint
public import Kakeya.DimensionThree.Plank.Geometry
public import Kakeya.Thickness.Volume

/-!
# O5 as it stood was false in the non-slab regime: the refutation, and the repaired clause pinned

**What this file establishes.** The clause
`Kakeya.VeryNotSticky.CaseScale.transverseFill_fullness` (blueprint obligation **O5** of
Configuration `hyp:ml2thinsetup`, the fullness `λ(𝒫, Y_𝒫) ⪆ (a')^η` of the plank family that
GWZ feed to Lemma 6.13, GWZ, where the `⪆` is rendered as a
plain `≥` with constant `1`) **without a transverse guard or a fixed middle dimension** — unguarded, with the
middle plank dimension `b'` unpinned — is **false** for every configuration in the non-slab
regime `cfg.b ≤ δ^{2·exscal}`, for every `bd`, every thin ball `tb`, and every sufficiently
small `δ`. That is `Kakeya.VeryNotSticky.false_of_transverseFill_fullness`, which takes the old
clause verbatim as its hypothesis `hO5` and is kept here as the compiled record of the refuted
text.

**The repair .**
The live field now carries the transverse-case guard `δ^{-τ'} a/b ≤ 1` (GWZ invoke Lemma 6.13
only when `θ ≥ δ^{-τ'} a/b`, , and `θ ≤ 1`) and the *upper* pin `b' ≤ C₀ (b/r₁)` beside
the two pins on `a'`, at the unchanged exponent `cfg.η`. Its exact text is pinned below as
`Kakeya.VeryNotSticky.statement_of_universal_caseScale_O5`, with
`Kakeya.VeryNotSticky.statement_of_universal_caseScale_O5_pinned` checking that the field is
that proposition and nothing else (the `statement_of_universal_*` device of
`Kakeya.ThinCase.Refute.statement_of_universal_loc`: a plain tripwire survives a binder added
in lockstep, this does not).

Their content survives as
`false_of_transverseFill_fullness` (the mathematics) and as the ledger fact that *both*
producers of a `Kakeya.VeryNotSticky` in the tree
(`Kakeya.VeryNotSticky.eventually_exists_veryNotSticky_of_localMass` through
`Kakeya.VeryNotSticky.exists_veryNotSticky_of_rhoCount`, and
`Kakeya.VeryNotSticky.eventually_exists_veryNotSticky` through
`Kakeya.VeryNotSticky.exists_veryNotSticky_of_data`, each with `hdims := ⟨le_rfl, le_rfl, _⟩`
on a singleton factoring part) set `a = b = δ`; the arithmetic lemma `caseParams_nonslab_gap`
they shared is kept, being true and independent of the clause.

**The argument** (`Kakeya.VeryNotSticky.false_of_transverseFill_fullness`). The plank family
`SP` in the old O5 is universally quantified with the middle plank dimension `b'` *unpinned*
(`{a' b'} {hab' : a' ≤ b'} {hb1' : b' ≤ 1}`): only `a'` is tied to `a / r₁`. Take
`a' := a / r₁`, `b' := 1`, `t := tb.bodies'`, and for `SP i` the axis-aligned
`a' × 1 × 1` prism centred at `0` (`PrismNDim.mk'`) carrying a measurable shade of volume
exactly `|Y_{𝕎'_B}(W_i)| / (2 r₁)^3` (`Kakeya.VeryNotSticky.exists_subset_volume_eq`), which
is what the transport pin demands. Each body shade has volume
`≤ C_{vol}(3) · 8 · C₀^3 · r₁ · b · a`
(`Kakeya.ThinCase.ThinBall.W_le_cthickening`, `ConvexSpaceBody.volume_cthickening_le`,
`volume_le_prod_thickness`, `BallData.bodies_thickness`), while every plank carrier has volume
`8 a'` (`ShadedPlank.volume_carrier`); so the plank fullness is at most
`C_{vol}(3) · C₀^3 · b / (8 r₁) ≤ C_{vol}(3) · C₀^3 · r₁ / 8` in the non-slab regime, and
`CaseScale.transverse_fill` caps `C₀^3 ≤ δ^{-η/2}`. The old O5 demands `(a')^η ≥ (δ/r₁)^η =
δ^{(1-exscal)η}`; since `(3/2 - exscal)·η < exscal` (`CaseParams.slabDensity : 3η < exscal`
with `exscal < 1/2`), the two bounds are incompatible for all small `δ`.

Nothing here refutes the *repaired* clause, and nothing here bears on the exponent question
(plan §4.1; ruled on separately, (c)).
-/

@[expose] public section

open scoped NNReal ENNReal

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set Topology Filter ShadedBody
open scoped NNReal ENNReal

universe u


/-! ### The repaired clause, pinned

The `statement_of_universal_*` device (`Kakeya.ThinCase.Refute.statement_of_universal_loc`,
`Kakeya.Prop66BScale.statement_of_universal_prop66B_essDistinct`): the licensed text of the
field is a named `Prop`, and a theorem checks that the field *is* that proposition. A later
change to the field in either direction — a binder dropped, a pin removed, the guard weakened,
an exponent moved — fails to elaborate here, which a plain tripwire on a consumer would not
notice when the change is made in lockstep. -/

/-- **The clause O5 with its thin and transverse guards, as a named `Prop`**: the thin
guard `a ≤ δ^{1-τ}` (GWZ: the definition of §9.5's case) and the transverse guard
`δ^{-τ'} a/b ≤ 1` in front (GWZ: `θ ≤ 1`), the two pins on `a'` and the *upper* pin
`b' ≤ C₀ (b/r₁)` on `b'`, the two pins on `t` and `SP`, and the conclusion at the unchanged
exponent `cfg.η`. It is the text of `Kakeya.VeryNotSticky.CaseScale.transverseFill_fullness`
verbatim, at the parameters `(cfg, bd, τ, τ', C)` the field reads. -/
def statement_of_universal_caseScale_O5 (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
    (τ τ' : ℝ) (C : ℝ≥0) : Prop :=
  cfg.a ≤ cfg.δ ^ (1 - τ) →
    cfg.δ ^ (-τ') * (cfg.a / cfg.b) ≤ 1 →
    ∀ (B : bd.bι) (_hB : B ∈ bd.bs)
    (tb : ThinCase.ThinBall C bd.C₀ (bd.segs B) bd.Y (bd.bodies B) bd.Wb bd.blk
      cfg.δ cfg.a (2 * cfg.η))
    {a' b' : ℝ≥0} {hab' : a' ≤ b'} {hb1' : b' ≤ 1}
    (t : Finset bd.ω) (SP : bd.ω → ShadedPlank a' b' hab' hb1'),
    t ⊆ tb.bodies' →
    bd.C₀⁻¹ * (cfg.a / cfg.r₁) ≤ a' → a' ≤ bd.C₀ * (cfg.a / cfg.r₁) →
    b' ≤ bd.C₀ * (cfg.b / cfg.r₁) →
    ((plankSelectionConstant bd.C₀ : ℝ≥0∞))⁻¹ *
        (∑ i ∈ tb.bodies', volume (tb.W i).shade) ≤ ∑ i ∈ t, volume (tb.W i).shade →
    (∀ i ∈ t, volume (ShadedPlank.bodies SP i).shade * ENNReal.ofReal ((2 * (cfg.r₁ : ℝ)) ^ 3)
      = volume (tb.W i).shade) →
    a' ^ (16 * cfg.η) ≤ ShadedBody.fullness t (ShadedPlank.bodies SP)


end Kakeya.VeryNotSticky

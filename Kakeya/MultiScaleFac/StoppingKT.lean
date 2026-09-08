/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.MultiScaleFac.Homogenize
public import Kakeya.ChainUniform
public import Kakeya.MultiScaleFac.Clump
public import Kakeya.MultiScaleFac.FibreDensity
public import Kakeya.FibreCommon
public import Kakeya.Thickness.ConvexSpaceBody
public import Kakeya.Sticky
public import Kakeya.Uniform
public import Mathlib.Tactic.Linarith.NNRealPreprocessor
public import Kakeya.MultiScaleFac.Stopping
public import Kakeya.MultiScaleFac.Loss
public import Kakeya.Uniform.ParentBodyDensity
public import Kakeya.Tube.ChainScale
public import Kakeya.Tube.Nets
public import Kakeya.KatzTao
public import Kakeya.Frostman
public import Kakeya.Mathlib.Finset
public import Kakeya.Density
public import Kakeya.Tube.Basic
public import Kakeya.MultiScaleFac.RefineKT

/-!
# The half-(B) stopping time, hoisted and banded

The Katz-Tao stopping time with its constants hoisted before `δ`, its banded variant, and the
quadratic loss accounting both are displayed at.

This module is the merge of the former `MultiScaleRefineKTHoisted`, `MultiScaleStoppingKTBand`,
`SsfLossQuad`.  Each keeps its own section, so its file-level `open`s and `variable`s stay confined
to it. -/

/-!
# The Katz-Tao stopping time carrying a homogenization band

The stopping time of `Kakeya/MultiScaleFac/StoppingKT.lean` returns a grid-uniform system on which
the block bound and the terminal alternative hold.  The amended dichotomy needs one more clause on
that same family: the paired homogenization band of
`Kakeya.Homogenize.exists_homogenizing_pass_gridUniform`.

Neither order of the two operations works on its own.  A band established *before* the stopping time
does not survive its refinements, and the stopping time's own terminal alternative does not survive
a band established *afterwards*: `Kakeya.maxDensity` only falls when members are deleted, and both
operations delete, while the failing half of the terminal test compares `tL.card` with the number of
passing nodes and moves under any deletion.  The band therefore has to be established inside each
refinement step, as its last operation.

That is what this file does, and the one structural obstruction it has to clear is the *constant*.
A homogenizing pass inflates the grid-uniform constant, so the composite of a refinement step and a
pass cannot preserve any single constant unless the refinement step's output constant is
independent of its input.  It is: the re-uniformization
`Kakeya.MultiScaleFac.exists_uniformize_subfamily_hoisted` hands back a system with a canonical
constant `Cu₀` whatever the constant of the system it was run against.  So
`Kakeya.MultiScaleFac.exists_refined_cutKT_hoisted_in` takes an arbitrary input constant and returns
`Cu₀`, and the pass turns `Cu₀` into `gridUniformBandConst Cu₀ 2`; the state of the stopping time is
read at that constant, and the composite maps it to itself.

The per-round cost gains one factor `(1 - log δ)^{2 (Mgrid+2)(Mgrid+1)}`, quadratic in the grid
length where the refinement step's own factor is linear.  It is absorbed by `gridLoss`, whose
polylogarithmic exponent is quadratic in `ssfGridLen δ` for exactly this reason, and the number of
rounds is at most `N + 1` with `N` fixed before `δ`, so `Kakeya.MultiScaleFac.gridLoss_pow` keeps
the accumulated cost a `gridLoss`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Real Metric ConvexSpaceBody
open Kakeya.Homogenize
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya
open scoped NNReal ENNReal

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

universe u

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

variable {ι : Type*}

/-! ### The band, as a predicate on a grid-uniform system -/

open scoped Classical in
/-- **The paired homogenization band carried by a grid-uniform system**. For every pair of levels
`a`, `c` of the grid and every level-`a` node in use,
the maximal density of the level-`c` nodes met by the class of that node lies in
`[Φ a c, C₁ · Φ a c]`.  Naming it as a predicate lets it be threaded through the abstract run. -/
def PairBandOn {δ : ℝ≥0} (t : Finset ι) {T : ι → Tube δ E} {Mgrid : ℕ} {Cv : ℝ≥0}
    (𝒢 : GridUniform t T Mgrid Cv) (C₁ : ℝ≥0) (Φ : ℕ → ℕ → ℝ≥0∞) (M : ℕ) : Prop :=
  ∀ a ≤ M, ∀ c ≤ M, ∀ j ∈ 𝒢.cover.indexSet a,
    Φ a c ≤ Kakeya.maxDensity
              ((coverClass t (𝒢.cover.assign a) j).image (𝒢.cover.assign c))
              (fun j' => (𝒢.cover.tube c j').toConvexSpaceBody) ∧
      Kakeya.maxDensity
          ((coverClass t (𝒢.cover.assign a) j).image (𝒢.cover.assign c))
          (fun j' => (𝒢.cover.tube c j').toConvexSpaceBody) ≤ (C₁ : ℝ≥0∞) * Φ a c

/-! ### Transport along a refined grid-uniform system -/


/-! ### The refinement step with its input constant freed -/


/-! ### The stopping-time run with the band in the state -/


/-! ### Numerical preliminaries for the accumulated loss -/

omit [Nontrivial E] in
/-- **The band weakens in its ratio**.  A two-sided bracket at
ratio `C₁` is one at any larger ratio, the lower half being untouched. -/
theorem PairBandOn.mono {δ : ℝ≥0} {t : Finset ι} {T : ι → Tube δ E} {Mgrid : ℕ} {Cv : ℝ≥0}
    {𝒢 : GridUniform t T Mgrid Cv} {C₁ C₁' : ℝ≥0} (hC : C₁ ≤ C₁') {Φ : ℕ → ℕ → ℝ≥0∞}
    {M : ℕ} (h : PairBandOn t 𝒢 C₁ Φ M) : PairBandOn t 𝒢 C₁' Φ M := fun a ha c hc j hj =>
  ⟨(h a ha c hc j hj).1,
    (h a ha c hc j hj).2.trans (mul_le_mul_left (by exact_mod_cast hC) (Φ a c))⟩


/-! ### One refinement step followed by one homogenizing pass -/


/-! ### The banded stopping time -/


/-! ### The clause the amended dichotomy consumes -/


/-! ### The threshold the accumulated loss is absorbed at -/


end MultiScaleFac

end Kakeya

end

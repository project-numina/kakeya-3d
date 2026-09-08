/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.MultiScaleFac.Clump
public import Kakeya.ChainUniform
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
public import Kakeya.MultiScaleFac.StoppingKT
public import Kakeya.MultiScaleFac.Clamp
public import Kakeya.MultiScaleFac.GapsKT
public import Kakeya.GridScale
public import Kakeya.MultiScaleFac.Bridge
public import Kakeya.MultiScaleLoss
public import Kakeya.MultiScaleFac.GapsA

/-!
# GWZ Lemma 7.7, the dividing-scales dichotomy

The two statements that Sections 8 and 9 consume.  Only the statements are here; the machinery
they are assembled from is `Kakeya/MultiScaleFac/`.

Three conventions are shared by both halves.  The hierarchy is carried on GWZ's own grid of length
`Tube.ssfGridLen δ = ⌈log log 1/δ⌉`, leaving `N` its single role of bounding the number of
stopping-time steps.  Every loss is the displayed `StickyKakeya.totalLoss`, absorbed by the consumer
at whatever accuracy it can afford (`StickyKakeya.exists_threshold_totalLoss_le`).  And every bullet
of alternative (ii) is universal and computed in the returned hierarchy: the upper bounds at the
grid indices of a block `a < b`, the lower bound at every real scale `ρ` in the window.  The halves
take that last bullet in opposite directions — (A) fixes the fine family and runs the container over
the concentric `ρ`-rescales of a level-`b` node, GWZ's `T_ρ ∈ 𝕋_ρ` and not an arbitrary container,
against which it would be false; (B) fixes the coarse node
and runs the family over `ρ` — which the inheritance asymmetry of GWZ Remark 3.3 forces rather than
merely suggests.

## Two forms of (A), and which one to consume

`StickyKakeya.dividingScalesFrostman_unbundled` is the statement as the proof produces it, with
alternative (ii) spelled out as a chain of conjunctions.  `StickyKakeya.dividingScalesFrostman` is
the same theorem with that chain bundled into the named predicate
`StickyKakeya.IsFrostmanDividingBlock`, and is derived from the unbundled form by
destructuring alone — the two can therefore never drift apart.  Section 8 consumes the bundled
form: it names the predicate in its own hypotheses instead of transcribing the conjunction, and
reads the individual bullets through the structure's field names.

(B) is left unbundled; nothing yet consumes it through a named predicate.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Real Metric
open scoped Topology NNReal ENNReal
open Tube
open Kakeya.StickyKakeya
open Kakeya.MultiScaleFac

universe u

namespace StickyKakeya

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- **Alternative (ii) of GWZ Lemma 7.7(A), as a named predicate** (blueprint
`dividingScalesLemmaA`, Conclusion (ii)).

This is *literally* the second disjunct of `StickyKakeya.dividingScalesFrostman_unbundled`,
extracted so that the consumers in Section 8 can name it instead of transcribing it; the bundled
form of the dichotomy, `StickyKakeya.dividingScalesFrostman`, is obtained from the unbundled one by
destructuring alone, so the two cannot drift apart.  `𝒰'` is the hierarchy the dichotomy returns,
`a < b ≤ ssfGridLen δ` are the two grid indices of the block (`a` the coarse end, `b` the fine end)
and `m < N` is the exponent index.  `Cb` is the constant of the three bounds, `K` the
polylogarithmic exponent and `c` the grid-gap exponent; the dichotomy instantiates `Cb` at the same
constant `C` that governs the hierarchy, but a consumer holding an already-absorbed constant may
use a different one.

**Everything is computed in `𝒰'`.**  The classes and node families are those of the returned
hierarchy, never of the input family.

**The losses are subpolynomial.**  All three bounds carry `StickyKakeya.totalLoss Cb K c δ`,
which covers both the per-level re-uniformizations and the transports across grid gaps, and
which a consumer may absorb into a `∀ᶠ δ in 𝓝[>] 0` at any fixed power it can afford
(`StickyKakeya.exists_threshold_totalLoss_le`).

**The container of the lower bound is the concentric rescale.**  It is GWZ's `T_ρ ∈ 𝕋_ρ`, not an
arbitrary `ρ`-tube containing the node: read against an arbitrary container the bullet is false,
since a container meeting a single level-`b` node pins the Frostman constant to `O(1)` against a
left-hand side that is a genuine power of `δ⁻¹`.  The
arbitrary-container reading §8 consumes is a consequence of this sharper one, obtained by enlarging
the container at the cost of a further `scaleGapLoss` factor, so nothing is lost by stating the
sharper form here.

`N` is not the grid length; the hierarchy lives on the grid of length `ssfGridLen δ`, and `N`
bounds the exponent index `m` alone. -/
structure IsFrostmanDividingBlock {ι : Type u} {δ : ℝ≥0} {s' : Finset ι} {T : ι → Tube δ E}
    {C : ℝ≥0} (𝒰' : UniformTubeSet s' T (ssfGridLen δ) C) (Cb : ℝ≥0) (K c : ℕ) (η : ℕ → ℝ)
    (ε : ℝ) (a b m N : ℕ) : Prop where
  /-- The exponent index lies in the ladder. -/
  exponent_lt : m < N
  /-- The block runs from the coarse index `a` to the strictly finer index `b`. -/
  coarse_lt_fine : a < b
  /-- The fine index is a grid index of the `⌈log log 1/δ⌉`-grid. -/
  fine_le : b ≤ ssfGridLen δ
  /-- The two ends of the block are separated by at least `δ ^ ε`. -/
  separated : (gridScale δ (ssfGridLen δ) b : ℝ)
    ≤ (δ : ℝ) ^ ε * (gridScale δ (ssfGridLen δ) a : ℝ)
  /-- First bullet: the leaves assigned to a fine node are Frostman in it. -/
  frostman_leaves : ∀ j ∈ 𝒰'.cover.indexSet b,
    ConvexSpaceBody.frostmanConstant (coverClass s' (𝒰'.cover.assign b) j)
        (fun i => (T i).toConvexSpaceBody) (𝒰'.cover.tube b j).toConvexSpaceBody
      ≤ (Cb : ℝ≥0∞) * totalLoss Cb K c δ *
          ENNReal.ofReal (((gridScale δ (ssfGridLen δ) b : ℝ) / (δ : ℝ)) ^ η m)
  /-- Second bullet: the fine nodes under a coarse node are Frostman in it. -/
  frostman_nodes : ∀ j ∈ 𝒰'.cover.indexSet a,
    ConvexSpaceBody.frostmanConstant (𝒰'.nodesUnder b a j)
        (fun j' => (𝒰'.cover.tube b j').toConvexSpaceBody)
        (𝒰'.cover.tube a j).toConvexSpaceBody
      ≤ (Cb : ℝ≥0∞) * totalLoss Cb K c δ *
          ENNReal.ofReal (((gridScale δ (ssfGridLen δ) a : ℝ)
            / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ η m)
  /-- Third bullet: at every real scale `ρ` of the `ε`-window and at *every* node of level `b`,
  the matching lower bound holds inside the concentric `ρ`-rescale of that node, with the
  subpolynomial loss `StickyKakeya.totalLoss`. -/
  frostman_lower : ∀ ρ : ℝ≥0,
    (gridScale δ (ssfGridLen δ) b : ℝ)
        * ((gridScale δ (ssfGridLen δ) a : ℝ)
            / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ ε ≤ (ρ : ℝ) →
    (ρ : ℝ) ≤ (gridScale δ (ssfGridLen δ) a : ℝ)
        * ((gridScale δ (ssfGridLen δ) b : ℝ)
            / (gridScale δ (ssfGridLen δ) a : ℝ)) ^ ε →
    ∀ j ∈ 𝒰'.cover.indexSet b,
      ENNReal.ofReal (((ρ : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ η (m + 1))
        ≤ (Cb : ℝ≥0∞) * totalLoss Cb K c δ *
            ConvexSpaceBody.frostmanConstant
              (𝒰'.nodesIn b ((𝒰'.cover.tube b j).rescale ρ).toConvexSpaceBody)
              (fun j' => (𝒰'.cover.tube b j').toConvexSpaceBody)
              ((𝒰'.cover.tube b j).rescale ρ).toConvexSpaceBody


end StickyKakeya

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.CoarseBallUpstreamW50
public import Kakeya.DimensionThree.MainLemma1.ScalarFactorization
public import Kakeya.Factoring.RhoFreeParentCount

/-!
This is the setup-safe packet boundary for the endpoint coarse consumer.  It
contains exactly the fields which are needed after the hierarchy packet has
been assembled: the selected singleton certificate and the radius-four (or
radius-`R`) parent containment.  In particular, it deliberately does not
mention the historical `EndpointHierarchySelectedPacket`, whose source file
is not a Lean `module` and therefore cannot be imported by `CaseTwo`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Convexity ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya.ml1Boot.W48EndpointPacketHierarchyModuleBridgeSafe

noncomputable section

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

structure EndpointSelectedCoarseSetupW48
    (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (iota : Type u) [DecidableEq iota]
    (delta sigma rho : ℝ≥0) (R : ℝ) where
  c : ℝ≥0∞
  L : ℝ≥0∞
  amb : Finset iota
  act : Finset iota
  act' : Finset iota
  V : iota → ShadedTube sigma E
  Z' : iota → ShadedTube sigma E
  pMap : iota → iota
  p : iota
  k0 : iota
  Vrho : iota → Tube rho E
  tAct : Finset iota
  Zrho : iota → ShadedTube rho E
  lamP : ℝ≥0
  lamF : ℝ≥0
  selected : IsOneScaleSelected c L amb act V ({p} : Finset iota) Vrho pMap
    act' Z' tAct Zrho k0 lamP lamF
  parentBall : (Vrho p).carrier ⊆ Metric.closedBall (0 : E) R

/-!
Apply the module-safe singleton consumer to a packet whose construction is
performed by the caller.  This theorem is the replacement for the old bridge:
all hierarchy-specific fields stay on the producer side, while `CaseTwo` only
imports this declaration and supplies the two retained fields above.
-/

end
end Kakeya.ml1Boot.W48EndpointPacketHierarchyModuleBridgeSafe

end

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceParameterChoice
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineDefectPotential
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceSmallness

/-!
# Full source indices and the source potential anchor

Source indices range from one to N + 1. The total natural-index function below
is not the separately chosen source input exponent called eta_0.
-/

@[expose] public section

namespace Kakeya.ML2Assembly

universe u


/-- The full finite index map and both endpoint pairs. -/
structure SourceIndexBookkeeping (N : Nat) (q eta : Nat -> ℝ) : Prop where
  count_pos : 1 <= N
  window_index_iff : forall m : Nat,
    Iff (m < N) (And (1 <= m + 1) (m + 1 <= N))
  window_inverse_iff : forall J : Nat,
    Iff (And (1 <= J) (J <= N)) (And (J - 1 < N) ((J - 1) + 1 = J))
  ladder_index_iff : forall j : Nat,
    Iff (And (1 <= j) (j <= N + 1)) (And (j - 1 <= N) ((j - 1) + 1 = j))
  ladder_identification : forall j : Nat, 1 <= j -> j <= N + 1 -> eta j = q (j - 1)
  selected_pair : forall m : Nat, m < N ->
    (eta (m + 1), eta (m + 2)) = (q m, q (m + 1))
  bottom_pair : (eta 1, eta 2) = (q 0, q 1)
  top_pair : (eta N, eta (N + 1)) = (q (N - 1), q N)

/-- Source-indexed ladder properties and the two separately identified anchors. -/
structure SourceLadderAnchorBounds (beta e : ℝ) (N : Nat) (eta : Nat -> ℝ)
    (hSrc oldH : ℝ) : Prop where
  count_pos : 1 <= N
  div_pos : 0 < e
  ladder_pos : forall j : Nat, 1 <= j -> j <= N + 1 -> 0 < eta j
  ladder_mono : MonotoneOn eta (Set.Icc 1 (N + 1))
  ladder_top : eta (N + 1) = e
  ladder_le_div : forall j : Nat, 1 <= j -> j <= N + 1 -> eta j <= e
  ladder_separation : forall J : Nat, 1 <= J -> J <= N ->
    eta J <= e ^ 2 * eta (J + 1) / 100
  source_anchor_formula : hSrc = eta 1 * e ^ 2 / 8
  source_anchor_pos : 0 < hSrc
  old_anchor_formula : oldH = eta 2 * e ^ 2 / 8


end Kakeya.ML2Assembly

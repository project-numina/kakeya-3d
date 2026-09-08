/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Probability
public import Kakeya.RandomTranslation.FrostmanCancellation

/-!
# Chernoff bound for the total ED bad count of `J` rigid copies

GWZ Lemma 3.8 applies `J` **independent** rigid motions and needs the total bad count
`∑_{j<J} X_j` against a fixed test tube to be small with high probability. The tail bound is GWZ
Lemma A.1, which this repository already has in fully general form as
`Kakeya.Probability.lemma_A1_case_lt`: for independent, identically distributed, `[0, M]`-valued
random variables with `J · 𝔼[X] < M`,

`P[∑_j X_j > S] ≤ exp (10e - S/M)`.

This file supplies the three hypotheses of that lemma for the rigid-motion bad counts:

* the sample space is the `J`-fold product `Kakeya.rigidPiMeasure`, so independence and identical
  distribution are structural (`iIndepFun_pi`, exactly as in
  `Kakeya.productTubeContainedCount_iIndepFun` for the translation-only case);
* the pointwise cap `X_j ≤ Cpack` is `Kakeya.edBadCount_le` — a *dimensional* constant, with no
  factor of `J`;
* the mean condition `J · 𝔼[X] < M` is the canonical Frostman cancellation
  `Kakeya.ceil_frostmanConstant_mul_lintegral_edBadCount_le`, with `J = ⌈C_F⌉₊`.

Because the cap and the mean bound are both dimensional, `M` can be chosen dimensional, and the
resulting threshold `S ≍ M · log(1/δ)` after a union bound over the `δ^(-O(1))` test-tube net is
`O(log(1/δ))` — independent of `C_F`. That is the whole point: it replaces the old
`M_ED := ⌈CF⌉₊ * C_pack_ext + 1`.
-/

@[expose] public section

open MeasureTheory Metric Set

namespace Kakeya

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The `J`-fold product of the rigid-motion probability space: `J` independent rigid motions. -/
def rigidPiMeasure (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (J : ℕ) :
    Measure (Fin J → (unitary (E →L[ℝ] E) × E)) :=
  Measure.pi fun _ => rigidMeasure E

instance instIsProbabilityMeasureRigidPiMeasure (J : ℕ) :
    IsProbabilityMeasure (rigidPiMeasure E J) := by
  unfold rigidPiMeasure
  infer_instance


end

end Kakeya

end

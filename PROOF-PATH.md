# Proof path and assumptions

The conditional endpoint is `KakeyaDimensionThree` in
`Kakeya/DimensionThree/KakeyaConjecture.lean`. From the sticky Kakeya hypothesis
below it proves the project's existing `KakeyaSetConjecture 3`, defined in
`Kakeya/IsBesicovitch.lean` for compact Besicovitch sets in
`EuclideanSpace Real (Fin 3)`.

| Stage | Lean declaration | Source module |
| --- | --- | --- |
| Sticky input, GWZ 7.3(A) | `StickyKakeya.StickyFrostmanHypothesis` | `Kakeya/Sticky.lean` |
| Sticky reduction, 7.3(A) to 7.3(B) | `StickyKakeya.stickyKatzTaoEstimate_of_stickyFrostmanEstimate` | `Kakeya/StickyKakeya.lean` |
| Main Lemma 1 | `Kakeya.KatzTaoEstimate.frostmanEstimate` | `Kakeya/DimensionThree/MainLemma1.lean` |
| Main Lemma 2 | `Kakeya.KatzTaoEstimate.katzTaoEstimate_sub_of_frostmanEstimate` | `Kakeya/DimensionThree/MainLemma2.lean` |
| Katz-Tao bootstrap | `Kakeya.katzTaoEstimateDimensionThree` | `Kakeya/DimensionThree/KakeyaEstimate.lean` |
| Shaded Kakeya estimate | `KakeyaEstimateDimensionThree_pos` | `Kakeya/DimensionThree/KakeyaEstimate.lean` |
| Hausdorff lower bound | `dimH_ge_three_of_kakeyaEstimate` | `Kakeya/DimensionThree/KakeyaConjecture.lean` |
| Dimension equality | `KakeyaDimensionThree` | `Kakeya/DimensionThree/KakeyaConjecture.lean` |

Main Lemma 1 converts a Katz-Tao partial estimate at exponent beta to the
Frostman estimate at every strictly larger exponent. Main Lemma 2 supplies a
positive monotone exponent improvement from the Katz-Tao and Frostman inputs.
The bootstrap obtains the Katz-Tao estimate at every positive exponent up to
one. The shaded estimate and Hausdorff reduction then give the dimension lower
bound; the ambient dimension supplies the upper bound.

## Exact sticky boundary

The `Kakeya` library declares no axiom. Its external mathematical input is the hypothesis
`StickyKakeya.StickyFrostmanHypothesis`: from an explicit proof
`hdim : Module.finrank Real E = 3` it yields
`StickyKakeya.StickyFrostmanEstimate (E := E)` for the specified finite-dimensional
real inner-product space with its Borel measurable structure. The conditional endpoint carries it as an explicit argument.

The predicate `StickyKakeya.StickyFrostmanEstimate` itself is defined for general
ambient dimension; nothing here asserts it outside dimension three. The
reduction from part (A) to part (B) remains dimension-independent because it
takes part (A) as a hypothesis.

The precise predicate in `Kakeya/Sticky.lean` is authoritative. In particular,
the powers appearing in its ENNReal volume bounds use `ENNReal.ofReal` applied
to real powers. This encoding is part of the inherited formalization; no
equivalence to older variants using `ENNReal.ofNNReal` is claimed here.

The final argument therefore proves the displayed Kakeya conclusion conditional
on this three-dimensional Sticky input and Lean's standard three axioms.
An axiom check does not constitute a proof of the Sticky input.

## Discharging the sticky input

The `Unconditional` library links the conditional endpoint to the separately
obtained upstream proof at the revision in
`verification/unconditional/bridge-lock.json`.

| Stage | Lean declaration | Source module |
| --- | --- | --- |
| Wang-Zahl Theorem 5.2 | `Kakeya.Assouad.PureWZ2Theorem5_2Unconditional` | Upstream `MyLeanRepo.Kakeya.Assouad.PureWZ2.Theorem5_2Unconditional` |
| Convert the upstream estimate to the Numina sticky hypothesis | `stickyFrostmanHypothesis_of_pureWZ2` | `Unconditional.StickyFrostman` |
| Apply the conditional Numina theorem | `Unconditional.KakeyaDimensionThree` | `Unconditional.KakeyaConjecture` |

The conversion is needed because the two developments use different cover and
Frostman formulations. The final theorem has type `KakeyaSetConjecture 3` and
carries no sticky hypothesis. `verification/unconditional/AxiomCheck.lean`
asserts that both linking endpoints depend on exactly `propext`,
`Classical.choice`, and `Quot.sound`.

The default Lake build checks the conditional library and `FinalCheck`.
The full command in [RELEASING.md](RELEASING.md) also builds the upstream import
closure and linking library, runs their axiom assertions, and compares the final
theorem against a separately written Mathlib-only statement. A successful source
scan alone does not establish any of these compiler or comparator results.

## Reading the development

The Lean entry files above identify the main steps and their formal statements.
For the mathematical exposition, see Guth, Wang and Zahl's
[A streamlined proof of the Kakeya conjecture in R3](https://arxiv.org/abs/2601.14411)
and the related papers listed in [README.md](README.md).

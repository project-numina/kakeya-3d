# Kakeya in Dimension Three

This is a standalone Lean 4 formalization of the three-dimensional Kakeya
argument following Guth, Wang and Zahl: every compact set in real Euclidean
three-space containing a unit segment in every direction has Hausdorff
dimension three. The statement is reached in two layers. `KakeyaDimensionThree`
proves it from one explicit mathematical input, and `Unconditional.KakeyaDimensionThree`
discharges that input, so the conjecture is obtained with no hypothesis, no
`sorry` and no project axiom.

`KakeyaDimensionThree` takes one explicit mathematical input as a hypothesis:
`StickyKakeya.StickyFrostmanHypothesis`, the project's formulation of GWZ
Theorem 7.3(A), asserted for every ambient real inner-product space satisfying
`Module.finrank Real E = 3`. That input is *not* proved in the `Kakeya` library,
so the library on its own establishes an implication. It declares no axiom of
its own; the remaining axioms are Lean's `propext`, `Classical.choice`, and
`Quot.sound`. See [PROOF-PATH.md](PROOF-PATH.md) for the exact entry points.

The hypothesis is discharged by the `Unconditional` library in this repository,
which yields

```lean
theorem Unconditional.KakeyaDimensionThree : KakeyaSetConjecture 3
```

with no `sorry` and no project axiom. See
[The unconditional result](#the-unconditional-result) below; that library needs a
second development, which this repository does not vendor and which you download
yourself.

## Build and Check

Install [elan](https://github.com/leanprover/elan), Git, Bash, and Python 3.11 or
later. The committed `lean-toolchain` selects Lean `v4.32.0-rc1` and
`lake-manifest.json` fixes all dependency commits, including Mathlib
`1b0782d8191b03e0001caac10e1601d17f2cd580`.

```sh
lake exe cache get
lake build
bash verification/run.sh
```

The cache download is optional; `lake build` can compile the pinned dependencies
from source. Keep the manifest when reproducing the build. `lake update` changes
the dependency resolution and is not part of these verification commands.

`verification/run.sh` scans every project Lean source outside ignored build
products, builds the entire `Kakeya` library, and checks the expected public
axiom closures through `FinalCheck.lean`. A source census and compiler check
serve different purposes: the former finds unfinished proof tokens and
confirms that the sources declare no axiom, while the latter verifies
elaborated declarations and their actual dependencies.

Comparator setup and its recorded result are documented separately in
`verification/comparator/README.md`. No independent-kernel result is claimed
unless a corresponding completed receipt is present.

## Source Layout

| Path | Content |
| --- | --- |
| `Kakeya/` | Definitions, infrastructure and proofs |
| `Kakeya.lean` | Complete library import root |
| `FinalCheck.lean` | Public theorem and axiom assertions |
| `Unconditional/` | The linking layer that discharges the Sticky hypothesis |
| `Unconditional.lean` | Import root of the linking layer |
| `verification/` | Source, axiom and comparator checks |
| `verification/unconditional/` | Build and check tooling for the linking layer |

The repository contains the Kakeya mathematical development and its maintained
verification tools. See [ATTRIBUTION.md](ATTRIBUTION.md) for mathematical
attribution and dependency information.

Comments cite labels of the form `lem:...`, `def:...` and `note:...`. These name
the statements of the informal proof outline that the formalization follows; the
outline itself is not distributed here, and the labels are kept because they
record which informal statement a Lean declaration corresponds to.

## The unconditional result

GWZ record that their Theorem 7.3(A) — the hypothesis of `KakeyaDimensionThree` —
is Theorem 5.2 of Wang and Zahl, *The Assouad dimension of Kakeya sets in R3*.
That theorem has been formalized, unconditionally, by Nankai University and the
ByteDance Seed AI4Math Team in
[`M32026/3d-sticky-kakeya`](https://github.com/M32026/3d-sticky-kakeya) as
`Kakeya.Assouad.PureWZ2Theorem5_2Unconditional`.

The two formulations of the hypothesis are not the same Lean statement: GWZ
Definition 7.1(A) imposes a Frostman condition on the classes of a nested cover
hierarchy, while the Assouad paper's Definition 2.12 asks for Convex Wolff Axioms
on covers at every nearby scale, and GWZ Remark 7.2 relates the two without proof.
The `Unconditional/` library closes that gap. Its endpoints are

| Declaration | Module |
| --- | --- |
| `stickyFrostmanHypothesis_of_pureWZ2` | `Unconditional/StickyFrostman.lean` |
| `Unconditional.KakeyaDimensionThree` | `Unconditional/KakeyaConjecture.lean` |

`Unconditional` is not a default build target, because it imports the second
development and this repository does not vendor it. Obtain that development into
`upstream/` (which is not tracked here) and run one command:

```sh
git clone https://github.com/M32026/3d-sticky-kakeya upstream/3d-sticky-kakeya
git -C upstream/3d-sticky-kakeya checkout 42f739b484fd055e0aa29601c35677ad996f2ef2
bash verification/unconditional/run.sh -j 8
```

Pass `--upstream DIR` if you keep it elsewhere. The script verifies both
checkouts against the recorded pins, builds `Unconditional`, and then asserts the
axiom closure of both endpoints through
`verification/unconditional/AxiomCheck.lean`, which must report exactly

```
[propext, Classical.choice, Quot.sound]
```

Both sides are compiled against Lean `v4.32.0-rc1` and Mathlib
`1b0782d8191b03e0001caac10e1601d17f2cd580`. The pinned identities, the five exact
hash-checked local notation mappings that reconcile renamed Mathlib identifiers,
and the build driver are in `verification/unconditional/`; its `configure` step
verifies both checkouts' commits, clean Git state, every package pin and the
compiler version before building.

Building the linking layer compiles the whole of the second development, which is
substantially larger than this one; budget accordingly. The `lake build` and
`verification/` checks described above do not depend on it and remain
self-contained.

## References and Attribution

- Guth, Wang and Zahl, [A streamlined proof of the Kakeya conjecture in
  R3](https://arxiv.org/abs/2601.14411). The argument formalized here.
- Wang and Zahl, [The Assouad dimension of Kakeya sets in
  R3](https://arxiv.org/abs/2401.12337), Invent. Math. 241(1):153-206, 2025.
  Theorem 5.2 is GWZ Theorem 7.3(A), the estimate this development assumes.
- Wang and Zahl, [Volume estimates for unions of convex sets, and the Kakeya
  set conjecture in three dimensions](https://arxiv.org/abs/2502.17655).
- Wang and Zahl, [Sticky Kakeya sets and the sticky Kakeya
  conjecture](https://arxiv.org/abs/2210.09581).
- Nankai University and ByteDance Seed AI4Math Team,
  [3d-sticky-kakeya](https://github.com/M32026/3d-sticky-kakeya). Formalization of
  Wang-Zahl Theorem 5.2, the input this development assumes.

Lean sources originate in Project Numina's Kakeya development. Existing source
notices are preserved; see [ATTRIBUTION.md](ATTRIBUTION.md), [NOTICE](NOTICE)
and [LICENSE](LICENSE).

## Acknowledgements

We are deeply grateful to Professor [Hong Wang](https://sites.google.com/view/hongwang/home)
and Professor [Xiao Ma](https://sites.google.com/view/xiaom-homepage) for their generous help
and guidance.

We thank the Nankai University and ByteDance Seed AI4Math Team for their
formalization of Wang-Zahl Theorem 5.2 in
[3d-sticky-kakeya](https://github.com/M32026/3d-sticky-kakeya), and for their work
on integrating it with this development, which is what makes the unconditional
result above possible.

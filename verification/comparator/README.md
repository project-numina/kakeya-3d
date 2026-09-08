# Comparator

Run this after the ordinary build:

```sh
bash verification/comparator/run.sh --target conditional
```

The script uses the exact tool revisions in `tools.json` and the project's
unchanged Lean `v4.32.0-rc1`. It checks a frozen source boundary, builds the
project and final axiom assertions, fetches and builds the pinned comparator,
then runs the actual comparison and Lean kernel replay. A successful result
requires exit status zero and the final verdict `Your solution is okay!`.
Results and full logs are saved under `.verify-work/comparator/`.

`Challenge.lean.in` independently states the existing compact Besicovitch-set
definition, the Hausdorff-dimension conclusion, and the three-dimensional
Sticky hypothesis and its predicate. The challenge imports neither
`Kakeya.Sticky` nor the proved main theorem. Its five lower Kakeya imports
provide the formal language needed to state the external Sticky assumption; it
is therefore not a Mathlib-only challenge. `trusted-boundary.json` freezes their transitive
source closure, including 55 project modules, package sources and Lean source
files, together with all package pins. Verification checks this file;
it never regenerates it from an edited solution.

Comparator recursively compares the theorem type, named predicates, permitted
axiom types, and the constants appearing in those types. It also checks the
solution's actual axiom dependencies and replays the exported solution through
Lean's kernel. No project axiom is permitted: the Sticky input appears as a
hypothesis of the challenge theorem, so this checks a conditional Kakeya proof,
not a proof of Sticky itself.

The tracked challenge is a template, not a Lean proof module. Its single
protocol marker is replaced by an admitted target only inside the ignored
runtime wrapper. That specification is kept separate from `Solution.lean`,
which imports the actual proved theorem. No placeholder is added to the
tracked proof library.

The wrapper exposes existing compiled modules through links wholly inside
this standalone repository. Any module-name collision is a hard error. The
pinned upstream `fake-landrun.sh` adapter runs without a sandbox; this is a
check of locally owned sources, not an adversarial-code isolation claim.
Nanoda is disabled and no independent second-kernel result is claimed.

The pinned comparator version is compatible with the project's fixed Lean
toolchain; its own source and dependency manifest are checked before use.

## Unconditional target

After building and configuring the linking library, run:

```sh
bash verification/comparator/run.sh --target unconditional --jobs 2
```

`ChallengeUnconditional.lean.in` states `IsBesicovitch`,
`KakeyaSetConjecture`, and `KakeyaDimensionThree_of_pureWZ2` using only Mathlib
imports. `SolutionUnconditional.lean` imports the linked theorem. The runner
checks the bridge inputs, builds its closure, and runs `AxiomCheck.lean` before
the comparison. Its receipt includes the clean upstream revision and source
hash, the current Numina source identity, and the bridge build-receipt hash.
It checks these identities again after comparison.

The same frozen dependency boundary is checked for both targets. For the
conditional target it also freezes the lower Numina statement vocabulary;
the unconditional challenge has no Numina imports. `--challenge-only` compiles
a specification without claiming a solution check. `--prepare-only` prepares
the wrapper without claiming a comparator pass.

Use `python3 verification/check.py --scope full --require-clean` to run both
targets and the build and axiom checks with one aggregate receipt. Release
publication is waiting for the comparator to be committed. A completed receipt
must match the release candidate; the presence of these scripts is not evidence
that the comparator has passed.

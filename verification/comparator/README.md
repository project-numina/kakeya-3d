# Comparator

Run this after the ordinary build:

```sh
bash verification/comparator/run.sh
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

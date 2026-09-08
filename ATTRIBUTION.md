# Attribution and sources

The mathematical argument is due to Larry Guth, Hong Wang and Joshua Zahl,
building on the Wang-Zahl Kakeya work. The source papers are linked in
[README.md](README.md); their full texts are not included in this repository.

[CONTRIBUTORS.md](CONTRIBUTORS.md) lists the project contributors.
[CITATION.cff](CITATION.cff) contains citation metadata for this repository.
Existing per-file author and copyright notices are preserved.

## Source provenance

The public Numina source baseline used for this release preparation is
[`f305ef6555788849c87caa987f161abc990d8c2c`](https://github.com/project-numina/kakeya-3d/commit/f305ef6555788849c87caa987f161abc990d8c2c).
Its public history begins with that assembled development; the earlier working
history is not included. Verification receipts record the actual checkout commit
and a hash of the Git-visible source inventory, so a later release is tied to its
own sources. This baseline is not a build pin for subsequent Numina commits.

The `Unconditional/` sources link the Numina proof to Nankai University and the
ByteDance Seed AI4Math Team's
[`M32026/3d-sticky-kakeya`](https://github.com/M32026/3d-sticky-kakeya), pinned at
[`42f739b484fd055e0aa29601c35677ad996f2ef2`](https://github.com/M32026/3d-sticky-kakeya/tree/42f739b484fd055e0aa29601c35677ad996f2ef2).
The imported endpoint is `Kakeya.Assouad.PureWZ2Theorem5_2Unconditional`.
The checkout is fetched separately and must remain clean. Five compatibility
insertions are applied to generated copies outside that checkout; the original
and resulting SHA-256 hashes and each insertion are recorded in
`verification/unconditional/compatibility/patches.json`.

No tracked license file was found in that pinned upstream revision. This
repository's Apache-2.0 license does not state the upstream project's terms.
Record an upstream license or permission reference before a combined release;
see [RELEASING.md](RELEASING.md). The contributor list here does not replace
upstream attribution.

## Dependencies

Mathlib and the other Lake packages are fetched separately at the exact commits
in `lake-manifest.json`, under their respective licenses. The comparator and
its dependencies are fixed in `verification/comparator/tools.json`; upstream
copyright and license files remain in those separately fetched distributions.
The bridge checks the same package manifest and the Lean compiler revision.

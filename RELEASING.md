# Release preparation

Release publication is deferred until the comparator is committed. A configured
comparator, a prepared wrapper, or a passing core build is not a full verification
result. Do not mark the unconditional result as release-verified without a
completed full receipt for the release candidate.

## Reproduce the checks

The verification scripts support Linux and WSL2 with Bash, Git, Python 3.11 or
later, and elan. Ubuntu 24.04 is the CI environment. Keep `lean-toolchain` and
`lake-manifest.json` unchanged: they select Lean 4.32.0-rc1 and the reviewed
package revisions. The upstream checkout must be clean at the commit in
`verification/unconditional/bridge-lock.json`.

From a fresh checkout of the candidate commit:

```sh
lake exe cache get
git clone https://github.com/M32026/3d-sticky-kakeya upstream/3d-sticky-kakeya
git -C upstream/3d-sticky-kakeya checkout 42f739b484fd055e0aa29601c35677ad996f2ef2
python3 verification/check.py --scope full --require-clean --jobs 2
```

Use `--upstream DIR` for an existing upstream checkout. Use a fresh project
checkout for release verification so that project artifacts are compiled from
source. The pinned Mathlib cache is allowed. Local development runs may reuse
artifacts built by the bridge; its receipts hash the source, imported artifacts
(including private and IR fragments), compiler, and options. An external cache
without matching local build receipts is rebuilt.

The full command runs verifier regressions, the source census, `Kakeya` and
`FinalCheck`, the upstream closure and `Unconditional`, both endpoint axiom
assertions, and the conditional and unconditional comparator targets. It stops
on failure and retains the failing log. The core command is:

```sh
python3 verification/check.py --scope core
```

`verification/run.sh` remains the source census and conditional build check.
`verification/unconditional/run.sh` checks the linked endpoints after the core
library is built. Neither command alone runs the comparator.

## Evidence and resources

Each `verification/check.py` run creates `.verification-results/<UTC time>/`
with a `result.json` and stage logs. A full successful run also copies both
comparator receipts there. The main receipt records the commit, dirty state,
source inventory hash, upstream identity, toolchain, stage exit codes, log
hashes, elapsed time, machine details, and free disk space before and after.
A source change during verification fails the run. Use `--require-clean` for
release evidence; a passing development run with a dirty source tree is not
attributed to its HEAD commit alone.

`largest_child_peak_rss_kib` is Linux's largest child-process memory high-water
mark, not the sum of simultaneous compiler processes. It is not a machine RAM
requirement. Record the runner's RAM and bridge concurrency with the receipt.
The upstream proof is large; completed full runs are needed before stating
minimum RAM, disk, or runtime requirements. The default bridge concurrency is
two processes. Increase it only when the runner has enough memory. The core
Lake build uses Lake's own scheduling.

The `Verification` workflow checks regressions and the core build on pull
requests and pushes to `main`. Its manual `full` option runs the full suite on a
fresh hosted runner and uploads receipts and logs even on failure. If that job
exceeds the runner's resources or time limit, run the same command on a suitable
Linux machine and retain the failed CI receipt as well as the completed result.
The workflow does not publish releases or deposit archives.

## Before publishing

- Confirm the comparator commit has landed. Run the full suite on the final
  candidate commit and retain both comparator receipts with `status: pass`.
  Review the independent challenge statements and the proof path for the paper.
- Confirm who will maintain the release. Replace the organization-level
  `responsible_maintainers` entry in `formalization.yaml` with the agreed names.
- Obtain an upstream license or permission reference for the pinned Sticky
  development. Record its scope and required notices in `ATTRIBUTION.md` before
  distributing a combined archive or upstream compiled artifacts. The current
  pin has no tracked license file; this repository does not assign it one.
- Check the contributor list, citation metadata, and source provenance with the
  contributors. Preserve upstream and per-file notices. A software contributor
  list does not decide a paper's author list.
- Choose the release version and archive destination. After these gates pass,
  create an annotated tag for the tested commit, archive the source and
  verification evidence, and record the archive checksum. Do not include
  `.lake`, `.verify-work`, or the upstream checkout in a source-only archive.
- Deposit the approved artifact in the project's chosen persistent archive.
  Add its version, release date, and identifier to `CITATION.cff` and cite that
  artifact in the paper. No DOI or completed archive is claimed by the current
  metadata. If this changes the candidate sources, verify the final commit again.

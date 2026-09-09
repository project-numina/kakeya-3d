# Verification and reproduction

## Reproduce the checks

The verification scripts support Linux and WSL2 with Bash, Git, Python 3.11 or
later, and elan. Use Ubuntu 24.04 for CI. Keep `lean-toolchain` and
`lake-manifest.json` unchanged: they select Lean 4.32.0-rc1 and the reviewed
package revisions. The upstream checkout must be clean at the commit in
`verification/unconditional/bridge-lock.json`.

From a fresh checkout of the commit to verify:

```sh
lake exe cache get
git clone https://github.com/M32026/3d-sticky-kakeya upstream/3d-sticky-kakeya
git -C upstream/3d-sticky-kakeya checkout 42f739b484fd055e0aa29601c35677ad996f2ef2
python3 verification/check.py --scope full --require-clean --jobs 2
```

Use `--upstream DIR` for an existing upstream checkout. Use a fresh project
checkout to compile the project artifacts from source. The pinned Mathlib cache
is allowed. The bridge compiles all 4,706 upstream modules in the endpoint's
import closure from source on its first run. It does not adopt externally built
upstream artifacts. Later runs may reuse artifacts built by the bridge; its
receipts hash the source, imported artifacts (including private and IR
fragments), compiler, and options. Artifacts without matching local build
receipts are rebuilt.

The full command runs verifier regressions, the source census, `Kakeya` and
`FinalCheck`, the upstream closure and `Unconditional`, both endpoint axiom
assertions, and the conditional and unconditional comparator targets. It stops
on failure and retains the failing log. The core command is:

```sh
python3 verification/check.py --scope core
```

`verification/run.sh` remains the source census and conditional build check.
`verification/unconditional/run.sh` checks the linked endpoints after the core
library is built. Neither command alone runs the comparator. Both comparator
targets have passed in review; see the
[completed checks](verification/comparator/README.md#completed-checks).

## Evidence and resources

Each `verification/check.py` run creates `.verification-results/<UTC time>/`
with a `result.json` and stage logs. A full successful run also copies both
comparator receipts there. The main receipt records the commit, dirty state,
source inventory hash, upstream identity, toolchain, stage exit codes, log
hashes, elapsed time, machine details, and free disk space before and after.
A source change during verification fails the run. Use `--require-clean` for
receipts tied to a committed snapshot; a passing development run with a dirty
source tree is not attributed to its HEAD commit alone.

`largest_child_peak_rss_kib` is Linux's largest child-process memory high-water
mark, not the sum of simultaneous compiler processes. It is not a machine RAM
requirement. Record the runner's RAM and bridge concurrency with the receipt.

Review measurements found 7.9 GB in `.lake/packages`, 5.3 GB in `.lake/build`,
and 3.4 GB in `verification/unconditional/.bridge`. The unconditional comparator's
kernel replay peaked at 15.7 GB RSS. Use at least 24 GB RAM and 25 GB free working
disk space, with the operating system and toolchain already installed. More RAM
may be needed when increasing compiler concurrency.

The default bridge concurrency is two processes. Budget more than six hours
for a first full run at `--jobs 2`; elapsed time depends on the machine. A higher
setting, such as `--jobs 8`, can reduce build time when enough memory is available.
Subsequent runs can reuse matching local receipts. The core Lake build uses
Lake's own scheduling.

The `Verification` workflow runs regressions and the source census on pull
requests and pushes to `main`. Core and full builds run only through
`workflow_dispatch` on a self-hosted Linux x64 runner labeled
`kakeya-verification`. A matching runner must be registered with the resources
above before dispatching either build. Leave `full` unchecked for core checks;
select it for the full suite, which has a 24-hour job timeout. Both jobs upload
receipts and logs even on failure. The same commands can also run directly on a
suitable Linux machine.

Core build products and packages alone occupy about 13.2 GB. Standard
[GitHub-hosted Ubuntu runners](https://docs.github.com/en/actions/reference/runners/github-hosted-runners)
have 14 GB disk and 16 GB RAM, so automatic CI is limited to the lightweight
checks. A hosted core build would need a smaller, measured disk footprint first.

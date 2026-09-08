#!/usr/bin/env bash
# Build the linked theorem and check both endpoint axiom closures.
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
root=$(cd "$here/../.." && pwd)
upstream="$root/upstream/3d-sticky-kakeya"
jobs=2

usage() {
  echo "Usage: bash verification/unconditional/run.sh [--upstream DIR] [-j N]"
}
while [ $# -gt 0 ]; do
  case "$1" in
    --upstream)
      [ $# -ge 2 ] || { usage >&2; exit 2; }
      upstream=$(cd "$2" && pwd)
      shift 2 ;;
    -j|--jobs)
      [ $# -ge 2 ] || { usage >&2; exit 2; }
      jobs="$2"
      shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) usage >&2; echo "Unknown argument: $1" >&2; exit 2 ;;
  esac
done
[[ "$jobs" =~ ^[1-9][0-9]*$ ]] || { echo "Jobs must be a positive integer." >&2; exit 2; }

if [ ! -d "$upstream" ]; then
  echo "Missing upstream checkout: $upstream" >&2
  echo "See README.md for the pinned clone command, or pass --upstream DIR." >&2
  exit 1
fi

# Select this repository's elan toolchain even when called from another directory.
cd "$root"
lean_prefix=$(lean --print-prefix)
python3 "$here/tools/bridge.py" configure \
  --numina "$root" --bytedance "$upstream" \
  --packages "$root/.lake/packages" --lean "$lean_prefix/bin/lean"
python3 "$here/tools/bridge.py" build Unconditional -j "$jobs"
python3 "$here/tools/bridge.py" lean "$here/AxiomCheck.lean"
echo "Unconditional build and axiom checks passed."

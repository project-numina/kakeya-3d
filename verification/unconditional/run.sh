#!/usr/bin/env bash
# Build and check the unconditional Kakeya result.
#
# Usage:
#   bash verification/unconditional/run.sh [--upstream DIR] [-j N]
#
# The second development is not vendored here. Obtain it first, either into the
# default location or anywhere you like:
#
#   git clone https://github.com/M32026/3d-sticky-kakeya upstream/3d-sticky-kakeya
#   git -C upstream/3d-sticky-kakeya checkout <bytedance_commit from bridge-lock.json>
#
# This script then verifies both checkouts against the recorded pins, builds the
# `Unconditional` library, and reports the axiom closure of the endpoints.
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
root=$(cd "$here/../.." && pwd)
upstream="$root/upstream/3d-sticky-kakeya"
jobs=8

while [ $# -gt 0 ]; do
  case "$1" in
    --upstream) upstream=$(cd "$2" && pwd); shift 2 ;;
    -j) jobs="$2"; shift 2 ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done

if [ ! -d "$upstream" ]; then
  cat >&2 <<MSG
The second development was not found at:
  $upstream

Obtain it with

  git clone https://github.com/M32026/3d-sticky-kakeya $root/upstream/3d-sticky-kakeya
  git -C $root/upstream/3d-sticky-kakeya checkout \$(python3 -c \
    "import json;print(json.load(open('$here/bridge-lock.json'))['bytedance_commit'])")

or pass --upstream DIR.
MSG
  exit 1
fi

lean_prefix=$(lean --print-prefix)
packages="$root/.lake/packages"

echo "== configure"
python3 "$here/tools/bridge.py" configure \
  --numina "$root" --bytedance "$upstream" \
  --packages "$packages" --lean "$lean_prefix/bin/lean"

echo "== build Unconditional"
python3 "$here/tools/bridge.py" build Unconditional -j "$jobs"

echo "== axiom closure of the endpoints"
python3 "$here/tools/bridge.py" lean "$here/AxiomCheck.lean"

echo
echo "Unconditional check finished."

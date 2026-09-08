#!/usr/bin/env bash
set -euo pipefail
project_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
exec python3 "$project_root/verification/comparator/run.py" "$@"


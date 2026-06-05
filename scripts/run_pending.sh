#!/usr/bin/env bash
# Run end-to-end pipeline only for problems that have NO existing output/ workspace
# (i.e. not yet attempted). Each invocation picks the next batch of un-attempted
# raw/<name>.md problems, so repeated runs march through the dataset without
# redoing anything already in output/.
#
# Usage:
#   scripts/run_pending.sh                 # next 10 pending, jobs=2
#   scripts/run_pending.sh --count 20 --jobs 4
#   scripts/run_pending.sh --count 5 --verify-timeout 5400   # extra flags pass through
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

COUNT=10
JOBS=2
PASS=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --count) COUNT="$2"; shift 2 ;;
    --jobs|-j) JOBS="$2"; shift 2 ;;
    *) PASS+=("$1"); shift ;;
  esac
done

# Problem names that already have ANY stage workspace under output/.
attempted() {
  ls output 2>/dev/null \
    | grep -E '^(verify|pipeline|eval|contract)_[0-9]{8}_[0-9]{6}' \
    | sed -E 's/^(verify|pipeline|eval|contract)_[0-9]{8}_[0-9]{6}[a-z0-9]*_//' \
    | sort -u
}

# Problem names already exported as a verified end-to-end example.
exported() {
  find experiences/end-end -mindepth 1 -maxdepth 1 -type d -printf '%f\n' 2>/dev/null | sort -u
}

mapfile -t names < <(
  comm -23 \
    <(find raw -maxdepth 1 -type f -name '*.md' -printf '%f\n' | sed 's/\.md$//' | sort) \
    <( { attempted; exported; } | sort -u ) \
  | head -n "$COUNT"
)

if [[ ${#names[@]} -eq 0 ]]; then
  echo "no pending problems — every raw/*.md already has an output/ workspace or end-end example"
  exit 0
fi

echo "pending batch (${#names[@]}): ${names[*]}"
exec ./scripts/run_pipeline_many.sh --jobs "$JOBS" "${PASS[@]}" "${names[@]}"

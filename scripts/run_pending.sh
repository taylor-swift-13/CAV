#!/usr/bin/env bash
# Run the end-to-end pipeline only for problems in a dataset that have NO existing
# output/ workspace and are not yet exported. Each invocation picks the next batch
# of un-attempted raw/<dataset>/<name>.md problems, so repeated runs march through
# the dataset without redoing anything.
#
# Usage:
#   scripts/run_pending.sh                              # dataset=algo, next 10, jobs=2
#   scripts/run_pending.sh --dataset humaneval --count 20 --jobs 4
#   scripts/run_pending.sh --count 5 --verify-timeout 5400   # extra flags pass through
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

DATASET="algo"
COUNT=10
JOBS=2
PASS=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --dataset) DATASET="$2"; shift 2 ;;
    --count) COUNT="$2"; shift 2 ;;
    --jobs|-j) JOBS="$2"; shift 2 ;;
    *) PASS+=("$1"); shift ;;
  esac
done

# Bare problem names (within this dataset) that already have ANY stage workspace.
# Workspaces are named <stage>_<ts>_<dataset>_<name>.
attempted() {
  ls output 2>/dev/null \
    | grep -E "^(verify|pipeline|eval|contract)_[0-9]{8}_[0-9]{6}[a-z0-9]*_" \
    | sed -E "s/^(verify|pipeline|eval|contract)_[0-9]{8}_[0-9]{6}[a-z0-9]*_//" \
    | sort -u
}

# Bare problem names already exported as a verified example (named <dataset>_<name>).
exported() {
  find QualifiedCProgramming/SeparationLogic/examples/CAV -mindepth 1 -maxdepth 1 -type d -printf '%f\n' 2>/dev/null \
    | sort -u
}

if [[ ! -d "raw/${DATASET}" ]]; then
  echo "no such dataset dir: raw/${DATASET}" >&2
  exit 2
fi

mapfile -t names < <(
  comm -23 \
    <(find "raw/${DATASET}" -maxdepth 1 -type f -name '*.md' -printf '%f\n' | sed 's/\.md$//' | sort) \
    <( { attempted; exported; } | sort -u ) \
  | head -n "$COUNT"
)

if [[ ${#names[@]} -eq 0 ]]; then
  echo "no pending problems in dataset '${DATASET}' — all attempted or exported"
  exit 0
fi

echo "pending batch [${DATASET}] (${#names[@]}): ${names[*]}"
exec ./scripts/run_pipeline_many.sh --dataset "$DATASET" --jobs "$JOBS" "${PASS[@]}" "${names[@]}"

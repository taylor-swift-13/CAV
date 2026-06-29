#!/usr/bin/env bash
# Re-run end-to-end (contract -> eval -> verify) for the tasks whose
# decimal-parse signed-overflow bug was fixed.
#
# Inputs were corrected at all three layers (generator / raw / input), so this full
# flow from raw/<name>.md regenerates a correct, RTE-free input C.
#
# Usage:
#   scripts/legacy/rerun_overflow_fixed.sh                 # serial, default timeouts
#   scripts/legacy/rerun_overflow_fixed.sh -j 4            # 4 tasks concurrently
#   scripts/legacy/rerun_overflow_fixed.sh -j 4 --verify-timeout 5400   # extra flags pass through
#
# Any extra args are forwarded to run_pipeline_many.sh.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"

NAMES=(
  aug_first_ge_stream_001
  aug_first_ge_array_001
  aug_count_ge_array_000
  aug_count_ge_array_007
  aug_count_ge_stream_000
  aug_count_ge_stream_007
  aug_last_le_array_006
  aug_sum_prefix_array_002
  aug_all_multiple_array_003
  aug_all_multiple_stream_003
  array_is_sorted_csv
  array_min_csv
  ex_binary_search_index_csv
  best_stock_profit_csv
)

cd "$ROOT"   # run_pipeline.py resolves raw/<name>.md relative to repo root
echo "Re-running ${#NAMES[@]} tasks via run_pipeline_many.sh"
echo "Extra flags: $*"
exec "$ROOT/scripts/run_pipeline_many.sh" "$@" "${NAMES[@]}"

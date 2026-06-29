#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SUMMARY_ROOT="${SUMMARY_ROOT:-/tmp/cav_verify_efficiency_regression}"
LABEL="run"
JOBS=1
CONTRACT_TIMEOUT=300
EVAL_TIMEOUT=900
VERIFY_TIMEOUT=3600
DRY_RUN=0
COMPARE_SUMMARY=""
ONLY_NAME=""

NAMES=(
  add_binary_strings
  armstrong_number
  array_copy_even
  array_count_between
  array_index_of_max
  array_is_sorted_csv
  array_product_small
  array_sum_abs
)

usage() {
  cat <<'EOF'
usage: run_fast_verify_regression.sh [--label NAME] [--only TASK] [--jobs N] [--contract-timeout N] [--eval-timeout N] [--verify-timeout N] [--compare SUMMARY.tsv] [--dry-run]

Runs the fixed FAST regression set without exporting examples. After metrics are summarized, deletes the eight tasks' generated
input/annotated/output artifacts so future runs cannot copy prior answers.
Default --jobs is 1. Regression runs must stay serial when comparing Accuracy/Time;
passing any other --jobs value is rejected.

Outputs:
  summary.tsv     per-task status, attempts, wall time, tokens, retrieval count
  aggregate.tsv   run-level Accuracy and Time metrics
  comparison.tsv  optional delta against --compare
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --label)
      LABEL="$2"
      shift 2
      ;;
    --jobs|-j)
      JOBS="$2"
      shift 2
      ;;
    --only)
      ONLY_NAME="$2"
      shift 2
      ;;
    --contract-timeout)
      CONTRACT_TIMEOUT="$2"
      shift 2
      ;;
    --eval-timeout)
      EVAL_TIMEOUT="$2"
      shift 2
      ;;
    --verify-timeout)
      VERIFY_TIMEOUT="$2"
      shift 2
      ;;
    --compare)
      COMPARE_SUMMARY="$2"
      shift 2
      ;;
    --dry-run)
      DRY_RUN=1
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "unknown argument: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

cd "$ROOT"

if [[ "$JOBS" != "1" ]]; then
  echo "regression must run serial for stable Accuracy/Time comparison; use --jobs 1" >&2
  exit 2
fi

if [[ -n "$ONLY_NAME" ]]; then
  found=0
  for name in "${NAMES[@]}"; do
    if [[ "$name" == "$ONLY_NAME" ]]; then
      found=1
      break
    fi
  done
  if [[ "$found" != "1" ]]; then
    echo "--only must name one of the fixed regression tasks: $ONLY_NAME" >&2
    printf 'allowed: %s\n' "${NAMES[*]}" >&2
    exit 2
  fi
  NAMES=("$ONLY_NAME")
fi

for name in "${NAMES[@]}"; do
  if [[ ! -f "raw/$name.md" ]]; then
    echo "missing raw file: raw/$name.md" >&2
    exit 4
  fi
done

RUN_ID="$(date +%Y%m%d_%H%M%S)"
SUMMARY_DIR="$SUMMARY_ROOT/$LABEL-$RUN_ID"
mkdir -p "$SUMMARY_DIR"
SUMMARY_TSV="$SUMMARY_DIR/summary.tsv"
AGGREGATE_TSV="$SUMMARY_DIR/aggregate.tsv"
COMPARISON_TSV="$SUMMARY_DIR/comparison.tsv"

cleanup_regression_artifacts() {
  remove_if_untracked() {
    local path="$1"
    if [[ -e "$path" ]] && ! git ls-files --error-unmatch "$path" >/dev/null 2>&1; then
      rm -f "$path"
    fi
  }

  rm -rf output/pipeline_many_*
  for name in "${NAMES[@]}"; do
    rm -rf "output/pipeline_"*"_${name}" \
           "output/contract_"*"_${name}" \
           "output/eval_"*"_${name}" \
           "output/verify_"*"_${name}"
    rm -f "annotated/verify_"*"_${name}.c"
    remove_if_untracked "input/${name}.c"
    remove_if_untracked "input/${name}.v"
  done
}

assert_no_regression_artifacts() {
  local leftover=()
  shopt -s nullglob
  for name in "${NAMES[@]}"; do
    leftover+=(output/pipeline_*_"$name")
    leftover+=(output/contract_*_"$name")
    leftover+=(output/eval_*_"$name")
    leftover+=(output/verify_*_"$name")
    leftover+=(annotated/verify_*_"$name".c)
    if [[ -e "input/${name}.c" ]] && ! git ls-files --error-unmatch "input/${name}.c" >/dev/null 2>&1; then
      leftover+=("input/${name}.c")
    fi
    if [[ -e "input/${name}.v" ]] && ! git ls-files --error-unmatch "input/${name}.v" >/dev/null 2>&1; then
      leftover+=("input/${name}.v")
    fi
  done
  shopt -u nullglob
  if [[ ${#leftover[@]} -gt 0 ]]; then
    printf 'regression artifacts remain after cleanup; refusing to run to avoid answer leakage:\n' >&2
    printf '  %s\n' "${leftover[@]}" >&2
    exit 5
  fi
}

write_summary() {
  {
    printf 'name\tstatus\tattempts\twall_clock_seconds\tinput_tokens\tcached_input_tokens\toutput_tokens\treasoning_output_tokens\tretrieval_mentions\tverify_workspace\n'
    for name in "${NAMES[@]}"; do
      metrics="$(find output -maxdepth 3 -path "*/logs/metrics.md" -path "*verify_*_${name}/logs/metrics.md" -print 2>/dev/null | sort | tail -n 1 || true)"
      if [[ -z "$metrics" ]]; then
        pipeline_log="$(find output -maxdepth 2 -path "output/pipeline_many_*/${name}.log" -print 2>/dev/null | sort | tail -n 1 || true)"
        pipeline_status=""
        if [[ -n "$pipeline_log" ]]; then
          pipeline_status="$(rg -o '\[pipeline\] status=[^ ]+' "$pipeline_log" | tail -n1 | sed 's/.*status=//' || true)"
        fi
        if [[ "$pipeline_status" == "success" ]]; then
          pipeline_status="Success"
        elif [[ -n "$pipeline_status" ]]; then
          pipeline_status="Fail:${pipeline_status}"
        else
          pipeline_status="missing"
        fi
        printf '%s\t%s\t\t\t\t\t\t\t0\t\n' "$name" "$pipeline_status"
        continue
      fi
      ws="${metrics%/logs/metrics.md}"
      status="$(rg -o '^- Status: `[^`]+`' "$metrics" | tail -n1 | sed 's/^- Status: `//; s/`$//' || true)"
      final="$(rg -o '^Final Result: (Success|Fail)' "$metrics" | tail -n1 | sed 's/^Final Result: //' || true)"
      attempts="$(rg -o '^- Attempts: `[^`]+`' "$metrics" | tail -n1 | sed 's/^- Attempts: `//; s/`$//' || true)"
      wall="$(rg -o '^- Wall-clock time \\(seconds\\): `[^`]+`' "$metrics" | tail -n1 | sed 's/^- Wall-clock time (seconds): `//; s/`$//' || true)"
      input_tokens="$(rg -o '^- Agent CLI input_tokens: `[^`]+`' "$metrics" | tail -n1 | sed 's/^- Agent CLI input_tokens: `//; s/`$//' || true)"
      cached_tokens="$(rg -o '^- Agent CLI cached_input_tokens: `[^`]+`' "$metrics" | tail -n1 | sed 's/^- Agent CLI cached_input_tokens: `//; s/`$//' || true)"
      output_tokens="$(rg -o '^- Agent CLI output_tokens: `[^`]+`' "$metrics" | tail -n1 | sed 's/^- Agent CLI output_tokens: `//; s/`$//' || true)"
      reasoning_tokens="$(rg -o '^- Agent CLI reasoning_output_tokens: `[^`]+`' "$metrics" | tail -n1 | sed 's/^- Agent CLI reasoning_output_tokens: `//; s/`$//' || true)"
      retrieval_mentions="$(rg -o 'Retrieval|检索|QualifiedCProgramming/SeparationLogic/examples' "$ws/logs" 2>/dev/null | wc -l | tr -d ' ')"
      printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
        "$name" "${status:-$final}" "$attempts" "$wall" "$input_tokens" "$cached_tokens" "$output_tokens" "$reasoning_tokens" "$retrieval_mentions" "$ws"
    done
  } > "$SUMMARY_TSV"
}

write_aggregate() {
  local elapsed_seconds="$1"
  awk -F '\t' -v label="$LABEL" -v run_id="$RUN_ID" -v elapsed="$elapsed_seconds" -v summary="$SUMMARY_TSV" '
    BEGIN {
      total = success = wall = attempts = input = cached = output = reasoning = retrieval = 0
    }
    NR == 1 { next }
    {
      total += 1
      if ($2 == "Success" || $2 == "success") success += 1
      if ($3 ~ /^[0-9]+$/) attempts += $3
      if ($4 ~ /^[0-9.]+$/) wall += $4
      if ($5 ~ /^[0-9]+$/) input += $5
      if ($6 ~ /^[0-9]+$/) cached += $6
      if ($7 ~ /^[0-9]+$/) output += $7
      if ($8 ~ /^[0-9]+$/) reasoning += $8
      if ($9 ~ /^[0-9]+$/) retrieval += $9
    }
    END {
      failure = total - success
      accuracy = total ? success / total : 0
      printf "label\trun_id\ttotal\tsuccess\tfailure\taccuracy\ttotal_elapsed_seconds\tsum_wall_clock_seconds\ttotal_attempts\ttotal_input_tokens\ttotal_cached_input_tokens\ttotal_output_tokens\ttotal_reasoning_output_tokens\ttotal_retrieval_mentions\tsummary_tsv\n"
      printf "%s\t%s\t%d\t%d\t%d\t%.6f\t%d\t%.2f\t%d\t%d\t%d\t%d\t%d\t%d\t%s\n", label, run_id, total, success, failure, accuracy, elapsed, wall, attempts, input, cached, output, reasoning, retrieval, summary
    }
  ' "$SUMMARY_TSV" > "$AGGREGATE_TSV"
}

write_comparison() {
  local previous_summary="$1"
  [[ -n "$previous_summary" ]] || return 0
  if [[ ! -f "$previous_summary" ]]; then
    echo "compare summary not found: $previous_summary" >&2
    return 0
  fi

  awk -F '\t' -v prev="$previous_summary" -v curr="$SUMMARY_TSV" '
    function read_summary(path, prefix,    total, success, wall, attempts, input, cached, output, reasoning, retrieval) {
      total = success = wall = attempts = input = cached = output = reasoning = retrieval = 0
      while ((getline line < path) > 0) {
        split(line, f, "\t")
        if (f[1] == "name") continue
        total += 1
        if (f[2] == "Success" || f[2] == "success") success += 1
        if (f[3] ~ /^[0-9]+$/) attempts += f[3]
        if (f[4] ~ /^[0-9.]+$/) wall += f[4]
        if (f[5] ~ /^[0-9]+$/) input += f[5]
        if (f[6] ~ /^[0-9]+$/) cached += f[6]
        if (f[7] ~ /^[0-9]+$/) output += f[7]
        if (f[8] ~ /^[0-9]+$/) reasoning += f[8]
        if (f[9] ~ /^[0-9]+$/) retrieval += f[9]
      }
      close(path)
      vals[prefix "_total"] = total
      vals[prefix "_success"] = success
      vals[prefix "_failure"] = total - success
      vals[prefix "_accuracy"] = total ? success / total : 0
      vals[prefix "_wall"] = wall
      vals[prefix "_attempts"] = attempts
      vals[prefix "_input"] = input
      vals[prefix "_cached"] = cached
      vals[prefix "_output"] = output
      vals[prefix "_reasoning"] = reasoning
      vals[prefix "_retrieval"] = retrieval
    }
    BEGIN {
      read_summary(prev, "prev")
      read_summary(curr, "curr")
      print "metric\tprevious\tcurrent\tdelta"
      printf "success\t%d\t%d\t%d\n", vals["prev_success"], vals["curr_success"], vals["curr_success"] - vals["prev_success"]
      printf "failure\t%d\t%d\t%d\n", vals["prev_failure"], vals["curr_failure"], vals["curr_failure"] - vals["prev_failure"]
      printf "accuracy\t%.6f\t%.6f\t%.6f\n", vals["prev_accuracy"], vals["curr_accuracy"], vals["curr_accuracy"] - vals["prev_accuracy"]
      printf "sum_wall_clock_seconds\t%.2f\t%.2f\t%.2f\n", vals["prev_wall"], vals["curr_wall"], vals["curr_wall"] - vals["prev_wall"]
      printf "total_attempts\t%d\t%d\t%d\n", vals["prev_attempts"], vals["curr_attempts"], vals["curr_attempts"] - vals["prev_attempts"]
      printf "total_input_tokens\t%d\t%d\t%d\n", vals["prev_input"], vals["curr_input"], vals["curr_input"] - vals["prev_input"]
      printf "total_output_tokens\t%d\t%d\t%d\n", vals["prev_output"], vals["curr_output"], vals["curr_output"] - vals["prev_output"]
      printf "total_reasoning_output_tokens\t%d\t%d\t%d\n", vals["prev_reasoning"], vals["curr_reasoning"], vals["curr_reasoning"] - vals["prev_reasoning"]
      printf "total_retrieval_mentions\t%d\t%d\t%d\n", vals["prev_retrieval"], vals["curr_retrieval"], vals["curr_retrieval"] - vals["prev_retrieval"]
    }
  ' > "$COMPARISON_TSV"
}

cmd=(
  ./scripts/run_pipeline_many.sh
  --jobs "$JOBS"
  --contract-timeout "$CONTRACT_TIMEOUT"
  --eval-timeout "$EVAL_TIMEOUT"
  --verify-timeout "$VERIFY_TIMEOUT"
  "${NAMES[@]}"
)

printf '%q ' "${cmd[@]}" > "$SUMMARY_DIR/command.txt"
printf '\n' >> "$SUMMARY_DIR/command.txt"

if [[ "$DRY_RUN" -eq 1 ]]; then
  cat "$SUMMARY_DIR/command.txt"
  exit 0
fi

cleanup_regression_artifacts
assert_no_regression_artifacts
RUN_START_EPOCH="$(date +%s)"
set +e
"${cmd[@]}"
run_rc=$?
set -e
RUN_END_EPOCH="$(date +%s)"
RUN_ELAPSED_SECONDS="$((RUN_END_EPOCH - RUN_START_EPOCH))"

write_summary
write_aggregate "$RUN_ELAPSED_SECONDS"
write_comparison "$COMPARE_SUMMARY"
cleanup_regression_artifacts

echo "summary: $SUMMARY_TSV"
echo "aggregate: $AGGREGATE_TSV"
if [[ -n "$COMPARE_SUMMARY" && -f "$COMPARISON_TSV" ]]; then
  echo "comparison: $COMPARISON_TSV"
fi
exit "$run_rc"

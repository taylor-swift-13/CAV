#!/usr/bin/env bash
# Start the three humaneval verify batches and copy finished output workspaces
# into each agent's result directory. Existing result workspaces are skipped.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

RESULTS_ROOT="/home/yangfp/CAV/results"
DATASET="humaneval"
TIMEOUT="${TIMEOUT:-3600}"
JOBS="${JOBS:-1}"
CODEX_JOBS="${CODEX_JOBS:-$JOBS}"
CLAUDE_JOBS="${CLAUDE_JOBS:-$JOBS}"
KIMI_JOBS="${KIMI_JOBS:-$JOBS}"

existing_names() {
  find "$RESULTS_ROOT" -maxdepth 3 -type d -name 'verify_*' -printf '%f\n' 2>/dev/null \
    | sed -E 's/^verify_[0-9]{8}_[0-9]{6}_//' \
    | sort -u
}

filter_existing() {
  local name
  for name in "$@"; do
    if ! grep -qxF "$name" "$EXISTING_FILE"; then
      printf '%s\n' "$name"
    fi
  done
}

start_batch() {
  local label="$1"
  local agent="$2"
  local model="$3"
  local result_dir="$4"
  local log_file="$5"
  local jobs="$6"
  shift 6
  local -a all_names=("$@")
  local -a names=()
  mapfile -t names < <(filter_existing "${all_names[@]}")
  if [[ ${#names[@]} -eq 0 ]]; then
    echo "[$label] nothing to run; all requested problems already exist in $RESULTS_ROOT"
    return 0
  fi
  echo "[$label] starting ${#names[@]} problems jobs=$jobs -> $result_dir"
  (
    set -o pipefail
    set +e
    scripts/verify_batch.sh --dataset "$DATASET" --agent "$agent" --model "$model" \
      --jobs "$jobs" --timeout "$TIMEOUT" "${names[@]}"
    rc=$?
    set -e
    shopt -s nullglob
    local name workspace
    for name in "${names[@]}"; do
      for workspace in output/verify_*_"$name"; do
        cp -a "$workspace" "$result_dir"/ 2>/dev/null || true
      done
    done
    exit "$rc"
  ) > "$log_file" 2>&1 &
  echo "[$label] pid=$! log=$log_file"
}

EXISTING_FILE="$(mktemp)"
trap 'rm -f "$EXISTING_FILE"' EXIT
existing_names > "$EXISTING_FILE"

requested="${1:-all}"

case "$requested" in
  all|codex)
    start_batch \
      codex codex gpt-5.4 "$RESULTS_ROOT/codex-54-medium" output/verify_batch_he_simple_codex_1.out "$CODEX_JOBS" \
      p131_digits p139_special_factorial p009_rolling_max \
      p042_incr_list p063_fibfib p076_is_simple_power \
      p126_is_sorted p040_triples_sum_to_zero p048_is_palindrome \
      p064_vowels_count p066_digitSum p082_prime_length
    ;;&
esac

# case "$requested" in
#   all|claude)
#     start_batch \
#       claude claude sonnet "$RESULTS_ROOT/claude-sonnet-medium" output/verify_batch_he_simple_claude_1.out "$CLAUDE_JOBS" \
#       p121_solutions p073_smallest_change p109_move_one_ball \
#       p135_can_arrange p043_pairs_sum_to_zero p128_prod_signs \
#       p027_filp_case p056_correct_bracketing
#     ;;&
# esac

case "$requested" in
  all|kimi|kimicode)
    start_batch \
      kimi kimicode kimi-code/kimi-for-coding "$RESULTS_ROOT/kimi-thinking" output/verify_batch_he_simple_kimi_1.out "$KIMI_JOBS" \
      p122_add_elements p072_will_it_fly p142_sum_squares \
      p114_minSubArraySum p089_encrypt p098_count_upper \
      p100_make_a_pile p146_specialFilter
    ;;&
esac

case "$requested" in
  all|codex|claude|kimi|kimicode) ;;
  *)
    echo "usage: $0 [all|codex|claude|kimi]" >&2
    exit 2
    ;;
esac

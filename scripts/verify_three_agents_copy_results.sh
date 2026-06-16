#!/usr/bin/env bash
# Start the three humaneval verify batches and copy finished output workspaces
# into each agent's result directory. Existing result workspaces are skipped.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

RESULTS_ROOT="/home/yangfp/CAV/C/CAV/results"
DATASET="humaneval"
TIMEOUT="${TIMEOUT:-5400}"
JOBS="${JOBS:-1}"
CODEX_JOBS="${CODEX_JOBS:-1}"
CLAUDE_JOBS="${CLAUDE_JOBS:-$JOBS}"
KIMI_JOBS="${KIMI_JOBS:-$JOBS}"

# label|agent|model|effort|result_dir|log_file|jobs
RUN_CONFIGS=(
  "claude-haiku-medium|claude|haiku|medium|$RESULTS_ROOT/claude-haiku-meduim|output/verify_batch_claude_haiku_medium.out|$CLAUDE_JOBS"
  "claude-opus-medium|claude|opus|medium|$RESULTS_ROOT/claude-opus-medium|output/verify_batch_claude_opus_medium.out|$CLAUDE_JOBS"
  "claude-sonnet-high|claude|sonnet|high|$RESULTS_ROOT/claude-sonnet-high|output/verify_batch_claude_sonnet_high.out|$CLAUDE_JOBS"
  "claude-sonnet-low|claude|sonnet|low|$RESULTS_ROOT/claude-sonnet-low|output/verify_batch_claude_sonnet_low.out|$CLAUDE_JOBS"
  "claude-sonnet-medium|claude|sonnet|medium|$RESULTS_ROOT/claude-sonnet-medium|output/verify_batch_he_simple_claude_1.out|$CLAUDE_JOBS"
  "codex-54-mini-medium|codex|gpt-5.4-mini|medium|$RESULTS_ROOT/codex-54-mini-medium|$RESULTS_ROOT/codex-54-mini-medium/verify_batch.out|$CODEX_JOBS"
  "codex-54-high|codex|gpt-5.4|high|$RESULTS_ROOT/codex-54-high|output/verify_batch_codex_54_high.out|$CODEX_JOBS"
  "codex-54-low|codex|gpt-5.4|low|$RESULTS_ROOT/codex-54-low|$RESULTS_ROOT/codex-54-low/verify_batch.out|$CODEX_JOBS"
  "codex-54-medium|codex|gpt-5.4|medium|$RESULTS_ROOT/codex-54-medium|output/verify_batch_codex_54_medium.out|$CODEX_JOBS"
  "codex-55-medium|codex|gpt-5.5|medium|$RESULTS_ROOT/codex-55-medium|output/verify_batch_codex_55_medium.out|$CODEX_JOBS"
  "kimi-thinking|kimicode|kimi-code/kimi-for-coding|thinking|$RESULTS_ROOT/kimi-thinking|output/verify_batch_he_simple_kimi_1.out|$KIMI_JOBS"
)

metric_value() {
  local metrics="$1"
  local key="$2"
  sed -n "s/^- ${key}: \`\([^\`]*\)\`$/\1/p" "$metrics" | tail -n 1
}

workspace_problem_name() {
  basename "$1" | sed -E 's/^verify_[0-9]{8}_[0-9]{6}[0-9]*_//'
}

existing_names() {
  local result_dir="$1"
  local agent="$2"
  local model="$3"
  local effort="$4"
  local workspace metrics got_agent got_model got_effort
  shopt -s nullglob
  for workspace in "$result_dir"/verify_*; do
    metrics="$workspace/logs/metrics.md"
    [[ -f "$metrics" ]] || continue
    got_agent="$(metric_value "$metrics" "Agent")"
    got_model="$(metric_value "$metrics" "Model")"
    got_effort="$(metric_value "$metrics" "Reasoning effort")"
    if [[ "$got_agent" == "$agent" && "$got_model" == "$model" && "$got_effort" == "$effort" ]]; then
      workspace_problem_name "$workspace"
    fi
  done | sort -u
  shopt -u nullglob
}

successful_names_global() {
  local metrics workspace
  find "$RESULTS_ROOT" output -path '*/logs/metrics.md' -type f 2>/dev/null | while read -r metrics; do
    if grep -Eq '^(Final Result: Success|- Status: `Success`)' "$metrics"; then
      workspace="$(dirname "$(dirname "$metrics")")"
      workspace_problem_name "$workspace"
    fi
  done | sort -u
}

filter_existing() {
  local existing_file="$1"
  shift
  local name
  for name in "$@"; do
    if ! grep -qxF "$name" "$existing_file"; then
      printf '%s\n' "$name"
    fi
  done
}

humaneval_names() {
  find "input/$DATASET" -maxdepth 1 -type f -name '*.c' -printf '%f\n' \
    | sed 's/\.c$//' \
    | sort
}

start_batch() {
  local config="$1"
  shift
  local label agent model effort result_dir log_file jobs
  IFS='|' read -r label agent model effort result_dir log_file jobs <<< "$config"
  local -a all_names=("$@")
  local -a names=()
  local existing_file
  mkdir -p "$result_dir"
  existing_file="$(mktemp)"
  {
    existing_names "$result_dir" "$agent" "$model" "$effort"
    successful_names_global
  } | sort -u > "$existing_file"
  mapfile -t names < <(filter_existing "$existing_file" "${all_names[@]}")
  rm -f "$existing_file"
  if [[ ${#names[@]} -eq 0 ]]; then
    echo "[$label] nothing to run; all requested problems already exist for agent=$agent model=$model effort=$effort in $result_dir"
    return 0
  fi
  echo "[$label] starting ${#names[@]} problems agent=$agent model=$model effort=$effort jobs=$jobs -> $result_dir"
  (
    set -o pipefail
    set +e
    mkdir -p "$result_dir/logs"
    export DATASET agent model effort TIMEOUT result_dir label
    printf '%s\n' "${names[@]}" | xargs -P "$jobs" -I{} bash -c '
      set +e
      name="$1"
      c="input/$DATASET/$name.c"
      problem_log="$result_dir/logs/$name.log"
      if [[ ! -f "$c" ]]; then
        echo "[$label] MISS $name (no $c)" | tee -a "$problem_log"
        exit 0
      fi
      ts="$(date +%Y%m%d_%H%M%S)$RANDOM"
      echo "[$label] START $name ts=$ts" | tee "$problem_log"
      python3 scripts/run_verify.py "$c" \
        --function-name "$name" --workspace-name "$name" \
        --timestamp "$ts" \
        --agent "$agent" --model "$model" --reasoning-effort "$effort" \
        --timeout-seconds "$TIMEOUT" \
        >> "$problem_log" 2>&1
      rc=$?
      workspace="$(awk "/^\\/.*\\/output\\/verify_/ {p=\\$0} END {print p}" "$problem_log")"
      if [[ -z "$workspace" || ! -d "$workspace" ]]; then
        workspace="$(ls -dt output/verify_*_"$name" 2>/dev/null | head -n 1)"
      fi
      if [[ -n "$workspace" && -d "$workspace" ]]; then
        mv "$workspace" "$result_dir"/
        echo "[$label] MOVED $name rc=$rc -> $result_dir/$(basename "$workspace")" | tee -a "$problem_log"
      else
        echo "[$label] NO_WORKSPACE $name rc=$rc" | tee -a "$problem_log"
      fi
      exit "$rc"
    ' _ {}
    rc=$?
    exit "$rc"
  ) > "$log_file" 2>&1 &
  echo "[$label] pid=$! log=$log_file"
}

config_for() {
  local label="$1"
  local config
  for config in "${RUN_CONFIGS[@]}"; do
    if [[ "${config%%|*}" == "$label" ]]; then
      printf '%s\n' "$config"
      return 0
    fi
  done
  return 1
}

requested="${1:-all}"

case "$requested" in
  all|codex|codex-54-mini-medium|mini)
    config="$(config_for codex-54-mini-medium)"
    mapfile -t names < <(humaneval_names)
    start_batch \
      "$config" \
      "${names[@]}"
    ;;&
esac

# case "$requested" in
#   all|claude)
#     config="$(config_for claude-sonnet-medium)"
#     start_batch \
#       "$config" \
#       p122_add_elements p072_will_it_fly p142_sum_squares \
#       p114_minSubArraySum p098_count_upper \
#       p100_make_a_pile p146_specialFilter p139_special_factorial p009_rolling_max \
#       p042_incr_list p063_fibfib p076_is_simple_power \
#       p126_is_sorted p040_triples_sum_to_zero p048_is_palindrome \
#       p064_vowels_count p066_digitSum p082_prime_length
#     ;;&
# esac

# case "$requested" in
#   all|kimi|kimicode)
#     config="$(config_for kimi-thinking)"
#     start_batch \
#       "$config" \
#       p015_string_sequence p016_count_distinct_characters \
#       p027_filp_case p050_decode_shift p051_remove_vowels \
#       p056_correct_bracketing p061_correct_bracketing \
#       p067_fruit_distribution p103_rounded_avg p150_x_or_y \
#       p017_parse_music p043_pairs_sum_to_zero p058_common \
#       p065_circular_shift p079_decimal_to_binary p091_is_bored \
#       p104_unique_digits p118_get_closest_vowel \
#       p119_match_parens p152_compare
#     ;;&
# esac

case "$requested" in
  all|codex|codex-54-mini-medium|mini|claude|kimi|kimicode) ;;
  *)
    echo "usage: $0 [all|codex|codex-54-mini-medium|mini|claude|kimi]" >&2
    exit 2
    ;;
esac

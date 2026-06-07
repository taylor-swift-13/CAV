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

# label|agent|model|effort|result_dir|log_file|jobs
RUN_CONFIGS=(
  "claude-haiku-medium|claude|haiku|medium|$RESULTS_ROOT/claude-haiku-meduim|output/verify_batch_claude_haiku_medium.out|$CLAUDE_JOBS"
  "claude-opus-medium|claude|opus|medium|$RESULTS_ROOT/claude-opus-medium|output/verify_batch_claude_opus_medium.out|$CLAUDE_JOBS"
  "claude-sonnet-high|claude|sonnet|high|$RESULTS_ROOT/claude-sonnet-high|output/verify_batch_claude_sonnet_high.out|$CLAUDE_JOBS"
  "claude-sonnet-low|claude|sonnet|low|$RESULTS_ROOT/claude-sonnet-low|output/verify_batch_claude_sonnet_low.out|$CLAUDE_JOBS"
  "claude-sonnet-medium|claude|sonnet|medium|$RESULTS_ROOT/claude-sonnet-medium|output/verify_batch_he_simple_claude_1.out|$CLAUDE_JOBS"
  "codex-54-high|codex|gpt-5.4|high|$RESULTS_ROOT/codex-54-high|output/verify_batch_codex_54_high.out|$CODEX_JOBS"
  "codex-54-low|codex|gpt-5.4|low|$RESULTS_ROOT/codex-54-low|output/verify_batch_codex_54_low.out|$CODEX_JOBS"
  "codex-54-medium|codex|gpt-5.4|medium|$RESULTS_ROOT/codex-54-medium|output/verify_batch_codex_54_medium.out|$CODEX_JOBS"
  "codex-55-medium|codex|gpt-5.5|medium|$RESULTS_ROOT/codex-55-medium|output/verify_batch_codex_55_medium.out|$CODEX_JOBS"
  "kimi-thinking|kimicode|kimi-code/kimi-for-coding|thinking|$RESULTS_ROOT/kimi-thinking|output/verify_batch_he_simple_kimi_1.out|$KIMI_JOBS"
)

metric_value() {
  local metrics="$1"
  local key="$2"
  sed -n "s/^- ${key}: \`\([^\`]*\)\`$/\1/p" "$metrics" | tail -n 1
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
      basename "$workspace" | sed -E 's/^verify_[0-9]{8}_[0-9]{6}_//'
    fi
  done | sort -u
  shopt -u nullglob
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
  existing_names "$result_dir" "$agent" "$model" "$effort" > "$existing_file"
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
    scripts/verify_batch.sh --dataset "$DATASET" --agent "$agent" --model "$model" \
      --reasoning-effort "$effort" --jobs "$jobs" --timeout "$TIMEOUT" "${names[@]}"
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

# case "$requested" in
#   codex)
#     echo "[codex] no problems assigned in this rotation"
#     ;;&
# esac

# case "$requested" in
#   all|claude)
#     config="$(config_for claude-sonnet-medium)"
#     start_batch \
#       "$config" \
#       p122_add_elements p072_will_it_fly p142_sum_squares \
#       p114_minSubArraySum p089_encrypt p098_count_upper \
#       p100_make_a_pile p146_specialFilter
#     ;;&
# esac

case "$requested" in
  all|kimi|kimicode)
    config="$(config_for kimi-thinking)"
    start_batch \
      "$config" \
      p131_digits p139_special_factorial p009_rolling_max \
      p042_incr_list p063_fibfib p076_is_simple_power \
      p126_is_sorted p040_triples_sum_to_zero p048_is_palindrome \
      p064_vowels_count p066_digitSum p082_prime_length
    ;;&
esac

case "$requested" in
  all|codex|claude|kimi|kimicode) ;;
  *)
    echo "usage: $0 [all|codex|claude|kimi]" >&2
    exit 2
    ;;
esac

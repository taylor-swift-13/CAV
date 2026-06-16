#!/usr/bin/env bash
# Run one verify agent/model configuration for one or more problems.
# Finished output workspaces are copied to results/<agent>/<model>/<effort>/,
# then the corresponding output/QCP/annotated workspaces are removed.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

RESULTS_ROOT="${RESULTS_ROOT:-$ROOT/results}"
DATASET="${DATASET:-humaneval}"
TIMEOUT="${TIMEOUT:-5400}"
JOBS="${JOBS:-1}"
CODEX_JOBS="${CODEX_JOBS:-$JOBS}"
CLAUDE_JOBS="${CLAUDE_JOBS:-$JOBS}"
KIMI_JOBS="${KIMI_JOBS:-$JOBS}"
FOREGROUND="${FOREGROUND:-1}"
FORCE=0

usage() {
  cat <<'EOF'
usage: scripts/verify_agent_copy_results.sh [options] <config> [problem_name ...]

Runs exactly one verify agent/model configuration. Multiple problem names run
concurrently according to that config's jobs value. If no problem names are
provided, all input/<dataset>/*.c problems are considered.

Results are saved under:
  results/<agent>/<model>/<effort>/

After a workspace is copied to results, the matching output/, annotated/, and
QCP mirror directories are removed.

Configs:
  claude-ark-api
  codex-ark-api       (disabled: third-party APIs must use Claude Code)
  codex-54-high
  codex-54-medium
  codex-54-low
  codex-54-mini-medium
  codex-55-medium
  claude-haiku-medium
  claude-opus-medium
  claude-sonnet-high
  claude-sonnet-low
  claude-sonnet-medium
  kimi-thinking

Aliases:
  ark     -> claude-ark-api
  high    -> codex-54-high
  medium  -> codex-54-medium
  low     -> codex-54-low
  mini    -> codex-54-mini-medium
  kimi    -> kimi-thinking

Options:
  --dataset NAME       Read input/<dataset>/*.c. Default: humaneval.
  --jobs N, -j N       Override concurrency for this run.
  --timeout N          Per-problem verify timeout in seconds. Default: 5400.
  --results-root DIR   Archive root. Default: ./results.
  --background         Start the batch in background.
  --foreground         Run in foreground. Default.
  --force              Run even if a matching result already exists.
  -h, --help           Show this help.

Examples:
  scripts/verify_agent_copy_results.sh codex-54-high p127_intersection
  scripts/verify_agent_copy_results.sh --jobs 3 codex-54-high p001_separate_paren_groups p002_truncate_number
EOF
}

safe_path_component() {
  printf '%s\n' "$1" | sed 's#[/[:space:]]#__#g'
}

result_dir_for() {
  local root="$1"
  local harness="$2"
  local model="$3"
  local effort="$4"
  printf '%s/%s/%s/%s\n' "$root" "$(safe_path_component "$harness")" "$(safe_path_component "$model")" "$(safe_path_component "$effort")"
}

build_run_configs() {
  local ark_agent_config="$ROOT/config/ark_api/agents_ark.json"
  local claude_ark_agent_config="$ROOT/config/ark_api/agents_ark_claude.json"
  RUN_CONFIGS=(
    "claude-haiku-medium|claude|haiku|medium|$(result_dir_for "$RESULTS_ROOT" claude haiku medium)|output/verify_batch_claude_haiku_medium.out|$CLAUDE_JOBS|"
    "claude-opus-medium|claude|opus|medium|$(result_dir_for "$RESULTS_ROOT" claude opus medium)|output/verify_batch_claude_opus_medium.out|$CLAUDE_JOBS|"
    "claude-sonnet-high|claude|sonnet|high|$(result_dir_for "$RESULTS_ROOT" claude sonnet high)|output/verify_batch_claude_sonnet_high.out|$CLAUDE_JOBS|"
    "claude-sonnet-low|claude|sonnet|low|$(result_dir_for "$RESULTS_ROOT" claude sonnet low)|output/verify_batch_claude_sonnet_low.out|$CLAUDE_JOBS|"
    "claude-sonnet-medium|claude|sonnet|medium|$(result_dir_for "$RESULTS_ROOT" claude sonnet medium)|output/verify_batch_claude_sonnet_medium.out|$CLAUDE_JOBS|"
    "claude-ark-api|claude|ark-code-latest|api|$(result_dir_for "$RESULTS_ROOT" claude ark-code-latest api)|output/verify_batch_claude_ark_api.out|$CLAUDE_JOBS|$claude_ark_agent_config"
    "codex-ark-api|codex|ark-code-latest|api|$(result_dir_for "$RESULTS_ROOT" codex ark-code-latest api)|output/verify_batch_codex_ark_api.out|$CODEX_JOBS|$ark_agent_config"
    "codex-54-mini-medium|codex|gpt-5.4-mini|medium|$(result_dir_for "$RESULTS_ROOT" codex gpt-5.4-mini medium)|output/verify_batch_codex_54_mini_medium.out|$CODEX_JOBS|"
    "codex-54-high|codex|gpt-5.4|high|$(result_dir_for "$RESULTS_ROOT" codex gpt-5.4 high)|output/verify_batch_codex_54_high.out|$CODEX_JOBS|"
    "codex-54-low|codex|gpt-5.4|low|$(result_dir_for "$RESULTS_ROOT" codex gpt-5.4 low)|output/verify_batch_codex_54_low.out|$CODEX_JOBS|"
    "codex-54-medium|codex|gpt-5.4|medium|$(result_dir_for "$RESULTS_ROOT" codex gpt-5.4 medium)|output/verify_batch_codex_54_medium.out|$CODEX_JOBS|"
    "codex-55-medium|codex|gpt-5.5|medium|$(result_dir_for "$RESULTS_ROOT" codex gpt-5.5 medium)|output/verify_batch_codex_55_medium.out|$CODEX_JOBS|"
    "kimi-thinking|kimicode|kimi-code/kimi-for-coding|thinking|$(result_dir_for "$RESULTS_ROOT" kimicode kimi-code/kimi-for-coding thinking)|output/verify_batch_kimi_thinking.out|$KIMI_JOBS|"
  )
}

canonical_config() {
  case "$1" in
    ark|ark-api) printf '%s\n' "claude-ark-api" ;;
    codex-ark|codex-ark-api)
      echo "third-party API runs via Codex are disabled; add/use a Claude Code config instead" >&2
      exit 2
      ;;
    high) printf '%s\n' "codex-54-high" ;;
    medium|codex) printf '%s\n' "codex-54-medium" ;;
    low) printf '%s\n' "codex-54-low" ;;
    mini|codex-mini) printf '%s\n' "codex-54-mini-medium" ;;
    kimi|kimicode) printf '%s\n' "kimi-thinking" ;;
    *) printf '%s\n' "$1" ;;
  esac
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

metric_value() {
  local metrics="$1"
  local key="$2"
  sed -n "s/^- ${key}: \`\([^\`]*\)\`$/\1/p" "$metrics" | tail -n 1
}

workspace_problem_name() {
  basename "$1" | sed -E 's/^verify_[0-9]{8}_[0-9]{6}[0-9]*_//'
}

cleanup_workspace_after_result_copy() {
  local workspace="$1"
  local base
  base="$(basename "$workspace")"
  if [[ -z "$base" || "$base" != verify_* ]]; then
    echo "refusing to clean unexpected workspace path: $workspace" >&2
    return 1
  fi
  rm -rf \
    "$ROOT/QualifiedCProgramming/QCP_examples/CAV/$base" \
    "$ROOT/QualifiedCProgramming/.tmp/QCP_examples/CAV/$base" \
    "$ROOT/QualifiedCProgramming/SeparationLogic/examples/CAV/$base" \
    "$ROOT/QualifiedCProgramming/.tmp/SeparationLogic/examples/CAV/$base" \
    "$ROOT/QualifiedCProgramming/SeparationLogic/_cav_locks/$base" \
    "$ROOT/annotated/$base.c" \
    "$workspace"
}

copy_workspace_to_result_dir() {
  local workspace="$1"
  local result_dir="$2"
  local label="$3"
  local name="$4"
  local dest
  dest="$result_dir/$(basename "$workspace")"
  if [[ -e "$dest" ]]; then
    echo "[$label] SKIP_COPY $name -> $dest (exists)"
    cleanup_workspace_after_result_copy "$workspace"
    return 0
  fi
  mkdir -p "$result_dir"
  if cp -a "$workspace" "$result_dir"/; then
    echo "[$label] COPIED $name -> $dest"
    cleanup_workspace_after_result_copy "$workspace"
    return 0
  fi
  echo "[$label] COPY_FAILED $name -> $dest"
  return 1
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

filter_existing() {
  local existing_file="$1"
  shift
  local name
  for name in "$@"; do
    if [[ "$FORCE" -eq 1 ]] || ! grep -qxF "$name" "$existing_file"; then
      printf '%s\n' "$name"
    fi
  done
}

input_names() {
  local input_dir="input/$DATASET"
  [[ -d "$input_dir" ]] || { echo "missing input dataset directory: $input_dir" >&2; return 2; }
  find "$input_dir" -maxdepth 1 -type f -name '*.c' -printf '%f\n' \
    | sed 's/\.c$//' \
    | sort
}

validate_positive_int() {
  local name="$1"
  local value="$2"
  if ! [[ "$value" =~ ^[0-9]+$ ]] || [[ "$value" -lt 1 ]]; then
    echo "$name must be a positive integer: $value" >&2
    exit 2
  fi
}

start_batch() {
  local config="$1"
  shift
  local label agent model effort result_dir log_file jobs agent_config
  IFS='|' read -r label agent model effort result_dir log_file jobs agent_config <<< "$config"
  if [[ -n "${BATCH_LOG_SUFFIX:-}" ]]; then
    log_file="${log_file%.out}_${BATCH_LOG_SUFFIX}.out"
  fi
  local -a all_names=("$@")
  local -a names=()
  local existing_file

  mkdir -p "$result_dir"
  existing_file="$(mktemp)"
  existing_names "$result_dir" "$agent" "$model" "$effort" > "$existing_file"
  mapfile -t names < <(filter_existing "$existing_file" "${all_names[@]}" | awk '!seen[$0]++')
  rm -f "$existing_file"

  if [[ ${#names[@]} -eq 0 ]]; then
    echo "[$label] nothing to run; requested problems already exist for agent=$agent model=$model effort=$effort in $result_dir"
    return 0
  fi

  echo "[$label] starting ${#names[@]} problems agent=$agent model=$model effort=$effort jobs=$jobs -> $result_dir"

  run_batch_jobs() {
    set -o pipefail
    set +e
    mkdir -p output
    lock_dir="output/.${LOCK_LABEL:-$label}.lock"
    if ! mkdir "$lock_dir" 2>/dev/null; then
      lock_pid="$(cat "$lock_dir/pid" 2>/dev/null || true)"
      if [[ -n "$lock_pid" ]] && kill -0 "$lock_pid" 2>/dev/null; then
        echo "[$label] lock exists at $lock_dir; pid=$lock_pid is still running"
        return 1
      fi
      echo "[$label] removing stale lock at $lock_dir"
      rm -rf "$lock_dir"
      if ! mkdir "$lock_dir" 2>/dev/null; then
        echo "[$label] could not acquire lock at $lock_dir"
        return 1
      fi
    fi
    printf '%s\n' "$$" > "$lock_dir/pid"
    trap 'rm -rf "$lock_dir"' EXIT
    problem_lock_root="$lock_dir/problems"
    mkdir -p "$problem_lock_root"

    export ROOT DATASET TIMEOUT
    export agent model effort result_dir label problem_lock_root agent_config
    export -f cleanup_workspace_after_result_copy
    export -f copy_workspace_to_result_dir

    printf '%s\n' "${names[@]}" | xargs -P "$jobs" -I{} bash -c '
      set +e
      name="$1"
      problem_lock="$problem_lock_root/$name.lock"
      if ! mkdir "$problem_lock" 2>/dev/null; then
        lock_pid="$(cat "$problem_lock/pid" 2>/dev/null || true)"
        if [[ -n "$lock_pid" ]] && kill -0 "$lock_pid" 2>/dev/null; then
          echo "[$label] SKIP_RUNNING $name pid=$lock_pid"
          exit 0
        fi
        rm -rf "$problem_lock"
        if ! mkdir "$problem_lock" 2>/dev/null; then
          echo "[$label] SKIP_LOCKED $name"
          exit 0
        fi
      fi
      printf "%s\n" "$$" > "$problem_lock/pid"
      trap "rm -rf \"$problem_lock\"" EXIT

      c="input/$DATASET/$name.c"
      if [[ ! -f "$c" ]]; then
        problem_log="output/missing_${label}_${name}.log"
        echo "[$label] MISS $name (no $c)" | tee -a "$problem_log"
        exit 0
      fi

      ts="$(date +%Y%m%d_%H%M%S)$RANDOM"
      workspace="output/verify_${ts}_${name}"
      mkdir -p "$workspace/logs"
      problem_log="$workspace/logs/batch.log"
      echo "[$label] START $name ts=$ts" | tee "$problem_log"

      if [[ -n "${agent_config:-}" ]]; then
        export CAV_AGENT_CONFIG="$agent_config"
      fi
      python3 scripts/run_verify.py "$c" \
        --function-name "$name" --workspace-name "$name" \
        --timestamp "$ts" \
        --agent "$agent" --model "$model" --reasoning-effort "$effort" \
        --timeout-seconds "$TIMEOUT" \
        >> "$problem_log" 2>&1
      rc=$?

      if [[ -z "$workspace" || ! -d "$workspace" ]]; then
        workspace="$(ls -dt output/verify_*_"$name" 2>/dev/null | head -n 1)"
      fi
      if [[ -n "$workspace" && -d "$workspace" ]]; then
        echo "[$label] RUN_DONE $name rc=$rc workspace=$workspace" | tee -a "$problem_log"
        if ! copy_workspace_to_result_dir "$workspace" "$result_dir" "$label" "$name"; then
          rc=1
        fi
        echo "[$label] DONE $name rc=$rc workspace=$workspace"
      else
        echo "[$label] NO_WORKSPACE $name rc=$rc" | tee -a "$problem_log"
        rc=1
      fi
      exit "$rc"
    ' _ {}
  }

  finalize_batch_log() {
    local batch_rc="$1"
    local final_log="$result_dir/$(basename "$log_file")"
    mkdir -p "$result_dir"
    if [[ -f "$log_file" ]]; then
      cp -a "$log_file" "$final_log"
      rm -f "$log_file"
    fi
    return "$batch_rc"
  }

  if [[ "$FOREGROUND" == "1" ]]; then
    mkdir -p "$(dirname "$log_file")"
    run_batch_jobs > "$log_file" 2>&1
    local batch_rc=$?
    finalize_batch_log "$batch_rc"
    echo "[$label] completed rc=$batch_rc log=$result_dir/$(basename "$log_file")"
    return "$batch_rc"
  fi

  mkdir -p "$(dirname "$log_file")"
  (
    trap "" HUP
    run_batch_jobs > "$log_file" 2>&1
    batch_rc=$?
    finalize_batch_log "$batch_rc"
    exit "$batch_rc"
  ) &
  disown "$!" 2>/dev/null || true
  echo "[$label] pid=$! log=$log_file final_log=$result_dir/$(basename "$log_file")"
}

POSITIONAL=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --dataset)
      [[ $# -ge 2 ]] || { echo "missing value for --dataset" >&2; exit 2; }
      DATASET="$2"
      shift 2
      ;;
    --jobs|-j)
      [[ $# -ge 2 ]] || { echo "missing value for $1" >&2; exit 2; }
      JOBS="$2"
      CODEX_JOBS="$2"
      CLAUDE_JOBS="$2"
      KIMI_JOBS="$2"
      shift 2
      ;;
    --timeout)
      [[ $# -ge 2 ]] || { echo "missing value for --timeout" >&2; exit 2; }
      TIMEOUT="$2"
      shift 2
      ;;
    --results-root)
      [[ $# -ge 2 ]] || { echo "missing value for --results-root" >&2; exit 2; }
      RESULTS_ROOT="$2"
      shift 2
      ;;
    --background)
      FOREGROUND=0
      shift
      ;;
    --foreground)
      FOREGROUND=1
      shift
      ;;
    --force)
      FORCE=1
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    --)
      shift
      while [[ $# -gt 0 ]]; do
        POSITIONAL+=("$1")
        shift
      done
      ;;
    -*)
      echo "unknown option: $1" >&2
      usage >&2
      exit 2
      ;;
    *)
      POSITIONAL+=("$1")
      shift
      ;;
  esac
done

validate_positive_int "JOBS" "$JOBS"
validate_positive_int "TIMEOUT" "$TIMEOUT"

if [[ ${#POSITIONAL[@]} -lt 1 ]]; then
  usage >&2
  exit 2
fi

requested="$(canonical_config "${POSITIONAL[0]}")"
REQUESTED_NAMES=("${POSITIONAL[@]:1}")

case "$requested" in
  all)
    echo "this script now runs exactly one config; pass a single config such as codex-54-high" >&2
    exit 2
    ;;
esac

build_run_configs
config="$(config_for "$requested" || true)"
if [[ -z "$config" ]]; then
  echo "unknown config: ${POSITIONAL[0]}" >&2
  usage >&2
  exit 2
fi

if [[ ${#REQUESTED_NAMES[@]} -gt 0 ]]; then
  names=("${REQUESTED_NAMES[@]}")
else
  mapfile -t names < <(input_names)
fi

start_batch "$config" "${names[@]}"

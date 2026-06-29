#!/usr/bin/env bash
# Automatically run the remaining CAV batches without exceeding quota/process limits.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

CHECK_INTERVAL_SECONDS="${CHECK_INTERVAL_SECONDS:-10800}"
MAX_ACTIVE_TASKS="${MAX_ACTIVE_TASKS:-2}"
MAX_AGENT_PROCESSES="${MAX_AGENT_PROCESSES:-2}"
MAX_PROBLEMS_PER_BATCH="${MAX_PROBLEMS_PER_BATCH:-10}"
QUOTA_SLEEP_SECONDS="${QUOTA_SLEEP_SECONDS:-18000}"
FAST_FAIL_SECONDS="${FAST_FAIL_SECONDS:-120}"
KIMI_NOT_BEFORE="${KIMI_NOT_BEFORE:-}"
STATE_DIR="${STATE_DIR:-$ROOT/output/cav_auto_scheduler}"
STATE_FILE="$STATE_DIR/queue_index"
LOG_DIR="$ROOT/output"

mkdir -p "$STATE_DIR" "$LOG_DIR"

TASK_IDS=(
  codex55_verify
  ark_verify
  codex54_pipeline
  codex54_proof
  kimi_verify
)

log() {
  printf '[%s] %s\n' "$(date '+%F %T %z')" "$*"
}

task_session() {
  case "$1" in
    codex55_verify) printf 'cav_codex55_verify\n' ;;
    ark_verify) printf 'cav_ark_verify\n' ;;
    codex54_pipeline) printf 'cav_codex54_pipeline\n' ;;
    codex54_proof) printf 'cav_codex54_proof\n' ;;
    kimi_verify) printf 'cav_kimi_verify\n' ;;
    *) return 1 ;;
  esac
}

task_group() {
  case "$1" in
    codex55_verify|codex54_pipeline|codex54_proof) printf 'codex\n' ;;
    ark_verify) printf 'ark\n' ;;
    kimi_verify) printf 'kimi\n' ;;
    *) return 1 ;;
  esac
}

task_label() {
  case "$1" in
    codex55_verify) printf 'verify codex gpt-5.5 medium\n' ;;
    ark_verify) printf 'verify ark deepseek-v4-pro api\n' ;;
    codex54_pipeline) printf 'pipeline codex gpt-5.4 medium\n' ;;
    codex54_proof) printf 'proof codex gpt-5.4 medium\n' ;;
    kimi_verify) printf 'verify kimi thinking\n' ;;
    *) return 1 ;;
  esac
}

session_exists() {
  tmux has-session -t "$1" 2>/dev/null
}

active_task_count() {
  local task session count=0
  for task in "${TASK_IDS[@]}"; do
    session="$(task_session "$task")"
    if session_exists "$session"; then
      count=$((count + 1))
    fi
  done
  printf '%s\n' "$count"
}

active_agent_count() {
  ps -eo comm=,args= \
    | awk '$1 == "python3" && $0 ~ /scripts\/(run_verify|run_pipeline)\.py/ { count++ } END { print count + 0 }'
}

group_is_active() {
  local group="$1"
  local task session
  for task in "${TASK_IDS[@]}"; do
    [[ "$(task_group "$task")" == "$group" ]] || continue
    session="$(task_session "$task")"
    if session_exists "$session"; then
      return 0
    fi
  done
  return 1
}

metric_exists_for_problem() {
  local result_dir="$1"
  local name="$2"
  find "$result_dir" -maxdepth 1 -type d -name "verify_*_${name}" -exec test -f '{}/logs/metrics.md' ';' -print -quit 2>/dev/null | grep -q .
}

count_verify_done() {
  local result_dir="$1"
  local total=0 done=0 name
  while IFS= read -r name; do
    total=$((total + 1))
    if metric_exists_for_problem "$result_dir" "$name"; then
      done=$((done + 1))
    fi
  done < <(find input/humaneval -maxdepth 1 -type f -name '*.c' -printf '%f\n' | sed 's/\.c$//' | sort)
  printf '%s/%s\n' "$done" "$total"
}

count_pipeline_done() {
  local result_dir="$1"
  local total=0 done=0 name
  while IFS= read -r name; do
    total=$((total + 1))
    if find "$result_dir" -maxdepth 1 -type d -name "pipeline_*_${name}" -print -quit 2>/dev/null | grep -q .; then
      done=$((done + 1))
    fi
  done < <(find raw/humaneval -maxdepth 1 -type f -name '*.md' -printf '%f\n' | sed 's/\.md$//' | sort)
  printf '%s/%s\n' "$done" "$total"
}

count_proof_done() {
  local result_dir="$1"
  local total=0 done=0 name
  while IFS= read -r name; do
    total=$((total + 1))
    if find "$result_dir" -maxdepth 1 -type d \( -name "proof_*_${name}" -o -name "verify_*_${name}" \) -exec test -f '{}/logs/metrics.md' ';' -print -quit 2>/dev/null | grep -q .; then
      done=$((done + 1))
    fi
  done < <(find annotated_input/humaneval -maxdepth 1 -type f -name '*.c' -printf '%f\n' | sed 's/\.c$//' | sort)
  printf '%s/%s\n' "$done" "$total"
}

task_progress() {
  case "$1" in
    codex55_verify) count_verify_done "$ROOT/results/codex/gpt-5.5/medium" ;;
    ark_verify) count_verify_done "$ROOT/results/claude/deepseek-v4-pro/api" ;;
    codex54_pipeline) count_pipeline_done "$ROOT/pipeline_results/codex/gpt-5.4/medium" ;;
    codex54_proof) count_proof_done "$ROOT/proof_results/codex/gpt-5.4/medium" ;;
    kimi_verify) count_verify_done "$ROOT/results/kimicode/kimi-code__kimi-for-coding/thinking" ;;
    *) return 1 ;;
  esac
}

task_complete() {
  local progress done total
  progress="$(task_progress "$1")"
  done="${progress%/*}"
  total="${progress#*/}"
  [[ "$total" != "0" && "$done" -ge "$total" ]]
}

kimi_allowed() {
  [[ -z "$KIMI_NOT_BEFORE" ]] && return 0
  local now target
  now="$(date +%s)"
  target="$(date -d "$KIMI_NOT_BEFORE" +%s)"
  [[ "$now" -ge "$target" ]]
}

launch_task() {
  local task="$1"
  local session log_file cmd ts
  session="$(task_session "$task")"
  ts="$(date +%Y%m%d_%H%M%S)"

  case "$task" in
    codex55_verify)
      rm -f "$ROOT/output/stop_codex-55-medium.flag"
      log_file="$LOG_DIR/batch_safe_codex55_auto_${ts}.out"
      cmd="cd '$ROOT'; MAX_PROBLEMS=$MAX_PROBLEMS_PER_BATCH QUOTA_SLEEP_SECONDS=$QUOTA_SLEEP_SECONDS FAST_FAIL_SECONDS=$FAST_FAIL_SECONDS scripts/batch_safe_verify.sh codex-55-medium >> '$log_file' 2>&1"
      ;;
    ark_verify)
      rm -f "$ROOT/output/stop_claude-ark-api.flag"
      log_file="$LOG_DIR/batch_safe_ark_auto_${ts}.out"
      cmd="cd '$ROOT'; MAX_PROBLEMS=$MAX_PROBLEMS_PER_BATCH QUOTA_SLEEP_SECONDS=$QUOTA_SLEEP_SECONDS FAST_FAIL_SECONDS=$FAST_FAIL_SECONDS scripts/batch_safe_verify.sh claude-ark-api >> '$log_file' 2>&1"
      ;;
    codex54_pipeline)
      rm -f "$ROOT/output/stop_pipeline_codex-54-medium.flag"
      log_file="$LOG_DIR/batch_safe_pipeline_codex54_auto_${ts}.out"
      cmd="cd '$ROOT'; MAX_PROBLEMS=$MAX_PROBLEMS_PER_BATCH QUOTA_SLEEP_SECONDS=$QUOTA_SLEEP_SECONDS FAST_FAIL_SECONDS=$FAST_FAIL_SECONDS scripts/batch_safe_pipeline.sh codex-54-medium >> '$log_file' 2>&1"
      ;;
    codex54_proof)
      rm -f "$ROOT/output/stop_proof_codex-54-medium.flag"
      log_file="$LOG_DIR/batch_safe_proof_codex54_auto_${ts}.out"
      cmd="cd '$ROOT'; MAX_PROBLEMS=$MAX_PROBLEMS_PER_BATCH QUOTA_SLEEP_SECONDS=$QUOTA_SLEEP_SECONDS FAST_FAIL_SECONDS=$FAST_FAIL_SECONDS scripts/batch_safe_proof.sh codex-54-medium >> '$log_file' 2>&1"
      ;;
    kimi_verify)
      rm -f "$ROOT/output/stop_kimi-thinking.flag"
      log_file="$LOG_DIR/batch_safe_kimi_auto_${ts}.out"
      cmd="cd '$ROOT'; MAX_PROBLEMS=$MAX_PROBLEMS_PER_BATCH QUOTA_SLEEP_SECONDS=$QUOTA_SLEEP_SECONDS FAST_FAIL_SECONDS=$FAST_FAIL_SECONDS scripts/batch_safe_verify.sh kimi-thinking >> '$log_file' 2>&1"
      ;;
    *)
      return 1
      ;;
  esac

  tmux new-session -d -s "$session" "$cmd"
  log "LAUNCH task=$task session=$session log=$log_file"
}

next_queue_index() {
  if [[ -f "$STATE_FILE" ]]; then
    cat "$STATE_FILE"
  else
    printf '0\n'
  fi
}

set_queue_index() {
  printf '%s\n' "$1" > "$STATE_FILE"
}

all_tasks_complete() {
  local task
  for task in "${TASK_IDS[@]}"; do
    task_complete "$task" || return 1
  done
  return 0
}

maybe_launch_available_tasks() {
  local active_tasks active_agents idx attempts task session group progress next_idx
  attempts=0

  while true; do
    active_tasks="$(active_task_count)"
    active_agents="$(active_agent_count)"
    if [[ "$active_tasks" -ge "$MAX_ACTIVE_TASKS" || "$active_agents" -ge "$MAX_AGENT_PROCESSES" ]]; then
      log "CAPACITY active_tasks=$active_tasks/$MAX_ACTIVE_TASKS active_agents=$active_agents/$MAX_AGENT_PROCESSES"
      return 0
    fi

    idx="$(next_queue_index)"
    while [[ "$attempts" -lt "${#TASK_IDS[@]}" ]]; do
      task="${TASK_IDS[$idx]}"
      next_idx=$(( (idx + 1) % ${#TASK_IDS[@]} ))
      set_queue_index "$next_idx"
      attempts=$((attempts + 1))

      session="$(task_session "$task")"
      group="$(task_group "$task")"
      progress="$(task_progress "$task")"

      if task_complete "$task"; then
        log "SKIP task=$task progress=$progress reason=complete"
        idx="$next_idx"
        continue
      fi
      if [[ "$task" == "kimi_verify" ]] && ! kimi_allowed; then
        log "SKIP task=$task progress=$progress reason=kimi_not_before value=$KIMI_NOT_BEFORE"
        idx="$next_idx"
        continue
      fi
      if session_exists "$session"; then
        log "SKIP task=$task progress=$progress reason=session_active session=$session"
        idx="$next_idx"
        continue
      fi
      if group_is_active "$group"; then
        log "SKIP task=$task progress=$progress reason=quota_group_active group=$group"
        idx="$next_idx"
        continue
      fi

      launch_task "$task"
      attempts=0
      break
    done

    if [[ "$attempts" -ge "${#TASK_IDS[@]}" ]]; then
      return 0
    fi
  done
}

main_loop() {
  log "START scheduler interval=${CHECK_INTERVAL_SECONDS}s max_active_tasks=$MAX_ACTIVE_TASKS max_agent_processes=$MAX_AGENT_PROCESSES max_batch=$MAX_PROBLEMS_PER_BATCH kimi_not_before=${KIMI_NOT_BEFORE:-none}"

  while true; do
    log "CHECK_BEGIN"
    for task in "${TASK_IDS[@]}"; do
      log "STATUS task=$task label=\"$(task_label "$task")\" progress=$(task_progress "$task") session=$(task_session "$task")"
    done

    if all_tasks_complete; then
      log "ALL_TASKS_COMPLETE"
      exit 0
    fi

    maybe_launch_available_tasks
    log "CHECK_END sleeping=${CHECK_INTERVAL_SECONDS}s"
    sleep "$CHECK_INTERVAL_SECONDS"
  done
}

main_loop "$@"

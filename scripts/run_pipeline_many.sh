#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PIPELINE_SCRIPT="$ROOT/scripts/run_pipeline.py"

EXPORT_EXAMPLES=1
SKIP_EVAL=0
SKIP_CONSOLIDATE=0
FORCE=0
DRY_RUN=0
JOBS=1
CONTRACT_ROUNDS=2
# Empty = defer to config/agents.json `timeouts` (run_pipeline.py resolves them).
# Set via the matching flag to override for this run.
CONTRACT_TIMEOUT=""
EVAL_TIMEOUT=""
VERIFY_TIMEOUT=""
CONSOLIDATE_TIMEOUT=""
CONFIG=""
AGENT=""
MODEL=""
REASONING_EFFORT=""

usage() {
  cat <<'EOF'
usage: run_pipeline_many.sh [pipeline options] [--jobs N|-j N] <name1> [name2 ...]

Multi-process wrapper for scripts/run_pipeline.py. For each <name>, run:
  python3 scripts/run_pipeline.py raw/<name>.md --function-name <name>

By default each item uses the full run_pipeline flow:
  contract -> eval -> verify -> consolidate

Options:
  --jobs N, -j N         Run up to N names concurrently. Default: 1.
  --contract-rounds N    Passed to run_pipeline.py. Default: 2.
  --contract-timeout N   Passed to run_pipeline.py. Default: 300.
  --eval-timeout N       Passed to run_pipeline.py. Default: 900.
  --verify-timeout N     Passed to run_pipeline.py. Default: 3600.
  --consolidate-timeout N
                         Passed to run_pipeline.py. Default: 600.
  --skip-eval            Passed to run_pipeline.py.
  --skip-consolidate     Passed to run_pipeline.py.
  --no-export-examples   Passed to run_pipeline.py as --no-export.
  --force                Passed to run_pipeline.py.
  --config PATH          Passed to run_pipeline.py.
  --agent codex|claude   Passed to run_pipeline.py.
  --model MODEL          Passed to run_pipeline.py.
  --reasoning-effort E   Passed to run_pipeline.py.
  --dry-run              Passed to run_pipeline.py.
EOF
}

NAMES=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --no-export-examples)
      EXPORT_EXAMPLES=0
      shift
      ;;
    --skip-eval)
      SKIP_EVAL=1
      shift
      ;;
    --skip-consolidate)
      SKIP_CONSOLIDATE=1
      shift
      ;;
    --force)
      FORCE=1
      shift
      ;;
    --dry-run)
      DRY_RUN=1
      shift
      ;;
    --jobs|-j)
      if [[ $# -lt 2 ]]; then
        echo "missing value for $1" >&2
        usage >&2
        exit 2
      fi
      JOBS="$2"
      shift 2
      ;;
    --contract-rounds)
      if [[ $# -lt 2 ]]; then
        echo "missing value for $1" >&2
        usage >&2
        exit 2
      fi
      CONTRACT_ROUNDS="$2"
      shift 2
      ;;
    --contract-timeout)
      if [[ $# -lt 2 ]]; then
        echo "missing value for $1" >&2
        usage >&2
        exit 2
      fi
      CONTRACT_TIMEOUT="$2"
      shift 2
      ;;
    --eval-timeout)
      if [[ $# -lt 2 ]]; then
        echo "missing value for $1" >&2
        usage >&2
        exit 2
      fi
      EVAL_TIMEOUT="$2"
      shift 2
      ;;
    --verify-timeout)
      if [[ $# -lt 2 ]]; then
        echo "missing value for $1" >&2
        usage >&2
        exit 2
      fi
      VERIFY_TIMEOUT="$2"
      shift 2
      ;;
    --consolidate-timeout)
      if [[ $# -lt 2 ]]; then
        echo "missing value for $1" >&2
        usage >&2
        exit 2
      fi
      CONSOLIDATE_TIMEOUT="$2"
      shift 2
      ;;
    --config)
      if [[ $# -lt 2 ]]; then
        echo "missing value for $1" >&2
        usage >&2
        exit 2
      fi
      CONFIG="$2"
      shift 2
      ;;
    --agent)
      if [[ $# -lt 2 ]]; then
        echo "missing value for $1" >&2
        usage >&2
        exit 2
      fi
      AGENT="$2"
      shift 2
      ;;
    --model)
      if [[ $# -lt 2 ]]; then
        echo "missing value for $1" >&2
        usage >&2
        exit 2
      fi
      MODEL="$2"
      shift 2
      ;;
    --reasoning-effort)
      if [[ $# -lt 2 ]]; then
        echo "missing value for $1" >&2
        usage >&2
        exit 2
      fi
      REASONING_EFFORT="$2"
      shift 2
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    --)
      shift
      while [[ $# -gt 0 ]]; do
        NAMES+=("$1")
        shift
      done
      ;;
    -*)
      echo "unknown option: $1" >&2
      usage >&2
      exit 2
      ;;
    *)
      NAMES+=("$1")
      shift
      ;;
  esac
done

if [[ ${#NAMES[@]} -lt 1 ]]; then
  usage >&2
  exit 2
fi

if ! [[ "$JOBS" =~ ^[0-9]+$ ]] || [[ "$JOBS" -lt 1 ]]; then
  echo "--jobs must be a positive integer: $JOBS" >&2
  exit 2
fi

if ! [[ "$CONTRACT_ROUNDS" =~ ^[0-9]+$ ]] || [[ "$CONTRACT_ROUNDS" -lt 1 ]]; then
  echo "--contract-rounds must be a positive integer: $CONTRACT_ROUNDS" >&2
  exit 2
fi

# Timeouts default to empty (defer to config). Validate only when explicitly set.
if [[ -n "$CONTRACT_TIMEOUT" ]] && { ! [[ "$CONTRACT_TIMEOUT" =~ ^[0-9]+$ ]] || [[ "$CONTRACT_TIMEOUT" -lt 1 ]]; }; then
  echo "--contract-timeout must be a positive integer: $CONTRACT_TIMEOUT" >&2
  exit 2
fi

if [[ -n "$EVAL_TIMEOUT" ]] && { ! [[ "$EVAL_TIMEOUT" =~ ^[0-9]+$ ]] || [[ "$EVAL_TIMEOUT" -lt 1 ]]; }; then
  echo "--eval-timeout must be a positive integer: $EVAL_TIMEOUT" >&2
  exit 2
fi

if [[ -n "$VERIFY_TIMEOUT" ]] && { ! [[ "$VERIFY_TIMEOUT" =~ ^[0-9]+$ ]] || [[ "$VERIFY_TIMEOUT" -lt 1 ]]; }; then
  echo "--verify-timeout must be a positive integer: $VERIFY_TIMEOUT" >&2
  exit 2
fi

if [[ -n "$CONSOLIDATE_TIMEOUT" ]] && { ! [[ "$CONSOLIDATE_TIMEOUT" =~ ^[0-9]+$ ]] || [[ "$CONSOLIDATE_TIMEOUT" -lt 1 ]]; }; then
  echo "--consolidate-timeout must be a positive integer: $CONSOLIDATE_TIMEOUT" >&2
  exit 2
fi

if [[ -n "$AGENT" && "$AGENT" != "codex" && "$AGENT" != "claude" ]]; then
  echo "--agent must be codex or claude: $AGENT" >&2
  exit 2
fi

cd "$ROOT"

RUN_ID="$(date +%Y%m%d_%H%M%S)"
RUN_DIR="$ROOT/output/pipeline_many_${RUN_ID}"
mkdir -p "$RUN_DIR"

run_one() {
  local name="$1"
  RAW_PATH="raw/${name}.md"

  if [[ ! -f "$RAW_PATH" ]]; then
    echo "[pipeline-many] missing raw file: $RAW_PATH" >&2
    return 10
  fi

  local cmd=(python3 "$PIPELINE_SCRIPT" "$RAW_PATH" --function-name "$name")
  cmd+=(--contract-rounds "$CONTRACT_ROUNDS")
  # Only pass a timeout flag when set; otherwise run_pipeline.py uses config/agents.json.
  [[ -n "$CONTRACT_TIMEOUT" ]] && cmd+=(--contract-timeout "$CONTRACT_TIMEOUT")
  [[ -n "$EVAL_TIMEOUT" ]] && cmd+=(--eval-timeout "$EVAL_TIMEOUT")
  [[ -n "$VERIFY_TIMEOUT" ]] && cmd+=(--verify-timeout "$VERIFY_TIMEOUT")
  [[ -n "$CONSOLIDATE_TIMEOUT" ]] && cmd+=(--consolidate-timeout "$CONSOLIDATE_TIMEOUT")
  [[ $SKIP_EVAL -eq 1 ]] && cmd+=(--skip-eval)
  [[ $SKIP_CONSOLIDATE -eq 1 ]] && cmd+=(--skip-consolidate)
  [[ $EXPORT_EXAMPLES -eq 0 ]] && cmd+=(--no-export)
  [[ $FORCE -eq 1 ]] && cmd+=(--force)
  [[ $DRY_RUN -eq 1 ]] && cmd+=(--dry-run)
  [[ -n "$CONFIG" ]] && cmd+=(--config "$CONFIG")
  [[ -n "$AGENT" ]] && cmd+=(--agent "$AGENT")
  [[ -n "$MODEL" ]] && cmd+=(--model "$MODEL")
  [[ -n "$REASONING_EFFORT" ]] && cmd+=(--reasoning-effort "$REASONING_EFFORT")

  echo "[pipeline-many] pipeline start name=$name"
  printf '[pipeline-many] $'
  printf ' %q' "${cmd[@]}"
  printf '\n'
  set +e
  "${cmd[@]}"
  pipeline_rc=$?
  set -e
  if [[ $pipeline_rc -ne 0 ]]; then
    echo "[pipeline-many] pipeline failed name=$name rc=$pipeline_rc" >&2
    return "$pipeline_rc"
  fi
  echo "[pipeline-many] pipeline done name=$name"
}

status_label() {
  case "$1" in
    0) echo "success" ;;
    10) echo "missing_raw" ;;
    1) echo "pipeline" ;;
    2) echo "usage" ;;
    *) echo "unknown_$1" ;;
  esac
}

FAILURES=()
SUCCESSES=()

if [[ "$JOBS" -eq 1 ]]; then
  for name in "${NAMES[@]}"; do
    if run_one "$name" 2>&1 | tee "$RUN_DIR/${name}.log"; then
      SUCCESSES+=("$name")
    else
      rc=${PIPESTATUS[0]}
      label="$(status_label "$rc")"
      FAILURES+=("$name:$label")
    fi
  done
else
  echo "[pipeline-many] running with jobs=$JOBS log_dir=$RUN_DIR"
  for name in "${NAMES[@]}"; do
    while [[ "$(jobs -rp | wc -l)" -ge "$JOBS" ]]; do
      sleep 1
    done

    log="$RUN_DIR/${name}.log"
    status_file="$RUN_DIR/${name}.status"
    (
      set +e
      run_one "$name" >"$log" 2>&1
      rc=$?
      label="$(status_label "$rc")"
      printf '%s:%s\n' "$name" "$label" >"$status_file"
      exit 0
    ) &
    echo "[pipeline-many] launched name=$name pid=$! log=$log"
  done

  wait

  for name in "${NAMES[@]}"; do
    status_file="$RUN_DIR/${name}.status"
    log="$RUN_DIR/${name}.log"
    if [[ ! -f "$status_file" ]]; then
      FAILURES+=("$name:missing_status")
      echo "[pipeline-many] failed name=$name reason=missing_status log=$log" >&2
      continue
    fi

    status="$(<"$status_file")"
    label="${status#*:}"
    if [[ "$label" == "success" ]]; then
      SUCCESSES+=("$name")
      echo "[pipeline-many] done name=$name log=$log"
    else
      FAILURES+=("$name:$label")
      echo "[pipeline-many] failed name=$name reason=$label log=$log" >&2
    fi
  done
fi

echo "[pipeline-many] summary: total=${#NAMES[@]} success=${#SUCCESSES[@]} failure=${#FAILURES[@]}"
echo "[pipeline-many] logs: $RUN_DIR"

if [[ ${#SUCCESSES[@]} -gt 0 ]]; then
  echo "[pipeline-many] successes:"
  for success in "${SUCCESSES[@]}"; do
    echo "  $success"
  done
fi

if [[ ${#FAILURES[@]} -gt 0 ]]; then
  echo "[pipeline-many] failures:" >&2
  for failure in "${FAILURES[@]}"; do
    echo "  $failure" >&2
  done
  exit 1
fi

echo "[pipeline-many] all done"

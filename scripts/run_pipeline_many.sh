#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PIPELINE_SCRIPT="$ROOT/scripts/run_pipeline.py"

RUN_EVAL=0
RUN_AUDIT=0
EXPORT_EXAMPLES=1
TIMEOUT_SECONDS=7200
MAX_OVERTURN_ROUNDS=2
JOBS=1
CONFIG=""
AGENT=""
MODEL=""
REASONING_EFFORT=""
CODEX_BIN=""
CLAUDE_BIN=""
DRY_RUN=0
SKIP_CONSOLIDATE=0

usage() {
  cat <<'EOF'
usage: run_pipeline_many.sh [--eval] [--audit] [--skip-consolidate] [--no-export-examples] [--timeout-seconds N] [--max-overturn-rounds N] [--jobs N|-j N] [--config PATH] [--agent codex|claude] [--model MODEL] [--reasoning-effort LEVEL] [--codex-bin PATH] [--claude-bin PATH] [--dry-run] <name1> [name2 ...]

For each <name>, run:
  1. python3 scripts/run_pipeline.py raw/<name>.md --function-name <name>
  2. optionally add --eval to enable the contract critic
  3. optionally add --audit to enable the verify critic

Options:
  --eval                   Run eval between contract and verify.
  --audit                  Run audit after verify.
  --skip-consolidate       Forwarded to run_pipeline.py.
  --no-export-examples     Do not pass --export-examples to verify.
  --timeout-seconds N      Total budget passed to each pipeline run. Default: 7200.
  --max-overturn-rounds N  Max critic overturn rounds per pipeline run. Default: 2.
  --jobs N, -j N           Run up to N names concurrently. Default: 1.
  --config PATH            Forwarded to run_pipeline.py.
  --agent codex|claude     Forwarded to run_pipeline.py.
  --model MODEL            Forwarded to run_pipeline.py.
  --reasoning-effort LVL   Forwarded to run_pipeline.py.
  --codex-bin PATH         Forwarded to run_pipeline.py.
  --claude-bin PATH        Forwarded to run_pipeline.py.
  --dry-run                Forwarded to run_pipeline.py.
EOF
}

NAMES=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --eval)
      RUN_EVAL=1
      shift
      ;;
    --audit)
      RUN_AUDIT=1
      shift
      ;;
    --skip-consolidate)
      SKIP_CONSOLIDATE=1
      shift
      ;;
    --no-export-examples)
      EXPORT_EXAMPLES=0
      shift
      ;;
    --timeout-seconds)
      TIMEOUT_SECONDS="$2"
      shift 2
      ;;
    --max-overturn-rounds)
      MAX_OVERTURN_ROUNDS="$2"
      shift 2
      ;;
    --jobs|-j)
      JOBS="$2"
      shift 2
      ;;
    --config)
      CONFIG="$2"
      shift 2
      ;;
    --agent)
      AGENT="$2"
      shift 2
      ;;
    --model)
      MODEL="$2"
      shift 2
      ;;
    --reasoning-effort)
      REASONING_EFFORT="$2"
      shift 2
      ;;
    --codex-bin)
      CODEX_BIN="$2"
      shift 2
      ;;
    --claude-bin)
      CLAUDE_BIN="$2"
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

if ! [[ "$TIMEOUT_SECONDS" =~ ^[0-9]+$ ]] || [[ "$TIMEOUT_SECONDS" -lt 1 ]]; then
  echo "--timeout-seconds must be a positive integer: $TIMEOUT_SECONDS" >&2
  exit 2
fi

if ! [[ "$MAX_OVERTURN_ROUNDS" =~ ^[0-9]+$ ]] || [[ "$MAX_OVERTURN_ROUNDS" -lt 0 ]]; then
  echo "--max-overturn-rounds must be a non-negative integer: $MAX_OVERTURN_ROUNDS" >&2
  exit 2
fi

if ! [[ "$JOBS" =~ ^[0-9]+$ ]] || [[ "$JOBS" -lt 1 ]]; then
  echo "--jobs must be a positive integer: $JOBS" >&2
  exit 2
fi

cd "$ROOT"

RUN_ID="$(date +%Y%m%d_%H%M%S)"
TMP_ROOT="${TMPDIR:-/tmp}"
BATCH_TMP="$(mktemp -d "$TMP_ROOT/cav-java-pipeline-many_${RUN_ID}.XXXXXX")"
trap 'rm -rf "$BATCH_TMP"' EXIT

run_one() {
  local name="$1"
  local raw_path="raw/${name}.md"
  local cmd=(python3 "$PIPELINE_SCRIPT" "$raw_path" --function-name "$name" --total-budget-seconds "$TIMEOUT_SECONDS" --max-overturn-rounds "$MAX_OVERTURN_ROUNDS")

  if [[ ! -f "$raw_path" ]]; then
    echo "[pipeline-many] missing raw file: $raw_path" >&2
    return 10
  fi

  if [[ "$RUN_EVAL" -eq 1 ]]; then
    cmd+=(--eval)
  fi
  if [[ "$RUN_AUDIT" -eq 1 ]]; then
    cmd+=(--audit)
  fi
  if [[ "$EXPORT_EXAMPLES" -eq 1 ]]; then
    cmd+=(--export-examples)
  fi
  if [[ -n "$CONFIG" ]]; then
    cmd+=(--config "$CONFIG")
  fi
  if [[ -n "$AGENT" ]]; then
    cmd+=(--agent "$AGENT")
  fi
  if [[ -n "$MODEL" ]]; then
    cmd+=(--model "$MODEL")
  fi
  if [[ -n "$REASONING_EFFORT" ]]; then
    cmd+=(--reasoning-effort "$REASONING_EFFORT")
  fi
  if [[ -n "$CODEX_BIN" ]]; then
    cmd+=(--codex-bin "$CODEX_BIN")
  fi
  if [[ -n "$CLAUDE_BIN" ]]; then
    cmd+=(--claude-bin "$CLAUDE_BIN")
  fi
  if [[ "$DRY_RUN" -eq 1 ]]; then
    cmd+=(--dry-run)
  fi
  if [[ "$SKIP_CONSOLIDATE" -eq 1 ]]; then
    cmd+=(--skip-consolidate)
  fi

  echo "[pipeline-many] start name=$name eval=$RUN_EVAL audit=$RUN_AUDIT export=$EXPORT_EXAMPLES skip_consolidate=$SKIP_CONSOLIDATE"
  if ! "${cmd[@]}"; then
    echo "[pipeline-many] failed name=$name" >&2
    return 20
  fi
  echo "[pipeline-many] done name=$name"
}

status_label() {
  case "$1" in
    0) echo "success" ;;
    10) echo "missing_raw" ;;
    20) echo "pipeline" ;;
    *) echo "unknown_$1" ;;
  esac
}

FAILURES=()
SUCCESSES=()

if [[ "$JOBS" -eq 1 ]]; then
  for name in "${NAMES[@]}"; do
    if run_one "$name"; then
      SUCCESSES+=("$name")
    else
      rc=$?
      label="$(status_label "$rc")"
      FAILURES+=("$name:$label")
    fi
  done
else
  echo "[pipeline-many] running with jobs=$JOBS"
  for name in "${NAMES[@]}"; do
    while [[ "$(jobs -rp | wc -l)" -ge "$JOBS" ]]; do
      sleep 1
    done

    log="$BATCH_TMP/${name}.log"
    status_file="$BATCH_TMP/${name}.status"
    (
      set +e
      run_one "$name" >"$log" 2>&1
      rc=$?
      label="$(status_label "$rc")"
      printf '%s:%s\n' "$name" "$label" >"$status_file"
      exit 0
    ) &
    echo "[pipeline-many] launched name=$name pid=$!"
  done

  wait

  for name in "${NAMES[@]}"; do
    status_file="$BATCH_TMP/${name}.status"
    log="$BATCH_TMP/${name}.log"
    if [[ -f "$log" ]]; then
      sed "s/^/[pipeline-many][$name] /" "$log"
    fi

    if [[ ! -f "$status_file" ]]; then
      FAILURES+=("$name:missing_status")
      echo "[pipeline-many] failed name=$name reason=missing_status" >&2
      continue
    fi

    status="$(<"$status_file")"
    label="${status#*:}"
    if [[ "$label" == "success" ]]; then
      SUCCESSES+=("$name")
      echo "[pipeline-many] done name=$name"
    else
      FAILURES+=("$name:$label")
      echo "[pipeline-many] failed name=$name reason=$label" >&2
    fi
  done
fi

echo "[pipeline-many] summary: total=${#NAMES[@]} success=${#SUCCESSES[@]} failure=${#FAILURES[@]} eval=$RUN_EVAL audit=$RUN_AUDIT export=$EXPORT_EXAMPLES"

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

#!/usr/bin/env bash
# Parallel batch verify (input -> verify entry) with configurable agent/model.
#
# Usage:
#   scripts/verify_batch.sh                                  # all of input/humaneval, jobs=4
#   scripts/verify_batch.sh --dataset humaneval --jobs 4
#   scripts/verify_batch.sh --dataset algo --jobs 8 below_zero_3 is_prime_31
#   scripts/verify_batch.sh --timeout 2400                  # override per-task budget (default 3600s)
#   scripts/verify_batch.sh --agent claude --model sonnet
#
# Each problem runs:
#   run_verify.py input/<dataset>/<name>.c --function-name <name> --workspace-name <name>
#       --agent <agent> --model <model> --reasoning-effort medium
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

DATASET="humaneval"
JOBS=4
MODEL="gpt-5.4"
AGENT="codex"
EFFORT="medium"
TIMEOUT=3600
NAMES=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --dataset) DATASET="$2"; shift 2 ;;
    --jobs|-j) JOBS="$2"; shift 2 ;;
    --agent) AGENT="$2"; shift 2 ;;
    --model) MODEL="$2"; shift 2 ;;
    --reasoning-effort) EFFORT="$2"; shift 2 ;;
    --timeout) TIMEOUT="$2"; shift 2 ;;
    -h|--help) sed -n '2,15p' "$0"; exit 0 ;;
    *) NAMES+=("$1"); shift ;;
  esac
done

[[ -d "input/$DATASET" ]] || { echo "no such dataset: input/$DATASET" >&2; exit 2; }

# default: every problem in input/<dataset>/
if [[ ${#NAMES[@]} -eq 0 ]]; then
  mapfile -t NAMES < <(find "input/$DATASET" -maxdepth 1 -type f -name '*.c' -printf '%f\n' | sed 's/\.c$//' | sort)
fi
[[ ${#NAMES[@]} -gt 0 ]] || { echo "no problems to verify" >&2; exit 2; }

RUNID="$(date +%Y%m%d_%H%M%S)"
RUNDIR="output/verify_batch_${RUNID}"
mkdir -p "$RUNDIR"
echo "verify batch [$DATASET]  agent=$AGENT model=$MODEL effort=$EFFORT jobs=$JOBS  count=${#NAMES[@]}  logs=$RUNDIR"

run_one() {
  local name="$1"
  local c="input/$DATASET/$name.c"
  [[ -f "$c" ]] || { echo "MISS $name (no $c)"; return 0; }
  python3 scripts/run_verify.py "$c" \
    --function-name "$name" --workspace-name "$name" \
    --agent "$AGENT" --model "$MODEL" --reasoning-effort "$EFFORT" \
    --timeout-seconds "$TIMEOUT" \
    > "$RUNDIR/$name.log" 2>&1
  local rc=$?
  echo "[rc=$rc] $name"
}
export -f run_one
export DATASET AGENT MODEL EFFORT TIMEOUT RUNDIR

printf '%s\n' "${NAMES[@]}" | xargs -P "$JOBS" -I{} bash -c 'run_one "$@"' _ {}

# ---- summary ----
echo ""
echo "==== summary (genuine Final Result per latest workspace) ===="
ok=0; fail=0; other=0
# single pass over output/: map each problem name -> its newest verify workspace
declare -A WS
while read -r d; do
  nm=$(basename "$d" | sed -E 's/^verify_[0-9]{8}_[0-9]{6}[a-z0-9]*_//')
  [[ -n "${WS[$nm]:-}" ]] || WS[$nm]="$d/"   # ls -dt is newest-first; keep first seen
done < <(ls -dt output/verify_*/ 2>/dev/null)
for name in "${NAMES[@]}"; do
  d="${WS[$name]:-}"
  res=""
  [[ -n "$d" ]] && res=$(grep -E "^Final Result:" "${d}logs/metrics.md" 2>/dev/null | tail -1 | sed 's/Final Result: //')
  case "$res" in
    Success) ok=$((ok+1));   printf "  ✅ %s\n" "$name" ;;
    Fail)    fail=$((fail+1));printf "  ✗  %s\n" "$name" ;;
    *)       other=$((other+1)); printf "  ?  %s (%s)\n" "$name" "${res:-no-result}" ;;
  esac
done
echo "Success=$ok  Fail=$fail  Other=$other  (of ${#NAMES[@]})"

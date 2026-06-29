#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
ARK_PROFILE_CONFIG="${ARK_PROFILE_CONFIG:-$ROOT/config/ark_api/profiles.json}"

if [[ -n "${ARK_PROFILE:-}" ]]; then
  eval "$("$ROOT/scripts/ark_profile_env.py" --config "$ARK_PROFILE_CONFIG" "$ARK_PROFILE")"
fi

if [[ -z "${ANTHROPIC_AUTH_TOKEN:-}" && -n "${ARK_API_KEY:-}" ]]; then
  export ANTHROPIC_AUTH_TOKEN="$ARK_API_KEY"
fi

if [[ -z "${ANTHROPIC_API_KEY:-}" && -n "${ARK_API_KEY:-}" ]]; then
  export ANTHROPIC_API_KEY="$ARK_API_KEY"
fi

if [[ -z "${ANTHROPIC_BASE_URL:-}" || -z "${ANTHROPIC_API_KEY:-}" ]]; then
  echo "claude_ark_wrapper requires ARK_PROFILE or ANTHROPIC_BASE_URL plus ANTHROPIC_API_KEY" >&2
  exit 2
fi

if [[ -z "${ANTHROPIC_MODEL:-}" && -n "${ARK_MODEL:-}" ]]; then
  export ANTHROPIC_MODEL="$ARK_MODEL"
fi
export CLAUDE_CODE_DISABLE_NONESSENTIAL_TRAFFIC="${CLAUDE_CODE_DISABLE_NONESSENTIAL_TRAFFIC:-1}"

exec claude "$@"

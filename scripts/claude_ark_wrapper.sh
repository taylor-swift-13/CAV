#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
ARK_CONFIG="$ROOT/config/ark_api/ark.config.toml"

if [[ -z "${ARK_API_KEY:-}" && -f "$ARK_CONFIG" ]]; then
  ARK_API_KEY="$(
    sed -n 's/^api_key[[:space:]]*=[[:space:]]*"\(.*\)"[[:space:]]*$/\1/p' "$ARK_CONFIG" | head -n 1
  )"
  export ARK_API_KEY
fi

if [[ -z "${ANTHROPIC_AUTH_TOKEN:-}" && -n "${ARK_API_KEY:-}" ]]; then
  export ANTHROPIC_AUTH_TOKEN="$ARK_API_KEY"
fi

if [[ -z "${ANTHROPIC_API_KEY:-}" && -n "${ARK_API_KEY:-}" ]]; then
  export ANTHROPIC_API_KEY="$ARK_API_KEY"
fi

export ANTHROPIC_BASE_URL="${ANTHROPIC_BASE_URL:-https://ark.cn-beijing.volces.com/api/coding}"
export ANTHROPIC_MODEL="${ANTHROPIC_MODEL:-ark-code-latest}"
export CLAUDE_CODE_DISABLE_NONESSENTIAL_TRAFFIC="${CLAUDE_CODE_DISABLE_NONESSENTIAL_TRAFFIC:-1}"

exec claude "$@"

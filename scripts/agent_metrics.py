#!/usr/bin/env python3
"""Shared time/token accounting for stage runners.

Every stage runner records the same two things
in its workspace ``logs/metrics.md``:

  * wall-clock time — measured by the runner around the whole stage;
  * token usage — read from the agent CLI's own structured output.

This module owns the token side so the four runners stop carrying divergent
copies. It provides:

  * ``parse_usage(agent, path)`` — agent-aware usage extraction. ``codex`` keeps
    the last ``turn.completed.usage`` in the JSONL stream; ``claude`` reads the
    top-level ``usage`` of the single JSON object. (The old per-runner
    ``parse_usage`` was codex-only, so claude solver runs silently fell back to
    word-count approximation.)
  * ``add_usage(acc, new)`` — sum usage across rounds. Some solver stages run
    multiple rounds; each round is a fresh agent session, so summing the
    per-round totals gives the stage total.
  * ``usage_lines(...)`` — render the unified key set (or the approx fallback)
    as ``metrics.md`` lines, with a single ``Agent CLI`` prefix.
"""
from __future__ import annotations

import json
from pathlib import Path


# Canonical order for token fields. codex emits ``cached_input_tokens``; claude
# emits ``cache_creation_input_tokens`` / ``cache_read_input_tokens``. We render
# whichever are present, always in this order, then any extra int fields.
UNIFIED_USAGE_KEYS = (
    "input_tokens",
    "cached_input_tokens",
    "output_tokens",
    "cache_creation_input_tokens",
    "cache_read_input_tokens",
)


def token_count(path: Path | None) -> int:
    """Whitespace word count — the approximate-token fallback when no CLI usage."""
    if path is None or not path.exists():
        return 0
    return len(path.read_text(encoding="utf-8", errors="replace").split())


def parse_codex_usage(stdout_jsonl: Path | None) -> dict[str, int] | None:
    """Last ``turn.completed.usage`` object in a codex ``exec --json`` stream."""
    if stdout_jsonl is None or not stdout_jsonl.exists():
        return None
    usage = None
    for raw in stdout_jsonl.read_text(encoding="utf-8", errors="replace").splitlines():
        if not raw.strip().startswith("{"):
            continue
        try:
            obj = json.loads(raw)
        except json.JSONDecodeError:
            continue
        if obj.get("type") == "turn.completed" and isinstance(obj.get("usage"), dict):
            usage = obj["usage"]
    if usage is None:
        return None
    return {k: v for k, v in usage.items() if isinstance(v, int)}


def parse_claude_usage(stdout_path: Path | None) -> dict[str, int] | None:
    """Token usage from a claude ``--print`` result.

    Handles both output formats:

      * ``--output-format json`` — one object with a top-level ``usage``;
      * ``--output-format stream-json`` — a JSONL event stream whose final
        ``{"type": "result", ...}`` event carries the cumulative ``usage``.
    """
    if stdout_path is None or not stdout_path.exists():
        return None
    text = stdout_path.read_text(encoding="utf-8", errors="replace").strip()
    if not text:
        return None
    # --output-format json: the whole file is one object.
    try:
        obj = json.loads(text)
    except json.JSONDecodeError:
        obj = None
    if isinstance(obj, dict):
        usage = obj.get("usage")
        if isinstance(usage, dict):
            return {k: v for k, v in usage.items() if isinstance(v, int)}
        return None
    # --output-format stream-json: scan for the last `result` event's usage.
    usage = None
    for raw in text.splitlines():
        raw = raw.strip()
        if not raw.startswith("{"):
            continue
        try:
            ev = json.loads(raw)
        except json.JSONDecodeError:
            continue
        if isinstance(ev, dict) and ev.get("type") == "result" and isinstance(ev.get("usage"), dict):
            usage = ev["usage"]
    if usage is None:
        return None
    return {k: v for k, v in usage.items() if isinstance(v, int)}


def extract_claude_last_message(stdout_path: Path | None) -> str | None:
    """Final assistant text from a claude ``--print`` result file.

    For ``--output-format json`` it is the object's ``result``; for
    ``--output-format stream-json`` it is the ``result`` event's ``result``.
    Returns None when no result text is present (caller falls back to raw stdout).
    """
    if stdout_path is None or not stdout_path.exists():
        return None
    text = stdout_path.read_text(encoding="utf-8", errors="replace").strip()
    if not text:
        return None
    try:
        obj = json.loads(text)
    except json.JSONDecodeError:
        obj = None
    if isinstance(obj, dict):
        result = obj.get("result")
        return result if isinstance(result, str) else None
    last = None
    for raw in text.splitlines():
        raw = raw.strip()
        if not raw.startswith("{"):
            continue
        try:
            ev = json.loads(raw)
        except json.JSONDecodeError:
            continue
        if isinstance(ev, dict) and ev.get("type") == "result" and isinstance(ev.get("result"), str):
            last = ev["result"]
    return last


def parse_usage(agent: str, stdout_path: Path | None) -> dict[str, int] | None:
    """Dispatch usage parsing by agent backend."""
    if agent == "claude":
        return parse_claude_usage(stdout_path)
    return parse_codex_usage(stdout_path)


def add_usage(acc: dict[str, int] | None, new: dict[str, int] | None) -> dict[str, int] | None:
    """Sum two usage dicts field-by-field. None-safe; returns None iff both None."""
    if not acc and not new:
        return None
    out: dict[str, int] = dict(acc) if acc else {}
    for key, value in (new or {}).items():
        if isinstance(value, int):
            out[key] = out.get(key, 0) + value
    return out


def usage_lines(
    usage: dict[str, int] | None,
    *,
    prefix: str = "Agent CLI",
    prompt_path: Path | None = None,
    last_message_path: Path | None = None,
) -> list[str]:
    """metrics.md lines for token usage, or the approx fallback when unavailable."""
    if usage:
        ordered = [k for k in UNIFIED_USAGE_KEYS if k in usage]
        extras = sorted(k for k in usage if k not in UNIFIED_USAGE_KEYS)
        return [f"- {prefix} {key}: `{usage[key]}`" for key in (*ordered, *extras)]
    lines = []
    if prompt_path is not None:
        lines.append(f"- Approx prompt tokens: `{token_count(prompt_path)}`")
    if last_message_path is not None:
        lines.append(f"- Approx last-message tokens: `{token_count(last_message_path)}`")
    return lines

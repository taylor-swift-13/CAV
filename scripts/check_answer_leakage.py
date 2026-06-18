#!/usr/bin/env python3
"""Standalone transcript audit for answer/workspace leakage.

This check is intentionally separate from ``check_verify_audit.py`` because
reading prior answers or unrelated workspaces is a process-compliance issue; it
does not by itself prove that the final Coq artifact is invalid.
"""
from __future__ import annotations

import check_agent_transcript_cheating


if __name__ == "__main__":
    raise SystemExit(check_agent_transcript_cheating.main())

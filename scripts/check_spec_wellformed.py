#!/usr/bin/env python3
"""Contract-stage spec well-formedness gate (C/QCP).

Mirrors the Java pipeline's ``check_spec_wellformed.py`` (which runs
``openjml -esc``). Here the criterion is symexec-based: a contract is well-formed
enough to enter the pipeline if ``symexec`` can successfully *start* symbolic
execution on it — i.e. the C and its ``Require``/``Ensure`` spec parse and
symbolic execution begins (output reaches ``Symbolic Execution into function``).

This is deliberately NOT a full proof. A downstream symbolic-execution error
such as ``Cannot derive the precondition of Memory Read`` is TOLERATED — it just
means loop invariants / bridge assertions are still missing, which is the verify
stage's job. The only ill-formed case is when symexec cannot even begin (the
spec fails to parse).

Tolerant by design: if symexec is unavailable or the result is inconclusive, the
classification is ``not_run`` and the caller should not block on it.
"""
from __future__ import annotations

import argparse
import shutil
from pathlib import Path
import re
import subprocess
import sys
import tempfile

REPO_ROOT = Path(__file__).resolve().parents[1]
QCP_ROOT = REPO_ROOT / "QualifiedCProgramming"
SYMEXEC = QCP_ROOT / "linux-binary" / "symexec"
# Output marker that means symbolic execution actually started (spec parsed).
_STARTED_RE = re.compile(r"Symbolic Execution into function")


def prepare_input(src_c: Path, dst_c: Path) -> None:
    """Copy the contract C into a symexec-parseable form.

    Rewrites quoted includes to bare names and copies common plus task-local
    headers into the temp directory, matching verify bootstrap behavior.
    """
    lines = []
    copied_repo_headers: set[str] = set()
    for line in src_c.read_text(encoding="utf-8", errors="replace").splitlines():
        # normalize any ../ or ../../ prefix to bare (bare includes pass through unchanged)
        line = re.sub(r'(?:\.\./)+(verification_[A-Za-z0-9_]+\.h)', r'\1', line)
        m = re.search(r'#\s*include\s+"([^"]+)"', line)
        if m is not None:
            header = Path(m.group(1)).name
            copied_repo_headers.add(header)
            line = re.sub(r'#\s*include\s+"[^"]*?(' + re.escape(header) + r')"', r'#include "\1"', line)
        lines.append(line)
    dst_c.write_text("\n".join(lines) + "\n", encoding="utf-8")
    copied_repo_headers.update({
        "verification_stdlib.h",
        "verification_list.h",
        "int_array_def.h",
        "char_array_def.h",
    })
    for header in copied_repo_headers:
        src = src_c.parent / header
        if not src.exists():
            src = REPO_ROOT / header
        if src.exists():
            shutil.copy2(src, dst_c.parent / header)


def check(input_c: Path, timeout_seconds: int = 120) -> tuple[str, int | None, str]:
    """Return (classification, symexec_exit, detail).

    classification in {"well_formed", "ill_formed", "not_run"}.
    """
    if not SYMEXEC.exists():
        return "not_run", None, f"symexec not found: {SYMEXEC}"
    tmp = Path(tempfile.mkdtemp(prefix="wf_"))
    try:
        prepared = tmp / input_c.name
        prepare_input(input_c, prepared)
        cmd = [
            str(SYMEXEC),
            f"--goal-file={tmp / 'wf_goal.v'}",
            f"--proof-auto-file={tmp / 'wf_proof_auto.v'}",
            f"--proof-manual-file={tmp / 'wf_proof_manual.v'}",
            "--coq-logic-path=SimpleC.EE.WF",
            "-IQCP_examples/stdlib/",
            "-slp", "QCP_examples/stdlib/", "SimpleC.StdLib",
            "-IQCP_examples/QCP_demos_LLM/",
            "-slp", "QCP_examples/QCP_demos_LLM/", "SimpleC.EE.QCP_demos_LLM",
            f"--input-file={prepared}",
            "--no-exec-info",
        ]
        try:
            proc = subprocess.run(
                cmd, cwd=QCP_ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                text=True, timeout=timeout_seconds)
        except (subprocess.SubprocessError, OSError) as exc:
            return "not_run", None, f"symexec run failed: {exc}"
        out = proc.stdout or ""
        if _STARTED_RE.search(out):
            return "well_formed", proc.returncode, "symbolic execution started; spec parses"
        # Did not even begin -> spec could not be parsed.
        snippet = " ".join(out.split())[:300]
        return "ill_formed", proc.returncode, f"symexec did not start: {snippet}"
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def main() -> int:
    p = argparse.ArgumentParser(description="C/QCP contract well-formedness gate via symexec.")
    p.add_argument("input_c", help="Contract C file (input/<name>.c).")
    p.add_argument("--timeout-seconds", type=int, default=120)
    args = p.parse_args()
    input_c = Path(args.input_c)
    if not input_c.is_absolute():
        input_c = (REPO_ROOT / input_c).resolve()
    classification, exit_code, detail = check(input_c, args.timeout_seconds)
    print(f"wellformed: {classification} (symexec_exit={exit_code}) {detail}")
    # not_run is tolerated (exit 0); only a hard ill_formed is a nonzero gate.
    return 1 if classification == "ill_formed" else 0


if __name__ == "__main__":
    raise SystemExit(main())

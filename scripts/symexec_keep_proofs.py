#!/usr/bin/env python3
"""Re-run symexec WITHOUT throwing away already-proven witnesses.

Plain `symexec` deletes and regenerates proof_manual.v with every witness back
to `Admitted` — so a retry that re-runs symexec wipes all the work already done.
This wrapper preserves it:

  1. snapshot the current proof_manual.v: keep each proven (`Qed.`/`Defined.`)
     `proof_of_<func>_<wit>` block, plus any agent-added helper lemmas; record
     each witness's VC body from goal.v.
  2. run the real symexec (canonical command from SYMEXEC/README §1).
  3. for each freshly-generated witness whose VC body in the NEW goal.v is
     byte-identical to the OLD one, splice the old proof back in (PROOF §24:
     only reuse when the VC body is unchanged); re-insert helper lemmas.
  4. witnesses whose VC changed, or that were never proven, stay `Admitted`.

On symexec failure the original generated files are restored, so the workspace
is never left worse than before.

Usage (drop-in for the SYMEXEC §1 command):
  python3 scripts/symexec_keep_proofs.py --name <NAME> --stamp <STAMP>
"""
import argparse, re, shutil, subprocess, sys, tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
SYMEXEC_BIN = REPO_ROOT / "QualifiedCProgramming" / "linux-binary" / "symexec"
GEN_SUFFIXES = ("goal", "proof_auto", "proof_manual", "goal_check", "proof_check")

ITEM_BOUNDARY = re.compile(r"(?m)^(?=(?:Lemma|Theorem|Corollary|Definition|Fixpoint)\s)")
NAME_RE = re.compile(r"^(?:Lemma|Theorem|Corollary|Definition|Fixpoint)\s+([A-Za-z_][\w']*)")
DEF_BOUNDARY = re.compile(r"(?m)^(?=Definition\s)")


def _norm(s: str) -> str:
    return re.sub(r"\s+", " ", s).strip()


def split_items(text: str):
    """Return (header, [item_text, ...]) split on top-level decl boundaries."""
    parts = ITEM_BOUNDARY.split(text)
    return parts[0], parts[1:]


def item_name(item: str):
    m = NAME_RE.match(item)
    return m.group(1) if m else None


def goal_defs(text: str) -> dict[str, str]:
    """name -> full Definition chunk text (the VC body)."""
    out = {}
    for chunk in DEF_BOUNDARY.split(text):
        m = re.match(r"Definition\s+([A-Za-z_][\w']*)", chunk)
        if m:
            out[m.group(1)] = chunk
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--name", required=True)
    ap.add_argument("--stamp", required=True, help="e.g. 20260605_134551v (matches workspace/annotated)")
    ap.add_argument("--symexec-timeout", type=int, default=300)
    args = ap.parse_args()

    name, stamp = args.name, args.stamp
    ws = REPO_ROOT / "output" / f"verify_{stamp}_{name}"
    gen = ws / "coq" / "generated"
    annotated = REPO_ROOT / "annotated" / f"verify_{stamp}_{name}.c"
    logic_path = f"SimpleC.EE.CAV.verify_{stamp}_{name}"
    gen.mkdir(parents=True, exist_ok=True)

    pm = gen / f"{name}_proof_manual.v"
    old_goal = gen / f"{name}_goal.v"

    # ---- 1. snapshot old proofs + helpers + old VC bodies ----
    old_proven: dict[str, str] = {}
    old_helpers: list[str] = []
    old_goal_defs: dict[str, str] = {}
    if pm.exists() and old_goal.exists():
        _, items = split_items(pm.read_text(encoding="utf-8", errors="replace"))
        for it in items:
            nm = item_name(it)
            if not nm:
                continue
            proven = bool(re.search(r"\b(Qed|Defined)\s*\.", it)) and not re.search(r"\bAdmitted\s*\.", it)
            if nm.startswith("proof_of_"):
                if proven:
                    old_proven[nm] = it
            elif proven:  # agent-added helper lemma/def
                old_helpers.append(it)
        old_goal_defs = goal_defs(old_goal.read_text(encoding="utf-8", errors="replace"))

    # ---- back up current generated files, then clean (SYMEXEC §3) ----
    backup = Path(tempfile.mkdtemp(prefix="symexec_keep_"))
    for suf in GEN_SUFFIXES:
        f = gen / f"{name}_{suf}.v"
        if f.exists():
            shutil.copy2(f, backup / f.name)
            f.unlink()

    # ---- 2. run real symexec ----
    cmd = [
        str(SYMEXEC_BIN),
        f"--goal-file={gen / f'{name}_goal.v'}",
        f"--proof-auto-file={gen / f'{name}_proof_auto.v'}",
        f"--proof-manual-file={gen / f'{name}_proof_manual.v'}",
        f"--coq-logic-path={logic_path}",
        "-slp", str(REPO_ROOT / "annotated") + "/", "SimpleC.EE.CAV",
        f"--input-file={annotated}",
        "--no-exec-info",
    ]
    proc = subprocess.run(cmd, cwd=REPO_ROOT / "QualifiedCProgramming",
                          text=True, capture_output=True, timeout=args.symexec_timeout)
    sys.stdout.write(proc.stdout)
    sys.stderr.write(proc.stderr)
    if proc.returncode != 0 or not pm.exists():
        # restore so we never leave the workspace worse than before
        for f in backup.glob("*.v"):
            shutil.copy2(f, gen / f.name)
        print(f"[keep-proofs] symexec failed (exit {proc.returncode}); restored previous generated files", file=sys.stderr)
        shutil.rmtree(backup, ignore_errors=True)
        return proc.returncode or 1

    # ---- 3. splice preserved proofs into the fresh proof_manual ----
    new_goal_defs = goal_defs((gen / f"{name}_goal.v").read_text(encoding="utf-8", errors="replace"))
    header, new_items = split_items(pm.read_text(encoding="utf-8", errors="replace"))
    out = [header]
    helpers_done = not old_helpers
    preserved = changed = admitted = 0
    for it in new_items:
        nm = item_name(it)
        if nm and nm.startswith("proof_of_") and not helpers_done:
            out.extend(old_helpers)          # helpers before first witness
            helpers_done = True
        if nm and nm.startswith("proof_of_"):
            defname = nm[len("proof_of_"):]
            if (nm in old_proven and defname in old_goal_defs and defname in new_goal_defs
                    and _norm(old_goal_defs[defname]) == _norm(new_goal_defs[defname])):
                out.append(old_proven[nm]); preserved += 1; continue
            if nm in old_proven:
                changed += 1                  # had a proof but VC changed -> drop, stays Admitted
            admitted += 1
        out.append(it)
    pm.write_text("".join(out), encoding="utf-8")
    shutil.rmtree(backup, ignore_errors=True)

    print(f"[keep-proofs] preserved={preserved} helpers={len(old_helpers)} "
          f"still_admitted={admitted} dropped_vc_changed={changed}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())

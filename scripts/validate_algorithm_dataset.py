#!/usr/bin/env python3
"""Compile-check code blocks in datasets/internal."""

from __future__ import annotations

import argparse
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_DATASET = REPO_ROOT / "datasets" / "internal"


def code_block(path: Path, lang: str) -> str:
    text = path.read_text(encoding="utf-8")
    match = re.search(rf"```{lang}\n(.*?)```", text, re.S)
    if not match:
        raise ValueError(f"missing {lang} block: {path}")
    return match.group(1).strip() + "\n"


def run(cmd: list[str]) -> None:
    subprocess.run(cmd, cwd=REPO_ROOT, check=True)


def validate_text_alignment(dataset: Path) -> None:
    names = sorted(p.name for p in (dataset / "c").glob("*.md"))
    for name in names:
        pieces = []
        for lang in ("c", "java", "rust"):
            path = dataset / lang / name
            text = path.read_text(encoding="utf-8")
            match = re.search(rf"```{lang}\n.*?```", text, re.S)
            if not match:
                raise ValueError(f"missing {lang} block: {path}")
            pieces.append((text[: match.start()], text[match.end() :]))
        if not (pieces[0] == pieces[1] == pieces[2]):
            raise ValueError(f"problem text differs across languages: {name}")
    print(f"text alignment: ok ({len(names)} problems)")


def validate_c(dataset: Path) -> None:
    with tempfile.TemporaryDirectory() as td:
        out = Path(td)
        files = []
        for path in (dataset / "c").glob("*.md"):
            target = out / f"{path.stem}.c"
            target.write_text(code_block(path, "c"), encoding="utf-8")
            files.append(target)
        for file in files:
            run(["gcc", "-std=c11", "-Wall", "-Wextra", "-Werror", "-Wno-unused-parameter", "-c", str(file), "-o", "/dev/null"])
    print(f"c compile: ok ({len(files)} files)")


def validate_java(dataset: Path, release: str) -> None:
    with tempfile.TemporaryDirectory() as td:
        out = Path(td)
        files = []
        for path in (dataset / "java").glob("*.md"):
            code = code_block(path, "java")
            match = re.search(r"class\s+([A-Za-z_]\w*)", code)
            if not match:
                raise ValueError(f"missing Java class: {path}")
            target = out / f"{match.group(1)}.java"
            target.write_text(code, encoding="utf-8")
            files.append(target)
        run(["javac", "--release", release, *[str(f) for f in files]])
    print(f"java compile: ok ({len(files)} files)")


def validate_rust(dataset: Path, require: bool, edition: str) -> None:
    rustc = shutil.which("rustc")
    if not rustc:
        candidate = Path.home() / ".cargo" / "bin" / "rustc"
        if candidate.exists():
            rustc = str(candidate)
    if not rustc:
        message = "rust compile: skipped (rustc not found)"
        if require:
            raise RuntimeError(message)
        print(message)
        return
    with tempfile.TemporaryDirectory() as td:
        out = Path(td)
        files = []
        for path in (dataset / "rust").glob("*.md"):
            target = out / f"{path.stem}.rs"
            target.write_text(code_block(path, "rust"), encoding="utf-8")
            files.append(target)
        for file in files:
            run([rustc, "--edition", edition, "--crate-type", "lib", str(file), "-o", str(file.with_suffix(".rlib"))])
    print(f"rust compile: ok ({len(files)} files)")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dataset", default=str(DEFAULT_DATASET), help="Dataset root with c/java/rust subdirectories.")
    parser.add_argument("--java-release", default="8", help="javac --release value.")
    parser.add_argument("--rust-edition", default="2021", help="rustc --edition value.")
    parser.add_argument("--require-rust", action="store_true", help="Fail if rustc is unavailable.")
    args = parser.parse_args()
    dataset = Path(args.dataset)
    if not dataset.is_absolute():
        dataset = (REPO_ROOT / dataset).resolve()
    validate_text_alignment(dataset)
    validate_c(dataset)
    validate_java(dataset, args.java_release)
    validate_rust(dataset, args.require_rust, args.rust_edition)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(f"validation failed: {exc}", file=sys.stderr)
        raise SystemExit(1)

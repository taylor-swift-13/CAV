#!/usr/bin/env python3
"""Build a parallel C/Java/Rust dataset from Exercism practice exercises.

Sources are expected under .tools/exercism_sources, created with shallow clones
of exercism/problem-specifications, exercism/c, exercism/java, and exercism/rust.
"""

from __future__ import annotations

import json
import shutil
import subprocess
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SRC_ROOT = REPO_ROOT / ".tools" / "exercism_sources"
OUT_ROOT = REPO_ROOT / "datasets" / "exercism_algorithms"
TRACKS = ("c", "java", "rust")


def git_head(path: Path) -> str:
    return subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"], text=True).strip()


def read(path: Path) -> str:
    return path.read_text(encoding="utf-8").strip()


def sanitize_instructions(text: str) -> str:
    # Keep examples in the statement, but remove track-specific fence labels so
    # the only c/java/rust code block in each generated file is the final answer.
    return "\n".join("```text" if line.startswith("```") and line.strip() != "```" else line for line in text.splitlines())


def reference_java(exercise: Path) -> Path | None:
    ref_dir = exercise / ".meta" / "src" / "reference" / "java"
    if not ref_dir.exists():
        return None
    files = sorted(ref_dir.glob("*.java"))
    return files[0] if len(files) == 1 else None


def rust_has_external_dependencies(exercise: Path) -> bool:
    cargo = exercise / "Cargo.toml"
    if not cargo.exists():
        return False
    in_dependencies = False
    for raw in cargo.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if line.startswith("["):
            in_dependencies = line == "[dependencies]"
            continue
        if in_dependencies and line and not line.startswith("#"):
            return True
    return False


def exercise_title(slug: str) -> str:
    return " ".join(part.capitalize() for part in slug.split("-"))


def md(slug: str, instructions: str, lang: str, code: str, source: str) -> str:
    code = code.replace("```", "~~~")
    return (
        f"# {exercise_title(slug)}\n\n"
        "## 来源\n\n"
        f"- Source: {source}\n"
        "- License: MIT License, Exercism\n\n"
        "## 问题描述\n\n"
        f"{instructions.strip()}\n\n"
        "## 参考实现\n\n"
        f"```{lang}\n{code.rstrip()}\n```\n"
    )


def c_code(exercise: Path) -> str:
    pieces = []
    header = exercise / ".meta" / "example.h"
    if header.exists():
        pieces.append(read(header))
    for header in sorted(exercise.glob("*.h")):
        pieces.append(read(header))
    source = read(exercise / ".meta" / "example.c")
    source = "\n".join(line for line in source.splitlines() if not (line.strip().startswith('#include "') and line.strip().endswith('.h"')))
    pieces.append(source)
    return "\n\n".join(pieces)


def main() -> int:
    roots = {track: SRC_ROOT / track / "exercises" / "practice" for track in TRACKS}
    for track, root in roots.items():
        if not root.exists():
            raise FileNotFoundError(f"missing Exercism source: {root}")

    common = sorted(set.intersection(*[{p.name for p in root.iterdir() if p.is_dir()} for root in roots.values()]))
    selected: list[str] = []
    for slug in common:
        c_ex = roots["c"] / slug
        java_ex = roots["java"] / slug
        rust_ex = roots["rust"] / slug
        if not (c_ex / ".meta" / "example.c").exists():
            continue
        if reference_java(java_ex) is None:
            continue
        if not (rust_ex / ".meta" / "example.rs").exists():
            continue
        rust_example = read(rust_ex / ".meta" / "example.rs")
        if "use regex_lite::" in rust_example:
            continue
        if rust_has_external_dependencies(rust_ex):
            continue
        if not (rust_ex / ".docs" / "instructions.md").exists():
            continue
        selected.append(slug)

    shutil.rmtree(OUT_ROOT, ignore_errors=True)
    for track in TRACKS:
        (OUT_ROOT / track).mkdir(parents=True, exist_ok=True)

    for slug in selected:
        instructions = sanitize_instructions(read(roots["rust"] / slug / ".docs" / "instructions.md"))
        source = f"exercism/{slug}"
        (OUT_ROOT / "c" / f"{slug}.md").write_text(
            md(slug, instructions, "c", c_code(roots["c"] / slug), source),
            encoding="utf-8",
        )
        (OUT_ROOT / "java" / f"{slug}.md").write_text(
            md(slug, instructions, "java", read(reference_java(roots["java"] / slug)), source),
            encoding="utf-8",
        )
        (OUT_ROOT / "rust" / f"{slug}.md").write_text(
            md(slug, instructions, "rust", read(roots["rust"] / slug / ".meta" / "example.rs"), source),
            encoding="utf-8",
        )

    manifest = {
        "source": "Exercism practice exercises",
        "license": "MIT",
        "problems": len(selected),
        "tracks": list(TRACKS),
        "exercises": selected,
        "commits": {name: git_head(SRC_ROOT / name) for name in ("problem-specifications", "c", "java", "rust")},
    }
    (OUT_ROOT / "manifest.json").write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    (OUT_ROOT / "README.md").write_text(
        "# Exercism Algorithm Dataset\n\n"
        f"- Problems: {len(selected)}\n"
        "- Languages: C, Java, Rust\n"
        "- Source: Exercism practice exercises with official/reference example implementations.\n"
        "- License: MIT License, Exercism. See `manifest.json` for source commits and exercise list.\n"
        "- Same-name files in `c/`, `java/`, and `rust/` share identical problem text; only the reference implementation differs.\n"
        "- Generation: `python3 scripts/generate_exercism_dataset.py`\n",
        encoding="utf-8",
    )
    print(f"generated {len(selected)} Exercism exercises under {OUT_ROOT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

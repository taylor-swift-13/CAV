#!/usr/bin/env python3
"""Build a smaller, easier Exercism-based C/Java/Rust dataset."""

from __future__ import annotations

import json
import shutil
import subprocess
from pathlib import Path

from generate_exercism_dataset import (
    REPO_ROOT,
    SRC_ROOT,
    c_code,
    exercise_title,
    git_head,
    md,
    read,
    reference_java,
    rust_has_external_dependencies,
    sanitize_instructions,
)


OUT_ROOT = REPO_ROOT / "datasets" / "exercism_easy"
TRACKS = ("c", "java", "rust")

# Kept intentionally small and beginner-friendly: arithmetic, simple loops,
# short strings, direct mappings, and basic predicates.
EASY_EXERCISES = [
    "hello-world",
    "two-fer",
    "leap",
    "difference-of-squares",
    "reverse-string",
    "rna-transcription",
    "hamming",
    "raindrops",
    "scrabble-score",
    "armstrong-numbers",
    "grains",
    "eliuds-eggs",
    "collatz-conjecture",
    "isogram",
    "pangram",
    "nucleotide-count",
    "protein-translation",
    "resistor-color",
    "resistor-color-duo",
    "resistor-color-trio",
    "bob",
    "acronym",
    "series",
    "sieve",
    "binary-search",
]


def main() -> int:
    roots = {track: SRC_ROOT / track / "exercises" / "practice" for track in TRACKS}
    selected: list[str] = []
    skipped: dict[str, str] = {}
    for slug in EASY_EXERCISES:
        c_ex = roots["c"] / slug
        java_ex = roots["java"] / slug
        rust_ex = roots["rust"] / slug
        reason = None
        if not c_ex.exists() or not java_ex.exists() or not rust_ex.exists():
            reason = "missing one language track"
        elif not (c_ex / ".meta" / "example.c").exists():
            reason = "missing C example"
        elif reference_java(java_ex) is None:
            reason = "missing single Java reference"
        elif not (rust_ex / ".meta" / "example.rs").exists():
            reason = "missing Rust example"
        elif rust_has_external_dependencies(rust_ex):
            reason = "requires external Rust dependency"
        elif not (rust_ex / ".docs" / "instructions.md").exists():
            reason = "missing instructions"
        if reason:
            skipped[slug] = reason
        else:
            selected.append(slug)

    shutil.rmtree(OUT_ROOT, ignore_errors=True)
    for track in TRACKS:
        (OUT_ROOT / track).mkdir(parents=True, exist_ok=True)

    for slug in selected:
        instructions = sanitize_instructions(read(roots["rust"] / slug / ".docs" / "instructions.md"))
        source = f"exercism/{slug}"
        (OUT_ROOT / "c" / f"{slug}.md").write_text(md(slug, instructions, "c", c_code(roots["c"] / slug), source), encoding="utf-8")
        (OUT_ROOT / "java" / f"{slug}.md").write_text(md(slug, instructions, "java", read(reference_java(roots["java"] / slug)), source), encoding="utf-8")
        (OUT_ROOT / "rust" / f"{slug}.md").write_text(md(slug, instructions, "rust", read(roots["rust"] / slug / ".meta" / "example.rs"), source), encoding="utf-8")

    manifest = {
        "source": "Exercism practice exercises",
        "license": "MIT",
        "difficulty": "easy",
        "problems": len(selected),
        "tracks": list(TRACKS),
        "exercises": selected,
        "skipped": skipped,
        "commits": {name: git_head(SRC_ROOT / name) for name in ("problem-specifications", "c", "java", "rust")},
    }
    (OUT_ROOT / "manifest.json").write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    (OUT_ROOT / "README.md").write_text(
        "# Exercism Easy Algorithm Dataset\n\n"
        f"- Problems: {len(selected)}\n"
        "- Difficulty: easy / beginner-friendly\n"
        "- Languages: C, Java, Rust\n"
        "- Source: Exercism practice exercises with official/reference example implementations.\n"
        "- License: MIT License, Exercism. See `manifest.json` for source commits and exercise list.\n"
        "- Same-name files in `c/`, `java/`, and `rust/` share identical problem text; only the reference implementation differs.\n"
        "- Generation: `python3 scripts/generate_exercism_easy_dataset.py`\n"
        "- Validation: `python3 scripts/validate_algorithm_dataset.py --dataset datasets/exercism_easy --java-release 21 --rust-edition 2024 --require-rust`\n",
        encoding="utf-8",
    )
    print(f"generated {len(selected)} easy Exercism exercises under {OUT_ROOT}")
    if skipped:
        print("skipped:")
        for slug, reason in skipped.items():
            print(f"- {slug}: {reason}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

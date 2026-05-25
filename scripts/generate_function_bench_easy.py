#!/usr/bin/env python3
"""Generate HumanEval-like easy function tasks without using HumanEval or MBPP.

The source problems and reference implementations are from Exercism easy
exercises (MIT licensed).  This script rewrites the statements into short,
function-oriented prompts while preserving source attribution.
"""

from __future__ import annotations

import json
import re
import shutil
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SRC_ROOT = REPO_ROOT / "datasets" / "exercism_easy"
OUT_ROOT = REPO_ROOT / "datasets" / "function_bench_easy"
TRACKS = ("c", "java", "rust")


PROMPTS = {
    "hello-world": "Return the greeting string `Hello, World!`.",
    "two-fer": "Given an optional name, return the phrase `One for X, one for me.` using `you` when the name is absent.",
    "leap": "Given a year, return whether it is a leap year under the Gregorian calendar rules.",
    "difference-of-squares": "Given `n`, compute the square of the sum of `1..n`, the sum of squares of `1..n`, and their difference.",
    "reverse-string": "Given a string, return a new string with the characters in reverse order.",
    "rna-transcription": "Given a DNA string, return its RNA complement using `G->C`, `C->G`, `T->A`, and `A->U`.",
    "hamming": "Given two equal-length DNA strings, return the number of positions at which they differ.",
    "raindrops": "Given a number, return `Pling` for factor 3, `Plang` for factor 5, `Plong` for factor 7, concatenating matches; return the number as text if none match.",
    "scrabble-score": "Given a word, return its Scrabble score using the standard English letter values.",
    "armstrong-numbers": "Given a non-negative integer, return whether it equals the sum of its digits each raised to the number of digits.",
    "grains": "Given a chessboard square number, return the grains on that square and support computing the total grains on the board.",
    "eliuds-eggs": "Given a non-negative integer, return the number of set bits in its binary representation.",
    "collatz-conjecture": "Given a positive integer, return the number of Collatz steps needed to reach 1.",
    "isogram": "Given a phrase, return whether no alphabetic letter appears more than once, ignoring case and separators.",
    "pangram": "Given a sentence, return whether it contains every English alphabet letter at least once.",
    "nucleotide-count": "Given a DNA string, count occurrences of the nucleotides `A`, `C`, `G`, and `T`.",
    "protein-translation": "Given an RNA string, translate codons into protein names until a stop codon is reached.",
    "bob": "Given a remark, return Bob's response according to whether it is a question, yelling, silence, or normal speech.",
    "acronym": "Given a phrase, return the acronym formed from the first letter of each word-like part.",
    "series": "Given a digit string and a slice length, return all consecutive slices of that length.",
    "sieve": "Given a limit, return all prime numbers up to that limit using the sieve of Eratosthenes.",
}


def code_block(path: Path, lang: str) -> str:
    text = path.read_text(encoding="utf-8")
    match = re.search(rf"```{lang}\n(.*?)```", text, re.S)
    if not match:
        raise ValueError(f"missing {lang} block: {path}")
    return match.group(1).strip()


def title(slug: str) -> str:
    return " ".join(part.capitalize() for part in slug.split("-"))


def md(slug: str, lang: str, code: str) -> str:
    return (
        f"# {title(slug)}\n\n"
        "## Problem\n\n"
        f"{PROMPTS[slug]}\n\n"
        "## Source\n\n"
        "- Source: Exercism practice exercise\n"
        "- License: MIT License, Exercism\n"
        "- Note: This is a short function-benchmark style rewrite; it is not HumanEval or MBPP.\n\n"
        "## Reference Implementation\n\n"
        f"```{lang}\n{code.rstrip()}\n```\n"
    )


def main() -> int:
    manifest_path = SRC_ROOT / "manifest.json"
    if not manifest_path.exists():
        raise FileNotFoundError("run scripts/generate_exercism_easy_dataset.py first")
    source_manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    exercises = [slug for slug in source_manifest["exercises"] if slug in PROMPTS]

    shutil.rmtree(OUT_ROOT, ignore_errors=True)
    for track in TRACKS:
        (OUT_ROOT / track).mkdir(parents=True, exist_ok=True)

    for slug in exercises:
        for track in TRACKS:
            source = SRC_ROOT / track / f"{slug}.md"
            (OUT_ROOT / track / f"{slug}.md").write_text(
                md(slug, track, code_block(source, track)),
                encoding="utf-8",
            )

    manifest = {
        "source": "Exercism easy exercises, rewritten into short function-benchmark prompts",
        "license": "MIT",
        "not_used": ["HumanEval", "MBPP"],
        "problems": len(exercises),
        "tracks": list(TRACKS),
        "exercises": exercises,
        "upstream_commits": source_manifest.get("commits", {}),
    }
    (OUT_ROOT / "manifest.json").write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    (OUT_ROOT / "README.md").write_text(
        "# Function Bench Easy\n\n"
        f"- Problems: {len(exercises)}\n"
        "- Style: HumanEval-like short function tasks\n"
        "- Sources: Exercism easy practice exercises, MIT License\n"
        "- Explicitly not sourced from HumanEval or MBPP\n"
        "- Languages: C, Java, Rust\n"
        "- Same-name files in `c/`, `java/`, and `rust/` share identical short problem text; only the implementation code block differs.\n"
        "- Generation: `python3 scripts/generate_function_bench_easy.py`\n"
        "- Validation: `python3 scripts/validate_algorithm_dataset.py --dataset datasets/function_bench_easy --java-release 21 --rust-edition 2024 --require-rust`\n",
        encoding="utf-8",
    )
    print(f"generated {len(exercises)} function-bench easy tasks under {OUT_ROOT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

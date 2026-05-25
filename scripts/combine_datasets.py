#!/usr/bin/env python3
"""Combine split dataset buckets into one language-partitioned dataset."""

from __future__ import annotations

import json
import shutil
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
DATASETS = REPO_ROOT / "datasets"
BUCKETS = ("internal", "external", "augment")
LANGUAGES = ("c", "java", "rust")


def read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def clear(path: Path) -> None:
    if path.exists():
        shutil.rmtree(path)
    path.mkdir(parents=True)


def external_manifest_by_name() -> dict[str, dict]:
    path = DATASETS / "external" / "manifest.json"
    if not path.exists():
        return {}
    manifest = read_json(path)
    return {problem["name"]: problem for problem in manifest.get("problems", [])}


def augment_manifest_by_name() -> dict[str, dict]:
    path = DATASETS / "augment" / "manifest.json"
    if not path.exists():
        return {}
    manifest = read_json(path)
    return {problem["name"]: problem for problem in manifest.get("problems", [])}


def explicit_source(source: dict | None) -> dict | None:
    if not source:
        return None
    if source.get("name") == "local" or not source.get("url"):
        return None
    return source


def manifest_source(problem: dict | None) -> dict | None:
    if not problem:
        return None
    source = {
        "name": problem.get("source"),
        "slug": problem.get("source_slug"),
        "url": problem.get("source_url"),
        "license": problem.get("license"),
    }
    return explicit_source(source)


def copy_markdown(out_root: Path) -> None:
    for language in LANGUAGES:
        target = out_root / language
        target.mkdir(parents=True)
        for bucket in BUCKETS:
            for source in sorted((DATASETS / bucket / language).glob("*.md")):
                shutil.copy2(source, target / source.name)


def copy_tests(out_root: Path, external_meta: dict[str, dict]) -> list[dict]:
    problems: list[dict] = []
    tests_dir = out_root / "tests"
    tests_dir.mkdir(parents=True)
    augment_meta = augment_manifest_by_name()

    for bucket in BUCKETS:
        for source in sorted((DATASETS / bucket / "tests").glob("*.json")):
            data = read_json(source)
            source_meta = explicit_source(data.get("source"))
            if source_meta:
                data["source"] = source_meta
            else:
                data.pop("source", None)

            target = tests_dir / source.name
            target.write_text(
                json.dumps(data, indent=2, ensure_ascii=False) + "\n",
                encoding="utf-8",
            )

            entry = {
                "name": data["name"],
                "return_type": data.get("return_type"),
                "params": data.get("params", []),
            }
            if "function" in data:
                entry["function"] = data["function"]
            if "augment" in data:
                entry["augment"] = data["augment"]
            elif data["name"] in augment_meta:
                entry["augment"] = {
                    "parent_dataset": augment_meta[data["name"]]["parent_dataset"],
                    "parent_problem": augment_meta[data["name"]]["parent_problem"],
                    "variant_kind": augment_meta[data["name"]]["variant_kind"],
                    "constants": augment_meta[data["name"]]["constants"],
                }
            source_for_manifest = source_meta or manifest_source(external_meta.get(data["name"]))
            if source_for_manifest:
                entry["source"] = source_for_manifest
            problems.append(entry)
    return problems


def write_readme(out_root: Path, problem_count: int) -> None:
    (out_root / "README.md").write_text(
        "# Combined Algorithm Dataset\n\n"
        f"- Problems: {problem_count}\n"
        "- Languages: C, Java, Rust\n"
        "- Layout: one Markdown file per problem per language in `c/`, `java/`, and `rust/`.\n"
        "- Tests: shared JSON files in `tests/`.\n"
        "- Source attribution: problems with a clear external origin include a `source` field in `tests/*.json` and `manifest.json`.\n"
        "- Generation: `python3 scripts/combine_datasets.py`\n",
        encoding="utf-8",
    )


def main() -> None:
    missing = [bucket for bucket in BUCKETS if not (DATASETS / bucket).exists()]
    if missing:
        names = ", ".join(missing)
        sys.exit(f"missing source dataset bucket(s): {names}")

    out_root = DATASETS / ".combined_tmp"
    clear(out_root)

    external_meta = external_manifest_by_name()
    copy_markdown(out_root)
    problems = copy_tests(out_root, external_meta)
    problems.sort(key=lambda p: p["name"])

    manifest = {
        "source": "Combined internal, external, and augment algorithm datasets",
        "style": "HumanEval-like single-function tasks",
        "languages": list(LANGUAGES),
        "requirements": ["single function", "standard library only", "shared tests"],
        "problems": problems,
    }
    (out_root / "manifest.json").write_text(
        json.dumps(manifest, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    write_readme(out_root, len(problems))

    for bucket in BUCKETS:
        shutil.rmtree(DATASETS / bucket)
    for language in LANGUAGES:
        clear(DATASETS / language)
        shutil.rmtree(DATASETS / language)
    if (DATASETS / "tests").exists():
        shutil.rmtree(DATASETS / "tests")
    for child in out_root.iterdir():
        shutil.move(str(child), DATASETS / child.name)
    shutil.rmtree(out_root)


if __name__ == "__main__":
    main()

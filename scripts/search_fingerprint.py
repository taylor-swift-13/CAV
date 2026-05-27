#!/usr/bin/env python3
"""Search end-to-end examples by the four-field algorithm fingerprint.

The script intentionally performs only cheap coarse filtering:

  * controlled keywords: problem_kind, data, pattern
  * free text: semantic_description

It does not read source files, proof files, or reasoning logs. The caller should
expand only the top returned candidates.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_ROOT = REPO_ROOT / "experiences" / "end-end"
KEYS = ("problem_kind", "data", "pattern")

STOPWORDS = {
    "a", "an", "and", "are", "as", "by", "for", "from", "in", "into",
    "is", "it", "its", "no", "not", "of", "on", "or", "the", "to",
    "with", "without", "all", "one", "two", "this", "that",
}


def _as_set(value: Any) -> set[str]:
    if isinstance(value, str):
        return {value}
    if isinstance(value, list):
        return {x for x in value if isinstance(x, str)}
    return set()


def _tokens(text: str) -> set[str]:
    words = re.findall(r"[A-Za-z_][A-Za-z0-9_]*|\d+", text.lower())
    return {w for w in words if len(w) > 1 and w not in STOPWORDS}


def _read_json(path: Path) -> dict[str, Any] | None:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    return data if isinstance(data, dict) else None


def load_query(args: argparse.Namespace) -> dict[str, Any]:
    if args.fingerprint:
        fp = _read_json(Path(args.fingerprint))
        if fp is None:
            raise SystemExit(f"cannot read fingerprint JSON: {args.fingerprint}")
        return fp

    keywords = {
        k: v
        for k, v in {
            "problem_kind": args.problem_kind,
            "data": args.data,
            "pattern": args.pattern,
        }.items()
        if v
    }
    if not keywords and not args.semantic_description:
        raise SystemExit("provide --fingerprint or at least one query field")
    return {
        "function_name": args.function_name or "",
        "semantic_description": args.semantic_description or "",
        "keywords": keywords,
    }


def keyword_match(query_kw: dict[str, Any], cand_kw: dict[str, Any]) -> tuple[int, list[str]]:
    matched: list[str] = []
    for key in KEYS:
        q_values = _as_set(query_kw.get(key))
        c_values = _as_set(cand_kw.get(key))
        if q_values and c_values and q_values.intersection(c_values):
            matched.append(key)
    return len(matched), matched


def semantic_overlap(query_desc: str, cand_desc: str) -> float:
    q = _tokens(query_desc)
    c = _tokens(cand_desc)
    if not q or not c:
        return 0.0
    return len(q & c) / len(q | c)


def artifact_paths(case_dir: Path, function_name: str) -> dict[str, str]:
    generated = case_dir / "coq" / "generated"
    return {
        "case_dir": str(case_dir),
        "fingerprint": str(case_dir / "logs" / "workspace_fingerprint.json"),
        "annotation_reasoning": str(case_dir / "logs" / "annotation_reasoning.md"),
        "proof_reasoning": str(case_dir / "logs" / "proof_reasoning.md"),
        "issues": str(case_dir / "logs" / "issues.md"),
        "original_c": str(case_dir / "original" / f"{function_name}.c"),
        "annotated_c": str(case_dir / "annotated" / f"{function_name}.c"),
        "proof_manual": str(generated / f"{function_name}_proof_manual.v"),
        "generated_dir": str(generated),
    }


def iter_fingerprints(root: Path):
    if not root.exists():
        return
    yield from sorted(root.glob("*/logs/workspace_fingerprint.json"))


def search(query: dict[str, Any], root: Path, *, min_keyword_matches: int, top: int) -> dict[str, Any]:
    query_kw = query.get("keywords") if isinstance(query.get("keywords"), dict) else {}
    query_desc = query.get("semantic_description") if isinstance(query.get("semantic_description"), str) else ""

    results: list[dict[str, Any]] = []
    scanned = 0
    for fp_path in iter_fingerprints(root) or []:
        cand = _read_json(fp_path)
        if cand is None:
            continue
        scanned += 1
        cand_kw = cand.get("keywords") if isinstance(cand.get("keywords"), dict) else {}
        matches, matched_fields = keyword_match(query_kw, cand_kw)
        if matches < min_keyword_matches:
            continue
        cand_desc = cand.get("semantic_description") if isinstance(cand.get("semantic_description"), str) else ""
        overlap = semantic_overlap(query_desc, cand_desc)
        score = matches * 100 + round(overlap * 100, 2)
        function_name = cand.get("function_name") if isinstance(cand.get("function_name"), str) else fp_path.parents[1].name
        case_dir = fp_path.parents[1]
        results.append({
            "score": score,
            "keyword_matches": matches,
            "matched_keywords": matched_fields,
            "semantic_overlap": round(overlap, 4),
            "function_name": function_name,
            "keywords": {k: cand_kw.get(k) for k in KEYS if k in cand_kw},
            "semantic_description": cand_desc,
            "paths": artifact_paths(case_dir, function_name),
        })

    results.sort(key=lambda r: (-r["keyword_matches"], -r["semantic_overlap"], r["function_name"]))
    for i, item in enumerate(results[:top], start=1):
        item["rank"] = i
    return {
        "query": {
            "function_name": query.get("function_name", ""),
            "keywords": {k: query_kw.get(k) for k in KEYS if k in query_kw},
            "semantic_description": query_desc,
        },
        "root": str(root),
        "scanned": scanned,
        "returned": min(len(results), top),
        "results": results[:top],
    }


def render_markdown(result: dict[str, Any]) -> str:
    lines = [
        f"searched: `{result['root']}`",
        f"fingerprints_scanned: `{result['scanned']}`",
        f"results_returned: `{result['returned']}`",
        "",
    ]
    for item in result["results"]:
        lines.extend([
            f"## {item['rank']}. {item['function_name']}",
            f"- score: `{item['score']}`",
            f"- keyword_matches: `{item['keyword_matches']}` ({', '.join(item['matched_keywords'])})",
            f"- semantic_overlap: `{item['semantic_overlap']}`",
            f"- keywords: `{json.dumps(item['keywords'], ensure_ascii=False)}`",
            f"- fingerprint: `{item['paths']['fingerprint']}`",
            f"- case_dir: `{item['paths']['case_dir']}`",
            f"- description: {item['semantic_description']}",
            "",
        ])
    return "\n".join(lines).rstrip() + "\n"


def render_paths(result: dict[str, Any]) -> str:
    return "".join(f"{item['paths']['case_dir']}\n" for item in result["results"])


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Search experiences/end-end by four-field fingerprint.")
    p.add_argument("--fingerprint", help="Current logs/workspace_fingerprint.json.")
    p.add_argument("--problem-kind", choices=[
        "identity", "min_max", "count", "sum", "product", "search", "compare",
        "transform", "partition", "sort", "prefix", "dp", "math",
    ])
    p.add_argument("--data", choices=[
        "scalar", "array", "string", "matrix", "linked_list", "tree", "graph",
    ])
    p.add_argument("--pattern", choices=[
        "straight_line", "branch", "single_loop", "nested_loop", "two_pointers",
        "sliding_window", "prefix_scan", "binary_search", "recursion", "state_machine",
    ])
    p.add_argument("--semantic-description", default="")
    p.add_argument("--function-name", default="")
    p.add_argument("--root", default=str(DEFAULT_ROOT), help="Directory containing end-to-end examples.")
    p.add_argument("--min-keyword-matches", type=int, default=2, choices=[0, 1, 2, 3])
    p.add_argument("--top", type=int, default=5)
    p.add_argument("--format", choices=["paths", "json", "markdown"], default="paths")
    return p


def main() -> int:
    args = build_parser().parse_args()
    query = load_query(args)
    result = search(query, Path(args.root), min_keyword_matches=args.min_keyword_matches, top=max(1, args.top))
    if args.format == "paths":
        sys.stdout.write(render_paths(result))
    elif args.format == "markdown":
        sys.stdout.write(render_markdown(result))
    else:
        json.dump(result, sys.stdout, indent=2, ensure_ascii=False)
        sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

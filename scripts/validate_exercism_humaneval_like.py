#!/usr/bin/env python3
"""Validate the Exercism HumanEval-like dataset with shared tests."""

from __future__ import annotations

import json
import re
import shutil
import subprocess
import tempfile
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
DATASET = REPO_ROOT / "datasets" / "external"


def block(path: Path, lang: str) -> str:
    text = path.read_text(encoding="utf-8")
    match = re.search(rf"```{lang}\n(.*?)```", text, re.S)
    if not match:
        raise ValueError(f"missing {lang} block in {path}")
    return match.group(1).strip() + "\n"


def c_lit(value, typ: str) -> str:
    if typ == "int":
        return str(value)
    if typ == "bool":
        return "1" if value else "0"
    if typ == "string":
        return json.dumps(value)
    raise ValueError(typ)


def java_lit(value, typ: str) -> str:
    if typ == "int":
        return str(value)
    if typ == "bool":
        return "true" if value else "false"
    if typ == "string":
        return json.dumps(value)
    raise ValueError(typ)


def rust_lit(value, typ: str) -> str:
    if typ == "int":
        return str(value)
    if typ == "bool":
        return "true" if value else "false"
    if typ == "string":
        return json.dumps(value)
    raise ValueError(typ)


def args(case: dict, params: list[dict], literal) -> str:
    return ", ".join(literal(case["input"][p["name"]], p["type"]) for p in params)


def c_harness(name: str, spec: dict, code: str) -> str:
    lines = ["#include <stdio.h>", "#include <stdlib.h>", "#include <string.h>", code, "int main(void) {"]
    ret = spec["return_type"]
    for i, case in enumerate(spec["tests"]):
        call = f"{name}({args(case, spec['params'], c_lit)})"
        if ret == "string":
            lines.append(f"    char *r{i} = {call};")
            lines.append(f"    if (strcmp(r{i}, {c_lit(case['expected'], 'string')}) != 0) return {i + 1};")
            lines.append(f"    free(r{i});")
        else:
            lines.append(f"    if ({call} != {c_lit(case['expected'], ret)}) return {i + 1};")
    lines.append('    printf("ok\\n");')
    lines.append("    return 0;")
    lines.append("}")
    return "\n".join(lines)


def java_harness(name: str, spec: dict, code: str) -> str:
    cls = re.search(r"class\s+([A-Za-z_]\w*)", code).group(1)
    lines = [code, "class Harness {", "  public static void main(String[] args) {"]
    ret = spec["return_type"]
    for i, case in enumerate(spec["tests"]):
        call = f"{cls}.{name}({args(case, spec['params'], java_lit)})"
        if ret == "string":
            lines.append(f"    if (!{call}.equals({java_lit(case['expected'], 'string')})) System.exit({i + 1});")
        else:
            lines.append(f"    if ({call} != {java_lit(case['expected'], ret)}) System.exit({i + 1});")
    lines.append('    System.out.println("ok");')
    lines.append("  }")
    lines.append("}")
    return "\n".join(lines)


def rust_harness(name: str, spec: dict, code: str) -> str:
    lines = [code, "fn main() {"]
    ret = spec["return_type"]
    for case in spec["tests"]:
        call = f"{name}({args(case, spec['params'], rust_lit)})"
        expected = rust_lit(case["expected"], ret)
        if ret == "string":
            lines.append(f"    assert_eq!({call}, {expected}.to_string());")
        else:
            lines.append(f"    assert_eq!({call}, {expected});")
    lines.append('    println!("ok");')
    lines.append("}")
    return "\n".join(lines)


def run(cmd: list[str], cwd: Path) -> None:
    subprocess.run(cmd, cwd=cwd, check=True)


def validate_one(name: str, tmp: Path) -> None:
    spec = json.loads((DATASET / "tests" / f"{name}.json").read_text(encoding="utf-8"))
    c_code = block(DATASET / "c" / f"{name}.md", "c")
    java_code = block(DATASET / "java" / f"{name}.md", "java")
    rust_code = block(DATASET / "rust" / f"{name}.md", "rust")

    c_file = tmp / f"{name}.c"
    c_bin = tmp / f"{name}_c"
    c_file.write_text(c_harness(name, spec, c_code), encoding="utf-8")
    run(["gcc", "-std=c11", "-Wall", "-Wextra", "-Werror", str(c_file), "-o", str(c_bin)], tmp)
    run([str(c_bin)], tmp)

    java_file = tmp / "Harness.java"
    java_file.write_text(java_harness(name, spec, java_code), encoding="utf-8")
    run(["javac", "--release", "8", str(java_file)], tmp)
    run(["java", "-cp", str(tmp), "Harness"], tmp)
    for f in tmp.glob("*.class"):
        f.unlink()

    rust_file = tmp / f"{name}.rs"
    rust_bin = tmp / f"{name}_rust"
    rust_file.write_text(rust_harness(name, spec, rust_code), encoding="utf-8")
    rustc = shutil.which("rustc") or str(Path.home() / ".cargo" / "bin" / "rustc")
    run([rustc, "--edition", "2024", str(rust_file), "-o", str(rust_bin)], tmp)
    run([str(rust_bin)], tmp)


def c_harness_all(items: list[tuple[str, dict, str]]) -> str:
    lines = ["#include <stdio.h>", "#include <stdlib.h>", "#include <string.h>"]
    lines.extend(code for _, _, code in items)
    lines.append("int main(void) {")
    check = 1
    for name, spec, _ in items:
        ret = spec["return_type"]
        for case in spec["tests"]:
            call = f"{name}({args(case, spec['params'], c_lit)})"
            if ret == "string":
                lines.append(f"    char *r{check} = {call};")
                lines.append(f"    if (strcmp(r{check}, {c_lit(case['expected'], 'string')}) != 0) return {check};")
                lines.append(f"    free(r{check});")
            else:
                lines.append(f"    if ({call} != {c_lit(case['expected'], ret)}) return {check};")
            check += 1
    lines.append('    printf("ok\\n");')
    lines.append("    return 0;")
    lines.append("}")
    return "\n".join(lines)


def java_harness_all(items: list[tuple[str, dict, str]]) -> str:
    lines = [code for _, _, code in items]
    lines.append("class Harness {")
    check = 1
    chunk = 0
    in_method = False
    per_method = 0
    for name, spec, code in items:
        cls = re.search(r"class\s+([A-Za-z_]\w*)", code).group(1)
        ret = spec["return_type"]
        for case in spec["tests"]:
            if not in_method:
                lines.append(f"  static void check{chunk}() {{")
                in_method = True
                per_method = 0
            call = f"{cls}.{name}({args(case, spec['params'], java_lit)})"
            if ret == "string":
                lines.append(f"    if (!{call}.equals({java_lit(case['expected'], 'string')})) System.exit({check});")
            else:
                lines.append(f"    if ({call} != {java_lit(case['expected'], ret)}) System.exit({check});")
            check += 1
            per_method += 1
            if per_method >= 700:
                lines.append("  }")
                chunk += 1
                in_method = False
    if in_method:
        lines.append("  }")
        chunk += 1
    lines.append("  public static void main(String[] args) {")
    for i in range(chunk):
        lines.append(f"    check{i}();")
    lines.append('    System.out.println("ok");')
    lines.append("  }")
    lines.append("}")
    return "\n".join(lines)


def rust_harness_all(items: list[tuple[str, dict, str]]) -> str:
    lines = [code for _, _, code in items]
    lines.append("fn main() {")
    for name, spec, _ in items:
        ret = spec["return_type"]
        for case in spec["tests"]:
            call = f"{name}({args(case, spec['params'], rust_lit)})"
            expected = rust_lit(case["expected"], ret)
            if ret == "string":
                lines.append(f"    assert_eq!({call}, {expected}.to_string());")
            else:
                lines.append(f"    assert_eq!({call}, {expected});")
    lines.append('    println!("ok");')
    lines.append("}")
    return "\n".join(lines)


def validate_all(names: list[str], tmp: Path) -> None:
    c_items = [(name, json.loads((DATASET / "tests" / f"{name}.json").read_text(encoding="utf-8")), block(DATASET / "c" / f"{name}.md", "c")) for name in names]
    c_file = tmp / "external_all.c"
    c_bin = tmp / "external_c"
    c_file.write_text(c_harness_all(c_items), encoding="utf-8")
    run(["gcc", "-std=c11", "-Wall", "-Wextra", "-Werror", str(c_file), "-o", str(c_bin)], tmp)
    run([str(c_bin)], tmp)

    java_items = [(name, json.loads((DATASET / "tests" / f"{name}.json").read_text(encoding="utf-8")), block(DATASET / "java" / f"{name}.md", "java")) for name in names]
    java_file = tmp / "Harness.java"
    java_file.write_text(java_harness_all(java_items), encoding="utf-8")
    run(["javac", "--release", "8", str(java_file)], tmp)
    run(["java", "-cp", str(tmp), "Harness"], tmp)

    rust_items = [(name, json.loads((DATASET / "tests" / f"{name}.json").read_text(encoding="utf-8")), block(DATASET / "rust" / f"{name}.md", "rust")) for name in names]
    rust_file = tmp / "external_all.rs"
    rust_bin = tmp / "external_rust"
    rust_file.write_text(rust_harness_all(rust_items), encoding="utf-8")
    rustc = shutil.which("rustc") or str(Path.home() / ".cargo" / "bin" / "rustc")
    run([rustc, "--edition", "2024", str(rust_file), "-o", str(rust_bin)], tmp)
    run([str(rust_bin)], tmp)


def main() -> int:
    manifest = json.loads((DATASET / "manifest.json").read_text(encoding="utf-8"))
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td)
        names = [item["name"] if isinstance(item, dict) else item for item in manifest["problems"]]
        validate_all(names, tmp)
    print(f"validated {len(names)} problems with shared tests across C/Java/Rust")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

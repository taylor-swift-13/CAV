#!/usr/bin/env python3
"""Run shared tests for datasets/internal across C, Java, and Rust."""

from __future__ import annotations

import json
import re
import shutil
import subprocess
import tempfile
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
DATASET = REPO_ROOT / "datasets" / "internal"


def block(path: Path, lang: str) -> str:
    text = path.read_text(encoding="utf-8")
    match = re.search(rf"```{lang}\n(.*?)```", text, re.S)
    if not match:
        raise ValueError(f"missing {lang} block: {path}")
    return match.group(1).strip() + "\n"


def c_char(value: str) -> str:
    return "'" + value.replace("\\", "\\\\").replace("'", "\\'") + "'"


def java_char(value: str) -> str:
    return "'" + value.replace("\\", "\\\\").replace("'", "\\'") + "'"


def rust_char(value: str) -> str:
    return str(ord(value))


def c_lit(value, typ: str) -> str:
    if typ == "int":
        return str(value)
    if typ == "char":
        return c_char(value)
    if typ in ("c_string", "mut_c_string", "out_c_string"):
        return json.dumps(value)
    if typ in ("int_array", "mut_int_array", "out_int_array"):
        return "{" + ", ".join(str(x) for x in value) + "}"
    raise ValueError(typ)


def java_lit(value, typ: str) -> str:
    if typ == "int":
        return str(value)
    if typ == "char":
        return java_char(value)
    if typ in ("c_string", "mut_c_string", "out_c_string"):
        chars = [java_char(ch) for ch in value] + ["'\\0'"]
        return "new char[]{" + ", ".join(chars) + "}"
    if typ in ("int_array", "mut_int_array", "out_int_array"):
        return "new int[]{" + ", ".join(str(x) for x in value) + "}"
    raise ValueError(typ)


def rust_lit(value, typ: str) -> str:
    if typ == "int":
        return str(value)
    if typ == "char":
        return rust_char(value)
    if typ in ("c_string", "mut_c_string", "out_c_string"):
        nums = [str(ord(ch)) for ch in value] + ["0"]
        return "[" + ", ".join(nums) + "]"
    if typ in ("int_array", "mut_int_array", "out_int_array"):
        return "[" + ", ".join(str(x) for x in value) + "]"
    raise ValueError(typ)


def c_decl(name: str, value, typ: str) -> str:
    if typ in ("int_array", "mut_int_array", "out_int_array"):
        length = max(1, len(value))
        return f"        int {name}[{length}] = {c_lit(value, typ)};"
    if typ in ("c_string", "mut_c_string", "out_c_string"):
        length = max(1, len(value) + 1)
        return f"        char {name}[{length}] = {c_lit(value, typ)};"
    if typ == "int":
        return f"        int {name} = {c_lit(value, typ)};"
    if typ == "char":
        return f"        char {name} = {c_lit(value, typ)};"
    raise ValueError(typ)


def c_args(case: dict, params: list[dict]) -> tuple[list[str], str]:
    decls = []
    args = []
    for idx, p in enumerate(params):
        val = case["input"][p["name"]]
        typ = p["type"]
        if typ in ("int_array", "mut_int_array", "out_int_array", "c_string", "mut_c_string", "out_c_string"):
            name = f"{p['name']}_{idx}"
            decls.append(c_decl(name, val, typ))
            args.append(name)
        else:
            args.append(c_lit(val, typ))
    return decls, ", ".join(args)


def java_args(case: dict, params: list[dict]) -> tuple[list[str], str, dict[str, str]]:
    decls = []
    args = []
    names = {}
    for idx, p in enumerate(params):
        val = case["input"][p["name"]]
        typ = p["type"]
        if typ in ("int_array", "mut_int_array", "out_int_array"):
            var = f"{p['name']}_{idx}"
            decls.append(f"    int[] {var} = {java_lit(val, typ)};")
            args.append(var)
            names[p["name"]] = var
        elif typ in ("c_string", "mut_c_string", "out_c_string"):
            var = f"{p['name']}_{idx}"
            decls.append(f"    char[] {var} = {java_lit(val, typ)};")
            args.append(var)
            names[p["name"]] = var
        else:
            args.append(java_lit(val, typ))
    return decls, ", ".join(args), names


def rust_args(case: dict, params: list[dict]) -> tuple[list[str], str, dict[str, str]]:
    decls = []
    args = []
    names = {}
    for idx, p in enumerate(params):
        val = case["input"][p["name"]]
        typ = p["type"]
        if typ in ("int_array", "c_string"):
            var = f"{p['name']}_{idx}"
            decls.append(f"    let {var} = {rust_lit(val, typ)};")
            args.append(f"&{var}")
            names[p["name"]] = var
        elif typ in ("mut_int_array", "out_int_array", "mut_c_string", "out_c_string"):
            var = f"{p['name']}_{idx}"
            decls.append(f"    let mut {var} = {rust_lit(val, typ)};")
            args.append(f"&mut {var}")
            names[p["name"]] = var
        else:
            args.append(rust_lit(val, typ))
    return decls, ", ".join(args), names


def c_expected(value, return_type: str) -> str:
    if return_type == "int":
        return str(value)
    if return_type == "char":
        return c_char(value)
    raise ValueError(return_type)


def java_expected(value, return_type: str) -> str:
    if return_type == "int":
        return str(value)
    if return_type == "char":
        return java_char(value)
    raise ValueError(return_type)


def rust_expected(value, return_type: str) -> str:
    if return_type == "int":
        return str(value)
    if return_type == "char":
        return rust_char(value)
    raise ValueError(return_type)


def c_check_mutation(var: str, typ: str, expected, exit_code: int) -> list[str]:
    lines = []
    if typ in ("mut_int_array", "out_int_array"):
        exp = f"exp_{var}"
        lines.append(f"        int {exp}[{max(1, len(expected))}] = {c_lit(expected, typ)};")
        lines.append(f"        for (int j = 0; j < {len(expected)}; ++j) if ({var}[j] != {exp}[j]) return {exit_code};")
    elif typ in ("mut_c_string", "out_c_string"):
        lines.append(f"        if (strcmp({var}, {json.dumps(expected)}) != 0) return {exit_code};")
    return lines


def java_check_mutation(var: str, typ: str, expected, exit_code: int) -> str | None:
    if typ in ("mut_int_array", "out_int_array"):
        return f"    if (!Arrays.equals({var}, {java_lit(expected, typ)})) System.exit({exit_code});"
    if typ in ("mut_c_string", "out_c_string"):
        return f"    if (!cstrEquals({var}, {json.dumps(expected)})) System.exit({exit_code});"
    return None


def rust_check_mutation(var: str, typ: str, expected) -> str | None:
    if typ in ("mut_int_array", "out_int_array"):
        return f"    assert_eq!({var}, {rust_lit(expected, typ)});"
    if typ in ("mut_c_string", "out_c_string"):
        return f"    assert_eq!(cstr_to_string(&{var}), {json.dumps(expected)});"
    return None


def c_harness(function: str, spec: dict, code: str) -> str:
    lines = ["#include <stdio.h>", "#include <string.h>", code, "int main(void) {"]
    for i, case in enumerate(spec["tests"]):
        lines.append("    {")
        decls, call_args = c_args(case, spec["params"])
        lines.extend(decls)
        if spec["return_type"] == "void":
            lines.append(f"        {function}({call_args});")
        else:
            lines.append(f"        if ({function}({call_args}) != {c_expected(case['expected'], spec['return_type'])}) return {i + 1};")
        mutations = case.get("mutations", {})
        for idx, p in enumerate(spec["params"]):
            if p["name"] in mutations:
                lines.extend(c_check_mutation(f"{p['name']}_{idx}", p["type"], mutations[p["name"]], i + 1))
        lines.append("    }")
    lines.append('    printf("ok\\n");')
    lines.append("    return 0;")
    lines.append("}")
    return "\n".join(lines)


def java_harness(function: str, spec: dict, code: str) -> str:
    cls = re.search(r"class\s+([A-Za-z_]\w*)", code).group(1)
    lines = [
        "import java.util.Arrays;",
        code,
        "class Harness {",
        "  static boolean cstrEquals(char[] s, String expected) {",
        "    int i = 0;",
        "    while (i < s.length && s[i] != '\\0') i++;",
        "    return new String(s, 0, i).equals(expected);",
        "  }",
        "  public static void main(String[] args) {",
    ]
    for i, case in enumerate(spec["tests"]):
        lines.append("    {")
        decls, call_args, names = java_args(case, spec["params"])
        lines.extend(decls)
        if spec["return_type"] == "void":
            lines.append(f"      {cls}.{function}({call_args});")
        else:
            lines.append(f"      if ({cls}.{function}({call_args}) != {java_expected(case['expected'], spec['return_type'])}) System.exit({i + 1});")
        for p in spec["params"]:
            if p["name"] in case.get("mutations", {}):
                check = java_check_mutation(names[p["name"]], p["type"], case["mutations"][p["name"]], i + 1)
                if check:
                    lines.append("  " + check)
        lines.append("    }")
    lines.append('    System.out.println("ok");')
    lines.append("  }")
    lines.append("}")
    return "\n".join(lines)


def rust_harness(function: str, spec: dict, code: str) -> str:
    lines = [
        code,
        "fn cstr_to_string(s: &[u8]) -> String {",
        "    let end = s.iter().position(|&x| x == 0).unwrap_or(s.len());",
        "    String::from_utf8(s[..end].to_vec()).unwrap()",
        "}",
        "fn main() {",
    ]
    for case in spec["tests"]:
        decls, call_args, names = rust_args(case, spec["params"])
        lines.extend(decls)
        if spec["return_type"] == "void":
            lines.append(f"    {function}({call_args});")
        else:
            lines.append(f"    assert_eq!({function}({call_args}), {rust_expected(case['expected'], spec['return_type'])});")
        for p in spec["params"]:
            if p["name"] in case.get("mutations", {}):
                check = rust_check_mutation(names[p["name"]], p["type"], case["mutations"][p["name"]])
                if check:
                    lines.append(check)
    lines.append('    println!("ok");')
    lines.append("}")
    return "\n".join(lines)


def run(cmd: list[str], cwd: Path) -> None:
    proc = subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if proc.returncode != 0:
        if proc.stdout:
            print(proc.stdout, end="")
        if proc.stderr:
            print(proc.stderr, end="")
        raise subprocess.CalledProcessError(proc.returncode, cmd)


def validate_one(path: Path, tmp: Path) -> None:
    spec = json.loads(path.read_text(encoding="utf-8"))
    name = spec["name"]
    function = spec.get("function", name)
    c_code = block(DATASET / "c" / f"{name}.md", "c")
    java_code = block(DATASET / "java" / f"{name}.md", "java")
    rust_code = block(DATASET / "rust" / f"{name}.md", "rust")

    c_file = tmp / f"{name}.c"
    c_bin = tmp / f"{name}_c"
    c_file.write_text(c_harness(function, spec, c_code), encoding="utf-8")
    run(["gcc", "-std=c11", "-Wall", "-Wextra", "-Werror", "-Wno-unused-parameter", str(c_file), "-o", str(c_bin)], tmp)
    run([str(c_bin)], tmp)

    java_file = tmp / "Harness.java"
    java_file.write_text(java_harness(function, spec, java_code), encoding="utf-8")
    run(["javac", "--release", "8", str(java_file)], tmp)
    run(["java", "-cp", str(tmp), "Harness"], tmp)
    for f in tmp.glob("*.class"):
        f.unlink()

    rust_file = tmp / f"{name}.rs"
    rust_bin = tmp / f"{name}_rust"
    rust_file.write_text(rust_harness(function, spec, rust_code), encoding="utf-8")
    rustc = shutil.which("rustc") or str(Path.home() / ".cargo" / "bin" / "rustc")
    run([rustc, "--edition", "2024", str(rust_file), "-o", str(rust_bin)], tmp)
    run([str(rust_bin)], tmp)


def main() -> int:
    test_files = sorted((DATASET / "tests").glob("*.json"))
    if not test_files:
        raise SystemExit("no shared tests found; run scripts/generate_algorithm_shared_tests.py")
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td)
        for path in test_files:
            validate_one(path, tmp)
    total = len(list((DATASET / "c").glob("*.md")))
    print(f"validated {len(test_files)} / {total} datasets/internal problems with shared C/Java/Rust tests")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

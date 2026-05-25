#!/usr/bin/env python3
"""Generate augmented variants of existing internal/external problems.

The augment dataset records small variants of problems that already exist in
datasets/internal or datasets/external.  Each item is still HumanEval-like: one
function, standard library only, and one shared JSON test suite for C/Java/Rust.
"""

from __future__ import annotations

import json
import shutil
from dataclasses import dataclass
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
OUT = REPO_ROOT / "datasets" / "augment"
TARGET_PROBLEMS = 14
CASES_PER_PROBLEM = 10


@dataclass
class Problem:
    name: str
    prompt: str
    return_type: str
    params: list[dict]
    c: str
    java: str
    rust: str
    tests: list[dict]
    parent_dataset: str
    parent_problem: str
    variant_kind: str
    constants: dict


def java_class(name: str) -> str:
    return "".join(part.capitalize() for part in name.split("_"))


def md(p: Problem, lang: str, code: str) -> str:
    params = ", ".join(f"{x['name']}:{x['type']}" for x in p.params)
    reqs = [
        "Implement exactly the named function.",
        "Use only the language standard library.",
        "Do not read stdin or write stdout.",
        "Inputs satisfy the stated encoding constraints.",
        "This is an augment item: it is a same-problem implementation variant or a small semantic variant of the recorded parent problem.",
    ]
    return (
        f"# {p.name}\n\n"
        "## Problem\n\n"
        f"{p.prompt}\n\n"
        "## Augment Metadata\n\n"
        f"- Parent dataset: `{p.parent_dataset}`\n"
        f"- Parent problem: `{p.parent_problem}`\n"
        f"- Variant kind: `{p.variant_kind}`\n"
        f"- Constants: `{json.dumps(p.constants, sort_keys=True)}`\n\n"
        "## Signature\n\n"
        f"- Return: `{p.return_type}`\n"
        f"- Params: `{params}`\n\n"
        "## Requirements\n\n"
        + "\n".join(f"- {x}" for x in reqs)
        + f"\n\n## Reference Implementation\n\n```{lang}\n{code}\n```\n"
    )


def csv_values(i: int, salt: int) -> list[int]:
    n = (i + salt) % 7
    return [((i * (j + 3) + salt * 5 + j * j) % 17) - 8 for j in range(n)]


def csv(xs: list[int]) -> str:
    return ",".join(str(x) for x in xs)


def parse_csv_expr(lang: str, var: str) -> str:
    if lang == "c":
        return (
            f"    int values[64];\n"
            f"    int n = 0;\n"
            f"    int i = 0;\n"
            f"    while ({var}[i] != '\\0') {{\n"
            f"        int sign = 1;\n"
            f"        if ({var}[i] == '-') {{ sign = -1; i++; }}\n"
            f"        int v = 0;\n"
            f"        while ({var}[i] >= '0' && {var}[i] <= '9') {{ v = v * 10 + {var}[i] - '0'; i++; }}\n"
            f"        values[n++] = sign * v;\n"
            f"        if ({var}[i] == ',') i++;\n"
            f"    }}\n"
        )
    if lang == "java":
        return f"        String[] parts = nums.isEmpty() ? new String[0] : nums.split(\",\");\n"
    return (
        f"    let values: Vec<i32> = if {var}.is_empty() {{ Vec::new() }} "
        f"else {{ {var}.split(',').map(|x| x.parse::<i32>().unwrap()).collect() }};\n"
    )


def build_tests(kind: str, constants: dict, ref) -> list[dict]:
    tests = []
    for salt in range(CASES_PER_PROBLEM):
        if kind.startswith("string_"):
            pool = ["", "abc123", "banana", "abracadabra", "zzzza", "a_b-c!", "leetcode", "AAaa11", "mississippi", "xyz"]
            inp = {"s": pool[salt]}
        else:
            inp = {"nums": csv(csv_values(constants["i"], salt))}
        tests.append({"kind": "positive" if salt % 4 else "negative", "input": inp, "expected": ref(inp)})
    return tests


def count_ge(i: int) -> Problem:
    threshold = i % 17 - 8
    name = f"aug_count_ge_{i:03d}"
    c = f"int {name}(const char *nums) {{\n{parse_csv_expr('c', 'nums')}    int count = 0;\n    for (int j = 0; j < n; j++) if (values[j] >= {threshold}) count++;\n    return count;\n}}"
    java = f"class {java_class(name)} {{\n    public static int {name}(String nums) {{\n{parse_csv_expr('java', 'nums')}        int count = 0;\n        for (String p : parts) if (Integer.parseInt(p) >= {threshold}) count++;\n        return count;\n    }}\n}}"
    rust = f"pub fn {name}(nums: &str) -> i32 {{\n{parse_csv_expr('rust', 'nums')}    values.iter().filter(|&&v| v >= {threshold}).count() as i32\n}}"
    const = {"i": i, "threshold": threshold}
    return Problem(name, f"Return how many comma-separated integers are at least `{threshold}`.", "int", [{"name": "nums", "type": "string"}], c, java, rust, build_tests("array_count", const, lambda x: sum(v >= threshold for v in csv_to_list(x["nums"]))), "internal", "array_count_between", "threshold-count-ge", const)


def count_le(i: int) -> Problem:
    threshold = i % 19 - 9
    name = f"aug_count_le_{i:03d}"
    c = f"int {name}(const char *nums) {{\n{parse_csv_expr('c', 'nums')}    int count = 0;\n    for (int j = 0; j < n; j++) if (values[j] <= {threshold}) count++;\n    return count;\n}}"
    java = f"class {java_class(name)} {{\n    public static int {name}(String nums) {{\n{parse_csv_expr('java', 'nums')}        int count = 0;\n        for (String p : parts) if (Integer.parseInt(p) <= {threshold}) count++;\n        return count;\n    }}\n}}"
    rust = f"pub fn {name}(nums: &str) -> i32 {{\n{parse_csv_expr('rust', 'nums')}    values.iter().filter(|&&v| v <= {threshold}).count() as i32\n}}"
    const = {"i": i, "threshold": threshold}
    return Problem(name, f"Return how many comma-separated integers are at most `{threshold}`.", "int", [{"name": "nums", "type": "string"}], c, java, rust, build_tests("array_count", const, lambda x: sum(v <= threshold for v in csv_to_list(x["nums"]))), "internal", "array_count_between", "threshold-count-le", const)


def first_ge(i: int) -> Problem:
    threshold = i % 13 - 6
    name = f"aug_first_ge_{i:03d}"
    c = f"int {name}(const char *nums) {{\n{parse_csv_expr('c', 'nums')}    for (int j = 0; j < n; j++) if (values[j] >= {threshold}) return j;\n    return -1;\n}}"
    java = f"class {java_class(name)} {{\n    public static int {name}(String nums) {{\n{parse_csv_expr('java', 'nums')}        for (int j = 0; j < parts.length; j++) if (Integer.parseInt(parts[j]) >= {threshold}) return j;\n        return -1;\n    }}\n}}"
    rust = f"pub fn {name}(nums: &str) -> i32 {{\n{parse_csv_expr('rust', 'nums')}    for i in 0..values.len() {{ if values[i] >= {threshold} {{ return i as i32; }} }}\n    -1\n}}"
    const = {"i": i, "threshold": threshold}
    return Problem(name, f"Return the first index whose value is at least `{threshold}`, or `-1`.", "int", [{"name": "nums", "type": "string"}], c, java, rust, build_tests("array_find", const, lambda x: next((k for k, v in enumerate(csv_to_list(x["nums"])) if v >= threshold), -1)), "internal", "find_first_equal", "first-index-ge", const)


def last_le(i: int) -> Problem:
    threshold = i % 11 - 5
    name = f"aug_last_le_{i:03d}"
    c = f"int {name}(const char *nums) {{\n{parse_csv_expr('c', 'nums')}    int last = -1;\n    for (int j = 0; j < n; j++) if (values[j] <= {threshold}) last = j;\n    return last;\n}}"
    java = f"class {java_class(name)} {{\n    public static int {name}(String nums) {{\n{parse_csv_expr('java', 'nums')}        int last = -1;\n        for (int j = 0; j < parts.length; j++) if (Integer.parseInt(parts[j]) <= {threshold}) last = j;\n        return last;\n    }}\n}}"
    rust = f"pub fn {name}(nums: &str) -> i32 {{\n{parse_csv_expr('rust', 'nums')}    let mut last = -1;\n    for i in 0..values.len() {{ if values[i] <= {threshold} {{ last = i as i32; }} }}\n    last\n}}"
    const = {"i": i, "threshold": threshold}
    return Problem(name, f"Return the last index whose value is at most `{threshold}`, or `-1`.", "int", [{"name": "nums", "type": "string"}], c, java, rust, build_tests("array_find", const, lambda x: last_index([v <= threshold for v in csv_to_list(x["nums"])])), "internal", "array_find_last_equal", "last-index-le", const)


def sum_prefix(i: int) -> Problem:
    limit = i % 8
    name = f"aug_sum_prefix_{i:03d}"
    c = f"int {name}(const char *nums) {{\n{parse_csv_expr('c', 'nums')}    int sum = 0;\n    int stop = n < {limit} ? n : {limit};\n    for (int j = 0; j < stop; j++) sum += values[j];\n    return sum;\n}}"
    java = f"class {java_class(name)} {{\n    public static int {name}(String nums) {{\n{parse_csv_expr('java', 'nums')}        int sum = 0;\n        int stop = parts.length < {limit} ? parts.length : {limit};\n        for (int j = 0; j < stop; j++) sum += Integer.parseInt(parts[j]);\n        return sum;\n    }}\n}}"
    rust = f"pub fn {name}(nums: &str) -> i32 {{\n{parse_csv_expr('rust', 'nums')}    values.iter().take({limit}).sum()\n}}"
    const = {"i": i, "limit": limit}
    return Problem(name, f"Return the sum of the first `{limit}` encoded integers, or fewer if the input is shorter.", "int", [{"name": "nums", "type": "string"}], c, java, rust, build_tests("array_prefix_sum", const, lambda x: sum(csv_to_list(x["nums"])[:limit])), "internal", "prefix_sum", "fixed-prefix-sum", const)


def all_mod(i: int) -> Problem:
    mod = i % 9 + 2
    name = f"aug_all_multiple_{i:03d}"
    c = f"int {name}(const char *nums) {{\n{parse_csv_expr('c', 'nums')}    for (int j = 0; j < n; j++) if (values[j] % {mod} != 0) return 0;\n    return 1;\n}}"
    java = f"class {java_class(name)} {{\n    public static boolean {name}(String nums) {{\n{parse_csv_expr('java', 'nums')}        for (String p : parts) if (Integer.parseInt(p) % {mod} != 0) return false;\n        return true;\n    }}\n}}"
    rust = f"pub fn {name}(nums: &str) -> bool {{\n{parse_csv_expr('rust', 'nums')}    values.iter().all(|v| v % {mod} == 0)\n}}"
    const = {"i": i, "mod": mod}
    return Problem(name, f"Return true if every encoded integer is divisible by `{mod}`. The empty array returns true.", "bool", [{"name": "nums", "type": "string"}], c, java, rust, build_tests("array_all", const, lambda x: all(v % mod == 0 for v in csv_to_list(x["nums"]))), "internal", "array_all_even", "fixed-divisibility-all", const)


def replace_value(i: int) -> Problem:
    old = i % 9 - 4
    new = (i * 3) % 11 - 5
    name = f"aug_replace_value_{i:03d}"
    c = f"char *{name}(const char *nums) {{\n{parse_csv_expr('c', 'nums')}    char *out = (char *)malloc(1024);\n    int pos = 0;\n    for (int j = 0; j < n; j++) {{ int v = values[j] == {old} ? {new} : values[j]; pos += sprintf(out + pos, \"%s%d\", j == 0 ? \"\" : \",\", v); }}\n    out[pos] = '\\0';\n    return out;\n}}"
    java = f"class {java_class(name)} {{\n    public static String {name}(String nums) {{\n{parse_csv_expr('java', 'nums')}        StringBuilder out = new StringBuilder();\n        for (int j = 0; j < parts.length; j++) {{ int v = Integer.parseInt(parts[j]); if (v == {old}) v = {new}; if (out.length() > 0) out.append(','); out.append(v); }}\n        return out.toString();\n    }}\n}}"
    rust = f"pub fn {name}(nums: &str) -> String {{\n{parse_csv_expr('rust', 'nums')}    let mut out: Vec<String> = Vec::new();\n    for v in values {{ let x = if v == {old} {{ {new} }} else {{ v }}; out.push(x.to_string()); }}\n    out.join(\",\")\n}}"
    const = {"i": i, "old": old, "new": new}
    return Problem(name, f"Replace every `{old}` value in the encoded integer list with `{new}` and return the encoded list.", "string", [{"name": "nums", "type": "string"}], c, java, rust, build_tests("array_replace", const, lambda x: csv([new if v == old else v for v in csv_to_list(x["nums"])])), "internal", "array_replace_k", "fixed-value-replace", const)


def drop_value(i: int) -> Problem:
    value = i % 15 - 7
    name = f"aug_drop_value_list_{i:03d}"
    c = f"char *{name}(const char *nums) {{\n{parse_csv_expr('c', 'nums')}    char *out = (char *)malloc(1024);\n    int pos = 0;\n    int first = 1;\n    for (int j = 0; j < n; j++) if (values[j] != {value}) {{ pos += sprintf(out + pos, \"%s%d\", first ? \"\" : \",\", values[j]); first = 0; }}\n    out[pos] = '\\0';\n    return out;\n}}"
    java = f"class {java_class(name)} {{\n    public static String {name}(String nums) {{\n{parse_csv_expr('java', 'nums')}        StringBuilder out = new StringBuilder();\n        for (String p : parts) {{ int v = Integer.parseInt(p); if (v != {value}) {{ if (out.length() > 0) out.append(','); out.append(v); }} }}\n        return out.toString();\n    }}\n}}"
    rust = f"pub fn {name}(nums: &str) -> String {{\n{parse_csv_expr('rust', 'nums')}    values.into_iter().filter(|&v| v != {value}).map(|v| v.to_string()).collect::<Vec<String>>().join(\",\")\n}}"
    const = {"i": i, "value": value}
    return Problem(name, f"Remove every `{value}` value from the encoded linked-list-style integer list.", "string", [{"name": "nums", "type": "string"}], c, java, rust, build_tests("list_drop", const, lambda x: csv([v for v in csv_to_list(x["nums"]) if v != value])), "external", "remove_element_count_csv", "linked-list-drop-fixed-value", const)


def string_count_char(i: int) -> Problem:
    ch = chr(ord("a") + i % 26)
    name = f"aug_string_count_{i:03d}"
    c = f"int {name}(const char *s) {{\n    int count = 0;\n    for (int i = 0; s[i] != '\\0'; i++) if (s[i] == '{ch}') count++;\n    return count;\n}}"
    java = f"class {java_class(name)} {{\n    public static int {name}(String s) {{\n        int count = 0;\n        for (int i = 0; i < s.length(); i++) if (s.charAt(i) == '{ch}') count++;\n        return count;\n    }}\n}}"
    rust = f"pub fn {name}(s: &str) -> i32 {{\n    s.bytes().filter(|&b| b == b'{ch}').count() as i32\n}}"
    const = {"i": i, "char": ch}
    return Problem(name, f"Return the number of `{ch}` characters in `s`.", "int", [{"name": "s", "type": "string"}], c, java, rust, build_tests("string_count", const, lambda x: x["s"].count(ch)), "internal", "string_count_char", "fixed-character-count", const)


def string_count_char_pointer(i: int) -> Problem:
    ch = chr(ord("a") + i % 26)
    name = f"aug_string_count_ptr_{i:03d}"
    c = f"int {name}(const char *s) {{\n    int count = 0;\n    const char *p = s;\n    while (*p != '\\0') {{\n        if (*p == '{ch}') count++;\n        p++;\n    }}\n    return count;\n}}"
    java = f"class {java_class(name)} {{\n    public static int {name}(String s) {{\n        int count = 0;\n        int i = 0;\n        while (i < s.length()) {{\n            if (s.charAt(i) == '{ch}') count++;\n            i++;\n        }}\n        return count;\n    }}\n}}"
    rust = f"pub fn {name}(s: &str) -> i32 {{\n    let bytes = s.as_bytes();\n    let mut count = 0;\n    let mut i = 0;\n    while i < bytes.len() {{\n        if bytes[i] == b'{ch}' {{ count += 1; }}\n        i += 1;\n    }}\n    count\n}}"
    const = {"i": i, "char": ch, "implementation_strategy": "pointer-walk"}
    return Problem(name, f"Return the number of `{ch}` characters in `s` using a pointer-walk style C implementation.", "int", [{"name": "s", "type": "string"}], c, java, rust, build_tests("string_count", const, lambda x: x["s"].count(ch)), "internal", "string_count_char", "fixed-character-count-pointer-walk", const)


def string_remove_char(i: int) -> Problem:
    ch = chr(ord("a") + (i * 7) % 26)
    name = f"aug_string_remove_{i:03d}"
    c = f"char *{name}(const char *s) {{\n    int n = 0;\n    while (s[n] != '\\0') n++;\n    char *out = (char *)malloc((unsigned long)n + 1);\n    int pos = 0;\n    for (int i = 0; s[i] != '\\0'; i++) if (s[i] != '{ch}') out[pos++] = s[i];\n    out[pos] = '\\0';\n    return out;\n}}"
    java = f"class {java_class(name)} {{\n    public static String {name}(String s) {{\n        StringBuilder out = new StringBuilder();\n        for (int i = 0; i < s.length(); i++) if (s.charAt(i) != '{ch}') out.append(s.charAt(i));\n        return out.toString();\n    }}\n}}"
    rust = f"pub fn {name}(s: &str) -> String {{\n    s.chars().filter(|&c| c != '{ch}').collect()\n}}"
    const = {"i": i, "char": ch}
    return Problem(name, f"Return `s` with every `{ch}` character removed.", "string", [{"name": "s", "type": "string"}], c, java, rust, build_tests("string_remove", const, lambda x: x["s"].replace(ch, "")), "internal", "string_remove_char_to_output", "fixed-character-remove", const)


def csv_to_list(s: str) -> list[int]:
    if not s:
        return []
    return [int(x) for x in s.split(",")]


def last_index(flags: list[bool]) -> int:
    ans = -1
    for i, ok in enumerate(flags):
        if ok:
            ans = i
    return ans


FAMILIES = [count_ge, count_le, first_ge, last_le, sum_prefix, all_mod, replace_value, drop_value, string_count_char, string_remove_char]


def generate() -> list[Problem]:
    problems: list[Problem] = []
    for i in range(TARGET_PROBLEMS // len(FAMILIES)):
        for family in FAMILIES:
            problems.append(family(i))
    return problems[:TARGET_PROBLEMS]


def rename_problem(p: Problem, new_name: str, strategy: str) -> Problem:
    old_name = p.name
    p.c = p.c.replace(old_name, new_name)
    p.java = p.java.replace(java_class(old_name), java_class(new_name)).replace(old_name, new_name)
    p.rust = p.rust.replace(old_name, new_name)
    p.name = new_name
    p.variant_kind = f"{p.variant_kind}-{strategy}"
    p.constants = {**p.constants, "implementation_strategy": strategy}
    return p


def stream_count_ge(i: int) -> Problem:
    threshold = i % 17 - 8
    name = f"aug_count_ge_stream_{i:03d}"
    c = f"int {name}(const char *nums) {{\n    int count = 0;\n    int i = 0;\n    while (nums[i] != '\\0') {{\n        int sign = 1;\n        if (nums[i] == '-') {{ sign = -1; i++; }}\n        int v = 0;\n        while (nums[i] >= '0' && nums[i] <= '9') {{ v = v * 10 + nums[i] - '0'; i++; }}\n        if (sign * v >= {threshold}) count++;\n        if (nums[i] == ',') i++;\n    }}\n    return count;\n}}"
    java = f"class {java_class(name)} {{\n    public static int {name}(String nums) {{\n        int count = 0;\n        int i = 0;\n        while (i < nums.length()) {{\n            int sign = 1;\n            if (nums.charAt(i) == '-') {{ sign = -1; i++; }}\n            int v = 0;\n            while (i < nums.length() && nums.charAt(i) >= '0' && nums.charAt(i) <= '9') {{ v = v * 10 + nums.charAt(i) - '0'; i++; }}\n            if (sign * v >= {threshold}) count++;\n            if (i < nums.length() && nums.charAt(i) == ',') i++;\n        }}\n        return count;\n    }}\n}}"
    rust = f"pub fn {name}(nums: &str) -> i32 {{\n    if nums.is_empty() {{ return 0; }}\n    let mut count = 0;\n    for p in nums.split(',') {{ if p.parse::<i32>().unwrap() >= {threshold} {{ count += 1; }} }}\n    count\n}}"
    const = {"i": i, "threshold": threshold, "implementation_strategy": "streaming-no-array"}
    return Problem(name, f"Return how many comma-separated integers are at least `{threshold}` using a streaming/no-array implementation.", "int", [{"name": "nums", "type": "string"}], c, java, rust, build_tests("array_count", const, lambda x: sum(v >= threshold for v in csv_to_list(x["nums"]))), "internal", "array_count_between", "threshold-count-ge-streaming-no-array", const)


def stream_first_ge(i: int) -> Problem:
    threshold = i % 13 - 6
    name = f"aug_first_ge_stream_{i:03d}"
    c = f"int {name}(const char *nums) {{\n    int idx = 0;\n    int i = 0;\n    while (nums[i] != '\\0') {{\n        int sign = 1;\n        if (nums[i] == '-') {{ sign = -1; i++; }}\n        int v = 0;\n        while (nums[i] >= '0' && nums[i] <= '9') {{ v = v * 10 + nums[i] - '0'; i++; }}\n        if (sign * v >= {threshold}) return idx;\n        idx++;\n        if (nums[i] == ',') i++;\n    }}\n    return -1;\n}}"
    java = f"class {java_class(name)} {{\n    public static int {name}(String nums) {{\n        int idx = 0;\n        int i = 0;\n        while (i < nums.length()) {{\n            int sign = 1;\n            if (nums.charAt(i) == '-') {{ sign = -1; i++; }}\n            int v = 0;\n            while (i < nums.length() && nums.charAt(i) >= '0' && nums.charAt(i) <= '9') {{ v = v * 10 + nums.charAt(i) - '0'; i++; }}\n            if (sign * v >= {threshold}) return idx;\n            idx++;\n            if (i < nums.length() && nums.charAt(i) == ',') i++;\n        }}\n        return -1;\n    }}\n}}"
    rust = f"pub fn {name}(nums: &str) -> i32 {{\n    if nums.is_empty() {{ return -1; }}\n    for (i, p) in nums.split(',').enumerate() {{ if p.parse::<i32>().unwrap() >= {threshold} {{ return i as i32; }} }}\n    -1\n}}"
    const = {"i": i, "threshold": threshold, "implementation_strategy": "streaming-no-array"}
    return Problem(name, f"Return the first index whose encoded value is at least `{threshold}` using a streaming/no-array implementation.", "int", [{"name": "nums", "type": "string"}], c, java, rust, build_tests("array_find", const, lambda x: next((k for k, v in enumerate(csv_to_list(x["nums"])) if v >= threshold), -1)), "internal", "find_first_equal", "first-index-ge-streaming-no-array", const)


def stream_sum_prefix(i: int) -> Problem:
    limit = i % 8
    name = f"aug_sum_prefix_stream_{i:03d}"
    c = f"int {name}(const char *nums) {{\n    int idx = 0;\n    int sum = 0;\n    int i = 0;\n    while (nums[i] != '\\0') {{\n        int sign = 1;\n        if (nums[i] == '-') {{ sign = -1; i++; }}\n        int v = 0;\n        while (nums[i] >= '0' && nums[i] <= '9') {{ v = v * 10 + nums[i] - '0'; i++; }}\n        if (idx < {limit}) sum += sign * v;\n        idx++;\n        if (nums[i] == ',') i++;\n    }}\n    return sum;\n}}"
    java = f"class {java_class(name)} {{\n    public static int {name}(String nums) {{\n        int idx = 0, sum = 0, i = 0;\n        while (i < nums.length()) {{\n            int sign = 1;\n            if (nums.charAt(i) == '-') {{ sign = -1; i++; }}\n            int v = 0;\n            while (i < nums.length() && nums.charAt(i) >= '0' && nums.charAt(i) <= '9') {{ v = v * 10 + nums.charAt(i) - '0'; i++; }}\n            if (idx < {limit}) sum += sign * v;\n            idx++;\n            if (i < nums.length() && nums.charAt(i) == ',') i++;\n        }}\n        return sum;\n    }}\n}}"
    rust = f"pub fn {name}(nums: &str) -> i32 {{\n    if nums.is_empty() {{ return 0; }}\n    nums.split(',').take({limit}).map(|p| p.parse::<i32>().unwrap()).sum()\n}}"
    const = {"i": i, "limit": limit, "implementation_strategy": "streaming-no-array"}
    return Problem(name, f"Return the sum of the first `{limit}` encoded integers using a streaming/no-array implementation.", "int", [{"name": "nums", "type": "string"}], c, java, rust, build_tests("array_prefix_sum", const, lambda x: sum(csv_to_list(x["nums"])[:limit])), "internal", "prefix_sum", "fixed-prefix-sum-streaming-no-array", const)


def stream_all_mod(i: int) -> Problem:
    mod = i % 9 + 2
    name = f"aug_all_multiple_stream_{i:03d}"
    c = f"int {name}(const char *nums) {{\n    int i = 0;\n    while (nums[i] != '\\0') {{\n        int sign = 1;\n        if (nums[i] == '-') {{ sign = -1; i++; }}\n        int v = 0;\n        while (nums[i] >= '0' && nums[i] <= '9') {{ v = v * 10 + nums[i] - '0'; i++; }}\n        if ((sign * v) % {mod} != 0) return 0;\n        if (nums[i] == ',') i++;\n    }}\n    return 1;\n}}"
    java = f"class {java_class(name)} {{\n    public static boolean {name}(String nums) {{\n        int i = 0;\n        while (i < nums.length()) {{\n            int sign = 1;\n            if (nums.charAt(i) == '-') {{ sign = -1; i++; }}\n            int v = 0;\n            while (i < nums.length() && nums.charAt(i) >= '0' && nums.charAt(i) <= '9') {{ v = v * 10 + nums.charAt(i) - '0'; i++; }}\n            if ((sign * v) % {mod} != 0) return false;\n            if (i < nums.length() && nums.charAt(i) == ',') i++;\n        }}\n        return true;\n    }}\n}}"
    rust = f"pub fn {name}(nums: &str) -> bool {{\n    if nums.is_empty() {{ return true; }}\n    nums.split(',').all(|p| p.parse::<i32>().unwrap() % {mod} == 0)\n}}"
    const = {"i": i, "mod": mod, "implementation_strategy": "streaming-no-array"}
    return Problem(name, f"Return true if every encoded integer is divisible by `{mod}` using a streaming/no-array implementation.", "bool", [{"name": "nums", "type": "string"}], c, java, rust, build_tests("array_all", const, lambda x: all(v % mod == 0 for v in csv_to_list(x["nums"]))), "internal", "array_all_even", "fixed-divisibility-all-streaming-no-array", const)


def stream_drop_value(i: int) -> Problem:
    value = i % 15 - 7
    name = f"aug_drop_value_stream_{i:03d}"
    c = f"char *{name}(const char *nums) {{\n    char *out = (char *)malloc(1024);\n    int pos = 0;\n    int first = 1;\n    int i = 0;\n    while (nums[i] != '\\0') {{\n        int sign = 1;\n        if (nums[i] == '-') {{ sign = -1; i++; }}\n        int v = 0;\n        while (nums[i] >= '0' && nums[i] <= '9') {{ v = v * 10 + nums[i] - '0'; i++; }}\n        v *= sign;\n        if (v != {value}) {{ pos += sprintf(out + pos, \"%s%d\", first ? \"\" : \",\", v); first = 0; }}\n        if (nums[i] == ',') i++;\n    }}\n    out[pos] = '\\0';\n    return out;\n}}"
    java = f"class {java_class(name)} {{\n    public static String {name}(String nums) {{\n        StringBuilder out = new StringBuilder();\n        int i = 0;\n        while (i < nums.length()) {{\n            int sign = 1;\n            if (nums.charAt(i) == '-') {{ sign = -1; i++; }}\n            int v = 0;\n            while (i < nums.length() && nums.charAt(i) >= '0' && nums.charAt(i) <= '9') {{ v = v * 10 + nums.charAt(i) - '0'; i++; }}\n            v *= sign;\n            if (v != {value}) {{ if (out.length() > 0) out.append(','); out.append(v); }}\n            if (i < nums.length() && nums.charAt(i) == ',') i++;\n        }}\n        return out.toString();\n    }}\n}}"
    rust = f"pub fn {name}(nums: &str) -> String {{\n    if nums.is_empty() {{ return String::new(); }}\n    nums.split(',').filter_map(|p| {{ let v = p.parse::<i32>().unwrap(); if v == {value} {{ None }} else {{ Some(v.to_string()) }} }}).collect::<Vec<String>>().join(\",\")\n}}"
    const = {"i": i, "value": value, "implementation_strategy": "streaming-no-array"}
    return Problem(name, f"Remove every `{value}` value from the encoded linked-list-style integer list using a streaming/no-array implementation.", "string", [{"name": "nums", "type": "string"}], c, java, rust, build_tests("list_drop", const, lambda x: csv([v for v in csv_to_list(x["nums"]) if v != value])), "external", "remove_element_count_csv", "linked-list-drop-fixed-value-streaming-no-array", const)


def representative_generate() -> list[Problem]:
    return [
        rename_problem(count_ge(0), "aug_count_ge_array_000", "array-backed"),
        stream_count_ge(0),
        rename_problem(first_ge(1), "aug_first_ge_array_001", "array-backed"),
        stream_first_ge(1),
        rename_problem(sum_prefix(2), "aug_sum_prefix_array_002", "array-backed"),
        stream_sum_prefix(2),
        rename_problem(all_mod(3), "aug_all_multiple_array_003", "array-backed"),
        stream_all_mod(3),
        rename_problem(string_count_char(4), "aug_string_count_index_004", "index-scan"),
        string_count_char_pointer(4),
        rename_problem(count_le(5), "aug_count_le_array_005", "array-backed"),
        rename_problem(last_le(6), "aug_last_le_array_006", "array-backed"),
        rename_problem(count_ge(7), "aug_count_ge_array_007", "array-backed"),
        stream_count_ge(7),
    ][:TARGET_PROBLEMS]


def generate() -> list[Problem]:
    return representative_generate()


def main() -> int:
    shutil.rmtree(OUT, ignore_errors=True)
    for sub in ("c", "java", "rust", "tests"):
        (OUT / sub).mkdir(parents=True, exist_ok=True)
    manifest = {
        "source": "Augmented local variants of datasets/internal and datasets/external",
        "style": "HumanEval-like augment",
        "not_used": ["HumanEval", "MBPP"],
        "languages": ["c", "java", "rust"],
        "requirements": ["single function", "standard library only", "shared tests", "records parent problem and variant kind"],
        "problems": [],
    }
    for p in generate():
        for lang, code in (("c", p.c), ("java", p.java), ("rust", p.rust)):
            (OUT / lang / f"{p.name}.md").write_text(md(p, lang, code), encoding="utf-8")
        spec = {
            "name": p.name,
            "return_type": p.return_type,
            "params": p.params,
            "tests": p.tests,
            "augment": {
                "parent_dataset": p.parent_dataset,
                "parent_problem": p.parent_problem,
                "variant_kind": p.variant_kind,
                "constants": p.constants,
            },
        }
        (OUT / "tests" / f"{p.name}.json").write_text(json.dumps(spec, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
        manifest["problems"].append({"name": p.name, **spec["augment"]})
    (OUT / "manifest.json").write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    (OUT / "README.md").write_text(
        "# Augment Dataset\n\n"
        f"- Problems: {len(manifest['problems'])}\n"
        "- Purpose: record same-problem implementation variants and small variants of problems from `datasets/internal` and `datasets/external`.\n"
        "- Languages: C, Java, Rust\n"
        "- Tests: shared JSON files in `tests/`, exactly 10 cases per problem\n"
        "- Metadata: each test spec and manifest entry records `parent_dataset`, `parent_problem`, `variant_kind`, and constants\n"
        "- Generation: `python3 scripts/generate_augment_dataset.py`\n"
        "- Validation: `python3 scripts/validate_augment_dataset.py`\n",
        encoding="utf-8",
    )
    print(f"generated {len(manifest['problems'])} augment problems under {OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

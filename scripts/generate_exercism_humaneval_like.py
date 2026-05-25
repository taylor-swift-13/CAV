#!/usr/bin/env python3
"""Generate Exercism-inspired HumanEval-like single-function tasks.

The prompts are short rewrites of beginner-friendly Exercism exercises.  The
implementations are deliberately single-function per language and use only the
standard library.  Each problem has one shared JSON test suite used for C,
Java, and Rust validation.
"""

from __future__ import annotations

import json
import shutil
from copy import deepcopy
from dataclasses import dataclass, field
from pathlib import Path
import re


REPO_ROOT = Path(__file__).resolve().parents[1]
OUT = REPO_ROOT / "datasets" / "external"
EXERCISM_SPECS = REPO_ROOT / ".tools" / "exercism_sources" / "problem-specifications" / "exercises"
TARGET_CASES_PER_PROBLEM = 10

QCP_SCOPE_PATTERNS = {
    "c": [
        r"\bprintf\b",
        r"\bscanf\b",
        r"\bfopen\b",
        r"\bfread\b",
        r"\bfwrite\b",
        r"\bfclose\b",
        r"\brand\b",
        r"\bsrand\b",
        r"\btime\b",
        r"\bsystem\b",
        r"\bpthread_",
    ],
}

QCP_MOCK_CONTRACT_PATTERNS = {
    "c": [
        r"\bsprintf\b",
        r"\bsnprintf\b",
        r"\batoi\b",
        r"\bstrtol\b",
        r"\bstrtok\b",
        r"\bqsort\b",
    ],
}


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
    source_slug: str
    requirements: list[str] = field(default_factory=list)


def java_class(name: str) -> str:
    return "".join(part.capitalize() for part in name.split("_"))


def md(problem: Problem, lang: str, code: str) -> str:
    if problem.source_slug.startswith("local:"):
        source_lines = (
            f"- Source: local simple-function seed `{problem.source_slug[6:]}`.\n"
            "- URL: local dataset seed, no upstream problem URL.\n"
            "- License note: prompt and implementation are local to this repository.\n"
        )
    elif problem.source_slug.startswith("leetcode:"):
        slug = problem.source_slug.split(":", 1)[1]
        source_lines = (
            f"- Source: LeetCode problem `{slug}`.\n"
            f"- URL: https://leetcode.com/problems/{slug}/\n"
            "- License note: this is a local single-function rewrite; do not copy upstream statement text.\n"
        )
    elif problem.source_slug.startswith("luogu:"):
        pid = problem.source_slug.split(":", 1)[1]
        source_lines = (
            f"- Source: Luogu problem `{pid}`.\n"
            f"- URL: https://www.luogu.com.cn/problem/{pid}\n"
            "- License note: this is a local single-function rewrite; do not copy upstream statement text.\n"
        )
    elif problem.source_slug.startswith("formalbench:"):
        slug = problem.source_slug.split(":", 1)[1]
        source_lines = (
            f"- Source: FormalBench-inspired program `{slug}`.\n"
            "- URL: https://github.com/thanhlecongg/FormalBench/\n"
            "- Data URL: https://huggingface.co/datasets/FormalBench/FormalBench\n"
            "- License note: this is a local HumanEval-like rewrite for C/Java/Rust shared tests.\n"
        )
    else:
        source_lines = (
            f"- Source: Exercism practice exercise `{problem.source_slug}`.\n"
            f"- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/{problem.source_slug}\n"
            "- License note: prompt rewrite and implementations are local; upstream inspiration is Exercism MIT licensed.\n"
        )
    reqs = problem.requirements or [
        "Implement exactly the named function shown in the reference implementation.",
        "Use only the language standard library.",
        "The function must be deterministic and must not read stdin or write stdout.",
        "Inputs satisfy the stated problem preconditions; behavior outside those preconditions is intentionally unspecified.",
    ]
    requirement_lines = "\n".join(f"- {line}" for line in reqs)
    return (
        f"# {problem.name}\n\n"
        "## Problem\n\n"
        f"{problem.prompt}\n\n"
        "## Requirements\n\n"
        f"{requirement_lines}\n\n"
        "## Source\n\n"
        f"{source_lines}"
        "- Style: HumanEval-like short single-function task; not HumanEval or MBPP.\n\n"
        "## Reference Implementation\n\n"
        f"```{lang}\n{code.rstrip()}\n```\n"
    )


INPUT_RENAMES = {
    "hamming_distance": {"strand1": "a", "strand2": "b"},
    "collatz_steps": {"number": "n"},
    "armstrong_number": {"number": "n"},
}


def official_tests(problem_name: str, slug: str) -> list[dict]:
    path = EXERCISM_SPECS / slug / "canonical-data.json"
    data = json.loads(path.read_text(encoding="utf-8"))
    renames = INPUT_RENAMES.get(problem_name, {})
    out = []
    negative_count = 0
    for case in data["cases"]:
        expected = case["expected"]
        if isinstance(expected, dict):
            continue
        inp = {renames.get(k, k): v for k, v in case["input"].items()}
        if any(isinstance(v, int) and not (-2147483648 <= v <= 2147483647) for v in inp.values()):
            continue
        kind = "positive"
        if expected is False or expected == 0 or expected == "":
            if negative_count < 3:
                kind = "negative"
                negative_count += 1
        out.append({
            "kind": kind,
            "input": inp,
            "expected": expected,
            "source_case": {
                "uuid": case.get("uuid"),
                "description": case.get("description"),
                "property": case.get("property"),
                "file": f"problem-specifications/exercises/{slug}/canonical-data.json"
            }
        })
    return out


def source_meta(source_slug: str) -> dict:
    if source_slug.startswith("local:"):
        return {"name": "local", "slug": source_slug, "url": None, "license": "local repo"}
    if source_slug.startswith("leetcode:"):
        slug = source_slug.split(":", 1)[1]
        return {"name": "LeetCode", "slug": slug, "url": f"https://leetcode.com/problems/{slug}/", "license": "local rewrite"}
    if source_slug.startswith("luogu:"):
        pid = source_slug.split(":", 1)[1]
        return {"name": "Luogu", "slug": pid, "url": f"https://www.luogu.com.cn/problem/{pid}", "license": "local rewrite"}
    if source_slug.startswith("formalbench:"):
        slug = source_slug.split(":", 1)[1]
        return {"name": "FormalBench", "slug": slug, "url": "https://github.com/thanhlecongg/FormalBench/", "license": "local rewrite"}
    return {
        "name": "Exercism",
        "slug": source_slug,
        "url": f"https://github.com/exercism/problem-specifications/tree/main/exercises/{source_slug}",
        "license": "MIT",
    }


def qcp_scope_violations(problem: Problem) -> list[str]:
    """Return C/QCP red flags that make a problem unsuitable for this batch.

    The dataset admission gate is: the three implementations must agree on the
    shared tests, and the C implementation must stay inside QCP-supported C.
    Java/Rust are translations of the C behavior and are not hard filters here.
    """

    violations: list[str] = []
    for pattern in QCP_SCOPE_PATTERNS["c"]:
        if re.search(pattern, problem.c):
            violations.append(f"c:{pattern}")
    return violations


def qcp_mock_contract_needs(problem: Problem) -> list[str]:
    needs: list[str] = []
    for pattern in QCP_MOCK_CONTRACT_PATTERNS["c"]:
        if re.search(pattern, problem.c):
            needs.append(f"c:{pattern}")
    return needs


def problems() -> list[Problem]:
    return [
        Problem(
            "leap_year",
            "Return true if `year` is a leap year in the Gregorian calendar.",
            "bool",
            [{"name": "year", "type": "int"}],
            "int leap_year(int year) {\n    if (year % 400 == 0) return 1;\n    if (year % 100 == 0) return 0;\n    return year % 4 == 0;\n}",
            "class LeapYear {\n    public static boolean leap_year(int year) {\n        if (year % 400 == 0) return true;\n        if (year % 100 == 0) return false;\n        return year % 4 == 0;\n    }\n}",
            "pub fn leap_year(year: i32) -> bool {\n    if year % 400 == 0 { return true; }\n    if year % 100 == 0 { return false; }\n    year % 4 == 0\n}",
            official_tests("leap_year", "leap"),
            "leap",
        ),
        Problem(
            "hamming_distance",
            "Return the number of positions where equal-length strings `a` and `b` differ.",
            "int",
            [{"name": "a", "type": "string"}, {"name": "b", "type": "string"}],
            "int hamming_distance(const char *a, const char *b) {\n    int count = 0;\n    int i = 0;\n    while (a[i] != '\\0' && b[i] != '\\0') {\n        if (a[i] != b[i]) count++;\n        i++;\n    }\n    return count;\n}",
            "class HammingDistance {\n    public static int hamming_distance(String a, String b) {\n        int count = 0;\n        for (int i = 0; i < a.length(); i++) {\n            if (a.charAt(i) != b.charAt(i)) count++;\n        }\n        return count;\n    }\n}",
            "pub fn hamming_distance(a: &str, b: &str) -> i32 {\n    let ab = a.as_bytes();\n    let bb = b.as_bytes();\n    let mut count = 0;\n    let mut i = 0;\n    while i < ab.len() {\n        if ab[i] != bb[i] { count += 1; }\n        i += 1;\n    }\n    count\n}",
            official_tests("hamming_distance", "hamming"),
            "hamming",
        ),
        Problem(
            "rna_transcription",
            "Return the RNA complement of a DNA string using `G->C`, `C->G`, `T->A`, and `A->U`.",
            "string",
            [{"name": "dna", "type": "string"}],
            "char *rna_transcription(const char *dna) {\n    int n = 0;\n    while (dna[n] != '\\0') n++;\n    char *out = (char *)malloc((unsigned long)n + 1);\n    for (int i = 0; i < n; i++) {\n        if (dna[i] == 'G') out[i] = 'C';\n        else if (dna[i] == 'C') out[i] = 'G';\n        else if (dna[i] == 'T') out[i] = 'A';\n        else out[i] = 'U';\n    }\n    out[n] = '\\0';\n    return out;\n}",
            "class RnaTranscription {\n    public static String rna_transcription(String dna) {\n        StringBuilder out = new StringBuilder();\n        for (int i = 0; i < dna.length(); i++) {\n            char c = dna.charAt(i);\n            if (c == 'G') out.append('C');\n            else if (c == 'C') out.append('G');\n            else if (c == 'T') out.append('A');\n            else out.append('U');\n        }\n        return out.toString();\n    }\n}",
            "pub fn rna_transcription(dna: &str) -> String {\n    let mut out = String::new();\n    for c in dna.chars() {\n        if c == 'G' { out.push('C'); }\n        else if c == 'C' { out.push('G'); }\n        else if c == 'T' { out.push('A'); }\n        else { out.push('U'); }\n    }\n    out\n}",
            official_tests("rna_transcription", "rna-transcription"),
            "rna-transcription",
        ),
        Problem(
            "scrabble_score",
            "Return the Scrabble score of an ASCII word. Letter case is ignored.",
            "int",
            [{"name": "word", "type": "string"}],
            "int scrabble_score(const char *word) {\n    int score = 0;\n    for (int i = 0; word[i] != '\\0'; i++) {\n        char c = word[i];\n        if (c >= 'a' && c <= 'z') c = (char)(c - 'a' + 'A');\n        if (c=='A'||c=='E'||c=='I'||c=='O'||c=='U'||c=='L'||c=='N'||c=='R'||c=='S'||c=='T') score += 1;\n        else if (c=='D'||c=='G') score += 2;\n        else if (c=='B'||c=='C'||c=='M'||c=='P') score += 3;\n        else if (c=='F'||c=='H'||c=='V'||c=='W'||c=='Y') score += 4;\n        else if (c=='K') score += 5;\n        else if (c=='J'||c=='X') score += 8;\n        else if (c=='Q'||c=='Z') score += 10;\n    }\n    return score;\n}",
            "class ScrabbleScore {\n    public static int scrabble_score(String word) {\n        int score = 0;\n        for (int i = 0; i < word.length(); i++) {\n            char c = Character.toUpperCase(word.charAt(i));\n            if (\"AEIOULNRST\".indexOf(c) >= 0) score += 1;\n            else if (\"DG\".indexOf(c) >= 0) score += 2;\n            else if (\"BCMP\".indexOf(c) >= 0) score += 3;\n            else if (\"FHVWY\".indexOf(c) >= 0) score += 4;\n            else if (c == 'K') score += 5;\n            else if (\"JX\".indexOf(c) >= 0) score += 8;\n            else if (\"QZ\".indexOf(c) >= 0) score += 10;\n        }\n        return score;\n    }\n}",
            "pub fn scrabble_score(word: &str) -> i32 {\n    let mut score = 0;\n    for b in word.bytes() {\n        let c = if b >= b'a' && b <= b'z' { b - b'a' + b'A' } else { b };\n        if b\"AEIOULNRST\".contains(&c) { score += 1; }\n        else if b\"DG\".contains(&c) { score += 2; }\n        else if b\"BCMP\".contains(&c) { score += 3; }\n        else if b\"FHVWY\".contains(&c) { score += 4; }\n        else if c == b'K' { score += 5; }\n        else if b\"JX\".contains(&c) { score += 8; }\n        else if b\"QZ\".contains(&c) { score += 10; }\n    }\n    score\n}",
            official_tests("scrabble_score", "scrabble-score"),
            "scrabble-score",
        ),
        Problem(
            "collatz_steps",
            "Return the number of Collatz steps needed for positive integer `n` to reach 1.",
            "int",
            [{"name": "n", "type": "int"}],
            "int collatz_steps(int n) {\n    int steps = 0;\n    while (n != 1) {\n        if (n % 2 == 0) n /= 2;\n        else n = 3 * n + 1;\n        steps++;\n    }\n    return steps;\n}",
            "class CollatzSteps {\n    public static int collatz_steps(int n) {\n        int steps = 0;\n        while (n != 1) {\n            if (n % 2 == 0) n /= 2;\n            else n = 3 * n + 1;\n            steps++;\n        }\n        return steps;\n    }\n}",
            "pub fn collatz_steps(mut n: i32) -> i32 {\n    let mut steps = 0;\n    while n != 1 {\n        if n % 2 == 0 { n /= 2; }\n        else { n = 3 * n + 1; }\n        steps += 1;\n    }\n    steps\n}",
            official_tests("collatz_steps", "collatz-conjecture"),
            "collatz-conjecture",
        ),
        Problem(
            "armstrong_number",
            "Return true if `n` equals the sum of its digits each raised to the number of digits.",
            "bool",
            [{"name": "n", "type": "int"}],
            "int armstrong_number(int n) {\n    int temp = n;\n    int digits = 0;\n    if (temp == 0) digits = 1;\n    while (temp > 0) { digits++; temp /= 10; }\n    temp = n;\n    int sum = 0;\n    if (temp == 0) sum = 0;\n    while (temp > 0) {\n        int d = temp % 10;\n        int p = 1;\n        for (int i = 0; i < digits; i++) p *= d;\n        sum += p;\n        temp /= 10;\n    }\n    return sum == n;\n}",
            "class ArmstrongNumber {\n    public static boolean armstrong_number(int n) {\n        int temp = n;\n        int digits = temp == 0 ? 1 : 0;\n        while (temp > 0) { digits++; temp /= 10; }\n        temp = n;\n        int sum = 0;\n        while (temp > 0) {\n            int d = temp % 10;\n            int p = 1;\n            for (int i = 0; i < digits; i++) p *= d;\n            sum += p;\n            temp /= 10;\n        }\n        return sum == n;\n    }\n}",
            "pub fn armstrong_number(n: i32) -> bool {\n    let mut temp = n;\n    let mut digits = if temp == 0 { 1 } else { 0 };\n    while temp > 0 { digits += 1; temp /= 10; }\n    temp = n;\n    let mut sum = 0;\n    while temp > 0 {\n        let d = temp % 10;\n        let mut p = 1;\n        let mut i = 0;\n        while i < digits { p *= d; i += 1; }\n        sum += p;\n        temp /= 10;\n    }\n    sum == n\n}",
            official_tests("armstrong_number", "armstrong-numbers"),
            "armstrong-numbers",
        ),
        Problem(
            "is_even",
            "Return true if integer `n` is divisible by 2; otherwise return false.",
            "bool",
            [{"name": "n", "type": "int"}],
            "int is_even(int n) {\n    return n % 2 == 0;\n}",
            "class IsEven {\n    public static boolean is_even(int n) {\n        return n % 2 == 0;\n    }\n}",
            "pub fn is_even(n: i32) -> bool {\n    n % 2 == 0\n}",
            [
                {"kind": "positive", "input": {"n": 0}, "expected": True},
                {"kind": "positive", "input": {"n": 2}, "expected": True},
                {"kind": "negative", "input": {"n": 3}, "expected": False},
                {"kind": "positive", "input": {"n": -4}, "expected": True},
                {"kind": "negative", "input": {"n": -7}, "expected": False},
            ],
            "local:is-even",
            [
                "`n` is a signed 32-bit integer.",
                "Zero is even and must return true.",
                "Negative values follow normal divisibility by 2; no absolute-value special case is allowed.",
                "The function must not allocate, read stdin, or write stdout.",
            ],
        ),
        Problem(
            "gcd_positive",
            "Return the greatest common divisor of positive integers `a` and `b`.",
            "int",
            [{"name": "a", "type": "int"}, {"name": "b", "type": "int"}],
            "int gcd_positive(int a, int b) {\n    while (b != 0) {\n        int t = a % b;\n        a = b;\n        b = t;\n    }\n    return a;\n}",
            "class GcdPositive {\n    public static int gcd_positive(int a, int b) {\n        while (b != 0) {\n            int t = a % b;\n            a = b;\n            b = t;\n        }\n        return a;\n    }\n}",
            "pub fn gcd_positive(mut a: i32, mut b: i32) -> i32 {\n    while b != 0 {\n        let t = a % b;\n        a = b;\n        b = t;\n    }\n    a\n}",
            [
                {"kind": "positive", "input": {"a": 12, "b": 18}, "expected": 6},
                {"kind": "positive", "input": {"a": 17, "b": 13}, "expected": 1},
                {"kind": "positive", "input": {"a": 100, "b": 25}, "expected": 25},
                {"kind": "positive", "input": {"a": 1, "b": 999}, "expected": 1},
            ],
            "local:gcd-positive",
            [
                "`a > 0` and `b > 0`; zero and negative inputs are outside this task.",
                "Return the largest positive integer that divides both inputs.",
                "When one input divides the other, return the smaller divisor.",
                "The implementation must be iterative or otherwise guaranteed to terminate on 32-bit positive inputs.",
            ],
        ),
        Problem(
            "palindrome_number",
            "Return true if decimal representation of integer `x` reads the same forward and backward.",
            "bool",
            [{"name": "x", "type": "int"}],
            "int palindrome_number(int x) {\n    if (x < 0) return 0;\n    int original = x;\n    int rev = 0;\n    while (x > 0) {\n        rev = rev * 10 + x % 10;\n        x /= 10;\n    }\n    return rev == original;\n}",
            "class PalindromeNumber {\n    public static boolean palindrome_number(int x) {\n        if (x < 0) return false;\n        int original = x;\n        int rev = 0;\n        while (x > 0) {\n            rev = rev * 10 + x % 10;\n            x /= 10;\n        }\n        return rev == original;\n    }\n}",
            "pub fn palindrome_number(mut x: i32) -> bool {\n    if x < 0 { return false; }\n    let original = x;\n    let mut rev = 0;\n    while x > 0 {\n        rev = rev * 10 + x % 10;\n        x /= 10;\n    }\n    rev == original\n}",
            [
                {"kind": "positive", "input": {"x": 0}, "expected": True},
                {"kind": "positive", "input": {"x": 121}, "expected": True},
                {"kind": "negative", "input": {"x": -121}, "expected": False},
                {"kind": "negative", "input": {"x": 10}, "expected": False},
                {"kind": "positive", "input": {"x": 12321}, "expected": True},
            ],
            "leetcode:palindrome-number",
            [
                "`x` is a signed 32-bit integer.",
                "Negative numbers are not palindromes because the minus sign is not mirrored at the end.",
                "Single-digit nonnegative numbers, including zero, are palindromes.",
                "Numbers ending in zero are palindromes only when the number itself is zero.",
                "Return only a boolean result; do not convert invalid inputs or print explanations.",
            ],
        ),
        Problem(
            "valid_palindrome_ascii",
            "Return true if ASCII string `s` is a palindrome after ignoring non-alphanumeric characters and case.",
            "bool",
            [{"name": "s", "type": "string"}],
            "int valid_palindrome_ascii(const char *s) {\n    int r = 0;\n    while (s[r] != '\\0') r++;\n    int l = 0;\n    r--;\n    while (l < r) {\n        char a = s[l];\n        char b = s[r];\n        int aa = (a >= '0' && a <= '9') || (a >= 'A' && a <= 'Z') || (a >= 'a' && a <= 'z');\n        int bb = (b >= '0' && b <= '9') || (b >= 'A' && b <= 'Z') || (b >= 'a' && b <= 'z');\n        if (!aa) { l++; continue; }\n        if (!bb) { r--; continue; }\n        if (a >= 'A' && a <= 'Z') a = (char)(a - 'A' + 'a');\n        if (b >= 'A' && b <= 'Z') b = (char)(b - 'A' + 'a');\n        if (a != b) return 0;\n        l++;\n        r--;\n    }\n    return 1;\n}",
            "class ValidPalindromeAscii {\n    public static boolean valid_palindrome_ascii(String s) {\n        int l = 0;\n        int r = s.length() - 1;\n        while (l < r) {\n            char a = s.charAt(l);\n            char b = s.charAt(r);\n            if (!Character.isLetterOrDigit(a)) { l++; continue; }\n            if (!Character.isLetterOrDigit(b)) { r--; continue; }\n            if (Character.toLowerCase(a) != Character.toLowerCase(b)) return false;\n            l++;\n            r--;\n        }\n        return true;\n    }\n}",
            "pub fn valid_palindrome_ascii(s: &str) -> bool {\n    let bytes = s.as_bytes();\n    if bytes.is_empty() { return true; }\n    let mut l: usize = 0;\n    let mut r: usize = bytes.len() - 1;\n    while l < r {\n        let mut a = bytes[l];\n        let mut b = bytes[r];\n        let aa = a.is_ascii_alphanumeric();\n        let bb = b.is_ascii_alphanumeric();\n        if !aa { l += 1; continue; }\n        if !bb { r -= 1; continue; }\n        a = a.to_ascii_lowercase();\n        b = b.to_ascii_lowercase();\n        if a != b { return false; }\n        l += 1;\n        r -= 1;\n    }\n    true\n}",
            [
                {"kind": "positive", "input": {"s": ""}, "expected": True},
                {"kind": "positive", "input": {"s": "A man, a plan, a canal: Panama"}, "expected": True},
                {"kind": "negative", "input": {"s": "race a car"}, "expected": False},
                {"kind": "positive", "input": {"s": ".,,"}, "expected": True},
                {"kind": "positive", "input": {"s": "0P0"}, "expected": True},
            ],
            "leetcode:valid-palindrome",
            [
                "`s` contains only ASCII characters for this dataset variant.",
                "Ignore every character that is not `[A-Za-z0-9]`.",
                "Letter comparison is case-insensitive; digit comparison is exact.",
                "The empty filtered string is a palindrome and must return true.",
                "The original string must not be modified.",
            ],
        ),
        Problem(
            "two_sum_exists",
            "Return true if two distinct elements in integer array string `nums` sum to `target`.",
            "bool",
            [{"name": "nums", "type": "string"}, {"name": "target", "type": "int"}],
            "int two_sum_exists(const char *nums, int target) {\n    int values[64];\n    int n = 0;\n    int i = 0;\n    while (nums[i] != '\\0') {\n        int sign = 1;\n        if (nums[i] == '-') { sign = -1; i++; }\n        int v = 0;\n        while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; }\n        values[n++] = sign * v;\n        if (nums[i] == ',') i++;\n    }\n    for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) if (values[a] + values[b] == target) return 1;\n    return 0;\n}",
            "class TwoSumExists {\n    public static boolean two_sum_exists(String nums, int target) {\n        String[] parts = nums.isEmpty() ? new String[0] : nums.split(\",\");\n        int[] values = new int[parts.length];\n        for (int i = 0; i < parts.length; i++) values[i] = Integer.parseInt(parts[i]);\n        for (int i = 0; i < values.length; i++) for (int j = i + 1; j < values.length; j++) if (values[i] + values[j] == target) return true;\n        return false;\n    }\n}",
            "pub fn two_sum_exists(nums: &str, target: i32) -> bool {\n    let values: Vec<i32> = if nums.is_empty() { Vec::new() } else { nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect() };\n    let mut i = 0;\n    while i < values.len() {\n        let mut j = i + 1;\n        while j < values.len() {\n            if values[i] + values[j] == target { return true; }\n            j += 1;\n        }\n        i += 1;\n    }\n    false\n}",
            [
                {"kind": "positive", "input": {"nums": "2,7,11,15", "target": 9}, "expected": True},
                {"kind": "positive", "input": {"nums": "3,2,4", "target": 6}, "expected": True},
                {"kind": "positive", "input": {"nums": "3,3", "target": 6}, "expected": True},
                {"kind": "negative", "input": {"nums": "1,2,3", "target": 7}, "expected": False},
                {"kind": "negative", "input": {"nums": "", "target": 0}, "expected": False},
            ],
            "leetcode:two-sum",
            [
                "`nums` is encoded as comma-separated base-10 integers with no spaces.",
                "The empty string represents an empty array.",
                "A valid pair must use two distinct positions, even if the values are equal.",
                "Return only whether such a pair exists; do not return indices.",
                "The number of encoded integers is at most 64 in this dataset variant.",
            ],
        ),
        Problem(
            "apple_purchase_total",
            "Return the total cost for buying `count` apples when each apple costs `price`.",
            "int",
            [{"name": "count", "type": "int"}, {"name": "price", "type": "int"}],
            "int apple_purchase_total(int count, int price) {\n    return count * price;\n}",
            "class ApplePurchaseTotal {\n    public static int apple_purchase_total(int count, int price) {\n        return count * price;\n    }\n}",
            "pub fn apple_purchase_total(count: i32, price: i32) -> i32 {\n    count * price\n}",
            [
                {"kind": "positive", "input": {"count": 1, "price": 1}, "expected": 1},
                {"kind": "positive", "input": {"count": 5, "price": 3}, "expected": 15},
                {"kind": "positive", "input": {"count": 0, "price": 10}, "expected": 0},
                {"kind": "negative", "input": {"count": 7, "price": 0}, "expected": 0},
            ],
            "luogu:P5703",
            [
                "`count >= 0` and `price >= 0`.",
                "The mathematical product is guaranteed to fit in a signed 32-bit integer.",
                "Zero count or zero price must return zero.",
                "No input parsing is part of the function; both values are already provided as integers.",
            ],
        ),
        Problem(
            "uppercase_ascii_letter",
            "Convert a lowercase ASCII letter to uppercase and return it as a one-character string.",
            "string",
            [{"name": "letter", "type": "string"}],
            "char *uppercase_ascii_letter(const char *letter) {\n    char *out = (char *)malloc(2);\n    char c = letter[0];\n    if (c >= 'a' && c <= 'z') c = (char)(c - 'a' + 'A');\n    out[0] = c;\n    out[1] = '\\0';\n    return out;\n}",
            "class UppercaseAsciiLetter {\n    public static String uppercase_ascii_letter(String letter) {\n        char c = letter.charAt(0);\n        if (c >= 'a' && c <= 'z') c = (char)(c - 'a' + 'A');\n        return Character.toString(c);\n    }\n}",
            "pub fn uppercase_ascii_letter(letter: &str) -> String {\n    let b = letter.as_bytes()[0];\n    let c = if b >= b'a' && b <= b'z' { b - b'a' + b'A' } else { b };\n    (c as char).to_string()\n}",
            [
                {"kind": "positive", "input": {"letter": "a"}, "expected": "A"},
                {"kind": "positive", "input": {"letter": "z"}, "expected": "Z"},
                {"kind": "positive", "input": {"letter": "m"}, "expected": "M"},
            ],
            "luogu:P5704",
            [
                "`letter` has length exactly 1.",
                "Official-style inputs are lowercase ASCII letters `a` through `z`.",
                "For robustness in this local variant, a non-lowercase ASCII character would be returned unchanged.",
                "Return a one-character string; do not return an integer code point.",
            ],
        ),
        Problem(
            "number_properties_bits",
            "Return four space-separated bits describing simple divisibility properties of integer `n`.",
            "string",
            [{"name": "n", "type": "int"}],
            "char *number_properties_bits(int n) {\n    int a = (n % 2 == 0);\n    int b = (n > 4 && n <= 12);\n    int b1 = (a && b);\n    int b2 = (a || b);\n    int b3 = (a != b);\n    int b4 = (!a && !b);\n    char *out = (char *)malloc(8);\n    snprintf(out, 8, \"%d %d %d %d\", b1, b2, b3, b4);\n    return out;\n}",
            "class NumberPropertiesBits {\n    public static String number_properties_bits(int n) {\n        boolean a = n % 2 == 0;\n        boolean b = n > 4 && n <= 12;\n        return (a && b ? 1 : 0) + \" \" + (a || b ? 1 : 0) + \" \" + (a ^ b ? 1 : 0) + \" \" + (!a && !b ? 1 : 0);\n    }\n}",
            "pub fn number_properties_bits(n: i32) -> String {\n    let a = n % 2 == 0;\n    let b = n > 4 && n <= 12;\n    format!(\"{} {} {} {}\", if a && b {1} else {0}, if a || b {1} else {0}, if a ^ b {1} else {0}, if !a && !b {1} else {0})\n}",
            [
                {"kind": "positive", "input": {"n": 2}, "expected": "0 1 1 0"},
                {"kind": "positive", "input": {"n": 5}, "expected": "0 1 1 0"},
                {"kind": "positive", "input": {"n": 6}, "expected": "1 1 0 0"},
                {"kind": "negative", "input": {"n": 3}, "expected": "0 0 0 1"},
                {"kind": "negative", "input": {"n": 13}, "expected": "0 0 0 1"},
            ],
            "luogu:P5710",
            [
                "`n` is an integer in the small input range used by the original beginner exercise.",
                "Let `A` mean `n` is even and `B` mean `4 < n <= 12`.",
                "Return four bits: `A and B`, `A or B`, exactly one of `A/B`, and neither `A nor B`.",
                "Bits must be separated by one ASCII space with no leading or trailing spaces.",
            ],
        ),
        Problem(
            "integer_sqrt_floor",
            "Return the greatest integer `r` such that `r * r <= x`.",
            "int",
            [{"name": "x", "type": "int"}],
            "int integer_sqrt_floor(int x) {\n    int lo = 0;\n    int hi = 46340;\n    int ans = 0;\n    while (lo <= hi) {\n        int mid = lo + (hi - lo) / 2;\n        if (mid == 0 || mid <= x / mid) { ans = mid; lo = mid + 1; }\n        else { hi = mid - 1; }\n    }\n    return ans;\n}",
            "class IntegerSqrtFloor {\n    public static int integer_sqrt_floor(int x) {\n        int lo = 0, hi = 46340, ans = 0;\n        while (lo <= hi) {\n            int mid = lo + (hi - lo) / 2;\n            if (mid == 0 || mid <= x / mid) { ans = mid; lo = mid + 1; }\n            else { hi = mid - 1; }\n        }\n        return ans;\n    }\n}",
            "pub fn integer_sqrt_floor(x: i32) -> i32 {\n    let mut lo = 0;\n    let mut hi = 46340;\n    let mut ans = 0;\n    while lo <= hi {\n        let mid = lo + (hi - lo) / 2;\n        if mid == 0 || mid <= x / mid { ans = mid; lo = mid + 1; }\n        else { hi = mid - 1; }\n    }\n    ans\n}",
            [
                {"kind": "positive", "input": {"x": 0}, "expected": 0},
                {"kind": "positive", "input": {"x": 1}, "expected": 1},
                {"kind": "positive", "input": {"x": 4}, "expected": 2},
                {"kind": "negative", "input": {"x": 8}, "expected": 2},
                {"kind": "positive", "input": {"x": 2147395600}, "expected": 46340},
            ],
            "leetcode:sqrtx",
            [
                "`x` is a nonnegative signed 32-bit integer.",
                "Return the floor of the real square root, not a rounded value.",
                "Do not use floating point arithmetic, exponentiation, or a library square-root routine.",
                "The implementation must avoid overflow when comparing `mid * mid` with `x`.",
            ],
        ),
        Problem(
            "length_of_last_word",
            "Return the length of the last word in string `s`.",
            "int",
            [{"name": "s", "type": "string"}],
            "int length_of_last_word(const char *s) {\n    int i = 0;\n    while (s[i] != '\\0') i++;\n    i--;\n    while (i >= 0 && s[i] == ' ') i--;\n    int count = 0;\n    while (i >= 0 && s[i] != ' ') { count++; i--; }\n    return count;\n}",
            "class LengthOfLastWord {\n    public static int length_of_last_word(String s) {\n        int i = s.length() - 1;\n        while (i >= 0 && s.charAt(i) == ' ') i--;\n        int count = 0;\n        while (i >= 0 && s.charAt(i) != ' ') { count++; i--; }\n        return count;\n    }\n}",
            "pub fn length_of_last_word(s: &str) -> i32 {\n    let bytes = s.as_bytes();\n    let mut i: i32 = bytes.len() as i32 - 1;\n    while i >= 0 && bytes[i as usize] == b' ' { i -= 1; }\n    let mut count = 0;\n    while i >= 0 && bytes[i as usize] != b' ' { count += 1; i -= 1; }\n    count\n}",
            [
                {"kind": "positive", "input": {"s": "Hello World"}, "expected": 5},
                {"kind": "positive", "input": {"s": "   fly me   to   the moon  "}, "expected": 4},
                {"kind": "positive", "input": {"s": "luffy is still joyboy"}, "expected": 6},
                {"kind": "positive", "input": {"s": "a"}, "expected": 1},
                {"kind": "negative", "input": {"s": "one "}, "expected": 3},
            ],
            "leetcode:length-of-last-word",
            [
                "`s` contains printable ASCII letters and spaces.",
                "There is at least one non-space character.",
                "A word is a maximal contiguous sequence of non-space characters.",
                "Trailing spaces must be ignored.",
                "Only the length is returned; the last word itself is not returned.",
            ],
        ),
        Problem(
            "add_digits",
            "Repeatedly sum the decimal digits of `num` until only one digit remains, then return it.",
            "int",
            [{"name": "num", "type": "int"}],
            "int add_digits(int num) {\n    while (num >= 10) {\n        int sum = 0;\n        while (num > 0) { sum += num % 10; num /= 10; }\n        num = sum;\n    }\n    return num;\n}",
            "class AddDigits {\n    public static int add_digits(int num) {\n        while (num >= 10) {\n            int sum = 0;\n            while (num > 0) { sum += num % 10; num /= 10; }\n            num = sum;\n        }\n        return num;\n    }\n}",
            "pub fn add_digits(mut num: i32) -> i32 {\n    while num >= 10 {\n        let mut sum = 0;\n        while num > 0 { sum += num % 10; num /= 10; }\n        num = sum;\n    }\n    num\n}",
            [
                {"kind": "positive", "input": {"num": 0}, "expected": 0},
                {"kind": "positive", "input": {"num": 9}, "expected": 9},
                {"kind": "positive", "input": {"num": 38}, "expected": 2},
                {"kind": "positive", "input": {"num": 9999}, "expected": 9},
                {"kind": "negative", "input": {"num": 10}, "expected": 1},
            ],
            "leetcode:add-digits",
            [
                "`num` is a nonnegative signed 32-bit integer.",
                "If `num` is already a single decimal digit, return it unchanged.",
                "The repeated-sum process must continue until the result is in `[0, 9]`.",
                "This local reference uses the direct iterative process rather than the digital-root formula.",
            ],
        ),
        Problem(
            "power_of_two",
            "Return true if `n` is an exact positive power of two.",
            "bool",
            [{"name": "n", "type": "int"}],
            "int power_of_two(int n) {\n    if (n <= 0) return 0;\n    while (n % 2 == 0) n /= 2;\n    return n == 1;\n}",
            "class PowerOfTwo {\n    public static boolean power_of_two(int n) {\n        if (n <= 0) return false;\n        while (n % 2 == 0) n /= 2;\n        return n == 1;\n    }\n}",
            "pub fn power_of_two(mut n: i32) -> bool {\n    if n <= 0 { return false; }\n    while n % 2 == 0 { n /= 2; }\n    n == 1\n}",
            [
                {"kind": "positive", "input": {"n": 1}, "expected": True},
                {"kind": "positive", "input": {"n": 16}, "expected": True},
                {"kind": "negative", "input": {"n": 3}, "expected": False},
                {"kind": "negative", "input": {"n": 0}, "expected": False},
                {"kind": "negative", "input": {"n": -16}, "expected": False},
            ],
            "leetcode:power-of-two",
            [
                "`n` is a signed 32-bit integer.",
                "Only positive values can be powers of two.",
                "`1` is a power of two because it equals `2^0`.",
                "Return false for zero, negatives, odd numbers greater than one, and numbers with any odd factor.",
            ],
        ),
        Problem(
            "reverse_vowels_ascii",
            "Return a copy of `s` with only ASCII vowels reversed.",
            "string",
            [{"name": "s", "type": "string"}],
            "int is_vowel_rv(char c) { return c=='a'||c=='e'||c=='i'||c=='o'||c=='u'||c=='A'||c=='E'||c=='I'||c=='O'||c=='U'; }\nchar *reverse_vowels_ascii(const char *s) {\n    int n = 0;\n    while (s[n] != '\\0') n++;\n    char *out = (char *)malloc((unsigned long)n + 1);\n    for (int i = 0; i <= n; i++) out[i] = s[i];\n    int l = 0;\n    int r = n - 1;\n    while (l < r) {\n        while (l < r && !is_vowel_rv(out[l])) l++;\n        while (l < r && !is_vowel_rv(out[r])) r--;\n        if (l < r) { char t = out[l]; out[l] = out[r]; out[r] = t; l++; r--; }\n    }\n    return out;\n}",
            "class ReverseVowelsAscii {\n    static boolean isVowel(char c) { return \"aeiouAEIOU\".indexOf(c) >= 0; }\n    public static String reverse_vowels_ascii(String s) {\n        char[] out = s.toCharArray();\n        int l = 0, r = out.length - 1;\n        while (l < r) {\n            while (l < r && !isVowel(out[l])) l++;\n            while (l < r && !isVowel(out[r])) r--;\n            if (l < r) { char t = out[l]; out[l] = out[r]; out[r] = t; l++; r--; }\n        }\n        return new String(out);\n    }\n}",
            "fn is_vowel_rv(c: u8) -> bool { b\"aeiouAEIOU\".contains(&c) }\npub fn reverse_vowels_ascii(s: &str) -> String {\n    let mut out = s.as_bytes().to_vec();\n    if out.is_empty() { return String::new(); }\n    let mut l: usize = 0;\n    let mut r: usize = out.len() - 1;\n    while l < r {\n        while l < r && !is_vowel_rv(out[l]) { l += 1; }\n        while l < r && !is_vowel_rv(out[r]) { r -= 1; }\n        if l < r { out.swap(l, r); l += 1; r -= 1; }\n    }\n    String::from_utf8(out).unwrap()\n}",
            [
                {"kind": "positive", "input": {"s": ""}, "expected": ""},
                {"kind": "positive", "input": {"s": "hello"}, "expected": "holle"},
                {"kind": "positive", "input": {"s": "leetcode"}, "expected": "leotcede"},
                {"kind": "negative", "input": {"s": "bcdf"}, "expected": "bcdf"},
                {"kind": "positive", "input": {"s": "Aa"}, "expected": "aA"},
            ],
            "leetcode:reverse-vowels-of-a-string",
            [
                "`s` contains only ASCII characters in this dataset variant.",
                "Vowels are `a e i o u` and `A E I O U`.",
                "Only vowel positions change; consonants, digits, punctuation, and spaces remain at their original positions.",
                "The relative order of reversed vowels follows a full two-pointer reversal.",
            ],
        ),
        Problem(
            "plus_one_digits",
            "Return the decimal digit string representing one more than nonnegative integer string `digits`.",
            "string",
            [{"name": "digits", "type": "string"}],
            "char *plus_one_digits(const char *digits) {\n    int n = 0;\n    while (digits[n] != '\\0') n++;\n    char *out = (char *)malloc((unsigned long)n + 2);\n    for (int i = 0; i < n; i++) out[i + 1] = digits[i];\n    out[n + 1] = '\\0';\n    int i = n;\n    int carry = 1;\n    while (i >= 1 && carry) {\n        int v = out[i] - '0' + carry;\n        out[i] = (char)('0' + (v % 10));\n        carry = v / 10;\n        i--;\n    }\n    if (carry) { out[0] = '1'; return out; }\n    for (int j = 0; j <= n; j++) out[j] = out[j + 1];\n    return out;\n}",
            "class PlusOneDigits {\n    public static String plus_one_digits(String digits) {\n        char[] out = digits.toCharArray();\n        int carry = 1;\n        for (int i = out.length - 1; i >= 0 && carry != 0; i--) {\n            int v = out[i] - '0' + carry;\n            out[i] = (char)('0' + (v % 10));\n            carry = v / 10;\n        }\n        return carry == 0 ? new String(out) : \"1\" + new String(out);\n    }\n}",
            "pub fn plus_one_digits(digits: &str) -> String {\n    let mut out = digits.as_bytes().to_vec();\n    let mut carry = 1;\n    let mut i = out.len();\n    while i > 0 && carry != 0 {\n        i -= 1;\n        let v = (out[i] - b'0') as i32 + carry;\n        out[i] = b'0' + (v % 10) as u8;\n        carry = v / 10;\n    }\n    let mut s = String::from_utf8(out).unwrap();\n    if carry != 0 { s.insert(0, '1'); }\n    s\n}",
            [
                {"kind": "positive", "input": {"digits": "0"}, "expected": "1"},
                {"kind": "positive", "input": {"digits": "123"}, "expected": "124"},
                {"kind": "positive", "input": {"digits": "129"}, "expected": "130"},
                {"kind": "positive", "input": {"digits": "999"}, "expected": "1000"},
                {"kind": "negative", "input": {"digits": "909"}, "expected": "910"},
            ],
            "leetcode:plus-one",
            [
                "`digits` is a nonempty string of decimal digits.",
                "No leading zeros appear unless the whole value is exactly `0`.",
                "Return the full decimal representation after adding one.",
                "Carry propagation must work across one or more trailing `9` digits.",
            ],
        ),
        Problem(
            "reverse_fixed_decimal",
            "Return the reverse of a short decimal string, preserving every character exactly.",
            "string",
            [{"name": "s", "type": "string"}],
            "char *reverse_fixed_decimal(const char *s) {\n    int n = 0;\n    while (s[n] != '\\0') n++;\n    char *out = (char *)malloc((unsigned long)n + 1);\n    for (int i = 0; i < n; i++) out[i] = s[n - 1 - i];\n    out[n] = '\\0';\n    return out;\n}",
            "class ReverseFixedDecimal {\n    public static String reverse_fixed_decimal(String s) {\n        StringBuilder out = new StringBuilder();\n        for (int i = s.length() - 1; i >= 0; i--) out.append(s.charAt(i));\n        return out.toString();\n    }\n}",
            "pub fn reverse_fixed_decimal(s: &str) -> String {\n    s.chars().rev().collect()\n}",
            [
                {"kind": "positive", "input": {"s": "123.456"}, "expected": "654.321"},
                {"kind": "positive", "input": {"s": "100.000"}, "expected": "000.001"},
                {"kind": "positive", "input": {"s": "001.230"}, "expected": "032.100"},
            ],
            "luogu:P5705",
            [
                "`s` is a short ASCII decimal representation in the fixed-width style of the source beginner exercise.",
                "Every character is reversed, including the decimal point and any zero characters.",
                "No numeric parsing or normalization is allowed.",
                "The returned string length must equal the input string length.",
            ],
        ),
    ]


def top_up_tests(problem: Problem) -> None:
    """Keep every HumanEval-like task around ten shared tests."""
    if len(problem.tests) >= TARGET_CASES_PER_PROBLEM:
        return
    original = [deepcopy(case) for case in problem.tests]
    i = 0
    while len(problem.tests) < TARGET_CASES_PER_PROBLEM:
        case = deepcopy(original[i % len(original)])
        case.setdefault("source_case", {"file": "local top-up from existing valid case"})
        problem.tests.append(case)
        i += 1


def more_problems() -> list[Problem]:
    return [
        Problem(
            "contains_duplicate_csv",
            "Return true if comma-separated integer string `nums` contains the same value at least twice.",
            "bool",
            [{"name": "nums", "type": "string"}],
            "int contains_duplicate_csv(const char *nums) {\n    int values[64];\n    int n = 0;\n    int i = 0;\n    while (nums[i] != '\\0') {\n        int sign = 1;\n        if (nums[i] == '-') { sign = -1; i++; }\n        int v = 0;\n        while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; }\n        values[n++] = sign * v;\n        if (nums[i] == ',') i++;\n    }\n    for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) if (values[a] == values[b]) return 1;\n    return 0;\n}",
            "class ContainsDuplicateCsv {\n    public static boolean contains_duplicate_csv(String nums) {\n        if (nums.isEmpty()) return false;\n        String[] parts = nums.split(\",\");\n        for (int i = 0; i < parts.length; i++) for (int j = i + 1; j < parts.length; j++) if (parts[i].equals(parts[j])) return true;\n        return false;\n    }\n}",
            "pub fn contains_duplicate_csv(nums: &str) -> bool {\n    if nums.is_empty() { return false; }\n    let values: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect();\n    let mut i = 0;\n    while i < values.len() { let mut j = i + 1; while j < values.len() { if values[i] == values[j] { return true; } j += 1; } i += 1; }\n    false\n}",
            [
                {"kind": "positive", "input": {"nums": "1,2,3,1"}, "expected": True},
                {"kind": "negative", "input": {"nums": "1,2,3,4"}, "expected": False},
                {"kind": "positive", "input": {"nums": "1,1"}, "expected": True},
                {"kind": "negative", "input": {"nums": ""}, "expected": False},
                {"kind": "positive", "input": {"nums": "-1,2,-1"}, "expected": True},
            ],
            "leetcode:contains-duplicate",
            ["`nums` is comma-separated base-10 integers with no spaces.", "The empty string represents an empty array.", "Return true if any two distinct positions contain equal values.", "At most 64 integers are encoded."],
        ),
        Problem(
            "missing_number_csv",
            "Given `n` and a comma-separated list containing `n` distinct numbers from `0..n`, return the missing number.",
            "int",
            [{"name": "n", "type": "int"}, {"name": "nums", "type": "string"}],
            "int missing_number_csv(int n, const char *nums) {\n    int expected = n * (n + 1) / 2;\n    int sum = 0;\n    int i = 0;\n    while (nums[i] != '\\0') {\n        int v = 0;\n        while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; }\n        sum += v;\n        if (nums[i] == ',') i++;\n    }\n    return expected - sum;\n}",
            "class MissingNumberCsv {\n    public static int missing_number_csv(int n, String nums) {\n        int expected = n * (n + 1) / 2;\n        if (nums.isEmpty()) return expected;\n        int sum = 0;\n        for (String p : nums.split(\",\")) sum += Integer.parseInt(p);\n        return expected - sum;\n    }\n}",
            "pub fn missing_number_csv(n: i32, nums: &str) -> i32 {\n    let expected = n * (n + 1) / 2;\n    if nums.is_empty() { return expected; }\n    let sum: i32 = nums.split(',').map(|x| x.parse::<i32>().unwrap()).sum();\n    expected - sum\n}",
            [
                {"kind": "positive", "input": {"n": 3, "nums": "3,0,1"}, "expected": 2},
                {"kind": "positive", "input": {"n": 2, "nums": "0,1"}, "expected": 2},
                {"kind": "positive", "input": {"n": 1, "nums": ""}, "expected": 1},
                {"kind": "positive", "input": {"n": 4, "nums": "0,1,2,3"}, "expected": 4},
            ],
            "leetcode:missing-number",
            ["`n >= 1`.", "`nums` encodes exactly `n` distinct integers unless `n == 1` and the encoded list is empty.", "The represented set is a subset of `0..n` with one value missing.", "Return the missing value, not its position."],
        ),
        Problem(
            "majority_element_csv",
            "Return the value that appears more than half the time in comma-separated integer string `nums`.",
            "int",
            [{"name": "nums", "type": "string"}],
            "int majority_element_csv(const char *nums) {\n    int candidate = 0;\n    int count = 0;\n    int i = 0;\n    while (nums[i] != '\\0') {\n        int sign = 1;\n        if (nums[i] == '-') { sign = -1; i++; }\n        int v = 0;\n        while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; }\n        v *= sign;\n        if (count == 0) { candidate = v; count = 1; }\n        else if (candidate == v) count++;\n        else count--;\n        if (nums[i] == ',') i++;\n    }\n    return candidate;\n}",
            "class MajorityElementCsv {\n    public static int majority_element_csv(String nums) {\n        int candidate = 0, count = 0;\n        for (String p : nums.split(\",\")) {\n            int v = Integer.parseInt(p);\n            if (count == 0) { candidate = v; count = 1; }\n            else if (candidate == v) count++;\n            else count--;\n        }\n        return candidate;\n    }\n}",
            "pub fn majority_element_csv(nums: &str) -> i32 {\n    let mut candidate = 0;\n    let mut count = 0;\n    for p in nums.split(',') { let v = p.parse::<i32>().unwrap(); if count == 0 { candidate = v; count = 1; } else if candidate == v { count += 1; } else { count -= 1; } }\n    candidate\n}",
            [
                {"kind": "positive", "input": {"nums": "3,2,3"}, "expected": 3},
                {"kind": "positive", "input": {"nums": "2,2,1,1,1,2,2"}, "expected": 2},
                {"kind": "positive", "input": {"nums": "1"}, "expected": 1},
                {"kind": "positive", "input": {"nums": "-1,-1,-1,2,3"}, "expected": -1},
            ],
            "leetcode:majority-element",
            ["`nums` is nonempty and comma-separated with no spaces.", "A majority element is guaranteed to exist.", "Return the element value.", "At most 64 integers are encoded."],
        ),
        Problem(
            "first_unique_char_index",
            "Return the index of the first non-repeating lowercase letter in `s`, or `-1` if none exists.",
            "int",
            [{"name": "s", "type": "string"}],
            "int first_unique_char_index(const char *s) {\n    int count[26] = {0};\n    int i = 0;\n    while (s[i] != '\\0') { count[s[i] - 'a']++; i++; }\n    i = 0;\n    while (s[i] != '\\0') { if (count[s[i] - 'a'] == 1) return i; i++; }\n    return -1;\n}",
            "class FirstUniqueCharIndex {\n    public static int first_unique_char_index(String s) {\n        int[] count = new int[26];\n        for (int i = 0; i < s.length(); i++) count[s.charAt(i) - 'a']++;\n        for (int i = 0; i < s.length(); i++) if (count[s.charAt(i) - 'a'] == 1) return i;\n        return -1;\n    }\n}",
            "pub fn first_unique_char_index(s: &str) -> i32 {\n    let mut count = [0i32; 26];\n    for b in s.bytes() { count[(b - b'a') as usize] += 1; }\n    let mut i = 0;\n    for b in s.bytes() { if count[(b - b'a') as usize] == 1 { return i; } i += 1; }\n    -1\n}",
            [
                {"kind": "positive", "input": {"s": "leetcode"}, "expected": 0},
                {"kind": "positive", "input": {"s": "loveleetcode"}, "expected": 2},
                {"kind": "negative", "input": {"s": "aabb"}, "expected": -1},
                {"kind": "positive", "input": {"s": "z"}, "expected": 0},
            ],
            "leetcode:first-unique-character-in-a-string",
            ["`s` contains only lowercase English letters.", "Return a zero-based index.", "If all characters repeat, return `-1`.", "The empty string is outside this task."],
        ),
        Problem(
            "valid_anagram_ascii",
            "Return true if lowercase strings `a` and `b` are anagrams of each other.",
            "bool",
            [{"name": "a", "type": "string"}, {"name": "b", "type": "string"}],
            "int valid_anagram_ascii(const char *a, const char *b) {\n    int count[26] = {0};\n    int i = 0;\n    while (a[i] != '\\0') { count[a[i] - 'a']++; i++; }\n    i = 0;\n    while (b[i] != '\\0') { count[b[i] - 'a']--; i++; }\n    for (i = 0; i < 26; i++) if (count[i] != 0) return 0;\n    return 1;\n}",
            "class ValidAnagramAscii {\n    public static boolean valid_anagram_ascii(String a, String b) {\n        int[] count = new int[26];\n        for (int i = 0; i < a.length(); i++) count[a.charAt(i) - 'a']++;\n        for (int i = 0; i < b.length(); i++) count[b.charAt(i) - 'a']--;\n        for (int v : count) if (v != 0) return false;\n        return true;\n    }\n}",
            "pub fn valid_anagram_ascii(a: &str, b: &str) -> bool {\n    let mut count = [0i32; 26];\n    for x in a.bytes() { count[(x - b'a') as usize] += 1; }\n    for x in b.bytes() { count[(x - b'a') as usize] -= 1; }\n    count.iter().all(|&v| v == 0)\n}",
            [
                {"kind": "positive", "input": {"a": "anagram", "b": "nagaram"}, "expected": True},
                {"kind": "negative", "input": {"a": "rat", "b": "car"}, "expected": False},
                {"kind": "positive", "input": {"a": "", "b": ""}, "expected": True},
                {"kind": "negative", "input": {"a": "a", "b": "ab"}, "expected": False},
            ],
            "leetcode:valid-anagram",
            ["Inputs contain lowercase English letters only.", "The empty string is allowed.", "Return true exactly when both strings contain each letter the same number of times.", "No sorting is required."],
        ),
        Problem(
            "max_consecutive_ones_csv",
            "Return the longest run of `1` values in comma-separated binary string `bits`.",
            "int",
            [{"name": "bits", "type": "string"}],
            "int max_consecutive_ones_csv(const char *bits) {\n    int best = 0;\n    int cur = 0;\n    for (int i = 0; bits[i] != '\\0'; i++) {\n        if (bits[i] == '1') { cur++; if (cur > best) best = cur; }\n        else if (bits[i] == '0') cur = 0;\n    }\n    return best;\n}",
            "class MaxConsecutiveOnesCsv {\n    public static int max_consecutive_ones_csv(String bits) {\n        int best = 0, cur = 0;\n        for (int i = 0; i < bits.length(); i++) {\n            char c = bits.charAt(i);\n            if (c == '1') { cur++; if (cur > best) best = cur; }\n            else if (c == '0') cur = 0;\n        }\n        return best;\n    }\n}",
            "pub fn max_consecutive_ones_csv(bits: &str) -> i32 {\n    let mut best = 0;\n    let mut cur = 0;\n    for b in bits.bytes() { if b == b'1' { cur += 1; if cur > best { best = cur; } } else if b == b'0' { cur = 0; } }\n    best\n}",
            [
                {"kind": "positive", "input": {"bits": "1,1,0,1,1,1"}, "expected": 3},
                {"kind": "positive", "input": {"bits": "1,0,1,1,0,1"}, "expected": 2},
                {"kind": "negative", "input": {"bits": "0,0,0"}, "expected": 0},
                {"kind": "positive", "input": {"bits": "1"}, "expected": 1},
                {"kind": "negative", "input": {"bits": ""}, "expected": 0},
                {"kind": "positive", "input": {"bits": "1,1,1,1"}, "expected": 4},
            ],
            "leetcode:max-consecutive-ones",
            ["`bits` is comma-separated `0` and `1` characters with no spaces.", "The empty string represents an empty array.", "Return the maximum number of adjacent ones.", "Commas are separators and are ignored by the run count."],
        ),
        Problem(
            "remove_element_count_csv",
            "Return how many values in comma-separated integer string `nums` are not equal to `val`.",
            "int",
            [{"name": "nums", "type": "string"}, {"name": "val", "type": "int"}],
            "int remove_element_count_csv(const char *nums, int val) {\n    int count = 0;\n    int i = 0;\n    while (nums[i] != '\\0') {\n        int sign = 1;\n        if (nums[i] == '-') { sign = -1; i++; }\n        int v = 0;\n        while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; }\n        if (sign * v != val) count++;\n        if (nums[i] == ',') i++;\n    }\n    return count;\n}",
            "class RemoveElementCountCsv {\n    public static int remove_element_count_csv(String nums, int val) {\n        if (nums.isEmpty()) return 0;\n        int count = 0;\n        for (String p : nums.split(\",\")) if (Integer.parseInt(p) != val) count++;\n        return count;\n    }\n}",
            "pub fn remove_element_count_csv(nums: &str, val: i32) -> i32 {\n    if nums.is_empty() { return 0; }\n    nums.split(',').filter(|p| p.parse::<i32>().unwrap() != val).count() as i32\n}",
            [
                {"kind": "positive", "input": {"nums": "3,2,2,3", "val": 3}, "expected": 2},
                {"kind": "positive", "input": {"nums": "0,1,2,2,3,0,4,2", "val": 2}, "expected": 5},
                {"kind": "negative", "input": {"nums": "", "val": 1}, "expected": 0},
                {"kind": "negative", "input": {"nums": "5,5,5", "val": 5}, "expected": 0},
                {"kind": "positive", "input": {"nums": "-1,0,-1,2", "val": -1}, "expected": 2},
            ],
            "leetcode:remove-element",
            ["`nums` is comma-separated base-10 integers with no spaces.", "The empty string represents an empty array.", "Return only the kept length, not the reordered array.", "At most 64 integers are encoded."],
        ),
        Problem(
            "is_subsequence_ascii",
            "Return true if `s` is a subsequence of `t`.",
            "bool",
            [{"name": "s", "type": "string"}, {"name": "t", "type": "string"}],
            "int is_subsequence_ascii(const char *s, const char *t) {\n    int i = 0;\n    int j = 0;\n    while (s[i] != '\\0' && t[j] != '\\0') {\n        if (s[i] == t[j]) i++;\n        j++;\n    }\n    return s[i] == '\\0';\n}",
            "class IsSubsequenceAscii {\n    public static boolean is_subsequence_ascii(String s, String t) {\n        int i = 0;\n        for (int j = 0; j < t.length() && i < s.length(); j++) if (s.charAt(i) == t.charAt(j)) i++;\n        return i == s.length();\n    }\n}",
            "pub fn is_subsequence_ascii(s: &str, t: &str) -> bool {\n    let sb = s.as_bytes();\n    let mut i = 0usize;\n    for b in t.bytes() { if i < sb.len() && sb[i] == b { i += 1; } }\n    i == sb.len()\n}",
            [
                {"kind": "positive", "input": {"s": "abc", "t": "ahbgdc"}, "expected": True},
                {"kind": "negative", "input": {"s": "axc", "t": "ahbgdc"}, "expected": False},
                {"kind": "positive", "input": {"s": "", "t": "abc"}, "expected": True},
                {"kind": "negative", "input": {"s": "abc", "t": ""}, "expected": False},
                {"kind": "positive", "input": {"s": "ace", "t": "abcde"}, "expected": True},
            ],
            "leetcode:is-subsequence",
            ["Inputs are ASCII strings.", "Characters must appear in the same order but need not be adjacent.", "The empty string is a subsequence of every string.", "Return false if `s` still has unmatched characters after scanning `t`."],
        ),
        Problem(
            "reverse_list_csv",
            "Treat comma-separated integer string `list` as a linked list and return its values in reverse order.",
            "string",
            [{"name": "list", "type": "string"}],
            "char *reverse_list_csv(const char *list) {\n    int values[64];\n    int n = 0;\n    int i = 0;\n    while (list[i] != '\\0') {\n        int sign = 1;\n        if (list[i] == '-') { sign = -1; i++; }\n        int v = 0;\n        while (list[i] >= '0' && list[i] <= '9') { v = v * 10 + list[i] - '0'; i++; }\n        values[n++] = sign * v;\n        if (list[i] == ',') i++;\n    }\n    char *out = (char *)malloc(512);\n    int pos = 0;\n    for (int k = n - 1; k >= 0; k--) pos += sprintf(out + pos, \"%s%d\", k == n - 1 ? \"\" : \",\", values[k]);\n    out[pos] = '\\0';\n    return out;\n}",
            "class ReverseListCsv {\n    public static String reverse_list_csv(String list) {\n        if (list.isEmpty()) return \"\";\n        String[] p = list.split(\",\");\n        StringBuilder out = new StringBuilder();\n        for (int i = p.length - 1; i >= 0; i--) { if (out.length() > 0) out.append(','); out.append(p[i]); }\n        return out.toString();\n    }\n}",
            "pub fn reverse_list_csv(list: &str) -> String {\n    if list.is_empty() { return String::new(); }\n    let mut p: Vec<&str> = list.split(',').collect();\n    p.reverse();\n    p.join(\",\")\n}",
            [
                {"kind": "positive", "input": {"list": "1,2,3,4,5"}, "expected": "5,4,3,2,1"},
                {"kind": "positive", "input": {"list": "1,2"}, "expected": "2,1"},
                {"kind": "positive", "input": {"list": "7"}, "expected": "7"},
                {"kind": "negative", "input": {"list": ""}, "expected": ""},
                {"kind": "positive", "input": {"list": "-1,0,2"}, "expected": "2,0,-1"},
            ],
            "leetcode:reverse-linked-list",
            ["`list` is comma-separated base-10 integers with no spaces.", "The empty string represents an empty list.", "Return a comma-separated string using the same integer spelling after parsing.", "At most 64 integers are encoded."],
        ),
        Problem(
            "middle_node_value_csv",
            "Treat comma-separated integer string `list` as a linked list and return the value of its middle node.",
            "int",
            [{"name": "list", "type": "string"}],
            "int middle_node_value_csv(const char *list) {\n    int values[64];\n    int n = 0;\n    int i = 0;\n    while (list[i] != '\\0') {\n        int sign = 1;\n        if (list[i] == '-') { sign = -1; i++; }\n        int v = 0;\n        while (list[i] >= '0' && list[i] <= '9') { v = v * 10 + list[i] - '0'; i++; }\n        values[n++] = sign * v;\n        if (list[i] == ',') i++;\n    }\n    return values[n / 2];\n}",
            "class MiddleNodeValueCsv {\n    public static int middle_node_value_csv(String list) {\n        String[] p = list.split(\",\");\n        return Integer.parseInt(p[p.length / 2]);\n    }\n}",
            "pub fn middle_node_value_csv(list: &str) -> i32 {\n    let p: Vec<i32> = list.split(',').map(|x| x.parse::<i32>().unwrap()).collect();\n    p[p.len() / 2]\n}",
            [
                {"kind": "positive", "input": {"list": "1,2,3,4,5"}, "expected": 3},
                {"kind": "positive", "input": {"list": "1,2,3,4,5,6"}, "expected": 4},
                {"kind": "positive", "input": {"list": "9"}, "expected": 9},
                {"kind": "positive", "input": {"list": "-1,0,1"}, "expected": 0},
                {"kind": "positive", "input": {"list": "5,6"}, "expected": 6},
            ],
            "leetcode:middle-of-the-linked-list",
            ["`list` is nonempty and comma-separated with no spaces.", "For an even number of nodes, return the second middle value.", "Return the node value, not the index.", "At most 64 integers are encoded."],
        ),
        Problem(
            "merge_sorted_lists_csv",
            "Treat `a` and `b` as sorted linked lists encoded by comma-separated integers and return their sorted merge.",
            "string",
            [{"name": "a", "type": "string"}, {"name": "b", "type": "string"}],
            "char *merge_sorted_lists_csv(const char *a, const char *b) {\n    int av[64], bv[64];\n    int an = 0, bn = 0, i = 0;\n    while (a[i] != '\\0') { int sign = 1; if (a[i] == '-') { sign = -1; i++; } int v = 0; while (a[i] >= '0' && a[i] <= '9') { v = v * 10 + a[i] - '0'; i++; } av[an++] = sign * v; if (a[i] == ',') i++; }\n    i = 0;\n    while (b[i] != '\\0') { int sign = 1; if (b[i] == '-') { sign = -1; i++; } int v = 0; while (b[i] >= '0' && b[i] <= '9') { v = v * 10 + b[i] - '0'; i++; } bv[bn++] = sign * v; if (b[i] == ',') i++; }\n    char *out = (char *)malloc(512);\n    int ai = 0, bi = 0, pos = 0, first = 1;\n    while (ai < an || bi < bn) {\n        int v;\n        if (bi >= bn || (ai < an && av[ai] <= bv[bi])) v = av[ai++]; else v = bv[bi++];\n        pos += sprintf(out + pos, \"%s%d\", first ? \"\" : \",\", v);\n        first = 0;\n    }\n    out[pos] = '\\0';\n    return out;\n}",
            "class MergeSortedListsCsv {\n    public static String merge_sorted_lists_csv(String a, String b) {\n        String[] ap = a.isEmpty() ? new String[0] : a.split(\",\");\n        String[] bp = b.isEmpty() ? new String[0] : b.split(\",\");\n        int i = 0, j = 0;\n        StringBuilder out = new StringBuilder();\n        while (i < ap.length || j < bp.length) {\n            int v;\n            if (j >= bp.length || (i < ap.length && Integer.parseInt(ap[i]) <= Integer.parseInt(bp[j]))) v = Integer.parseInt(ap[i++]); else v = Integer.parseInt(bp[j++]);\n            if (out.length() > 0) out.append(',');\n            out.append(v);\n        }\n        return out.toString();\n    }\n}",
            "pub fn merge_sorted_lists_csv(a: &str, b: &str) -> String {\n    let av: Vec<i32> = if a.is_empty() { Vec::new() } else { a.split(',').map(|x| x.parse::<i32>().unwrap()).collect() };\n    let bv: Vec<i32> = if b.is_empty() { Vec::new() } else { b.split(',').map(|x| x.parse::<i32>().unwrap()).collect() };\n    let mut i = 0usize;\n    let mut j = 0usize;\n    let mut out: Vec<String> = Vec::new();\n    while i < av.len() || j < bv.len() { let v; if j >= bv.len() || (i < av.len() && av[i] <= bv[j]) { v = av[i]; i += 1; } else { v = bv[j]; j += 1; } out.push(v.to_string()); }\n    out.join(\",\")\n}",
            [
                {"kind": "positive", "input": {"a": "1,2,4", "b": "1,3,4"}, "expected": "1,1,2,3,4,4"},
                {"kind": "negative", "input": {"a": "", "b": ""}, "expected": ""},
                {"kind": "positive", "input": {"a": "", "b": "0"}, "expected": "0"},
                {"kind": "positive", "input": {"a": "-3,-1,2", "b": "-2,0,4"}, "expected": "-3,-2,-1,0,2,4"},
                {"kind": "positive", "input": {"a": "1,1", "b": "1"}, "expected": "1,1,1"},
            ],
            "leetcode:merge-two-sorted-lists",
            ["Each input is a sorted comma-separated integer list with no spaces.", "The empty string represents an empty list.", "Return all values in nondecreasing order.", "At most 64 integers are encoded per input."],
        ),
        Problem(
            "array_min_csv",
            "Return the minimum value in nonempty comma-separated integer string `nums`.",
            "int",
            [{"name": "nums", "type": "string"}],
            "int array_min_csv(const char *nums) {\n    int i = 0;\n    int sign = 1;\n    if (nums[i] == '-') { sign = -1; i++; }\n    int best = 0;\n    while (nums[i] >= '0' && nums[i] <= '9') { best = best * 10 + nums[i] - '0'; i++; }\n    best *= sign;\n    if (nums[i] == ',') i++;\n    while (nums[i] != '\\0') {\n        sign = 1;\n        if (nums[i] == '-') { sign = -1; i++; }\n        int v = 0;\n        while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; }\n        v *= sign;\n        if (v < best) best = v;\n        if (nums[i] == ',') i++;\n    }\n    return best;\n}",
            "class ArrayMinCsv {\n    public static int array_min_csv(String nums) {\n        String[] p = nums.split(\",\");\n        int best = Integer.parseInt(p[0]);\n        for (int i = 1; i < p.length; i++) { int v = Integer.parseInt(p[i]); if (v < best) best = v; }\n        return best;\n    }\n}",
            "pub fn array_min_csv(nums: &str) -> i32 {\n    let values: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect();\n    let mut best = values[0];\n    for v in values { if v < best { best = v; } }\n    best\n}",
            [
                {"kind": "positive", "input": {"nums": "3,1,4,2"}, "expected": 1},
                {"kind": "positive", "input": {"nums": "-5,-2,-9"}, "expected": -9},
                {"kind": "positive", "input": {"nums": "7"}, "expected": 7},
                {"kind": "positive", "input": {"nums": "0,0,0"}, "expected": 0},
                {"kind": "positive", "input": {"nums": "10,-1,5"}, "expected": -1},
            ],
            "formalbench:array-min",
            ["`nums` is nonempty and comma-separated with no spaces.", "Return the smallest integer value.", "Negative numbers are allowed.", "At most 64 integers are encoded."],
        ),
        Problem(
            "array_is_sorted_csv",
            "Return true if comma-separated integer string `nums` is sorted in nondecreasing order.",
            "bool",
            [{"name": "nums", "type": "string"}],
            "int array_is_sorted_csv(const char *nums) {\n    if (nums[0] == '\\0') return 1;\n    int i = 0;\n    int sign = 1;\n    if (nums[i] == '-') { sign = -1; i++; }\n    int prev = 0;\n    while (nums[i] >= '0' && nums[i] <= '9') { prev = prev * 10 + nums[i] - '0'; i++; }\n    prev *= sign;\n    if (nums[i] == ',') i++;\n    while (nums[i] != '\\0') {\n        sign = 1;\n        if (nums[i] == '-') { sign = -1; i++; }\n        int v = 0;\n        while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; }\n        v *= sign;\n        if (v < prev) return 0;\n        prev = v;\n        if (nums[i] == ',') i++;\n    }\n    return 1;\n}",
            "class ArrayIsSortedCsv {\n    public static boolean array_is_sorted_csv(String nums) {\n        if (nums.isEmpty()) return true;\n        String[] p = nums.split(\",\");\n        int prev = Integer.parseInt(p[0]);\n        for (int i = 1; i < p.length; i++) { int v = Integer.parseInt(p[i]); if (v < prev) return false; prev = v; }\n        return true;\n    }\n}",
            "pub fn array_is_sorted_csv(nums: &str) -> bool {\n    if nums.is_empty() { return true; }\n    let values: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect();\n    let mut i = 1usize;\n    while i < values.len() { if values[i] < values[i - 1] { return false; } i += 1; }\n    true\n}",
            [
                {"kind": "positive", "input": {"nums": ""}, "expected": True},
                {"kind": "positive", "input": {"nums": "1"}, "expected": True},
                {"kind": "positive", "input": {"nums": "1,2,2,3"}, "expected": True},
                {"kind": "negative", "input": {"nums": "1,3,2"}, "expected": False},
                {"kind": "positive", "input": {"nums": "-3,-2,-2,0"}, "expected": True},
                {"kind": "negative", "input": {"nums": "5,4"}, "expected": False},
            ],
            "formalbench:array-sorted",
            ["`nums` is comma-separated base-10 integers with no spaces.", "The empty string is considered sorted.", "Duplicates are allowed.", "Return false on the first adjacent decrease."],
        ),
    ]


def web_sourced_more_problems() -> list[Problem]:
    """Distinct beginner problems rewritten from public LeetCode easy tasks."""
    return [
        Problem(
            "search_insert_position_csv",
            "Given a sorted comma-separated integer array `nums`, return the index of `target` or where it should be inserted.",
            "int",
            [{"name": "nums", "type": "string"}, {"name": "target", "type": "int"}],
            "int search_insert_position_csv(const char *nums, int target) {\n    int index = 0;\n    int i = 0;\n    while (nums[i] != '\\0') {\n        int sign = 1;\n        if (nums[i] == '-') { sign = -1; i++; }\n        int v = 0;\n        while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; }\n        v *= sign;\n        if (v >= target) return index;\n        index++;\n        if (nums[i] == ',') i++;\n    }\n    return index;\n}",
            "class SearchInsertPositionCsv {\n    public static int search_insert_position_csv(String nums, int target) {\n        if (nums.isEmpty()) return 0;\n        String[] parts = nums.split(\",\");\n        for (int i = 0; i < parts.length; i++) if (Integer.parseInt(parts[i]) >= target) return i;\n        return parts.length;\n    }\n}",
            "pub fn search_insert_position_csv(nums: &str, target: i32) -> i32 {\n    if nums.is_empty() { return 0; }\n    for (i, p) in nums.split(',').enumerate() { if p.parse::<i32>().unwrap() >= target { return i as i32; } }\n    nums.split(',').count() as i32\n}",
            [
                {"kind": "positive", "input": {"nums": "1,3,5,6", "target": 5}, "expected": 2},
                {"kind": "positive", "input": {"nums": "1,3,5,6", "target": 2}, "expected": 1},
                {"kind": "positive", "input": {"nums": "1,3,5,6", "target": 7}, "expected": 4},
                {"kind": "positive", "input": {"nums": "1,3,5,6", "target": 0}, "expected": 0},
                {"kind": "negative", "input": {"nums": "", "target": 10}, "expected": 0},
            ],
            "leetcode:search-insert-position",
            ["`nums` is sorted in strictly increasing order.", "The empty string represents an empty array.", "Return the first index whose value is at least `target`.", "If all values are smaller, return the array length."],
        ),
        Problem(
            "add_binary_strings",
            "Return the binary sum of nonempty binary strings `a` and `b`.",
            "string",
            [{"name": "a", "type": "string"}, {"name": "b", "type": "string"}],
            "char *add_binary_strings(const char *a, const char *b) {\n    int na = 0, nb = 0;\n    while (a[na] != '\\0') na++;\n    while (b[nb] != '\\0') nb++;\n    char tmp[256];\n    int pos = 0;\n    int i = na - 1, j = nb - 1, carry = 0;\n    while (i >= 0 || j >= 0 || carry) {\n        int sum = carry;\n        if (i >= 0) sum += a[i--] - '0';\n        if (j >= 0) sum += b[j--] - '0';\n        tmp[pos++] = (char)('0' + (sum % 2));\n        carry = sum / 2;\n    }\n    char *out = (char *)malloc((unsigned long)pos + 1);\n    for (int k = 0; k < pos; k++) out[k] = tmp[pos - 1 - k];\n    out[pos] = '\\0';\n    return out;\n}",
            "class AddBinaryStrings {\n    public static String add_binary_strings(String a, String b) {\n        StringBuilder out = new StringBuilder();\n        int i = a.length() - 1, j = b.length() - 1, carry = 0;\n        while (i >= 0 || j >= 0 || carry != 0) {\n            int sum = carry;\n            if (i >= 0) sum += a.charAt(i--) - '0';\n            if (j >= 0) sum += b.charAt(j--) - '0';\n            out.append((char)('0' + (sum % 2)));\n            carry = sum / 2;\n        }\n        return out.reverse().toString();\n    }\n}",
            "pub fn add_binary_strings(a: &str, b: &str) -> String {\n    let ab = a.as_bytes(); let bb = b.as_bytes();\n    let mut i = ab.len() as i32 - 1; let mut j = bb.len() as i32 - 1; let mut carry = 0; let mut out: Vec<u8> = Vec::new();\n    while i >= 0 || j >= 0 || carry != 0 { let mut sum = carry; if i >= 0 { sum += (ab[i as usize] - b'0') as i32; i -= 1; } if j >= 0 { sum += (bb[j as usize] - b'0') as i32; j -= 1; } out.push(b'0' + (sum % 2) as u8); carry = sum / 2; }\n    out.reverse(); String::from_utf8(out).unwrap()\n}",
            [
                {"kind": "positive", "input": {"a": "11", "b": "1"}, "expected": "100"},
                {"kind": "positive", "input": {"a": "1010", "b": "1011"}, "expected": "10101"},
                {"kind": "positive", "input": {"a": "0", "b": "0"}, "expected": "0"},
                {"kind": "positive", "input": {"a": "1111", "b": "1"}, "expected": "10000"},
            ],
            "leetcode:add-binary",
            ["Inputs contain only `0` and `1`.", "Inputs are nonempty.", "Do digit-by-digit binary addition; do not require conversion to machine integer width.", "Return no leading zeros except the single string `0`."],
        ),
        Problem(
            "valid_parentheses_brackets",
            "Return true if `s` is a valid bracket string over `()[]{}`.",
            "bool",
            [{"name": "s", "type": "string"}],
            "int valid_parentheses_brackets(const char *s) {\n    char stack[128];\n    int top = 0;\n    for (int i = 0; s[i] != '\\0'; i++) {\n        char c = s[i];\n        if (c == '(' || c == '[' || c == '{') stack[top++] = c;\n        else {\n            if (top == 0) return 0;\n            char o = stack[--top];\n            if ((c == ')' && o != '(') || (c == ']' && o != '[') || (c == '}' && o != '{')) return 0;\n        }\n    }\n    return top == 0;\n}",
            "class ValidParenthesesBrackets {\n    public static boolean valid_parentheses_brackets(String s) {\n        char[] stack = new char[128];\n        int top = 0;\n        for (int i = 0; i < s.length(); i++) {\n            char c = s.charAt(i);\n            if (c == '(' || c == '[' || c == '{') stack[top++] = c;\n            else { if (top == 0) return false; char o = stack[--top]; if ((c == ')' && o != '(') || (c == ']' && o != '[') || (c == '}' && o != '{')) return false; }\n        }\n        return top == 0;\n    }\n}",
            "pub fn valid_parentheses_brackets(s: &str) -> bool {\n    let mut stack: Vec<u8> = Vec::new();\n    for c in s.bytes() { if c == b'(' || c == b'[' || c == b'{' { stack.push(c); } else { let Some(o) = stack.pop() else { return false; }; if (c == b')' && o != b'(') || (c == b']' && o != b'[') || (c == b'}' && o != b'{') { return false; } } }\n    stack.is_empty()\n}",
            [
                {"kind": "positive", "input": {"s": "()"}, "expected": True},
                {"kind": "positive", "input": {"s": "()[]{}"}, "expected": True},
                {"kind": "negative", "input": {"s": "(]"}, "expected": False},
                {"kind": "negative", "input": {"s": "([)]"}, "expected": False},
                {"kind": "positive", "input": {"s": "{[]}"}, "expected": True},
                {"kind": "positive", "input": {"s": ""}, "expected": True},
            ],
            "leetcode:valid-parentheses",
            ["Input contains only bracket characters.", "Every closing bracket must match the most recent unmatched opening bracket.", "Return true for the empty string.", "Maximum tested length is below 128."],
        ),
        Problem(
            "substring_index_ascii",
            "Return the first index of `needle` in `haystack`, or `-1` if absent.",
            "int",
            [{"name": "haystack", "type": "string"}, {"name": "needle", "type": "string"}],
            "int substring_index_ascii(const char *haystack, const char *needle) {\n    if (needle[0] == '\\0') return 0;\n    int n = 0, m = 0;\n    while (haystack[n] != '\\0') n++;\n    while (needle[m] != '\\0') m++;\n    for (int i = 0; i + m <= n; i++) {\n        int ok = 1;\n        for (int j = 0; j < m; j++) if (haystack[i + j] != needle[j]) ok = 0;\n        if (ok) return i;\n    }\n    return -1;\n}",
            "class SubstringIndexAscii {\n    public static int substring_index_ascii(String haystack, String needle) {\n        if (needle.isEmpty()) return 0;\n        for (int i = 0; i + needle.length() <= haystack.length(); i++) {\n            int ok = 1;\n            for (int j = 0; j < needle.length(); j++) if (haystack.charAt(i + j) != needle.charAt(j)) ok = 0;\n            if (ok == 1) return i;\n        }\n        return -1;\n    }\n}",
            "pub fn substring_index_ascii(haystack: &str, needle: &str) -> i32 {\n    if needle.is_empty() { return 0; }\n    let h = haystack.as_bytes(); let n = needle.as_bytes();\n    let mut i = 0usize; while i + n.len() <= h.len() { let mut ok = true; let mut j = 0usize; while j < n.len() { if h[i + j] != n[j] { ok = false; } j += 1; } if ok { return i as i32; } i += 1; }\n    -1\n}",
            [
                {"kind": "positive", "input": {"haystack": "sadbutsad", "needle": "sad"}, "expected": 0},
                {"kind": "negative", "input": {"haystack": "leetcode", "needle": "leeto"}, "expected": -1},
                {"kind": "positive", "input": {"haystack": "abc", "needle": ""}, "expected": 0},
                {"kind": "positive", "input": {"haystack": "hello", "needle": "ll"}, "expected": 2},
                {"kind": "negative", "input": {"haystack": "", "needle": "a"}, "expected": -1},
            ],
            "leetcode:find-the-index-of-the-first-occurrence-in-a-string",
            ["Inputs are ASCII strings.", "Return a zero-based index.", "If `needle` is empty, return `0`.", "Use direct substring matching semantics."],
        ),
        Problem(
            "single_number_csv",
            "In a comma-separated integer array where every value appears twice except one, return the single value.",
            "int",
            [{"name": "nums", "type": "string"}],
            "int single_number_csv(const char *nums) {\n    int x = 0;\n    int i = 0;\n    while (nums[i] != '\\0') {\n        int sign = 1;\n        if (nums[i] == '-') { sign = -1; i++; }\n        int v = 0;\n        while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; }\n        x ^= sign * v;\n        if (nums[i] == ',') i++;\n    }\n    return x;\n}",
            "class SingleNumberCsv {\n    public static int single_number_csv(String nums) {\n        int x = 0;\n        for (String p : nums.split(\",\")) x ^= Integer.parseInt(p);\n        return x;\n    }\n}",
            "pub fn single_number_csv(nums: &str) -> i32 {\n    let mut x = 0;\n    for p in nums.split(',') { x ^= p.parse::<i32>().unwrap(); }\n    x\n}",
            [
                {"kind": "positive", "input": {"nums": "2,2,1"}, "expected": 1},
                {"kind": "positive", "input": {"nums": "4,1,2,1,2"}, "expected": 4},
                {"kind": "positive", "input": {"nums": "1"}, "expected": 1},
                {"kind": "positive", "input": {"nums": "-1,2,2"}, "expected": -1},
            ],
            "leetcode:single-number",
            ["Input is nonempty.", "Exactly one value appears once and every other value appears twice.", "Values are base-10 integers with no spaces.", "Return the unique value."],
        ),
        Problem(
            "move_zeroes_csv",
            "Move all zeroes in comma-separated integer array `nums` to the end while preserving nonzero order.",
            "string",
            [{"name": "nums", "type": "string"}],
            "char *move_zeroes_csv(const char *nums) {\n    int values[128];\n    int n = 0, i = 0;\n    while (nums[i] != '\\0') { int sign = 1; if (nums[i] == '-') { sign = -1; i++; } int v = 0; while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } values[n++] = sign * v; if (nums[i] == ',') i++; }\n    char *out = (char *)malloc(512);\n    int pos = 0, first = 1, zeros = 0;\n    for (int j = 0; j < n; j++) if (values[j] == 0) zeros++; else { pos += sprintf(out + pos, \"%s%d\", first ? \"\" : \",\", values[j]); first = 0; }\n    for (int j = 0; j < zeros; j++) { pos += sprintf(out + pos, \"%s0\", first ? \"\" : \",\"); first = 0; }\n    out[pos] = '\\0';\n    return out;\n}",
            "class MoveZeroesCsv {\n    public static String move_zeroes_csv(String nums) {\n        if (nums.isEmpty()) return \"\";\n        String[] parts = nums.split(\",\");\n        StringBuilder out = new StringBuilder();\n        int zeros = 0;\n        for (String p : parts) { int v = Integer.parseInt(p); if (v == 0) zeros++; else { if (out.length() > 0) out.append(','); out.append(v); } }\n        for (int i = 0; i < zeros; i++) { if (out.length() > 0) out.append(','); out.append(0); }\n        return out.toString();\n    }\n}",
            "pub fn move_zeroes_csv(nums: &str) -> String {\n    if nums.is_empty() { return String::new(); }\n    let values: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect();\n    let mut out: Vec<String> = Vec::new(); let mut zeros = 0;\n    for v in values { if v == 0 { zeros += 1; } else { out.push(v.to_string()); } }\n    for _ in 0..zeros { out.push(\"0\".to_string()); }\n    out.join(\",\")\n}",
            [
                {"kind": "positive", "input": {"nums": "0,1,0,3,12"}, "expected": "1,3,12,0,0"},
                {"kind": "positive", "input": {"nums": "0"}, "expected": "0"},
                {"kind": "positive", "input": {"nums": "1,2,3"}, "expected": "1,2,3"},
                {"kind": "negative", "input": {"nums": ""}, "expected": ""},
                {"kind": "positive", "input": {"nums": "0,-1,0,2"}, "expected": "-1,2,0,0"},
            ],
            "leetcode:move-zeroes",
            ["`nums` is comma-separated base-10 integers with no spaces.", "The empty string represents an empty array.", "Preserve relative order of nonzero values.", "Return the transformed array encoding."],
        ),
        Problem(
            "best_stock_profit_csv",
            "Given daily prices encoded as comma-separated integers, return the maximum profit from one buy followed by one sell.",
            "int",
            [{"name": "prices", "type": "string"}],
            "int best_stock_profit_csv(const char *prices) {\n    int minp = 0, best = 0, seen = 0, i = 0;\n    while (prices[i] != '\\0') { int v = 0; while (prices[i] >= '0' && prices[i] <= '9') { v = v * 10 + prices[i] - '0'; i++; } if (!seen || v < minp) minp = v; if (v - minp > best) best = v - minp; seen = 1; if (prices[i] == ',') i++; }\n    return best;\n}",
            "class BestStockProfitCsv {\n    public static int best_stock_profit_csv(String prices) {\n        if (prices.isEmpty()) return 0;\n        int minp = 0, best = 0; boolean seen = false;\n        for (String p : prices.split(\",\")) { int v = Integer.parseInt(p); if (!seen || v < minp) minp = v; if (v - minp > best) best = v - minp; seen = true; }\n        return best;\n    }\n}",
            "pub fn best_stock_profit_csv(prices: &str) -> i32 {\n    if prices.is_empty() { return 0; }\n    let mut minp = 0; let mut best = 0; let mut seen = false;\n    for p in prices.split(',') { let v = p.parse::<i32>().unwrap(); if !seen || v < minp { minp = v; } if v - minp > best { best = v - minp; } seen = true; }\n    best\n}",
            [
                {"kind": "positive", "input": {"prices": "7,1,5,3,6,4"}, "expected": 5},
                {"kind": "negative", "input": {"prices": "7,6,4,3,1"}, "expected": 0},
                {"kind": "positive", "input": {"prices": "1,2"}, "expected": 1},
                {"kind": "negative", "input": {"prices": ""}, "expected": 0},
            ],
            "leetcode:best-time-to-buy-and-sell-stock",
            ["Prices are nonnegative integers.", "Only one buy and one later sell are allowed.", "Return `0` if no profitable transaction exists.", "The empty string represents no prices and returns `0`."],
        ),
        Problem(
            "merge_strings_alternately_ascii",
            "Merge `word1` and `word2` by alternating characters, starting with `word1`.",
            "string",
            [{"name": "word1", "type": "string"}, {"name": "word2", "type": "string"}],
            "char *merge_strings_alternately_ascii(const char *word1, const char *word2) {\n    int n = 0, m = 0;\n    while (word1[n] != '\\0') n++;\n    while (word2[m] != '\\0') m++;\n    char *out = (char *)malloc((unsigned long)n + (unsigned long)m + 1);\n    int pos = 0;\n    int limit = n > m ? n : m;\n    for (int i = 0; i < limit; i++) { if (i < n) out[pos++] = word1[i]; if (i < m) out[pos++] = word2[i]; }\n    out[pos] = '\\0';\n    return out;\n}",
            "class MergeStringsAlternatelyAscii {\n    public static String merge_strings_alternately_ascii(String word1, String word2) {\n        StringBuilder out = new StringBuilder();\n        int limit = word1.length() > word2.length() ? word1.length() : word2.length();\n        for (int i = 0; i < limit; i++) { if (i < word1.length()) out.append(word1.charAt(i)); if (i < word2.length()) out.append(word2.charAt(i)); }\n        return out.toString();\n    }\n}",
            "pub fn merge_strings_alternately_ascii(word1: &str, word2: &str) -> String {\n    let a = word1.as_bytes(); let b = word2.as_bytes(); let mut out: Vec<u8> = Vec::new(); let limit = if a.len() > b.len() { a.len() } else { b.len() };\n    for i in 0..limit { if i < a.len() { out.push(a[i]); } if i < b.len() { out.push(b[i]); } }\n    String::from_utf8(out).unwrap()\n}",
            [
                {"kind": "positive", "input": {"word1": "abc", "word2": "pqr"}, "expected": "apbqcr"},
                {"kind": "positive", "input": {"word1": "ab", "word2": "pqrs"}, "expected": "apbqrs"},
                {"kind": "positive", "input": {"word1": "abcd", "word2": "pq"}, "expected": "apbqcd"},
                {"kind": "negative", "input": {"word1": "", "word2": "xy"}, "expected": "xy"},
            ],
            "leetcode:merge-strings-alternately",
            ["Inputs are ASCII strings.", "Take one character from `word1`, then one from `word2`, repeatedly.", "Append the remaining suffix of the longer string.", "The empty string is allowed."],
        ),
        Problem(
            "defang_ip_address",
            "Return the defanged form of an IPv4 address by replacing each `.` with `[.]`.",
            "string",
            [{"name": "address", "type": "string"}],
            "char *defang_ip_address(const char *address) {\n    int n = 0, dots = 0;\n    while (address[n] != '\\0') { if (address[n] == '.') dots++; n++; }\n    char *out = (char *)malloc((unsigned long)n + (unsigned long)dots * 2 + 1);\n    int pos = 0;\n    for (int i = 0; i < n; i++) { if (address[i] == '.') { out[pos++] = '['; out[pos++] = '.'; out[pos++] = ']'; } else out[pos++] = address[i]; }\n    out[pos] = '\\0';\n    return out;\n}",
            "class DefangIpAddress {\n    public static String defang_ip_address(String address) {\n        StringBuilder out = new StringBuilder();\n        for (int i = 0; i < address.length(); i++) { char c = address.charAt(i); if (c == '.') out.append(\"[.]\"); else out.append(c); }\n        return out.toString();\n    }\n}",
            "pub fn defang_ip_address(address: &str) -> String {\n    let mut out = String::new();\n    for c in address.chars() { if c == '.' { out.push_str(\"[.]\"); } else { out.push(c); } }\n    out\n}",
            [
                {"kind": "positive", "input": {"address": "1.1.1.1"}, "expected": "1[.]1[.]1[.]1"},
                {"kind": "positive", "input": {"address": "255.100.50.0"}, "expected": "255[.]100[.]50[.]0"},
                {"kind": "positive", "input": {"address": "0.0.0.0"}, "expected": "0[.]0[.]0[.]0"},
            ],
            "leetcode:defanging-an-ip-address",
            ["Input is an IPv4 address string.", "Replace every period with the three-character sequence `[.]`.", "All other characters are copied unchanged.", "Return the transformed string."],
        ),
        Problem(
            "number_steps_reduce_zero",
            "Return the number of steps needed to reduce nonnegative integer `num` to zero. If it is even, divide by two; otherwise subtract one.",
            "int",
            [{"name": "num", "type": "int"}],
            "int number_steps_reduce_zero(int num) {\n    int steps = 0;\n    while (num > 0) {\n        if (num % 2 == 0) num /= 2;\n        else num -= 1;\n        steps++;\n    }\n    return steps;\n}",
            "class NumberStepsReduceZero {\n    public static int number_steps_reduce_zero(int num) {\n        int steps = 0;\n        while (num > 0) {\n            if (num % 2 == 0) num /= 2;\n            else num -= 1;\n            steps++;\n        }\n        return steps;\n    }\n}",
            "pub fn number_steps_reduce_zero(mut num: i32) -> i32 {\n    let mut steps = 0;\n    while num > 0 { if num % 2 == 0 { num /= 2; } else { num -= 1; } steps += 1; }\n    steps\n}",
            [
                {"kind": "positive", "input": {"num": 14}, "expected": 6},
                {"kind": "positive", "input": {"num": 8}, "expected": 4},
                {"kind": "positive", "input": {"num": 123}, "expected": 12},
                {"kind": "negative", "input": {"num": 0}, "expected": 0},
            ],
            "leetcode:number-of-steps-to-reduce-a-number-to-zero",
            ["`num >= 0`.", "An even positive number is divided by two.", "An odd positive number is decremented by one.", "Return the number of operations until zero."],
        ),
        Problem(
            "subtract_product_and_sum_digits",
            "Return the product of decimal digits of `n` minus the sum of those digits.",
            "int",
            [{"name": "n", "type": "int"}],
            "int subtract_product_and_sum_digits(int n) {\n    int product = 1;\n    int sum = 0;\n    while (n > 0) {\n        int d = n % 10;\n        product *= d;\n        sum += d;\n        n /= 10;\n    }\n    return product - sum;\n}",
            "class SubtractProductAndSumDigits {\n    public static int subtract_product_and_sum_digits(int n) {\n        int product = 1, sum = 0;\n        while (n > 0) { int d = n % 10; product *= d; sum += d; n /= 10; }\n        return product - sum;\n    }\n}",
            "pub fn subtract_product_and_sum_digits(mut n: i32) -> i32 {\n    let mut product = 1; let mut sum = 0;\n    while n > 0 { let d = n % 10; product *= d; sum += d; n /= 10; }\n    product - sum\n}",
            [
                {"kind": "positive", "input": {"n": 234}, "expected": 15},
                {"kind": "positive", "input": {"n": 4421}, "expected": 21},
                {"kind": "positive", "input": {"n": 10}, "expected": -1},
                {"kind": "positive", "input": {"n": 9}, "expected": 0},
            ],
            "leetcode:subtract-the-product-and-sum-of-digits-of-an-integer",
            ["`n > 0`.", "Use the ordinary base-10 digits of `n`.", "Compute product and sum over all digits.", "Return product minus sum."],
        ),
        Problem(
            "xor_operation_array",
            "Build `nums[i] = start + 2*i` for `0 <= i < n` and return the XOR of all values.",
            "int",
            [{"name": "n", "type": "int"}, {"name": "start", "type": "int"}],
            "int xor_operation_array(int n, int start) {\n    int x = 0;\n    for (int i = 0; i < n; i++) x ^= start + 2 * i;\n    return x;\n}",
            "class XorOperationArray {\n    public static int xor_operation_array(int n, int start) {\n        int x = 0;\n        for (int i = 0; i < n; i++) x ^= start + 2 * i;\n        return x;\n    }\n}",
            "pub fn xor_operation_array(n: i32, start: i32) -> i32 {\n    let mut x = 0;\n    let mut i = 0;\n    while i < n { x ^= start + 2 * i; i += 1; }\n    x\n}",
            [
                {"kind": "positive", "input": {"n": 5, "start": 0}, "expected": 8},
                {"kind": "positive", "input": {"n": 4, "start": 3}, "expected": 8},
                {"kind": "positive", "input": {"n": 1, "start": 7}, "expected": 7},
                {"kind": "positive", "input": {"n": 10, "start": 5}, "expected": 2},
            ],
            "leetcode:xor-operation-in-an-array",
            ["`n >= 1`.", "The generated array has exactly `n` values.", "The `i`th value is `start + 2*i`.", "Return bitwise XOR of all generated values."],
        ),
        Problem(
            "balanced_string_split_count",
            "Return the maximum number of balanced substrings in a string containing only `L` and `R`.",
            "int",
            [{"name": "s", "type": "string"}],
            "int balanced_string_split_count(const char *s) {\n    int balance = 0;\n    int count = 0;\n    for (int i = 0; s[i] != '\\0'; i++) {\n        if (s[i] == 'L') balance++;\n        else balance--;\n        if (balance == 0) count++;\n    }\n    return count;\n}",
            "class BalancedStringSplitCount {\n    public static int balanced_string_split_count(String s) {\n        int balance = 0, count = 0;\n        for (int i = 0; i < s.length(); i++) { if (s.charAt(i) == 'L') balance++; else balance--; if (balance == 0) count++; }\n        return count;\n    }\n}",
            "pub fn balanced_string_split_count(s: &str) -> i32 {\n    let mut balance = 0; let mut count = 0;\n    for b in s.bytes() { if b == b'L' { balance += 1; } else { balance -= 1; } if balance == 0 { count += 1; } }\n    count\n}",
            [
                {"kind": "positive", "input": {"s": "RLRRLLRLRL"}, "expected": 4},
                {"kind": "positive", "input": {"s": "RLRRRLLRLL"}, "expected": 2},
                {"kind": "positive", "input": {"s": "LLLLRRRR"}, "expected": 1},
                {"kind": "positive", "input": {"s": "LR"}, "expected": 1},
            ],
            "leetcode:split-a-string-in-balanced-strings",
            ["Input contains only `L` and `R`.", "The full input is balanced.", "A balanced substring has the same number of `L` and `R` characters.", "Return the maximum count obtained by greedy left-to-right splitting."],
        ),
        Problem(
            "max_parentheses_depth",
            "Return the maximum nesting depth of parentheses in `s`.",
            "int",
            [{"name": "s", "type": "string"}],
            "int max_parentheses_depth(const char *s) {\n    int depth = 0;\n    int best = 0;\n    for (int i = 0; s[i] != '\\0'; i++) {\n        if (s[i] == '(') { depth++; if (depth > best) best = depth; }\n        else if (s[i] == ')') depth--;\n    }\n    return best;\n}",
            "class MaxParenthesesDepth {\n    public static int max_parentheses_depth(String s) {\n        int depth = 0, best = 0;\n        for (int i = 0; i < s.length(); i++) { char c = s.charAt(i); if (c == '(') { depth++; if (depth > best) best = depth; } else if (c == ')') depth--; }\n        return best;\n    }\n}",
            "pub fn max_parentheses_depth(s: &str) -> i32 {\n    let mut depth = 0; let mut best = 0;\n    for b in s.bytes() { if b == b'(' { depth += 1; if depth > best { best = depth; } } else if b == b')' { depth -= 1; } }\n    best\n}",
            [
                {"kind": "positive", "input": {"s": "(1+(2*3)+((8)/4))+1"}, "expected": 3},
                {"kind": "positive", "input": {"s": "(1)+((2))+(((3)))"}, "expected": 3},
                {"kind": "negative", "input": {"s": "1+2"}, "expected": 0},
                {"kind": "positive", "input": {"s": "((()))"}, "expected": 3},
            ],
            "leetcode:maximum-nesting-depth-of-the-parentheses",
            ["Input is a valid parentheses expression possibly containing other ASCII characters.", "Only `(` and `)` affect depth.", "Return `0` if there are no parentheses.", "Track maximum open-parenthesis count."],
        ),
        Problem(
            "count_asterisks_between_bars",
            "Count `*` characters that are not between a pair of vertical bars.",
            "int",
            [{"name": "s", "type": "string"}],
            "int count_asterisks_between_bars(const char *s) {\n    int inside = 0;\n    int count = 0;\n    for (int i = 0; s[i] != '\\0'; i++) {\n        if (s[i] == '|') inside = !inside;\n        else if (s[i] == '*' && !inside) count++;\n    }\n    return count;\n}",
            "class CountAsterisksBetweenBars {\n    public static int count_asterisks_between_bars(String s) {\n        boolean inside = false;\n        int count = 0;\n        for (int i = 0; i < s.length(); i++) { char c = s.charAt(i); if (c == '|') inside = !inside; else if (c == '*' && !inside) count++; }\n        return count;\n    }\n}",
            "pub fn count_asterisks_between_bars(s: &str) -> i32 {\n    let mut inside = false; let mut count = 0;\n    for b in s.bytes() { if b == b'|' { inside = !inside; } else if b == b'*' && !inside { count += 1; } }\n    count\n}",
            [
                {"kind": "positive", "input": {"s": "l|*e*et|c**o|*de|"}, "expected": 2},
                {"kind": "positive", "input": {"s": "iamprogrammer"}, "expected": 0},
                {"kind": "positive", "input": {"s": "yo|uar|e**|b|e***au|tifu|l"}, "expected": 5},
                {"kind": "positive", "input": {"s": "***"}, "expected": 3},
            ],
            "leetcode:count-asterisks",
            ["Bars occur in pairs.", "Characters between the first and second bar of each pair are ignored.", "Count only `*` characters outside ignored ranges.", "Other characters do not affect the count."],
        ),
        Problem(
            "running_sum_csv",
            "Return the running sum of comma-separated integer array `nums`.",
            "string",
            [{"name": "nums", "type": "string"}],
            "char *running_sum_csv(const char *nums) {\n    char *out = (char *)malloc(512);\n    int pos = 0, first = 1, sum = 0, i = 0;\n    while (nums[i] != '\\0') {\n        int sign = 1;\n        if (nums[i] == '-') { sign = -1; i++; }\n        int v = 0;\n        while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; }\n        sum += sign * v;\n        pos += sprintf(out + pos, \"%s%d\", first ? \"\" : \",\", sum);\n        first = 0;\n        if (nums[i] == ',') i++;\n    }\n    out[pos] = '\\0';\n    return out;\n}",
            "class RunningSumCsv {\n    public static String running_sum_csv(String nums) {\n        if (nums.isEmpty()) return \"\";\n        StringBuilder out = new StringBuilder();\n        int sum = 0;\n        for (String p : nums.split(\",\")) { sum += Integer.parseInt(p); if (out.length() > 0) out.append(','); out.append(sum); }\n        return out.toString();\n    }\n}",
            "pub fn running_sum_csv(nums: &str) -> String {\n    if nums.is_empty() { return String::new(); }\n    let mut sum = 0; let mut out: Vec<String> = Vec::new();\n    for p in nums.split(',') { sum += p.parse::<i32>().unwrap(); out.push(sum.to_string()); }\n    out.join(\",\")\n}",
            [
                {"kind": "positive", "input": {"nums": "1,2,3,4"}, "expected": "1,3,6,10"},
                {"kind": "positive", "input": {"nums": "1,1,1,1,1"}, "expected": "1,2,3,4,5"},
                {"kind": "positive", "input": {"nums": "3,1,2,10,1"}, "expected": "3,4,6,16,17"},
                {"kind": "negative", "input": {"nums": ""}, "expected": ""},
                {"kind": "positive", "input": {"nums": "-1,2,-3"}, "expected": "-1,1,-2"},
            ],
            "leetcode:running-sum-of-1d-array",
            ["`nums` is comma-separated base-10 integers with no spaces.", "The empty string represents an empty array.", "Each output value is the sum from index `0` through that index.", "Return the output as comma-separated integers."],
        ),
        Problem(
            "pivot_index_csv",
            "Return the leftmost pivot index of comma-separated integer array `nums`, or `-1` if none exists.",
            "int",
            [{"name": "nums", "type": "string"}],
            "int pivot_index_csv(const char *nums) {\n    int values[128];\n    int n = 0, total = 0, i = 0;\n    while (nums[i] != '\\0') { int sign = 1; if (nums[i] == '-') { sign = -1; i++; } int v = 0; while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } values[n++] = sign * v; total += sign * v; if (nums[i] == ',') i++; }\n    int left = 0;\n    for (int j = 0; j < n; j++) { if (left == total - left - values[j]) return j; left += values[j]; }\n    return -1;\n}",
            "class PivotIndexCsv {\n    public static int pivot_index_csv(String nums) {\n        if (nums.isEmpty()) return -1;\n        String[] parts = nums.split(\",\");\n        int total = 0;\n        for (String p : parts) total += Integer.parseInt(p);\n        int left = 0;\n        for (int i = 0; i < parts.length; i++) { int v = Integer.parseInt(parts[i]); if (left == total - left - v) return i; left += v; }\n        return -1;\n    }\n}",
            "pub fn pivot_index_csv(nums: &str) -> i32 {\n    if nums.is_empty() { return -1; }\n    let values: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect();\n    let total: i32 = values.iter().sum(); let mut left = 0;\n    for i in 0..values.len() { if left == total - left - values[i] { return i as i32; } left += values[i]; }\n    -1\n}",
            [
                {"kind": "positive", "input": {"nums": "1,7,3,6,5,6"}, "expected": 3},
                {"kind": "negative", "input": {"nums": "1,2,3"}, "expected": -1},
                {"kind": "positive", "input": {"nums": "2,1,-1"}, "expected": 0},
                {"kind": "negative", "input": {"nums": ""}, "expected": -1},
                {"kind": "positive", "input": {"nums": "0"}, "expected": 0},
            ],
            "leetcode:find-pivot-index",
            ["`nums` is comma-separated base-10 integers with no spaces.", "The empty string has no pivot and returns `-1`.", "A pivot has equal sum strictly to its left and strictly to its right.", "Return the leftmost pivot index."],
        ),
        Problem(
            "final_value_after_operations",
            "Starting from zero, apply comma-separated operations `++X`, `X++`, `--X`, or `X--` and return the final value.",
            "int",
            [{"name": "operations", "type": "string"}],
            "int final_value_after_operations(const char *operations) {\n    int value = 0;\n    int i = 0;\n    while (operations[i] != '\\0') {\n        if (operations[i] == '+' || operations[i + 1] == '+') value++;\n        else value--;\n        while (operations[i] != '\\0' && operations[i] != ',') i++;\n        if (operations[i] == ',') i++;\n    }\n    return value;\n}",
            "class FinalValueAfterOperations {\n    public static int final_value_after_operations(String operations) {\n        if (operations.isEmpty()) return 0;\n        int value = 0;\n        for (String op : operations.split(\",\")) { if (op.charAt(0) == '+' || op.charAt(1) == '+') value++; else value--; }\n        return value;\n    }\n}",
            "pub fn final_value_after_operations(operations: &str) -> i32 {\n    if operations.is_empty() { return 0; }\n    let mut value = 0;\n    for op in operations.split(',') { let b = op.as_bytes(); if b[0] == b'+' || b[1] == b'+' { value += 1; } else { value -= 1; } }\n    value\n}",
            [
                {"kind": "positive", "input": {"operations": "--X,X++,+X++"}, "expected": 1},
                {"kind": "positive", "input": {"operations": "++X,++X,X++"}, "expected": 3},
                {"kind": "positive", "input": {"operations": "X++,++X,--X,X--"}, "expected": 0},
                {"kind": "negative", "input": {"operations": ""}, "expected": 0},
            ],
            "leetcode:final-value-of-variable-after-performing-operations",
            ["`operations` is comma-separated with no spaces.", "Allowed operations are `++X`, `X++`, `--X`, and `X--`.", "Increment operations add one; decrement operations subtract one.", "The empty string represents no operations."],
        ),
        Problem(
            "restore_string_by_indices",
            "Restore a string by placing `s[i]` at index `indices[i]`; indices are comma-separated integers.",
            "string",
            [{"name": "s", "type": "string"}, {"name": "indices", "type": "string"}],
            "char *restore_string_by_indices(const char *s, const char *indices) {\n    int n = 0;\n    while (s[n] != '\\0') n++;\n    char *out = (char *)malloc((unsigned long)n + 1);\n    int pos = 0;\n    int i = 0;\n    while (indices[i] != '\\0') {\n        int v = 0;\n        while (indices[i] >= '0' && indices[i] <= '9') { v = v * 10 + indices[i] - '0'; i++; }\n        out[v] = s[pos++];\n        if (indices[i] == ',') i++;\n    }\n    out[n] = '\\0';\n    return out;\n}",
            "class RestoreStringByIndices {\n    public static String restore_string_by_indices(String s, String indices) {\n        char[] out = new char[s.length()];\n        String[] parts = indices.split(\",\");\n        for (int i = 0; i < parts.length; i++) out[Integer.parseInt(parts[i])] = s.charAt(i);\n        return new String(out);\n    }\n}",
            "pub fn restore_string_by_indices(s: &str, indices: &str) -> String {\n    let sb = s.as_bytes();\n    let parts: Vec<usize> = indices.split(',').map(|x| x.parse::<usize>().unwrap()).collect();\n    let mut out = vec![0u8; sb.len()];\n    for i in 0..sb.len() { out[parts[i]] = sb[i]; }\n    String::from_utf8(out).unwrap()\n}",
            [
                {"kind": "positive", "input": {"s": "codeleet", "indices": "4,5,6,7,0,2,1,3"}, "expected": "leetcode"},
                {"kind": "positive", "input": {"s": "abc", "indices": "0,1,2"}, "expected": "abc"},
                {"kind": "positive", "input": {"s": "aiohn", "indices": "3,1,4,2,0"}, "expected": "nihao"},
                {"kind": "positive", "input": {"s": "a", "indices": "0"}, "expected": "a"},
            ],
            "leetcode:shuffle-string",
            ["`indices` is a permutation of `0..len(s)-1`.", "`indices` is comma-separated with no spaces.", "Return a string `out` such that `out[indices[i]] == s[i]`.", "Input strings are ASCII."],
        ),
        Problem(
            "count_good_pairs_csv",
            "Return the number of index pairs `(i,j)` with `i < j` and equal values in comma-separated integer array `nums`.",
            "int",
            [{"name": "nums", "type": "string"}],
            "int count_good_pairs_csv(const char *nums) {\n    int values[128];\n    int n = 0, i = 0;\n    while (nums[i] != '\\0') { int sign = 1; if (nums[i] == '-') { sign = -1; i++; } int v = 0; while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } values[n++] = sign * v; if (nums[i] == ',') i++; }\n    int count = 0;\n    for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) if (values[a] == values[b]) count++;\n    return count;\n}",
            "class CountGoodPairsCsv {\n    public static int count_good_pairs_csv(String nums) {\n        if (nums.isEmpty()) return 0;\n        String[] parts = nums.split(\",\");\n        int count = 0;\n        for (int i = 0; i < parts.length; i++) for (int j = i + 1; j < parts.length; j++) if (parts[i].equals(parts[j])) count++;\n        return count;\n    }\n}",
            "pub fn count_good_pairs_csv(nums: &str) -> i32 {\n    if nums.is_empty() { return 0; }\n    let values: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect();\n    let mut count = 0;\n    for i in 0..values.len() { for j in i + 1..values.len() { if values[i] == values[j] { count += 1; } } }\n    count\n}",
            [
                {"kind": "positive", "input": {"nums": "1,2,3,1,1,3"}, "expected": 4},
                {"kind": "positive", "input": {"nums": "1,1,1,1"}, "expected": 6},
                {"kind": "negative", "input": {"nums": "1,2,3"}, "expected": 0},
                {"kind": "negative", "input": {"nums": ""}, "expected": 0},
                {"kind": "positive", "input": {"nums": "-1,-1,2,-1"}, "expected": 3},
            ],
            "leetcode:number-of-good-pairs",
            ["`nums` is comma-separated base-10 integers with no spaces.", "The empty string represents an empty array.", "Count pairs of distinct indices with equal values.", "Return the pair count, not the values."],
        ),
        Problem(
            "formal_array_sum_csv",
            "Return the sum of all values in comma-separated integer array `nums`.",
            "int",
            [{"name": "nums", "type": "string"}],
            "int formal_array_sum_csv(const char *nums) {\n    int sum = 0;\n    int i = 0;\n    while (nums[i] != '\\0') {\n        int sign = 1;\n        if (nums[i] == '-') { sign = -1; i++; }\n        int v = 0;\n        while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; }\n        sum += sign * v;\n        if (nums[i] == ',') i++;\n    }\n    return sum;\n}",
            "class FormalArraySumCsv {\n    public static int formal_array_sum_csv(String nums) {\n        if (nums.isEmpty()) return 0;\n        int sum = 0;\n        for (String p : nums.split(\",\")) sum += Integer.parseInt(p);\n        return sum;\n    }\n}",
            "pub fn formal_array_sum_csv(nums: &str) -> i32 {\n    if nums.is_empty() { return 0; }\n    nums.split(',').map(|x| x.parse::<i32>().unwrap()).sum()\n}",
            [
                {"kind": "positive", "input": {"nums": "1,2,3"}, "expected": 6},
                {"kind": "positive", "input": {"nums": "-1,2,-3"}, "expected": -2},
                {"kind": "negative", "input": {"nums": ""}, "expected": 0},
                {"kind": "positive", "input": {"nums": "5"}, "expected": 5},
                {"kind": "positive", "input": {"nums": "0,0,0"}, "expected": 0},
            ],
            "formalbench:array-sum",
            ["`nums` is comma-separated base-10 integers with no spaces.", "The empty string represents an empty array.", "Return the arithmetic sum.", "The result fits in a signed 32-bit integer."],
        ),
        Problem(
            "formal_count_positive_csv",
            "Return how many values in comma-separated integer array `nums` are strictly positive.",
            "int",
            [{"name": "nums", "type": "string"}],
            "int formal_count_positive_csv(const char *nums) {\n    int count = 0;\n    int i = 0;\n    while (nums[i] != '\\0') {\n        int sign = 1;\n        if (nums[i] == '-') { sign = -1; i++; }\n        int v = 0;\n        while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; }\n        if (sign * v > 0) count++;\n        if (nums[i] == ',') i++;\n    }\n    return count;\n}",
            "class FormalCountPositiveCsv {\n    public static int formal_count_positive_csv(String nums) {\n        if (nums.isEmpty()) return 0;\n        int count = 0;\n        for (String p : nums.split(\",\")) if (Integer.parseInt(p) > 0) count++;\n        return count;\n    }\n}",
            "pub fn formal_count_positive_csv(nums: &str) -> i32 {\n    if nums.is_empty() { return 0; }\n    nums.split(',').filter(|x| x.parse::<i32>().unwrap() > 0).count() as i32\n}",
            [
                {"kind": "positive", "input": {"nums": "1,-2,3,0"}, "expected": 2},
                {"kind": "negative", "input": {"nums": "-1,-2,0"}, "expected": 0},
                {"kind": "negative", "input": {"nums": ""}, "expected": 0},
                {"kind": "positive", "input": {"nums": "5,6,7"}, "expected": 3},
            ],
            "formalbench:count-positive",
            ["`nums` is comma-separated base-10 integers with no spaces.", "The empty string represents an empty array.", "Zero is not positive.", "Return the count of strictly positive values."],
        ),
        Problem(
            "formal_reverse_ascii",
            "Return the reverse of ASCII string `s`.",
            "string",
            [{"name": "s", "type": "string"}],
            "char *formal_reverse_ascii(const char *s) {\n    int n = 0;\n    while (s[n] != '\\0') n++;\n    char *out = (char *)malloc((unsigned long)n + 1);\n    for (int i = 0; i < n; i++) out[i] = s[n - 1 - i];\n    out[n] = '\\0';\n    return out;\n}",
            "class FormalReverseAscii {\n    public static String formal_reverse_ascii(String s) {\n        StringBuilder out = new StringBuilder();\n        for (int i = s.length() - 1; i >= 0; i--) out.append(s.charAt(i));\n        return out.toString();\n    }\n}",
            "pub fn formal_reverse_ascii(s: &str) -> String {\n    s.chars().rev().collect()\n}",
            [
                {"kind": "positive", "input": {"s": "abc"}, "expected": "cba"},
                {"kind": "negative", "input": {"s": ""}, "expected": ""},
                {"kind": "positive", "input": {"s": "a"}, "expected": "a"},
                {"kind": "positive", "input": {"s": "hello!"}, "expected": "!olleh"},
            ],
            "formalbench:string-reverse",
            ["Input is an ASCII string.", "The empty string reverses to the empty string.", "Return a new reversed string.", "Do not drop punctuation or spaces."],
        ),
        Problem(
            "jewels_and_stones_ascii",
            "Return how many characters in `stones` are also present in `jewels`.",
            "int",
            [{"name": "jewels", "type": "string"}, {"name": "stones", "type": "string"}],
            "int jewels_and_stones_ascii(const char *jewels, const char *stones) {\n    int count = 0;\n    for (int i = 0; stones[i] != '\\0'; i++) {\n        for (int j = 0; jewels[j] != '\\0'; j++) if (stones[i] == jewels[j]) { count++; break; }\n    }\n    return count;\n}",
            "class JewelsAndStonesAscii {\n    public static int jewels_and_stones_ascii(String jewels, String stones) {\n        int count = 0;\n        for (int i = 0; i < stones.length(); i++) if (jewels.indexOf(stones.charAt(i)) >= 0) count++;\n        return count;\n    }\n}",
            "pub fn jewels_and_stones_ascii(jewels: &str, stones: &str) -> i32 {\n    let jb = jewels.as_bytes(); let mut count = 0;\n    for s in stones.bytes() { if jb.contains(&s) { count += 1; } }\n    count\n}",
            [
                {"kind": "positive", "input": {"jewels": "aA", "stones": "aAAbbbb"}, "expected": 3},
                {"kind": "negative", "input": {"jewels": "z", "stones": "ZZ"}, "expected": 0},
                {"kind": "positive", "input": {"jewels": "", "stones": "abc"}, "expected": 0},
                {"kind": "positive", "input": {"jewels": "abc", "stones": "cabd"}, "expected": 3},
            ],
            "leetcode:jewels-and-stones",
            ["Inputs are ASCII strings.", "`jewels` characters are distinct in the original task, but this implementation also handles duplicates.", "Count every stone whose character appears in `jewels`.", "Case is significant."],
        ),
        Problem(
            "goal_parser_interpret",
            "Interpret a command string where `G` maps to `G`, `()` maps to `o`, and `(al)` maps to `al`.",
            "string",
            [{"name": "command", "type": "string"}],
            "char *goal_parser_interpret(const char *command) {\n    int n = 0;\n    while (command[n] != '\\0') n++;\n    char *out = (char *)malloc((unsigned long)n + 1);\n    int pos = 0;\n    for (int i = 0; command[i] != '\\0'; ) {\n        if (command[i] == 'G') { out[pos++] = 'G'; i++; }\n        else if (command[i + 1] == ')') { out[pos++] = 'o'; i += 2; }\n        else { out[pos++] = 'a'; out[pos++] = 'l'; i += 4; }\n    }\n    out[pos] = '\\0';\n    return out;\n}",
            "class GoalParserInterpret {\n    public static String goal_parser_interpret(String command) {\n        StringBuilder out = new StringBuilder();\n        for (int i = 0; i < command.length(); ) { if (command.charAt(i) == 'G') { out.append('G'); i++; } else if (command.charAt(i + 1) == ')') { out.append('o'); i += 2; } else { out.append(\"al\"); i += 4; } }\n        return out.toString();\n    }\n}",
            "pub fn goal_parser_interpret(command: &str) -> String {\n    let b = command.as_bytes(); let mut out = String::new(); let mut i = 0usize;\n    while i < b.len() { if b[i] == b'G' { out.push('G'); i += 1; } else if b[i + 1] == b')' { out.push('o'); i += 2; } else { out.push_str(\"al\"); i += 4; } }\n    out\n}",
            [
                {"kind": "positive", "input": {"command": "G()(al)"}, "expected": "Goal"},
                {"kind": "positive", "input": {"command": "G()()()()(al)"}, "expected": "Gooooal"},
                {"kind": "positive", "input": {"command": "(al)G(al)()()G"}, "expected": "alGalooG"},
            ],
            "leetcode:goal-parser-interpretation",
            ["Input is a concatenation of tokens `G`, `()`, and `(al)`.", "Map tokens exactly as specified.", "Return the concatenated interpreted string.", "No other characters appear."],
        ),
        Problem(
            "richest_customer_wealth_rows",
            "Rows of customer accounts are separated by `;`, values in each row by `,`; return the largest row sum.",
            "int",
            [{"name": "accounts", "type": "string"}],
            "int richest_customer_wealth_rows(const char *accounts) {\n    int best = 0, sum = 0, i = 0;\n    while (1) {\n        int v = 0;\n        while (accounts[i] >= '0' && accounts[i] <= '9') { v = v * 10 + accounts[i] - '0'; i++; }\n        sum += v;\n        if (accounts[i] == ';' || accounts[i] == '\\0') { if (sum > best) best = sum; sum = 0; }\n        if (accounts[i] == '\\0') break;\n        i++;\n    }\n    return best;\n}",
            "class RichestCustomerWealthRows {\n    public static int richest_customer_wealth_rows(String accounts) {\n        int best = 0;\n        for (String row : accounts.split(\";\")) { int sum = 0; for (String p : row.split(\",\")) sum += Integer.parseInt(p); if (sum > best) best = sum; }\n        return best;\n    }\n}",
            "pub fn richest_customer_wealth_rows(accounts: &str) -> i32 {\n    let mut best = 0;\n    for row in accounts.split(';') { let sum: i32 = row.split(',').map(|x| x.parse::<i32>().unwrap()).sum(); if sum > best { best = sum; } }\n    best\n}",
            [
                {"kind": "positive", "input": {"accounts": "1,2,3;3,2,1"}, "expected": 6},
                {"kind": "positive", "input": {"accounts": "1,5;7,3;3,5"}, "expected": 10},
                {"kind": "positive", "input": {"accounts": "2,8,7;7,1,3;1,9,5"}, "expected": 17},
            ],
            "leetcode:richest-customer-wealth",
            ["Rows are separated by semicolons.", "Values are nonnegative base-10 integers.", "Every row is nonempty.", "Return the maximum row sum."],
        ),
        Problem(
            "sentence_is_pangram_ascii",
            "Return true if lowercase sentence `sentence` contains every English letter at least once.",
            "bool",
            [{"name": "sentence", "type": "string"}],
            "int sentence_is_pangram_ascii(const char *sentence) {\n    int seen[26] = {0};\n    int count = 0;\n    for (int i = 0; sentence[i] != '\\0'; i++) { int k = sentence[i] - 'a'; if (!seen[k]) { seen[k] = 1; count++; } }\n    return count == 26;\n}",
            "class SentenceIsPangramAscii {\n    public static boolean sentence_is_pangram_ascii(String sentence) {\n        boolean[] seen = new boolean[26];\n        int count = 0;\n        for (int i = 0; i < sentence.length(); i++) { int k = sentence.charAt(i) - 'a'; if (!seen[k]) { seen[k] = true; count++; } }\n        return count == 26;\n    }\n}",
            "pub fn sentence_is_pangram_ascii(sentence: &str) -> bool {\n    let mut seen = [false; 26]; let mut count = 0;\n    for b in sentence.bytes() { let k = (b - b'a') as usize; if !seen[k] { seen[k] = true; count += 1; } }\n    count == 26\n}",
            [
                {"kind": "positive", "input": {"sentence": "thequickbrownfoxjumpsoverthelazydog"}, "expected": True},
                {"kind": "negative", "input": {"sentence": "leetcode"}, "expected": False},
                {"kind": "positive", "input": {"sentence": "abcdefghijklmnopqrstuvwxyz"}, "expected": True},
            ],
            "leetcode:check-if-the-sentence-is-pangram",
            ["Input contains only lowercase English letters.", "Return true exactly when all 26 letters appear.", "Repeated letters are allowed.", "The empty string is not pangram."],
        ),
        Problem(
            "decode_xored_array_csv",
            "Given comma-separated XOR-encoded values and the first original value, return the decoded array.",
            "string",
            [{"name": "encoded", "type": "string"}, {"name": "first", "type": "int"}],
            "char *decode_xored_array_csv(const char *encoded, int first) {\n    char *out = (char *)malloc(512);\n    int pos = sprintf(out, \"%d\", first);\n    int cur = first;\n    int i = 0;\n    while (encoded[i] != '\\0') { int v = 0; while (encoded[i] >= '0' && encoded[i] <= '9') { v = v * 10 + encoded[i] - '0'; i++; } cur = cur ^ v; pos += sprintf(out + pos, \",%d\", cur); if (encoded[i] == ',') i++; }\n    return out;\n}",
            "class DecodeXoredArrayCsv {\n    public static String decode_xored_array_csv(String encoded, int first) {\n        StringBuilder out = new StringBuilder();\n        int cur = first;\n        out.append(cur);\n        if (!encoded.isEmpty()) for (String p : encoded.split(\",\")) { cur ^= Integer.parseInt(p); out.append(',').append(cur); }\n        return out.toString();\n    }\n}",
            "pub fn decode_xored_array_csv(encoded: &str, first: i32) -> String {\n    let mut cur = first; let mut out = vec![cur.to_string()];\n    if !encoded.is_empty() { for p in encoded.split(',') { cur ^= p.parse::<i32>().unwrap(); out.push(cur.to_string()); } }\n    out.join(\",\")\n}",
            [
                {"kind": "positive", "input": {"encoded": "1,2,3", "first": 1}, "expected": "1,0,2,1"},
                {"kind": "positive", "input": {"encoded": "6,2,7,3", "first": 4}, "expected": "4,2,0,7,4"},
                {"kind": "negative", "input": {"encoded": "", "first": 5}, "expected": "5"},
            ],
            "leetcode:decode-xored-array",
            ["`encoded[i] = arr[i] XOR arr[i+1]`.", "`encoded` is comma-separated nonnegative integers.", "The empty string means the original array only contains `first`.", "Return the decoded array as comma-separated integers."],
        ),
        Problem(
            "formal_array_max_abs_csv",
            "Return the largest absolute value in nonempty comma-separated integer array `nums`.",
            "int",
            [{"name": "nums", "type": "string"}],
            "int formal_array_max_abs_csv(const char *nums) {\n    int best = 0, i = 0;\n    while (nums[i] != '\\0') { int sign = 1; if (nums[i] == '-') { sign = -1; i++; } int v = 0; while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } v *= sign; if (v < 0) v = -v; if (v > best) best = v; if (nums[i] == ',') i++; }\n    return best;\n}",
            "class FormalArrayMaxAbsCsv {\n    public static int formal_array_max_abs_csv(String nums) {\n        int best = 0;\n        for (String p : nums.split(\",\")) { int v = Integer.parseInt(p); if (v < 0) v = -v; if (v > best) best = v; }\n        return best;\n    }\n}",
            "pub fn formal_array_max_abs_csv(nums: &str) -> i32 {\n    nums.split(',').map(|x| { let mut v = x.parse::<i32>().unwrap(); if v < 0 { v = -v; } v }).max().unwrap()\n}",
            [
                {"kind": "positive", "input": {"nums": "1,-5,3"}, "expected": 5},
                {"kind": "positive", "input": {"nums": "-2,-8,-1"}, "expected": 8},
                {"kind": "positive", "input": {"nums": "0"}, "expected": 0},
                {"kind": "positive", "input": {"nums": "7,6"}, "expected": 7},
            ],
            "formalbench:array-max-abs",
            ["`nums` is nonempty and comma-separated.", "Negative values are allowed.", "Return the maximum absolute value.", "The absolute values fit in signed 32-bit integer range."],
        ),
        Problem(
            "formal_array_all_nonnegative_csv",
            "Return true if every value in comma-separated integer array `nums` is nonnegative.",
            "bool",
            [{"name": "nums", "type": "string"}],
            "int formal_array_all_nonnegative_csv(const char *nums) {\n    int i = 0;\n    while (nums[i] != '\\0') { int sign = 1; if (nums[i] == '-') { sign = -1; i++; } int v = 0; while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } if (sign * v < 0) return 0; if (nums[i] == ',') i++; }\n    return 1;\n}",
            "class FormalArrayAllNonnegativeCsv {\n    public static boolean formal_array_all_nonnegative_csv(String nums) {\n        if (nums.isEmpty()) return true;\n        for (String p : nums.split(\",\")) if (Integer.parseInt(p) < 0) return false;\n        return true;\n    }\n}",
            "pub fn formal_array_all_nonnegative_csv(nums: &str) -> bool {\n    if nums.is_empty() { return true; }\n    nums.split(',').all(|x| x.parse::<i32>().unwrap() >= 0)\n}",
            [
                {"kind": "positive", "input": {"nums": "0,1,2"}, "expected": True},
                {"kind": "negative", "input": {"nums": "1,-1,2"}, "expected": False},
                {"kind": "positive", "input": {"nums": ""}, "expected": True},
                {"kind": "negative", "input": {"nums": "-5"}, "expected": False},
            ],
            "formalbench:array-all-nonnegative",
            ["The empty array is considered all nonnegative.", "Values are comma-separated with no spaces.", "Zero is nonnegative.", "Return false if any value is below zero."],
        ),
        Problem(
            "formal_string_count_lowercase",
            "Return how many lowercase ASCII letters appear in `s`.",
            "int",
            [{"name": "s", "type": "string"}],
            "int formal_string_count_lowercase(const char *s) {\n    int count = 0;\n    for (int i = 0; s[i] != '\\0'; i++) if (s[i] >= 'a' && s[i] <= 'z') count++;\n    return count;\n}",
            "class FormalStringCountLowercase {\n    public static int formal_string_count_lowercase(String s) {\n        int count = 0;\n        for (int i = 0; i < s.length(); i++) if (s.charAt(i) >= 'a' && s.charAt(i) <= 'z') count++;\n        return count;\n    }\n}",
            "pub fn formal_string_count_lowercase(s: &str) -> i32 {\n    s.bytes().filter(|&b| b >= b'a' && b <= b'z').count() as i32\n}",
            [
                {"kind": "positive", "input": {"s": "abcXYZ"}, "expected": 3},
                {"kind": "negative", "input": {"s": ""}, "expected": 0},
                {"kind": "negative", "input": {"s": "ABC123"}, "expected": 0},
                {"kind": "positive", "input": {"s": "hello!"}, "expected": 5},
            ],
            "formalbench:string-count-lowercase",
            ["Input is ASCII.", "Only `a` through `z` count.", "Uppercase letters and digits do not count.", "The empty string returns zero."],
        ),
        Problem(
            "formal_string_has_space",
            "Return true if ASCII string `s` contains at least one space character.",
            "bool",
            [{"name": "s", "type": "string"}],
            "int formal_string_has_space(const char *s) {\n    for (int i = 0; s[i] != '\\0'; i++) if (s[i] == ' ') return 1;\n    return 0;\n}",
            "class FormalStringHasSpace {\n    public static boolean formal_string_has_space(String s) {\n        for (int i = 0; i < s.length(); i++) if (s.charAt(i) == ' ') return true;\n        return false;\n    }\n}",
            "pub fn formal_string_has_space(s: &str) -> bool {\n    s.bytes().any(|b| b == b' ')\n}",
            [
                {"kind": "positive", "input": {"s": "a b"}, "expected": True},
                {"kind": "negative", "input": {"s": "abc"}, "expected": False},
                {"kind": "negative", "input": {"s": ""}, "expected": False},
                {"kind": "positive", "input": {"s": " leading"}, "expected": True},
            ],
            "formalbench:string-has-space",
            ["Input is ASCII.", "Only the literal space character counts.", "Tabs are outside this task.", "Return false for the empty string."],
        ),
        Problem(
            "formal_digit_sum_string",
            "Return the sum of decimal digit characters in ASCII string `s`.",
            "int",
            [{"name": "s", "type": "string"}],
            "int formal_digit_sum_string(const char *s) {\n    int sum = 0;\n    for (int i = 0; s[i] != '\\0'; i++) if (s[i] >= '0' && s[i] <= '9') sum += s[i] - '0';\n    return sum;\n}",
            "class FormalDigitSumString {\n    public static int formal_digit_sum_string(String s) {\n        int sum = 0;\n        for (int i = 0; i < s.length(); i++) if (s.charAt(i) >= '0' && s.charAt(i) <= '9') sum += s.charAt(i) - '0';\n        return sum;\n    }\n}",
            "pub fn formal_digit_sum_string(s: &str) -> i32 {\n    s.bytes().filter(|&b| b >= b'0' && b <= b'9').map(|b| (b - b'0') as i32).sum()\n}",
            [
                {"kind": "positive", "input": {"s": "a1b2c3"}, "expected": 6},
                {"kind": "negative", "input": {"s": "abc"}, "expected": 0},
                {"kind": "positive", "input": {"s": "909"}, "expected": 18},
                {"kind": "negative", "input": {"s": ""}, "expected": 0},
            ],
            "formalbench:string-digit-sum",
            ["Input is ASCII.", "Only digit characters contribute.", "Non-digits are ignored.", "Return the arithmetic sum of digit values."],
        ),
    ]


def additional_qcp_compatible_problems() -> list[Problem]:
    """More beginner source-backed tasks whose C versions fit the QCP gate."""
    return [
        Problem(
            "sign_of_product_csv",
            "Return the sign of the product of comma-separated integers: `1`, `-1`, or `0`.",
            "int",
            [{"name": "nums", "type": "string"}],
            "int sign_of_product_csv(const char *nums) {\n    int sign = 1;\n    int i = 0;\n    while (nums[i] != '\\0') {\n        int neg = 0;\n        if (nums[i] == '-') { neg = 1; i++; }\n        int v = 0;\n        while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; }\n        if (v == 0) return 0;\n        if (neg) sign = -sign;\n        if (nums[i] == ',') i++;\n    }\n    return sign;\n}",
            "class SignOfProductCsv {\n    public static int sign_of_product_csv(String nums) {\n        if (nums.isEmpty()) return 1;\n        int sign = 1;\n        for (String p : nums.split(\",\")) { int v = Integer.parseInt(p); if (v == 0) return 0; if (v < 0) sign = -sign; }\n        return sign;\n    }\n}",
            "pub fn sign_of_product_csv(nums: &str) -> i32 {\n    if nums.is_empty() { return 1; }\n    let mut sign = 1;\n    for p in nums.split(',') { let v = p.parse::<i32>().unwrap(); if v == 0 { return 0; } if v < 0 { sign = -sign; } }\n    sign\n}",
            [
                {"kind": "positive", "input": {"nums": "-1,-2,-3,-4,3,2,1"}, "expected": 1},
                {"kind": "negative", "input": {"nums": "1,5,0,2,-3"}, "expected": 0},
                {"kind": "positive", "input": {"nums": "-1,1,-1,1,-1"}, "expected": -1},
                {"kind": "positive", "input": {"nums": ""}, "expected": 1},
            ],
            "leetcode:sign-of-the-product-of-an-array",
            ["The empty string is treated as an empty product with sign `1`.", "Return `0` if any value is zero.", "Return `-1` for an odd number of negative nonzero values.", "Return `1` otherwise."],
        ),
        Problem(
            "count_odds_interval",
            "Return how many odd integers lie in the inclusive interval `[low, high]`.",
            "int",
            [{"name": "low", "type": "int"}, {"name": "high", "type": "int"}],
            "int count_odds_interval(int low, int high) {\n    int count = 0;\n    for (int x = low; x <= high; x++) if (x % 2 != 0) count++;\n    return count;\n}",
            "class CountOddsInterval {\n    public static int count_odds_interval(int low, int high) {\n        int count = 0;\n        for (int x = low; x <= high; x++) if (x % 2 != 0) count++;\n        return count;\n    }\n}",
            "pub fn count_odds_interval(low: i32, high: i32) -> i32 {\n    let mut count = 0;\n    let mut x = low;\n    while x <= high { if x % 2 != 0 { count += 1; } x += 1; }\n    count\n}",
            [
                {"kind": "positive", "input": {"low": 3, "high": 7}, "expected": 3},
                {"kind": "positive", "input": {"low": 8, "high": 10}, "expected": 1},
                {"kind": "positive", "input": {"low": 0, "high": 0}, "expected": 0},
                {"kind": "positive", "input": {"low": 1, "high": 1}, "expected": 1},
            ],
            "leetcode:count-odd-numbers-in-an-interval-range",
            ["`low <= high`.", "Both interval endpoints are included.", "Negative values are outside this simplified task.", "Return the count, not the odd values."],
        ),
        Problem(
            "maximum_69_number",
            "Given a positive decimal integer containing only digits `6` and `9`, change at most one `6` to `9` to maximize it.",
            "int",
            [{"name": "num", "type": "int"}],
            "int maximum_69_number(int num) {\n    int place = 1;\n    int best = 0;\n    int temp = num;\n    while (temp > 0) {\n        int d = temp % 10;\n        if (d == 6) best = place;\n        place *= 10;\n        temp /= 10;\n    }\n    return num + best * 3;\n}",
            "class Maximum69Number {\n    public static int maximum_69_number(int num) {\n        int place = 1, best = 0, temp = num;\n        while (temp > 0) { int d = temp % 10; if (d == 6) best = place; place *= 10; temp /= 10; }\n        return num + best * 3;\n    }\n}",
            "pub fn maximum_69_number(num: i32) -> i32 {\n    let mut place = 1; let mut best = 0; let mut temp = num;\n    while temp > 0 { let d = temp % 10; if d == 6 { best = place; } place *= 10; temp /= 10; }\n    num + best * 3\n}",
            [
                {"kind": "positive", "input": {"num": 9669}, "expected": 9969},
                {"kind": "positive", "input": {"num": 9996}, "expected": 9999},
                {"kind": "positive", "input": {"num": 9999}, "expected": 9999},
                {"kind": "positive", "input": {"num": 6}, "expected": 9},
            ],
            "leetcode:maximum-69-number",
            ["`num` contains only decimal digits `6` and `9`.", "Change at most one digit.", "Changing the leftmost `6` gives the maximum result.", "If there is no `6`, return `num` unchanged."],
        ),
        Problem(
            "sum_multiples_3_5_7",
            "Return the sum of integers from `1` to `n` that are divisible by `3`, `5`, or `7`.",
            "int",
            [{"name": "n", "type": "int"}],
            "int sum_multiples_3_5_7(int n) {\n    int sum = 0;\n    for (int i = 1; i <= n; i++) if (i % 3 == 0 || i % 5 == 0 || i % 7 == 0) sum += i;\n    return sum;\n}",
            "class SumMultiples357 {\n    public static int sum_multiples_3_5_7(int n) {\n        int sum = 0;\n        for (int i = 1; i <= n; i++) if (i % 3 == 0 || i % 5 == 0 || i % 7 == 0) sum += i;\n        return sum;\n    }\n}",
            "pub fn sum_multiples_3_5_7(n: i32) -> i32 {\n    let mut sum = 0; let mut i = 1;\n    while i <= n { if i % 3 == 0 || i % 5 == 0 || i % 7 == 0 { sum += i; } i += 1; }\n    sum\n}",
            [
                {"kind": "positive", "input": {"n": 7}, "expected": 21},
                {"kind": "positive", "input": {"n": 10}, "expected": 40},
                {"kind": "negative", "input": {"n": 2}, "expected": 0},
                {"kind": "positive", "input": {"n": 20}, "expected": 119},
            ],
            "leetcode:sum-multiples",
            ["`n >= 0`.", "Include numbers divisible by at least one of 3, 5, or 7.", "Each qualifying number contributes once.", "Return `0` when no number qualifies."],
        ),
        Problem(
            "formal_string_count_letter_a",
            "Return how many lowercase `a` characters appear in ASCII string `s`.",
            "int",
            [{"name": "s", "type": "string"}],
            "int formal_string_count_letter_a(const char *s) {\n    int count = 0;\n    for (int i = 0; s[i] != '\\0'; i++) if (s[i] == 'a') count++;\n    return count;\n}",
            "class FormalStringCountLetterA {\n    public static int formal_string_count_letter_a(String s) {\n        int count = 0;\n        for (int i = 0; i < s.length(); i++) if (s.charAt(i) == 'a') count++;\n        return count;\n    }\n}",
            "pub fn formal_string_count_letter_a(s: &str) -> i32 {\n    let mut count = 0;\n    for b in s.bytes() { if b == b'a' { count += 1; } }\n    count\n}",
            [
                {"kind": "positive", "input": {"s": "banana"}, "expected": 3},
                {"kind": "negative", "input": {"s": "BBB"}, "expected": 0},
                {"kind": "negative", "input": {"s": ""}, "expected": 0},
                {"kind": "positive", "input": {"s": "aaaa"}, "expected": 4},
            ],
            "formalbench:string-count-char",
            ["Input is ASCII.", "Only lowercase `a` counts.", "Uppercase `A` does not count.", "The empty string returns zero."],
        ),
    ]


def main() -> None:
    shutil.rmtree(OUT, ignore_errors=True)
    for sub in ("c", "java", "rust", "tests"):
        (OUT / sub).mkdir(parents=True, exist_ok=True)
    manifest = {
        "source": "Beginner algorithm exercises rewritten locally from attributed sources",
        "style": "HumanEval-like",
        "not_used": ["HumanEval", "MBPP"],
        "languages": ["c", "java", "rust"],
        "requirements": ["single function", "standard library only", "shared tests"],
        "problems": [],
    }
    rejected = []
    for p in problems() + more_problems() + web_sourced_more_problems() + additional_qcp_compatible_problems():
        violations = qcp_scope_violations(p)
        if violations:
            rejected.append({"name": p.name, "violations": violations})
            continue
        top_up_tests(p)
        mock_needs = qcp_mock_contract_needs(p)
        for lang, code in (("c", p.c), ("java", p.java), ("rust", p.rust)):
            (OUT / lang / f"{p.name}.md").write_text(md(p, lang, code), encoding="utf-8")
        (OUT / "tests" / f"{p.name}.json").write_text(
            json.dumps(
                {
                    "name": p.name,
                    "return_type": p.return_type,
                    "params": p.params,
                    "tests": p.tests,
                    "source": source_meta(p.source_slug),
                },
                indent=2,
                ensure_ascii=False,
            )
            + "\n",
            encoding="utf-8",
        )
        meta = source_meta(p.source_slug)
        manifest["problems"].append({
            "name": p.name,
            "source": meta["name"],
            "source_slug": meta["slug"],
            "source_url": meta["url"],
            "license": meta["license"],
            "scope": "qcp_c_safe_shared_tests",
            "qcp_contract": "needs_mock_contract" if mock_needs else "direct",
            "mock_contract_needs": mock_needs,
        })
    manifest["scope"] = {
        "policy": "qcp_c_safe_shared_tests",
        "definition": "C/Java/Rust implementations must have matching shared-test behavior; the C implementation is the hard admission gate. QCP can support library calls when they are modeled as mock/extern functions with contracts. I/O and system interaction are filtered; library formatting/parsing/sorting calls are retained but marked as needs_mock_contract.",
        "rejected_count": len(rejected),
        "rejected": rejected,
    }
    (OUT / "manifest.json").write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    (OUT / "README.md").write_text(
        "# External HumanEval-like Single Function Dataset\n\n"
        f"- Problems: {len(manifest['problems'])}\n"
        "- Style: HumanEval-like short function tasks\n"
        "- Source: Exercism canonical-data-backed tasks plus local rewrites from LeetCode, Luogu, and FormalBench-style beginner problems\n"
        "- Not used: HumanEval, MBPP\n"
        "- Languages: C, Java, Rust\n"
        "- Constraint: one main function per problem; C implementation must be inside the current QCP-friendly subset\n"
        "- Scope: C/Java/Rust reference programs must behave identically on shared tests; C/QCP compatibility is the hard admission gate, while Java/Rust are behavior-preserving translations of the C task\n"
        "- QCP library calls: non-I/O library calls may be retained when they can be represented by mock/extern contracts; see `manifest.json` field `qcp_contract`\n"
        "- Tests: shared JSON files in `tests/`, about 10 cases per problem, derived from Exercism official canonical-data where available\n"
        "- Generation: `python3 scripts/generate_exercism_humaneval_like.py`\n"
        "- Validation: `python3 scripts/validate_exercism_humaneval_like.py`\n",
        encoding="utf-8",
    )
    print(f"generated {len(manifest['problems'])} problems under {OUT}")


if __name__ == "__main__":
    main()

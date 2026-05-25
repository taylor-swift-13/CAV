#!/usr/bin/env python3
"""Add another batch of easy scalar SESpec/FormalBenchHF tasks."""

from __future__ import annotations

import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DATASETS = ROOT / "datasets"
SOURCE = {
    "name": "FormalBench",
    "slug": "FormalBenchHF/base/programs",
    "url": "https://github.com/thanhlecongg/FormalBench/",
    "license": "local rewrite from SESpec java_flat",
}


def int_param(name: str) -> dict:
    return {"name": name, "type": "int"}


def camel(name: str) -> str:
    return "".join(part.capitalize() for part in name.split("_"))


def cases(fn, names: list[str], values: list[tuple[int, ...]]) -> list[dict]:
    out = []
    for value in values:
        if not isinstance(value, tuple):
            value = (value,)
        out.append({"input": dict(zip(names, value)), "expected": fn(*value)})
    return out


def md(problem: dict, language: str) -> str:
    reqs = "\n".join(f"- {line}" for line in problem["requirements"])
    return (
        f"# {problem['name']}\n\n"
        "## Problem\n\n"
        f"{problem['description']}\n\n"
        "## Requirements\n\n"
        f"{reqs}\n\n"
        "## Source\n\n"
        f"- Source: FormalBenchHF base program `{problem['source_path']}` from SESpec `represent/bench/java_flat`.\n"
        "- URL: https://github.com/thanhlecongg/FormalBench/\n"
        "- License note: this is a local single-function rewrite; do not copy upstream statement text.\n"
        "- Style: HumanEval-like short single-function task; not HumanEval or MBPP.\n\n"
        "## Reference Implementation\n\n"
        f"```{language}\n{problem['code'][language]}\n```\n"
    )


def make_problem(name: str, source_path: str, description: str, requirements: list[str],
                 params: list[dict], tests: list[dict], java_body: str, c_body: str,
                 rust_body: str) -> dict:
    return {
        "name": name,
        "source_path": source_path,
        "description": description,
        "requirements": requirements,
        "params": params,
        "tests": tests,
        "code": {
            "java": f"class {camel(name)} {{\n{java_body}\n}}",
            "c": c_body,
            "rust": rust_body,
        },
    }


def write_problem(problem: dict) -> None:
    for language in ("c", "java", "rust"):
        (DATASETS / language / f"{problem['name']}.md").write_text(md(problem, language), encoding="utf-8")
    spec = {
        "name": problem["name"],
        "return_type": "int",
        "params": problem["params"],
        "tests": [{"kind": "positive", **case} for case in problem["tests"]],
        "source": SOURCE | {"slug": f"FormalBenchHF/base/programs/{problem['source_path']}"},
    }
    (DATASETS / "tests" / f"{problem['name']}.json").write_text(
        json.dumps(spec, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


def update_manifest(problems: list[dict]) -> None:
    manifest_path = DATASETS / "manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    by_name = {p["name"]: p for p in manifest["problems"]}
    for problem in problems:
        by_name[problem["name"]] = {
            "name": problem["name"],
            "return_type": "int",
            "params": problem["params"],
            "source": SOURCE | {"slug": f"FormalBenchHF/base/programs/{problem['source_path']}"},
        }
    manifest["problems"] = [by_name[name] for name in sorted(by_name)]
    manifest_path.write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")

    readme_path = DATASETS / "README.md"
    text = readme_path.read_text(encoding="utf-8")
    text = re.sub(r"- Problems: \d+", f"- Problems: {len(by_name)}", text)
    readme_path.write_text(text, encoding="utf-8")


def octagonal(n): return sum(6 * i + 1 for i in range(n))
def decagonal(n): return sum(8 * i + 1 for i in range(n))
def nonagonal(n): return sum(7 * i + 1 for i in range(n))
def hamming(n1, n2):
    count = 0
    while n1 or n2:
        if (n1 & 1) != (n2 & 1): count += 1
        n1 >>= 1; n2 >>= 1
    return count
def unset_bits_upto(n):
    count = 0
    for i in range(1, n + 1):
        t = i
        while t:
            if (t & 1) == 0: count += 1
            t >>= 1
    return count
def toggle_even_bits(n):
    res = 0; count = 0; temp = n
    while temp > 0:
        if count % 2 == 0: res |= 1 << count
        count += 1; temp >>= 1
    return n ^ res
def set_odd_bits(n):
    res = 0; count = 0; temp = n
    while temp > 0:
        if count % 2 == 1: res |= 1 << count
        count += 1; temp >>= 1
    return n | res
def odd_days(n):
    hund1 = n // 100; hund4 = n // 400; leap = n // 4; ordinary = n - leap
    if hund1: ordinary += hund1; leap -= hund1
    if hund4: ordinary -= hund4; leap += hund4
    return (ordinary + leap * 2) % 7
def proper_divisor_sum(n): return sum(i for i in range(1, n // 2 + 1) if n % i == 0)
def max_mod_value(n, x, y):
    ans = 0
    for i in range(1, n + 1):
        if i % x == y: ans = i
    return ans
def divisor_count(n): return sum(1 for i in range(1, n + 1) if n % i == 0)
def round_down_multiple(n, m):
    for i in range(n, -1, -1):
        if i % m == 0: return i
    return -1
def nth_fraction_digit(p, q, n):
    res = 0
    while n > 0:
        n -= 1; p *= 10; res = p // q; p %= q
    return res
def permutation(n, k):
    res = 1
    for i in range(1, k + 1): res *= n - i + 1
    return res
def next_square(n):
    i = 1; square = 1
    while square <= n:
        square = i * i; i += 1
    return square
def even_power_sum(n): return sum((2 * i) ** 4 for i in range(1, n + 1))
def digit_count(n):
    count = 0
    while n > 0: n //= 10; count += 1
    return count
def centered_hex(n):
    r = 1
    while n > 0:
        n -= 1; r += 6 * n
    return r
def cube_sum(n): return sum(i * i * i for i in range(1, n + 1))
def set_bit_count(n):
    count = 0
    while n > 0:
        if n & 1: count += 1
        n >>= 1
    return count


def simple_unary(name: str, source: str, desc: str, req: list[str], fn, values: list[int],
                 java_loop: str, c_loop: str, rust_loop: str, param: str = "n") -> dict:
    return make_problem(
        name, source, desc, req, [int_param(param)], cases(fn, [param], values),
        f"    public static int {name}(int {param}) {{\n{java_loop}\n    }}",
        f"int {name}(int {param}) {{\n{c_loop}\n}}",
        f"pub fn {name}(mut {param}: i32) -> i32 {{\n{rust_loop}\n}}",
    )


def problems() -> list[dict]:
    return [
        simple_unary("fb_easy_octagonal_number", "IsOctagonal.java", "Return the `n`th value of the FormalBench octagonal-number recurrence.", ["`0 <= n <= 1000`.", "Use `f[0]=0` and `f[i+1]=f[i]+6*i+1`."], octagonal, [0, 1, 2, 3, 10, 100],
                     "        int value = 0;\n        for (int i = 0; i <= n - 1; i++) value += 6 * i + 1;\n        return value;",
                     "    int value = 0;\n    for (int i = 0; i <= n - 1; i++) value += 6 * i + 1;\n    return value;",
                     "    let mut value = 0;\n    for i in 0..n { value += 6 * i + 1; }\n    value"),
        simple_unary("fb_easy_decagonal_number", "IsNumDecagonal.java", "Return the `n`th value of the FormalBench decagonal-number recurrence.", ["`0 <= n <= 1000`.", "Use `f[0]=0` and `f[i+1]=f[i]+8*i+1`."], decagonal, [0, 1, 2, 3, 10, 100],
                     "        int value = 0;\n        for (int i = 0; i <= n - 1; i++) value += 8 * i + 1;\n        return value;",
                     "    int value = 0;\n    for (int i = 0; i <= n - 1; i++) value += 8 * i + 1;\n    return value;",
                     "    let mut value = 0;\n    for i in 0..n { value += 8 * i + 1; }\n    value"),
        simple_unary("fb_easy_nonagonal_number", "IsNonagonal.java", "Return the `n`th value of the FormalBench nonagonal-number recurrence.", ["`0 <= n <= 1000`.", "Use `f[0]=0` and `f[i+1]=f[i]+7*i+1`."], nonagonal, [0, 1, 2, 3, 10, 100],
                     "        int value = 0;\n        for (int i = 0; i <= n - 1; i++) value += 7 * i + 1;\n        return value;",
                     "    int value = 0;\n    for (int i = 0; i <= n - 1; i++) value += 7 * i + 1;\n    return value;",
                     "    let mut value = 0;\n    for i in 0..n { value += 7 * i + 1; }\n    value"),
        make_problem("fb_easy_hamming_distance_bits", "HammingDistance.java", "Return the number of bit positions where nonnegative integers `n1` and `n2` differ.", ["`0 <= n1, n2 <= 1000000`.", "Compare binary representations until both numbers become zero."], [int_param("n1"), int_param("n2")], cases(hamming, ["n1", "n2"], [(0, 0), (1, 0), (1, 4), (7, 3), (255, 0)]),
                     "    public static int fb_easy_hamming_distance_bits(int n1, int n2) {\n        int count = 0;\n        while (n1 != 0 || n2 != 0) { if ((n1 & 1) != (n2 & 1)) count++; n1 >>= 1; n2 >>= 1; }\n        return count;\n    }",
                     "int fb_easy_hamming_distance_bits(int n1, int n2) {\n    int count = 0;\n    while (n1 != 0 || n2 != 0) { if ((n1 & 1) != (n2 & 1)) count++; n1 >>= 1; n2 >>= 1; }\n    return count;\n}",
                     "pub fn fb_easy_hamming_distance_bits(mut n1: i32, mut n2: i32) -> i32 {\n    let mut count = 0;\n    while n1 != 0 || n2 != 0 { if (n1 & 1) != (n2 & 1) { count += 1; } n1 >>= 1; n2 >>= 1; }\n    count\n}"),
        simple_unary("fb_easy_unset_bit_count_upto", "CountUnsetBits.java", "Return the total number of zero bits seen while scanning the binary forms of all integers from `1` through `n`.", ["`1 <= n <= 1000`.", "Ignore leading zeros."], unset_bits_upto, [1, 2, 3, 4, 8, 15],
                     "        int count = 0;\n        for (int i = 1; i <= n; i++) { int temp = i; while (temp != 0) { if ((temp & 1) == 0) count++; temp >>= 1; } }\n        return count;",
                     "    int count = 0;\n    for (int i = 1; i <= n; i++) { int temp = i; while (temp != 0) { if ((temp & 1) == 0) count++; temp >>= 1; } }\n    return count;",
                     "    let mut count = 0;\n    for i in 1..=n { let mut temp = i; while temp != 0 { if (temp & 1) == 0 { count += 1; } temp >>= 1; } }\n    count"),
        simple_unary("fb_easy_toggle_even_bit_positions", "EvenBitToggleNumber.java", "Toggle every even-indexed bit position that exists in the binary representation of `n`, using zero-based bit positions.", ["`1 <= n <= 1000000`.", "Only positions below the highest set bit are considered."], toggle_even_bits, [1, 2, 3, 8, 15, 42],
                     "        int res = 0, count = 0, temp = n;\n        while (temp > 0) { if (count % 2 == 0) res |= (1 << count); count++; temp >>= 1; }\n        return n ^ res;",
                     "    int res = 0, count = 0, temp = n;\n    while (temp > 0) { if (count % 2 == 0) res |= (1 << count); count++; temp >>= 1; }\n    return n ^ res;",
                     "    let (mut res, mut count, mut temp) = (0, 0, n);\n    while temp > 0 { if count % 2 == 0 { res |= 1 << count; } count += 1; temp >>= 1; }\n    n ^ res"),
        simple_unary("fb_easy_set_odd_bit_positions", "EvenBitSetNumber.java", "Set every odd-indexed bit position that exists in the binary representation of `n`, using zero-based bit positions.", ["`1 <= n <= 1000000`.", "Only positions below the highest set bit are considered."], set_odd_bits, [1, 2, 3, 8, 15, 42],
                     "        int res = 0, count = 0, temp = n;\n        while (temp > 0) { if (count % 2 == 1) res |= (1 << count); count++; temp >>= 1; }\n        return n | res;",
                     "    int res = 0, count = 0, temp = n;\n    while (temp > 0) { if (count % 2 == 1) res |= (1 << count); count++; temp >>= 1; }\n    return n | res;",
                     "    let (mut res, mut count, mut temp) = (0, 0, n);\n    while temp > 0 { if count % 2 == 1 { res |= 1 << count; } count += 1; temp >>= 1; }\n    n | res"),
        simple_unary("fb_easy_odd_days_mod_week", "OddDays.java", "Return the FormalBench odd-days value for the first `n` years modulo `7`.", ["`0 <= n <= 10000`.", "Use the leap-year adjustment from the reference recurrence."], odd_days, [0, 1, 4, 100, 400, 2024],
                     "        int hund1 = n / 100, hund4 = n / 400, leap = n / 4, ordinary = n - leap;\n        if (hund1 != 0) { ordinary += hund1; leap -= hund1; }\n        if (hund4 != 0) { ordinary -= hund4; leap += hund4; }\n        return (ordinary + leap * 2) % 7;",
                     "    int hund1 = n / 100, hund4 = n / 400, leap = n / 4, ordinary = n - leap;\n    if (hund1 != 0) { ordinary += hund1; leap -= hund1; }\n    if (hund4 != 0) { ordinary -= hund4; leap += hund4; }\n    return (ordinary + leap * 2) % 7;",
                     "    let hund1 = n / 100; let hund4 = n / 400; let mut leap = n / 4; let mut ordinary = n - leap;\n    if hund1 != 0 { ordinary += hund1; leap -= hund1; }\n    if hund4 != 0 { ordinary -= hund4; leap += hund4; }\n    (ordinary + leap * 2) % 7"),
        simple_unary("fb_easy_proper_divisor_sum", "SumDiv.java", "Return the sum of all proper positive divisors of `number`.", ["`1 <= number <= 10000`.", "Do not include `number` itself."], proper_divisor_sum, [1, 2, 6, 12, 28, 97],
                     "        int sum = 0;\n        for (int i = 1; i <= number / 2; i++) if (number % i == 0) sum += i;\n        return sum;",
                     "    int sum = 0;\n    for (int i = 1; i <= number / 2; i++) if (number % i == 0) sum += i;\n    return sum;",
                     "    let mut sum = 0;\n    for i in 1..=(number / 2) { if number % i == 0 { sum += i; } }\n    sum", "number"),
        make_problem("fb_easy_max_mod_remainder_value", "FindMaxVal.java", "Return the largest integer `i` in `[1, n]` such that `i % x == y`, or `0` if no such value exists.", ["`1 <= n <= 10000`.", "`1 <= x <= 1000`.", "`0 <= y < x`."], [int_param("n"), int_param("x"), int_param("y")], cases(max_mod_value, ["n", "x", "y"], [(10, 3, 1), (10, 3, 2), (5, 7, 6), (100, 10, 0)]),
                     "    public static int fb_easy_max_mod_remainder_value(int n, int x, int y) {\n        int max = 0;\n        for (int i = 1; i <= n; i++) if (i % x == y) max = i;\n        return max;\n    }",
                     "int fb_easy_max_mod_remainder_value(int n, int x, int y) {\n    int max = 0;\n    for (int i = 1; i <= n; i++) if (i % x == y) max = i;\n    return max;\n}",
                     "pub fn fb_easy_max_mod_remainder_value(n: i32, x: i32, y: i32) -> i32 {\n    let mut max = 0;\n    for i in 1..=n { if i % x == y { max = i; } }\n    max\n}"),
        simple_unary("fb_easy_divisor_count", "Divisor.java", "Return the number of positive divisors of `n`.", ["`1 <= n <= 10000`.", "Count both `1` and `n`."], divisor_count, [1, 2, 6, 12, 36, 97],
                     "        int count = 0;\n        for (int i = 1; i <= n; i++) if (n % i == 0) count++;\n        return count;",
                     "    int count = 0;\n    for (int i = 1; i <= n; i++) if (n % i == 0) count++;\n    return count;",
                     "    let mut count = 0;\n    for i in 1..=n { if n % i == 0 { count += 1; } }\n    count"),
        make_problem("fb_easy_round_down_multiple", "RoundNum.java", "Return the largest multiple of `m` that is less than or equal to `n`.", ["`0 <= n <= 10000`.", "`1 <= m <= 1000`."], [int_param("n"), int_param("m")], cases(round_down_multiple, ["n", "m"], [(0, 3), (10, 3), (20, 5), (23, 7)]),
                     "    public static int fb_easy_round_down_multiple(int n, int m) {\n        for (int i = n; i >= 0; i--) if (i % m == 0) return i;\n        return -1;\n    }",
                     "int fb_easy_round_down_multiple(int n, int m) {\n    for (int i = n; i >= 0; i--) if (i % m == 0) return i;\n    return -1;\n}",
                     "pub fn fb_easy_round_down_multiple(n: i32, m: i32) -> i32 {\n    let mut i = n;\n    while i >= 0 { if i % m == 0 { return i; } i -= 1; }\n    -1\n}"),
        make_problem("fb_easy_nth_fraction_digit", "FindNthDigit.java", "Return the `n`th decimal digit after the decimal point in the fraction `p / q`.", ["`0 <= p < q <= 1000`.", "`1 <= n <= 20`."], [int_param("p"), int_param("q"), int_param("n")], cases(nth_fraction_digit, ["p", "q", "n"], [(1, 2, 1), (1, 3, 3), (22, 7, 5), (5, 8, 3)]),
                     "    public static int fb_easy_nth_fraction_digit(int p, int q, int n) {\n        int res = 0;\n        while (n > 0) { n--; p *= 10; res = p / q; p %= q; }\n        return res;\n    }",
                     "int fb_easy_nth_fraction_digit(int p, int q, int n) {\n    int res = 0;\n    while (n > 0) { n--; p *= 10; res = p / q; p %= q; }\n    return res;\n}",
                     "pub fn fb_easy_nth_fraction_digit(mut p: i32, q: i32, mut n: i32) -> i32 {\n    let mut res = 0;\n    while n > 0 { n -= 1; p *= 10; res = p / q; p %= q; }\n    res\n}"),
        make_problem("fb_easy_permutation_coefficient", "PermutationCoefficient.java", "Return `nPk`, the number of ordered selections of `k` items from `n` items.", ["`0 <= k <= n <= 12`.", "Use integer arithmetic."], [int_param("n"), int_param("k")], cases(permutation, ["n", "k"], [(5, 0), (5, 1), (5, 2), (10, 3), (12, 4)]),
                     "    public static int fb_easy_permutation_coefficient(int n, int k) {\n        int res = 1;\n        for (int i = 1; i <= k; i++) res *= (n - i + 1);\n        return res;\n    }",
                     "int fb_easy_permutation_coefficient(int n, int k) {\n    int res = 1;\n    for (int i = 1; i <= k; i++) res *= (n - i + 1);\n    return res;\n}",
                     "pub fn fb_easy_permutation_coefficient(n: i32, k: i32) -> i32 {\n    let mut res = 1;\n    for i in 1..=k { res *= n - i + 1; }\n    res\n}"),
        simple_unary("fb_easy_next_perfect_square", "NextPerfectSquare.java", "Return the smallest perfect square that is strictly greater than `n`.", ["`0 <= n <= 1000000`.", "Return `1` when `n` is `0`."], next_square, [0, 1, 2, 15, 16, 99],
                     "        int i = 1, square = 1;\n        while (square <= n) { square = i * i; i++; }\n        return square;",
                     "    int i = 1, square = 1;\n    while (square <= n) { square = i * i; i++; }\n    return square;",
                     "    let (mut i, mut square) = (1, 1);\n    while square <= n { square = i * i; i += 1; }\n    square"),
        simple_unary("fb_easy_even_fourth_power_sum", "EvenPowerSum.java", "Return the sum of the fourth powers of the first `n` positive even numbers.", ["`0 <= n <= 50`.", "The `i`th term is `(2*i)^4`."], even_power_sum, [0, 1, 2, 3, 10, 20],
                     "        int sum = 0;\n        for (int i = 1; i <= n; i++) { int j = 2 * i; sum += j * j * j * j; }\n        return sum;",
                     "    int sum = 0;\n    for (int i = 1; i <= n; i++) { int j = 2 * i; sum += j * j * j * j; }\n    return sum;",
                     "    let mut sum = 0;\n    for i in 1..=n { let j = 2 * i; sum += j * j * j * j; }\n    sum"),
        simple_unary("fb_easy_digit_count", "CountDigit.java", "Return the number of decimal digits in positive integer `n`.", ["`1 <= n <= 1000000000`.", "Use repeated division by `10`."], digit_count, [1, 9, 10, 123, 1000000000],
                     "        int count = 0;\n        while (n > 0) { n /= 10; count++; }\n        return count;",
                     "    int count = 0;\n    while (n > 0) { n /= 10; count++; }\n    return count;",
                     "    let mut count = 0;\n    while n > 0 { n /= 10; count += 1; }\n    count"),
        simple_unary("fb_easy_centered_hexagonal_number", "CenteredHexagonalNumber.java", "Return the FormalBench centered hexagonal number value for `n`.", ["`0 <= n <= 10000`.", "Use the reference loop `r=1; while n>0 { n--; r += 6*n; }`."], centered_hex, [0, 1, 2, 3, 10, 100],
                     "        int r = 1;\n        while (n > 0) { n--; r += 6 * n; }\n        return r;",
                     "    int r = 1;\n    while (n > 0) { n--; r += 6 * n; }\n    return r;",
                     "    let mut r = 1;\n    while n > 0 { n -= 1; r += 6 * n; }\n    r"),
        simple_unary("fb_easy_cube_sum_series", "SumSeries.java", "Return `1^3 + 2^3 + ... + number^3`.", ["`0 <= number <= 1000`.", "Return `0` when `number` is `0`."], cube_sum, [0, 1, 2, 3, 10, 100],
                     "        int sum = 0;\n        for (int i = 1; i <= number; i++) sum += i * i * i;\n        return sum;",
                     "    int sum = 0;\n    for (int i = 1; i <= number; i++) sum += i * i * i;\n    return sum;",
                     "    let mut sum = 0;\n    for i in 1..=number { sum += i * i * i; }\n    sum", "number"),
        simple_unary("fb_easy_set_bit_count", "CountNum.java", "Return the number of set bits in the binary representation of `n`.", ["`0 <= n <= 1000000`.", "Ignore leading zeros."], set_bit_count, [0, 1, 2, 3, 7, 255, 1024],
                     "        int count = 0;\n        while (n > 0) { if ((n & 1) == 1) count++; n >>= 1; }\n        return count;",
                     "    int count = 0;\n    while (n > 0) { if ((n & 1) == 1) count++; n >>= 1; }\n    return count;",
                     "    let mut count = 0;\n    while n > 0 { if (n & 1) == 1 { count += 1; } n >>= 1; }\n    count"),
    ]


def main() -> None:
    selected = problems()
    for problem in selected:
        write_problem(problem)
    update_manifest(selected)
    print(f"added {len(selected)} easy SESpec/FormalBench problems")


if __name__ == "__main__":
    main()

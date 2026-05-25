#!/usr/bin/env python3
"""Add selected SESpec/FormalBenchHF base programs to the combined dataset."""

from __future__ import annotations

import json
import re
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
DATASETS = REPO_ROOT / "datasets"

SOURCE = {
    "name": "FormalBench",
    "slug": "FormalBenchHF/base/programs",
    "url": "https://github.com/thanhlecongg/FormalBench/",
    "license": "local rewrite from SESpec java_flat",
}


def camel(name: str) -> str:
    return "".join(part.capitalize() for part in name.split("_"))


def md(problem: dict, language: str) -> str:
    reqs = "\n".join(f"- {line}" for line in problem["requirements"])
    source_path = problem["source_path"]
    return (
        f"# {problem['name']}\n\n"
        "## Problem\n\n"
        f"{problem['description']}\n\n"
        "## Requirements\n\n"
        f"{reqs}\n\n"
        "## Source\n\n"
        f"- Source: FormalBenchHF base program `{source_path}` from SESpec `represent/bench/java_flat`.\n"
        "- URL: https://github.com/thanhlecongg/FormalBench/\n"
        "- License note: this is a local single-function rewrite; do not copy upstream statement text.\n"
        "- Style: HumanEval-like short single-function task; not HumanEval or MBPP.\n\n"
        "## Reference Implementation\n\n"
        f"```{language}\n{problem['code'][language]}\n```\n"
    )


def write_problem(problem: dict) -> None:
    name = problem["name"]
    for language in ("c", "java", "rust"):
        path = DATASETS / language / f"{name}.md"
        path.write_text(md(problem, language), encoding="utf-8")

    test_spec = {
        "name": name,
        "return_type": problem["return_type"],
        "params": problem["params"],
        "tests": [
            {"kind": case.get("kind", "positive"), "input": case["input"], "expected": case["expected"]}
            for case in problem["tests"]
        ],
        "source": SOURCE | {"slug": f"FormalBenchHF/base/programs/{problem['source_path']}"},
    }
    (DATASETS / "tests" / f"{name}.json").write_text(
        json.dumps(test_spec, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


def update_manifest(problems: list[dict]) -> None:
    path = DATASETS / "manifest.json"
    manifest = json.loads(path.read_text(encoding="utf-8"))
    by_name = {entry["name"]: entry for entry in manifest["problems"]}
    for problem in problems:
        by_name[problem["name"]] = {
            "name": problem["name"],
            "return_type": problem["return_type"],
            "params": problem["params"],
            "source": SOURCE | {"slug": f"FormalBenchHF/base/programs/{problem['source_path']}"},
        }
    manifest["problems"] = [by_name[name] for name in sorted(by_name)]
    path.write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def update_readme() -> None:
    path = DATASETS / "README.md"
    text = path.read_text(encoding="utf-8")
    count = len(list((DATASETS / "tests").glob("*.json")))
    text = re.sub(r"- Problems: \d+", f"- Problems: {count}", text)
    path.write_text(text, encoding="utf-8")


def int_param(name: str) -> dict:
    return {"name": name, "type": "int"}


def gcd(a: int, b: int) -> int:
    while b:
        a, b = b, a % b
    return abs(a)


def smallest_multiple(n: int) -> int:
    if n <= 2:
        return n
    answer = n * 2
    while True:
        for factor in range(1, n + 1):
            if answer % factor != 0:
                answer += n
                break
        else:
            return answer


def cal_sum(n: int) -> int:
    if n in (0, 1):
        return 3
    if n == 2:
        return 5
    total, a, b, c = 5, 3, 0, 2
    while n > 2:
        d = a + b
        total += d
        a, b, c = b, c, d
        n -= 1
    return total


def prime_divisor_sum(n: int) -> int:
    total = 0
    for i in range(2, n + 1):
        if n % i == 0:
            is_prime = all(i % d for d in range(2, int(i ** 0.5) + 1))
            if is_prime:
                total += i
    return total


def tiling_count(n: int) -> int:
    a = [0] * (n + 1)
    b = [0] * (n + 1)
    a[0], a[1], b[0], b[1] = 1, 0, 0, 1
    for i in range(2, n + 1):
        a[i] = a[i - 2] + 2 * b[i - 1]
        b[i] = a[i - 1] + b[i - 2]
    return a[n]


def sqrt_root(num: int) -> int:
    if num < 0:
        return -1
    left, right = 0, num
    while left <= right:
        mid = left + (right - left) // 2
        square = mid * mid
        if square == num:
            return mid
        if square < num:
            left = mid + 1
        else:
            right = mid - 1
    return right


def catalan(num: int) -> int:
    values = [0] * (num + 1)
    values[0] = 1
    for i in range(1, num + 1):
        for j in range(i):
            values[i] += values[j] * values[i - j - 1]
    return values[num]


def even_binomial_sum(n: int) -> int:
    dp = [0] * (n + 1)
    dp[0] = 1
    for i in range(1, n + 1):
        for j in range(i):
            dp[i] += dp[j]
    return dp[n]


def first_digit_factorial(n: int) -> int:
    fact = 1
    for i in range(2, n + 1):
        fact *= i
    first = 0
    while fact > 0:
        first = fact % 10
        fact //= 10
    return first


def last_digit_product_range(a: int, b: int) -> int:
    if a == b:
        return 1
    if b - a >= 5:
        return 0
    value = 1
    for i in range(a + 1, b + 1):
        value = (value * (i % 10)) % 10
    return value % 10


def largest_prime_factor(n: int) -> int:
    max_factor = 0
    i = 2
    while i <= n:
        while n % i == 0:
            max_factor = i
            n //= i
        i += 1
    return max_factor


def jacobsthal(n: int) -> int:
    values = [0] * (n + 1)
    values[0] = 0
    values[1] = 1
    for i in range(2, n + 1):
        values[i] = values[i - 1] + 2 * values[i - 2]
    return values[n]


def pell(n: int) -> int:
    values = [0] * (n + 1)
    values[0] = 0
    values[1] = 1
    for i in range(2, n + 1):
        values[i] = (2 * values[i - 1] + values[i - 2]) % 1000000000
    return values[n]


def lucas(n: int) -> int:
    values = [0] * (n + 1)
    values[0] = 2
    values[1] = 1
    for i in range(2, n + 1):
        values[i] = values[i - 1] + values[i - 2]
    return values[n]


def first_set_bit_pos(n: int) -> int:
    pos = 1
    while n & 1 == 0:
        n >>= 1
        pos += 1
    return pos


def simple_cases(fn, arg_name: str, values: list[int]) -> list[dict]:
    return [{"input": {arg_name: value}, "expected": fn(value)} for value in values]


def binary_cases(fn, a: str, b: str, values: list[tuple[int, int]]) -> list[dict]:
    return [{"input": {a: x, b: y}, "expected": fn(x, y)} for x, y in values]


def build_problem(name: str, source_path: str, description: str, requirements: list[str], params: list[dict],
                  tests: list[dict], java_body: str, c_body: str, rust_body: str) -> dict:
    class_name = camel(name)
    return {
        "name": name,
        "source_path": source_path,
        "description": description,
        "requirements": requirements,
        "return_type": "int",
        "params": params,
        "tests": tests,
        "code": {
            "java": f"class {class_name} {{\n{java_body}\n}}",
            "c": c_body,
            "rust": rust_body,
        },
    }


def problems() -> list[dict]:
    return [
        build_problem(
            "fb_smallest_multiple",
            "SmallestMultiple.java",
            "Return the smallest positive integer that is divisible by every integer from `1` through `n`.",
            ["`1 <= n <= 10`.", "Return the answer as a signed 32-bit integer."],
            [int_param("n")],
            simple_cases(smallest_multiple, "n", [1, 2, 3, 4, 5, 6, 7, 8, 10]),
            """    public static int fb_smallest_multiple(int n) {\n        if (n <= 2) return n;\n        int i = n * 2;\n        while (true) {\n            for (int factor = 1; factor <= n; factor++) {\n                if (i % factor != 0) { i += n; break; }\n                if (factor == n) return i;\n            }\n        }\n    }""",
            """int fb_smallest_multiple(int n) {\n    if (n <= 2) return n;\n    int i = n * 2;\n    while (1) {\n        for (int factor = 1; factor <= n; factor++) {\n            if (i % factor != 0) { i += n; break; }\n            if (factor == n) return i;\n        }\n    }\n}""",
            """pub fn fb_smallest_multiple(n: i32) -> i32 {\n    if n <= 2 { return n; }\n    let mut i = n * 2;\n    loop {\n        for factor in 1..=n {\n            if i % factor != 0 { i += n; break; }\n            if factor == n { return i; }\n        }\n    }\n}""",
        ),
        build_problem(
            "fb_cal_sum",
            "CalSum.java",
            "Compute the FormalBench recurrence sum with base results `3, 3, 5` and transition `d = a + b` while rotating `(a, b, c)` to `(b, c, d)`.",
            ["`0 <= n <= 20`.", "Follow the recurrence exactly as stated."],
            [int_param("n")],
            simple_cases(cal_sum, "n", [0, 1, 2, 3, 4, 5, 8, 12, 20]),
            """    public static int fb_cal_sum(int n) {\n        if (n == 0 || n == 1) return 3;\n        if (n == 2) return 5;\n        int sum = 5, a = 3, b = 0, c = 2;\n        while (n > 2) {\n            int d = a + b;\n            sum += d;\n            a = b; b = c; c = d;\n            n--;\n        }\n        return sum;\n    }""",
            """int fb_cal_sum(int n) {\n    if (n == 0 || n == 1) return 3;\n    if (n == 2) return 5;\n    int sum = 5, a = 3, b = 0, c = 2;\n    while (n > 2) {\n        int d = a + b;\n        sum += d;\n        a = b; b = c; c = d;\n        n--;\n    }\n    return sum;\n}""",
            """pub fn fb_cal_sum(mut n: i32) -> i32 {\n    if n == 0 || n == 1 { return 3; }\n    if n == 2 { return 5; }\n    let (mut sum, mut a, mut b, mut c) = (5, 3, 0, 2);\n    while n > 2 {\n        let d = a + b;\n        sum += d;\n        a = b; b = c; c = d;\n        n -= 1;\n    }\n    sum\n}""",
        ),
        build_problem(
            "fb_prime_divisor_sum",
            "Sum.java",
            "Return the sum of the distinct prime divisors of `n`.",
            ["`2 <= n <= 10000`.", "Each prime divisor is counted once."],
            [int_param("n")],
            simple_cases(prime_divisor_sum, "n", [2, 6, 12, 18, 49, 60, 97, 210]),
            """    public static int fb_prime_divisor_sum(int n) {\n        int[] sums = new int[n + 1];\n        for (int i = 2; i <= n; i++) {\n            if (sums[i] == 0) {\n                for (int j = i; j <= n; j += i) sums[j] += i;\n            }\n        }\n        return sums[n];\n    }""",
            """int fb_prime_divisor_sum(int n) {\n    int sums[10001] = {0};\n    for (int i = 2; i <= n; i++) {\n        if (sums[i] == 0) {\n            for (int j = i; j <= n; j += i) sums[j] += i;\n        }\n    }\n    return sums[n];\n}""",
            """pub fn fb_prime_divisor_sum(n: i32) -> i32 {\n    let n = n as usize;\n    let mut sums = vec![0; n + 1];\n    for i in 2..=n {\n        if sums[i] == 0 {\n            let mut j = i;\n            while j <= n { sums[j] += i as i32; j += i; }\n        }\n    }\n    sums[n]\n}""",
        ),
        build_problem(
            "fb_tiling_count_ways",
            "CountWays.java",
            "Return the FormalBench two-state tiling recurrence value `A[n]`, where `A[0]=1`, `A[1]=0`, `B[0]=0`, `B[1]=1`, `A[i]=A[i-2]+2*B[i-1]`, and `B[i]=A[i-1]+B[i-2]`.",
            ["`1 <= n <= 20`.", "Return `A[n]`."],
            [int_param("n")],
            simple_cases(tiling_count, "n", [1, 2, 3, 4, 5, 6, 10, 15]),
            """    public static int fb_tiling_count_ways(int n) {\n        int[] A = new int[n + 1];\n        int[] B = new int[n + 1];\n        A[0] = 1; A[1] = 0; B[0] = 0; B[1] = 1;\n        for (int i = 2; i <= n; i++) {\n            A[i] = A[i - 2] + 2 * B[i - 1];\n            B[i] = A[i - 1] + B[i - 2];\n        }\n        return A[n];\n    }""",
            """int fb_tiling_count_ways(int n) {\n    int A[21] = {0};\n    int B[21] = {0};\n    A[0] = 1; A[1] = 0; B[0] = 0; B[1] = 1;\n    for (int i = 2; i <= n; i++) {\n        A[i] = A[i - 2] + 2 * B[i - 1];\n        B[i] = A[i - 1] + B[i - 2];\n    }\n    return A[n];\n}""",
            """pub fn fb_tiling_count_ways(n: i32) -> i32 {\n    let n = n as usize;\n    let mut a = vec![0; n + 1];\n    let mut b = vec![0; n + 1];\n    a[0] = 1; b[1] = 1;\n    for i in 2..=n {\n        a[i] = a[i - 2] + 2 * b[i - 1];\n        b[i] = a[i - 1] + b[i - 2];\n    }\n    a[n]\n}""",
        ),
        build_problem(
            "fb_sqrt_root",
            "SqrtRoot.java",
            "Return the floor of the square root of `num`; return `-1` when `num` is negative.",
            ["`-10000 <= num <= 10000`.", "Use integer arithmetic and return the floor for non-perfect squares."],
            [int_param("num")],
            simple_cases(sqrt_root, "num", [-1, 0, 1, 2, 4, 15, 16, 99, 10000]),
            """    public static int fb_sqrt_root(int num) {\n        if (num < 0) return -1;\n        int left = 0, right = num;\n        while (left <= right) {\n            int mid = left + (right - left) / 2;\n            if (mid * mid == num) return mid;\n            if (mid * mid < num) left = mid + 1;\n            else right = mid - 1;\n        }\n        return right;\n    }""",
            """int fb_sqrt_root(int num) {\n    if (num < 0) return -1;\n    int left = 0, right = num;\n    while (left <= right) {\n        int mid = left + (right - left) / 2;\n        if (mid * mid == num) return mid;\n        if (mid * mid < num) left = mid + 1;\n        else right = mid - 1;\n    }\n    return right;\n}""",
            """pub fn fb_sqrt_root(num: i32) -> i32 {\n    if num < 0 { return -1; }\n    let (mut left, mut right) = (0, num);\n    while left <= right {\n        let mid = left + (right - left) / 2;\n        if mid * mid == num { return mid; }\n        if mid * mid < num { left = mid + 1; } else { right = mid - 1; }\n    }\n    right\n}""",
        ),
        build_problem(
            "fb_catalan_number",
            "CatalanNumber.java",
            "Return the `num`th Catalan number using the standard dynamic programming recurrence.",
            ["`0 <= num <= 12`.", "Use `C[0]=1` and `C[i]=sum(C[j]*C[i-j-1])` for `0 <= j < i`."],
            [int_param("num")],
            simple_cases(catalan, "num", [0, 1, 2, 3, 4, 5, 8, 12]),
            """    public static int fb_catalan_number(int num) {\n        int[] catalan = new int[num + 1];\n        catalan[0] = 1;\n        for (int i = 1; i <= num; i++) {\n            for (int j = 0; j < i; j++) catalan[i] += catalan[j] * catalan[i - j - 1];\n        }\n        return catalan[num];\n    }""",
            """int fb_catalan_number(int num) {\n    int catalan[13] = {0};\n    catalan[0] = 1;\n    for (int i = 1; i <= num; i++) {\n        for (int j = 0; j < i; j++) catalan[i] += catalan[j] * catalan[i - j - 1];\n    }\n    return catalan[num];\n}""",
            """pub fn fb_catalan_number(num: i32) -> i32 {\n    let num = num as usize;\n    let mut catalan = vec![0; num + 1];\n    catalan[0] = 1;\n    for i in 1..=num {\n        for j in 0..i { catalan[i] += catalan[j] * catalan[i - j - 1]; }\n    }\n    catalan[num]\n}""",
        ),
        build_problem(
            "fb_even_binomial_coeff_sum",
            "EvenBinomialCoeffSum.java",
            "Return the FormalBench DP value defined by `dp[0]=1` and `dp[i]=dp[0]+...+dp[i-1]`.",
            ["`0 <= n <= 30`.", "Follow the stated recurrence directly."],
            [int_param("n")],
            simple_cases(even_binomial_sum, "n", [0, 1, 2, 3, 4, 8, 16, 30]),
            """    public static int fb_even_binomial_coeff_sum(int n) {\n        int[] dp = new int[n + 1];\n        dp[0] = 1;\n        for (int i = 1; i <= n; i++) {\n            for (int j = 0; j < i; j++) dp[i] += dp[j];\n        }\n        return dp[n];\n    }""",
            """int fb_even_binomial_coeff_sum(int n) {\n    int dp[31] = {0};\n    dp[0] = 1;\n    for (int i = 1; i <= n; i++) {\n        for (int j = 0; j < i; j++) dp[i] += dp[j];\n    }\n    return dp[n];\n}""",
            """pub fn fb_even_binomial_coeff_sum(n: i32) -> i32 {\n    let n = n as usize;\n    let mut dp = vec![0; n + 1];\n    dp[0] = 1;\n    for i in 1..=n { for j in 0..i { dp[i] += dp[j]; } }\n    dp[n]\n}""",
        ),
        build_problem(
            "fb_lcm",
            "Lcm.java",
            "Return the least common multiple of positive integers `x` and `y`.",
            ["`1 <= x, y <= 10000`.", "Return the answer as a signed 32-bit integer."],
            [int_param("x"), int_param("y")],
            binary_cases(lambda x, y: x * y // gcd(x, y), "x", "y", [(1, 1), (3, 5), (4, 6), (12, 18), (21, 6), (25, 10), (97, 89)]),
            """    public static int fb_lcm(int x, int y) {\n        int a = x, b = y;\n        if (a > b) { int t = a; a = b; b = t; }\n        int gcd = 1;\n        for (int i = 1; i <= a; i++) if (a % i == 0 && b % i == 0) gcd = i;\n        return (x * y) / gcd;\n    }""",
            """int fb_lcm(int x, int y) {\n    int a = x, b = y;\n    if (a > b) { int t = a; a = b; b = t; }\n    int gcd = 1;\n    for (int i = 1; i <= a; i++) if (a % i == 0 && b % i == 0) gcd = i;\n    return (x * y) / gcd;\n}""",
            """pub fn fb_lcm(x: i32, y: i32) -> i32 {\n    let (mut a, mut b) = (x, y);\n    if a > b { let t = a; a = b; b = t; }\n    let mut gcd = 1;\n    for i in 1..=a { if a % i == 0 && b % i == 0 { gcd = i; } }\n    (x * y) / gcd\n}""",
        ),
    ] + generated_simple_problems()


def generated_simple_problems() -> list[dict]:
    specs = [
        ("fb_first_digit_factorial", "FirstDigit.java", "Return the first decimal digit of `n!`.", ["`1 <= n <= 10`.", "Compute the factorial using integer arithmetic."], [int_param("n")], simple_cases(first_digit_factorial, "n", [1, 2, 3, 4, 5, 6, 7, 8, 10])),
        ("fb_cube_sum_difference", "Difference.java", "Return `(1^3 + 2^3 + ... + n^3) - (1 + 2 + ... + n)`.", ["`1 <= n <= 200`.", "Return the signed 32-bit integer result."], [int_param("n")], simple_cases(lambda n: sum(i ** 3 for i in range(1, n + 1)) - sum(range(1, n + 1)), "n", [1, 2, 3, 5, 10, 20, 50])),
        ("fb_last_digit_product_range", "ComputeLastDigit.java", "Return the last decimal digit of the product `(a+1) * (a+2) * ... * b`, with the special case `a == b` returning `1`.", ["`0 <= a <= b <= 1000`.", "If `b - a >= 5`, return `0`."], [int_param("a"), int_param("b")], binary_cases(last_digit_product_range, "a", "b", [(0, 0), (0, 1), (1, 3), (2, 4), (7, 9), (10, 15), (25, 29)])),
        ("fb_sum_even_factors", "Sumoffactors.java", "Return the sum of all positive even divisors of `n`, excluding `1`.", ["`1 <= n <= 10000`.", "Count each divisor once."], [int_param("n")], simple_cases(lambda n: sum(i for i in range(2, n + 1) if n % i == 0 and i % 2 == 0), "n", [1, 2, 6, 12, 18, 45, 64, 100])),
        ("fb_largest_prime_factor", "MaxPrimeFactors.java", "Return the largest prime factor of `n`.", ["`2 <= n <= 100000`.", "Return `n` itself when `n` is prime."], [int_param("n")], simple_cases(largest_prime_factor, "n", [2, 3, 12, 49, 97, 13195, 99991])),
        ("fb_sum_odd_factors", "SumOfOddFactors.java", "Return the sum of all positive odd divisors of `n`.", ["`1 <= n <= 10000`.", "Count each divisor once."], [int_param("n")], simple_cases(lambda n: sum(i for i in range(1, n + 1) if n % i == 0 and i % 2 != 0), "n", [1, 2, 9, 12, 18, 45, 64, 100])),
        ("fb_jacobsthal_number", "JacobsthalNum.java", "Return the `n`th Jacobsthal number with `J(0)=0`, `J(1)=1`, and `J(n)=J(n-1)+2*J(n-2)`.", ["`1 <= n <= 30`.", "Return the signed 32-bit integer result."], [int_param("n")], simple_cases(jacobsthal, "n", [1, 2, 3, 4, 5, 10, 20, 30])),
        ("fb_pell_number", "GetPell.java", "Return the `n`th Pell number modulo `1000000000`, with `P(0)=0`, `P(1)=1`, and `P(n)=2*P(n-1)+P(n-2)`.", ["`1 <= n <= 30`.", "Apply the modulo at each recurrence step."], [int_param("n")], simple_cases(pell, "n", [1, 2, 3, 4, 5, 10, 20, 30])),
        ("fb_lucas_number", "FindLucas.java", "Return the `n`th Lucas number with `L(0)=2`, `L(1)=1`, and `L(n)=L(n-1)+L(n-2)`.", ["`1 <= n <= 30`.", "Return the signed 32-bit integer result."], [int_param("n")], simple_cases(lucas, "n", [1, 2, 3, 4, 5, 10, 20, 30])),
        ("fb_average_odd_upto", "AverageOdd.java", "Return the integer average of all positive odd integers from `1` through `n`.", ["`1 <= n <= 10000`.", "Use truncating integer division."], [int_param("n")], simple_cases(lambda n: sum(i for i in range(1, n + 1) if i % 2) // len([i for i in range(1, n + 1) if i % 2]), "n", [1, 2, 3, 5, 10, 99, 100])),
        ("fb_average_even_upto", "AverageEven.java", "Return the integer average of all positive even integers from `1` through `n`.", ["`2 <= n <= 10000`.", "Use truncating integer division."], [int_param("n")], simple_cases(lambda n: sum(i for i in range(1, n + 1) if i % 2 == 0) // len([i for i in range(1, n + 1) if i % 2 == 0]), "n", [2, 3, 4, 6, 10, 99, 100])),
        ("fb_smallest_divisor", "SmallestDivisor.java", "Return the smallest divisor of `n` that is greater than `1`.", ["`2 <= n <= 100000`.", "Return `n` itself when `n` is prime."], [int_param("n")], simple_cases(lambda n: next((i for i in range(2, n + 1) if n % i == 0), n), "n", [2, 3, 4, 9, 49, 97, 100])),
        ("fb_next_power_of_two", "NextPowerOf2.java", "Return the smallest power of two that is greater than or equal to `n`.", ["`0 <= n <= 1000000`.", "Return `1` when `n` is `0`."], [int_param("n")], simple_cases(lambda n: 1 if n == 0 else 1 << (n - 1).bit_length(), "n", [0, 1, 2, 3, 5, 16, 17, 1000])),
        ("fb_sum_odd_range", "SumInRange.java", "Return the sum of all odd integers in the inclusive range `[l, r]`.", ["`0 <= l <= r <= 10000`.", "Return `0` if the range contains no odd values."], [int_param("l"), int_param("r")], binary_cases(lambda l, r: sum(i for i in range(l, r + 1) if i % 2 != 0), "l", "r", [(0, 0), (0, 1), (2, 4), (3, 9), (10, 20), (99, 101)])),
        ("fb_sum_even_range", "SumEven.java", "Return the sum of all even integers in the inclusive range `[l, r]`.", ["`0 <= l <= r <= 10000`.", "Return `0` if the range contains no even values."], [int_param("l"), int_param("r")], binary_cases(lambda l, r: sum(i for i in range(l, r + 1) if i % 2 == 0), "l", "r", [(0, 0), (0, 1), (1, 3), (3, 9), (10, 20), (99, 101)])),
        ("fb_common_divisor_count", "NumCommDiv.java", "Return the number of positive common divisors of `x` and `y`.", ["`1 <= x, y <= 10000`.", "Count each common divisor once."], [int_param("x"), int_param("y")], binary_cases(lambda x, y: sum(1 for i in range(1, min(x, y) + 1) if x % i == 0 and y % i == 0), "x", "y", [(1, 1), (2, 4), (12, 18), (36, 60), (97, 89), (100, 10)])),
        ("fb_binomial_coefficient", "BinomialCoeff.java", "Return the binomial coefficient `C(n, k)`.", ["`0 <= k <= n <= 20`.", "Use integer arithmetic."], [int_param("n"), int_param("k")], binary_cases(lambda n, k: __import__("math").comb(n, k), "n", "k", [(0, 0), (5, 0), (5, 2), (10, 5), (20, 3), (20, 10)])),
        ("fb_digit_sum_simple", "SumDigits.java", "Return the sum of the decimal digits of `n`.", ["`0 <= n <= 1000000000`.", "Return `0` when `n` is `0`."], [int_param("n")], simple_cases(lambda n: sum(map(int, str(n))), "n", [0, 1, 10, 123, 9999, 1000000000])),
        ("fb_factorial_last_two_digits", "LastTwoDigits.java", "Return the last two decimal digits of `n!`.", ["`1 <= n <= 12`.", "Compute the factorial using signed 32-bit integer arithmetic."], [int_param("n")], simple_cases(lambda n: (__import__("math").factorial(n) % 100), "n", [1, 2, 3, 4, 5, 6, 10, 12])),
        ("fb_first_set_bit_position", "GetFirstSetBitPos.java", "Return the one-based position of the least significant set bit in `n`.", ["`1 <= n <= 1000000`.", "The least significant bit has position `1`."], [int_param("n")], simple_cases(first_set_bit_pos, "n", [1, 2, 3, 4, 8, 12, 40, 1024])),
    ]
    built = []
    for name, source_path, description, requirements, params, tests in specs:
        built.append(build_loop_problem(name, source_path, description, requirements, params, tests))
    return built


def build_loop_problem(name: str, source_path: str, description: str, requirements: list[str],
                       params: list[dict], tests: list[dict]) -> dict:
    fn = name
    if name == "fb_first_digit_factorial":
        java = f"""    public static int {fn}(int n) {{\n        int fact = 1;\n        for (int i = 2; i <= n; i++) fact *= i;\n        int first = 0;\n        while (fact > 0) {{ first = fact % 10; fact /= 10; }}\n        return first;\n    }}"""
        c = f"""int {fn}(int n) {{\n    int fact = 1;\n    for (int i = 2; i <= n; i++) fact *= i;\n    int first = 0;\n    while (fact > 0) {{ first = fact % 10; fact /= 10; }}\n    return first;\n}}"""
        rust = f"""pub fn {fn}(n: i32) -> i32 {{\n    let mut fact = 1;\n    for i in 2..=n {{ fact *= i; }}\n    let mut first = 0;\n    while fact > 0 {{ first = fact % 10; fact /= 10; }}\n    first\n}}"""
    elif name == "fb_cube_sum_difference":
        java = f"""    public static int {fn}(int n) {{\n        int cubes = 0, linear = 0;\n        for (int i = 1; i <= n; i++) {{ cubes += i * i * i; linear += i; }}\n        return cubes - linear;\n    }}"""
        c = f"""int {fn}(int n) {{\n    int cubes = 0, linear = 0;\n    for (int i = 1; i <= n; i++) {{ cubes += i * i * i; linear += i; }}\n    return cubes - linear;\n}}"""
        rust = f"""pub fn {fn}(n: i32) -> i32 {{\n    let (mut cubes, mut linear) = (0, 0);\n    for i in 1..=n {{ cubes += i * i * i; linear += i; }}\n    cubes - linear\n}}"""
    elif name == "fb_last_digit_product_range":
        java = f"""    public static int {fn}(int a, int b) {{\n        if (a == b) return 1;\n        if (b - a >= 5) return 0;\n        int value = 1;\n        for (int i = a + 1; i <= b; i++) value = (value * (i % 10)) % 10;\n        return value % 10;\n    }}"""
        c = f"""int {fn}(int a, int b) {{\n    if (a == b) return 1;\n    if (b - a >= 5) return 0;\n    int value = 1;\n    for (int i = a + 1; i <= b; i++) value = (value * (i % 10)) % 10;\n    return value % 10;\n}}"""
        rust = f"""pub fn {fn}(a: i32, b: i32) -> i32 {{\n    if a == b {{ return 1; }}\n    if b - a >= 5 {{ return 0; }}\n    let mut value = 1;\n    for i in (a + 1)..=b {{ value = (value * (i % 10)) % 10; }}\n    value % 10\n}}"""
    elif name in {"fb_sum_even_factors", "fb_sum_odd_factors"}:
        parity = "0" if name == "fb_sum_even_factors" else "1"
        start = "2" if name == "fb_sum_even_factors" else "1"
        java = f"""    public static int {fn}(int n) {{\n        int sum = 0;\n        for (int i = {start}; i <= n; i++) if (n % i == 0 && i % 2 == {parity}) sum += i;\n        return sum;\n    }}"""
        c = f"""int {fn}(int n) {{\n    int sum = 0;\n    for (int i = {start}; i <= n; i++) if (n % i == 0 && i % 2 == {parity}) sum += i;\n    return sum;\n}}"""
        rust = f"""pub fn {fn}(n: i32) -> i32 {{\n    let mut sum = 0;\n    for i in {start}..=n {{ if n % i == 0 && i % 2 == {parity} {{ sum += i; }} }}\n    sum\n}}"""
    elif name == "fb_largest_prime_factor":
        java = f"""    public static int {fn}(int n) {{\n        int max = 0;\n        for (int i = 2; i <= n; i++) while (n % i == 0) {{ max = i; n /= i; }}\n        return max;\n    }}"""
        c = f"""int {fn}(int n) {{\n    int max = 0;\n    for (int i = 2; i <= n; i++) while (n % i == 0) {{ max = i; n /= i; }}\n    return max;\n}}"""
        rust = f"""pub fn {fn}(mut n: i32) -> i32 {{\n    let mut max = 0;\n    for i in 2..=n {{ while n % i == 0 {{ max = i; n /= i; }} }}\n    max\n}}"""
    elif name in {"fb_jacobsthal_number", "fb_pell_number", "fb_lucas_number"}:
        java, c, rust = recurrence_code(fn, name)
    elif name in {"fb_average_odd_upto", "fb_average_even_upto"}:
        parity = "1" if name == "fb_average_odd_upto" else "0"
        java = f"""    public static int {fn}(int n) {{\n        int sum = 0, count = 0;\n        for (int i = 1; i <= n; i++) if (i % 2 == {parity}) {{ sum += i; count++; }}\n        return sum / count;\n    }}"""
        c = f"""int {fn}(int n) {{\n    int sum = 0, count = 0;\n    for (int i = 1; i <= n; i++) if (i % 2 == {parity}) {{ sum += i; count++; }}\n    return sum / count;\n}}"""
        rust = f"""pub fn {fn}(n: i32) -> i32 {{\n    let (mut sum, mut count) = (0, 0);\n    for i in 1..=n {{ if i % 2 == {parity} {{ sum += i; count += 1; }} }}\n    sum / count\n}}"""
    elif name == "fb_smallest_divisor":
        java = f"""    public static int {fn}(int n) {{\n        int i = 2;\n        while (i <= n / i) {{ if (n % i == 0) return i; i++; }}\n        return n;\n    }}"""
        c = f"""int {fn}(int n) {{\n    int i = 2;\n    while (i <= n / i) {{ if (n % i == 0) return i; i++; }}\n    return n;\n}}"""
        rust = f"""pub fn {fn}(n: i32) -> i32 {{\n    let mut i = 2;\n    while i <= n / i {{ if n % i == 0 {{ return i; }} i += 1; }}\n    n\n}}"""
    elif name == "fb_next_power_of_two":
        java = f"""    public static int {fn}(int n) {{\n        if (n == 0) return 1;\n        int i = 1;\n        while (i < n) i <<= 1;\n        return i;\n    }}"""
        c = f"""int {fn}(int n) {{\n    if (n == 0) return 1;\n    int i = 1;\n    while (i < n) i <<= 1;\n    return i;\n}}"""
        rust = f"""pub fn {fn}(n: i32) -> i32 {{\n    if n == 0 {{ return 1; }}\n    let mut i = 1;\n    while i < n {{ i <<= 1; }}\n    i\n}}"""
    elif name in {"fb_sum_odd_range", "fb_sum_even_range"}:
        parity = "1" if name == "fb_sum_odd_range" else "0"
        java = f"""    public static int {fn}(int l, int r) {{\n        int sum = 0;\n        for (int i = l; i <= r; i++) if (i % 2 == {parity}) sum += i;\n        return sum;\n    }}"""
        c = f"""int {fn}(int l, int r) {{\n    int sum = 0;\n    for (int i = l; i <= r; i++) if (i % 2 == {parity}) sum += i;\n    return sum;\n}}"""
        rust = f"""pub fn {fn}(l: i32, r: i32) -> i32 {{\n    let mut sum = 0;\n    for i in l..=r {{ if i % 2 == {parity} {{ sum += i; }} }}\n    sum\n}}"""
    elif name == "fb_common_divisor_count":
        java = f"""    public static int {fn}(int x, int y) {{\n        int count = 0;\n        for (int i = 1; i <= x && i <= y; i++) if (x % i == 0 && y % i == 0) count++;\n        return count;\n    }}"""
        c = f"""int {fn}(int x, int y) {{\n    int count = 0;\n    for (int i = 1; i <= x && i <= y; i++) if (x % i == 0 && y % i == 0) count++;\n    return count;\n}}"""
        rust = f"""pub fn {fn}(x: i32, y: i32) -> i32 {{\n    let mut count = 0;\n    for i in 1..=x.min(y) {{ if x % i == 0 && y % i == 0 {{ count += 1; }} }}\n    count\n}}"""
    elif name == "fb_binomial_coefficient":
        java = f"""    public static int {fn}(int n, int k) {{\n        if (k > n - k) k = n - k;\n        int c = 1;\n        for (int i = 1; i <= k; i++) c = c * (n - i + 1) / i;\n        return c;\n    }}"""
        c = f"""int {fn}(int n, int k) {{\n    if (k > n - k) k = n - k;\n    int c = 1;\n    for (int i = 1; i <= k; i++) c = c * (n - i + 1) / i;\n    return c;\n}}"""
        rust = f"""pub fn {fn}(n: i32, mut k: i32) -> i32 {{\n    if k > n - k {{ k = n - k; }}\n    let mut c = 1;\n    for i in 1..=k {{ c = c * (n - i + 1) / i; }}\n    c\n}}"""
    elif name == "fb_digit_sum_simple":
        java = f"""    public static int {fn}(int n) {{\n        int sum = 0;\n        while (n > 0) {{ sum += n % 10; n /= 10; }}\n        return sum;\n    }}"""
        c = f"""int {fn}(int n) {{\n    int sum = 0;\n    while (n > 0) {{ sum += n % 10; n /= 10; }}\n    return sum;\n}}"""
        rust = f"""pub fn {fn}(mut n: i32) -> i32 {{\n    let mut sum = 0;\n    while n > 0 {{ sum += n % 10; n /= 10; }}\n    sum\n}}"""
    elif name == "fb_factorial_last_two_digits":
        java = f"""    public static int {fn}(int n) {{\n        int factorial = 1;\n        for (int i = 1; i <= n; i++) factorial *= i;\n        return factorial % 100;\n    }}"""
        c = f"""int {fn}(int n) {{\n    int factorial = 1;\n    for (int i = 1; i <= n; i++) factorial *= i;\n    return factorial % 100;\n}}"""
        rust = f"""pub fn {fn}(n: i32) -> i32 {{\n    let mut factorial = 1;\n    for i in 1..=n {{ factorial *= i; }}\n    factorial % 100\n}}"""
    elif name == "fb_first_set_bit_position":
        java = f"""    public static int {fn}(int n) {{\n        int i = 1;\n        while ((n & 1) == 0) {{ n >>= 1; i++; }}\n        return i;\n    }}"""
        c = f"""int {fn}(int n) {{\n    int i = 1;\n    while ((n & 1) == 0) {{ n >>= 1; i++; }}\n    return i;\n}}"""
        rust = f"""pub fn {fn}(mut n: i32) -> i32 {{\n    let mut i = 1;\n    while n & 1 == 0 {{ n >>= 1; i += 1; }}\n    i\n}}"""
    else:
        raise ValueError(name)
    return build_problem(name, source_path, description, requirements, params, tests, java, c, rust)


def recurrence_code(fn: str, name: str) -> tuple[str, str, str]:
    if name == "fb_jacobsthal_number":
        init0, init1, expr = 0, 1, "values[i - 1] + 2 * values[i - 2]"
        rexpr = "values[i - 1] + 2 * values[i - 2]"
    elif name == "fb_pell_number":
        init0, init1, expr = 0, 1, "(2 * values[i - 1] + values[i - 2]) % 1000000000"
        rexpr = "(2 * values[i - 1] + values[i - 2]) % 1000000000"
    else:
        init0, init1, expr = 2, 1, "values[i - 1] + values[i - 2]"
        rexpr = "values[i - 1] + values[i - 2]"
    java = f"""    public static int {fn}(int n) {{\n        int[] values = new int[n + 1];\n        values[0] = {init0}; values[1] = {init1};\n        for (int i = 2; i <= n; i++) values[i] = {expr};\n        return values[n];\n    }}"""
    c = f"""int {fn}(int n) {{\n    int values[51] = {{0}};\n    values[0] = {init0}; values[1] = {init1};\n    for (int i = 2; i <= n; i++) values[i] = {expr};\n    return values[n];\n}}"""
    rust = f"""pub fn {fn}(n: i32) -> i32 {{\n    let n = n as usize;\n    let mut values = vec![0; n + 1];\n    values[0] = {init0}; values[1] = {init1};\n    for i in 2..=n {{ values[i] = {rexpr}; }}\n    values[n]\n}}"""
    return java, c, rust


def main() -> None:
    selected = problems()
    for problem in selected:
        write_problem(problem)
    update_manifest(selected)
    update_readme()
    print(f"added {len(selected)} SESpec/FormalBench problems")


if __name__ == "__main__":
    main()

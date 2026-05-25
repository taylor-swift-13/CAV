#!/usr/bin/env python3
"""Add a small follow-up batch of easy SESpec/FormalBenchHF tasks."""

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


def arr_param(name: str) -> dict:
    return {"name": name, "type": "int_array"}


def camel(name: str) -> str:
    return "".join(part.capitalize() for part in name.split("_"))


def make(name, source_path, desc, reqs, params, tests, java, c, rust):
    return {
        "name": name,
        "source_path": source_path,
        "description": desc,
        "requirements": reqs,
        "params": params,
        "tests": tests,
        "code": {
            "java": f"class {camel(name)} {{\n{java}\n}}",
            "c": c,
            "rust": rust,
        },
    }


def case(names, values, expected):
    return {"input": dict(zip(names, values)), "expected": expected}


def md(problem, lang):
    reqs = "\n".join(f"- {r}" for r in problem["requirements"])
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
        f"```{lang}\n{problem['code'][lang]}\n```\n"
    )


def write_problem(problem):
    for lang in ("c", "java", "rust"):
        (DATASETS / lang / f"{problem['name']}.md").write_text(md(problem, lang), encoding="utf-8")
    spec = {
        "name": problem["name"],
        "return_type": "int",
        "params": problem["params"],
        "tests": [{"kind": "positive", **t} for t in problem["tests"]],
        "source": SOURCE | {"slug": f"FormalBenchHF/base/programs/{problem['source_path']}"},
    }
    (DATASETS / "tests" / f"{problem['name']}.json").write_text(
        json.dumps(spec, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


def update_manifest(problems):
    path = DATASETS / "manifest.json"
    manifest = json.loads(path.read_text(encoding="utf-8"))
    by_name = {p["name"]: p for p in manifest["problems"]}
    for p in problems:
        by_name[p["name"]] = {
            "name": p["name"],
            "return_type": "int",
            "params": p["params"],
            "source": SOURCE | {"slug": f"FormalBenchHF/base/programs/{p['source_path']}"},
        }
    manifest["problems"] = [by_name[name] for name in sorted(by_name)]
    path.write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    readme = DATASETS / "README.md"
    text = re.sub(r"- Problems: \d+", f"- Problems: {len(by_name)}", readme.read_text(encoding="utf-8"))
    readme.write_text(text, encoding="utf-8")


def set_leftmost_unset(n):
    if n & (n + 1) == 0:
        return n
    pos = count = 0
    temp = n
    while temp:
        if temp & 1 == 0:
            pos = count
        count += 1
        temp >>= 1
    return n | (1 << pos)


def factor_pair_count(n):
    if n == 1:
        return 1
    count = 0
    i = 2
    while i <= n // i:
        if n % i == 0:
            count += 1
            if n // i == i:
                break
        i += 1
    return count


def paint_ways(n, k):
    mod = 1000000007
    if n == 0:
        return 1
    if n == 1:
        return k
    dp = [0] * (n + 1)
    dp[0], dp[1], dp[2] = 1, k, k * k
    for i in range(3, n + 1):
        dp[i] = ((k - 1) * (dp[i - 1] + dp[i - 2])) % mod
    return dp[n]


def divisor_count_by_abs_bound(x, y):
    if y < 0:
        y = -y
    return sum(1 for i in range(1, y + 1) if x % i == 0)


def nth_non_multiple(a, n, l, r):
    count = 0
    for i in range(l, r + 1):
        if i % a != 0:
            count += 1
        if count == n:
            return i
    return -1


def jacobsthal_lucas(n):
    dp = [0] * (n + 1)
    dp[0], dp[1] = 2, 1
    for i in range(2, n + 1):
        dp[i] = dp[i - 1] + 2 * dp[i - 2]
    return dp[n]


def ncr_mod(n, r, p):
    if n < r:
        return 0
    value = 1
    for i in range(1, r + 1):
        value = (value * (n - i + 1)) // i
    return value % p


def modular_inverse_count(arr, n, p):
    return sum(1 for x in arr[:n] if (x * x) % p == 1)


def position_plus_offset(arr, n, value, offset):
    pos = 0
    for i in range(n):
        if arr[i] == value:
            pos = i
            break
    return pos + offset


def smallest_missing_index(arr, left, right):
    i, j = left, right
    while i <= j:
        mid = (i + j) // 2
        if arr[mid] == mid:
            i = mid + 1
        else:
            j = mid - 1
    return i


def product_remainder(arr, lens, n):
    prod = 1
    for x in arr[:lens]:
        prod *= x
    return prod % n


def problems():
    base = ["Use only integer arithmetic.", "Do not read stdin or write stdout."]
    out = []

    out.append(make(
        "fb_more_set_leftmost_unset_bit", "SetLeftMostUnsetBit.java",
        "Set the highest zero bit that appears below the highest set bit of `n`; return `n` unchanged if all such bits are already set.",
        ["`1 <= n <= 1000000`.", *base], [int_param("n")],
        [case(["n"], [v], set_leftmost_unset(v)) for v in [1, 2, 5, 10, 15, 42]],
        "    public static int fb_more_set_leftmost_unset_bit(int n) {\n        if ((n & (n + 1)) == 0) return n;\n        int pos = 0, count = 0, temp = n;\n        while (temp != 0) { if ((temp & 1) == 0) pos = count; count++; temp >>= 1; }\n        return n | (1 << pos);\n    }",
        "int fb_more_set_leftmost_unset_bit(int n) {\n    if ((n & (n + 1)) == 0) return n;\n    int pos = 0, count = 0, temp = n;\n    while (temp != 0) { if ((temp & 1) == 0) pos = count; count++; temp >>= 1; }\n    return n | (1 << pos);\n}",
        "pub fn fb_more_set_leftmost_unset_bit(n: i32) -> i32 {\n    if (n & (n + 1)) == 0 { return n; }\n    let (mut pos, mut count, mut temp) = (0, 0, n);\n    while temp != 0 { if (temp & 1) == 0 { pos = count; } count += 1; temp >>= 1; }\n    n | (1 << pos)\n}",
    ))
    out.append(make(
        "fb_more_factor_pair_count", "CountFac.java",
        "Count factor pairs of `n` found by scanning divisors from `2` through `sqrt(n)`, with the FormalBench special case `n == 1` returning `1`.",
        ["`1 <= n <= 100000`.", *base], [int_param("n")],
        [case(["n"], [v], factor_pair_count(v)) for v in [1, 2, 4, 6, 12, 36, 97]],
        "    public static int fb_more_factor_pair_count(int n) {\n        int count = 0;\n        if (n == 1) return 1;\n        for (int i = 2; i <= n / i; i++) { if (n % i == 0) { count++; if (n / i == i) break; } }\n        return count;\n    }",
        "int fb_more_factor_pair_count(int n) {\n    int count = 0;\n    if (n == 1) return 1;\n    for (int i = 2; i <= n / i; i++) { if (n % i == 0) { count++; if (n / i == i) break; } }\n    return count;\n}",
        "pub fn fb_more_factor_pair_count(n: i32) -> i32 {\n    let mut count = 0;\n    if n == 1 { return 1; }\n    let mut i = 2;\n    while i <= n / i { if n % i == 0 { count += 1; if n / i == i { break; } } i += 1; }\n    count\n}",
    ))
    out.append(make(
        "fb_more_paint_fence_ways", "CountNoOfWays.java",
        "Return the FormalBench paint-fence recurrence value for `n` posts and `k` colors.",
        ["`1 <= n <= 20`.", "`1 <= k <= 20`.", "Use modulo `1000000007` in the recurrence."], [int_param("n"), int_param("k")],
        [case(["n", "k"], list(v), paint_ways(*v)) for v in [(1, 3), (2, 3), (3, 2), (5, 3), (10, 2)]],
        "    public static int fb_more_paint_fence_ways(int n, int k) {\n        int mod = 1000000007;\n        int[] dp = new int[n + 1];\n        dp[0] = 1; dp[1] = k;\n        if (n >= 2) dp[2] = k * k;\n        for (int i = 3; i <= n; i++) dp[i] = ((k - 1) * (dp[i - 1] + dp[i - 2])) % mod;\n        return dp[n];\n    }",
        "int fb_more_paint_fence_ways(int n, int k) {\n    int mod = 1000000007;\n    int dp[21] = {0};\n    dp[0] = 1; dp[1] = k;\n    if (n >= 2) dp[2] = k * k;\n    for (int i = 3; i <= n; i++) dp[i] = ((k - 1) * (dp[i - 1] + dp[i - 2])) % mod;\n    return dp[n];\n}",
        "pub fn fb_more_paint_fence_ways(n: i32, k: i32) -> i32 {\n    let n = n as usize;\n    let mut dp = vec![0; n + 1];\n    dp[0] = 1; dp[1] = k;\n    if n >= 2 { dp[2] = k * k; }\n    for i in 3..=n { dp[i] = ((k - 1) * (dp[i - 1] + dp[i - 2])) % 1000000007; }\n    dp[n]\n}",
    ))
    out.append(make(
        "fb_more_divisor_count_to_abs_bound", "FindDivisor.java",
        "Count positive integers up to `abs(y)` that divide `x`.",
        ["`1 <= x <= 100000`.", "`-10000 <= y <= 10000`.", *base], [int_param("x"), int_param("y")],
        [case(["x", "y"], list(v), divisor_count_by_abs_bound(*v)) for v in [(12, 6), (12, -6), (10, 3), (97, 100)]],
        "    public static int fb_more_divisor_count_to_abs_bound(int x, int y) {\n        if (y < 0) y = -y;\n        int count = 0;\n        for (int i = 1; i <= y; i++) if (x % i == 0) count++;\n        return count;\n    }",
        "int fb_more_divisor_count_to_abs_bound(int x, int y) {\n    if (y < 0) y = -y;\n    int count = 0;\n    for (int i = 1; i <= y; i++) if (x % i == 0) count++;\n    return count;\n}",
        "pub fn fb_more_divisor_count_to_abs_bound(x: i32, mut y: i32) -> i32 {\n    if y < 0 { y = -y; }\n    let mut count = 0;\n    for i in 1..=y { if x % i == 0 { count += 1; } }\n    count\n}",
    ))
    out.append(make(
        "fb_more_nth_non_multiple_in_range", "CountNo.java",
        "Return the `n`th integer in `[l, r]` that is not divisible by `a`, or `-1` if fewer than `n` such integers exist.",
        ["`1 <= a <= 1000`.", "`1 <= n <= 1000`.", "`0 <= l <= r <= 10000`."], [int_param("a"), int_param("n"), int_param("l"), int_param("r")],
        [case(["a", "n", "l", "r"], list(v), nth_non_multiple(*v)) for v in [(2, 1, 1, 5), (2, 3, 1, 5), (3, 4, 1, 10), (5, 10, 1, 20)]],
        "    public static int fb_more_nth_non_multiple_in_range(int a, int n, int l, int r) {\n        int count = 0;\n        for (int i = l; i <= r; i++) { if (i % a != 0) count++; if (count == n) return i; }\n        return -1;\n    }",
        "int fb_more_nth_non_multiple_in_range(int a, int n, int l, int r) {\n    int count = 0;\n    for (int i = l; i <= r; i++) { if (i % a != 0) count++; if (count == n) return i; }\n    return -1;\n}",
        "pub fn fb_more_nth_non_multiple_in_range(a: i32, n: i32, l: i32, r: i32) -> i32 {\n    let mut count = 0;\n    for i in l..=r { if i % a != 0 { count += 1; } if count == n { return i; } }\n    -1\n}",
    ))
    out.append(make(
        "fb_more_jacobsthal_lucas", "JacobsthalLucas.java",
        "Return the `n`th Jacobsthal-Lucas number with `J(0)=2`, `J(1)=1`, and `J(n)=J(n-1)+2*J(n-2)`.",
        ["`1 <= n <= 30`.", *base], [int_param("n")],
        [case(["n"], [v], jacobsthal_lucas(v)) for v in [1, 2, 3, 4, 10, 20, 30]],
        "    public static int fb_more_jacobsthal_lucas(int n) {\n        int[] dp = new int[n + 1];\n        dp[0] = 2; dp[1] = 1;\n        for (int i = 2; i <= n; i++) dp[i] = dp[i - 1] + 2 * dp[i - 2];\n        return dp[n];\n    }",
        "int fb_more_jacobsthal_lucas(int n) {\n    int dp[31] = {0};\n    dp[0] = 2; dp[1] = 1;\n    for (int i = 2; i <= n; i++) dp[i] = dp[i - 1] + 2 * dp[i - 2];\n    return dp[n];\n}",
        "pub fn fb_more_jacobsthal_lucas(n: i32) -> i32 {\n    let n = n as usize;\n    let mut dp = vec![0; n + 1];\n    dp[0] = 2; dp[1] = 1;\n    for i in 2..=n { dp[i] = dp[i - 1] + 2 * dp[i - 2]; }\n    dp[n]\n}",
    ))
    out.append(make(
        "fb_more_ncr_mod", "NcrModP.java",
        "Return `C(n, r) mod p`, with `0` returned when `n < r`.",
        ["`0 <= r <= 12`.", "`0 <= n <= 20`.", "`2 <= p <= 1000`."], [int_param("n"), int_param("r"), int_param("p")],
        [case(["n", "r", "p"], list(v), ncr_mod(*v)) for v in [(5, 2, 7), (10, 3, 11), (3, 5, 13), (20, 10, 997)]],
        "    public static int fb_more_ncr_mod(int n, int r, int p) {\n        if (n < r) return 0;\n        int ncr = 1;\n        for (int i = 1; i <= r; i++) ncr = (ncr * (n - i + 1)) / i;\n        return ncr % p;\n    }",
        "int fb_more_ncr_mod(int n, int r, int p) {\n    if (n < r) return 0;\n    int ncr = 1;\n    for (int i = 1; i <= r; i++) ncr = (ncr * (n - i + 1)) / i;\n    return ncr % p;\n}",
        "pub fn fb_more_ncr_mod(n: i32, r: i32, p: i32) -> i32 {\n    if n < r { return 0; }\n    let mut ncr = 1;\n    for i in 1..=r { ncr = (ncr * (n - i + 1)) / i; }\n    ncr % p\n}",
    ))
    out.append(make(
        "fb_more_modular_inverse_square_count", "ModularInverse.java",
        "Count how many of the first `n` array values satisfy `(x*x) % p == 1`.",
        ["Array length is at most `50`.", "`2 <= p <= 1000`.", "Array values are nonnegative and small enough that `x*x` fits in signed 32-bit integer."],
        [arr_param("arr"), int_param("n"), int_param("p")],
        [case(["arr", "n", "p"], [arr, n, p], modular_inverse_count(arr, n, p)) for arr, n, p in [([1, 2, 3], 3, 5), ([1, 4, 6, 9], 4, 10), ([2, 3, 5], 3, 7)]],
        "    public static int fb_more_modular_inverse_square_count(int[] arr, int n, int p) {\n        int count = 0;\n        for (int i = 0; i < n; i++) if ((arr[i] * arr[i]) % p == 1) count++;\n        return count;\n    }",
        "int fb_more_modular_inverse_square_count(int arr[], int n, int p) {\n    int count = 0;\n    for (int i = 0; i < n; i++) if ((arr[i] * arr[i]) % p == 1) count++;\n    return count;\n}",
        "pub fn fb_more_modular_inverse_square_count(arr: &[i32], n: i32, p: i32) -> i32 {\n    let mut count = 0;\n    for i in 0..(n as usize) { if (arr[i] * arr[i]) % p == 1 { count += 1; } }\n    count\n}",
    ))
    out.append(make(
        "fb_more_position_plus_offset", "GetPosition.java",
        "Return the first index of `value` in the first `n` elements of `a`, plus `offset`; use index `0` if the value is not found.",
        ["Array length is at most `50`.", "Use zero-based indexing."], [arr_param("a"), int_param("n"), int_param("value"), int_param("offset")],
        [case(["a", "n", "value", "offset"], [arr, n, v, off], position_plus_offset(arr, n, v, off)) for arr, n, v, off in [([3, 4, 5], 3, 4, 10), ([1, 2, 3], 3, 9, 5), ([7, 7, 8], 3, 7, 2)]],
        "    public static int fb_more_position_plus_offset(int[] a, int n, int value, int offset) {\n        int pos = 0;\n        for (int i = 0; i < n; i++) { if (a[i] == value) { pos = i; break; } }\n        return pos + offset;\n    }",
        "int fb_more_position_plus_offset(int a[], int n, int value, int offset) {\n    int pos = 0;\n    for (int i = 0; i < n; i++) { if (a[i] == value) { pos = i; break; } }\n    return pos + offset;\n}",
        "pub fn fb_more_position_plus_offset(a: &[i32], n: i32, value: i32, offset: i32) -> i32 {\n    let mut pos = 0;\n    for i in 0..(n as usize) { if a[i] == value { pos = i as i32; break; } }\n    pos + offset\n}",
    ))
    out.append(make(
        "fb_more_smallest_missing_index", "SmallestMissing.java",
        "Given a sorted array segment where values may equal their indices, return the first index in `[left, right+1]` whose value is missing from its matching index.",
        ["Array length is at most `50`.", "`0 <= left <= right < array length`."], [arr_param("a"), int_param("left"), int_param("right")],
        [case(["a", "left", "right"], [arr, l, r], smallest_missing_index(arr, l, r)) for arr, l, r in [([0, 1, 2, 6], 0, 3), ([0, 1, 2, 3], 0, 3), ([0, 2, 3, 4], 0, 3)]],
        "    public static int fb_more_smallest_missing_index(int[] a, int left, int right) {\n        int i = left, j = right;\n        while (i <= j) { int mid = (i + j) / 2; if (a[mid] == mid) i = mid + 1; else j = mid - 1; }\n        return i;\n    }",
        "int fb_more_smallest_missing_index(int a[], int left, int right) {\n    int i = left, j = right;\n    while (i <= j) { int mid = (i + j) / 2; if (a[mid] == mid) i = mid + 1; else j = mid - 1; }\n    return i;\n}",
        "pub fn fb_more_smallest_missing_index(a: &[i32], left: i32, right: i32) -> i32 {\n    let (mut i, mut j) = (left, right);\n    while i <= j { let mid = (i + j) / 2; if a[mid as usize] == mid { i = mid + 1; } else { j = mid - 1; } }\n    i\n}",
    ))
    out.append(make(
        "fb_more_product_remainder", "FindRemainder.java",
        "Return the product of the first `lens` elements of `arr`, modulo `n`.",
        ["Array length is at most `20`.", "`1 <= n <= 100000`.", "The product fits in signed 64-bit integer for the stated tests."], [arr_param("arr"), int_param("lens"), int_param("n")],
        [case(["arr", "lens", "n"], [arr, lens, n], product_remainder(arr, lens, n)) for arr, lens, n in [([1, 2, 3], 3, 5), ([4, 5, 6], 2, 7), ([2, 2, 2, 2], 4, 3)]],
        "    public static int fb_more_product_remainder(int[] arr, int lens, int n) {\n        long product = 1;\n        for (int i = 0; i < lens; i++) product *= arr[i];\n        return (int)(product % n);\n    }",
        "int fb_more_product_remainder(int arr[], int lens, int n) {\n    long long product = 1;\n    for (int i = 0; i < lens; i++) product *= arr[i];\n    return (int)(product % n);\n}",
        "pub fn fb_more_product_remainder(arr: &[i32], lens: i32, n: i32) -> i32 {\n    let mut product: i64 = 1;\n    for i in 0..(lens as usize) { product *= arr[i] as i64; }\n    (product % n as i64) as i32\n}",
    ))
    return out


def main():
    selected = problems()
    for p in selected:
        write_problem(p)
    update_manifest(selected)
    print(f"added {len(selected)} more easy SESpec/FormalBench problems")


if __name__ == "__main__":
    main()

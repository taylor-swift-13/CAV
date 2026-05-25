#!/usr/bin/env python3
"""Add selected array-only SESpec/FormalBenchHF programs to the dataset."""

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


def camel(name: str) -> str:
    return "".join(part.capitalize() for part in name.split("_"))


def int_param(name: str) -> dict:
    return {"name": name, "type": "int"}


def arr_param(name: str) -> dict:
    return {"name": name, "type": "int_array"}


def cases(fn, params: list[str], values: list[tuple]) -> list[dict]:
    out = []
    for value in values:
        if not isinstance(value, tuple):
            value = (value,)
        out.append({"input": dict(zip(params, value)), "expected": fn(*value)})
    return out


def md(problem: dict, lang: str) -> str:
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
        f"```{lang}\n{problem['code'][lang]}\n```\n"
    )


def write_problem(problem: dict) -> None:
    for lang in ("c", "java", "rust"):
        (DATASETS / lang / f"{problem['name']}.md").write_text(md(problem, lang), encoding="utf-8")
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
    path = DATASETS / "manifest.json"
    manifest = json.loads(path.read_text(encoding="utf-8"))
    by_name = {p["name"]: p for p in manifest["problems"]}
    for problem in problems:
        by_name[problem["name"]] = {
            "name": problem["name"],
            "return_type": "int",
            "params": problem["params"],
            "source": SOURCE | {"slug": f"FormalBenchHF/base/programs/{problem['source_path']}"},
        }
    manifest["problems"] = [by_name[name] for name in sorted(by_name)]
    path.write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")

    readme = DATASETS / "README.md"
    text = readme.read_text(encoding="utf-8")
    text = re.sub(r"- Problems: \d+", f"- Problems: {len(by_name)}", text)
    readme.write_text(text, encoding="utf-8")


def array_problem(name: str, source_path: str, description: str, requirements: list[str],
                  params: list[dict], tests: list[dict], java: str, c: str, rust: str) -> dict:
    return {
        "name": name,
        "source_path": source_path,
        "description": description,
        "requirements": requirements,
        "params": params,
        "tests": tests,
        "code": {
            "java": f"class {camel(name)} {{\n{java}\n}}",
            "c": c,
            "rust": rust,
        },
    }


def freq_smallest(n, arr): return 0 if n == 0 else arr[:n].count(min(arr[:n]))
def max_subarray_len(a, size):
    best = cur = start = end = s = 0
    for i in range(size):
        cur += a[i]
        if best < cur:
            best, start, end = cur, s, i
        if cur < 0:
            cur, s = 0, i + 1
    return end - start + 1
def min_swaps_like(arr, n):
    count = i = 0; j = 1
    while i < n and j < n:
        if arr[i] == arr[j]: i += 1; j += 1; count += 1
        elif arr[i] > arr[j]: i += 1
        else: j += 1
    return count
def odd_occurrence(arr, n):
    result = count = 0
    for x in arr[:n]:
        if x % 2 != 0:
            count += 1
            if count % 2 != 0: result = x
    return result
def subarray_prod_sum(arr, n):
    total = 0
    for i in range(n):
        prod = 1
        for j in range(i, n):
            prod *= arr[j]; total += prod
    return total
def sum_even_even_index(arr, n): return sum(arr[i] for i in range(n) if i % 2 == 0 and arr[i] % 2 == 0)
def pair_xor_sum(arr, n): return sum(arr[i] ^ arr[j] for i in range(len(arr)) for j in range(i + 1, len(arr)))
def single_in_pairs(arr, n):
    i = 0
    while i < n - 1:
        if arr[i] == arr[i + 1]: i += 2
        else: return arr[i]
    return arr[n - 1]
def second_rise_value(arr, n): 
    result = 0; mn = arr[0]
    for x in arr[1:n]:
        if x > mn: result = result if result > mn else mn
        else: mn = x
    return result
def largest_positive(arr, n): return max([0] + [x for x in arr[:n] if x > 0])
def first_even(arr, n): return next((x for x in arr[:n] if x % 2 == 0), 0)
def neg_count(arr, n): return sum(1 for x in arr[:n] if x < 0)
def count_value(arr, n, value): return sum(1 for x in arr[:n] if x == value)
def odd_length_sum(arr):
    n = len(arr)
    return sum((((i + 1) * (n - i) + 1) // 2) * arr[i] for i in range(n))
def range_sum(arr, m, n): return sum(arr[m:n + 1])
def peak_index(arr, n):
    left, right = 0, n - 1
    while left < right:
        mid = left + (right - left) // 2
        if arr[mid] < arr[mid + 1]: left = mid + 1
        else: right = mid
    return left
def fixed_point(arr, n):
    start, end = 0, n - 1
    while start <= end:
        mid = start + (end - start) // 2
        if arr[mid] == mid: return mid
        if arr[mid] < mid: start = mid + 1
        else: end = mid - 1
    return -1
def even_xor_pairs(arr, n): return sum(1 for i in range(len(arr)) for j in range(i + 1, len(arr)) if ((arr[i] ^ arr[j]) & 1) == 0)
def odd_xor_pairs(arr, n): return sum(1 for i in range(len(arr)) for j in range(i + 1, len(arr)) if (arr[i] ^ arr[j]) % 2 == 1)
def distinct_pairs(arr, n): return sum(1 for i in range(len(arr) - 1) for j in range(i + 1, len(arr)) if arr[i] != arr[j])
def inversions(arr, n): return sum(1 for i in range(n) for j in range(i + 1, n) if arr[i] > arr[j])


def code_for(name: str) -> tuple[str, str, str]:
    if name == "fb_array_frequency_smallest":
        return (
            """    public static int fb_array_frequency_smallest(int n, int[] arr) {\n        if (n == 0) return 0;\n        int min = arr[0], count = 1;\n        for (int i = 1; i < n; i++) {\n            if (min > arr[i]) { min = arr[i]; count = 1; }\n            else if (min == arr[i]) count++;\n        }\n        return count;\n    }""",
            """int fb_array_frequency_smallest(int n, int arr[]) {\n    if (n == 0) return 0;\n    int min = arr[0], count = 1;\n    for (int i = 1; i < n; i++) {\n        if (min > arr[i]) { min = arr[i]; count = 1; }\n        else if (min == arr[i]) count++;\n    }\n    return count;\n}""",
            """pub fn fb_array_frequency_smallest(n: i32, arr: &[i32]) -> i32 {\n    if n == 0 { return 0; }\n    let (mut min, mut count) = (arr[0], 1);\n    for i in 1..(n as usize) {\n        if min > arr[i] { min = arr[i]; count = 1; }\n        else if min == arr[i] { count += 1; }\n    }\n    count\n}""",
        )
    if name == "fb_array_max_subarray_length":
        return (
            """    public static int fb_array_max_subarray_length(int[] a, int size) {\n        int best = 0, cur = 0, start = 0, end = 0, s = 0;\n        for (int i = 0; i < size; i++) {\n            cur += a[i];\n            if (best < cur) { best = cur; start = s; end = i; }\n            if (cur < 0) { cur = 0; s = i + 1; }\n        }\n        return end - start + 1;\n    }""",
            """int fb_array_max_subarray_length(int a[], int size) {\n    int best = 0, cur = 0, start = 0, end = 0, s = 0;\n    for (int i = 0; i < size; i++) {\n        cur += a[i];\n        if (best < cur) { best = cur; start = s; end = i; }\n        if (cur < 0) { cur = 0; s = i + 1; }\n    }\n    return end - start + 1;\n}""",
            """pub fn fb_array_max_subarray_length(a: &[i32], size: i32) -> i32 {\n    let (mut best, mut cur, mut start, mut end, mut s) = (0, 0, 0, 0, 0);\n    for i in 0..(size as usize) {\n        cur += a[i];\n        if best < cur { best = cur; start = s; end = i as i32; }\n        if cur < 0 { cur = 0; s = i as i32 + 1; }\n    }\n    end - start + 1\n}""",
        )
    templates = {
        "fb_array_min_swaps_like": ("int[] arr, int n", "int arr[], int n", "arr: &[i32], n: i32", "int count = 0, i = 0, j = 1;\n        while (i < n && j < n) {\n            if (arr[i] == arr[j]) { i++; j++; count++; }\n            else if (arr[i] > arr[j]) i++;\n            else j++;\n        }\n        return count;", "let (mut count, mut i, mut j) = (0, 0usize, 1usize);\n    while i < n as usize && j < n as usize {\n        if arr[i] == arr[j] { i += 1; j += 1; count += 1; }\n        else if arr[i] > arr[j] { i += 1; }\n        else { j += 1; }\n    }\n    count"),
        "fb_array_odd_occurrence_scan": ("int[] arr, int n", "int arr[], int n", "arr: &[i32], n: i32", "int result = 0, count = 0;\n        for (int i = 0; i < n; i++) if (arr[i] % 2 != 0) { count++; if (count % 2 != 0) result = arr[i]; }\n        return result;", "let (mut result, mut count) = (0, 0);\n    for i in 0..(n as usize) { if arr[i] % 2 != 0 { count += 1; if count % 2 != 0 { result = arr[i]; } } }\n    result"),
        "fb_array_subarray_product_sum": ("int[] arr, int n", "int arr[], int n", "arr: &[i32], n: i32", "int sum = 0;\n        for (int i = 0; i < n; i++) { int product = 1; for (int j = i; j < n; j++) { product *= arr[j]; sum += product; } }\n        return sum;", "let mut sum = 0;\n    for i in 0..(n as usize) { let mut product = 1; for j in i..(n as usize) { product *= arr[j]; sum += product; } }\n    sum"),
        "fb_array_sum_even_even_index": ("int[] arr, int n", "int arr[], int n", "arr: &[i32], n: i32", "int sum = 0;\n        for (int i = 0; i < n; i++) if (i % 2 == 0 && arr[i] % 2 == 0) sum += arr[i];\n        return sum;", "let mut sum = 0;\n    for i in 0..(n as usize) { if i % 2 == 0 && arr[i] % 2 == 0 { sum += arr[i]; } }\n    sum"),
        "fb_array_pair_xor_sum": ("int[] arr, int n", "int arr[], int n", "arr: &[i32], n: i32", "int sum = 0;\n        for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) sum += arr[i] ^ arr[j];\n        return sum;", "let mut sum = 0;\n    for i in 0..(n as usize) { for j in (i + 1)..(n as usize) { sum += arr[i] ^ arr[j]; } }\n    sum"),
        "fb_array_single_in_pairs": ("int[] arr, int n", "int arr[], int n", "arr: &[i32], n: i32", "int i = 0;\n        while (i < n - 1) { if (arr[i] == arr[i + 1]) i += 2; else return arr[i]; }\n        return arr[n - 1];", "let mut i = 0usize;\n    while i < n as usize - 1 { if arr[i] == arr[i + 1] { i += 2; } else { return arr[i]; } }\n    arr[n as usize - 1]"),
        "fb_array_second_rise_value": ("int[] arr, int n", "int arr[], int n", "arr: &[i32], n: i32", "int result = 0, min = arr[0];\n        for (int i = 1; i < n; i++) { if (arr[i] > min) result = result > min ? result : min; else min = arr[i]; }\n        return result;", "let (mut result, mut min) = (0, arr[0]);\n    for i in 1..(n as usize) { let x = arr[i]; if x > min { if result < min { result = min; } } else { min = x; } }\n    result"),
        "fb_array_largest_positive": ("int[] array, int n", "int array[], int n", "array: &[i32], n: i32", "int max = 0;\n        for (int i = 0; i < n; i++) if (array[i] > 0 && array[i] > max) max = array[i];\n        return max;", "let mut max = 0;\n    for i in 0..(n as usize) { let x = array[i]; if x > 0 && x > max { max = x; } }\n    max"),
        "fb_array_first_even": ("int[] nums, int n", "int nums[], int n", "nums: &[i32], n: i32", "int even = 0;\n        for (int i = 0; i < n; i++) if (nums[i] % 2 == 0) { even = nums[i]; break; }\n        return even;", "for i in 0..(n as usize) { if nums[i] % 2 == 0 { return nums[i]; } }\n    0"),
        "fb_array_negative_count": ("int[] array, int n", "int array[], int n", "array: &[i32], n: i32", "int count = 0;\n        for (int i = 0; i < n; i++) if (array[i] < 0) count++;\n        return count;", "let mut count = 0;\n    for i in 0..(n as usize) { if array[i] < 0 { count += 1; } }\n    count"),
        "fb_array_count_value": ("int[] tuplex, int n, int value", "int tuplex[], int n, int value", "tuplex: &[i32], n: i32, value: i32", "int count = 0;\n        for (int i = 0; i < n; i++) if (tuplex[i] == value) count++;\n        return count;", "let mut count = 0;\n    for i in 0..(n as usize) { if tuplex[i] == value { count += 1; } }\n    count"),
        "fb_array_frequency_value": ("int[] a, int n, int x", "int a[], int n, int x", "a: &[i32], n: i32, x: i32", "int count = 0;\n        for (int i = 0; i < n; i++) if (a[i] == x) count++;\n        return count;", "let mut count = 0;\n    for i in 0..(n as usize) { if a[i] == x { count += 1; } }\n    count"),
        "fb_array_odd_length_subarray_sum": ("int[] arr, int n", "int arr[], int n", "arr: &[i32], n: i32", "int sum = 0, l = n;\n        for (int i = 0; i < l; i++) sum += ((((i + 1) * (l - i) + 1) / 2) * arr[i]);\n        return sum;", "let mut sum = 0;\n    let l = n as usize;\n    for i in 0..l { sum += ((((i + 1) * (l - i) + 1) / 2) as i32) * arr[i]; }\n    sum"),
        "fb_array_range_sum": ("int[] nums, int m, int n", "int nums[], int m, int n", "nums: &[i32], m: i32, n: i32", "int sum = 0;\n        for (int i = m; i <= n; i++) sum += nums[i];\n        return sum;", "let mut sum = 0;\n    for i in (m as usize)..=(n as usize) { sum += nums[i]; }\n    sum"),
        "fb_array_peak_index": ("int[] arr, int n", "int arr[], int n", "arr: &[i32], n: i32", "int left = 0, right = n - 1;\n        while (left < right) { int mid = left + (right - left) / 2; if (arr[mid] < arr[mid + 1]) left = mid + 1; else right = mid; }\n        return left;", "let (mut left, mut right) = (0usize, n as usize - 1);\n    while left < right { let mid = left + (right - left) / 2; if arr[mid] < arr[mid + 1] { left = mid + 1; } else { right = mid; } }\n    left as i32"),
        "fb_array_fixed_point": ("int[] arr, int n", "int arr[], int n", "arr: &[i32], n: i32", "int start = 0, end = n - 1;\n        while (start <= end) { int mid = start + (end - start) / 2; if (arr[mid] == mid) return mid; else if (arr[mid] < mid) start = mid + 1; else end = mid - 1; }\n        return -1;", "let (mut start, mut end) = (0, n - 1);\n    while start <= end { let mid = start + (end - start) / 2; let value = arr[mid as usize]; if value == mid { return mid; } else if value < mid { start = mid + 1; } else { end = mid - 1; } }\n    -1"),
        "fb_array_even_xor_pair_count": ("int[] a, int n", "int a[], int n", "a: &[i32], n: i32", "int count = 0;\n        for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) if (((a[i] ^ a[j]) & 1) == 0) count++;\n        return count;", "let mut count = 0;\n    for i in 0..(n as usize) { for j in (i + 1)..(n as usize) { if ((a[i] ^ a[j]) & 1) == 0 { count += 1; } } }\n    count"),
        "fb_array_odd_xor_pair_count": ("int[] a, int n", "int a[], int n", "a: &[i32], n: i32", "int count = 0;\n        for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) if ((a[i] ^ a[j]) % 2 == 1) count++;\n        return count;", "let mut count = 0;\n    for i in 0..(n as usize) { for j in (i + 1)..(n as usize) { if (a[i] ^ a[j]) % 2 == 1 { count += 1; } } }\n    count"),
        "fb_array_distinct_pair_count": ("int[] arr, int n", "int arr[], int n", "arr: &[i32], n: i32", "int count = 0;\n        for (int i = 0; i < n - 1; i++) for (int j = i + 1; j < n; j++) if (arr[i] != arr[j]) count++;\n        return count;", "let mut count = 0;\n    for i in 0..(n as usize - 1) { for j in (i + 1)..(n as usize) { if arr[i] != arr[j] { count += 1; } } }\n    count"),
        "fb_array_inversion_count": ("int[] arr, int n", "int arr[], int n", "arr: &[i32], n: i32", "int count = 0;\n        for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) if (arr[i] > arr[j]) count++;\n        return count;", "let mut count = 0;\n    for i in 0..(n as usize) { for j in (i + 1)..(n as usize) { if arr[i] > arr[j] { count += 1; } } }\n    count"),
    }
    jparams, cparams, rparams, jbody, rbody = templates[name]
    java = f"    public static int {name}({jparams}) {{\n        {jbody}\n    }}"
    c = f"int {name}({cparams}) {{\n    {jbody.replace('        ', '    ')}\n}}"
    rust = f"pub fn {name}({rparams}) -> i32 {{\n    {rbody}\n}}"
    return java, c, rust


def problems() -> list[dict]:
    base_req = ["Array length is at most `50`.", "Array values are signed 32-bit integers.", "Do not read stdin or write stdout."]
    specs = [
        ("fb_array_frequency_smallest", "FrequencyOfSmallest.java", "Return how many times the smallest value appears in the first `n` elements of `arr`.", [int_param("n"), arr_param("arr")], cases(freq_smallest, ["n", "arr"], [(0, []), (1, [5]), (5, [3, 1, 1, 2, 1]), (4, [-2, -2, 0, -1])])),
        ("fb_array_max_subarray_length", "MaxSubArraySum.java", "Return the length of the contiguous subarray with the largest positive running sum, following the FormalBench zero-baseline scan.", [arr_param("a"), int_param("size")], cases(max_subarray_len, ["a", "size"], [([1, 2, 3], 3), ([-1, 5, -2, 3], 4), ([-5, -1], 2), ([4, -10, 2, 2], 4)])),
        ("fb_array_min_swaps_like", "FindMinSwaps.java", "Run the two-pointer FormalBench scan and return how many equal aligned pairs it counts.", [arr_param("arr"), int_param("n")], cases(min_swaps_like, ["arr", "n"], [([1, 1, 2, 2], 4), ([1, 2, 1, 2], 4), ([3, 1, 3, 2], 4)])),
        ("fb_array_odd_occurrence_scan", "GetOddOccurrence.java", "Scan the first `n` elements and return the odd value seen at each odd-numbered odd occurrence.", [arr_param("arr"), int_param("n")], cases(odd_occurrence, ["arr", "n"], [([2, 4], 2), ([1, 2, 3, 5], 4), ([7, 9, 11], 3)])),
        ("fb_array_subarray_product_sum", "SumOfSubarrayProd.java", "Return the sum of products of every contiguous subarray in the first `n` elements.", [arr_param("arr"), int_param("n")], cases(subarray_prod_sum, ["arr", "n"], [([1], 1), ([1, 2], 2), ([1, 2, 3], 3), ([2, -1, 3], 3)])),
        ("fb_array_sum_even_even_index", "SumEvenAndEvenIndex.java", "Return the sum of elements that are both at an even index and even-valued in the first `n` elements.", [arr_param("arr"), int_param("n")], cases(sum_even_even_index, ["arr", "n"], [([2, 3, 4], 3), ([1, 2, 6, 8], 4), ([-2, 4, -6], 3)])),
        ("fb_array_pair_xor_sum", "PairOrSum.java", "Return the sum of bitwise XOR over all unordered pairs in the first `n` elements.", [arr_param("arr"), int_param("n")], cases(pair_xor_sum, ["arr", "n"], [([1, 2], 2), ([1, 2, 3], 3), ([4, 4, 1], 3)])),
        ("fb_array_single_in_pairs", "Search.java", "Given adjacent equal pairs with one unpaired value, return the unpaired value.", [arr_param("arr"), int_param("n")], cases(single_in_pairs, ["arr", "n"], [([1], 1), ([1, 1, 2], 3), ([1, 1, 3, 4, 4], 5)])),
        ("fb_array_second_rise_value", "GetGcd.java", "Return the FormalBench scan value that tracks the previous minimum before a later larger value.", [arr_param("arr"), int_param("n")], cases(second_rise_value, ["arr", "n"], [([1, 2, 3], 3), ([5, 1, 4], 3), ([3, 2, 1], 3)])),
        ("fb_array_largest_positive", "LargestPos.java", "Return the largest positive value in the first `n` elements of `array`, or `0` if there is none.", [arr_param("array"), int_param("n")], cases(largest_positive, ["array", "n"], [([-1, -2], 2), ([0, 5, 3], 3), ([7, -1, 9], 3)])),
        ("fb_array_first_even", "FirstEven.java", "Return the first even value in the first `n` elements of `nums`, or `0` if no even value appears.", [arr_param("nums"), int_param("n")], cases(first_even, ["nums", "n"], [([1, 3, 5], 3), ([1, 4, 6], 3), ([-3, -2, 8], 3)])),
        ("fb_array_negative_count", "NegCount.java", "Return the number of negative values in the first `n` elements of `array`.", [arr_param("array"), int_param("n")], cases(neg_count, ["array", "n"], [([], 0), ([1, -1, -2], 3), ([0, 3], 2)])),
        ("fb_array_count_value", "CountTuplex.java", "Return how many of the first `n` elements of `tuplex` are equal to `value`.", [arr_param("tuplex"), int_param("n"), int_param("value")], cases(count_value, ["tuplex", "n", "value"], [([1, 2, 1], 3, 1), ([0, 0], 2, 3), ([-1, -1, 2], 3, -1)])),
        ("fb_array_frequency_value", "Frequency.java", "Return how many of the first `n` elements of `a` are equal to `x`.", [arr_param("a"), int_param("n"), int_param("x")], cases(count_value, ["a", "n", "x"], [([1, 2, 1], 3, 2), ([5, 5, 5], 3, 5), ([], 0, 1)])),
        ("fb_array_odd_length_subarray_sum", "OddLengthSum.java", "Return the sum of every odd-length contiguous subarray in the first `n` elements of `arr`.", [arr_param("arr"), int_param("n")], cases(lambda arr, n: odd_length_sum(arr[:n]), ["arr", "n"], [([1], 1), ([1, 2], 2), ([1, 4, 2, 5, 3], 5)])),
        ("fb_array_range_sum", "SumRangeList.java", "Return the sum of `nums[m]` through `nums[n]`, inclusive.", [arr_param("nums"), int_param("m"), int_param("n")], cases(range_sum, ["nums", "m", "n"], [([1, 2, 3], 0, 2), ([5, -1, 4, 2], 1, 3), ([7], 0, 0)])),
        ("fb_array_peak_index", "FindPeak.java", "Return a peak index found by the FormalBench binary scan.", [arr_param("arr"), int_param("n")], cases(peak_index, ["arr", "n"], [([1], 1), ([1, 3, 2], 3), ([1, 2, 3, 4], 4), ([4, 3, 2], 3)])),
        ("fb_array_fixed_point", "FindFixedPoint.java", "For a sorted array, return an index `i` such that `arr[i] == i`, or `-1` if none exists.", [arr_param("arr"), int_param("n")], cases(fixed_point, ["arr", "n"], [([-1, 0, 2], 3), ([-1, 0, 1], 3), ([0, 2, 5], 3)])),
        ("fb_array_even_xor_pair_count", "FindEvenPair.java", "Return how many unordered pairs have an even bitwise XOR.", [arr_param("a"), int_param("n")], cases(even_xor_pairs, ["a", "n"], [([1, 3, 5], 3), ([1, 2, 3], 3), ([2, 4, 6, 8], 4)])),
        ("fb_array_odd_xor_pair_count", "FindOddPair.java", "Return how many unordered pairs have an odd bitwise XOR.", [arr_param("a"), int_param("n")], cases(odd_xor_pairs, ["a", "n"], [([1, 3, 5], 3), ([1, 2, 3], 3), ([2, 4, 6, 8], 4)])),
        ("fb_array_distinct_pair_count", "CountPairs.java", "Return how many unordered pairs contain two different values.", [arr_param("arr"), int_param("n")], cases(distinct_pairs, ["arr", "n"], [([1, 1], 2), ([1, 2, 3], 3), ([2, 2, 3, 3], 4)])),
        ("fb_array_inversion_count", "GetInvCount.java", "Return the number of inversions in the first `n` elements of `arr`.", [arr_param("arr"), int_param("n")], cases(inversions, ["arr", "n"], [([1, 2, 3], 3), ([3, 2, 1], 3), ([2, 4, 1, 3], 4)])),
    ]
    out = []
    for name, source, desc, params, tests in specs:
        java, c, rust = code_for(name)
        out.append(array_problem(name, source, desc, base_req, params, tests, java, c, rust))
    return out


def main() -> None:
    selected = problems()
    for problem in selected:
        write_problem(problem)
    update_manifest(selected)
    print(f"added {len(selected)} SESpec/FormalBench array problems")


if __name__ == "__main__":
    main()

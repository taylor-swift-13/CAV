#!/usr/bin/env python3
"""Add easy search/count SESpec/FormalBenchHF tasks."""

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


def make(name, source_path, desc, params, tests, java, c, rust, reqs=None):
    reqs = reqs or ["Inputs satisfy the stated bounds.", "Do not read stdin or write stdout."]
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
    (DATASETS / "tests" / f"{problem['name']}.json").write_text(json.dumps(spec, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


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
    readme.write_text(re.sub(r"- Problems: \d+", f"- Problems: {len(by_name)}", readme.read_text(encoding="utf-8")), encoding="utf-8")


def big_diff(nums, n): return max(nums[:n]) - min(nums[:n])
def count_rectangles(radius):
    total = 0; d2 = (2 * radius) * (2 * radius)
    for a in range(1, 2 * radius + 1):
        for b in range(1, 2 * radius + 1):
            if a * a + b * b <= d2: total += 1
    return total
def first_occ(a, n, x):
    lo, hi, ans = 0, n - 1, -1
    while lo <= hi:
        mid = (lo + hi) // 2
        if a[mid] == x: ans = mid; hi = mid - 1
        elif a[mid] < x: lo = mid + 1
        else: hi = mid - 1
    return ans
def last_occ(a, n, x):
    lo, hi, ans = 0, n - 1, -1
    while lo <= hi:
        mid = (lo + hi) // 2
        if a[mid] == x: ans = mid; lo = mid + 1
        elif a[mid] < x: lo = mid + 1
        else: hi = mid - 1
    return ans
def rotation_count(a, n):
    start, end = 0, n - 1
    while start <= end:
        mid = start + (end - start) // 2
        if mid < end and a[mid] > a[mid + 1]: return mid + 1
        if mid > start and a[mid] < a[mid - 1]: return mid
        if a[mid] >= a[start]: start = mid + 1
        else: end = mid - 1
    return 0
def odd_then_even_number(n, k):
    count = 0
    for i in range(1, n + 1, 2):
        count += 1
        if count == k: return i
    for i in range(2, n + 1, 2):
        count += 1
        if count == k: return i
    return 0
def pair_sum_count(arr, n, target): return sum(1 for i in range(n) for j in range(i + 1, n) if arr[i] + arr[j] == target)
def lateral_surface_special(l): return 100 if l == 5 else 324 if l == 9 else 400 if l == 10 else -1
def max_volume(s):
    best = 0
    for l in range(1, s + 1):
        for b in range(1, s - l + 2):
            h = s - l - b
            best = max(best, l * b * h)
    return best
def min3(a,b,c): return min(a,b,c)
def min_ops(arr,n,k):
    mx=max(arr[:n]); total=0
    for x in arr[:n]:
        if (mx-x)%k != 0: return -1
        total += (mx-x)//k
    return total
def missing_seq(ar,n):
    missing=1
    if n==0 or n==1: return missing
    for i in range(1,n+1):
        if ar[i-1]==i: missing=i
        else: return i
    return missing
def insertion_left(a,n,x):
    lo,hi=0,n-1
    while lo<=hi:
        mid=(lo+hi)//2
        if a[mid]==x: return mid
        if a[mid]<x: lo=mid+1
        else: hi=mid-1
    return lo


def problems():
    p=[]
    p.append(make("fb_search_big_difference","BigDiff.java","Return the difference between the maximum and minimum value in the first `n` elements of `nums`.",[arr_param("nums"),int_param("n")],[case(["nums","n"],[a,len(a)],big_diff(a,len(a))) for a in [[1,2,3],[5,1,9,-2],[7]]],
        "    public static int fb_search_big_difference(int[] nums, int n) {\n        int max = nums[0], min = nums[0];\n        for (int i = 1; i < n; i++) { if (nums[i] > max) max = nums[i]; if (nums[i] < min) min = nums[i]; }\n        return max - min;\n    }",
        "int fb_search_big_difference(int nums[], int n) {\n    int max = nums[0], min = nums[0];\n    for (int i = 1; i < n; i++) { if (nums[i] > max) max = nums[i]; if (nums[i] < min) min = nums[i]; }\n    return max - min;\n}",
        "pub fn fb_search_big_difference(nums: &[i32], n: i32) -> i32 {\n    let (mut max, mut min) = (nums[0], nums[0]);\n    for i in 1..(n as usize) { if nums[i] > max { max = nums[i]; } if nums[i] < min { min = nums[i]; } }\n    max - min\n}",["`1 <= n <= nums.length <= 50`.","Values are signed 32-bit integers."]))
    p.append(make("fb_search_rectangle_count","CountRectangles.java","Count positive integer side pairs `(a,b)` whose rectangle diagonal fits inside a circle with the given `radius`.",[int_param("radius")],[case(["radius"],[r],count_rectangles(r)) for r in [1,2,3,5]],
        "    public static int fb_search_rectangle_count(int radius) {\n        int count = 0, limit = 2 * radius, d2 = limit * limit;\n        for (int a = 1; a <= limit; a++) for (int b = 1; b <= limit; b++) if (a * a + b * b <= d2) count++;\n        return count;\n    }",
        "int fb_search_rectangle_count(int radius) {\n    int count = 0, limit = 2 * radius, d2 = limit * limit;\n    for (int a = 1; a <= limit; a++) for (int b = 1; b <= limit; b++) if (a * a + b * b <= d2) count++;\n    return count;\n}",
        "pub fn fb_search_rectangle_count(radius: i32) -> i32 {\n    let (mut count, limit) = (0, 2 * radius); let d2 = limit * limit;\n    for a in 1..=limit { for b in 1..=limit { if a * a + b * b <= d2 { count += 1; } } }\n    count\n}",["`1 <= radius <= 20`.","Use inclusive loops over side lengths from `1` to `2*radius`."]))
    for name, src, desc, fn, java_name in [
        ("fb_search_first_occurrence","FindFirstOccurrence.java","Return the first index of `x` in the sorted first `n` elements of `a`, or `-1` if absent.",first_occ,"first"),
        ("fb_search_last_occurrence","FindLastOccurrence.java","Return the last index of `x` in the sorted first `n` elements of `a`, or `-1` if absent.",last_occ,"last"),
    ]:
        body_cmp = "high = mid - 1" if "first" in name else "low = mid + 1"
        p.append(make(name,src,desc,[arr_param("a"),int_param("n"),int_param("x")],[case(["a","n","x"],[a,len(a),x],fn(a,len(a),x)) for a,x in [([1,2,2,2,3],2),([1,3,5],4),([7,7,7],7)]],
            f"    public static int {name}(int[] a, int n, int x) {{\n        int low = 0, high = n - 1, result = -1;\n        while (low <= high) {{ int mid = (low + high) / 2; if (a[mid] == x) {{ result = mid; {body_cmp}; }} else if (a[mid] < x) low = mid + 1; else high = mid - 1; }}\n        return result;\n    }}",
            f"int {name}(int a[], int n, int x) {{\n    int low = 0, high = n - 1, result = -1;\n    while (low <= high) {{ int mid = (low + high) / 2; if (a[mid] == x) {{ result = mid; {body_cmp}; }} else if (a[mid] < x) low = mid + 1; else high = mid - 1; }}\n    return result;\n}}",
            f"pub fn {name}(a: &[i32], n: i32, x: i32) -> i32 {{\n    let (mut low, mut high, mut result) = (0, n - 1, -1);\n    while low <= high {{ let mid = (low + high) / 2; let v = a[mid as usize]; if v == x {{ result = mid; {'high = mid - 1' if 'first' in name else 'low = mid + 1'}; }} else if v < x {{ low = mid + 1; }} else {{ high = mid - 1; }} }}\n    result\n}}",["`0 <= n <= a.length <= 50`.","The first `n` elements are sorted in nondecreasing order."]))
    p.append(make("fb_search_rotation_count","FindRotationCount.java","Return the rotation count of a sorted array that was rotated, or `0` when no pivot is found.",[arr_param("a"),int_param("n")],[case(["a","n"],[a,len(a)],rotation_count(a,len(a))) for a in [[1,2,3],[3,4,5,1,2],[2,3,4,5,1]]],
        "    public static int fb_search_rotation_count(int[] a, int n) {\n        int start = 0, end = n - 1;\n        while (start <= end) { int mid = start + (end - start) / 2; if (mid < end && a[mid] > a[mid + 1]) return mid + 1; if (mid > start && a[mid] < a[mid - 1]) return mid; if (a[mid] >= a[start]) start = mid + 1; else end = mid - 1; }\n        return 0;\n    }",
        "int fb_search_rotation_count(int a[], int n) {\n    int start = 0, end = n - 1;\n    while (start <= end) { int mid = start + (end - start) / 2; if (mid < end && a[mid] > a[mid + 1]) return mid + 1; if (mid > start && a[mid] < a[mid - 1]) return mid; if (a[mid] >= a[start]) start = mid + 1; else end = mid - 1; }\n    return 0;\n}",
        "pub fn fb_search_rotation_count(a: &[i32], n: i32) -> i32 {\n    let (mut start, mut end) = (0, n - 1);\n    while start <= end { let mid = start + (end - start) / 2; if mid < end && a[mid as usize] > a[mid as usize + 1] { return mid + 1; } if mid > start && a[mid as usize] < a[mid as usize - 1] { return mid; } if a[mid as usize] >= a[start as usize] { start = mid + 1; } else { end = mid - 1; } }\n    0\n}",["`1 <= n <= a.length <= 50`.","The first `n` elements are strictly increasing after some rotation."]))
    p.append(make("fb_search_odd_then_even_number","GetNumber.java","List numbers `1..n` with odds first and evens second; return the `k`th listed number, or `0` if `k` is out of range.",[int_param("n"),int_param("k")],[case(["n","k"],[n,k],odd_then_even_number(n,k)) for n,k in [(5,1),(5,3),(5,4),(4,4),(3,5)]],
        "    public static int fb_search_odd_then_even_number(int n, int k) {\n        int count = 0;\n        for (int i = 1; i <= n; i += 2) { count++; if (count == k) return i; }\n        for (int i = 2; i <= n; i += 2) { count++; if (count == k) return i; }\n        return 0;\n    }",
        "int fb_search_odd_then_even_number(int n, int k) {\n    int count = 0;\n    for (int i = 1; i <= n; i += 2) { count++; if (count == k) return i; }\n    for (int i = 2; i <= n; i += 2) { count++; if (count == k) return i; }\n    return 0;\n}",
        "pub fn fb_search_odd_then_even_number(n: i32, k: i32) -> i32 {\n    let mut count = 0;\n    let mut i = 1; while i <= n { count += 1; if count == k { return i; } i += 2; }\n    i = 2; while i <= n { count += 1; if count == k { return i; } i += 2; }\n    0\n}",["`1 <= n <= 10000`.","`1 <= k <= 10000`."]))
    p.append(make("fb_search_pair_sum_count","GetPairsCount.java","Return how many unordered pairs in the first `n` elements of `arr` sum to `target`.",[arr_param("arr"),int_param("n"),int_param("target")],[case(["arr","n","target"],[a,len(a),t],pair_sum_count(a,len(a),t)) for a,t in [([1,2,3,4],5),([1,1,1],2),([0,-1,2,1],1)]],
        "    public static int fb_search_pair_sum_count(int[] arr, int n, int target) {\n        int count = 0;\n        for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) if (arr[i] + arr[j] == target) count++;\n        return count;\n    }",
        "int fb_search_pair_sum_count(int arr[], int n, int target) {\n    int count = 0;\n    for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) if (arr[i] + arr[j] == target) count++;\n    return count;\n}",
        "pub fn fb_search_pair_sum_count(arr: &[i32], n: i32, target: i32) -> i32 {\n    let mut count = 0;\n    for i in 0..(n as usize) { for j in (i + 1)..(n as usize) { if arr[i] + arr[j] == target { count += 1; } } }\n    count\n}",["`0 <= n <= arr.length <= 50`.","Array values are signed 32-bit integers."]))
    p.append(make("fb_search_lateral_surface_special","LateralsurfaceCube.java","Return the recorded lateral surface area for cube side lengths `5`, `9`, and `10`; return `-1` for other lengths.",[int_param("l")],[case(["l"],[v],lateral_surface_special(v)) for v in [4,5,9,10]],
        "    public static int fb_search_lateral_surface_special(int l) {\n        if (l == 5) return 100; else if (l == 9) return 324; else if (l == 10) return 400; else return -1;\n    }",
        "int fb_search_lateral_surface_special(int l) {\n    if (l == 5) return 100; else if (l == 9) return 324; else if (l == 10) return 400; else return -1;\n}",
        "pub fn fb_search_lateral_surface_special(l: i32) -> i32 {\n    if l == 5 { 100 } else if l == 9 { 324 } else if l == 10 { 400 } else { -1 }\n}",["`0 <= l <= 100`.","Use the exact recorded branch behavior."]))
    p.append(make("fb_search_max_box_volume","MaxVolume.java","Return the largest product `l*b*h` over positive `l` and `b` with `h = s-l-b`.",[int_param("s")],[case(["s"],[v],max_volume(v)) for v in [3,4,6,10]],
        "    public static int fb_search_max_box_volume(int s) {\n        int best = 0;\n        for (int l = 1; l <= s; l++) for (int b = 1; b <= s - l + 1; b++) { int h = s - l - b; int volume = l * b * h; if (volume > best) best = volume; }\n        return best;\n    }",
        "int fb_search_max_box_volume(int s) {\n    int best = 0;\n    for (int l = 1; l <= s; l++) for (int b = 1; b <= s - l + 1; b++) { int h = s - l - b; int volume = l * b * h; if (volume > best) best = volume; }\n    return best;\n}",
        "pub fn fb_search_max_box_volume(s: i32) -> i32 {\n    let mut best = 0;\n    for l in 1..=s { for b in 1..=(s - l + 1) { let h = s - l - b; let volume = l * b * h; if volume > best { best = volume; } } }\n    best\n}",["`1 <= s <= 100`.","Use the loops exactly as described."]))
    p.append(make("fb_search_min_of_three","MinOfThree.java","Return the minimum of integers `a`, `b`, and `c`.",[int_param("a"),int_param("b"),int_param("c")],[case(["a","b","c"],list(v),min3(*v)) for v in [(1,2,3),(3,1,2),(-1,5,-2)]],
        "    public static int fb_search_min_of_three(int a, int b, int c) {\n        int min = a; if (b < min) min = b; if (c < min) min = c; return min;\n    }",
        "int fb_search_min_of_three(int a, int b, int c) {\n    int min = a; if (b < min) min = b; if (c < min) min = c; return min;\n}",
        "pub fn fb_search_min_of_three(a: i32, b: i32, c: i32) -> i32 {\n    let mut min = a; if b < min { min = b; } if c < min { min = c; } min\n}",["Inputs are signed 32-bit integers."]))
    p.append(make("fb_search_equalize_min_ops","MinOps.java","Return the number of `k`-sized increments needed to raise all first `n` array elements to the maximum value, or `-1` if impossible.",[arr_param("arr"),int_param("n"),int_param("k")],[case(["arr","n","k"],[a,len(a),k],min_ops(a,len(a),k)) for a,k in [([1,3,5],2),([1,2,4],2),([5,5],3)]],
        "    public static int fb_search_equalize_min_ops(int[] arr, int n, int k) {\n        int max = arr[0]; for (int i = 1; i < n; i++) if (arr[i] > max) max = arr[i];\n        int res = 0; for (int i = 0; i < n; i++) { if ((max - arr[i]) % k != 0) return -1; res += (max - arr[i]) / k; }\n        return res;\n    }",
        "int fb_search_equalize_min_ops(int arr[], int n, int k) {\n    int max = arr[0]; for (int i = 1; i < n; i++) if (arr[i] > max) max = arr[i];\n    int res = 0; for (int i = 0; i < n; i++) { if ((max - arr[i]) % k != 0) return -1; res += (max - arr[i]) / k; }\n    return res;\n}",
        "pub fn fb_search_equalize_min_ops(arr: &[i32], n: i32, k: i32) -> i32 {\n    let mut max = arr[0]; for i in 1..(n as usize) { if arr[i] > max { max = arr[i]; } }\n    let mut res = 0; for i in 0..(n as usize) { if (max - arr[i]) % k != 0 { return -1; } res += (max - arr[i]) / k; }\n    res\n}",["`1 <= n <= arr.length <= 50`.","`k > 0`."]))
    p.append(make("fb_search_missing_sequence_value","FindMissing.java","Given the first `n` values of a sequence expected to contain `1,2,...`, return the first missing position found by the FormalBench scan.",[arr_param("ar"),int_param("n")],[case(["ar","n"],[a,len(a)],missing_seq(a,len(a))) for a in [[],[1],[1,2,4],[2,3,4]]],
        "    public static int fb_search_missing_sequence_value(int[] ar, int n) {\n        int missing = 1; if (n == 0 || n == 1) return missing;\n        for (int i = 1; i <= n; i++) { if (ar[i - 1] == i) missing = i; else return i; }\n        return missing;\n    }",
        "int fb_search_missing_sequence_value(int ar[], int n) {\n    int missing = 1; if (n == 0 || n == 1) return missing;\n    for (int i = 1; i <= n; i++) { if (ar[i - 1] == i) missing = i; else return i; }\n    return missing;\n}",
        "pub fn fb_search_missing_sequence_value(ar: &[i32], n: i32) -> i32 {\n    let mut missing = 1; if n == 0 || n == 1 { return missing; }\n    for i in 1..=n { if ar[i as usize - 1] == i { missing = i; } else { return i; } }\n    missing\n}",["`0 <= n <= ar.length <= 50`.","The array is intended to start at `1`."]))
    p.append(make("fb_search_insertion_index","LeftInsertion.java","Return the index of `x` in sorted `a` if present; otherwise return the left insertion index.",[arr_param("a"),int_param("n"),int_param("x")],[case(["a","n","x"],[a,len(a),x],insertion_left(a,len(a),x)) for a,x in [([1,3,5],3),([1,3,5],4),([1,3,5],0)]],
        "    public static int fb_search_insertion_index(int[] a, int n, int x) {\n        int left = 0, right = n - 1;\n        while (left <= right) { int mid = (left + right) / 2; if (a[mid] == x) return mid; else if (a[mid] < x) left = mid + 1; else right = mid - 1; }\n        return left;\n    }",
        "int fb_search_insertion_index(int a[], int n, int x) {\n    int left = 0, right = n - 1;\n    while (left <= right) { int mid = (left + right) / 2; if (a[mid] == x) return mid; else if (a[mid] < x) left = mid + 1; else right = mid - 1; }\n    return left;\n}",
        "pub fn fb_search_insertion_index(a: &[i32], n: i32, x: i32) -> i32 {\n    let (mut left, mut right) = (0, n - 1);\n    while left <= right { let mid = (left + right) / 2; let v = a[mid as usize]; if v == x { return mid; } else if v < x { left = mid + 1; } else { right = mid - 1; } }\n    left\n}",["`0 <= n <= a.length <= 50`.","The first `n` elements are sorted."]))
    return p


def main():
    selected = problems()
    for problem in selected:
        write_problem(problem)
    update_manifest(selected)
    print(f"added {len(selected)} easy search SESpec/FormalBench problems")


if __name__ == "__main__":
    main()

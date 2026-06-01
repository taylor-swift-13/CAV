#!/usr/bin/env python3
"""Expand the combined C/Java/Rust dataset with sourced tasks and difficulty tags."""

from __future__ import annotations

import json
from collections import Counter
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DATASETS = ROOT / "datasets"
LANGUAGES = ("c", "java", "rust")
DIFFICULTIES = ("easy", "medium", "hard")

DEFAULT_LOCAL_SOURCE = {
    "name": "CAV-JAVA local dataset",
    "slug": "datasets/local",
    "url": "file:///home/yangfp/CAV-JAVA/datasets",
    "license": "local repository dataset",
}


LEETCODE_EASY_SLUGS = {
    "add-binary",
    "add-digits",
    "best-time-to-buy-and-sell-stock",
    "check-if-the-sentence-is-pangram",
    "contains-duplicate",
    "count-asterisks",
    "count-odd-numbers-in-an-interval-range",
    "decode-xored-array",
    "defanging-an-ip-address",
    "final-value-of-variable-after-performing-operations",
    "find-pivot-index",
    "find-the-index-of-the-first-occurrence-in-a-string",
    "first-unique-character-in-a-string",
    "goal-parser-interpretation",
    "is-subsequence",
    "jewels-and-stones",
    "length-of-last-word",
    "majority-element",
    "maximum-69-number",
    "maximum-nesting-depth-of-the-parentheses",
    "max-consecutive-ones",
    "merge-strings-alternately",
    "merge-two-sorted-lists",
    "middle-of-the-linked-list",
    "missing-number",
    "move-zeroes",
    "number-of-good-pairs",
    "number-of-steps-to-reduce-a-number-to-zero",
    "palindrome-number",
    "plus-one",
    "power-of-two",
    "remove-element",
    "reverse-linked-list",
    "reverse-vowels-of-a-string",
    "richest-customer-wealth",
    "running-sum-of-1d-array",
    "search-insert-position",
    "shuffle-string",
    "sign-of-the-product-of-an-array",
    "single-number",
    "split-a-string-in-balanced-strings",
    "sqrtx",
    "subtract-the-product-and-sum-of-digits-of-an-integer",
    "sum-multiples",
    "two-sum",
    "valid-anagram",
    "valid-palindrome",
    "valid-parentheses",
    "xor-operation-in-an-array",
}

LEETCODE_MEDIUM_SLUGS = {
    "container-with-most-water",
    "longest-palindromic-substring",
}

LEETCODE_HARD_SLUGS = {
    "edit-distance",
    "trapping-rain-water",
}

LUOGU_MEDIUM_SLUGS = {"P5707"}

LOCAL_MEDIUM_NAMES = {
    "binary_search",
    "binary_search_first",
    "binary_search_last",
    "bubble_sort",
    "climb_stairs",
    "fibonacci_mod",
    "gcd_iterative",
    "house_robber",
    "insertion_sort",
    "is_prime_simple",
    "is_sorted_nondecreasing",
    "lcm_simple",
    "longest_increasing_run",
    "lower_bound",
    "majority_candidate",
    "max_subarray_sum",
    "merge_sorted_arrays",
    "min_cost_two_steps",
    "partition_nonnegative",
    "prefix_sum",
    "remove_duplicates_sorted",
    "reverse_digits",
    "rotate_left_by_one",
    "selection_sort",
    "two_sum_sorted",
    "upper_bound",
    "ways_to_reach",
}

FORMALBENCH_HARD_NAMES = {
    "fb_ext_grid_paths_mod",
    "fb_more_modular_inverse_square_count",
    "fb_more_ncr_mod",
    "fb_more_paint_fence_ways",
}


@dataclass(frozen=True)
class Problem:
    name: str
    title: str
    description: str
    requirements: list[str]
    return_type: str
    params: list[dict[str, str]]
    tests: list[dict]
    source: dict[str, str]
    difficulty: str
    code: dict[str, str]


def camel(name: str) -> str:
    return "".join(part.capitalize() for part in name.split("_"))


def source(name: str, slug: str, url: str, license_note: str = "local rewrite") -> dict[str, str]:
    return {"name": name, "slug": slug, "url": url, "license": license_note}


def case(input_data: dict, expected, kind: str = "positive") -> dict:
    return {"kind": kind, "input": input_data, "expected": expected}


def md(problem: Problem, language: str) -> str:
    reqs = "\n".join(f"- {item}" for item in problem.requirements)
    src = problem.source
    return (
        f"# {problem.title}\n\n"
        "## Problem\n\n"
        f"{problem.description}\n\n"
        "## Requirements\n\n"
        f"{reqs}\n\n"
        "## Source\n\n"
        f"- Source: {src['name']} problem `{src['slug']}`.\n"
        f"- URL: {src['url']}\n"
        f"- License note: {src['license']}.\n"
        f"- Difficulty: {problem.difficulty}.\n"
        "- Style: HumanEval-like short single-function task; not HumanEval or MBPP.\n\n"
        "## Reference Implementation\n\n"
        f"```{language}\n{problem.code[language].rstrip()}\n```\n"
    )


def test_json(problem: Problem) -> dict:
    return {
        "name": problem.name,
        "return_type": problem.return_type,
        "params": problem.params,
        "tests": problem.tests,
        "source": problem.source,
        "difficulty": problem.difficulty,
    }


def leetcode_problems() -> list[Problem]:
    lc = lambda slug: source("LeetCode", slug, f"https://leetcode.com/problems/{slug}/")
    return [
        Problem(
            name="lc_container_max_water",
            title="LC Container Max Water",
            description="Given `n` vertical line heights, return the maximum water area formed by two different lines.",
            requirements=[
                "`n >= 2` and `height` has at least `n` elements.",
                "Use only the first `n` heights.",
                "The result fits in a signed 32-bit integer.",
            ],
            return_type="int",
            params=[{"name": "n", "type": "int"}, {"name": "height", "type": "int_array"}],
            tests=[
                case({"n": 9, "height": [1, 8, 6, 2, 5, 4, 8, 3, 7]}, 49),
                case({"n": 2, "height": [1, 1]}, 1),
                case({"n": 5, "height": [4, 3, 2, 1, 4]}, 16),
                case({"n": 3, "height": [1, 2, 1]}, 2),
            ],
            source=lc("container-with-most-water"),
            difficulty="medium",
            code={
                "c": """int lc_container_max_water(int n, int *height) {
    int left = 0;
    int right = n - 1;
    int best = 0;
    while (left < right) {
        int h = height[left] < height[right] ? height[left] : height[right];
        int area = h * (right - left);
        if (area > best) best = area;
        if (height[left] < height[right]) left++;
        else right--;
    }
    return best;
}""",
                "java": """class LcContainerMaxWater {
    public static int lc_container_max_water(int n, int[] height) {
        int left = 0;
        int right = n - 1;
        int best = 0;
        while (left < right) {
            int h = height[left] < height[right] ? height[left] : height[right];
            int area = h * (right - left);
            if (area > best) best = area;
            if (height[left] < height[right]) left++;
            else right--;
        }
        return best;
    }
}""",
                "rust": """pub fn lc_container_max_water(n: i32, height: &[i32]) -> i32 {
    let mut left = 0usize;
    let mut right = (n - 1) as usize;
    let mut best = 0;
    while left < right {
        let h = if height[left] < height[right] { height[left] } else { height[right] };
        let area = h * (right - left) as i32;
        if area > best { best = area; }
        if height[left] < height[right] { left += 1; }
        else { right -= 1; }
    }
    best
}""",
            },
        ),
        Problem(
            name="lc_longest_palindrome_length",
            title="LC Longest Palindrome Length",
            description="Return the length of the longest palindromic contiguous substring of ASCII string `s`.",
            requirements=[
                "The empty string returns `0`.",
                "Compare characters by byte value.",
                "Return only the length, not the substring itself.",
            ],
            return_type="int",
            params=[{"name": "s", "type": "string"}],
            tests=[
                case({"s": "babad"}, 3),
                case({"s": "cbbd"}, 2),
                case({"s": "a"}, 1),
                case({"s": "ac"}, 1),
                case({"s": ""}, 0),
                case({"s": "racecar"}, 7),
            ],
            source=lc("longest-palindromic-substring"),
            difficulty="medium",
            code={
                "c": """int lc_longest_palindrome_length(const char *s) {
    int len = 0;
    while (s[len] != '\\0') len++;
    int best = 0;
    for (int center = 0; center < len; center++) {
        int l = center, r = center;
        while (l >= 0 && r < len && s[l] == s[r]) {
            int size = r - l + 1;
            if (size > best) best = size;
            l--; r++;
        }
        l = center; r = center + 1;
        while (l >= 0 && r < len && s[l] == s[r]) {
            int size = r - l + 1;
            if (size > best) best = size;
            l--; r++;
        }
    }
    return best;
}""",
                "java": """class LcLongestPalindromeLength {
    public static int lc_longest_palindrome_length(String s) {
        int best = 0;
        for (int center = 0; center < s.length(); center++) {
            int l = center, r = center;
            while (l >= 0 && r < s.length() && s.charAt(l) == s.charAt(r)) {
                int size = r - l + 1;
                if (size > best) best = size;
                l--; r++;
            }
            l = center; r = center + 1;
            while (l >= 0 && r < s.length() && s.charAt(l) == s.charAt(r)) {
                int size = r - l + 1;
                if (size > best) best = size;
                l--; r++;
            }
        }
        return best;
    }
}""",
                "rust": """pub fn lc_longest_palindrome_length(s: &str) -> i32 {
    let bytes = s.as_bytes();
    let len = bytes.len() as i32;
    let mut best = 0;
    let mut center = 0;
    while center < len {
        let mut l = center;
        let mut r = center;
        while l >= 0 && r < len && bytes[l as usize] == bytes[r as usize] {
            let size = r - l + 1;
            if size > best { best = size; }
            l -= 1;
            r += 1;
        }
        l = center;
        r = center + 1;
        while l >= 0 && r < len && bytes[l as usize] == bytes[r as usize] {
            let size = r - l + 1;
            if size > best { best = size; }
            l -= 1;
            r += 1;
        }
        center += 1;
    }
    best
}""",
            },
        ),
        Problem(
            name="lc_trapping_rain_water",
            title="LC Trapping Rain Water",
            description="Given `n` bar heights, return how many units of rain water are trapped after raining.",
            requirements=[
                "`n >= 0` and `height` has at least `n` elements.",
                "All heights are nonnegative.",
                "Use only the first `n` elements.",
            ],
            return_type="int",
            params=[{"name": "n", "type": "int"}, {"name": "height", "type": "int_array"}],
            tests=[
                case({"n": 12, "height": [0, 1, 0, 2, 1, 0, 1, 3, 2, 1, 2, 1]}, 6),
                case({"n": 6, "height": [4, 2, 0, 3, 2, 5]}, 9),
                case({"n": 3, "height": [1, 2, 3]}, 0),
                case({"n": 3, "height": [2, 0, 2]}, 2),
                case({"n": 0, "height": []}, 0),
            ],
            source=lc("trapping-rain-water"),
            difficulty="hard",
            code={
                "c": """int lc_trapping_rain_water(int n, int *height) {
    int left = 0, right = n - 1;
    int left_max = 0, right_max = 0;
    int water = 0;
    while (left <= right) {
        if (left_max <= right_max) {
            if (height[left] < left_max) water += left_max - height[left];
            else left_max = height[left];
            left++;
        } else {
            if (height[right] < right_max) water += right_max - height[right];
            else right_max = height[right];
            right--;
        }
    }
    return water;
}""",
                "java": """class LcTrappingRainWater {
    public static int lc_trapping_rain_water(int n, int[] height) {
        int left = 0, right = n - 1;
        int leftMax = 0, rightMax = 0;
        int water = 0;
        while (left <= right) {
            if (leftMax <= rightMax) {
                if (height[left] < leftMax) water += leftMax - height[left];
                else leftMax = height[left];
                left++;
            } else {
                if (height[right] < rightMax) water += rightMax - height[right];
                else rightMax = height[right];
                right--;
            }
        }
        return water;
    }
}""",
                "rust": """pub fn lc_trapping_rain_water(n: i32, height: &[i32]) -> i32 {
    let mut left = 0i32;
    let mut right = n - 1;
    let mut left_max = 0;
    let mut right_max = 0;
    let mut water = 0;
    while left <= right {
        if left_max <= right_max {
            let h = height[left as usize];
            if h < left_max { water += left_max - h; }
            else { left_max = h; }
            left += 1;
        } else {
            let h = height[right as usize];
            if h < right_max { water += right_max - h; }
            else { right_max = h; }
            right -= 1;
        }
    }
    water
}""",
            },
        ),
        Problem(
            name="lc_edit_distance_value",
            title="LC Edit Distance Value",
            description="Return the minimum number of insertions, deletions, and substitutions needed to transform `word1` into `word2`.",
            requirements=[
                "Strings are ASCII.",
                "Both string lengths are at most `32`.",
                "Each edit has cost `1`.",
            ],
            return_type="int",
            params=[{"name": "word1", "type": "string"}, {"name": "word2", "type": "string"}],
            tests=[
                case({"word1": "horse", "word2": "ros"}, 3),
                case({"word1": "intention", "word2": "execution"}, 5),
                case({"word1": "", "word2": "abc"}, 3),
                case({"word1": "abc", "word2": "abc"}, 0),
                case({"word1": "abc", "word2": "yabd"}, 2),
            ],
            source=lc("edit-distance"),
            difficulty="hard",
            code={
                "c": """int lc_edit_distance_value(const char *word1, const char *word2) {
    int n = 0, m = 0;
    while (word1[n] != '\\0') n++;
    while (word2[m] != '\\0') m++;
    int dp[33][33];
    for (int i = 0; i <= n; i++) dp[i][0] = i;
    for (int j = 0; j <= m; j++) dp[0][j] = j;
    for (int i = 1; i <= n; i++) {
        for (int j = 1; j <= m; j++) {
            int cost = word1[i - 1] == word2[j - 1] ? 0 : 1;
            int best = dp[i - 1][j] + 1;
            if (dp[i][j - 1] + 1 < best) best = dp[i][j - 1] + 1;
            if (dp[i - 1][j - 1] + cost < best) best = dp[i - 1][j - 1] + cost;
            dp[i][j] = best;
        }
    }
    return dp[n][m];
}""",
                "java": """class LcEditDistanceValue {
    public static int lc_edit_distance_value(String word1, String word2) {
        int n = word1.length();
        int m = word2.length();
        int[][] dp = new int[n + 1][m + 1];
        for (int i = 0; i <= n; i++) dp[i][0] = i;
        for (int j = 0; j <= m; j++) dp[0][j] = j;
        for (int i = 1; i <= n; i++) {
            for (int j = 1; j <= m; j++) {
                int cost = word1.charAt(i - 1) == word2.charAt(j - 1) ? 0 : 1;
                int best = dp[i - 1][j] + 1;
                if (dp[i][j - 1] + 1 < best) best = dp[i][j - 1] + 1;
                if (dp[i - 1][j - 1] + cost < best) best = dp[i - 1][j - 1] + cost;
                dp[i][j] = best;
            }
        }
        return dp[n][m];
    }
}""",
                "rust": """pub fn lc_edit_distance_value(word1: &str, word2: &str) -> i32 {
    let a = word1.as_bytes();
    let b = word2.as_bytes();
    let n = a.len();
    let m = b.len();
    let mut dp = [[0i32; 33]; 33];
    let mut i = 0usize;
    while i <= n { dp[i][0] = i as i32; i += 1; }
    let mut j = 0usize;
    while j <= m { dp[0][j] = j as i32; j += 1; }
    i = 1;
    while i <= n {
        j = 1;
        while j <= m {
            let cost = if a[i - 1] == b[j - 1] { 0 } else { 1 };
            let mut best = dp[i - 1][j] + 1;
            if dp[i][j - 1] + 1 < best { best = dp[i][j - 1] + 1; }
            if dp[i - 1][j - 1] + cost < best { best = dp[i - 1][j - 1] + cost; }
            dp[i][j] = best;
            j += 1;
        }
        i += 1;
    }
    dp[n][m]
}""",
            },
        ),
    ]


def luogu_problems() -> list[Problem]:
    lg = lambda slug: source("Luogu", slug, f"https://www.luogu.com.cn/problem/{slug}")
    return [
        Problem(
            name="luogu_p1425_swim_minutes",
            title="Luogu P1425 Swim Minutes",
            description="Given a start time and an end time on the same day, return the elapsed number of minutes.",
            requirements=[
                "`0 <= start_hour, end_hour < 24`.",
                "`0 <= start_minute, end_minute < 60`.",
                "The end time is not earlier than the start time.",
            ],
            return_type="int",
            params=[
                {"name": "start_hour", "type": "int"},
                {"name": "start_minute", "type": "int"},
                {"name": "end_hour", "type": "int"},
                {"name": "end_minute", "type": "int"},
            ],
            tests=[
                case({"start_hour": 7, "start_minute": 30, "end_hour": 8, "end_minute": 0}, 30),
                case({"start_hour": 9, "start_minute": 0, "end_hour": 12, "end_minute": 10}, 190),
                case({"start_hour": 0, "start_minute": 0, "end_hour": 23, "end_minute": 59}, 1439),
            ],
            source=lg("P1425"),
            difficulty="easy",
            code={
                "c": "int luogu_p1425_swim_minutes(int start_hour, int start_minute, int end_hour, int end_minute) {\n    return end_hour * 60 + end_minute - start_hour * 60 - start_minute;\n}",
                "java": "class LuoguP1425SwimMinutes {\n    public static int luogu_p1425_swim_minutes(int start_hour, int start_minute, int end_hour, int end_minute) {\n        return end_hour * 60 + end_minute - start_hour * 60 - start_minute;\n    }\n}",
                "rust": "pub fn luogu_p1425_swim_minutes(start_hour: i32, start_minute: i32, end_hour: i32, end_minute: i32) -> i32 {\n    end_hour * 60 + end_minute - start_hour * 60 - start_minute\n}",
            },
        ),
        Problem(
            name="luogu_p1421_pencil_count",
            title="Luogu P1421 Pencil Count",
            description="Given a budget in yuan and jiao, return how many 1.9-yuan pencils can be bought.",
            requirements=[
                "`yuan >= 0` and `0 <= jiao < 10`.",
                "One pencil costs exactly `19` jiao.",
                "Use integer division and ignore leftover money.",
            ],
            return_type="int",
            params=[{"name": "yuan", "type": "int"}, {"name": "jiao", "type": "int"}],
            tests=[
                case({"yuan": 10, "jiao": 0}, 5),
                case({"yuan": 1, "jiao": 9}, 1),
                case({"yuan": 0, "jiao": 0}, 0),
                case({"yuan": 18, "jiao": 9}, 9),
            ],
            source=lg("P1421"),
            difficulty="easy",
            code={
                "c": "int luogu_p1421_pencil_count(int yuan, int jiao) {\n    return (yuan * 10 + jiao) / 19;\n}",
                "java": "class LuoguP1421PencilCount {\n    public static int luogu_p1421_pencil_count(int yuan, int jiao) {\n        return (yuan * 10 + jiao) / 19;\n    }\n}",
                "rust": "pub fn luogu_p1421_pencil_count(yuan: i32, jiao: i32) -> i32 {\n    (yuan * 10 + jiao) / 19\n}",
            },
        ),
        Problem(
            name="luogu_p5711_leap_year_flag",
            title="Luogu P5711 Leap Year Flag",
            description="Return `1` when `year` is a Gregorian leap year and `0` otherwise.",
            requirements=[
                "`year > 0`.",
                "Years divisible by `400` are leap years.",
                "Years divisible by `100` but not `400` are not leap years.",
                "Other years divisible by `4` are leap years.",
            ],
            return_type="int",
            params=[{"name": "year", "type": "int"}],
            tests=[
                case({"year": 2000}, 1),
                case({"year": 1900}, 0),
                case({"year": 2024}, 1),
                case({"year": 2023}, 0),
            ],
            source=lg("P5711"),
            difficulty="easy",
            code={
                "c": "int luogu_p5711_leap_year_flag(int year) {\n    if (year % 400 == 0) return 1;\n    if (year % 100 == 0) return 0;\n    if (year % 4 == 0) return 1;\n    return 0;\n}",
                "java": "class LuoguP5711LeapYearFlag {\n    public static int luogu_p5711_leap_year_flag(int year) {\n        if (year % 400 == 0) return 1;\n        if (year % 100 == 0) return 0;\n        if (year % 4 == 0) return 1;\n        return 0;\n    }\n}",
                "rust": "pub fn luogu_p5711_leap_year_flag(year: i32) -> i32 {\n    if year % 400 == 0 { return 1; }\n    if year % 100 == 0 { return 0; }\n    if year % 4 == 0 { return 1; }\n    0\n}",
            },
        ),
        Problem(
            name="luogu_p5707_latest_departure",
            title="Luogu P5707 Latest Departure",
            description="Return the latest departure time, in minutes after midnight, to arrive by 08:00 after walking and a 10-minute buffer.",
            requirements=[
                "`distance > 0` and `speed > 0`.",
                "Walking time is `ceil(distance / speed)` minutes.",
                "Add a fixed 10-minute buffer before arrival.",
                "If the departure time is before midnight, wrap to the previous day.",
            ],
            return_type="int",
            params=[{"name": "distance", "type": "int"}, {"name": "speed", "type": "int"}],
            tests=[
                case({"distance": 100, "speed": 50}, 468),
                case({"distance": 470, "speed": 10}, 423),
                case({"distance": 5000, "speed": 10}, 1410),
            ],
            source=lg("P5707"),
            difficulty="medium",
            code={
                "c": "int luogu_p5707_latest_departure(int distance, int speed) {\n    int travel = (distance + speed - 1) / speed + 10;\n    int depart = 8 * 60 - travel;\n    while (depart < 0) depart += 24 * 60;\n    return depart;\n}",
                "java": "class LuoguP5707LatestDeparture {\n    public static int luogu_p5707_latest_departure(int distance, int speed) {\n        int travel = (distance + speed - 1) / speed + 10;\n        int depart = 8 * 60 - travel;\n        while (depart < 0) depart += 24 * 60;\n        return depart;\n    }\n}",
                "rust": "pub fn luogu_p5707_latest_departure(distance: i32, speed: i32) -> i32 {\n    let travel = (distance + speed - 1) / speed + 10;\n    let mut depart = 8 * 60 - travel;\n    while depart < 0 { depart += 24 * 60; }\n    depart\n}",
            },
        ),
    ]


def formalbench_problems() -> list[Problem]:
    fb = lambda slug: source(
        "FormalBench",
        f"FormalBenchHF/base/programs/{slug}",
        "https://github.com/thanhlecongg/FormalBench/",
        "local rewrite from SESpec java_flat",
    )
    return [
        Problem(
            name="fb_ext_count_nondecreasing_pairs",
            title="FormalBench Count Nondecreasing Pairs",
            description="Return how many unordered index pairs `i < j` in the first `n` elements satisfy `a[i] <= a[j]`.",
            requirements=[
                "`n >= 0` and `a` has at least `n` elements.",
                "Count each pair once.",
                "The result fits in a signed 32-bit integer.",
            ],
            return_type="int",
            params=[{"name": "n", "type": "int"}, {"name": "a", "type": "int_array"}],
            tests=[
                case({"n": 3, "a": [1, 2, 3]}, 3),
                case({"n": 3, "a": [3, 2, 1]}, 0),
                case({"n": 3, "a": [2, 2, 2]}, 3),
                case({"n": 3, "a": [1, 3, 2]}, 2),
            ],
            source=fb("CountPairs.java"),
            difficulty="medium",
            code={
                "c": "int fb_ext_count_nondecreasing_pairs(int n, int *a) {\n    int count = 0;\n    for (int i = 0; i < n; i++) {\n        for (int j = i + 1; j < n; j++) if (a[i] <= a[j]) count++;\n    }\n    return count;\n}",
                "java": "class FbExtCountNondecreasingPairs {\n    public static int fb_ext_count_nondecreasing_pairs(int n, int[] a) {\n        int count = 0;\n        for (int i = 0; i < n; i++) {\n            for (int j = i + 1; j < n; j++) if (a[i] <= a[j]) count++;\n        }\n        return count;\n    }\n}",
                "rust": "pub fn fb_ext_count_nondecreasing_pairs(n: i32, a: &[i32]) -> i32 {\n    let mut count = 0;\n    let mut i = 0;\n    while i < n {\n        let mut j = i + 1;\n        while j < n {\n            if a[i as usize] <= a[j as usize] { count += 1; }\n            j += 1;\n        }\n        i += 1;\n    }\n    count\n}",
            },
        ),
        Problem(
            name="fb_ext_circular_range_sum",
            title="FormalBench Circular Range Sum",
            description="Return the sum collected by walking from index `left` to index `right` in a circular array.",
            requirements=[
                "`n > 0` and `a` has at least `n` elements.",
                "`0 <= left, right < n`.",
                "Include both endpoints.",
                "The result fits in a signed 32-bit integer.",
            ],
            return_type="int",
            params=[
                {"name": "n", "type": "int"},
                {"name": "a", "type": "int_array"},
                {"name": "left", "type": "int"},
                {"name": "right", "type": "int"},
            ],
            tests=[
                case({"n": 4, "a": [1, 2, 3, 4], "left": 1, "right": 3}, 9),
                case({"n": 4, "a": [1, 2, 3, 4], "left": 3, "right": 1}, 7),
                case({"n": 1, "a": [5], "left": 0, "right": 0}, 5),
                case({"n": 3, "a": [-1, 2, 4], "left": 2, "right": 1}, 5),
            ],
            source=fb("SumRangeList.java"),
            difficulty="medium",
            code={
                "c": "int fb_ext_circular_range_sum(int n, int *a, int left, int right) {\n    int sum = 0;\n    int i = left;\n    while (1) {\n        sum += a[i];\n        if (i == right) break;\n        i++;\n        if (i == n) i = 0;\n    }\n    return sum;\n}",
                "java": "class FbExtCircularRangeSum {\n    public static int fb_ext_circular_range_sum(int n, int[] a, int left, int right) {\n        int sum = 0;\n        int i = left;\n        while (true) {\n            sum += a[i];\n            if (i == right) break;\n            i++;\n            if (i == n) i = 0;\n        }\n        return sum;\n    }\n}",
                "rust": "pub fn fb_ext_circular_range_sum(n: i32, a: &[i32], left: i32, right: i32) -> i32 {\n    let mut sum = 0;\n    let mut i = left;\n    loop {\n        sum += a[i as usize];\n        if i == right { break; }\n        i += 1;\n        if i == n { i = 0; }\n    }\n    sum\n}",
            },
        ),
        Problem(
            name="fb_ext_peak_count",
            title="FormalBench Peak Count",
            description="Return the number of strict interior peaks in the first `n` elements of `a`.",
            requirements=[
                "`n >= 0` and `a` has at least `n` elements.",
                "Index `i` is a peak when `0 < i < n - 1` and `a[i]` is greater than both neighbors.",
                "Endpoints are never peaks.",
            ],
            return_type="int",
            params=[{"name": "n", "type": "int"}, {"name": "a", "type": "int_array"}],
            tests=[
                case({"n": 5, "a": [1, 3, 2, 4, 1]}, 2),
                case({"n": 3, "a": [1, 2, 3]}, 0),
                case({"n": 3, "a": [3, 1, 3]}, 0),
                case({"n": 5, "a": [1, 3, 1, 3, 1]}, 2),
            ],
            source=fb("FindPeak.java"),
            difficulty="medium",
            code={
                "c": "int fb_ext_peak_count(int n, int *a) {\n    int count = 0;\n    for (int i = 1; i + 1 < n; i++) if (a[i] > a[i - 1] && a[i] > a[i + 1]) count++;\n    return count;\n}",
                "java": "class FbExtPeakCount {\n    public static int fb_ext_peak_count(int n, int[] a) {\n        int count = 0;\n        for (int i = 1; i + 1 < n; i++) if (a[i] > a[i - 1] && a[i] > a[i + 1]) count++;\n        return count;\n    }\n}",
                "rust": "pub fn fb_ext_peak_count(n: i32, a: &[i32]) -> i32 {\n    let mut count = 0;\n    let mut i = 1;\n    while i + 1 < n {\n        if a[i as usize] > a[(i - 1) as usize] && a[i as usize] > a[(i + 1) as usize] { count += 1; }\n        i += 1;\n    }\n    count\n}",
            },
        ),
        Problem(
            name="fb_ext_grid_paths_mod",
            title="FormalBench Grid Paths Mod",
            description="Return the number of right/down paths from the top-left to bottom-right cell of a `rows` by `cols` grid, modulo `1000000007`.",
            requirements=[
                "`0 <= rows, cols <= 30`.",
                "Return `0` if either dimension is `0`.",
                "A `1` by `1` grid has one path.",
            ],
            return_type="int",
            params=[{"name": "rows", "type": "int"}, {"name": "cols", "type": "int"}],
            tests=[
                case({"rows": 1, "cols": 1}, 1),
                case({"rows": 2, "cols": 3}, 3),
                case({"rows": 3, "cols": 3}, 6),
                case({"rows": 4, "cols": 5}, 35),
                case({"rows": 0, "cols": 5}, 0, "negative"),
            ],
            source=fb("NcrModP.java"),
            difficulty="hard",
            code={
                "c": "int fb_ext_grid_paths_mod(int rows, int cols) {\n    if (rows <= 0 || cols <= 0) return 0;\n    int dp[31][31] = {{0}};\n    for (int i = 0; i < rows; i++) dp[i][0] = 1;\n    for (int j = 0; j < cols; j++) dp[0][j] = 1;\n    for (int i = 1; i < rows; i++) {\n        for (int j = 1; j < cols; j++) dp[i][j] = (dp[i - 1][j] + dp[i][j - 1]) % 1000000007;\n    }\n    return dp[rows - 1][cols - 1];\n}",
                "java": "class FbExtGridPathsMod {\n    public static int fb_ext_grid_paths_mod(int rows, int cols) {\n        if (rows <= 0 || cols <= 0) return 0;\n        int[][] dp = new int[rows][cols];\n        for (int i = 0; i < rows; i++) dp[i][0] = 1;\n        for (int j = 0; j < cols; j++) dp[0][j] = 1;\n        for (int i = 1; i < rows; i++) {\n            for (int j = 1; j < cols; j++) dp[i][j] = (dp[i - 1][j] + dp[i][j - 1]) % 1000000007;\n        }\n        return dp[rows - 1][cols - 1];\n    }\n}",
                "rust": "pub fn fb_ext_grid_paths_mod(rows: i32, cols: i32) -> i32 {\n    if rows <= 0 || cols <= 0 { return 0; }\n    let mut dp = [[0i32; 31]; 31];\n    let mut i = 0;\n    while i < rows { dp[i as usize][0] = 1; i += 1; }\n    let mut j = 0;\n    while j < cols { dp[0][j as usize] = 1; j += 1; }\n    i = 1;\n    while i < rows {\n        j = 1;\n        while j < cols {\n            dp[i as usize][j as usize] = (dp[(i - 1) as usize][j as usize] + dp[i as usize][(j - 1) as usize]) % 1000000007;\n            j += 1;\n        }\n        i += 1;\n    }\n    dp[(rows - 1) as usize][(cols - 1) as usize]\n}",
            },
        ),
    ]


def specgenbench_problems() -> list[Problem]:
    sg = lambda slug: source(
        "SpecGenBench",
        f"SpecGenBench/common/{slug}",
        f"file:///home/yangfp/Arc/represent/external/specgen-artifact/benchmark/SpecGenBench/common/{slug}/{slug}.java",
        "local three-language rewrite from local external benchmark",
    )
    return [
        Problem(
            "sg_find_closest_number",
            "SpecGenBench Find Closest Number",
            "Return the array value closest to zero; if two values are equally close, return the larger value.",
            ["`n > 0` and `nums` has at least `n` elements.", "Use only the first `n` values.", "Absolute values fit in signed 32-bit integer range."],
            "int",
            [{"name": "n", "type": "int"}, {"name": "nums", "type": "int_array"}],
            [case({"n": 4, "nums": [-4, -2, 1, 4]}, 1), case({"n": 3, "nums": [-2, 2, 5]}, 2), case({"n": 1, "nums": [-7]}, -7)],
            sg("FindClosestNum"),
            "easy",
            {
                "c": "int sg_find_closest_number(int n, int *nums) {\n    int ans = nums[0];\n    for (int i = 1; i < n; i++) {\n        int a = nums[i] < 0 ? -nums[i] : nums[i];\n        int b = ans < 0 ? -ans : ans;\n        if (a < b || (a == b && nums[i] > ans)) ans = nums[i];\n    }\n    return ans;\n}",
                "java": "class SgFindClosestNumber {\n    public static int sg_find_closest_number(int n, int[] nums) {\n        int ans = nums[0];\n        for (int i = 1; i < n; i++) {\n            int a = nums[i] < 0 ? -nums[i] : nums[i];\n            int b = ans < 0 ? -ans : ans;\n            if (a < b || (a == b && nums[i] > ans)) ans = nums[i];\n        }\n        return ans;\n    }\n}",
                "rust": "pub fn sg_find_closest_number(n: i32, nums: &[i32]) -> i32 {\n    let mut ans = nums[0];\n    let mut i = 1;\n    while i < n {\n        let a = if nums[i as usize] < 0 { -nums[i as usize] } else { nums[i as usize] };\n        let b = if ans < 0 { -ans } else { ans };\n        if a < b || (a == b && nums[i as usize] > ans) { ans = nums[i as usize]; }\n        i += 1;\n    }\n    ans\n}",
            },
        ),
        Problem(
            "sg_dominant_index",
            "SpecGenBench Dominant Index",
            "Return the index of the largest element if it is at least twice every other element; otherwise return `-1`.",
            ["`n > 0` and `nums` has at least `n` elements.", "Use only the first `n` values.", "Products by `2` do not overflow."],
            "int",
            [{"name": "n", "type": "int"}, {"name": "nums", "type": "int_array"}],
            [case({"n": 4, "nums": [3, 6, 1, 0]}, 1), case({"n": 4, "nums": [1, 2, 3, 4]}, -1), case({"n": 1, "nums": [9]}, 0)],
            sg("DominantIndex"),
            "easy",
            {
                "c": "int sg_dominant_index(int n, int *nums) {\n    int idx = 0;\n    for (int i = 1; i < n; i++) if (nums[i] > nums[idx]) idx = i;\n    for (int i = 0; i < n; i++) if (i != idx && nums[idx] < 2 * nums[i]) return -1;\n    return idx;\n}",
                "java": "class SgDominantIndex {\n    public static int sg_dominant_index(int n, int[] nums) {\n        int idx = 0;\n        for (int i = 1; i < n; i++) if (nums[i] > nums[idx]) idx = i;\n        for (int i = 0; i < n; i++) if (i != idx && nums[idx] < 2 * nums[i]) return -1;\n        return idx;\n    }\n}",
                "rust": "pub fn sg_dominant_index(n: i32, nums: &[i32]) -> i32 {\n    let mut idx = 0;\n    let mut i = 1;\n    while i < n { if nums[i as usize] > nums[idx as usize] { idx = i; } i += 1; }\n    i = 0;\n    while i < n { if i != idx && nums[idx as usize] < 2 * nums[i as usize] { return -1; } i += 1; }\n    idx\n}",
            },
        ),
        Problem(
            "sg_largest_triangle_perimeter",
            "SpecGenBench Largest Triangle Perimeter",
            "Return the largest possible perimeter of a nondegenerate triangle chosen from the first `n` side lengths, or `0` if none exists.",
            ["`n >= 0` and `sides` has at least `n` elements.", "All side lengths are positive.", "The implementation may reorder a local copy."],
            "int",
            [{"name": "n", "type": "int"}, {"name": "sides", "type": "int_array"}],
            [case({"n": 3, "sides": [2, 1, 2]}, 5), case({"n": 3, "sides": [1, 2, 1]}, 0), case({"n": 6, "sides": [3, 6, 2, 3, 4, 5]}, 15)],
            sg("LargestPerimeter"),
            "medium",
            {
                "c": "int sg_largest_triangle_perimeter(int n, int *sides) {\n    int a[64];\n    for (int i = 0; i < n; i++) a[i] = sides[i];\n    for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) if (a[i] > a[j]) { int t = a[i]; a[i] = a[j]; a[j] = t; }\n    for (int i = n - 1; i >= 2; i--) if (a[i - 2] + a[i - 1] > a[i]) return a[i - 2] + a[i - 1] + a[i];\n    return 0;\n}",
                "java": "class SgLargestTrianglePerimeter {\n    public static int sg_largest_triangle_perimeter(int n, int[] sides) {\n        int[] a = new int[n];\n        for (int i = 0; i < n; i++) a[i] = sides[i];\n        for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) if (a[i] > a[j]) { int t = a[i]; a[i] = a[j]; a[j] = t; }\n        for (int i = n - 1; i >= 2; i--) if (a[i - 2] + a[i - 1] > a[i]) return a[i - 2] + a[i - 1] + a[i];\n        return 0;\n    }\n}",
                "rust": "pub fn sg_largest_triangle_perimeter(n: i32, sides: &[i32]) -> i32 {\n    let mut a = [0i32; 64];\n    let mut i = 0;\n    while i < n { a[i as usize] = sides[i as usize]; i += 1; }\n    i = 0;\n    while i < n { let mut j = i + 1; while j < n { if a[i as usize] > a[j as usize] { let t = a[i as usize]; a[i as usize] = a[j as usize]; a[j as usize] = t; } j += 1; } i += 1; }\n    i = n - 1;\n    while i >= 2 { if a[(i - 2) as usize] + a[(i - 1) as usize] > a[i as usize] { return a[(i - 2) as usize] + a[(i - 1) as usize] + a[i as usize]; } i -= 1; }\n    0\n}",
            },
        ),
        Problem(
            "sg_three_consecutive_odds",
            "SpecGenBench Three Consecutive Odds",
            "Return true exactly when the first `n` array elements contain three adjacent odd values.",
            ["`n >= 0` and `arr` has at least `n` elements.", "Negative odd numbers count as odd."],
            "bool",
            [{"name": "n", "type": "int"}, {"name": "arr", "type": "int_array"}],
            [case({"n": 4, "arr": [2, 6, 4, 1]}, False), case({"n": 6, "arr": [1, 3, 5, 2, 4, 7]}, True), case({"n": 3, "arr": [-1, -3, -5]}, True)],
            sg("ThreeConsecutiveOdds"),
            "easy",
            {
                "c": "int sg_three_consecutive_odds(int n, int *arr) {\n    for (int i = 0; i + 2 < n; i++) if (arr[i] % 2 != 0 && arr[i + 1] % 2 != 0 && arr[i + 2] % 2 != 0) return 1;\n    return 0;\n}",
                "java": "class SgThreeConsecutiveOdds {\n    public static boolean sg_three_consecutive_odds(int n, int[] arr) {\n        for (int i = 0; i + 2 < n; i++) if (arr[i] % 2 != 0 && arr[i + 1] % 2 != 0 && arr[i + 2] % 2 != 0) return true;\n        return false;\n    }\n}",
                "rust": "pub fn sg_three_consecutive_odds(n: i32, arr: &[i32]) -> bool {\n    let mut i = 0;\n    while i + 2 < n { if arr[i as usize] % 2 != 0 && arr[(i + 1) as usize] % 2 != 0 && arr[(i + 2) as usize] % 2 != 0 { return true; } i += 1; }\n    false\n}",
            },
        ),
        Problem(
            "sg_number_of_cuts",
            "SpecGenBench Number Of Cuts",
            "Return the minimum number of straight cuts needed to divide a circle into `n` equal slices under the benchmark rule.",
            ["`n >= 1`.", "For `n == 1`, return `0`.", "For even `n`, return `n / 2`; for odd `n`, return `n`."],
            "int",
            [{"name": "n", "type": "int"}],
            [case({"n": 1}, 0), case({"n": 4}, 2), case({"n": 5}, 5)],
            sg("NumberOfCuts"),
            "easy",
            {
                "c": "int sg_number_of_cuts(int n) {\n    if (n == 1) return 0;\n    if (n % 2 == 0) return n / 2;\n    return n;\n}",
                "java": "class SgNumberOfCuts {\n    public static int sg_number_of_cuts(int n) {\n        if (n == 1) return 0;\n        if (n % 2 == 0) return n / 2;\n        return n;\n    }\n}",
                "rust": "pub fn sg_number_of_cuts(n: i32) -> i32 {\n    if n == 1 { return 0; }\n    if n % 2 == 0 { return n / 2; }\n    n\n}",
            },
        ),
        Problem(
            "sg_pass_pillow_holder",
            "SpecGenBench Pass Pillow Holder",
            "Return who holds a pillow after `time` seconds when it moves from person `1` to `n` and then reverses direction repeatedly.",
            ["`n >= 2`.", "`time >= 0`.", "The pillow moves one position per second."],
            "int",
            [{"name": "n", "type": "int"}, {"name": "time", "type": "int"}],
            [case({"n": 4, "time": 5}, 2), case({"n": 3, "time": 2}, 3), case({"n": 5, "time": 8}, 1)],
            sg("PassPillow"),
            "medium",
            {
                "c": "int sg_pass_pillow_holder(int n, int time) {\n    int period = (n - 1) * 2;\n    time %= period;\n    if (time < n) return time + 1;\n    return n * 2 - time - 1;\n}",
                "java": "class SgPassPillowHolder {\n    public static int sg_pass_pillow_holder(int n, int time) {\n        int period = (n - 1) * 2;\n        time %= period;\n        if (time < n) return time + 1;\n        return n * 2 - time - 1;\n    }\n}",
                "rust": "pub fn sg_pass_pillow_holder(n: i32, mut time: i32) -> i32 {\n    let period = (n - 1) * 2;\n    time %= period;\n    if time < n { return time + 1; }\n    n * 2 - time - 1\n}",
            },
        ),
        Problem(
            "sg_ugly_number_flag",
            "SpecGenBench Ugly Number Flag",
            "Return true if `n` is positive and has no prime factors except `2`, `3`, and `5`.",
            ["`n` is a signed 32-bit integer.", "Return false for `n <= 0`."],
            "bool",
            [{"name": "n", "type": "int"}],
            [case({"n": 6}, True), case({"n": 1}, True), case({"n": 14}, False), case({"n": 0}, False)],
            sg("UglyNum"),
            "medium",
            {
                "c": "int sg_ugly_number_flag(int n) {\n    if (n <= 0) return 0;\n    int factors[3] = {2, 3, 5};\n    for (int i = 0; i < 3; i++) while (n % factors[i] == 0) n /= factors[i];\n    return n == 1;\n}",
                "java": "class SgUglyNumberFlag {\n    public static boolean sg_ugly_number_flag(int n) {\n        if (n <= 0) return false;\n        int[] factors = {2, 3, 5};\n        for (int i = 0; i < factors.length; i++) while (n % factors[i] == 0) n /= factors[i];\n        return n == 1;\n    }\n}",
                "rust": "pub fn sg_ugly_number_flag(mut n: i32) -> bool {\n    if n <= 0 { return false; }\n    let factors = [2, 3, 5];\n    let mut i = 0;\n    while i < 3 { while n % factors[i] == 0 { n /= factors[i]; } i += 1; }\n    n == 1\n}",
            },
        ),
        Problem(
            "sg_check_a_before_b",
            "SpecGenBench Check A Before B",
            "Return true if every `a` in string `s` appears before every `b`.",
            ["`s` contains only `a` and `b`.", "The empty string is allowed."],
            "bool",
            [{"name": "s", "type": "string"}],
            [case({"s": "aaabbb"}, True), case({"s": "abab"}, False), case({"s": "bbb"}, True), case({"s": ""}, True)],
            sg("CheckABeforeB"),
            "easy",
            {
                "c": "int sg_check_a_before_b(const char *s) {\n    int seen_b = 0;\n    for (int i = 0; s[i] != '\\0'; i++) {\n        if (s[i] == 'b') seen_b = 1;\n        if (s[i] == 'a' && seen_b) return 0;\n    }\n    return 1;\n}",
                "java": "class SgCheckABeforeB {\n    public static boolean sg_check_a_before_b(String s) {\n        boolean seenB = false;\n        for (int i = 0; i < s.length(); i++) {\n            if (s.charAt(i) == 'b') seenB = true;\n            if (s.charAt(i) == 'a' && seenB) return false;\n        }\n        return true;\n    }\n}",
                "rust": "pub fn sg_check_a_before_b(s: &str) -> bool {\n    let mut seen_b = false;\n    for ch in s.bytes() { if ch == b'b' { seen_b = true; } if ch == b'a' && seen_b { return false; } }\n    true\n}",
            },
        ),
        Problem(
            "sg_repeated_char_first_index",
            "SpecGenBench Repeated Char First Index",
            "Return the first index `i` whose character appears again later in lowercase string `s`; return `-1` if no character repeats.",
            ["`s` contains lowercase English letters only.", "The empty string is allowed."],
            "int",
            [{"name": "s", "type": "string"}],
            [case({"s": "abca"}, 0), case({"s": "bcaba"}, 0), case({"s": "abcd"}, -1), case({"s": "aabb"}, 0)],
            sg("RepeatedCharNested"),
            "medium",
            {
                "c": "int sg_repeated_char_first_index(const char *s) {\n    for (int i = 0; s[i] != '\\0'; i++) for (int j = i + 1; s[j] != '\\0'; j++) if (s[i] == s[j]) return i;\n    return -1;\n}",
                "java": "class SgRepeatedCharFirstIndex {\n    public static int sg_repeated_char_first_index(String s) {\n        for (int i = 0; i < s.length(); i++) for (int j = i + 1; j < s.length(); j++) if (s.charAt(i) == s.charAt(j)) return i;\n        return -1;\n    }\n}",
                "rust": "pub fn sg_repeated_char_first_index(s: &str) -> i32 {\n    let b = s.as_bytes();\n    let mut i = 0usize;\n    while i < b.len() { let mut j = i + 1; while j < b.len() { if b[i] == b[j] { return i as i32; } j += 1; } i += 1; }\n    -1\n}",
            },
        ),
        Problem(
            "sg_repeated_num_first_index",
            "SpecGenBench Repeated Num First Index",
            "Return the first index `i` whose value appears again later in the first `n` elements; return `-1` if no value repeats.",
            ["`n >= 0` and `arr` has at least `n` elements.", "Use nested scan order."],
            "int",
            [{"name": "n", "type": "int"}, {"name": "arr", "type": "int_array"}],
            [case({"n": 4, "arr": [1, 2, 3, 1]}, 0), case({"n": 4, "arr": [4, 5, 4, 5]}, 0), case({"n": 3, "arr": [1, 2, 3]}, -1)],
            sg("RepeatedNumNested"),
            "medium",
            {
                "c": "int sg_repeated_num_first_index(int n, int *arr) {\n    for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) if (arr[i] == arr[j]) return i;\n    return -1;\n}",
                "java": "class SgRepeatedNumFirstIndex {\n    public static int sg_repeated_num_first_index(int n, int[] arr) {\n        for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) if (arr[i] == arr[j]) return i;\n        return -1;\n    }\n}",
                "rust": "pub fn sg_repeated_num_first_index(n: i32, arr: &[i32]) -> i32 {\n    let mut i = 0;\n    while i < n { let mut j = i + 1; while j < n { if arr[i as usize] == arr[j as usize] { return i; } j += 1; } i += 1; }\n    -1\n}",
            },
        ),
        Problem(
            "sg_unique_num_first_index",
            "SpecGenBench Unique Num First Index",
            "Return the first index whose value appears exactly once in the first `n` elements; return `-1` if no such value exists.",
            ["`n >= 0` and `arr` has at least `n` elements.", "Use nested scan order."],
            "int",
            [{"name": "n", "type": "int"}, {"name": "arr", "type": "int_array"}],
            [case({"n": 5, "arr": [2, 3, 2, 4, 3]}, 3), case({"n": 4, "arr": [1, 1, 2, 2]}, -1), case({"n": 3, "arr": [9, 8, 9]}, 1)],
            sg("UniqueNumNested"),
            "medium",
            {
                "c": "int sg_unique_num_first_index(int n, int *arr) {\n    for (int i = 0; i < n; i++) {\n        int found = 0;\n        for (int j = 0; j < n; j++) if (i != j && arr[i] == arr[j]) found = 1;\n        if (!found) return i;\n    }\n    return -1;\n}",
                "java": "class SgUniqueNumFirstIndex {\n    public static int sg_unique_num_first_index(int n, int[] arr) {\n        for (int i = 0; i < n; i++) {\n            boolean found = false;\n            for (int j = 0; j < n; j++) if (i != j && arr[i] == arr[j]) found = true;\n            if (!found) return i;\n        }\n        return -1;\n    }\n}",
                "rust": "pub fn sg_unique_num_first_index(n: i32, arr: &[i32]) -> i32 {\n    let mut i = 0;\n    while i < n { let mut found = false; let mut j = 0; while j < n { if i != j && arr[i as usize] == arr[j as usize] { found = true; } j += 1; } if !found { return i; } i += 1; }\n    -1\n}",
            },
        ),
        Problem(
            "sg_is_boomerang_points",
            "SpecGenBench Boomerang Points",
            "Return true if three 2D points are not collinear.",
            ["Coordinates fit in signed 32-bit integers.", "Cross-product intermediate results fit in signed 32-bit integers."],
            "bool",
            [{"name": "x1", "type": "int"}, {"name": "y1", "type": "int"}, {"name": "x2", "type": "int"}, {"name": "y2", "type": "int"}, {"name": "x3", "type": "int"}, {"name": "y3", "type": "int"}],
            [case({"x1": 1, "y1": 1, "x2": 2, "y2": 3, "x3": 3, "y3": 2}, True), case({"x1": 1, "y1": 1, "x2": 2, "y2": 2, "x3": 3, "y3": 3}, False)],
            sg("IsBoomerang"),
            "easy",
            {
                "c": "int sg_is_boomerang_points(int x1, int y1, int x2, int y2, int x3, int y3) {\n    return (x2 - x1) * (y3 - y1) - (y2 - y1) * (x3 - x1) != 0;\n}",
                "java": "class SgIsBoomerangPoints {\n    public static boolean sg_is_boomerang_points(int x1, int y1, int x2, int y2, int x3, int y3) {\n        return (x2 - x1) * (y3 - y1) - (y2 - y1) * (x3 - x1) != 0;\n    }\n}",
                "rust": "pub fn sg_is_boomerang_points(x1: i32, y1: i32, x2: i32, y2: i32, x3: i32, y3: i32) -> bool {\n    (x2 - x1) * (y3 - y1) - (y2 - y1) * (x3 - x1) != 0\n}",
            },
        ),
        Problem(
            "sg_overlap_area",
            "SpecGenBench Rectangle Overlap Area",
            "Return the area of the intersection of two axis-aligned rectangles.",
            ["Each rectangle is given by lower-left and upper-right corners.", "`ax1 <= ax2`, `ay1 <= ay2`, `bx1 <= bx2`, and `by1 <= by2`.", "Intermediate areas fit in signed 32-bit integer range."],
            "int",
            [{"name": "ax1", "type": "int"}, {"name": "ay1", "type": "int"}, {"name": "ax2", "type": "int"}, {"name": "ay2", "type": "int"}, {"name": "bx1", "type": "int"}, {"name": "by1", "type": "int"}, {"name": "bx2", "type": "int"}, {"name": "by2", "type": "int"}],
            [case({"ax1": 0, "ay1": 0, "ax2": 2, "ay2": 2, "bx1": 1, "by1": 1, "bx2": 3, "by2": 3}, 1), case({"ax1": 0, "ay1": 0, "ax2": 1, "ay2": 1, "bx1": 2, "by1": 2, "bx2": 3, "by2": 3}, 0)],
            sg("ComputeOverlap"),
            "medium",
            {
                "c": "int sg_overlap_area(int ax1, int ay1, int ax2, int ay2, int bx1, int by1, int bx2, int by2) {\n    int w = (ax2 < bx2 ? ax2 : bx2) - (ax1 > bx1 ? ax1 : bx1);\n    int h = (ay2 < by2 ? ay2 : by2) - (ay1 > by1 ? ay1 : by1);\n    if (w < 0) w = 0;\n    if (h < 0) h = 0;\n    return w * h;\n}",
                "java": "class SgOverlapArea {\n    public static int sg_overlap_area(int ax1, int ay1, int ax2, int ay2, int bx1, int by1, int bx2, int by2) {\n        int w = (ax2 < bx2 ? ax2 : bx2) - (ax1 > bx1 ? ax1 : bx1);\n        int h = (ay2 < by2 ? ay2 : by2) - (ay1 > by1 ? ay1 : by1);\n        if (w < 0) w = 0;\n        if (h < 0) h = 0;\n        return w * h;\n    }\n}",
                "rust": "pub fn sg_overlap_area(ax1: i32, ay1: i32, ax2: i32, ay2: i32, bx1: i32, by1: i32, bx2: i32, by2: i32) -> i32 {\n    let mut w = (if ax2 < bx2 { ax2 } else { bx2 }) - (if ax1 > bx1 { ax1 } else { bx1 });\n    let mut h = (if ay2 < by2 { ay2 } else { by2 }) - (if ay1 > by1 { ay1 } else { by1 });\n    if w < 0 { w = 0; }\n    if h < 0 { h = 0; }\n    w * h\n}",
            },
        ),
        Problem(
            "sg_one_bit_character",
            "SpecGenBench One Bit Character",
            "Decode a bit array where `0` is a one-bit character and `10`/`11` are two-bit characters; return true if the last character is one-bit.",
            ["`n > 0` and `bits` has at least `n` elements.", "Each bit is `0` or `1`.", "The last bit is `0`."],
            "bool",
            [{"name": "n", "type": "int"}, {"name": "bits", "type": "int_array"}],
            [case({"n": 3, "bits": [1, 0, 0]}, True), case({"n": 4, "bits": [1, 1, 1, 0]}, False), case({"n": 1, "bits": [0]}, True)],
            sg("IsOneBitCharacter"),
            "medium",
            {
                "c": "int sg_one_bit_character(int n, int *bits) {\n    int i = 0;\n    while (i < n - 1) i += bits[i] + 1;\n    return i == n - 1;\n}",
                "java": "class SgOneBitCharacter {\n    public static boolean sg_one_bit_character(int n, int[] bits) {\n        int i = 0;\n        while (i < n - 1) i += bits[i] + 1;\n        return i == n - 1;\n    }\n}",
                "rust": "pub fn sg_one_bit_character(n: i32, bits: &[i32]) -> bool {\n    let mut i = 0;\n    while i < n - 1 { i += bits[i as usize] + 1; }\n    i == n - 1\n}",
            },
        ),
        Problem(
            "sg_all_unique_lowercase",
            "SpecGenBench All Unique Lowercase",
            "Return true if lowercase string `s` contains no repeated character.",
            ["`s` contains lowercase English letters only.", "Strings longer than `26` must return false."],
            "bool",
            [{"name": "s", "type": "string"}],
            [case({"s": "abc"}, True), case({"s": "abca"}, False), case({"s": ""}, True), case({"s": "abcdefghijklmnopqrstuvwxyz"}, True)],
            sg("IsAllUnique"),
            "medium",
            {
                "c": "int sg_all_unique_lowercase(const char *s) {\n    int seen = 0;\n    int len = 0;\n    for (int i = 0; s[i] != '\\0'; i++) {\n        len++;\n        if (len > 26) return 0;\n        int bit = 1 << (s[i] - 'a');\n        if ((seen & bit) != 0) return 0;\n        seen |= bit;\n    }\n    return 1;\n}",
                "java": "class SgAllUniqueLowercase {\n    public static boolean sg_all_unique_lowercase(String s) {\n        int seen = 0;\n        if (s.length() > 26) return false;\n        for (int i = 0; i < s.length(); i++) {\n            int bit = 1 << (s.charAt(i) - 'a');\n            if ((seen & bit) != 0) return false;\n            seen |= bit;\n        }\n        return true;\n    }\n}",
                "rust": "pub fn sg_all_unique_lowercase(s: &str) -> bool {\n    let mut seen: i32 = 0;\n    if s.len() > 26 { return false; }\n    for ch in s.bytes() { let bit = 1 << (ch - b'a'); if (seen & bit) != 0 { return false; } seen |= bit; }\n    true\n}",
            },
        ),
        Problem(
            "sg_matrix_2x2_product_trace",
            "SpecGenBench Matrix 2x2 Product Trace",
            "Return the trace of the product of two 2x2 matrices `A` and `B`.",
            ["Inputs are provided row-major as eight integers.", "Intermediate products and the final sum fit in signed 32-bit integer range."],
            "int",
            [{"name": "a00", "type": "int"}, {"name": "a01", "type": "int"}, {"name": "a10", "type": "int"}, {"name": "a11", "type": "int"}, {"name": "b00", "type": "int"}, {"name": "b01", "type": "int"}, {"name": "b10", "type": "int"}, {"name": "b11", "type": "int"}],
            [case({"a00": 1, "a01": 2, "a10": 3, "a11": 4, "b00": 5, "b01": 6, "b10": 7, "b11": 8}, 69), case({"a00": 1, "a01": 0, "a10": 0, "a11": 1, "b00": 2, "b01": 3, "b10": 4, "b11": 5}, 7)],
            sg("MatrixMul"),
            "hard",
            {
                "c": "int sg_matrix_2x2_product_trace(int a00, int a01, int a10, int a11, int b00, int b01, int b10, int b11) {\n    int c00 = a00 * b00 + a01 * b10;\n    int c11 = a10 * b01 + a11 * b11;\n    return c00 + c11;\n}",
                "java": "class SgMatrix2x2ProductTrace {\n    public static int sg_matrix_2x2_product_trace(int a00, int a01, int a10, int a11, int b00, int b01, int b10, int b11) {\n        int c00 = a00 * b00 + a01 * b10;\n        int c11 = a10 * b01 + a11 * b11;\n        return c00 + c11;\n    }\n}",
                "rust": "pub fn sg_matrix_2x2_product_trace(a00: i32, a01: i32, a10: i32, a11: i32, b00: i32, b01: i32, b10: i32, b11: i32) -> i32 {\n    let c00 = a00 * b00 + a01 * b10;\n    let c11 = a10 * b01 + a11 * b11;\n    c00 + c11\n}",
            },
        ),
    ]


def curated_expansion_problems() -> list[Problem]:
    lc = lambda slug: source("LeetCode", slug, f"https://leetcode.com/problems/{slug}/")
    lg = lambda slug: source("Luogu", slug, f"https://www.luogu.com.cn/problem/{slug}")
    sg = lambda slug: source(
        "SpecGenBench",
        f"SpecGenBench/common/{slug}",
        f"file:///home/yangfp/Arc/represent/external/specgen-artifact/benchmark/SpecGenBench/common/{slug}/{slug}.java",
        "local three-language rewrite from local external benchmark",
    )
    return [
        Problem("lc_unique_paths_count", "LC Unique Paths Count", "Return the number of right/down paths in an `m` by `n` grid.", ["`1 <= m, n <= 30`.", "The result fits in signed 32-bit integer range."], "int", [{"name": "m", "type": "int"}, {"name": "n", "type": "int"}], [case({"m": 3, "n": 7}, 28), case({"m": 3, "n": 2}, 3), case({"m": 1, "n": 10}, 1)], lc("unique-paths"), "medium", {
            "c": "int lc_unique_paths_count(int m, int n) {\n    int dp[31][31];\n    for (int i = 0; i < m; i++) dp[i][0] = 1;\n    for (int j = 0; j < n; j++) dp[0][j] = 1;\n    for (int i = 1; i < m; i++) for (int j = 1; j < n; j++) dp[i][j] = dp[i - 1][j] + dp[i][j - 1];\n    return dp[m - 1][n - 1];\n}",
            "java": "class LcUniquePathsCount {\n    public static int lc_unique_paths_count(int m, int n) {\n        int[][] dp = new int[m][n];\n        for (int i = 0; i < m; i++) dp[i][0] = 1;\n        for (int j = 0; j < n; j++) dp[0][j] = 1;\n        for (int i = 1; i < m; i++) for (int j = 1; j < n; j++) dp[i][j] = dp[i - 1][j] + dp[i][j - 1];\n        return dp[m - 1][n - 1];\n    }\n}",
            "rust": "pub fn lc_unique_paths_count(m: i32, n: i32) -> i32 {\n    let mut dp = [[0i32; 31]; 31];\n    let mut i = 0;\n    while i < m { dp[i as usize][0] = 1; i += 1; }\n    let mut j = 0;\n    while j < n { dp[0][j as usize] = 1; j += 1; }\n    i = 1;\n    while i < m { j = 1; while j < n { dp[i as usize][j as usize] = dp[(i - 1) as usize][j as usize] + dp[i as usize][(j - 1) as usize]; j += 1; } i += 1; }\n    dp[(m - 1) as usize][(n - 1) as usize]\n}",
        }),
        Problem("lc_lcs_length", "LC Longest Common Subsequence Length", "Return the length of the longest common subsequence of two ASCII strings.", ["String lengths are at most `63`.", "Subsequence characters keep relative order but need not be contiguous."], "int", [{"name": "text1", "type": "string"}, {"name": "text2", "type": "string"}], [case({"text1": "abcde", "text2": "ace"}, 3), case({"text1": "abc", "text2": "abc"}, 3), case({"text1": "abc", "text2": "def"}, 0)], lc("longest-common-subsequence"), "medium", {
            "c": "int lc_lcs_length(const char *text1, const char *text2) {\n    int n = 0, m = 0;\n    while (text1[n] != '\\0') n++;\n    while (text2[m] != '\\0') m++;\n    int dp[64][64] = {{0}};\n    for (int i = 1; i <= n; i++) for (int j = 1; j <= m; j++) {\n        if (text1[i - 1] == text2[j - 1]) dp[i][j] = dp[i - 1][j - 1] + 1;\n        else dp[i][j] = dp[i - 1][j] > dp[i][j - 1] ? dp[i - 1][j] : dp[i][j - 1];\n    }\n    return dp[n][m];\n}",
            "java": "class LcLcsLength {\n    public static int lc_lcs_length(String text1, String text2) {\n        int n = text1.length(), m = text2.length();\n        int[][] dp = new int[n + 1][m + 1];\n        for (int i = 1; i <= n; i++) for (int j = 1; j <= m; j++) {\n            if (text1.charAt(i - 1) == text2.charAt(j - 1)) dp[i][j] = dp[i - 1][j - 1] + 1;\n            else dp[i][j] = dp[i - 1][j] > dp[i][j - 1] ? dp[i - 1][j] : dp[i][j - 1];\n        }\n        return dp[n][m];\n    }\n}",
            "rust": "pub fn lc_lcs_length(text1: &str, text2: &str) -> i32 {\n    let a = text1.as_bytes();\n    let b = text2.as_bytes();\n    let mut dp = [[0i32; 64]; 64];\n    let mut i = 1usize;\n    while i <= a.len() { let mut j = 1usize; while j <= b.len() { if a[i - 1] == b[j - 1] { dp[i][j] = dp[i - 1][j - 1] + 1; } else { dp[i][j] = if dp[i - 1][j] > dp[i][j - 1] { dp[i - 1][j] } else { dp[i][j - 1] }; } j += 1; } i += 1; }\n    dp[a.len()][b.len()]\n}",
        }),
        Problem("lc_decode_ways_count", "LC Decode Ways Count", "Return how many ways digit string `s` can be decoded with `1 -> A` through `26 -> Z`.", ["`s` contains digits only.", "The empty string returns `0`.", "The result fits in signed 32-bit integer range."], "int", [{"name": "s", "type": "string"}], [case({"s": "12"}, 2), case({"s": "226"}, 3), case({"s": "06"}, 0), case({"s": ""}, 0)], lc("decode-ways"), "medium", {
            "c": "int lc_decode_ways_count(const char *s) {\n    int n = 0;\n    while (s[n] != '\\0') n++;\n    if (n == 0) return 0;\n    int dp[128] = {0};\n    dp[0] = 1;\n    dp[1] = s[0] == '0' ? 0 : 1;\n    for (int i = 2; i <= n; i++) {\n        if (s[i - 1] != '0') dp[i] += dp[i - 1];\n        int two = (s[i - 2] - '0') * 10 + (s[i - 1] - '0');\n        if (two >= 10 && two <= 26) dp[i] += dp[i - 2];\n    }\n    return dp[n];\n}",
            "java": "class LcDecodeWaysCount {\n    public static int lc_decode_ways_count(String s) {\n        int n = s.length();\n        if (n == 0) return 0;\n        int[] dp = new int[n + 1];\n        dp[0] = 1;\n        dp[1] = s.charAt(0) == '0' ? 0 : 1;\n        for (int i = 2; i <= n; i++) {\n            if (s.charAt(i - 1) != '0') dp[i] += dp[i - 1];\n            int two = (s.charAt(i - 2) - '0') * 10 + (s.charAt(i - 1) - '0');\n            if (two >= 10 && two <= 26) dp[i] += dp[i - 2];\n        }\n        return dp[n];\n    }\n}",
            "rust": "pub fn lc_decode_ways_count(s: &str) -> i32 {\n    let b = s.as_bytes();\n    let n = b.len();\n    if n == 0 { return 0; }\n    let mut dp = [0i32; 128];\n    dp[0] = 1;\n    dp[1] = if b[0] == b'0' { 0 } else { 1 };\n    let mut i = 2usize;\n    while i <= n { if b[i - 1] != b'0' { dp[i] += dp[i - 1]; } let two = ((b[i - 2] - b'0') as i32) * 10 + (b[i - 1] - b'0') as i32; if two >= 10 && two <= 26 { dp[i] += dp[i - 2]; } i += 1; }\n    dp[n]\n}",
        }),
        Problem("lc_longest_substring_unique_len", "LC Longest Substring Unique Length", "Return the length of the longest substring of `s` without repeated ASCII characters.", ["`s` is ASCII.", "The empty string returns `0`."], "int", [{"name": "s", "type": "string"}], [case({"s": "abcabcbb"}, 3), case({"s": "bbbbb"}, 1), case({"s": "pwwkew"}, 3), case({"s": ""}, 0)], lc("longest-substring-without-repeating-characters"), "medium", {
            "c": "int lc_longest_substring_unique_len(const char *s) {\n    int last[256];\n    for (int i = 0; i < 256; i++) last[i] = -1;\n    int left = 0, best = 0;\n    for (int right = 0; s[right] != '\\0'; right++) {\n        unsigned char ch = (unsigned char)s[right];\n        if (last[ch] >= left) left = last[ch] + 1;\n        last[ch] = right;\n        if (right - left + 1 > best) best = right - left + 1;\n    }\n    return best;\n}",
            "java": "class LcLongestSubstringUniqueLen {\n    public static int lc_longest_substring_unique_len(String s) {\n        int[] last = new int[256];\n        for (int i = 0; i < 256; i++) last[i] = -1;\n        int left = 0, best = 0;\n        for (int right = 0; right < s.length(); right++) {\n            int ch = s.charAt(right);\n            if (last[ch] >= left) left = last[ch] + 1;\n            last[ch] = right;\n            if (right - left + 1 > best) best = right - left + 1;\n        }\n        return best;\n    }\n}",
            "rust": "pub fn lc_longest_substring_unique_len(s: &str) -> i32 {\n    let mut last = [-1i32; 256];\n    let mut left = 0i32;\n    let mut best = 0i32;\n    for (right, ch) in s.bytes().enumerate() { let r = right as i32; if last[ch as usize] >= left { left = last[ch as usize] + 1; } last[ch as usize] = r; if r - left + 1 > best { best = r - left + 1; } }\n    best\n}",
        }),
        Problem("lc_valid_mountain_array_csv", "LC Valid Mountain Array CSV", "Return true if comma-separated array `arr` is a valid mountain array.", ["The empty string represents an empty array.", "A valid mountain has length at least `3`, strictly increases, then strictly decreases."], "bool", [{"name": "arr", "type": "string"}], [case({"arr": "2,1"}, False), case({"arr": "3,5,5"}, False), case({"arr": "0,3,2,1"}, True)], lc("valid-mountain-array"), "easy", {
            "c": "int lc_valid_mountain_array_csv(const char *arr) {\n    int a[128], n = 0, i = 0;\n    if (arr[0] == '\\0') return 0;\n    while (arr[i] != '\\0') { int sign = 1, v = 0; if (arr[i] == '-') { sign = -1; i++; } while (arr[i] >= '0' && arr[i] <= '9') { v = v * 10 + arr[i] - '0'; i++; } a[n++] = sign * v; if (arr[i] == ',') i++; }\n    if (n < 3) return 0;\n    int p = 0;\n    while (p + 1 < n && a[p] < a[p + 1]) p++;\n    if (p == 0 || p == n - 1) return 0;\n    while (p + 1 < n && a[p] > a[p + 1]) p++;\n    return p == n - 1;\n}",
            "java": "class LcValidMountainArrayCsv {\n    public static boolean lc_valid_mountain_array_csv(String arr) {\n        if (arr.isEmpty()) return false;\n        String[] parts = arr.split(\",\");\n        int n = parts.length;\n        if (n < 3) return false;\n        int[] a = new int[n];\n        for (int i = 0; i < n; i++) a[i] = Integer.parseInt(parts[i]);\n        int p = 0;\n        while (p + 1 < n && a[p] < a[p + 1]) p++;\n        if (p == 0 || p == n - 1) return false;\n        while (p + 1 < n && a[p] > a[p + 1]) p++;\n        return p == n - 1;\n    }\n}",
            "rust": "pub fn lc_valid_mountain_array_csv(arr: &str) -> bool {\n    if arr.is_empty() { return false; }\n    let a: Vec<i32> = arr.split(',').map(|x| x.parse::<i32>().unwrap()).collect();\n    let n = a.len();\n    if n < 3 { return false; }\n    let mut p = 0usize;\n    while p + 1 < n && a[p] < a[p + 1] { p += 1; }\n    if p == 0 || p == n - 1 { return false; }\n    while p + 1 < n && a[p] > a[p + 1] { p += 1; }\n    p == n - 1\n}",
        }),
        Problem("lc_can_jump_csv", "LC Jump Game CSV", "Return true if the last index is reachable from index `0` in comma-separated jump lengths.", ["The empty string represents an empty array and returns false.", "Each value is nonnegative."], "bool", [{"name": "nums", "type": "string"}], [case({"nums": "2,3,1,1,4"}, True), case({"nums": "3,2,1,0,4"}, False), case({"nums": "0"}, True)], lc("jump-game"), "medium", {
            "c": "int lc_can_jump_csv(const char *nums) {\n    int reach = 0, idx = 0, i = 0;\n    if (nums[0] == '\\0') return 0;\n    while (nums[i] != '\\0') { int v = 0; while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } if (idx > reach) return 0; if (idx + v > reach) reach = idx + v; idx++; if (nums[i] == ',') i++; }\n    return 1;\n}",
            "java": "class LcCanJumpCsv {\n    public static boolean lc_can_jump_csv(String nums) {\n        if (nums.isEmpty()) return false;\n        String[] parts = nums.split(\",\");\n        int reach = 0;\n        for (int i = 0; i < parts.length; i++) { if (i > reach) return false; int v = Integer.parseInt(parts[i]); if (i + v > reach) reach = i + v; }\n        return true;\n    }\n}",
            "rust": "pub fn lc_can_jump_csv(nums: &str) -> bool {\n    if nums.is_empty() { return false; }\n    let mut reach = 0i32;\n    for (i, part) in nums.split(',').enumerate() { let idx = i as i32; if idx > reach { return false; } let v = part.parse::<i32>().unwrap(); if idx + v > reach { reach = idx + v; } }\n    true\n}",
        }),
        Problem("lc_subarray_sum_k_count_csv", "LC Subarray Sum Equals K Count CSV", "Return how many contiguous subarrays of comma-separated `nums` sum to `k`.", ["The empty string represents an empty array.", "The count fits in signed 32-bit integer range."], "int", [{"name": "nums", "type": "string"}, {"name": "k", "type": "int"}], [case({"nums": "1,1,1", "k": 2}, 2), case({"nums": "1,2,3", "k": 3}, 2), case({"nums": "", "k": 0}, 0)], lc("subarray-sum-equals-k"), "medium", {
            "c": "int lc_subarray_sum_k_count_csv(const char *nums, int k) {\n    int a[128], n = 0, i = 0;\n    if (nums[0] == '\\0') return 0;\n    while (nums[i] != '\\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } a[n++] = sign * v; if (nums[i] == ',') i++; }\n    int count = 0;\n    for (int l = 0; l < n; l++) { int sum = 0; for (int r = l; r < n; r++) { sum += a[r]; if (sum == k) count++; } }\n    return count;\n}",
            "java": "class LcSubarraySumKCountCsv {\n    public static int lc_subarray_sum_k_count_csv(String nums, int k) {\n        if (nums.isEmpty()) return 0;\n        String[] parts = nums.split(\",\");\n        int[] a = new int[parts.length];\n        for (int i = 0; i < parts.length; i++) a[i] = Integer.parseInt(parts[i]);\n        int count = 0;\n        for (int l = 0; l < a.length; l++) { int sum = 0; for (int r = l; r < a.length; r++) { sum += a[r]; if (sum == k) count++; } }\n        return count;\n    }\n}",
            "rust": "pub fn lc_subarray_sum_k_count_csv(nums: &str, k: i32) -> i32 {\n    if nums.is_empty() { return 0; }\n    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect();\n    let mut count = 0;\n    let mut l = 0usize;\n    while l < a.len() { let mut sum = 0; let mut r = l; while r < a.len() { sum += a[r]; if sum == k { count += 1; } r += 1; } l += 1; }\n    count\n}",
        }),
        Problem("lc_search_rotated_index_csv", "LC Search Rotated Index CSV", "Return the index of `target` in a rotated sorted distinct integer array, or `-1` if absent.", ["`nums` is comma-separated and nonempty.", "Values are distinct."], "int", [{"name": "nums", "type": "string"}, {"name": "target", "type": "int"}], [case({"nums": "4,5,6,7,0,1,2", "target": 0}, 4), case({"nums": "4,5,6,7,0,1,2", "target": 3}, -1), case({"nums": "1", "target": 1}, 0)], lc("search-in-rotated-sorted-array"), "medium", {
            "c": "int lc_search_rotated_index_csv(const char *nums, int target) {\n    int a[128], n = 0, i = 0;\n    while (nums[i] != '\\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } a[n++] = sign * v; if (nums[i] == ',') i++; }\n    int l = 0, r = n - 1;\n    while (l <= r) { int mid = l + (r - l) / 2; if (a[mid] == target) return mid; if (a[l] <= a[mid]) { if (a[l] <= target && target < a[mid]) r = mid - 1; else l = mid + 1; } else { if (a[mid] < target && target <= a[r]) l = mid + 1; else r = mid - 1; } }\n    return -1;\n}",
            "java": "class LcSearchRotatedIndexCsv {\n    public static int lc_search_rotated_index_csv(String nums, int target) {\n        String[] parts = nums.split(\",\");\n        int[] a = new int[parts.length];\n        for (int i = 0; i < parts.length; i++) a[i] = Integer.parseInt(parts[i]);\n        int l = 0, r = a.length - 1;\n        while (l <= r) { int mid = l + (r - l) / 2; if (a[mid] == target) return mid; if (a[l] <= a[mid]) { if (a[l] <= target && target < a[mid]) r = mid - 1; else l = mid + 1; } else { if (a[mid] < target && target <= a[r]) l = mid + 1; else r = mid - 1; } }\n        return -1;\n    }\n}",
            "rust": "pub fn lc_search_rotated_index_csv(nums: &str, target: i32) -> i32 {\n    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect();\n    let mut l = 0i32; let mut r = a.len() as i32 - 1;\n    while l <= r { let mid = l + (r - l) / 2; let mv = a[mid as usize]; if mv == target { return mid; } if a[l as usize] <= mv { if a[l as usize] <= target && target < mv { r = mid - 1; } else { l = mid + 1; } } else if mv < target && target <= a[r as usize] { l = mid + 1; } else { r = mid - 1; } }\n    -1\n}",
        }),
        Problem("lc_koko_min_speed_csv", "LC Koko Minimum Speed CSV", "Return the minimum integer banana-eating speed needed to finish all piles within `h` hours.", ["`piles` is a nonempty comma-separated list of positive integers.", "`h` is at least the number of piles."], "int", [{"name": "piles", "type": "string"}, {"name": "h", "type": "int"}], [case({"piles": "3,6,7,11", "h": 8}, 4), case({"piles": "30,11,23,4,20", "h": 5}, 30), case({"piles": "30,11,23,4,20", "h": 6}, 23)], lc("koko-eating-bananas"), "medium", {
            "c": "int lc_koko_min_speed_csv(const char *piles, int h) {\n    int a[128], n = 0, i = 0, max = 0;\n    while (piles[i] != '\\0') { int v = 0; while (piles[i] >= '0' && piles[i] <= '9') { v = v * 10 + piles[i] - '0'; i++; } a[n++] = v; if (v > max) max = v; if (piles[i] == ',') i++; }\n    int lo = 1, hi = max;\n    while (lo < hi) { int mid = lo + (hi - lo) / 2; int hours = 0; for (int j = 0; j < n; j++) hours += (a[j] + mid - 1) / mid; if (hours <= h) hi = mid; else lo = mid + 1; }\n    return lo;\n}",
            "java": "class LcKokoMinSpeedCsv {\n    public static int lc_koko_min_speed_csv(String piles, int h) {\n        String[] parts = piles.split(\",\");\n        int[] a = new int[parts.length];\n        int max = 0;\n        for (int i = 0; i < parts.length; i++) { a[i] = Integer.parseInt(parts[i]); if (a[i] > max) max = a[i]; }\n        int lo = 1, hi = max;\n        while (lo < hi) { int mid = lo + (hi - lo) / 2; int hours = 0; for (int v : a) hours += (v + mid - 1) / mid; if (hours <= h) hi = mid; else lo = mid + 1; }\n        return lo;\n    }\n}",
            "rust": "pub fn lc_koko_min_speed_csv(piles: &str, h: i32) -> i32 {\n    let a: Vec<i32> = piles.split(',').map(|x| x.parse::<i32>().unwrap()).collect();\n    let mut max = 0; for &v in &a { if v > max { max = v; } }\n    let mut lo = 1; let mut hi = max;\n    while lo < hi { let mid = lo + (hi - lo) / 2; let mut hours = 0; for &v in &a { hours += (v + mid - 1) / mid; } if hours <= h { hi = mid; } else { lo = mid + 1; } }\n    lo\n}",
        }),
        Problem("lc_eval_rpn_csv", "LC Evaluate RPN CSV", "Evaluate a reverse Polish notation expression encoded as comma-separated tokens.", ["Tokens are integers or one of `+`, `-`, `*`, `/`.", "Division truncates toward zero.", "The expression is valid."], "int", [{"name": "tokens", "type": "string"}], [case({"tokens": "2,1,+,3,*"}, 9), case({"tokens": "4,13,5,/,+ "}, 6), case({"tokens": "10,6,9,3,+,-11,*,/,*,17,+,5,+"}, 22)], lc("evaluate-reverse-polish-notation"), "medium", {
            "c": "int lc_eval_rpn_csv(const char *tokens) {\n    int stack[128], top = 0, i = 0;\n    while (tokens[i] != '\\0') { while (tokens[i] == ' ') i++; if ((tokens[i] == '+' || tokens[i] == '*' || tokens[i] == '/') && (tokens[i + 1] == ',' || tokens[i + 1] == '\\0' || tokens[i + 1] == ' ')) { int b = stack[--top], a = stack[--top]; char op = tokens[i++]; stack[top++] = op == '+' ? a + b : (op == '*' ? a * b : a / b); } else if (tokens[i] == '-' && (tokens[i + 1] == ',' || tokens[i + 1] == '\\0' || tokens[i + 1] == ' ')) { int b = stack[--top], a = stack[--top]; i++; stack[top++] = a - b; } else { int sign = 1, v = 0; if (tokens[i] == '-') { sign = -1; i++; } while (tokens[i] >= '0' && tokens[i] <= '9') { v = v * 10 + tokens[i] - '0'; i++; } stack[top++] = sign * v; } while (tokens[i] == ' ') i++; if (tokens[i] == ',') i++; }\n    return stack[0];\n}",
            "java": "class LcEvalRpnCsv {\n    public static int lc_eval_rpn_csv(String tokens) {\n        String[] parts = tokens.split(\",\");\n        int[] stack = new int[parts.length];\n        int top = 0;\n        for (String raw : parts) { String t = raw.trim(); if (t.equals(\"+\") || t.equals(\"-\") || t.equals(\"*\") || t.equals(\"/\")) { int b = stack[--top], a = stack[--top]; if (t.equals(\"+\")) stack[top++] = a + b; else if (t.equals(\"-\")) stack[top++] = a - b; else if (t.equals(\"*\")) stack[top++] = a * b; else stack[top++] = a / b; } else stack[top++] = Integer.parseInt(t); }\n        return stack[0];\n    }\n}",
            "rust": "pub fn lc_eval_rpn_csv(tokens: &str) -> i32 {\n    let mut stack: Vec<i32> = Vec::new();\n    for raw in tokens.split(',') { let t = raw.trim(); match t { \"+\" => { let b = stack.pop().unwrap(); let a = stack.pop().unwrap(); stack.push(a + b); }, \"-\" => { let b = stack.pop().unwrap(); let a = stack.pop().unwrap(); stack.push(a - b); }, \"*\" => { let b = stack.pop().unwrap(); let a = stack.pop().unwrap(); stack.push(a * b); }, \"/\" => { let b = stack.pop().unwrap(); let a = stack.pop().unwrap(); stack.push(a / b); }, _ => stack.push(t.parse::<i32>().unwrap()), } }\n    stack[0]\n}",
        }),
        Problem("luogu_p5714_bmi_category", "Luogu P5714 BMI Category", "Return BMI category code for mass `m` kilograms and height `h` centimeters.", ["`m > 0` and `h > 0`.", "Use BMI `m / meters^2`.", "Return `0` for underweight, `1` for normal, `2` for overweight."], "int", [{"name": "m", "type": "int"}, {"name": "h", "type": "int"}], [case({"m": 70, "h": 170}, 1), case({"m": 45, "h": 170}, 0), case({"m": 90, "h": 170}, 2)], lg("P5714"), "easy", {
            "c": "int luogu_p5714_bmi_category(int m, int h) {\n    int bmi100 = m * 1000000 / (h * h);\n    if (bmi100 < 1850) return 0;\n    if (bmi100 < 2400) return 1;\n    return 2;\n}",
            "java": "class LuoguP5714BmiCategory {\n    public static int luogu_p5714_bmi_category(int m, int h) {\n        int bmi100 = m * 1000000 / (h * h);\n        if (bmi100 < 1850) return 0;\n        if (bmi100 < 2400) return 1;\n        return 2;\n    }\n}",
            "rust": "pub fn luogu_p5714_bmi_category(m: i32, h: i32) -> i32 {\n    let bmi100 = m * 1000000 / (h * h);\n    if bmi100 < 1850 { return 0; }\n    if bmi100 < 2400 { return 1; }\n    2\n}",
        }),
        Problem("luogu_p5717_triangle_type_code", "Luogu P5717 Triangle Type Code", "Classify three side lengths.", ["Return `0` when the sides cannot form a triangle.", "Return `3` for equilateral, `2` for isosceles non-equilateral, and `1` for scalene."], "int", [{"name": "a", "type": "int"}, {"name": "b", "type": "int"}, {"name": "c", "type": "int"}], [case({"a": 1, "b": 2, "c": 3}, 0), case({"a": 3, "b": 3, "c": 3}, 3), case({"a": 3, "b": 3, "c": 4}, 2), case({"a": 3, "b": 4, "c": 5}, 1)], lg("P5717"), "easy", {
            "c": "int luogu_p5717_triangle_type_code(int a, int b, int c) {\n    if (a + b <= c || a + c <= b || b + c <= a) return 0;\n    if (a == b && b == c) return 3;\n    if (a == b || a == c || b == c) return 2;\n    return 1;\n}",
            "java": "class LuoguP5717TriangleTypeCode {\n    public static int luogu_p5717_triangle_type_code(int a, int b, int c) {\n        if (a + b <= c || a + c <= b || b + c <= a) return 0;\n        if (a == b && b == c) return 3;\n        if (a == b || a == c || b == c) return 2;\n        return 1;\n    }\n}",
            "rust": "pub fn luogu_p5717_triangle_type_code(a: i32, b: i32, c: i32) -> i32 {\n    if a + b <= c || a + c <= b || b + c <= a { return 0; }\n    if a == b && b == c { return 3; }\n    if a == b || a == c || b == c { return 2; }\n    1\n}",
        }),
        Problem("luogu_p5720_half_until_one_days", "Luogu P5720 Half Until One Days", "Starting with length `n`, repeatedly replace it by half rounded down until it becomes `1`; return the number of values printed including the initial value.", ["`n >= 1`."], "int", [{"name": "n", "type": "int"}], [case({"n": 1}, 1), case({"n": 10}, 4), case({"n": 100}, 7)], lg("P5720"), "easy", {
            "c": "int luogu_p5720_half_until_one_days(int n) {\n    int count = 1;\n    while (n > 1) { n /= 2; count++; }\n    return count;\n}",
            "java": "class LuoguP5720HalfUntilOneDays {\n    public static int luogu_p5720_half_until_one_days(int n) {\n        int count = 1;\n        while (n > 1) { n /= 2; count++; }\n        return count;\n    }\n}",
            "rust": "pub fn luogu_p5720_half_until_one_days(mut n: i32) -> i32 {\n    let mut count = 1;\n    while n > 1 { n /= 2; count += 1; }\n    count\n}",
        }),
        Problem("luogu_p5723_prime_sum_count", "Luogu P5723 Prime Sum Count", "Return how many consecutive primes starting from `2` can be added without the sum exceeding `limit`.", ["`limit >= 0`.", "Primes are considered in increasing order."], "int", [{"name": "limit", "type": "int"}], [case({"limit": 10}, 3), case({"limit": 2}, 1), case({"limit": 1}, 0)], lg("P5723"), "medium", {
            "c": "int luogu_p5723_prime_sum_count(int limit) {\n    int sum = 0, count = 0;\n    for (int x = 2; x <= limit; x++) { int prime = 1; for (int d = 2; d * d <= x; d++) if (x % d == 0) prime = 0; if (prime) { if (sum + x > limit) break; sum += x; count++; } }\n    return count;\n}",
            "java": "class LuoguP5723PrimeSumCount {\n    public static int luogu_p5723_prime_sum_count(int limit) {\n        int sum = 0, count = 0;\n        for (int x = 2; x <= limit; x++) { boolean prime = true; for (int d = 2; d * d <= x; d++) if (x % d == 0) prime = false; if (prime) { if (sum + x > limit) break; sum += x; count++; } }\n        return count;\n    }\n}",
            "rust": "pub fn luogu_p5723_prime_sum_count(limit: i32) -> i32 {\n    let mut sum = 0; let mut count = 0; let mut x = 2;\n    while x <= limit { let mut prime = true; let mut d = 2; while d * d <= x { if x % d == 0 { prime = false; } d += 1; } if prime { if sum + x > limit { break; } sum += x; count += 1; } x += 1; }\n    count\n}",
        }),
        Problem("sg_is_monotonic_array", "SpecGenBench Is Monotonic Array", "Return true if the first `n` values are monotone nondecreasing or monotone nonincreasing.", ["`n >= 0` and `nums` has at least `n` elements.", "Arrays of length `0`, `1`, or `2` can be monotone."], "bool", [{"name": "n", "type": "int"}, {"name": "nums", "type": "int_array"}], [case({"n": 4, "nums": [1, 2, 2, 3]}, True), case({"n": 4, "nums": [6, 5, 4, 4]}, True), case({"n": 3, "nums": [1, 3, 2]}, False)], sg("IsMonotonic"), "easy", {
            "c": "int sg_is_monotonic_array(int n, int *nums) {\n    int inc = 1, dec = 1;\n    for (int i = 0; i + 1 < n; i++) { if (nums[i] > nums[i + 1]) inc = 0; if (nums[i] < nums[i + 1]) dec = 0; }\n    return inc || dec;\n}",
            "java": "class SgIsMonotonicArray {\n    public static boolean sg_is_monotonic_array(int n, int[] nums) {\n        boolean inc = true, dec = true;\n        for (int i = 0; i + 1 < n; i++) { if (nums[i] > nums[i + 1]) inc = false; if (nums[i] < nums[i + 1]) dec = false; }\n        return inc || dec;\n    }\n}",
            "rust": "pub fn sg_is_monotonic_array(n: i32, nums: &[i32]) -> bool {\n    let mut inc = true; let mut dec = true; let mut i = 0;\n    while i + 1 < n { if nums[i as usize] > nums[(i + 1) as usize] { inc = false; } if nums[i as usize] < nums[(i + 1) as usize] { dec = false; } i += 1; }\n    inc || dec\n}",
        }),
        Problem("sg_power_of_four_flag", "SpecGenBench Power Of Four Flag", "Return true if `n` is a positive power of four.", ["`n` is a signed 32-bit integer."], "bool", [{"name": "n", "type": "int"}], [case({"n": 16}, True), case({"n": 5}, False), case({"n": 1}, True), case({"n": 0}, False)], sg("PowerOfFourLoop"), "easy", {
            "c": "int sg_power_of_four_flag(int n) {\n    if (n <= 0) return 0;\n    while (n % 4 == 0) n /= 4;\n    return n == 1;\n}",
            "java": "class SgPowerOfFourFlag {\n    public static boolean sg_power_of_four_flag(int n) {\n        if (n <= 0) return false;\n        while (n % 4 == 0) n /= 4;\n        return n == 1;\n    }\n}",
            "rust": "pub fn sg_power_of_four_flag(mut n: i32) -> bool {\n    if n <= 0 { return false; }\n    while n % 4 == 0 { n /= 4; }\n    n == 1\n}",
        }),
        Problem("sg_prime_check_flag", "SpecGenBench Prime Check Flag", "Return true if `n` is prime.", ["`n >= 0`.", "Values less than `2` are not prime."], "bool", [{"name": "n", "type": "int"}], [case({"n": 2}, True), case({"n": 9}, False), case({"n": 17}, True), case({"n": 1}, False)], sg("PrimeCheck"), "medium", {
            "c": "int sg_prime_check_flag(int n) {\n    if (n < 2) return 0;\n    for (int d = 2; d * d <= n; d++) if (n % d == 0) return 0;\n    return 1;\n}",
            "java": "class SgPrimeCheckFlag {\n    public static boolean sg_prime_check_flag(int n) {\n        if (n < 2) return false;\n        for (int d = 2; d * d <= n; d++) if (n % d == 0) return false;\n        return true;\n    }\n}",
            "rust": "pub fn sg_prime_check_flag(n: i32) -> bool {\n    if n < 2 { return false; }\n    let mut d = 2;\n    while d * d <= n { if n % d == 0 { return false; } d += 1; }\n    true\n}",
        }),
        Problem("sg_total_rectangle_area", "SpecGenBench Total Rectangle Area", "Return the total covered area of two axis-aligned rectangles.", ["Each rectangle is given by lower-left and upper-right corners.", "`ax1 <= ax2`, `ay1 <= ay2`, `bx1 <= bx2`, and `by1 <= by2`."], "int", [{"name": "ax1", "type": "int"}, {"name": "ay1", "type": "int"}, {"name": "ax2", "type": "int"}, {"name": "ay2", "type": "int"}, {"name": "bx1", "type": "int"}, {"name": "by1", "type": "int"}, {"name": "bx2", "type": "int"}, {"name": "by2", "type": "int"}], [case({"ax1": -3, "ay1": 0, "ax2": 3, "ay2": 4, "bx1": 0, "by1": -1, "bx2": 9, "by2": 2}, 45), case({"ax1": 0, "ay1": 0, "ax2": 1, "ay2": 1, "bx1": 2, "by1": 2, "bx2": 3, "by2": 3}, 2)], sg("ComputeArea"), "medium", {
            "c": "int sg_total_rectangle_area(int ax1, int ay1, int ax2, int ay2, int bx1, int by1, int bx2, int by2) {\n    int area1 = (ax2 - ax1) * (ay2 - ay1);\n    int area2 = (bx2 - bx1) * (by2 - by1);\n    int w = (ax2 < bx2 ? ax2 : bx2) - (ax1 > bx1 ? ax1 : bx1);\n    int h = (ay2 < by2 ? ay2 : by2) - (ay1 > by1 ? ay1 : by1);\n    if (w < 0) w = 0;\n    if (h < 0) h = 0;\n    return area1 + area2 - w * h;\n}",
            "java": "class SgTotalRectangleArea {\n    public static int sg_total_rectangle_area(int ax1, int ay1, int ax2, int ay2, int bx1, int by1, int bx2, int by2) {\n        int area1 = (ax2 - ax1) * (ay2 - ay1);\n        int area2 = (bx2 - bx1) * (by2 - by1);\n        int w = (ax2 < bx2 ? ax2 : bx2) - (ax1 > bx1 ? ax1 : bx1);\n        int h = (ay2 < by2 ? ay2 : by2) - (ay1 > by1 ? ay1 : by1);\n        if (w < 0) w = 0;\n        if (h < 0) h = 0;\n        return area1 + area2 - w * h;\n    }\n}",
            "rust": "pub fn sg_total_rectangle_area(ax1: i32, ay1: i32, ax2: i32, ay2: i32, bx1: i32, by1: i32, bx2: i32, by2: i32) -> i32 {\n    let area1 = (ax2 - ax1) * (ay2 - ay1);\n    let area2 = (bx2 - bx1) * (by2 - by1);\n    let mut w = (if ax2 < bx2 { ax2 } else { bx2 }) - (if ax1 > bx1 { ax1 } else { bx1 });\n    let mut h = (if ay2 < by2 { ay2 } else { by2 }) - (if ay1 > by1 { ay1 } else { by1 });\n    if w < 0 { w = 0; }\n    if h < 0 { h = 0; }\n    area1 + area2 - w * h\n}",
        }),
    ]


def exercism_expansion_problems() -> list[Problem]:
    ex = lambda slug: source(
        "Exercism",
        slug,
        f"https://github.com/exercism/problem-specifications/tree/main/exercises/{slug}",
        "MIT",
    )
    return [
        Problem("ex_difference_of_squares", "Exercism Difference Of Squares", "Return the square of the sum `1..n` minus the sum of squares `1^2..n^2`.", ["`n >= 0`.", "The result fits in signed 32-bit integer range."], "int", [{"name": "n", "type": "int"}], [case({"n": 1}, 0), case({"n": 5}, 170), case({"n": 10}, 2640)], ex("difference-of-squares"), "easy", {
            "c": "int ex_difference_of_squares(int n) {\n    int sum = n * (n + 1) / 2;\n    int square_sum = n * (n + 1) * (2 * n + 1) / 6;\n    return sum * sum - square_sum;\n}",
            "java": "class ExDifferenceOfSquares {\n    public static int ex_difference_of_squares(int n) {\n        int sum = n * (n + 1) / 2;\n        int squareSum = n * (n + 1) * (2 * n + 1) / 6;\n        return sum * sum - squareSum;\n    }\n}",
            "rust": "pub fn ex_difference_of_squares(n: i32) -> i32 {\n    let sum = n * (n + 1) / 2;\n    let square_sum = n * (n + 1) * (2 * n + 1) / 6;\n    sum * sum - square_sum\n}",
        }),
        Problem("ex_grains_square_value", "Exercism Grains Square Value", "Return how many grains are on chessboard square `square` when the first square has 1 grain and each square doubles.", ["`1 <= square <= 30`.", "The result fits in signed 32-bit integer range."], "int", [{"name": "square", "type": "int"}], [case({"square": 1}, 1), case({"square": 2}, 2), case({"square": 16}, 32768)], ex("grains"), "easy", {
            "c": "int ex_grains_square_value(int square) {\n    int value = 1;\n    for (int i = 1; i < square; i++) value *= 2;\n    return value;\n}",
            "java": "class ExGrainsSquareValue {\n    public static int ex_grains_square_value(int square) {\n        int value = 1;\n        for (int i = 1; i < square; i++) value *= 2;\n        return value;\n    }\n}",
            "rust": "pub fn ex_grains_square_value(square: i32) -> i32 {\n    let mut value = 1;\n    let mut i = 1;\n    while i < square { value *= 2; i += 1; }\n    value\n}",
        }),
        Problem("ex_isogram_ascii", "Exercism Isogram ASCII", "Return true if a phrase contains no repeated alphabetic letter, ignoring case and nonletters.", ["Input is ASCII.", "Hyphens and spaces are ignored."], "bool", [{"name": "s", "type": "string"}], [case({"s": "lumberjacks"}, True), case({"s": "background"}, True), case({"s": "six-year-old"}, True), case({"s": "Alphabet"}, False)], ex("isogram"), "easy", {
            "c": "int ex_isogram_ascii(const char *s) {\n    int seen[26] = {0};\n    for (int i = 0; s[i] != '\\0'; i++) { char c = s[i]; if (c >= 'A' && c <= 'Z') c = (char)(c - 'A' + 'a'); if (c >= 'a' && c <= 'z') { int k = c - 'a'; if (seen[k]) return 0; seen[k] = 1; } }\n    return 1;\n}",
            "java": "class ExIsogramAscii {\n    public static boolean ex_isogram_ascii(String s) {\n        boolean[] seen = new boolean[26];\n        for (int i = 0; i < s.length(); i++) { char c = s.charAt(i); if (c >= 'A' && c <= 'Z') c = (char)(c - 'A' + 'a'); if (c >= 'a' && c <= 'z') { int k = c - 'a'; if (seen[k]) return false; seen[k] = true; } }\n        return true;\n    }\n}",
            "rust": "pub fn ex_isogram_ascii(s: &str) -> bool {\n    let mut seen = [false; 26];\n    for mut c in s.bytes() { if c >= b'A' && c <= b'Z' { c = c - b'A' + b'a'; } if c >= b'a' && c <= b'z' { let k = (c - b'a') as usize; if seen[k] { return false; } seen[k] = true; } }\n    true\n}",
        }),
        Problem("ex_luhn_valid_ascii", "Exercism Luhn Valid ASCII", "Return true if `s` passes the Luhn checksum, ignoring spaces.", ["Only digits and spaces are accepted.", "After removing spaces, length must be at least 2."], "bool", [{"name": "s", "type": "string"}], [case({"s": "4539 3195 0343 6467"}, True), case({"s": "8273 1232 7352 0569"}, False), case({"s": "0"}, False)], ex("luhn"), "medium", {
            "c": "int ex_luhn_valid_ascii(const char *s) {\n    int digits[128], n = 0;\n    for (int i = 0; s[i] != '\\0'; i++) { if (s[i] == ' ') continue; if (s[i] < '0' || s[i] > '9') return 0; digits[n++] = s[i] - '0'; }\n    if (n < 2) return 0;\n    int sum = 0, dbl = 0;\n    for (int i = n - 1; i >= 0; i--) { int v = digits[i]; if (dbl) { v *= 2; if (v > 9) v -= 9; } sum += v; dbl = !dbl; }\n    return sum % 10 == 0;\n}",
            "java": "class ExLuhnValidAscii {\n    public static boolean ex_luhn_valid_ascii(String s) {\n        int[] digits = new int[128];\n        int n = 0;\n        for (int i = 0; i < s.length(); i++) { char c = s.charAt(i); if (c == ' ') continue; if (c < '0' || c > '9') return false; digits[n++] = c - '0'; }\n        if (n < 2) return false;\n        int sum = 0; boolean dbl = false;\n        for (int i = n - 1; i >= 0; i--) { int v = digits[i]; if (dbl) { v *= 2; if (v > 9) v -= 9; } sum += v; dbl = !dbl; }\n        return sum % 10 == 0;\n    }\n}",
            "rust": "pub fn ex_luhn_valid_ascii(s: &str) -> bool {\n    let mut digits = [0i32; 128]; let mut n = 0usize;\n    for c in s.bytes() { if c == b' ' { continue; } if c < b'0' || c > b'9' { return false; } digits[n] = (c - b'0') as i32; n += 1; }\n    if n < 2 { return false; }\n    let mut sum = 0; let mut dbl = false; let mut i = n;\n    while i > 0 { i -= 1; let mut v = digits[i]; if dbl { v *= 2; if v > 9 { v -= 9; } } sum += v; dbl = !dbl; }\n    sum % 10 == 0\n}",
        }),
        Problem("ex_matching_brackets_ascii", "Exercism Matching Brackets ASCII", "Return true if brackets in `s` are correctly nested and matched.", ["Only `()`, `[]`, and `{}` are bracket tokens.", "Other ASCII characters are ignored."], "bool", [{"name": "s", "type": "string"}], [case({"s": "{[()]}"}, True), case({"s": "{[(])}"}, False), case({"s": "([]"}, False)], ex("matching-brackets"), "medium", {
            "c": "int ex_matching_brackets_ascii(const char *s) {\n    char st[128]; int top = 0;\n    for (int i = 0; s[i] != '\\0'; i++) { char c = s[i]; if (c == '(' || c == '[' || c == '{') st[top++] = c; else if (c == ')' || c == ']' || c == '}') { if (top == 0) return 0; char o = st[--top]; if ((c == ')' && o != '(') || (c == ']' && o != '[') || (c == '}' && o != '{')) return 0; } }\n    return top == 0;\n}",
            "java": "class ExMatchingBracketsAscii {\n    public static boolean ex_matching_brackets_ascii(String s) {\n        char[] st = new char[128]; int top = 0;\n        for (int i = 0; i < s.length(); i++) { char c = s.charAt(i); if (c == '(' || c == '[' || c == '{') st[top++] = c; else if (c == ')' || c == ']' || c == '}') { if (top == 0) return false; char o = st[--top]; if ((c == ')' && o != '(') || (c == ']' && o != '[') || (c == '}' && o != '{')) return false; } }\n        return top == 0;\n    }\n}",
            "rust": "pub fn ex_matching_brackets_ascii(s: &str) -> bool {\n    let mut st = [0u8; 128]; let mut top = 0usize;\n    for c in s.bytes() { if c == b'(' || c == b'[' || c == b'{' { st[top] = c; top += 1; } else if c == b')' || c == b']' || c == b'}' { if top == 0 { return false; } top -= 1; let o = st[top]; if (c == b')' && o != b'(') || (c == b']' && o != b'[') || (c == b'}' && o != b'{') { return false; } } }\n    top == 0\n}",
        }),
        Problem("ex_nth_prime_value", "Exercism Nth Prime Value", "Return the `n`th prime number using one-based indexing.", ["`n >= 1`.", "The answer fits in signed 32-bit integer range."], "int", [{"name": "n", "type": "int"}], [case({"n": 1}, 2), case({"n": 6}, 13), case({"n": 10}, 29)], ex("nth-prime"), "medium", {
            "c": "int ex_nth_prime_value(int n) {\n    int count = 0;\n    for (int x = 2;; x++) { int prime = 1; for (int d = 2; d * d <= x; d++) if (x % d == 0) prime = 0; if (prime && ++count == n) return x; }\n}",
            "java": "class ExNthPrimeValue {\n    public static int ex_nth_prime_value(int n) {\n        int count = 0;\n        for (int x = 2;; x++) { boolean prime = true; for (int d = 2; d * d <= x; d++) if (x % d == 0) prime = false; if (prime && ++count == n) return x; }\n    }\n}",
            "rust": "pub fn ex_nth_prime_value(n: i32) -> i32 {\n    let mut count = 0; let mut x = 2;\n    loop { let mut prime = true; let mut d = 2; while d * d <= x { if x % d == 0 { prime = false; } d += 1; } if prime { count += 1; if count == n { return x; } } x += 1; }\n}",
        }),
        Problem("ex_largest_series_product", "Exercism Largest Series Product", "Return the largest product of `span` adjacent digits in string `digits`.", ["`digits` contains decimal digits only.", "`0 <= span <= length(digits)`.", "An empty span has product `1`."], "int", [{"name": "digits", "type": "string"}, {"name": "span", "type": "int"}], [case({"digits": "1027839564", "span": 3}, 270), case({"digits": "12345", "span": 0}, 1), case({"digits": "12345", "span": 2}, 20)], ex("largest-series-product"), "medium", {
            "c": "int ex_largest_series_product(const char *digits, int span) {\n    int n = 0; while (digits[n] != '\\0') n++;\n    if (span == 0) return 1;\n    int best = 0;\n    for (int i = 0; i + span <= n; i++) { int p = 1; for (int j = 0; j < span; j++) p *= digits[i + j] - '0'; if (p > best) best = p; }\n    return best;\n}",
            "java": "class ExLargestSeriesProduct {\n    public static int ex_largest_series_product(String digits, int span) {\n        if (span == 0) return 1;\n        int best = 0;\n        for (int i = 0; i + span <= digits.length(); i++) { int p = 1; for (int j = 0; j < span; j++) p *= digits.charAt(i + j) - '0'; if (p > best) best = p; }\n        return best;\n    }\n}",
            "rust": "pub fn ex_largest_series_product(digits: &str, span: i32) -> i32 {\n    if span == 0 { return 1; }\n    let b = digits.as_bytes(); let mut best = 0; let sp = span as usize; let mut i = 0usize;\n    while i + sp <= b.len() { let mut p = 1; let mut j = 0usize; while j < sp { p *= (b[i + j] - b'0') as i32; j += 1; } if p > best { best = p; } i += 1; }\n    best\n}",
        }),
        Problem("ex_square_root_int", "Exercism Square Root Int", "Return the integer square root of a perfect-square radicand.", ["`radicand >= 1`.", "The input is a perfect square."], "int", [{"name": "radicand", "type": "int"}], [case({"radicand": 1}, 1), case({"radicand": 25}, 5), case({"radicand": 81}, 9)], ex("square-root"), "easy", {
            "c": "int ex_square_root_int(int radicand) {\n    int x = 1;\n    while (x * x < radicand) x++;\n    return x;\n}",
            "java": "class ExSquareRootInt {\n    public static int ex_square_root_int(int radicand) {\n        int x = 1;\n        while (x * x < radicand) x++;\n        return x;\n    }\n}",
            "rust": "pub fn ex_square_root_int(radicand: i32) -> i32 {\n    let mut x = 1;\n    while x * x < radicand { x += 1; }\n    x\n}",
        }),
        Problem("ex_sum_of_multiples_3_5", "Exercism Sum Of Multiples 3 5", "Return the sum of positive integers below `limit` that are divisible by `3` or `5`.", ["`limit >= 0`.", "Count each value once."], "int", [{"name": "limit", "type": "int"}], [case({"limit": 10}, 23), case({"limit": 1}, 0), case({"limit": 20}, 78)], ex("sum-of-multiples"), "easy", {
            "c": "int ex_sum_of_multiples_3_5(int limit) {\n    int sum = 0;\n    for (int i = 1; i < limit; i++) if (i % 3 == 0 || i % 5 == 0) sum += i;\n    return sum;\n}",
            "java": "class ExSumOfMultiples35 {\n    public static int ex_sum_of_multiples_3_5(int limit) {\n        int sum = 0;\n        for (int i = 1; i < limit; i++) if (i % 3 == 0 || i % 5 == 0) sum += i;\n        return sum;\n    }\n}",
            "rust": "pub fn ex_sum_of_multiples_3_5(limit: i32) -> i32 {\n    let mut sum = 0; let mut i = 1;\n    while i < limit { if i % 3 == 0 || i % 5 == 0 { sum += i; } i += 1; }\n    sum\n}",
        }),
        Problem("ex_triangle_kind_code", "Exercism Triangle Kind Code", "Classify a triangle by side lengths.", ["Return `0` for invalid, `1` for equilateral, `2` for isosceles, and `3` for scalene.", "All sides are signed 32-bit integers."], "int", [{"name": "a", "type": "int"}, {"name": "b", "type": "int"}, {"name": "c", "type": "int"}], [case({"a": 2, "b": 2, "c": 2}, 1), case({"a": 3, "b": 4, "c": 4}, 2), case({"a": 3, "b": 4, "c": 5}, 3), case({"a": 1, "b": 1, "c": 3}, 0)], ex("triangle"), "easy", {
            "c": "int ex_triangle_kind_code(int a, int b, int c) {\n    if (a <= 0 || b <= 0 || c <= 0 || a + b <= c || a + c <= b || b + c <= a) return 0;\n    if (a == b && b == c) return 1;\n    if (a == b || a == c || b == c) return 2;\n    return 3;\n}",
            "java": "class ExTriangleKindCode {\n    public static int ex_triangle_kind_code(int a, int b, int c) {\n        if (a <= 0 || b <= 0 || c <= 0 || a + b <= c || a + c <= b || b + c <= a) return 0;\n        if (a == b && b == c) return 1;\n        if (a == b || a == c || b == c) return 2;\n        return 3;\n    }\n}",
            "rust": "pub fn ex_triangle_kind_code(a: i32, b: i32, c: i32) -> i32 {\n    if a <= 0 || b <= 0 || c <= 0 || a + b <= c || a + c <= b || b + c <= a { return 0; }\n    if a == b && b == c { return 1; }\n    if a == b || a == c || b == c { return 2; }\n    3\n}",
        }),
    ]


def more_real_source_problems() -> list[Problem]:
    ex = lambda slug: source(
        "Exercism",
        slug,
        f"https://github.com/exercism/problem-specifications/tree/main/exercises/{slug}",
        "MIT",
    )
    lg = lambda slug: source("Luogu", slug, f"https://www.luogu.com.cn/problem/{slug}")
    return [
        Problem("ex_allergies_score_count", "Exercism Allergies Score Count", "Return how many of the standard 8 allergy flags are present in `score`.", ["Use bit positions 0 through 7 only.", "`score >= 0`."], "int", [{"name": "score", "type": "int"}], [case({"score": 0}, 0), case({"score": 34}, 2), case({"score": 255}, 8), case({"score": 509}, 7)], ex("allergies"), "easy", {
            "c": "int ex_allergies_score_count(int score) {\n    int count = 0;\n    for (int i = 0; i < 8; i++) if ((score & (1 << i)) != 0) count++;\n    return count;\n}",
            "java": "class ExAllergiesScoreCount {\n    public static int ex_allergies_score_count(int score) {\n        int count = 0;\n        for (int i = 0; i < 8; i++) if ((score & (1 << i)) != 0) count++;\n        return count;\n    }\n}",
            "rust": "pub fn ex_allergies_score_count(score: i32) -> i32 {\n    let mut count = 0;\n    let mut i = 0;\n    while i < 8 { if (score & (1 << i)) != 0 { count += 1; } i += 1; }\n    count\n}",
        }),
        Problem("ex_binary_search_index_csv", "Exercism Binary Search Index CSV", "Return the index of `target` in a sorted comma-separated array, or `-1` if absent.", ["The empty string represents an empty array.", "Values are sorted ascending."], "int", [{"name": "nums", "type": "string"}, {"name": "target", "type": "int"}], [case({"nums": "1,3,4,6,8,9,11", "target": 6}, 3), case({"nums": "1,3,4,6,8,9,11", "target": 7}, -1), case({"nums": "", "target": 1}, -1)], ex("binary-search"), "easy", {
            "c": "int ex_binary_search_index_csv(const char *nums, int target) {\n    if (nums[0] == '\\0') return -1;\n    int a[128], n = 0, i = 0;\n    while (nums[i] != '\\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } a[n++] = sign * v; if (nums[i] == ',') i++; }\n    int l = 0, r = n - 1;\n    while (l <= r) { int m = l + (r - l) / 2; if (a[m] == target) return m; if (a[m] < target) l = m + 1; else r = m - 1; }\n    return -1;\n}",
            "java": "class ExBinarySearchIndexCsv {\n    public static int ex_binary_search_index_csv(String nums, int target) {\n        if (nums.isEmpty()) return -1;\n        String[] parts = nums.split(\",\");\n        int l = 0, r = parts.length - 1;\n        while (l <= r) { int m = l + (r - l) / 2; int v = Integer.parseInt(parts[m]); if (v == target) return m; if (v < target) l = m + 1; else r = m - 1; }\n        return -1;\n    }\n}",
            "rust": "pub fn ex_binary_search_index_csv(nums: &str, target: i32) -> i32 {\n    if nums.is_empty() { return -1; }\n    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect();\n    let mut l = 0i32; let mut r = a.len() as i32 - 1;\n    while l <= r { let m = l + (r - l) / 2; let v = a[m as usize]; if v == target { return m; } if v < target { l = m + 1; } else { r = m - 1; } }\n    -1\n}",
        }),
        Problem("ex_raindrops_code", "Exercism Raindrops Code", "Return a bitmask for raindrop sounds: bit 0 for factor 3, bit 1 for factor 5, bit 2 for factor 7.", ["`n > 0`.", "This numeric code is a single-function rewrite of the raindrops exercise."], "int", [{"name": "n", "type": "int"}], [case({"n": 28}, 4), case({"n": 30}, 3), case({"n": 34}, 0)], ex("raindrops"), "easy", {
            "c": "int ex_raindrops_code(int n) {\n    int code = 0;\n    if (n % 3 == 0) code |= 1;\n    if (n % 5 == 0) code |= 2;\n    if (n % 7 == 0) code |= 4;\n    return code;\n}",
            "java": "class ExRaindropsCode {\n    public static int ex_raindrops_code(int n) {\n        int code = 0;\n        if (n % 3 == 0) code |= 1;\n        if (n % 5 == 0) code |= 2;\n        if (n % 7 == 0) code |= 4;\n        return code;\n    }\n}",
            "rust": "pub fn ex_raindrops_code(n: i32) -> i32 {\n    let mut code = 0;\n    if n % 3 == 0 { code |= 1; }\n    if n % 5 == 0 { code |= 2; }\n    if n % 7 == 0 { code |= 4; }\n    code\n}",
        }),
        Problem("ex_roman_value", "Exercism Roman Numerals Value", "Return the integer value of a valid Roman numeral string.", ["Input is a valid Roman numeral using `I,V,X,L,C,D,M`.", "Result fits in signed 32-bit integer range."], "int", [{"name": "s", "type": "string"}], [case({"s": "I"}, 1), case({"s": "IV"}, 4), case({"s": "MCMXC"}, 1990), case({"s": "MMVIII"}, 2008)], ex("roman-numerals"), "medium", {
            "c": "int ex_roman_value(const char *s) {\n    int sum = 0, prev = 0;\n    for (int i = 0; s[i] != '\\0'; i++) { char c = s[i]; int v = c == 'I' ? 1 : c == 'V' ? 5 : c == 'X' ? 10 : c == 'L' ? 50 : c == 'C' ? 100 : c == 'D' ? 500 : 1000; sum += v; if (prev < v) sum -= 2 * prev; prev = v; }\n    return sum;\n}",
            "java": "class ExRomanValue {\n    public static int ex_roman_value(String s) {\n        int sum = 0, prev = 0;\n        for (int i = 0; i < s.length(); i++) { char c = s.charAt(i); int v = c == 'I' ? 1 : c == 'V' ? 5 : c == 'X' ? 10 : c == 'L' ? 50 : c == 'C' ? 100 : c == 'D' ? 500 : 1000; sum += v; if (prev < v) sum -= 2 * prev; prev = v; }\n        return sum;\n    }\n}",
            "rust": "pub fn ex_roman_value(s: &str) -> i32 {\n    let mut sum = 0; let mut prev = 0;\n    for c in s.bytes() { let v = match c { b'I' => 1, b'V' => 5, b'X' => 10, b'L' => 50, b'C' => 100, b'D' => 500, _ => 1000 }; sum += v; if prev < v { sum -= 2 * prev; } prev = v; }\n    sum\n}",
        }),
        Problem("ex_sieve_prime_count", "Exercism Sieve Prime Count", "Return how many primes are less than or equal to `limit` using sieve-style marking.", ["`0 <= limit <= 1000`."], "int", [{"name": "limit", "type": "int"}], [case({"limit": 1}, 0), case({"limit": 10}, 4), case({"limit": 30}, 10)], ex("sieve"), "medium", {
            "c": "int ex_sieve_prime_count(int limit) {\n    int prime[1001];\n    for (int i = 0; i <= limit; i++) prime[i] = i >= 2;\n    for (int p = 2; p * p <= limit; p++) if (prime[p]) for (int q = p * p; q <= limit; q += p) prime[q] = 0;\n    int count = 0;\n    for (int i = 2; i <= limit; i++) if (prime[i]) count++;\n    return count;\n}",
            "java": "class ExSievePrimeCount {\n    public static int ex_sieve_prime_count(int limit) {\n        boolean[] prime = new boolean[limit + 1];\n        for (int i = 2; i <= limit; i++) prime[i] = true;\n        for (int p = 2; p * p <= limit; p++) if (prime[p]) for (int q = p * p; q <= limit; q += p) prime[q] = false;\n        int count = 0;\n        for (int i = 2; i <= limit; i++) if (prime[i]) count++;\n        return count;\n    }\n}",
            "rust": "pub fn ex_sieve_prime_count(limit: i32) -> i32 {\n    let mut prime = [false; 1001]; let mut i = 2; while i <= limit { prime[i as usize] = true; i += 1; }\n    let mut p = 2; while p * p <= limit { if prime[p as usize] { let mut q = p * p; while q <= limit { prime[q as usize] = false; q += p; } } p += 1; }\n    let mut count = 0; i = 2; while i <= limit { if prime[i as usize] { count += 1; } i += 1; }\n    count\n}",
        }),
        Problem("ex_prime_factors_count", "Exercism Prime Factors Count", "Return the number of prime factors of `n`, counted with multiplicity.", ["`n >= 1`."], "int", [{"name": "n", "type": "int"}], [case({"n": 1}, 0), case({"n": 12}, 3), case({"n": 60}, 4), case({"n": 97}, 1)], ex("prime-factors"), "medium", {
            "c": "int ex_prime_factors_count(int n) {\n    int count = 0;\n    for (int d = 2; d * d <= n; d++) while (n % d == 0) { count++; n /= d; }\n    if (n > 1) count++;\n    return count;\n}",
            "java": "class ExPrimeFactorsCount {\n    public static int ex_prime_factors_count(int n) {\n        int count = 0;\n        for (int d = 2; d * d <= n; d++) while (n % d == 0) { count++; n /= d; }\n        if (n > 1) count++;\n        return count;\n    }\n}",
            "rust": "pub fn ex_prime_factors_count(mut n: i32) -> i32 {\n    let mut count = 0; let mut d = 2;\n    while d * d <= n { while n % d == 0 { count += 1; n /= d; } d += 1; }\n    if n > 1 { count += 1; }\n    count\n}",
        }),
        Problem("ex_pangram_ascii", "Exercism Pangram ASCII", "Return true if `s` contains every English letter at least once, ignoring case.", ["Input is ASCII.", "Nonletters are ignored."], "bool", [{"name": "s", "type": "string"}], [case({"s": "The quick brown fox jumps over the lazy dog."}, True), case({"s": "abcdefghijklm ABCDEFGHIJKLM"}, False)], ex("pangram"), "easy", {
            "c": "int ex_pangram_ascii(const char *s) {\n    int mask = 0;\n    for (int i = 0; s[i] != '\\0'; i++) { char c = s[i]; if (c >= 'A' && c <= 'Z') c = (char)(c - 'A' + 'a'); if (c >= 'a' && c <= 'z') mask |= 1 << (c - 'a'); }\n    return mask == ((1 << 26) - 1);\n}",
            "java": "class ExPangramAscii {\n    public static boolean ex_pangram_ascii(String s) {\n        int mask = 0;\n        for (int i = 0; i < s.length(); i++) { char c = s.charAt(i); if (c >= 'A' && c <= 'Z') c = (char)(c - 'A' + 'a'); if (c >= 'a' && c <= 'z') mask |= 1 << (c - 'a'); }\n        return mask == (1 << 26) - 1;\n    }\n}",
            "rust": "pub fn ex_pangram_ascii(s: &str) -> bool {\n    let mut mask: i32 = 0;\n    for mut c in s.bytes() { if c >= b'A' && c <= b'Z' { c = c - b'A' + b'a'; } if c >= b'a' && c <= b'z' { mask |= 1 << (c - b'a'); } }\n    mask == (1 << 26) - 1\n}",
        }),
        Problem("ex_secret_handshake_code", "Exercism Secret Handshake Code", "Return a compact code for the secret-handshake actions selected by bits 0 through 3 of `n`.", ["Ignore reverse-order bit 4.", "`n >= 0`.", "Bit `i` contributes `1 << i` to the returned code."], "int", [{"name": "n", "type": "int"}], [case({"n": 1}, 1), case({"n": 9}, 9), case({"n": 19}, 3)], ex("secret-handshake"), "easy", {
            "c": "int ex_secret_handshake_code(int n) {\n    return n & 15;\n}",
            "java": "class ExSecretHandshakeCode {\n    public static int ex_secret_handshake_code(int n) {\n        return n & 15;\n    }\n}",
            "rust": "pub fn ex_secret_handshake_code(n: i32) -> i32 {\n    n & 15\n}",
        }),
        Problem("luogu_p5736_prime_count_csv", "Luogu P5736 Prime Count CSV", "Return how many comma-separated integers are prime.", ["The empty string represents an empty list.", "Values are nonnegative."], "int", [{"name": "nums", "type": "string"}], [case({"nums": "2,3,4,5,6"}, 3), case({"nums": ""}, 0), case({"nums": "1,9,11,13"}, 2)], lg("P5736"), "medium", {
            "c": "int luogu_p5736_prime_count_csv(const char *nums) {\n    if (nums[0] == '\\0') return 0;\n    int count = 0, i = 0;\n    while (nums[i] != '\\0') { int x = 0; while (nums[i] >= '0' && nums[i] <= '9') { x = x * 10 + nums[i] - '0'; i++; } int prime = x >= 2; for (int d = 2; d * d <= x; d++) if (x % d == 0) prime = 0; if (prime) count++; if (nums[i] == ',') i++; }\n    return count;\n}",
            "java": "class LuoguP5736PrimeCountCsv {\n    public static int luogu_p5736_prime_count_csv(String nums) {\n        if (nums.isEmpty()) return 0;\n        int count = 0;\n        for (String part : nums.split(\",\")) { int x = Integer.parseInt(part); boolean prime = x >= 2; for (int d = 2; d * d <= x; d++) if (x % d == 0) prime = false; if (prime) count++; }\n        return count;\n    }\n}",
            "rust": "pub fn luogu_p5736_prime_count_csv(nums: &str) -> i32 {\n    if nums.is_empty() { return 0; }\n    let mut count = 0;\n    for part in nums.split(',') { let x = part.parse::<i32>().unwrap(); let mut prime = x >= 2; let mut d = 2; while d * d <= x { if x % d == 0 { prime = false; } d += 1; } if prime { count += 1; } }\n    count\n}",
        }),
        Problem("luogu_p5737_leap_year_count", "Luogu P5737 Leap Year Count", "Return how many leap years are in the inclusive range `[start, end]`.", ["`start <= end`.", "Use Gregorian leap-year rules."], "int", [{"name": "start", "type": "int"}, {"name": "end", "type": "int"}], [case({"start": 2000, "end": 2004}, 2), case({"start": 1900, "end": 1900}, 0), case({"start": 1996, "end": 2000}, 2)], lg("P5737"), "easy", {
            "c": "int luogu_p5737_leap_year_count(int start, int end) {\n    int count = 0;\n    for (int y = start; y <= end; y++) if (y % 400 == 0 || (y % 4 == 0 && y % 100 != 0)) count++;\n    return count;\n}",
            "java": "class LuoguP5737LeapYearCount {\n    public static int luogu_p5737_leap_year_count(int start, int end) {\n        int count = 0;\n        for (int y = start; y <= end; y++) if (y % 400 == 0 || (y % 4 == 0 && y % 100 != 0)) count++;\n        return count;\n    }\n}",
            "rust": "pub fn luogu_p5737_leap_year_count(start: i32, end: i32) -> i32 {\n    let mut count = 0; let mut y = start;\n    while y <= end { if y % 400 == 0 || (y % 4 == 0 && y % 100 != 0) { count += 1; } y += 1; }\n    count\n}",
        }),
    ]


def more_real_source_problems_2() -> list[Problem]:
    ex = lambda slug: source(
        "Exercism",
        slug,
        f"https://github.com/exercism/problem-specifications/tree/main/exercises/{slug}",
        "MIT",
    )
    lg = lambda slug: source("Luogu", slug, f"https://www.luogu.com.cn/problem/{slug}")
    lc = lambda slug: source("LeetCode", slug, f"https://leetcode.com/problems/{slug}/")
    return [
        Problem("ex_perfect_number_code", "Exercism Perfect Number Code", "Classify `n` by aliquot sum: return `1` for perfect, `2` for abundant, and `3` for deficient.", ["`n > 0`.", "The aliquot sum is the sum of positive divisors strictly smaller than `n`."], "int", [{"name": "n", "type": "int"}], [case({"n": 6}, 1), case({"n": 12}, 2), case({"n": 8}, 3)], ex("perfect-numbers"), "easy", {
            "c": "int ex_perfect_number_code(int n) {\n    int sum = 0;\n    for (int d = 1; d < n; d++) if (n % d == 0) sum += d;\n    if (sum == n) return 1;\n    if (sum > n) return 2;\n    return 3;\n}",
            "java": "class ExPerfectNumberCode {\n    public static int ex_perfect_number_code(int n) {\n        int sum = 0;\n        for (int d = 1; d < n; d++) if (n % d == 0) sum += d;\n        if (sum == n) return 1;\n        if (sum > n) return 2;\n        return 3;\n    }\n}",
            "rust": "pub fn ex_perfect_number_code(n: i32) -> i32 {\n    let mut sum = 0;\n    let mut d = 1;\n    while d < n { if n % d == 0 { sum += d; } d += 1; }\n    if sum == n { return 1; }\n    if sum > n { return 2; }\n    3\n}",
        }),
        Problem("ex_pascals_triangle_value", "Exercism Pascal Triangle Value", "Return the value at zero-based `row` and `col` in Pascal's triangle.", ["`0 <= col <= row <= 30`.", "The result fits in signed 32-bit integer range."], "int", [{"name": "row", "type": "int"}, {"name": "col", "type": "int"}], [case({"row": 0, "col": 0}, 1), case({"row": 4, "col": 2}, 6), case({"row": 6, "col": 3}, 20)], ex("pascals-triangle"), "medium", {
            "c": "int ex_pascals_triangle_value(int row, int col) {\n    int v[31][31] = {{0}};\n    for (int i = 0; i <= row; i++) { v[i][0] = 1; v[i][i] = 1; for (int j = 1; j < i; j++) v[i][j] = v[i - 1][j - 1] + v[i - 1][j]; }\n    return v[row][col];\n}",
            "java": "class ExPascalsTriangleValue {\n    public static int ex_pascals_triangle_value(int row, int col) {\n        int[][] v = new int[row + 1][row + 1];\n        for (int i = 0; i <= row; i++) { v[i][0] = 1; v[i][i] = 1; for (int j = 1; j < i; j++) v[i][j] = v[i - 1][j - 1] + v[i - 1][j]; }\n        return v[row][col];\n    }\n}",
            "rust": "pub fn ex_pascals_triangle_value(row: i32, col: i32) -> i32 {\n    let mut v = [[0i32; 31]; 31];\n    let mut i = 0;\n    while i <= row { v[i as usize][0] = 1; v[i as usize][i as usize] = 1; let mut j = 1; while j < i { v[i as usize][j as usize] = v[(i - 1) as usize][(j - 1) as usize] + v[(i - 1) as usize][j as usize]; j += 1; } i += 1; }\n    v[row as usize][col as usize]\n}",
        }),
        Problem("ex_pythagorean_triplet_product", "Exercism Pythagorean Triplet Product", "Return the product `a*b*c` for the first Pythagorean triplet with `a < b < c` and `a+b+c == sum`, or `0` if none exists.", ["`sum > 0`.", "The product fits in signed 32-bit integer range."], "int", [{"name": "sum", "type": "int"}], [case({"sum": 12}, 60), case({"sum": 30}, 780), case({"sum": 11}, 0)], ex("pythagorean-triplet"), "medium", {
            "c": "int ex_pythagorean_triplet_product(int sum) {\n    for (int a = 1; a < sum; a++) for (int b = a + 1; b < sum; b++) { int c = sum - a - b; if (b < c && a * a + b * b == c * c) return a * b * c; }\n    return 0;\n}",
            "java": "class ExPythagoreanTripletProduct {\n    public static int ex_pythagorean_triplet_product(int sum) {\n        for (int a = 1; a < sum; a++) for (int b = a + 1; b < sum; b++) { int c = sum - a - b; if (b < c && a * a + b * b == c * c) return a * b * c; }\n        return 0;\n    }\n}",
            "rust": "pub fn ex_pythagorean_triplet_product(sum: i32) -> i32 {\n    let mut a = 1;\n    while a < sum { let mut b = a + 1; while b < sum { let c = sum - a - b; if b < c && a * a + b * b == c * c { return a * b * c; } b += 1; } a += 1; }\n    0\n}",
        }),
        Problem("ex_protein_stop_index", "Exercism Protein Stop Index", "Return the zero-based codon index of the first stop codon in an RNA string, or the number of codons if no stop codon appears.", ["RNA length is a multiple of 3.", "Stop codons are `UAA`, `UAG`, and `UGA`."], "int", [{"name": "rna", "type": "string"}], [case({"rna": "AUGUUUUAA"}, 2), case({"rna": "AUGUUUUGG"}, 3), case({"rna": "UAA"}, 0)], ex("protein-translation"), "medium", {
            "c": "int ex_protein_stop_index(const char *rna) {\n    int idx = 0;\n    for (int i = 0; rna[i] != '\\0'; i += 3) { if (rna[i] == 'U' && ((rna[i + 1] == 'A' && (rna[i + 2] == 'A' || rna[i + 2] == 'G')) || (rna[i + 1] == 'G' && rna[i + 2] == 'A'))) return idx; idx++; }\n    return idx;\n}",
            "java": "class ExProteinStopIndex {\n    public static int ex_protein_stop_index(String rna) {\n        int idx = 0;\n        for (int i = 0; i < rna.length(); i += 3) { char a = rna.charAt(i), b = rna.charAt(i + 1), c = rna.charAt(i + 2); if (a == 'U' && ((b == 'A' && (c == 'A' || c == 'G')) || (b == 'G' && c == 'A'))) return idx; idx++; }\n        return idx;\n    }\n}",
            "rust": "pub fn ex_protein_stop_index(rna: &str) -> i32 {\n    let b = rna.as_bytes(); let mut idx = 0; let mut i = 0usize;\n    while i < b.len() { if b[i] == b'U' && ((b[i + 1] == b'A' && (b[i + 2] == b'A' || b[i + 2] == b'G')) || (b[i + 1] == b'G' && b[i + 2] == b'A')) { return idx; } idx += 1; i += 3; }\n    idx\n}",
        }),
        Problem("ex_resistor_color_duo_value", "Exercism Resistor Color Duo Value", "Return the two-digit resistor value formed by the first two color codes.", ["Colors are encoded as digits `0..9` in the standard resistor-color order.", "The result is `10 * first + second`."], "int", [{"name": "first", "type": "int"}, {"name": "second", "type": "int"}], [case({"first": 0, "second": 1}, 1), case({"first": 2, "second": 3}, 23), case({"first": 9, "second": 9}, 99)], ex("resistor-color-duo"), "easy", {
            "c": "int ex_resistor_color_duo_value(int first, int second) {\n    return first * 10 + second;\n}",
            "java": "class ExResistorColorDuoValue {\n    public static int ex_resistor_color_duo_value(int first, int second) {\n        return first * 10 + second;\n    }\n}",
            "rust": "pub fn ex_resistor_color_duo_value(first: i32, second: i32) -> i32 {\n    first * 10 + second\n}",
        }),
        Problem("ex_series_largest_digit_sum", "Exercism Series Largest Digit Sum", "Return the largest sum of `span` adjacent digits in `digits`.", ["`digits` contains decimal digits only.", "`0 <= span <= length(digits)`.", "An empty span has sum `0`."], "int", [{"name": "digits", "type": "string"}, {"name": "span", "type": "int"}], [case({"digits": "01234", "span": 2}, 7), case({"digits": "999", "span": 2}, 18), case({"digits": "12345", "span": 0}, 0)], ex("series"), "easy", {
            "c": "int ex_series_largest_digit_sum(const char *digits, int span) {\n    int n = 0; while (digits[n] != '\\0') n++;\n    if (span == 0) return 0;\n    int best = 0;\n    for (int i = 0; i + span <= n; i++) { int sum = 0; for (int j = 0; j < span; j++) sum += digits[i + j] - '0'; if (sum > best) best = sum; }\n    return best;\n}",
            "java": "class ExSeriesLargestDigitSum {\n    public static int ex_series_largest_digit_sum(String digits, int span) {\n        if (span == 0) return 0;\n        int best = 0;\n        for (int i = 0; i + span <= digits.length(); i++) { int sum = 0; for (int j = 0; j < span; j++) sum += digits.charAt(i + j) - '0'; if (sum > best) best = sum; }\n        return best;\n    }\n}",
            "rust": "pub fn ex_series_largest_digit_sum(digits: &str, span: i32) -> i32 {\n    if span == 0 { return 0; }\n    let b = digits.as_bytes(); let sp = span as usize; let mut best = 0; let mut i = 0usize;\n    while i + sp <= b.len() { let mut sum = 0; let mut j = 0usize; while j < sp { sum += (b[i + j] - b'0') as i32; j += 1; } if sum > best { best = sum; } i += 1; }\n    best\n}",
        }),
        Problem("lc_min_path_sum_grid2x3", "LC Min Path Sum 2x3", "Return the minimum path sum from top-left to bottom-right in a 2x3 grid moving only right or down.", ["Grid values are supplied row-major.", "All values are nonnegative."], "int", [{"name": "a00", "type": "int"}, {"name": "a01", "type": "int"}, {"name": "a02", "type": "int"}, {"name": "a10", "type": "int"}, {"name": "a11", "type": "int"}, {"name": "a12", "type": "int"}], [case({"a00": 1, "a01": 3, "a02": 1, "a10": 1, "a11": 5, "a12": 1}, 6), case({"a00": 1, "a01": 2, "a02": 3, "a10": 4, "a11": 5, "a12": 6}, 12)], lc("minimum-path-sum"), "medium", {
            "c": "int lc_min_path_sum_grid2x3(int a00, int a01, int a02, int a10, int a11, int a12) {\n    int d00 = a00;\n    int d01 = d00 + a01;\n    int d02 = d01 + a02;\n    int d10 = d00 + a10;\n    int d11 = (d01 < d10 ? d01 : d10) + a11;\n    int d12 = (d02 < d11 ? d02 : d11) + a12;\n    return d12;\n}",
            "java": "class LcMinPathSumGrid2x3 {\n    public static int lc_min_path_sum_grid2x3(int a00, int a01, int a02, int a10, int a11, int a12) {\n        int d00 = a00;\n        int d01 = d00 + a01;\n        int d02 = d01 + a02;\n        int d10 = d00 + a10;\n        int d11 = (d01 < d10 ? d01 : d10) + a11;\n        int d12 = (d02 < d11 ? d02 : d11) + a12;\n        return d12;\n    }\n}",
            "rust": "pub fn lc_min_path_sum_grid2x3(a00: i32, a01: i32, a02: i32, a10: i32, a11: i32, a12: i32) -> i32 {\n    let d00 = a00;\n    let d01 = d00 + a01;\n    let d02 = d01 + a02;\n    let d10 = d00 + a10;\n    let d11 = if d01 < d10 { d01 } else { d10 } + a11;\n    let d12 = if d02 < d11 { d02 } else { d11 } + a12;\n    d12\n}",
        }),
        Problem("lc_partition_equal_subset_csv", "LC Partition Equal Subset CSV", "Return true if comma-separated positive integers can be partitioned into two subsets with equal sum.", ["The empty string returns false.", "The total sum is at most `2000`."], "bool", [{"name": "nums", "type": "string"}], [case({"nums": "1,5,11,5"}, True), case({"nums": "1,2,3,5"}, False), case({"nums": ""}, False)], lc("partition-equal-subset-sum"), "medium", {
            "c": "int lc_partition_equal_subset_csv(const char *nums) {\n    if (nums[0] == '\\0') return 0;\n    int a[128], n = 0, sum = 0, i = 0;\n    while (nums[i] != '\\0') { int v = 0; while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } a[n++] = v; sum += v; if (nums[i] == ',') i++; }\n    if (sum % 2 != 0) return 0;\n    int target = sum / 2; int dp[2001] = {0}; dp[0] = 1;\n    for (int k = 0; k < n; k++) for (int s = target; s >= a[k]; s--) if (dp[s - a[k]]) dp[s] = 1;\n    return dp[target];\n}",
            "java": "class LcPartitionEqualSubsetCsv {\n    public static boolean lc_partition_equal_subset_csv(String nums) {\n        if (nums.isEmpty()) return false;\n        String[] parts = nums.split(\",\"); int[] a = new int[parts.length]; int sum = 0;\n        for (int i = 0; i < parts.length; i++) { a[i] = Integer.parseInt(parts[i]); sum += a[i]; }\n        if (sum % 2 != 0) return false;\n        int target = sum / 2; boolean[] dp = new boolean[target + 1]; dp[0] = true;\n        for (int v : a) for (int s = target; s >= v; s--) if (dp[s - v]) dp[s] = true;\n        return dp[target];\n    }\n}",
            "rust": "pub fn lc_partition_equal_subset_csv(nums: &str) -> bool {\n    if nums.is_empty() { return false; }\n    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut sum = 0; for &v in &a { sum += v; }\n    if sum % 2 != 0 { return false; }\n    let target = (sum / 2) as usize; let mut dp = vec![false; target + 1]; dp[0] = true;\n    for &v in &a { let vv = v as usize; let mut s = target; while s >= vv { if dp[s - vv] { dp[s] = true; } if s == 0 { break; } s -= 1; } }\n    dp[target]\n}",
        }),
        Problem("luogu_p5740_best_total_score", "Luogu P5740 Best Total Score", "Return the maximum total score among students encoded as triples `chinese,math,english;...`.", ["The empty string returns `0`.", "Scores are nonnegative integers."], "int", [{"name": "rows", "type": "string"}], [case({"rows": "80,90,70;100,60,70"}, 250), case({"rows": ""}, 0), case({"rows": "1,2,3;4,5,6"}, 15)], lg("P5740"), "easy", {
            "c": "int luogu_p5740_best_total_score(const char *rows) {\n    int best = 0, i = 0;\n    while (rows[i] != '\\0') { int total = 0; for (int k = 0; k < 3; k++) { int v = 0; while (rows[i] >= '0' && rows[i] <= '9') { v = v * 10 + rows[i] - '0'; i++; } total += v; if (rows[i] == ',') i++; } if (total > best) best = total; if (rows[i] == ';') i++; }\n    return best;\n}",
            "java": "class LuoguP5740BestTotalScore {\n    public static int luogu_p5740_best_total_score(String rows) {\n        if (rows.isEmpty()) return 0;\n        int best = 0;\n        for (String row : rows.split(\";\")) { String[] p = row.split(\",\"); int total = Integer.parseInt(p[0]) + Integer.parseInt(p[1]) + Integer.parseInt(p[2]); if (total > best) best = total; }\n        return best;\n    }\n}",
            "rust": "pub fn luogu_p5740_best_total_score(rows: &str) -> i32 {\n    if rows.is_empty() { return 0; }\n    let mut best = 0;\n    for row in rows.split(';') { let vals: Vec<i32> = row.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let total = vals[0] + vals[1] + vals[2]; if total > best { best = total; } }\n    best\n}",
        }),
        Problem("luogu_p5728_similar_triples_count", "Luogu P5728 Similar Triples Count", "Count pairs of students whose three subject scores differ by at most 5 each and total scores differ by at most 10.", ["Rows are encoded as `a,b,c;a,b,c;...`.", "The empty string returns `0`."], "int", [{"name": "rows", "type": "string"}], [case({"rows": "90,90,90;92,93,91;80,80,80"}, 1), case({"rows": ""}, 0), case({"rows": "1,1,1;2,2,2;3,3,3"}, 3)], lg("P5728"), "medium", {
            "c": "int luogu_p5728_similar_triples_count(const char *rows) {\n    if (rows[0] == '\\0') return 0;\n    int a[64][3], n = 0, i = 0;\n    while (rows[i] != '\\0') { for (int k = 0; k < 3; k++) { int v = 0; while (rows[i] >= '0' && rows[i] <= '9') { v = v * 10 + rows[i] - '0'; i++; } a[n][k] = v; if (rows[i] == ',') i++; } n++; if (rows[i] == ';') i++; }\n    int count = 0;\n    for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) { int ok = 1; for (int k = 0; k < 3; k++) { int d = a[x][k] - a[y][k]; if (d < 0) d = -d; if (d > 5) ok = 0; } int tx = a[x][0] + a[x][1] + a[x][2], ty = a[y][0] + a[y][1] + a[y][2], td = tx - ty; if (td < 0) td = -td; if (ok && td <= 10) count++; }\n    return count;\n}",
            "java": "class LuoguP5728SimilarTriplesCount {\n    public static int luogu_p5728_similar_triples_count(String rows) {\n        if (rows.isEmpty()) return 0;\n        String[] rs = rows.split(\";\"); int[][] a = new int[rs.length][3];\n        for (int i = 0; i < rs.length; i++) { String[] p = rs[i].split(\",\"); for (int k = 0; k < 3; k++) a[i][k] = Integer.parseInt(p[k]); }\n        int count = 0;\n        for (int x = 0; x < a.length; x++) for (int y = x + 1; y < a.length; y++) { boolean ok = true; for (int k = 0; k < 3; k++) if (Math.abs(a[x][k] - a[y][k]) > 5) ok = false; int tx = a[x][0] + a[x][1] + a[x][2], ty = a[y][0] + a[y][1] + a[y][2]; if (ok && Math.abs(tx - ty) <= 10) count++; }\n        return count;\n    }\n}",
            "rust": "pub fn luogu_p5728_similar_triples_count(rows: &str) -> i32 {\n    if rows.is_empty() { return 0; }\n    let a: Vec<Vec<i32>> = rows.split(';').map(|row| row.split(',').map(|x| x.parse::<i32>().unwrap()).collect()).collect();\n    let mut count = 0;\n    let mut x = 0usize; while x < a.len() { let mut y = x + 1; while y < a.len() { let mut ok = true; let mut k = 0usize; while k < 3 { let mut d = a[x][k] - a[y][k]; if d < 0 { d = -d; } if d > 5 { ok = false; } k += 1; } let tx = a[x][0] + a[x][1] + a[x][2]; let ty = a[y][0] + a[y][1] + a[y][2]; let mut td = tx - ty; if td < 0 { td = -td; } if ok && td <= 10 { count += 1; } y += 1; } x += 1; }\n    count\n}",
        }),
    ]


def more_real_source_problems_3() -> list[Problem]:
    lc = lambda slug: source("LeetCode", slug, f"https://leetcode.com/problems/{slug}/")
    lg = lambda slug: source("Luogu", slug, f"https://www.luogu.com.cn/problem/{slug}")
    ex = lambda slug: source(
        "Exercism",
        slug,
        f"https://github.com/exercism/problem-specifications/tree/main/exercises/{slug}",
        "MIT",
    )
    return [
        Problem("lc_product_except_self_sum_csv", "LC Product Except Self Sum CSV", "Compute product-except-self for each comma-separated integer and return the sum of the output array.", ["`nums` is nonempty.", "No division is used.", "Intermediate products fit in signed 32-bit integer range."], "int", [{"name": "nums", "type": "string"}], [case({"nums": "1,2,3,4"}, 50), case({"nums": "-1,1,0,-3,3"}, 0), case({"nums": "2,3"}, 5)], lc("product-of-array-except-self"), "medium", {
            "c": "int lc_product_except_self_sum_csv(const char *nums) {\n    int a[128], n = 0, i = 0;\n    while (nums[i] != '\\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } a[n++] = sign * v; if (nums[i] == ',') i++; }\n    int left[128], right[128]; left[0] = 1; for (int j = 1; j < n; j++) left[j] = left[j - 1] * a[j - 1]; right[n - 1] = 1; for (int j = n - 2; j >= 0; j--) right[j] = right[j + 1] * a[j + 1];\n    int sum = 0; for (int j = 0; j < n; j++) sum += left[j] * right[j];\n    return sum;\n}",
            "java": "class LcProductExceptSelfSumCsv {\n    public static int lc_product_except_self_sum_csv(String nums) {\n        String[] parts = nums.split(\",\"); int n = parts.length; int[] a = new int[n];\n        for (int i = 0; i < n; i++) a[i] = Integer.parseInt(parts[i]);\n        int[] left = new int[n], right = new int[n]; left[0] = 1; for (int i = 1; i < n; i++) left[i] = left[i - 1] * a[i - 1]; right[n - 1] = 1; for (int i = n - 2; i >= 0; i--) right[i] = right[i + 1] * a[i + 1];\n        int sum = 0; for (int i = 0; i < n; i++) sum += left[i] * right[i];\n        return sum;\n    }\n}",
            "rust": "pub fn lc_product_except_self_sum_csv(nums: &str) -> i32 {\n    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let n = a.len();\n    let mut left = vec![1; n]; let mut right = vec![1; n]; let mut i = 1usize; while i < n { left[i] = left[i - 1] * a[i - 1]; i += 1; } if n > 0 { let mut j = n - 1; while j > 0 { right[j - 1] = right[j] * a[j]; j -= 1; } }\n    let mut sum = 0; i = 0; while i < n { sum += left[i] * right[i]; i += 1; }\n    sum\n}",
        }),
        Problem("lc_maximal_square_area_rows", "LC Maximal Square Area Rows", "Given binary matrix rows separated by semicolons, return the area of the largest all-1 square.", ["Rows contain only `0` and `1`.", "All rows have the same positive length.", "The empty string returns `0`."], "int", [{"name": "rows", "type": "string"}], [case({"rows": "10100;10111;11111;10010"}, 4), case({"rows": "01;10"}, 1), case({"rows": ""}, 0)], lc("maximal-square"), "medium", {
            "c": "int lc_maximal_square_area_rows(const char *rows) {\n    if (rows[0] == '\\0') return 0;\n    int a[64][64], r = 0, c = 0, cols = 0, i = 0;\n    while (rows[i] != '\\0') { c = 0; while (rows[i] == '0' || rows[i] == '1') { a[r][c++] = rows[i++] - '0'; } if (cols == 0) cols = c; r++; if (rows[i] == ';') i++; }\n    int dp[65][65] = {{0}}, best = 0;\n    for (int x = 1; x <= r; x++) for (int y = 1; y <= cols; y++) if (a[x - 1][y - 1]) { int m = dp[x - 1][y] < dp[x][y - 1] ? dp[x - 1][y] : dp[x][y - 1]; if (dp[x - 1][y - 1] < m) m = dp[x - 1][y - 1]; dp[x][y] = m + 1; if (dp[x][y] > best) best = dp[x][y]; }\n    return best * best;\n}",
            "java": "class LcMaximalSquareAreaRows {\n    public static int lc_maximal_square_area_rows(String rows) {\n        if (rows.isEmpty()) return 0;\n        String[] rs = rows.split(\";\"); int r = rs.length, c = rs[0].length(); int[][] dp = new int[r + 1][c + 1]; int best = 0;\n        for (int i = 1; i <= r; i++) for (int j = 1; j <= c; j++) if (rs[i - 1].charAt(j - 1) == '1') { int m = Math.min(dp[i - 1][j], dp[i][j - 1]); m = Math.min(m, dp[i - 1][j - 1]); dp[i][j] = m + 1; if (dp[i][j] > best) best = dp[i][j]; }\n        return best * best;\n    }\n}",
            "rust": "pub fn lc_maximal_square_area_rows(rows: &str) -> i32 {\n    if rows.is_empty() { return 0; }\n    let rs: Vec<&[u8]> = rows.split(';').map(|s| s.as_bytes()).collect(); let r = rs.len(); let c = rs[0].len(); let mut dp = vec![vec![0i32; c + 1]; r + 1]; let mut best = 0;\n    let mut i = 1usize; while i <= r { let mut j = 1usize; while j <= c { if rs[i - 1][j - 1] == b'1' { let mut m = if dp[i - 1][j] < dp[i][j - 1] { dp[i - 1][j] } else { dp[i][j - 1] }; if dp[i - 1][j - 1] < m { m = dp[i - 1][j - 1]; } dp[i][j] = m + 1; if dp[i][j] > best { best = dp[i][j]; } } j += 1; } i += 1; }\n    best * best\n}",
        }),
        Problem("lc_find_peak_index_csv", "LC Find Peak Index CSV", "Return an index `i` such that `nums[i]` is greater than its neighbors; endpoints only need their one neighbor.", ["`nums` is nonempty.", "Adjacent values are distinct in the supplied tests."], "int", [{"name": "nums", "type": "string"}], [case({"nums": "1,2,3,1"}, 2), case({"nums": "1,2,1,3,5,6,4"}, 1), case({"nums": "1"}, 0)], lc("find-peak-element"), "medium", {
            "c": "int lc_find_peak_index_csv(const char *nums) {\n    int a[128], n = 0, i = 0;\n    while (nums[i] != '\\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } a[n++] = sign * v; if (nums[i] == ',') i++; }\n    int l = 0, r = n - 1;\n    while (l < r) { int m = l + (r - l) / 2; if (a[m] < a[m + 1]) l = m + 1; else r = m; }\n    return l;\n}",
            "java": "class LcFindPeakIndexCsv {\n    public static int lc_find_peak_index_csv(String nums) {\n        String[] p = nums.split(\",\"); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]);\n        int l = 0, r = a.length - 1; while (l < r) { int m = l + (r - l) / 2; if (a[m] < a[m + 1]) l = m + 1; else r = m; }\n        return l;\n    }\n}",
            "rust": "pub fn lc_find_peak_index_csv(nums: &str) -> i32 {\n    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut l = 0usize; let mut r = a.len() - 1;\n    while l < r { let m = l + (r - l) / 2; if a[m] < a[m + 1] { l = m + 1; } else { r = m; } }\n    l as i32\n}",
        }),
        Problem("lc_min_stack_final_min_csv", "LC Min Stack Final Min CSV", "Simulate stack operations and return the minimum value after all operations.", ["Operations are semicolon-separated: `push:x` or `pop`.", "The final stack is nonempty.", "Pop operations are valid."], "int", [{"name": "ops", "type": "string"}], [case({"ops": "push:-2;push:0;push:-3;pop"}, -2), case({"ops": "push:5;push:3;push:7"}, 3), case({"ops": "push:2;push:1;pop"}, 2)], lc("min-stack"), "medium", {
            "c": "int lc_min_stack_final_min_csv(const char *ops) {\n    int st[128], top = 0, i = 0;\n    while (ops[i] != '\\0') { if (ops[i] == 'p' && ops[i + 1] == 'u') { while (ops[i] != ':') i++; i++; int sign = 1, v = 0; if (ops[i] == '-') { sign = -1; i++; } while (ops[i] >= '0' && ops[i] <= '9') { v = v * 10 + ops[i] - '0'; i++; } st[top++] = sign * v; } else { top--; while (ops[i] != '\\0' && ops[i] != ';') i++; } if (ops[i] == ';') i++; }\n    int min = st[0]; for (int j = 1; j < top; j++) if (st[j] < min) min = st[j];\n    return min;\n}",
            "java": "class LcMinStackFinalMinCsv {\n    public static int lc_min_stack_final_min_csv(String ops) {\n        int[] st = new int[128]; int top = 0;\n        for (String op : ops.split(\";\")) { if (op.startsWith(\"push:\")) st[top++] = Integer.parseInt(op.substring(5)); else top--; }\n        int min = st[0]; for (int i = 1; i < top; i++) if (st[i] < min) min = st[i];\n        return min;\n    }\n}",
            "rust": "pub fn lc_min_stack_final_min_csv(ops: &str) -> i32 {\n    let mut st: Vec<i32> = Vec::new();\n    for op in ops.split(';') { if op.starts_with(\"push:\") { st.push(op[5..].parse::<i32>().unwrap()); } else { st.pop(); } }\n    let mut min = st[0]; for &v in &st { if v < min { min = v; } }\n    min\n}",
        }),
        Problem("luogu_p5741_rival_pair_count", "Luogu P5741 Rival Pair Count", "Given semicolon-separated student score triples, count pairs whose three subject differences are all at most 5 and total-score difference is at most 10.", ["Each record is `name:chinese,math,english`.", "Names are ignored for the count.", "There are at most 128 records."], "int", [{"name": "students", "type": "string"}], [case({"students": "a:100,100,100;b:104,101,96;c:120,100,100"}, 1), case({"students": "aa:90,91,92;bb:95,96,97;cc:80,80,80"}, 1), case({"students": "x:100,100,100;y:106,100,100"}, 0)], lg("P5741"), "easy", {
            "c": "int luogu_p5741_rival_pair_count(const char *students) {\n    int s[128][3], n = 0, i = 0;\n    while (students[i] != '\\0') {\n        while (students[i] != ':' && students[i] != '\\0') i++;\n        if (students[i] == ':') i++;\n        for (int k = 0; k < 3; k++) { int v = 0; while (students[i] >= '0' && students[i] <= '9') { v = v * 10 + students[i] - '0'; i++; } s[n][k] = v; if (students[i] == ',') i++; }\n        n++; if (students[i] == ';') i++;\n    }\n    int ans = 0;\n    for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) {\n        int ok = 1, suma = 0, sumb = 0;\n        for (int k = 0; k < 3; k++) { int d = s[a][k] - s[b][k]; if (d < 0) d = -d; if (d > 5) ok = 0; suma += s[a][k]; sumb += s[b][k]; }\n        int td = suma - sumb; if (td < 0) td = -td; if (ok && td <= 10) ans++;\n    }\n    return ans;\n}",
            "java": "class LuoguP5741RivalPairCount {\n    public static int luogu_p5741_rival_pair_count(String students) {\n        String[] rows = students.split(\";\"); int n = rows.length; int[][] s = new int[n][3];\n        for (int i = 0; i < n; i++) { String[] parts = rows[i].substring(rows[i].indexOf(':') + 1).split(\",\"); for (int k = 0; k < 3; k++) s[i][k] = Integer.parseInt(parts[k]); }\n        int ans = 0;\n        for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) { boolean ok = true; int suma = 0, sumb = 0; for (int k = 0; k < 3; k++) { if (Math.abs(s[a][k] - s[b][k]) > 5) ok = false; suma += s[a][k]; sumb += s[b][k]; } if (ok && Math.abs(suma - sumb) <= 10) ans++; }\n        return ans;\n    }\n}",
            "rust": "pub fn luogu_p5741_rival_pair_count(students: &str) -> i32 {\n    let mut s: Vec<[i32; 3]> = Vec::new();\n    for row in students.split(';') { let scores = row.split(':').nth(1).unwrap(); let vals: Vec<i32> = scores.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); s.push([vals[0], vals[1], vals[2]]); }\n    let mut ans = 0;\n    let mut a = 0usize; while a < s.len() { let mut b = a + 1; while b < s.len() { let mut ok = true; let mut suma = 0; let mut sumb = 0; let mut k = 0usize; while k < 3 { if (s[a][k] - s[b][k]).abs() > 5 { ok = false; } suma += s[a][k]; sumb += s[b][k]; k += 1; } if ok && (suma - sumb).abs() <= 10 { ans += 1; } b += 1; } a += 1; }\n    ans\n}",
        }),
        Problem("luogu_p5744_training_after_years", "Luogu P5744 Training After Years", "After `years` yearly updates, return `age + score` where age increases by 1 each year and score increases by 20 percent capped at 600.", ["`years >= 0`.", "Use truncating integer arithmetic after each yearly score update."], "int", [{"name": "age", "type": "int"}, {"name": "score", "type": "int"}, {"name": "years", "type": "int"}], [case({"age": 10, "score": 100, "years": 1}, 131), case({"age": 10, "score": 500, "years": 2}, 612), case({"age": 20, "score": 600, "years": 3}, 623)], lg("P5744"), "easy", {
            "c": "int luogu_p5744_training_after_years(int age, int score, int years) {\n    for (int i = 0; i < years; i++) { age++; score = score * 120 / 100; if (score > 600) score = 600; }\n    return age + score;\n}",
            "java": "class LuoguP5744TrainingAfterYears {\n    public static int luogu_p5744_training_after_years(int age, int score, int years) {\n        for (int i = 0; i < years; i++) { age++; score = score * 120 / 100; if (score > 600) score = 600; }\n        return age + score;\n    }\n}",
            "rust": "pub fn luogu_p5744_training_after_years(mut age: i32, mut score: i32, years: i32) -> i32 {\n    let mut i = 0;\n    while i < years { age += 1; score = score * 120 / 100; if score > 600 { score = 600; } i += 1; }\n    age + score\n}",
        }),
    ]


def more_real_source_problems_4() -> list[Problem]:
    lc = lambda slug: source("LeetCode", slug, f"https://leetcode.com/problems/{slug}/")
    lg = lambda slug: source("Luogu", slug, f"https://www.luogu.com.cn/problem/{slug}")
    ex = lambda slug: source(
        "Exercism",
        slug,
        f"https://github.com/exercism/problem-specifications/tree/main/exercises/{slug}",
        "MIT",
    )
    return [
        Problem("lc_coin_change_min_csv", "LC Coin Change Min CSV", "Return the fewest coins needed to make `amount`, or `-1` if impossible.", ["`coins` is a nonempty comma-separated list of positive integers.", "`amount >= 0`.", "This is the standard unbounded coin-change objective."], "int", [{"name": "coins", "type": "string"}, {"name": "amount", "type": "int"}], [case({"coins": "1,2,5", "amount": 11}, 3), case({"coins": "2", "amount": 3}, -1), case({"coins": "1", "amount": 0}, 0)], lc("coin-change"), "medium", {
            "c": "int lc_coin_change_min_csv(const char *coins, int amount) {\n    int c[128], n = 0, i = 0;\n    while (coins[i] != '\\0') { int v = 0; while (coins[i] >= '0' && coins[i] <= '9') { v = v * 10 + coins[i] - '0'; i++; } c[n++] = v; if (coins[i] == ',') i++; }\n    int dp[2001]; for (int j = 0; j <= amount; j++) dp[j] = 1000000; dp[0] = 0;\n    for (int j = 1; j <= amount; j++) for (int k = 0; k < n; k++) if (j >= c[k] && dp[j - c[k]] + 1 < dp[j]) dp[j] = dp[j - c[k]] + 1;\n    return dp[amount] >= 1000000 ? -1 : dp[amount];\n}",
            "java": "class LcCoinChangeMinCsv {\n    public static int lc_coin_change_min_csv(String coins, int amount) {\n        String[] parts = coins.split(\",\"); int[] c = new int[parts.length]; for (int i = 0; i < parts.length; i++) c[i] = Integer.parseInt(parts[i]);\n        int[] dp = new int[amount + 1]; for (int i = 1; i <= amount; i++) dp[i] = 1000000;\n        for (int i = 1; i <= amount; i++) for (int coin : c) if (i >= coin && dp[i - coin] + 1 < dp[i]) dp[i] = dp[i - coin] + 1;\n        return dp[amount] >= 1000000 ? -1 : dp[amount];\n    }\n}",
            "rust": "pub fn lc_coin_change_min_csv(coins: &str, amount: i32) -> i32 {\n    let c: Vec<i32> = coins.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut dp = vec![1000000; (amount + 1) as usize]; dp[0] = 0;\n    let mut i = 1; while i <= amount { for &coin in &c { if i >= coin { let cand = dp[(i - coin) as usize] + 1; if cand < dp[i as usize] { dp[i as usize] = cand; } } } i += 1; }\n    if dp[amount as usize] >= 1000000 { -1 } else { dp[amount as usize] }\n}",
        }),
        Problem("lc_lis_length_csv", "LC Longest Increasing Subsequence Length CSV", "Return the length of the longest strictly increasing subsequence in comma-separated integers.", ["`nums` is nonempty.", "The answer fits in signed 32-bit integer range."], "int", [{"name": "nums", "type": "string"}], [case({"nums": "10,9,2,5,3,7,101,18"}, 4), case({"nums": "0,1,0,3,2,3"}, 4), case({"nums": "7,7,7,7"}, 1)], lc("longest-increasing-subsequence"), "medium", {
            "c": "int lc_lis_length_csv(const char *nums) {\n    int a[256], n = 0, i = 0;\n    while (nums[i] != '\\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } a[n++] = sign * v; if (nums[i] == ',') i++; }\n    int dp[256], best = 1; for (int x = 0; x < n; x++) { dp[x] = 1; for (int y = 0; y < x; y++) if (a[y] < a[x] && dp[y] + 1 > dp[x]) dp[x] = dp[y] + 1; if (dp[x] > best) best = dp[x]; }\n    return best;\n}",
            "java": "class LcLisLengthCsv {\n    public static int lc_lis_length_csv(String nums) {\n        String[] p = nums.split(\",\"); int n = p.length; int[] a = new int[n]; for (int i = 0; i < n; i++) a[i] = Integer.parseInt(p[i]);\n        int[] dp = new int[n]; int best = 1; for (int i = 0; i < n; i++) { dp[i] = 1; for (int j = 0; j < i; j++) if (a[j] < a[i] && dp[j] + 1 > dp[i]) dp[i] = dp[j] + 1; if (dp[i] > best) best = dp[i]; }\n        return best;\n    }\n}",
            "rust": "pub fn lc_lis_length_csv(nums: &str) -> i32 {\n    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let n = a.len(); let mut dp = vec![1; n]; let mut best = 1;\n    let mut i = 0usize; while i < n { let mut j = 0usize; while j < i { if a[j] < a[i] && dp[j] + 1 > dp[i] { dp[i] = dp[j] + 1; } j += 1; } if dp[i] > best { best = dp[i]; } i += 1; }\n    best\n}",
        }),
        Problem("lc_longest_consecutive_len_csv", "LC Longest Consecutive Sequence Length CSV", "Return the length of the longest consecutive integer run in a comma-separated list.", ["The empty string returns `0`.", "Duplicate values do not extend a run."], "int", [{"name": "nums", "type": "string"}], [case({"nums": "100,4,200,1,3,2"}, 4), case({"nums": "0,3,7,2,5,8,4,6,0,1"}, 9), case({"nums": ""}, 0)], lc("longest-consecutive-sequence"), "medium", {
            "c": "int lc_longest_consecutive_len_csv(const char *nums) {\n    if (nums[0] == '\\0') return 0;\n    int a[256], n = 0, i = 0;\n    while (nums[i] != '\\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } a[n++] = sign * v; if (nums[i] == ',') i++; }\n    for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) if (a[y] < a[x]) { int t = a[x]; a[x] = a[y]; a[y] = t; }\n    int best = 1, cur = 1; for (int x = 1; x < n; x++) { if (a[x] == a[x - 1]) continue; if (a[x] == a[x - 1] + 1) cur++; else cur = 1; if (cur > best) best = cur; }\n    return best;\n}",
            "java": "class LcLongestConsecutiveLenCsv {\n    public static int lc_longest_consecutive_len_csv(String nums) {\n        if (nums.isEmpty()) return 0; String[] p = nums.split(\",\"); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); java.util.Arrays.sort(a);\n        int best = 1, cur = 1; for (int i = 1; i < a.length; i++) { if (a[i] == a[i - 1]) continue; if (a[i] == a[i - 1] + 1) cur++; else cur = 1; if (cur > best) best = cur; }\n        return best;\n    }\n}",
            "rust": "pub fn lc_longest_consecutive_len_csv(nums: &str) -> i32 {\n    if nums.is_empty() { return 0; } let mut a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); a.sort();\n    let mut best = 1; let mut cur = 1; let mut i = 1usize; while i < a.len() { if a[i] != a[i - 1] { if a[i] == a[i - 1] + 1 { cur += 1; } else { cur = 1; } if cur > best { best = cur; } } i += 1; }\n    best\n}",
        }),
        Problem("luogu_p5709_apples_remaining", "Luogu P5709 Apples Remaining", "Return how many apples remain after worms eat one apple every `t` seconds for `s` seconds.", ["`m >= 0`, `t > 0`, and `s >= 0`.", "A partially eaten apple counts as eaten."], "int", [{"name": "m", "type": "int"}, {"name": "t", "type": "int"}, {"name": "s", "type": "int"}], [case({"m": 10, "t": 3, "s": 17}, 4), case({"m": 5, "t": 2, "s": 1}, 4), case({"m": 3, "t": 1, "s": 9}, 0)], lg("P5709"), "easy", {
            "c": "int luogu_p5709_apples_remaining(int m, int t, int s) {\n    int eaten = (s + t - 1) / t;\n    int left = m - eaten;\n    return left > 0 ? left : 0;\n}",
            "java": "class LuoguP5709ApplesRemaining {\n    public static int luogu_p5709_apples_remaining(int m, int t, int s) {\n        int eaten = (s + t - 1) / t; int left = m - eaten; return left > 0 ? left : 0;\n    }\n}",
            "rust": "pub fn luogu_p5709_apples_remaining(m: i32, t: i32, s: i32) -> i32 {\n    let eaten = (s + t - 1) / t; let left = m - eaten; if left > 0 { left } else { 0 }\n}",
        }),
        Problem("luogu_p5713_local_or_luogu", "Luogu P5713 Local Or Luogu", "Compare `5*x` with `11+3*x`; return `1` when Local is cheaper, otherwise `2` for Luogu.", ["`x >= 0`.", "This numeric code preserves the original two-way output decision."], "int", [{"name": "x", "type": "int"}], [case({"x": 1}, 1), case({"x": 6}, 2), case({"x": 10}, 2)], lg("P5713"), "easy", {
            "c": "int luogu_p5713_local_or_luogu(int x) {\n    return 5 * x < 11 + 3 * x ? 1 : 2;\n}",
            "java": "class LuoguP5713LocalOrLuogu {\n    public static int luogu_p5713_local_or_luogu(int x) {\n        return 5 * x < 11 + 3 * x ? 1 : 2;\n    }\n}",
            "rust": "pub fn luogu_p5713_local_or_luogu(x: i32) -> i32 {\n    if 5 * x < 11 + 3 * x { 1 } else { 2 }\n}",
        }),
        Problem("luogu_p5716_month_days", "Luogu P5716 Month Days", "Return the number of days in `month` for Gregorian `year`.", ["`1 <= month <= 12`.", "Use standard leap-year rules."], "int", [{"name": "year", "type": "int"}, {"name": "month", "type": "int"}], [case({"year": 2020, "month": 2}, 29), case({"year": 1900, "month": 2}, 28), case({"year": 2021, "month": 11}, 30)], lg("P5716"), "easy", {
            "c": "int luogu_p5716_month_days(int year, int month) {\n    int days[13] = {0,31,28,31,30,31,30,31,31,30,31,30,31};\n    int leap = (year % 400 == 0) || (year % 4 == 0 && year % 100 != 0);\n    if (month == 2 && leap) return 29;\n    return days[month];\n}",
            "java": "class LuoguP5716MonthDays {\n    public static int luogu_p5716_month_days(int year, int month) {\n        int[] days = {0,31,28,31,30,31,30,31,31,30,31,30,31}; boolean leap = year % 400 == 0 || (year % 4 == 0 && year % 100 != 0); return month == 2 && leap ? 29 : days[month];\n    }\n}",
            "rust": "pub fn luogu_p5716_month_days(year: i32, month: i32) -> i32 {\n    let days = [0,31,28,31,30,31,30,31,31,30,31,30,31]; let leap = year % 400 == 0 || (year % 4 == 0 && year % 100 != 0); if month == 2 && leap { 29 } else { days[month as usize] }\n}",
        }),
        Problem("luogu_p5718_min_csv", "Luogu P5718 Minimum CSV", "Return the minimum value in a comma-separated integer list.", ["`nums` is nonempty.", "Values fit in signed 32-bit integer range."], "int", [{"name": "nums", "type": "string"}], [case({"nums": "3,1,4,1,5"}, 1), case({"nums": "-2,7,0"}, -2), case({"nums": "9"}, 9)], lg("P5718"), "easy", {
            "c": "int luogu_p5718_min_csv(const char *nums) {\n    int i = 0, first = 1, best = 0;\n    while (nums[i] != '\\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } v *= sign; if (first || v < best) { best = v; first = 0; } if (nums[i] == ',') i++; }\n    return best;\n}",
            "java": "class LuoguP5718MinCsv {\n    public static int luogu_p5718_min_csv(String nums) {\n        String[] p = nums.split(\",\"); int best = Integer.parseInt(p[0]); for (int i = 1; i < p.length; i++) { int v = Integer.parseInt(p[i]); if (v < best) best = v; } return best;\n    }\n}",
            "rust": "pub fn luogu_p5718_min_csv(nums: &str) -> i32 {\n    let mut best = 0; let mut first = true; for part in nums.split(',') { let v = part.parse::<i32>().unwrap(); if first || v < best { best = v; first = false; } } best\n}",
        }),
        Problem("luogu_p5724_range_csv", "Luogu P5724 Range CSV", "Return the difference between the maximum and minimum value in a comma-separated integer list.", ["`nums` is nonempty.", "Values fit in signed 32-bit integer range."], "int", [{"name": "nums", "type": "string"}], [case({"nums": "1,5,9,2"}, 8), case({"nums": "7,7,7"}, 0), case({"nums": "-3,4,1"}, 7)], lg("P5724"), "easy", {
            "c": "int luogu_p5724_range_csv(const char *nums) {\n    int i = 0, first = 1, mn = 0, mx = 0;\n    while (nums[i] != '\\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } v *= sign; if (first) { mn = mx = v; first = 0; } else { if (v < mn) mn = v; if (v > mx) mx = v; } if (nums[i] == ',') i++; }\n    return mx - mn;\n}",
            "java": "class LuoguP5724RangeCsv {\n    public static int luogu_p5724_range_csv(String nums) {\n        String[] p = nums.split(\",\"); int mn = Integer.parseInt(p[0]), mx = mn; for (int i = 1; i < p.length; i++) { int v = Integer.parseInt(p[i]); if (v < mn) mn = v; if (v > mx) mx = v; } return mx - mn;\n    }\n}",
            "rust": "pub fn luogu_p5724_range_csv(nums: &str) -> i32 {\n    let mut mn = 0; let mut mx = 0; let mut first = true; for part in nums.split(',') { let v = part.parse::<i32>().unwrap(); if first { mn = v; mx = v; first = false; } else { if v < mn { mn = v; } if v > mx { mx = v; } } } mx - mn\n}",
        }),
        Problem("ex_collatz_steps", "Exercism Collatz Steps", "Return the number of Collatz steps needed to reach `1`.", ["`n > 0`.", "Intermediate values fit in signed 64-bit integer range."], "int", [{"name": "n", "type": "int"}], [case({"n": 1}, 0), case({"n": 12}, 9), case({"n": 19}, 20)], ex("collatz-conjecture"), "easy", {
            "c": "int ex_collatz_steps(int n) {\n    long long x = n; int steps = 0;\n    while (x != 1) { if (x % 2 == 0) x /= 2; else x = 3 * x + 1; steps++; }\n    return steps;\n}",
            "java": "class ExCollatzSteps {\n    public static int ex_collatz_steps(int n) {\n        long x = n; int steps = 0; while (x != 1) { if (x % 2 == 0) x /= 2; else x = 3 * x + 1; steps++; } return steps;\n    }\n}",
            "rust": "pub fn ex_collatz_steps(n: i32) -> i32 {\n    let mut x = n as i64; let mut steps = 0; while x != 1 { if x % 2 == 0 { x /= 2; } else { x = 3 * x + 1; } steps += 1; } steps\n}",
        }),
        Problem("ex_hamming_distance", "Exercism Hamming Distance", "Return the Hamming distance between equal-length strings `a` and `b`.", ["Inputs have equal length.", "Strings are ASCII."], "int", [{"name": "a", "type": "string"}, {"name": "b", "type": "string"}], [case({"a": "GAGCCTACTAACGGGAT", "b": "CATCGTAATGACGGCCT"}, 7), case({"a": "A", "b": "A"}, 0), case({"a": "GG", "b": "TT"}, 2)], ex("hamming"), "easy", {
            "c": "int ex_hamming_distance(const char *a, const char *b) {\n    int d = 0; for (int i = 0; a[i] != '\\0'; i++) if (a[i] != b[i]) d++; return d;\n}",
            "java": "class ExHammingDistance {\n    public static int ex_hamming_distance(String a, String b) {\n        int d = 0; for (int i = 0; i < a.length(); i++) if (a.charAt(i) != b.charAt(i)) d++; return d;\n    }\n}",
            "rust": "pub fn ex_hamming_distance(a: &str, b: &str) -> i32 {\n    let ab = a.as_bytes(); let bb = b.as_bytes(); let mut d = 0; let mut i = 0usize; while i < ab.len() { if ab[i] != bb[i] { d += 1; } i += 1; } d\n}",
        }),
        Problem("ex_armstrong_number_bool", "Exercism Armstrong Number Bool", "Return true if `n` is an Armstrong number.", ["`n >= 0`.", "Use the decimal digit count as the exponent."], "bool", [{"name": "n", "type": "int"}], [case({"n": 9}, True), case({"n": 153}, True), case({"n": 154}, False), case({"n": 9474}, True)], ex("armstrong-numbers"), "easy", {
            "c": "int ex_armstrong_number_bool(int n) {\n    int tmp = n, digits = 0; if (tmp == 0) digits = 1; while (tmp > 0) { digits++; tmp /= 10; }\n    tmp = n; int sum = 0; if (tmp == 0) sum = 0;\n    while (tmp > 0) { int d = tmp % 10, p = 1; for (int i = 0; i < digits; i++) p *= d; sum += p; tmp /= 10; }\n    return sum == n;\n}",
            "java": "class ExArmstrongNumberBool {\n    public static boolean ex_armstrong_number_bool(int n) {\n        int tmp = n, digits = 0; if (tmp == 0) digits = 1; while (tmp > 0) { digits++; tmp /= 10; }\n        tmp = n; int sum = 0; while (tmp > 0) { int d = tmp % 10, p = 1; for (int i = 0; i < digits; i++) p *= d; sum += p; tmp /= 10; }\n        return sum == n;\n    }\n}",
            "rust": "pub fn ex_armstrong_number_bool(n: i32) -> bool {\n    let mut tmp = n; let mut digits = 0; if tmp == 0 { digits = 1; } while tmp > 0 { digits += 1; tmp /= 10; }\n    tmp = n; let mut sum = 0; while tmp > 0 { let d = tmp % 10; let mut p = 1; let mut i = 0; while i < digits { p *= d; i += 1; } sum += p; tmp /= 10; }\n    sum == n\n}",
        }),
    ]


def more_real_source_problems_5() -> list[Problem]:
    lc = lambda slug: source("LeetCode", slug, f"https://leetcode.com/problems/{slug}/")
    lg = lambda slug: source("Luogu", slug, f"https://www.luogu.com.cn/problem/{slug}")
    ex = lambda slug: source(
        "Exercism",
        slug,
        f"https://github.com/exercism/problem-specifications/tree/main/exercises/{slug}",
        "MIT",
    )
    return [
        Problem("lc_number_of_islands_rows", "LC Number Of Islands Rows", "Count 4-directionally connected islands of `1` cells in a semicolon-separated binary grid.", ["Rows contain only `0` and `1`.", "All rows have equal positive length.", "The empty string returns `0`."], "int", [{"name": "rows", "type": "string"}], [case({"rows": "11110;11010;11000;00000"}, 1), case({"rows": "11000;11000;00100;00011"}, 3), case({"rows": ""}, 0)], lc("number-of-islands"), "medium", {
            "c": "int lc_number_of_islands_rows(const char *rows) {\n    if (rows[0] == '\\0') return 0;\n    char g[64][64]; int r = 0, c = 0, cols = 0, i = 0;\n    while (rows[i] != '\\0') { c = 0; while (rows[i] == '0' || rows[i] == '1') g[r][c++] = rows[i++]; if (cols == 0) cols = c; r++; if (rows[i] == ';') i++; }\n    int ans = 0, sx[4096], sy[4096];\n    for (int x = 0; x < r; x++) for (int y = 0; y < cols; y++) if (g[x][y] == '1') { ans++; int top = 0; sx[top] = x; sy[top++] = y; g[x][y] = '0'; while (top > 0) { top--; int cx = sx[top], cy = sy[top]; int dx[4] = {1,-1,0,0}, dy[4] = {0,0,1,-1}; for (int k = 0; k < 4; k++) { int nx = cx + dx[k], ny = cy + dy[k]; if (nx >= 0 && nx < r && ny >= 0 && ny < cols && g[nx][ny] == '1') { g[nx][ny] = '0'; sx[top] = nx; sy[top++] = ny; } } } }\n    return ans;\n}",
            "java": "class LcNumberOfIslandsRows {\n    public static int lc_number_of_islands_rows(String rows) {\n        if (rows.isEmpty()) return 0; String[] rs = rows.split(\";\"); int r = rs.length, c = rs[0].length(); char[][] g = new char[r][c]; for (int i = 0; i < r; i++) g[i] = rs[i].toCharArray();\n        int ans = 0; int[] sx = new int[r * c], sy = new int[r * c]; int[] dx = {1,-1,0,0}, dy = {0,0,1,-1};\n        for (int i = 0; i < r; i++) for (int j = 0; j < c; j++) if (g[i][j] == '1') { ans++; int top = 0; sx[top] = i; sy[top++] = j; g[i][j] = '0'; while (top > 0) { top--; int x = sx[top], y = sy[top]; for (int k = 0; k < 4; k++) { int nx = x + dx[k], ny = y + dy[k]; if (nx >= 0 && nx < r && ny >= 0 && ny < c && g[nx][ny] == '1') { g[nx][ny] = '0'; sx[top] = nx; sy[top++] = ny; } } } }\n        return ans;\n    }\n}",
            "rust": "pub fn lc_number_of_islands_rows(rows: &str) -> i32 {\n    if rows.is_empty() { return 0; } let mut g: Vec<Vec<u8>> = rows.split(';').map(|s| s.as_bytes().to_vec()).collect(); let r = g.len(); let c = g[0].len(); let mut ans = 0;\n    let dirs = [(1i32,0i32),(-1,0),(0,1),(0,-1)]; let mut x = 0usize; while x < r { let mut y = 0usize; while y < c { if g[x][y] == b'1' { ans += 1; let mut st = vec![(x,y)]; g[x][y] = b'0'; while let Some((cx,cy)) = st.pop() { for (dx,dy) in dirs { let nx = cx as i32 + dx; let ny = cy as i32 + dy; if nx >= 0 && nx < r as i32 && ny >= 0 && ny < c as i32 && g[nx as usize][ny as usize] == b'1' { g[nx as usize][ny as usize] = b'0'; st.push((nx as usize, ny as usize)); } } } } y += 1; } x += 1; }\n    ans\n}",
        }),
        Problem("lc_daily_temperatures_wait_sum_csv", "LC Daily Temperatures Wait Sum CSV", "Compute daily-temperature waiting days and return their sum.", ["`temps` is a nonempty comma-separated list of integers.", "For days with no warmer future day, the wait is `0`."], "int", [{"name": "temps", "type": "string"}], [case({"temps": "73,74,75,71,69,72,76,73"}, 10), case({"temps": "30,40,50,60"}, 3), case({"temps": "30,60,90"}, 2)], lc("daily-temperatures"), "medium", {
            "c": "int lc_daily_temperatures_wait_sum_csv(const char *temps) {\n    int a[256], n = 0, i = 0;\n    while (temps[i] != '\\0') { int v = 0; while (temps[i] >= '0' && temps[i] <= '9') { v = v * 10 + temps[i] - '0'; i++; } a[n++] = v; if (temps[i] == ',') i++; }\n    int st[256], top = 0, sum = 0;\n    for (int d = 0; d < n; d++) { while (top > 0 && a[d] > a[st[top - 1]]) { int prev = st[--top]; sum += d - prev; } st[top++] = d; }\n    return sum;\n}",
            "java": "class LcDailyTemperaturesWaitSumCsv {\n    public static int lc_daily_temperatures_wait_sum_csv(String temps) {\n        String[] p = temps.split(\",\"); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); int[] st = new int[a.length]; int top = 0, sum = 0;\n        for (int d = 0; d < a.length; d++) { while (top > 0 && a[d] > a[st[top - 1]]) { int prev = st[--top]; sum += d - prev; } st[top++] = d; }\n        return sum;\n    }\n}",
            "rust": "pub fn lc_daily_temperatures_wait_sum_csv(temps: &str) -> i32 {\n    let a: Vec<i32> = temps.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut st: Vec<usize> = Vec::new(); let mut sum = 0;\n    let mut d = 0usize; while d < a.len() { while !st.is_empty() && a[d] > a[*st.last().unwrap()] { let prev = st.pop().unwrap(); sum += (d - prev) as i32; } st.push(d); d += 1; }\n    sum\n}",
        }),
        Problem("lc_set_matrix_zeroes_count_rows", "LC Set Matrix Zeroes Count Rows", "Apply the set-matrix-zeroes rule to a semicolon-separated 0/1 matrix and return the final number of zero cells.", ["Rows use comma-separated `0` or `1` values.", "All rows have equal positive length."], "int", [{"name": "rows", "type": "string"}], [case({"rows": "1,1,1;1,0,1;1,1,1"}, 5), case({"rows": "0,1,2,0;3,4,5,2;1,3,1,5"}, 10), case({"rows": "1,1;1,1"}, 0)], lc("set-matrix-zeroes"), "medium", {
            "c": "int lc_set_matrix_zeroes_count_rows(const char *rows) {\n    int row[64] = {0}, col[64] = {0}, r = 0, c = 0, cols = 0, i = 0;\n    while (rows[i] != '\\0') { c = 0; while (rows[i] != '\\0' && rows[i] != ';') { int v = 0; while (rows[i] >= '0' && rows[i] <= '9') { v = v * 10 + rows[i] - '0'; i++; } if (v == 0) { row[r] = 1; col[c] = 1; } c++; if (rows[i] == ',') i++; } if (cols == 0) cols = c; r++; if (rows[i] == ';') i++; }\n    int zeros = 0; for (int x = 0; x < r; x++) for (int y = 0; y < cols; y++) if (row[x] || col[y]) zeros++;\n    return zeros;\n}",
            "java": "class LcSetMatrixZeroesCountRows {\n    public static int lc_set_matrix_zeroes_count_rows(String rows) {\n        String[] rs = rows.split(\";\"); int r = rs.length, c = rs[0].split(\",\").length; boolean[] row = new boolean[r], col = new boolean[c]; int[][] a = new int[r][c];\n        for (int i = 0; i < r; i++) { String[] p = rs[i].split(\",\"); for (int j = 0; j < c; j++) { a[i][j] = Integer.parseInt(p[j]); if (a[i][j] == 0) { row[i] = true; col[j] = true; } } }\n        int zeros = 0; for (int i = 0; i < r; i++) for (int j = 0; j < c; j++) if (row[i] || col[j]) zeros++; return zeros;\n    }\n}",
            "rust": "pub fn lc_set_matrix_zeroes_count_rows(rows: &str) -> i32 {\n    let rs: Vec<&str> = rows.split(';').collect(); let r = rs.len(); let c = rs[0].split(',').count(); let mut row = vec![false; r]; let mut col = vec![false; c];\n    for (i, line) in rs.iter().enumerate() { for (j, part) in line.split(',').enumerate() { if part.parse::<i32>().unwrap() == 0 { row[i] = true; col[j] = true; } } }\n    let mut zeros = 0; let mut i = 0usize; while i < r { let mut j = 0usize; while j < c { if row[i] || col[j] { zeros += 1; } j += 1; } i += 1; } zeros\n}",
        }),
        Problem("luogu_p5722_sequence_sum", "Luogu P5722 Sequence Sum", "Return the sum `1 + 2 + ... + n`.", ["`n >= 1`.", "The result fits in signed 32-bit integer range."], "int", [{"name": "n", "type": "int"}], [case({"n": 1}, 1), case({"n": 10}, 55), case({"n": 100}, 5050)], lg("P5722"), "easy", {
            "c": "int luogu_p5722_sequence_sum(int n) {\n    return n * (n + 1) / 2;\n}",
            "java": "class LuoguP5722SequenceSum {\n    public static int luogu_p5722_sequence_sum(int n) {\n        return n * (n + 1) / 2;\n    }\n}",
            "rust": "pub fn luogu_p5722_sequence_sum(n: i32) -> i32 {\n    n * (n + 1) / 2\n}",
        }),
        Problem("luogu_p5739_factorial", "Luogu P5739 Factorial", "Return `n!`.", ["`0 <= n <= 12`.", "The result fits in signed 32-bit integer range."], "int", [{"name": "n", "type": "int"}], [case({"n": 0}, 1), case({"n": 5}, 120), case({"n": 8}, 40320)], lg("P5739"), "easy", {
            "c": "int luogu_p5739_factorial(int n) {\n    int ans = 1; for (int i = 2; i <= n; i++) ans *= i; return ans;\n}",
            "java": "class LuoguP5739Factorial {\n    public static int luogu_p5739_factorial(int n) {\n        int ans = 1; for (int i = 2; i <= n; i++) ans *= i; return ans;\n    }\n}",
            "rust": "pub fn luogu_p5739_factorial(n: i32) -> i32 {\n    let mut ans = 1; let mut i = 2; while i <= n { ans *= i; i += 1; } ans\n}",
        }),
        Problem("ex_darts_score", "Exercism Darts Score", "Return the dart score for integer coordinates using radii 1, 5, and 10.", ["Coordinates are integer grid points.", "Use squared-distance comparisons to avoid floating point."], "int", [{"name": "x", "type": "int"}, {"name": "y", "type": "int"}], [case({"x": 0, "y": 0}, 10), case({"x": 3, "y": 4}, 5), case({"x": 8, "y": 8}, 0)], ex("darts"), "easy", {
            "c": "int ex_darts_score(int x, int y) {\n    int d = x * x + y * y; if (d <= 1) return 10; if (d <= 25) return 5; if (d <= 100) return 1; return 0;\n}",
            "java": "class ExDartsScore {\n    public static int ex_darts_score(int x, int y) {\n        int d = x * x + y * y; if (d <= 1) return 10; if (d <= 25) return 5; if (d <= 100) return 1; return 0;\n    }\n}",
            "rust": "pub fn ex_darts_score(x: i32, y: i32) -> i32 {\n    let d = x * x + y * y; if d <= 1 { 10 } else if d <= 25 { 5 } else if d <= 100 { 1 } else { 0 }\n}",
        }),
        Problem("ex_resistor_color_trio_value", "Exercism Resistor Color Trio Value", "Return the resistance value from two color digits and a multiplier digit.", ["Colors are encoded as standard resistor-color digits `0..9`.", "The value is `(10*first + second) * 10^multiplier`."], "int", [{"name": "first", "type": "int"}, {"name": "second", "type": "int"}, {"name": "multiplier", "type": "int"}], [case({"first": 2, "second": 2, "multiplier": 1}, 220), case({"first": 4, "second": 7, "multiplier": 2}, 4700), case({"first": 0, "second": 1, "multiplier": 0}, 1)], ex("resistor-color-trio"), "easy", {
            "c": "int ex_resistor_color_trio_value(int first, int second, int multiplier) {\n    int value = first * 10 + second; for (int i = 0; i < multiplier; i++) value *= 10; return value;\n}",
            "java": "class ExResistorColorTrioValue {\n    public static int ex_resistor_color_trio_value(int first, int second, int multiplier) {\n        int value = first * 10 + second; for (int i = 0; i < multiplier; i++) value *= 10; return value;\n    }\n}",
            "rust": "pub fn ex_resistor_color_trio_value(first: i32, second: i32, multiplier: i32) -> i32 {\n    let mut value = first * 10 + second; let mut i = 0; while i < multiplier { value *= 10; i += 1; } value\n}",
        }),
        Problem("ex_isbn10_valid", "Exercism ISBN Verifier Valid", "Return true if an ISBN-10 string has exactly 10 digits after hyphen removal and a valid checksum.", ["Hyphens are ignored.", "`X` may appear only as the final check character and has value 10."], "bool", [{"name": "s", "type": "string"}], [case({"s": "3-598-21508-8"}, True), case({"s": "3-598-21508-9"}, False), case({"s": "3-598-21507-X"}, True), case({"s": "3-598-2X507-9"}, False)], ex("isbn-verifier"), "medium", {
            "c": "int ex_isbn10_valid(const char *s) {\n    int pos = 0, sum = 0;\n    for (int i = 0; s[i] != '\\0'; i++) { if (s[i] == '-') continue; int v; if (s[i] == 'X') { if (pos != 9) return 0; v = 10; } else if (s[i] >= '0' && s[i] <= '9') v = s[i] - '0'; else return 0; if (pos >= 10) return 0; sum += v * (10 - pos); pos++; }\n    return pos == 10 && sum % 11 == 0;\n}",
            "java": "class ExIsbn10Valid {\n    public static boolean ex_isbn10_valid(String s) {\n        int pos = 0, sum = 0; for (int i = 0; i < s.length(); i++) { char ch = s.charAt(i); if (ch == '-') continue; int v; if (ch == 'X') { if (pos != 9) return false; v = 10; } else if (ch >= '0' && ch <= '9') v = ch - '0'; else return false; if (pos >= 10) return false; sum += v * (10 - pos); pos++; } return pos == 10 && sum % 11 == 0;\n    }\n}",
            "rust": "pub fn ex_isbn10_valid(s: &str) -> bool {\n    let mut pos = 0; let mut sum = 0; for ch in s.bytes() { if ch == b'-' { continue; } let v: i32; if ch == b'X' { if pos != 9 { return false; } v = 10; } else if ch >= b'0' && ch <= b'9' { v = (ch - b'0') as i32; } else { return false; } if pos >= 10 { return false; } sum += v * (10 - pos); pos += 1; } pos == 10 && sum % 11 == 0\n}",
        }),
    ]


def more_real_source_problems_6() -> list[Problem]:
    lc = lambda slug: source("LeetCode", slug, f"https://leetcode.com/problems/{slug}/")
    return [
        Problem("lc_perfect_squares_min", "LC Perfect Squares Min", "Return the least number of perfect squares whose sum is `n`.", ["`1 <= n <= 2000`.", "The answer fits in signed 32-bit integer range."], "int", [{"name": "n", "type": "int"}], [case({"n": 12}, 3), case({"n": 13}, 2), case({"n": 1}, 1)], lc("perfect-squares"), "medium", {
            "c": "int lc_perfect_squares_min(int n) {\n    int dp[2001]; for (int i = 0; i <= n; i++) dp[i] = 1000000; dp[0] = 0;\n    for (int i = 1; i * i <= n; i++) { int sq = i * i; for (int s = sq; s <= n; s++) if (dp[s - sq] + 1 < dp[s]) dp[s] = dp[s - sq] + 1; }\n    return dp[n];\n}",
            "java": "class LcPerfectSquaresMin {\n    public static int lc_perfect_squares_min(int n) {\n        int[] dp = new int[n + 1]; for (int i = 1; i <= n; i++) dp[i] = 1000000;\n        for (int i = 1; i * i <= n; i++) { int sq = i * i; for (int s = sq; s <= n; s++) if (dp[s - sq] + 1 < dp[s]) dp[s] = dp[s - sq] + 1; }\n        return dp[n];\n    }\n}",
            "rust": "pub fn lc_perfect_squares_min(n: i32) -> i32 {\n    let mut dp = vec![1000000; (n + 1) as usize]; dp[0] = 0;\n    let mut i = 1; while i * i <= n { let sq = i * i; let mut s = sq; while s <= n { let cand = dp[(s - sq) as usize] + 1; if cand < dp[s as usize] { dp[s as usize] = cand; } s += 1; } i += 1; }\n    dp[n as usize]\n}",
        }),
        Problem("lc_combination_sum4_count_csv", "LC Combination Sum IV Count CSV", "Return the number of ordered combinations from `nums` that sum to `target`.", ["`nums` is a nonempty comma-separated list of positive distinct integers.", "`target >= 0`.", "The count fits in signed 32-bit integer range."], "int", [{"name": "nums", "type": "string"}, {"name": "target", "type": "int"}], [case({"nums": "1,2,3", "target": 4}, 7), case({"nums": "9", "target": 3}, 0), case({"nums": "2,4", "target": 6}, 2)], lc("combination-sum-iv"), "medium", {
            "c": "int lc_combination_sum4_count_csv(const char *nums, int target) {\n    int a[128], n = 0, i = 0; while (nums[i] != '\\0') { int v = 0; while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } a[n++] = v; if (nums[i] == ',') i++; }\n    int dp[1001] = {0}; dp[0] = 1; for (int s = 1; s <= target; s++) for (int j = 0; j < n; j++) if (s >= a[j]) dp[s] += dp[s - a[j]];\n    return dp[target];\n}",
            "java": "class LcCombinationSum4CountCsv {\n    public static int lc_combination_sum4_count_csv(String nums, int target) {\n        String[] p = nums.split(\",\"); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); int[] dp = new int[target + 1]; dp[0] = 1;\n        for (int s = 1; s <= target; s++) for (int v : a) if (s >= v) dp[s] += dp[s - v]; return dp[target];\n    }\n}",
            "rust": "pub fn lc_combination_sum4_count_csv(nums: &str, target: i32) -> i32 {\n    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut dp = vec![0; (target + 1) as usize]; dp[0] = 1;\n    let mut s = 1; while s <= target { for &v in &a { if s >= v { dp[s as usize] += dp[(s - v) as usize]; } } s += 1; } dp[target as usize]\n}",
        }),
        Problem("lc_target_sum_ways_csv", "LC Target Sum Ways CSV", "Return how many sign assignments make comma-separated nonnegative integers sum to `target`.", ["`nums` contains nonnegative integers.", "The transformed subset sum fits the fixed DP capacity used by the tests."], "int", [{"name": "nums", "type": "string"}, {"name": "target", "type": "int"}], [case({"nums": "1,1,1,1,1", "target": 3}, 5), case({"nums": "1", "target": 1}, 1), case({"nums": "1,2,7", "target": 4}, 0)], lc("target-sum"), "medium", {
            "c": "int lc_target_sum_ways_csv(const char *nums, int target) {\n    int a[128], n = 0, total = 0, i = 0; while (nums[i] != '\\0') { int v = 0; while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } a[n++] = v; total += v; if (nums[i] == ',') i++; }\n    int want = total + target; if (want < 0 || want % 2 != 0) return 0; want /= 2; int dp[2001] = {0}; dp[0] = 1;\n    for (int j = 0; j < n; j++) for (int s = want; s >= a[j]; s--) dp[s] += dp[s - a[j]];\n    return dp[want];\n}",
            "java": "class LcTargetSumWaysCsv {\n    public static int lc_target_sum_ways_csv(String nums, int target) {\n        String[] p = nums.split(\",\"); int[] a = new int[p.length]; int total = 0; for (int i = 0; i < p.length; i++) { a[i] = Integer.parseInt(p[i]); total += a[i]; }\n        int want = total + target; if (want < 0 || want % 2 != 0) return 0; want /= 2; int[] dp = new int[want + 1]; dp[0] = 1; for (int v : a) for (int s = want; s >= v; s--) dp[s] += dp[s - v]; return dp[want];\n    }\n}",
            "rust": "pub fn lc_target_sum_ways_csv(nums: &str, target: i32) -> i32 {\n    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let total: i32 = a.iter().sum(); let mut want = total + target; if want < 0 || want % 2 != 0 { return 0; } want /= 2; let mut dp = vec![0; (want + 1) as usize]; dp[0] = 1;\n    for &v in &a { let mut s = want; while s >= v { dp[s as usize] += dp[(s - v) as usize]; s -= 1; } } dp[want as usize]\n}",
        }),
        Problem("lc_min_subarray_len_csv", "LC Minimum Size Subarray Sum Length CSV", "Return the minimum length of a contiguous subarray with sum at least `target`, or `0` if none exists.", ["`nums` is a nonempty comma-separated list of positive integers.", "`target > 0`."], "int", [{"name": "target", "type": "int"}, {"name": "nums", "type": "string"}], [case({"target": 7, "nums": "2,3,1,2,4,3"}, 2), case({"target": 4, "nums": "1,4,4"}, 1), case({"target": 11, "nums": "1,1,1,1,1,1,1,1"}, 0)], lc("minimum-size-subarray-sum"), "medium", {
            "c": "int lc_min_subarray_len_csv(int target, const char *nums) {\n    int a[256], n = 0, i = 0; while (nums[i] != '\\0') { int v = 0; while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } a[n++] = v; if (nums[i] == ',') i++; }\n    int left = 0, sum = 0, best = 1000000; for (int right = 0; right < n; right++) { sum += a[right]; while (sum >= target) { int len = right - left + 1; if (len < best) best = len; sum -= a[left++]; } }\n    return best == 1000000 ? 0 : best;\n}",
            "java": "class LcMinSubarrayLenCsv {\n    public static int lc_min_subarray_len_csv(int target, String nums) {\n        String[] p = nums.split(\",\"); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); int left = 0, sum = 0, best = 1000000;\n        for (int right = 0; right < a.length; right++) { sum += a[right]; while (sum >= target) { int len = right - left + 1; if (len < best) best = len; sum -= a[left++]; } } return best == 1000000 ? 0 : best;\n    }\n}",
            "rust": "pub fn lc_min_subarray_len_csv(target: i32, nums: &str) -> i32 {\n    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut left = 0usize; let mut sum = 0; let mut best = 1000000;\n    let mut right = 0usize; while right < a.len() { sum += a[right]; while sum >= target { let len = (right - left + 1) as i32; if len < best { best = len; } sum -= a[left]; left += 1; } right += 1; } if best == 1000000 { 0 } else { best }\n}",
        }),
        Problem("lc_valid_sudoku_rows", "LC Valid Sudoku Rows", "Return true if a 9x9 Sudoku board has no repeated digit in any row, column, or 3x3 box.", ["Rows are separated by semicolons.", "Each row has digits `1` to `9` or `.` for empty cells."], "bool", [{"name": "rows", "type": "string"}], [case({"rows": "53..7....;6..195...;.98....6.;8...6...3;4..8.3..1;7...2...6;.6....28.;...419..5;....8..79"}, True), case({"rows": "83..7....;6..195...;.98....6.;8...6...3;4..8.3..1;7...2...6;.6....28.;...419..5;....8..79"}, False)], lc("valid-sudoku"), "medium", {
            "c": "int lc_valid_sudoku_rows(const char *rows) {\n    int row[9][10] = {{0}}, col[9][10] = {{0}}, box[9][10] = {{0}}, r = 0, c = 0;\n    for (int i = 0; rows[i] != '\\0'; i++) { if (rows[i] == ';') { r++; c = 0; continue; } if (rows[i] != '.') { int d = rows[i] - '0'; int b = (r / 3) * 3 + c / 3; if (row[r][d] || col[c][d] || box[b][d]) return 0; row[r][d] = col[c][d] = box[b][d] = 1; } c++; }\n    return 1;\n}",
            "java": "class LcValidSudokuRows {\n    public static boolean lc_valid_sudoku_rows(String rows) {\n        boolean[][] row = new boolean[9][10], col = new boolean[9][10], box = new boolean[9][10]; String[] rs = rows.split(\";\");\n        for (int r = 0; r < 9; r++) for (int c = 0; c < 9; c++) { char ch = rs[r].charAt(c); if (ch != '.') { int d = ch - '0'; int b = (r / 3) * 3 + c / 3; if (row[r][d] || col[c][d] || box[b][d]) return false; row[r][d] = col[c][d] = box[b][d] = true; } } return true;\n    }\n}",
            "rust": "pub fn lc_valid_sudoku_rows(rows: &str) -> bool {\n    let rs: Vec<&[u8]> = rows.split(';').map(|s| s.as_bytes()).collect(); let mut row = [[false; 10]; 9]; let mut col = [[false; 10]; 9]; let mut boxs = [[false; 10]; 9];\n    let mut r = 0usize; while r < 9 { let mut c = 0usize; while c < 9 { let ch = rs[r][c]; if ch != b'.' { let d = (ch - b'0') as usize; let b = (r / 3) * 3 + c / 3; if row[r][d] || col[c][d] || boxs[b][d] { return false; } row[r][d] = true; col[c][d] = true; boxs[b][d] = true; } c += 1; } r += 1; } true\n}",
        }),
    ]


def more_real_source_problems_7() -> list[Problem]:
    lc = lambda slug: source("LeetCode", slug, f"https://leetcode.com/problems/{slug}/")
    lg = lambda slug: source("Luogu", slug, f"https://www.luogu.com.cn/problem/{slug}")
    ex = lambda slug: source(
        "Exercism",
        slug,
        f"https://github.com/exercism/problem-specifications/tree/main/exercises/{slug}",
        "MIT",
    )
    return [
        Problem("lc_house_robber_ii_csv", "LC House Robber II CSV", "Return the maximum amount that can be robbed from circularly arranged houses.", ["`nums` is a nonempty comma-separated list of nonnegative integers.", "Adjacent houses in the circle cannot both be robbed."], "int", [{"name": "nums", "type": "string"}], [case({"nums": "2,3,2"}, 3), case({"nums": "1,2,3,1"}, 4), case({"nums": "1"}, 1)], lc("house-robber-ii"), "medium", {
            "c": "int lc_house_robber_ii_csv(const char *nums) {\n    int a[256], n = 0, i = 0;\n    while (nums[i] != '\\0') { int v = 0; while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } a[n++] = v; if (nums[i] == ',') i++; }\n    if (n == 1) return a[0];\n    int prev = 0, cur = 0; for (int j = 0; j < n - 1; j++) { int next = prev + a[j] > cur ? prev + a[j] : cur; prev = cur; cur = next; } int best1 = cur;\n    prev = 0; cur = 0; for (int j = 1; j < n; j++) { int next = prev + a[j] > cur ? prev + a[j] : cur; prev = cur; cur = next; }\n    return best1 > cur ? best1 : cur;\n}",
            "java": "class LcHouseRobberIiCsv {\n    public static int lc_house_robber_ii_csv(String nums) {\n        String[] p = nums.split(\",\"); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); if (a.length == 1) return a[0];\n        int prev = 0, cur = 0; for (int i = 0; i < a.length - 1; i++) { int next = Math.max(prev + a[i], cur); prev = cur; cur = next; } int best = cur;\n        prev = 0; cur = 0; for (int i = 1; i < a.length; i++) { int next = Math.max(prev + a[i], cur); prev = cur; cur = next; } return Math.max(best, cur);\n    }\n}",
            "rust": "pub fn lc_house_robber_ii_csv(nums: &str) -> i32 {\n    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); if a.len() == 1 { return a[0]; }\n    fn rob(slice: &[i32]) -> i32 { let mut prev = 0; let mut cur = 0; for &v in slice { let next = if prev + v > cur { prev + v } else { cur }; prev = cur; cur = next; } cur }\n    let a1 = rob(&a[0..a.len()-1]); let a2 = rob(&a[1..]); if a1 > a2 { a1 } else { a2 }\n}",
        }),
        Problem("lc_word_break_bool", "LC Word Break Bool", "Return true if `s` can be segmented into dictionary words.", ["Dictionary words are semicolon-separated.", "All strings are lowercase ASCII in the supplied tests."], "bool", [{"name": "s", "type": "string"}, {"name": "dict", "type": "string"}], [case({"s": "leetcode", "dict": "leet;code"}, True), case({"s": "applepenapple", "dict": "apple;pen"}, True), case({"s": "catsandog", "dict": "cats;dog;sand;and;cat"}, False)], lc("word-break"), "medium", {
            "c": "int lc_word_break_bool(const char *s, const char *dict) {\n    char w[64][32]; int wl[64], wn = 0, i = 0;\n    while (dict[i] != '\\0') { int j = 0; while (dict[i] != '\\0' && dict[i] != ';') w[wn][j++] = dict[i++]; w[wn][j] = '\\0'; wl[wn++] = j; if (dict[i] == ';') i++; }\n    int n = 0; while (s[n] != '\\0') n++; int dp[128] = {0}; dp[0] = 1;\n    for (int pos = 0; pos < n; pos++) if (dp[pos]) for (int k = 0; k < wn; k++) { int ok = pos + wl[k] <= n; for (int j = 0; ok && j < wl[k]; j++) if (s[pos + j] != w[k][j]) ok = 0; if (ok) dp[pos + wl[k]] = 1; }\n    return dp[n];\n}",
            "java": "class LcWordBreakBool {\n    public static boolean lc_word_break_bool(String s, String dict) {\n        String[] words = dict.split(\";\"); boolean[] dp = new boolean[s.length() + 1]; dp[0] = true;\n        for (int i = 0; i < s.length(); i++) if (dp[i]) for (String w : words) if (i + w.length() <= s.length() && s.startsWith(w, i)) dp[i + w.length()] = true;\n        return dp[s.length()];\n    }\n}",
            "rust": "pub fn lc_word_break_bool(s: &str, dict: &str) -> bool {\n    let words: Vec<&[u8]> = dict.split(';').map(|x| x.as_bytes()).collect(); let b = s.as_bytes(); let mut dp = vec![false; b.len() + 1]; dp[0] = true;\n    let mut i = 0usize; while i < b.len() { if dp[i] { for w in &words { if i + w.len() <= b.len() && &b[i..i + w.len()] == *w { dp[i + w.len()] = true; } } } i += 1; } dp[b.len()]\n}",
        }),
        Problem("lc_course_schedule_can_finish", "LC Course Schedule Can Finish", "Return true if all courses can be completed from prerequisite pairs.", ["Pairs are encoded as `course,prerequisite;...`.", "The empty prerequisite string has no edges.", "`num_courses <= 128`."], "bool", [{"name": "num_courses", "type": "int"}, {"name": "prereqs", "type": "string"}], [case({"num_courses": 2, "prereqs": "1,0"}, True), case({"num_courses": 2, "prereqs": "1,0;0,1"}, False), case({"num_courses": 3, "prereqs": "1,0;2,1"}, True)], lc("course-schedule"), "medium", {
            "c": "int lc_course_schedule_can_finish(int num_courses, const char *prereqs) {\n    int g[128][128] = {{0}}, indeg[128] = {0}, i = 0;\n    while (prereqs[i] != '\\0') { int a = 0, b = 0; while (prereqs[i] >= '0' && prereqs[i] <= '9') { a = a * 10 + prereqs[i] - '0'; i++; } if (prereqs[i] == ',') i++; while (prereqs[i] >= '0' && prereqs[i] <= '9') { b = b * 10 + prereqs[i] - '0'; i++; } if (!g[b][a]) { g[b][a] = 1; indeg[a]++; } if (prereqs[i] == ';') i++; }\n    int q[128], head = 0, tail = 0, seen = 0; for (int c = 0; c < num_courses; c++) if (indeg[c] == 0) q[tail++] = c;\n    while (head < tail) { int v = q[head++]; seen++; for (int to = 0; to < num_courses; to++) if (g[v][to] && --indeg[to] == 0) q[tail++] = to; }\n    return seen == num_courses;\n}",
            "java": "class LcCourseScheduleCanFinish {\n    public static boolean lc_course_schedule_can_finish(int num_courses, String prereqs) {\n        boolean[][] g = new boolean[num_courses][num_courses]; int[] indeg = new int[num_courses];\n        if (!prereqs.isEmpty()) for (String e : prereqs.split(\";\")) { String[] p = e.split(\",\"); int a = Integer.parseInt(p[0]), b = Integer.parseInt(p[1]); if (!g[b][a]) { g[b][a] = true; indeg[a]++; } }\n        int[] q = new int[num_courses]; int head = 0, tail = 0, seen = 0; for (int i = 0; i < num_courses; i++) if (indeg[i] == 0) q[tail++] = i;\n        while (head < tail) { int v = q[head++]; seen++; for (int to = 0; to < num_courses; to++) if (g[v][to] && --indeg[to] == 0) q[tail++] = to; } return seen == num_courses;\n    }\n}",
            "rust": "pub fn lc_course_schedule_can_finish(num_courses: i32, prereqs: &str) -> bool {\n    let n = num_courses as usize; let mut g = vec![vec![false; n]; n]; let mut indeg = vec![0; n];\n    if !prereqs.is_empty() { for e in prereqs.split(';') { let p: Vec<usize> = e.split(',').map(|x| x.parse::<usize>().unwrap()).collect(); if !g[p[1]][p[0]] { g[p[1]][p[0]] = true; indeg[p[0]] += 1; } } }\n    let mut q: Vec<usize> = Vec::new(); let mut i = 0usize; while i < n { if indeg[i] == 0 { q.push(i); } i += 1; } let mut head = 0usize; let mut seen = 0usize;\n    while head < q.len() { let v = q[head]; head += 1; seen += 1; let mut to = 0usize; while to < n { if g[v][to] { indeg[to] -= 1; if indeg[to] == 0 { q.push(to); } } to += 1; } } seen == n\n}",
        }),
        Problem("lc_word_search_exists", "LC Word Search Exists", "Return true if `word` can be formed by adjacent cells in a semicolon-separated board.", ["Adjacent means up/down/left/right.", "Each cell can be used at most once in a path.", "Rows have equal length."], "bool", [{"name": "rows", "type": "string"}, {"name": "word", "type": "string"}], [case({"rows": "ABCE;SFCS;ADEE", "word": "ABCCED"}, True), case({"rows": "ABCE;SFCS;ADEE", "word": "SEE"}, True), case({"rows": "ABCE;SFCS;ADEE", "word": "ABCB"}, False)], lc("word-search"), "medium", {
            "c": "static int lc_word_search_dfs(char g[16][16], int r, int c, int x, int y, const char *w, int p) { if (w[p] == '\\0') return 1; if (x < 0 || x >= r || y < 0 || y >= c || g[x][y] != w[p]) return 0; char old = g[x][y]; g[x][y] = '#'; int ok = lc_word_search_dfs(g,r,c,x+1,y,w,p+1) || lc_word_search_dfs(g,r,c,x-1,y,w,p+1) || lc_word_search_dfs(g,r,c,x,y+1,w,p+1) || lc_word_search_dfs(g,r,c,x,y-1,w,p+1); g[x][y] = old; return ok; }\nint lc_word_search_exists(const char *rows, const char *word) {\n    char g[16][16]; int r = 0, c = 0, cols = 0, i = 0;\n    while (rows[i] != '\\0') { c = 0; while (rows[i] != '\\0' && rows[i] != ';') g[r][c++] = rows[i++]; if (cols == 0) cols = c; r++; if (rows[i] == ';') i++; }\n    for (int x = 0; x < r; x++) for (int y = 0; y < cols; y++) if (lc_word_search_dfs(g, r, cols, x, y, word, 0)) return 1;\n    return 0;\n}",
            "java": "class LcWordSearchExists {\n    static boolean dfs(char[][] g, int x, int y, String w, int p) { if (p == w.length()) return true; if (x < 0 || x >= g.length || y < 0 || y >= g[0].length || g[x][y] != w.charAt(p)) return false; char old = g[x][y]; g[x][y] = '#'; boolean ok = dfs(g,x+1,y,w,p+1) || dfs(g,x-1,y,w,p+1) || dfs(g,x,y+1,w,p+1) || dfs(g,x,y-1,w,p+1); g[x][y] = old; return ok; }\n    public static boolean lc_word_search_exists(String rows, String word) {\n        String[] rs = rows.split(\";\"); char[][] g = new char[rs.length][rs[0].length()]; for (int i = 0; i < rs.length; i++) g[i] = rs[i].toCharArray();\n        for (int i = 0; i < g.length; i++) for (int j = 0; j < g[0].length; j++) if (dfs(g, i, j, word, 0)) return true; return false;\n    }\n}",
            "rust": "pub fn lc_word_search_exists(rows: &str, word: &str) -> bool {\n    fn dfs(g: &mut Vec<Vec<u8>>, x: i32, y: i32, w: &[u8], p: usize) -> bool { if p == w.len() { return true; } if x < 0 || y < 0 || x >= g.len() as i32 || y >= g[0].len() as i32 || g[x as usize][y as usize] != w[p] { return false; } let old = g[x as usize][y as usize]; g[x as usize][y as usize] = b'#'; let ok = dfs(g,x+1,y,w,p+1) || dfs(g,x-1,y,w,p+1) || dfs(g,x,y+1,w,p+1) || dfs(g,x,y-1,w,p+1); g[x as usize][y as usize] = old; ok }\n    let mut g: Vec<Vec<u8>> = rows.split(';').map(|s| s.as_bytes().to_vec()).collect(); let w = word.as_bytes(); let mut i = 0usize; while i < g.len() { let mut j = 0usize; while j < g[0].len() { if dfs(&mut g, i as i32, j as i32, w, 0) { return true; } j += 1; } i += 1; } false\n}",
        }),
        Problem("lc_maximal_rectangle_area_rows", "LC Maximal Rectangle Area Rows", "Return the area of the largest all-1 rectangle in a semicolon-separated binary matrix.", ["Rows contain only `0` and `1`.", "All rows have equal positive length.", "The empty string returns `0`."], "int", [{"name": "rows", "type": "string"}], [case({"rows": "10100;10111;11111;10010"}, 6), case({"rows": "0"}, 0), case({"rows": "1"}, 1)], lc("maximal-rectangle"), "hard", {
            "c": "int lc_maximal_rectangle_area_rows(const char *rows) {\n    if (rows[0] == '\\0') return 0;\n    char g[64][64]; int r = 0, c = 0, cols = 0, i = 0;\n    while (rows[i] != '\\0') { c = 0; while (rows[i] == '0' || rows[i] == '1') g[r][c++] = rows[i++]; if (cols == 0) cols = c; r++; if (rows[i] == ';') i++; }\n    int h[64] = {0}, best = 0, st[65];\n    for (int x = 0; x < r; x++) { for (int y = 0; y < cols; y++) h[y] = g[x][y] == '1' ? h[y] + 1 : 0; int top = 0; for (int y = 0; y <= cols; y++) { int cur = y == cols ? 0 : h[y]; while (top > 0 && h[st[top - 1]] > cur) { int height = h[st[--top]]; int left = top == 0 ? -1 : st[top - 1]; int area = height * (y - left - 1); if (area > best) best = area; } st[top++] = y; } }\n    return best;\n}",
            "java": "class LcMaximalRectangleAreaRows {\n    public static int lc_maximal_rectangle_area_rows(String rows) {\n        if (rows.isEmpty()) return 0; String[] rs = rows.split(\";\"); int r = rs.length, c = rs[0].length(), best = 0; int[] h = new int[c], st = new int[c + 1];\n        for (int i = 0; i < r; i++) { for (int j = 0; j < c; j++) h[j] = rs[i].charAt(j) == '1' ? h[j] + 1 : 0; int top = 0; for (int j = 0; j <= c; j++) { int cur = j == c ? 0 : h[j]; while (top > 0 && h[st[top - 1]] > cur) { int height = h[st[--top]]; int left = top == 0 ? -1 : st[top - 1]; int area = height * (j - left - 1); if (area > best) best = area; } st[top++] = j; } } return best;\n    }\n}",
            "rust": "pub fn lc_maximal_rectangle_area_rows(rows: &str) -> i32 {\n    if rows.is_empty() { return 0; } let rs: Vec<&[u8]> = rows.split(';').map(|s| s.as_bytes()).collect(); let c = rs[0].len(); let mut h = vec![0i32; c]; let mut best = 0;\n    for row in rs { let mut j = 0usize; while j < c { h[j] = if row[j] == b'1' { h[j] + 1 } else { 0 }; j += 1; } let mut st: Vec<usize> = Vec::new(); j = 0; while j <= c { let cur = if j == c { 0 } else { h[j] }; while !st.is_empty() && h[*st.last().unwrap()] > cur { let idx = st.pop().unwrap(); let left = if st.is_empty() { -1 } else { *st.last().unwrap() as i32 }; let area = h[idx] * (j as i32 - left - 1); if area > best { best = area; } } st.push(j); j += 1; } }\n    best\n}",
        }),
        Problem("luogu_p5711_leap_year_bool", "Luogu P5711 Leap Year Bool", "Return true if `year` is a Gregorian leap year.", ["Use the standard rule: divisible by 400, or divisible by 4 and not by 100."], "bool", [{"name": "year", "type": "int"}], [case({"year": 2000}, True), case({"year": 1900}, False), case({"year": 2024}, True)], lg("P5711"), "easy", {
            "c": "int luogu_p5711_leap_year_bool(int year) {\n    return year % 400 == 0 || (year % 4 == 0 && year % 100 != 0);\n}",
            "java": "class LuoguP5711LeapYearBool {\n    public static boolean luogu_p5711_leap_year_bool(int year) {\n        return year % 400 == 0 || (year % 4 == 0 && year % 100 != 0);\n    }\n}",
            "rust": "pub fn luogu_p5711_leap_year_bool(year: i32) -> bool {\n    year % 400 == 0 || (year % 4 == 0 && year % 100 != 0)\n}",
        }),
        Problem("luogu_p5742_excellent_count", "Luogu P5742 Excellent Count", "Count students satisfying Luogu P5742's excellent condition.", ["Rows are encoded as `id,academic,quality;...`.", "A student is excellent if `academic + quality > 140` and `7*academic + 3*quality >= 800`."], "int", [{"name": "rows", "type": "string"}], [case({"rows": "1,80,80;2,90,70;3,60,90"}, 2), case({"rows": "1,70,70;2,100,30"}, 0)], lg("P5742"), "easy", {
            "c": "int luogu_p5742_excellent_count(const char *rows) {\n    int ans = 0, i = 0;\n    while (rows[i] != '\\0') { int id = 0, a = 0, q = 0; while (rows[i] >= '0' && rows[i] <= '9') { id = id * 10 + rows[i] - '0'; i++; } if (rows[i] == ',') i++; while (rows[i] >= '0' && rows[i] <= '9') { a = a * 10 + rows[i] - '0'; i++; } if (rows[i] == ',') i++; while (rows[i] >= '0' && rows[i] <= '9') { q = q * 10 + rows[i] - '0'; i++; } if (a + q > 140 && 7 * a + 3 * q >= 800) ans++; if (rows[i] == ';') i++; }\n    return ans;\n}",
            "java": "class LuoguP5742ExcellentCount {\n    public static int luogu_p5742_excellent_count(String rows) {\n        int ans = 0; for (String row : rows.split(\";\")) { String[] p = row.split(\",\"); int a = Integer.parseInt(p[1]), q = Integer.parseInt(p[2]); if (a + q > 140 && 7 * a + 3 * q >= 800) ans++; } return ans;\n    }\n}",
            "rust": "pub fn luogu_p5742_excellent_count(rows: &str) -> i32 {\n    let mut ans = 0; for row in rows.split(';') { let p: Vec<i32> = row.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let a = p[1]; let q = p[2]; if a + q > 140 && 7 * a + 3 * q >= 800 { ans += 1; } } ans\n}",
        }),
        Problem("ex_nucleotide_count_char", "Exercism Nucleotide Count Char", "Return how many times nucleotide `target` appears in DNA string `dna`.", ["`target` is a one-character string among `A,C,G,T`.", "`dna` contains only valid DNA nucleotides."], "int", [{"name": "dna", "type": "string"}, {"name": "target", "type": "string"}], [case({"dna": "GATTACA", "target": "A"}, 3), case({"dna": "CCCCC", "target": "C"}, 5), case({"dna": "", "target": "G"}, 0)], ex("nucleotide-count"), "easy", {
            "c": "int ex_nucleotide_count_char(const char *dna, const char *target) {\n    int ans = 0; for (int i = 0; dna[i] != '\\0'; i++) if (dna[i] == target[0]) ans++; return ans;\n}",
            "java": "class ExNucleotideCountChar {\n    public static int ex_nucleotide_count_char(String dna, String target) {\n        char t = target.charAt(0); int ans = 0; for (int i = 0; i < dna.length(); i++) if (dna.charAt(i) == t) ans++; return ans;\n    }\n}",
            "rust": "pub fn ex_nucleotide_count_char(dna: &str, target: &str) -> i32 {\n    let t = target.as_bytes()[0]; let mut ans = 0; for ch in dna.bytes() { if ch == t { ans += 1; } } ans\n}",
        }),
        Problem("ex_queen_attack_bool", "Exercism Queen Attack Bool", "Return true if two queens can attack each other.", ["Coordinates are zero-based row/column pairs.", "Queens attack along the same row, column, or diagonal."], "bool", [{"name": "r1", "type": "int"}, {"name": "c1", "type": "int"}, {"name": "r2", "type": "int"}, {"name": "c2", "type": "int"}], [case({"r1": 2, "c1": 4, "r2": 2, "c2": 6}, True), case({"r1": 2, "c1": 4, "r2": 6, "c2": 4}, True), case({"r1": 2, "c1": 4, "r2": 6, "c2": 7}, False)], ex("queen-attack"), "easy", {
            "c": "int ex_queen_attack_bool(int r1, int c1, int r2, int c2) {\n    int dr = r1 - r2, dc = c1 - c2; if (dr < 0) dr = -dr; if (dc < 0) dc = -dc; return r1 == r2 || c1 == c2 || dr == dc;\n}",
            "java": "class ExQueenAttackBool {\n    public static boolean ex_queen_attack_bool(int r1, int c1, int r2, int c2) {\n        return r1 == r2 || c1 == c2 || Math.abs(r1 - r2) == Math.abs(c1 - c2);\n    }\n}",
            "rust": "pub fn ex_queen_attack_bool(r1: i32, c1: i32, r2: i32, c2: i32) -> bool {\n    r1 == r2 || c1 == c2 || (r1 - r2).abs() == (c1 - c2).abs()\n}",
        }),
    ]


def more_real_source_problems_8() -> list[Problem]:
    lc = lambda slug: source("LeetCode", slug, f"https://leetcode.com/problems/{slug}/")
    lg = lambda slug: source("Luogu", slug, f"https://www.luogu.com.cn/problem/{slug}")
    ex = lambda slug: source(
        "Exercism",
        slug,
        f"https://github.com/exercism/problem-specifications/tree/main/exercises/{slug}",
        "MIT",
    )
    return [
        Problem("lc_valid_perfect_square_bool", "LC Valid Perfect Square Bool", "Return true if `num` is a perfect square.", ["`num > 0`.", "Use integer arithmetic only."], "bool", [{"name": "num", "type": "int"}], [case({"num": 16}, True), case({"num": 14}, False), case({"num": 1}, True)], lc("valid-perfect-square"), "easy", {
            "c": "int lc_valid_perfect_square_bool(int num) {\n    long long l = 1, r = num;\n    while (l <= r) { long long m = (l + r) / 2, sq = m * m; if (sq == num) return 1; if (sq < num) l = m + 1; else r = m - 1; }\n    return 0;\n}",
            "java": "class LcValidPerfectSquareBool {\n    public static boolean lc_valid_perfect_square_bool(int num) {\n        long l = 1, r = num; while (l <= r) { long m = (l + r) / 2, sq = m * m; if (sq == num) return true; if (sq < num) l = m + 1; else r = m - 1; } return false;\n    }\n}",
            "rust": "pub fn lc_valid_perfect_square_bool(num: i32) -> bool {\n    let mut l: i64 = 1; let mut r: i64 = num as i64; while l <= r { let m = (l + r) / 2; let sq = m * m; if sq == num as i64 { return true; } if sq < num as i64 { l = m + 1; } else { r = m - 1; } } false\n}",
        }),
        Problem("lc_happy_number_bool", "LC Happy Number Bool", "Return true if repeated sum-of-squares of digits reaches `1`.", ["`n > 0`.", "Use cycle detection by the known bounded digit-square process."], "bool", [{"name": "n", "type": "int"}], [case({"n": 19}, True), case({"n": 2}, False), case({"n": 1}, True)], lc("happy-number"), "easy", {
            "c": "int lc_happy_number_bool(int n) {\n    int seen[1000] = {0};\n    while (n != 1 && !seen[n]) { seen[n] = 1; int s = 0; while (n > 0) { int d = n % 10; s += d * d; n /= 10; } n = s; }\n    return n == 1;\n}",
            "java": "class LcHappyNumberBool {\n    public static boolean lc_happy_number_bool(int n) {\n        boolean[] seen = new boolean[1000]; while (n != 1 && !seen[n]) { seen[n] = true; int s = 0; while (n > 0) { int d = n % 10; s += d * d; n /= 10; } n = s; } return n == 1;\n    }\n}",
            "rust": "pub fn lc_happy_number_bool(mut n: i32) -> bool {\n    let mut seen = vec![false; 1000]; while n != 1 && !seen[n as usize] { seen[n as usize] = true; let mut s = 0; while n > 0 { let d = n % 10; s += d * d; n /= 10; } n = s; } n == 1\n}",
        }),
        Problem("lc_count_primes_below", "LC Count Primes Below", "Return the number of prime numbers strictly less than `n`.", ["`0 <= n <= 10000`."], "int", [{"name": "n", "type": "int"}], [case({"n": 10}, 4), case({"n": 0}, 0), case({"n": 100}, 25)], lc("count-primes"), "medium", {
            "c": "int lc_count_primes_below(int n) {\n    if (n <= 2) return 0;\n    int is[10000]; for (int i = 0; i < n; i++) is[i] = 1; is[0] = is[1] = 0;\n    for (int p = 2; p * p < n; p++) if (is[p]) for (int x = p * p; x < n; x += p) is[x] = 0;\n    int ans = 0; for (int i = 2; i < n; i++) if (is[i]) ans++; return ans;\n}",
            "java": "class LcCountPrimesBelow {\n    public static int lc_count_primes_below(int n) {\n        if (n <= 2) return 0; boolean[] is = new boolean[n]; for (int i = 2; i < n; i++) is[i] = true; for (int p = 2; p * p < n; p++) if (is[p]) for (int x = p * p; x < n; x += p) is[x] = false; int ans = 0; for (int i = 2; i < n; i++) if (is[i]) ans++; return ans;\n    }\n}",
            "rust": "pub fn lc_count_primes_below(n: i32) -> i32 {\n    if n <= 2 { return 0; } let nn = n as usize; let mut is = vec![true; nn]; is[0] = false; is[1] = false; let mut p = 2usize; while p * p < nn { if is[p] { let mut x = p * p; while x < nn { is[x] = false; x += p; } } p += 1; } let mut ans = 0; for v in is { if v { ans += 1; } } ans\n}",
        }),
        Problem("lc_integer_break_max_product", "LC Integer Break Max Product", "Break `n` into at least two positive integers and return the maximum product.", ["`2 <= n <= 58`.", "The answer fits in signed 32-bit integer range."], "int", [{"name": "n", "type": "int"}], [case({"n": 2}, 1), case({"n": 10}, 36), case({"n": 8}, 18)], lc("integer-break"), "medium", {
            "c": "int lc_integer_break_max_product(int n) {\n    int dp[59] = {0}; dp[1] = 1;\n    for (int i = 2; i <= n; i++) for (int j = 1; j < i; j++) { int a = j > dp[j] ? j : dp[j]; int b = i - j > dp[i - j] ? i - j : dp[i - j]; if (a * b > dp[i]) dp[i] = a * b; }\n    return dp[n];\n}",
            "java": "class LcIntegerBreakMaxProduct {\n    public static int lc_integer_break_max_product(int n) {\n        int[] dp = new int[n + 1]; dp[1] = 1; for (int i = 2; i <= n; i++) for (int j = 1; j < i; j++) dp[i] = Math.max(dp[i], Math.max(j, dp[j]) * Math.max(i - j, dp[i - j])); return dp[n];\n    }\n}",
            "rust": "pub fn lc_integer_break_max_product(n: i32) -> i32 {\n    let mut dp = vec![0; (n + 1) as usize]; dp[1] = 1; let mut i = 2; while i <= n { let mut j = 1; while j < i { let a = if j > dp[j as usize] { j } else { dp[j as usize] }; let b = if i - j > dp[(i - j) as usize] { i - j } else { dp[(i - j) as usize] }; if a * b > dp[i as usize] { dp[i as usize] = a * b; } j += 1; } i += 1; } dp[n as usize]\n}",
        }),
        Problem("lc_unique_bst_count", "LC Unique Binary Search Trees Count", "Return how many structurally unique BSTs can store values `1..n`.", ["`0 <= n <= 19`.", "This is the Catalan-number DP used by the original problem."], "int", [{"name": "n", "type": "int"}], [case({"n": 1}, 1), case({"n": 3}, 5), case({"n": 5}, 42)], lc("unique-binary-search-trees"), "medium", {
            "c": "int lc_unique_bst_count(int n) {\n    int dp[20] = {0}; dp[0] = 1;\n    for (int nodes = 1; nodes <= n; nodes++) for (int root = 1; root <= nodes; root++) dp[nodes] += dp[root - 1] * dp[nodes - root];\n    return dp[n];\n}",
            "java": "class LcUniqueBstCount {\n    public static int lc_unique_bst_count(int n) {\n        int[] dp = new int[n + 1]; dp[0] = 1; for (int nodes = 1; nodes <= n; nodes++) for (int root = 1; root <= nodes; root++) dp[nodes] += dp[root - 1] * dp[nodes - root]; return dp[n];\n    }\n}",
            "rust": "pub fn lc_unique_bst_count(n: i32) -> i32 {\n    let mut dp = vec![0; (n + 1) as usize]; dp[0] = 1; let mut nodes = 1; while nodes <= n { let mut root = 1; while root <= nodes { dp[nodes as usize] += dp[(root - 1) as usize] * dp[(nodes - root) as usize]; root += 1; } nodes += 1; } dp[n as usize]\n}",
        }),
        Problem("lc_stock_cooldown_profit_csv", "LC Stock Cooldown Profit CSV", "Return the maximum stock profit with as many transactions as desired and a one-day cooldown after selling.", ["`prices` is a nonempty comma-separated list of nonnegative integers."], "int", [{"name": "prices", "type": "string"}], [case({"prices": "1,2,3,0,2"}, 3), case({"prices": "1"}, 0), case({"prices": "6,1,3,2,4,7"}, 6)], lc("best-time-to-buy-and-sell-stock-with-cooldown"), "medium", {
            "c": "int lc_stock_cooldown_profit_csv(const char *prices) {\n    int a[256], n = 0, i = 0; while (prices[i] != '\\0') { int v = 0; while (prices[i] >= '0' && prices[i] <= '9') { v = v * 10 + prices[i] - '0'; i++; } a[n++] = v; if (prices[i] == ',') i++; }\n    int hold = -a[0], sold = 0, rest = 0;\n    for (int d = 1; d < n; d++) { int old_hold = hold, old_sold = sold; hold = hold > rest - a[d] ? hold : rest - a[d]; sold = old_hold + a[d]; rest = rest > old_sold ? rest : old_sold; }\n    return sold > rest ? sold : rest;\n}",
            "java": "class LcStockCooldownProfitCsv {\n    public static int lc_stock_cooldown_profit_csv(String prices) {\n        String[] p = prices.split(\",\"); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); int hold = -a[0], sold = 0, rest = 0;\n        for (int i = 1; i < a.length; i++) { int oldHold = hold, oldSold = sold; hold = Math.max(hold, rest - a[i]); sold = oldHold + a[i]; rest = Math.max(rest, oldSold); } return Math.max(sold, rest);\n    }\n}",
            "rust": "pub fn lc_stock_cooldown_profit_csv(prices: &str) -> i32 {\n    let a: Vec<i32> = prices.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut hold = -a[0]; let mut sold = 0; let mut rest = 0;\n    let mut i = 1usize; while i < a.len() { let old_hold = hold; let old_sold = sold; hold = if hold > rest - a[i] { hold } else { rest - a[i] }; sold = old_hold + a[i]; rest = if rest > old_sold { rest } else { old_sold }; i += 1; } if sold > rest { sold } else { rest }\n}",
        }),
        Problem("luogu_p5710_property_mask", "Luogu P5710 Property Mask", "Return the four boolean results from Luogu P5710 packed as bits 0..3.", ["For input `x`, the predicates are: even and greater than 4; even or greater than 4; exactly one of those; neither.", "Bit `i` is set when predicate `i` is true."], "int", [{"name": "x", "type": "int"}], [case({"x": 6}, 3), case({"x": 3}, 8), case({"x": 4}, 6), case({"x": 5}, 6)], lg("P5710"), "easy", {
            "c": "int luogu_p5710_property_mask(int x) {\n    int a = x % 2 == 0, b = x > 4, ans = 0; if (a && b) ans |= 1; if (a || b) ans |= 2; if (a != b) ans |= 4; if (!a && !b) ans |= 8; return ans;\n}",
            "java": "class LuoguP5710PropertyMask {\n    public static int luogu_p5710_property_mask(int x) {\n        boolean a = x % 2 == 0, b = x > 4; int ans = 0; if (a && b) ans |= 1; if (a || b) ans |= 2; if (a != b) ans |= 4; if (!a && !b) ans |= 8; return ans;\n    }\n}",
            "rust": "pub fn luogu_p5710_property_mask(x: i32) -> i32 {\n    let a = x % 2 == 0; let b = x > 4; let mut ans = 0; if a && b { ans |= 1; } if a || b { ans |= 2; } if a != b { ans |= 4; } if !a && !b { ans |= 8; } ans\n}",
        }),
        Problem("luogu_p5727_hailstone_length", "Luogu P5727 Hailstone Length", "Return how many numbers appear in the Collatz sequence from `n` down to `1`, including both endpoints.", ["`n >= 1`.", "Use `n/2` for even values and `3*n+1` for odd values."], "int", [{"name": "n", "type": "int"}], [case({"n": 1}, 1), case({"n": 3}, 8), case({"n": 10}, 7)], lg("P5727"), "easy", {
            "c": "int luogu_p5727_hailstone_length(int n) {\n    int len = 1; while (n != 1) { if (n % 2 == 0) n /= 2; else n = 3 * n + 1; len++; } return len;\n}",
            "java": "class LuoguP5727HailstoneLength {\n    public static int luogu_p5727_hailstone_length(int n) {\n        int len = 1; while (n != 1) { if (n % 2 == 0) n /= 2; else n = 3 * n + 1; len++; } return len;\n    }\n}",
            "rust": "pub fn luogu_p5727_hailstone_length(mut n: i32) -> i32 {\n    let mut len = 1; while n != 1 { if n % 2 == 0 { n /= 2; } else { n = 3 * n + 1; } len += 1; } len\n}",
        }),
        Problem("ex_saddle_points_count_rows", "Exercism Saddle Points Count Rows", "Count saddle points in an integer matrix.", ["Rows are semicolon-separated and values inside a row are comma-separated.", "A saddle point is at least every value in its row and at most every value in its column."], "int", [{"name": "rows", "type": "string"}], [case({"rows": "9,8,7;5,3,2;6,6,7"}, 1), case({"rows": "4,5,4;3,5,5;1,5,4"}, 3), case({"rows": "1,2;3,4"}, 0)], ex("saddle-points"), "medium", {
            "c": "int ex_saddle_points_count_rows(const char *rows) {\n    int a[32][32], r = 0, c = 0, cols = 0, i = 0;\n    while (rows[i] != '\\0') { c = 0; while (rows[i] != '\\0' && rows[i] != ';') { int sign = 1, v = 0; if (rows[i] == '-') { sign = -1; i++; } while (rows[i] >= '0' && rows[i] <= '9') { v = v * 10 + rows[i] - '0'; i++; } a[r][c++] = sign * v; if (rows[i] == ',') i++; } if (cols == 0) cols = c; r++; if (rows[i] == ';') i++; }\n    int ans = 0; for (int x = 0; x < r; x++) for (int y = 0; y < cols; y++) { int ok = 1; for (int j = 0; j < cols; j++) if (a[x][j] > a[x][y]) ok = 0; for (int j = 0; j < r; j++) if (a[j][y] < a[x][y]) ok = 0; if (ok) ans++; }\n    return ans;\n}",
            "java": "class ExSaddlePointsCountRows {\n    public static int ex_saddle_points_count_rows(String rows) {\n        String[] rs = rows.split(\";\"); int r = rs.length, c = rs[0].split(\",\").length; int[][] a = new int[r][c]; for (int i = 0; i < r; i++) { String[] p = rs[i].split(\",\"); for (int j = 0; j < c; j++) a[i][j] = Integer.parseInt(p[j]); }\n        int ans = 0; for (int i = 0; i < r; i++) for (int j = 0; j < c; j++) { boolean ok = true; for (int y = 0; y < c; y++) if (a[i][y] > a[i][j]) ok = false; for (int x = 0; x < r; x++) if (a[x][j] < a[i][j]) ok = false; if (ok) ans++; } return ans;\n    }\n}",
            "rust": "pub fn ex_saddle_points_count_rows(rows: &str) -> i32 {\n    let a: Vec<Vec<i32>> = rows.split(';').map(|r| r.split(',').map(|x| x.parse::<i32>().unwrap()).collect()).collect(); let r = a.len(); let c = a[0].len(); let mut ans = 0;\n    let mut i = 0usize; while i < r { let mut j = 0usize; while j < c { let mut ok = true; let mut y = 0usize; while y < c { if a[i][y] > a[i][j] { ok = false; } y += 1; } let mut x = 0usize; while x < r { if a[x][j] < a[i][j] { ok = false; } x += 1; } if ok { ans += 1; } j += 1; } i += 1; } ans\n}",
        }),
    ]


def more_real_source_problems_9() -> list[Problem]:
    lc = lambda slug: source("LeetCode", slug, f"https://leetcode.com/problems/{slug}/")
    lg = lambda slug: source("Luogu", slug, f"https://www.luogu.com.cn/problem/{slug}")
    ex = lambda slug: source(
        "Exercism",
        slug,
        f"https://github.com/exercism/problem-specifications/tree/main/exercises/{slug}",
        "MIT",
    )
    return [
        Problem("lc_isomorphic_strings_bool", "LC Isomorphic Strings Bool", "Return true if two ASCII strings are isomorphic.", ["Both strings have the same length.", "A bijection between characters must preserve order."], "bool", [{"name": "s", "type": "string"}, {"name": "t", "type": "string"}], [case({"s": "egg", "t": "add"}, True), case({"s": "foo", "t": "bar"}, False), case({"s": "paper", "t": "title"}, True)], lc("isomorphic-strings"), "easy", {
            "c": "int lc_isomorphic_strings_bool(const char *s, const char *t) {\n    int st[256] = {0}, ts[256] = {0};\n    for (int i = 0; s[i] != '\\0'; i++) { unsigned char a = (unsigned char)s[i], b = (unsigned char)t[i]; if (st[a] != ts[b]) return 0; st[a] = i + 1; ts[b] = i + 1; }\n    return 1;\n}",
            "java": "class LcIsomorphicStringsBool {\n    public static boolean lc_isomorphic_strings_bool(String s, String t) {\n        int[] st = new int[256], ts = new int[256]; for (int i = 0; i < s.length(); i++) { int a = s.charAt(i), b = t.charAt(i); if (st[a] != ts[b]) return false; st[a] = i + 1; ts[b] = i + 1; } return true;\n    }\n}",
            "rust": "pub fn lc_isomorphic_strings_bool(s: &str, t: &str) -> bool {\n    let sb = s.as_bytes(); let tb = t.as_bytes(); let mut st = [0usize; 256]; let mut ts = [0usize; 256]; let mut i = 0usize; while i < sb.len() { let a = sb[i] as usize; let b = tb[i] as usize; if st[a] != ts[b] { return false; } st[a] = i + 1; ts[b] = i + 1; i += 1; } true\n}",
        }),
        Problem("lc_word_pattern_bool", "LC Word Pattern Bool", "Return true if pattern letters bijectively match the words in `s`.", ["Words in `s` are separated by single spaces.", "Pattern is lowercase ASCII."], "bool", [{"name": "pattern", "type": "string"}, {"name": "s", "type": "string"}], [case({"pattern": "abba", "s": "dog cat cat dog"}, True), case({"pattern": "abba", "s": "dog cat cat fish"}, False), case({"pattern": "aaaa", "s": "dog cat cat dog"}, False)], lc("word-pattern"), "easy", {
            "c": "int lc_word_pattern_bool(const char *pattern, const char *s) {\n    char words[64][32]; int wn = 0, i = 0;\n    while (s[i] != '\\0') { int j = 0; while (s[i] != '\\0' && s[i] != ' ') words[wn][j++] = s[i++]; words[wn][j] = '\\0'; wn++; if (s[i] == ' ') i++; }\n    int pn = 0; while (pattern[pn] != '\\0') pn++; if (pn != wn) return 0;\n    for (int a = 0; a < pn; a++) for (int b = a + 1; b < pn; b++) { int samep = pattern[a] == pattern[b]; int samew = 1; for (int k = 0; words[a][k] != '\\0' || words[b][k] != '\\0'; k++) if (words[a][k] != words[b][k]) samew = 0; if (samep != samew) return 0; }\n    return 1;\n}",
            "java": "class LcWordPatternBool {\n    public static boolean lc_word_pattern_bool(String pattern, String s) {\n        String[] w = s.split(\" \"); if (w.length != pattern.length()) return false; for (int i = 0; i < w.length; i++) for (int j = i + 1; j < w.length; j++) if ((pattern.charAt(i) == pattern.charAt(j)) != w[i].equals(w[j])) return false; return true;\n    }\n}",
            "rust": "pub fn lc_word_pattern_bool(pattern: &str, s: &str) -> bool {\n    let words: Vec<&str> = s.split(' ').collect(); let p = pattern.as_bytes(); if p.len() != words.len() { return false; } let mut i = 0usize; while i < p.len() { let mut j = i + 1; while j < p.len() { if (p[i] == p[j]) != (words[i] == words[j]) { return false; } j += 1; } i += 1; } true\n}",
        }),
        Problem("lc_valid_palindrome_ii_bool", "LC Valid Palindrome II Bool", "Return true if `s` can be a palindrome after deleting at most one character.", ["Input is lowercase ASCII."], "bool", [{"name": "s", "type": "string"}], [case({"s": "aba"}, True), case({"s": "abca"}, True), case({"s": "abc"}, False)], lc("valid-palindrome-ii"), "easy", {
            "c": "static int lc_vp2_range(const char *s, int l, int r) { while (l < r) { if (s[l] != s[r]) return 0; l++; r--; } return 1; }\nint lc_valid_palindrome_ii_bool(const char *s) {\n    int r = 0; while (s[r] != '\\0') r++; r--;\n    int l = 0; while (l < r) { if (s[l] != s[r]) return lc_vp2_range(s, l + 1, r) || lc_vp2_range(s, l, r - 1); l++; r--; }\n    return 1;\n}",
            "java": "class LcValidPalindromeIiBool {\n    static boolean ok(String s, int l, int r) { while (l < r) { if (s.charAt(l++) != s.charAt(r--)) return false; } return true; }\n    public static boolean lc_valid_palindrome_ii_bool(String s) {\n        int l = 0, r = s.length() - 1; while (l < r) { if (s.charAt(l) != s.charAt(r)) return ok(s, l + 1, r) || ok(s, l, r - 1); l++; r--; } return true;\n    }\n}",
            "rust": "pub fn lc_valid_palindrome_ii_bool(s: &str) -> bool {\n    fn ok(b: &[u8], mut l: usize, mut r: usize) -> bool { while l < r { if b[l] != b[r] { return false; } l += 1; r -= 1; } true }\n    let b = s.as_bytes(); let mut l = 0usize; let mut r = b.len() - 1; while l < r { if b[l] != b[r] { return ok(b, l + 1, r) || ok(b, l, r - 1); } l += 1; r -= 1; } true\n}",
        }),
        Problem("lc_power_of_three_bool", "LC Power Of Three Bool", "Return true if `n` is a positive power of three.", ["`n` is a signed 32-bit integer."], "bool", [{"name": "n", "type": "int"}], [case({"n": 27}, True), case({"n": 0}, False), case({"n": 45}, False)], lc("power-of-three"), "easy", {
            "c": "int lc_power_of_three_bool(int n) {\n    if (n <= 0) return 0;\n    while (n % 3 == 0) n /= 3;\n    return n == 1;\n}",
            "java": "class LcPowerOfThreeBool {\n    public static boolean lc_power_of_three_bool(int n) {\n        if (n <= 0) return false; while (n % 3 == 0) n /= 3; return n == 1;\n    }\n}",
            "rust": "pub fn lc_power_of_three_bool(mut n: i32) -> bool {\n    if n <= 0 { return false; } while n % 3 == 0 { n /= 3; } n == 1\n}",
        }),
        Problem("lc_range_sum_query_csv", "LC Range Sum Query CSV", "Return the sum of comma-separated `nums[left..right]` inclusive.", ["`nums` is nonempty.", "`0 <= left <= right < len(nums)`."], "int", [{"name": "nums", "type": "string"}, {"name": "left", "type": "int"}, {"name": "right", "type": "int"}], [case({"nums": "-2,0,3,-5,2,-1", "left": 0, "right": 2}, 1), case({"nums": "-2,0,3,-5,2,-1", "left": 2, "right": 5}, -1), case({"nums": "5", "left": 0, "right": 0}, 5)], lc("range-sum-query-immutable"), "easy", {
            "c": "int lc_range_sum_query_csv(const char *nums, int left, int right) {\n    int idx = 0, i = 0, sum = 0; while (nums[i] != '\\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } if (idx >= left && idx <= right) sum += sign * v; idx++; if (nums[i] == ',') i++; } return sum;\n}",
            "java": "class LcRangeSumQueryCsv {\n    public static int lc_range_sum_query_csv(String nums, int left, int right) {\n        String[] p = nums.split(\",\"); int sum = 0; for (int i = left; i <= right; i++) sum += Integer.parseInt(p[i]); return sum;\n    }\n}",
            "rust": "pub fn lc_range_sum_query_csv(nums: &str, left: i32, right: i32) -> i32 {\n    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut sum = 0; let mut i = left as usize; while i <= right as usize { sum += a[i]; i += 1; } sum\n}",
        }),
        Problem("lc_arithmetic_slices_count_csv", "LC Arithmetic Slices Count CSV", "Return how many contiguous arithmetic subarrays of length at least 3 exist.", ["`nums` is a nonempty comma-separated list of integers."], "int", [{"name": "nums", "type": "string"}], [case({"nums": "1,2,3,4"}, 3), case({"nums": "1"}, 0), case({"nums": "1,3,5,7,9"}, 6)], lc("arithmetic-slices"), "medium", {
            "c": "int lc_arithmetic_slices_count_csv(const char *nums) {\n    int a[256], n = 0, i = 0; while (nums[i] != '\\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } a[n++] = sign * v; if (nums[i] == ',') i++; }\n    int cur = 0, ans = 0; for (int j = 2; j < n; j++) { if (a[j] - a[j - 1] == a[j - 1] - a[j - 2]) cur++; else cur = 0; ans += cur; } return ans;\n}",
            "java": "class LcArithmeticSlicesCountCsv {\n    public static int lc_arithmetic_slices_count_csv(String nums) {\n        String[] p = nums.split(\",\"); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); int cur = 0, ans = 0; for (int i = 2; i < a.length; i++) { if (a[i] - a[i - 1] == a[i - 1] - a[i - 2]) cur++; else cur = 0; ans += cur; } return ans;\n    }\n}",
            "rust": "pub fn lc_arithmetic_slices_count_csv(nums: &str) -> i32 {\n    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut cur = 0; let mut ans = 0; let mut i = 2usize; while i < a.len() { if a[i] - a[i - 1] == a[i - 1] - a[i - 2] { cur += 1; } else { cur = 0; } ans += cur; i += 1; } ans\n}",
        }),
        Problem("luogu_p5703_apple_purchase", "Luogu P5703 Apple Purchase", "Return the total number of apples bought as `a * b`.", ["`a` and `b` are nonnegative integers."], "int", [{"name": "a", "type": "int"}, {"name": "b", "type": "int"}], [case({"a": 2, "b": 3}, 6), case({"a": 0, "b": 5}, 0), case({"a": 7, "b": 8}, 56)], lg("P5703"), "easy", {
            "c": "int luogu_p5703_apple_purchase(int a, int b) {\n    return a * b;\n}",
            "java": "class LuoguP5703ApplePurchase {\n    public static int luogu_p5703_apple_purchase(int a, int b) {\n        return a * b;\n    }\n}",
            "rust": "pub fn luogu_p5703_apple_purchase(a: i32, b: i32) -> i32 {\n    a * b\n}",
        }),
        Problem("ex_matrix_row_sum", "Exercism Matrix Row Sum", "Return the sum of a one-based row from a matrix string.", ["Rows are semicolon-separated and values inside a row are comma-separated.", "`row` is one-based."], "int", [{"name": "rows", "type": "string"}, {"name": "row", "type": "int"}], [case({"rows": "1,2;3,4", "row": 1}, 3), case({"rows": "1,2;3,4", "row": 2}, 7), case({"rows": "9", "row": 1}, 9)], ex("matrix"), "easy", {
            "c": "int ex_matrix_row_sum(const char *rows, int row) {\n    int current = 1, i = 0, sum = 0;\n    while (rows[i] != '\\0') { int sign = 1, v = 0; if (rows[i] == '-') { sign = -1; i++; } while (rows[i] >= '0' && rows[i] <= '9') { v = v * 10 + rows[i] - '0'; i++; } if (current == row) sum += sign * v; if (rows[i] == ';') { current++; i++; } else if (rows[i] == ',') i++; }\n    return sum;\n}",
            "java": "class ExMatrixRowSum {\n    public static int ex_matrix_row_sum(String rows, int row) {\n        String[] rs = rows.split(\";\"); int sum = 0; for (String p : rs[row - 1].split(\",\")) sum += Integer.parseInt(p); return sum;\n    }\n}",
            "rust": "pub fn ex_matrix_row_sum(rows: &str, row: i32) -> i32 {\n    rows.split(';').nth((row - 1) as usize).unwrap().split(',').map(|x| x.parse::<i32>().unwrap()).sum()\n}",
        }),
    ]


def more_real_source_problems_10() -> list[Problem]:
    lc = lambda slug: source("LeetCode", slug, f"https://leetcode.com/problems/{slug}/")
    lg = lambda slug: source("Luogu", slug, f"https://www.luogu.com.cn/problem/{slug}")
    ex = lambda slug: source(
        "Exercism",
        slug,
        f"https://github.com/exercism/problem-specifications/tree/main/exercises/{slug}",
        "MIT",
    )
    return [
        Problem("lc_max_product_three_csv", "LC Maximum Product Of Three Numbers CSV", "Return the maximum product of any three integers in comma-separated `nums`.", ["`nums` contains at least three integers.", "The result fits in signed 32-bit integer range."], "int", [{"name": "nums", "type": "string"}], [case({"nums": "1,2,3"}, 6), case({"nums": "1,2,3,4"}, 24), case({"nums": "-1,-2,-3"}, -6), case({"nums": "-100,-98,-1,2,3,4"}, 39200)], lc("maximum-product-of-three-numbers"), "easy", {
            "c": "int lc_max_product_three_csv(const char *nums) {\n    int max1 = -2147483647, max2 = -2147483647, max3 = -2147483647, min1 = 2147483647, min2 = 2147483647, i = 0;\n    while (nums[i] != '\\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } v *= sign; if (v > max1) { max3 = max2; max2 = max1; max1 = v; } else if (v > max2) { max3 = max2; max2 = v; } else if (v > max3) max3 = v; if (v < min1) { min2 = min1; min1 = v; } else if (v < min2) min2 = v; if (nums[i] == ',') i++; }\n    int a = max1 * max2 * max3, b = max1 * min1 * min2; return a > b ? a : b;\n}",
            "java": "class LcMaxProductThreeCsv {\n    public static int lc_max_product_three_csv(String nums) {\n        String[] p = nums.split(\",\"); int max1 = Integer.MIN_VALUE, max2 = Integer.MIN_VALUE, max3 = Integer.MIN_VALUE, min1 = Integer.MAX_VALUE, min2 = Integer.MAX_VALUE;\n        for (String part : p) { int v = Integer.parseInt(part); if (v > max1) { max3 = max2; max2 = max1; max1 = v; } else if (v > max2) { max3 = max2; max2 = v; } else if (v > max3) max3 = v; if (v < min1) { min2 = min1; min1 = v; } else if (v < min2) min2 = v; }\n        return Math.max(max1 * max2 * max3, max1 * min1 * min2);\n    }\n}",
            "rust": "pub fn lc_max_product_three_csv(nums: &str) -> i32 {\n    let mut a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); a.sort(); let n = a.len(); let p1 = a[n - 1] * a[n - 2] * a[n - 3]; let p2 = a[n - 1] * a[0] * a[1]; if p1 > p2 { p1 } else { p2 }\n}",
        }),
        Problem("lc_island_perimeter_rows", "LC Island Perimeter Rows", "Return the perimeter of land cells in a semicolon-separated 0/1 grid.", ["Rows contain only `0` and `1`.", "All rows have equal positive length."], "int", [{"name": "rows", "type": "string"}], [case({"rows": "0100;1110;0100;1100"}, 16), case({"rows": "1"}, 4), case({"rows": "11"}, 6)], lc("island-perimeter"), "easy", {
            "c": "int lc_island_perimeter_rows(const char *rows) {\n    char g[64][64]; int r = 0, c = 0, cols = 0, i = 0;\n    while (rows[i] != '\\0') { c = 0; while (rows[i] == '0' || rows[i] == '1') g[r][c++] = rows[i++]; if (cols == 0) cols = c; r++; if (rows[i] == ';') i++; }\n    int ans = 0; for (int x = 0; x < r; x++) for (int y = 0; y < cols; y++) if (g[x][y] == '1') { ans += 4; if (x > 0 && g[x - 1][y] == '1') ans -= 2; if (y > 0 && g[x][y - 1] == '1') ans -= 2; }\n    return ans;\n}",
            "java": "class LcIslandPerimeterRows {\n    public static int lc_island_perimeter_rows(String rows) {\n        String[] rs = rows.split(\";\"); int r = rs.length, c = rs[0].length(), ans = 0;\n        for (int i = 0; i < r; i++) for (int j = 0; j < c; j++) if (rs[i].charAt(j) == '1') { ans += 4; if (i > 0 && rs[i - 1].charAt(j) == '1') ans -= 2; if (j > 0 && rs[i].charAt(j - 1) == '1') ans -= 2; }\n        return ans;\n    }\n}",
            "rust": "pub fn lc_island_perimeter_rows(rows: &str) -> i32 {\n    let g: Vec<&[u8]> = rows.split(';').map(|s| s.as_bytes()).collect(); let r = g.len(); let c = g[0].len(); let mut ans = 0; let mut i = 0usize; while i < r { let mut j = 0usize; while j < c { if g[i][j] == b'1' { ans += 4; if i > 0 && g[i - 1][j] == b'1' { ans -= 2; } if j > 0 && g[i][j - 1] == b'1' { ans -= 2; } } j += 1; } i += 1; } ans\n}",
        }),
        Problem("lc_robot_return_origin_bool", "LC Robot Return To Origin Bool", "Return true if robot moves return to coordinate `(0,0)`.", ["`moves` contains only `U`, `D`, `L`, and `R`."], "bool", [{"name": "moves", "type": "string"}], [case({"moves": "UD"}, True), case({"moves": "LL"}, False), case({"moves": "UDLRRLLD"}, False)], lc("robot-return-to-origin"), "easy", {
            "c": "int lc_robot_return_origin_bool(const char *moves) {\n    int x = 0, y = 0; for (int i = 0; moves[i] != '\\0'; i++) { if (moves[i] == 'U') y++; else if (moves[i] == 'D') y--; else if (moves[i] == 'L') x--; else if (moves[i] == 'R') x++; } return x == 0 && y == 0;\n}",
            "java": "class LcRobotReturnOriginBool {\n    public static boolean lc_robot_return_origin_bool(String moves) {\n        int x = 0, y = 0; for (int i = 0; i < moves.length(); i++) { char ch = moves.charAt(i); if (ch == 'U') y++; else if (ch == 'D') y--; else if (ch == 'L') x--; else if (ch == 'R') x++; } return x == 0 && y == 0;\n    }\n}",
            "rust": "pub fn lc_robot_return_origin_bool(moves: &str) -> bool {\n    let mut x = 0; let mut y = 0; for ch in moves.bytes() { if ch == b'U' { y += 1; } else if ch == b'D' { y -= 1; } else if ch == b'L' { x -= 1; } else if ch == b'R' { x += 1; } } x == 0 && y == 0\n}",
        }),
        Problem("lc_monotonic_array_bool_csv", "LC Monotonic Array Bool CSV", "Return true if comma-separated `nums` is monotone nondecreasing or nonincreasing.", ["`nums` is nonempty."], "bool", [{"name": "nums", "type": "string"}], [case({"nums": "1,2,2,3"}, True), case({"nums": "6,5,4,4"}, True), case({"nums": "1,3,2"}, False)], lc("monotonic-array"), "easy", {
            "c": "int lc_monotonic_array_bool_csv(const char *nums) {\n    int prev = 0, first = 1, inc = 1, dec = 1, i = 0;\n    while (nums[i] != '\\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } v *= sign; if (!first) { if (v < prev) inc = 0; if (v > prev) dec = 0; } first = 0; prev = v; if (nums[i] == ',') i++; }\n    return inc || dec;\n}",
            "java": "class LcMonotonicArrayBoolCsv {\n    public static boolean lc_monotonic_array_bool_csv(String nums) {\n        String[] p = nums.split(\",\"); boolean inc = true, dec = true; int prev = Integer.parseInt(p[0]); for (int i = 1; i < p.length; i++) { int v = Integer.parseInt(p[i]); if (v < prev) inc = false; if (v > prev) dec = false; prev = v; } return inc || dec;\n    }\n}",
            "rust": "pub fn lc_monotonic_array_bool_csv(nums: &str) -> bool {\n    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut inc = true; let mut dec = true; let mut i = 1usize; while i < a.len() { if a[i] < a[i - 1] { inc = false; } if a[i] > a[i - 1] { dec = false; } i += 1; } inc || dec\n}",
        }),
        Problem("lc_toeplitz_matrix_bool_rows", "LC Toeplitz Matrix Bool Rows", "Return true if every diagonal from top-left to bottom-right has the same value.", ["Rows are semicolon-separated and values in a row are comma-separated.", "All rows have equal positive length."], "bool", [{"name": "rows", "type": "string"}], [case({"rows": "1,2,3,4;5,1,2,3;9,5,1,2"}, True), case({"rows": "1,2;2,2"}, False)], lc("toeplitz-matrix"), "easy", {
            "c": "int lc_toeplitz_matrix_bool_rows(const char *rows) {\n    int a[64][64], r = 0, c = 0, cols = 0, i = 0;\n    while (rows[i] != '\\0') { c = 0; while (rows[i] != '\\0' && rows[i] != ';') { int sign = 1, v = 0; if (rows[i] == '-') { sign = -1; i++; } while (rows[i] >= '0' && rows[i] <= '9') { v = v * 10 + rows[i] - '0'; i++; } a[r][c++] = sign * v; if (rows[i] == ',') i++; } if (cols == 0) cols = c; r++; if (rows[i] == ';') i++; }\n    for (int x = 1; x < r; x++) {\n        for (int y = 1; y < cols; y++) if (a[x][y] != a[x - 1][y - 1]) return 0;\n    }\n    return 1;\n}",
            "java": "class LcToeplitzMatrixBoolRows {\n    public static boolean lc_toeplitz_matrix_bool_rows(String rows) {\n        String[] rs = rows.split(\";\"); int r = rs.length, c = rs[0].split(\",\").length; int[][] a = new int[r][c]; for (int i = 0; i < r; i++) { String[] p = rs[i].split(\",\"); for (int j = 0; j < c; j++) a[i][j] = Integer.parseInt(p[j]); }\n        for (int i = 1; i < r; i++) for (int j = 1; j < c; j++) if (a[i][j] != a[i - 1][j - 1]) return false; return true;\n    }\n}",
            "rust": "pub fn lc_toeplitz_matrix_bool_rows(rows: &str) -> bool {\n    let a: Vec<Vec<i32>> = rows.split(';').map(|r| r.split(',').map(|x| x.parse::<i32>().unwrap()).collect()).collect(); let mut i = 1usize; while i < a.len() { let mut j = 1usize; while j < a[0].len() { if a[i][j] != a[i - 1][j - 1] { return false; } j += 1; } i += 1; } true\n}",
        }),
        Problem("lc_three_sum_closest_csv", "LC 3Sum Closest CSV", "Return the sum of three integers in `nums` closest to `target`.", ["`nums` contains at least three integers.", "There is exactly one closest answer in supplied tests."], "int", [{"name": "nums", "type": "string"}, {"name": "target", "type": "int"}], [case({"nums": "-1,2,1,-4", "target": 1}, 2), case({"nums": "0,0,0", "target": 1}, 0), case({"nums": "1,1,1,0", "target": -100}, 2)], lc("3sum-closest"), "medium", {
            "c": "int lc_three_sum_closest_csv(const char *nums, int target) {\n    int a[256], n = 0, i = 0; while (nums[i] != '\\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } a[n++] = sign * v; if (nums[i] == ',') i++; }\n    for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) if (a[y] < a[x]) { int t = a[x]; a[x] = a[y]; a[y] = t; }\n    int best = a[0] + a[1] + a[2];\n    for (int x = 0; x < n - 2; x++) { int l = x + 1, r = n - 1; while (l < r) { int sum = a[x] + a[l] + a[r]; int d1 = sum - target; if (d1 < 0) d1 = -d1; int d2 = best - target; if (d2 < 0) d2 = -d2; if (d1 < d2) best = sum; if (sum < target) l++; else r--; } }\n    return best;\n}",
            "java": "class LcThreeSumClosestCsv {\n    public static int lc_three_sum_closest_csv(String nums, int target) {\n        String[] p = nums.split(\",\"); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); java.util.Arrays.sort(a); int best = a[0] + a[1] + a[2];\n        for (int i = 0; i < a.length - 2; i++) { int l = i + 1, r = a.length - 1; while (l < r) { int sum = a[i] + a[l] + a[r]; if (Math.abs(sum - target) < Math.abs(best - target)) best = sum; if (sum < target) l++; else r--; } } return best;\n    }\n}",
            "rust": "pub fn lc_three_sum_closest_csv(nums: &str, target: i32) -> i32 {\n    let mut a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); a.sort(); let mut best = a[0] + a[1] + a[2]; let mut i = 0usize; while i + 2 < a.len() { let mut l = i + 1; let mut r = a.len() - 1; while l < r { let sum = a[i] + a[l] + a[r]; if (sum - target).abs() < (best - target).abs() { best = sum; } if sum < target { l += 1; } else { r -= 1; } } i += 1; } best\n}",
        }),
        Problem("luogu_p5729_remaining_cubes", "Luogu P5729 Remaining Cubes", "Return how many unit cubes remain after deleting inclusive cuboids from a `w*x*h` block.", ["Cuboids are encoded as `x1,y1,z1,x2,y2,z2;...` using one-based inclusive coordinates.", "The empty cuboid string deletes nothing.", "`w`, `x`, and `h` are at most 20 in supplied tests."], "int", [{"name": "w", "type": "int"}, {"name": "x", "type": "int"}, {"name": "h", "type": "int"}, {"name": "cuts", "type": "string"}], [case({"w": 2, "x": 2, "h": 2, "cuts": "1,1,1,1,1,1"}, 7), case({"w": 3, "x": 3, "h": 3, "cuts": "1,1,1,3,3,1;2,2,2,2,2,3"}, 16), case({"w": 2, "x": 2, "h": 1, "cuts": ""}, 4)], lg("P5729"), "medium", {
            "c": "int luogu_p5729_remaining_cubes(int w, int x, int h, const char *cuts) {\n    int used[21][21][21] = {{{0}}}, i = 0;\n    while (cuts[i] != '\\0') { int v[6]; for (int k = 0; k < 6; k++) { v[k] = 0; while (cuts[i] >= '0' && cuts[i] <= '9') { v[k] = v[k] * 10 + cuts[i] - '0'; i++; } if (cuts[i] == ',') i++; } for (int a = v[0]; a <= v[3]; a++) for (int b = v[1]; b <= v[4]; b++) for (int c = v[2]; c <= v[5]; c++) used[a][b][c] = 1; if (cuts[i] == ';') i++; }\n    int left = 0; for (int a = 1; a <= w; a++) for (int b = 1; b <= x; b++) for (int c = 1; c <= h; c++) if (!used[a][b][c]) left++; return left;\n}",
            "java": "class LuoguP5729RemainingCubes {\n    public static int luogu_p5729_remaining_cubes(int w, int x, int h, String cuts) {\n        boolean[][][] used = new boolean[w + 1][x + 1][h + 1]; if (!cuts.isEmpty()) for (String cut : cuts.split(\";\")) { String[] p = cut.split(\",\"); int[] v = new int[6]; for (int i = 0; i < 6; i++) v[i] = Integer.parseInt(p[i]); for (int a = v[0]; a <= v[3]; a++) for (int b = v[1]; b <= v[4]; b++) for (int c = v[2]; c <= v[5]; c++) used[a][b][c] = true; }\n        int left = 0; for (int a = 1; a <= w; a++) for (int b = 1; b <= x; b++) for (int c = 1; c <= h; c++) if (!used[a][b][c]) left++; return left;\n    }\n}",
            "rust": "pub fn luogu_p5729_remaining_cubes(w: i32, x: i32, h: i32, cuts: &str) -> i32 {\n    let mut used = vec![vec![vec![false; (h + 1) as usize]; (x + 1) as usize]; (w + 1) as usize]; if !cuts.is_empty() { for cut in cuts.split(';') { let v: Vec<usize> = cut.split(',').map(|p| p.parse::<usize>().unwrap()).collect(); let mut a = v[0]; while a <= v[3] { let mut b = v[1]; while b <= v[4] { let mut c = v[2]; while c <= v[5] { used[a][b][c] = true; c += 1; } b += 1; } a += 1; } } }\n    let mut left = 0; let mut a = 1usize; while a <= w as usize { let mut b = 1usize; while b <= x as usize { let mut c = 1usize; while c <= h as usize { if !used[a][b][c] { left += 1; } c += 1; } b += 1; } a += 1; } left\n}",
        }),
        Problem("luogu_p5743_monkey_peaches", "Luogu P5743 Monkey Peaches", "Return the initial number of peaches if after `n` days of eating half plus one each day, one peach remains.", ["`n >= 1`.", "Work backward from the final remaining peach."], "int", [{"name": "n", "type": "int"}], [case({"n": 1}, 1), case({"n": 2}, 4), case({"n": 3}, 10), case({"n": 5}, 94)], lg("P5743"), "easy", {
            "c": "int luogu_p5743_monkey_peaches(int n) {\n    int peaches = 1; for (int day = 1; day < n; day++) peaches = (peaches + 1) * 2; return peaches;\n}",
            "java": "class LuoguP5743MonkeyPeaches {\n    public static int luogu_p5743_monkey_peaches(int n) {\n        int peaches = 1; for (int day = 1; day < n; day++) peaches = (peaches + 1) * 2; return peaches;\n    }\n}",
            "rust": "pub fn luogu_p5743_monkey_peaches(n: i32) -> i32 {\n    let mut peaches = 1; let mut day = 1; while day < n { peaches = (peaches + 1) * 2; day += 1; } peaches\n}",
        }),
        Problem("ex_scrabble_score", "Exercism Scrabble Score", "Return the Scrabble score of an ASCII word.", ["Letters are scored case-insensitively.", "Nonletters score zero."], "int", [{"name": "word", "type": "string"}], [case({"word": "cabbage"}, 14), case({"word": "quirky"}, 22), case({"word": ""}, 0)], ex("scrabble-score"), "easy", {
            "c": "int ex_scrabble_score(const char *word) {\n    int score[26] = {1,3,3,2,1,4,2,4,1,8,5,1,3,1,1,3,10,1,1,1,1,4,4,8,4,10}; int ans = 0;\n    for (int i = 0; word[i] != '\\0'; i++) { char ch = word[i]; if (ch >= 'A' && ch <= 'Z') ch = ch - 'A' + 'a'; if (ch >= 'a' && ch <= 'z') ans += score[ch - 'a']; }\n    return ans;\n}",
            "java": "class ExScrabbleScore {\n    public static int ex_scrabble_score(String word) {\n        int[] score = {1,3,3,2,1,4,2,4,1,8,5,1,3,1,1,3,10,1,1,1,1,4,4,8,4,10}; int ans = 0; for (int i = 0; i < word.length(); i++) { char ch = Character.toLowerCase(word.charAt(i)); if (ch >= 'a' && ch <= 'z') ans += score[ch - 'a']; } return ans;\n    }\n}",
            "rust": "pub fn ex_scrabble_score(word: &str) -> i32 {\n    let score = [1,3,3,2,1,4,2,4,1,8,5,1,3,1,1,3,10,1,1,1,1,4,4,8,4,10]; let mut ans = 0; for mut ch in word.bytes() { if ch >= b'A' && ch <= b'Z' { ch = ch - b'A' + b'a'; } if ch >= b'a' && ch <= b'z' { ans += score[(ch - b'a') as usize]; } } ans\n}",
        }),
        Problem("ex_anagram_count", "Exercism Anagram Count", "Count candidate words that are anagrams of `subject` but not equal to it ignoring case.", ["Candidates are separated by semicolons.", "Inputs are ASCII alphabetic words."], "int", [{"name": "subject", "type": "string"}, {"name": "candidates", "type": "string"}], [case({"subject": "listen", "candidates": "enlists;google;inlets;banana"}, 1), case({"subject": "master", "candidates": "stream;pigeon;maters"}, 2), case({"subject": "BANANA", "candidates": "banana;Banana"}, 0)], ex("anagram"), "medium", {
            "c": "static void ex_anagram_counts(const char *s, int start, int end, int out[26]) { for (int i = 0; i < 26; i++) out[i] = 0; for (int i = start; i < end; i++) { char ch = s[i]; if (ch >= 'A' && ch <= 'Z') ch = ch - 'A' + 'a'; out[ch - 'a']++; } }\nint ex_anagram_count(const char *subject, const char *candidates) {\n    int sl = 0; while (subject[sl] != '\\0') sl++; int base[26]; ex_anagram_counts(subject, 0, sl, base); int ans = 0, i = 0;\n    while (candidates[i] != '\\0') { int start = i; while (candidates[i] != '\\0' && candidates[i] != ';') i++; int end = i, same = sl == end - start; for (int k = 0; same && k < sl; k++) { char a = subject[k], b = candidates[start + k]; if (a >= 'A' && a <= 'Z') a = a - 'A' + 'a'; if (b >= 'A' && b <= 'Z') b = b - 'A' + 'a'; if (a != b) same = 0; } int cur[26]; ex_anagram_counts(candidates, start, end, cur); int ok = !same; for (int k = 0; k < 26; k++) if (base[k] != cur[k]) ok = 0; if (ok) ans++; if (candidates[i] == ';') i++; }\n    return ans;\n}",
            "java": "class ExAnagramCount {\n    static int[] counts(String s) { int[] c = new int[26]; for (int i = 0; i < s.length(); i++) c[Character.toLowerCase(s.charAt(i)) - 'a']++; return c; }\n    public static int ex_anagram_count(String subject, String candidates) {\n        int[] base = counts(subject); String lower = subject.toLowerCase(); int ans = 0; for (String cand : candidates.split(\";\")) { if (cand.toLowerCase().equals(lower)) continue; int[] cur = counts(cand); boolean ok = true; for (int i = 0; i < 26; i++) if (base[i] != cur[i]) ok = false; if (ok) ans++; } return ans;\n    }\n}",
            "rust": "pub fn ex_anagram_count(subject: &str, candidates: &str) -> i32 {\n    fn counts(s: &str) -> [i32; 26] { let mut c = [0; 26]; for mut ch in s.bytes() { if ch >= b'A' && ch <= b'Z' { ch = ch - b'A' + b'a'; } c[(ch - b'a') as usize] += 1; } c }\n    let base = counts(subject); let lower = subject.to_ascii_lowercase(); let mut ans = 0; for cand in candidates.split(';') { if cand.to_ascii_lowercase() == lower { continue; } if counts(cand) == base { ans += 1; } } ans\n}",
        }),
    ]


def more_real_source_problems_11() -> list[Problem]:
    lc = lambda slug: source("LeetCode", slug, f"https://leetcode.com/problems/{slug}/")
    return [
        Problem("lc_find_difference_ascii", "LC Find The Difference ASCII", "Return the ASCII code of the extra character in `t` compared with `s`.", ["`t` is formed by shuffling `s` and adding one extra lowercase letter."], "int", [{"name": "s", "type": "string"}, {"name": "t", "type": "string"}], [case({"s": "abcd", "t": "abcde"}, 101), case({"s": "", "t": "y"}, 121), case({"s": "a", "t": "aa"}, 97)], lc("find-the-difference"), "easy", {
            "c": "int lc_find_difference_ascii(const char *s, const char *t) {\n    int x = 0; for (int i = 0; s[i] != '\\0'; i++) x ^= s[i]; for (int i = 0; t[i] != '\\0'; i++) x ^= t[i]; return x;\n}",
            "java": "class LcFindDifferenceAscii {\n    public static int lc_find_difference_ascii(String s, String t) {\n        int x = 0; for (int i = 0; i < s.length(); i++) x ^= s.charAt(i); for (int i = 0; i < t.length(); i++) x ^= t.charAt(i); return x;\n    }\n}",
            "rust": "pub fn lc_find_difference_ascii(s: &str, t: &str) -> i32 {\n    let mut x = 0u8; for b in s.bytes() { x ^= b; } for b in t.bytes() { x ^= b; } x as i32\n}",
        }),
        Problem("lc_ransom_note_bool", "LC Ransom Note Bool", "Return true if `ransom` can be constructed from letters in `magazine`.", ["Inputs contain lowercase English letters."], "bool", [{"name": "ransom", "type": "string"}, {"name": "magazine", "type": "string"}], [case({"ransom": "a", "magazine": "b"}, False), case({"ransom": "aa", "magazine": "ab"}, False), case({"ransom": "aa", "magazine": "aab"}, True)], lc("ransom-note"), "easy", {
            "c": "int lc_ransom_note_bool(const char *ransom, const char *magazine) {\n    int cnt[26] = {0}; for (int i = 0; magazine[i] != '\\0'; i++) cnt[magazine[i] - 'a']++; for (int i = 0; ransom[i] != '\\0'; i++) if (--cnt[ransom[i] - 'a'] < 0) return 0; return 1;\n}",
            "java": "class LcRansomNoteBool {\n    public static boolean lc_ransom_note_bool(String ransom, String magazine) {\n        int[] cnt = new int[26]; for (int i = 0; i < magazine.length(); i++) cnt[magazine.charAt(i) - 'a']++; for (int i = 0; i < ransom.length(); i++) if (--cnt[ransom.charAt(i) - 'a'] < 0) return false; return true;\n    }\n}",
            "rust": "pub fn lc_ransom_note_bool(ransom: &str, magazine: &str) -> bool {\n    let mut cnt = [0i32; 26]; for b in magazine.bytes() { cnt[(b - b'a') as usize] += 1; } for b in ransom.bytes() { let i = (b - b'a') as usize; cnt[i] -= 1; if cnt[i] < 0 { return false; } } true\n}",
        }),
        Problem("lc_can_place_flowers_bool_csv", "LC Can Place Flowers Bool CSV", "Return true if `n` new flowers can be planted without adjacent flowers.", ["`bed` is a comma-separated list of `0` and `1`.", "Existing flowers are not adjacent."], "bool", [{"name": "bed", "type": "string"}, {"name": "n", "type": "int"}], [case({"bed": "1,0,0,0,1", "n": 1}, True), case({"bed": "1,0,0,0,1", "n": 2}, False), case({"bed": "0,0,1,0,0", "n": 2}, True)], lc("can-place-flowers"), "easy", {
            "c": "int lc_can_place_flowers_bool_csv(const char *bed, int n) {\n    int a[256], len = 0, i = 0; while (bed[i] != '\\0') { a[len++] = bed[i] - '0'; i++; if (bed[i] == ',') i++; }\n    for (int j = 0; j < len && n > 0; j++) if (a[j] == 0 && (j == 0 || a[j - 1] == 0) && (j == len - 1 || a[j + 1] == 0)) { a[j] = 1; n--; }\n    return n <= 0;\n}",
            "java": "class LcCanPlaceFlowersBoolCsv {\n    public static boolean lc_can_place_flowers_bool_csv(String bed, int n) {\n        String[] p = bed.split(\",\"); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); for (int i = 0; i < a.length && n > 0; i++) if (a[i] == 0 && (i == 0 || a[i - 1] == 0) && (i == a.length - 1 || a[i + 1] == 0)) { a[i] = 1; n--; } return n <= 0;\n    }\n}",
            "rust": "pub fn lc_can_place_flowers_bool_csv(bed: &str, mut n: i32) -> bool {\n    let mut a: Vec<i32> = bed.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut i = 0usize; while i < a.len() && n > 0 { if a[i] == 0 && (i == 0 || a[i - 1] == 0) && (i == a.len() - 1 || a[i + 1] == 0) { a[i] = 1; n -= 1; } i += 1; } n <= 0\n}",
        }),
        Problem("lc_teemo_attacking_duration_csv", "LC Teemo Attacking Duration CSV", "Return total poisoned duration from attack times and a fixed duration.", ["`times` is a nonempty sorted comma-separated list of attack times.", "`duration > 0`."], "int", [{"name": "times", "type": "string"}, {"name": "duration", "type": "int"}], [case({"times": "1,4", "duration": 2}, 4), case({"times": "1,2", "duration": 2}, 3), case({"times": "5", "duration": 10}, 10)], lc("teemo-attacking"), "easy", {
            "c": "int lc_teemo_attacking_duration_csv(const char *times, int duration) {\n    int prev = -1000000000, ans = 0, i = 0; while (times[i] != '\\0') { int v = 0; while (times[i] >= '0' && times[i] <= '9') { v = v * 10 + times[i] - '0'; i++; } if (prev < 0) ans += duration; else ans += v - prev < duration ? v - prev : duration; prev = v; if (times[i] == ',') i++; } return ans;\n}",
            "java": "class LcTeemoAttackingDurationCsv {\n    public static int lc_teemo_attacking_duration_csv(String times, int duration) {\n        String[] p = times.split(\",\"); int ans = duration, prev = Integer.parseInt(p[0]); for (int i = 1; i < p.length; i++) { int v = Integer.parseInt(p[i]); ans += Math.min(duration, v - prev); prev = v; } return ans;\n    }\n}",
            "rust": "pub fn lc_teemo_attacking_duration_csv(times: &str, duration: i32) -> i32 {\n    let a: Vec<i32> = times.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut ans = duration; let mut i = 1usize; while i < a.len() { let gap = a[i] - a[i - 1]; ans += if gap < duration { gap } else { duration }; i += 1; } ans\n}",
        }),
        Problem("lc_degree_shortest_subarray_csv", "LC Degree Of Array Shortest Subarray CSV", "Return the shortest contiguous subarray length with the same degree as the whole array.", ["`nums` is a nonempty comma-separated list of nonnegative integers less than 1000."], "int", [{"name": "nums", "type": "string"}], [case({"nums": "1,2,2,3,1"}, 2), case({"nums": "1,2,2,3,1,4,2"}, 6), case({"nums": "1"}, 1)], lc("degree-of-an-array"), "easy", {
            "c": "int lc_degree_shortest_subarray_csv(const char *nums) {\n    int first[1000], count[1000] = {0}, best = 1000000, degree = 0, idx = 0, i = 0; for (int k = 0; k < 1000; k++) first[k] = -1;\n    while (nums[i] != '\\0') { int v = 0; while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } if (first[v] < 0) first[v] = idx; count[v]++; int len = idx - first[v] + 1; if (count[v] > degree) { degree = count[v]; best = len; } else if (count[v] == degree && len < best) best = len; idx++; if (nums[i] == ',') i++; }\n    return best;\n}",
            "java": "class LcDegreeShortestSubarrayCsv {\n    public static int lc_degree_shortest_subarray_csv(String nums) {\n        int[] first = new int[1000], count = new int[1000]; java.util.Arrays.fill(first, -1); String[] p = nums.split(\",\"); int degree = 0, best = 1000000;\n        for (int i = 0; i < p.length; i++) { int v = Integer.parseInt(p[i]); if (first[v] < 0) first[v] = i; count[v]++; int len = i - first[v] + 1; if (count[v] > degree) { degree = count[v]; best = len; } else if (count[v] == degree && len < best) best = len; } return best;\n    }\n}",
            "rust": "pub fn lc_degree_shortest_subarray_csv(nums: &str) -> i32 {\n    let a: Vec<usize> = nums.split(',').map(|x| x.parse::<usize>().unwrap()).collect(); let mut first = vec![-1i32; 1000]; let mut count = vec![0i32; 1000]; let mut degree = 0; let mut best = 1000000; for (i, &v) in a.iter().enumerate() { if first[v] < 0 { first[v] = i as i32; } count[v] += 1; let len = i as i32 - first[v] + 1; if count[v] > degree { degree = count[v]; best = len; } else if count[v] == degree && len < best { best = len; } } best\n}",
        }),
        Problem("lc_subarray_product_less_than_k_csv", "LC Subarray Product Less Than K CSV", "Return how many contiguous subarrays have product strictly less than `k`.", ["`nums` is a nonempty comma-separated list of positive integers.", "`k >= 0`."], "int", [{"name": "nums", "type": "string"}, {"name": "k", "type": "int"}], [case({"nums": "10,5,2,6", "k": 100}, 8), case({"nums": "1,2,3", "k": 0}, 0), case({"nums": "1,1,1", "k": 2}, 6)], lc("subarray-product-less-than-k"), "medium", {
            "c": "int lc_subarray_product_less_than_k_csv(const char *nums, int k) {\n    if (k <= 1) return 0;\n    int a[256], n = 0, i = 0;\n    while (nums[i] != '\\0') { int v = 0; while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } a[n++] = v; if (nums[i] == ',') i++; }\n    int left = 0, prod = 1, ans = 0; for (int right = 0; right < n; right++) { prod *= a[right]; while (prod >= k) prod /= a[left++]; ans += right - left + 1; } return ans;\n}",
            "java": "class LcSubarrayProductLessThanKCsv {\n    public static int lc_subarray_product_less_than_k_csv(String nums, int k) {\n        if (k <= 1) return 0; String[] p = nums.split(\",\"); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); int left = 0, prod = 1, ans = 0; for (int right = 0; right < a.length; right++) { prod *= a[right]; while (prod >= k) prod /= a[left++]; ans += right - left + 1; } return ans;\n    }\n}",
            "rust": "pub fn lc_subarray_product_less_than_k_csv(nums: &str, k: i32) -> i32 {\n    if k <= 1 { return 0; } let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut left = 0usize; let mut prod = 1; let mut ans = 0; let mut right = 0usize; while right < a.len() { prod *= a[right]; while prod >= k { prod /= a[left]; left += 1; } ans += (right - left + 1) as i32; right += 1; } ans\n}",
        }),
        Problem("lc_min_cost_climbing_stairs_csv", "LC Min Cost Climbing Stairs CSV", "Return the minimum cost to reach the top of the staircase.", ["`cost` is a comma-separated list of nonnegative integers.", "You may start at step 0 or step 1."], "int", [{"name": "cost", "type": "string"}], [case({"cost": "10,15,20"}, 15), case({"cost": "1,100,1,1,1,100,1,1,100,1"}, 6), case({"cost": "0,0"}, 0)], lc("min-cost-climbing-stairs"), "easy", {
            "c": "int lc_min_cost_climbing_stairs_csv(const char *cost) {\n    int a[256], n = 0, i = 0; while (cost[i] != '\\0') { int v = 0; while (cost[i] >= '0' && cost[i] <= '9') { v = v * 10 + cost[i] - '0'; i++; } a[n++] = v; if (cost[i] == ',') i++; }\n    int p2 = 0, p1 = 0; for (int j = 2; j <= n; j++) { int x = p1 + a[j - 1], y = p2 + a[j - 2], cur = x < y ? x : y; p2 = p1; p1 = cur; } return p1;\n}",
            "java": "class LcMinCostClimbingStairsCsv {\n    public static int lc_min_cost_climbing_stairs_csv(String cost) {\n        String[] p = cost.split(\",\"); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); int p2 = 0, p1 = 0; for (int i = 2; i <= a.length; i++) { int cur = Math.min(p1 + a[i - 1], p2 + a[i - 2]); p2 = p1; p1 = cur; } return p1;\n    }\n}",
            "rust": "pub fn lc_min_cost_climbing_stairs_csv(cost: &str) -> i32 {\n    let a: Vec<i32> = cost.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut p2 = 0; let mut p1 = 0; let mut i = 2usize; while i <= a.len() { let x = p1 + a[i - 1]; let y = p2 + a[i - 2]; let cur = if x < y { x } else { y }; p2 = p1; p1 = cur; i += 1; } p1\n}",
        }),
        Problem("lc_delete_and_earn_csv", "LC Delete And Earn CSV", "Return the maximum points from the delete-and-earn rule.", ["`nums` is a nonempty comma-separated list of positive integers less than 1000."], "int", [{"name": "nums", "type": "string"}], [case({"nums": "3,4,2"}, 6), case({"nums": "2,2,3,3,3,4"}, 9), case({"nums": "1"}, 1)], lc("delete-and-earn"), "medium", {
            "c": "int lc_delete_and_earn_csv(const char *nums) {\n    int points[1000] = {0}, i = 0, maxv = 0; while (nums[i] != '\\0') { int v = 0; while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } points[v] += v; if (v > maxv) maxv = v; if (nums[i] == ',') i++; }\n    int take = 0, skip = 0; for (int v = 1; v <= maxv; v++) { int ntake = skip + points[v]; int nskip = take > skip ? take : skip; take = ntake; skip = nskip; } return take > skip ? take : skip;\n}",
            "java": "class LcDeleteAndEarnCsv {\n    public static int lc_delete_and_earn_csv(String nums) {\n        int[] points = new int[1000]; int max = 0; for (String p : nums.split(\",\")) { int v = Integer.parseInt(p); points[v] += v; if (v > max) max = v; } int take = 0, skip = 0; for (int v = 1; v <= max; v++) { int ntake = skip + points[v], nskip = Math.max(take, skip); take = ntake; skip = nskip; } return Math.max(take, skip);\n    }\n}",
            "rust": "pub fn lc_delete_and_earn_csv(nums: &str) -> i32 {\n    let mut points = vec![0; 1000]; let mut maxv = 0usize; for part in nums.split(',') { let v = part.parse::<usize>().unwrap(); points[v] += v as i32; if v > maxv { maxv = v; } } let mut take = 0; let mut skip = 0; let mut v = 1usize; while v <= maxv { let ntake = skip + points[v]; let nskip = if take > skip { take } else { skip }; take = ntake; skip = nskip; v += 1; } if take > skip { take } else { skip }\n}",
        }),
        Problem("lc_partition_labels_count", "LC Partition Labels Count", "Return the number of partitions made by the partition-labels greedy algorithm.", ["Input contains lowercase English letters.", "Each letter appears in at most one returned partition."], "int", [{"name": "s", "type": "string"}], [case({"s": "ababcbacadefegdehijhklij"}, 3), case({"s": "eccbbbbdec"}, 1), case({"s": "abc"}, 3)], lc("partition-labels"), "medium", {
            "c": "int lc_partition_labels_count(const char *s) {\n    int last[26] = {0}; for (int i = 0; s[i] != '\\0'; i++) last[s[i] - 'a'] = i; int ans = 0, end = 0; for (int i = 0; s[i] != '\\0'; i++) { if (last[s[i] - 'a'] > end) end = last[s[i] - 'a']; if (i == end) ans++; } return ans;\n}",
            "java": "class LcPartitionLabelsCount {\n    public static int lc_partition_labels_count(String s) {\n        int[] last = new int[26]; for (int i = 0; i < s.length(); i++) last[s.charAt(i) - 'a'] = i; int ans = 0, end = 0; for (int i = 0; i < s.length(); i++) { end = Math.max(end, last[s.charAt(i) - 'a']); if (i == end) ans++; } return ans;\n    }\n}",
            "rust": "pub fn lc_partition_labels_count(s: &str) -> i32 {\n    let b = s.as_bytes(); let mut last = [0usize; 26]; let mut i = 0usize; while i < b.len() { last[(b[i] - b'a') as usize] = i; i += 1; } let mut ans = 0; let mut end = 0usize; i = 0; while i < b.len() { let l = last[(b[i] - b'a') as usize]; if l > end { end = l; } if i == end { ans += 1; } i += 1; } ans\n}",
        }),
        Problem("lc_longest_palindrome_len", "LC Longest Palindrome Length", "Return the length of the longest palindrome that can be built from the letters of `s`.", ["Input is ASCII letters."], "int", [{"name": "s", "type": "string"}], [case({"s": "abccccdd"}, 7), case({"s": "a"}, 1), case({"s": "Aa"}, 1)], lc("longest-palindrome"), "easy", {
            "c": "int lc_longest_palindrome_len(const char *s) {\n    int cnt[128] = {0}; for (int i = 0; s[i] != '\\0'; i++) cnt[(int)s[i]]++; int ans = 0, odd = 0; for (int i = 0; i < 128; i++) { ans += cnt[i] / 2 * 2; if (cnt[i] % 2) odd = 1; } return ans + odd;\n}",
            "java": "class LcLongestPalindromeLen {\n    public static int lc_longest_palindrome_len(String s) {\n        int[] cnt = new int[128]; for (int i = 0; i < s.length(); i++) cnt[s.charAt(i)]++; int ans = 0; boolean odd = false; for (int v : cnt) { ans += v / 2 * 2; if (v % 2 == 1) odd = true; } return ans + (odd ? 1 : 0);\n    }\n}",
            "rust": "pub fn lc_longest_palindrome_len(s: &str) -> i32 {\n    let mut cnt = [0i32; 128]; for b in s.bytes() { cnt[b as usize] += 1; } let mut ans = 0; let mut odd = 0; for v in cnt { ans += v / 2 * 2; if v % 2 == 1 { odd = 1; } } ans + odd\n}",
        }),
    ]


def more_real_source_problems_12() -> list[Problem]:
    lc = lambda slug: source("LeetCode", slug, f"https://leetcode.com/problems/{slug}/")
    return [
        Problem("lc_lemonade_change_bool_csv", "LC Lemonade Change Bool CSV", "Return true if correct change can be given for every customer.", ["`bills` is a comma-separated list of `5`, `10`, or `20`."], "bool", [{"name": "bills", "type": "string"}], [case({"bills": "5,5,5,10,20"}, True), case({"bills": "5,5,10,10,20"}, False), case({"bills": "5,5,10"}, True)], lc("lemonade-change"), "easy", {
            "c": "int lc_lemonade_change_bool_csv(const char *bills) {\n    int five = 0, ten = 0, i = 0;\n    while (bills[i] != '\\0') { int v = 0; while (bills[i] >= '0' && bills[i] <= '9') { v = v * 10 + bills[i] - '0'; i++; } if (v == 5) five++; else if (v == 10) { if (five == 0) return 0; five--; ten++; } else { if (ten > 0 && five > 0) { ten--; five--; } else if (five >= 3) five -= 3; else return 0; } if (bills[i] == ',') i++; }\n    return 1;\n}",
            "java": "class LcLemonadeChangeBoolCsv {\n    public static boolean lc_lemonade_change_bool_csv(String bills) {\n        int five = 0, ten = 0; for (String part : bills.split(\",\")) { int v = Integer.parseInt(part); if (v == 5) five++; else if (v == 10) { if (five == 0) return false; five--; ten++; } else { if (ten > 0 && five > 0) { ten--; five--; } else if (five >= 3) five -= 3; else return false; } } return true;\n    }\n}",
            "rust": "pub fn lc_lemonade_change_bool_csv(bills: &str) -> bool {\n    let mut five = 0; let mut ten = 0; for part in bills.split(',') { let v = part.parse::<i32>().unwrap(); if v == 5 { five += 1; } else if v == 10 { if five == 0 { return false; } five -= 1; ten += 1; } else if ten > 0 && five > 0 { ten -= 1; five -= 1; } else if five >= 3 { five -= 3; } else { return false; } } true\n}",
        }),
        Problem("lc_buddy_strings_bool", "LC Buddy Strings Bool", "Return true if swapping exactly two letters in `s` can make it equal to `goal`.", ["Inputs contain lowercase English letters."], "bool", [{"name": "s", "type": "string"}, {"name": "goal", "type": "string"}], [case({"s": "ab", "goal": "ba"}, True), case({"s": "ab", "goal": "ab"}, False), case({"s": "aa", "goal": "aa"}, True)], lc("buddy-strings"), "easy", {
            "c": "int lc_buddy_strings_bool(const char *s, const char *goal) {\n    int n = 0, m = 0; while (s[n] != '\\0') n++; while (goal[m] != '\\0') m++; if (n != m) return 0; int diff[2], d = 0, cnt[26] = {0}, dup = 0;\n    for (int i = 0; i < n; i++) { int idx = s[i] - 'a'; cnt[idx]++; if (cnt[idx] > 1) dup = 1; if (s[i] != goal[i]) { if (d >= 2) return 0; diff[d++] = i; } }\n    if (d == 0) return dup;\n    return d == 2 && s[diff[0]] == goal[diff[1]] && s[diff[1]] == goal[diff[0]];\n}",
            "java": "class LcBuddyStringsBool {\n    public static boolean lc_buddy_strings_bool(String s, String goal) {\n        if (s.length() != goal.length()) return false; int[] diff = new int[2], cnt = new int[26]; int d = 0; boolean dup = false; for (int i = 0; i < s.length(); i++) { int idx = s.charAt(i) - 'a'; if (++cnt[idx] > 1) dup = true; if (s.charAt(i) != goal.charAt(i)) { if (d >= 2) return false; diff[d++] = i; } } if (d == 0) return dup; return d == 2 && s.charAt(diff[0]) == goal.charAt(diff[1]) && s.charAt(diff[1]) == goal.charAt(diff[0]);\n    }\n}",
            "rust": "pub fn lc_buddy_strings_bool(s: &str, goal: &str) -> bool {\n    let a = s.as_bytes(); let b = goal.as_bytes(); if a.len() != b.len() { return false; } let mut diff = [0usize; 2]; let mut d = 0usize; let mut cnt = [0; 26]; let mut dup = false; let mut i = 0usize; while i < a.len() { let idx = (a[i] - b'a') as usize; cnt[idx] += 1; if cnt[idx] > 1 { dup = true; } if a[i] != b[i] { if d >= 2 { return false; } diff[d] = i; d += 1; } i += 1; } if d == 0 { dup } else { d == 2 && a[diff[0]] == b[diff[1]] && a[diff[1]] == b[diff[0]] }\n}",
        }),
        Problem("lc_distribute_candies_kinds_csv", "LC Distribute Candies Kinds CSV", "Return the maximum number of candy kinds the sister can receive.", ["`types` is a comma-separated list of integer candy types.", "The sister receives exactly half of the candies."], "int", [{"name": "types", "type": "string"}], [case({"types": "1,1,2,2,3,3"}, 3), case({"types": "1,1,2,3"}, 2), case({"types": "6,6,6,6"}, 1)], lc("distribute-candies"), "easy", {
            "c": "int lc_distribute_candies_kinds_csv(const char *types) {\n    int a[512], n = 0, i = 0;\n    while (types[i] != '\\0') { int sign = 1, v = 0; if (types[i] == '-') { sign = -1; i++; } while (types[i] >= '0' && types[i] <= '9') { v = v * 10 + types[i] - '0'; i++; } a[n++] = sign * v; if (types[i] == ',') i++; }\n    int distinct = 0; for (int x = 0; x < n; x++) { int seen = 0; for (int y = 0; y < x; y++) if (a[y] == a[x]) seen = 1; if (!seen) distinct++; } return distinct < n / 2 ? distinct : n / 2;\n}",
            "java": "class LcDistributeCandiesKindsCsv {\n    public static int lc_distribute_candies_kinds_csv(String types) {\n        String[] p = types.split(\",\"); java.util.HashSet<Integer> set = new java.util.HashSet<Integer>(); for (String x : p) set.add(Integer.parseInt(x)); return Math.min(set.size(), p.length / 2);\n    }\n}",
            "rust": "pub fn lc_distribute_candies_kinds_csv(types: &str) -> i32 {\n    let a: Vec<i32> = types.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut distinct = 0; let mut i = 0usize; while i < a.len() { let mut seen = false; let mut j = 0usize; while j < i { if a[j] == a[i] { seen = true; } j += 1; } if !seen { distinct += 1; } i += 1; } let half = (a.len() / 2) as i32; if distinct < half { distinct } else { half }\n}",
        }),
        Problem("lc_find_min_rotated_csv", "LC Find Minimum In Rotated Sorted Array CSV", "Return the minimum value in a rotated sorted array with distinct integers.", ["`nums` is a nonempty comma-separated list.", "Values are distinct."], "int", [{"name": "nums", "type": "string"}], [case({"nums": "3,4,5,1,2"}, 1), case({"nums": "4,5,6,7,0,1,2"}, 0), case({"nums": "11,13,15,17"}, 11)], lc("find-minimum-in-rotated-sorted-array"), "medium", {
            "c": "int lc_find_min_rotated_csv(const char *nums) {\n    int a[256], n = 0, i = 0; while (nums[i] != '\\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } a[n++] = sign * v; if (nums[i] == ',') i++; }\n    int l = 0, r = n - 1; while (l < r) { int m = l + (r - l) / 2; if (a[m] > a[r]) l = m + 1; else r = m; } return a[l];\n}",
            "java": "class LcFindMinRotatedCsv {\n    public static int lc_find_min_rotated_csv(String nums) {\n        String[] p = nums.split(\",\"); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); int l = 0, r = a.length - 1; while (l < r) { int m = l + (r - l) / 2; if (a[m] > a[r]) l = m + 1; else r = m; } return a[l];\n    }\n}",
            "rust": "pub fn lc_find_min_rotated_csv(nums: &str) -> i32 {\n    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut l = 0usize; let mut r = a.len() - 1; while l < r { let m = l + (r - l) / 2; if a[m] > a[r] { l = m + 1; } else { r = m; } } a[l]\n}",
        }),
        Problem("lc_gas_station_start_csv", "LC Gas Station Start CSV", "Return the starting gas station index that completes the circuit, or `-1`.", ["`gas` and `cost` are comma-separated arrays of equal positive length.", "The original problem guarantees uniqueness when a solution exists."], "int", [{"name": "gas", "type": "string"}, {"name": "cost", "type": "string"}], [case({"gas": "1,2,3,4,5", "cost": "3,4,5,1,2"}, 3), case({"gas": "2,3,4", "cost": "3,4,3"}, -1), case({"gas": "5", "cost": "4"}, 0)], lc("gas-station"), "medium", {
            "c": "int lc_gas_station_start_csv(const char *gas, const char *cost) {\n    int g[256], c[256], n = 0, i = 0; while (gas[i] != '\\0') { int v = 0; while (gas[i] >= '0' && gas[i] <= '9') { v = v * 10 + gas[i] - '0'; i++; } g[n++] = v; if (gas[i] == ',') i++; } i = 0; int m = 0; while (cost[i] != '\\0') { int v = 0; while (cost[i] >= '0' && cost[i] <= '9') { v = v * 10 + cost[i] - '0'; i++; } c[m++] = v; if (cost[i] == ',') i++; }\n    int total = 0, tank = 0, start = 0; for (int k = 0; k < n; k++) { int d = g[k] - c[k]; total += d; tank += d; if (tank < 0) { start = k + 1; tank = 0; } } return total >= 0 ? start : -1;\n}",
            "java": "class LcGasStationStartCsv {\n    public static int lc_gas_station_start_csv(String gas, String cost) {\n        String[] gp = gas.split(\",\"), cp = cost.split(\",\"); int total = 0, tank = 0, start = 0; for (int i = 0; i < gp.length; i++) { int d = Integer.parseInt(gp[i]) - Integer.parseInt(cp[i]); total += d; tank += d; if (tank < 0) { start = i + 1; tank = 0; } } return total >= 0 ? start : -1;\n    }\n}",
            "rust": "pub fn lc_gas_station_start_csv(gas: &str, cost: &str) -> i32 {\n    let g: Vec<i32> = gas.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let c: Vec<i32> = cost.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut total = 0; let mut tank = 0; let mut start = 0; let mut i = 0usize; while i < g.len() { let d = g[i] - c[i]; total += d; tank += d; if tank < 0 { start = i as i32 + 1; tank = 0; } i += 1; } if total >= 0 { start } else { -1 }\n}",
        }),
        Problem("lc_task_scheduler_least_interval", "LC Task Scheduler Least Interval", "Return the minimum intervals needed to execute tasks with cooldown `n`.", ["`tasks` is a string of uppercase task letters.", "`n >= 0`."], "int", [{"name": "tasks", "type": "string"}, {"name": "n", "type": "int"}], [case({"tasks": "AAABBB", "n": 2}, 8), case({"tasks": "AAABBB", "n": 0}, 6), case({"tasks": "AAAAAABCDEFG", "n": 2}, 16)], lc("task-scheduler"), "medium", {
            "c": "int lc_task_scheduler_least_interval(const char *tasks, int n) {\n    int cnt[26] = {0}, len = 0, max = 0, same = 0; for (int i = 0; tasks[i] != '\\0'; i++) { int v = ++cnt[tasks[i] - 'A']; len++; if (v > max) max = v; }\n    for (int i = 0; i < 26; i++) if (cnt[i] == max) same++;\n    int frame = (max - 1) * (n + 1) + same;\n    return frame > len ? frame : len;\n}",
            "java": "class LcTaskSchedulerLeastInterval {\n    public static int lc_task_scheduler_least_interval(String tasks, int n) {\n        int[] cnt = new int[26]; int max = 0; for (int i = 0; i < tasks.length(); i++) { int v = ++cnt[tasks.charAt(i) - 'A']; if (v > max) max = v; } int same = 0; for (int v : cnt) if (v == max) same++; int frame = (max - 1) * (n + 1) + same; return Math.max(frame, tasks.length());\n    }\n}",
            "rust": "pub fn lc_task_scheduler_least_interval(tasks: &str, n: i32) -> i32 {\n    let mut cnt = [0; 26]; let mut max = 0; for b in tasks.bytes() { let i = (b - b'A') as usize; cnt[i] += 1; if cnt[i] > max { max = cnt[i]; } } let mut same = 0; for v in cnt { if v == max { same += 1; } } let frame = (max - 1) * (n + 1) + same; let len = tasks.len() as i32; if frame > len { frame } else { len }\n}",
        }),
        Problem("lc_asteroid_collision_survivors_count_csv", "LC Asteroid Collision Survivors Count CSV", "Simulate asteroid collisions and return the number of surviving asteroids.", ["`asteroids` is a comma-separated list of nonzero integers.", "Positive moves right and negative moves left."], "int", [{"name": "asteroids", "type": "string"}], [case({"asteroids": "5,10,-5"}, 2), case({"asteroids": "8,-8"}, 0), case({"asteroids": "10,2,-5"}, 1)], lc("asteroid-collision"), "medium", {
            "c": "int lc_asteroid_collision_survivors_count_csv(const char *asteroids) {\n    int st[256], top = 0, i = 0; while (asteroids[i] != '\\0') { int sign = 1, v = 0; if (asteroids[i] == '-') { sign = -1; i++; } while (asteroids[i] >= '0' && asteroids[i] <= '9') { v = v * 10 + asteroids[i] - '0'; i++; } v *= sign; int alive = 1; while (alive && v < 0 && top > 0 && st[top - 1] > 0) { if (st[top - 1] < -v) top--; else if (st[top - 1] == -v) { top--; alive = 0; } else alive = 0; } if (alive) st[top++] = v; if (asteroids[i] == ',') i++; } return top;\n}",
            "java": "class LcAsteroidCollisionSurvivorsCountCsv {\n    public static int lc_asteroid_collision_survivors_count_csv(String asteroids) {\n        int[] st = new int[256]; int top = 0; for (String part : asteroids.split(\",\")) { int v = Integer.parseInt(part); boolean alive = true; while (alive && v < 0 && top > 0 && st[top - 1] > 0) { if (st[top - 1] < -v) top--; else if (st[top - 1] == -v) { top--; alive = false; } else alive = false; } if (alive) st[top++] = v; } return top;\n    }\n}",
            "rust": "pub fn lc_asteroid_collision_survivors_count_csv(asteroids: &str) -> i32 {\n    let mut st: Vec<i32> = Vec::new(); for part in asteroids.split(',') { let v = part.parse::<i32>().unwrap(); let mut alive = true; while alive && v < 0 && !st.is_empty() && *st.last().unwrap() > 0 { let last = *st.last().unwrap(); if last < -v { st.pop(); } else if last == -v { st.pop(); alive = false; } else { alive = false; } } if alive { st.push(v); } } st.len() as i32\n}",
        }),
        Problem("lc_single_number_ii_csv", "LC Single Number II CSV", "Return the element that appears once when every other element appears three times.", ["`nums` is a comma-separated list of signed integers."], "int", [{"name": "nums", "type": "string"}], [case({"nums": "2,2,3,2"}, 3), case({"nums": "0,1,0,1,0,1,99"}, 99), case({"nums": "-2,-2,1,1,4,1,4,4,-4,-2"}, -4)], lc("single-number-ii"), "medium", {
            "c": "int lc_single_number_ii_csv(const char *nums) {\n    int ones = 0, twos = 0, i = 0; while (nums[i] != '\\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } v *= sign; ones = (ones ^ v) & ~twos; twos = (twos ^ v) & ~ones; if (nums[i] == ',') i++; } return ones;\n}",
            "java": "class LcSingleNumberIiCsv {\n    public static int lc_single_number_ii_csv(String nums) {\n        int ones = 0, twos = 0; for (String part : nums.split(\",\")) { int v = Integer.parseInt(part); ones = (ones ^ v) & ~twos; twos = (twos ^ v) & ~ones; } return ones;\n    }\n}",
            "rust": "pub fn lc_single_number_ii_csv(nums: &str) -> i32 {\n    let mut ones = 0; let mut twos = 0; for part in nums.split(',') { let v = part.parse::<i32>().unwrap(); ones = (ones ^ v) & !twos; twos = (twos ^ v) & !ones; } ones\n}",
        }),
        Problem("lc_max_area_island_rows", "LC Max Area Of Island Rows", "Return the maximum area of a 4-directionally connected island in a 0/1 grid.", ["Rows are semicolon-separated.", "Rows contain only `0` and `1`."], "int", [{"name": "rows", "type": "string"}], [case({"rows": "00100;01110;00100"}, 5), case({"rows": "000;000"}, 0), case({"rows": "110;010;011"}, 5)], lc("max-area-of-island"), "medium", {
            "c": "int lc_max_area_island_rows(const char *rows) {\n    char g[64][64]; int r = 0, c = 0, cols = 0, i = 0; while (rows[i] != '\\0') { c = 0; while (rows[i] == '0' || rows[i] == '1') g[r][c++] = rows[i++]; if (cols == 0) cols = c; r++; if (rows[i] == ';') i++; }\n    int best = 0, sx[4096], sy[4096]; for (int x = 0; x < r; x++) for (int y = 0; y < cols; y++) if (g[x][y] == '1') { int area = 0, top = 0; sx[top] = x; sy[top++] = y; g[x][y] = '0'; while (top > 0) { top--; int cx = sx[top], cy = sy[top]; area++; int dx[4] = {1,-1,0,0}, dy[4] = {0,0,1,-1}; for (int k = 0; k < 4; k++) { int nx = cx + dx[k], ny = cy + dy[k]; if (nx >= 0 && nx < r && ny >= 0 && ny < cols && g[nx][ny] == '1') { g[nx][ny] = '0'; sx[top] = nx; sy[top++] = ny; } } } if (area > best) best = area; }\n    return best;\n}",
            "java": "class LcMaxAreaIslandRows {\n    public static int lc_max_area_island_rows(String rows) {\n        String[] rs = rows.split(\";\"); int r = rs.length, c = rs[0].length(), best = 0; char[][] g = new char[r][c]; for (int i = 0; i < r; i++) g[i] = rs[i].toCharArray(); int[] sx = new int[r * c], sy = new int[r * c], dx = {1,-1,0,0}, dy = {0,0,1,-1};\n        for (int i = 0; i < r; i++) for (int j = 0; j < c; j++) if (g[i][j] == '1') { int area = 0, top = 0; sx[top] = i; sy[top++] = j; g[i][j] = '0'; while (top > 0) { top--; int x = sx[top], y = sy[top]; area++; for (int k = 0; k < 4; k++) { int nx = x + dx[k], ny = y + dy[k]; if (nx >= 0 && nx < r && ny >= 0 && ny < c && g[nx][ny] == '1') { g[nx][ny] = '0'; sx[top] = nx; sy[top++] = ny; } } } if (area > best) best = area; } return best;\n    }\n}",
            "rust": "pub fn lc_max_area_island_rows(rows: &str) -> i32 {\n    let mut g: Vec<Vec<u8>> = rows.split(';').map(|s| s.as_bytes().to_vec()).collect(); let r = g.len(); let c = g[0].len(); let dirs = [(1i32,0i32),(-1,0),(0,1),(0,-1)]; let mut best = 0; let mut i = 0usize; while i < r { let mut j = 0usize; while j < c { if g[i][j] == b'1' { let mut area = 0; let mut st = vec![(i,j)]; g[i][j] = b'0'; while let Some((x,y)) = st.pop() { area += 1; for (dx,dy) in dirs { let nx = x as i32 + dx; let ny = y as i32 + dy; if nx >= 0 && nx < r as i32 && ny >= 0 && ny < c as i32 && g[nx as usize][ny as usize] == b'1' { g[nx as usize][ny as usize] = b'0'; st.push((nx as usize, ny as usize)); } } } if area > best { best = area; } } j += 1; } i += 1; } best\n}",
        }),
    ]


def more_real_source_problems_13() -> list[Problem]:
    lc = lambda slug: source("LeetCode", slug, f"https://leetcode.com/problems/{slug}/")
    return [
        Problem("lc_h_index_csv", "LC H Index CSV", "Return the H-index for comma-separated citation counts.", ["`citations` is a nonempty comma-separated list of nonnegative integers."], "int", [{"name": "citations", "type": "string"}], [case({"citations": "3,0,6,1,5"}, 3), case({"citations": "1,3,1"}, 1), case({"citations": "0"}, 0)], lc("h-index"), "medium", {
            "c": "int lc_h_index_csv(const char *citations) {\n    int a[256], n = 0, i = 0; while (citations[i] != '\\0') { int v = 0; while (citations[i] >= '0' && citations[i] <= '9') { v = v * 10 + citations[i] - '0'; i++; } a[n++] = v; if (citations[i] == ',') i++; }\n    for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) if (a[y] < a[x]) { int t = a[x]; a[x] = a[y]; a[y] = t; }\n    int h = 0; for (int x = 0; x < n; x++) { int cand = n - x; if (a[x] >= cand && cand > h) h = cand; } return h;\n}",
            "java": "class LcHIndexCsv {\n    public static int lc_h_index_csv(String citations) {\n        String[] p = citations.split(\",\"); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); java.util.Arrays.sort(a); int h = 0; for (int i = 0; i < a.length; i++) { int cand = a.length - i; if (a[i] >= cand && cand > h) h = cand; } return h;\n    }\n}",
            "rust": "pub fn lc_h_index_csv(citations: &str) -> i32 {\n    let mut a: Vec<i32> = citations.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); a.sort(); let n = a.len(); let mut h = 0; let mut i = 0usize; while i < n { let cand = (n - i) as i32; if a[i] >= cand && cand > h { h = cand; } i += 1; } h\n}",
        }),
        Problem("lc_find_duplicate_number_csv", "LC Find Duplicate Number CSV", "Return the duplicated number in comma-separated `nums`.", ["`nums` has length `n+1` and values in `1..n`.", "At least one duplicate exists."], "int", [{"name": "nums", "type": "string"}], [case({"nums": "1,3,4,2,2"}, 2), case({"nums": "3,1,3,4,2"}, 3), case({"nums": "1,1"}, 1)], lc("find-the-duplicate-number"), "medium", {
            "c": "int lc_find_duplicate_number_csv(const char *nums) {\n    int seen[2048] = {0}, i = 0; while (nums[i] != '\\0') { int v = 0; while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } if (seen[v]) return v; seen[v] = 1; if (nums[i] == ',') i++; } return -1;\n}",
            "java": "class LcFindDuplicateNumberCsv {\n    public static int lc_find_duplicate_number_csv(String nums) {\n        boolean[] seen = new boolean[2048]; for (String part : nums.split(\",\")) { int v = Integer.parseInt(part); if (seen[v]) return v; seen[v] = true; } return -1;\n    }\n}",
            "rust": "pub fn lc_find_duplicate_number_csv(nums: &str) -> i32 {\n    let mut seen = vec![false; 2048]; for part in nums.split(',') { let v = part.parse::<usize>().unwrap(); if seen[v] { return v as i32; } seen[v] = true; } -1\n}",
        }),
        Problem("lc_kth_largest_csv", "LC Kth Largest Element CSV", "Return the `k`th largest value in comma-separated `nums`.", ["`nums` is nonempty.", "`1 <= k <= len(nums)`."], "int", [{"name": "nums", "type": "string"}, {"name": "k", "type": "int"}], [case({"nums": "3,2,1,5,6,4", "k": 2}, 5), case({"nums": "3,2,3,1,2,4,5,5,6", "k": 4}, 4), case({"nums": "1", "k": 1}, 1)], lc("kth-largest-element-in-an-array"), "medium", {
            "c": "int lc_kth_largest_csv(const char *nums, int k) {\n    int a[256], n = 0, i = 0; while (nums[i] != '\\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } a[n++] = sign * v; if (nums[i] == ',') i++; }\n    for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) if (a[y] > a[x]) { int t = a[x]; a[x] = a[y]; a[y] = t; }\n    return a[k - 1];\n}",
            "java": "class LcKthLargestCsv {\n    public static int lc_kth_largest_csv(String nums, int k) {\n        String[] p = nums.split(\",\"); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); java.util.Arrays.sort(a); return a[a.length - k];\n    }\n}",
            "rust": "pub fn lc_kth_largest_csv(nums: &str, k: i32) -> i32 {\n    let mut a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); a.sort(); a[a.len() - k as usize]\n}",
        }),
        Problem("lc_character_replacement_len", "LC Longest Repeating Character Replacement Length", "Return the longest substring length that can be made of one repeated character after at most `k` replacements.", ["`s` contains uppercase English letters.", "`k >= 0`."], "int", [{"name": "s", "type": "string"}, {"name": "k", "type": "int"}], [case({"s": "ABAB", "k": 2}, 4), case({"s": "AABABBA", "k": 1}, 4), case({"s": "AAAA", "k": 0}, 4)], lc("longest-repeating-character-replacement"), "medium", {
            "c": "int lc_character_replacement_len(const char *s, int k) {\n    int cnt[26] = {0}, left = 0, maxc = 0, best = 0; for (int right = 0; s[right] != '\\0'; right++) { int idx = s[right] - 'A'; cnt[idx]++; if (cnt[idx] > maxc) maxc = cnt[idx]; while (right - left + 1 - maxc > k) { cnt[s[left] - 'A']--; left++; } int len = right - left + 1; if (len > best) best = len; } return best;\n}",
            "java": "class LcCharacterReplacementLen {\n    public static int lc_character_replacement_len(String s, int k) {\n        int[] cnt = new int[26]; int left = 0, maxc = 0, best = 0; for (int right = 0; right < s.length(); right++) { int idx = s.charAt(right) - 'A'; maxc = Math.max(maxc, ++cnt[idx]); while (right - left + 1 - maxc > k) cnt[s.charAt(left++) - 'A']--; best = Math.max(best, right - left + 1); } return best;\n    }\n}",
            "rust": "pub fn lc_character_replacement_len(s: &str, k: i32) -> i32 {\n    let b = s.as_bytes(); let mut cnt = [0i32; 26]; let mut left = 0usize; let mut maxc = 0; let mut best = 0; let mut right = 0usize; while right < b.len() { let idx = (b[right] - b'A') as usize; cnt[idx] += 1; if cnt[idx] > maxc { maxc = cnt[idx]; } while right as i32 - left as i32 + 1 - maxc > k { cnt[(b[left] - b'A') as usize] -= 1; left += 1; } let len = right as i32 - left as i32 + 1; if len > best { best = len; } right += 1; } best\n}",
        }),
        Problem("lc_min_window_substring_len", "LC Minimum Window Substring Length", "Return the length of the shortest substring of `s` containing all characters of `t`, or `0` if none exists.", ["Inputs are ASCII.", "Character multiplicity in `t` matters."], "int", [{"name": "s", "type": "string"}, {"name": "t", "type": "string"}], [case({"s": "ADOBECODEBANC", "t": "ABC"}, 4), case({"s": "a", "t": "a"}, 1), case({"s": "a", "t": "aa"}, 0)], lc("minimum-window-substring"), "hard", {
            "c": "int lc_min_window_substring_len(const char *s, const char *t) {\n    int need[128] = {0}, have[128] = {0}, required = 0; for (int i = 0; t[i] != '\\0'; i++) { if (need[(int)t[i]] == 0) required++; need[(int)t[i]]++; }\n    int formed = 0, left = 0, best = 1000000; for (int right = 0; s[right] != '\\0'; right++) { int ch = (int)s[right]; have[ch]++; if (need[ch] > 0 && have[ch] == need[ch]) formed++; while (formed == required) { int len = right - left + 1; if (len < best) best = len; int lc = (int)s[left++]; if (need[lc] > 0 && have[lc] == need[lc]) formed--; have[lc]--; } } return best == 1000000 ? 0 : best;\n}",
            "java": "class LcMinWindowSubstringLen {\n    public static int lc_min_window_substring_len(String s, String t) {\n        int[] need = new int[128], have = new int[128]; int required = 0; for (int i = 0; i < t.length(); i++) { int ch = t.charAt(i); if (need[ch] == 0) required++; need[ch]++; } int formed = 0, left = 0, best = 1000000; for (int right = 0; right < s.length(); right++) { int ch = s.charAt(right); have[ch]++; if (need[ch] > 0 && have[ch] == need[ch]) formed++; while (formed == required) { best = Math.min(best, right - left + 1); int lc = s.charAt(left++); if (need[lc] > 0 && have[lc] == need[lc]) formed--; have[lc]--; } } return best == 1000000 ? 0 : best;\n    }\n}",
            "rust": "pub fn lc_min_window_substring_len(s: &str, t: &str) -> i32 {\n    let sb = s.as_bytes(); let tb = t.as_bytes(); let mut need = [0i32; 128]; let mut have = [0i32; 128]; let mut required = 0; for &ch in tb { let i = ch as usize; if need[i] == 0 { required += 1; } need[i] += 1; } let mut formed = 0; let mut left = 0usize; let mut best = 1000000; let mut right = 0usize; while right < sb.len() { let ch = sb[right] as usize; have[ch] += 1; if need[ch] > 0 && have[ch] == need[ch] { formed += 1; } while formed == required { let len = (right - left + 1) as i32; if len < best { best = len; } let lc = sb[left] as usize; left += 1; if need[lc] > 0 && have[lc] == need[lc] { formed -= 1; } have[lc] -= 1; } right += 1; } if best == 1000000 { 0 } else { best }\n}",
        }),
        Problem("lc_non_overlapping_intervals_remove_count", "LC Non Overlapping Intervals Remove Count", "Return the minimum number of intervals to remove so the rest do not overlap.", ["Intervals are encoded as `start,end;...`.", "Use half-open overlap semantics matching the original problem examples."], "int", [{"name": "intervals", "type": "string"}], [case({"intervals": "1,2;2,3;3,4;1,3"}, 1), case({"intervals": "1,2;1,2;1,2"}, 2), case({"intervals": "1,2;2,3"}, 0)], lc("non-overlapping-intervals"), "medium", {
            "c": "int lc_non_overlapping_intervals_remove_count(const char *intervals) {\n    int a[256][2], n = 0, i = 0; while (intervals[i] != '\\0') { for (int k = 0; k < 2; k++) { int sign = 1, v = 0; if (intervals[i] == '-') { sign = -1; i++; } while (intervals[i] >= '0' && intervals[i] <= '9') { v = v * 10 + intervals[i] - '0'; i++; } a[n][k] = sign * v; if (intervals[i] == ',') i++; } n++; if (intervals[i] == ';') i++; }\n    for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) if (a[y][1] < a[x][1]) { int s = a[x][0], e = a[x][1]; a[x][0] = a[y][0]; a[x][1] = a[y][1]; a[y][0] = s; a[y][1] = e; }\n    int keep = 0, end = -2147483647; for (int x = 0; x < n; x++) if (a[x][0] >= end) { keep++; end = a[x][1]; } return n - keep;\n}",
            "java": "class LcNonOverlappingIntervalsRemoveCount {\n    public static int lc_non_overlapping_intervals_remove_count(String intervals) {\n        String[] rows = intervals.split(\";\"); int[][] a = new int[rows.length][2]; for (int i = 0; i < rows.length; i++) { String[] p = rows[i].split(\",\"); a[i][0] = Integer.parseInt(p[0]); a[i][1] = Integer.parseInt(p[1]); } java.util.Arrays.sort(a, (x, y) -> x[1] - y[1]); int keep = 0, end = Integer.MIN_VALUE; for (int[] in : a) if (in[0] >= end) { keep++; end = in[1]; } return a.length - keep;\n    }\n}",
            "rust": "pub fn lc_non_overlapping_intervals_remove_count(intervals: &str) -> i32 {\n    let mut a: Vec<[i32; 2]> = intervals.split(';').map(|r| { let p: Vec<i32> = r.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); [p[0], p[1]] }).collect(); a.sort_by_key(|x| x[1]); let mut keep = 0; let mut end = i32::MIN; for inr in &a { if inr[0] >= end { keep += 1; end = inr[1]; } } a.len() as i32 - keep\n}",
        }),
        Problem("lc_car_fleet_count", "LC Car Fleet Count", "Return how many car fleets arrive at the target.", ["`position` and `speed` are comma-separated lists of equal length.", "Positions are distinct and less than target."], "int", [{"name": "target", "type": "int"}, {"name": "position", "type": "string"}, {"name": "speed", "type": "string"}], [case({"target": 12, "position": "10,8,0,5,3", "speed": "2,4,1,1,3"}, 3), case({"target": 10, "position": "3", "speed": "3"}, 1), case({"target": 100, "position": "0,2,4", "speed": "4,2,1"}, 1)], lc("car-fleet"), "medium", {
            "c": "int lc_car_fleet_count(int target, const char *position, const char *speed) {\n    int p[256], s[256], n = 0, i = 0; while (position[i] != '\\0') { int v = 0; while (position[i] >= '0' && position[i] <= '9') { v = v * 10 + position[i] - '0'; i++; } p[n++] = v; if (position[i] == ',') i++; } i = 0; int m = 0; while (speed[i] != '\\0') { int v = 0; while (speed[i] >= '0' && speed[i] <= '9') { v = v * 10 + speed[i] - '0'; i++; } s[m++] = v; if (speed[i] == ',') i++; }\n    for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) if (p[y] > p[x]) { int tp = p[x], ts = s[x]; p[x] = p[y]; s[x] = s[y]; p[y] = tp; s[y] = ts; }\n    int fleets = 0; double slow = -1.0; for (int x = 0; x < n; x++) { double t = (double)(target - p[x]) / (double)s[x]; if (t > slow) { fleets++; slow = t; } } return fleets;\n}",
            "java": "class LcCarFleetCount {\n    public static int lc_car_fleet_count(int target, String position, String speed) {\n        String[] pp = position.split(\",\"), ss = speed.split(\",\"); int n = pp.length; int[][] cars = new int[n][2]; for (int i = 0; i < n; i++) { cars[i][0] = Integer.parseInt(pp[i]); cars[i][1] = Integer.parseInt(ss[i]); } java.util.Arrays.sort(cars, (a, b) -> b[0] - a[0]); int fleets = 0; double slow = -1.0; for (int[] car : cars) { double t = (double)(target - car[0]) / car[1]; if (t > slow) { fleets++; slow = t; } } return fleets;\n    }\n}",
            "rust": "pub fn lc_car_fleet_count(target: i32, position: &str, speed: &str) -> i32 {\n    let p: Vec<i32> = position.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let s: Vec<i32> = speed.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut cars: Vec<(i32, i32)> = p.into_iter().zip(s.into_iter()).collect(); cars.sort_by(|a, b| b.0.cmp(&a.0)); let mut fleets = 0; let mut slow = -1.0f64; for (pos, spd) in cars { let t = (target - pos) as f64 / spd as f64; if t > slow { fleets += 1; slow = t; } } fleets\n}",
        }),
        Problem("lc_sort_colors_code_csv", "LC Sort Colors Code CSV", "Sort comma-separated colors `0`, `1`, and `2`, then return the decimal code formed by the sorted colors.", ["This scalar return is a deterministic encoding of the original sorted-array output.", "The supplied arrays have at most 9 elements."], "int", [{"name": "colors", "type": "string"}], [case({"colors": "2,0,2,1,1,0"}, 1122), case({"colors": "2,0,1"}, 12), case({"colors": "0"}, 0)], lc("sort-colors"), "medium", {
            "c": "int lc_sort_colors_code_csv(const char *colors) {\n    int cnt[3] = {0}, i = 0; while (colors[i] != '\\0') { cnt[colors[i] - '0']++; i++; if (colors[i] == ',') i++; } int code = 0; for (int v = 0; v < 3; v++) for (int k = 0; k < cnt[v]; k++) code = code * 10 + v; return code;\n}",
            "java": "class LcSortColorsCodeCsv {\n    public static int lc_sort_colors_code_csv(String colors) {\n        int[] cnt = new int[3]; for (String p : colors.split(\",\")) cnt[Integer.parseInt(p)]++; int code = 0; for (int v = 0; v < 3; v++) for (int k = 0; k < cnt[v]; k++) code = code * 10 + v; return code;\n    }\n}",
            "rust": "pub fn lc_sort_colors_code_csv(colors: &str) -> i32 {\n    let mut cnt = [0; 3]; for p in colors.split(',') { cnt[p.parse::<usize>().unwrap()] += 1; } let mut code = 0; let mut v = 0usize; while v < 3 { let mut k = 0; while k < cnt[v] { code = code * 10 + v as i32; k += 1; } v += 1; } code\n}",
        }),
        Problem("lc_rotate_array_first_csv", "LC Rotate Array First CSV", "Rotate comma-separated `nums` to the right by `k` steps and return the first element after rotation.", ["`nums` is nonempty.", "`k >= 0`."], "int", [{"name": "nums", "type": "string"}, {"name": "k", "type": "int"}], [case({"nums": "1,2,3,4,5,6,7", "k": 3}, 5), case({"nums": "-1,-100,3,99", "k": 2}, 3), case({"nums": "1", "k": 10}, 1)], lc("rotate-array"), "medium", {
            "c": "int lc_rotate_array_first_csv(const char *nums, int k) {\n    int a[256], n = 0, i = 0; while (nums[i] != '\\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } a[n++] = sign * v; if (nums[i] == ',') i++; } k %= n; return a[(n - k) % n];\n}",
            "java": "class LcRotateArrayFirstCsv {\n    public static int lc_rotate_array_first_csv(String nums, int k) {\n        String[] p = nums.split(\",\"); int n = p.length; k %= n; return Integer.parseInt(p[(n - k) % n]);\n    }\n}",
            "rust": "pub fn lc_rotate_array_first_csv(nums: &str, k: i32) -> i32 {\n    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let n = a.len(); let kk = k as usize % n; a[(n - kk) % n]\n}",
        }),
        Problem("lc_majority_element_ii_count_csv", "LC Majority Element II Count CSV", "Return how many distinct values appear more than `n/3` times.", ["`nums` is a nonempty comma-separated list of signed integers.", "The answer is at most 2."], "int", [{"name": "nums", "type": "string"}], [case({"nums": "3,2,3"}, 1), case({"nums": "1"}, 1), case({"nums": "1,2"}, 2), case({"nums": "1,2,3,4"}, 0)], lc("majority-element-ii"), "medium", {
            "c": "int lc_majority_element_ii_count_csv(const char *nums) {\n    int a[256], n = 0, i = 0; while (nums[i] != '\\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } a[n++] = sign * v; if (nums[i] == ',') i++; }\n    int ans = 0; for (int x = 0; x < n; x++) { int seen = 0; for (int y = 0; y < x; y++) if (a[y] == a[x]) seen = 1; if (!seen) { int cnt = 0; for (int y = 0; y < n; y++) if (a[y] == a[x]) cnt++; if (cnt > n / 3) ans++; } } return ans;\n}",
            "java": "class LcMajorityElementIiCountCsv {\n    public static int lc_majority_element_ii_count_csv(String nums) {\n        String[] p = nums.split(\",\"); int ans = 0; for (int i = 0; i < p.length; i++) { boolean seen = false; for (int j = 0; j < i; j++) if (p[j].equals(p[i])) seen = true; if (!seen) { int cnt = 0; for (String x : p) if (x.equals(p[i])) cnt++; if (cnt > p.length / 3) ans++; } } return ans;\n    }\n}",
            "rust": "pub fn lc_majority_element_ii_count_csv(nums: &str) -> i32 {\n    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut ans = 0; let mut i = 0usize; while i < a.len() { let mut seen = false; let mut j = 0usize; while j < i { if a[j] == a[i] { seen = true; } j += 1; } if !seen { let mut cnt = 0; for &v in &a { if v == a[i] { cnt += 1; } } if cnt > a.len() as i32 / 3 { ans += 1; } } i += 1; } ans\n}",
        }),
    ]


def more_real_source_problems_14() -> list[Problem]:
    lc = lambda slug: source("LeetCode", slug, f"https://leetcode.com/problems/{slug}/")
    return [
        Problem("lc_max_subarray_sum_csv", "LC Maximum Subarray Sum CSV", "Return the maximum sum over all nonempty contiguous subarrays.", ["`nums` is a nonempty comma-separated list of signed integers."], "int", [{"name": "nums", "type": "string"}], [case({"nums": "-2,1,-3,4,-1,2,1,-5,4"}, 6), case({"nums": "1"}, 1), case({"nums": "5,4,-1,7,8"}, 23)], lc("maximum-subarray"), "medium", {
            "c": "int lc_max_subarray_sum_csv(const char *nums) {\n    int best = -2147483647, cur = 0, i = 0;\n    while (nums[i] != '\\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } v *= sign; if (cur < 0) cur = v; else cur += v; if (cur > best) best = cur; if (nums[i] == ',') i++; }\n    return best;\n}",
            "java": "class LcMaxSubarraySumCsv {\n    public static int lc_max_subarray_sum_csv(String nums) {\n        int best = Integer.MIN_VALUE, cur = 0; for (String part : nums.split(\",\")) { int v = Integer.parseInt(part); cur = cur < 0 ? v : cur + v; best = Math.max(best, cur); } return best;\n    }\n}",
            "rust": "pub fn lc_max_subarray_sum_csv(nums: &str) -> i32 {\n    let mut best = i32::MIN; let mut cur = 0; for part in nums.split(',') { let v = part.parse::<i32>().unwrap(); cur = if cur < 0 { v } else { cur + v }; if cur > best { best = cur; } } best\n}",
        }),
        Problem("lc_unique_paths_obstacles_rows", "LC Unique Paths II Rows", "Return the number of paths from top-left to bottom-right while avoiding obstacles.", ["Rows are semicolon-separated strings of `0` and `1`.", "`1` marks an obstacle."], "int", [{"name": "rows", "type": "string"}], [case({"rows": "000;010;000"}, 2), case({"rows": "01;00"}, 1), case({"rows": "0"}, 1)], lc("unique-paths-ii"), "medium", {
            "c": "int lc_unique_paths_obstacles_rows(const char *rows) {\n    int dp[64] = {0}, i = 0; dp[0] = 1;\n    while (rows[i] != '\\0') { int c = 0; while (rows[i] == '0' || rows[i] == '1') { if (rows[i] == '1') dp[c] = 0; else if (c > 0) dp[c] += dp[c - 1]; c++; i++; } if (rows[i] == ';') i++; }\n    int last = 0; while (rows[last] != '\\0' && rows[last] != ';') last++; return dp[last - 1];\n}",
            "java": "class LcUniquePathsObstaclesRows {\n    public static int lc_unique_paths_obstacles_rows(String rows) {\n        String[] rs = rows.split(\";\"); int[] dp = new int[rs[0].length()]; dp[0] = 1; for (String row : rs) { for (int c = 0; c < row.length(); c++) { if (row.charAt(c) == '1') dp[c] = 0; else if (c > 0) dp[c] += dp[c - 1]; } } return dp[dp.length - 1];\n    }\n}",
            "rust": "pub fn lc_unique_paths_obstacles_rows(rows: &str) -> i32 {\n    let mut dp = vec![0i32; rows.split(';').next().unwrap().len()]; dp[0] = 1; for row in rows.split(';') { for (c, b) in row.bytes().enumerate() { if b == b'1' { dp[c] = 0; } else if c > 0 { dp[c] += dp[c - 1]; } } } *dp.last().unwrap()\n}",
        }),
        Problem("lc_search_matrix_bool_rows", "LC Search A 2D Matrix Bool Rows", "Return true if `target` appears in a row-major sorted matrix.", ["Rows are semicolon-separated.", "Numbers inside each row are comma-separated signed integers."], "bool", [{"name": "rows", "type": "string"}, {"name": "target", "type": "int"}], [case({"rows": "1,3,5,7;10,11,16,20;23,30,34,60", "target": 3}, True), case({"rows": "1,3,5,7;10,11,16,20;23,30,34,60", "target": 13}, False), case({"rows": "1", "target": 1}, True)], lc("search-a-2d-matrix"), "medium", {
            "c": "int lc_search_matrix_bool_rows(const char *rows, int target) {\n    int a[4096], n = 0, i = 0; while (rows[i] != '\\0') { int sign = 1, v = 0; if (rows[i] == '-') { sign = -1; i++; } while (rows[i] >= '0' && rows[i] <= '9') { v = v * 10 + rows[i] - '0'; i++; } a[n++] = sign * v; if (rows[i] == ',' || rows[i] == ';') i++; }\n    int l = 0, r = n - 1; while (l <= r) { int m = l + (r - l) / 2; if (a[m] == target) return 1; if (a[m] < target) l = m + 1; else r = m - 1; } return 0;\n}",
            "java": "class LcSearchMatrixBoolRows {\n    public static boolean lc_search_matrix_bool_rows(String rows, int target) {\n        String flat = rows.replace(';', ','); String[] p = flat.split(\",\"); int l = 0, r = p.length - 1; while (l <= r) { int m = l + (r - l) / 2; int v = Integer.parseInt(p[m]); if (v == target) return true; if (v < target) l = m + 1; else r = m - 1; } return false;\n    }\n}",
            "rust": "pub fn lc_search_matrix_bool_rows(rows: &str, target: i32) -> bool {\n    let a: Vec<i32> = rows.split(|ch| ch == ',' || ch == ';').map(|x| x.parse::<i32>().unwrap()).collect(); let mut l = 0i32; let mut r = a.len() as i32 - 1; while l <= r { let m = l + (r - l) / 2; let v = a[m as usize]; if v == target { return true; } if v < target { l = m + 1; } else { r = m - 1; } } false\n}",
        }),
        Problem("lc_merge_intervals_total_length", "LC Merge Intervals Total Length", "Merge overlapping intervals and return the total covered length.", ["Intervals are encoded as `start,end;...`.", "Touching intervals merge as in the original problem."], "int", [{"name": "intervals", "type": "string"}], [case({"intervals": "1,3;2,6;8,10;15,18"}, 10), case({"intervals": "1,4;4,5"}, 4), case({"intervals": "1,4;0,2;3,5"}, 5)], lc("merge-intervals"), "medium", {
            "c": "int lc_merge_intervals_total_length(const char *intervals) {\n    int a[256][2], n = 0, i = 0; while (intervals[i] != '\\0') { for (int k = 0; k < 2; k++) { int sign = 1, v = 0; if (intervals[i] == '-') { sign = -1; i++; } while (intervals[i] >= '0' && intervals[i] <= '9') { v = v * 10 + intervals[i] - '0'; i++; } a[n][k] = sign * v; if (intervals[i] == ',') i++; } n++; if (intervals[i] == ';') i++; }\n    for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) if (a[y][0] < a[x][0]) { int s = a[x][0], e = a[x][1]; a[x][0] = a[y][0]; a[x][1] = a[y][1]; a[y][0] = s; a[y][1] = e; }\n    int total = 0, cs = a[0][0], ce = a[0][1]; for (int x = 1; x < n; x++) { if (a[x][0] <= ce) { if (a[x][1] > ce) ce = a[x][1]; } else { total += ce - cs; cs = a[x][0]; ce = a[x][1]; } } return total + ce - cs;\n}",
            "java": "class LcMergeIntervalsTotalLength {\n    public static int lc_merge_intervals_total_length(String intervals) {\n        String[] rows = intervals.split(\";\"); int[][] a = new int[rows.length][2]; for (int i = 0; i < rows.length; i++) { String[] p = rows[i].split(\",\"); a[i][0] = Integer.parseInt(p[0]); a[i][1] = Integer.parseInt(p[1]); } java.util.Arrays.sort(a, (x, y) -> Integer.compare(x[0], y[0])); int total = 0, s = a[0][0], e = a[0][1]; for (int i = 1; i < a.length; i++) { if (a[i][0] <= e) e = Math.max(e, a[i][1]); else { total += e - s; s = a[i][0]; e = a[i][1]; } } return total + e - s;\n    }\n}",
            "rust": "pub fn lc_merge_intervals_total_length(intervals: &str) -> i32 {\n    let mut a: Vec<[i32; 2]> = intervals.split(';').map(|r| { let p: Vec<i32> = r.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); [p[0], p[1]] }).collect(); a.sort_by_key(|x| x[0]); let mut total = 0; let mut s = a[0][0]; let mut e = a[0][1]; for inr in a.iter().skip(1) { if inr[0] <= e { if inr[1] > e { e = inr[1]; } } else { total += e - s; s = inr[0]; e = inr[1]; } } total + e - s\n}",
        }),
        Problem("lc_insert_interval_total_length", "LC Insert Interval Total Length", "Insert a new interval, merge overlaps, and return the total covered length.", ["Existing intervals are encoded as `start,end;...`.", "Existing intervals are sorted and non-overlapping."], "int", [{"name": "intervals", "type": "string"}, {"name": "new_start", "type": "int"}, {"name": "new_end", "type": "int"}], [case({"intervals": "1,3;6,9", "new_start": 2, "new_end": 5}, 7), case({"intervals": "1,2;3,5;6,7;8,10;12,16", "new_start": 4, "new_end": 8}, 12), case({"intervals": "1,5", "new_start": 2, "new_end": 3}, 4)], lc("insert-interval"), "medium", {
            "c": "int lc_insert_interval_total_length(const char *intervals, int new_start, int new_end) {\n    int a[256][2], n = 0, i = 0; while (intervals[i] != '\\0') { for (int k = 0; k < 2; k++) { int sign = 1, v = 0; if (intervals[i] == '-') { sign = -1; i++; } while (intervals[i] >= '0' && intervals[i] <= '9') { v = v * 10 + intervals[i] - '0'; i++; } a[n][k] = sign * v; if (intervals[i] == ',') i++; } n++; if (intervals[i] == ';') i++; } a[n][0] = new_start; a[n][1] = new_end; n++;\n    for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) if (a[y][0] < a[x][0]) { int s = a[x][0], e = a[x][1]; a[x][0] = a[y][0]; a[x][1] = a[y][1]; a[y][0] = s; a[y][1] = e; }\n    int total = 0, cs = a[0][0], ce = a[0][1]; for (int x = 1; x < n; x++) { if (a[x][0] <= ce) { if (a[x][1] > ce) ce = a[x][1]; } else { total += ce - cs; cs = a[x][0]; ce = a[x][1]; } } return total + ce - cs;\n}",
            "java": "class LcInsertIntervalTotalLength {\n    public static int lc_insert_interval_total_length(String intervals, int new_start, int new_end) {\n        String[] rows = intervals.split(\";\"); int[][] a = new int[rows.length + 1][2]; for (int i = 0; i < rows.length; i++) { String[] p = rows[i].split(\",\"); a[i][0] = Integer.parseInt(p[0]); a[i][1] = Integer.parseInt(p[1]); } a[rows.length][0] = new_start; a[rows.length][1] = new_end; java.util.Arrays.sort(a, (x, y) -> Integer.compare(x[0], y[0])); int total = 0, s = a[0][0], e = a[0][1]; for (int i = 1; i < a.length; i++) { if (a[i][0] <= e) e = Math.max(e, a[i][1]); else { total += e - s; s = a[i][0]; e = a[i][1]; } } return total + e - s;\n    }\n}",
            "rust": "pub fn lc_insert_interval_total_length(intervals: &str, new_start: i32, new_end: i32) -> i32 {\n    let mut a: Vec<[i32; 2]> = intervals.split(';').map(|r| { let p: Vec<i32> = r.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); [p[0], p[1]] }).collect(); a.push([new_start, new_end]); a.sort_by_key(|x| x[0]); let mut total = 0; let mut s = a[0][0]; let mut e = a[0][1]; for inr in a.iter().skip(1) { if inr[0] <= e { if inr[1] > e { e = inr[1]; } } else { total += e - s; s = inr[0]; e = inr[1]; } } total + e - s\n}",
        }),
        Problem("lc_triangle_min_path_rows", "LC Triangle Minimum Path Rows", "Return the minimum path sum from top to bottom in a number triangle.", ["Rows are semicolon-separated.", "Numbers inside each row are comma-separated signed integers."], "int", [{"name": "rows", "type": "string"}], [case({"rows": "2;3,4;6,5,7;4,1,8,3"}, 11), case({"rows": "-10"}, -10), case({"rows": "1;2,3;3,6,1"}, 5)], lc("triangle"), "medium", {
            "c": "int lc_triangle_min_path_rows(const char *rows) {\n    int dp[128] = {0}, i = 0, row = 0;\n    while (rows[i] != '\\0') { int vals[128], c = 0; while (rows[i] != '\\0' && rows[i] != ';') { int sign = 1, v = 0; if (rows[i] == '-') { sign = -1; i++; } while (rows[i] >= '0' && rows[i] <= '9') { v = v * 10 + rows[i] - '0'; i++; } vals[c++] = sign * v; if (rows[i] == ',') i++; } if (row == 0) dp[0] = vals[0]; else { for (int j = c - 1; j >= 0; j--) { if (j == 0) dp[j] = dp[j] + vals[j]; else if (j == c - 1) dp[j] = dp[j - 1] + vals[j]; else dp[j] = (dp[j - 1] < dp[j] ? dp[j - 1] : dp[j]) + vals[j]; } } row++; if (rows[i] == ';') i++; }\n    int best = dp[0]; for (int j = 1; j < row; j++) if (dp[j] < best) best = dp[j]; return best;\n}",
            "java": "class LcTriangleMinPathRows {\n    public static int lc_triangle_min_path_rows(String rows) {\n        String[] rs = rows.split(\";\"); int[] dp = new int[rs.length]; for (int r = 0; r < rs.length; r++) { String[] p = rs[r].split(\",\"); for (int j = p.length - 1; j >= 0; j--) { int v = Integer.parseInt(p[j]); if (r == 0) dp[0] = v; else if (j == 0) dp[j] += v; else if (j == p.length - 1) dp[j] = dp[j - 1] + v; else dp[j] = Math.min(dp[j - 1], dp[j]) + v; } } int best = dp[0]; for (int i = 1; i < rs.length; i++) best = Math.min(best, dp[i]); return best;\n    }\n}",
            "rust": "pub fn lc_triangle_min_path_rows(rows: &str) -> i32 {\n    let rs: Vec<&str> = rows.split(';').collect(); let mut dp = vec![0i32; rs.len()]; for (r, row) in rs.iter().enumerate() { let vals: Vec<i32> = row.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut j = vals.len(); while j > 0 { j -= 1; if r == 0 { dp[0] = vals[0]; } else if j == 0 { dp[j] += vals[j]; } else if j == vals.len() - 1 { dp[j] = dp[j - 1] + vals[j]; } else { dp[j] = dp[j - 1].min(dp[j]) + vals[j]; } } } *dp.iter().min().unwrap()\n}",
        }),
        Problem("lc_palindromic_substrings_count", "LC Palindromic Substrings Count", "Return the number of palindromic substrings of `s`.", ["`s` contains lowercase English letters."], "int", [{"name": "s", "type": "string"}], [case({"s": "abc"}, 3), case({"s": "aaa"}, 6), case({"s": "racecar"}, 10)], lc("palindromic-substrings"), "medium", {
            "c": "int lc_palindromic_substrings_count(const char *s) {\n    int n = 0; while (s[n] != '\\0') n++; int ans = 0; for (int center = 0; center < 2 * n - 1; center++) { int l = center / 2, r = l + center % 2; while (l >= 0 && r < n && s[l] == s[r]) { ans++; l--; r++; } } return ans;\n}",
            "java": "class LcPalindromicSubstringsCount {\n    public static int lc_palindromic_substrings_count(String s) {\n        int ans = 0; for (int center = 0; center < 2 * s.length() - 1; center++) { int l = center / 2, r = l + center % 2; while (l >= 0 && r < s.length() && s.charAt(l) == s.charAt(r)) { ans++; l--; r++; } } return ans;\n    }\n}",
            "rust": "pub fn lc_palindromic_substrings_count(s: &str) -> i32 {\n    let b = s.as_bytes(); let n = b.len() as i32; let mut ans = 0; let mut center = 0; while center < 2 * n - 1 { let mut l = center / 2; let mut r = l + center % 2; while l >= 0 && r < n && b[l as usize] == b[r as usize] { ans += 1; l -= 1; r += 1; } center += 1; } ans\n}",
        }),
        Problem("lc_max_profit_fee_csv", "LC Stock Profit With Fee CSV", "Return the maximum profit from unlimited transactions with a fixed transaction fee.", ["`prices` is a nonempty comma-separated list of positive integers.", "`fee >= 0`."], "int", [{"name": "prices", "type": "string"}, {"name": "fee", "type": "int"}], [case({"prices": "1,3,2,8,4,9", "fee": 2}, 8), case({"prices": "1,3,7,5,10,3", "fee": 3}, 6), case({"prices": "9,8,7", "fee": 1}, 0)], lc("best-time-to-buy-and-sell-stock-with-transaction-fee"), "medium", {
            "c": "int lc_max_profit_fee_csv(const char *prices, int fee) {\n    int a[512], n = 0, i = 0; while (prices[i] != '\\0') { int v = 0; while (prices[i] >= '0' && prices[i] <= '9') { v = v * 10 + prices[i] - '0'; i++; } a[n++] = v; if (prices[i] == ',') i++; }\n    int cash = 0, hold = -a[0]; for (int k = 1; k < n; k++) { int old_cash = cash; int sell = hold + a[k] - fee; if (sell > cash) cash = sell; int buy = old_cash - a[k]; if (buy > hold) hold = buy; } return cash;\n}",
            "java": "class LcMaxProfitFeeCsv {\n    public static int lc_max_profit_fee_csv(String prices, int fee) {\n        String[] p = prices.split(\",\"); int cash = 0, hold = -Integer.parseInt(p[0]); for (int i = 1; i < p.length; i++) { int price = Integer.parseInt(p[i]); int oldCash = cash; cash = Math.max(cash, hold + price - fee); hold = Math.max(hold, oldCash - price); } return cash;\n    }\n}",
            "rust": "pub fn lc_max_profit_fee_csv(prices: &str, fee: i32) -> i32 {\n    let a: Vec<i32> = prices.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut cash = 0; let mut hold = -a[0]; let mut i = 1usize; while i < a.len() { let old_cash = cash; cash = cash.max(hold + a[i] - fee); hold = hold.max(old_cash - a[i]); i += 1; } cash\n}",
        }),
    ]


def more_real_source_problems_15() -> list[Problem]:
    lc = lambda slug: source("LeetCode", slug, f"https://leetcode.com/problems/{slug}/")
    return [
        Problem("lc_rotting_oranges_minutes_rows", "LC Rotting Oranges Minutes Rows", "Return the minimum minutes until no fresh orange remains, or `-1` if impossible.", ["Rows are semicolon-separated strings of digits.", "`0` is empty, `1` fresh, and `2` rotten."], "int", [{"name": "rows", "type": "string"}], [case({"rows": "211;110;011"}, 4), case({"rows": "210;010;011"}, -1), case({"rows": "0"}, 0)], lc("rotting-oranges"), "medium", {
            "c": "int lc_rotting_oranges_minutes_rows(const char *rows) {\n    char g[64][64]; int r = 0, cols = 0, i = 0, qx[4096], qy[4096], qt[4096], head = 0, tail = 0, fresh = 0, minutes = 0;\n    while (rows[i] != '\\0') { int c = 0; while (rows[i] >= '0' && rows[i] <= '2') { g[r][c] = rows[i]; if (g[r][c] == '1') fresh++; if (g[r][c] == '2') { qx[tail] = r; qy[tail] = c; qt[tail++] = 0; } c++; i++; } if (cols == 0) cols = c; r++; if (rows[i] == ';') i++; }\n    int dx[4] = {1,-1,0,0}, dy[4] = {0,0,1,-1}; while (head < tail) { int x = qx[head], y = qy[head], t = qt[head++]; if (t > minutes) minutes = t; for (int d = 0; d < 4; d++) { int nx = x + dx[d], ny = y + dy[d]; if (nx >= 0 && nx < r && ny >= 0 && ny < cols && g[nx][ny] == '1') { g[nx][ny] = '2'; fresh--; qx[tail] = nx; qy[tail] = ny; qt[tail++] = t + 1; } } } return fresh == 0 ? minutes : -1;\n}",
            "java": "class LcRottingOrangesMinutesRows {\n    public static int lc_rotting_oranges_minutes_rows(String rows) {\n        String[] rs = rows.split(\";\"); int r = rs.length, c = rs[0].length(), fresh = 0, head = 0, tail = 0, minutes = 0; char[][] g = new char[r][c]; int[] qx = new int[r * c], qy = new int[r * c], qt = new int[r * c]; for (int i = 0; i < r; i++) for (int j = 0; j < c; j++) { g[i][j] = rs[i].charAt(j); if (g[i][j] == '1') fresh++; if (g[i][j] == '2') { qx[tail] = i; qy[tail] = j; qt[tail++] = 0; } } int[] dx = {1,-1,0,0}, dy = {0,0,1,-1}; while (head < tail) { int x = qx[head], y = qy[head], t = qt[head++]; minutes = Math.max(minutes, t); for (int d = 0; d < 4; d++) { int nx = x + dx[d], ny = y + dy[d]; if (nx >= 0 && nx < r && ny >= 0 && ny < c && g[nx][ny] == '1') { g[nx][ny] = '2'; fresh--; qx[tail] = nx; qy[tail] = ny; qt[tail++] = t + 1; } } } return fresh == 0 ? minutes : -1;\n    }\n}",
            "rust": "pub fn lc_rotting_oranges_minutes_rows(rows: &str) -> i32 {\n    let mut g: Vec<Vec<u8>> = rows.split(';').map(|s| s.as_bytes().to_vec()).collect(); let r = g.len(); let c = g[0].len(); let mut fresh = 0; let mut q: Vec<(usize,usize,i32)> = Vec::new(); let mut i = 0usize; while i < r { let mut j = 0usize; while j < c { if g[i][j] == b'1' { fresh += 1; } if g[i][j] == b'2' { q.push((i,j,0)); } j += 1; } i += 1; } let dirs = [(1i32,0i32),(-1,0),(0,1),(0,-1)]; let mut head = 0usize; let mut minutes = 0; while head < q.len() { let (x,y,t) = q[head]; head += 1; if t > minutes { minutes = t; } for &(dx,dy) in dirs.iter() { let nx = x as i32 + dx; let ny = y as i32 + dy; if nx >= 0 && nx < r as i32 && ny >= 0 && ny < c as i32 && g[nx as usize][ny as usize] == b'1' { g[nx as usize][ny as usize] = b'2'; fresh -= 1; q.push((nx as usize, ny as usize, t + 1)); } } } if fresh == 0 { minutes } else { -1 }\n}",
        }),
        Problem("lc_continuous_subarray_sum_bool_csv", "LC Continuous Subarray Sum Bool CSV", "Return true if a length-at-least-two contiguous subarray has sum divisible by `k`.", ["`nums` is a comma-separated list of nonnegative integers.", "`k > 0`."], "bool", [{"name": "nums", "type": "string"}, {"name": "k", "type": "int"}], [case({"nums": "23,2,4,6,7", "k": 6}, True), case({"nums": "23,2,6,4,7", "k": 6}, True), case({"nums": "23,2,6,4,7", "k": 13}, False)], lc("continuous-subarray-sum"), "medium", {
            "c": "int lc_continuous_subarray_sum_bool_csv(const char *nums, int k) {\n    int a[512], n = 0, i = 0; while (nums[i] != '\\0') { int v = 0; while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } a[n++] = v; if (nums[i] == ',') i++; }\n    for (int l = 0; l < n; l++) { int sum = 0; for (int r = l; r < n; r++) { sum += a[r]; if (r > l && sum % k == 0) return 1; } } return 0;\n}",
            "java": "class LcContinuousSubarraySumBoolCsv {\n    public static boolean lc_continuous_subarray_sum_bool_csv(String nums, int k) {\n        String[] p = nums.split(\",\"); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); for (int l = 0; l < a.length; l++) { int sum = 0; for (int r = l; r < a.length; r++) { sum += a[r]; if (r > l && sum % k == 0) return true; } } return false;\n    }\n}",
            "rust": "pub fn lc_continuous_subarray_sum_bool_csv(nums: &str, k: i32) -> bool {\n    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut l = 0usize; while l < a.len() { let mut sum = 0; let mut r = l; while r < a.len() { sum += a[r]; if r > l && sum % k == 0 { return true; } r += 1; } l += 1; } false\n}",
        }),
        Problem("lc_find_anagrams_count", "LC Find All Anagrams Count", "Return how many start positions in `s` are anagrams of `p`.", ["`s` and `p` contain lowercase English letters."], "int", [{"name": "s", "type": "string"}, {"name": "p", "type": "string"}], [case({"s": "cbaebabacd", "p": "abc"}, 2), case({"s": "abab", "p": "ab"}, 3), case({"s": "aaaa", "p": "aa"}, 3)], lc("find-all-anagrams-in-a-string"), "medium", {
            "c": "int lc_find_anagrams_count(const char *s, const char *p) {\n    int n = 0, m = 0; while (s[n] != '\\0') n++; while (p[m] != '\\0') m++; if (m > n) return 0; int need[26] = {0}, win[26] = {0}, ans = 0; for (int i = 0; i < m; i++) { need[p[i] - 'a']++; win[s[i] - 'a']++; } for (int i = 0; i <= n - m; i++) { int ok = 1; for (int c = 0; c < 26; c++) if (need[c] != win[c]) ok = 0; if (ok) ans++; if (i + m < n) { win[s[i] - 'a']--; win[s[i + m] - 'a']++; } } return ans;\n}",
            "java": "class LcFindAnagramsCount {\n    public static int lc_find_anagrams_count(String s, String p) {\n        int n = s.length(), m = p.length(); if (m > n) return 0; int[] need = new int[26], win = new int[26]; for (int i = 0; i < m; i++) { need[p.charAt(i) - 'a']++; win[s.charAt(i) - 'a']++; } int ans = 0; for (int i = 0; i <= n - m; i++) { if (java.util.Arrays.equals(need, win)) ans++; if (i + m < n) { win[s.charAt(i) - 'a']--; win[s.charAt(i + m) - 'a']++; } } return ans;\n    }\n}",
            "rust": "pub fn lc_find_anagrams_count(s: &str, p: &str) -> i32 {\n    let sb = s.as_bytes(); let pb = p.as_bytes(); if pb.len() > sb.len() { return 0; } let mut need = [0; 26]; let mut win = [0; 26]; let mut i = 0usize; while i < pb.len() { need[(pb[i] - b'a') as usize] += 1; win[(sb[i] - b'a') as usize] += 1; i += 1; } let mut ans = 0; let mut start = 0usize; while start + pb.len() <= sb.len() { if need == win { ans += 1; } if start + pb.len() < sb.len() { win[(sb[start] - b'a') as usize] -= 1; win[(sb[start + pb.len()] - b'a') as usize] += 1; } start += 1; } ans\n}",
        }),
        Problem("lc_permutation_in_string_bool", "LC Permutation In String Bool", "Return true if `s2` contains any permutation of `s1` as a substring.", ["Both strings contain lowercase English letters."], "bool", [{"name": "s1", "type": "string"}, {"name": "s2", "type": "string"}], [case({"s1": "ab", "s2": "eidbaooo"}, True), case({"s1": "ab", "s2": "eidboaoo"}, False), case({"s1": "adc", "s2": "dcda"}, True)], lc("permutation-in-string"), "medium", {
            "c": "int lc_permutation_in_string_bool(const char *s1, const char *s2) {\n    int n = 0, m = 0; while (s1[n] != '\\0') n++; while (s2[m] != '\\0') m++; if (n > m) return 0; int need[26] = {0}, win[26] = {0}; for (int i = 0; i < n; i++) { need[s1[i] - 'a']++; win[s2[i] - 'a']++; } for (int i = 0; i <= m - n; i++) { int ok = 1; for (int c = 0; c < 26; c++) if (need[c] != win[c]) ok = 0; if (ok) return 1; if (i + n < m) { win[s2[i] - 'a']--; win[s2[i + n] - 'a']++; } } return 0;\n}",
            "java": "class LcPermutationInStringBool {\n    public static boolean lc_permutation_in_string_bool(String s1, String s2) {\n        int n = s1.length(), m = s2.length(); if (n > m) return false; int[] need = new int[26], win = new int[26]; for (int i = 0; i < n; i++) { need[s1.charAt(i) - 'a']++; win[s2.charAt(i) - 'a']++; } for (int i = 0; i <= m - n; i++) { if (java.util.Arrays.equals(need, win)) return true; if (i + n < m) { win[s2.charAt(i) - 'a']--; win[s2.charAt(i + n) - 'a']++; } } return false;\n    }\n}",
            "rust": "pub fn lc_permutation_in_string_bool(s1: &str, s2: &str) -> bool {\n    let a = s1.as_bytes(); let b = s2.as_bytes(); if a.len() > b.len() { return false; } let mut need = [0; 26]; let mut win = [0; 26]; let mut i = 0usize; while i < a.len() { need[(a[i] - b'a') as usize] += 1; win[(b[i] - b'a') as usize] += 1; i += 1; } let mut start = 0usize; while start + a.len() <= b.len() { if need == win { return true; } if start + a.len() < b.len() { win[(b[start] - b'a') as usize] -= 1; win[(b[start + a.len()] - b'a') as usize] += 1; } start += 1; } false\n}",
        }),
        Problem("lc_number_of_provinces_rows", "LC Number Of Provinces Rows", "Return the number of connected components in an adjacency matrix.", ["Rows are semicolon-separated strings of `0` and `1`.", "The matrix is square."], "int", [{"name": "rows", "type": "string"}], [case({"rows": "110;110;001"}, 2), case({"rows": "100;010;001"}, 3), case({"rows": "111;111;111"}, 1)], lc("number-of-provinces"), "medium", {
            "c": "int lc_number_of_provinces_rows(const char *rows) {\n    char g[128][128]; int n = 0, cols = 0, i = 0; while (rows[i] != '\\0') { int c = 0; while (rows[i] == '0' || rows[i] == '1') g[n][c++] = rows[i++]; if (cols == 0) cols = c; n++; if (rows[i] == ';') i++; }\n    int seen[128] = {0}, stack[128], ans = 0; for (int s = 0; s < n; s++) if (!seen[s]) { ans++; int top = 0; stack[top++] = s; seen[s] = 1; while (top > 0) { int v = stack[--top]; for (int to = 0; to < cols; to++) if (g[v][to] == '1' && !seen[to]) { seen[to] = 1; stack[top++] = to; } } } return ans;\n}",
            "java": "class LcNumberOfProvincesRows {\n    public static int lc_number_of_provinces_rows(String rows) {\n        String[] rs = rows.split(\";\"); int n = rs.length, ans = 0; boolean[] seen = new boolean[n]; int[] stack = new int[n]; for (int s = 0; s < n; s++) if (!seen[s]) { ans++; int top = 0; stack[top++] = s; seen[s] = true; while (top > 0) { int v = stack[--top]; for (int to = 0; to < n; to++) if (rs[v].charAt(to) == '1' && !seen[to]) { seen[to] = true; stack[top++] = to; } } } return ans;\n    }\n}",
            "rust": "pub fn lc_number_of_provinces_rows(rows: &str) -> i32 {\n    let g: Vec<&[u8]> = rows.split(';').map(|s| s.as_bytes()).collect(); let n = g.len(); let mut seen = vec![false; n]; let mut ans = 0; let mut s = 0usize; while s < n { if !seen[s] { ans += 1; let mut st = vec![s]; seen[s] = true; while let Some(v) = st.pop() { let mut to = 0usize; while to < n { if g[v][to] == b'1' && !seen[to] { seen[to] = true; st.push(to); } to += 1; } } } s += 1; } ans\n}",
        }),
        Problem("lc_network_delay_time", "LC Network Delay Time", "Return the time for all nodes to receive a signal, or `-1`.", ["Directed weighted edges are encoded as `u,v,w;...`.", "Nodes are numbered from `1` to `n`."], "int", [{"name": "times", "type": "string"}, {"name": "n", "type": "int"}, {"name": "k", "type": "int"}], [case({"times": "2,1,1;2,3,1;3,4,1", "n": 4, "k": 2}, 2), case({"times": "1,2,1", "n": 2, "k": 1}, 1), case({"times": "1,2,1", "n": 2, "k": 2}, -1)], lc("network-delay-time"), "medium", {
            "c": "int lc_network_delay_time(const char *times, int n, int k) {\n    int u[512], v[512], w[512], m = 0, i = 0; while (times[i] != '\\0') { int vals[3]; for (int t = 0; t < 3; t++) { int x = 0; while (times[i] >= '0' && times[i] <= '9') { x = x * 10 + times[i] - '0'; i++; } vals[t] = x; if (times[i] == ',') i++; } u[m] = vals[0]; v[m] = vals[1]; w[m++] = vals[2]; if (times[i] == ';') i++; }\n    int dist[128], used[128] = {0}; for (int x = 1; x <= n; x++) dist[x] = 1000000000; dist[k] = 0; for (int step = 0; step < n; step++) { int node = -1; for (int x = 1; x <= n; x++) if (!used[x] && (node == -1 || dist[x] < dist[node])) node = x; if (node == -1 || dist[node] == 1000000000) break; used[node] = 1; for (int e = 0; e < m; e++) if (u[e] == node && dist[node] + w[e] < dist[v[e]]) dist[v[e]] = dist[node] + w[e]; }\n    int ans = 0; for (int x = 1; x <= n; x++) { if (dist[x] == 1000000000) return -1; if (dist[x] > ans) ans = dist[x]; } return ans;\n}",
            "java": "class LcNetworkDelayTime {\n    public static int lc_network_delay_time(String times, int n, int k) {\n        String[] rows = times.split(\";\"); int[][] e = new int[rows.length][3]; for (int i = 0; i < rows.length; i++) { String[] p = rows[i].split(\",\"); for (int j = 0; j < 3; j++) e[i][j] = Integer.parseInt(p[j]); } int[] dist = new int[n + 1]; boolean[] used = new boolean[n + 1]; java.util.Arrays.fill(dist, 1000000000); dist[k] = 0; for (int step = 0; step < n; step++) { int node = -1; for (int i = 1; i <= n; i++) if (!used[i] && (node == -1 || dist[i] < dist[node])) node = i; if (node == -1 || dist[node] == 1000000000) break; used[node] = true; for (int[] edge : e) if (edge[0] == node && dist[node] + edge[2] < dist[edge[1]]) dist[edge[1]] = dist[node] + edge[2]; } int ans = 0; for (int i = 1; i <= n; i++) { if (dist[i] == 1000000000) return -1; ans = Math.max(ans, dist[i]); } return ans;\n    }\n}",
            "rust": "pub fn lc_network_delay_time(times: &str, n: i32, k: i32) -> i32 {\n    let edges: Vec<[i32; 3]> = times.split(';').map(|r| { let p: Vec<i32> = r.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); [p[0], p[1], p[2]] }).collect(); let nn = n as usize; let mut dist = vec![1000000000; nn + 1]; let mut used = vec![false; nn + 1]; dist[k as usize] = 0; let mut step = 0usize; while step < nn { let mut node = 0usize; let mut i = 1usize; while i <= nn { if !used[i] && (node == 0 || dist[i] < dist[node]) { node = i; } i += 1; } if node == 0 || dist[node] == 1000000000 { break; } used[node] = true; for e in &edges { if e[0] as usize == node && dist[node] + e[2] < dist[e[1] as usize] { dist[e[1] as usize] = dist[node] + e[2]; } } step += 1; } let mut ans = 0; let mut i = 1usize; while i <= nn { if dist[i] == 1000000000 { return -1; } if dist[i] > ans { ans = dist[i]; } i += 1; } ans\n}",
        }),
        Problem("lc_shortest_path_binary_matrix_rows", "LC Shortest Path Binary Matrix Rows", "Return the shortest 8-direction path length from top-left to bottom-right, or `-1`.", ["Rows are semicolon-separated strings of `0` and `1`.", "`0` means open and `1` means blocked."], "int", [{"name": "rows", "type": "string"}], [case({"rows": "01;10"}, 2), case({"rows": "001;110;110"}, 4), case({"rows": "1"}, -1)], lc("shortest-path-in-binary-matrix"), "medium", {
            "c": "int lc_shortest_path_binary_matrix_rows(const char *rows) {\n    char g[64][64]; int n = 0, cols = 0, i = 0; while (rows[i] != '\\0') { int c = 0; while (rows[i] == '0' || rows[i] == '1') g[n][c++] = rows[i++]; if (cols == 0) cols = c; n++; if (rows[i] == ';') i++; } if (g[0][0] == '1' || g[n - 1][cols - 1] == '1') return -1;\n    int qx[4096], qy[4096], qd[4096], head = 0, tail = 0; qx[tail] = 0; qy[tail] = 0; qd[tail++] = 1; g[0][0] = '1'; int dx[8] = {1,1,1,0,0,-1,-1,-1}, dy[8] = {-1,0,1,-1,1,-1,0,1}; while (head < tail) { int x = qx[head], y = qy[head], d = qd[head++]; if (x == n - 1 && y == cols - 1) return d; for (int t = 0; t < 8; t++) { int nx = x + dx[t], ny = y + dy[t]; if (nx >= 0 && nx < n && ny >= 0 && ny < cols && g[nx][ny] == '0') { g[nx][ny] = '1'; qx[tail] = nx; qy[tail] = ny; qd[tail++] = d + 1; } } } return -1;\n}",
            "java": "class LcShortestPathBinaryMatrixRows {\n    public static int lc_shortest_path_binary_matrix_rows(String rows) {\n        String[] rs = rows.split(\";\"); int n = rs.length, c = rs[0].length(); char[][] g = new char[n][c]; for (int i = 0; i < n; i++) g[i] = rs[i].toCharArray(); if (g[0][0] == '1' || g[n - 1][c - 1] == '1') return -1; int[] qx = new int[n * c], qy = new int[n * c], qd = new int[n * c], dx = {1,1,1,0,0,-1,-1,-1}, dy = {-1,0,1,-1,1,-1,0,1}; int head = 0, tail = 0; qx[tail] = 0; qy[tail] = 0; qd[tail++] = 1; g[0][0] = '1'; while (head < tail) { int x = qx[head], y = qy[head], d = qd[head++]; if (x == n - 1 && y == c - 1) return d; for (int t = 0; t < 8; t++) { int nx = x + dx[t], ny = y + dy[t]; if (nx >= 0 && nx < n && ny >= 0 && ny < c && g[nx][ny] == '0') { g[nx][ny] = '1'; qx[tail] = nx; qy[tail] = ny; qd[tail++] = d + 1; } } } return -1;\n    }\n}",
            "rust": "pub fn lc_shortest_path_binary_matrix_rows(rows: &str) -> i32 {\n    let mut g: Vec<Vec<u8>> = rows.split(';').map(|s| s.as_bytes().to_vec()).collect(); let n = g.len(); let c = g[0].len(); if g[0][0] == b'1' || g[n - 1][c - 1] == b'1' { return -1; } let dirs = [(1i32,-1i32),(1,0),(1,1),(0,-1),(0,1),(-1,-1),(-1,0),(-1,1)]; let mut q = vec![(0usize,0usize,1i32)]; let mut head = 0usize; g[0][0] = b'1'; while head < q.len() { let (x,y,d) = q[head]; head += 1; if x == n - 1 && y == c - 1 { return d; } for &(dx,dy) in dirs.iter() { let nx = x as i32 + dx; let ny = y as i32 + dy; if nx >= 0 && nx < n as i32 && ny >= 0 && ny < c as i32 && g[nx as usize][ny as usize] == b'0' { g[nx as usize][ny as usize] = b'1'; q.push((nx as usize, ny as usize, d + 1)); } } } -1\n}",
        }),
        Problem("lc_cheapest_flights_k_stops", "LC Cheapest Flights Within K Stops", "Return the cheapest price from `src` to `dst` using at most `k` stops, or `-1`.", ["Flights are encoded as `from,to,price;...`.", "Cities are numbered from `0` to `n-1`."], "int", [{"name": "n", "type": "int"}, {"name": "flights", "type": "string"}, {"name": "src", "type": "int"}, {"name": "dst", "type": "int"}, {"name": "k", "type": "int"}], [case({"n": 4, "flights": "0,1,100;1,2,100;2,0,100;1,3,600;2,3,200", "src": 0, "dst": 3, "k": 1}, 700), case({"n": 3, "flights": "0,1,100;1,2,100;0,2,500", "src": 0, "dst": 2, "k": 1}, 200), case({"n": 3, "flights": "0,1,100;1,2,100;0,2,500", "src": 0, "dst": 2, "k": 0}, 500)], lc("cheapest-flights-within-k-stops"), "medium", {
            "c": "int lc_cheapest_flights_k_stops(int n, const char *flights, int src, int dst, int k) {\n    int u[512], v[512], w[512], m = 0, i = 0; while (flights[i] != '\\0') { int vals[3]; for (int t = 0; t < 3; t++) { int x = 0; while (flights[i] >= '0' && flights[i] <= '9') { x = x * 10 + flights[i] - '0'; i++; } vals[t] = x; if (flights[i] == ',') i++; } u[m] = vals[0]; v[m] = vals[1]; w[m++] = vals[2]; if (flights[i] == ';') i++; }\n    int dist[128], next[128]; for (int x = 0; x < n; x++) dist[x] = 1000000000; dist[src] = 0; for (int step = 0; step <= k; step++) { for (int x = 0; x < n; x++) next[x] = dist[x]; for (int e = 0; e < m; e++) if (dist[u[e]] != 1000000000 && dist[u[e]] + w[e] < next[v[e]]) next[v[e]] = dist[u[e]] + w[e]; for (int x = 0; x < n; x++) dist[x] = next[x]; } return dist[dst] == 1000000000 ? -1 : dist[dst];\n}",
            "java": "class LcCheapestFlightsKStops {\n    public static int lc_cheapest_flights_k_stops(int n, String flights, int src, int dst, int k) {\n        String[] rows = flights.split(\";\"); int[][] e = new int[rows.length][3]; for (int i = 0; i < rows.length; i++) { String[] p = rows[i].split(\",\"); for (int j = 0; j < 3; j++) e[i][j] = Integer.parseInt(p[j]); } int[] dist = new int[n]; java.util.Arrays.fill(dist, 1000000000); dist[src] = 0; for (int step = 0; step <= k; step++) { int[] next = dist.clone(); for (int[] f : e) if (dist[f[0]] != 1000000000 && dist[f[0]] + f[2] < next[f[1]]) next[f[1]] = dist[f[0]] + f[2]; dist = next; } return dist[dst] == 1000000000 ? -1 : dist[dst];\n    }\n}",
            "rust": "pub fn lc_cheapest_flights_k_stops(n: i32, flights: &str, src: i32, dst: i32, k: i32) -> i32 {\n    let edges: Vec<[usize; 3]> = flights.split(';').map(|r| { let p: Vec<usize> = r.split(',').map(|x| x.parse::<usize>().unwrap()).collect(); [p[0], p[1], p[2]] }).collect(); let nn = n as usize; let inf = 1000000000; let mut dist = vec![inf; nn]; dist[src as usize] = 0; let mut step = 0; while step <= k { let mut next = dist.clone(); for e in &edges { if dist[e[0]] != inf && dist[e[0]] + (e[2] as i32) < next[e[1]] { next[e[1]] = dist[e[0]] + (e[2] as i32); } } dist = next; step += 1; } if dist[dst as usize] == inf { -1 } else { dist[dst as usize] }\n}",
        }),
    ]


def more_real_source_problems_16() -> list[Problem]:
    lg = lambda slug: source("Luogu", slug, f"https://www.luogu.com.cn/problem/{slug}")
    return [
        Problem("luogu_p1090_merge_fruit_cost_csv", "Luogu P1090 Merge Fruit Cost CSV", "Return the minimum total cost of repeatedly merging the two smallest piles.", ["`piles` is a nonempty comma-separated list of positive integers.", "This is the Huffman-style greedy objective from Luogu P1090."], "int", [{"name": "piles", "type": "string"}], [case({"piles": "1,2,9"}, 15), case({"piles": "1,2,3,4,5"}, 33), case({"piles": "10"}, 0)], lg("P1090"), "medium", {
            "c": "int luogu_p1090_merge_fruit_cost_csv(const char *piles) {\n    int a[512], n = 0, i = 0; while (piles[i] != '\\0') { int v = 0; while (piles[i] >= '0' && piles[i] <= '9') { v = v * 10 + piles[i] - '0'; i++; } a[n++] = v; if (piles[i] == ',') i++; }\n    int cost = 0; while (n > 1) { for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) if (a[y] < a[x]) { int t = a[x]; a[x] = a[y]; a[y] = t; } int merged = a[0] + a[1]; cost += merged; a[1] = merged; for (int x = 2; x < n; x++) a[x - 1] = a[x]; n--; } return cost;\n}",
            "java": "class LuoguP1090MergeFruitCostCsv {\n    public static int luogu_p1090_merge_fruit_cost_csv(String piles) {\n        java.util.PriorityQueue<Integer> pq = new java.util.PriorityQueue<Integer>(); for (String p : piles.split(\",\")) pq.add(Integer.parseInt(p)); int cost = 0; while (pq.size() > 1) { int merged = pq.poll() + pq.poll(); cost += merged; pq.add(merged); } return cost;\n    }\n}",
            "rust": "pub fn luogu_p1090_merge_fruit_cost_csv(piles: &str) -> i32 {\n    let mut a: Vec<i32> = piles.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut cost = 0; while a.len() > 1 { a.sort(); let merged = a[0] + a[1]; cost += merged; a[1] = merged; a.remove(0); } cost\n}",
        }),
        Problem("luogu_p1803_interval_schedule_count", "Luogu P1803 Interval Schedule Count", "Return the maximum number of non-overlapping intervals that can be selected.", ["Intervals are encoded as `start,end;...`.", "Select by earliest finishing time."], "int", [{"name": "intervals", "type": "string"}], [case({"intervals": "1,3;2,4;3,5;0,6;5,7"}, 3), case({"intervals": "1,2;2,3;3,4"}, 3), case({"intervals": "1,10;2,3;4,5"}, 2)], lg("P1803"), "medium", {
            "c": "int luogu_p1803_interval_schedule_count(const char *intervals) {\n    int a[512][2], n = 0, i = 0; while (intervals[i] != '\\0') { for (int k = 0; k < 2; k++) { int v = 0; while (intervals[i] >= '0' && intervals[i] <= '9') { v = v * 10 + intervals[i] - '0'; i++; } a[n][k] = v; if (intervals[i] == ',') i++; } n++; if (intervals[i] == ';') i++; }\n    for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) if (a[y][1] < a[x][1]) { int s = a[x][0], e = a[x][1]; a[x][0] = a[y][0]; a[x][1] = a[y][1]; a[y][0] = s; a[y][1] = e; }\n    int ans = 0, end = -1; for (int x = 0; x < n; x++) if (a[x][0] >= end) { ans++; end = a[x][1]; } return ans;\n}",
            "java": "class LuoguP1803IntervalScheduleCount {\n    public static int luogu_p1803_interval_schedule_count(String intervals) {\n        String[] rows = intervals.split(\";\"); int[][] a = new int[rows.length][2]; for (int i = 0; i < rows.length; i++) { String[] p = rows[i].split(\",\"); a[i][0] = Integer.parseInt(p[0]); a[i][1] = Integer.parseInt(p[1]); } java.util.Arrays.sort(a, (x, y) -> Integer.compare(x[1], y[1])); int ans = 0, end = -1; for (int[] in : a) if (in[0] >= end) { ans++; end = in[1]; } return ans;\n    }\n}",
            "rust": "pub fn luogu_p1803_interval_schedule_count(intervals: &str) -> i32 {\n    let mut a: Vec<[i32; 2]> = intervals.split(';').map(|r| { let p: Vec<i32> = r.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); [p[0], p[1]] }).collect(); a.sort_by_key(|x| x[1]); let mut ans = 0; let mut end = -1; for inr in &a { if inr[0] >= end { ans += 1; end = inr[1]; } } ans\n}",
        }),
        Problem("luogu_p3366_mst_weight", "Luogu P3366 MST Weight", "Return the total weight of a minimum spanning tree, or `-1` if the graph is disconnected.", ["Undirected weighted edges are encoded as `u,v,w;...`.", "Vertices are numbered from `1` to `n`."], "int", [{"name": "n", "type": "int"}, {"name": "edges", "type": "string"}], [case({"n": 4, "edges": "1,2,1;2,3,2;3,4,3;1,4,10"}, 6), case({"n": 3, "edges": "1,2,5"}, -1), case({"n": 3, "edges": "1,2,2;1,3,1;2,3,4"}, 3)], lg("P3366"), "medium", {
            "c": "int luogu_p3366_mst_weight(int n, const char *edges) {\n    int u[1024], v[1024], w[1024], m = 0, i = 0; while (edges[i] != '\\0') { int vals[3]; for (int k = 0; k < 3; k++) { int x = 0; while (edges[i] >= '0' && edges[i] <= '9') { x = x * 10 + edges[i] - '0'; i++; } vals[k] = x; if (edges[i] == ',') i++; } u[m] = vals[0]; v[m] = vals[1]; w[m++] = vals[2]; if (edges[i] == ';') i++; }\n    for (int a = 0; a < m; a++) for (int b = a + 1; b < m; b++) if (w[b] < w[a]) { int tu = u[a], tv = v[a], tw = w[a]; u[a] = u[b]; v[a] = v[b]; w[a] = w[b]; u[b] = tu; v[b] = tv; w[b] = tw; }\n    int parent[256]; for (int x = 1; x <= n; x++) parent[x] = x; int total = 0, used = 0; for (int e = 0; e < m; e++) { int a = u[e], b = v[e]; while (parent[a] != a) a = parent[a]; while (parent[b] != b) b = parent[b]; if (a != b) { parent[a] = b; total += w[e]; used++; } } return used == n - 1 ? total : -1;\n}",
            "java": "class LuoguP3366MstWeight {\n    public static int luogu_p3366_mst_weight(int n, String edges) {\n        String[] rows = edges.split(\";\"); int[][] e = new int[rows.length][3]; for (int i = 0; i < rows.length; i++) { String[] p = rows[i].split(\",\"); for (int j = 0; j < 3; j++) e[i][j] = Integer.parseInt(p[j]); } java.util.Arrays.sort(e, (a, b) -> Integer.compare(a[2], b[2])); int[] parent = new int[n + 1]; for (int i = 1; i <= n; i++) parent[i] = i; int total = 0, used = 0; for (int[] edge : e) { int a = edge[0], b = edge[1]; while (parent[a] != a) a = parent[a]; while (parent[b] != b) b = parent[b]; if (a != b) { parent[a] = b; total += edge[2]; used++; } } return used == n - 1 ? total : -1;\n    }\n}",
            "rust": "pub fn luogu_p3366_mst_weight(n: i32, edges: &str) -> i32 {\n    let mut e: Vec<[i32; 3]> = edges.split(';').map(|r| { let p: Vec<i32> = r.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); [p[0], p[1], p[2]] }).collect(); e.sort_by_key(|x| x[2]); let mut parent: Vec<usize> = (0..=n as usize).collect(); fn find(parent: &mut Vec<usize>, x: usize) -> usize { if parent[x] != x { let r = find(parent, parent[x]); parent[x] = r; } parent[x] } let mut total = 0; let mut used = 0; for edge in e { let a = find(&mut parent, edge[0] as usize); let b = find(&mut parent, edge[1] as usize); if a != b { parent[a] = b; total += edge[2]; used += 1; } } if used == n - 1 { total } else { -1 }\n}",
        }),
        Problem("luogu_p3371_shortest_path", "Luogu P3371 Shortest Path", "Return the shortest-path distance from source `s` to `target`, or `-1` if unreachable.", ["Directed weighted edges are encoded as `u,v,w;...`.", "Vertices are numbered from `1` to `n`."], "int", [{"name": "n", "type": "int"}, {"name": "edges", "type": "string"}, {"name": "s", "type": "int"}, {"name": "target", "type": "int"}], [case({"n": 4, "edges": "1,2,2;1,3,5;2,3,1;3,4,2", "s": 1, "target": 4}, 5), case({"n": 3, "edges": "1,2,7", "s": 2, "target": 3}, -1), case({"n": 3, "edges": "1,2,4;2,3,6;1,3,15", "s": 1, "target": 3}, 10)], lg("P3371"), "medium", {
            "c": "int luogu_p3371_shortest_path(int n, const char *edges, int s, int target) {\n    int u[1024], v[1024], w[1024], m = 0, i = 0; while (edges[i] != '\\0') { int vals[3]; for (int k = 0; k < 3; k++) { int x = 0; while (edges[i] >= '0' && edges[i] <= '9') { x = x * 10 + edges[i] - '0'; i++; } vals[k] = x; if (edges[i] == ',') i++; } u[m] = vals[0]; v[m] = vals[1]; w[m++] = vals[2]; if (edges[i] == ';') i++; }\n    int dist[256], used[256] = {0}; for (int x = 1; x <= n; x++) dist[x] = 1000000000; dist[s] = 0; for (int step = 0; step < n; step++) { int node = -1; for (int x = 1; x <= n; x++) if (!used[x] && (node == -1 || dist[x] < dist[node])) node = x; if (node == -1 || dist[node] == 1000000000) break; used[node] = 1; for (int e = 0; e < m; e++) if (u[e] == node && dist[node] + w[e] < dist[v[e]]) dist[v[e]] = dist[node] + w[e]; } return dist[target] == 1000000000 ? -1 : dist[target];\n}",
            "java": "class LuoguP3371ShortestPath {\n    public static int luogu_p3371_shortest_path(int n, String edges, int s, int target) {\n        String[] rows = edges.split(\";\"); int[][] e = new int[rows.length][3]; for (int i = 0; i < rows.length; i++) { String[] p = rows[i].split(\",\"); for (int j = 0; j < 3; j++) e[i][j] = Integer.parseInt(p[j]); } int[] dist = new int[n + 1]; boolean[] used = new boolean[n + 1]; java.util.Arrays.fill(dist, 1000000000); dist[s] = 0; for (int step = 0; step < n; step++) { int node = -1; for (int i = 1; i <= n; i++) if (!used[i] && (node == -1 || dist[i] < dist[node])) node = i; if (node == -1 || dist[node] == 1000000000) break; used[node] = true; for (int[] edge : e) if (edge[0] == node && dist[node] + edge[2] < dist[edge[1]]) dist[edge[1]] = dist[node] + edge[2]; } return dist[target] == 1000000000 ? -1 : dist[target];\n    }\n}",
            "rust": "pub fn luogu_p3371_shortest_path(n: i32, edges: &str, s: i32, target: i32) -> i32 {\n    let e: Vec<[i32; 3]> = edges.split(';').map(|r| { let p: Vec<i32> = r.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); [p[0], p[1], p[2]] }).collect(); let nn = n as usize; let mut dist = vec![1000000000; nn + 1]; let mut used = vec![false; nn + 1]; dist[s as usize] = 0; let mut step = 0usize; while step < nn { let mut node = 0usize; let mut i = 1usize; while i <= nn { if !used[i] && (node == 0 || dist[i] < dist[node]) { node = i; } i += 1; } if node == 0 || dist[node] == 1000000000 { break; } used[node] = true; for edge in &e { if edge[0] as usize == node && dist[node] + edge[2] < dist[edge[1] as usize] { dist[edge[1] as usize] = dist[node] + edge[2]; } } step += 1; } if dist[target as usize] == 1000000000 { -1 } else { dist[target as usize] }\n}",
        }),
        Problem("luogu_p2678_jump_stone_distance", "Luogu P2678 Jump Stone Distance", "Return the largest possible minimum jump distance after removing at most `remove` stones.", ["`length` is the river length.", "`stones` is a comma-separated sorted list of internal stone positions."], "int", [{"name": "length", "type": "int"}, {"name": "stones", "type": "string"}, {"name": "remove", "type": "int"}], [case({"length": 25, "stones": "2,11,14,17,21", "remove": 2}, 4), case({"length": 10, "stones": "2,4,7", "remove": 1}, 3), case({"length": 9, "stones": "3,6", "remove": 0}, 3)], lg("P2678"), "medium", {
            "c": "int luogu_p2678_jump_stone_distance(int length, const char *stones, int remove) {\n    int a[512], n = 0, i = 0; while (stones[i] != '\\0') { int v = 0; while (stones[i] >= '0' && stones[i] <= '9') { v = v * 10 + stones[i] - '0'; i++; } a[n++] = v; if (stones[i] == ',') i++; } a[n++] = length; int lo = 1, hi = length, ans = 0; while (lo <= hi) { int mid = lo + (hi - lo) / 2, last = 0, removed = 0; for (int x = 0; x < n; x++) { if (a[x] - last < mid) removed++; else last = a[x]; } if (removed <= remove) { ans = mid; lo = mid + 1; } else hi = mid - 1; } return ans;\n}",
            "java": "class LuoguP2678JumpStoneDistance {\n    public static int luogu_p2678_jump_stone_distance(int length, String stones, int remove) {\n        String[] p = stones.split(\",\"); int[] a = new int[p.length + 1]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); a[p.length] = length; int lo = 1, hi = length, ans = 0; while (lo <= hi) { int mid = lo + (hi - lo) / 2, last = 0, removed = 0; for (int x : a) { if (x - last < mid) removed++; else last = x; } if (removed <= remove) { ans = mid; lo = mid + 1; } else hi = mid - 1; } return ans;\n    }\n}",
            "rust": "pub fn luogu_p2678_jump_stone_distance(length: i32, stones: &str, remove: i32) -> i32 {\n    let mut a: Vec<i32> = stones.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); a.push(length); let mut lo = 1; let mut hi = length; let mut ans = 0; while lo <= hi { let mid = lo + (hi - lo) / 2; let mut last = 0; let mut removed = 0; for &x in &a { if x - last < mid { removed += 1; } else { last = x; } } if removed <= remove { ans = mid; lo = mid + 1; } else { hi = mid - 1; } } ans\n}",
        }),
    ]


def infer_difficulty(data: dict) -> str:
    if data.get("difficulty") in DIFFICULTIES:
        return data["difficulty"]
    name = data.get("name", "")
    src = data.get("source") or {}
    src_name = src.get("name")
    slug = src.get("slug", "")
    if src_name == "LeetCode":
        if slug in LEETCODE_HARD_SLUGS:
            return "hard"
        if slug in LEETCODE_MEDIUM_SLUGS:
            return "medium"
        return "easy"
    if src_name == "Luogu":
        return "medium" if slug in LUOGU_MEDIUM_SLUGS else "easy"
    if src_name == "FormalBench":
        if name in FORMALBENCH_HARD_NAMES:
            return "hard"
        if name.startswith("fb_easy_") or name.startswith("formal_"):
            return "easy"
        return "medium"
    if src_name == "SpecGenBench":
        if name in {"sg_matrix_2x2_product_trace"}:
            return "hard"
        if name in {
            "sg_largest_triangle_perimeter",
            "sg_pass_pillow_holder",
            "sg_ugly_number_flag",
            "sg_repeated_char_first_index",
            "sg_repeated_num_first_index",
            "sg_unique_num_first_index",
            "sg_overlap_area",
            "sg_one_bit_character",
            "sg_all_unique_lowercase",
        }:
            return "medium"
        return "easy"
    if name in LOCAL_MEDIUM_NAMES:
        return "medium"
    if name.startswith(("aug_", "array_", "string_")) and any(token in name for token in ("search", "intersection", "move", "reverse", "duplicates", "longest", "sorted")):
        return "medium"
    return "easy"


def write_problem(problem: Problem) -> None:
    if problem.difficulty not in DIFFICULTIES:
        raise ValueError(f"bad difficulty for {problem.name}: {problem.difficulty}")
    for language in LANGUAGES:
        path = DATASETS / language / f"{problem.name}.md"
        path.write_text(md(problem, language), encoding="utf-8")
    (DATASETS / "tests" / f"{problem.name}.json").write_text(
        json.dumps(test_json(problem), indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


def normalize_json_files() -> list[dict]:
    problems = []
    for path in sorted((DATASETS / "tests").glob("*.json")):
        data = json.loads(path.read_text(encoding="utf-8"))
        if data.get("name") in {"climb_stairs", "factorial"}:
            data["function"] = data["name"]
        data["difficulty"] = infer_difficulty(data)
        if not data.get("source"):
            data["source"] = DEFAULT_LOCAL_SOURCE
        path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
        entry = {
            "name": data["name"],
            "return_type": data.get("return_type"),
            "params": data.get("params", []),
            "difficulty": data["difficulty"],
        }
        if "function" in data:
            entry["function"] = data["function"]
        if "augment" in data:
            entry["augment"] = data["augment"]
        entry["source"] = data["source"]
        problems.append(entry)
    problems.sort(key=lambda p: p["name"])
    return problems


def write_manifest_and_readme(problems: list[dict]) -> None:
    manifest = {
        "source": "Combined internal, external, and augment algorithm datasets",
        "style": "HumanEval-like single-function tasks",
        "languages": list(LANGUAGES),
        "requirements": ["single function", "standard library only", "shared tests"],
        "difficulty_levels": list(DIFFICULTIES),
        "problems": problems,
    }
    (DATASETS / "manifest.json").write_text(
        json.dumps(manifest, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    counts = Counter(p["difficulty"] for p in problems)
    source_counts = Counter((p.get("source") or {}).get("name", "local") for p in problems)
    (DATASETS / "README.md").write_text(
        "# Combined Algorithm Dataset\n\n"
        f"- Problems: {len(problems)}\n"
        "- Languages: C, Java, Rust\n"
        "- Layout: one Markdown file per problem per language in `c/`, `java/`, and `rust/`.\n"
        "- Tests: shared JSON files in `tests/`.\n"
        "- Difficulty: every problem has a `difficulty` field in `tests/*.json` and `manifest.json`.\n"
        f"- Difficulty counts: easy {counts['easy']}, medium {counts['medium']}, hard {counts['hard']}.\n"
        f"- Source counts: CAV-JAVA local dataset {source_counts['CAV-JAVA local dataset']}, LeetCode {source_counts['LeetCode']}, Luogu {source_counts['Luogu']}, FormalBench {source_counts['FormalBench']}, SpecGenBench {source_counts['SpecGenBench']}, Exercism {source_counts['Exercism']}.\n"
        "- Source attribution: every problem includes a `source` field in `tests/*.json` and `manifest.json`.\n"
        "- Generation: `python3 scripts/expand_multisource_dataset.py`\n",
        encoding="utf-8",
    )


def main() -> None:
    for directory in [DATASETS / lang for lang in LANGUAGES] + [DATASETS / "tests"]:
        if not directory.exists():
            raise FileNotFoundError(f"missing dataset directory: {directory}")
    new_problems = (
        leetcode_problems()
        + luogu_problems()
        + formalbench_problems()
        + specgenbench_problems()
        + curated_expansion_problems()
        + exercism_expansion_problems()
        + more_real_source_problems()
        + more_real_source_problems_2()
        + more_real_source_problems_3()
        + more_real_source_problems_4()
        + more_real_source_problems_5()
        + more_real_source_problems_6()
        + more_real_source_problems_7()
        + more_real_source_problems_8()
        + more_real_source_problems_9()
        + more_real_source_problems_10()
        + more_real_source_problems_11()
        + more_real_source_problems_12()
        + more_real_source_problems_13()
        + more_real_source_problems_14()
        + more_real_source_problems_15()
        + more_real_source_problems_16()
    )
    names = [p.name for p in new_problems]
    if len(names) != len(set(names)):
        raise ValueError("duplicate new problem names")
    for problem in new_problems:
        write_problem(problem)
    problems = normalize_json_files()
    write_manifest_and_readme(problems)
    counts = Counter(p["difficulty"] for p in problems)
    print(
        f"dataset now has {len(problems)} problems: "
        f"easy={counts['easy']}, medium={counts['medium']}, hard={counts['hard']}"
    )


if __name__ == "__main__":
    main()

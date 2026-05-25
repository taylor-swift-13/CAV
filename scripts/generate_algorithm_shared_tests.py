#!/usr/bin/env python3
"""Generate shared JSON tests for datasets/internal."""

from __future__ import annotations

import json
import shutil
from copy import deepcopy
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
TEST_DIR = REPO_ROOT / "datasets" / "internal" / "tests"
TARGET_CASES_PER_PROBLEM = 10


def ip(name: str) -> dict:
    return {"name": name, "type": "int"}


def cp(name: str) -> dict:
    return {"name": name, "type": "char"}


def arr(name: str) -> dict:
    return {"name": name, "type": "int_array"}


def marr(name: str) -> dict:
    return {"name": name, "type": "mut_int_array"}


def oarr(name: str) -> dict:
    return {"name": name, "type": "out_int_array"}


def cstr(name: str) -> dict:
    return {"name": name, "type": "c_string"}


def mcstr(name: str) -> dict:
    return {"name": name, "type": "mut_c_string"}


def ocstr(name: str) -> dict:
    return {"name": name, "type": "out_c_string"}


SPECS = {
    "abs_value": ("int", [ip("x")]),
    "add_two": ("int", [ip("a"), ip("b")]),
    "arithmetic_series": ("int", [ip("a"), ip("d"), ip("n")]),
    "array_add": ("void", [ip("n"), arr("a"), arr("b"), oarr("out")]),
    "array_adjacent_diff": ("void", [ip("n"), arr("a"), oarr("out")]),
    "array_all_less_than_k": ("int", [ip("n"), arr("a"), ip("k")]),
    "array_all_positive": ("int", [ip("n"), arr("a")]),
    "array_all_zero": ("int", [ip("n"), arr("a")]),
    "array_any_equal_sum": ("int", [ip("n"), arr("a"), ip("x"), ip("y")]),
    "array_any_negative": ("int", [ip("n"), arr("a")]),
    "array_any_zero": ("int", [ip("n"), arr("a")]),
    "array_clamp_nonnegative": ("void", [ip("n"), marr("a")]),
    "array_contains": ("int", [ip("n"), arr("a"), ip("k")]),
    "array_copy_positive": ("void", [ip("n"), arr("a"), oarr("out")]),
    "array_count_distinct_sorted": ("int", [ip("n"), arr("a")]),
    "array_count_even": ("int", [ip("n"), arr("a")]),
    "array_count_greater_than_k": ("int", [ip("n"), arr("a"), ip("k")]),
    "array_count_increasing_steps": ("int", [ip("n"), arr("a")]),
    "array_count_nonzero": ("int", [ip("n"), arr("a")]),
    "array_count_negative": ("int", [ip("n"), arr("a")]),
    "array_count_odd": ("int", [ip("n"), arr("a")]),
    "array_count_between": ("int", [ip("n"), arr("a"), ip("lo"), ip("hi")]),
    "array_count_transitions": ("int", [ip("n"), arr("a")]),
    "array_count_zero": ("int", [ip("n"), arr("a")]),
    "array_equal": ("int", [ip("n"), arr("a"), arr("b")]),
    "array_all_even": ("int", [ip("n"), arr("a")]),
    "array_sum_abs": ("int", [ip("n"), arr("a")]),
    "array_fill_value": ("void", [ip("n"), ip("k"), marr("a")]),
    "array_copy_even": ("void", [ip("n"), arr("a"), oarr("out")]),
    "array_find_last_equal": ("int", [ip("n"), arr("a"), ip("k")]),
    "array_first": ("int", [ip("n"), arr("a")]),
    "array_first_negative": ("int", [ip("n"), arr("a")]),
    "array_first_peak": ("int", [ip("n"), arr("a")]),
    "array_has_adjacent_equal": ("int", [ip("n"), arr("a")]),
    "array_increment": ("void", [ip("n"), marr("a")]),
    "array_init": ("void", [ip("n"), marr("a")]),
    "array_index_of_min": ("int", [ip("n"), arr("a")]),
    "array_index_of_max": ("int", [ip("n"), arr("a")]),
    "array_intersection_count_sorted": ("int", [ip("n"), arr("a"), ip("m"), arr("b")]),
    "array_is_strictly_increasing": ("int", [ip("n"), arr("a")]),
    "array_last": ("int", [ip("n"), arr("a")]),
    "array_last_positive": ("int", [ip("n"), arr("a")]),
    "array_longest_nonnegative_run": ("int", [ip("n"), arr("a")]),
    "array_max": ("int", [ip("n"), arr("a")]),
    "array_min": ("int", [ip("n"), arr("a")]),
    "array_move_zeroes_to_end": ("void", [ip("n"), marr("a")]),
    "array_negate": ("void", [ip("n"), arr("a"), oarr("out")]),
    "array_pairwise_sum": ("void", [ip("n"), arr("a"), arr("b"), oarr("out")]),
    "array_prefix_max": ("void", [ip("n"), arr("a"), oarr("out")]),
    "array_product_small": ("int", [ip("n"), arr("a")]),
    "array_remove_value_to_output": ("int", [ip("n"), arr("a"), ip("k"), oarr("out")]),
    "array_replace_k": ("void", [ip("n"), marr("a"), ip("old_k"), ip("new_k")]),
    "array_replace_negative_zero": ("void", [ip("n"), marr("a")]),
    "array_reverse_in_place": ("void", [ip("n"), marr("a")]),
    "array_scale": ("void", [ip("n"), arr("a"), ip("k"), oarr("out")]),
    "array_second_largest": ("int", [ip("n"), arr("a")]),
    "array_sign": ("void", [ip("n"), arr("a"), oarr("out")]),
    "array_sum": ("int", [ip("n"), arr("a")]),
    "array_sum_even_indices": ("int", [ip("n"), arr("a")]),
    "array_sum_nonnegative": ("int", [ip("n"), arr("a")]),
    "array_sum_positive": ("int", [ip("n"), arr("a")]),
    "array_none_zero": ("int", [ip("n"), arr("a")]),
    "array_swap_ends": ("void", [ip("n"), marr("a")]),
    "binary_search": ("int", [ip("n"), arr("a"), ip("target")]),
    "binary_search_first": ("int", [ip("n"), arr("a"), ip("target")]),
    "binary_search_last": ("int", [ip("n"), arr("a"), ip("target")]),
    "bubble_sort": ("void", [marr("a"), ip("n")]),
    "climb_stairs": ("int", [ip("n")]),
    "copy_array": ("void", [ip("n"), arr("src"), oarr("dst")]),
    "count_digits": ("int", [ip("n")]),
    "count_divisors": ("int", [ip("n")]),
    "count_equal_to_k": ("int", [ip("n"), arr("a"), ip("k")]),
    "count_multiples": ("int", [ip("n"), ip("k")]),
    "count_positive": ("int", [ip("n"), arr("a")]),
    "count_set_bits": ("int", [ip("n")]),
    "digit_sum": ("int", [ip("n")]),
    "digit_product": ("int", [ip("n")]),
    "double_nonnegative": ("int", [ip("n")]),
    "factorial": ("int", [ip("n")]),
    "fibonacci": ("int", [ip("n")]),
    "fibonacci_mod": ("int", [ip("n"), ip("mod")]),
    "find_first_equal": ("int", [ip("n"), arr("a"), ip("k")]),
    "gcd_iterative": ("int", [ip("a"), ip("b")]),
    "house_robber": ("int", [ip("n"), arr("a")]),
    "insertion_sort": ("void", [ip("n"), marr("a")]),
    "is_multiple": ("int", [ip("a"), ip("b")]),
    "is_between_inclusive": ("int", [ip("x"), ip("lo"), ip("hi")]),
    "is_prime_simple": ("int", [ip("n")]),
    "is_sorted_nondecreasing": ("int", [ip("n"), arr("a")]),
    "last_digit": ("int", [ip("n")]),
    "lcm_simple": ("int", [ip("a"), ip("b")]),
    "longest_increasing_run": ("int", [ip("n"), arr("a")]),
    "lower_bound": ("int", [ip("n"), arr("a"), ip("target")]),
    "majority_candidate": ("int", [ip("n"), arr("a")]),
    "max_abs_two": ("int", [ip("a"), ip("b")]),
    "max_of_three": ("int", [ip("a"), ip("b"), ip("c")]),
    "max_of_two": ("int", [ip("a"), ip("b")]),
    "max_subarray_sum": ("int", [ip("n"), arr("a")]),
    "merge_sorted_arrays": ("void", [ip("n"), arr("a"), ip("m"), arr("b"), oarr("out")]),
    "min_cost_two_steps": ("int", [ip("n"), arr("cost")]),
    "min_of_three": ("int", [ip("a"), ip("b"), ip("c")]),
    "partition_nonnegative": ("int", [ip("n"), marr("a")]),
    "power_nonnegative": ("int", [ip("base"), ip("exp")]),
    "clamp_int": ("int", [ip("x"), ip("lo"), ip("hi")]),
    "prefix_sum": ("void", [ip("n"), arr("a"), oarr("out")]),
    "remove_duplicates_sorted": ("int", [ip("n"), marr("a")]),
    "reverse_copy": ("void", [ip("n"), arr("src"), oarr("dst")]),
    "reverse_digits": ("int", [ip("n")]),
    "rotate_left_by_one": ("void", [ip("n"), marr("a")]),
    "selection_sort": ("void", [ip("n"), marr("a")]),
    "set_zero": ("void", [ip("n"), marr("a")]),
    "square_nonnegative": ("int", [ip("n")]),
    "string_all_digits": ("int", [cstr("s")]),
    "string_all_lowercase": ("int", [cstr("s")]),
    "string_all_uppercase": ("int", [cstr("s")]),
    "string_any_lowercase": ("int", [cstr("s")]),
    "string_collapse_spaces": ("void", [cstr("s"), ocstr("out")]),
    "string_contains_char": ("int", [cstr("s"), cp("c")]),
    "string_copy": ("void", [cstr("src"), ocstr("dst")]),
    "string_copy_prefix": ("void", [ip("k"), cstr("src"), ocstr("dst")]),
    "string_count_char": ("int", [cstr("s"), cp("c")]),
    "string_count_digits": ("int", [cstr("s")]),
    "string_count_hash": ("int", [cstr("s")]),
    "string_count_alnum": ("int", [cstr("s")]),
    "string_count_lowercase": ("int", [cstr("s")]),
    "string_count_not_char": ("int", [cstr("s"), cp("c")]),
    "string_count_punctuation": ("int", [cstr("s")]),
    "string_count_spaces": ("int", [cstr("s")]),
    "string_count_uppercase": ("int", [cstr("s")]),
    "string_count_vowels": ("int", [cstr("s")]),
    "string_count_words_simple": ("int", [cstr("s")]),
    "string_ends_with_char": ("int", [cstr("s"), cp("c")]),
    "string_equal": ("int", [cstr("a"), cstr("b")]),
    "string_fill_char": ("void", [ip("n"), cp("c"), ocstr("s")]),
    "string_find_char": ("int", [cstr("s"), cp("c")]),
    "string_find_last_char": ("int", [cstr("s"), cp("c")]),
    "string_first_char": ("char", [cstr("s")]),
    "string_has_double_char": ("int", [cstr("s")]),
    "string_has_digit": ("int", [cstr("s")]),
    "string_is_empty": ("int", [cstr("s")]),
    "string_is_palindrome": ("int", [ip("n"), cstr("s")]),
    "string_last_char": ("char", [cstr("s")]),
    "string_length": ("int", [cstr("s")]),
    "string_remove_char_to_output": ("int", [cstr("s"), ocstr("out"), cp("c")]),
    "string_replace_char": ("void", [mcstr("s"), cp("old_c"), cp("new_c")]),
    "string_replace_spaces_underscore": ("void", [mcstr("s")]),
    "string_reverse_copy": ("void", [ip("n"), cstr("src"), ocstr("dst")]),
    "string_set_a": ("void", [ip("n"), mcstr("s")]),
    "string_starts_with": ("int", [cstr("s"), cp("c")]),
    "string_starts_with_char": ("int", [cstr("s"), cp("c")]),
    "string_to_lower_ascii": ("void", [mcstr("s")]),
    "string_to_upper_ascii": ("void", [mcstr("s")]),
    "string_trim_last_char": ("void", [ip("n"), mcstr("s")]),
    "sum_to_n": ("int", [ip("n")]),
    "sum_squares_to_n": ("int", [ip("n")]),
    "tribonacci": ("int", [ip("n")]),
    "two_sum_sorted": ("int", [ip("n"), arr("a"), ip("target")]),
    "upper_bound": ("int", [ip("n"), arr("a"), ip("target")]),
    "ways_to_reach": ("int", [ip("n")]),
}

FUNCTION_OVERRIDES = {"factorial": "fac", "climb_stairs": "climbStairs"}


def arrn(x: dict, name: str = "a") -> list[int]:
    return x[name][: x["n"]]


def cbuf(size: int) -> str:
    return "_" * max(1, size)


def sign(v: int) -> int:
    return 1 if v > 0 else -1 if v < 0 else 0


def lower_bound(a: list[int], target: int) -> int:
    lo, hi = 0, len(a)
    while lo < hi:
        mid = (lo + hi) // 2
        if a[mid] < target:
            lo = mid + 1
        else:
            hi = mid
    return lo


def upper_bound(a: list[int], target: int) -> int:
    lo, hi = 0, len(a)
    while lo < hi:
        mid = (lo + hi) // 2
        if a[mid] <= target:
            lo = mid + 1
        else:
            hi = mid
    return lo


def reference(name: str, x: dict) -> tuple[object | None, dict]:
    a = arrn(x) if isinstance(x.get("a"), list) and "n" in x else x.get("a", [])
    if name == "abs_value": return (abs(x["x"]), {})
    if name == "add_two": return (x["a"] + x["b"], {})
    if name == "arithmetic_series": return (sum(x["a"] + i * x["d"] for i in range(x["n"])), {})
    if name == "array_add": return (None, {"out": [u + v for u, v in zip(a, x["b"][: x["n"]])]})
    if name == "array_adjacent_diff": return (None, {"out": [a[i + 1] - a[i] for i in range(max(0, x["n"] - 1))] + ([0] if x["n"] else [])})
    if name == "array_all_less_than_k": return (int(all(v < x["k"] for v in a)), {})
    if name == "array_all_positive": return (int(all(v > 0 for v in a)), {})
    if name == "array_all_zero": return (int(all(v == 0 for v in a)), {})
    if name == "array_any_equal_sum": return (int(any(v == x["x"] + x["y"] for v in a)), {})
    if name == "array_any_negative": return (int(any(v < 0 for v in a)), {})
    if name == "array_any_zero": return (int(any(v == 0 for v in a)), {})
    if name == "array_clamp_nonnegative": return (None, {"a": [max(0, v) for v in a]})
    if name == "array_contains": return (int(x["k"] in a), {})
    if name == "array_copy_positive": return (None, {"out": [v if v > 0 else 0 for v in a]})
    if name == "array_count_distinct_sorted": return ((0 if not a else 1 + sum(a[i] != a[i - 1] for i in range(1, len(a)))), {})
    if name == "array_count_even": return (sum(v % 2 == 0 for v in a), {})
    if name == "array_count_greater_than_k": return (sum(v > x["k"] for v in a), {})
    if name == "array_count_increasing_steps": return (sum(a[i] > a[i - 1] for i in range(1, len(a))), {})
    if name == "array_count_negative": return (sum(v < 0 for v in a), {})
    if name == "array_count_nonzero": return (sum(v != 0 for v in a), {})
    if name == "array_count_odd": return (sum(v % 2 != 0 for v in a), {})
    if name == "array_count_between": return (sum(x["lo"] <= v <= x["hi"] for v in a), {})
    if name == "array_count_transitions": return (sum(a[i] != a[i - 1] for i in range(1, len(a))), {})
    if name == "array_count_zero": return (sum(v == 0 for v in a), {})
    if name == "array_equal": return (int(a == x["b"][: x["n"]]), {})
    if name == "array_all_even": return (int(all(v % 2 == 0 for v in a)), {})
    if name == "array_sum_abs": return (sum(abs(v) for v in a), {})
    if name == "array_fill_value": return (None, {"a": [x["k"]] * x["n"]})
    if name == "array_copy_even": return (None, {"out": [v if v % 2 == 0 else 0 for v in a]})
    if name == "array_find_last_equal": return (next((i for i in range(len(a) - 1, -1, -1) if a[i] == x["k"]), -1), {})
    if name == "array_first": return (a[0], {})
    if name == "array_first_negative": return (next((i for i, v in enumerate(a) if v < 0), -1), {})
    if name == "array_first_peak": return (next((i for i in range(1, len(a) - 1) if a[i] > a[i - 1] and a[i] > a[i + 1]), -1), {})
    if name == "array_has_adjacent_equal": return (int(any(a[i] == a[i - 1] for i in range(1, len(a)))), {})
    if name == "array_increment": return (None, {"a": [v + 1 for v in a]})
    if name == "array_init": return (None, {"a": [0] * x["n"]})
    if name == "array_index_of_min": return (min(range(len(a)), key=lambda i: a[i]), {})
    if name == "array_index_of_max": return (max(range(len(a)), key=lambda i: a[i]), {})
    if name == "array_intersection_count_sorted":
        b, i, j, cnt = x["b"][: x["m"]], 0, 0, 0
        while i < len(a) and j < len(b):
            if a[i] == b[j]: cnt += 1; i += 1; j += 1
            elif a[i] < b[j]: i += 1
            else: j += 1
        return (cnt, {})
    if name == "array_is_strictly_increasing": return (int(all(a[i] > a[i - 1] for i in range(1, len(a)))), {})
    if name == "array_last": return (a[-1], {})
    if name == "array_last_positive": return (next((i for i in range(len(a) - 1, -1, -1) if a[i] > 0), -1), {})
    if name == "array_longest_nonnegative_run":
        best = cur = 0
        for v in a:
            cur = cur + 1 if v >= 0 else 0
            best = max(best, cur)
        return (best, {})
    if name == "array_max": return (max(a), {})
    if name == "array_min": return (min(a), {})
    if name == "array_move_zeroes_to_end":
        nz = [v for v in a if v != 0]
        return (None, {"a": nz + [0] * (len(a) - len(nz))})
    if name == "array_none_zero": return (int(all(v != 0 for v in a)), {})
    if name == "array_negate": return (None, {"out": [-v for v in a]})
    if name == "array_pairwise_sum": return (None, {"out": [u + v for u, v in zip(a, x["b"][: x["n"]])]})
    if name == "array_prefix_max":
        out, m = [], None
        for v in a:
            m = v if m is None else max(m, v)
            out.append(m)
        return (None, {"out": out})
    if name == "array_product_small":
        product = 1
        for v in a: product *= v
        return (product, {})
    if name == "array_remove_value_to_output":
        out = [v for v in a if v != x["k"]]
        return (len(out), {"out": out + [0] * (x["n"] - len(out))})
    if name == "array_replace_k": return (None, {"a": [x["new_k"] if v == x["old_k"] else v for v in a]})
    if name == "array_replace_negative_zero": return (None, {"a": [0 if v < 0 else v for v in a]})
    if name == "array_reverse_in_place": return (None, {"a": list(reversed(a))})
    if name == "array_scale": return (None, {"out": [v * x["k"] for v in a]})
    if name == "array_second_largest":
        vals = sorted(a, reverse=True)
        return (vals[1], {})
    if name == "array_sign": return (None, {"out": [sign(v) for v in a]})
    if name == "array_sum": return (sum(a), {})
    if name == "array_sum_even_indices": return (sum(a[0::2]), {})
    if name == "array_sum_nonnegative": return (sum(v for v in a if v >= 0), {})
    if name == "array_sum_positive": return (sum(v for v in a if v > 0), {})
    if name == "array_swap_ends":
        out = a[:]
        if len(out) > 1: out[0], out[-1] = out[-1], out[0]
        return (None, {"a": out})
    if name in ("binary_search", "binary_search_first"):
        return (next((i for i, v in enumerate(a) if v == x["target"]), -1), {})
    if name == "binary_search_last":
        return (next((i for i in range(len(a) - 1, -1, -1) if a[i] == x["target"]), -1), {})
    if name in ("bubble_sort", "insertion_sort", "selection_sort"): return (None, {"a": sorted(a)})
    if name == "climb_stairs" or name == "ways_to_reach":
        n = x["n"]; f = [1, 1]
        for i in range(2, n + 1): f.append(f[-1] + f[-2])
        return (f[n], {})
    if name == "copy_array": return (None, {"dst": x["src"][: x["n"]]})
    if name == "count_digits": return (len(str(abs(x["n"]))), {})
    if name == "count_divisors": return (sum(x["n"] % i == 0 for i in range(1, x["n"] + 1)), {})
    if name == "count_equal_to_k": return (sum(v == x["k"] for v in a), {})
    if name == "count_multiples": return (sum(i % x["k"] == 0 for i in range(1, x["n"] + 1)), {})
    if name == "count_positive": return (sum(v > 0 for v in a), {})
    if name == "count_set_bits": return (bin(x["n"]).count("1"), {})
    if name == "digit_sum": return (sum(int(ch) for ch in str(abs(x["n"]))), {})
    if name == "digit_product":
        if x["n"] == 0:
            return (0, {})
        p = 1
        for ch in str(abs(x["n"])):
            p *= int(ch)
        return (p, {})
    if name == "double_nonnegative": return (x["n"] + x["n"], {})
    if name == "factorial":
        r = 1
        for i in range(2, x["n"] + 1): r *= i
        return (r, {})
    if name == "fibonacci" or name == "tribonacci":
        if name == "fibonacci":
            f = [0, 1]
            for i in range(2, x["n"] + 1): f.append(f[-1] + f[-2])
        else:
            f = [0, 1, 1]
            for i in range(3, x["n"] + 1): f.append(f[-1] + f[-2] + f[-3])
        return (f[x["n"]], {})
    if name == "fibonacci_mod":
        r, _ = reference("fibonacci", {"n": x["n"]})
        return (r % x["mod"], {})
    if name == "find_first_equal": return (next((i for i, v in enumerate(a) if v == x["k"]), -1), {})
    if name == "gcd_iterative":
        aa, bb = abs(x["a"]), abs(x["b"])
        while bb: aa, bb = bb, aa % bb
        return (aa, {})
    if name == "house_robber":
        prev = cur = 0
        for v in a: prev, cur = cur, max(cur, prev + v)
        return (cur, {})
    if name == "is_multiple": return (int(x["b"] != 0 and x["a"] % x["b"] == 0), {})
    if name == "is_between_inclusive": return (int(x["lo"] <= x["x"] <= x["hi"]), {})
    if name == "is_prime_simple":
        n = x["n"]
        return (int(n >= 2 and all(n % i for i in range(2, int(n**0.5) + 1))), {})
    if name == "is_sorted_nondecreasing": return (int(all(a[i] >= a[i - 1] for i in range(1, len(a)))), {})
    if name == "last_digit": return (x["n"] % 10, {})
    if name == "lcm_simple":
        g, _ = reference("gcd_iterative", {"a": x["a"], "b": x["b"]})
        return (abs(x["a"] * x["b"]) // g, {})
    if name == "longest_increasing_run":
        best = cur = 1
        for i in range(1, len(a)):
            cur = cur + 1 if a[i] > a[i - 1] else 1
            best = max(best, cur)
        return (best if a else 0, {})
    if name == "lower_bound": return (lower_bound(a, x["target"]), {})
    if name == "majority_candidate":
        cand = count = 0
        for v in a:
            if count == 0: cand, count = v, 1
            elif v == cand: count += 1
            else: count -= 1
        return (cand, {})
    if name == "max_abs_two": return (max(abs(x["a"]), abs(x["b"])), {})
    if name == "max_of_three": return (max(x["a"], x["b"], x["c"]), {})
    if name == "max_of_two": return (max(x["a"], x["b"]), {})
    if name == "max_subarray_sum":
        best = cur = a[0]
        for v in a[1:]: cur = max(v, cur + v); best = max(best, cur)
        return (best, {})
    if name == "merge_sorted_arrays":
        return (None, {"out": sorted(x["a"][: x["n"]] + x["b"][: x["m"]])})
    if name == "min_cost_two_steps":
        cost = x["cost"][: x["n"]]
        if len(cost) == 1: return (cost[0], {})
        dp0, dp1 = cost[0], cost[0] + cost[1]
        for v in cost[2:]: dp0, dp1 = dp1, min(dp0, dp1) + v
        return (dp1, {})
    if name == "min_of_three": return (min(x["a"], x["b"], x["c"]), {})
    if name == "partition_nonnegative":
        out = a[:]
        i, j = 0, len(out) - 1
        while i <= j:
            if out[i] < 0:
                i += 1
            else:
                out[i], out[j] = out[j], out[i]
                j -= 1
        return (i, {"a": out})
    if name == "power_nonnegative": return (x["base"] ** x["exp"], {})
    if name == "clamp_int": return (min(max(x["x"], x["lo"]), x["hi"]), {})
    if name == "prefix_sum":
        s = 0; out = []
        for v in a: s += v; out.append(s)
        return (None, {"out": out})
    if name == "remove_duplicates_sorted":
        out = []
        for v in a:
            if not out or out[-1] != v: out.append(v)
        return (len(out), {"a": out + a[len(out):]})
    if name == "reverse_copy": return (None, {"dst": list(reversed(x["src"][: x["n"]]))})
    if name == "reverse_digits": return (int(str(abs(x["n"]))[::-1]), {})
    if name == "rotate_left_by_one": return (None, {"a": (a[1:] + a[:1]) if a else []})
    if name == "set_zero": return (None, {"a": [0] * x["n"]})
    if name == "square_nonnegative": return (x["n"] * x["n"], {})
    if name.startswith("string_"): return string_reference(name, x)
    if name == "sum_to_n": return (x["n"] * (x["n"] + 1) // 2, {})
    if name == "sum_squares_to_n": return (sum(i * i for i in range(1, x["n"] + 1)), {})
    if name == "two_sum_sorted":
        s = set()
        for v in a:
            if x["target"] - v in s: return (1, {})
            s.add(v)
        return (0, {})
    if name == "upper_bound": return (upper_bound(a, x["target"]), {})
    raise KeyError(name)


def string_reference(name: str, x: dict) -> tuple[object | None, dict]:
    s = x.get("s", "")
    if name == "string_all_digits": return (int(all("0" <= ch <= "9" for ch in s)), {})
    if name == "string_all_lowercase": return (int(all("a" <= ch <= "z" for ch in s)), {})
    if name == "string_all_uppercase": return (int(all("A" <= ch <= "Z" for ch in s)), {})
    if name == "string_any_lowercase": return (int(any("a" <= ch <= "z" for ch in s)), {})
    if name == "string_collapse_spaces": return (None, {"out": " ".join(s.split(" ")) if False else collapse_spaces(s)})
    if name == "string_contains_char": return (int(x["c"] in s), {})
    if name == "string_copy": return (None, {"dst": x["src"]})
    if name == "string_copy_prefix": return (None, {"dst": x["src"][: x["k"]]})
    if name == "string_count_char": return (s.count(x["c"]), {})
    if name == "string_count_digits": return (sum("0" <= ch <= "9" for ch in s), {})
    if name == "string_count_hash": return (s.count("#"), {})
    if name == "string_count_alnum": return (sum(("A" <= ch <= "Z") or ("a" <= ch <= "z") or ("0" <= ch <= "9") for ch in s), {})
    if name == "string_count_lowercase": return (sum("a" <= ch <= "z" for ch in s), {})
    if name == "string_count_not_char": return (sum(ch != x["c"] for ch in s), {})
    if name == "string_count_punctuation": return (sum(ch in ".,!?" for ch in s), {})
    if name == "string_count_spaces": return (s.count(" "), {})
    if name == "string_count_uppercase": return (sum("A" <= ch <= "Z" for ch in s), {})
    if name == "string_count_vowels": return (sum(ch in "aeiouAEIOU" for ch in s), {})
    if name == "string_count_words_simple":
        in_word = False; count = 0
        for ch in s:
            if ch == " ": in_word = False
            elif not in_word: count += 1; in_word = True
        return (count, {})
    if name == "string_ends_with_char": return (int(bool(s) and s[-1] == x["c"]), {})
    if name == "string_equal": return (int(x["a"] == x["b"]), {})
    if name == "string_fill_char": return (None, {"s": x["c"] * x["n"]})
    if name == "string_find_char": return (s.find(x["c"]), {})
    if name == "string_find_last_char": return (s.rfind(x["c"]), {})
    if name == "string_first_char": return (s[0], {})
    if name == "string_has_double_char": return (int(any(s[i] == s[i - 1] for i in range(1, len(s)))), {})
    if name == "string_has_digit": return (int(any("0" <= ch <= "9" for ch in s)), {})
    if name == "string_is_empty": return (int(s == ""), {})
    if name == "string_is_palindrome": return (int(s[: x["n"]] == s[: x["n"]][::-1]), {})
    if name == "string_last_char": return (s[-1], {})
    if name == "string_length": return (len(s), {})
    if name == "string_remove_char_to_output":
        out = "".join(ch for ch in s if ch != x["c"])
        return (len(out), {"out": out})
    if name == "string_replace_char": return (None, {"s": s.replace(x["old_c"], x["new_c"])})
    if name == "string_replace_spaces_underscore": return (None, {"s": s.replace(" ", "_")})
    if name == "string_reverse_copy": return (None, {"dst": x["src"][: x["n"]][::-1]})
    if name == "string_set_a": return (None, {"s": "a" * x["n"]})
    if name in ("string_starts_with", "string_starts_with_char"): return (int(bool(s) and s[0] == x["c"]), {})
    if name == "string_to_lower_ascii": return (None, {"s": "".join(chr(ord(ch) + 32) if "A" <= ch <= "Z" else ch for ch in s)})
    if name == "string_to_upper_ascii": return (None, {"s": "".join(chr(ord(ch) - 32) if "a" <= ch <= "z" else ch for ch in s)})
    if name == "string_trim_last_char": return (None, {"s": s[: max(0, x["n"] - 1)]})
    raise KeyError(name)


def collapse_spaces(s: str) -> str:
    out = []
    in_space = False
    for ch in s:
        if ch == " ":
            if not in_space:
                out.append(ch)
            in_space = True
        else:
            out.append(ch)
            in_space = False
    return "".join(out)


BASE_CASES = {
    "abs_value": [{"x": 0}, {"x": 9}, {"x": -9}],
    "add_two": [{"a": 1, "b": 2}, {"a": -3, "b": 7}, {"a": -5, "b": -6}],
    "arithmetic_series": [{"a": 1, "d": 1, "n": 5}, {"a": 3, "d": 2, "n": 4}, {"a": 10, "d": -1, "n": 3}, {"a": 7, "d": 5, "n": 0}],
    "array_add": [{"n": 3, "a": [1, 2, 3], "b": [4, 5, 6], "out": [0, 0, 0]}, {"n": 2, "a": [-1, 5], "b": [3, -5], "out": [0, 0]}],
    "array_adjacent_diff": [{"n": 4, "a": [2, 5, 1, 6], "out": [0, 0, 0, 0]}, {"n": 1, "a": [7], "out": [0]}],
    "array_all_less_than_k": [{"n": 3, "a": [1, 2, 3], "k": 4}, {"n": 3, "a": [1, 5, 3], "k": 4}],
    "array_all_positive": [{"n": 3, "a": [1, 2, 3]}, {"n": 3, "a": [1, 0, 3]}],
    "array_all_zero": [{"n": 3, "a": [0, 0, 0]}, {"n": 2, "a": [0, 1]}],
    "array_any_equal_sum": [{"n": 3, "a": [2, 5, 9], "x": 2, "y": 3}, {"n": 3, "a": [1, 2, 3], "x": 4, "y": 5}],
    "array_any_negative": [{"n": 3, "a": [1, -2, 3]}, {"n": 2, "a": [0, 4]}],
    "array_any_zero": [{"n": 0, "a": []}, {"n": 3, "a": [1, 0, 2]}, {"n": 3, "a": [1, 2, 3]}, {"n": 2, "a": [0, 0]}],
    "array_clamp_nonnegative": [{"n": 4, "a": [-2, 0, 3, -1]}, {"n": 2, "a": [5, 6]}],
    "array_contains": [{"n": 4, "a": [1, 3, 5, 7], "k": 5}, {"n": 4, "a": [1, 3, 5, 7], "k": 2}],
    "array_copy_positive": [{"n": 4, "a": [-1, 2, 0, 3], "out": [0, 0, 0, 0]}],
    "array_count_distinct_sorted": [{"n": 6, "a": [1, 1, 2, 2, 2, 5]}, {"n": 1, "a": [9]}],
    "array_count_even": [{"n": 5, "a": [1, 2, 4, 5, 6]}, {"n": 3, "a": [1, 3, 5]}],
    "array_count_greater_than_k": [{"n": 4, "a": [1, 5, 7, 2], "k": 3}, {"n": 3, "a": [1, 2, 3], "k": 9}],
    "array_count_increasing_steps": [{"n": 5, "a": [1, 2, 2, 5, 4]}, {"n": 3, "a": [3, 2, 1]}],
    "array_count_negative": [{"n": 0, "a": []}, {"n": 5, "a": [-1, 0, 2, -3, 4]}, {"n": 3, "a": [1, 2, 3]}, {"n": 2, "a": [-5, -6]}],
    "array_count_nonzero": [{"n": 0, "a": []}, {"n": 5, "a": [0, 1, -2, 0, 3]}, {"n": 3, "a": [0, 0, 0]}, {"n": 2, "a": [-1, 1]}],
    "array_count_odd": [{"n": 0, "a": []}, {"n": 5, "a": [1, 2, 3, 4, 5]}, {"n": 4, "a": [-1, -2, 0, 7]}, {"n": 3, "a": [2, 4, 6]}],
    "array_count_between": [{"n": 0, "a": [], "lo": 1, "hi": 3}, {"n": 5, "a": [1, 2, 3, 4, 5], "lo": 2, "hi": 4}, {"n": 4, "a": [-3, -1, 0, 2], "lo": -1, "hi": 0}, {"n": 3, "a": [7, 8, 9], "lo": 1, "hi": 6}],
    "array_count_transitions": [{"n": 5, "a": [1, 1, 2, 2, 3]}, {"n": 3, "a": [4, 4, 4]}],
    "array_count_zero": [{"n": 5, "a": [0, 1, 0, 2, 0]}, {"n": 2, "a": [1, 2]}],
    "array_equal": [{"n": 3, "a": [1, 2, 3], "b": [1, 2, 3]}, {"n": 3, "a": [1, 2, 3], "b": [1, 2, 4]}],
    "array_all_even": [{"n": 0, "a": []}, {"n": 4, "a": [2, 4, 0, -6]}, {"n": 3, "a": [2, 3, 4]}, {"n": 2, "a": [-1, -3]}],
    "array_sum_abs": [{"n": 0, "a": []}, {"n": 4, "a": [-1, 2, -3, 0]}, {"n": 3, "a": [5, 6, 7]}, {"n": 2, "a": [-10, -20]}],
    "array_fill_value": [{"n": 0, "k": 5, "a": []}, {"n": 4, "k": 7, "a": [0, 1, 2, 3]}, {"n": 3, "k": -2, "a": [5, 5, 5]}],
    "array_copy_even": [{"n": 0, "a": [], "out": []}, {"n": 5, "a": [1, 2, 3, 4, 0], "out": [9, 9, 9, 9, 9]}, {"n": 3, "a": [-2, -1, 6], "out": [0, 0, 0]}],
    "array_find_last_equal": [{"n": 5, "a": [1, 2, 3, 2, 1], "k": 2}, {"n": 3, "a": [1, 2, 3], "k": 9}],
    "array_first": [{"n": 3, "a": [8, 2, 3]}],
    "array_first_negative": [{"n": 4, "a": [1, 0, -2, -3]}, {"n": 2, "a": [1, 2]}],
    "array_first_peak": [{"n": 5, "a": [1, 3, 2, 4, 1]}, {"n": 4, "a": [1, 2, 3, 4]}],
    "array_has_adjacent_equal": [{"n": 4, "a": [1, 2, 2, 3]}, {"n": 3, "a": [1, 2, 3]}],
    "array_increment": [{"n": 3, "a": [1, -1, 0]}],
    "array_init": [{"n": 4, "a": [9, 9, 9, 9]}],
    "array_index_of_min": [{"n": 4, "a": [3, 1, 2, 1]}, {"n": 1, "a": [7]}, {"n": 3, "a": [-1, -5, -3]}, {"n": 4, "a": [0, 0, 1, 2]}],
    "array_index_of_max": [{"n": 4, "a": [3, 7, 2, 7]}, {"n": 1, "a": [7]}, {"n": 3, "a": [-1, -5, -3]}, {"n": 4, "a": [0, 0, -1, -2]}],
    "array_intersection_count_sorted": [{"n": 4, "a": [1, 2, 4, 5], "m": 4, "b": [2, 3, 4, 6]}, {"n": 2, "a": [1, 2], "m": 2, "b": [3, 4]}],
    "array_is_strictly_increasing": [{"n": 4, "a": [1, 2, 3, 4]}, {"n": 3, "a": [1, 1, 2]}],
    "array_last": [{"n": 3, "a": [1, 2, 9]}],
    "array_last_positive": [{"n": 4, "a": [-1, 2, 0, 3]}, {"n": 2, "a": [-1, 0]}],
    "array_longest_nonnegative_run": [{"n": 6, "a": [1, 0, -1, 2, 3, 4]}, {"n": 3, "a": [-1, -2, -3]}],
    "array_max": [{"n": 4, "a": [2, -1, 7, 3]}, {"n": 3, "a": [-5, -2, -9]}],
    "array_min": [{"n": 4, "a": [2, -1, 7, 3]}, {"n": 3, "a": [-5, -2, -9]}],
    "array_move_zeroes_to_end": [{"n": 5, "a": [0, 1, 0, 2, 3]}, {"n": 3, "a": [0, 0, 1]}],
    "array_none_zero": [{"n": 0, "a": []}, {"n": 3, "a": [1, 2, 3]}, {"n": 3, "a": [1, 0, 2]}, {"n": 2, "a": [-1, -2]}],
    "array_negate": [{"n": 3, "a": [1, -2, 0], "out": [0, 0, 0]}],
    "array_pairwise_sum": [{"n": 3, "a": [1, 2, 3], "b": [4, -2, 0], "out": [0, 0, 0]}],
    "array_prefix_max": [{"n": 5, "a": [1, 3, 2, 5, 4], "out": [0, 0, 0, 0, 0]}],
    "array_product_small": [{"n": 0, "a": []}, {"n": 3, "a": [2, 3, 4]}, {"n": 3, "a": [-1, 2, -3]}, {"n": 4, "a": [1, 0, 5, 6]}],
    "array_remove_value_to_output": [{"n": 5, "a": [1, 2, 3, 2, 4], "k": 2, "out": [0, 0, 0, 0, 0]}],
    "array_replace_k": [{"n": 4, "a": [1, 2, 2, 3], "old_k": 2, "new_k": 9}],
    "array_replace_negative_zero": [{"n": 4, "a": [-1, 2, -3, 0]}],
    "array_reverse_in_place": [{"n": 4, "a": [1, 2, 3, 4]}],
    "array_scale": [{"n": 3, "a": [1, -2, 3], "k": 3, "out": [0, 0, 0]}],
    "array_second_largest": [{"n": 4, "a": [1, 7, 3, 5]}, {"n": 3, "a": [-1, -5, -3]}],
    "array_sign": [{"n": 4, "a": [-2, 0, 5, -1], "out": [0, 0, 0, 0]}],
    "array_sum": [{"n": 3, "a": [1, 2, 3]}, {"n": 4, "a": [2, -1, 7, 3]}],
    "array_sum_even_indices": [{"n": 5, "a": [1, 2, 3, 4, 5]}, {"n": 2, "a": [10, 20]}],
    "array_sum_nonnegative": [{"n": 0, "a": []}, {"n": 5, "a": [1, -2, 0, 3, -4]}, {"n": 3, "a": [-1, -2, -3]}, {"n": 3, "a": [4, 5, 6]}],
    "array_sum_positive": [{"n": 0, "a": []}, {"n": 5, "a": [1, -2, 3, 0, 4]}, {"n": 3, "a": [-1, 0, -5]}, {"n": 2, "a": [7, 8]}],
    "array_swap_ends": [{"n": 4, "a": [1, 2, 3, 4]}, {"n": 1, "a": [9]}],
    "binary_search": [{"n": 5, "a": [1, 3, 5, 7, 9], "target": 7}, {"n": 5, "a": [1, 3, 5, 7, 9], "target": 4}],
    "binary_search_first": [{"n": 6, "a": [1, 2, 2, 2, 3, 4], "target": 2}, {"n": 3, "a": [1, 2, 3], "target": 9}],
    "binary_search_last": [{"n": 6, "a": [1, 2, 2, 2, 3, 4], "target": 2}, {"n": 3, "a": [1, 2, 3], "target": 9}],
    "bubble_sort": [{"n": 5, "a": [5, 1, 4, 2, 3]}],
    "climb_stairs": [{"n": 0}, {"n": 4}, {"n": 6}],
    "copy_array": [{"n": 3, "src": [7, 8, 9], "dst": [0, 0, 0]}],
    "count_digits": [{"n": 0}, {"n": 7}, {"n": 1000}],
    "count_divisors": [{"n": 1}, {"n": 6}, {"n": 12}],
    "count_equal_to_k": [{"n": 5, "a": [1, 2, 2, 3, 2], "k": 2}, {"n": 3, "a": [1, 2, 3], "k": 9}],
    "count_multiples": [{"n": 10, "k": 3}, {"n": 5, "k": 2}],
    "count_positive": [{"n": 4, "a": [-1, 2, 0, 3]}, {"n": 2, "a": [-1, 0]}],
    "count_set_bits": [{"n": 0}, {"n": 1}, {"n": 7}, {"n": 8}, {"n": 255}],
    "digit_sum": [{"n": 0}, {"n": 123}, {"n": 999}],
    "digit_product": [{"n": 0}, {"n": 7}, {"n": 123}, {"n": 105}, {"n": 999}],
    "double_nonnegative": [{"n": 0}, {"n": 1}, {"n": 7}, {"n": 100}, {"n": 12345}],
    "factorial": [{"n": 0}, {"n": 5}, {"n": 6}],
    "fibonacci": [{"n": 0}, {"n": 2}, {"n": 10}],
    "fibonacci_mod": [{"n": 10, "mod": 7}, {"n": 8, "mod": 5}],
    "find_first_equal": [{"n": 5, "a": [1, 2, 3, 2, 1], "k": 2}, {"n": 3, "a": [1, 2, 3], "k": 9}],
    "gcd_iterative": [{"a": 12, "b": 18}, {"a": 17, "b": 13}],
    "house_robber": [{"n": 4, "a": [1, 2, 3, 1]}, {"n": 5, "a": [2, 7, 9, 3, 1]}],
    "insertion_sort": [{"n": 5, "a": [5, 2, 4, 1, 3]}],
    "is_multiple": [{"a": 10, "b": 5}, {"a": 10, "b": 3}],
    "is_between_inclusive": [{"x": 5, "lo": 1, "hi": 9}, {"x": 1, "lo": 1, "hi": 9}, {"x": 9, "lo": 1, "hi": 9}, {"x": 0, "lo": 1, "hi": 9}, {"x": 10, "lo": 1, "hi": 9}],
    "is_prime_simple": [{"n": 2}, {"n": 17}, {"n": 18}],
    "is_sorted_nondecreasing": [{"n": 4, "a": [1, 2, 2, 3]}, {"n": 3, "a": [1, 3, 2]}],
    "last_digit": [{"n": 0}, {"n": 7}, {"n": 123}, {"n": 1000}, {"n": 999}],
    "lcm_simple": [{"a": 4, "b": 6}, {"a": 7, "b": 5}],
    "longest_increasing_run": [{"n": 6, "a": [1, 2, 1, 2, 3, 0]}, {"n": 3, "a": [3, 2, 1]}],
    "lower_bound": [{"n": 5, "a": [1, 2, 4, 4, 8], "target": 4}, {"n": 5, "a": [1, 2, 4, 4, 8], "target": 5}],
    "majority_candidate": [{"n": 7, "a": [2, 2, 1, 2, 3, 2, 2]}, {"n": 3, "a": [1, 2, 3]}],
    "max_abs_two": [{"a": 3, "b": -5}, {"a": -8, "b": 2}, {"a": -4, "b": 4}, {"a": 0, "b": 0}],
    "max_of_three": [{"a": 1, "b": 2, "c": 3}, {"a": -1, "b": -2, "c": -3}],
    "max_of_two": [{"a": 1, "b": 2}, {"a": -1, "b": -5}],
    "max_subarray_sum": [{"n": 5, "a": [-2, 1, -3, 4, -1]}, {"n": 3, "a": [-5, -2, -9]}],
    "merge_sorted_arrays": [{"n": 3, "a": [1, 3, 5], "m": 3, "b": [2, 4, 6], "out": [0, 0, 0, 0, 0, 0]}],
    "min_cost_two_steps": [{"n": 3, "cost": [10, 15, 20]}, {"n": 4, "cost": [1, 100, 1, 1]}],
    "min_of_three": [{"a": 1, "b": 2, "c": 3}, {"a": -1, "b": -2, "c": -3}],
    "partition_nonnegative": [{"n": 5, "a": [1, -2, 3, -4, 0]}],
    "power_nonnegative": [{"base": 2, "exp": 0}, {"base": 2, "exp": 5}, {"base": 3, "exp": 3}],
    "clamp_int": [{"x": 5, "lo": 0, "hi": 10}, {"x": -1, "lo": 0, "hi": 10}, {"x": 11, "lo": 0, "hi": 10}, {"x": 7, "lo": 7, "hi": 7}],
    "prefix_sum": [{"n": 4, "a": [1, 2, 3, 4], "out": [0, 0, 0, 0]}],
    "remove_duplicates_sorted": [{"n": 6, "a": [1, 1, 2, 2, 3, 3]}],
    "reverse_copy": [{"n": 4, "src": [1, 2, 3, 4], "dst": [0, 0, 0, 0]}],
    "reverse_digits": [{"n": 123}, {"n": 1000}, {"n": 7}],
    "rotate_left_by_one": [{"n": 4, "a": [1, 2, 3, 4]}, {"n": 1, "a": [9]}],
    "selection_sort": [{"n": 5, "a": [5, 1, 4, 2, 3]}],
    "set_zero": [{"n": 3, "a": [1, 2, 3]}],
    "square_nonnegative": [{"n": 0}, {"n": 1}, {"n": 7}, {"n": 100}],
    "string_all_digits": [{"s": "123"}, {"s": "12a"}, {"s": ""}],
    "string_all_lowercase": [{"s": "abc"}, {"s": "abC"}, {"s": ""}],
    "string_all_uppercase": [{"s": ""}, {"s": "ABC"}, {"s": "AB1"}, {"s": "abc"}],
    "string_any_lowercase": [{"s": ""}, {"s": "ABC"}, {"s": "AbC"}, {"s": "123z"}],
    "string_collapse_spaces": [{"s": "a  b   c", "out": cbuf(10)}, {"s": "  a", "out": cbuf(5)}],
    "string_contains_char": [{"s": "abc", "c": "b"}, {"s": "abc", "c": "z"}],
    "string_copy": [{"src": "hello", "dst": cbuf(6)}],
    "string_copy_prefix": [{"k": 3, "src": "hello", "dst": cbuf(6)}, {"k": 0, "src": "abc", "dst": cbuf(4)}],
    "string_count_char": [{"s": "banana", "c": "a"}, {"s": "abc", "c": "z"}],
    "string_count_digits": [{"s": "a1b2c3"}, {"s": "abc"}],
    "string_count_hash": [{"s": ""}, {"s": "a#b#"}, {"s": "plain"}, {"s": "###"}],
    "string_count_alnum": [{"s": ""}, {"s": "abc123"}, {"s": "a_b-9"}, {"s": "!!"}],
    "string_count_lowercase": [{"s": "aBcD"}, {"s": "XYZ"}],
    "string_count_not_char": [{"s": "banana", "c": "a"}, {"s": "aaa", "c": "a"}],
    "string_count_punctuation": [{"s": ""}, {"s": "Hi, Bob!"}, {"s": "a.b?c!"}, {"s": "plain"}],
    "string_count_spaces": [{"s": "a b  c"}, {"s": "abc"}],
    "string_count_uppercase": [{"s": ""}, {"s": "ABC"}, {"s": "AbC123z"}, {"s": "lower"}],
    "string_count_vowels": [{"s": "hello"}, {"s": "xyz"}],
    "string_count_words_simple": [{"s": "a bc  d"}, {"s": "   "}],
    "string_ends_with_char": [{"s": "abc", "c": "c"}, {"s": "abc", "c": "a"}],
    "string_equal": [{"a": "abc", "b": "abc"}, {"a": "abc", "b": "abd"}],
    "string_fill_char": [{"n": 4, "c": "x", "s": cbuf(5)}],
    "string_find_char": [{"s": "abcabc", "c": "b"}, {"s": "abc", "c": "z"}],
    "string_find_last_char": [{"s": "banana", "c": "a"}, {"s": "abc", "c": "z"}, {"s": "", "c": "x"}, {"s": "aaaa", "c": "a"}],
    "string_first_char": [{"s": "abc"}, {"s": "z"}],
    "string_has_double_char": [{"s": "book"}, {"s": "abc"}],
    "string_has_digit": [{"s": ""}, {"s": "abc"}, {"s": "a1b"}, {"s": "007"}],
    "string_is_empty": [{"s": ""}, {"s": "a"}],
    "string_is_palindrome": [{"n": 5, "s": "level"}, {"n": 4, "s": "test"}],
    "string_last_char": [{"s": "abc"}, {"s": "z"}],
    "string_length": [{"s": ""}, {"s": "hello"}],
    "string_remove_char_to_output": [{"s": "banana", "out": cbuf(7), "c": "a"}, {"s": "abc", "out": cbuf(4), "c": "z"}],
    "string_replace_char": [{"s": "banana", "old_c": "a", "new_c": "o"}],
    "string_replace_spaces_underscore": [{"s": ""}, {"s": "a b c"}, {"s": "nospace"}, {"s": "  lead"}],
    "string_reverse_copy": [{"n": 5, "src": "hello", "dst": cbuf(6)}],
    "string_set_a": [{"n": 4, "s": cbuf(5)}],
    "string_starts_with": [{"s": "abc", "c": "a"}, {"s": "abc", "c": "b"}],
    "string_starts_with_char": [{"s": "abc", "c": "a"}, {"s": "abc", "c": "b"}],
    "string_to_lower_ascii": [{"s": "AbC1"}],
    "string_to_upper_ascii": [{"s": "aBc1"}],
    "string_trim_last_char": [{"n": 5, "s": "hello"}, {"n": 1, "s": "x"}],
    "sum_to_n": [{"n": 0}, {"n": 10}, {"n": 100}],
    "sum_squares_to_n": [{"n": 0}, {"n": 1}, {"n": 3}, {"n": 10}],
    "tribonacci": [{"n": 0}, {"n": 4}, {"n": 6}],
    "two_sum_sorted": [{"n": 5, "a": [1, 2, 4, 6, 9], "target": 10}, {"n": 3, "a": [1, 2, 3], "target": 9}],
    "upper_bound": [{"n": 5, "a": [1, 2, 4, 4, 8], "target": 4}, {"n": 5, "a": [1, 2, 4, 4, 8], "target": 5}],
    "ways_to_reach": [{"n": 0}, {"n": 4}, {"n": 6}],
}

EXTRA_CASES = {
    "abs_value": [{"x": -1}, {"x": 12345}],
    "add_two": [{"a": 0, "b": 0}, {"a": 100, "b": -40}],
    "array_add": [{"n": 0, "a": [], "b": [], "out": []}, {"n": 4, "a": [0, -2, 8, 1], "b": [5, 2, -3, 9], "out": [0, 0, 0, 0]}],
    "array_adjacent_diff": [{"n": 5, "a": [10, 7, 7, 1, -2], "out": [0, 0, 0, 0, 0]}],
    "array_all_less_than_k": [{"n": 0, "a": [], "k": 1}, {"n": 3, "a": [-5, -1, 0], "k": 0}],
    "array_all_positive": [{"n": 0, "a": []}, {"n": 1, "a": [-1]}],
    "array_all_zero": [{"n": 0, "a": []}, {"n": 1, "a": [0]}],
    "array_any_negative": [{"n": 0, "a": []}, {"n": 1, "a": [-1]}],
    "array_contains": [{"n": 0, "a": [], "k": 1}, {"n": 3, "a": [5, 5, 5], "k": 5}],
    "array_copy_positive": [{"n": 0, "a": [], "out": []}, {"n": 3, "a": [4, 5, 6], "out": [0, 0, 0]}],
    "array_count_distinct_sorted": [{"n": 0, "a": []}, {"n": 5, "a": [-2, -1, 0, 1, 2]}],
    "array_count_even": [{"n": 0, "a": []}, {"n": 4, "a": [-2, -1, 0, 1]}],
    "array_count_zero": [{"n": 0, "a": []}, {"n": 4, "a": [0, 0, 0, 0]}],
    "array_equal": [{"n": 0, "a": [], "b": []}, {"n": 1, "a": [7], "b": [7]}],
    "array_increment": [{"n": 0, "a": []}, {"n": 4, "a": [-2, -1, 0, 1]}],
    "array_init": [{"n": 0, "a": []}, {"n": 2, "a": [-1, 5]}],
    "array_max": [{"n": 1, "a": [42]}, {"n": 5, "a": [0, 0, -1, 3, 3]}],
    "array_min": [{"n": 1, "a": [42]}, {"n": 5, "a": [0, 0, -1, 3, 3]}],
    "array_move_zeroes_to_end": [{"n": 0, "a": []}, {"n": 4, "a": [1, 2, 3, 4]}],
    "array_reverse_in_place": [{"n": 0, "a": []}, {"n": 5, "a": [1, 2, 3, 4, 5]}],
    "binary_search": [{"n": 5, "a": [1, 3, 5, 7, 9], "target": 1}, {"n": 5, "a": [1, 3, 5, 7, 9], "target": 9}],
    "binary_search_first": [{"n": 5, "a": [1, 1, 1, 2, 3], "target": 1}],
    "binary_search_last": [{"n": 5, "a": [1, 2, 3, 3, 3], "target": 3}],
    "bubble_sort": [{"n": 0, "a": []}, {"n": 4, "a": [1, 1, -1, 0]}],
    "count_digits": [{"n": 10}, {"n": 100000}],
    "count_divisors": [{"n": 7}, {"n": 16}],
    "factorial": [{"n": 1}, {"n": 4}],
    "fibonacci": [{"n": 1}, {"n": 7}],
    "gcd_iterative": [{"a": 100, "b": 25}, {"a": 14, "b": 15}],
    "insertion_sort": [{"n": 0, "a": []}, {"n": 4, "a": [1, 1, -1, 0]}],
    "is_prime_simple": [{"n": 1}, {"n": 19}, {"n": 49}],
    "partition_nonnegative": [{"n": 0, "a": []}, {"n": 3, "a": [-1, -2, -3]}, {"n": 3, "a": [0, 1, 2]}],
    "selection_sort": [{"n": 0, "a": []}, {"n": 4, "a": [1, 1, -1, 0]}],
    "string_length": [{"s": "a"}, {"s": "abcdef"}],
    "string_count_digits": [{"s": ""}, {"s": "0123456789"}],
    "string_equal": [{"a": "", "b": ""}, {"a": "a", "b": ""}],
    "string_is_palindrome": [{"n": 0, "s": ""}, {"n": 1, "s": "x"}, {"n": 6, "s": "abccba"}],
    "sum_to_n": [{"n": 1}, {"n": 50}],
    "two_sum_sorted": [{"n": 4, "a": [1, 2, 3, 4], "target": 8}, {"n": 4, "a": [-3, -1, 2, 6], "target": 1}],
}

for _name, _cases in EXTRA_CASES.items():
    BASE_CASES[_name].extend(_cases)


def top_up_cases() -> None:
    """Keep every problem near ten shared tests.

    The hand-written suites above contain the meaningful edge cases.  For
    problems that still have fewer than the target, repeat valid inputs in a
    stable order so every generated JSON file has the same test budget and the
    validator exercises every language harness uniformly.
    """
    for name, items in BASE_CASES.items():
        original = [deepcopy(item) for item in items]
        i = 0
        while len(items) < TARGET_CASES_PER_PROBLEM:
            items.append(deepcopy(original[i % len(original)]))
            i += 1


top_up_cases()


def build_case(name: str, idx: int, inp: dict) -> dict:
    expected, mutations = reference(name, inp)
    case = {"kind": "positive" if idx == 0 else "negative" if idx == len(BASE_CASES[name]) - 1 else "positive", "input": inp}
    if expected is not None:
        case["expected"] = expected
    if mutations:
        case["mutations"] = mutations
    return case


def write(name: str) -> None:
    return_type, params = SPECS[name]
    tests = [build_case(name, i, x) for i, x in enumerate(BASE_CASES[name])]
    spec = {"name": name, "function": FUNCTION_OVERRIDES.get(name, name), "return_type": return_type, "params": params, "tests": tests}
    (TEST_DIR / f"{name}.json").write_text(json.dumps(spec, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def main() -> None:
    missing = sorted(set(SPECS) ^ set(BASE_CASES))
    if missing:
        raise SystemExit(f"spec/test mismatch: {missing}")
    shutil.rmtree(TEST_DIR, ignore_errors=True)
    TEST_DIR.mkdir(parents=True, exist_ok=True)
    for name in sorted(SPECS):
        write(name)
    print(f"generated {len(list(TEST_DIR.glob('*.json')))} shared test files in {TEST_DIR}")


if __name__ == "__main__":
    main()

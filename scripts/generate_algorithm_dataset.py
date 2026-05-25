#!/usr/bin/env python3
"""Generate parallel C/Java/Rust markdown algorithm examples.

The first batch is derived from the local CAV raw tasks.  Each language gets the
same problem text and a language-specific reference implementation.
"""

from __future__ import annotations

import re
import shutil
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
CAV_RAW = Path("/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/raw")
JAVA_RAW = REPO_ROOT / "raw"
OUT_ROOT = REPO_ROOT / "datasets" / "internal"

INTERNAL_EXTRA_TASKS = [
    {
        "name": "clamp_int",
        "title": "Clamp Int",
        "problem": "实现一个函数，把整数 `x` 限制在闭区间 `[lo, hi]` 内并返回结果。",
        "requirements": ["`lo <= hi`。", "如果 `x < lo` 返回 `lo`。", "如果 `x > hi` 返回 `hi`。", "否则返回 `x`。"],
        "c": "int clamp_int(int x, int lo, int hi) {\n    if (x < lo) return lo;\n    if (x > hi) return hi;\n    return x;\n}",
        "java": "class ClampInt {\n    public static int clamp_int(int x, int lo, int hi) {\n        if (x < lo) return lo;\n        if (x > hi) return hi;\n        return x;\n    }\n}",
        "rust": "pub fn clamp_int(x: i32, lo: i32, hi: i32) -> i32 {\n    if x < lo { return lo; }\n    if x > hi { return hi; }\n    x\n}",
    },
    {
        "name": "is_between_inclusive",
        "title": "Is Between Inclusive",
        "problem": "实现一个函数，判断整数 `x` 是否位于闭区间 `[lo, hi]` 内。",
        "requirements": ["`lo <= hi`。", "如果 `lo <= x <= hi` 返回 `1`。", "否则返回 `0`。"],
        "c": "int is_between_inclusive(int x, int lo, int hi) {\n    return x >= lo && x <= hi;\n}",
        "java": "class IsBetweenInclusive {\n    public static int is_between_inclusive(int x, int lo, int hi) {\n        return (x >= lo && x <= hi) ? 1 : 0;\n    }\n}",
        "rust": "pub fn is_between_inclusive(x: i32, lo: i32, hi: i32) -> i32 {\n    if x >= lo && x <= hi { 1 } else { 0 }\n}",
    },
    {
        "name": "square_nonnegative",
        "title": "Square Nonnegative",
        "problem": "实现一个函数，返回非负整数 `n` 的平方。",
        "requirements": ["`n >= 0`。", "结果保证在 32 位有符号整数范围内。"],
        "c": "int square_nonnegative(int n) {\n    return n * n;\n}",
        "java": "class SquareNonnegative {\n    public static int square_nonnegative(int n) {\n        return n * n;\n    }\n}",
        "rust": "pub fn square_nonnegative(n: i32) -> i32 {\n    n * n\n}",
    },
    {
        "name": "sum_squares_to_n",
        "title": "Sum Squares To N",
        "problem": "实现一个函数，返回 `1^2 + 2^2 + ... + n^2`。",
        "requirements": ["`n >= 0`。", "`n == 0` 时返回 `0`。", "结果保证在 32 位有符号整数范围内。"],
        "c": "int sum_squares_to_n(int n) {\n    int i = 1;\n    int sum = 0;\n    while (i <= n) {\n        sum += i * i;\n        i++;\n    }\n    return sum;\n}",
        "java": "class SumSquaresToN {\n    public static int sum_squares_to_n(int n) {\n        int i = 1;\n        int sum = 0;\n        while (i <= n) {\n            sum += i * i;\n            i++;\n        }\n        return sum;\n    }\n}",
        "rust": "pub fn sum_squares_to_n(n: i32) -> i32 {\n    let mut i = 1;\n    let mut sum = 0;\n    while i <= n {\n        sum += i * i;\n        i += 1;\n    }\n    sum\n}",
    },
    {
        "name": "count_set_bits",
        "title": "Count Set Bits",
        "problem": "实现一个函数，返回非负整数 `n` 的二进制表示中 `1` 的个数。",
        "requirements": ["`n >= 0`。", "`n == 0` 时返回 `0`。", "只需要处理 32 位非负整数。"],
        "c": "int count_set_bits(int n) {\n    int count = 0;\n    while (n > 0) {\n        if (n % 2 == 1) count++;\n        n /= 2;\n    }\n    return count;\n}",
        "java": "class CountSetBits {\n    public static int count_set_bits(int n) {\n        int count = 0;\n        while (n > 0) {\n            if (n % 2 == 1) count++;\n            n /= 2;\n        }\n        return count;\n    }\n}",
        "rust": "pub fn count_set_bits(mut n: i32) -> i32 {\n    let mut count = 0;\n    while n > 0 {\n        if n % 2 == 1 { count += 1; }\n        n /= 2;\n    }\n    count\n}",
    },
    {
        "name": "digit_product",
        "title": "Digit Product",
        "problem": "实现一个函数，返回非负整数 `n` 的十进制各位数字乘积。",
        "requirements": ["`n >= 0`。", "`n == 0` 时返回 `0`。", "结果保证在 32 位有符号整数范围内。"],
        "c": "int digit_product(int n) {\n    if (n == 0) return 0;\n    int product = 1;\n    while (n > 0) {\n        product *= n % 10;\n        n /= 10;\n    }\n    return product;\n}",
        "java": "class DigitProduct {\n    public static int digit_product(int n) {\n        if (n == 0) return 0;\n        int product = 1;\n        while (n > 0) {\n            product *= n % 10;\n            n /= 10;\n        }\n        return product;\n    }\n}",
        "rust": "pub fn digit_product(mut n: i32) -> i32 {\n    if n == 0 { return 0; }\n    let mut product = 1;\n    while n > 0 {\n        product *= n % 10;\n        n /= 10;\n    }\n    product\n}",
    },
    {
        "name": "max_abs_two",
        "title": "Max Abs Two",
        "problem": "实现一个函数，返回 `a` 和 `b` 中绝对值较大的那个绝对值。",
        "requirements": ["输入和结果都在 32 位有符号整数范围内。", "如果两个绝对值相等，返回该绝对值。"],
        "c": "int max_abs_two(int a, int b) {\n    if (a < 0) a = -a;\n    if (b < 0) b = -b;\n    return a > b ? a : b;\n}",
        "java": "class MaxAbsTwo {\n    public static int max_abs_two(int a, int b) {\n        if (a < 0) a = -a;\n        if (b < 0) b = -b;\n        return a > b ? a : b;\n    }\n}",
        "rust": "pub fn max_abs_two(mut a: i32, mut b: i32) -> i32 {\n    if a < 0 { a = -a; }\n    if b < 0 { b = -b; }\n    if a > b { a } else { b }\n}",
    },
    {
        "name": "arithmetic_series",
        "title": "Arithmetic Series",
        "problem": "实现一个函数，返回等差数列前 `n` 项之和，首项为 `a`，公差为 `d`。",
        "requirements": ["`n >= 0`。", "`n == 0` 时返回 `0`。", "结果保证在 32 位有符号整数范围内。"],
        "c": "int arithmetic_series(int a, int d, int n) {\n    int i = 0;\n    int cur = a;\n    int sum = 0;\n    while (i < n) {\n        sum += cur;\n        cur += d;\n        i++;\n    }\n    return sum;\n}",
        "java": "class ArithmeticSeries {\n    public static int arithmetic_series(int a, int d, int n) {\n        int i = 0;\n        int cur = a;\n        int sum = 0;\n        while (i < n) {\n            sum += cur;\n            cur += d;\n            i++;\n        }\n        return sum;\n    }\n}",
        "rust": "pub fn arithmetic_series(a: i32, d: i32, n: i32) -> i32 {\n    let mut i = 0;\n    let mut cur = a;\n    let mut sum = 0;\n    while i < n {\n        sum += cur;\n        cur += d;\n        i += 1;\n    }\n    sum\n}",
    },
    {
        "name": "array_count_odd",
        "title": "Array Count Odd",
        "problem": "实现一个函数，返回长度为 `n` 的整数数组中奇数元素的个数。",
        "requirements": ["`n >= 0`。", "数组长度至少为 `n`。", "负奇数也应被计入。"],
        "c": "int array_count_odd(int n, int *a) {\n    int i = 0;\n    int count = 0;\n    while (i < n) {\n        if (a[i] % 2 != 0) count++;\n        i++;\n    }\n    return count;\n}",
        "java": "class ArrayCountOdd {\n    public static int array_count_odd(int n, int[] a) {\n        int i = 0;\n        int count = 0;\n        while (i < n) {\n            if (a[i] % 2 != 0) count++;\n            i++;\n        }\n        return count;\n    }\n}",
        "rust": "pub fn array_count_odd(n: i32, a: &[i32]) -> i32 {\n    let mut i = 0;\n    let mut count = 0;\n    while i < n {\n        if a[i as usize] % 2 != 0 { count += 1; }\n        i += 1;\n    }\n    count\n}",
    },
    {
        "name": "array_all_even",
        "title": "Array All Even",
        "problem": "实现一个函数，判断长度为 `n` 的整数数组是否全部为偶数。",
        "requirements": ["`n >= 0`。", "空数组返回 `1`。", "负偶数也视为偶数。"],
        "c": "int array_all_even(int n, int *a) {\n    int i = 0;\n    while (i < n) {\n        if (a[i] % 2 != 0) return 0;\n        i++;\n    }\n    return 1;\n}",
        "java": "class ArrayAllEven {\n    public static int array_all_even(int n, int[] a) {\n        int i = 0;\n        while (i < n) {\n            if (a[i] % 2 != 0) return 0;\n            i++;\n        }\n        return 1;\n    }\n}",
        "rust": "pub fn array_all_even(n: i32, a: &[i32]) -> i32 {\n    let mut i = 0;\n    while i < n {\n        if a[i as usize] % 2 != 0 { return 0; }\n        i += 1;\n    }\n    1\n}",
    },
    {
        "name": "array_sum_abs",
        "title": "Array Sum Abs",
        "problem": "实现一个函数，返回长度为 `n` 的整数数组中所有元素绝对值之和。",
        "requirements": ["`n >= 0`。", "结果保证在 32 位有符号整数范围内。", "不修改输入数组。"],
        "c": "int array_sum_abs(int n, int *a) {\n    int i = 0;\n    int sum = 0;\n    while (i < n) {\n        int v = a[i];\n        if (v < 0) v = -v;\n        sum += v;\n        i++;\n    }\n    return sum;\n}",
        "java": "class ArraySumAbs {\n    public static int array_sum_abs(int n, int[] a) {\n        int i = 0;\n        int sum = 0;\n        while (i < n) {\n            int v = a[i];\n            if (v < 0) v = -v;\n            sum += v;\n            i++;\n        }\n        return sum;\n    }\n}",
        "rust": "pub fn array_sum_abs(n: i32, a: &[i32]) -> i32 {\n    let mut i = 0;\n    let mut sum = 0;\n    while i < n {\n        let mut v = a[i as usize];\n        if v < 0 { v = -v; }\n        sum += v;\n        i += 1;\n    }\n    sum\n}",
    },
    {
        "name": "array_fill_value",
        "title": "Array Fill Value",
        "problem": "实现一个函数，把数组前 `n` 个位置全部原地写成给定值 `k`。",
        "requirements": ["`n >= 0`。", "数组长度至少为 `n`。", "只修改前 `n` 个元素。"],
        "c": "void array_fill_value(int n, int k, int *a) {\n    int i = 0;\n    while (i < n) {\n        a[i] = k;\n        i++;\n    }\n}",
        "java": "class ArrayFillValue {\n    public static void array_fill_value(int n, int k, int[] a) {\n        int i = 0;\n        while (i < n) {\n            a[i] = k;\n            i++;\n        }\n    }\n}",
        "rust": "pub fn array_fill_value(n: i32, k: i32, a: &mut [i32]) {\n    let mut i = 0;\n    while i < n {\n        a[i as usize] = k;\n        i += 1;\n    }\n}",
    },
    {
        "name": "array_copy_even",
        "title": "Array Copy Even",
        "problem": "实现一个函数，把输入数组中的偶数复制到输出数组同位置，奇数位置写 `0`。",
        "requirements": ["`n >= 0`。", "`a` 和 `out` 长度至少为 `n`。", "不修改输入数组。"],
        "c": "void array_copy_even(int n, int *a, int *out) {\n    int i = 0;\n    while (i < n) {\n        if (a[i] % 2 == 0) out[i] = a[i];\n        else out[i] = 0;\n        i++;\n    }\n}",
        "java": "class ArrayCopyEven {\n    public static void array_copy_even(int n, int[] a, int[] out) {\n        int i = 0;\n        while (i < n) {\n            if (a[i] % 2 == 0) out[i] = a[i];\n            else out[i] = 0;\n            i++;\n        }\n    }\n}",
        "rust": "pub fn array_copy_even(n: i32, a: &[i32], out: &mut [i32]) {\n    let mut i = 0;\n    while i < n {\n        if a[i as usize] % 2 == 0 { out[i as usize] = a[i as usize]; }\n        else { out[i as usize] = 0; }\n        i += 1;\n    }\n}",
    },
    {
        "name": "string_count_uppercase",
        "title": "String Count Uppercase",
        "problem": "实现一个函数，统计 C 风格字符串中 ASCII 大写字母的数量。",
        "requirements": ["输入是以 `\\0` 结尾的字符串。", "只统计 `'A'` 到 `'Z'`。", "空字符串返回 `0`。"],
        "c": "int string_count_uppercase(char *s) {\n    int i = 0;\n    int count = 0;\n    while (s[i] != '\\0') {\n        if (s[i] >= 'A' && s[i] <= 'Z') count++;\n        i++;\n    }\n    return count;\n}",
        "java": "class StringCountUppercase {\n    public static int string_count_uppercase(char[] s) {\n        int i = 0;\n        int count = 0;\n        while (s[i] != '\\0') {\n            if (s[i] >= 'A' && s[i] <= 'Z') count++;\n            i++;\n        }\n        return count;\n    }\n}",
        "rust": "pub fn string_count_uppercase(s: &[u8]) -> i32 {\n    let mut i = 0;\n    let mut count = 0;\n    while s[i as usize] != b'\\0' {\n        if s[i as usize] >= b'A' && s[i as usize] <= b'Z' { count += 1; }\n        i += 1;\n    }\n    count\n}",
    },
    {
        "name": "array_count_between",
        "title": "Array Count Between",
        "problem": "实现一个函数，统计长度为 `n` 的整数数组中位于闭区间 `[lo, hi]` 内的元素个数。",
        "requirements": ["`n >= 0`。", "`lo <= hi`。", "数组长度至少为 `n`。"],
        "c": "int array_count_between(int n, int *a, int lo, int hi) {\n    int i = 0;\n    int count = 0;\n    while (i < n) {\n        if (a[i] >= lo && a[i] <= hi) count++;\n        i++;\n    }\n    return count;\n}",
        "java": "class ArrayCountBetween {\n    public static int array_count_between(int n, int[] a, int lo, int hi) {\n        int i = 0;\n        int count = 0;\n        while (i < n) {\n            if (a[i] >= lo && a[i] <= hi) count++;\n            i++;\n        }\n        return count;\n    }\n}",
        "rust": "pub fn array_count_between(n: i32, a: &[i32], lo: i32, hi: i32) -> i32 {\n    let mut i = 0;\n    let mut count = 0;\n    while i < n {\n        if a[i as usize] >= lo && a[i as usize] <= hi { count += 1; }\n        i += 1;\n    }\n    count\n}",
    },
    {
        "name": "array_index_of_min",
        "title": "Array Index Of Min",
        "problem": "实现一个函数，返回长度为 `n` 的非空整数数组中最小值第一次出现的位置。",
        "requirements": ["`n > 0`。", "数组长度至少为 `n`。", "如果最小值出现多次，返回最小下标。"],
        "c": "int array_index_of_min(int n, int *a) {\n    int idx = 0;\n    int i = 1;\n    while (i < n) {\n        if (a[i] < a[idx]) idx = i;\n        i++;\n    }\n    return idx;\n}",
        "java": "class ArrayIndexOfMin {\n    public static int array_index_of_min(int n, int[] a) {\n        int idx = 0;\n        int i = 1;\n        while (i < n) {\n            if (a[i] < a[idx]) idx = i;\n            i++;\n        }\n        return idx;\n    }\n}",
        "rust": "pub fn array_index_of_min(n: i32, a: &[i32]) -> i32 {\n    let mut idx = 0;\n    let mut i = 1;\n    while i < n {\n        if a[i as usize] < a[idx as usize] { idx = i; }\n        i += 1;\n    }\n    idx\n}",
    },
    {
        "name": "string_count_alnum",
        "title": "String Count Alnum",
        "problem": "实现一个函数，统计 C 风格字符串中 ASCII 字母或数字的数量。",
        "requirements": ["输入是以 `\\0` 结尾的字符串。", "字母包括 `'A'..'Z'` 和 `'a'..'z'`。", "数字包括 `'0'..'9'`。"],
        "c": "int string_count_alnum(char *s) {\n    int i = 0;\n    int count = 0;\n    while (s[i] != '\\0') {\n        char c = s[i];\n        if ((c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9')) count++;\n        i++;\n    }\n    return count;\n}",
        "java": "class StringCountAlnum {\n    public static int string_count_alnum(char[] s) {\n        int i = 0;\n        int count = 0;\n        while (s[i] != '\\0') {\n            char c = s[i];\n            if ((c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9')) count++;\n            i++;\n        }\n        return count;\n    }\n}",
        "rust": "pub fn string_count_alnum(s: &[u8]) -> i32 {\n    let mut i = 0;\n    let mut count = 0;\n    while s[i as usize] != b'\\0' {\n        let c = s[i as usize];\n        if (c >= b'A' && c <= b'Z') || (c >= b'a' && c <= b'z') || (c >= b'0' && c <= b'9') { count += 1; }\n        i += 1;\n    }\n    count\n}",
    },
    {
        "name": "string_find_last_char",
        "title": "String Find Last Char",
        "problem": "实现一个函数，返回字符 `c` 在 C 风格字符串中最后一次出现的位置，不存在则返回 `-1`。",
        "requirements": ["输入是以 `\\0` 结尾的字符串。", "返回从 `0` 开始的下标。", "空字符串返回 `-1`。"],
        "c": "int string_find_last_char(char *s, char c) {\n    int i = 0;\n    int last = -1;\n    while (s[i] != '\\0') {\n        if (s[i] == c) last = i;\n        i++;\n    }\n    return last;\n}",
        "java": "class StringFindLastChar {\n    public static int string_find_last_char(char[] s, char c) {\n        int i = 0;\n        int last = -1;\n        while (s[i] != '\\0') {\n            if (s[i] == c) last = i;\n            i++;\n        }\n        return last;\n    }\n}",
        "rust": "pub fn string_find_last_char(s: &[u8], c: u8) -> i32 {\n    let mut i = 0;\n    let mut last = -1;\n    while s[i as usize] != b'\\0' {\n        if s[i as usize] == c { last = i; }\n        i += 1;\n    }\n    last\n}",
    },
]


def extra_md(task: dict, lang: str) -> str:
    reqs = "\n".join(f"- {item}" for item in task["requirements"])
    return (
        f"# {task['title']}\n\n"
        "## 问题描述\n\n"
        f"{task['problem']}\n\n"
        "约定：\n\n"
        f"{reqs}\n\n"
        "## 参考实现\n\n"
        f"```{lang}\n{task[lang]}\n```\n\n"
        "## 说明\n\n"
        "这是 internal 本地补充的基础单函数算法题。\n"
    )


def more_internal_tasks() -> list[dict]:
    specs = [
        ("array_count_nonzero", "Array Count Nonzero", "实现一个函数，统计长度为 `n` 的整数数组中非零元素个数。", ["`n >= 0`。", "数组长度至少为 `n`。", "正数和负数都算非零。"], "int array_count_nonzero(int n, int *a) {\n    int count = 0;\n    for (int i = 0; i < n; i++) if (a[i] != 0) count++;\n    return count;\n}", "class ArrayCountNonzero {\n    public static int array_count_nonzero(int n, int[] a) {\n        int count = 0;\n        for (int i = 0; i < n; i++) if (a[i] != 0) count++;\n        return count;\n    }\n}", "pub fn array_count_nonzero(n: i32, a: &[i32]) -> i32 {\n    let mut count = 0;\n    let mut i = 0;\n    while i < n { if a[i as usize] != 0 { count += 1; } i += 1; }\n    count\n}"),
        ("array_sum_positive", "Array Sum Positive", "实现一个函数，返回长度为 `n` 的整数数组中所有正数之和。", ["`n >= 0`。", "零和负数不计入。", "结果保证在 32 位有符号整数范围内。"], "int array_sum_positive(int n, int *a) {\n    int sum = 0;\n    for (int i = 0; i < n; i++) if (a[i] > 0) sum += a[i];\n    return sum;\n}", "class ArraySumPositive {\n    public static int array_sum_positive(int n, int[] a) {\n        int sum = 0;\n        for (int i = 0; i < n; i++) if (a[i] > 0) sum += a[i];\n        return sum;\n    }\n}", "pub fn array_sum_positive(n: i32, a: &[i32]) -> i32 {\n    let mut sum = 0;\n    let mut i = 0;\n    while i < n { if a[i as usize] > 0 { sum += a[i as usize]; } i += 1; }\n    sum\n}"),
        ("array_any_zero", "Array Any Zero", "实现一个函数，判断长度为 `n` 的整数数组中是否存在零。", ["`n >= 0`。", "存在零返回 `1`。", "不存在零返回 `0`。"], "int array_any_zero(int n, int *a) {\n    for (int i = 0; i < n; i++) if (a[i] == 0) return 1;\n    return 0;\n}", "class ArrayAnyZero {\n    public static int array_any_zero(int n, int[] a) {\n        for (int i = 0; i < n; i++) if (a[i] == 0) return 1;\n        return 0;\n    }\n}", "pub fn array_any_zero(n: i32, a: &[i32]) -> i32 {\n    let mut i = 0;\n    while i < n { if a[i as usize] == 0 { return 1; } i += 1; }\n    0\n}"),
        ("array_product_small", "Array Product Small", "实现一个函数，返回长度为 `n` 的整数数组所有元素乘积。", ["`n >= 0`。", "空数组乘积返回 `1`。", "结果保证在 32 位有符号整数范围内。"], "int array_product_small(int n, int *a) {\n    int product = 1;\n    for (int i = 0; i < n; i++) product *= a[i];\n    return product;\n}", "class ArrayProductSmall {\n    public static int array_product_small(int n, int[] a) {\n        int product = 1;\n        for (int i = 0; i < n; i++) product *= a[i];\n        return product;\n    }\n}", "pub fn array_product_small(n: i32, a: &[i32]) -> i32 {\n    let mut product = 1;\n    let mut i = 0;\n    while i < n { product *= a[i as usize]; i += 1; }\n    product\n}"),
        ("array_index_of_max", "Array Index Of Max", "实现一个函数，返回长度为 `n` 的非空整数数组中最大值第一次出现的位置。", ["`n > 0`。", "数组长度至少为 `n`。", "如果最大值出现多次，返回最小下标。"], "int array_index_of_max(int n, int *a) {\n    int idx = 0;\n    for (int i = 1; i < n; i++) if (a[i] > a[idx]) idx = i;\n    return idx;\n}", "class ArrayIndexOfMax {\n    public static int array_index_of_max(int n, int[] a) {\n        int idx = 0;\n        for (int i = 1; i < n; i++) if (a[i] > a[idx]) idx = i;\n        return idx;\n    }\n}", "pub fn array_index_of_max(n: i32, a: &[i32]) -> i32 {\n    let mut idx = 0;\n    let mut i = 1;\n    while i < n { if a[i as usize] > a[idx as usize] { idx = i; } i += 1; }\n    idx\n}"),
        ("string_all_uppercase", "String All Uppercase", "实现一个函数，判断 C 风格字符串是否全部由 ASCII 大写字母组成。", ["输入是以 `\\0` 结尾的字符串。", "空字符串返回 `1`。", "非大写字母字符会导致返回 `0`。"], "int string_all_uppercase(char *s) {\n    for (int i = 0; s[i] != '\\0'; i++) if (s[i] < 'A' || s[i] > 'Z') return 0;\n    return 1;\n}", "class StringAllUppercase {\n    public static int string_all_uppercase(char[] s) {\n        for (int i = 0; s[i] != '\\0'; i++) if (s[i] < 'A' || s[i] > 'Z') return 0;\n        return 1;\n    }\n}", "pub fn string_all_uppercase(s: &[u8]) -> i32 {\n    let mut i = 0;\n    while s[i as usize] != b'\\0' { if s[i as usize] < b'A' || s[i as usize] > b'Z' { return 0; } i += 1; }\n    1\n}"),
        ("string_count_punctuation", "String Count Punctuation", "实现一个函数，统计 C 风格字符串中 `.`, `,`, `!`, `?` 四种标点数量。", ["输入是以 `\\0` 结尾的字符串。", "只统计四种指定 ASCII 标点。", "空字符串返回 `0`。"], "int string_count_punctuation(char *s) {\n    int count = 0;\n    for (int i = 0; s[i] != '\\0'; i++) if (s[i] == '.' || s[i] == ',' || s[i] == '!' || s[i] == '?') count++;\n    return count;\n}", "class StringCountPunctuation {\n    public static int string_count_punctuation(char[] s) {\n        int count = 0;\n        for (int i = 0; s[i] != '\\0'; i++) if (s[i] == '.' || s[i] == ',' || s[i] == '!' || s[i] == '?') count++;\n        return count;\n    }\n}", "pub fn string_count_punctuation(s: &[u8]) -> i32 {\n    let mut count = 0;\n    let mut i = 0;\n    while s[i as usize] != b'\\0' { let c = s[i as usize]; if c == b'.' || c == b',' || c == b'!' || c == b'?' { count += 1; } i += 1; }\n    count\n}"),
        ("string_has_digit", "String Has Digit", "实现一个函数，判断 C 风格字符串中是否存在 ASCII 数字。", ["输入是以 `\\0` 结尾的字符串。", "存在 `'0'..'9'` 返回 `1`。", "否则返回 `0`。"], "int string_has_digit(char *s) {\n    for (int i = 0; s[i] != '\\0'; i++) if (s[i] >= '0' && s[i] <= '9') return 1;\n    return 0;\n}", "class StringHasDigit {\n    public static int string_has_digit(char[] s) {\n        for (int i = 0; s[i] != '\\0'; i++) if (s[i] >= '0' && s[i] <= '9') return 1;\n        return 0;\n    }\n}", "pub fn string_has_digit(s: &[u8]) -> i32 {\n    let mut i = 0;\n    while s[i as usize] != b'\\0' { if s[i as usize] >= b'0' && s[i as usize] <= b'9' { return 1; } i += 1; }\n    0\n}"),
        ("string_replace_spaces_underscore", "String Replace Spaces Underscore", "实现一个函数，把 C 风格字符串中的空格原地替换为下划线。", ["输入是以 `\\0` 结尾的可变字符串。", "只替换 ASCII 空格 `' '`。", "字符串长度不变。"], "void string_replace_spaces_underscore(char *s) {\n    for (int i = 0; s[i] != '\\0'; i++) if (s[i] == ' ') s[i] = '_';\n}", "class StringReplaceSpacesUnderscore {\n    public static void string_replace_spaces_underscore(char[] s) {\n        for (int i = 0; s[i] != '\\0'; i++) if (s[i] == ' ') s[i] = '_';\n    }\n}", "pub fn string_replace_spaces_underscore(s: &mut [u8]) {\n    let mut i = 0;\n    while s[i as usize] != b'\\0' { if s[i as usize] == b' ' { s[i as usize] = b'_'; } i += 1; }\n}"),
        ("last_digit", "Last Digit", "实现一个函数，返回非负整数 `n` 的十进制个位数字。", ["`n >= 0`。", "返回值在 `0..9`。", "`n == 0` 时返回 `0`。"], "int last_digit(int n) {\n    return n % 10;\n}", "class LastDigit {\n    public static int last_digit(int n) {\n        return n % 10;\n    }\n}", "pub fn last_digit(n: i32) -> i32 {\n    n % 10\n}"),
        ("double_nonnegative", "Double Nonnegative", "实现一个函数，返回非负整数 `n` 的两倍。", ["`n >= 0`。", "结果保证在 32 位有符号整数范围内。"], "int double_nonnegative(int n) {\n    return n + n;\n}", "class DoubleNonnegative {\n    public static int double_nonnegative(int n) {\n        return n + n;\n    }\n}", "pub fn double_nonnegative(n: i32) -> i32 {\n    n + n\n}"),
        ("array_count_negative", "Array Count Negative", "实现一个函数，统计长度为 `n` 的整数数组中负数元素个数。", ["`n >= 0`。", "数组长度至少为 `n`。", "只统计严格小于零的元素。"], "int array_count_negative(int n, int *a) {\n    int count = 0;\n    for (int i = 0; i < n; i++) if (a[i] < 0) count++;\n    return count;\n}", "class ArrayCountNegative {\n    public static int array_count_negative(int n, int[] a) {\n        int count = 0;\n        for (int i = 0; i < n; i++) if (a[i] < 0) count++;\n        return count;\n    }\n}", "pub fn array_count_negative(n: i32, a: &[i32]) -> i32 {\n    let mut count = 0;\n    let mut i = 0;\n    while i < n { if a[i as usize] < 0 { count += 1; } i += 1; }\n    count\n}"),
        ("array_none_zero", "Array None Zero", "实现一个函数，判断长度为 `n` 的整数数组中是否没有零。", ["`n >= 0`。", "没有零返回 `1`。", "存在零返回 `0`。", "空数组返回 `1`。"], "int array_none_zero(int n, int *a) {\n    for (int i = 0; i < n; i++) if (a[i] == 0) return 0;\n    return 1;\n}", "class ArrayNoneZero {\n    public static int array_none_zero(int n, int[] a) {\n        for (int i = 0; i < n; i++) if (a[i] == 0) return 0;\n        return 1;\n    }\n}", "pub fn array_none_zero(n: i32, a: &[i32]) -> i32 {\n    let mut i = 0;\n    while i < n { if a[i as usize] == 0 { return 0; } i += 1; }\n    1\n}"),
        ("array_sum_nonnegative", "Array Sum Nonnegative", "实现一个函数，返回长度为 `n` 的整数数组中所有非负数之和。", ["`n >= 0`。", "只累加大于等于零的元素。", "结果保证在 32 位有符号整数范围内。"], "int array_sum_nonnegative(int n, int *a) {\n    int sum = 0;\n    for (int i = 0; i < n; i++) if (a[i] >= 0) sum += a[i];\n    return sum;\n}", "class ArraySumNonnegative {\n    public static int array_sum_nonnegative(int n, int[] a) {\n        int sum = 0;\n        for (int i = 0; i < n; i++) if (a[i] >= 0) sum += a[i];\n        return sum;\n    }\n}", "pub fn array_sum_nonnegative(n: i32, a: &[i32]) -> i32 {\n    let mut sum = 0;\n    let mut i = 0;\n    while i < n { if a[i as usize] >= 0 { sum += a[i as usize]; } i += 1; }\n    sum\n}"),
        ("string_any_lowercase", "String Any Lowercase", "实现一个函数，判断 C 风格字符串中是否存在 ASCII 小写字母。", ["输入是以 `\\0` 结尾的字符串。", "存在 `'a'..'z'` 返回 `1`。", "否则返回 `0`。"], "int string_any_lowercase(char *s) {\n    for (int i = 0; s[i] != '\\0'; i++) if (s[i] >= 'a' && s[i] <= 'z') return 1;\n    return 0;\n}", "class StringAnyLowercase {\n    public static int string_any_lowercase(char[] s) {\n        for (int i = 0; s[i] != '\\0'; i++) if (s[i] >= 'a' && s[i] <= 'z') return 1;\n        return 0;\n    }\n}", "pub fn string_any_lowercase(s: &[u8]) -> i32 {\n    let mut i = 0;\n    while s[i as usize] != b'\\0' { if s[i as usize] >= b'a' && s[i as usize] <= b'z' { return 1; } i += 1; }\n    0\n}"),
        ("string_count_hash", "String Count Hash", "实现一个函数，统计 C 风格字符串中 `#` 字符的数量。", ["输入是以 `\\0` 结尾的字符串。", "只统计 ASCII `#`。", "空字符串返回 `0`。"], "int string_count_hash(char *s) {\n    int count = 0;\n    for (int i = 0; s[i] != '\\0'; i++) if (s[i] == '#') count++;\n    return count;\n}", "class StringCountHash {\n    public static int string_count_hash(char[] s) {\n        int count = 0;\n        for (int i = 0; s[i] != '\\0'; i++) if (s[i] == '#') count++;\n        return count;\n    }\n}", "pub fn string_count_hash(s: &[u8]) -> i32 {\n    let mut count = 0;\n    let mut i = 0;\n    while s[i as usize] != b'\\0' { if s[i as usize] == b'#' { count += 1; } i += 1; }\n    count\n}"),
    ]
    return [{"name": n, "title": t, "problem": p, "requirements": r, "c": c, "java": j, "rust": rs} for n, t, p, r, c, j, rs in specs]


def read_code(text: str, lang: str) -> str:
    match = re.search(rf"```{lang}\n(.*?)```", text, re.S)
    if not match:
        raise ValueError(f"missing {lang} code block")
    return match.group(1).strip("\n").replace("\x00", r"\0")


def problem_text(c_text: str) -> tuple[str, str]:
    match = re.search(r"```c\n.*?```", c_text, re.S)
    if not match:
        raise ValueError("missing c code block")
    before = c_text[: match.start()]
    after = c_text[match.end() :]
    before = before.replace("## 正确代码", "## 参考实现")
    after = after.replace("contract", "规格").replace("Contract", "规格")
    return before.rstrip() + "\n\n", after.lstrip()


def write_md(path: Path, before: str, lang: str, code: str, after: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(f"{before}```{lang}\n{code.rstrip()}\n```\n\n{after}", encoding="utf-8")


def parse_signature(code: str) -> tuple[str, str, str]:
    first = code.splitlines()[0]
    match = re.match(r"^(int|void|char)\s+([A-Za-z_]\w*)\s*\(([^)]*)\)\s*\{\s*$", first)
    if not match:
        raise ValueError(f"unsupported signature: {first}")
    return match.group(1), match.group(2), match.group(3)


def split_params(params: str) -> list[tuple[str, str, bool]]:
    params = params.strip()
    if not params or params == "void":
        return []
    out: list[tuple[str, str, bool]] = []
    for part in [p.strip() for p in params.split(",")]:
        match = re.match(r"^(int|char)\s*(\*)?\s*([A-Za-z_]\w*)$", part)
        if not match:
            raise ValueError(f"unsupported parameter: {part}")
        c_type, pointer, name = match.groups()
        out.append((c_type, name, bool(pointer)))
    return out


def mutable_array_names(code: str, params: list[tuple[str, str, bool]]) -> set[str]:
    names = {name for _, name, pointer in params if pointer}
    mutable: set[str] = set()
    for name in names:
        if re.search(rf"\b{name}\s*\[[^\]]+\]\s*=(?!=)", code):
            mutable.add(name)
    return mutable


def rust_name(name: str) -> str:
    return "r#mod" if name == "mod" else name


def rust_signature(c_ret: str, name: str, params: list[tuple[str, str, bool]], mutable: set[str], mutable_scalars: set[str]) -> tuple[str, set[str], bool]:
    array_names = {name for _, name, pointer in params if pointer}
    has_char = any(c_type == "char" for c_type, _, _ in params) or c_ret == "char"
    rendered: list[str] = []
    for c_type, param_name, pointer in params:
        if pointer:
            base = "u8" if c_type == "char" else "i32"
            mut = "mut " if param_name in mutable else ""
            rendered.append(f"{rust_name(param_name)}: &{mut}[{base}]")
        else:
            mut = "mut " if param_name in mutable_scalars else ""
            rendered.append(f"{mut}{rust_name(param_name)}: {'u8' if c_type == 'char' else 'i32'}")
    ret = {"int": "i32", "char": "u8", "void": "()"}[c_ret]
    suffix = "" if ret == "()" else f" -> {ret}"
    return f"pub fn {name}({', '.join(rendered)}){suffix} {{", array_names, has_char


def convert_char_literals(line: str) -> str:
    return re.sub(r"'(\\0|[^'\\]|\\.)'", r"b'\1'", line)


def index_arrays(line: str, array_names: set[str]) -> str:
    for name in sorted(array_names, key=len, reverse=True):
        line = re.sub(rf"\b{name}\[([^\]]+)\]", lambda m: f"{name}[({m.group(1).strip()}) as usize]", line)
    return line


def strip_outer_parens(expr: str) -> str:
    expr = expr.strip()
    if expr.startswith("(") and expr.endswith(")"):
        return expr[1:-1].strip()
    return expr


def merge_multiline_conditions(lines: list[str]) -> list[str]:
    merged: list[str] = []
    i = 0
    while i < len(lines):
        stripped = lines[i].strip()
        if (
            (stripped.startswith("if (") or stripped.startswith("while ("))
            and "{" not in stripped
            and not stripped.endswith(";")
        ):
            indent = lines[i][: len(lines[i]) - len(lines[i].lstrip())]
            parts = [stripped]
            i += 1
            while i < len(lines):
                parts.append(lines[i].strip())
                if "{" in lines[i]:
                    break
                i += 1
            merged.append(indent + " ".join(parts))
        else:
            merged.append(lines[i])
        i += 1
    return merged


def convert_decl(stripped: str) -> list[str] | None:
    code, sep, comment = stripped.partition("//")
    code = code.strip()
    comment = (sep + comment) if sep else ""
    if code.startswith("int ") and code.endswith(";"):
        rest = code[4:-1].strip()
        if "," in rest and "=" not in rest:
            return [f"let mut {name.strip()}: i32;" for name in rest.split(",")]
        if "=" in rest:
            name, expr = [x.strip() for x in rest.split("=", 1)]
            return [f"let mut {name}: i32 = {expr};{(' ' + comment) if comment else ''}"]
        return [f"let mut {rest}: i32;{(' ' + comment) if comment else ''}"]
    if code.startswith("char ") and code.endswith(";"):
        rest = code[5:-1].strip()
        if "=" in rest:
            name, expr = [x.strip() for x in rest.split("=", 1)]
            return [f"let mut {name}: u8 = {expr};{(' ' + comment) if comment else ''}"]
        return [f"let mut {rest}: u8;{(' ' + comment) if comment else ''}"]
    return None


def convert_statement(line: str, array_names: set[str], has_char: bool) -> tuple[list[str], str | None, bool]:
    indent = line[: len(line) - len(line.lstrip())]
    stripped = line.strip()
    if not stripped:
        return [""], None, False
    if has_char:
        stripped = convert_char_literals(stripped)
    stripped = index_arrays(stripped, array_names)
    stripped = re.sub(r"!\s*([A-Za-z_]\w*)", r"\1 == 0", stripped)

    for_match = re.match(r"^for\s*\((.*?);(.*?);(.*?)\)\s*\{\s*$", stripped)
    if for_match:
        init, cond, inc = [x.strip() for x in for_match.groups()]
        init = init.replace("int ", "let mut ")
        if init.startswith("let mut ") and ":" not in init:
            init = re.sub(r"^let mut ([A-Za-z_]\w*) =", r"let mut \1: i32 =", init)
        inc = re.sub(r"^([A-Za-z_]\w*)\+\+$", r"\1 += 1", inc)
        inc = re.sub(r"^\+\+([A-Za-z_]\w*)$", r"\1 += 1", inc)
        inc = re.sub(r"^([A-Za-z_]\w*)--$", r"\1 -= 1", inc)
        inc = re.sub(r"^--([A-Za-z_]\w*)$", r"\1 -= 1", inc)
        return [f"{indent}{init};", f"{indent}while {cond} {{"], inc + ";", True

    decl = convert_decl(stripped)
    if decl is not None:
        return [indent + item for item in decl], None, False

    if stripped.startswith("if "):
        single = re.match(r"^if\s*\((.*?)\)\s*(return\s+.*;)$", stripped)
        if single:
            return [f"{indent}if {single.group(1).strip()} {{ {single.group(2)} }}"], None, False
        cond = stripped[3:].strip()
        cond = cond[:-1].strip() if cond.endswith("{") else cond
        return [f"{indent}if {strip_outer_parens(cond)} {{"], None, True
    if stripped.startswith("while "):
        cond = stripped[6:].strip()
        cond = cond[:-1].strip() if cond.endswith("{") else cond
        return [f"{indent}while {strip_outer_parens(cond)} {{"], None, True

    stripped = re.sub(r"^([A-Za-z_]\w*)\+\+;$", r"\1 += 1;", stripped)
    stripped = re.sub(r"^([A-Za-z_]\w*)--;$", r"\1 -= 1;", stripped)
    stripped = re.sub(r"^\+\+([A-Za-z_]\w*);$", r"\1 += 1;", stripped)
    stripped = re.sub(r"^--([A-Za-z_]\w*);$", r"\1 -= 1;", stripped)
    opens = stripped.endswith("{") and not stripped.startswith("}")
    return [indent + stripped], None, opens


def c_to_rust(c_code: str) -> str:
    c_code = c_code.replace("\x00", r"\0")
    c_ret, name, param_text = parse_signature(c_code)
    params = split_params(param_text)
    mutable = mutable_array_names(c_code, params)
    mutable_scalars = {
        param_name
        for _, param_name, pointer in params
        if not pointer and re.search(rf"\b{param_name}\s*=", c_code)
    }
    signature, array_names, has_char = rust_signature(c_ret, name, params, mutable, mutable_scalars)
    lines = merge_multiline_conditions(c_code.splitlines()[1:-1])

    out = [signature]
    stack: list[str | None] = []
    for line in lines:
        stripped = line.strip()
        if stripped == "}":
            if stack:
                inc = stack.pop()
                if inc:
                    out.append(line[: len(line) - len(line.lstrip())] + "    " + inc)
            out.append(line)
            continue
        if stripped.startswith("} else if"):
            if stack:
                stack.pop()
            indent = line[: len(line) - len(line.lstrip())]
            cond = stripped[len("} else if") :].strip()
            cond = cond[:-1].strip() if cond.endswith("{") else cond
            if has_char:
                cond = convert_char_literals(cond)
            cond = index_arrays(cond, array_names)
            cond = re.sub(r"!\s*([A-Za-z_]\w*)", r"\1 == 0", cond)
            out.append(f"{indent}}} else if {strip_outer_parens(cond)} {{")
            stack.append(None)
            continue
        if stripped.startswith("} else"):
            if stack:
                stack.pop()
            out.append(line)
            stack.append(None)
            continue
        converted, loop_inc, opens = convert_statement(line, array_names, has_char)
        converted = [re.sub(r"\bmod\b", "r#mod", item) for item in converted]
        if loop_inc:
            loop_inc = re.sub(r"\bmod\b", "r#mod", loop_inc)
        out.extend(converted)
        if loop_inc:
            stack.append(loop_inc)
        elif opens:
            stack.append(None)
    out.append("}")
    return "\n".join(out)


def main() -> None:
    for lang in ("c", "java", "rust"):
        shutil.rmtree(OUT_ROOT / lang, ignore_errors=True)
        (OUT_ROOT / lang).mkdir(parents=True, exist_ok=True)

    count = 0
    for c_path in sorted(CAV_RAW.glob("*.md")):
        java_path = JAVA_RAW / c_path.name
        if not java_path.exists():
            raise FileNotFoundError(java_path)
        c_text = c_path.read_text(encoding="utf-8")
        java_text = java_path.read_text(encoding="utf-8")
        before, after = problem_text(c_text)
        c_code = read_code(c_text, "c")
        java_code = read_code(java_text, "java")
        rust_code = c_to_rust(c_code)
        write_md(OUT_ROOT / "c" / c_path.name, before, "c", c_code, after)
        write_md(OUT_ROOT / "java" / c_path.name, before, "java", java_code, after)
        write_md(OUT_ROOT / "rust" / c_path.name, before, "rust", rust_code, after)
        count += 1

    for task in INTERNAL_EXTRA_TASKS + more_internal_tasks():
        filename = f"{task['name']}.md"
        for lang in ("c", "java", "rust"):
            (OUT_ROOT / lang / filename).write_text(extra_md(task, lang), encoding="utf-8")
        count += 1

    (OUT_ROOT / "README.md").write_text(
        "# Internal Algorithm Dataset\n\n"
        f"- Problems: {count}\n"
        "- Languages: C, Java, Rust\n"
        "- Format: one Markdown file per problem per language.\n"
        "- The problem text is shared across languages; only the reference implementation code block differs.\n"
        "- First batch source: local CAV simple algorithm raw tasks, suitable as LeetCode/Luogu-style elementary problems.\n",
        encoding="utf-8",
    )
    print(f"generated {count} problems under {OUT_ROOT}")


if __name__ == "__main__":
    main()

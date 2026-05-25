#!/usr/bin/env python3
"""Generate a new LeetCode/Luogu-style elementary algorithm dataset."""

from __future__ import annotations

import re
import shutil
from dataclasses import dataclass
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
OUT_ROOT = REPO_ROOT / "datasets" / "new_algorithms"


@dataclass
class Task:
    name: str
    title: str
    description: str
    c: str
    java: str
    rust: str


def pascal(name: str) -> str:
    return "".join(part[:1].upper() + part[1:] for part in name.split("_"))


def md(task: Task, lang: str, code: str) -> str:
    return (
        f"# {task.title}\n\n"
        "## 问题描述\n\n"
        f"{task.description.rstrip()}\n\n"
        "## 参考实现\n\n"
        f"```{lang}\n{code.rstrip()}\n```\n"
    )


def scalar_task(name: str, title: str, desc: str, params: str, java_params: str, rust_params: str, c_body: str, java_body: str | None = None, rust_body: str | None = None) -> Task:
    cls = pascal(name)
    java_body = java_body or c_body
    rust_body = rust_body or java_body
    return Task(
        name,
        title,
        desc,
        f"int {name}({params}) {{\n{indent(c_body, 4)}\n}}",
        f"class {cls} {{\n    public static int {name}({java_params}) {{\n{indent(java_body, 8)}\n    }}\n}}",
        f"pub fn {name}({rust_params}) -> i32 {{\n{indent(rust_body, 4)}\n}}",
    )


def indent(text: str, spaces: int) -> str:
    prefix = " " * spaces
    return "\n".join(prefix + line if line else "" for line in text.strip("\n").splitlines())


def scalar_tasks() -> list[Task]:
    common = "所有输入均为 Java/C/Rust 的 32 位有符号整数范围内的值；题目约束保证参考实现中的中间结果不会溢出。"
    return [
        scalar_task("fresh_sum_three", "Sum Three Integers", f"实现函数 `fresh_sum_three`，返回 `a + b + c`。\n\n约定：\n- {common}", "int a, int b, int c", "int a, int b, int c", "a: i32, b: i32, c: i32", "return a + b + c;"),
        scalar_task("fresh_average_floor_three", "Floor Average Of Three", f"实现函数 `fresh_average_floor_three`，返回三个整数和除以 `3` 的整数商。\n\n约定：\n- `a + b + c >= 0`\n- {common}", "int a, int b, int c", "int a, int b, int c", "a: i32, b: i32, c: i32", "return (a + b + c) / 3;"),
        scalar_task("fresh_abs_diff", "Absolute Difference", f"实现函数 `fresh_abs_diff`，返回两个整数差的绝对值。\n\n约定：\n- `a - b` 和 `b - a` 都不会溢出。", "int a, int b", "int a, int b", "a: i32, b: i32", "if (a >= b) {\n    return a - b;\n}\nreturn b - a;", rust_body="if a >= b {\n    return a - b;\n}\nreturn b - a;"),
        scalar_task("fresh_max_four", "Maximum Of Four", "实现函数 `fresh_max_four`，返回四个整数中的最大值。", "int a, int b, int c, int d", "int a, int b, int c, int d", "a: i32, b: i32, c: i32, d: i32", "int m = a;\nif (b > m) m = b;\nif (c > m) m = c;\nif (d > m) m = d;\nreturn m;", java_body="int m = a;\nif (b > m) m = b;\nif (c > m) m = c;\nif (d > m) m = d;\nreturn m;", rust_body="let mut m = a;\nif b > m { m = b; }\nif c > m { m = c; }\nif d > m { m = d; }\nreturn m;"),
        scalar_task("fresh_min_four", "Minimum Of Four", "实现函数 `fresh_min_four`，返回四个整数中的最小值。", "int a, int b, int c, int d", "int a, int b, int c, int d", "a: i32, b: i32, c: i32, d: i32", "int m = a;\nif (b < m) m = b;\nif (c < m) m = c;\nif (d < m) m = d;\nreturn m;", rust_body="let mut m = a;\nif b < m { m = b; }\nif c < m { m = c; }\nif d < m { m = d; }\nreturn m;"),
        scalar_task("fresh_signum", "Integer Sign", "实现函数 `fresh_signum`，正数返回 `1`，负数返回 `-1`，零返回 `0`。", "int x", "int x", "x: i32", "if (x > 0) return 1;\nif (x < 0) return -1;\nreturn 0;", rust_body="if x > 0 { return 1; }\nif x < 0 { return -1; }\nreturn 0;"),
        scalar_task("fresh_is_even", "Is Even", "实现函数 `fresh_is_even`，如果 `x` 是偶数返回 `1`，否则返回 `0`。", "int x", "int x", "x: i32", "return x % 2 == 0 ? 1 : 0;", rust_body="if x % 2 == 0 { return 1; }\nreturn 0;"),
        scalar_task("fresh_is_odd", "Is Odd", "实现函数 `fresh_is_odd`，如果 `x` 是奇数返回 `1`，否则返回 `0`。", "int x", "int x", "x: i32", "return x % 2 != 0 ? 1 : 0;", rust_body="if x % 2 != 0 { return 1; }\nreturn 0;"),
        scalar_task("fresh_clamp_0_100", "Clamp To 0 100", "实现函数 `fresh_clamp_0_100`，把整数限制在闭区间 `[0, 100]` 内。", "int x", "int x", "x: i32", "if (x < 0) return 0;\nif (x > 100) return 100;\nreturn x;", rust_body="if x < 0 { return 0; }\nif x > 100 { return 100; }\nreturn x;"),
        scalar_task("fresh_ceil_div_positive", "Ceil Division Positive", "实现函数 `fresh_ceil_div_positive`，返回非负整数 `a` 除以正整数 `b` 的向上取整结果。\n\n约定：\n- `a >= 0`\n- `b > 0`\n- `a + b - 1` 不会溢出。", "int a, int b", "int a, int b", "a: i32, b: i32", "return (a + b - 1) / b;"),
        scalar_task("fresh_leap_year", "Leap Year", "实现函数 `fresh_leap_year`，如果 `year` 是闰年返回 `1`，否则返回 `0`。\n\n约定：\n- `year > 0`", "int year", "int year", "year: i32", "if (year % 400 == 0) return 1;\nif (year % 100 == 0) return 0;\nif (year % 4 == 0) return 1;\nreturn 0;", rust_body="if year % 400 == 0 { return 1; }\nif year % 100 == 0 { return 0; }\nif year % 4 == 0 { return 1; }\nreturn 0;"),
        scalar_task("fresh_days_in_month_common", "Days In Month Common Year", "实现函数 `fresh_days_in_month_common`，输入普通年份中的月份 `month`，返回该月天数。\n\n约定：\n- `1 <= month <= 12`\n- 二月按 28 天计算。", "int month", "int month", "month: i32", "if (month == 2) return 28;\nif (month == 4 || month == 6 || month == 9 || month == 11) return 30;\nreturn 31;", rust_body="if month == 2 { return 28; }\nif month == 4 || month == 6 || month == 9 || month == 11 { return 30; }\nreturn 31;"),
        scalar_task("fresh_digit_sum", "Digit Sum Nonnegative", "实现函数 `fresh_digit_sum`，返回非负整数十进制各位数字之和。\n\n约定：\n- `x >= 0`", "int x", "int x", "mut x: i32", "int sum = 0;\nwhile (x > 0) {\n    sum += x % 10;\n    x /= 10;\n}\nreturn sum;", rust_body="let mut sum = 0;\nwhile x > 0 {\n    sum += x % 10;\n    x /= 10;\n}\nreturn sum;"),
        scalar_task("fresh_count_bits", "Count Set Bits", "实现函数 `fresh_count_bits`，返回非负整数二进制表示中 `1` 的个数。\n\n约定：\n- `x >= 0`", "int x", "int x", "mut x: i32", "int count = 0;\nwhile (x > 0) {\n    count += x % 2;\n    x /= 2;\n}\nreturn count;", rust_body="let mut count = 0;\nwhile x > 0 {\n    count += x % 2;\n    x /= 2;\n}\nreturn count;"),
        scalar_task("fresh_is_power_of_two", "Is Power Of Two", "实现函数 `fresh_is_power_of_two`，如果正整数 `x` 是 2 的幂返回 `1`，否则返回 `0`。\n\n约定：\n- `x > 0`", "int x", "int x", "mut x: i32", "while (x % 2 == 0) {\n    x /= 2;\n}\nreturn x == 1 ? 1 : 0;", rust_body="while x % 2 == 0 {\n    x /= 2;\n}\nif x == 1 { return 1; }\nreturn 0;"),
        scalar_task("fresh_gcd_positive", "GCD Positive", "实现函数 `fresh_gcd_positive`，返回两个正整数的最大公约数。\n\n约定：\n- `a > 0`\n- `b > 0`", "int a, int b", "int a, int b", "mut a: i32, mut b: i32", "while (b != 0) {\n    int t = a % b;\n    a = b;\n    b = t;\n}\nreturn a;", rust_body="while b != 0 {\n    let t = a % b;\n    a = b;\n    b = t;\n}\nreturn a;"),
        scalar_task("fresh_lcm_positive", "LCM Positive", "实现函数 `fresh_lcm_positive`，返回两个正整数的最小公倍数。\n\n约定：\n- `a > 0`\n- `b > 0`\n- 结果不会溢出。", "int a, int b", "int a, int b", "a: i32, b: i32", "int x = a;\nint y = b;\nwhile (y != 0) {\n    int t = x % y;\n    x = y;\n    y = t;\n}\nreturn a / x * b;", rust_body="let mut x = a;\nlet mut y = b;\nwhile y != 0 {\n    let t = x % y;\n    x = y;\n    y = t;\n}\nreturn a / x * b;"),
        scalar_task("fresh_factorial_small", "Factorial Small", "实现函数 `fresh_factorial_small`，返回 `n!`。\n\n约定：\n- `0 <= n <= 12`", "int n", "int n", "n: i32", "int ans = 1;\nint i;\nfor (i = 2; i <= n; ++i) {\n    ans *= i;\n}\nreturn ans;", rust_body="let mut ans = 1;\nlet mut i = 2;\nwhile i <= n {\n    ans *= i;\n    i += 1;\n}\nreturn ans;"),
        scalar_task("fresh_fibonacci_small", "Fibonacci Small", "实现函数 `fresh_fibonacci_small`，返回第 `n` 个斐波那契数，其中 `F(0)=0`，`F(1)=1`。\n\n约定：\n- `0 <= n <= 45`", "int n", "int n", "n: i32", "if (n <= 1) return n;\nint a = 0;\nint b = 1;\nint i;\nfor (i = 2; i <= n; ++i) {\n    int c = a + b;\n    a = b;\n    b = c;\n}\nreturn b;", rust_body="if n <= 1 { return n; }\nlet mut a = 0;\nlet mut b = 1;\nlet mut i = 2;\nwhile i <= n {\n    let c = a + b;\n    a = b;\n    b = c;\n    i += 1;\n}\nreturn b;"),
        scalar_task("fresh_integer_sqrt_floor", "Integer Square Root Floor", "实现函数 `fresh_integer_sqrt_floor`，返回非负整数 `x` 的平方根向下取整值。\n\n约定：\n- `0 <= x <= 46340 * 46340`", "int x", "int x", "x: i32", "int r = 0;\nwhile ((r + 1) * (r + 1) <= x) {\n    r++;\n}\nreturn r;", rust_body="let mut r = 0;\nwhile (r + 1) * (r + 1) <= x {\n    r += 1;\n}\nreturn r;"),
        scalar_task("fresh_triangle_valid", "Triangle Valid", "实现函数 `fresh_triangle_valid`，如果三条边能组成三角形返回 `1`，否则返回 `0`。\n\n约定：\n- `a > 0`, `b > 0`, `c > 0`\n- 任意两边之和不会溢出。", "int a, int b, int c", "int a, int b, int c", "a: i32, b: i32, c: i32", "if (a + b > c && a + c > b && b + c > a) return 1;\nreturn 0;", rust_body="if a + b > c && a + c > b && b + c > a { return 1; }\nreturn 0;"),
        scalar_task("fresh_manhattan_distance", "Manhattan Distance", "实现函数 `fresh_manhattan_distance`，返回两点 `(x1,y1)` 与 `(x2,y2)` 的曼哈顿距离。\n\n约定：\n- 坐标差和最终结果不会溢出。", "int x1, int y1, int x2, int y2", "int x1, int y1, int x2, int y2", "x1: i32, y1: i32, x2: i32, y2: i32", "int dx = x1 >= x2 ? x1 - x2 : x2 - x1;\nint dy = y1 >= y2 ? y1 - y2 : y2 - y1;\nreturn dx + dy;", rust_body="let dx = if x1 >= x2 { x1 - x2 } else { x2 - x1 };\nlet dy = if y1 >= y2 { y1 - y2 } else { y2 - y1 };\nreturn dx + dy;"),
    ]


COND = [
    ("positive", "正数", "a[i] > 0", "a[i] > 0", "a[i as usize] > 0", ""),
    ("negative", "负数", "a[i] < 0", "a[i] < 0", "a[i as usize] < 0", ""),
    ("zero", "等于 0", "a[i] == 0", "a[i] == 0", "a[i as usize] == 0", ""),
    ("nonzero", "不等于 0", "a[i] != 0", "a[i] != 0", "a[i as usize] != 0", ""),
    ("even", "偶数", "a[i] % 2 == 0", "a[i] % 2 == 0", "a[i as usize] % 2 == 0", ""),
    ("odd", "奇数", "a[i] % 2 != 0", "a[i] % 2 != 0", "a[i as usize] % 2 != 0", ""),
    ("greater_than_k", "大于 `k`", "a[i] > k", "a[i] > k", "a[i as usize] > k", "int k"),
    ("less_than_k", "小于 `k`", "a[i] < k", "a[i] < k", "a[i as usize] < k", "int k"),
    ("at_least_k", "大于等于 `k`", "a[i] >= k", "a[i] >= k", "a[i as usize] >= k", "int k"),
    ("at_most_k", "小于等于 `k`", "a[i] <= k", "a[i] <= k", "a[i as usize] <= k", "int k"),
    ("in_closed_range", "位于闭区间 `[low, high]`", "a[i] >= low && a[i] <= high", "a[i] >= low && a[i] <= high", "a[i as usize] >= low && a[i as usize] <= high", "int low, int high"),
    ("outside_closed_range", "位于闭区间 `[low, high]` 外", "a[i] < low || a[i] > high", "a[i] < low || a[i] > high", "a[i as usize] < low || a[i as usize] > high", "int low, int high"),
]


def extra_params(extra: str, lang: str) -> str:
    if not extra:
        return ""
    if lang == "rust":
        return ", " + ", ".join(part.strip().split()[-1] + ": i32" for part in extra.split(","))
    return ", " + extra


def array_task(kind: str, cond_name: str, cond_desc: str, c_cond: str, java_cond: str, rust_cond: str, extra: str) -> Task:
    name = f"fresh_array_{kind}_{cond_name}"
    title = " ".join(part.capitalize() for part in name.split("_")[1:])
    c_params = f"int n, int *a{extra_params(extra, 'c')}"
    j_params = f"int n, int[] a{extra_params(extra, 'java')}"
    r_params = f"n: i32, a: &[i32]{extra_params(extra, 'rust')}"
    base = f"实现函数 `{name}`，输入长度为 `n` 的整数序列 `a`，"
    rules = "\n\n约定：\n- `n >= 0`\n- `a` 的长度至少为 `n`"
    if "range" in cond_name:
        rules += "\n- `low <= high`"
    if kind == "count":
        desc = base + f"返回其中{cond_desc}的元素个数。" + rules
        c_body = f"int ans = 0;\nint i;\nfor (i = 0; i < n; ++i) {{\n    if ({c_cond}) ans++;\n}}\nreturn ans;"
        r_body = f"let mut ans = 0;\nlet mut i = 0;\nwhile i < n {{\n    if {rust_cond} {{ ans += 1; }}\n    i += 1;\n}}\nreturn ans;"
    elif kind == "exists":
        desc = base + f"如果存在{cond_desc}的元素返回 `1`，否则返回 `0`。" + rules
        c_body = f"int i;\nfor (i = 0; i < n; ++i) {{\n    if ({c_cond}) return 1;\n}}\nreturn 0;"
        r_body = f"let mut i = 0;\nwhile i < n {{\n    if {rust_cond} {{ return 1; }}\n    i += 1;\n}}\nreturn 0;"
    elif kind == "all":
        desc = base + f"如果所有元素都{cond_desc}返回 `1`，否则返回 `0`。" + rules + "\n- 空序列返回 `1`"
        c_body = f"int i;\nfor (i = 0; i < n; ++i) {{\n    if (!({c_cond})) return 0;\n}}\nreturn 1;"
        r_body = f"let mut i = 0;\nwhile i < n {{\n    if !({rust_cond}) {{ return 0; }}\n    i += 1;\n}}\nreturn 1;"
    elif kind == "first_index":
        desc = base + f"返回第一个{cond_desc}的元素下标；如果不存在返回 `-1`。" + rules
        c_body = f"int i;\nfor (i = 0; i < n; ++i) {{\n    if ({c_cond}) return i;\n}}\nreturn -1;"
        r_body = f"let mut i = 0;\nwhile i < n {{\n    if {rust_cond} {{ return i; }}\n    i += 1;\n}}\nreturn -1;"
    elif kind == "last_index":
        desc = base + f"返回最后一个{cond_desc}的元素下标；如果不存在返回 `-1`。" + rules
        c_body = f"int i;\nfor (i = n - 1; i >= 0; --i) {{\n    if ({c_cond}) return i;\n}}\nreturn -1;"
        r_body = f"let mut i = n - 1;\nwhile i >= 0 {{\n    if {rust_cond} {{ return i; }}\n    if i == 0 {{ break; }}\n    i -= 1;\n}}\nreturn -1;"
    else:
        desc = base + f"返回所有{cond_desc}元素的和。" + rules + "\n- 结果不会溢出"
        c_body = f"int ans = 0;\nint i;\nfor (i = 0; i < n; ++i) {{\n    if ({c_cond}) ans += a[i];\n}}\nreturn ans;"
        r_body = f"let mut ans = 0;\nlet mut i = 0;\nwhile i < n {{\n    if {rust_cond} {{ ans += a[i as usize]; }}\n    i += 1;\n}}\nreturn ans;"
    cls = pascal(name)
    java_body = c_body.replace("int *a", "int[] a")
    return Task(
        name,
        title,
        desc,
        f"int {name}({c_params}) {{\n{indent(c_body, 4)}\n}}",
        f"class {cls} {{\n    public static int {name}({j_params}) {{\n{indent(java_body, 8)}\n    }}\n}}",
        f"pub fn {name}({r_params}) -> i32 {{\n{indent(r_body, 4)}\n}}",
    )


def array_tasks() -> list[Task]:
    tasks: list[Task] = []
    for kind in ("count", "exists", "all", "first_index", "last_index", "sum"):
        for item in COND:
            tasks.append(array_task(kind, *item))
    return tasks


def structural_tasks() -> list[Task]:
    specs = [
        ("fresh_array_sum_total", "Array Sum Total", "返回长度为 `n` 的整数序列 `a` 的元素总和。", "int ans = 0;\nint i;\nfor (i = 0; i < n; ++i) ans += a[i];\nreturn ans;", "let mut ans = 0;\nlet mut i = 0;\nwhile i < n { ans += a[i as usize]; i += 1; }\nreturn ans;"),
        ("fresh_array_max_index_first", "Array First Max Index", "返回长度为 `n` 的整数序列 `a` 中最大元素第一次出现的下标。\n\n约定：\n- `n > 0`", "int idx = 0;\nint i;\nfor (i = 1; i < n; ++i) if (a[i] > a[idx]) idx = i;\nreturn idx;", "let mut idx = 0;\nlet mut i = 1;\nwhile i < n { if a[i as usize] > a[idx as usize] { idx = i; } i += 1; }\nreturn idx;"),
        ("fresh_array_min_index_last", "Array Last Min Index", "返回长度为 `n` 的整数序列 `a` 中最小元素最后一次出现的下标。\n\n约定：\n- `n > 0`", "int idx = 0;\nint i;\nfor (i = 1; i < n; ++i) if (a[i] <= a[idx]) idx = i;\nreturn idx;", "let mut idx = 0;\nlet mut i = 1;\nwhile i < n { if a[i as usize] <= a[idx as usize] { idx = i; } i += 1; }\nreturn idx;"),
        ("fresh_array_is_non_decreasing", "Array Is Non Decreasing", "如果长度为 `n` 的整数序列 `a` 非递减返回 `1`，否则返回 `0`。", "int i;\nfor (i = 1; i < n; ++i) if (a[i] < a[i - 1]) return 0;\nreturn 1;", "let mut i = 1;\nwhile i < n { if a[i as usize] < a[(i - 1) as usize] { return 0; } i += 1; }\nreturn 1;"),
        ("fresh_array_adjacent_equal_count", "Array Adjacent Equal Count", "返回长度为 `n` 的整数序列 `a` 中相邻且相等的下标对数量。", "int ans = 0;\nint i;\nfor (i = 1; i < n; ++i) if (a[i] == a[i - 1]) ans++;\nreturn ans;", "let mut ans = 0;\nlet mut i = 1;\nwhile i < n { if a[i as usize] == a[(i - 1) as usize] { ans += 1; } i += 1; }\nreturn ans;"),
        ("fresh_array_peak_count", "Array Strict Peak Count", "返回长度为 `n` 的整数序列 `a` 中严格峰值的个数。下标 `i` 是严格峰值，当且仅当 `0 < i < n-1` 且 `a[i]` 大于左右相邻元素。", "int ans = 0;\nint i;\nfor (i = 1; i + 1 < n; ++i) if (a[i] > a[i - 1] && a[i] > a[i + 1]) ans++;\nreturn ans;", "let mut ans = 0;\nlet mut i = 1;\nwhile i + 1 < n { if a[i as usize] > a[(i - 1) as usize] && a[i as usize] > a[(i + 1) as usize] { ans += 1; } i += 1; }\nreturn ans;"),
    ]
    tasks = []
    for name, title, desc, c_body, rust_body in specs:
        full_desc = f"实现函数 `{name}`，{desc}\n\n约定：\n- `n >= 0`\n- `a` 的长度至少为 `n`\n- 结果不会溢出"
        if "`n > 0`" in desc:
            full_desc = f"实现函数 `{name}`，{desc}\n- `a` 的长度至少为 `n`"
        cls = pascal(name)
        tasks.append(Task(name, title, full_desc, f"int {name}(int n, int *a) {{\n{indent(c_body, 4)}\n}}", f"class {cls} {{\n    public static int {name}(int n, int[] a) {{\n{indent(c_body, 8)}\n    }}\n}}", f"pub fn {name}(n: i32, a: &[i32]) -> i32 {{\n{indent(rust_body, 4)}\n}}"))
    return tasks


def main() -> None:
    shutil.rmtree(OUT_ROOT, ignore_errors=True)
    for lang in ("c", "java", "rust"):
        (OUT_ROOT / lang).mkdir(parents=True, exist_ok=True)
    tasks = scalar_tasks() + array_tasks() + structural_tasks()
    seen = set()
    for task in tasks:
        if task.name in seen:
            raise ValueError(f"duplicate task: {task.name}")
        seen.add(task.name)
        (OUT_ROOT / "c" / f"{task.name}.md").write_text(md(task, "c", task.c), encoding="utf-8")
        (OUT_ROOT / "java" / f"{task.name}.md").write_text(md(task, "java", task.java), encoding="utf-8")
        (OUT_ROOT / "rust" / f"{task.name}.md").write_text(md(task, "rust", task.rust), encoding="utf-8")
    (OUT_ROOT / "README.md").write_text(
        "# New Algorithm Raw Dataset\n\n"
        f"- Problems: {len(tasks)}\n"
        "- Languages: C, Java, Rust\n"
        "- Source: newly written LeetCode/Luogu-style elementary tasks; not migrated from CAV.\n"
        "- Same-name files in `c/`, `java/`, and `rust/` share identical problem text; only the reference implementation differs.\n"
        "- Validation: `python3 scripts/validate_algorithm_dataset.py --dataset datasets/new_algorithms --require-rust`\n",
        encoding="utf-8",
    )
    print(f"generated {len(tasks)} new problems under {OUT_ROOT}")


if __name__ == "__main__":
    main()

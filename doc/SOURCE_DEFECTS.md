# 源码 / 契约层缺陷模式（导致 VC 不可证的真实 bug）

本文件记录 **不是证明技巧问题、而是输入本身有缺陷** 的模式：这类任务在 verify 阶段无论怎么加注解、怎么写证明都证不出来，因为生成的安全 VC 对**合法输入为假**。沉淀这些模式是为了：

- 让 verify agent 早点判定"这是输入缺陷、不是 proof 债"，按 `experiences/general/PROOF/README.md §32` 收尾，不要白跑满预算；
- 让 Contract / 数据集生成阶段在源头拦掉这类 bug；
- 区分清楚三种容易混淆的情况：**C 实现 bug** vs **契约太弱** vs **证明难但可证**。

## 判定三分法

| 情况 | VC 真假 | 表现 | 正确处理 |
| --- | --- | --- | --- |
| C 实现 bug | **假**（对合法输入） | 能算出具体反例；UBSan 也会报同一行 | 改 C 源码 |
| 契约太弱 | VC 真但缺前提 | `entailer!` 后残留 LHS 不带的纯条件（如 `p <> NULL`） | 回 Contract 加前置（见 `experiences/general/CONTRACT/README.md §15`） |
| 证明难但可证 | **真** | 反复 `coqc` 失败但找不到反例 | 继续证 / 优化 tactic（见 PROOF §3、§35） |

关键区别：**能不能对一个满足前置的合法输入，把 witness 的结论算成 `false`**。能 → C bug 或契约缺陷（改输入）；不能 → 继续证。

---

## 模式 1：十进制解析的有符号整数溢出 `v = v*10 + byte - 48`

### 症状（verify 阶段）

- 首个未解 witness 是形如 `(v * 10 + Znth i (l ++ ...) 0) <= INT_MAX` 的 `safety_wit`，反复成为 first blocker，跨多次 attempt 零进展。
- agent 能给出反例：合法最大 token `"2147483647"` → 中间量 `214748364 * 10 + 55 = 2147483695 > 2147483647`。
- 常被 runner 当成 `proof_manual_has_obligations` 反复强制重试到 exit 124（看起来像 timeout，其实是这个缺陷）。

### 根因

C 写法

```c
v = v * 10 + nums[i] - 48;        // 按结合律 = ((v*10) + nums[i]) - 48
```

中间量 `v*10 + nums[i]` 比目标值 **多 48**（因为 `nums[i]` 是数字字符的 ASCII 码，digit offset 48 还没减掉）。契约只约束**最终解析值** `≤ INT_MAX`，对值接近 INT_MAX 的合法输入，这个中间量就溢出了。**有符号整数溢出在 C 里是未定义行为（UB）**，所以 symexec 生成的"不许溢出"安全 VC 对合法输入为假，证不出来。

### 证据（可复现）

```c
/* /tmp/overflow_demo.c */
#include <stdio.h>
#include <limits.h>
int main(void) {
    char *s = "2147483647";              /* 合法 int，正好 = INT_MAX */
    int v = 0;
    for (int i = 0; s[i]; i++) v = v * 10 + s[i] - 48;        /* 写法A：漏括号 */
    int w = 0;
    for (int i = 0; s[i]; i++) w = w * 10 + (s[i] - 48);      /* 写法B：带括号 */
    printf("A=%d  B=%d  INT_MAX=%d\n", v, w, INT_MAX);
    return 0;
}
```

```
$ gcc -O2 overflow_demo.c -o d && ./d
A=2147483647  B=2147483647  INT_MAX=2147483647        # 普通编译两者都"碰巧"对——测试测不出来

$ gcc -fsanitize=signed-integer-overflow -O0 overflow_demo.c -o d && ./d
overflow_demo.c: runtime error: signed integer overflow: 2147483640 + 55 cannot be represented in type 'int'
overflow_demo.c: runtime error: signed integer overflow: -2147483601 - 48 cannot be represented in type 'int'
A=2147483647  B=2147483647
```

写法 A 在 `-O2` 下"碰巧"返回正确值，只是因为 x86 上两次回绕正好抵消——这**不是 C 保证的**，换编译器/优化级/平台就可能给垃圾值。UBSan 和形式化验证器是两个独立工具，都指着同一行说"这里溢出了"。

### 这是 C bug，不是契约 bug

- 契约 intent 正确：解析函数本就该能处理到 INT_MAX 的值。
- 真正错的是 C：digit offset 减晚了，导致中间量溢出。
- **反例修法（不推荐）**：把前置收紧到 `digit_prefix_value l <= 2147483647 - 48`。能让 VC 可证，但会**误拒 2147483600..2147483647 这 48 个合法 int**——等于用过紧的前置把 bug 藏起来。

### 正确修法

把 digit offset 先减掉再累加（与同仓库已写对的 `best_stock_profit_csv.c` 一致）：

```c
v = v * 10 + (nums[i] - 48);
```

此时中间量 `v*10` ≤ final ≤ INT_MAX、`v*10 + digit = 下一个前缀值` ≤ final ≤ INT_MAX，不再溢出；生成的 VC 从假的 `final + 48 ≤ INT_MAX` 变成可证的 `final ≤ INT_MAX`。

> 注意：修完只是从"不可证"变"可证"。这个溢出 VC 仍非平凡（需要 loop invariant `v ≤ final ≤ INT_MAX` + 单调性），还要配合 `entailer_pure` / 预算优化（PROOF §35）才能在预算内证完。

### 受影响文件与上游根因（数据集 codegen 漏括号）

`best_stock_profit_csv.c` 写法正确（`v*10 + (prices[i]-48)`），可作范例。

**上游根因**：这些 `.c` 由 `scripts/expand_multisource_dataset.py` 生成，该生成器的内嵌 C 模板用的是漏括号的 `v = v*10 + X[i] - '0'`（`'0'` == 48），共 **157 处**。只改 input 文件，重新生成会回退。

**已修复（2026-06-05）**：
- 生成器 `scripts/expand_multisource_dataset.py`：157 处 C 累加全部括号化为 `v*10 + (X[i] - '0')`（标量 `*10+` 如 `yuan*10+jiao` 未动；`py_compile` 通过）。
- 当时已落地的 **19 个 input/*.c**（漏括号的 `* 10 + <byte> - 48`），按各自变量名（`v` / `best` / `prev`）补括号：
  ```
  array_min_csv            aug_count_ge_array_007     aug_count_le_array_005
  aug_count_ge_stream_007  count_good_pairs_csv       ex_binary_search_index_csv
  aug_count_ge_stream_000  ex_matrix_row_sum          aug_first_ge_stream_001
  array_is_sorted_csv      aug_count_ge_array_000     aug_last_le_array_006
  aug_sum_prefix_array_002 contains_duplicate_csv     aug_first_ge_array_001
  aug_sum_prefix_stream_002 aug_all_multiple_array_003 decode_xored_array_csv
  aug_all_multiple_stream_003
  ```

**未处理（需另行决定）**：生成器里 Java（1 处）、Rust（4 处）的同款 idiom 未改——Java 溢出是 defined（回绕，非 UB），Rust debug panic / release 回绕，与 C 的 UB 性质不同，且不在本 C 验证 pipeline 范围内。

### 快速诊断

```bash
# 找出所有漏括号的累加（命中即疑似本缺陷）
grep -rnE "\* *10 *\+[^()]*- *48" input/*.c

# 对单个文件确认是否真的运行时溢出
gcc -fsanitize=signed-integer-overflow -O0 <file>.c -o /tmp/ub && echo "<合法最大输入>" | /tmp/ub
```

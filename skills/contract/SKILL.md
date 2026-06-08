---
name: contract
description: Contract skill，把原始题意 + C 实现整理成 verify 友好的 `mid/<dataset>/<name>.c` / `.v`。
---

Contract 把原始题意 + C 实现整理成 verify 友好的入口/出口 contract，不写 verify 阶段 annotation。

## 0. 职责

- spec 写法、谓词选择、spec 质量判定依照 QCP `.agents/skills/annotation-filling/docs/` 和 `.agents/skills/annotation-checking/docs/spec-quality-checklist.md`。用到前必须先读。
- 本 skill 只规定 CAV 工程约束、产物、gate、退出和日志。
- 唯一文字产物是 `logs/issues.md` 和 `logs/metrics.md`。

## 1. 路径和边界

- 输入：原始 C 实现 + 题意 / 约束 / 边界 / 示例。
- 输出：`mid/<dataset>/<name>.c`；仅在确需额外 Coq 定义时写 `mid/<dataset>/<name>.v`。
- `input/` 只读，contract 阶段不写。
- Contract 不创建、不写 verify QCP mirror：
  - `QualifiedCProgramming/QCP_examples/CAV/`
  - `QualifiedCProgramming/SeparationLogic/examples/CAV/`
  - `QualifiedCProgramming/SeparationLogic/_cav_original/`

公共验证头必须裸名 include 且保持原名：

```c
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"
#include "char_array_def.h"
```

禁止 `../` 等路径前缀，禁止改成 `p008_verification_stdlib.h`、`p008_int_array_def.h` 等题目私有名。

## 2. Contract 规则

- `mid/.c` 只含目标函数 + 完整 `Require` / `Ensure`；不得提前写 `Inv` / `Assert` / `which implies` / proof bridge。
- 不得修改原程序语义；verification-friendly 改写必须保持题意等价并写入 `logs/issues.md`。
- `Require` / `Ensure` 只表达函数入口/出口语义，不塞循环不变式、中间断言或未来 witness 事实。
- `mid/.v` 只放题目专用定义，必须 definition-only：无 `Axiom` / `Hypothesis` / `Parameter` / `Conjecture` / `Variable` / `Admitted` / `admit` / `Abort`。
- `mid/.v` 必须自包含或只依赖同一 `mid/<dataset>/` 下可由 runner gate 编译的共享 `.v`，不得依赖 verify workspace、`output/` 或 QCP mirror。
- C 字符串用 `CharArray::full(p, n + 1, app(l, cons(0, nil)))` 时，`Require` / `Ensure` 必须同时保留 `Zlength(l) == n` 和中间非零约束：
  `(forall (k: Z), (0 <= k && k < n) => Znth(k, l, 0) != 0)`。
- 前条件必须排除所有 RTE/UB：空指针、数组越界、除零、非法移位、有符号整数溢出、`abs`/取负/累加/循环变元更新溢出等。审计结论写入 `logs/issues.md`。

## 3. 工作循环

1. 读题意和代码，按需读 QCP `.agents` 文档和参考例子。
2. 生成 `mid/<dataset>/<name>.c` 和必要的 `.v`。
3. 跑 runner gate：`check_spec_wellformed` / `.v` definition-only / `coqc mid/.v`。
4. gate 失败则读第一个报错，修改，重跑；不得通过改脚本、QCP 源码或 verify mirror 绕过。

## 4. 退出条件

退出和成功的 spec 判定以 QCP `.agents/skills/annotation-filling/` 与 `.agents/skills/annotation-checking/` 为准；CAV 只增加下面的产物、RTE/UB 和 runner gate 要求。

全部满足才写 `Final Result: Success`：

- QCP annotation/spec-quality 检查口径判定 contract 合格。
- `mid/.c` 有完整入口/出口 contract，且无 verify 阶段 annotation。
- 公共头裸名 include 且保持原名。
- 字符串 contract 保留长度和中间 no-zero 约束。
- 前条件排除 RTE/UB，审计写入 `logs/issues.md`。
- `check_spec_wellformed == well_formed`。
- `.v` 如存在，definition-only 且 runner `coqc` gate 通过。
- `logs/issues.md` 和 `logs/metrics.md` 已更新。

只有按 QCP annotation/spec-quality 检查口径确认题意、原始实现或所需 contract 本身矛盾，必须用户/上游决策时，才写 `Final Result: Fail`。可通过修改 `mid/.c` / `.v` 修复的 gate 失败必须继续推进。

## 5. 日志

`logs/issues.md` 退出前必须存在。若没有真正 issue，写 `No issues encountered.`；否则记录 RTE/UB 审计、gate 失败、修复动作和结果。

`logs/metrics.md` 记录最终结果、耗时、输入/输出路径、agent/model 和 gate 结果。

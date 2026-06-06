---
name: contract
description: Contract skill，把原始题意 + C 实现整理成 verify 友好的 `mid/<dataset>/<name>.c` / `.v`(raw→pipeline 的产物;`input/` 是只读 curated 数据,contract 不写)。
---

Contract 把原始题意 + C 实现整理成 verify 友好的 `mid/<dataset>/<name>.c`(+ 可选 `.v`)。

## 职责划分（先读）

- **写 spec 的 how-to（注解语法、谓词选择、spec 质量）完全依照 QCP `.agents/skills/`**：`annotation-filling/docs/`（`annotation-rules.md`、`predicate-first-annotation.md`、`builtin-array-string-support.md`、`array-predicate-selection.md`）、`annotation-checking/docs/spec-quality-checklist.md`。照那边写，本 skill 不复述。**read-before-act：用到这些规则时必须先读对应文档再动手,不能凭猜。**
- **本 skill 只管 CAV 工程约束**：输入输出路径、读写边界、contract 专有硬规则、well-formed/编译 gate、宏观错误迭代、issues。
- **唯一文字产物 = `logs/issues.md`（含 RTE/UB 审计结论、每条 gate 失败 / critic finding 的对照修复）+ `logs/metrics.md`**；不写过程 reasoning 日志。
- 跨阶段共用读写边界/效率/`Final Result` 格式见 `skills/COMMON.md`。

## 1. 输入输出（CAV）

- 输入：原始 C 实现 + 题意 / 约束 / 边界 / 示例。
- 输出：`mid/<dataset>/<name>.c`（目标函数 + 完整 contract，**不含**任何 verify 阶段注释）；仅在确需额外 Coq 定义时写 `mid/<dataset>/<name>.v`。
- `input/` 是只读 curated 数据，contract **不写**。

## 2. CAV 硬规则

- `mid/.c` 只含目标函数 + 完整 contract；**不要**提前写 `Inv` / `Assert` / `which implies` / bridge / loop-exit（那是 verify 阶段）。
- `mid/.v` 只放题目专用 Coq 定义，definition-only（无 `Axiom`/`Hypothesis`/`Parameter`/`Conjecture`/`Variable`/`Admitted`/`admit`/`Abort`），且能被 `coqc` 编译。
- 公共验证头一律**裸名 include**（头文件已复制到该 dataset 目录）：`#include "verification_stdlib.h"`、`"verification_list.h"`、`"int_array_def.h"`，字符数组用 `"char_array_def.h"`；禁 `../` 等路径前缀。
- 保持原程序语义；必须改接口时只做 verification-friendly 改写。
- **spec 质量与谓词选择照「职责划分」里的 `.agents` 文档**：优先「量词 + 已定义函数（`Permutation`/`Znth`/`Zlength`/`app`/`sorted` 等）」刻画输入输出关系，实在无法表达才写题目专用 `Fixpoint`/`Inductive`。
- **RTE/UB 安全（contract 的核心义务）**：前条件必须排除空指针解引用、数组越界、除零、非法移位、有符号整数加减乘 / 取负 / `abs` / 累加 / 循环变元更新等所有可能溢出与 C UB/RTE（用 `Require` / 前条件，`INT_MIN <= ... <= INT_MAX` 风格界）。逐项审计结论写进 `logs/issues.md`，不依赖「运行时自然不会发生」。后条件优先写蕴含，避免顶层析取。

## 3. 宏观流程（极简 + 错误迭代）

1. 读题意和代码；按需读「职责划分」的 `.agents` 文档与 `QualifiedCProgramming/SeparationLogic/examples/`，不预读。
2. 生成 `mid/<dataset>/<name>.c`（+ 必要的 `.v`）。
3. 跑 gate（`check_spec_wellformed` / 可选 `coqc .v`）；失败就读**第一个**报错 → 改 → 重跑，**循环到通过或确认不可修**。
4. gate 全过 → 写 metrics + `Final Result: Success`；确属不可修（题意矛盾、需越界改动）→ `issues.md` 记录 + `Final Result: Fail`。

## 4. 完成判据（CAV gate）

`Final Result: Success` 仅当：

- `mid/.c` 前后条件完整、无 verify 阶段注释、root 头裸名 include
- 通过 QCP well-formedness：`check_spec_wellformed == well_formed`
- 前条件排除所有 RTE/UB（审计写入 `issues.md`）
- `.v`（如有）definition-only 且 `coqc` 通过
- `issues.md` / `metrics.md` 写完

任一 gate 失败且不能在本阶段修复 → `Final Result: Fail`，并在 `logs/issues.md` 记：失败 gate 名（verify-stage annotation scan / input V definition-only scan / `check_spec_wellformed` / `coqc mid/.v`）、退出码、关键报错、本轮 `mid/.c`/`.v` 路径、下一轮修正点。runner 会用同组 contract syntax check 复核后才放行 eval/verify。

## 5. 带反馈重跑（统一 retry 机制）

由 `Critic findings:` 块（被 eval critic 拒）或 `Restart feedback` 块（被 runner syntax check 拒）任一触发。**这是带反馈的接力重跑，不是从零重做**：

- **先读再动**：读上一轮的 `logs/issues.md`、`logs/continue.md`（如有）、上一轮生成的 `mid/<dataset>/<name>.{c,v}`，定位到底哪条 finding / gate 失败。
- **continue.md 追加 section**（改文件之前）：在 `logs/continue.md` 末尾追加一段（**只追加不覆盖**）——上轮被拒的 finding / gate 原文、当前精确定位、本轮准备改哪几行、为什么这样改能修。
- **逐条修，保留已通过工作**：把每条 finding / gate 失败原因当 blocker 逐条修；只改与之相关处，**不扩散**到无关改动；保留上一轮已通过的 contract 部分。
- 在 `logs/issues.md` 追加逐条对照（finding/失败原文 1–2 行 + 当前状态 + 修复动作 + 结果）。
- 修完重新输出 `mid/<dataset>/<name>.{c,v}`，重跑对应 gate（§3/§4），直到通过或确认不可修。可继续推进的反馈 blocker 不能以 `Final Result: Fail` 收尾。

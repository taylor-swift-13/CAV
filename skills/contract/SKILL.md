---
name: contract
description: Contract skill，把原始题意 + C 实现整理成 verify 友好的 `input/<name>.c` / `.v`。
---

跨阶段共用规则（读写边界、效率、reasoning log、`Final Result` 格式）见 `skills/COMMON.md`。本文件只描述 contract-specific 内容。

任务开始读：`QualifiedCProgramming/README.md`、`QualifiedCProgramming/tutorial/`。其他 QCP 文档/例子卡住再按需读。

## 1. 输入

原始 C 实现、原始题意 / 自然语言描述、约束 / 边界 / 示例、可选辅助定义草稿。

## 2. 输出

- `input/<name>.c`（目标函数 + 完整 contract，**不含**任何 verify 阶段注释）
- `input/<name>.v`（仅当确实需要额外 Coq 定义；能不用就不用）
- `output/contract_<timestamp>_<name>/logs/reasoning.md`、`issues.md`、`metrics.md`

## 3. 硬规则

- **先写** `logs/reasoning.md`（语义、边界、内存与 Coq 依赖判断），**再写** `input/<name>.c`
- `input/<name>.c` 只包含目标函数 + 完整 contract；**不要**提前写 `Inv` / `Assert` / `which implies` / bridge / loop-exit assertion（那是 verify 阶段的事）
- `input/<name>.v` 只放题目专用 Coq 定义
- 保持原程序语义不变；必须改接口时，只做 verification-friendly 改写
- **规格优先用「量词 + 已定义函数」表达输入输出关系，而不是把实现重写一遍**。能用 stdlib / 已有谓词 / 已有函数(`Permutation`、`Znth`、`app`、`Zlength`、`join`/连接、`sorted` 等)+ `exists` / `forall` 刻画"输出和输入满足什么关系"时,就不要新写递归。**只有关系实在无法用现有部件 + 量词表达时,才退而写题目专用 `Fixpoint` / `Inductive`**。优先写**逆关系/特征性质**:如"按空格拆分→字符串数组",写成 `exists ps, join_sep(ps, ' ') == 输入 && (每段不含空格)`(用更简单的 `join` 逆向刻画),而不是定义一个 `split` 递归。
- `input/<dataset>/` 下的 C 文件引用公共验证头时，用**裸名直接 include**（头文件已复制到该 dataset 目录内）：
  ```c
  #include "verification_stdlib.h"
  #include "verification_list.h"
  #include "int_array_def.h"
  ```
  需要字符数组时同理 `#include "char_array_def.h"`。不要写 `../`、`../../` 或其它路径前缀。
- contract 设计要保证下游所有 VC 可证：指针解引用需要显式非空前提；后条件优先写蕴含关系，避免不必要的顶层析取。

## 4. 最短流程

1. 读原始题意和代码
2. 写 `logs/reasoning.md`（语义、边界、内存、Coq 依赖判断）
3. 生成 `input/<name>.c`
4. 判断是否真的需要 `input/<name>.v`，需要才写
5. 写 `logs/issues.md`、`logs/metrics.md`

写合同时**按需读**(不预读):选空间谓词、纯函数/语义部件(`Znth`/`Zlength`/max-min/Int 界/集合)优先看 `QualifiedCProgramming/tutorial/` 和 `QualifiedCProgramming/SeparationLogic/examples/`。

## 5. 完成判据

`logs/metrics.md` 写自判摘要即可；runner 会复核并覆盖最终 metrics。

`Final Result: Success` 仅当：

- `input/<name>.c` 前后条件完整、无 verify 阶段注释混入
- `input/<dataset>/<name>.c` 中 root 头文件 include 使用裸名 `<header>`（头文件与 .c 同目录）
- `input/<name>.c` 已通过 QCP well-formedness gate：`check_spec_wellformed == well_formed`，也就是 symexec 至少能解析 contract 并开始 symbolic execution
- `.v`（如有）只包含额外逻辑定义，不含 `Axiom` / `Hypothesis` / `Parameter` / `Conjecture` / `Variable` / `Admitted` / `admit` / `Abort` 等假设或占位，且必须能被 `coqc` 编译通过
- `reasoning.md` / `issues.md` / `metrics.md` 已写完

如果任一机器 gate 失败，必须写 `Final Result: Fail`，并在 `logs/issues.md` 中记录：

- 失败的 gate 名称（如 verify-stage annotation scan、input V definition-only scan、`check_spec_wellformed` 或 `coqc input/<name>.v`）
- 退出码
- 关键报错
- 本轮生成的 `input/<name>.c` / `.v` 路径
- 下一轮 contract 需要修正的具体点

Agent 自判成功后，runner 还会用同一组 contract syntax check 复核：检查 `input/<name>.c` 存在且无 verify 阶段 `Inv` / `Assert` / `which implies` 注释、root 头文件 include 为裸名 `<header>`、QCP wellformed、可选 `.v` definition-only 且能 `coqc`。只有 runner 复核通过，contract 阶段才允许进入 eval 或 verify。

## 6. 条件性 mode addendum

| Prompt 标记 | 含义 |
|------------|------|
| `Critic findings:` 块出现 | 上一轮 contract 被 eval critic 拒绝的 RE-RUN。把每条 critic finding 当 blocker，在 `logs/reasoning.md` 追加一段对照检查 + 修复说明；修完再重新输出 `input/<name>.{c,v}`。修复期间不要扩到与 finding 无关的改动。 |
| `Restart feedback` 块出现 | 上一轮 contract 被 runner syntax check 拒绝的重试。必须逐条修复反馈中的机器 gate 失败原因；修完后重新输出 `input/<name>.{c,v}`，并在 `logs/reasoning.md` / `logs/issues.md` 追加本轮修复说明。 |

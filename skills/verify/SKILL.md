---
name: verify
description: Verify skill，消费 Contract 输出完成注解、证明和编译检查。
---

Verify 在 QCP C 程序上完成 annotation + proof + compile，不修改 contract。

## 0. 职责

- 流程与 how-to 细节依照 QCP `.agents/skills/`：阶段编排看 `verification-orchestrator`；补注解看 `annotation-filling` + `annotation-checking`；证明 VC 看 `vc-proving`；编译收尾看 `final-check`。本 skill 只规定 CAV 工程约束。
- 不写过程 reasoning 日志。唯一文字产物是 `logs/issues.md` 和 `logs/metrics.md`。

## 1. 路径和边界

- 输入：`input/<dataset>/<name>.c`、可选 `input/<dataset>/<name>.v`，只读不改。
- 工作副本：`annotated/verify_<timestamp>_<name>.c`。
- workspace：`output/verify_<timestamp>_<name>/`，包含 `coq/generated/`、`logs/`、`original/`、最终 `annotated/` 快照。
- QCP mirror scratch：
  - C/header：`QualifiedCProgramming/QCP_examples/CAV/<workspace>/`
  - Coq：`QualifiedCProgramming/SeparationLogic/examples/CAV/<workspace>/`
  - 原始 `.v` bare import：`QualifiedCProgramming/SeparationLogic/_cav_original/<workspace>/`

**允许读**：QCP `.agents/skills/`、QCP 背景文档、参考例子 `QCP_examples/` / `SeparationLogic/examples/`，但不包括其它 CAV runner mirror workspace。

**禁止读**：`scripts/`、QCP 非白名单源码、其它 `output/` workspace、其它 QCP mirror workspace、自己的 `logs/agent_stdout_*.jsonl`、`git log` / `git show`、`symexec --help`。

**允许写**：当前 annotated C、当前 workspace 的 `coq/generated/<name>_proof_manual.v`、当前 workspace 的 `logs/*`、当前 workspace 对应的 QCP mirror scratch。

**禁止写**：`input/`、`scripts/`、其它 workspace、QCP 源码、其它 QCP mirror workspace、`coq/generated/*_goal.v` / `*_proof_auto.v` / `*_goal_check.v`。

公共验证头必须使用裸名 include，且保持原名，不得加路径前缀或改成题目私有名：

```c
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"
#include "char_array_def.h"
```

## 2. 权威资料

动手前先读 `QualifiedCProgramming/.agents/skills/verification-orchestrator/SKILL.md`，进入具体阶段前再读对应 QCP skill/docs。

| 阶段 | 权威来源 |
|---|---|
| annotation | `.agents/skills/annotation-filling/docs/`、`.agents/skills/annotation-checking/docs/`、`tutorial/` |
| symexec 刷新 | `.agents/skills/annotation-filling/docs/symexec-refresh.md` |
| proof | `.agents/skills/vc-proving/docs/`、参考例子 |
| final compile | `.agents/skills/final-check/docs/coq-compilation.md` + 当前 QCP mirror |

## 3. 工作循环

1. 参考 QCP 文档和相似例子，修改 `Inv` / `Assert` / `Inv Assert` / `which implies` / `where`。
2. 运行 symexec 生成 VC。若 symexec 失败或 VC 缺 annotation 中间事实，回到 annotation 修改。
3. 进入 proof 阶段后，只编辑 `proof_manual.v` 和允许的 local helper；若 proof 暴露 annotation 缺口，回到 annotation 阶段并重跑 symexec。
4. 若 QCP 官方流程判定没有 manual witness，不要编造证明工作，直接进入 final-check。
5. 每次 annotation 变更重跑 symexec 前，保存旧 `coq/generated/` 到 `coq/last/`，并复用旧 proof 结构；只编辑 proof 时不得重跑 symexec。

## 4. QCP 编译链路

正式成功判定只使用 QCP mirror audit，不在 `output/<workspace>/coq/generated` 下直接编译：

1. 将当前 annotated C 和公共头镜像到 `QualifiedCProgramming/QCP_examples/CAV/<workspace>/`。
2. 将当前 `proof_manual.v` 镜像到 `QualifiedCProgramming/SeparationLogic/examples/CAV/<workspace>/`。
3. 将 `input/<dataset>/*.v` 镜像到 `QualifiedCProgramming/SeparationLogic/_cav_original/<workspace>/`。
4. 在 QCP 根目录运行 symexec，`--coq-logic-path=SimpleC.EE.CAV.<workspace>`。
5. 从 `QualifiedCProgramming/SeparationLogic` 按顺序编译：
   `original deps -> goal -> proof_auto -> proof_manual -> goal_check`。
6. 成功后 runner 只复制最终四个 `.v` 到 workspace；不得把 `.vo/.glob/.aux` 复制回 `output/`。

不得手工改 generated import 前缀来适配本地 `output` load-path。

## 5. 退出条件

退出和成功的 phase 判定以 QCP `.agents/skills/verification-orchestrator/SKILL.md` 与 `.agents/skills/final-check/SKILL.md` 为准；

Verify 是长迭代任务。所有 annotation、symexec、proof、coqc、runner-audit blocker 都必须按 QCP orchestrator 继续推进，直到成功或 runner 从外部打断。

以下情况必须继续，禁止结束本轮、非零退出或写 `Final Result: Fail`：

- `proof_manual.v` 还有 theorem 没证完。
- `goal_check.v` 暴露 manual obligation。
- `symexec` 报 annotation 或资源错误。
- `coqc` 报 tactic、lemma、load-path 错误。
- 只定位到 blocker 或下一步修法。
- “证明没证出来”“Verification is not complete”“Work is not complete”。

只有一种情况允许写 `Final Result: Fail`： Contract 或原始 C/V 规格缺失、矛盾，必须回 Contract 阶段或用户决策。

全部满足才写 `Final Result: Success`：

- QCP final-check 成功。
- symexec 基于最新 annotated C 成功。
- `proof_manual.v` 无 `Admitted` / `admit` / `Abort` / 新增 `Axiom`。
- QCP mirror audit 编译通过 `original deps -> goal -> proof_auto -> proof_manual -> goal_check`。
- 未改原始 contract 或函数实现；annotated C 只新增验证注解；公共验证头使用裸名 include。
- `coq/generated/` 只保留最终 `.v` 产物，不保留编译中间文件。
- `logs/issues.md` 和 `logs/metrics.md` 已更新。

满足退出条件后，最后一行写裸的 `Final Result: Success` 或 `Final Result: Fail`。失败点仍可继续推进时，不得写最终结果，也不得只写 `agent_last_message` 后退出。

## 6. 日志

只维护 `logs/issues.md` 和 `logs/metrics.md`。

`logs/issues.md`：

- 退出前必须存在。若没有真正遇到 issue，写明 `No issues encountered.`。
- 只记录真正遇到的 issue：现象、定位、关键报错片段、最终解决方式或卡住原因。
- 写 `Final Result: Fail` 时，必须包含 `contract_or_original_spec_blocker`：失败 gate、退出码或 theorem/witness 名、关键报错、相关路径、contract 或原始 C/V 规格哪里缺失或矛盾，以及为什么必须回 Contract 阶段或用户决策。

`logs/metrics.md`：记录最终结果、attempt、耗时、agent/model、输入/输出路径和 runner audit 结果。

## 7. proof-only

`Mode: proof-only` 标记触发时，读取 `MODE_PROOF_ONLY.md`。该模式适用于 symexec 已跑过、仅补 `proof_manual.v` 的子场景；若 proof 暴露 annotation 缺口，按本文工作循环回到 annotation/symexec。

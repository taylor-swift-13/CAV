---
name: verify
description: Verify skill，消费 Contract 输出完成注解、证明和编译检查。
---

Verify 在 QCP C 程序上完成 annotation + proof + compile，不修改 function contract。
这里的 function contract 只指函数级 `Require` / `Ensure` 前后条件；loop invariant、`Assert`、`Inv Assert`、`which implies` 和 `where` 属于 verification annotation。

本 skill 自包含 Verify 阶段需要遵守的 CAV 规则。Verify 必须读取同型 QCP C/annotation 示例和对应 proof 示例；只读 `.agents/skills/*/reference-cases.md` 不够。

## 0. 职责

本 skill 只规定 CAV 工程约束。Annotation、symexec、proof、final-check 的具体 how-to 以 QCP `.agents/skills/` 为准。

规则：

- Agent 直接在 QCP 根目录启动，在当前 QCP mirror scratch 内工作。
- 唯一文字产物是当前 QCP mirror logs 中的 `issues.md` 和 `metrics.md`。
- 不写过程 reasoning 日志。

## 1. 路径和读写边界

路径：

- 输入：`input/<dataset>/<name>.c`、可选 `input/<dataset>/<name>.v`。
- Workspace：`output/verify_<timestamp>_<name>/`，runner-owned artifact collection。
- QCP C/header mirror：`QualifiedCProgramming/QCP_examples/CAV/<workspace>/`
- QCP Coq mirror：`QualifiedCProgramming/SeparationLogic/examples/CAV/<workspace>/`
- 原始 `.v` bare import deps：`QualifiedCProgramming/SeparationLogic/examples/CAV/<workspace>/deps/`
- QCP mirror logs：`QualifiedCProgramming/SeparationLogic/examples/CAV/<workspace>/logs/`

规则：

- 只读本 verify skill、QCP `.agents/skills/` 官方说明、本 skill 允许的官方示例/教程目录，以及当前 workspace 对应的 QCP mirror C/header、Coq、original spec deps 和 mirror logs。
- 只写当前 workspace 对应的 QCP mirror C/header、Coq 目录中除 `deps/` 外的文件，以及 mirror logs 中的 `issues.md` / `metrics.md`。
- 禁止修改 `output/`、repo-level `annotated/`、`input/`、原始 function contract、原始 C 实现、`scripts/`、repo-level `skills/`、QCP 源码或其它 workspace。
- 禁止读取 `output/`、repo-level `annotated/`、`input/`、`scripts/`、自己的 `agent_stdout_*.jsonl`、`git log` / `git show`。除官方示例/教程目录和当前 workspace 外，禁止读取其它 QCP mirror workspace。
- 禁止修改 `QualifiedCProgramming/SeparationLogic/examples/CAV/<workspace>/deps/` 中 staged 原始 `.v` 规格；若原始规格错误，只能走 `contract_program_mismatch_blocker`。

## 2. 权威资料

QCP `.agents/skills/` 是 annotation、symexec、proof 和 final-check 的权威资料。Runner prompt 提供当前 case 的 QCP mirror 路径、audit 脚本和 CAV 边界。

启动后先读取并遵守以下全部 QCP 官方 skill：

- `.agents/skills/verification-orchestrator/SKILL.md`
- `.agents/skills/annotation-filling/SKILL.md`
- `.agents/skills/annotation-checking/SKILL.md`
- `.agents/skills/vc-checking/SKILL.md`
- `.agents/skills/vc-proving/SKILL.md`
- `.agents/skills/final-check/SKILL.md`

同时必须读取相关 `docs/`，包括：

- `.agents/skills/annotation-filling/docs/annotation-rules.md` — C annotation 的语法、位置和基本写法规则。
- `.agents/skills/annotation-filling/docs/predicate-first-annotation.md` — 如何优先写数学性质谓词，避免把 C 算法镜像到 Rocq。
- `.agents/skills/annotation-filling/docs/common-annotation-errors.md` — 常见 annotation 错误、symexec 报错形态和修复方向。
- `.agents/skills/vc-proving/docs/` — proof tactic、witness 和分离逻辑证明套路。
- `.agents/skills/final-check/` — 最终 symexec/coqc/audit 检查链路。

| 阶段 | 资料 |
|---|---|
| orchestration | `verification-orchestrator` + prompt + 当前 QCP mirror |
| annotation | `annotation-filling` + `annotation-checking` + prompt + 当前 QCP mirror 的 staged C/header |
| symexec 刷新 | `verification-orchestrator` + `annotation-filling` + prompt + 当前 QCP mirror |
| proof 分诊 | `vc-checking` + prompt + 当前 QCP mirror 的 generated `.v` |
| proof 填写 | `vc-proving` + prompt + 当前 QCP mirror 的 generated `.v` |
| final compile | `final-check` + prompt + 当前 QCP mirror + `run_audit.sh` |

规则：

- 先读取上面列出的全部 QCP 官方 skill 和必读 `docs/`，再结合 runner prompt 和当前 QCP mirror 内容推进。
- 进入 annotation/proof 修改前，必须按本 skill 检索并读取具体相关示例：
  - C/annotation 示例来自 `QCP_examples/{Applications_human,LLM_bench,QCP_demos_human,QCP_demos_LLM}/`；
  - 对应证明来自 `SeparationLogic/examples/{Applications_human,LLM_bench,QCP_demos_human,QCP_demos_LLM}/`；
  - 相关教程来自 `tutorial/`；
  - CAV 历史同型 workspace 只能作为补充参考，不能替代上述官方示例源。
- 示例检索必须围绕当前失败点和题型关键词；实际读取的示例路径要记录到 `logs/issues.md` 或 `logs/metrics.md`。
- 按 runner prompt 给出的 QCP 阶段摘要推进 annotation、symexec、proof、final-check。
- `verification-orchestrator` 是端到端编排入口；其它 skill 按对应 phase 使用。
- 禁止用泛搜库源码或无关 demos 代替当前失败点驱动的 annotation/proof 修补。

## 3. Annotation 和 Symexec

工作循环：

1. 修改 annotation。
2. 运行 symexec 生成 VC。
3. 若 symexec 失败或 VC 缺 annotation 中间事实，回到 annotation 修改。

规则：

- Annotation 只新增或修改验证注解，不修改原始 C 实现。
- 公共验证头使用裸名 include，并保持原名：
  ```c
  #include "verification_stdlib.h"
  #include "verification_list.h"
  #include "int_array_def.h"
  #include "char_array_def.h"
  ```
- Annotation 变更后重跑 symexec。
- 重跑 symexec 前保存当前 generated `.v` 到当前 QCP mirror 的 `.tmp/` 或 runner prompt 指定位置，并复用旧 proof 结构。
- 禁止手改 `*_goal.v`、`*_proof_auto.v`、`*_goal_check.v`；这些文件只能由 symexec 生成。

## 4. Proof

工作循环：

1. 进入 proof 阶段后，补当前 QCP Coq mirror 中的 `<name>_proof_manual.v`。
2. 若 proof 暴露 annotation 缺口，回到 annotation 阶段并重跑 symexec。
3. 若 QCP 官方流程判定没有 manual witness，进入 final-check。

规则：

- 只改 `proof_manual.v` 时不重跑 symexec。
- 禁止证明或编辑 `proof_auto.v`；`Admitted` in `proof_auto.v` 是正常 QCP auto-proof 输出。
- 禁止在 `proof_manual.v` 中保留或新增 `Admitted` / `admit` / `Abort` / `Axiom`。
- 禁止改 VC 目标或导入绕过性 lemma。
- 禁止因普通 proof obligation、单个 theorem、tactic 失败、缺 lemma、耗时或模型不会证而退出。
- 退出前当前 QCP mirror 中必须有当前已填写的 `<name>_proof_manual.v`。

## 5. QCP 编译链路

正式成功判定只使用 runner 提供的 QCP mirror audit。

链路：

1. annotated C 和公共头位于 `QualifiedCProgramming/QCP_examples/CAV/<workspace>/`。
2. target Coq 文件位于 `QualifiedCProgramming/SeparationLogic/examples/CAV/<workspace>/`。
3. 原始 `.v` bare-import 依赖闭包位于 `QualifiedCProgramming/SeparationLogic/examples/CAV/<workspace>/deps/`。
4. symexec 使用 `--coq-logic-path=SimpleC.EE.CAV.<workspace>`。
5. QCP final-check 编译顺序是：
   `original deps -> goal -> proof_auto -> proof_manual -> goal_check`。
6. Runner 从 QCP mirror 收集 annotated C、`logs/issues.md`、`logs/metrics.md` 和最终四个 `.v`。

规则：

- 所有 symexec、coqc、final-check 都在当前 QCP mirror scratch 中完成。
- 以 runner 提供的当前 QCP mirror `run_audit.sh` 作为最终检查。
- 禁止在 `output/<workspace>/coq/generated` 下直接编译作为成功判定。
- 禁止手工改 generated import 前缀来适配本地 `output` load-path。
- 禁止 agent 复制产物；runner 负责复制回 output，且不复制 `.vo/.glob/.aux`。

## 6. 退出规则

规则：

- `run_audit.sh` 返回非零时不要退出；继续编辑 annotation/proof 并再次运行 audit。
- `run_audit.sh` 返回 0 后，维护 `logs/issues.md` 和 `logs/metrics.md`，最后一行写裸的 `Final Result: Success`。
- 只有确认 `contract_program_mismatch_blocker` 时，最后一行才写裸的 `Final Result: Fail`。
- `contract_program_mismatch_blocker` 指 Contract 与原始程序语义冲突，当前 case 必须回 Contract 阶段或用户决策，且无法通过 annotation/proof 修复。
- 禁止任何第三种最终状态。
- 写完 `issues.md` 或 `metrics.md` 不是退出理由；audit 非零就继续。
- 普通 annotation、symexec、coqc、proof、audit 失败都不是退出理由。

## 7. 日志规则

规则：

- `logs/issues.md` 记录真正遇到的 issue：现象、定位、关键报错片段、最终解决方式或卡住原因。
- audit 非零时可以持续更新 `logs/issues.md`，但更新后继续工作。
- 写 `Final Result: Fail` 时，`logs/issues.md` 必须包含 `contract_program_mismatch_blocker`：失败 gate、退出码或 theorem/witness 名、关键报错、相关路径、Contract 与程序语义哪里冲突、为什么无法通过 annotation/proof 修复且必须回 Contract/用户决策。
- `logs/metrics.md` 记录最终结果、attempt、耗时、agent/model、输入/输出路径和 runner audit 结果。
- 禁止在 mirror logs 下写 probe 文件、proof 备份或临时 Coq 文件；logs 只放 `issues.md` 和 `metrics.md`，临时 probe/备份放当前 Coq mirror 的 `.tmp/`。

## 8. proof-only

`Mode: proof-only` 标记触发时，读取 `MODE_PROOF_ONLY.md`。该模式适用于 symexec 已跑过、仅补 `proof_manual.v` 的子场景；若 proof 暴露 annotation 缺口，按本文工作循环回到 annotation/symexec。

规则：

- proof-only 模式下只补 `proof_manual.v` 和运行 proof/final-check 相关 audit。
- 若 proof-only 暴露 annotation 缺口，回到 annotation/symexec 工作循环。

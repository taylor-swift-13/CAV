---
name: verify
description: Verify skill，消费 Contract 输出完成注解、证明和编译检查。
---

Verify 在 QCP C 程序上做 annotation + proof + compile，**不重写 contract**。

## 职责划分（最重要，先读）

- **流程 + 一切 how-to 细节完全依照 QCP `.agents/skills/`**：阶段编排看 `verification-orchestrator`；补注解看 `annotation-filling` + `annotation-checking`；证 VC 看 `vc-proving`；编译收尾看 `final-check`。**照那边的流程和命令执行，本 skill 不复述、不自创。**
- **本 skill 只规定 CAV 这边的工程约束**：输入输出路径、读写边界、symexec/编译的 CAV override、产物清理、退出/结果契约、issues 记录、retry mode。这些约束**叠加在 QCP 流程之上**。
- **不写过程 reasoning 日志**（不再有 `annotation_reasoning.md` / `proof_reasoning.md`）。唯一文字产物是 `logs/issues.md`（只记真正遇到的 issue）和 `logs/metrics.md`（结果）。

## 1. 输入输出路径（CAV，固定）

- 输入：`input/<dataset>/<name>.c`、可选 `input/<dataset>/<name>.v`（只读，不改）
- 工作副本：`annotated/verify_<timestamp>_<name>.c`
- workspace：`output/verify_<timestamp>_<name>/`（含 `coq/generated/`、`logs/`、`original/`、最终 `annotated/` 快照）

脚本调用和手动执行必须用这同一组路径，不可发明新位置。

## 2. 读写边界（CAV，硬规则）

**读**（除自身 I/O 外，参考只在白名单内）：
- QCP 流程与细节：`QualifiedCProgramming/.agents/skills/`（全部子 skill 及其 `docs/`）——这是流程和细节的权威来源。
- 背景：`QualifiedCProgramming/README.md`、`SeparationLogic/README.md`、`tutorial/`。
- 例子：`QualifiedCProgramming/QCP_examples/` 和 `QualifiedCProgramming/SeparationLogic/examples/`。

**不要读**：`scripts/` 编排脚本、`QualifiedCProgramming/` 下除上面白名单外的库源码、其它 workspace（包括 `output/` 下其它 stage、其它时间戳、其它题目的 workspace）、自己的 `logs/agent_stdout_*.jsonl`、`git log`/`git show` 考古、`symexec --help` 之类反推命令。

**写**：当前 `annotated/...c`、当前 workspace 的 `coq/generated/<name>_proof_manual.v`（+ 必要本地 helper）、当前 workspace 的 `logs/*`。其余一律不写——包括 `input/`、`scripts/`、其它 workspace、QCP 源码。

**不手改** `*_goal.v` / `*_proof_auto.v` / `*_goal_check.v`（只能通过重跑 symexec 刷新）。

**`scripts/` 交互限制**：不读不写 `scripts/`。需要重跑 symexec 时只使用 runner 已给出的封装/命令，不为反推参数去读脚本源码。

**annotated 头文件硬规则**：公共验证头已**复制到 `annotated/` 目录下**，C 文件一律用**裸名直接 include**（不带任何路径）：

```c
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"
```

需要字符数组时同理 `#include "char_array_def.h"`。禁止 `../`、`../../` 或其它路径前缀；发现带路径前缀必须改回裸名再跑 symexec/compile。

## 3. 流程 = QCP `.agents`（用到就必须读，不要一次读完、也不要跳过）

主线先读 `QualifiedCProgramming/.agents/skills/verification-orchestrator/SKILL.md` 了解阶段编排，再按阶段去对应 skill。

**硬规则(read-before-act)**：每进入一个阶段、**动手之前**(补注解 / 重跑 symexec / 写 proof / 编译),**必须先读下表里该阶段对应的权威文档**——不能凭猜先做、不能跳过。没读对应文档就硬试导致的失败(尤其 proof tactic 乱试),不算"已尽力";必须**先补读对应文档再继续**,也不允许据此写 `Final Result: Fail`。

| 阶段 / 触发 | 权威来源（照搬命令与规则） | 取什么 |
|---|---|---|
| 补 annotation（`Require`/`Ensure`/`Inv`/`Assert`/`where`） | `.agents/skills/annotation-filling/docs/`（`annotation-rules.md`、`predicate-first-annotation.md`、`builtin-array-string-support.md` 数组/字符串必读、`array-predicate-selection.md` 数组问题）+ `tutorial/`（T2 前后条件、T3 `Inv`/`Assert`、T8 调用与 call-site `where`） | 注解语法与谓词选择 |
| spec 质量自检 | `.agents/skills/annotation-checking/docs/spec-quality-checklist.md` | spec 是否过弱/镜像算法 |
| 理解 symexec 生成物 / 刷新规则 | `.agents/skills/annotation-filling/docs/symexec-refresh.md` | symexec 命令语义、刷新后产物判断。CAV 重跑前先保留旧 generated 到 `coq/last`，重跑后参考旧 proof，不自动拼接 proof。 |
| 找相似题 / witness 结构 / proof pattern | `QCP_examples/` + `SeparationLogic/examples/`（按目录名/语义找完整已解例子） | 复用 proof/annotation pattern |
| 写 proof / 证 VC | `.agents/skills/vc-proving/docs/`（`separation-logic-whole-proof-tactics`、`use-notes`、`reference-cases`、`refinement-*`） | 分离逻辑 tactic、参考案例 |
| 编译 `goal/proof_auto/proof_manual/goal_check` | `.agents/skills/final-check/docs/coq-compilation.md` | **完整 coqc 命令 + 整套 `-R` load-path**（依赖序：lib → goal → proof_auto → proof_manual → goal_check）。**照抄整条命令**，不要删改 `-R` 项。 |

上表是常用索引、非穷举;**整棵 `.agents/skills/` 都可按需读**,遇到具体情况去对应 skill 的 `docs/` 翻:注解报错→`annotation-filling/docs/common-annotation-errors.md`、资源/内存回收报错→`qcp-resource-reclaim-errors.md`、VC 检查→`vc-checking/docs/`、收尾清 admit/调试残留→`final-check/docs/admitted-review-and-cleanup.md`。

**写 annotation/proof 的第一动作 = 找结构最相似的已验证例子(`QCP_examples/` + `SeparationLogic/examples/`,按语义/控制结构找),逐字照抄其 `Inv`/witness/proof 套路**——比读文档更关键,别自己发明证法;tactic 细节再看 `vc-proving/docs/`。同类错误连续失败 2 次→回去重找/重读例子,别盲改 tactic。没先吃透相似例子,不允许因证明/witness/tactic 失败写 `Final Result: Fail`。

**编译/symexec 报错**：load-path / 工具链由 infra 保证正确;确属本 workspace 改不了的 infra 问题,记 `logs/issues.md` 交回,不在本 workspace 硬改。

## 4. CAV override（叠加在 QCP 流程上，必须遵守）

QCP 流程怎么走照 §3，但下面几处用 CAV 的方式：

- **symexec 何时跑 / 重跑后怎么复用旧 proof**（symexec 命令语义、刷新后产物判断——见 §3 的 `symexec-refresh.md`，这里不复述）：
  - **何时**：初次生成；之后**只在 annotation（`Inv`/`Assert`/`which implies`/`where`/contract）变更后**重跑；只编辑 `proof_manual.v`、annotation 未变时**不要重跑**。
  - **重跑前保存参考**：每次重跑 symexec 前，必须把当前 `coq/generated/` 快照到当前 workspace 的 `coq/last/`；runner 的 `run_symexec` helper 会自动做这一步。不要使用自动拼接/keep-proofs 机制。
  - **重跑后复用 proof**：symexec 会重新生成新的 `coq/generated/<name>_proof_manual.v`，通常回到 `Admitted`。这时把 `coq/last/<name>_proof_manual.v` 当只读参考，按新 witness 目标手工迁移可复用的 proof 结构，避免从零重写；如果旧 witness statement 和新 witness statement 完全一致，对应证明可以从 `coq/last` 直接照抄。正式修改只写新的 `coq/generated/<name>_proof_manual.v`。重跑后以最新 witness 编号为准。
- **annotated 头文件裸名 include**（见 §2）。
- **每次 coqc 后清中间产物**：删 `coq/` 下非 `.v` 产物；并删本题 input `.v` 编译出的 `input/<dataset>/<name>.{vo,glob,vok,vos}` 和 `.<name>.aux`（只删本题的，parallel 安全）。
- 生成的 manual VC 语义不可证时**回 annotation**，不要硬写 proof；proof 里**禁止** `Admitted`/`admit`/`Abort`/新增 `Axiom`/改 VC 目标/导入 `derivable1` 绕过。
- 怀疑 VC 对**合法输入为假**（输入/契约缺陷）→ 记 `logs/issues.md`，停止 verify 交回 Contract/用户，不要在本 workspace 硬改 contract。

## 5. 退出 / 结果契约（CAV）

Verify 是长迭代任务。**不要**因为遇到一个可继续推进的 `symexec`/`coqc`/proof blocker 就结束。只要还在外层超时预算内、blocker 能在本 workspace 通过 annotation/proof edit 继续，就持续“改一处 → 跑对应 gate → 读第一个失败点 → 再改”。

只有以下情况才写 `Final Result: Fail` 退出：

- contract 或原始 C/V 规格缺失、矛盾，必须回 Contract 阶段或用户决策；
- 当前 generated VC 在现有 contract/annotation 下确实不可证，且已定位缺失前提或语义矛盾；
- 需要改写边界外的文件才能继续；
- 外部命令/agent run 已接近或触达 runner 超时；
- 已完成全部可行修复但确定性 gate 仍失败且无法在本 workspace 内推进。

普通的 `proof_manual_has_obligations`、单 theorem `coqc` 报错、symexec 具体 annotation 报错、tactic 失败、可修的 load-path 错误，**都不是退出理由**，是本轮继续工作的输入。

**全部满足才写 `Final Result: Success`**：

- symexec 基于最新 annotated 文件成功，生成最新 `goal/proof_auto/proof_manual/goal_check`
- `proof_manual.v` 无 `Admitted`/`admit`/`Abort`/新增 `Axiom`
- 四个 `.v` 全编译通过
- 没改原始 contract 或函数实现；annotated C 只新增验证注解；公共验证头裸名 include
- runner 能用当前 annotated C 重新 symexec，且 `goal/proof_auto/goal_check` 与现产物一致
- `coq/` 与 `input/` 中间产物已清理
- `logs/issues.md` 和 `logs/metrics.md` 已更新

满足退出条件后，写完 `logs/issues.md`（追加，详细记录踩坑）、`logs/metrics.md`（自判摘要），最后一行写**裸的** `Final Result: Success` 或 `Final Result: Fail`——整行就是这十几个字符，禁止 markdown 加粗、反引号、后缀（如 `(round N)`），否则外部判据误判。失败点仍可继续推进时不要写最终结果，继续迭代。

runner 会复核：生成文件存在、`proof_manual.v` 无未解占位、重编 `goal/proof_auto/proof_manual/goal_check`、确定性检查 input C/V 未改、annotated C 的 contract 与 executable implementation 未偏离原始 input、重新 symexec 对比 `goal/proof_auto/goal_check`。runner 复核通过才算成功。

## 6. issues 日志规范（CAV，唯一过程产物）

只维护 `logs/issues.md`（遇到的问题/踩坑），不写其它 reasoning 日志。`issues.md`：

- **只追加，不覆盖**
- 只记**真正遇到的 issue**：现象、定位（文件路径 + theorem/witness/行号）、关键代码或报错片段（C annotation / Coq theorem-subgoal-tactic / `coqc`-`symexec` 报错）、最终怎么解决或为什么卡住。顺利通过的步骤不记流水账。

写 `Final Result: Fail` 时，`issues.md` 必须含：失败 gate 名（如 symexec、manual proof obligation、`coqc goal_check.v`）、退出码或 theorem/witness 名、关键报错、当前 `annotated/...c` 与相关 `coq/generated/*.v` 路径、下一轮需修正的具体点。

## 7. 条件性 mode（runner 在 prompt 加标记触发，没标记就不读；可叠加）

### 7.1 带反馈重跑（统一 retry，内联）

由 `Attempt: N (retry…)`（N>1）/ `Restart feedback` 块 / `Audit findings:` 块 任一触发。**带反馈的接力重跑，不从零重做**：

- **先读再动**：读 `logs/continue.md`（如有）、`logs/issues.md`、`logs/agent_stderr_*.log`（上轮编译错误）、当前 `coq/generated/*.v`、当前 `annotated/verify_<timestamp>_<name>.c`，定位上轮 blocker。
- **改文件前在 `logs/continue.md` 末尾追加新 section**（禁覆盖/合并旧 section）：上轮卡在哪条 wit / tactic / 编译错误（文件路径 + theorem/witness 名 + 报错片段）、当前精确定位、本轮改哪几行、为什么这样改能修。
- **逐条修、复用已通过工作**（annotation 未变则 symexec 不重跑；annotation 变更必须重跑时，先把旧 `coq/generated/` 保存在 `coq/last/`，再参考 `coq/last/*_proof_manual.v` 迁移 proof，不整段从零重写）；定位到新 blocker 不算完成，必须立刻修它并重跑对应 gate，直到 §5 允许退出。
- `Restart feedback`：逐条修机器 gate 失败原因。`Audit findings:`：每条 finding 当 blocker 逐条对照修，在 `logs/issues.md` 追加逐条记录（finding 原文 1–2 行 + 当前状态 + 修复动作 + 结果），**禁止**残留 `assume` / 新增 `axiom` / `skipesc` / `nowarn` 等绕过。
- proof 类 blocker 改 proof 前必须按 §3 先**找/吃透最相似的已验证例子**(再看 vc-proving 文档),不要盲改 tactic。可继续推进的 retry blocker 不能以 `Final Result: Fail` 收尾。

### 7.2 proof-only 场景

`Mode: proof-only` 标记 → 读 `MODE_PROOF_ONLY.md`（loop-free + symexec 已跑过、仅补 `proof_manual.v` 的子场景）。

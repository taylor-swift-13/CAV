---
name: verify
description: Verify skill，消费 Contract 输出完成注解、证明和编译检查。
---

Verify 在 QCP C 程序上完成 annotation + proof + compile，**不重写 contract**。

## 0. 职责

- **流程与 how-to 细节依照 QCP `.agents/skills/`**：阶段编排看 `verification-orchestrator`；补注解看 `annotation-filling` + `annotation-checking`；证明 VC 看 `vc-proving`；编译收尾看 `final-check`。本 skill 不复述 QCP 细节，不自创流程。
- **本 skill 只规定 CAV 工程约束**：输入输出路径、读写边界、两层工作循环、symexec/编译规则、产物清理、退出条件、issues 记录和 retry mode。
- **不写过程 reasoning 日志**：不再写 `annotation_reasoning.md` / `proof_reasoning.md`。唯一文字产物是 `logs/issues.md`（只记真正遇到的 issue）和 `logs/metrics.md`（结果）。

## 1. 路径

- 输入：`input/<dataset>/<name>.c`、可选 `input/<dataset>/<name>.v`（只读，不改）。
- 工作副本：`annotated/verify_<timestamp>_<name>.c`。
- workspace：`output/verify_<timestamp>_<name>/`，包含 `coq/generated/`、`logs/`、`original/`、最终 `annotated/` 快照。

脚本调用和手动执行必须使用这组路径，不得发明新位置。

## 2. 读写边界

**允许读**：
- QCP 流程与细节：`QualifiedCProgramming/.agents/skills/`（全部子 skill 及其 `docs/`）。
- 背景资料：`QualifiedCProgramming/README.md`、`SeparationLogic/README.md`、`tutorial/`。
- 参考例子：`QualifiedCProgramming/QCP_examples/`、`QualifiedCProgramming/SeparationLogic/examples/`。

**禁止读**：
- `scripts/` 编排脚本。
- `QualifiedCProgramming/` 下除上面白名单外的库源码。
- 其它 workspace，包括 `output/` 下其它 stage、其它时间戳、其它题目的 workspace。
- 自己的 `logs/agent_stdout_*.jsonl`、`git log` / `git show` 考古、`symexec --help` 等反推命令。

**允许写**：
- 当前 `annotated/verify_<timestamp>_<name>.c`。
- 当前 workspace 的 `coq/generated/<name>_proof_manual.v`（及必要本地 helper）。
- 当前 workspace 的 `logs/*`。

**禁止写**：
- `input/`、`scripts/`、其它 workspace、QCP 源码。
- `coq/generated/*_goal.v`、`*_proof_auto.v`、`*_goal_check.v`。这些文件只能通过重跑 symexec 刷新。

**annotated 头文件规则**：公共验证头已复制到 `annotated/` 目录下，C 文件必须使用裸名 include，不得带路径前缀。

```c
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"
#include "char_array_def.h"
```

发现 `../`、`../../` 或其它路径前缀时，必须改回裸名再跑 symexec/compile。

## 3. 权威资料

主线先读 `QualifiedCProgramming/.agents/skills/verification-orchestrator/SKILL.md` 理解阶段编排，再按阶段读对应资料。每进入一个阶段、动手之前，必须先读该阶段的权威文档；没读文档导致的失败不算已尽力，也不得据此写 `Final Result: Fail`。

| 阶段 / 触发 | 权威来源 | 取什么 |
|---|---|---|
| 补 annotation（`Require`/`Ensure`/`Inv`/`Assert`/`where`） | `.agents/skills/annotation-filling/docs/`（`annotation-rules.md`、`predicate-first-annotation.md`、`builtin-array-string-support.md`、`array-predicate-selection.md`）+ `tutorial/` | 注解语法、谓词选择、循环/调用规则 |
| spec 质量自检 | `.agents/skills/annotation-checking/docs/spec-quality-checklist.md` | spec 是否过弱或镜像算法 |
| symexec 生成物 / 刷新规则 | `.agents/skills/annotation-filling/docs/symexec-refresh.md` | symexec 命令语义、刷新后产物判断 |
| 相似题 / witness / proof pattern | `QCP_examples/` + `SeparationLogic/examples/` | 复用 annotation/proof 结构 |
| 写 proof / 证 VC | `.agents/skills/vc-proving/docs/`（`separation-logic-whole-proof-tactics`、`use-notes`、`reference-cases`、`refinement-*`） | 分离逻辑 tactic、参考案例 |
| 编译 `goal/proof_auto/proof_manual/goal_check` | `.agents/skills/final-check/docs/coq-compilation.md` | 完整 `coqc` 命令和整套 `-R` load-path |

上表是常用索引，不是穷举。遇到具体问题时按需读 `.agents/skills/` 下对应文档，例如 annotation 报错、资源回收报错、VC 检查、admit 清理等。

## 4. 工作循环

### 4.1 verify 外层主循环

verify 阶段按以下外层循环推进：

`检索相似例子/阅读必要文档 → 修改 Inv / Assert / Inv Assert / which implies / where → 运行 symexec 生成 VC → 进入 proof 阶段主循环`

若 symexec 不能生成完整、可进入证明阶段的 VC，或生成的 VC 明确缺少 annotation 中间事实，则回到参考检索/文档阅读与 annotation 修改环节，修正后重新运行 symexec。不得在尚未获得有效 VC 时进入 proof 阶段，也不得在 symexec 失败可由 annotation 修改推进时写 `Final Result: Fail`。

### 4.2 proof 阶段主循环

进入 proof 阶段后，按以下内层循环推进：

`检索相似例子/阅读必要文档 → 修改 proof_manual.v → 编译 → 阅读第一个失败点`

每轮检索必须服务于当前编译或 witness 失败点，检索后必须回到证明构造与编译验证。若 proof 过程中确认当前 VC 在现有 annotation 下不可证，或编译失败表明 VC 缺少必要中间事实，且该事实可通过加强或修正 `Inv` / `Assert` / `Inv Assert` / `which implies` / `where` 表达，则必须退出 proof 循环，回到外层“写 annotation”阶段，修改 annotation 后重跑 symexec 刷新 VC，再重新进入 proof 阶段主循环。

仅在确认问题不能通过允许范围内的 annotation/proof 修改推进时，才按 §6 的失败条件处理。

## 5. 规则

### 5.1 必须遵守

- 必须使用固定路径：输入为 `input/<dataset>/<name>.c` 和可选 `.v`，工作副本为 `annotated/verify_<timestamp>_<name>.c`，workspace 为 `output/verify_<timestamp>_<name>/`。
- 必须先读 QCP `.agents/skills/verification-orchestrator/SKILL.md`，并在进入 annotation、symexec、proof、final compile 等阶段前读取对应权威文档。
- 必须在 proof 中发现当前 VC 依赖缺失 annotation 中间事实时，退出 proof 循环，回到外层写 annotation 阶段，重跑 symexec 后再进入 proof。
- 必须只在当前 workspace 写 `annotated/...c`、`coq/generated/<name>_proof_manual.v` 和 `logs/*`。
- 必须在重跑 symexec 前保留当前 `coq/generated/` 到 `coq/last/`，并在重跑后按新 witness 手工迁移可复用 proof。
- 必须使用裸名 include 公共验证头；发现带路径 include 必须修正。
- 必须在每次 `coqc` 后清理 `coq/` `original/` 和本题 `input/<dataset>/<name>.v` 产生的编译中间产物。
- 必须只在 annotation（`Inv` / `Assert` / `which implies` / `where` / contract）变更后重跑 symexec；只编辑 `proof_manual.v`、annotation 未变时不得重跑。
- 必须将 `coq/last/<name>_proof_manual.v` 作为重跑后的只读 proof 参考，按新 witness 目标手工迁移可复用结构；旧新 witness statement 完全一致时可直接照抄对应证明。
- 必须在满足所有成功判据后才写裸行 `Final Result: Success`；失败也必须只在满足失败条件后写裸行 `Final Result: Fail`。

### 5.2 必须禁止

- 禁止重写 contract、原始函数实现或原始 `input/` 文件。
- 禁止读取或修改 `scripts/`、其它 workspace、QCP 非白名单源码、`git log` / `git show` 考古、自己的 `logs/agent_stdout_*.jsonl`，以及通过 `symexec --help` 等方式反推脚本参数。
- 禁止手改 `coq/generated/*_goal.v`、`*_proof_auto.v`、`*_goal_check.v`；这些文件只能由 symexec 生成。
- 禁止在 `proof_manual.v` 中保留或新增 `Admitted` / `admit` / `Abort` / `Axiom`，禁止改 VC 目标或导入 `derivable1` 等绕过方式。
- 禁止以连续泛搜 demos、库源码或 lemma 代替 annotation/proof 构造；除非当前报错明确指向缺失 lemma，否则不得扩大检索范围。
- 禁止在尚未获得有效 VC 时进入 proof 阶段。
- 禁止在 symexec/proof/coqc blocker 仍可通过允许范围内的 annotation/proof 修改推进时写 `Final Result: Fail`。
- 禁止在只编辑 `proof_manual.v` 且 annotation 未变化时重跑 symexec。
- 禁止修改边界外文件以修复当前 workspace 的问题；确属 contract、输入规格或 infra 问题时，只记录 issue 并交回。
- 禁止在本 workspace 硬改 contract、脚本或 QCP 源码处理 contract 缺陷或 infra 问题；此类问题只能记录 `logs/issues.md` 并交回。

## 6. 退出条件

Verify 是长迭代任务。遇到可继续推进的 `symexec` / `coqc` / proof blocker 时，不得结束；应持续“改一处 → 跑对应 gate → 读第一个失败点 → 再改”，直到成功、确认无法推进或外部超时。

**只有以下情况才写 `Final Result: Fail`**：

- contract 或原始 C/V 规格缺失、矛盾，必须回 Contract 阶段或用户决策。
- 当前 generated VC 已确认不能通过加强/修正 `Inv` / `Assert` / `Inv Assert` / `which implies` / `where` 推进，且问题来自 contract 或原始 C/V 规格本身不可证、缺失前提或语义矛盾。
- 需要改写边界外文件才能继续。
- 外部命令/agent run 已接近或触达 runner 超时。
- 已完成全部可行修复，但确定性 gate 仍失败且无法在本 workspace 内继续推进。

普通的 `proof_manual_has_obligations`、单 theorem `coqc` 报错、symexec annotation 报错、tactic 失败、可修的 load-path 错误，都不是退出理由，而是本轮继续工作的输入。

**全部满足才写 `Final Result: Success`**：

- symexec 基于最新 annotated 文件成功，生成最新 `goal/proof_auto/proof_manual/goal_check`。
- `proof_manual.v` 无 `Admitted` / `admit` / `Abort` / 新增 `Axiom`。
- 四个 `.v` 全部编译通过。
- 未改原始 contract 或函数实现；annotated C 只新增验证注解；公共验证头使用裸名 include。
- runner 能用当前 annotated C 重新 symexec，且 `goal/proof_auto/goal_check` 与现产物一致。
- `coq/` 与 `input/` 中间产物已清理。
- `logs/issues.md` 和 `logs/metrics.md` 已更新。

满足退出条件后，写完 `logs/issues.md` 和 `logs/metrics.md`，最后一行写裸的 `Final Result: Success` 或 `Final Result: Fail`。整行不得加 markdown、反引号或后缀，否则外部判据会误判。失败点仍可继续推进时，不得写最终结果。

runner 会复核：生成文件存在、`proof_manual.v` 无未解占位、四个 Coq 文件可重编、input C/V 未改、annotated C 的 contract 与 executable implementation 未偏离原始 input、重新 symexec 后 `goal/proof_auto/goal_check` 一致。runner 复核通过才算成功。

## 7. 日志

只维护 `logs/issues.md` 和 `logs/metrics.md`。

`logs/issues.md`：
- 只追加，不覆盖。
- 只记录真正遇到的 issue：现象、定位（文件路径 + theorem/witness/行号）、关键代码或报错片段（C annotation / Coq theorem-subgoal-tactic / `coqc` / `symexec` 报错）、最终解决方式或卡住原因。
- 顺利通过的步骤不记流水账。
- 写 `Final Result: Fail` 时，必须包含失败 gate 名、退出码或 theorem/witness 名、关键报错、当前 `annotated/...c` 与相关 `coq/generated/*.v` 路径、下一轮需修正的具体点。

## 8. Retry 和 Mode

### 8.1 带反馈重跑

由 `Attempt: N (retry...)`（N > 1）、`Restart feedback` 块或 `Audit findings:` 块触发。带反馈重跑不从零重做。

- 先读 `logs/continue.md`（如有）、`logs/issues.md`、`logs/agent_stderr_*.log`、当前 `coq/generated/*.v`、当前 `annotated/verify_<timestamp>_<name>.c`，定位上轮 blocker。
- 改文件前在 `logs/continue.md` 末尾追加新 section，记录上轮卡在哪条 witness/tactic/编译错误、当前定位、本轮改哪些行、为什么能修。
- 逐条修复反馈。annotation 未变则不重跑 symexec；annotation 变更必须重跑时，先保存旧 `coq/generated/` 到 `coq/last/`，再参考 `coq/last/*_proof_manual.v` 迁移 proof。
- 定位到新 blocker 不算完成，必须继续按 §4 的循环推进，直到 §6 允许退出。
- `Audit findings:` 每条 finding 都作为 blocker 处理，并在 `logs/issues.md` 追加记录原文摘要、当前状态、修复动作和结果。禁止残留 `assume` / 新增 `axiom` / `skipesc` / `nowarn` 等绕过。
- proof 类 blocker 必须按 §4 的错误驱动策略检索并分析最相近例子，随后立即修改 `proof_manual.v` 并重跑 gate；不得以泛搜参考代替 proof 构造。

### 8.2 proof-only

`Mode: proof-only` 标记触发时，读取 `MODE_PROOF_ONLY.md`。该模式适用于 symexec 已跑过、仅补 `proof_manual.v` 的子场景；若 proof 暴露 annotation 缺口，按本文 §4 回到外层 annotation/symexec 循环。

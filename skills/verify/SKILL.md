---
name: verify
description: Verify skill，消费 Contract 输出完成注解、证明和编译检查。
---

Verify 消费 Contract 已经准备好的输入做 annotation + proof + compile，**不重写 contract**。所有 reasoning / issues 日志必须独立可读：现象 + 定位（文件/theorem/witness） + 修复动作 + 关键 C/Coq/报错片段 + 为什么这样改。

## 0. 退出纪律

Verify 是长迭代任务。**不要**因为遇到一个可继续推进的 `symexec` / `coqc` / proof blocker 就结束当前 agent run。只要还在当前外层超时预算内，并且 blocker 可以通过本 workspace 的 annotation / proof edit 继续尝试，就必须继续执行“改一处 -> 跑对应 gate -> 读第一个失败点 -> 再改”的循环。

只有以下情况才能写 `Final Result: Fail` 并退出：

- contract 或原始 C/V 规格缺失、矛盾，必须回到 Contract 阶段或用户决策；
- 当前 generated VC 在现有 contract/annotation 下确实不可证，且已经定位到缺失的前提或语义矛盾；
- 需要修改写边界外的文件才能继续；
- 外部命令或 agent run 已经接近/触达 runner 超时，无法再完成一次有意义的编辑和 gate；
- 已经完成全部可行修复但确定性 runner gate 仍失败，且失败原因不再能在当前 workspace 内推进。

普通的 `proof_manual_has_obligations`、单个 theorem 的 `coqc` 报错、`symexec` 的具体 annotation 报错、tactic 失败、load-path 可修复错误，都不是退出理由；这些是本轮继续工作的输入。

## 0.1 检索纪律

Verify 不能只靠局部猜 tactic 硬顶。进入 manual proof 后，必须先**直接到仓库里找相似的已解例子**，并把结果写入 `logs/proof_reasoning.md`：

- 先看 `QualifiedCProgramming/SeparationLogic/examples/`：按目录名/语义找最接近当前题的完整例子；命中就展开相关 `.v` / `.c` / 报告文件，比对 witness 结构 / proof pattern。
- 直接按文件名、目录名、相关 `.c`/`.v` 内容和 verification report 搜索 QCP examples。

同一个 theorem 或同一类 `coqc` 错误连续失败 2 次后，必须再回去找例子。检索记录至少包含：

- 实际展开阅读的候选路径；
- 复用到的 proof / annotation pattern，或说明为什么候选不适用。

没有检索记录时，不允许因为 `proof_manual_has_obligations`、`Cannot find witness`、rewrite/unification 失败、`entailer!`/`lia` 失败写 `Final Result: Fail`。这些错误必须先去找相似例子，再继续证明。

## 1. 路径约定

- 输入：`input/<name>.c`、可选 `input/<name>.v`
- 工作副本：`annotated/verify_<timestamp>_<name>.c`
- workspace：`output/verify_<timestamp>_<name>/`（含 `coq/generated/`、`logs/`、`original/`）

脚本调用和手动执行必须用这同一组路径，不可发明新位置。

## 2. 读写边界

**读**（除自身 I/O 外，参考只能在白名单内）：`QualifiedCProgramming/README.md`、`QualifiedCProgramming/SeparationLogic/README.md`、`QualifiedCProgramming/tutorial/`、`QualifiedCProgramming/SeparationLogic/examples/`。

**不要**：`symexec --help` 之类的命令反推、读 `scripts/` 编排脚本、读 `QualifiedCProgramming/` 下除 README、`tutorial/`、`SeparationLogic/README.md`、`SeparationLogic/examples/` 外的库源码、读自己的 `logs/agent_stdout_*.jsonl`、`git log` / `git show` 考古。

**写**：当前 `annotated/...c`、当前 workspace 的 `coq/generated/<name>_proof_manual.v` + 必要本地 helper、当前 workspace 的 `logs/*`。其余一律不写——包括 `input/`、`scripts/`、其它 workspace、QCP 源码。

**不手改** `*_goal.v` / `*_proof_auto.v` / `*_goal_check.v`。

**annotated 头文件硬规则**：公共验证头已**复制到 `annotated/` 目录下**，C 文件一律用**裸名直接 include**（不带任何路径）：

```c
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"
```

需要字符数组时同理 `#include "char_array_def.h"`。禁止写 `../`、`../../` 或其它路径前缀；发现带路径前缀必须改回裸名再跑 symexec/compile。

## 3. 分步读 QCP 文档（按需读，不要一次读完）

- 任务开始：`QualifiedCProgramming/README.md`、`QualifiedCProgramming/SeparationLogic/README.md`
- 不知道 annotation / contract 基本写法 → `QualifiedCProgramming/tutorial/`
- 需要相似题思路 / witness 结构 / proof pattern → `QualifiedCProgramming/SeparationLogic/examples/`

下面这些**只在命中具体触发时才读**（按需,不预读）：

- 某 witness 反复证不出、怀疑 VC 对**合法输入为假**(可能是输入/契约缺陷) → 记录到 `logs/issues.md`，停止 verify 并交回 Contract/用户处理。

## 4. 主流程

1. 读 `input/<name>.{c,v}`，确认有基本规格。规格缺失或必须改 contract / 原始 C 时，**停止 verify**，记 `logs/issues.md`，找用户。
2. 需要相似题思路时，按 §0.1 直接到 `QualifiedCProgramming/SeparationLogic/examples/` 找已解例子（按目录名/语义找）。
3. 需要补 `Inv` / `Assert` 时：读 INV/ASSERTION，先 append `logs/annotation_reasoning.md`，再改 annotated 工作副本。loop invariant 写完整 `Inv Assert`；中间断言优先写完整 `Assert`，`which implies` 只做局部 bridge。生成的 manual VC 语义不可证时**回 annotation**，不要硬写 proof。无需注释就跳过这一步。
4. 跑 `symexec`（每改 annotation 必须重跑）。以最新 witness 编号为准，不要盲用旧 proof。
5. 看 `proof_manual.v`：
   - 若**没有需要手工证明的 theorem**（所有 witness 都在 `proof_auto.v` 的 `Admitted` 占位里）= trivial case，**直接跳 6**，不检索 retrieval/examples。
   - 否则先按 §0.1 到 `QualifiedCProgramming/SeparationLogic/examples/` 找相似例子，再写 proof，编译失败迭代；每轮先 append `logs/proof_reasoning.md` 再改 proof。手工 witness 逐个证、当前没证完不跳下一个。可补 helper lemma；**不准** `Admitted` / `admit` / `Abort` / 新增 `Axiom` / 改 VC 目标 / 导入 `derivable1` 绕过。
6. 编译 `goal` / `proof_auto` / `proof_manual` / `goal_check`。
7. 自检 source integrity / freshness：确认 `input/<name>.c` / 可选 `input/<name>.v` 没被改；确认 `annotated/verify_<timestamp>_<name>.c` 里的函数 contract 和 executable C implementation 与原始 input 一致，只新增验证注解；确认当前 Coq 产物来自最新 annotated C。
8. 清理 `coq/` 下非 `.v` 中间产物和 `input/` 下非 `.v`/`.c` 产物。
9. 只有满足 §0 的退出条件后，才写完 `logs/issues.md`（追加，详细记录所有踩坑）、`logs/metrics.md`（自判摘要即可），最后一行写裸的 `Final Result: Success` 或 `Final Result: Fail`——**整行就是这十几个字符**，禁止 markdown 加粗、反引号、后缀（如 `(round N)`），否则外部判据会误判未完成。若当前失败点仍可通过继续改 annotation/proof 推进，不要写最终结果，继续迭代。

## 5. 完成条件

`logs/metrics.md` 写自判摘要即可；runner 会复核并覆盖最终 metrics。

全部满足才能写 `Final Result: Success`：

- symexec 基于最新 annotated 文件成功，生成最新 `goal/proof_auto/proof_manual/goal_check`
- `proof_manual.v` 无 `Admitted` / `admit` / `Abort` / 新增 `Axiom`
- 四个 `.v` 文件全编译通过
- 没有修改原始 contract 或函数实现；annotated C 只新增验证注解
- `annotated/...c` 中公共验证头一律裸名 include（`#include "verification_stdlib.h"` 等，头文件已在 `annotated/` 目录内），不得带 `../` 等路径前缀
- runner 能用当前 annotated C 重新 symexec，并确认 `goal/proof_auto/goal_check` 与当前产物一致
- `coq/` 与 `input/` 中间产物已清理
- `logs/issues.md` 和 `logs/metrics.md` 已完整更新

如果任一机器 gate 失败，先按 §0 判断能否继续推进。能继续推进时，记录到对应 reasoning 日志并继续迭代，**不要**写 `Final Result: Fail`。只有满足 §0 的退出条件时，才写 `Final Result: Fail`，并在 `logs/issues.md` 中记录：

- 失败的 gate 名称（如 symexec、manual proof obligation、`coqc goal_check.v`）
- 退出码或 theorem/witness 名称
- 关键报错
- 当前 `annotated/...c` 和相关 `coq/generated/*.v` 路径
- 下一轮 verify 需要修正的具体点

Agent 自判成功后，runner 还会复核：检查生成文件存在、`proof_manual.v` 无未解占位、重新编译 `goal/proof_auto/proof_manual/goal_check`，确定性检查 input C/V 未被修改、annotated C 的 contract 和 executable implementation 未偏离原始 input，并记录当前 annotated C hash 后重新 symexec 对比 `goal/proof_auto/goal_check`。只有 runner 复核通过，verify 阶段才算成功。

## 6. Reasoning 日志规范（共用）

`annotation_reasoning.md` / `proof_reasoning.md` / `issues.md` / `continue.md` 共同遵守：

- **只追加，不覆盖**
- 每段独立可读：现象、定位（文件路径 + theorem / witness / 行号）、修复动作、关键代码或日志片段（C annotation / Coq theorem-subgoal-tactic / `coqc`-`symexec` 报错）、**为什么这样改**。不准只写「尝试证明失败」「修改了 invariant」这类笼统话。
- 每轮迭代前贴出新一轮的片段，不只贴最后一版

## 7. 条件性 mode addendum

runner 在 prompt 加标记触发以下附录，**没标记就不读**。多个标记可叠加。

| Prompt 标记 | 附录文件 | 含义 |
|------------|---------|------|
| `Attempt: N (retry — ...)` 且 N > 1 | `MODE_RETRY.md` | 接力上一轮工作，必须追加 `logs/continue.md` 新 section |
| `Restart feedback` 块 | `MODE_RETRY.md` | runner audit check 反馈后的内部重试，逐条修复 feedback |
| `Mode: proof-only` | `MODE_PROOF_ONLY.md` | loop-free + symexec 已跑过、仅补 `proof_manual.v` 的子场景 |

---
name: contract
description: Contract skill，把原始题意 + C 实现整理成 verify 友好的 `mid/<dataset>/<name>.c` / `.v`。
---

Contract 把原始题意 + C 实现整理成 verify 友好的入口/出口 function contract，不写 verify 阶段 annotation。
本文中的 function contract 只指函数级 `Require` / `Ensure` 前后条件，不包含 `Inv`、`Assert`、`Inv Assert`、`which implies`、`where` 或任何 loop invariant。

本 skill 自包含 Contract 阶段需要遵守的 CAV 规则。Contract 必须读取同型 function contract / annotation 示例和 `tutorial/` 中相关教程；Contract 不用看证明，不读取 `*_proof_manual.v` / `*_proof_auto.v` / `*_goal.v` / `*_goal_check.v`。

## 0. 职责

- spec 写法、谓词选择、spec 质量判定以本 skill 的 Contract 规则和当前任务语义为主。只有缺少 QCP annotation 语法、内置 predicate 或 spec-quality 细节时，才最小读取相关 QCP skill 文档；可选路径见 §1。
- 本 skill 只规定 CAV 工程约束、产物、gate、退出和日志。
- 唯一文字产物是 `logs/issues.md` 和 `logs/metrics.md`。
- 必须按本 skill 的示例检索规则读取具体相关示例；只读 `reference-cases.md` 不够。

## 1. 路径和边界

- 输入：原始 C 实现 + 题意 / 约束 / 边界 / 示例。
- 输出：`mid/<dataset>/<name>.c`；仅在确需额外 Coq 定义时写 `mid/<dataset>/<name>.v`。
- `input/` 只读，contract 阶段不写。
- 只读当前任务 prompt 列出的输入/输出路径、本 skill、§3 列出的相关示例目录和 `tutorial/`；确实需要 QCP 语法或 spec-quality 细节时，才最小读取相关 QCP skill 文档。
- QCP skill 文档路径只作为可选参考，不要求启动时读取；Contract 阶段常用路径：
  - `QualifiedCProgramming/.agents/skills/annotation-filling/SKILL.md`
  - `QualifiedCProgramming/.agents/skills/annotation-filling/docs/annotation-rules.md`
  - `QualifiedCProgramming/.agents/skills/annotation-filling/docs/predicate-first-annotation.md`
  - `QualifiedCProgramming/.agents/skills/annotation-checking/SKILL.md`
  - `QualifiedCProgramming/.agents/skills/annotation-checking/docs/spec-quality-checklist.md`
- 禁止读取自己的 harness transcript 或 prompt 产物：`logs/agent_stdout_*.jsonl`、`logs/agent_prompt_*`、`logs/agent_stderr_*`、`logs/agent_last_message_*`。
- 禁止对仓库根或父目录做广搜：不要运行 `rg .`、`rg ..`、`find .`、`find ..`、`ls ..` 来探索；检索必须限定到本 skill 允许的具体 QCP 文档/示例目录或当前任务文件。
- 禁止读取 `../scripts/`、其它 `../skills/`、`../output/` 下其它 workspace、`../pipeline_results/`、git history 或未在 prompt 中列出的 repo-level 文件。
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
- 若 C annotation 中引入任何承载题目功能语义的外部 Coq 谓词（例如 `problem_*_spec`、`*_spec`、`*_pre`、`*_rel`、`*_model`），必须满足二选一：
  1. 该谓词在可见 companion `.v` 或已存在可读库中有 definition-only 定义，并且名称和参数与 C annotation 一致；
  2. 不使用该外部谓词，直接在 C function contract 中展开可评审的语义。
  禁止用只有 `Extern Coq` 声明、没有定义的 opaque predicate 承载功能语义。`check_spec_wellformed` 通过只说明语法/runner 可启动，不代表 spec-quality 合格。
- C 字符串用 `CharArray::full(p, n + 1, app(l, cons(0, nil)))` 时，`Require` / `Ensure` 必须同时保留 `Zlength(l) == n` 和中间非零约束：
  `(forall (k: Z), (0 <= k && k < n) => Znth(k, l, 0) != 0)`。
- 前条件必须排除所有 RTE/UB：空指针、数组越界、除零、非法移位、有符号整数溢出、`abs`/取负/累加/循环变元更新溢出等。审计结论写入 `logs/issues.md`。

## 3. 工作循环

1. 读题意和代码；若当前 contract 写法需要额外 QCP 语法/spec-quality 细节，最小读取相关 QCP skill 文档。
2. 按题型关键词检索并读取具体相关示例：`QCP_examples/{Applications_human,LLM_bench,QCP_demos_human,QCP_demos_LLM}/`。
3. 选择性读取 `tutorial/`。
4. 生成 `mid/<dataset>/<name>.c` 和必要的 `.v`。
5. 跑 runner gate：`check_spec_wellformed` / `.v` definition-only / `coqc mid/.v`。
6. gate 失败则读第一个报错，修改，重跑；不得通过改脚本、QCP 源码或 verify mirror 绕过。

## 4. 退出条件

退出和成功的 spec 判定以本文 Contract 规则、题意语义和 runner gate 为准。

全部满足才写 `Final Result: Success`：

- 入口/出口 function contract 按本文 spec-quality 要求判定合格。
- `mid/.c` 有完整入口/出口 function contract，且无 verify 阶段 annotation。
- 公共头裸名 include 且保持原名。
- 字符串相关 function contract 保留长度和中间 no-zero 约束。
- 前条件排除 RTE/UB，审计写入 `logs/issues.md`。
- `check_spec_wellformed == well_formed`。
- `.v` 如存在，definition-only 且 runner `coqc` gate 通过。
- `logs/issues.md` 和 `logs/metrics.md` 已更新。

只有确认题意、原始实现或所需 function contract 本身矛盾，必须用户/上游决策时，才写 `Final Result: Fail`。可通过修改 `mid/.c` / `.v` 修复的 gate 失败必须继续推进。

## 5. 日志

`logs/issues.md` 退出前必须存在。若没有真正 issue，写 `No issues encountered.`；否则记录 RTE/UB 审计、gate 失败、修复动作和结果。

`logs/metrics.md` 记录最终结果、耗时、输入/输出路径、agent/model、gate 结果和已读取的相关示例路径摘要。

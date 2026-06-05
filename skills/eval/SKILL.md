---
name: c-qcp-eval
description: Evaluate an existing C/QCP implementation by judging whether the contract fully characterizes the target behavior.
---

跨阶段共用规则（读写边界、效率、reasoning log、`Final Result` 格式）见 `skills/COMMON.md`。本文件只描述 eval-specific 内容。

按需读：`QualifiedCProgramming/README.md`、`QualifiedCProgramming/tutorial/`、`QualifiedCProgramming/SeparationLogic/examples/`。实现、contract 和 `.v` 文件作为只读语义目标。

阶段职责：eval 负责整体语义 judge，判断 spec 是否 sound / complete。contract runner 负责 QCP wellformed、companion `.v` 编译、verify 阶段注释检查和 `.v` 假设检查。eval 的 Coq 使用场景是本文件 §3 的 `compute_queries`，用于对具体闭式项做 `vm_compute`。

## 1. 输入

- 实现/规格 C 文件、可选 companion `.v`
- target function、workspace path、evaluation 目录

## 2. 输出

`output/eval_<timestamp>_<name>/` 下：

- `original/<name>.c`（+ `.v` 如有）
- `evaluation/evaluation.json`（可选，仅当需要结构化记录 judge/compute 依据）
- `logs/test_reasoning.md`、`logs/issues.md`、`logs/metrics.md`、`logs/final_result.md`
- agent 输出文件由 runner 自动放在 `logs/`

## 3. Optional Compute Queries

不要生成 positive/negative 测试用例，不要写 `cases/cases.json`，不要把 eval 成功条件建立在测试用例覆盖上。

如果某个判断可以归约到「具体闭式 Coq term `vm_compute` 求值」（典型：递归函数应用到字面量、复杂 list 操作的归一形式），把该计算任务 append 到 `evaluation/compute_queries.json`，由 runner 用 `vm_compute` 给出归一结果：

```json
{"queries": [
  {"id": "q1", "clause": "<clause text>",
   "coq_expr": "<closed Coq term of bool/Z/list/...>",
   "requires": ["Require Import ZArith.", "From SimpleC.EE Require Import ..."]}
]}
```

runner 会对每条 query 跑 `vm_compute` 并触发 finalize pass。这一轮先把相关判断标成 undecided；`Correct` verdict 需要所有 computable 判断都有决定性结果。

## 4. LLM Judge（写入 `logs/final_result.md`）

必须做整体 judge，判断 contract 是否真正刻画 raw 题目对应程序的完整输入输出关系。

逐项判断并在 `logs/final_result.md` 写出 `Pass` / `Fail` / `Inconclusive` 和一句依据：

- `Precondition strength`: 前条件是否过强，导致合法输入情况不能被刻画；最强错误形态是 `requires false`。
- `Precondition safety`: 前条件是否足以排除实现的运行时错误/未定义行为风险，例如除零、空指针解引用、数组越界、无效内存访问、会触发 C UB 的溢出或非法移位。
- `Postcondition strength`: 后条件是否过弱或 trivial，导致不能刻画程序行为；最弱错误形态是 `ensures true`。
- `Soundness`: 正确程序的所有输入输出是否都满足 spec。
- `Parameter coverage`: spec 是否约束了所有输入、输出和必要后状态参数。
- `Path coverage`: spec 是否覆盖程序所有路径/分支。
- `Completeness`: spec 是否完整刻画输入输出关系；任意满足 spec 的程序都应是这个问题的正确程序。

只有上面全部为 `Pass`，才能写：

```text
Judge verdict: Pass
```

任一项失败写 `Judge verdict: Fail`。无法判断写 `Judge verdict: Inconclusive`。

## 5. Aggregate verdict（写入 `logs/final_result.md`）

`Spec verdict:` 之一：

- `Correct` — contract sound + complete，且没有未消化的 undecided/compute query
- `Buggy` — contract 过强、过弱、unsound、incomplete，或遗漏关键输入/路径/后状态约束
- `Inconclusive` — 证据不足或仍有未消化的 compute query / undecided 判断

`logs/final_result.md` 必须同时包含：

```text
Spec verdict: Correct|Buggy|Inconclusive
Judge verdict: Pass|Fail|Inconclusive
```

## 6. Eval Integrity

- eval 产物只写入当前 eval workspace 的 `evaluation/` 和 `logs/`。
- 不生成测试用例，不写 `cases/`。
- `Correct` verdict 需要整体 judge 给出决定性通过依据。

## 7. 完成判据

`Final Result: Success` 只在以下条件全部满足时写：

- `logs/final_result.md` 是 `Spec verdict: Correct`
- `logs/final_result.md` 是 `Judge verdict: Pass`

`Spec verdict: Buggy`、`Spec verdict: Inconclusive`、`Judge verdict: Fail`、`Judge verdict: Inconclusive` 都对应 `Final Result: Fail`。

## 8. 条件性 mode addendum

| Prompt 标记 | 附录文件 | 含义 |
|------------|---------|------|
| `Compute results:` 路径出现 | `MODE_FINALIZE.md` | runner 跑完 compute_queries 后的 finalize pass，需把 vm_compute 的归一形折回 evaluation |

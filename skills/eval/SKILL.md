---
name: c-qcp-eval
description: Evaluate an existing C/QCP implementation against concrete positive/negative cases，把 contract 当语义目标。
---

跨阶段共用规则（读写边界、效率、experiences 只读、reasoning log、`Final Result` 格式）见 `skills/COMMON.md`。本文件只描述 eval-specific 内容。

按需读：`experiences/general/EVAL/README.md`、`experiences/general/AUDIT/README.md`、`experiences/general/CONTRACT/README.md`。实现、contract 和 `.v` 文件作为只读语义目标。

阶段职责：eval 负责 spec-test 和整体语义 judge，判断 spec 是否 sound / complete。contract runner 负责 QCP wellformed、companion `.v` 编译、verify 阶段注释检查和 `.v` 假设检查。eval 的 Coq 使用场景是本文件 §4.1 的 `compute_queries`，用于对具体闭式项做 `vm_compute`。

## 1. 输入

- 实现/规格 C 文件、可选 companion `.v`
- target function、workspace path、cases 数、evaluation 目录

## 2. 输出

`output/eval_<timestamp>_<name>/` 下：

- `original/<name>.c`（+ `.v` 如有）
- `cases/cases.json`、`evaluation/evaluation.json`
- `logs/test_reasoning.md`、`logs/issues.md`、`logs/metrics.md`、`logs/final_result.md`
- agent 输出文件由 runner 自动放在 `logs/`

## 3. Cases（写入 `cases/cases.json`）

按 prompt 要求的数量生成 positive + negative case。positive 满足每条 `Require`；negative 要么违反某条前条件、要么声称一个被 `Ensure` 拒绝的返回值 / 后状态。**偏向 adversarial 覆盖**：覆盖每个分支和每个后条件形状。

Schema：

```json
{
  "function_name": "abs_value",
  "positive": [
    {"id": "pos01", "description": "negative branch",
     "inputs": {"x": -3}, "result": 3, "post_state": {}}
  ],
  "negative": [
    {"id": "neg01_wrong_output", "kind": "postcondition",
     "description": "claims a wrong return value",
     "inputs": {"x": -3}, "result": -3, "post_state": {},
     "violated_clause": "__return >= 0"}
  ]
}
```

## 4. Spec-test（写入 `evaluation/evaluation.json`）

对每个 case 逐条 contract 子句机械代入；不能机械决定的，显式 reason 并记录原因。允许 verdict：`pass` / `fail` / `needs_judge`。`needs_judge` 必须附 `judge: {verdict, reason}`。

```json
{"cases": [{"id":"pos01","verdict":"pass","clauses":[{"clause":"__return >= 0","substituted":"3 >= 0","evaluated":true}]}]}
```

### 4.1 `needs_judge` 是可计算 Coq 项时，转 compute_queries

如果 `needs_judge` 子句的真伪可以归约到「对当前 case 的具体闭式 Coq term `vm_compute` 求值」（典型：递归函数应用到字面量、复杂 list 操作的归一形式），把该计算任务 append 到 `evaluation/compute_queries.json`，由 runner 用 `vm_compute` 给出归一结果：

```json
{"queries": [
  {"id": "pos03.c1", "clause": "<clause text>",
   "coq_expr": "<closed Coq term, all case values substituted, of bool/Z/list/...>",
   "requires": ["Require Import ZArith.", "From SimpleC.EE Require Import ..."]}
]}
```

runner 会对每条 query 跑 `vm_compute` 并触发 finalize pass。这一轮先把这些子句留作 `needs_judge`；`Correct` verdict 需要所有 computable 子句都有决定性结果。

## 5. LLM Judge（写入 `logs/final_result.md`）

spec-test 通过还不够。必须再做整体 judge，判断 contract 是否真正刻画 raw 题目对应程序的完整输入输出关系。

逐项判断并在 `logs/final_result.md` 写出 `Pass` / `Fail` / `Inconclusive` 和一句依据：

- `Precondition strength`: 前条件是否过强，导致合法输入情况不能被刻画；最强错误形态是 `requires false`。
- `Precondition safety`: 前条件是否足以排除实现的运行时错误/未定义行为风险，例如除零、空指针解引用、数组越界、无效内存访问、会触发 C UB 的溢出或非法移位。
- `Postcondition strength`: 后条件是否过弱或 trivial，导致不能刻画程序行为；最弱错误形态是 `ensures true`。
- `Soundness`: 正确程序的所有输入输出是否都满足 spec。
- `Positive coverage`: 所有正例是否都满足 spec。
- `Parameter coverage`: spec 是否约束了所有输入、输出和必要后状态参数。
- `Path coverage`: spec 是否覆盖程序所有路径/分支。
- `Negative rejection`: 负例是否都被 spec 拒绝。
- `Completeness`: spec 是否完整刻画输入输出关系；任意满足 spec 的程序都应是这个问题的正确程序。

只有上面全部为 `Pass`，才能写：

```text
Judge verdict: Pass
```

任一项失败写 `Judge verdict: Fail`。无法判断写 `Judge verdict: Inconclusive`。

## 6. Aggregate verdict（写入 `logs/final_result.md`）

`Spec verdict:` 之一：

- `Correct` — 每个 positive 都 pass、每个 negative 都 fail、没有 undecided
- `Buggy` — 至少一个 positive fail，或至少一个 negative pass
- `Inconclusive` — 任何子句/case 没有 decisive 结果（含未消化的 `needs_judge`）

`logs/final_result.md` 必须同时包含：

```text
Spec verdict: Correct|Buggy|Inconclusive
Judge verdict: Pass|Fail|Inconclusive
```

## 7. Eval Integrity

- eval 产物只写入当前 eval workspace 的 `cases/`、`evaluation/` 和 `logs/`。
- negative case 表示具体被拒绝的输入或错误声称的输出/后状态。
- `Correct` verdict 需要 spec-test 和 LLM judge 都给出决定性通过依据。
- 经验沉淀属于末尾 consolidate 阶段。

## 8. 完成判据

`Final Result: Success` 只在以下条件全部满足时写：

- 生成了请求数量的 positive + negative case
- `evaluation/evaluation.json` 存在且覆盖每个 case（含每个 case 的所有 clause）
- `logs/final_result.md` 是 `Spec verdict: Correct`
- `logs/final_result.md` 是 `Judge verdict: Pass`

`Spec verdict: Buggy`、`Spec verdict: Inconclusive`、`Judge verdict: Fail`、`Judge verdict: Inconclusive` 都对应 `Final Result: Fail`。

## 9. 条件性 mode addendum

| Prompt 标记 | 附录文件 | 含义 |
|------------|---------|------|
| `Compute results:` 路径出现 | `MODE_FINALIZE.md` | runner 跑完 compute_queries 后的 finalize pass，需把 vm_compute 的归一形折回 evaluation |

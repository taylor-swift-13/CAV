---
name: c-qcp-eval
description: Evaluate an existing C/QCP implementation by judging whether the contract fully characterizes the target behavior.
---

Eval 做整体 judge：contract 是否真正、完整刻画目标程序的输入输出关系（sound + complete）。

## 职责划分（先读）

- **spec 质量判据的细则完全依照 QCP `.agents/skills/annotation-checking/docs/spec-quality-checklist.md`**（前条件强度/安全、后条件强度、soundness、coverage、completeness 的判定口径）。照那边判，本 skill 不复述。**read-before-act：judge 之前必须先读这份 checklist 再下判定,不能凭印象。**
- **本 skill 只管 CAV 这边**：输入输出、judge/verdict 产物格式、issues。
- **唯一文字产物 = `logs/issues.md` + `logs/metrics.md` + `logs/final_result.md`（verdict）**；不写过程 reasoning 日志。
- eval 是**纯 LLM judge**：不生成测试用例、不写 `cases/`、不把成功条件建立在用例覆盖上。
- 跨阶段共用读写边界/效率/`Final Result` 格式见 `skills/COMMON.md`。

## 1. 输入输出（CAV）

- 输入：实现/规格 C + 可选 companion `.v`（只读语义目标）、target function、workspace。
- 输出：`output/eval_<ts>_<name>/` 下 `original/<name>.c`(+`.v`)、`logs/{issues,metrics,final_result}.md`。

## 2. LLM Judge（写 `logs/final_result.md`）

逐项写 `Pass`/`Fail`/`Inconclusive` + 一句依据（判据口径见职责划分的 spec-quality-checklist）：

- `Precondition strength`（最强错误：`requires false`）
- `Precondition safety`（前条件排除除零/空指针/越界/UB 溢出/非法移位）
- `Postcondition strength`（最弱错误：`ensures true`）
- `Soundness`（正确程序的所有输入输出都满足 spec）
- `Parameter coverage`（约束所有输入/输出/必要后状态）
- `Path coverage`（覆盖所有路径/分支）
- `Completeness`（任意满足 spec 的程序都应是该问题的正确程序）

全 `Pass` → `Judge verdict: Pass`；任一失败 → `Judge verdict: Fail`；无法判断 → `Judge verdict: Inconclusive`。

## 3. Aggregate verdict（写 `logs/final_result.md`，两行都要）

```text
Spec verdict: Correct|Buggy|Inconclusive
Judge verdict: Pass|Fail|Inconclusive
```

- `Correct` = sound + complete
- `Buggy` = 过强 / 过弱 / unsound / incomplete / 漏关键输入·路径·后状态约束
- `Inconclusive` = 证据不足以判定

## 4. 宏观流程 + 完成判据

读实现/contract → 按 §2 逐项 judge → 写 `final_result.md` 两行 verdict + `issues.md` / `metrics.md`。

`Final Result: Success` 仅当 `Spec verdict: Correct` 且 `Judge verdict: Pass`；`Buggy` / `Inconclusive` / `Judge verdict: Fail` / `Judge verdict: Inconclusive` 一律 `Final Result: Fail`。

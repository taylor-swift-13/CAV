---
name: c-qcp-eval
description: Evaluate an existing C/QCP implementation by judging whether the contract fully characterizes the target behavior.
---

Eval 判断 C/QCP contract 是否真正、完整刻画目标程序行为。

## 0. 职责

- spec 质量判据依照 QCP `.agents/skills/annotation-checking/docs/spec-quality-checklist.md`。judge 前必须先读。
- Eval 是纯 LLM judge：不生成测试用例，不写 `cases/`，不以测试覆盖作为成功条件。
- 唯一文字产物：`logs/issues.md`、`logs/metrics.md`、`logs/final_result.md`。

## 1. 输入输出

- 输入：实现/规格 C、可选 companion `.v`、target function、workspace。
- 输出：`output/eval_<ts>_<name>/` 下：
  - `original/<name>.c` 和可选 `.v`
  - `logs/issues.md`
  - `logs/metrics.md`
  - `logs/final_result.md`

## 2. Judge 项

在 `logs/final_result.md` 中逐项写 `Pass` / `Fail` / `Inconclusive` 和一句依据：

- `Precondition strength`
- `Precondition safety`
- `Postcondition strength`
- `Soundness`
- `Parameter coverage`
- `Path coverage`
- `Completeness`

判定口径：

- `Correct`：sound + complete，所有 judge 项为 `Pass`。
- `Buggy`：过强、过弱、unsound、incomplete，或漏关键输入/路径/后状态约束。
- `Inconclusive`：证据不足。

## 3. Verdict 格式

退出和成功的 judge 口径以 QCP `.agents/skills/annotation-checking/docs/spec-quality-checklist.md` 为准；CAV 只规定 verdict 文件和 `Final Result` 映射。

`logs/final_result.md` 必须包含这两行：

```text
Spec verdict: Correct|Buggy|Inconclusive
Judge verdict: Pass|Fail|Inconclusive
```

`Final Result: Success` 仅当：

- `Spec verdict: Correct`
- `Judge verdict: Pass`
- `logs/issues.md` 和 `logs/metrics.md` 已更新

其余情况一律 `Final Result: Fail`。

## 4. 日志

`logs/issues.md` 退出前必须存在。若 verdict 不是 `Correct/Pass`，必须记录具体失败项、对应 contract 位置和原因；若没有 issue，写 `No issues encountered.`。

`logs/metrics.md` 记录最终 verdict、耗时、输入/输出路径、agent/model。

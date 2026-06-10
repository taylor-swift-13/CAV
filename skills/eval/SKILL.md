---
name: c-qcp-eval
description: Evaluate an existing C/QCP implementation by judging whether the contract fully characterizes the target behavior.
---

Eval 判断 C/QCP contract 是否真正、完整刻画目标程序行为。

本 skill 自包含 Eval 阶段需要遵守的 CAV 规则。

## 0. 职责

- spec 质量判据依照 QCP 官方文档。judge 前必须读取下面的路径：
  - `.agents/skills/annotation-checking/docs/spec-quality-checklist.md` — spec-quality 判据；检查外部 Rocq 谓词是否有定义、function contract 是否刻画数学效果。
  - `.agents/skills/annotation-filling/docs/predicate-first-annotation.md` — 如何区分数学性质谓词和算法镜像。
- 唯一文字产物：`logs/issues.md`、`logs/metrics.md`、`logs/final_result.md`。
- 不做示例检索；只依据当前输入、题面语义、companion `.v` 定义和 QCP spec-quality 文档判定。

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

- 目标行为的合法输入域以题面为准。若输入 C 的题面注释、raw 题意或 companion spec 中明确写有
  `Constraints` / `Constrain` / `Restrictions` / `Preconditions` 等输入范围或结构约束，
  这些约束属于目标 domain。
- `Precondition strength` 只在 contract 排除题面合法输入、或加入题面/内存安全/整数安全都不需要的额外条件时判
  `Fail`。如果 `Require` 精确包含题面显式输入约束，不得仅因为实现数学上可扩展到题面 domain 之外就判为
  over-strong。
- `Completeness` 只要求 contract 在题面合法输入域内完整刻画行为；不要要求覆盖题面明确排除的输入。
- 为排除 C RTE/UB 可以加入必要安全条件，但这些条件应尽量精确；若用比安全所需更强的条件缩小题面 domain，
  仍应判为过强。
- `Correct`：sound + complete，所有 judge 项为 `Pass`。
- `Buggy`：过强、过弱、unsound、incomplete，或漏关键输入/路径/后状态约束。
- `Inconclusive`：证据不足。
- 如果 C annotation 中使用了承载题目功能语义的外部 Coq 谓词，但 eval artifacts 的 companion `.v` 或可见库中没有 definition-only 定义，必须按 `spec-quality-checklist.md` 判为 spec 缺失：相关 judge 项为 `Fail`，不能因为 `check_spec_wellformed` 通过而判 `Correct`。

## 3. Verdict 格式

退出和成功的 judge 口径以 `.agents/skills/annotation-checking/docs/spec-quality-checklist.md` 为准；CAV 只规定 verdict 文件和 `Final Result` 映射。

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

`logs/metrics.md` 记录最终 verdict、耗时、输入/输出路径、agent/model 和已读取的 QCP spec-quality 文档摘要。

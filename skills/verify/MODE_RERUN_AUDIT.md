# Mode: Re-run after audit critic

本附录只在 prompt 中出现 `Audit findings:`、`Restart feedback` 或 runner audit 反馈块时生效。本轮是带 critic 反馈的 QCP mirror 重跑。

## 处理规则

- 把 feedback 中每一条 finding 当作必须修复的 blocker；
- 逐条对照检查当前 QCP C mirror、Coq mirror、active QCP logs 和 `run_audit.sh` 输出；
- 修复期间禁止残留 `assume` / 新增 `axiom` / `skipesc` / `nowarn` / 改弱 contract 等绕过；
- 每次修复后重跑 `bash SeparationLogic/examples/CAV/<workspace>/run_audit.sh`。

## 日志要求

在 active QCP `logs/issues.md` 末尾追加一段，逐条列出：

- audit critic 原文 finding（quote 不超过 1-2 行）；
- 当前 QCP mirror 的对应状态；
- 本轮修复动作；
- 修复后的 `run_audit.sh` 结果。

## 和 retry 模式叠加

prompt 通常会同时带 `Attempt: N (retry...)`。两个 addendum 都生效：先按 `MODE_RETRY.md` 在 `continue.md` 追加 section、读上一轮状态，再按本附录逐条修复 audit finding。

## 完成判据

仍按主 SKILL：只有 QCP `run_audit.sh` 返回 0 才能写 `Final Result: Success`。

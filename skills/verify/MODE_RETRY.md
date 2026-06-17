# Mode: Retry round

本附录只在 prompt 标 `Attempt: N (retry — ...)` 且 `N > 1`，或 prompt 带 `Restart feedback` 时生效。

## 接力规则

不要从零开始重做。先读 active QCP logs 和当前 QCP mirror：

- `SeparationLogic/examples/CAV/<workspace>/logs/continue.md`（如已存在）
- 最近一轮 `agent_last_message_*.txt`
- `run_audit.sh` 及其 audit log
- 当前 QCP Coq mirror 的 `*.v`
- 当前 QCP C mirror 的 annotated C/header

## `continue.md` 必须追加新 section

改任何工作面文件之前，在 active QCP `logs/continue.md` 末尾追加一段新 section，内容至少包含：

- 上一轮卡在哪条 witness / theorem / tactic / audit gate；
- 当前 blocker 的精确定位；
- 本轮准备改哪几个文件/区域；
- 为什么这样改预期能修。

禁止覆盖、重写、合并既有 `continue.md` section。

## 修复范围

- 只针对定位到的 blocker；
- 保留已通过的工作，不整段重写 proof；
- 不动 fingerprint 已填好的字段，除非确实需要修正；
- 不把“定位到新的 blocker”当作完成，定位后必须继续修复并重跑 `run_audit.sh`。

如果上一轮 blocker 是 `proof_manual_has_obligations`、`qcp_audit_failed`、`Cannot find witness`、rewrite/unification、`entailer!` / `lia` 失败，本轮改 proof 前必须按主 SKILL 先检索并记录候选。

## 完成判据

仍按主 SKILL：`run_audit.sh` 返回 0 才能写 `Final Result: Success`。可继续推进的 retry blocker 不能以 `Final Result: Fail` 结束；未记录检索结果的 proof blocker 也不能以 `Final Result: Fail` 收尾。

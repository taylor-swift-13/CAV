# Mode: Retry round

本附录只在 prompt 标 `Attempt: N (retry — ...)` 且 `N > 1` 时生效。

## 接力规则

- **不要**从零开始重做。先读这些文件再动笔：
  - `logs/continue.md`（如已存在）
  - `logs/agent_last_message_*.txt`（最近一轮 agent 的自述）
  - `logs/agent_stderr_*.log`（最近一轮的编译错误）
  - 当前 `coq/generated/*.v`
  - 当前 `annotated/verify_<timestamp>_<name>.c`

## `continue.md` 必须追加新 section

改任何工作面文件**之前**，在 `logs/continue.md` 末尾追加一段新 section，内容至少包含：

- 上一轮卡在哪条 wit / 哪条 tactic / 哪个编译错误（引用具体 theorem/witness 名、文件路径、报错片段）；
- 当前 blocker 的精确定位；
- 本轮准备改哪几行；
- 为什么这样改预期能修。

**禁止**：覆盖、重写、合并既有 `continue.md` section。每轮 retry 都要追加新的一段。

## 修复范围

- 只针对定位到的 blocker；
- **保留**已通过的工作（symexec 不重跑、proof 不整段重写）；
- 不动 fingerprint 已填好的字段（除非真的需要修正）。
- 不要把“定位到新的 blocker”当作本轮完成。定位后必须立刻修它并重新跑对应 gate，直到主 SKILL §0 允许退出。

## 完成判据

仍按主 SKILL §5 / §0。可继续推进的 retry blocker 不能以 `Final Result: Fail` 结束当前 agent run。

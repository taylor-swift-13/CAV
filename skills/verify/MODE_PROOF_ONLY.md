# Mode: Proof-only

本附录只在 runner 在 prompt 顶部标 `Mode: proof-only` 时生效，是主 `SKILL.md` 的延伸约束，不替代主流程。

## 触发条件

`run_verify.py` 在以下三件事同时成立时进入本模式：

- 输入只有 `input/<name>.c`、无 `.v`；
- 函数是 loop-free（无 `for`/`while`/`do-while`/`switch`/`goto`）；
- 当前 workspace 的 `coq/generated/<name>_goal.v` 已经由确定性 fast path 跑过 symexec 生成。

进入本模式说明：symexec 已经成功、`proof_auto.v` 也已就位，但 `proof_manual.v` 还存在 `Admitted`，需要 agent 来写。

## 硬约束（覆盖主 SKILL 的写边界）

- **不改** `input/`、`raw/`、`annotated/`、`workspace/original/`；
- **不改** contract、loop invariant、annotation、`.c` 文件；
- **不改** `coq/generated/*_goal.v`、`*_proof_auto.v`、`*_goal_check.v`；
- 可写面**只剩**：`coq/generated/<name>_proof_manual.v` 和 `logs/*`。

如果发现 generated VC 在当前 contract/VC 下确实不可证（典型表现：`entailer!` 剩 `(p <> NULL)` 这种 LHS 不带的纯条件），写阻塞到 `logs/issues.md` 然后以 `Final Result: Fail` 收尾——**不要**改 contract 或 annotation 绕过。那是 Contract 阶段的义务（见 `experiences/general/CONTRACT/README.md §15`）。

## 工作流仍按主 SKILL

- §4.5a（10 次探索预算 try-first）继续生效；
- §4.5b 的 tactic 起手式直接套用；
- attempt > 1 或 prompt 带 `Restart feedback` 时按 `MODE_RETRY.md` 继续。

## 完成判据

和主 SKILL §6 一致：`goal_check.v` 编译通过 + `proof_manual.v` 无 `Admitted`/`admit`/`Abort`。

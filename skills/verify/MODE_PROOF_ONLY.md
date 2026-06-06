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

如果 generated VC 在当前 contract/annotation 下确实不可证，写阻塞到 `logs/issues.md` 然后以 `Final Result: Fail` 收尾——**不要**改 contract 或 annotation 绕过。那是 Contract 阶段的义务。

普通的 `proof_manual.v` 还有 `Admitted`、`coqc` 报错、tactic 暂时失败，都不是 proof-only 退出理由。只要能继续编辑 `proof_manual.v` 或添加允许范围内的 local helper，就必须继续证明并重新编译。

proof-only 模式仍必须执行主 SKILL §3 的检索（到 `QualifiedCProgramming/SeparationLogic/examples/` 找相似例子）。没有先检索就不允许因为单个 proof theorem、`Cannot find witness`、rewrite/unification 或 tactic 失败写 `Final Result: Fail`。

## 工作流仍按主 SKILL

- try-first / 探索预算等效率约束见 `skills/COMMON.md` §3；
- tactic 起手式与分离逻辑证明套路直接看 `QualifiedCProgramming/.agents/skills/vc-proving/docs/`；
- attempt > 1 或 prompt 带 `Restart feedback` / `Audit findings:` 时，叠加主 SKILL §7.1（带反馈重跑）继续。

## 完成判据

和主 SKILL §5 一致：四个 `.v` 编译通过 + `proof_manual.v` 无 `Admitted`/`admit`/`Abort`/新增 `Axiom`。

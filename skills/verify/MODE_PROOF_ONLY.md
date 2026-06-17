# Mode: Proof-only

本附录只在 runner 在 prompt 顶部标 `Mode: proof-only` 时生效，是主 `SKILL.md` 的延伸约束，不替代主流程。

## 触发条件

runner 只在 symexec 已经生成当前 case 的 QCP mirror VC，且还需要补 `proof_manual.v` 时进入本模式。所有路径以 prompt 中的 QCP mirror 为准：

- C mirror: `QCP_examples/CAV/<workspace>/`
- Coq mirror: `SeparationLogic/examples/CAV/<workspace>/`
- Logs: `SeparationLogic/examples/CAV/<workspace>/logs/`
- Audit: `SeparationLogic/examples/CAV/<workspace>/run_audit.sh`

## 写边界

- 不改 `../input/`、`../raw/`、`../output/`、`../annotated/`；
- 不改 `deps/` staged 原始 `.v` spec；
- 不改 function contract、原始 C implementation；
- 不手改 `*_goal.v`、`*_proof_auto.v`、`*_goal_check.v`；
- 优先只改当前 QCP Coq mirror 的 `<name>_proof_manual.v` 和必要 local helper，以及 active QCP logs。

如果 proof 暴露 annotation 缺口，可以按主 SKILL 回 annotation，并在 QCP mirror 中重跑 symexec；但仍不能改 function `Require` / `Ensure` 或 executable C。

## 检索和证明

proof-only 模式仍必须执行主 SKILL 的 fingerprint 检索。没有检索记录时，不允许因为单个 proof theorem、`Cannot find witness`、rewrite/unification、`entailer!` / `lia` 失败写 `Final Result: Fail`。

proof tactic、witness、分离逻辑套路优先从当前 VC、已有 proof、CAV experience 检索和同型 QCP 示例中迁移。只有具体 proof blocker 需要额外规则时，才按主 SKILL §0 打开 QCP `vc-proving` 的对应文件；不要预读整个 `.agents/skills/vc-proving/` 目录。

## 完成判据

只以 QCP mirror 的 `run_audit.sh` 返回 0 为成功。`proof_manual.v` 必须无 `Admitted` / `admit` / `Abort` / 新增 `Axiom`。

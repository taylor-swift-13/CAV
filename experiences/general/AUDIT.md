# Audit Experience

本文件只记录 audit 阶段的通用经验：如何判断一个 QCP proof 是否可信，如何识别
反作弊或伪证明。它不记录 contract 写法，也不记录具体 witness 证明技巧。

## 1. 只有 `proof_manual.v` 里的 stub 才算作弊

`proof_manual.v` 中留下 `Admitted.`、手写 `Axiom`、`Parameter`、`Abort`，都应视为
高优先级风险。verify 的人工证明责任就在这个文件里，stub 会直接让“证明成功”
失去意义。

反过来，`proof_auto.v` **全是 `Proof. Admitted.`（包括 `safety_wit` / `return_wit`
/ `partial_solve_wit`）是 symexec 生成的正常形态，不是作弊、不要报**。所有
`experiences/end-end/` 参考解的 `proof_auto.v` 都是 0 个 `Qed`、全 `Admitted`；
真正的证明负担只在 `proof_manual.v` 的 `entail_wit`（必须 `Qed`）。

因此**不要**用 `Print Assumptions` 把 `proof_auto.v` 的义务报成 axiom 来判
`NotVerified`——那会把这个被接受的约定当成不健全，错杀合格的 verify 结果。

## 2. compile replay 必须重放

audit 不能只信已有日志。至少要重放一次 `goal` / `proof_auto` / `proof_manual` /
`goal_check` 的编译链；如果重放失败，即使之前某次日志写着成功，也应判为
`NotVerified`。

## 4. `Require Import <function_name>.` 是结构性必需品，不是作弊（2026-05-26）

`proof_auto.v` 和 `proof_manual.v` 中的 `Require Import <function_name>.` 会触发
`forbidden_import` 扫描警告，但这始终是**有据可查的假阳性**：

- 该行来源是 annotated C 文件中的 `/*@ Import Coq Require Import <function_name> */` 注释
- QCP 把这条注释机械地插入所有生成的 `.v` 文件；删掉它会直接导致编译失败
- 对应的 `.v` 文件（`original/<name>.v`）里只含 `Definition`（透明定义），不含 `Axiom` 或 `Parameter`，因此不可能借此塞入额外假设

判断规则：如果 C 源文件包含 `/*@ Import Coq Require Import <name> */`，则
`proof_auto.v` / `proof_manual.v` 里对应的 `Require Import <name>.` 一律判为
`forbidden_import` 假阳性，记录为"justified false positive"，保留警告但不升级为 error。

## 5. verify 超时（exit 124）不等于证明错误（2026-05-26）

如果 verify 阶段以 `Final Result: Fail`、exit code 124（超时）结束，这只说明 agent
在时间限制内没有汇报完成，**不能据此判断证明本身不正确**。

audit 阶段的编译 replay 是独立的权威检查：

- 如果 5 步 replay（`original.v → goal.v → proof_auto.v → proof_manual.v → goal_check.v`）全部通过，且 `proof_manual.v` 无 `Admitted.` / 无新 `Axiom`，则证明完整正确
- 相应 audit 判定应为 `VerifiedWithWarnings`（或 `Verified`），不是 `NotVerified`

实例：本轮 verify 以 exit 124 超时结束，但 audit replay 确认所有 5 步通过，proof_manual.v 中 6 个 VC witnesses 和 22 个 helper lemma 全部 `Qed`，最终审计结果为 `VerifiedWithWarnings`。

## 3. contract 变弱要按语义审查

只要 verified 版本删掉、改弱或绕开了 original contract 的关键约束，就应该进入
审计发现。格式不同不一定是问题，但语义变弱必须被当成 error 处理。

---
name: verify
description: Verify skill，消费 Contract 输出完成注解、证明和编译检查。
---

Verify 消费 Contract 已经准备好的输入做 annotation + proof + compile，**不重写 contract**。所有 reasoning / issues 日志必须独立可读：现象 + 定位（文件/theorem/witness） + 修复动作 + 关键 C/Coq/报错片段 + 为什么这样改。

## 1. 路径约定

- 输入：`input/<name>.c`、可选 `input/<name>.v`
- 工作副本：`annotated/verify_<timestamp>_<name>.c`
- workspace：`output/verify_<timestamp>_<name>/`（含 `coq/generated/`、`logs/`、`original/`）

脚本调用和手动执行必须用这同一组路径，不可发明新位置。

## 2. 读写边界

**读**（除自身 I/O 外，参考只能在白名单内）：`doc/`、`experiences/`、`QualifiedCProgramming/QCP_examples/`。权威细节见 `doc/PERMISSIONS.md §3 / §3.1`。

**不要**：`symexec --help` 之类的命令反推、读 `scripts/` 编排脚本、读 `QualifiedCProgramming/` 下除 `QCP_examples/` 外的库源码、读自己的 `logs/agent_stdout_*.jsonl`、`git log` / `git show` 考古。

**写**：当前 `annotated/...c`、当前 workspace 的 `coq/generated/<name>_proof_manual.v` + 必要本地 helper、当前 workspace 的 `logs/*`。其余一律不写——包括 `input/`、`scripts/`、其它 workspace、QCP 源码、`experiences/`（只读，沉淀由末尾 consolidate 负责）。

**不手改** `*_goal.v` / `*_proof_auto.v` / `*_goal_check.v`。

## 3. 分步读经验（按需读，不要一次读完）

- 任务开始：`doc/SCOPE.md`、`doc/PERMISSIONS.md`、`experiences/general/README/README.md`
- 改 annotation 前：`experiences/general/INV/README.md`、`experiences/general/ASSERTION/README.md`
- 跑 symexec 前：`experiences/general/SYMEXEC/README.md`（命令在 §0；cwd = `QualifiedCProgramming/`）
- 写 `proof_manual.v` 前：`experiences/general/PROOF/README.md`（tactic 起手式在 §3）
- 编译前：`experiences/general/COMPILE/README.md` §5（cwd = `QualifiedCProgramming/SeparationLogic`；默认复用 `examples/*.vo`，缺失才回 `coq/deps/`）
- 卡住才查 `doc/retrieval/INDEX.md`、`doc/predict/`、`experiences/end-end/`、`QCP_examples/`

## 4. 主流程

1. 读 `input/<name>.{c,v}`，确认有基本规格。规格缺失或必须改 contract / 原始 C 时，**停止 verify**，记 `logs/issues.md`，找用户。
2. 读 `doc/retrieval/INDEX.md`，按受控词表回填 `logs/workspace_fingerprint.json` 的 `semantic_description` 和 `keywords`（不能留空）。
3. 需要补 `Inv` / `Assert` 时：读 INV/ASSERTION，先 append `logs/annotation_reasoning.md`，再改 annotated 工作副本。loop invariant 写完整 `Inv Assert`；中间断言优先写完整 `Assert`，`which implies` 只做局部 bridge。生成的 manual VC 语义不可证时**回 annotation**，不要硬写 proof。无需注释就跳过这一步。
4. 跑 `symexec`（每改 annotation 必须重跑）。以最新 witness 编号为准，不要盲用旧 proof。
5. 看 `proof_manual.v`：
   - 若**没有需要手工证明的 theorem**（所有 witness 都在 `proof_auto.v` 的 `Admitted` 占位里）= trivial case，**直接跳 6**，不读 `experiences/general/PROOF/README.md`、不检索 retrieval/end-end/QCP_examples。
   - 否则读 `experiences/general/PROOF/README.md`，按 §3 tactic 起手式套，编译失败迭代；每轮先 append `logs/proof_reasoning.md` 再改 proof。手工 witness 逐个证、当前没证完不跳下一个。可补 helper lemma；**不准** `Admitted` / `admit` / `Abort` / 新增 `Axiom` / 改 VC 目标 / 导入 `derivable1` 绕过。
6. 按 `experiences/general/COMPILE/README.md` §5 编译 `goal` / `proof_auto` / `proof_manual` / `goal_check`。
7. 自检 source integrity / freshness：确认 `input/<name>.c` / 可选 `input/<name>.v` 没被改；确认 `annotated/verify_<timestamp>_<name>.c` 里的函数 contract 和 executable C implementation 与原始 input 一致，只新增验证注解；确认当前 Coq 产物来自最新 annotated C。
8. 清理 `coq/` 下非 `.v` 中间产物和 `input/` 下非 `.v`/`.c` 产物。
9. 写完 `logs/issues.md`（追加，详细记录所有踩坑）、`logs/metrics.md`（自判摘要即可），最后一行写裸的 `Final Result: Success` 或 `Final Result: Fail`——**整行就是这十几个字符**，禁止 markdown 加粗、反引号、后缀（如 `(round N)`），否则外部判据会误判未完成。

## 5. 完成条件

`logs/metrics.md` 写自判摘要即可；runner 会复核并覆盖最终 metrics。

全部满足才能写 `Final Result: Success`：

- symexec 基于最新 annotated 文件成功，生成最新 `goal/proof_auto/proof_manual/goal_check`
- `proof_manual.v` 无 `Admitted` / `admit` / `Abort` / 新增 `Axiom`
- 四个 `.v` 文件全编译通过
- 没有修改原始 contract 或函数实现；annotated C 只新增验证注解
- `logs/workspace_fingerprint.json` 非空且字段合法
- runner 能用当前 annotated C 重新 symexec，并确认 `goal/proof_auto/goal_check` 与当前产物一致
- `coq/` 与 `input/` 中间产物已清理
- `logs/issues.md` 和 `logs/metrics.md` 已完整更新

如果任一机器 gate 失败，必须写 `Final Result: Fail`，并在 `logs/issues.md` 中记录：

- 失败的 gate 名称（如 symexec、manual proof obligation、`coqc goal_check.v`）
- 退出码或 theorem/witness 名称
- 关键报错
- 当前 `annotated/...c` 和相关 `coq/generated/*.v` 路径
- 下一轮 verify 需要修正的具体点

Agent 自判成功后，runner 还会复核：检查生成文件存在、`proof_manual.v` 无未解占位、重新编译 `goal/proof_auto/proof_manual/goal_check`，确定性检查 input C/V 未被修改、annotated C 的 contract 和 executable implementation 未偏离原始 input，检查 fingerprint 非空合法，并记录当前 annotated C hash 后重新 symexec 对比 `goal/proof_auto/goal_check`。只有 runner 复核通过，verify 阶段才算成功。

## 6. Reasoning 日志规范（共用）

`annotation_reasoning.md` / `proof_reasoning.md` / `issues.md` / `continue.md` 共同遵守：

- **只追加，不覆盖**
- 每段独立可读：现象、定位（文件路径 + theorem / witness / 行号）、修复动作、关键代码或日志片段（C annotation / Coq theorem-subgoal-tactic / `coqc`-`symexec` 报错）、**为什么这样改**。不准只写「尝试证明失败」「修改了 invariant」这类笼统话。
- 每轮迭代前贴出新一轮的片段，不只贴最后一版

## 7. 条件性 mode addendum

runner 在 prompt 加标记触发以下附录，**没标记就不读**。多个标记可叠加。

| Prompt 标记 | 附录文件 | 含义 |
|------------|---------|------|
| `Attempt: N (retry — ...)` 且 N > 1 | `MODE_RETRY.md` | 接力上一轮工作，必须追加 `logs/continue.md` 新 section |
| `Restart feedback` 块 | `MODE_RETRY.md` | runner audit check 反馈后的内部重试，逐条修复 feedback |
| `Mode: proof-only` | `MODE_PROOF_ONLY.md` | loop-free + symexec 已跑过、仅补 `proof_manual.v` 的子场景 |

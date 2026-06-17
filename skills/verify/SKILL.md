---
name: verify
description: Verify skill，消费 Contract 输出完成注解、证明和编译检查。
---

Verify 在 QCP mirror 中完成 annotation + proof + compile，**不重写 function contract**。本 skill 自包含 CAV 工程边界、经验检索、重启纪律和 runner audit 成功判定；QCP `.agents/skills/` 只作为按需补充资料，不要全量预读。

这里的 function contract 只指函数级 `Require` / `Ensure` 前后条件；loop invariant、`Assert`、`Inv Assert`、`which implies` 和 `where` 属于 verification annotation。

## 0. 必读顺序

先读 repo-level CAV skill，再按 prompt 标记读 mode addendum：

- `../skills/verify/SKILL.md`
- `../skills/verify/MODE_PROOF_ONLY.md`（仅 prompt 标 `Mode: proof-only` 时）
- `../skills/verify/MODE_RETRY.md`（仅 retry / restart feedback 时）
- `../skills/verify/MODE_RERUN_AUDIT.md`（仅 prompt 有 audit feedback 时）

QCP `.agents` 的使用原则：

- 默认使用 runner prompt 中的 exact commands、当前 QCP mirror、CAV `../experiences` 检索结果推进。
- 只有 prompt 和当前错误不足以决定下一步时，才读 `.agents/skills/verification-orchestrator/SKILL.md`。
- 只有遇到具体 annotation、symexec、VC diagnosis、proof 或 final-check blocker 时，才打开对应 phase 的 `.agents/skills/<phase>/SKILL.md` 或相关 `docs/`；禁止一次性读取 `.agents/skills/*` 或整个 docs 目录。

遇到具体 annotation/proof blocker 时，优先检索并阅读同型 QCP 官方示例：

- `QCP_examples/{Applications_human,LLM_bench,QCP_demos_human,QCP_demos_LLM}/`
- `SeparationLogic/examples/{Applications_human,LLM_bench,QCP_demos_human,QCP_demos_LLM}/`
- `tutorial/`

CAV `../doc` 和 `../experiences` 是保留的经验系统，用于 targeted retrieval / restart memory；不要用泛读 `.agents` 替代这些检索。

## 1. 路径和边界

runner 已经把当前 case staged 到 QCP mirror。以 prompt 中列出的路径为准：

- Active C mirror: `QCP_examples/CAV/<workspace>/`
- Active Coq mirror: `SeparationLogic/examples/CAV/<workspace>/`
- Read-only spec deps: `SeparationLogic/examples/CAV/<workspace>/deps/`
- Active logs: `SeparationLogic/examples/CAV/<workspace>/logs/`
- Required audit: `SeparationLogic/examples/CAV/<workspace>/run_audit.sh`

只写：

- 当前 QCP C mirror 中的 annotated C/header；
- 当前 QCP Coq mirror 中除 `deps/` 外的本 case `.v` 文件；
- 当前 QCP logs 中的 `issues.md`、`metrics.md`、`annotation_reasoning.md`、`proof_reasoning.md`、`continue.md`、`workspace_fingerprint.json`。

只读：

- 当前 QCP mirror；
- QCP `.agents/skills/` 中当前 blocker 对应的少量文件、`tutorial/` 和上述官方示例目录；
- `../skills/verify/*`；
- `../doc`、`../experiences` 和 `../scripts/search_fingerprint.py`，仅用于经验检索。

禁止：

- 读写 `../output/`、`../annotated/`、`../input/`、`../scripts/` 中除 `search_fingerprint.py` 外的文件；
- 读自己的 `agent_stdout_*.jsonl`、`git log` / `git show`；
- 读其它 CAV/QCP mirror workspace；
- 修改 `deps/` 中 staged 原始 `.v` spec；
- 修改原始 C implementation 或 function `Require` / `Ensure`。

## 2. 经验检索

进入 manual proof 前，必须先确保 active QCP `logs/workspace_fingerprint.json` 非空，字段合法：

```json
{
  "semantic_description": "...",
  "keywords": {
    "problem_kind": "...",
    "data": "...",
    "pattern": "..."
  }
}
```

然后运行 prompt 给出的命令，形如：

```bash
python3 ../scripts/search_fingerprint.py --fingerprint SeparationLogic/examples/CAV/<workspace>/logs/workspace_fingerprint.json --scope all --min-keyword-matches 1 --prefer-stage PROOF --top 5 --format markdown
```

把查询命令、前 1-3 个候选、实际展开阅读的候选、复用/拒绝的 pattern 追加到 active QCP `logs/proof_reasoning.md`。同一 theorem 或同类 `coqc` 错误连续失败 2 次后，必须再次检索。

没有检索记录时，不允许因为 `proof_manual_has_obligations`、`Cannot find witness`、rewrite/unification、`entailer!`、`lia` 失败写 `Final Result: Fail`。

## 3. 工作循环

按 runner prompt 的 exact commands 和当前 QCP mirror 推进：

1. 读当前 QCP mirror 的 staged C、Coq deps 和与当前失败点相关的示例。
2. 如需 annotation，先写 `logs/annotation_reasoning.md`，再只修改 verification annotation。
3. 每次 annotation 变化后，在 QCP mirror 中重跑 symexec；重跑前把旧 generated `.v` 备份到当前 Coq mirror 的 `.tmp/` 或 runner 已准备的 reference 目录，便于迁移旧 proof 结构。
4. proof 阶段只补 `<name>_proof_manual.v` 和必要 local helper；不要证明或编辑 `proof_auto.v`。
5. 若 proof 暴露 annotation 缺口，回到 annotation 并重跑 symexec。
6. 每轮用 `bash SeparationLogic/examples/CAV/<workspace>/run_audit.sh` 作为最终 gate。

若某一步缺少操作细节，再按 §0 打开对应的单个 QCP `.agents` phase 文件或 doc。

禁止在 `proof_manual.v` 中保留或新增 `Admitted` / `admit` / `Abort` / `Axiom`。禁止改 VC 目标、改 generated goal/proof_auto/goal_check，或导入绕过性 lemma。

## 4. 退出纪律

`run_audit.sh` 返回非零时不要退出；继续按第一个失败点修改 annotation/proof 并再次运行 audit。写 `issues.md` 或 `metrics.md` 不是退出理由。

只有两种最终结果：

- `Final Result: Success`：`run_audit.sh` 返回 0，`proof_manual.v` 无未解占位，source integrity 保持，logs/metrics 已更新。
- `Final Result: Fail`：只允许 confirmed `contract_program_mismatch_blocker` 或 `contract_or_original_spec_blocker`，即 function contract / 原始 spec 与程序语义冲突，必须回用户或上游 spec 决策，无法通过当前 annotation/proof 修复。

普通 symexec、coqc、proof obligation、tactic、load-path、witness 失败都不是 Fail 理由。

## 5. 日志

所有 reasoning 日志只追加，不覆盖。每段必须独立可读：现象、定位（文件/theorem/witness/行号）、修复动作、关键 C/Coq/报错片段、为什么这样改。

- `logs/annotation_reasoning.md`：annotation 变更前写。
- `logs/proof_reasoning.md`：proof 变更前写，并记录经验检索。
- `logs/issues.md`：记录真正遇到的 issue、audit 非零原因、最终解决方式或合法 blocker。
- `logs/continue.md`：retry/restart 接力，每轮追加新 section。
- `logs/metrics.md`：记录自判摘要，最后一行必须是裸的 `Final Result: Success` 或 `Final Result: Fail`。

写 `Final Result: Fail` 时，`issues.md` 必须包含 blocker 名称、失败 gate、退出码或 theorem/witness 名、关键报错、相关路径、function contract / spec 与程序语义冲突点、为什么当前 verify 无法修复。

## 6. Mode Addendum

prompt 标记触发附录：

| Prompt 标记 | 附录文件 | 含义 |
|---|---|---|
| `Attempt: N (retry — ...)` 且 N > 1 | `MODE_RETRY.md` | 接力上一轮 QCP mirror 工作，追加 `continue.md` |
| `Restart feedback` / audit feedback | `MODE_RETRY.md`、必要时 `MODE_RERUN_AUDIT.md` | 逐条修复 runner/audit feedback |
| `Mode: proof-only` | `MODE_PROOF_ONLY.md` | symexec 已就位，优先补 proof_manual |

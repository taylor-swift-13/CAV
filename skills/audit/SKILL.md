---
name: c-qcp-audit
description: 审计 verify workspace 是否有作弊（弱化 contract、proof stub、unverifiable artifact 等）。
---

跨阶段共用规则（读写边界、效率、experiences 只读、reasoning log、`Final Result` 格式）见 `skills/COMMON.md`。本文件只描述 audit-specific 内容。

按需读：`experiences/general/AUDIT/README.md`、`experiences/general/PROOF/README.md`、`experiences/general/COMPILE/README.md`。**Audit 不修改任何源码、annotation 或 proof 文件**，只判 verify 结果可不可信、不修复。

## 1. 输入

- 一个 verify workspace，或显式的 original / verified 文件对
- runner 已生成的 deterministic `audit/findings.json`
- runner 已生成的 compile-replay 日志

## 2. 输出

`output/audit_<timestamp>_<name>/` 下：

- `original/<name>.{c,v}`、`verified/<name>.c`
- `audit/findings.json`（runner 写）、`audit/findings.md`（agent 写）
- `logs/reasoning.md`、`logs/issues.md`、`logs/metrics.md`、`logs/final_result.md`
- `logs/cheating_scan_{stdout,stderr}.log`、`logs/compile_replay_{stdout,stderr}.log`、agent runtime 输出（runner 自动放）

## 3. 工作流

deterministic cheating scan 由 runner 跑完，agent 的工作是**判断**每条 finding 是真违规还是合理 false positive，并自己**做一次 compile-replay 交叉检查**记录在 reasoning 里。然后写：

- `audit/findings.md` — 每条 finding 的解释 + 处理意见
- `logs/reasoning.md` — 逐条审计分析
- `logs/issues.md` — 只放未解决的疑问
- `logs/final_result.md` — 单行 `Audit verdict: <verdict>`

## 4. Finding 类型（典型）

`contract_weakening` / `proof_stub` / `manual_axiom` / `forbidden_import` / `compile_replay_failure` / `suspicious_assumption`

## 5. Verdict 三选一

| Verdict | 条件 |
|---------|------|
| `VerifiedClean` | 无未解决 error-severity finding + compile replay 通过 |
| `VerifiedWithWarnings` | 仅剩 warning-severity finding + compile replay 通过 |
| `NotVerified` | 任何 error 未解决，或 compile replay 失败 |

判定规则：

- proof 文件出现 `Admitted.` / 手写 `Axiom` / 类似 stub 是 error，除非能论证属于**生成的 proof_auto.v 自动 stub**——`proof_auto.v` 的 Admitted 是 QCP 约定的正常状态（见 `experiences/general/PROOF/README.md`），只有 `proof_manual.v` 的 Admitted 才算违规。
- contract weakening 是 error，除非能论证 verified 文件保留了原 contract 的语义。

## 6. 完成判据

`Final Result: Success` 仅当：

- `audit/findings.json` 存在且能解析；
- `audit/findings.md` 和 `logs/final_result.md` 都已写；
- verdict 是 `VerifiedClean` 或 `VerifiedWithWarnings`。

`Audit verdict: NotVerified` 对应 `Final Result: Fail`。

---
name: contract
description: Contract skill，把原始题意 + C 实现整理成 verify 友好的 `input/<name>.c` / `.v`。
---

跨阶段共用规则（读写边界、效率、experiences 只读、reasoning log、`Final Result` 格式）见 `skills/COMMON.md`。本文件只描述 contract-specific 内容。

任务开始读：`doc/SCOPE.md`、`doc/PERMISSIONS.md`、`experiences/general/README/README.md`、`experiences/general/CONTRACT/README.md`。其他文档卡住再按需读。

## 1. 输入

原始 C 实现、原始题意 / 自然语言描述、约束 / 边界 / 示例、可选辅助定义草稿。

## 2. 输出

- `input/<name>.c`（目标函数 + 完整 contract，**不含**任何 verify 阶段注释）
- `input/<name>.v`（仅当确实需要额外 Coq 定义；能不用就不用）
- `output/contract_<timestamp>_<name>/logs/reasoning.md`、`issues.md`、`metrics.md`

## 3. 硬规则

- **先写** `logs/reasoning.md`（语义、边界、内存与 Coq 依赖判断），**再写** `input/<name>.c`
- `input/<name>.c` 只包含目标函数 + 完整 contract；**不要**提前写 `Inv` / `Assert` / `which implies` / bridge / loop-exit assertion（那是 verify 阶段的事）
- `input/<name>.v` 只放题目专用 Coq 定义
- 保持原程序语义不变；必须改接口时，只做 verification-friendly 改写
- contract 设计要保证下游所有 VC 可证：典型坑见 `../CONTRACT/1/pointer-deref-needs-non-null.md`（指针 deref 需 `p != 0`）和 `../CONTRACT/README.md §16`（后条件优先蕴含、避免顶层析取）

## 4. 最短流程

1. 读原始题意和代码
2. 写 `logs/reasoning.md`（语义、边界、内存、Coq 依赖判断）
3. 生成 `input/<name>.c`
4. 判断是否真的需要 `input/<name>.v`，需要才写
5. 写 `logs/issues.md`、`logs/metrics.md`

## 5. 完成判据

`Final Result: Success` 仅当：

- `input/<name>.c` 前后条件完整、无 verify 阶段注释混入
- `.v`（如有）只包含额外逻辑定义
- `reasoning.md` / `issues.md` / `metrics.md` 已写完

## 6. 条件性 mode addendum

| Prompt 标记 | 含义 |
|------------|------|
| `Critic findings:` 块出现 | 上一轮 contract 被 eval critic 拒绝的 RE-RUN。把每条 critic finding 当 blocker，在 `logs/reasoning.md` 追加一段对照检查 + 修复说明；修完再重新输出 `input/<name>.{c,v}`。修复期间不要扩到与 finding 无关的改动。 |

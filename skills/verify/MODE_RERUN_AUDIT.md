# Mode: Re-run after audit critic

本附录只在 prompt 中出现 `Audit findings:` 块时生效。表示 audit 阶段把上一次 verify 标记为不可信，本轮是带 critic 反馈的重跑。

## 处理规则

- 把 prompt 里 `Audit findings:` 块下的**每一条 finding** 当作必须修复的 blocker；
- 逐条对照检查当前 workspace 的规格 / 注解 / `logs/*` 状态——finding 说哪里有问题，就先打开那里看；
- 修复期间**禁止**残留任何 `assume` / 新增 `axiom` / `skipesc` / `nowarn` 之类的「绕过」标记（这是 audit 重跑的硬要求）。

## 日志要求

`logs/issues.md` 末尾追加一段，逐条列出：

- audit critic 原文 finding（quote 不超过 1–2 行）；
- 当前 workspace 的对应状态（finding 是否仍成立、相关文件路径 / 方法名 / 注解片段）；
- 本轮的修复动作（改了哪几行、为什么这样改）；
- 修复后的验证结果（OpenJML 通过、无 cheating 标记等）。

## 和 retry 模式叠加

prompt 通常会同时带 `Attempt: N (retry...)` 标记。两个 addendum 都生效：先按 `MODE_RETRY.md` 在 `continue.md` 追加 section、读上一轮状态，再按本附录逐条对照 audit findings 修。

## 完成判据

仍按主 SKILL §「Completion」——但实际上 audit 重跑等同于「绝对零 cheating 残留」的最严格判定。

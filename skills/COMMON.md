# 跨阶段共用规则（COMMON）

所有 stage skill（`contract` / `verify` / `eval` / `audit`）共用本文件。各 stage 的 `SKILL.md` 引用本文，**不**重复这些规则。

## 1. 读写边界

**读**（除当前任务自身的 I/O 外，参考只能在白名单内）：

- `doc/`、`experiences/`
- 当前任务的 `input/`（如适用）、当前 workspace
- OpenJML 官方文档与 specs 树（`doc/openjml-*` / `doc/JML_Reference_Manual.pdf` / `doc/OpenJMLUserGuide.pdf`）

**不要**做这些类型的探索：

- 不用 `--help` 反推 OpenJML 命令——精确命令模板在 `experiences/general/OPENJML/README.md`
- 不读 `scripts/` 编排脚本（`run_*.py`、`agent_loop.py`、`audit_jml.py` 等）
- 不读自己的 harness transcript（`logs/agent_stdout_*.jsonl`、`logs/agent_prompt_*`）
- 不做 `git log` / `git show` 考古
- 不读非白名单源码反推库内部行为

**写**（只写下列位置）：

- 当前 workspace 的 `logs/*`
- stage 特有的工作面（详见各 `SKILL.md`：contract 的 `input/<name>.java`、verify 的 annotated 工作副本、eval 的 `cases/` + `evaluation/`、audit 的 `audit/findings.md` + `logs/final_result.md`）
- **不写** `scripts/`、其它 stage 的 workspace、`doc/openjml-*` 等参考资料

## 2. `experiences/` 全程只读

每个 stage agent 都可以**读** `experiences/general/<NAME>/README.md`（universal 经验，按 README 顶部「常见入口」/symptom index 浏览）和 `experiences/general/<NAME>/<N>/<slug>.md`（topical 经验，按 `scripts/search_fingerprint.py` 检索）和 `experiences/end-end/`（参考解库）。

但**不得创建、写入、修改、或用 `cp`/`sed` 覆盖** `experiences/` 下任何文件——包括 `experiences/end-end/`（由 runner 的 export 步骤维护）和 `experiences/general/`（由末尾的 consolidate 阶段维护）。

`logs/metrics.md` 一律写 `Experience updates: none`。

## 3. 效率约束

- **首要：探索是这类任务的主要时间杀手。** 默认行为应该是「先写一版能跑的注解/规格、立即跑 OpenJML、读错误改」，而不是「先翻遍 demos / experiences / git history 找参考」。
- 工具调用预算是**硬上限**，不是目标。完成判据满足就立刻停，不要再读一遍文档「确认一下」。
- 命令和模板都在 `experiences/general/` 对应 README.md 里，按各 stage `SKILL.md` 的「分步读经验」指引按需读，不要一次性读完。

## 4. Reasoning 日志规范（共用）

各 stage 的 reasoning 日志（`reasoning.md` / `annotation_reasoning.md` / `test_reasoning.md` / `continue.md` / `issues.md`）共同遵守：

- **只追加，不覆盖**。
- 每段独立可读：写清楚现象、定位（文件路径 + 方法名 + 行号 / 诊断类别）、修复动作、关键代码或日志片段（Java/JML 注解 / OpenJML 报错 / SMT 反例）、以及**为什么这样改**。
- 后来的智能体只读这一段也能接管，不需要再回去翻源码或上一轮 transcript。
- 不写「尝试证明失败」「修改了 invariant」这类笼统话。
- 每轮迭代都贴当轮新的关键片段，不要只贴最后一版。

## 5. `Final Result` 行的硬格式

每个 stage 的 `logs/metrics.md` **最后一行**必须是裸的：

```
Final Result: Success
```

或

```
Final Result: Fail
```

整行就是这十几个字符——**不要**加 markdown 加粗 `**`、反引号、前后缀（如 `(confirmed in round N)`、`(round 2)`）、也**不要**并进其它句子。

外部判据按整行精确匹配这个标记；任何装饰都会被判为"未完成"从而触发无谓的重试。

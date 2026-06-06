# 跨阶段共用规则（COMMON）

所有 stage skill（`contract` / `verify` / `eval` / `audit`）共用本文件。各 stage 的 `SKILL.md` 引用本文，**不**重复这些规则。

## 1. 读写边界

**读**（除当前任务自身的 I/O 外，参考只能在白名单内）：

- **流程与一切 how-to 细节的权威来源：`QualifiedCProgramming/.agents/skills/`（全部子 skill 及其 `docs/`）**——各 stage 的流程和细节都依照这里，CAV skill 只加工程约束。
- `QualifiedCProgramming/README.md`、`QualifiedCProgramming/SeparationLogic/README.md`、`QualifiedCProgramming/tutorial/`、`QualifiedCProgramming/QCP_examples/`、`QualifiedCProgramming/SeparationLogic/examples/`
- 当前任务的 `input/`（如适用）、`annotated/<stage>_<timestamp>_<name>.c`（仅 verify）、当前 workspace

**不要**做这些类型的探索：

- 不用 `--help` 反推命令（symexec、coqc、claude/codex 等由 runner 脚本封装）
- 不读 `scripts/` 编排脚本（`run_*.py`、`agent_loop.py`、`coq_runner.py` 等）
- 不读 `QualifiedCProgramming/` 下除 `.agents/skills/`、README、`tutorial/`、`SeparationLogic/README.md`、`QCP_examples/`、`SeparationLogic/examples/` 外的库源码
- 不读自己的 harness transcript（`logs/agent_stdout_*.jsonl`、`logs/agent_prompt_*`）
- 不做 `git log` / `git show` 考古
- 不 `cat run-example-linux.sh` 反推参数

**写**（只写下列位置）：

- 当前 workspace 的 `logs/*`
- stage 特有的工作面（详见各 `SKILL.md`，例如 verify 的 `annotated/...c` + `coq/generated/<name>_proof_manual.v`、contract 的 `input/<name>.c`/`.v`、eval 的 `cases/` + `evaluation/`）
- **不写** `scripts/`、其它 stage 的 workspace、`QualifiedCProgramming/` 源码

## 2. 参考资料边界

每个 stage agent 都可以**读** QCP 流程文档、自带文档和例子：`QualifiedCProgramming/.agents/skills/`（流程与细节权威来源）、`QualifiedCProgramming/README.md`、`QualifiedCProgramming/SeparationLogic/README.md`、`QualifiedCProgramming/tutorial/`、`QualifiedCProgramming/QCP_examples/`、`QualifiedCProgramming/SeparationLogic/examples/`。

Agent 的 `logs/metrics.md` 只写自判摘要：stage、verdict、简短依据、`Experience updates: none`、最后一行 `Final Result: Success/Fail`。runner 会复核并覆盖最终 metrics。

## 3. 效率约束

- **首要：探索是这类任务的主要时间杀手。** 默认行为应该是「先猜一版能跑的、立即跑、读错误改」，而不是「先翻遍 demos / git history 找参考」。
- 工具调用预算是**硬上限**，不是目标。完成判据满足就立刻停，不要再读一遍文档「确认一下」。
- 按各 stage `SKILL.md` 的「分步读文档」指引按需读，不要一次性读完。
- trivial 早停：如果当前 stage 的完成判据在前几步就已满足（典型：verify 的 `proof_manual.v` 为空），直接收尾，**不要**再翻 demos / 找参考解。

## 4. 过程日志规范（共用）

**不写过程 reasoning 日志**（不再有 `reasoning.md` / `proof_reasoning.md` / `annotation_reasoning.md` / `test_reasoning.md`）。各 stage 唯一的文字过程产物是：

- `logs/issues.md`——只记**真正遇到的 issue**（含 contract 的 RTE/UB 审计结论、audit critic findings 的对照修复）。
- `logs/continue.md`——**仅 retry 接力用**（带反馈重跑时追加，跨 attempt 传递 blocker 定位；各 stage 的 retry 节内联在其 `SKILL.md`：verify §7.1、contract §5）。

两者共同遵守：

- **只追加，不覆盖**。
- 每段独立可读：现象、定位（文件路径 + theorem / witness / 行号）、关键代码或日志片段（C annotation / Coq theorem-subgoal-tactic / `coqc`-`symexec` 报错）、最终怎么解决或为什么卡住。
- 顺利通过的步骤不记流水账；不写「尝试证明失败」「修改了 invariant」这类笼统话。

## 5. `Final Result` 行的硬格式

Agent 自判版和 runner 最终版的 `logs/metrics.md` **最后一行**都必须是裸的：

```
Final Result: Success
```

或

```
Final Result: Fail
```

整行就是这十几个字符——**不要**加 markdown 加粗 `**`、反引号、前后缀（如 `(confirmed in round N)`、`(round 2)`）、也**不要**并进其它句子。

外部判据按整行精确匹配这个标记；任何装饰都会被判为"未完成"从而触发无谓的重试。

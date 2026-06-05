# 跨阶段共用规则（COMMON）

所有 stage skill（`contract` / `verify` / `eval` / `audit`）共用本文件。各 stage 的 `SKILL.md` 引用本文，**不**重复这些规则。

## 1. 读写边界

**读**（除当前任务自身的 I/O 外，参考只能在白名单内）：

- `QualifiedCProgramming/README.md`、`QualifiedCProgramming/SeparationLogic/README.md`、`QualifiedCProgramming/tutorial/`、`QualifiedCProgramming/SeparationLogic/examples/`
- 当前任务的 `input/`（如适用）、`annotated/<stage>_<timestamp>_<name>.c`（仅 verify）、当前 workspace

**不要**做这些类型的探索：

- 不用 `--help` 反推命令（symexec、coqc、claude/codex 等由 runner 脚本封装）
- 不读 `scripts/` 编排脚本（`run_*.py`、`agent_loop.py`、`coq_runner.py` 等）
- 不读 `QualifiedCProgramming/` 下除 README、`tutorial/`、`SeparationLogic/README.md`、`SeparationLogic/examples/` 外的库源码
- 不读自己的 harness transcript（`logs/agent_stdout_*.jsonl`、`logs/agent_prompt_*`）
- 不做 `git log` / `git show` 考古
- 不 `cat run-example-linux.sh` 反推参数

**写**（只写下列位置）：

- 当前 workspace 的 `logs/*`
- stage 特有的工作面（详见各 `SKILL.md`，例如 verify 的 `annotated/...c` + `coq/generated/<name>_proof_manual.v`、contract 的 `input/<name>.c`/`.v`、eval 的 `cases/` + `evaluation/`）
- **不写** `scripts/`、其它 stage 的 workspace、`QualifiedCProgramming/` 源码

## 2. 参考资料边界

每个 stage agent 都可以**读** QCP 自带文档和例子：`QualifiedCProgramming/README.md`、`QualifiedCProgramming/SeparationLogic/README.md`、`QualifiedCProgramming/tutorial/`、`QualifiedCProgramming/SeparationLogic/examples/`。

Agent 的 `logs/metrics.md` 只写自判摘要：stage、verdict、简短依据、`Experience updates: none`、最后一行 `Final Result: Success/Fail`。runner 会复核并覆盖最终 metrics。

## 3. 效率约束

- **首要：探索是这类任务的主要时间杀手。** 默认行为应该是「先猜一版能跑的、立即跑、读错误改」，而不是「先翻遍 demos / git history 找参考」。
- 工具调用预算是**硬上限**，不是目标。完成判据满足就立刻停，不要再读一遍文档「确认一下」。
- 按各 stage `SKILL.md` 的「分步读文档」指引按需读，不要一次性读完。
- trivial 早停：如果当前 stage 的完成判据在前几步就已满足（典型：verify 的 `proof_manual.v` 为空），直接收尾，**不要**再翻 demos / 找参考解。

## 4. Reasoning 日志规范（共用）

各 stage 的 reasoning 日志（`reasoning.md` / `proof_reasoning.md` / `annotation_reasoning.md` / `test_reasoning.md` / `issues.md` / `continue.md`）共同遵守：

- **只追加，不覆盖**。
- 每段独立可读：写清楚现象、定位（文件路径 + theorem / witness / 行号）、修复动作、关键代码或日志片段（C annotation / Coq theorem-subgoal-tactic / `coqc`-`symexec` 报错）、以及**为什么这样改**。
- 后来的智能体只读这一段也能接管，不需要再回去翻源码或上一轮 transcript。
- 不写「尝试证明失败」「修改了 invariant」这类笼统话。
- 每轮迭代都贴当轮新的关键片段，不要只贴最后一版。

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

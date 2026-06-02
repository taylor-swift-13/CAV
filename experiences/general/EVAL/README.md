# Eval Experience

本文件只记录 eval 阶段的通用经验：如何用具体 case 检查 contract 是否真正刻画了
实现行为。它不记录 verify 的 annotation / proof 技巧，也不记录 audit 的反作弊
结论。

常见入口：

- 覆盖所有控制分支：看 1
- 负例要针对具体子句：看 2
- 不可判定时要诚实给 `Inconclusive`：看 3
- 生成结果后用 `python3` 校验 JSON，不要先试 `jq` / `python`：看 4
- 蕴含式 `Ensure` 要专门检查“所有 antecedent 都为假”的残余合法区：看 5
- 有 `%`、加减乘等 C `int` 中间表达式时，要专门压边界检查 UB：看 6

## 1. 覆盖所有控制分支

如果正例没有覆盖所有实现分支，eval 很容易把单分支 spec bug 漏掉。生成 case 时，
先按控制流或输入分区划分，再为每个分区至少放一个正例。

## 2. 负例要针对具体子句

负例不要只写“这是错的”。必须明确它违反的是哪条 `Require` 或 `Ensure` 子句，
这样后面的 `evaluation.json` 才能把失败定位到具体 contract 语义。

## 3. 不可判定时要诚实给 `Inconclusive`

如果某条 contract 依赖外部 Coq 谓词、抽象关系或当前 case 无法机械判断的语义，
不能硬判 `Correct`。应把该 case 标成 `needs_judge`，仍无法确定时给
`Spec verdict: Inconclusive`。

## 4. 生成结果后用 `python3` 校验 JSON，不要先试 `jq` / `python`（2026-06-01）

eval 阶段的 `cases.json` 和 `evaluation.json` 是 runner 后续消费的正式产物，生成后应立刻做一次**机器可解析**检查，而不是只看文件存在。

这个环境里不能默认有 `jq`，也不能默认 `python` 命令存在；先试这两个只会白白烧掉失败命令。稳定做法是直接用 `python3`：

```bash
python3 -m json.tool output/eval_<ts>_<name>/cases/cases.json >/dev/null
python3 -m json.tool output/eval_<ts>_<name>/evaluation/evaluation.json >/dev/null
```

如果还要顺手核对 case 数和 verdict 覆盖，也直接用 `python3` 读 JSON：

```bash
python3 - <<'PY'
import json
from pathlib import Path
base = Path("output/eval_<ts>_<name>")
cases = json.loads((base / "cases/cases.json").read_text())
evaluation = json.loads((base / "evaluation/evaluation.json").read_text())
print(len(cases["positive"]), len(cases["negative"]), len(evaluation["cases"]))
PY
```

这条经验同时解决两件事：

- 正确性：尽早发现 JSON 语法损坏、字段漏写、case 数不匹配；
- 效率：避免先撞 `jq: command not found` / `python: command not found`，把校验一步做完。

## 5. 蕴含式 `Ensure` 要专门检查“所有 antecedent 都为假”的残余合法区（2026-06-02）

如果 contract 把后条件写成多条 implication：

- `cond1 => post1`
- `cond2 => post2`
- ...

eval 不要只按“看起来列出来的分支”生成正负例；还要额外检查 **是否存在满足 `Require`、但让所有 `condi` 都为假的合法输入区**。

这是 implication 规格最容易漏掉的 under-spec 形态：实现在该区域有真实行为，但 spec 因为所有 antecedent 都是假而真值真空成立，导致错误输出也会被接受。

稳定检查法：

1. 先把 valid input domain 按实现控制流或语义分区列全；
2. 再逐条对照 `Ensure` antecedent，确认每个分区至少命中一条 postcondition；
3. 如果某个合法分区一条都命不中，必须补一个正例确认真实返回值；
4. 同时补一个该分区的错误输出负例，检查 spec 会不会真空接受。

典型信号：

- positive case 通过，但对应 path 没有专属 clause；
- negative case 的错误输出仍被接受；
- `Path coverage`、`Negative rejection`、`Completeness` 同时失败。

这条规则尤其适合：

- 多分支纯标量函数；
- 用 `=>` 编码 case split 的 contract；
- 某个主分支还要按额外 flag / status 再细分的情况。

## 6. 有 `%`、加减乘等 C `int` 中间表达式时，要专门压边界检查 UB（2026-06-02）

eval 不要只看 contract 的语义分支覆盖；只要实现里真的执行了 C `int` 中间表达式，例如：

- `(a + b) % n`
- `(x - y + n) % n`
- `i * stride + base`

就要额外检查 admitted 输入域是否让这些**中间值**越过 `[-2147483648, 2147483647]`。

原因：

- contract 的正负例替换通常只能说明子句语义自洽；
- 但 eval 的最终 judge 按 C 语义看 soundness；
- 如果 contract 放进了会触发 signed overflow / UB 的状态，哪怕所有正负例都过，judge 仍会在 `Precondition safety` / `Soundness` / `Completeness` 上打回。

稳定做法：

1. 先从 `Require` 推出每个已执行中间表达式的范围；
2. 对每个表达式单独问：最大值和最小值是否仍在 32-bit signed `int` 范围内；
3. 如果边界刚好靠近 `INT_MAX` / `INT_MIN`，至少放一个贴近上界或下界的正例；
4. 如果当前 contract 还没排除溢出状态，在 reasoning / issues 里直接记成 semantic risk，不要因为现有 case 都过就写成完全正确。

典型信号：

- `evaluation.json` 的正负例全过；
- 但实现里有 `+ max_len`、`+ delta`、`* stride` 这类会先在 C 里求值的中间项；
- contract 只约束了抽象输入域，没有给出相应 overflow guard。

这条规则尤其适合：

- 环形缓冲区 / `% n` / 单次 wrap 的标量函数；
- 先做加减再取模的实现；
- 所有“数学上没问题，但 C 中间算术可能先炸掉”的 contract。

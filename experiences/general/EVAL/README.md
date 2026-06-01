# Eval Experience

本文件只记录 eval 阶段的通用经验：如何用具体 case 检查 contract 是否真正刻画了
实现行为。它不记录 verify 的 annotation / proof 技巧，也不记录 audit 的反作弊
结论。

常见入口：

- 覆盖所有控制分支：看 1
- 负例要针对具体子句：看 2
- 不可判定时要诚实给 `Inconclusive`：看 3
- 生成结果后用 `python3` 校验 JSON，不要先试 `jq` / `python`：看 4

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

# Compile Experience

本文件只记录 verify 阶段的 Coq 编译经验。

常见入口：

- 编译前先确认目录：看 1
- 编译参数必须包含两部分：看 2
- 有题目专用 `.v` 时，必须显式给 `original/` load path：看 3
- 长编译命令优先用 bash 数组，不要硬拼引号：看 4
- 当前项目的稳定编译模板：看 5
- 公共 strategy 缺失时再 fallback 到 `coq/deps/`：看 6
- 逻辑前缀必须一致：看 7
- 编译顺序固定：看 8
- `goal_check` 之前不要算完成：看 9
- 重新确认轮次跳过完整 recompile 的条件：看 10
- 编译后必须清理：看 11
- 短名 strategy import 命中多个物理文件时，用 `original/` wrapper 消歧：看 12
- runner 用 bare `coqc` 直编 generated 文件时，短名 strategy import 需要 generated 同目录 wrapper：看 13
- generated 文件短名导入共享 helper 时，helper 要在同一逻辑前缀下预编译：看 14
- runner 同时混用 bare replay 和 prefixed replay 时，共享 helper 需要在 `original/` 与 `generated/` 各保留一份：看 15

## 1. 编译前先确认目录

- 工作目录必须是 `QualifiedCProgramming/SeparationLogic`
- verify workspace 仍然位于仓库顶层 `output/verify_<timestamp>_<name>/`
- 也就是说：QCP 的 Coq 编译从子仓库 `QualifiedCProgramming/SeparationLogic` 发起，但输入/输出 workspace 路径都指向外层仓库
- 当前题目的 generated 文件在 `output/verify_<timestamp>_<name>/coq/generated/`
- 默认直接复用公共 `examples/*.vo`
- 只有公共 strategy 预编译产物缺失时，才回退到 `output/verify_<timestamp>_<name>/coq/deps/`

## 2. 编译参数必须包含两部分

必须同时带上：

- `_CoqProject` 里的基础 `-R`
- 当前 workspace 的额外 `-R`

基础参数缺失时，最常见报错是：

- `Cannot find a physical path bound to logical path int_auto with prefix AUXLib`

这说明少了 `_CoqProject` 里的 `-R auxlibs AUXLib` 等基础 load-path。

## 3. 有题目专用 `.v` 时，必须显式给 `original/` load path

如果当前题目有：

- `output/verify_<timestamp>_<name>/original/<name>.v`

就不能只给 `generated/` 的逻辑前缀。

还必须显式加入：

- `-Q "$ORIG" ""`

否则 `Require Import <name>` 或题目专用数学定义在编译 `proof_manual.v` / `goal_check.v` 时会找不到。

## 4. 长编译命令优先用 bash 数组，不要硬拼引号

长 `coqc` 命令里同时有：

- 多个 `-R`
- `-Q "$ORIG" ""`
- workspace 变量
- 逻辑前缀变量

这时优先用 bash 数组，例如：

- `BASE=(...)`
- `EXTRA=(...)`

原因：

- 避免引号地狱
- 避免路径里空格或变量展开出错
- 命令更容易复制、删改和调试

不要在很长的一行字符串里手工嵌套引号。

## 5. 当前项目的稳定编译模板

在 `QualifiedCProgramming/SeparationLogic` 下执行：

```bash
REPO_ROOT=/path/to/CAV-JAVA
WS="$REPO_ROOT/output/verify_<timestamp>_<name>"
NAME=<name>
GEN="$WS/coq/generated"
ORIG="$WS/original"
LP=SimpleC.EE.CAV.verify_<timestamp>_<name>
BASE=(
  -R SeparationLogic SimpleC.SL
  -R unifysl Logic
  -R sets SetsClass
  -R compcert_lib compcert.lib
  -R auxlibs AUXLib
  -R examples SimpleC.EE
  -R StrategyLib SimpleC.StrategyLib
  -R Common SimpleC.Common
  -R fixedpoints FP
  -R MonadLib MonadLib
  -R listlib ListLib
)
EXTRA=(
  -Q "$ORIG" ""
  -R "$GEN" "$LP"
)

coqc "${BASE[@]}" -Q "$ORIG" "" "$ORIG/${NAME}.v"
coqc "${BASE[@]}" "${EXTRA[@]}" "$GEN/${NAME}_goal.v"
coqc "${BASE[@]}" "${EXTRA[@]}" "$GEN/${NAME}_proof_auto.v"
coqc "${BASE[@]}" "${EXTRA[@]}" "$GEN/${NAME}_proof_manual.v"
coqc "${BASE[@]}" "${EXTRA[@]}" "$GEN/${NAME}_goal_check.v"
```

如果当前题目没有专用 `.v`，就跳过第一条 `coqc`。

不要把 `WS` 再写回 `QualifiedCProgramming/QCP_examples/CAV/output/...` 或 `output/...` 的相对子路径；现在 workspace 已经提升到外层仓库，编译命令应始终使用外层绝对路径。

## 6. 公共 strategy 缺失时再 fallback 到 `coq/deps/`

- 如果公共 `examples/*.vo` 已存在，直接复用，不要再复制到 workspace
- 只有公共 strategy 编译产物缺失或当前环境读不到时，才创建 `coq/deps/`
- fallback 时，把需要的 strategy `.v` 复制到当前 workspace 的 `coq/deps/`
- 然后把编译参数改成：`EXTRA=(-Q "$ORIG" "" -R "$DEPS" SimpleC.EE -R "$GEN" "$LP")`

## 7. 逻辑前缀必须一致

- `coq/deps/` 固定用 `-R "$DEPS" SimpleC.EE`
- `coq/generated/` 固定用 `-R "$GEN" SimpleC.EE.CAV.verify_<timestamp>_<name>`

不要混用不同前缀编出来的 `.vo`，否则常见报错是：

- `contains library X and not library Y`

## 8. 编译顺序固定

1. 先编 `coq/deps/` 里缺的依赖
2. 再编题目专用 `original/<name>.v`，如果存在
3. 再编 `goal.v`
4. 再编 `proof_auto.v`
5. 再编 `proof_manual.v`
6. 最后编 `goal_check.v`

## 9. `goal_check` 之前不要算完成

完成标准必须同时满足：

- `goal.v` 通过
- `proof_auto.v` 通过
- `proof_manual.v` 通过
- `goal_check.v` 通过
- `proof_manual.v` 无 `Admitted.`
- `proof_manual.v` 无新增 `Axiom`

## 10. 重新确认轮次跳过完整 recompile 的条件（2026-05-26）

在 verify 的"precautionary retry"轮次中，如果前一轮**已经确认** Final Result: Success，且进入当前轮次时以下条件全部满足：

1. `coq/generated/` 只含 `.v` 文件，无 `.vo/.glob/.vok/.vos/.aux` 中间产物
2. `proof_manual.v` 中 `Admitted.` 个数为 0（`grep -c "Admitted"` 退出码为 1）
3. `workspace_fingerprint.json` 已通过极简 fingerprint gate
4. `metrics.md` 的 Final Result 为 Success

此时**不必再跑完整 5 步 coqc**。直接核对上述四项，记录为"No new blockers found"后退出即可。

理由：每次 coqc 会生成新的中间产物（`.vo/.glob` 等），随即又需要 cleanup；在 16 个重复轮次中，这一"编译 → 生成中间产物 → 清理"的循环每轮耗时约 1–2 分钟，累计超过 25 分钟，最终因整体 timeout（exit 124）导致 verify 阶段标记为 Fail，尽管证明本身在第一轮 ~22 分钟内就已完成。

唯一例外：如果某轮因 API Overload 或其他故障中途终止（中间产物可能残留），才需要重跑 coqc 以恢复干净状态。

## 11. 编译后必须清理

- `coq/` 下删除非 `.v` 的编译中间产物
- `input/` 下删除非 `.v`、非 `.c` 的编译中间产物
- 如果环境限制导致删不掉，要写进 `logs/issues.md`

## 12. 短名 strategy import 命中多个物理文件时，用 `original/` wrapper 消歧（2026-06-04）

如果 replay 编译在 `goal.v` 的这类头部 import 处立即失败：

- `Require Import int_array_strategy_goal.`
- `Require Import int_array_strategy_proof.`
- `Require Import char_array_strategy_goal.`
- `Require Import char_array_strategy_proof.`

并报同类错误：

- `Required library int_array_strategy_goal matches several files in path`
- `Required library char_array_strategy_goal matches several files in path`

同时冲突出在 `SeparationLogic/examples/` 下多个子目录都提供同名 `.vo`（例如 `QCP_demos_LLM/` 和 `QCP_demos_human/`），不要去改生成出来的 `goal.v` / `proof_auto.v` / `goal_check.v`，也不要改共享 examples 树。

更稳的做法是在当前 workspace 的 `original/` 下放短名 wrapper，让 `-Q "$ORIG" ""` 优先为这些短名提供唯一解析：

例如，`*_goal` wrapper 用：

```coq
From SimpleC.EE.QCP_demos_LLM Require Export <strategy_goal_module>.
```

`*_proof` wrapper 用：

```coq
From SimpleC.EE.QCP_demos_LLM Require Import <strategy_proof_module>.
Include SimpleC.EE.QCP_demos_LLM.<strategy_proof_module>.
```

例如 `char_array` 题可写成：

```coq
From SimpleC.EE.QCP_demos_LLM Require Export char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
Include SimpleC.EE.QCP_demos_LLM.char_array_strategy_proof.
```

使用规则：

- 对所有冲突的 strategy 模块成对补齐 wrapper；不要只补第一个报错文件
- 这类“重名 strategy 消歧”不要放到 workspace-local `coq/deps/` 里做；`coq/deps/` 只用于“公共 strategy 产物缺失”的 fallback，不用于解决 duplicate-path。否则很容易继续踩到逻辑前缀不一致，报 `contains library char_array_strategy_goal and not library SimpleC.EE.char_array_strategy_goal`
- 先编这些 `original/*.v` wrapper，再按常规顺序编 `goal.v -> proof_auto.v -> proof_manual.v -> goal_check.v`
- `goal` 侧优先 `Require Export`，因为后续 generated 文件会继续依赖这些短名
- `proof` 侧需要 `Include ...`，否则 `goal_check.v` 里的 `Include <module>.` 可能找不到期望字段
- 这些 wrapper 的 `.vo` 是 replay 解析路径的一部分；如果清理掉了，后续 retry 会重新退化成 duplicate-path 失败

适用范围：

- 当前 `symexec` 生成了无法控制的短名 strategy import
- 共享 `examples/` 树中确实有重名策略库
- 你又需要保持 generated 文件和共享库原样不动

## 13. runner 用 bare `coqc` 直编 generated 文件时，短名 strategy import 需要 generated 同目录 wrapper（2026-06-05）

如果 verify 自己的 replay 命令能靠：

- `-Q "$ORIG" ""`

让 `original/` 里的短名 wrapper 通过，但 runner / audit log 里实际重放的是：

- `coqc /abs/path/to/original/<name>.v`
- `coqc /abs/path/to/coq/generated/<name>_goal.v`

这种 **bare `coqc` 直编单个 generated 文件** 的模式，那么只在 `original/` 放 wrapper 还不够。`goal.v` 头部的：

- `Require Import char_array_strategy_goal.`
- `Require Import int_array_strategy_goal.`

仍然可能直接落到共享 `examples/` 树里的多个重名 `.vo`，报：

- `Required library char_array_strategy_goal matches several files in path`

更稳的处理方式是：

1. 保留 `original/` wrapper，供标准 `-Q "$ORIG" ""` replay 使用；
2. 再在当前 workspace 的 `coq/generated/` 下放**同名 sibling wrapper**：
   - `*_goal.v`: `From SimpleC.EE.QCP_demos_LLM Require Export <strategy_goal_module>.`
   - `*_proof.v`: `From SimpleC.EE.QCP_demos_LLM Require Import <strategy_proof_module>.` 然后 `Include ...`
3. 先把这些 generated wrapper 编成当前目录下的唯一短名 `.vo`，再跑 bare replay。

判断规则：

- 如果 `audit_check_coqc.log` 显示的是带 `-Q "$ORIG" ""` 的标准 replay，优先用 §12 的 `original/` wrapper；
- 如果 `audit_check_coqc.log` 显示的是 bare `coqc /abs/.../generated/<file>.v`，就把 wrapper 补到 `coq/generated/` 同目录，不要只补 `original/`；
- 不要改 generated 的 `Require Import <short_name>.` 文本本身；消歧应通过 workspace-local wrapper 完成；
- 这种 generated 同目录 wrapper 只用于 **runner replay 解析路径**，不是 `coq/deps/` fallback，也不是新的语义 helper。

## 14. generated 文件短名导入共享 helper 时，helper 要在同一逻辑前缀下预编译（2026-06-05）

如果 generated 文件头部出现这类短名导入：

- `Require Import power_nonnegative.`
- 或其它不是 strategy、而是题目复用的共享数学 helper

并且标准 replay 用的是：

- `-R "$GEN" "$LP"`

那么只把 helper 源文件放进 `coq/generated/` 还不够。`goal.v` / `proof_auto.v` / `proof_manual.v` 在 `-R "$GEN" "$LP"` 下会把这个短名解析成：

- `$LP.power_nonnegative`

如果你先用 bare `coqc coq/generated/power_nonnegative.v` 编过它，生成的 `.vo` 实际库名只是：

- `power_nonnegative`

随后 replay 就会报：

- `The file .../power_nonnegative.vo contains library power_nonnegative and not library $LP.power_nonnegative`

更稳的处理方式是：

1. 把 helper 源文件放在当前 workspace 的 `coq/generated/` 同目录；
2. 用**和 replay 完全一致**的 generated 前缀先单独编它一次：
   - `coqc "${BASE[@]}" -R "$GEN" "$LP" "$GEN/power_nonnegative.v"`
3. 再按常规顺序编 `goal.v -> proof_auto.v -> proof_manual.v -> goal_check.v`；
4. 清理其它 generated 中间产物时，保留这个 helper 的最小必要 replay 依赖（至少保留能被后续 replay 命中的那份 prefixed `.vo`）。

判断规则：

- 报 `Cannot find a physical path bound to logical path <helper>` 时，先看缺的是不是 generated 文件里固化的短名 import；
- 如果 helper 不属于 input/original 的标准 load path，就不要只靠临时 `-Q input ""` 或一次性编译产物；runner replay 看不到这些临时条件；
- 如果已经补了 `coq/generated/<helper>.v` 但又报 `contains library X and not library Y`，优先怀疑是**编译 helper 时用错了逻辑前缀**，不是 helper 内容错；
- 这条适用于共享数学 helper、公共定义桥接等“非 strategy 短名模块”；strategy duplicate-path 冲突仍按 §12-§13 处理。

## 15. runner 同时混用 bare replay 和 prefixed replay 时，共享 helper 需要在 `original/` 与 `generated/` 各保留一份（2026-06-05）

如果 generated 文件头部固化了这类短名导入：

- `Require Import ex_perfect_number_code_helper.`
- 或其它题目局部的共享数学 helper

并且 runner 的两类重放同时存在：

- 审计侧直接跑 bare `coqc /abs/.../original/<name>.v`、`coqc /abs/.../coq/generated/<name>_goal.v`
- 常规 verify replay 仍使用 `-R "$GEN" "$LP"` 编译 generated 文件

那么只在 `coq/generated/` 放 helper 源文件、只保留一份 prefixed `.vo` 仍然不够。bare replay 解析短名时不会自动带上 `$LP` 前缀；反过来，如果你只保留 bare 编出来的 helper `.vo`，标准 replay 又会报：

- `contains library <helper> and not library $LP.<helper>`

更稳的处理方式是：

1. 在 `coq/generated/` 保留 helper 源文件，供 prefixed replay 使用；
2. 用标准 generated 前缀先编出 prefixed helper：
   - `coqc "${BASE[@]}" -R "$GEN" "$LP" "$GEN/<helper>.v"`
3. 在 `original/` 放同内容的 helper 源文件，供 bare short-name replay 使用；
4. 再单独编出 bare helper：
   - `coqc "$ORIG/<helper>.v"`
5. 清理时删除其他中间产物，但保留这两份 replay-critical `.vo`：
   - `coq/generated/<helper>.vo`
   - `original/<helper>.vo`

判断规则：

- 如果 `audit_check_coqc.log` 显示 bare `coqc /abs/.../generated/<file>.v`，不要假设 §14 的 prefixed helper 就足够；
- 如果同一个 `<helper>` 既要被 bare replay 命中，又要被 `-R "$GEN" "$LP"` replay 命中，就把它视为**两个逻辑库名**分别满足；
- 这条只适用于 generated 文件短名导入的 workspace-local helper；strategy 重名冲突仍按 §12-§13 处理。

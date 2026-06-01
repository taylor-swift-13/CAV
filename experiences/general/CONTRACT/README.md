# Contract Experience

本文件只记录 contract 阶段 contract 写法经验。

阶段职责、输入输出边界、强制规则、完成标准，以 [skills/contract/SKILL.md](../../skills/contract/SKILL.md) 为准；这里不重复这些总规则，只补充 contract 的具体写法和判断细节。

职责边界：

- 只记录 `Require` / `Ensure` / `With` 的写法
- 不记录 invariant/assert/symbolic（见 `../INV/README.md`、`../ASSERTION/README.md`、`../SYMEXEC/README.md`）
- 不记录 manual.v 证明（见 `../PROOF/README.md`）
- 不记录最终 Coq 编译（见 `../COMPILE/README.md`）

常见入口：

- QCP 基础表层语言：看 `../QCP/README.md`
- 阅读方式：看 1
- 合同写作重点：看 2
- 方式一：直接 `Extern Coq`：看 3
- 方式二：题目专用 `.v` 桥接：看 4
- 选择规则：看 5
- 先定数学语义，再定前后条件：看 6
- 前置条件优先约束最终结果，而不是穷举中间状态：看 7
- 有抽象语义和具体表示时，优先分两层规格：看 8
- 能用 shape-only 时，不要强行把值语义写满：看 9
- 缺 `.v` 的判断标准：看 10
- 避免在函数级 `Require` 中用顶层析取表达简单数值域：看 11
- QCP 前端不处理 C 预处理器——INT_MIN / INT_MAX 等常量必须改为字面量：看 12
- 后条件优先用蕴含刻画分支，避免证明析取；C 表层用 `=>`：看 13
- `Ensure` 表层不要用 `->`，QCP 蕴含写 `=>`：看 14
- 简单标量 contract 先跑 gate，不要先翻仓库找风格：看 15

## 1. 阅读方式

- 开始 contract 任务时，先从本文件开头顺序读
- 如果只是简单标量/判断函数，先读 `../QCP/README.md`，写最小 contract 后直接跑 gate
- 先看 workspace 约定和规格接入方式
- 再看后面的具体规格经验
## 2. 合同写作重点

- 前置条件里优先明确输入域、长度、内存形状和溢出边界
- 后置条件只写函数语义结果，不提前写 verify 阶段的中间断言
- `With` 只绑定后置确实需要引用的逻辑变量，避免无用绑定

## 3. 方式一：直接 `Extern Coq`

适用场景：
- 仓库公共库里已经有现成的 Coq 数学函数
- C 规格只需要直接引用这个函数
- 不需要额外包装成题目专用 `pre/spec`

典型写法：

```c
/*@ Extern Coq (factorial: Z -> Z) */

int factorial(int n)
/*@ Require
      0 <= n && n <= 10 && emp
    Ensure
      __return == factorial(n@pre) && emp
*/
```

使用原则：
- 优先先查仓库里是否已经有可复用的 Coq 名字
- 如果公共定义已经足够表达题意，就不要再额外创建 `input/<name>.v`
- 这种情况下，`input/<name>.v` 应留空或根本不创建

## 4. 方式二：题目专用 `.v` 桥接

适用场景：
- 题目语义不是一个现成公共函数就能表达
- 需要把自然语言题意包装成稳定的 `pre/spec`
- 需要额外定义辅助关系、辅助谓词或题目专用逻辑名

典型写法分两部分。

`input/<name>.c` 中：

```c
/*@ Extern Coq (factorial: Z -> Z)
               (bfact_coq: Z -> Z) */
/*@ Extern Coq (problem_139_pre_z: Z -> Prop) */
/*@ Extern Coq (problem_139_spec_z: Z -> Z -> Prop) */
/*@ Import Coq Require Import coins_139 */
```

然后在规格里直接用：

```c
/*@ Require
      problem_139_pre_z(n) &&
      1 <= n && n <= 10 && emp
    Ensure
      problem_139_spec_z(n@pre, __return) && emp
*/
```

对应的 `coins_139.v` 中再做桥接：

```coq
Definition problem_139_pre_z (n : Z) : Prop := ...
Definition problem_139_spec_z (n r : Z) : Prop := ...
```

使用原则：
- `.v` 只负责桥接和补题目专用逻辑，不要把本该直接写在 C 规格里的简单内容都搬进去
- 如果只是缺一个公共数学函数名，不要为了形式统一强行新建 `.v`
- 只有当 C 规格明显需要题目专用语义层时，才创建 `input/<name>.v`

## 5. 选择规则

- 公共数学函数已存在：优先用“直接 `Extern Coq`”
- 题目需要专用 `pre/spec` 包装：使用“题目专用 `.v` 桥接”
- 能不用 `.v` 就不用 `.v`；只有确实缺桥接层时才新建

## 6. 先定数学语义，再定前后条件

更稳的 contract 顺序是：

1. 先写清楚函数的数学语义
2. 再决定前置条件需要限制什么
3. 再决定是否需要高层/低层两层规格
4. 最后才把这些落成 `Require` / `Ensure` / `With`

如果数学语义本身没说清楚，后面的 contract 往往会反复返工。

## 7. 前置条件优先约束最终结果，而不是穷举中间状态

对单调累加、乘法递推、前缀构造这类题，前置条件优先约束“最终不会溢出”，通常比逐项约束中间状态更短、更稳。

例如：

- `factorial` 用 `0 <= n <= 10`
- `sum` / `sum2` 这类题优先约束最终闭式值在 `int` 范围内

如果中间状态天然单调且不超过最终状态，这种写法通常足够支撑 Verify 阶段的 safety witness。

## 8. 有抽象语义和具体表示时，优先分两层规格

如果一个题同时存在：

- 对外更自然的抽象语义
- 对实现更自然的具体表示

就优先分成高层语义规格和低层表示规格，不要一开始把两种职责揉在一个谓词里。

这样做的好处是：

- Contract 产出的 contract 对用户更稳定
- Verify 只需要在局部展开实现真正会用到的表示
- 高层语义不会被底层指针或局部更新污染

## 9. 能用 shape-only 时，不要强行把值语义写满

如果题目当前阶段真正需要的是：

- 内存安全
- 结构保持
- 局部可写性

而不是精确内容等价，那么 contract 应优先考虑 shape-only 谓词，不要在 Contract 阶段把值语义写得过满。

这能显著减少 Verify 阶段的 invariant 和 proof 负担。

## 10. 缺 `.v` 的判断标准

判断是否需要 `input/<name>.v`，优先问：

1. 现有公共 Coq 定义能否直接表达题意？
2. 是否真的需要题目专用 `pre/spec` 包装？
3. 是否需要额外的辅助关系或中间语义层？

只有这几个问题里至少一个必须回答“是”，才创建题目专用 `.v`。

参考：
- `factorial` 这类简单整数语义，适合直接 `Extern Coq`
- `QualifiedCProgramming/QCP_examples/humaneval/IntClaude/C_139.c`
- `QualifiedCProgramming/QCP_examples/humaneval/IntClaude/coins_139.v`

## 11. 避免在函数级 `Require` 中用顶层析取表达简单数值域

如果 `Ensure` 或后续 loop invariant 需要使用 `x@pre`，函数级 `Require` 中的顶层析取可能触发 QCP frontend 的 old-value 绑定问题。

已观察到的失败形态：

```c
/*@ Require
      0 <= a &&
      0 <= b &&
      (a != 0 || b != 0) &&
      emp
    Ensure
      gcd_iterative_spec(a@pre, b@pre, __return) && emp
*/
```

`symexec` 在生成 VC 前报：

```text
Old value at `pre' is not determined
```

对照实验表明：

- `a@pre` / `b@pre` 作为 imported Coq predicate 参数本身可以工作
- 去掉顶层析取后，`symexec` 可以生成 VC
- 在 `0 <= a && 0 <= b` 下，把 `(a != 0 || b != 0)` 改写成等价的 `0 < a + b` 后，`symexec` 也可以生成 VC

因此，Contract 阶段遇到简单数值域的“至少一个非零”“至少一个条件成立”时，优先使用无顶层析取的等价表达，尤其是后置条件需要 `@pre` 时。

GCD 的推荐写法：

```c
/*@ Require
      0 <= a &&
      0 <= b &&
      0 < a + b &&
      emp
    Ensure
      gcd_iterative_spec(a@pre, b@pre, __return) && emp
*/
```

不要把这个问题留给 Verify 阶段；这是 contract 编码形状导致的 frontend 问题，不是 loop invariant 或 manual proof 能修复的 Coq 目标。

**后置条件（`Ensure`）中的析取不受此限制**：`(__return == x@pre || __return == -x@pre)` 这类后条件析取可以正常工作，symexec 能正确生成 VC。只有 `Require` 中的顶层析取才会触发 old-value 绑定问题。

## 12. QCP 前端不处理 C 预处理器——INT_MIN / INT_MAX 等常量必须改为字面量（2026-05-26）

QCP 的 `symexec` 前端不运行 C 预处理器，`<limits.h>` 中定义的 `INT_MIN`、`INT_MAX`、`LLONG_MIN` 等符号在 QCP 注释里不可用，会被视为未定义符号。

在 `Require` / `Ensure` / `Inv` 中必须直接使用字面量：

| 常量 | 字面量 |
|------|--------|
| `INT_MIN` | `-2147483648` |
| `INT_MAX` | `2147483647` |
| `UINT_MAX` | `4294967295` |
| `LLONG_MIN` | `-9223372036854775808` |
| `LLONG_MAX` | `9223372036854775807` |

例如，溢出守卫 `x != INT_MIN` 写成 `x >= -2147483647`（等价且 lia 友好）；上界检查 `x <= INT_MAX` 写成 `x <= 2147483647`。

不要把这类符号替换留到 Verify 阶段；这是 Contract 层就该固定的形式。

## 13. 后条件优先用蕴含刻画分支，避免证明析取（2026-05-28）

contract 在**逻辑上正确**和**对下游证明友好**是两件事。`Ensure` 里的顶层析取 `||` 即便语义紧、eval 能放过，也会**强迫 verify 阶段在每个 `return_wit` 里手动用 `Left` / `Right` 选边**——标量 fast path 的 `pre_process; entailer!; try lia.` 不会自动挑分支，coqc 立刻报 "remaining open goals"，整个用例必须回退到 agent。

### 反例：abs_value 的析取写法（这次踩坑）

```c
int abs_value(int x)
/*@ Require x >= -2147483647 && emp
    Ensure  0 <= __return &&
            (__return == x@pre || __return == -x@pre) && emp
*/
```

- 逻辑上紧：`0 <= return` + 「return ∈ {x, -x}」对每个 x 只允许唯一值，等价于 `abs(x)`，eval 通过；
- 但有两个 return wit（C 有两条 return 路径），每条都要选对应的析取分支；
- agent 还易踩坑：QCP 的 SL 析取 introduction 是**大写** `Left` / `Right`（`derivable1_orp_intros1/2`），不是 Coq builtin 的 `left` / `right`，agent 摸索这个就要烧几分钟；
- 实际结果：标量 fast path 失败 → 回退 agent → 262s 才收敛。

### 推荐：语义上按前提分情况，用 `=>`

```c
/*@ Require x >= -2147483647 && emp
    Ensure  (x@pre >= 0 => __return == x@pre) &&
            (x@pre <  0 => __return == -x@pre) && emp
*/
```

这种“每个分支各管一条后条件”的语义仍然是对的：verify 侧最喜欢的就是每条 return path 只需要证明自己那一支。

更干净的写法是把语义函数 Extern 出来：

```
/*@ Extern Coq (abs : Z -> Z) */
...
/*@ Ensure __return == abs(x@pre) && emp */
```

contract 一目了然，verify 端无需任何选边逻辑——前提是要在 §3 或 §4 的方式里把这个 Coq 函数 import 进来。

通用规则：

- 后条件首选**单分支语义**：能直接写语义函数等式就写等式；需要分情况时，用 `=>` 让每条 return path 对应自己那一支结论；
- 仅当**真存在多种合法实现可选**（非确定性 spec、refinement 接口）时才用析取；
- 写析取前先问自己：这道题是「数学上有多个合法答案」还是「只是不想 Extern 函数所以用析取拼出来」？后者就是踩坑前兆。

## 14. `Ensure` 表层不要用 `->`，QCP 蕴含写 `=>`（2026-06-01）

本轮 `xizi_ready_bitmap_empty` 是最简单的标量判零函数，但第一版直接把上面的蕴含写进 C contract：

```c
/*@ Ensure
      (ready_group@pre == 0 -> __return == 1) &&
      (ready_group@pre != 0 -> __return == 0) && emp
*/
```

`python3 scripts/check_spec_wellformed.py` 立刻失败，报 `bison: syntax error, unexpected PT___RETURN`。也就是说：**“按前提分情况”这个想法是对的，但当前 QCP 的 C contract parser 不稳定支持 `->` 这种表层写法。**

因此要分两层看：

- **语义层**：优先让每条 return path 对应单独一支结论，不要把唯一返回值规格写成顶层析取；
- **语法层**：如果 contract 直接写在 C 注释里，蕴含优先写成 QCP 已广泛使用的 `=>`，再跑 gate 确认。

对纯标量分支函数，稳定写法是把“每支一个结论”写成多条蕴含，例如：

```c
/*@ Ensure
      (ready_group@pre == 0 => __return == 1) &&
      (ready_group@pre != 0 => __return == 0) &&
      emp
*/
```

这样比互斥 case 析取更直接：每条路径只需要证明当前前件下的结论，不需要在 `return_wit` 里手工选择 `Left` / `Right`。

这条规则跟 §11、§13 正好成对：**`Require` 顶层析取容易触发前端 old-value 问题；`Ensure` 里的“裸析取多个候选结果”容易触发证明选边问题；而 `Ensure` 表层 `->` 还可能直接触发 parser 问题。优先用 `=>` 刻画分支语义。**

## 15. 简单标量 contract 先跑 gate，不要先翻仓库找风格（2026-06-01）

这类 `emp` precondition + 标量返回值的题，最大的效率损失通常不是写错语义，而是**先花几十次读取去确认“repo 更喜欢哪种风格”**。更快的顺序是：

1. 直接写最小 contract 草稿；
2. 立刻跑 `python3 scripts/check_spec_wellformed.py input/<name>.c`；
3. 按 parser / symexec 的第一条硬错误改写；
4. gate 过了就停，不再继续搜相似例子。

原因很简单：对这类题，真正有信息量的是 gate 是否接受当前 contract dialect，而不是别的题用了哪种表面写法。

如果 gate 报错之外，**确实**还需要看一个模板，优先顺序也要收窄：

1. 先看 `experiences/end-end/` 里**同家族、同形状**的已完成题，尤其是相邻命名的一组小标量判断题；
2. 再看最近一次同类 `output/contract_*` 的 `reasoning.md`；
3. 只有前两者都没有时，才去翻 `QualifiedCProgramming/QCP_examples` 这类泛例子库。

原因：简单标量 contract 的主要问题通常是当前 repo 的 parser / symexec 接受哪种 contract 形状；同家族 end-to-end 题会直接暴露这套约定，而泛例子库只会扩大搜索面，容易把时间烧在无关风格对比上。

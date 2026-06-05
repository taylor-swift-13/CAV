# Contract Experience

本文件只记录 contract 阶段 contract 写法经验。

阶段职责、输入输出边界、强制规则、完成标准，以 [skills/contract/SKILL.md](../../skills/contract/SKILL.md) 为准；这里不重复这些总规则，只补充 contract 的具体写法和判断细节。

职责边界：

- 只记录 `Require` / `Ensure` / `With` 的写法
- 不记录 invariant/assert/symbolic（见 `../INV/README.md`、`../ASSERTION/README.md`、`../SYMEXEC/README.md`）
- 不记录 manual.v 证明（见 `../PROOF/README.md`）
- 不记录最终 Coq 编译（见 `../COMPILE/README.md`）

常见入口：

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
- 后条件能写蕴含就别写析取——析取强迫证明手动选边：看 13
- 输入/输出数组允许重叠时，不要默认用 disjoint `full * full` 收窄语义：看 14
- 乘法扫描循环不能只约束最终乘积范围：看 15
- 宽松流式 parser 的前置条件必须跟真实步进语义对齐：看 16
- `acc = acc * 10 + s[i] - 48` 的每步界必须贴合真实 C 求值顺序：看 17
- verification-friendly rewrite 删除临时缓冲后，不要保留旧容量上界：看 18
- ghost fuel / 终止见证不能替代 concrete `int` 循环计数的范围前提：看 19
- 输出缓冲后条件里，未修改的标量参数优先直接写当前名，不要机械写成 `@pre`：看 20
- `check_spec_wellformed` 的临时目录缺公共头文件时，修 checker staging，不改源码 include：看 21
- 多项 `int` 表达式要分别守每个溢出点，不只守最终结果：看 22

## 1. 阅读方式

- 开始 contract 任务时，先从本文件开头顺序读
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

对单调累加、前缀构造这类中间状态天然单调、且每步都不会超过最终界的题，前置条件优先约束“最终不会溢出”，通常比逐项约束中间状态更短、更稳。

例如：

- `factorial` 用 `0 <= n <= 10`
- `sum` / `sum2` 这类题优先约束最终闭式值在 `int` 范围内

如果中间状态天然单调且不超过最终状态，这种写法通常足够支撑 Verify 阶段的 safety witness。

但不要把这条经验机械套到一般乘法递推上：如果后续因子可能翻转符号或把大值乘回小值，仅约束最终结果在范围内并不能排除中间 prefix 已经发生 C `int` 溢出。此类乘法扫描见 §15。

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

## 13. 后条件能写蕴含就别写析取——析取强迫证明手动选边（2026-05-28）

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

### 推荐：用蕴含按前提分情况

```c
/*@ Require x >= -2147483647 && emp
    Ensure  (x@pre >= 0 -> __return == x@pre) &&
            (x@pre <  0 -> __return == -x@pre) && emp
*/
```

每条蕴含对应 C 的一个分支：`pre_process` 自动按 `x >= 0` / `x < 0` 把 context 切两份，每个 return wit 用 `pre_process; entailer!; try lia.` 直接收尾。**整道题在标量 fast path 上零 agent 跑过**，不再走 4 分钟 sonnet。

### 还更干净：把语义函数 Extern 出来

如果 `.v` 里桥得起 `abs : Z -> Z`，最直白的写法是：

```
/*@ Extern Coq (abs : Z -> Z) */
...
/*@ Ensure __return == abs(x@pre) && emp */
```

contract 一目了然，verify 端无需任何选边逻辑——前提是要在 §3 或 §4 的方式里把这个 Coq 函数 import 进来。

### 通用规则

- 后条件首选**蕴含**（按前提分情况）或**直接等式**（语义函数 Extern）；
- 仅当**真存在多种合法实现可选**（非确定性 spec、refinement 接口）时才用析取；
- 写析取前先问自己：这道题是「数学上有多个合法答案」还是「只是不想 Extern 函数所以用析取拼出来」？后者就是踩坑前兆。

这条规则跟 §13（`Require` 顶层析取触发 old-value 绑定问题）正好成对：**`Require` 顶层析取触发前端问题，`Ensure` 顶层析取触发证明问题，两边都尽量避免**。

## 14. 输入/输出数组允许重叠时，不要默认用 disjoint `full * full` 收窄语义（2026-06-04）

对“读 `a[i]`、写 `out[i]`”这类数组变换题，先不要习惯性写：

```c
IntArray::full(a, n, la) * IntArray::full(out, n, lo)
```

这只适用于**题意本来就要求两段内存不重叠**的接口。若实现对下面这些情况仍有确定行为：

- `a == out`（原地更新）
- `out == a + d * sizeof(int)`（前向重叠）
- `a == out + d * sizeof(int)`（后向重叠）

那么 disjoint `full * full` 会把真实可执行输入排除掉，eval 会把它判成 **precondition 过强 / completeness 不足**。

### 判断规则

先问两个问题：

1. 后续读操作会不会观察到前面写入过的单元？
2. 题目/实现是否明显允许 alias 或 overlap，而不是禁止它？

如果两个答案都是“会/是”，contract 阶段就必须在下面两条路里二选一，**不要拖到 verify 才发现**：

- **完整建模 alias 模式**：在 `Require/Ensure` 中把 disjoint、exact alias、forward overlap、backward overlap 分开写清楚，必要时用题目专用 `.v` 定义“顺序执行后的整段内存变换”；
- **直接收窄接口**：如果你真正想验证的就是“不重叠版 API”，那要把“不允许重叠”当成题意级接口约束写清楚，而不是默认拿 separation ownership 悄悄缩窄语义。

### 实操建议

- overlap 语义通常不是“从原始 source snapshot 复制”，而是“每轮在**当前内存状态**上读 source 再写 destination”；
- 这种情况下，后条件最好写成“整段 region 的最终状态”，不要只写 disjoint 情况下的 `a` 不变、`out` 变换；
- 如果需要同时覆盖多种 alias 布局，通常应尽早准备题目专用 `.v` bridge，把顺序 list-state transformer 放在 Coq 里，而不是只靠 C 注释拼。

这条经验首先是**正确性规则**：否则 eval 会直接指出 contract 不完整；其次也是**效率规则**：verify 才补 overlap 语义，往往已经太晚。

## 15. 乘法扫描循环不能只约束最终乘积范围（2026-06-05）

对这类实现：

- `ret` 从 `1` 开始
- 每轮执行 `ret *= a[i]`
- 后条件写成某个数学乘积函数 `product(l)`

不要只写“最终 `product(l)` 落在 `int` 范围内”。这对 C 有符号乘法通常**不够**，因为某个中间 prefix 可能先溢出，随后又因为乘上 `-1` 或 `0` 回到范围内。

典型反例：

- `l = [-2147483648, -1, 0]`
- 第 2 个 prefix 的数学乘积是 `2147483648`，已经超出 `int`
- 但最终乘积又回到 `0`，说明“最终结果在界内”并不能推出每一步 C 乘法都安全

因此，Contract 阶段应把安全条件写成 **prefix-closed** 形式：对每个 `0 <= k <= n`，都要求 `product(sublist(0, k, l))` 落在 `int` 范围内。

推荐形状：

```c
/*@ Require
      0 <= n &&
      Zlength(l) == n &&
      (forall (k: Z),
        (0 <= k && k <= n) =>
        (-2147483648 <= product(sublist(0, k, l)) &&
         product(sublist(0, k, l)) <= 2147483647)) &&
      IntArray::full(a, n, l)
*/
```

适用范围：

- 乘法累积
- 幂次递推
- 任何中间值不受最终值单调控制的乘法式循环

选择规则：

- 如果能从更简单的输入域直接推出所有 prefix 都在界内，例如 `factorial` 的 `0 <= n <= 10`，优先继续写这个更短的输入域约束
- 如果题目允许负数、零或混合符号，且实现真的逐步做 C `int` 乘法，就不要只约束最终结果，必须显式约束每个 prefix

## 16. 宽松流式 parser 的前置条件要先贴合题目域，再跟真实步进语义对齐（2026-06-05）

对这类实现：

- 外层循环按字节流逐步推进；
- 每轮可能先消费一个 `-`；
- 然后消费一个“尽可能长”的 digit run；
- digit run 允许为空；
- 最后再可选地消费一个分隔符。

contract 的输入域先来自 raw markdown 的题目要求、约束和边界；C 实现用于确定题目域内的可观察行为，以及补齐 C safety 条件。不要在 raw markdown 没有依据时，按“更整洁的题意”额外加强成严格 CSV / 严格 token grammar。否则 contract 很容易把题目未排除且实现**实际会接受并给出确定结果**的输入错误排除掉，eval 会报 `precondition` 过强或 completeness 不足。

典型反例：

- 前导分隔符：`,5`
- 尾随分隔符：`5,`
- 相邻分隔符：`5,,10`
- 只有符号没有 digit：`-`
- 连续符号后再进 digit：`--5`

如果 raw markdown 没有排除这些输入，并且这些输入在实现里都会：

- 继续前进；
- 不越界；
- 不触发 C overflow；
- 并给出确定返回值；

那么 contract 就应该把它们纳入 `pre/spec` 的真实语义，而不是仅因为“这不像标准整数 CSV”就排除。反过来，如果 raw markdown 明确要求“comma-separated base-10 integers”且约定 token 必须非空，那么把 empty field / sign-only token 排除在题目域外是合理的；仍然要补齐 C overflow、数组容量、NUL 终止等 safety 条件。

选择规则：

- **先排除 raw markdown 明确排除的输入**：题目域是 contract 的第一边界。
- **再排除真正不安全或不终止的输入**：例如会导致不前进的非法字符、会触发 C overflow 的 digit 串、会让逻辑字符串和具体 NUL 终止位置失配的内部 `0`。
- **不要无依据排除只是“不好看”的输入**：如果题目没有排除，且实现对 empty field、sign-only step、leading/trailing separator 有定义行为，contract 就应覆盖。

这条经验首先是**正确性规则**：否则 eval 会抓到 contract 不完整；其次也是**效率规则**：verify 之后再补这一层，往往要整套返工 parser 语义。

## 17. `acc = acc * 10 + s[i] - 48` 的每步界必须贴合真实 C 求值顺序（2026-06-05）

对这类实现：

```c
acc = acc * 10 + s[i] - 48;
```

不要只在 contract 里写：

- `parse_digits(tok, 0) <= 2147483647`

这对 safety / completeness 都可能不够，因为 parser 的风险通常发生在**每一步 digit 扩展**，不是只发生在完整 token 结束时。

更关键的是：这里不能只按“数学上的新累加器值”理解更新。对 C 表达式

```c
acc = acc * 10 + s[i] - 48;
```

如果 `acc` 和 `s[i]` 都在有符号 `int` 算术里求值，那么机器实际先检查中间子表达式：

- `acc * 10`
- `acc * 10 + s[i]`
- 最后才减去 `48`

因此，当前 executable code 的 safety 条件不是只有

- `acc * 10 + s[i] - 48 <= 2147483647`

还可能需要更强的中间界：

- `acc * 10 + s[i] <= 2147483647`

典型反例就是边界 token `"2147483647"`：

- 末位前缀 `acc = 214748364`
- 当前字符 `s[i] = 55`（字符 `'7'`）
- 最终新值 `214748364 * 10 + 55 - 48 = 2147483647`
- 但中间和 `214748364 * 10 + 55 = 2147483695 > INT_MAX`

这说明两种常见写法都会出错：

- **只约束最终 token 值**：太弱，verify 会生成更强的机器步 safety VC；
- **只约束数学新值 `acc' = acc * 10 + s[i] - 48`**：对当前 C 写法仍然可能太弱，因为 UB 先发生在减 `48` 之前；

因此，Contract 阶段应优先在下面两条路里二选一，**不要拖到 verify / eval**：

- **按真实 C 子表达式求值顺序写 safety 条件**：如果 executable code 仍是 `acc * 10 + s[i] - 48`，就要保证每个 digit 扩展步连中间子表达式都不溢出；
- **先改实现形状，再按新实现写规格**：例如先算 `digit = s[i] - 48`，再算 `acc = acc * 10 + digit`，或改用更宽的 checked type；然后 contract 跟着新代码写每步界。

判断规则：

- **只看最终 token 值**：太弱，可能漏掉中间步 UB；
- **只看数学上的新 `acc`**：对某些 C 写法仍然太弱；
- **看 executable C 的真实子表达式求值链**：这是稳妥写法。

适用范围：

- 逐字符十进制解析
- `char` / `unsigned char` 直接参加算术累积
- 任何需要在 contract 中逐步约束 prefix accumulator 的 parser / scanner

## 18. verification-friendly rewrite 删除临时缓冲后，不要保留旧容量上界（2026-06-05）

如果原实现先把解析结果写进固定大小的临时数组，例如：

```c
int values[64];
...
values[n++] = parsed;
```

后来为了 verify 友好，把实现改写成**单遍流式累计**，例如“边解析边计数”，那就要重新判断 contract 里的容量约束是不是还真的需要。

不要因为原参考实现里出现过 `values[64]`，就机械地把：

- `token_count <= 64`
- `iteration_count <= 64`
- “最多 64 个字段”

继续留在新的前置条件里。

判断规则：

- 如果**当前实现**仍然会把每个 token/materialized value 存进固定容量缓冲，那么这个上界是安全条件，应保留；
- 如果 rewrite 后**当前实现**已经不再保存整批 token，只保留常数个局部状态（如 `i/sign/v/count`），那旧数组容量通常只是历史实现细节，不再是当前 contract 的必要安全前提。

否则会出现两类问题：

- **正确性问题**：contract 无端排除更长但仍安全、仍终止、且返回值确定的输入；
- **效率问题**：eval 会把它报成 precondition-strength / completeness 失败，后面又得重做 `pre/spec`。

推荐做法：

- 先按**当前 executable code**列出真正会增长的资源：缓冲长度、递归深度、循环计数、算术中间量；
- 只为这些当前仍存在的资源写前置条件；
- 如果旧容量上界只是来自被删除的中间数组，就把它从 contract 里删掉，不要把“原算法形状”误当成“现算法 safety 条件”。

适用范围：

- array-backed 改写成 streaming 的 parser / scanner / aggregator；
- 两遍实现改写成一遍实现；
- 任何为了 verification-friendly proof 而消掉中间存储的重构。

## 19. ghost fuel / 终止见证不能替代 concrete `int` 循环计数的范围前提（2026-06-05）

如果 contract 用 ghost `fuel`、递归深度、或其它 termination witness 来说明“循环最终会停”，但 executable C 里还有一个每轮递增的 `int` 计数器，例如：

```c
int steps = 0;
while (...) {
    ...
    steps++;
}
```

那么**只**写“存在足够大的 witness 使数学语义终止”还不够。Verify 还会生成 concrete C 的自增安全 VC，需要证明：

- `steps + 1 <= 2147483647`

也就是说，contract 必须额外给出一个能推出“总迭代次数 / 返回值 / witness 本身在 `int` 范围内”的前提，而不是把这个范围留给 proof 阶段现推。

这次 `collatz_steps` 的失败形状就是：

- precondition 有 `1 <= n && 0 <= fuel && collatz_safe_fuel(n, fuel)`
- postcondition 用 `collatz_steps_fuel(n@pre, fuel)`
- imported spec 只保证“序列在 fuel 内安全到达终点”
- 但没有任何前提能推出 `collatz_steps_fuel(n, fuel) <= 2147483647` 或 `fuel <= 2147483647`

结果是 loop invariant 和 local helper 都能补齐，最后仍卡在 `steps++` 的 safety witness。

推荐写法二选一：

- 直接约束 witness / 迭代上界本身：例如 `0 <= fuel && fuel <= 2147483647`
- 或约束真正的数学结果界：例如 `collatz_steps_fuel(n, fuel) <= 2147483647`

选择规则：

- 如果 loop counter / return value 本来就等于 ghost witness，优先直接约束 witness 上界；
- 如果 witness 只是“足够大即可”，而实际返回值可能严格小于 witness，优先约束真正的数学 step-count / result-range；
- 不要指望 invariant 里补一个“总答案 <= INT_MAX”就能替代原始 contract：初始化 VC 仍会把它追溯成 contract 必须提供的事实。

适用范围：

- 用 ghost fuel 表达终止的单循环计数题；
- 用递归深度 / remaining budget 驱动规格的 simulator / iterator；
- 任何“数学终止见证”和“C `int` 计数器安全”是两个独立义务的 contract。

## 20. 输出缓冲后条件里，未修改的标量参数优先直接写当前名，不要机械写成 `@pre`（2026-06-05）

对“读输入字符串/数组，向 `out` 写结果字符串”的 contract，如果后条件形状是：

- `__return == Zlength(spec(...))`
- `CharArray::full(out, cap, app(app(spec(...), cons(0, nil)), tail))`
- 以及 `tail` 长度等于 `cap - 1 - Zlength(spec(...))`

并且 `spec` 还依赖某些**函数期间不会被修改**的标量参数（例如 `first`、`out_cap`、固定模式字符等），不要因为“后条件引用旧值”就机械把这些参数全写成 `param@pre`。

这次 `decode_xored_array_csv` 踩到的稳定失败形状是：

```c
/*@ Ensure
      exists t,
        __return == Zlength(decode_xored_array_csv_spec(l, first@pre)) &&
        Zlength(t) == out_cap@pre - 1 -
                     Zlength(decode_xored_array_csv_spec(l, first@pre)) &&
        CharArray::full(out, out_cap@pre,
          app(app(decode_xored_array_csv_spec(l, first@pre), cons(0, nil)), t))
*/
```

这里 `first`、`out_cap` 都是未修改的入参，语义上和当前状态相同；但在这种“`exists tail` + 输出缓冲 ownership + `Zlength(spec(...))`”的组合里，QCP wellformed/symexec 更稳定的写法是直接用当前参数名：

```c
/*@ Ensure
      exists t,
        __return == Zlength(decode_xored_array_csv_spec(l, first)) &&
        Zlength(t) == out_cap - 1 -
                     Zlength(decode_xored_array_csv_spec(l, first)) &&
        CharArray::full(out, out_cap,
          app(app(decode_xored_array_csv_spec(l, first), cons(0, nil)), t))
*/
```

判断规则：

- 如果参数在函数体里**确实没有被赋值/修改**，并且只是在后条件里作为 imported spec 的输入或输出缓冲容量参与长度计算，优先直接写当前名；
- `@pre` 继续保留给真正需要 old-value 语义的对象：被修改的数组/指针内容、会变化的局部状态、或需要显式区分前后状态的标量；
- 不要为了“形式统一”把所有标量都改成 `@pre`，尤其是输出字符串/数组后条件。

这样做的好处：

- 避免 contract 在 `check_spec_wellformed` 阶段就因为 old-value 绑定形状卡住；
- 少掉一轮“wellformed 失败 -> 改回当前参数名 -> 重跑”的无效返工；
- 对 verify 没有语义损失，因为这些参数本来就保持不变。

适用范围：

- `char *out` / `int *out` 这类 caller-provided output buffer；
- 后条件用 `spec(...) + terminator + suffix` 描述输出内容的字符串/数组构造题；
- imported spec 依赖固定输入参数，但函数本身不修改这些参数的 contract。

## 21. `check_spec_wellformed` 的临时目录缺公共头文件时，修 checker staging，不改源码 include（2026-06-05）

如果 contract 阶段的 `check_spec_wellformed` / annotation frontend 在临时目录里报这类错误：

- `../char_array_def.h: No such file or directory`
- `../int_array_def.h: No such file or directory`
- 或其它 repo-root 公共头文件在 temp workspace 中找不到

先不要改 `input/<name>.c` 里的 include 路径。

这次 `defang_ip_address` 的稳定现象是：

- 源文件本身使用 repo 约定的相对路径，例如 `#include "../char_array_def.h"`；
- 这个写法对顶层 `input/` / `annotated/` 是正确的；
- 失败发生在 contract checker 自己构造的 `.tmp/` 目录里，它没有自动带上 repo-root 头文件。

更稳的修法是：

1. 保持源码 include 不变；
2. 把 checker 运行所需的 repo-root 公共头文件镜像到这次检查使用的临时目录；
3. 如果 staging helper 会把 `../char_array_def.h` / `../int_array_def.h` 这类 include 改写成同目录短名（如 `char_array_def.h`），就把这些**改写后的 basename 头文件**也一起放到 temp C 文件旁边；
4. 重新跑 `check_spec_wellformed`，确认只是 staging 问题，而不是 contract 本身有误。

不要采用的修法：

- 把源码 include 改成只对当前 `.tmp/` 目录偶然成立的路径；
- 为了让 contract gate 通过而改坏 `input/` / `annotated/` 的统一 include 约定；
- 把这种 staging 缺文件问题误判成 verify 阶段 annotation / proof 问题。

判断规则：

- 如果同一个 `#include "../..._def.h"` 在顶层源码布局里本来正确，但只在 checker 临时目录失败，优先修 checker staging；
- 如果 checker 自己做了 include 重写，就同时检查“重写后的文件名”是否真的被 staged 到位；
- 只有当顶层 `input/` 或 `annotated/` 本身也解析不到头文件时，才回 source/setup 检查源码 include。

这样做的好处：

- 保持 contract/source 与 verify/source-integrity 的统一路径约定；
- 避免为了适配单次 temp workspace 而污染正式源码；
- 减少“改 include -> 后续 verify / replay 再坏一次”的无效返工。

## 22. 多项 `int` 表达式要分别守每个溢出点，不只守最终结果（2026-06-05）

对 loop-free 标量/分支函数，如果实现直接计算一个包含多个 signed `int` 子表达式的式子，不要只在 contract 里约束“最终数学结果在界内”。

这次 `ex_darts_score` 的稳定形状是：

```c
int d = x * x + y * y;
```

这里有三个独立的 UB 点：

- `x * x`
- `y * y`
- `(x * x) + (y * y)`

只约束最终 `x * x + y * y <= 2147483647` 还不够；如果某个乘法本身已经溢出，后面的求和约束就失去意义了。反过来，只给每个输入一个粗范围、保证单个平方不溢出，也仍然不足以保证最终加法安全。

更稳的写法是按**真实执行顺序**把 guard 拆开：

- 先约束每个会参与乘法的输入，使每个乘法各自有定义；
- 再额外约束组合后的最终和，使最后一次加法也有定义。

对平方和这类形状，可直接写成：

```c
/*@ Require
      -46340 <= x && x <= 46340 &&
      -46340 <= y && y <= 46340 &&
      x * x + y * y <= 2147483647 &&
      emp
*/
```

判断规则：

- 一个 executable C 表达式里只要有多个 signed overflow 风险点，就逐个检查每个子表达式，而不是把所有安全性折叠成一句“最终值合法”；
- 如果前面的子表达式会被后面的表达式继续消费，contract 必须同时覆盖“前一步已定义”和“后一步继续定义”；
- 对非负子项（平方、绝对值、计数等）的组合，通常不需要额外下界，但上界仍要分别覆盖每一步。

适用范围：

- `x * x + y * y`、`a * b + c * d`、`u + v + w` 这类多项 signed `int` 表达式；
- 按阈值分段返回的纯标量 classifier；
- 其它“无循环，但一条初始化表达式就包含多个算术 UB 点”的 contract。
## 23. 规格优先用「量词 + 已定义函数」写输入输出关系,而非重写实现(2026-06-05)

写后条件时,**首选用已有部件刻画"输出和输入满足什么关系",而不是把函数实现再写一遍**。优先级:

1. **已定义函数 / 谓词 + 量词**(`Permutation`、`Znth`、`app`、`Zlength`、`sublist`、连接/`join`、`sorted`、`In` 等)+ `exists` / `forall` —— 首选。
2. 现有部件 + 一点算术。
3. **题目专用 `Fixpoint` / `Inductive` —— 仅当关系实在无法用上面两层表达时的最后手段。** 新写的递归既要自己证性质,又是 §30/PROOF 里那些"递归 helper 归纳"痛点的来源,能不写就不写。

### 关键技巧:写逆关系 / 特征性质,而不是正向实现

很多"难以正向定义"的函数,其**逆运算很简单且常已存在**。用"存在输出,使得 `逆(输出) = 输入` ∧ 附加约束"来唯一刻画,比正向递归实现简单得多,也更好证。

### 例 1:按空格拆分字符串 → 字符串数组(用 `join` 的逆,不写 `split`)

不要定义 `Fixpoint split_spaces (s : list Z) : list (list Z) := ...`。改用已定义的连接函数 `join_sep`(用分隔符把字符串数组连回一个大串)反向刻画:

```c
/*@ Extern Coq (join_sep : list (list Z) -> Z -> list Z) */   /* 已有:用分隔符连接,递归简单 */
/*@ Extern Coq (no_sep   : list (list Z) -> Z -> Prop) */     /* 每段都不含该分隔符 */
int split_by_space(char *s, int n, char **parts)
/*@ With (l : list Z)
    Require CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure exists (ps : list (list Z)),
             join_sep(ps, 32) == l &&        /* 关系:拆出来的段用空格连回去 == 原串 */
             no_sep(ps, 32) &&               /* 约束:每段不含空格 32 */
             __return == Zlength ps          /* + parts 数组表示 ps 的空间断言 */
*/
```

要点:`∃ ps, join_sep(ps,空格)=输入 ∧ 每段无空格` **唯一刻画**了正确的拆分,而 `join_sep` 比 `split` 简单/常已定义。这就是"输入输出关系"而非"实现形式"。

### 例 2:数组排序(用 `Permutation` + 量词,不写 `sort`)

不要定义排序算法。用已有的 `Permutation`(重排关系)+ `forall`(有序性)刻画:

```c
int sort(int *a, int n)
/*@ With (l : list Z)
    Require IntArray::full(a, n, l)
    Ensure exists (l' : list Z),
             Permutation(l, l') &&                                          /* 已定义:是原数组的重排 */
             (forall i j, 0 <= i -> i <= j -> j < n -> Znth i l' 0 <= Znth j l' 0) &&  /* 量词:升序 */
             IntArray::full(a, n, l')
*/
```

要点:`Permutation(l, l') ∧ (∀ i≤j, l'[i] ≤ l'[j])` 完整刻画"排序后的数组",全程用已定义谓词 + 量词,**没有任何 `Fixpoint`**。

### 反面(尽量避免)

```coq
(* 把实现照抄成递归——除非真没别的写法,否则不要 *)
Fixpoint my_split (s : list Z) (acc : list Z) : list (list Z) := match s with ... end.
```
正向递归实现 = 既要在 contract 引入新定义,又要在 verify 阶段为它的每条性质做归纳证明(见 PROOF §30),成本远高于"量词 + 已有逆函数"。

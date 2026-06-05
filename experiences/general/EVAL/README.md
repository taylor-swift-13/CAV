# Eval Experience

本文件只记录 eval 阶段的通用经验：如何用具体 case 检查 contract 是否真正刻画了
实现行为。它不记录 verify 的 annotation / proof 技巧，也不记录 audit 的反作弊
结论。

常见入口：

- 覆盖所有控制分支：看 1
- 负例要针对具体子句：看 2
- 不可判定时要诚实给 `Inconclusive`：看 3
- 宽松 parser 要先按 raw 题目域筛选，再用“看似 malformed 但实现会前进”的 case 测 completeness：看 4
- 数字扫描题要用边界 token 区分“数学结果可表示”和“C 中间表达式已溢出”：看 5

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

## 4. 宽松 parser 要先按 raw 题目域筛选，再用“看似 malformed 但实现会前进”的 case 测 completeness（2026-06-05）

对按字符流扫描的 parser / scanner，不要只用“标准 grammar 内”的正反例测 contract。

如果实现形状是：

- 外层循环按字节推进；
- 每轮可选消费符号；
- digit run 可以为空；
- 再可选消费分隔符；

那么 eval 应先读 raw markdown 的输入要求。若 raw markdown 没有明确排除某类边界输入，再额外挑一组“看起来 malformed，但实现其实会继续前进并给出确定结果”的 case，例如：

- leading separator；
- trailing separator；
- adjacent separator；
- sign-only token；
- 其它 empty-field 变体。

这些 case 的作用不是证明实现“合理”，而是检查 contract 有没有把题目域内、且真实可观察的行为错排除在 precondition 外。

判断规则：

- 如果 raw markdown 没有排除这类输入，且实现对它们会前进、不会越界、不会触发 C overflow，并且返回值确定，那么它们应该优先作为 **precondition-strength / completeness** 检查样例；
- 如果 raw markdown 明确排除了这类输入（例如要求每个 token 是非空 base-10 integer），不要把它们作为合法输入 completeness 反例；可以改测 contract 是否正确表达题目域，以及题目域内的 C safety；
- 不要只把它们当“坏输入”直接丢进 negative rejection；
- 一旦这些 case 属于 raw 题目域、在实现里有定义行为、但被 contract 拒掉，eval 应明确报 contract 过强，而不是只给 soundness/pass。

## 5. 数字扫描题要用边界 token 区分“数学结果可表示”和“C 中间表达式已溢出”（2026-06-05）

对按十进制逐位累加的 parser / scanner，eval 不要只测“最终 parse 出来的整数是否在 `int` 范围内”。

如果实现步进形状是：

- `acc = acc * 10 + s[i] - 48`；
- 或其它先做乘法/加法、最后再减 digit bias 的等价写法；

那么必须专门挑一组边界 token，把下面两类情况拆开测：

- **定义行为但容易被 contract 错拒**：最终 C 步进值和返回值都在范围内，例如这次的 `"2147483600"`；
- **数学结果在范围内，但 C 中间子表达式已先溢出**：例如这次的 `"2147483647"`，最终值是 `INT_MAX`，但末位更新先形成 `214748364 * 10 + 55`。

这些 case 的作用是同时检查两种常见 contract 错误：

- precondition **过强**：把真实定义行为错排除在外；
- precondition **过弱**：只看最终数学值，漏掉 executable C 的中间 overflow UB。

判断规则：

- 只要实现是按字符逐位做有符号 `int` 累加，就至少放一个“定义但接近上界”的正向 completeness case；
- 再至少放一个“最终值看起来合法，但中间子表达式会 overflow”的负向 safety case；
- 如果这两类 case 给出相反结论，优先按 **executable C 的真实求值链** 判 contract 对错，而不是只看逻辑里的最终整数值。

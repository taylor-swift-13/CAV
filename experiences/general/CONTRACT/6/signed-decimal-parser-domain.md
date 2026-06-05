# 带符号十进制字符串解析器的 contract 要先按题目域、再按 C 安全域收前置

适用场景：

- 只读 `char *` / `const char *` NUL 结尾字符串
- 代码按字符扫描十进制 token
- 先做正数累积，再在 token 结束后按 `sign` 取负
- token 之间用逗号或同类分隔符分开

典型症状：

- 自然语义只写“字符串表示一串整数”，verify 之后却在解析循环里卡 safety；
- 或者 eval 报 `Precondition strength` / `Path coverage` / `Completeness` 失败，因为 contract 在题目没有排除时，额外排除了实现实际会处理的输入，例如 `",5"`、`"5,"`、`"1,,2"`、`"-"`；
- 或者 `"2147483647"`、`"-2147483648"`、`"2147483648"` 这类边界字面量在实现里先走正数累积，导致中途就触发有符号溢出。

原因：

- contract 的输入域首先来自 raw markdown 的题目要求、约束、边界和示例；C 实现只是用来确定题目域内的可观察行为和必要安全补充。
- 这类实现的真实安全域不是“任意非零字符串”，也不是“数学上可表示的任意有符号整数串”，也不自动等同于严格 CSV grammar。
- 很多 C parser 每轮是：可选消费 `-`，消费尽可能长的 digit run（允许为空），可选消费一个分隔符，然后进入下一轮。
- 对这种实现，empty field、sign-only token、leading/trailing separator 可能都会前进并产生确定语义，通常会被解析成 `0` 或不额外产生 token；但只有当 raw 题目域没有明确排除这些输入时，contract 才需要覆盖它们。
- 只有真正会导致不前进、越界、数组写爆或 C signed overflow 的输入，才应该被前置排除。
- 如果先累积正 magnitude 再乘 `sign`，那么负数最小值的字面量也必须按“正 magnitude 是否先溢出”来审查，而不能只看最终数学值是否落在 `int` 范围。
- 对 `acc = acc * 10 + s[i] - 48` 这种写法，还必须按 C 子表达式求值顺序检查中间值：`acc * 10` 和 `acc * 10 + s[i]` 都不能溢出，不能只检查最终 `acc * 10 + s[i] - 48`。

规则：

- contract 前置先定义 raw markdown 的题目输入域，再叠加真实 C 步进所需的安全条件，最后定义题目域内的数学语义。
- 前置不要凭空加强题目域；只有当 raw markdown 明确要求严格 CSV，或 C 实现确实要求每轮至少消费一个 digit 才能安全前进时，才写“digit 部分非空、无前导/尾随/相邻分隔符”。
- 对宽松 parser，若 raw markdown 没有排除 empty digit run，`csv_pre(l)` 应该允许实现会安全处理的 empty digit run，并让 `csv_spec(l)` 使用同一套宽松 tokenization。
- 前置里至少要限制：
  - 输入中没有内部 NUL：`forall k, 0 <= k < n -> l[k] != 0`；
  - 每轮循环都会前进，或者到达 NUL 后退出；
  - parsed token 数不超过本地数组容量，例如 `values[64]` 或 `values[128]`；如果实现不写本地 token 数组，不要随手加 64-token 限制；
  - 扫描索引和长度 witness 不会让 `int i` / `i++` 溢出；
  - 每个 digit 扩展步都满足 C 表达式的中间 overflow guard。
- 如果代码是 `acc = acc * 10 + digit`，guard 可以围绕 `digit = s[i] - 48` 后的新累加值写。
- 如果代码是 `acc = acc * 10 + s[i] - 48`，guard 必须覆盖 `acc * 10 + s[i] <= 2147483647` 这类中间表达式；这时 `"2147483647"` 可能需要被排除，除非实现先改成安全的 `digit` 形状或用更宽类型。
- 后置只保留“返回数学规格 + 输入缓冲区不变”，不要把解析中间状态塞回 contract。

最小形状：

```c
/*@ Extern Coq (csv_pre: list Z -> Prop) */
/*@ Extern Coq (csv_spec: list Z -> Z) */
/*@ Import Coq Require Import <task_module> */

/*@ Require
      0 <= n &&
      Zlength(l) == n &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      csv_pre(l) &&
      CharArray::full(nums, n + 1, app(l, cons(0, nil)))
    Ensure
      __return == csv_spec(l) &&
      CharArray::full(nums, n + 1, app(l, cons(0, nil)))
*/
```

其中 `csv_pre(l)` 应该编码：

- raw markdown 明确给出的 tokenization / encoding constraints；
- 在 raw markdown 未明确约束的边界上，与当前 C loop 一致的 tokenization，而不是自行发明更整洁的 CSV 语法；
- empty field / sign-only / leading 或 trailing separator 是否允许，先看 raw markdown 是否排除；若未排除，再看实现是否会安全前进并给出确定结果；
- 每个 digit-prefix 更新都满足当前 C 代码形状的 signed-int safety；
- token 数、输入长度、扫描索引等所有本地数组和 `int` 变量的容量边界。

反例检查：

- `",5"`：如果 raw markdown 没排除 leading separator，且实现先解析空 digit run 为 `0` 再跳过 comma，则 contract 不能把它当 malformed 拒掉。
- `"5,"`：如果 raw markdown 没排除 trailing separator，尾随 comma 后下一轮看到 NUL 退出，通常不会产生额外 token。
- `"1,,2"`：如果 raw markdown 没排除 adjacent separators，中间空字段通常会产生 `0`。
- `"-"`：如果 raw markdown 没要求 token 必须含 digit，sign-only token 通常会产生 `0` 或 `-0`。
- `"2147483647"`：对 `acc = acc * 10 + s[i] - 48`，最终数学值合法，但最后一步中间和 `214748364 * 10 + '7'` 已超过 `INT_MAX`。

适用范围：

- CSV / 分隔符整数串解析
- 先累积 magnitude、后处理符号的 `int` 解析器
- 任何“数学语义看起来合理，但 C 实现的安全域更窄”的字符串状态机题

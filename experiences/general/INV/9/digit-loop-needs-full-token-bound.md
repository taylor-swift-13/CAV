# 十进制 digit loop 的 invariant 不能只记 accumulator 前缀等式

适用场景：

- 字符串状态机按 token 逐段解析十进制数字
- 内层循环形如 `while (s[i] >= '0' && s[i] <= '9')`
- 循环体更新 `acc = acc * 10 + digit`
- contract 已经给了“整个 token 的 magnitude 有界”

典型症状：

- `symexec` 能走通 digit loop，甚至已经生成 `goal.v`；
- 但 `safety_wit` 卡在一步扩展：

```coq
acc * 10 + Znth i (l ++ 0 :: nil) 0 - 48 <= 2147483647
```

- 当前 invariant 里只有：

```coq
acc = parse_digits (sublist start i l) 0
```

这时 proof 看起来只差算术，实际却缺了语义前提。

原因：

- `acc = parse_digits(prefix)` 只说明“当前 accumulator 对应已消费前缀”，不说明“当前 guard digit 仍然属于那个有界 token”。
- 如果 invariant 没保留完整 token witness，`tok` 完全可能在当前位置之前就结束，剩下的 digit 落在别的片段里；此时 `parse_digits(tok, 0) <= INT_MAX` 对下一步更新没有任何约束力。

规则：

- 对这类 digit loop，invariant 要同时保留两层信息：
  - 已消费前缀的 accumulator 等式；
  - 当前正在解析的完整 token 及其边界/上界见证。
- 一个稳定的形状是同时携带：
  - `sublist(start, n, l) == app(tok, tok_rest)`
  - `digit_chars(tok)`
  - `parse_digits(tok, 0) <= 2147483647`
  - `i <= start + Zlength(tok)`
  - `acc == parse_digits(sublist(start, i, l), 0)`
- 如果还要排除“`tok` 太短，当前 digit 其实已经落到后缀里”的退化 witness，再补一个 delimiter-head 事实：
  - `forall x xs, tok_rest == cons(x, xs) => x == 44`

最小形状：

```c
/*@ Inv
      0 <= start && start <= i && i <= n &&
      sublist(start, n, l) == app(tok, tok_rest) &&
      digit_chars(tok) &&
      parse_digits(tok, 0) <= 2147483647 &&
      i <= start + Zlength(tok) &&
      (forall (x: Z) (xs: list Z), tok_rest == cons(x, xs) => x == 44) &&
      acc == parse_digits(sublist(start, i, l), 0) &&
      CharArray::full(nums, n + 1, app(l, cons(0, nil)))
*/
```

为什么这样更稳：

- `acc == parse_digits(sublist(start, i, l), 0)` 负责把当前 C 变量连到已消费 digit 前缀；
- `tok` 的完整见证负责把“下一位 digit 仍在同一个有界 token 内”变成可证明事实；
- delimiter-head 事实能排除 `tok` 过短的伪 witness，避免 proof 在 `i = start + Zlength(tok)` 这种边界分支反复卡住。

效率规则：

- 如果 proof blocker 是这类一步扩展 safety VC，优先回 annotation 把完整 token witness 补齐。
- 不要先绕去加 workspace-local helper 定义“sorted prefix”之类不直接服务于当前 digit 更新安全性的语义；那类 detour 很容易增加 replay 和 proof 维护成本，却不解决真正缺的边界前提。

适用范围：

- CSV / 分隔符十进制解析器
- 先解析 token，再在外层状态机里比较/聚合结果的字符串题
- 任何 safety 依赖“有界完整 token 的前缀扩展”而不是纯最终规格的 digit-accumulation 循环

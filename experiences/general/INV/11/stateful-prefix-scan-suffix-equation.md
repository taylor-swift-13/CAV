# 前缀扫描的最终答案依赖运行状态时，用“当前计数 + 剩余后缀语义 = 全局答案”做 invariant

适用场景：

- `problem_kind = count`
- `data = string` 或只读数组
- `pattern = single_loop`, `prefix_scan`
- 循环每步更新一个运行状态，再在某个状态命中时给答案加一
- 剩余后缀对最终答案的贡献依赖当前运行状态，而不是只依赖已处理前缀

典型症状：

- 直觉上想写 `count == spec(sublist(0, i, l))`
- 但 `symexec` 或 proof 很快发现这个 invariant 太弱：后续还需要知道当前 `balance` / mode / carry，才能解释未处理后缀会再贡献多少答案
- 退出时也很难直接把 prefix-summary 推到全局 `spec(l)`

原因：

- 这类扫描不是纯“前缀累计值 = 前缀规格”
- 已处理部分除了产出 `count`，还留下一个会影响未来行为的运行状态
- 所以 invariant 必须同时保存：
  - 前缀已经积累出的答案；
  - 当前运行状态对应的前缀摘要；
  - 从这个运行状态继续扫描剩余后缀时，还会贡献多少答案

规则：

1. 用索引 `i` 表示已处理前缀长度。
2. 用一个前缀摘要事实固定当前运行状态，例如：
   - `balance == lr_balance(sublist(0, i, l))`
3. 把主语义写成“已完成部分 + 剩余后缀语义 = 全局答案”：
   - `count + go(balance, sublist(i, n, l)) == spec(l)`
4. 再补一组便宜的数值界，把 safety VC 留给 `lia`：
   - `0 <= count && count <= i`
   - `-i <= balance && balance <= i`

最小形状：

```c
/*@ Inv
      0 <= i && i <= n &&
      0 <= count && count <= i &&
      -i <= balance && balance <= i &&
      balance == lr_balance(sublist(0, i, l)) &&
      count + balanced_string_split_count_go(balance, sublist(i, n, l)) ==
      balanced_string_split_count_spec(l)
*/
```

proof 侧的稳定分工：

- 先证明一步 prefix helper：`sublist 0 (i + 1)` 如何更新当前运行状态
- 再证明一步 suffix helper：`go state (sublist i n l)` 如何展开当前字符
- 退出时先证明 `i = n`，再把后缀化成 `nil`，最后由 invariant 推出 `count == spec(l)`

不要退回下面这种过弱形状：

```c
/*@ Inv
      ...
      count == spec(sublist(0, i, l))
*/
```

因为它把“未来答案还依赖当前状态”这个事实丢掉了，后续 witness 只能在 proof 里重新发明状态语义。

适用范围：

- balanced string split
- 扫描过程中维护括号/符号 balance 的计数题
- 任何“prefix scan + stateful residual semantics”的只读循环

# 读数组计数扫描的 invariant 要保留稳定纯事实

Date: `2026-06-05`

对“只读数组 + 单索引前向扫描 + 计数/累加器”等题，循环 invariant 只写前缀语义：

- `count == spec(sublist(0, i, l))`
- `IntArray::full(a, n, l)`
- `a == a@pre`
- `n == n@pre`

通常还不够。若后续 branch witness 或 return witness 需要一步扩展前缀、改写 `Znth` / `sublist`，生成的 VC 可能已经不再显式暴露：

- `Zlength(l) == n`
- `n <= INT_MAX`（或当前 proof 真正依赖的同类 machine-int 上界）

症状是 `symexec` 能过，但 `proof_manual.v` 在前缀扩展 lemma 的 side condition 处卡住，只剩数组谓词和前缀摘要，必须从 `IntArray::full` 里反向抠长度/范围事实。

更稳的规则是：如果这些纯事实在循环中保持不变，而且后续 proof 会直接用到，就把它们一起保留在 invariant 里，而不是指望 proof 层再从空间谓词或 local store 里重建。

最小形状：

```c
/*@ Inv Assert
      a == a@pre &&
      n == n@pre &&
      0 <= i && i <= n &&
      Zlength(l) == n &&
      n <= INT_MAX &&
      count == array_count_odd_spec(sublist(0, i, l)) &&
      IntArray::full(a, n, l)
*/
```

适用范围：

- read-only array scan
- accumulator 表示“已处理前缀摘要”
- manual proof 需要 one-step prefix lemma、`sublist_self`、`Znth` 边界或 `int` 上界

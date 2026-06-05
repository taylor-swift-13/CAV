# 字符串 parser 的 digit-loop cutpoint 里不要直接写 `nums[i]` 或 `l[i]`

适用场景：

- `data = string`
- `pattern = state_machine`
- 代码按字符扫描十进制 token，例如：
  - 可选 `'-'`
  - `while ('0' <= s[i] && s[i] <= '9')`
  - 逗号跳过
  - 重复解析下一个 token
- verify 侧已经有 `CharArray::full(..., app(l, cons(0, nil)))`

典型症状：

- 裸代码或较弱 invariant 时，`symexec` 本来可以继续推进；
- 一旦在 digit loop 的 `Inv` 或紧贴 guard 的 `Assert` 里加入：
  - `48 <= nums[i] && nums[i] <= 57`
  - `48 <= l[i] && l[i] <= 57`
  - 或任何直接依赖当前索引读取的同类事实
- `symexec` 立刻在 cutpoint 处失败：

```text
fatal error: Cannot infer size of array
```

原因：

- 这类 cutpoint 虽然已经持有整段 `CharArray::full`，但当前前端对“在 annotation 里再次显式索引当前字符”的形状很敏感；
- 无论索引的是程序数组 `nums[i]`，还是逻辑快照 `l[i]`，都可能把本来可接受的 prefix-summary witness 退化成需要额外数组尺寸推断的形状；
- 问题不一定在语义上缺信息，而是在注释形状上触发了 frontend blocker。

规则：

1. digit-loop invariant / branch-local `Assert` 里，优先避免直接出现 `nums[i]`、`l[i]` 这类当前位索引读取。
2. 把“下一步仍然是合法 digit 扩展”的信息改写成 prefix 语义摘要，例如：
   - `parse_digits(sublist(start, i + 1, l), 0) <= 2147483647`
   - `acc == parse_digits(sublist(start, i, l), 0)`
   - 完整 token witness + `i <= start + Zlength(tok)`
3. 如果下一条 proof 还需要 guard 自身的 digit 范围，不要先回到 indexed-read 形状；优先让该范围从完整 token witness、delimiter 事实或 one-step helper lemma 中推出。

最小替换方向：

不要这样写：

```c
/*@ Inv
      ...
      48 <= nums[i] && nums[i] <= 57 &&
      acc * 10 + nums[i] - 48 <= 2147483647
*/
```

也不要这样写：

```c
/*@ Assert
      ...
      48 <= l[i] && l[i] <= 57
*/
```

优先改成：

```c
/*@ Inv
      ...
      acc == parse_digits(sublist(start, i, l), 0) &&
      parse_digits(sublist(start, i + 1, l), 0) <= 2147483647
*/
```

为什么这样更稳：

- `sublist(..., i + 1, l)` 仍然停留在“已消费前缀 / 下一步前缀”的摘要层，不要求前端在注释点重新解释数组索引；
- 这通常足以把一步 digit 扩展 safety VC 交给 proof 侧的局部 rewrite / arithmetic，而不会先在 `symexec` 前端阶段崩掉。

适用范围：

- CSV / 分隔符数字串解析
- 任何“字符扫描 + digit accumulator + 状态机切换”的字符串 verify 题
- 尤其是当 blocker 发生在 cutpoint，而不是发生在 proof 阶段时

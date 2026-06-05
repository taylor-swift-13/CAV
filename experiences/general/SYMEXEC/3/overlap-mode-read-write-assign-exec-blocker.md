# 单循环数组变换把 disjoint / alias / overlap 混在一个 contract 分支里时，`Assign Exec fail` 要尽早回 Contract

症状：

- 函数是单循环数组变换，循环体同时读 `a[i]` 又写 `out[i]`；
- contract 在一个函数里同时覆盖 disjoint、`a == out`、forward overlap、backward overlap；
- `symexec` 在同一条语句上反复在两类错误之间切换：
  - `Cannot derive the precondition of Memory Read`
  - `Assign Exec fail`

常见诱因：

- overlap 模式下，当前轮的读会观察到前几轮刚写进去的值；
- 同一条 C 语句同时承担“按当前 alias 模式读 source”和“写 destination”两件事；
- verify 侧即使把 invariant、`IntArray::seg` 分段、source/destination focused cell、pointer equality、branch-local `Assert` 都补齐，`symexec` 仍可能卡在同一条 read-then-write 语句。

可复用规则：

1. 先做有限的 annotation 级排查：控制点对齐、分段 ownership、source cell、destination cell、必要的 alias 地址等式。
2. 如果 fresh `symexec` 仍长期卡在**同一条** overlap-sensitive 赋值语句，而且 proof/compile 阶段始终不可达，就不要继续靠更多 bridge 形状试错。
3. 这时应回到 Contract / source 设计层，优先考虑：
   - 把 alias 模式拆成更简单的 contract / 独立验证入口；
   - 或把实现改写成 verification-friendly 的“先读临时值，再写目的单元”的小步形式。

最小判断信号：

- 失败点一直是同一条 `out[i] = ...` / `a[i] = ...` 语句；
- 你已经验证过“读缺失”和“写缺失”都能通过局部桥接互相切换，但无法同时消掉；
- fresh `symexec` 从未稳定生成新的 `goal/proof_auto/proof_manual/goal_check`。

适用范围：

- `problem_kind = transform`
- `data = array`
- `pattern = single_loop`
- 尤其是“顺序传播”型 overlap 语义，而不是天然 disjoint 的普通数组复制/扫描

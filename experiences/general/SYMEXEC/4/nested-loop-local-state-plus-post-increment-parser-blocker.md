# 嵌套字符扫描循环里，若内层 invariant 一提到 loop-local 累加器就把后面的 `a[n++] = ...` 读成 `PT_PLUSPLUS`，应尽早回 Contract 改源代码形状

症状：

- 题目是字符串/CSV 解析，外层扫描 token，内层扫描 digit，后面还有数组写入；
- fresh `symexec` 在没有内层 invariant 时先报 `Lack of assertions in some paths for the loop!`，说明内层循环确实需要 summary；
- 但一旦在内层 loop invariant / body-entry `Assert` 里显式保留 loop-local 累加器（例如 `v`，无论写成纯事实、existential carrier、`store(&v, ...)`、更重的 read bridge），前端随后会在**后面未改过的** post-increment 数组写入处报：

```text
fatal error: bison: syntax error, unexpected PT_PLUSPLUS, expecting PT_RBRACK
```

典型源代码形状：

```c
int v = 0;
while (nums[i] >= 48 && nums[i] <= 57) {
    v = v * 10 + nums[i] - 48;
    i++;
}
values[n++] = sign * v;
```

原因判断：

- 这不是普通 proof 卡点，而是 QCP frontend 对“嵌套循环 cutpoint + loop-local 状态 + 后续 `a[n++]`”的解析/同步缺陷；
- 证据是：去掉对局部累加器的保留后，`symexec` 会退回到语义错误（例如 `cannot find the program variable v ...` 或 read precondition 缺失），说明真正需要的信息已经定位清楚；
- 继续在 verify 里换 invariant 语法、换 `Assert`/`Inv`、换 bridge 形状，通常只会在“缺少 `v`”和“`PT_PLUSPLUS` 崩溃”之间来回切换。

可复用规则：

1. 先做有限验证：确认内层循环确实需要 invariant，而不是缺一个普通 bridge assertion。
2. 如果一旦让 invariant/body bridge 显式携带 loop-local 累加器，fresh `symexec` 就稳定在后面的同一条 `a[n++] = ...` 语句报 `PT_PLUSPLUS`，不要继续在 verify 里堆更多 annotation 试错。
3. 直接回 Contract / input 改 executable source shape，把 post-increment 写法拆开，再开新 verify workspace。

推荐改写：

```c
values[n] = sign * v;
n++;
```

最小适用范围：

- `problem_kind = search`
- `data = string`
- `pattern = nested_loop`
- 尤其是“内层累计局部标量，外层稍后把结果写进固定数组”的解析器形状

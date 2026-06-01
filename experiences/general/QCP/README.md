# QCP Basic Language

本文件记录最基础的 QCP contract 表层语言。简单题先看这里，写出最小草稿后直接跑 gate；不要为了确认基础语法先大范围翻 `QCP_examples`。

职责边界：

- 记录 C 文件里的基础 contract / `Inv` / `Assert` 表层写法
- 只覆盖简单标量、数组长度、返回值语义这类 contract 入口
- `Inv` / `Assert` 只给最小语法模板，不记录复杂设计技巧
- 不记录 manual proof / compile replay

常见入口：

- 最小函数 contract：看 1
- 常用表达式：看 2
- `@pre` 和 `__return`：看 3
- 简单分支函数模板：看 4
- 最小 `Inv`：看 5
- 最小 `Assert`：看 6
- 何时需要 `.v`：看 7
- 已知不稳定写法：看 8
- 最小检查流程：看 9

## 1. 最小函数 contract

函数 contract 写在函数声明和函数体之间：

```c
int f(int x)
/*@ Require
      0 <= x &&
      x <= 100 &&
      emp
    Ensure
      __return == x@pre + 1 &&
      emp
*/
{
    return x + 1;
}
```

基本规则：

- `Require` 写输入域、内存形状、溢出边界
- `Ensure` 写返回值和输出状态
- 纯标量函数一般以 `emp` 结束
- 后条件只写函数语义，不提前写 verify 阶段的 `Inv` / `Assert`

## 2. 常用表达式

常用 C contract 表达式：

```c
0 <= x
x < n
x == y
x != y
x + y <= 2147483647
(rear + 1) % max_len == front
P && Q
P || Q
P => Q
```

写法习惯：

- 多个输入约束优先用 `&&` 串起来
- 分支语义优先用 `=>` 拆成多条蕴含
- `||` 只在语义本身确实是析取时使用
- 涉及优先级时主动加括号
- C 预处理器常量不要直接写进 contract；`INT_MAX` 写成 `2147483647`
- 简单题不需要先把语义搬进 `.v`

## 3. `@pre` 和 `__return`

`Ensure` 里引用函数入口时的参数值，用 `x@pre`：

```c
Ensure
  __return == x@pre + y@pre && emp
```

返回值用 `__return`：

```c
Ensure
  0 <= __return &&
  __return <= n@pre &&
  emp
```

经验规则：

- `Require` 里通常直接写参数名，不写 `@pre`
- `Ensure` 里描述输入输出关系时，参数优先写 `@pre`
- 如果实现会修改局部变量，后条件仍应使用入口值刻画语义

## 4. 简单分支函数模板

对返回 `1/0` 的判断函数，优先用多条蕴含刻画每个分支：

```c
int is_empty(int front, int rear)
/*@ Require
      emp
    Ensure
      (front@pre == rear@pre => __return == 1) &&
      (front@pre != rear@pre => __return == 0) &&
      emp
*/
{
    if (front == rear) {
        return 1;
    }
    return 0;
}
```

如果条件本身是析取，把它放在蕴含的前件里；另一支写成互补条件：

```c
Ensure
  ((sp@pre <= stack_start@pre ||
    sp@pre > stack_start@pre + stack_depth@pre) => __return == 1) &&
  (stack_start@pre < sp@pre &&
   sp@pre <= stack_start@pre + stack_depth@pre => __return == 0) &&
  emp
```

这个模板适合 OS 里的简单 bitmap、queue、stack range 判断题。

## 5. 最小 `Inv`

`Inv` 写在循环前，描述每次进入循环判断点前成立的事实：

```c
int sum_to_n(int n)
/*@ Require
      0 <= n &&
      n <= 1000 &&
      emp
    Ensure
      __return == n@pre * (n@pre + 1) / 2 &&
      emp
*/
{
    int i = 0;
    int ret = 0;
    /*@ Inv
          0 <= i &&
          i <= n &&
          n == n@pre &&
          ret == i * (i + 1) / 2 &&
          emp
    */
    while (i < n) {
        i = i + 1;
        ret = ret + i;
    }
    return ret;
}
```

最小 invariant 通常包含四类信息：

- 循环变量边界：`0 <= i && i <= n`
- 参数不变关系：`n == n@pre`
- 状态量语义：`ret == ...`
- 当前内存形状：纯标量函数写 `emp`

`for` 循环同样把 `Inv` 放在 `for` 前，按“初始化后、判断前”的状态写：

```c
int i;
int ret = 0;
/*@ Inv
      0 <= i &&
      i <= n &&
      n == n@pre &&
      ret == i * (i + 1) / 2 &&
      emp
*/
for (i = 0; i < n; ++i) {
    ret = ret + i + 1;
}
```

不要为了没有循环的简单题机械添加 `Inv`。

## 6. 最小 `Assert`

`Assert` 写在某条语句前，用来固定下一步需要消费的事实：

```c
/*@ Assert
      i == n &&
      ret == n@pre * (n@pre + 1) / 2 &&
      emp
*/
return ret;
```

常见用途：

- 循环退出后固定退出条件
- 调函数前整理前置条件
- 在局部表示和下一步需要的形状之间做小桥接

`which implies` 用来把当前资源改写成下一条语句需要的资源形状：

```c
/*@ current_fact && current_shape
    which implies
    next_fact && next_shape
*/
```

使用原则：

- `Assert` 只写后续马上会用的事实
- `which implies` 只做一小步桥接
- 如果需要大段推理，优先回去加强 `Inv`，不要把证明塞进 `Assert`

## 7. 何时需要 `.v`

能直接用 C contract 表达的简单整数关系，不需要 `input/<name>.v`。

只有在下面情况才考虑 `.v`：

- 需要题目专用 Coq 谓词或函数
- 需要复用仓库里已有 Coq 数学定义
- C contract 写不下清楚的抽象语义

直接引用 Coq 名字时，在 C 文件里声明：

```c
/*@ Extern Coq (spec_name: Z -> Z -> Prop) */
/*@ Import Coq Require Import my_spec */
```

对应的 `input/<name>.v` 只放定义和桥接逻辑，不夹带 `Axiom`、`Parameter`、`Admitted` 这类假设。

## 8. 已知不稳定写法

这些写法优先避开，除非 gate 已经证明当前文件可接受：

1. `Ensure` 里的 C 表层 `->`

   ```c
   ready_group@pre == 0 -> __return == 1
   ```

   这个写法曾触发 parser 报错。QCP 表层蕴含优先写 `=>`：

   ```c
   ready_group@pre == 0 => __return == 1
   ```

   简单分支题优先用第 4 节的多条蕴含模板。

2. `Require` 顶层析取

   ```c
   (a != 0 || b != 0) && emp
   ```

   如果后条件还要用 `a@pre` / `b@pre`，可能触发 old-value 绑定问题。简单数值域优先改成等价的合取、蕴含或算术约束，例如 `0 < a + b`。

3. C 预处理器常量

   ```c
   x <= INT_MAX
   ```

   QCP 前端不跑 C 预处理器，写成字面量：

   ```c
   x <= 2147483647
   ```

4. Contract 里调用 C 函数

   简单题先不用函数调用表达 spec。需要抽象语义时，用 Coq 逻辑函数或谓词桥接。

## 9. 最小检查流程

简单 contract 的默认流程：

```bash
python3 scripts/check_spec_wellformed.py input/<name>.c
```

通过标准：

```text
wellformed: well_formed
```

处理顺序：

1. 先写最小 contract
2. 立刻跑 `check_spec_wellformed.py`
3. 如果 parser / symexec 报错，按第一条硬错误改语法
4. gate 过了就停，不继续翻无关例子

如果还需要模板，搜索顺序是：

1. 本文件
2. `experiences/end-end/` 里同家族、同形状题
3. 最近同类 `output/contract_*` 的 `reasoning.md`
4. `QualifiedCProgramming/QCP_examples`

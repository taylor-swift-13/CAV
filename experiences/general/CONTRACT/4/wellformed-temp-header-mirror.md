# `check_spec_wellformed` 会在临时目录里重解析 `../char_array_def.h`

适用场景：

- contract C 在 `input/<name>.c`
- 题目使用 `#include "../char_array_def.h"`（同类 `../*_array_def.h` 也应按同样方式检查）
- contract 阶段运行 `python3 scripts/check_spec_wellformed.py input/<name>.c`

典型症状：

- `input/<name>.c` 本身路径写对了，后续 verify / symexec 也需要保留这条 repo-root include
- 但 contract wellformed gate 仍报：

```text
fatal error: No such file ../char_array_def.h in search path
```

原因：

- `check_spec_wellformed.py` 会把 `input/<name>.c` 复制到临时 `wf_*` 目录再调用 symexec
- 此时 `../char_array_def.h` 不再相对 repo root 解析，而是相对临时目录的父目录解析
- 所以“源码里 include 正确”不等于“wellformed checker 一定能找到 header”

规则：

- 不要为了迁就这个 gate 去改 contract 源码里的 include 形状；字符串/数组题仍应保留：

```c
#include "../char_array_def.h"
```

- 先保持 repo-root include 形状不变，再让临时目录的父目录也能看到同名 header
- 可复用的修复方式是：在当前 `TMPDIR` 对应的临时父目录下放一个指向 repo root header 的同名软链接，然后重跑 wellformed gate

命令形状：

```bash
ln -sf /repo/char_array_def.h "$TMPDIR/char_array_def.h"
python3 scripts/check_spec_wellformed.py input/<name>.c
```

适用边界：

- 这是 contract wellformed gate 的临时目录解析问题，不是 contract 语义问题
- 不要把它“修”成 verify 阶段改 annotated C，也不要把 repo-root include 改成更深的相对路径

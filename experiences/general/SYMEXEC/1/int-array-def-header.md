# `int_array_def.h` 必须从 repo root 正确引用

如果数组题需要 `int_array_def.h`，`input/<name>.c` 必须写：

```c
#include "../int_array_def.h"
```

原因：`input/` 和 `annotated/` 都只比 repo root 深一层，verify 的 source integrity gate 又要求 annotated C 保持 original/input C 的可执行实现不变。因此 contract 阶段必须一次性给出能在两个目录下解析的路径。

不要写：

```c
#include "../../int_array_def.h"
```

从 `annotated/verify_<timestamp>_<name>.c` 出发，这会越过 repo root，导致 `symexec` 报 `No such file ../../int_array_def.h`。也不要在 verify 阶段删除或改写这行 include；那会和 original/input C 不一致，被确定性 audit 拒绝。

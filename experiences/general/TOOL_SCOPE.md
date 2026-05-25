# Dataset Admission Scope

本文档记录当前 `datasets/internal`、`datasets/external`、`datasets/augment`
的入库标准。

核心标准只有两个：

1. C 版本必须落在 QCP 支持能力内。
2. Java 和 Rust 是 C 版本语义的翻译，三种语言必须通过同一批共享测试用例。

OpenJML 和 Verus 的能力不作为 dataset 入库硬门槛；它们用于后续 Java/Rust 侧验证。
因此不要因为 Java 使用 `String`、Rust 使用 `Vec` 就直接剔除题目。入库时先看 C/QCP，
再看三语言行为一致。

## 1. C/QCP 入库范围

QCP 仓库和 CAV 已验证例子显示，C 侧可以覆盖：

- 标量整数、字符和布尔风格的 `int` 返回值。
- `int *` 数组、`char *` 字符串/字符缓冲区、显式长度或 `'\0'` 终止。
- 读数组、写数组、原地更新、输出缓冲区。
- `struct`、单链表、双链表、树类结构，只要有对应 representation predicate。
- 普通指针读写、字段访问、数组索引、指针推进。
- `if`、`while`、`for`、`break`、函数调用。
- 动态分配/释放或抽象分配函数，只要能用 QCP 规格描述所有权、形状和释放义务。

当前默认批量集优先使用 CAV 已经跑通的大量模式：标量、数组、char 字符串、简单循环、
搜索、计数、复制、原地更新、排序、二分、基础动态规划。

## 2. C 侧库函数规则

QCP 可以支持库函数，但库函数要写成 mock/extern，并且只给 contract，不展开真实库实现。
也就是说，`sprintf`、`atoi`、`qsort` 这类函数不是语言层面禁止项；它们需要一个明确的
mock contract 来描述输入、输出缓冲区、返回值、frame 和错误条件。

当前入库规则：

- 如果库函数已有 mock contract 或本次明确生成 mock contract，题目可以入库。
- 如果库函数没有 mock contract，但题目语义简单，可以入库并标记 `needs_mock_contract`。
- 如果题目依赖 I/O、随机数、时间、线程、系统调用，则不入库。

必须过滤：

- `scanf`、`printf`、文件读写等 I/O。
- 随机数、时间、线程、系统调用。

需要标记 mock contract：

- `sprintf` / `snprintf` 等格式化输出。
- `atoi` / `strtol` / `strtok` 等解析。
- `qsort` 等库算法。

`malloc`、`free`、`struct`、链表、树、指针不是自动过滤项。是否入库取决于 C 版本能否
按 QCP 的 representation predicate、pre/post、invariant、assertion 和 proof flow 表达。

## 3. Java/Rust 入库规则

Java 和 Rust 版本是 C 语义的翻译：

- 必须和 C 版本使用同一份 `tests/*.json`。
- 必须在所有共享测试上行为一致。
- 可以使用各自语言的自然表示，如 Java `String`、Rust `Vec`，只要它们表达的是同一题意。
- 不因 Java/Rust 的库使用单独过滤 dataset；这些只影响后续 OpenJML/Verus 验证阶段如何改写或建模。

如果后续要做 Java/OpenJML 或 Rust/Verus 的独立验证，可以再生成验证专用版本；不要把这个
要求混入 dataset 入库筛选。

## 4. 当前生成策略

- `datasets/internal`：来自 CAV/raw 和本地补充题，默认以 CAV/QCP 风格为主。
- `datasets/external`：来自 Exercism/LeetCode/Luogu/FormalBench 风格来源；生成时只用 C/QCP
  硬过滤，Java/Rust 保持行为翻译。
- `datasets/augment`：只保留少量代表性增强；优先用 C 端直接循环表达不同实现策略。

当前 external 的生成脚本会记录被过滤题目：

- `datasets/external/manifest.json`
- `scope.policy == "qcp_c_safe_shared_tests"`
- `qcp_contract == "direct"` 表示 C 端不需要额外 mock contract。
- `qcp_contract == "needs_mock_contract"` 表示 C 端调用了非 I/O 库函数，后续 QCP 验证时要补 mock/extern contract。
- `scope.rejected` 只记录 I/O、随机数、时间、线程、系统调用等真正不入库原因。

## 5. Agent 使用规则

- 选题时先看 C 版本是否适合 QCP。
- Java/Rust 代码必须翻译 C 的题意，不要擅自改变边界条件。
- 测试必须是共享的；三语言任何一个失败都不能入库。
- 如果 C 版本需要复杂 QCP predicate，保留题目可以，但要在后续 contract/verify 阶段补充规格经验。
- Eval 只说明测试行为一致，不等于形式化验证已经完成。

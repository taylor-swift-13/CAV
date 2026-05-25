# Readme Experience

本目录是 Java/OpenJML 经验入口。经验逐条编号,按文件分主题;遇到问题优先按症状
跳到对应文件的某一条,不要从头通读。

## 1. Contract 入口

- `CONTRACT.md` — 把题意转成 Java + JML contract 的经验
- `EVAL.md` — 用具体 harness 静态检查 spec 是否刻画行为

## 2. Verify 入口

- `INV.md` — 循环 invariant 设计
- `ASSERTION.md` — `Assert` / bridge assertion
- `LEMMA.md` — pure helper / lemma 编码
- `OPENJML.md` — 运行 ESC 与读诊断

## 3. 跨阶段

- `AUDIT.md` — 反作弊政策(contract / verify / eval / audit 都适用)
- `OPENJML.md` — 通用 OpenJML 命令与诊断

## 4. 更新规则

- 只写可复用、通用的结论;不写单题一次性细节(可把某题当作规则的出处提一句,但规则本身要能独立成立)。
- 本轮没有学到通用经验时,可以什么都不更新。
- 对已有规则做更正/加强时,直接改原编号条目,不要新增近似重复条目。
- 新增一条后,在该文件的"症状索引"和本 README 第 5 节补一行 `症状 -> 文件 N`。
- 经验在流程末尾由 `scripts/experience_consolidate.py` 统一整理;各阶段 agent 不自行写经验。

## 5. 按症状检索

Contract:
- 该写哪些子句 / 保持题意 -> `CONTRACT.md` 1
- 整数可能溢出 -> `CONTRACT.md` 2、13
- 数组非空 / 下标·长度范围 -> `CONTRACT.md` 3
- `NOT IMPLEMENTED ... \num_of` / 计数·求和·求积结果 -> `CONTRACT.md` 4、6、7
- contract 阶段要不要写 invariant/assert -> `CONTRACT.md` 5
- 良构门 `check_spec_wellformed.py` 报 fatal -> `CONTRACT.md` 8
- 后置条件 / 选择型结果 -> `CONTRACT.md` 10
- frame / `assignable` / `\old` -> `CONTRACT.md` 11

Verify — invariant:
- invariant 的四类内容 -> `INV.md` 1、4
- 扫描 / 数组循环 -> `INV.md` 2、6
- 终止性 / `decreases` -> `INV.md` 3
- 控制点位置与语法(`maintaining`/`loop_writes`) -> `INV.md` 5
- invariant 报 `UndefinedNegativeIndex` 等良构性 -> `INV.md` 7
- 对象 / 类不变式 -> `INV.md` 8

Verify — assertion / lemma:
- 需要 loop-exit / 桥接断言 -> `ASSERTION.md` 1、3
- 失败先看 failure name -> `ASSERTION.md` 4
- 用 pure helper 当 lemma -> `LEMMA.md` 1、2、3
- bodyless lemma 被当假设 -> `LEMMA.md` 5、`AUDIT.md` 4
- model method / field / ghost -> `LEMMA.md` 6、7、8

Verify — OpenJML 诊断:
- public spec 引用 private 字段 -> `OPENJML.md` 2、9
- 算术溢出 -> `OPENJML.md` 3、`CONTRACT.md` 13
- 循环证明失败 -> `OPENJML.md` 4、`INV.md`
- `\num_of` / `\sum` 部分实现 -> `OPENJML.md` 5、`CONTRACT.md` 4
- `assignable` 失败 -> `OPENJML.md` 6
- `PossiblyNullDeReference` 等运行期检查名 -> `OPENJML.md` 8
- nullness 失败 -> `OPENJML.md` 10
- exit 0 是否就算成功 -> `OPENJML.md` 7、`AUDIT.md` 2

Eval:
- 要生成多少 case / 正反例怎么写 -> `EVAL.md` 1、2、3
- eval 终判条件 -> `EVAL.md` 9

Audit / 反作弊:
- 禁止项清单 -> `AUDIT.md` 1
- 扫描器与门禁 -> `AUDIT.md` 2
- `assume` 危险 -> `AUDIT.md` 3
- 空泛证明 / 不可达路径 -> `AUDIT.md` 6

# 可用库一览(写 contract / 写证明)

`QualifiedCProgramming/SeparationLogic/` 下的库,按"写 contract(`Require`/`Ensure` 里能用的谓词/函数)"和"写证明(`proof_manual.v` 里能用的引理/tactic)"两用途归类。谓词的**详细用法**见 `doc/predict/*`;本文件是库级地图 + import。

编译 load-path 见 `experiences/general/COMPILE/README.md §5`。import 形式:`From <前缀> Require Import <模块>.` 或 `Require Import <前缀>.<模块>.`

## 库 → 模块前缀 → 用途

| 目录 | 前缀 | 主要用途 |
|---|---|---|
| `SeparationLogic` | `SimpleC.SL` | ★ 数组/字符串/标量/map 谓词 + entailment tactic(契约+证明核心) |
| `listlib` | `ListLib` | ★ 纯列表函数(`Znth`/`sublist`/…)+ 下标引理(契约语义+证明) |
| `auxlibs` | `AUXLib` | Int/Z 范围 + 位运算引理 + tactic + 二叉树 |
| `MaxMinLib` | `MaxMinLib` | 最大/最小值语义 + 引理 |
| `compcert_lib` | `compcert.lib` | `Int.min_signed`/`max_signed`、Z 算术(Integers/Coqlib/Zbits) |
| `sets` | `SetsClass` | 集合语义(∈/⊆/∪/∩)——集合值规格 |
| `MonadLib` | `MonadLib` | 单子(状态/计算语义,少用) |
| `fixedpoints` | `FP` | 不动点(递归谓词的语义底座) |
| `unifysl` | `Logic` | 底层逻辑 `derivable1_*`/`logic_equiv_*`(硬 entailment 才用) |
| `examples` | `SimpleC.EE` | 领域谓词:`sll`/`dll`/`store_tree`/`store_queue`/`store_expr`(多在子目录;另见自动生成 VC,**不当库用**) |
| `Common`/`StrategyLib`/`GraphLib` | … | 内部支撑 / strategy / 图(图类题才用) |

## 一、写 contract 能用的(`Require` / `Ensure`)

**空间谓词(数组/字符串/链表/树/队列/表达式)→ 选型见 `doc/predict/INDEX.md`**(本文件不重复;那里有按数据结构的选型表 + 各 `*_def.h`)。底层模块:数组在 `SimpleC.SL` ArrayLib、字符串在 StringLib、`store_map` 在 MapLib、领域谓词在 `SimpleC.EE`。

predict 未覆盖、写规格常用的**纯函数 / 语义部件**(本文件补充):
- 标量 mapsto(`SimpleC.SL` StoreAux):`x # Int |-> v`、`# Char`/`# UInt`/`# Ptr`/`# Int64`,未定义态 `x # Int |->_`
- 纯列表函数(`ListLib`):`Znth i l d`、`Zlength l`、`sublist lo hi l`、`replace_Znth i x l`、`Znth_error`、`app`(`++`)
- 最大/最小(`MaxMinLib`):`max_value_of_subset` / `min_value_of_subset`(+ `_with_default`)
- 集合(`SetsClass`):成员/包含/并交——"输出是某集合"类规格
- Int 界(`compcert.lib` Integers):`Int.min_signed` = -2147483648、`Int.max_signed` = 2147483647(QCP 前端不展宏,契约写字面量,见 CONTRACT §12)
- 字符串常量 `store_stringLit`(`SimpleC.SL` StringLib;仓库**无示例**,慎用)

> 写规格优先用"已定义函数 + 量词"表达输入输出关系,少自写 `Fixpoint`/`Inductive`(见 `CONTRACT/README.md §23`)。

## 二、写证明能用的(`proof_manual.v`)

**Entailment tactic(`SimpleC.SL` CommonAssertion / SeparationLogic)**:
- `pre_process`、`entailer!`、`entailer_pure`(纯目标,不做空间归一化,见 PROOF §35)、`pre_process_pure`
- `Exists` / `Intros`(assertion 级 ∃,见 PROOF §17/§31)、`Left` / `Right`、`cancel`、`sep_apply`、`split_pure_spatial`

**标量范围 / 态转换(`SimpleC.SL` StoreAux)**:`store_int_range`(取回 `Int.min_signed<=v<=max_signed`,见 PROOF §33)、`store_int_undef_store_int`(值态→未定义态,见 PROOF §19),char/uint/int64 同名

**数组下标引理(`ListLib`)** — entail/safety 证明高频:`app_Znth1`/`app_Znth2`、`Znth_sublist`(及 `_lt`/`_ge`/`0`)、`Znth0_cons`、`Zlength_app`/`Zlength_cons`/`Zlength_app_cons`、`replace_Znth_Znth`、`sublist_split`/`sublist_single`/`sublist_nil`(见 PROOF §6/§8/§16)

**Int/Z 算术 + 位运算(`AUXLib` int_auto、`compcert.lib`)**:`Z_land_range`/`Z_lor_range`/`Z_lxor_range` 等位运算界;`int_auto` 还带自动化 tactic;Z 除法/取模引理在 stdlib(`Z.div_*`/`Z.rem_*`)

**最大/最小引理(`MaxMinLib`)**、**二叉树(`AUXLib` BinaryTree)**

**底层 entailment(`Logic` / unifysl)**:`derivable1_*`、`logic_equiv_*`、`coq_prop_*`——只有手抠空间蕴含、上面 tactic 收不掉时才下沉到这层

## 找具体引理

库里有就别自己证。按名/用途检索:`doc/retrieval/INDEX.md`(检索规则)+ `doc/predict/INDEX.md`(谓词选型表)。题型相近的完整例子在 `experiences/end-end/`(按目录名检索)。

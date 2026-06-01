# Experience Retrieval Index

本文件记录 Java/OpenJML experience 的检索规则，以及
`logs/workspace_fingerprint.json` 中 `keywords` 的统一三字段受控词表。
JAVA 与 C/QCP 使用同一组 fingerprint key：

- `problem_kind`
- `data`
- `pattern`

## 1. 检索顺序

- 先检索 `/home/yangfp/CAV-JAVA/experiences/end-end/`
- 如果这里没有足够接近的完整 Java/OpenJML 例子，再检索
  `/home/yangfp/CAV-JAVA/examples/`
- 不要一开始就全仓库泛搜

## 2. 什么时候才检索

- Contract 阶段：生成 Java/JML 前先看已完成例子的整体风格。
- Verify 阶段：开始编辑 verified 工作副本前，先检索相似例子。
- Eval 阶段：不要求检索相似例子。
- 如果当前输入和当前 workspace 已经足够推进，不要扩大检索范围。

## 3. 检索时先看什么

检索单元有两种，schema 共享（都用 `semantic_description` + `keywords`）：

- **end-end 样例**：每个 `experiences/end-end/<case>/logs/workspace_fingerprint.json`
- **专题经验**：每个 `experiences/general/<NAME>/<N>/<slug>.fingerprint`

建议顺序：

1. 先看 `keywords`
2. 再看 `semantic_description`
3. 命中 general：直接读对应 `<N>/<slug>.md`
4. 命中 end-end：再展开 `annotation_reasoning.md`、`issues.md` 和相关 Java 文件

## 4. fingerprint 要写什么

每个 verify workspace 的 `logs/workspace_fingerprint.json` 至少应包含：

- workspace 名称
- 输入 Java 文件
- original Java 文件
- verified Java 文件
- class name
- `semantic_description`
- `keywords.problem_kind`
- `keywords.data`
- `keywords.pattern`

## 5. `semantic_description` 怎么写

至少写清楚：

- 程序在做什么
- 输入输出的核心关系
- 关键控制结构
- 边界行为
- 是否修改内存或对象状态
- 关键 JML 证明形态

## 6. `keywords` 受控词表

`problem_kind` 只允许：

- `identity`
- `min_max`
- `count`
- `sum`
- `product`
- `search`
- `compare`
- `transform`
- `partition`
- `sort`
- `prefix`
- `dp`
- `math`

`data` 只允许：

- `scalar`
- `array`
- `string`
- `matrix`
- `linked_list`
- `tree`
- `graph`

`pattern` 只允许：

- `straight_line`
- `branch`
- `single_loop`
- `nested_loop`
- `two_pointers`
- `sliding_window`
- `prefix_scan`
- `binary_search`
- `recursion`
- `state_machine`

## 7. Java/OpenJML 映射约定

- 纯标量无分支方法：`data: scalar`，`pattern: straight_line`
- 纯标量 if/else 方法：`data: scalar`，`pattern: branch`
- 数组遍历：`data: array`，通常 `pattern: single_loop` 或 `prefix_scan`
- 字符串遍历：`data: string`，通常 `pattern: single_loop`
- min/max 选择：`problem_kind: min_max`
- 计数：`problem_kind: count`
- 累加求和：`problem_kind: sum`
- 查找：`problem_kind: search`
- 变换/原地更新：`problem_kind: transform`
- 纯数学关系：`problem_kind: math`

## 8. 示例 fingerprint

```json
{
  "semantic_description": "Computes the maximum of two int inputs without modifying memory. The method uses one branch on input order and returns one of the two inputs.",
  "keywords": {
    "problem_kind": "min_max",
    "data": "scalar",
    "pattern": "branch"
  }
}
```

## 9. `scripts/search_fingerprint.py` 调用方式

脚本同时覆盖 end-end 完整样例和 general 专题经验。默认 `--scope all` 检索两者：

```bash
python3 scripts/search_fingerprint.py --fingerprint output/verify_<timestamp>_<name>/logs/workspace_fingerprint.json
```

`--scope` 可限制范围：

- `--scope all`（默认）：同时检索 end-end 完整样例 + general 专题经验
- `--scope end-end`：只看完整 workspace 样例
- `--scope general`：只看 general 专题经验

输出（`--format paths`）：每行一个匹配路径。end-end 给 case dir，
general 给 `<NAME>/<N>/<slug>.md`。

如果还没有 fingerprint 文件，直接传 keyword 字段：

```bash
python3 scripts/search_fingerprint.py \
  --problem-kind sum --data array --pattern single_loop \
  --semantic-description "Sums all elements of a read-only int[] with one accumulator loop."
```

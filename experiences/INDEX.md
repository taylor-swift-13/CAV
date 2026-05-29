# Experience Retrieval Index

本文件只记录 Java/OpenJML experience 的检索规则，以及
`logs/workspace_fingerprint.json` 中 `keywords` 的受控词表。词表的 key

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

- **end-end 样例**：每个 `experiences/end-end/<case>/logs/workspace_fingerprint.json`（完整 workspace + 路径）
- **专题经验**：每个 `experiences/general/<NAME>/<N>/<slug>.fingerprint`（指向同目录 `<slug>.md`，只放 `semantic_description` 和 `keywords` 两字段）

在选择题目或改写题目表示前，先看：

- `/home/yangfp/CAV-JAVA/experiences/general/TOOL_SCOPE/README.md`

建议顺序：

1. 先看 `keywords`
2. 再看 `semantic_description`
3. 命中 general：直接读对应 `<N>/<slug>.md`（短，已 self-contained）
4. 命中 end-end：再展开 `annotation_reasoning.md`、`issues.md` 和相关 Java 文件

## 4. fingerprint 要写什么

每个 verify workspace 的 `logs/workspace_fingerprint.json` 至少应包含：

- workspace 名称
- 输入 Java 文件
- original Java 文件
- verified Java 文件
- class name
- `semantic_description`
- `keywords`

## 5. `semantic_description` 怎么写

至少写清楚：

- 程序在做什么
- 输入输出的核心关系
- 关键控制结构
- 边界行为
- 是否修改内存或对象状态
- 关键 JML 证明形态

## 6. `keywords` 怎么用

- `keywords` 必须来自下面的受控词表，不要自由发明 key 或 value。
- 先用 `keywords` 过滤，再用自然语言描述判断是否真的相似。
- 一个 key 可以对应单个字符串，或由受控 value 组成的列表。
- 如果当前任务不需要某个维度，就省略该 key。

## 7. `keywords` 受控词表

受控 key 只有这些：

- `algorithm_family`
- `control_flow`
- `data_shape`
- `semantic_intent`
- `proof_pattern`
- `numeric_properties`
- `edge_case_behavior`
- `verification_status`

`algorithm_family` 只允许：

- `identity`
- `selection`
- `counting`
- `accumulation`
- `arithmetic_series`
- `factorial`
- `prefix_sum`
- `simulation`
- `search`
- `two_pointers`
- `dynamic_programming`
- `greedy`
- `recursion`

`control_flow` 只允许：

- `straight_line`
- `if`
- `ternary`
- `for_loop`
- `while_loop`
- `do_while`
- `nested_loop`
- `recursion`

`data_shape` 只允许：

- `scalar_only`
- `array`
- `string`
- `pointer`
- `struct`
- `linked_list`
- `tree`
- `graph`

`semantic_intent` 只允许：

- `return_input`
- `return_max`
- `count_iterations`
- `sum_1_to_n`
- `sum_even_series`
- `compute_factorial`
- `preserve_input`
- `in_place_update`

`proof_pattern` 只允许：

- `pure_arithmetic`
- `loop_invariant`
- `case_split`
- `termination_by_bound`
- `closed_form`
- `monotonicity`
- `range_bound`
- `heap_reasoning`

`numeric_properties` 只允许：

- `nonnegative_input`
- `overflow_guard`
- `int_range`
- `monotone_accumulator`
- `exact_closed_form`

`edge_case_behavior` 只允许：

- `returns_zero_on_nonpositive`
- `returns_input_on_nonpositive`
- `defined_for_nonnegative_only`
- `branch_on_order`
- `empty_loop_possible`

`verification_status` 只允许：

- `goal_check_passed`
- `proof_check_passed`
- `manual_witness_needed`
- `auto_proof_contains_admitted`
- `generated_goal_contains_axioms`

## 8. Java/OpenJML 映射约定

- OpenJML ESC 通过时，`verification_status` 使用
  `goal_check_passed` 和 `proof_check_passed`。
- 没有循环的分支证明使用 `proof_pattern: case_split`。
- 防溢出 precondition 使用 `numeric_properties: overflow_guard`。
- Java 数组任务用 `data_shape: array`；字符串任务用 `data_shape:
  string`；纯标量任务用 `data_shape: scalar_only`。
- 只读方法可用 `semantic_intent: preserve_input`；原地更新方法可用
  `semantic_intent: in_place_update`。

## 9. ABS 示例 fingerprint

```json
{
  "semantic_description": "Computes the absolute value of an int except Integer.MIN_VALUE. The method is read-only, uses an if branch, returns x when x is nonnegative and -x otherwise, and relies on an overflow guard for negation.",
  "keywords": {
    "algorithm_family": "selection",
    "control_flow": "if",
    "data_shape": "scalar_only",
    "semantic_intent": "return_input",
    "proof_pattern": ["case_split", "pure_arithmetic", "range_bound"],
    "numeric_properties": ["overflow_guard", "int_range"],
    "edge_case_behavior": "branch_on_order",
    "verification_status": ["goal_check_passed", "proof_check_passed"]
  }
}
```

## 10. `scripts/search_fingerprint.py` 调用方式

脚本同时覆盖 end-end 完整样例和 general 专题经验。默认 `--scope all` 检索两者：

```bash
python3 scripts/search_fingerprint.py --fingerprint output/verify_<timestamp>_<name>/logs/workspace_fingerprint.json
```

`--scope` 可限制范围：

- `--scope all`（默认）：同时检索 end-end 完整样例 + general 专题经验
- `--scope end-end`：只看完整 workspace 样例
- `--scope general`：只看 general 专题经验

输出（`--format paths`）：每行一个匹配路径。end-end 给 case dir，general 给 `<NAME>/<N>/<slug>.md`。例如：

```text
experiences/end-end/array_sum
experiences/general/INV/4/merge-loop-invariant.md
```

如果还没有 fingerprint 文件，直接传 keyword 字段：

```bash
python3 scripts/search_fingerprint.py \
  --problem-kind sum --data array --pattern single_loop \
  --semantic-description "Sums all elements of a read-only int[] with one accumulator loop."
```

注：`scripts/search_fingerprint.py` 使用上游设计的 3 键 `keywords`（`problem_kind` / `data` / `pattern`），与本文档 §7 的 8 键 Java/OpenJML 受控词表是两套独立的检索 schema。topical fingerprint 文件按 §7 写 8 键 keywords；脚本默认用 3 键过滤。如需扩 schema，统一受控词表后再改 `scripts/search_fingerprint.py` 的 `KEYS` 常量。

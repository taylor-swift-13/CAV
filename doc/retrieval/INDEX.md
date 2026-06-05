# Retrieval Index

本文件只记录检索规则。

## 1. 检索顺序

- 先看仓库内 `experiences/end-end/`：按文件名/语义找最相近的完整例子(目录名基本表意,如 `array_sum`、`string_count_char`、`is_prime_simple`)
- 不够接近再放宽到 `QualifiedCProgramming/QCP_examples/`
- 不要一开始就全仓库泛搜

## 2. 什么时候才检索

- 只有当前步骤卡住、缺相似题思路 / 谓词用法 / witness 结构 / proof pattern 时才检索
- 当前输入和 workspace 已经足够推进,就不要先去搜例子

## 3. 命中后怎么用

- 展开该 case 的 `annotation_reasoning.md`、`proof_reasoning.md`、`issues.md` 和相关 `.v`
- 复用 proof 前**必须比较当前 VC 和旧 VC 主体**——"相似"不等于 VC 相同

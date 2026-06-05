# Mode: Finalize pass (eval)

只在 prompt 顶部出现 `Compute results: <path>` 时生效。表示上一轮 eval 提交了 `evaluation/compute_queries.json`，runner 已用 Coq `vm_compute` 求值完毕，本轮要把结果折回 evaluation 并定稿。

## 处理流程

1. 读 prompt 给出的 `Compute results:` 路径文件——内容是每条 query 的归一化结果（bool / Z / list / 错误信息）。
2. 对每条 result：
   - 找到 `evaluation/evaluation.json` 里对应 `id` 的 case 和 clause；
   - 把原 `needs_judge` 改写成 `pass` 或 `fail`（依据归一形）；
   - `evaluated` 字段填实际归一值（不再是占位）。
3. 把所有 `needs_judge` 都消化干净后，再写 `logs/final_result.md` 的 `Spec verdict:`。如果 vm_compute 报错（如类型不对、缺 import），不要直接 `pass`/`fail`——写 `judge: {verdict: needs_judge, reason: "vm_compute 错误：..."}` 并把 verdict 报成 `Inconclusive`。
4. 不允许在 finalize pass 里新增 compute_queries（runner 不会再跑第二次 vm_compute）；如果发现还有 computable 没提，记 `logs/issues.md` 并以 `Inconclusive` 收尾。

## 不变的约束

`Spec verdict: Inconclusive` 对应 `Final Result: Fail`（见主 SKILL §7）。日志规范、完成判据按主 SKILL 走。

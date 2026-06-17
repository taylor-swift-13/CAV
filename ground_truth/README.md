# Humaneval Ground Truth 标准

`ground_truth/<problem>` 是最终可验证证明库，不是中间导入缓存。每个 case 入库前必须在新版 QCP 下完整编译通过。

## 来源

- 题目全集以 `/home/yangfp/CAV/C/CAV/input/humaneval` 为准，共 102 题。
- C 函数签名、函数 contract、`Require`/`Ensure` 的 spec 以 `input/humaneval/<problem>.c` 为准。
- Coq spec 辅助文件优先使用 `input/humaneval/<problem>.v`。
- 证明优先从 `/home/yangfp/QualifiedCProgramming/QCP_examples/humaneval` 的完整证明迁移。

## 迁移规则

- 先复制 `input/humaneval` 中对应题目的 C 输入，再补 annotation。
- annotation 可以参考旧 QCP humaneval case，但不能改变 input 的函数签名和函数 contract。
- 如果旧 QCP proof 的 contract 与 input 不一致，以 input 为准改写 proof。
- 只有 contract 不同、函数名/变量名不同、annotation 形状不同，或新版 QCP API 不兼容时，才修改旧证明。
- 旧证明中的 helper lemma 要尽量复用；例如 `coins_N.v` 中真正用于证明的定义和 lemma 可以迁移成 case 根目录下的 `<problem>.v`。
- 旧 QCP `deps/` 不作为 ground truth 内容保留，除非确实是该题必要且已验证的本地 support 文件。
- 新版 QCP 生成的 assertion 使用引号形式，旧 `[| ... |]` 不能直接入库。
- `proof_auto.v` 是 symexec 生成的占位证明文件，可以保留生成的 `Admitted`，不要手写 auto 证明。
- 人工迁移和修改的目标是 `proof_manual.v` 以及必要的 support `.v`；`proof_manual.v` 不允许出现 `Admitted`、`admit`、`Abort` 或自造 `Axiom`。

## 验收

每个 case 必须用新版 QCP 重新跑 symexec 并编译：

```bash
python3 scripts/verify_ground_truth_humaneval.py --problem <problem> --timeout 180 --keep-workspace
```

只有输出 `Success stage=verified` 才算通过。只迁移文件、只跑旧 QCP、或只通过 `run_verify` 的 proof-only fast path 都不算 ground truth 通过。
验证脚本始终使用 fresh symexec 生成的 `proof_auto.v`，只用 ground truth 中的 `proof_manual.v` 覆盖 generated manual proof。

批量完成时运行：

```bash
python3 scripts/verify_ground_truth_humaneval.py --timeout 180
```

要求 102 题全部 `Success`。

## 目录内容

每个 `ground_truth/<problem>` 只保留必要文件：

- `<problem>.c`
- `<problem>_goal.v`
- `<problem>_proof_auto.v`
- `<problem>_proof_manual.v`
- `<problem>_goal_check.v`
- 必要的 case-local support `.v`
- `verify_ground_truth.log`

不保留 `manifest.json`，也不把冗余旧 QCP workspace/deps 作为完成标准。

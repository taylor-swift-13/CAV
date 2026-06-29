# DLC Humaneval Ground Truth 标准

`ground_truth/<problem>` 是最终可验证证明库，不是中间导入缓存。每个 case 入库前必须在新版 QCP 下完整编译通过。

## 来源

- DLC 只保留主分支 `/home/yangfp/CAV/C/CAV/ground_truth` 中没有的 case。
- 当前 DLC 数据来自 `/home/yangfp/QualifiedCProgramming/QCP_examples/humaneval/multi_dimensional_arrays` 中已证明通过的 11 个多维数组 case。
- C 输入、annotation、ground truth、QCP workspace 必须只覆盖这 11 个 case；102 题旧数据不能保留。
- DLC 的 QCP 子模块使用原版 `/home/yangfp/CAV/DLC/CAV/QualifiedCProgramming`，remote 为 `QinxiangCao/QualifiedCProgramming`。不要把子模块切到 `lixing-hust/QualifiedCProgramming`。
- 可以从 `/home/yangfp/QualifiedCProgramming/QCP_examples/humaneval/multi_dimensional_arrays` 迁移证明代码，但不能把 lixing 版 QCP 库改动迁移到 DLC 子模块库文件。
- `input/humaneval` 是模型输入，只保留题目 contract、`Extern Coq` 和 `Import Coq` 等必要接口；循环 invariant、内部 `Assert`、库调用处的 `where` hint 应由模型填写，不能预先放在 input 中。
- `annotated_input/humaneval` 和 `ground_truth/<problem>` 保留已验证 annotation。

## 迁移规则

- 每个问题目录使用真实题名，例如 `p087_get_row`，不要保留 `coins_N` 文件名。
- 旧证明中的 helper lemma 要尽量复用；例如 `coins_N.v` 中真正用于证明的定义和 lemma 迁移成 case 根目录下的 `<problem>.v`。
- 不在原版 QCP `string_lib.v` 等库文件里的定义，必须放到问题私有 `<problem>.v` 中，例如 p007 的 `substring_at` / `strstr_result`。
- 旧 QCP `deps/` 不作为 ground truth 内容保留；QCP workspace 中的 `deps/<problem>.v` 只是编译 staging。
- 新版 QCP 生成的 assertion 使用引号形式，旧 `[| ... |]` 不能直接入库。
- `proof_auto.v` 是 symexec 生成的占位证明文件，可以保留生成的 `Admitted`，不要手写 auto 证明。
- 人工迁移和修改的目标是 `proof_manual.v` 以及必要的 support `.v`；`proof_manual.v` 不允许出现 `Admitted`、`admit`、`Abort` 或自造 `Axiom`。

## 验收

每个 case 必须在 DLC 子模块的原版 QCP 下编译对应 workspace：

```bash
cd /home/yangfp/CAV/DLC/CAV/QualifiedCProgramming/SeparationLogic
coqc \
  -Q examples/CAV/<workspace>/deps "" \
  -R SeparationLogic SimpleC.SL \
  -R unifysl Logic \
  -R sets SetsClass \
  -R compcert_lib compcert.lib \
  -R auxlibs AUXLib \
  -R examples SimpleC.EE \
  -R stdlib SimpleC.StdLib \
  -R StrategyLib SimpleC.StrategyLib \
  -R Common SimpleC.Common \
  -R fixedpoints FP \
  -R MonadLib MonadLib \
  -R listlib ListLib \
  examples/CAV/<workspace>/<file>.v
```

每个 workspace 需要依次编译：

- `deps/<problem>.v`
- `<problem>_goal.v`
- `<problem>_proof_auto.v`
- `<problem>_proof_manual.v`
- `<problem>_goal_check.v`

编译结果必须放在对应问题目录内：

```text
ground_truth/<problem>/verify_ground_truth.log
```

每个 log 必须包含 5 个 `[OK]`，且不能包含 `[FAIL]` 或 `Error:`。不要只在 `ground_truth/` 根目录放总 log。

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

## 当前 Case

- `p007_filter_by_substring`
- `p012_longest`
- `p014_all_prefixes`
- `p028_concatenate`
- `p029_filter_by_prefix`
- `p074_total_match`
- `p087_get_row`
- `p095_check_dict_case`
- `p115_max_fill`
- `p129_minPath`
- `p158_find_max`

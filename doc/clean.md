# Clean Output/CAV Mirror

## 使用

清理前先确认正在跑的批量和 runner：

```bash
ps -eo pid=,ppid=,stat=,etime=,args= | rg 'batch_safe_|run_verify.py|run_proof.py|run_pipeline.py|run_contract.py'
```

只清理不在跑的 workspace/mirror 目录。正在跑的 workspace basename 必须保留，例如出现在进程参数或批量日志里的：

- `verify_*`
- `proof_*`
- `pipeline_*`
- `contract_*`
- `eval_*`

小 `.out` 日志也可以清理，但只清理未被当前进程打开、大小不超过 1KB 的文件。

## 清理范围

可以清理：

- `output/` 下面的 workspace 目录。
- `QualifiedCProgramming/QCP_examples/CAV/` 下面的 mirror 目录。
- `QualifiedCProgramming/SeparationLogic/examples/CAV/` 下面的 mirror 目录。
- `output/` 下面不超过 1KB 且未被打开的 `.out` 文件。
- `results/`、`proof_results/`、`pipeline_results/` 下面不超过 1KB 且未被打开的 `.out` 文件。

不清理：

- `results/`、`proof_results/`、`pipeline_results/` 里面的结果目录。
- 正在被进程打开的 `.out` 文件。
- 大于 1KB 的 `.out` 文件。
- 锁目录，例如 `output/.dlc_humaneval_problem_locks`

## 检查 1KB Out

列出当前仓库里不超过 1KB 的 `.out` 文件：

```bash
find output results proof_results pipeline_results \
  -type f -name '*.out' -size -1025c -printf '%s %p\n' 2>/dev/null | sort -n
```

删除前先确认这些文件没有被正在跑的进程打开：

```bash
ps -eo pid=,ppid=,stat=,etime=,args= | rg 'batch_safe_|run_verify.py|run_proof.py|run_pipeline.py|run_contract.py|\\.out'
```

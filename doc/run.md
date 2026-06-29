# Batch-Safe Run Scripts

当前批量入口只有三个：

- `scripts/batch_safe_verify.sh`
- `scripts/batch_safe_proof.sh`
- `scripts/batch_safe_pipeline.sh`

三个脚本都按问题串行运行。`--jobs` 可以传，但实际按 `1` 处理。

## 通用参数

常用环境变量：

```bash
MAX_PROBLEMS=10
FAST_FAIL_SECONDS=120
MAX_FAST_RETRIES=0
QUOTA_SLEEP_SECONDS=18000
```

含义：

- `MAX_PROBLEMS`: 本次最多启动多少个新问题。
- `FAST_FAIL_SECONDS`: 在这个秒数内失败，按 quota/network 快失败处理。
- `MAX_FAST_RETRIES`: 快失败后最多重试几次。
- `QUOTA_SLEEP_SECONDS`: 快失败重试前等待多久。
- `--force`: 忽略已有结果，强制重新跑。

推荐 quota 敏感运行：

```bash
FAST_FAIL_SECONDS=120 MAX_FAST_RETRIES=0
```

建议用 `tmux`：

```bash
tmux new-session -d -s verify54 \
  "FAST_FAIL_SECONDS=120 MAX_FAST_RETRIES=0 scripts/batch_safe_verify.sh codex-54-medium"
```

停止标记：

```bash
touch output/stop_<config>.flag
touch output/stop_proof_<config>.flag
touch output/stop_pipeline_<config>.flag
touch output/stop_all_batch_safe.flag
```

## Verify

命令：

```bash
scripts/batch_safe_verify.sh [options] <config> [problem_name ...]
```

输入：

- `input/<dataset>/<name>.c`
- `input/<dataset>/<name>.v` 如果存在

结果目录：

- `results/<agent>/<model>/<effort>/verify_*_<name>`

示例：

```bash
scripts/batch_safe_verify.sh codex-54-medium p087_get_row
scripts/batch_safe_verify.sh codex-55-xhigh
scripts/batch_safe_verify.sh kimi-thinking p014_all_prefixes
scripts/batch_safe_verify.sh ark-1-glm p029_filter_by_prefix
```

常用参数：

```bash
DATASET=humaneval
RESULTS_ROOT=/path/to/results
TIMEOUT=5400
```

## Proof

命令：

```bash
scripts/batch_safe_proof.sh [options] <config> [problem_name ...]
```

输入：

- `annotated_input/<dataset>/<name>.c`
- `annotated_input/<dataset>/<name>.v` 如果存在

结果目录：

- `proof_results/<agent>/<model>/<effort>/proof_*_<name>`

示例：

```bash
scripts/batch_safe_proof.sh codex-54-medium p087_get_row
scripts/batch_safe_proof.sh codex-55-medium
scripts/batch_safe_proof.sh kimi-thinking p014_all_prefixes
```

常用参数：

```bash
DATASET=humaneval
ANNOTATED_ROOT=/path/to/annotated_input
RESULTS_ROOT=/path/to/proof_results
TIMEOUT=5400
```

## Pipeline

命令：

```bash
scripts/batch_safe_pipeline.sh [options] [config|all] [problem_name ...]
```

输入：

- `raw/<dataset>/<name>.md`

结果目录：

- `pipeline_results/<agent>/<model>/<effort>/pipeline_*_<name>`
- `pipeline_results/<agent>/<model>/<effort>/contract_*_<name>`
- `pipeline_results/<agent>/<model>/<effort>/eval_*_<name>`
- `pipeline_results/<agent>/<model>/<effort>/verify_*_<name>`

流程：

```text
contract -> eval -> verify
```

示例：

```bash
scripts/batch_safe_pipeline.sh codex-54-medium p014_all_prefixes
scripts/batch_safe_pipeline.sh --dataset mbpp codex-54-mini-medium mbpp_511_find_Min_Sum
scripts/batch_safe_pipeline.sh --skip-eval codex-54-medium p012_longest
```

常用参数：

```bash
DATASET=humaneval
PIPELINE_RESULTS_ROOT=/path/to/pipeline_results
CONTRACT_TIMEOUT=1800
EVAL_TIMEOUT=900
VERIFY_TIMEOUT=3600
```

## DLC Scheduler

DLC 自动调度入口：

```bash
scripts/cav_auto_scheduler.sh
```

调度器会直接启动：

- `scripts/batch_safe_verify.sh`
- `scripts/batch_safe_proof.sh`
- `scripts/batch_safe_pipeline.sh`

日志写到：

```bash
output/batch_safe_*_auto_<timestamp>.out
```

## 清理

清理 `output/` 和 CAV mirror 的规则与本次结果见 [clean.md](clean.md)。

## 检查

查看正在跑的批量/runner 进程：

```bash
ps -eo pid=,ppid=,stat=,etime=,args= | rg 'batch_safe_|run_verify.py|run_proof.py|run_pipeline.py|run_contract.py'
```

统计结果：

```bash
find results/codex/gpt-5.4/medium -maxdepth 1 -type d -name 'verify_*' | wc -l
find proof_results/codex/gpt-5.4/medium -maxdepth 1 -type d -name 'proof_*' | wc -l
find pipeline_results/codex/gpt-5.4/medium -maxdepth 1 -type d -name 'pipeline_*' | wc -l
```

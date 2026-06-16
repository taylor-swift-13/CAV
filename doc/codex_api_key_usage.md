# 用 Ark API 跑 Verify 实验

> Ark 等第三方 API 必须改走 Claude Code 配置后再启动；`ark` / `codex-ark-api` 入口已在
> `scripts/verify_agent_copy_results.sh` 中禁用，避免误跑到 Codex。

本仓库用 `scripts/verify_agent_copy_results.sh` 统一启动实验、去重并自动复制结果。Ark API 的配置名是：

```bash
codex-ark-api
```

别名：

```bash
ark
```

## 配置文件

Ark API 配置放在：

```text
config/ark_api/ark.config.toml
config/ark_api/agents_ark.json
output/codex_ark_wrapper.sh
```

`config/ark_api/ark.config.toml` 是本地私有文件，包含 API key，结构如下：

```toml
model = "ark-code-latest"
model_provider = "ark"
api_key = "<ARK_API_KEY>"

[model_providers.ark]
name = "Volcengine Ark Coding"
base_url = "https://ark.cn-beijing.volces.com/api/coding/v3"
env_key = "ARK_API_KEY"
```

保持私有配置权限：

```bash
chmod 600 config/ark_api/ark.config.toml
```

## 跑实验

单线程跑一题：

```bash
tmux new-session -d -s verify_codex_ark_api_p005 \
  "cd /home/yangfp/CAV/C/CAV && BATCH_LOG_SUFFIX=single_p005 ./scripts/verify_agent_copy_results.sh --jobs 1 codex-ark-api p005_intersperse"
```

也可以前台跑：

```bash
./scripts/verify_agent_copy_results.sh --jobs 1 codex-ark-api p005_intersperse
```

跑多题：

```bash
tmux new-session -d -s verify_codex_ark_api_batch \
  "cd /home/yangfp/CAV/C/CAV && BATCH_LOG_SUFFIX=ark_batch ./scripts/verify_agent_copy_results.sh --jobs 1 codex-ark-api p005_intersperse p003_below_zero"
```

## 结果位置

完成后自动归档到：

```text
results/codex/ark-code-latest/api/
```

运行中的 workspace 在：

```text
output/verify_<timestamp>_<problem>
```

复制成功后脚本会清理对应的 `output/`、`annotated/` 和 QCP mirror workspace。

## 查看状态

```bash
tmux ls
tmux attach -t verify_codex_ark_api_p005
tail -f output/verify_batch_codex_ark_api_single_p005.out
```

确认模型：

```bash
ps -ef | rg 'ark-code-latest|codex_ark_wrapper|run_verify.py'
```

结果 metrics 里应看到：

```text
Agent: codex
Model: ark-code-latest
Reasoning effort: api
```

这里的 `api` 只是 results/metrics 的配置标签，不是 Ark 的真实 reasoning effort。

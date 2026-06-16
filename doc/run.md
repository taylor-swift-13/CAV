# Verify Agent Result Batch

This run compares Codex `gpt-5.4 high` and Kimi on relatively simple
HumanEval verify tasks.

`scripts/verify_agent_copy_results.sh` runs one verify agent/model config, copies
finished workspaces into `results/<agent>/<model>/<effort>/`, then removes the
matching `output/`, `annotated/`, and QCP mirror workspaces. Existing matching
results are skipped unless `--force` is passed.

## Selection Rule

For every model/config, select new problems by comparing only against that
same model/config's own result directory. Do not exclude a problem merely
because another model or agent has already run it.

Examples:

- Codex `gpt-5.4 high` must not repeat problems already present under
  `results/codex/gpt-5.4/high`.
- Kimi `kimi-code/kimi-for-coding` with `thinking` must not repeat problems
  already present under
  `results/kimicode/kimi-code__kimi-for-coding/thinking`.

This rule applies to every model/config: use that config's own
`results/<agent>/<model>/<effort>/` directory as its deduplication set. Two
different configs may run the same problem unless a run explicitly says
otherwise.

Within the remaining candidates, prefer smaller
`input/humaneval/<name>.c` plus `input/humaneval/<name>.v` total file size as
the simple-task heuristic.

## Historical Selected Problems

The original comparison list below was chosen from problems missing in both:

- `results/codex/gpt-5.4/high`
- `results/kimicode/kimi-code__kimi-for-coding/thinking`

The heuristic was smaller `input/humaneval/<name>.c` plus `<name>.v` size.

```bash
PROBLEMS=(
  p150_x_or_y
  p052_below_threshold
  p055_fib
  p076_is_simple_power
  p135_can_arrange
  p082_prime_length
  p085_add
  p048_is_palindrome
  p131_digits
  p100_make_a_pile
)

REVERSED_PROBLEMS=(
  p100_make_a_pile
  p131_digits
  p048_is_palindrome
  p085_add
  p082_prime_length
  p135_can_arrange
  p076_is_simple_power
  p055_fib
  p052_below_threshold
  p150_x_or_y
)
```

## Run Commands

Use `tmux` so the runs survive shell/session exits.

Codex uses two workers and the normal order:

```bash
tmux new-session -d -s verify_codex_54_high_10 \
  "cd /home/yangfp/CAV/C/CAV && ./scripts/verify_agent_copy_results.sh --jobs 2 codex-54-high p150_x_or_y p052_below_threshold p055_fib p076_is_simple_power p135_can_arrange p082_prime_length p085_add p048_is_palindrome p131_digits p100_make_a_pile"
```

Kimi uses one worker and the reverse order:

```bash
tmux new-session -d -s verify_kimi_thinking_10 \
  "cd /home/yangfp/CAV/C/CAV && ./scripts/verify_agent_copy_results.sh --jobs 1 kimi-thinking p100_make_a_pile p131_digits p048_is_palindrome p085_add p082_prime_length p135_can_arrange p076_is_simple_power p055_fib p052_below_threshold p150_x_or_y"
```

## Current Run

Started in tmux at `2026-06-13 06:49:31 +0800`.

Sessions:

```bash
tmux ls
tmux attach -t verify_codex_54_high_10
tmux attach -t verify_kimi_thinking_10
```

Current expected first tasks:

- Codex: `p150_x_or_y`, `p052_below_threshold`
- Kimi: `p100_make_a_pile`

Logs:

```bash
tail -f output/verify_batch_codex_54_high.out
tail -f output/verify_batch_kimi_thinking.out
```

Check active processes:

```bash
ps -ef | rg 'verify_agent_copy_results|run_verify.py|agent_loop.py'
```

Stop the runs if needed:

```bash
tmux kill-session -t verify_codex_54_high_10
tmux kill-session -t verify_kimi_thinking_10
```

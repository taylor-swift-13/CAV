# Weighted scan accumulators need a progress-sensitive safety bound

Symptom:

- A read-only string/array scan keeps a residual semantic invariant such as
  `spec(l) == scan(sublist(i, Zlength(l), l), pos, sum)`.
- Each accepted character adds a weighted contribution to `sum`, for example
  `sum += weight(pos) * value(ch)`.
- `symexec` succeeds, but the branch-step VC still asks for a next-state bound
  like `sum + weight(pos) * value(ch) <= B`, and manual proof gets stuck.

Cause:

- A flat invariant cap such as `sum <= 496` is not inductive for weighted scans.
- The current `sum` may already be close to the global maximum while the current
  `pos` still allows another positive contribution, so `sum <= B` does not imply
  `sum + next_contrib <= B`.
- What the proof really needs is the **maximal prefix contribution at the current
  progress state**, not just a final global maximum.

Rule:

- For single-pass weighted scanners, carry safety as a function of the progress
  variable.
- The invariant should bound `sum` by "the largest checksum reachable after
  exactly `pos` accepted symbols", then prove each branch preserves that bound.
- Keep the residual semantic equation and the progress-sensitive numeric bound
  together; either one alone is usually too weak.

Minimal shape:

```c
/*@ Inv
      0 <= i && i <= n &&
      0 <= pos && pos <= MAX_POS &&
      sum <= prefix_weight_bound(pos) &&
      spec(l) == scan(sublist(i, Zlength(l), l), pos, sum) &&
      CharArray::full((char *)s, n + 1, app(l, cons(0, nil)))
*/
```

For ISBN-10 style weights, a stable bound is not a constant. It must reflect how
many weighted slots have already been consumed. In this run, replacing an
underspecified flat cap with a `pos`-dependent bound was the change that made
the digit-step VC match the executable maximum.

Scope:

- weighted checksum scanners over read-only strings or arrays
- loops where the next update is `acc += step(progress, current_symbol)`
- especially cases with decreasing weights, special terminal symbols, or mixed
  branches where the legal next contribution depends on the current position

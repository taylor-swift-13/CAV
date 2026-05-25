# fb_more_set_leftmost_unset_bit

## Problem

Set the highest zero bit that appears below the highest set bit of `n`; return `n` unchanged if all such bits are already set.

## Requirements

- `1 <= n <= 1000000`.
- Use only integer arithmetic.
- Do not read stdin or write stdout.

## Source

- Source: FormalBenchHF base program `SetLeftMostUnsetBit.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_more_set_leftmost_unset_bit(n: i32) -> i32 {
    if (n & (n + 1)) == 0 { return n; }
    let (mut pos, mut count, mut temp) = (0, 0, n);
    while temp != 0 { if (temp & 1) == 0 { pos = count; } count += 1; temp >>= 1; }
    n | (1 << pos)
}
```

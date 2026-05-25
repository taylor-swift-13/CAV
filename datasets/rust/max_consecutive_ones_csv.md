# max_consecutive_ones_csv

## Problem

Return the longest run of `1` values in comma-separated binary string `bits`.

## Requirements

- `bits` is comma-separated `0` and `1` characters with no spaces.
- The empty string represents an empty array.
- Return the maximum number of adjacent ones.
- Commas are separators and are ignored by the run count.

## Source

- Source: LeetCode problem `max-consecutive-ones`.
- URL: https://leetcode.com/problems/max-consecutive-ones/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn max_consecutive_ones_csv(bits: &str) -> i32 {
    let mut best = 0;
    let mut cur = 0;
    for b in bits.bytes() { if b == b'1' { cur += 1; if cur > best { best = cur; } } else if b == b'0' { cur = 0; } }
    best
}
```

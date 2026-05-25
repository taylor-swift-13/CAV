# fb_easy_unset_bit_count_upto

## Problem

Return the total number of zero bits seen while scanning the binary forms of all integers from `1` through `n`.

## Requirements

- `1 <= n <= 1000`.
- Ignore leading zeros.

## Source

- Source: FormalBenchHF base program `CountUnsetBits.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_easy_unset_bit_count_upto(mut n: i32) -> i32 {
    let mut count = 0;
    for i in 1..=n { let mut temp = i; while temp != 0 { if (temp & 1) == 0 { count += 1; } temp >>= 1; } }
    count
}
```

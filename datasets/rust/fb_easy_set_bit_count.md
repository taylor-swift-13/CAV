# fb_easy_set_bit_count

## Problem

Return the number of set bits in the binary representation of `n`.

## Requirements

- `0 <= n <= 1000000`.
- Ignore leading zeros.

## Source

- Source: FormalBenchHF base program `CountNum.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_easy_set_bit_count(mut n: i32) -> i32 {
    let mut count = 0;
    while n > 0 { if (n & 1) == 1 { count += 1; } n >>= 1; }
    count
}
```

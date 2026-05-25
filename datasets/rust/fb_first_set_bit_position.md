# fb_first_set_bit_position

## Problem

Return the one-based position of the least significant set bit in `n`.

## Requirements

- `1 <= n <= 1000000`.
- The least significant bit has position `1`.

## Source

- Source: FormalBenchHF base program `GetFirstSetBitPos.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_first_set_bit_position(mut n: i32) -> i32 {
    let mut i = 1;
    while n & 1 == 0 { n >>= 1; i += 1; }
    i
}
```

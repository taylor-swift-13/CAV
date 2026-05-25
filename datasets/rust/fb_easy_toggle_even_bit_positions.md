# fb_easy_toggle_even_bit_positions

## Problem

Toggle every even-indexed bit position that exists in the binary representation of `n`, using zero-based bit positions.

## Requirements

- `1 <= n <= 1000000`.
- Only positions below the highest set bit are considered.

## Source

- Source: FormalBenchHF base program `EvenBitToggleNumber.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_easy_toggle_even_bit_positions(mut n: i32) -> i32 {
    let (mut res, mut count, mut temp) = (0, 0, n);
    while temp > 0 { if count % 2 == 0 { res |= 1 << count; } count += 1; temp >>= 1; }
    n ^ res
}
```

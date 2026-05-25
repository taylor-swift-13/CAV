# fb_cube_sum_difference

## Problem

Return `(1^3 + 2^3 + ... + n^3) - (1 + 2 + ... + n)`.

## Requirements

- `1 <= n <= 200`.
- Return the signed 32-bit integer result.

## Source

- Source: FormalBenchHF base program `Difference.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_cube_sum_difference(n: i32) -> i32 {
    let (mut cubes, mut linear) = (0, 0);
    for i in 1..=n { cubes += i * i * i; linear += i; }
    cubes - linear
}
```

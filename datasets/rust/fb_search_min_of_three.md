# fb_search_min_of_three

## Problem

Return the minimum of integers `a`, `b`, and `c`.

## Requirements

- Inputs are signed 32-bit integers.

## Source

- Source: FormalBenchHF base program `MinOfThree.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_search_min_of_three(a: i32, b: i32, c: i32) -> i32 {
    let mut min = a; if b < min { min = b; } if c < min { min = c; } min
}
```

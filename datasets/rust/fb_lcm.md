# fb_lcm

## Problem

Return the least common multiple of positive integers `x` and `y`.

## Requirements

- `1 <= x, y <= 10000`.
- Return the answer as a signed 32-bit integer.

## Source

- Source: FormalBenchHF base program `Lcm.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_lcm(x: i32, y: i32) -> i32 {
    let (mut a, mut b) = (x, y);
    if a > b { let t = a; a = b; b = t; }
    let mut gcd = 1;
    for i in 1..=a { if a % i == 0 && b % i == 0 { gcd = i; } }
    (x * y) / gcd
}
```

# SpecGenBench Ugly Number Flag

## Problem

Return true if `n` is positive and has no prime factors except `2`, `3`, and `5`.

## Requirements

- `n` is a signed 32-bit integer.
- Return false for `n <= 0`.

## Source

- Source: SpecGenBench problem `SpecGenBench/common/UglyNum`.
- URL: file:///home/yangfp/Arc/represent/external/specgen-artifact/benchmark/SpecGenBench/common/UglyNum/UglyNum.java
- License note: local three-language rewrite from local external benchmark.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn sg_ugly_number_flag(mut n: i32) -> bool {
    if n <= 0 { return false; }
    let factors = [2, 3, 5];
    let mut i = 0;
    while i < 3 { while n % factors[i] == 0 { n /= factors[i]; } i += 1; }
    n == 1
}
```

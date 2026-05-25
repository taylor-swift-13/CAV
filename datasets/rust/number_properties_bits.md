# number_properties_bits

## Problem

Return four space-separated bits describing simple divisibility properties of integer `n`.

## Requirements

- `n` is an integer in the small input range used by the original beginner exercise.
- Let `A` mean `n` is even and `B` mean `4 < n <= 12`.
- Return four bits: `A and B`, `A or B`, exactly one of `A/B`, and neither `A nor B`.
- Bits must be separated by one ASCII space with no leading or trailing spaces.

## Source

- Source: Luogu problem `P5710`.
- URL: https://www.luogu.com.cn/problem/P5710
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn number_properties_bits(n: i32) -> String {
    let a = n % 2 == 0;
    let b = n > 4 && n <= 12;
    format!("{} {} {} {}", if a && b {1} else {0}, if a || b {1} else {0}, if a ^ b {1} else {0}, if !a && !b {1} else {0})
}
```

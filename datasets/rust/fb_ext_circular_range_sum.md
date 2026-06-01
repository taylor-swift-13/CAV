# FormalBench Circular Range Sum

## Problem

Return the sum collected by walking from index `left` to index `right` in a circular array.

## Requirements

- `n > 0` and `a` has at least `n` elements.
- `0 <= left, right < n`.
- Include both endpoints.
- The result fits in a signed 32-bit integer.

## Source

- Source: FormalBench problem `FormalBenchHF/base/programs/SumRangeList.java`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: local rewrite from SESpec java_flat.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_ext_circular_range_sum(n: i32, a: &[i32], left: i32, right: i32) -> i32 {
    let mut sum = 0;
    let mut i = left;
    loop {
        sum += a[i as usize];
        if i == right { break; }
        i += 1;
        if i == n { i = 0; }
    }
    sum
}
```

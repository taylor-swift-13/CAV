# fb_array_max_subarray_length

## Problem

Return the length of the contiguous subarray with the largest positive running sum, following the FormalBench zero-baseline scan.

## Requirements

- Array length is at most `50`.
- Array values are signed 32-bit integers.
- Do not read stdin or write stdout.

## Source

- Source: FormalBenchHF base program `MaxSubArraySum.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_array_max_subarray_length(a: &[i32], size: i32) -> i32 {
    let (mut best, mut cur, mut start, mut end, mut s) = (0, 0, 0, 0, 0);
    for i in 0..(size as usize) {
        cur += a[i];
        if best < cur { best = cur; start = s; end = i as i32; }
        if cur < 0 { cur = 0; s = i as i32 + 1; }
    }
    end - start + 1
}
```

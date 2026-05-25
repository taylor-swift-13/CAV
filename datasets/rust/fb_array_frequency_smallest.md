# fb_array_frequency_smallest

## Problem

Return how many times the smallest value appears in the first `n` elements of `arr`.

## Requirements

- Array length is at most `50`.
- Array values are signed 32-bit integers.
- Do not read stdin or write stdout.

## Source

- Source: FormalBenchHF base program `FrequencyOfSmallest.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_array_frequency_smallest(n: i32, arr: &[i32]) -> i32 {
    if n == 0 { return 0; }
    let (mut min, mut count) = (arr[0], 1);
    for i in 1..(n as usize) {
        if min > arr[i] { min = arr[i]; count = 1; }
        else if min == arr[i] { count += 1; }
    }
    count
}
```

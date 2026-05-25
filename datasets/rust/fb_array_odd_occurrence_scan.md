# fb_array_odd_occurrence_scan

## Problem

Scan the first `n` elements and return the odd value seen at each odd-numbered odd occurrence.

## Requirements

- Array length is at most `50`.
- Array values are signed 32-bit integers.
- Do not read stdin or write stdout.

## Source

- Source: FormalBenchHF base program `GetOddOccurrence.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_array_odd_occurrence_scan(arr: &[i32], n: i32) -> i32 {
    let (mut result, mut count) = (0, 0);
    for i in 0..(n as usize) { if arr[i] % 2 != 0 { count += 1; if count % 2 != 0 { result = arr[i]; } } }
    result
}
```

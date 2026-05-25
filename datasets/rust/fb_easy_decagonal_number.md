# fb_easy_decagonal_number

## Problem

Return the `n`th value of the FormalBench decagonal-number recurrence.

## Requirements

- `0 <= n <= 1000`.
- Use `f[0]=0` and `f[i+1]=f[i]+8*i+1`.

## Source

- Source: FormalBenchHF base program `IsNumDecagonal.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_easy_decagonal_number(mut n: i32) -> i32 {
    let mut value = 0;
    for i in 0..n { value += 8 * i + 1; }
    value
}
```

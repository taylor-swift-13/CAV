# fb_lucas_number

## Problem

Return the `n`th Lucas number with `L(0)=2`, `L(1)=1`, and `L(n)=L(n-1)+L(n-2)`.

## Requirements

- `1 <= n <= 30`.
- Return the signed 32-bit integer result.

## Source

- Source: FormalBenchHF base program `FindLucas.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_lucas_number(n: i32) -> i32 {
    let n = n as usize;
    let mut values = vec![0; n + 1];
    values[0] = 2; values[1] = 1;
    for i in 2..=n { values[i] = values[i - 1] + values[i - 2]; }
    values[n]
}
```

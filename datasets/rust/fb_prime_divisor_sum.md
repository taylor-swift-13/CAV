# fb_prime_divisor_sum

## Problem

Return the sum of the distinct prime divisors of `n`.

## Requirements

- `2 <= n <= 10000`.
- Each prime divisor is counted once.

## Source

- Source: FormalBenchHF base program `Sum.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_prime_divisor_sum(n: i32) -> i32 {
    let n = n as usize;
    let mut sums = vec![0; n + 1];
    for i in 2..=n {
        if sums[i] == 0 {
            let mut j = i;
            while j <= n { sums[j] += i as i32; j += i; }
        }
    }
    sums[n]
}
```

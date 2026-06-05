# LC Ones And Zeroes Max Form

## Problem

Return the largest subset size with at most `m` zeroes and `n` ones.

## Requirements

- Binary strings are separated by semicolons.

## Source

- Source: LeetCode problem `ones-and-zeroes`.
- URL: https://leetcode.com/problems/ones-and-zeroes/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_ones_zeroes_max_form(strs: &str, m: i32, n: i32) -> i32 {
    let mm = m as usize; let nn = n as usize; let mut dp = vec![vec![0; nn + 1]; mm + 1]; for s in strs.split(';') { let z = s.bytes().filter(|&b| b == b'0').count(); let o = s.len() - z; let mut a = mm + 1; while a > z { a -= 1; let mut b = nn + 1; while b > o { b -= 1; let cand = dp[a - z][b - o] + 1; if cand > dp[a][b] { dp[a][b] = cand; } } } } dp[mm][nn]
}
```

# LC Find Town Judge

## Problem

Return the label of the town judge, or `-1` if no judge exists.

## Requirements

- `trust` is semicolon-separated `a,b` pairs.
- People are labeled from `1` to `n`.

## Source

- Source: LeetCode problem `find-the-town-judge`.
- URL: https://leetcode.com/problems/find-the-town-judge/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_find_town_judge(n: i32, trust: &str) -> i32 {
    let mut score = vec![0; n as usize + 1]; for pair in trust.split(';') { let p: Vec<usize> = pair.split(',').map(|x| x.parse::<usize>().unwrap()).collect(); score[p[0]] -= 1; score[p[1]] += 1; } for person in 1..=n as usize { if score[person] == n - 1 { return person as i32; } } -1
}
```

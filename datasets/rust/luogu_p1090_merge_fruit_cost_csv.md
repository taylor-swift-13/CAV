# Luogu P1090 Merge Fruit Cost CSV

## Problem

Return the minimum total cost of repeatedly merging the two smallest piles.

## Requirements

- `piles` is a nonempty comma-separated list of positive integers.
- This is the Huffman-style greedy objective from Luogu P1090.

## Source

- Source: Luogu problem `P1090`.
- URL: https://www.luogu.com.cn/problem/P1090
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn luogu_p1090_merge_fruit_cost_csv(piles: &str) -> i32 {
    let mut a: Vec<i32> = piles.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut cost = 0; while a.len() > 1 { a.sort(); let merged = a[0] + a[1]; cost += merged; a[1] = merged; a.remove(0); } cost
}
```

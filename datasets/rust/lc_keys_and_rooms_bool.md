# LC Keys And Rooms Bool

## Problem

Return true if every room can be visited starting from room `0`.

## Requirements

- Rooms are semicolon-separated.
- Keys inside a room are comma-separated room numbers; `-` encodes no keys.

## Source

- Source: LeetCode problem `keys-and-rooms`.
- URL: https://leetcode.com/problems/keys-and-rooms/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_keys_and_rooms_bool(rooms: &str) -> bool {
    let rs: Vec<&str> = rooms.split(';').collect(); let mut seen = vec![false; rs.len()]; let mut st = vec![0usize]; seen[0] = true; let mut count = 0; while let Some(v) = st.pop() { count += 1; if rs[v] != "-" { for p in rs[v].split(',') { let key = p.parse::<usize>().unwrap(); if !seen[key] { seen[key] = true; st.push(key); } } } } count == rs.len()
}
```

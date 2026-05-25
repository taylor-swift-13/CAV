# goal_parser_interpret

## Problem

Interpret a command string where `G` maps to `G`, `()` maps to `o`, and `(al)` maps to `al`.

## Requirements

- Input is a concatenation of tokens `G`, `()`, and `(al)`.
- Map tokens exactly as specified.
- Return the concatenated interpreted string.
- No other characters appear.

## Source

- Source: LeetCode problem `goal-parser-interpretation`.
- URL: https://leetcode.com/problems/goal-parser-interpretation/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn goal_parser_interpret(command: &str) -> String {
    let b = command.as_bytes(); let mut out = String::new(); let mut i = 0usize;
    while i < b.len() { if b[i] == b'G' { out.push('G'); i += 1; } else if b[i + 1] == b')' { out.push('o'); i += 2; } else { out.push_str("al"); i += 4; } }
    out
}
```

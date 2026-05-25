# scrabble_score

## Problem

Return the Scrabble score of an ASCII word. Letter case is ignored.

## Requirements

- Implement exactly the named function shown in the reference implementation.
- Use only the language standard library.
- The function must be deterministic and must not read stdin or write stdout.
- Inputs satisfy the stated problem preconditions; behavior outside those preconditions is intentionally unspecified.

## Source

- Source: Exercism practice exercise `scrabble-score`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/scrabble-score
- License note: prompt rewrite and implementations are local; upstream inspiration is Exercism MIT licensed.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn scrabble_score(word: &str) -> i32 {
    let mut score = 0;
    for b in word.bytes() {
        let c = if b >= b'a' && b <= b'z' { b - b'a' + b'A' } else { b };
        if b"AEIOULNRST".contains(&c) { score += 1; }
        else if b"DG".contains(&c) { score += 2; }
        else if b"BCMP".contains(&c) { score += 3; }
        else if b"FHVWY".contains(&c) { score += 4; }
        else if c == b'K' { score += 5; }
        else if b"JX".contains(&c) { score += 8; }
        else if b"QZ".contains(&c) { score += 10; }
    }
    score
}
```

# Exercism Secret Handshake Code

## Problem

Return a compact code for the secret-handshake actions selected by bits 0 through 3 of `n`.

## Requirements

- Ignore reverse-order bit 4.
- `n >= 0`.
- Bit `i` contributes `1 << i` to the returned code.

## Source

- Source: Exercism problem `secret-handshake`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/secret-handshake
- License note: MIT.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int ex_secret_handshake_code(int n) {
    return n & 15;
}
```

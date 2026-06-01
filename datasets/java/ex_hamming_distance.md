# Exercism Hamming Distance

## Problem

Return the Hamming distance between equal-length strings `a` and `b`.

## Requirements

- Inputs have equal length.
- Strings are ASCII.

## Source

- Source: Exercism problem `hamming`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/hamming
- License note: MIT.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class ExHammingDistance {
    public static int ex_hamming_distance(String a, String b) {
        int d = 0; for (int i = 0; i < a.length(); i++) if (a.charAt(i) != b.charAt(i)) d++; return d;
    }
}
```

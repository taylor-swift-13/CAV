# Exercism Roman Numerals Value

## Problem

Return the integer value of a valid Roman numeral string.

## Requirements

- Input is a valid Roman numeral using `I,V,X,L,C,D,M`.
- Result fits in signed 32-bit integer range.

## Source

- Source: Exercism problem `roman-numerals`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/roman-numerals
- License note: MIT.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class ExRomanValue {
    public static int ex_roman_value(String s) {
        int sum = 0, prev = 0;
        for (int i = 0; i < s.length(); i++) { char c = s.charAt(i); int v = c == 'I' ? 1 : c == 'V' ? 5 : c == 'X' ? 10 : c == 'L' ? 50 : c == 'C' ? 100 : c == 'D' ? 500 : 1000; sum += v; if (prev < v) sum -= 2 * prev; prev = v; }
        return sum;
    }
}
```

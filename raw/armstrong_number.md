# armstrong_number

## Problem

Return true if `n` equals the sum of its digits each raised to the number of digits.

## Requirements

- Implement exactly the named function shown in the reference implementation.
- Use only the language standard library.
- The function must be deterministic and must not read stdin or write stdout.
- Inputs satisfy the stated problem preconditions; behavior outside those preconditions is intentionally unspecified.

## Source

- Source: Exercism practice exercise `armstrong-numbers`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/armstrong-numbers
- License note: prompt rewrite and implementations are local; upstream inspiration is Exercism MIT licensed.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int armstrong_number(int n) {
    int temp = n;
    int digits = 0;
    if (temp == 0) digits = 1;
    while (temp > 0) { digits++; temp /= 10; }
    temp = n;
    int sum = 0;
    if (temp == 0) sum = 0;
    while (temp > 0) {
        int d = temp % 10;
        int p = 1;
        for (int i = 0; i < digits; i++) p *= d;
        sum += p;
        temp /= 10;
    }
    return sum == n;
}
```

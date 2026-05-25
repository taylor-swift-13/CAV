# is_even

## Problem

Return true if integer `n` is divisible by 2; otherwise return false.

## Requirements

- `n` is a signed 32-bit integer.
- Zero is even and must return true.
- Negative values follow normal divisibility by 2; no absolute-value special case is allowed.
- The function must not allocate, read stdin, or write stdout.

## Source

- Source: local simple-function seed `is-even`.
- URL: local dataset seed, no upstream problem URL.
- License note: prompt and implementation are local to this repository.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class IsEven {
    public static boolean is_even(int n) {
        return n % 2 == 0;
    }
}
```

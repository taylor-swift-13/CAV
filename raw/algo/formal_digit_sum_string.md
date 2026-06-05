# formal_digit_sum_string

## Problem

Return the sum of decimal digit characters in ASCII string `s`.

## Requirements

- Input is ASCII.
- Only digit characters contribute.
- Non-digits are ignored.
- Return the arithmetic sum of digit values.

## Source

- Source: FormalBench-inspired program `string-digit-sum`.
- URL: https://github.com/thanhlecongg/FormalBench/
- Data URL: https://huggingface.co/datasets/FormalBench/FormalBench
- License note: this is a local HumanEval-like rewrite for C/Java/Rust shared tests.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int formal_digit_sum_string(const char *s) {
    int sum = 0;
    for (int i = 0; s[i] != '\0'; i++) if (s[i] >= '0' && s[i] <= '9') sum += s[i] - '0';
    return sum;
}
```

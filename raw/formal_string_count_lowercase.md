# formal_string_count_lowercase

## Problem

Return how many lowercase ASCII letters appear in `s`.

## Requirements

- Input is ASCII.
- Only `a` through `z` count.
- Uppercase letters and digits do not count.
- The empty string returns zero.

## Source

- Source: FormalBench-inspired program `string-count-lowercase`.
- URL: https://github.com/thanhlecongg/FormalBench/
- Data URL: https://huggingface.co/datasets/FormalBench/FormalBench
- License note: this is a local HumanEval-like rewrite for C/Java/Rust shared tests.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int formal_string_count_lowercase(const char *s) {
    int count = 0;
    for (int i = 0; s[i] != '\0'; i++) if (s[i] >= 'a' && s[i] <= 'z') count++;
    return count;
}
```

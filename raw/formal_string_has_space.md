# formal_string_has_space

## Problem

Return true if ASCII string `s` contains at least one space character.

## Requirements

- Input is ASCII.
- Only the literal space character counts.
- Tabs are outside this task.
- Return false for the empty string.

## Source

- Source: FormalBench-inspired program `string-has-space`.
- URL: https://github.com/thanhlecongg/FormalBench/
- Data URL: https://huggingface.co/datasets/FormalBench/FormalBench
- License note: this is a local HumanEval-like rewrite for C/Java/Rust shared tests.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int formal_string_has_space(const char *s) {
    for (int i = 0; s[i] != '\0'; i++) if (s[i] == ' ') return 1;
    return 0;
}
```

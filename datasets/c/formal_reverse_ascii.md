# formal_reverse_ascii

## Problem

Return the reverse of ASCII string `s`.

## Requirements

- Input is an ASCII string.
- The empty string reverses to the empty string.
- Return a new reversed string.
- Do not drop punctuation or spaces.

## Source

- Source: FormalBench-inspired program `string-reverse`.
- URL: https://github.com/thanhlecongg/FormalBench/
- Data URL: https://huggingface.co/datasets/FormalBench/FormalBench
- License note: this is a local HumanEval-like rewrite for C/Java/Rust shared tests.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
char *formal_reverse_ascii(const char *s) {
    int n = 0;
    while (s[n] != '\0') n++;
    char *out = (char *)malloc((unsigned long)n + 1);
    for (int i = 0; i < n; i++) out[i] = s[n - 1 - i];
    out[n] = '\0';
    return out;
}
```

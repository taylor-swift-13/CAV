# formal_string_count_letter_a

## Problem

Return how many lowercase `a` characters appear in ASCII string `s`.

## Requirements

- Input is ASCII.
- Only lowercase `a` counts.
- Uppercase `A` does not count.
- The empty string returns zero.

## Source

- Source: FormalBench-inspired program `string-count-char`.
- URL: https://github.com/thanhlecongg/FormalBench/
- Data URL: https://huggingface.co/datasets/FormalBench/FormalBench
- License note: this is a local HumanEval-like rewrite for C/Java/Rust shared tests.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FormalStringCountLetterA {
    public static int formal_string_count_letter_a(String s) {
        int count = 0;
        for (int i = 0; i < s.length(); i++) if (s.charAt(i) == 'a') count++;
        return count;
    }
}
```

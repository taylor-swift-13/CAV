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

```java
class FormalReverseAscii {
    public static String formal_reverse_ascii(String s) {
        StringBuilder out = new StringBuilder();
        for (int i = s.length() - 1; i >= 0; i--) out.append(s.charAt(i));
        return out.toString();
    }
}
```

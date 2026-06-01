# Exercism Matching Brackets ASCII

## Problem

Return true if brackets in `s` are correctly nested and matched.

## Requirements

- Only `()`, `[]`, and `{}` are bracket tokens.
- Other ASCII characters are ignored.

## Source

- Source: Exercism problem `matching-brackets`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/matching-brackets
- License note: MIT.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class ExMatchingBracketsAscii {
    public static boolean ex_matching_brackets_ascii(String s) {
        char[] st = new char[128]; int top = 0;
        for (int i = 0; i < s.length(); i++) { char c = s.charAt(i); if (c == '(' || c == '[' || c == '{') st[top++] = c; else if (c == ')' || c == ']' || c == '}') { if (top == 0) return false; char o = st[--top]; if ((c == ')' && o != '(') || (c == ']' && o != '[') || (c == '}' && o != '{')) return false; } }
        return top == 0;
    }
}
```

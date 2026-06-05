# length_of_last_word

## Problem

Return the length of the last word in string `s`.

## Requirements

- `s` contains printable ASCII letters and spaces.
- There is at least one non-space character.
- A word is a maximal contiguous sequence of non-space characters.
- Trailing spaces must be ignored.
- Only the length is returned; the last word itself is not returned.

## Source

- Source: LeetCode problem `length-of-last-word`.
- URL: https://leetcode.com/problems/length-of-last-word/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int length_of_last_word(const char *s) {
    int i = 0;
    while (s[i] != '\0') i++;
    i--;
    while (i >= 0 && s[i] == ' ') i--;
    int count = 0;
    while (i >= 0 && s[i] != ' ') { count++; i--; }
    return count;
}
```

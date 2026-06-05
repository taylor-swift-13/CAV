# sentence_is_pangram_ascii

## Problem

Return true if lowercase sentence `sentence` contains every English letter at least once.

## Requirements

- Input contains only lowercase English letters.
- Return true exactly when all 26 letters appear.
- Repeated letters are allowed.
- The empty string is not pangram.

## Source

- Source: LeetCode problem `check-if-the-sentence-is-pangram`.
- URL: https://leetcode.com/problems/check-if-the-sentence-is-pangram/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int sentence_is_pangram_ascii(const char *sentence) {
    int seen[26] = {0};
    int count = 0;
    for (int i = 0; sentence[i] != '\0'; i++) { int k = sentence[i] - 'a'; if (!seen[k]) { seen[k] = 1; count++; } }
    return count == 26;
}
```

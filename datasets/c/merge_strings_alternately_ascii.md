# merge_strings_alternately_ascii

## Problem

Merge `word1` and `word2` by alternating characters, starting with `word1`.

## Requirements

- Inputs are ASCII strings.
- Take one character from `word1`, then one from `word2`, repeatedly.
- Append the remaining suffix of the longer string.
- The empty string is allowed.

## Source

- Source: LeetCode problem `merge-strings-alternately`.
- URL: https://leetcode.com/problems/merge-strings-alternately/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
#include <stdlib.h>
char *merge_strings_alternately_ascii(const char *word1, const char *word2) {
    int n = 0, m = 0;
    while (word1[n] != '\0') n++;
    while (word2[m] != '\0') m++;
    char *out = (char *)malloc((unsigned long)n + (unsigned long)m + 1);
    int pos = 0;
    int limit = n > m ? n : m;
    for (int i = 0; i < limit; i++) { if (i < n) out[pos++] = word1[i]; if (i < m) out[pos++] = word2[i]; }
    out[pos] = '\0';
    return out;
}
```

# reverse_vowels_ascii

## Problem

Return a copy of `s` with only ASCII vowels reversed.

## Requirements

- `s` contains only ASCII characters in this dataset variant.
- Vowels are `a e i o u` and `A E I O U`.
- Only vowel positions change; consonants, digits, punctuation, and spaces remain at their original positions.
- The relative order of reversed vowels follows a full two-pointer reversal.

## Source

- Source: LeetCode problem `reverse-vowels-of-a-string`.
- URL: https://leetcode.com/problems/reverse-vowels-of-a-string/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int is_vowel_rv(char c) { return c=='a'||c=='e'||c=='i'||c=='o'||c=='u'||c=='A'||c=='E'||c=='I'||c=='O'||c=='U'; }
char *reverse_vowels_ascii(const char *s) {
    int n = 0;
    while (s[n] != '\0') n++;
    char *out = (char *)malloc((unsigned long)n + 1);
    for (int i = 0; i <= n; i++) out[i] = s[i];
    int l = 0;
    int r = n - 1;
    while (l < r) {
        while (l < r && !is_vowel_rv(out[l])) l++;
        while (l < r && !is_vowel_rv(out[r])) r--;
        if (l < r) { char t = out[l]; out[l] = out[r]; out[r] = t; l++; r--; }
    }
    return out;
}
```

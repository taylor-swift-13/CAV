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

```java
class ReverseVowelsAscii {
    static boolean isVowel(char c) { return "aeiouAEIOU".indexOf(c) >= 0; }
    public static String reverse_vowels_ascii(String s) {
        char[] out = s.toCharArray();
        int l = 0, r = out.length - 1;
        while (l < r) {
            while (l < r && !isVowel(out[l])) l++;
            while (l < r && !isVowel(out[r])) r--;
            if (l < r) { char t = out[l]; out[l] = out[r]; out[r] = t; l++; r--; }
        }
        return new String(out);
    }
}
```

# restore_string_by_indices

## Problem

Restore a string by placing `s[i]` at index `indices[i]`; indices are comma-separated integers.

## Requirements

- `indices` is a permutation of `0..len(s)-1`.
- `indices` is comma-separated with no spaces.
- Return a string `out` such that `out[indices[i]] == s[i]`.
- Input strings are ASCII.

## Source

- Source: LeetCode problem `shuffle-string`.
- URL: https://leetcode.com/problems/shuffle-string/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class RestoreStringByIndices {
    public static String restore_string_by_indices(String s, String indices) {
        char[] out = new char[s.length()];
        String[] parts = indices.split(",");
        for (int i = 0; i < parts.length; i++) out[Integer.parseInt(parts[i])] = s.charAt(i);
        return new String(out);
    }
}
```

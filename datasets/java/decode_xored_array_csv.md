# decode_xored_array_csv

## Problem

Given comma-separated XOR-encoded values and the first original value, return the decoded array.

## Requirements

- `encoded[i] = arr[i] XOR arr[i+1]`.
- `encoded` is comma-separated nonnegative integers.
- The empty string means the original array only contains `first`.
- Return the decoded array as comma-separated integers.

## Source

- Source: LeetCode problem `decode-xored-array`.
- URL: https://leetcode.com/problems/decode-xored-array/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class DecodeXoredArrayCsv {
    public static String decode_xored_array_csv(String encoded, int first) {
        StringBuilder out = new StringBuilder();
        int cur = first;
        out.append(cur);
        if (!encoded.isEmpty()) for (String p : encoded.split(",")) { cur ^= Integer.parseInt(p); out.append(',').append(cur); }
        return out.toString();
    }
}
```

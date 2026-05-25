# reverse_list_csv

## Problem

Treat comma-separated integer string `list` as a linked list and return its values in reverse order.

## Requirements

- `list` is comma-separated base-10 integers with no spaces.
- The empty string represents an empty list.
- Return a comma-separated string using the same integer spelling after parsing.
- At most 64 integers are encoded.

## Source

- Source: LeetCode problem `reverse-linked-list`.
- URL: https://leetcode.com/problems/reverse-linked-list/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class ReverseListCsv {
    public static String reverse_list_csv(String list) {
        if (list.isEmpty()) return "";
        String[] p = list.split(",");
        StringBuilder out = new StringBuilder();
        for (int i = p.length - 1; i >= 0; i--) { if (out.length() > 0) out.append(','); out.append(p[i]); }
        return out.toString();
    }
}
```

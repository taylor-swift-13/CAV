# merge_sorted_lists_csv

## Problem

Treat `a` and `b` as sorted linked lists encoded by comma-separated integers and return their sorted merge.

## Requirements

- Each input is a sorted comma-separated integer list with no spaces.
- The empty string represents an empty list.
- Return all values in nondecreasing order.
- At most 64 integers are encoded per input.

## Source

- Source: LeetCode problem `merge-two-sorted-lists`.
- URL: https://leetcode.com/problems/merge-two-sorted-lists/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class MergeSortedListsCsv {
    public static String merge_sorted_lists_csv(String a, String b) {
        String[] ap = a.isEmpty() ? new String[0] : a.split(",");
        String[] bp = b.isEmpty() ? new String[0] : b.split(",");
        int i = 0, j = 0;
        StringBuilder out = new StringBuilder();
        while (i < ap.length || j < bp.length) {
            int v;
            if (j >= bp.length || (i < ap.length && Integer.parseInt(ap[i]) <= Integer.parseInt(bp[j]))) v = Integer.parseInt(ap[i++]); else v = Integer.parseInt(bp[j++]);
            if (out.length() > 0) out.append(',');
            out.append(v);
        }
        return out.toString();
    }
}
```

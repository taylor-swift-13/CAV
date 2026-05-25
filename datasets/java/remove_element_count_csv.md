# remove_element_count_csv

## Problem

Return how many values in comma-separated integer string `nums` are not equal to `val`.

## Requirements

- `nums` is comma-separated base-10 integers with no spaces.
- The empty string represents an empty array.
- Return only the kept length, not the reordered array.
- At most 64 integers are encoded.

## Source

- Source: LeetCode problem `remove-element`.
- URL: https://leetcode.com/problems/remove-element/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class RemoveElementCountCsv {
    public static int remove_element_count_csv(String nums, int val) {
        if (nums.isEmpty()) return 0;
        int count = 0;
        for (String p : nums.split(",")) if (Integer.parseInt(p) != val) count++;
        return count;
    }
}
```

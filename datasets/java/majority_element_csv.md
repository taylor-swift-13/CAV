# majority_element_csv

## Problem

Return the value that appears more than half the time in comma-separated integer string `nums`.

## Requirements

- `nums` is nonempty and comma-separated with no spaces.
- A majority element is guaranteed to exist.
- Return the element value.
- At most 64 integers are encoded.

## Source

- Source: LeetCode problem `majority-element`.
- URL: https://leetcode.com/problems/majority-element/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class MajorityElementCsv {
    public static int majority_element_csv(String nums) {
        int candidate = 0, count = 0;
        for (String p : nums.split(",")) {
            int v = Integer.parseInt(p);
            if (count == 0) { candidate = v; count = 1; }
            else if (candidate == v) count++;
            else count--;
        }
        return candidate;
    }
}
```

# MBPP 250 Count X

## Problem

Write a python function that takes in a tuple and an element and counts the occcurences of the element in the tuple.

## Signature

- Python: `count_X(tup: List[int], x: int) -> int`
- C entrypoint: `mbpp_250_count_X`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert count_X((10, 8, 5, 2, 10, 15, 10, 8, 5, 8, 8, 2),4) == 0`
- `assert count_X((10, 8, 5, 2, 10, 15, 10, 8, 5, 8, 8, 2),10) == 3`
- `assert count_X((10, 8, 5, 2, 10, 15, 10, 8, 5, 8, 8, 2),8) == 4`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 250.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def count_X(tup, x): 
    count = 0
    for ele in tup: 
        if (ele == x): 
            count = count + 1
    return count
```

## Reference Implementation

```c
int mbpp_250_count_X(int *tup, int tup_size, int x) {
    int count = 0;
    int ele;
    for (int __mbpp_i0 = 0; __mbpp_i0 < tup_size; __mbpp_i0++) {
        ele = tup[__mbpp_i0];
        if ((ele == x)) {
            count = (count + 1);
        }
    }
    return count;
}
```

# MBPP 66 Pos Count

## Problem

Write a python function to count the number of positive numbers in a list.

## Signature

- Python: `pos_count(list: List[int]) -> int`
- C entrypoint: `mbpp_66_pos_count`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert pos_count([1,-2,3,-4]) == 2`
- `assert pos_count([3,4,5,-1]) == 3`
- `assert pos_count([1,2,3,4]) == 4`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 66.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def pos_count(list):
  pos_count= 0
  for num in list: 
    if num >= 0: 
      pos_count += 1
  return pos_count
```

## Reference Implementation

```c
int mbpp_66_pos_count(int *list, int list_size) {
    int pos_count = 0;
    int num;
    for (int __mbpp_i0 = 0; __mbpp_i0 < list_size; __mbpp_i0++) {
        num = list[__mbpp_i0];
        if ((num >= 0)) {
            pos_count += 1;
        }
    }
    return pos_count;
}
```

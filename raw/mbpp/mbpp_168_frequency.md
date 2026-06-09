# MBPP 168 Frequency

## Problem

Write a function to count the number of occurrences of a number in a given list.

## Signature

- Python: `frequency(a: List[int], x: int) -> int`
- C entrypoint: `mbpp_168_frequency`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert frequency([1,2,3], 4) == 0`
- `assert frequency([1,2,2,3,3,3,4], 3) == 3`
- `assert frequency([0,1,2,3,1,2], 1) == 2`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 168.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def frequency(a,x): 
    count = 0  
    for i in a: 
      if i == x: 
        count += 1

    return count
```

## Reference Implementation

```c
int mbpp_168_frequency(int *a, int a_size, int x) {
    int count = 0;
    int i;
    for (int __mbpp_i0 = 0; __mbpp_i0 < a_size; __mbpp_i0++) {
        i = a[__mbpp_i0];
        if ((i == x)) {
            count += 1;
        }
    }
    return count;
}
```

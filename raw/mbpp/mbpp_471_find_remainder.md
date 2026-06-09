# MBPP 471 Find Remainder

## Problem

Write a python function to find the product of the array multiplication modulo n.

## Signature

- Python: `find_remainder(arr: List[int], n: int) -> int`
- C entrypoint: `mbpp_471_find_remainder`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert find_remainder([ 100, 10, 5, 25, 35, 14 ],11) ==9`
- `assert find_remainder([1,1,1],1) == 0`
- `assert find_remainder([1,2,1],2) == 0`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 471.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def find_remainder(arr, n): 
    mul = 1
    for i in range(len(arr)):  
        mul = (mul * (arr[i] % n)) % n 
    return mul % n
```

## Reference Implementation

```c
int mbpp_471_find_remainder(int *arr, int arr_size, int n) {
    int mul = 1;
    int i;
    for (i = 0; i < arr_size; i++) {
        mul = ((mul * (arr[i] % n)) % n);
    }
    return (mul % n);
}
```

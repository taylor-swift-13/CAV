# MBPP 119 Search

## Problem

Write a python function to find the element that appears only once in a sorted array.

## Signature

- Python: `search(arr: List[int]) -> int`
- C entrypoint: `mbpp_119_search`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert search([1,1,2,2,3]) == 3`
- `assert search([1,1,3,3,4,4,5,5,7,7,8]) == 8`
- `assert search([1,2,2,3,3,4,4]) == 1`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 119.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def search(arr):
    n = len(arr)
    XOR = 0
    for i in range(n) :
        XOR = XOR ^ arr[i]
    return (XOR)
```

## Reference Implementation

```c
int mbpp_119_search(int *arr, int arr_size) {
    int n = arr_size;
    int XOR = 0;
    int i;
    for (i = 0; i < n; i++) {
        XOR = (XOR ^ arr[i]);
    }
    return XOR;
}
```

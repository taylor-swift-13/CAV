# MBPP 270 Sum Even And Even Index

## Problem

Write a python function to find the sum of even numbers at even positions of a list.

## Signature

- Python: `sum_even_and_even_index(arr: List[int]) -> int`
- C entrypoint: `mbpp_270_sum_even_and_even_index`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert sum_even_and_even_index([5, 6, 12, 1, 18, 8]) == 30`
- `assert sum_even_and_even_index([3, 20, 17, 9, 2, 10, 18, 13, 6, 18]) == 26`
- `assert sum_even_and_even_index([5, 6, 12, 1]) == 12`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 270.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def sum_even_and_even_index(arr):  
    i = 0
    sum = 0
    for i in range(0, len(arr),2): 
        if (arr[i] % 2 == 0) : 
            sum += arr[i]  
    return sum
```

## Reference Implementation

```c
int mbpp_270_sum_even_and_even_index(int *arr, int arr_size) {
    int i = 0;
    int sum = 0;
    for (i = 0; i < arr_size; i += 2) {
        if (((arr[i] % 2) == 0)) {
            sum += arr[i];
        }
    }
    return sum;
}
```

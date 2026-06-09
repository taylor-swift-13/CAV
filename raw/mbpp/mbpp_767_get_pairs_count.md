# MBPP 767 Get Pairs Count

## Problem

Write a python function to count the number of pairs whose sum is equal to ‘sum’. The funtion gets as input a list of numbers and the sum,

## Signature

- Python: `get_pairs_count(arr: List[int], sum: int) -> int`
- C entrypoint: `mbpp_767_get_pairs_count`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert get_pairs_count([1,1,1,1],2) == 6`
- `assert get_pairs_count([1,5,7,-1,5],6) == 3`
- `assert get_pairs_count([1,-2,3],1) == 1`
- `assert get_pairs_count([-1,-2,3],-3) == 1`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 767.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def get_pairs_count(arr, sum):
    count = 0  
    for i in range(len(arr)):
        for j in range(i + 1,len(arr)):
            if arr[i] + arr[j] == sum:
                count += 1
    return count
```

## Reference Implementation

```c
int mbpp_767_get_pairs_count(int *arr, int arr_size, int sum) {
    int count = 0;
    int i;
    for (i = 0; i < arr_size; i++) {
        int j;
        for (j = (i + 1); j < arr_size; j++) {
            if (((arr[i] + arr[j]) == sum)) {
                count += 1;
            }
        }
    }
    return count;
}
```

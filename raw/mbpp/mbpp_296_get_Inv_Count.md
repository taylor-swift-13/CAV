# MBPP 296 Get Inv Count

## Problem

Write a python function to count inversions in an array.

## Signature

- Python: `get_Inv_Count(arr: List[int]) -> int`
- C entrypoint: `mbpp_296_get_Inv_Count`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert get_Inv_Count([1,20,6,4,5]) == 5`
- `assert get_Inv_Count([1,2,1]) == 1`
- `assert get_Inv_Count([1,2,5,6,1]) == 3`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 296.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def get_Inv_Count(arr): 
    inv_count = 0
    for i in range(len(arr)): 
        for j in range(i + 1, len(arr)): 
            if (arr[i] > arr[j]): 
                inv_count += 1
    return inv_count
```

## Reference Implementation

```c
int mbpp_296_get_Inv_Count(int *arr, int arr_size) {
    int inv_count = 0;
    int i;
    for (i = 0; i < arr_size; i++) {
        int j;
        for (j = (i + 1); j < arr_size; j++) {
            if ((arr[i] > arr[j])) {
                inv_count += 1;
            }
        }
    }
    return inv_count;
}
```

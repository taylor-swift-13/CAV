# MBPP 802 Count Rotation

## Problem

Write a python function to count the number of rotations required to generate a sorted array. https://www.geeksforgeeks.org/count-of-rotations-required-to-generate-a-sorted-array/

## Signature

- Python: `count_rotation(arr: List[int]) -> int`
- C entrypoint: `mbpp_802_count_rotation`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert count_rotation([3,2,1]) == 1`
- `assert count_rotation([4,5,1,2,3]) == 2`
- `assert count_rotation([7,8,9,1,2,3]) == 3`
- `assert count_rotation([1,2,3]) == 0`
- `assert count_rotation([1,3,2]) == 2`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 802.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def count_rotation(arr):   
    for i in range (1,len(arr)): 
        if (arr[i] < arr[i - 1]): 
            return i  
    return 0
```

## Reference Implementation

```c
int mbpp_802_count_rotation(int *arr, int arr_size) {
    int i;
    for (i = 1; i < arr_size; i++) {
        if ((arr[i] < arr[(i - 1)])) {
            return i;
        }
    }
    return 0;
}
```
